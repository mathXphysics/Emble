import random
import os
import pickle
from board import FULL

_CACHE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "magic_cache.pkl")
_CACHE_VERSION = 1

BISHOP_DIRS = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
ROOK_DIRS = [(1, 0), (-1, 0), (0, 1), (0, -1)]


def _popcount(bb):
    return bin(bb).count("1")


def _relevant_mask(square, dirs):
    r, f = square // 8, square % 8
    result = 0
    for dr, df in dirs:
        rr, ff = r + dr, f + df
        while 0 <= rr <= 7 and 0 <= ff <= 7:
            nr, nf = rr + dr, ff + df
            if 0 <= nr <= 7 and 0 <= nf <= 7:
                result |= 1 << (rr * 8 + ff)
            rr, ff = nr, nf
    return result


def _slow_attacks(square, occupancy, dirs):
    r, f = square // 8, square % 8
    result = 0
    for dr, df in dirs:
        rr, ff = r + dr, f + df
        while 0 <= rr <= 7 and 0 <= ff <= 7:
            target = rr * 8 + ff
            result |= 1 << target
            if occupancy & (1 << target):
                break
            rr += dr
            ff += df
    return result


def _subsets_of_mask(mask):
    subsets = []
    subset = 0
    while True:
        subsets.append(subset)
        subset = (subset - mask) & mask
        if subset == 0:
            break
    return subsets


def _find_magic(square, mask, dirs, rng):
    bits = _popcount(mask)
    size = 1 << bits
    shift = 64 - bits
    subsets = _subsets_of_mask(mask)
    ground_truth = [_slow_attacks(square, occ, dirs) for occ in subsets]

    while True:
        magic = rng.getrandbits(64) & rng.getrandbits(64) & rng.getrandbits(64)
        if magic == 0:
            continue
        table = [None] * size
        ok = True
        for occ, atk in zip(subsets, ground_truth):
            idx = ((occ * magic) & FULL) >> shift
            if table[idx] is None:
                table[idx] = atk
            elif table[idx] != atk:
                ok = False
                break
        if ok:
            return magic, shift, table


def _build_tables(dirs):
    rng = random.Random(1337)
    masks = [0] * 64
    magics = [0] * 64
    shifts = [0] * 64
    tables = [None] * 64
    for square in range(64):
        mask = _relevant_mask(square, dirs)
        magic, shift, table = _find_magic(square, mask, dirs, rng)
        masks[square] = mask
        magics[square] = magic
        shifts[square] = shift
        tables[square] = table
    return masks, magics, shifts, tables


def _load_or_build_all():
    if os.path.exists(_CACHE_PATH):
        try:
            with open(_CACHE_PATH, "rb") as f:
                cached = pickle.load(f)
            if cached.get("version") == _CACHE_VERSION:
                return (cached["bishop_masks"], cached["bishop_magics"],
                        cached["bishop_shifts"], cached["bishop_tables"],
                        cached["rook_masks"], cached["rook_magics"],
                        cached["rook_shifts"], cached["rook_tables"])
        except (pickle.PickleError, EOFError, KeyError, OSError):
            pass

    b_masks, b_magics, b_shifts, b_tables = _build_tables(BISHOP_DIRS)
    r_masks, r_magics, r_shifts, r_tables = _build_tables(ROOK_DIRS)

    try:
        with open(_CACHE_PATH, "wb") as f:
            pickle.dump({
                "version": _CACHE_VERSION,
                "bishop_masks": b_masks, "bishop_magics": b_magics,
                "bishop_shifts": b_shifts, "bishop_tables": b_tables,
                "rook_masks": r_masks, "rook_magics": r_magics,
                "rook_shifts": r_shifts, "rook_tables": r_tables,
            }, f)
    except OSError:
        pass

    return b_masks, b_magics, b_shifts, b_tables, r_masks, r_magics, r_shifts, r_tables


(BISHOP_MASKS, BISHOP_MAGICS, BISHOP_SHIFTS, BISHOP_TABLES,
 ROOK_MASKS, ROOK_MAGICS, ROOK_SHIFTS, ROOK_TABLES) = _load_or_build_all()


def get_bishop_attacks(square, occupancy):
    masked = occupancy & BISHOP_MASKS[square]
    idx = ((masked * BISHOP_MAGICS[square]) & FULL) >> BISHOP_SHIFTS[square]
    return BISHOP_TABLES[square][idx]


def get_rook_attacks(square, occupancy):
    masked = occupancy & ROOK_MASKS[square]
    idx = ((masked * ROOK_MAGICS[square]) & FULL) >> ROOK_SHIFTS[square]
    return ROOK_TABLES[square][idx]


def get_queen_attacks(square, occupancy):
    return get_bishop_attacks(square, occupancy) | get_rook_attacks(square, occupancy)
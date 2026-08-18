#!/usr/bin/env python3
"""
Find α and β that maximize min(μ_1, μ_2, μ_3, μ_4),
or compute min(μ_1, μ_2, μ_3, μ_4) for specific α and β.
"""

import sys
import argparse
import itertools
import math

from collections.abc import Callable, Sequence

VERBOSE = False


def constraints(α: float, β: float, n: int) -> bool:
    return (2 <= α and α <= β and β < α + n
        and α + n < α * β
        and (α+n) ** 3 > β * (α*β + 2*n*(α+n))
        and α*(β+n)**2 > β*n*n)

def get_μs(α: float, β: float, n: int) -> tuple[float, float, float, float]:
    if not constraints(α, β, n):
        μ = -(α + β)
        return (μ, μ, μ, μ)

    L1 = α + n - β
    L2 = n*n + α*n + α*β

    chat1 = L2 / ((n+1) * (n+α))
    p1 = 2 / (1 + math.sqrt(1 + 4/(α*chat1)))
    μ1 = chat1 / p1

    μ2 = (n + math.sqrt(L2)) / (n + β)
    μ3 = 2 * L2 / (L1 * n + math.sqrt((n*L1)**2 + 4*α*β*L2))
    μ4 = 1 + β * n / L2

    return (μ1, μ2, μ3, μ4)


def get_cstar(α: float, β: float, n: int) -> float:
    μs = get_μs(α, β, n)
    if VERBOSE:
        print(f'\t\tμs(α={α}, β={β}, n={n}) = {μs}', file=sys.stderr)
    return min(μs)


FS = Sequence[float]
FFP = tuple[float, float]
FFPS = Sequence[FFP]

def coords_to_point(lims: FFPS, m: int, coords: Sequence[int]) -> FS:
    n = len(lims)
    assert len(coords) == n
    x: FS = []
    for i in range(n):
        a = coords[i]/m
        x.append(lims[i][0] * (1 - a) + lims[i][1] * a)
    return x


def grid_max_iter(f: Callable[[FS], float], lims: FFPS, m: int, k: int) -> tuple[FFPS, FS, float, float]:
    n = len(lims)  # number of variables
    coords_list = itertools.product(range(m+1), repeat=n)

    best_coords = None
    best_x = None
    best_y = None
    worst_y = None
    for coords in coords_list:
        x = coords_to_point(lims, m, coords)
        y = f(x)
        if VERBOSE:
            print(f'\tcoords: {coords}, x: {x}, y: {y}', file=sys.stderr)
        if best_y is None or y > best_y:
            best_y, best_coords, best_x = y, coords, x
        if worst_y is None or y < worst_y:
            worst_y = y
    assert best_coords is not None
    assert best_y is not None
    assert best_x is not None
    assert worst_y is not None

    if VERBOSE:
        print(f'\tbest_coords: {best_coords}', file=sys.stderr)
    new_lims = []
    for i in range(n):
        amin = max(0, best_coords[i] - k) / m
        amax = min(m, best_coords[i] + k) / m
        lo, hi = lims[i]
        new_lims.append((lo * (1-amin) + hi * amin, lo * (1-amax) + hi * amax))
    if VERBOSE:
        print(f'\tnew_lims: {new_lims}', file=sys.stderr)

    return (new_lims, best_x, best_y, worst_y)


def grid_max(f: Callable[[FS], float], lims: FFPS, m: int, k: int, ε: float, max_iters: int) -> tuple[FS, float, int]:
    nit = 0
    while True:
        nit += 1
        lims, best_x, best_y, worst_y = grid_max_iter(f, lims, m, k)
        if VERBOSE:
            print(f'nit: {nit}, lims: {lims}, best_x: {best_x}, best_y: {best_y:.8f}, worst_y: {worst_y:.8f}', file=sys.stderr)
        if best_y - worst_y <= ε or nit >= max_iters:
            return (best_x, best_y, nit)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-n', type=int, required=True, help='number of poor buyers')
    parser.add_argument('-v', '--verbose', action='store_true', default=False)
    parser.add_argument('-a', type=float, help='a = n*α')
    parser.add_argument('-b', type=float, help='b = n*β')
    parser.add_argument('--max-iters', type=int, default=1000)
    args = parser.parse_args()
    n = args.n
    if args.verbose:
        global VERBOSE
        VERBOSE = True

    if args.a is not None and args.b is not None:
        α, β = n * args.a , n * args.b
        μs = get_μs(α, β, n)
        cstar = min(μs)
        print(f'min({μs}) = {cstar}')
    else:
        def f(x: FS) -> float:
            α, β = x
            return get_cstar(α, β, n)
        """
        def f(x: FS) -> float:
            x0, x1 = x
            return - (x0 - 0.314*n)**2 - (x1 - 0.515*n)**2
        """

        (α, β), c, nit = grid_max(f, [(2, n)] * 2, m=10, k=3, ε=1e-9, max_iters=args.max_iters)
        print(f'α/n = {α/n}, β/n = {β/n}, c = {c}, nit = {nit}')


if __name__ == '__main__':
    main()

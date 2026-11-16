# erdos-982-lean

Partial Lean 4 formalization of Erdős Problem #982: if n ≥ 3 points form a convex polygon,
some vertex has at least ⌊n/2⌋ distinct distances to the other vertices.

"Convex polygon" is modelled as `ConvexIndependent ℝ p` for `p : Fin n → EuclideanSpace ℝ (Fin 2)`.

## Status: PARTIAL, not a complete proof

* `Challenge.lean` states the theorem `erdos982` (with `sorry`, as a challenge file).
* `Solution.lean` proves, with no `sorry`:
  * `convex_no_three_collinear`
  * `isosceles_bound` (at most 2n(n-1) isosceles triples)
  * `moser_bound` (some vertex has `n - 1 ≤ 3 * dc p i`, i.e. about n/3 distinct distances)
* `half_bound` (the upgrade from n/3 to ⌊n/2⌋) is **open** and left as `sorry`, so the
  final `erdos982` in `Solution.lean` depends on it. The problem is an open conjecture.

The three proved steps were each checked on Principia's Lean/Mathlib (harness run 744f9daa).
The assembled project in this repository has not been compiled locally; the Mathlib version
pinned in `lakefile.toml` (v4.35.0) is a best guess and may need adjusting.

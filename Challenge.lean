import Mathlib

/-!
Erdős Problem #982 (open).

If `p : Fin n → ℝ²` is the vertex family of a convex polygon (convex independent),
then some vertex has at least `⌊n/2⌋` distinct distances to the other vertices.

The formalisation of "convex polygon" is `ConvexIndependent ℝ p` (Mathlib vocabulary).
-/

theorem erdos982 (n : ℕ) (hn : 3 ≤ n) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : ConvexIndependent ℝ p) :
    ∃ i : Fin n, n / 2 ≤ {d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j)}.ncard := by
  sorry

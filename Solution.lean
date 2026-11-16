import Mathlib

/-!
PARTIAL solution for Erdős Problem #982: NOT a complete proof.

Proved here (each step checked on Principia's Lean/Mathlib in harness run 744f9daa):
  * `convex_no_three_collinear`, `isosceles_bound`, `moser_bound` (Moser's n/3 bound).
Open: `half_bound` (upgrade from n/3 to ⌊n/2⌋) is `sorry`; `erdos982` depends on it.
-/

noncomputable def dc {n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin 2)) (i : Fin n) : ℕ :=
  {d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j)}.ncard

theorem convex_no_three_collinear {n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : ConvexIndependent ℝ p) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear ℝ ({p i, p j, p k} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcol
  have key : ∀ a b c : Fin n, a ≠ b → b ≠ c → Wbtw ℝ (p a) (p b) (p c) → False := by
    intro a b c hab hbc hw
    have hmem : p b ∈ convexHull ℝ (p '' ({a, c} : Set (Fin n))) := by
      rw [Set.image_pair]
      exact segment_subset_convexHull (by simp) (by simp) (mem_segment_iff_wbtw.2 hw)
    have := hp {a, c} b hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h
    · exact hab h.symm
    · exact hbc h
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact key i j k hij hjk h
  · exact key j k i hjk hik.symm h
  · exact key k i j hik.symm hij h

theorem isosceles_bound {n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : ConvexIndependent ℝ p) :
    ((Finset.univ : Finset (Fin n × Fin n × Fin n)).filter (fun t => t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ dist (p t.1) (p t.2.1) = dist (p t.1) (p t.2.2))).card ≤ 2 * n * (n - 1) := by
  classical
  have hinj := hp.injective
  have hbis : ∀ j k : Fin n, j ≠ k → ∀ a b c : Fin n,
      dist (p a) (p j) = dist (p a) (p k) → dist (p b) (p j) = dist (p b) (p k) →
      dist (p c) (p j) = dist (p c) (p k) →
      Collinear ℝ ({p a, p b, p c} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro j k hjk a b c ha hb hc
    have hne : p j ≠ p k := fun h => hjk (hinj h)
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
    rw [collinear_iff_finrank_le_one]
    have hsub : ({p a, p b, p c} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
        (AffineSubspace.perpBisector (p j) (p k) : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact AffineSubspace.mem_perpBisector_iff_dist_eq.2 ha
      · exact AffineSubspace.mem_perpBisector_iff_dist_eq.2 hb
      · exact AffineSubspace.mem_perpBisector_iff_dist_eq.2 hc
    have h1 : vectorSpan ℝ ({p a, p b, p c} : Set (EuclideanSpace ℝ (Fin 2))) ≤
        (AffineSubspace.perpBisector (p j) (p k)).direction := by
      rw [AffineSubspace.direction_eq_vectorSpan]
      exact vectorSpan_mono ℝ hsub
    have h2 := Submodule.finrank_mono h1
    rw [AffineSubspace.direction_perpBisector] at h2
    have h3 : Module.finrank ℝ (Submodule.span ℝ {p k -ᵥ p j})ᗮ = 1 :=
      Submodule.finrank_orthogonal_span_singleton (n := 1)
        (by rw [vsub_eq_sub]; exact sub_ne_zero.2 hne.symm)
    omega
  set T : Finset (Fin n × Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    (fun t => t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ dist (p t.1) (p t.2.1) = dist (p t.1) (p t.2.2)) with hT
  have hfib : ∀ a ∈ T.image (fun t => (t.2.1, t.2.2)),
      (T.filter (fun t => (t.2.1, t.2.2) = a)).card ≤ 2 := by
    intro a _
    by_contra hlt
    have hlt' : 2 < (T.filter (fun t => (t.2.1, t.2.2) = a)).card := not_le.1 hlt
    obtain ⟨t1, h1, t2, h2, t3, h3, h12, h13, h23⟩ := Finset.two_lt_card.1 hlt'
    simp only [Finset.mem_filter, hT, Finset.mem_univ, true_and] at h1 h2 h3
    obtain ⟨⟨hjk1, hi1j, hi1k, hd1⟩, ha1⟩ := h1
    obtain ⟨⟨hjk2, hi2j, hi2k, hd2⟩, ha2⟩ := h2
    obtain ⟨⟨hjk3, hi3j, hi3k, hd3⟩, ha3⟩ := h3
    obtain ⟨i1, j1, k1⟩ := t1
    obtain ⟨i2, j2, k2⟩ := t2
    obtain ⟨i3, j3, k3⟩ := t3
    simp only at hjk1 hi1j hi1k hd1 ha1 hjk2 hi2j hi2k hd2 ha2 hjk3 hi3j hi3k hd3 ha3
    have e2 : j2 = j1 ∧ k2 = k1 := by
      have := ha2.trans ha1.symm
      simpa [Prod.ext_iff] using this
    have e3 : j3 = j1 ∧ k3 = k1 := by
      have := ha3.trans ha1.symm
      simpa [Prod.ext_iff] using this
    rw [e2.1, e2.2] at hd2
    rw [e3.1, e3.2] at hd3
    have n12 : i1 ≠ i2 := fun h => h12 (by rw [h, e2.1, e2.2])
    have n13 : i1 ≠ i3 := fun h => h13 (by rw [h, e3.1, e3.2])
    have n23 : i2 ≠ i3 := fun h => h23 (by rw [h, e2.1, e2.2, e3.1, e3.2])
    exact convex_no_three_collinear p hp i1 i2 i3 n12 n13 n23 (hbis j1 k1 hjk1 i1 i2 i3 hd1 hd2 hd3)
  refine le_trans (Finset.card_le_mul_card_image T 2 hfib) ?_
  have himg : T.image (fun t => (t.2.1, t.2.2)) ⊆ (Finset.univ : Finset (Fin n)).offDiag := by
    intro a ha
    simp only [Finset.mem_image, hT, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨t, ⟨hjk, _⟩, rfl⟩ := ha
    simp [Finset.mem_offDiag, hjk]
  have hcard := Finset.card_le_card himg
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  have : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
  calc 2 * (T.image (fun t => (t.2.1, t.2.2))).card ≤ 2 * (n * n - n) := by omega
    _ = 2 * n * (n - 1) := by rw [← this]; ring

theorem moser_bound (n : ℕ) (hn : 3 ≤ n) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : ConvexIndependent ℝ p) : ∃ i : Fin n, n - 1 ≤ 3 * dc p i := by
  classical
  have cs : ∀ (S : Finset (Fin n)) (f : Fin n → ℝ),
      S.card ^ 2 ≤ (S.image f).card * ((S ×ˢ S).filter (fun x => f x.1 = f x.2)).card := by
    intro S f
    have h1 : ((S ×ˢ S).filter (fun x => f x.1 = f x.2)).card
        = ∑ d ∈ S.image f, (S.filter (fun a => f a = d)).card * (S.filter (fun a => f a = d)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      have : ∀ j ∈ S, (∑ k ∈ S, if f j = f k then 1 else 0) = (S.filter (fun a => f a = f j)).card := by
        intro j _
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro k _
        simp only [eq_comm]
      rw [Finset.sum_congr rfl this]
      exact Finset.sum_comp (fun d => (S.filter (fun a => f a = d)).card) f |>.trans (by simp [smul_eq_mul])
    have h2 : S.card = ∑ d ∈ S.image f, (S.filter (fun a => f a = d)).card :=
      Finset.card_eq_sum_card_image f S
    rw [h1]
    calc S.card ^ 2 = (∑ d ∈ S.image f, (S.filter (fun a => f a = d)).card) ^ 2 := by rw [← h2]
      _ ≤ (S.image f).card * ∑ d ∈ S.image f, ((S.filter (fun a => f a = d)).card) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = _ := by simp [sq]
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin n → ℕ, ∀ i, Q i = ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun x => x.1 ≠ x.2 ∧ i ≠ x.1 ∧ i ≠ x.2 ∧ dist (p i) (p x.1) = dist (p i) (p x.2))).card :=
    ⟨_, fun _ => rfl⟩
  have hsum : ((Finset.univ : Finset (Fin n × Fin n × Fin n)).filter (fun t => t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ dist (p t.1) (p t.2.1) = dist (p t.1) (p t.2.2))).card = ∑ i, Q i := by
    simp only [hQ, Finset.card_filter, Fintype.sum_prod_type]
  have hiso := isosceles_bound p hp
  have hper : ∀ i : Fin n, n - 1 ≤ 3 * dc p i ∨ 2 * (n - 1) < Q i := by
    intro i
    by_cases hd : n - 1 ≤ 3 * dc p i
    · exact Or.inl hd
    right
    have hd' : 3 * dc p i < n - 1 := not_le.1 hd
    have hSc : (Finset.univ.erase i).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have himg : ((Finset.univ.erase i).image (fun j => dist (p i) (p j))).card = dc p i := by
      have hset : {d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j)} =
          ↑((Finset.univ.erase i).image (fun j => dist (p i) (p j))) := by
        ext d
        simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
          Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, hj, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, hj, rfl⟩
      unfold dc
      rw [hset, Set.ncard_coe_finset]
    have hN : (((Finset.univ.erase i) ×ˢ (Finset.univ.erase i)).filter
        (fun x => dist (p i) (p x.1) = dist (p i) (p x.2))).card ≤ Q i + (n - 1) := by
      have hsub : (((Finset.univ.erase i) ×ˢ (Finset.univ.erase i)).filter
          (fun x => dist (p i) (p x.1) = dist (p i) (p x.2))) ⊆
          ((Finset.univ : Finset (Fin n × Fin n)).filter
            (fun x => x.1 ≠ x.2 ∧ i ≠ x.1 ∧ i ≠ x.2 ∧ dist (p i) (p x.1) = dist (p i) (p x.2))) ∪
          (Finset.univ.erase i).image (fun j => (j, j)) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_univ,
          and_true] at hx
        obtain ⟨⟨hj, hk⟩, hd⟩ := hx
        by_cases hjk : x.1 = x.2
        · apply Finset.mem_union_right
          simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨x.1, hj, Prod.ext rfl hjk⟩
        · apply Finset.mem_union_left
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hjk, fun h => hj h.symm, fun h => hk h.symm, hd⟩
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ Q i + (n - 1) := by
          rw [hQ i]
          have := Finset.card_image_le (s := Finset.univ.erase i) (f := fun j => (j, j))
          omega
    have hcs := cs (Finset.univ.erase i) (fun j => dist (p i) (p j))
    rw [hSc, himg] at hcs
    have hm : 0 < n - 1 := by omega
    by_contra hQle
    have hQle' : Q i ≤ 2 * (n - 1) := not_lt.1 hQle
    generalize n - 1 = m at *
    generalize dc p i = d at *
    nlinarith
  by_cases hex : ∃ i : Fin n, n - 1 ≤ 3 * dc p i
  · exact hex
  · exfalso
    push_neg at hex
    have hall : ∀ i : Fin n, 2 * (n - 1) + 1 ≤ Q i := by
      intro i
      rcases hper i with h | h
      · exact absurd h (not_le.2 (hex i))
      · omega
    have hge : ∑ _i : Fin n, (2 * (n - 1) + 1) ≤ ∑ i, Q i := Finset.sum_le_sum (fun i _ => hall i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hge
    rw [hsum] at hiso
    have : n * (2 * (n - 1) + 1) ≤ 2 * n * (n - 1) := le_trans hge hiso
    nlinarith

/-- OPEN: the actual content of Erdős #982. Not proved. -/
theorem half_bound (n : ℕ) (hn : 3 ≤ n) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : ConvexIndependent ℝ p) : ∃ i : Fin n, n / 2 ≤ dc p i := by
  sorry

theorem erdos982 (n : ℕ) (hn : 3 ≤ n) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hp : ConvexIndependent ℝ p) :
    ∃ i : Fin n, n / 2 ≤ {d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j)}.ncard := by
  obtain ⟨i, hi⟩ := half_bound n hn p hp
  exact ⟨i, hi⟩

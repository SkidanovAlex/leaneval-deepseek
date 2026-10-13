import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt.ZExt

open Filter
open scoped Topology

/-- Auxiliary explicit modulus: if `0 ≤ C` and `0 < r`, then `C * (2 * δ) ^ r → 0` as
`δ → 0⁺`, in the `ε`-`δ` form used in the main proof. -/
private lemma holder_delta {C r ε : ℝ} (_hC : 0 ≤ C) (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ C * (2 * δ) ^ r < ε := by
  have hcont : ContinuousAt (fun t : ℝ => C * (2 * t) ^ r) 0 := by
    have h1 : Continuous fun t : ℝ => (2 * t) ^ r :=
      (Real.continuous_rpow_const (le_of_lt hr)).comp
        ((continuous_const : Continuous fun _ : ℝ => (2 : ℝ)).mul continuous_id)
    exact h1.continuousAt.const_mul C
  have hf0 : C * (2 * 0) ^ r = 0 := by
    rw [mul_zero, Real.zero_rpow (ne_of_gt hr), mul_zero]
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨δ / 2, by linarith, ?_⟩
  have hx : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
    linarith
  have h := hδ hx
  rw [hf0, Real.dist_eq, sub_zero] at h
  have h' : C * (2 * (δ / 2)) ^ r < ε := lt_of_le_of_lt (le_abs_self _) h
  rw [show 2 * (δ / 2) = δ from by ring] at h' ⊢
  exact h'

theorem continuous_zeroExt_of_holder {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) {φ : ℝ × ℝ → ℝ}
    (h : ∀ x ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
           ∀ y ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
        |φ x - φ y| ≤ C * (|x.1 - y.1| + |x.2 - y.2|) ^ r)
    (h0 : ∀ p ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
        (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) → φ p = 0) :
    Continuous (fun p : ℝ × ℝ =>
      if p ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) then φ p else 0) := by
  set Q : Set (ℝ × ℝ) := Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2) with hQ
  set F : ℝ × ℝ → ℝ := (fun p => if p ∈ Q then φ p else 0) with hF
  have h' : ∀ x ∈ Q, ∀ y ∈ Q, |φ x - φ y| ≤ C * (|x.1 - y.1| + |x.2 - y.2|) ^ r := h
  have h0' : ∀ p ∈ Q, (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) → φ p = 0 := h0
  have hQclosed : IsClosed Q := by rw [hQ]; exact isClosed_Ici.prod isClosed_Icc
  -- the basic Hölder bound, transported to `F`
  have hbnd : ∀ p ∈ Q, ∀ x ∈ Q, |F x - F p| ≤ C * (|x.1 - p.1| + |x.2 - p.2|) ^ r := by
    intro p hp x hx
    have hxF : F x = φ x := by rw [hF]; exact ite_eq_left hx
    have hpF : F p = φ p := by rw [hF]; exact ite_eq_left hp
    rw [hxF, hpF]
    exact h' x hx p hp
  have hcontOn : ContinuousOn F Q := by
    rw [Metric.continuousOn_iff]
    intro p hp ε hε
    obtain ⟨δ, hδ0, hδε⟩ := holder_delta hC hr hε
    refine ⟨δ, hδ0, fun x hxQ hxd => ?_⟩
    rw [Real.dist_eq]
    calc |F x - F p| ≤ C * (|x.1 - p.1| + |x.2 - p.2|) ^ r := hbnd p hp x hxQ
      _ ≤ C * (2 * dist x p) ^ r := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          refine Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hr)
          simp only [Prod.dist_eq, Real.dist_eq]
          have h1 : |x.1 - p.1| ≤ max |x.1 - p.1| |x.2 - p.2| := le_max_left _ _
          have h2 : |x.2 - p.2| ≤ max |x.1 - p.1| |x.2 - p.2| := le_max_right _ _
          linarith
      _ ≤ C * (2 * δ) ^ r := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact Real.rpow_le_rpow (by positivity) (by linarith) (le_of_lt hr)
      _ < ε := hδε
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ Q
  · -- inside the closed quadrant
    have hcwa : ContinuousWithinAt F Q p := hcontOn.continuousWithinAt hp
    rw [Metric.continuousWithinAt_iff] at hcwa
    by_cases hφp : φ p = 0
    · -- `F p = 0`: both the inside and the outside of `Q` converge to `0`
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ0, hδ⟩ := hcwa ε hε
      refine ⟨δ, hδ0, fun x hxd => ?_⟩
      by_cases hxQ : x ∈ Q
      · exact hδ hxQ hxd
      · have hFx : F x = 0 := by rw [hF]; exact ite_eq_right hxQ
        have hFp : F p = 0 := by rw [hF]; exact (ite_eq_left hp).trans hφp
        rw [hFx, hFp, dist_self]
        exact hε
    · -- `φ p ≠ 0`: then `p` is an interior point of `Q`
      have hne : ¬ (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) := fun hh => hφp (h0' p hp hh)
      have hp1 : 0 < p.1 := lt_of_le_of_ne' hp.1 (fun hh => hne (Or.inl hh))
      have hp2 : 0 < p.2 := lt_of_le_of_ne' hp.2.1 (fun hh => hne (Or.inr (Or.inl hh)))
      have hp2' : p.2 < Real.pi / 2 :=
        lt_of_le_of_ne hp.2.2 (fun hh => hne (Or.inr (Or.inr hh)))
      have hpint : p ∈ interior Q := by
        rw [hQ, interior_prod_eq, interior_Ici, interior_Icc]
        exact ⟨hp1, hp2, hp2'⟩
      exact hcontOn.continuousAt
        (mem_of_superset (isOpen_interior.mem_nhds hpint) interior_subset)
  · -- outside the closed quadrant `F` vanishes identically near `p`
    have hmem : Qᶜ ∈ 𝓝 p := hQclosed.isOpen_compl.mem_nhds hp
    have heq : F =ᶠ[𝓝 p] (fun _ : ℝ × ℝ => (0 : ℝ)) :=
      eventually_of_mem hmem (fun x hx => by rw [hF]; exact ite_eq_right hx)
    exact continuousAt_const.congr heq.symm

end Work.FTS.FireFix.Clauses.PsiWt.ZExt

import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MDBasic.finite_sets

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Elementary facts

`𝓢*₁(Γ^{mix}_{x,y}(Q); 𝒯^{mix}_y(A,α))` sums `1/‖a‖` over the primitive `a` in the lattice
`Γ^{mix}_{x,y}(Q) = Λ_{ν(x)} ∩ Λ^{(Q)}_{ν(y)}` lying in the region
`𝒯^{mix}_y(A,α) ⊆ {‖a‖ ≤ A}`.  Its index set is therefore contained in the index set of
`𝓢₁(Λ_{ν(x)}; B(A)) = S1ball d n x A`, namely `{a ∈ Λ_{ν(x)} : a ≠ 0, ‖a‖ ≤ A}` (a primitive
vector is nonzero).  Since all summands `1/‖a‖ ≥ 0` are nonnegative, the finite sum over the
smaller set is at most the finite sum over the larger one. -/

/-- A primitive integer vector is nonzero. -/
private lemma sgt_isPrim_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  intro hv
  rw [IsPrim, hv] at h
  have h0 : Finset.univ.gcd (0 : ι → ℤ) = 0 := by
    rw [Finset.gcd_eq_zero_iff]; intro i _; rfl
  rw [h0] at h
  exact one_ne_zero h.symm

/-- Monotonicity of a finite `finsum` in its summand. -/
private lemma sgt_finsum_mem_mono {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ a ∈ s, f a ≤ g a) : (∑ᶠ a ∈ s, f a) ≤ ∑ᶠ a ∈ s, g a := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_le_sum fun a ha => h a (hs.mem_toFinset.mp ha)

/-- Monotonicity of a finite `finsum` in its index set, for nonnegative summands. -/
private lemma sgt_finsum_mem_le_of_subset {α : Type*} {s t : Set α} (hst : s ⊆ t)
    (ht : t.Finite) {g : α → ℝ} (hg : ∀ a, 0 ≤ g a) : (∑ᶠ a ∈ s, g a) ≤ ∑ᶠ a ∈ t, g a := by
  have hs : s.Finite := ht.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ ht]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hst) ?_
  intro a _ _
  exact hg a

/-- Sub-set/term comparison of two finite `finsum`s. -/
private lemma sgt_finsum_le_of_subset_terms {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (hst : s ⊆ t) {f g : α → ℝ} (hfg : ∀ a ∈ s, f a ≤ g a)
    (hg : ∀ a, 0 ≤ g a) : (∑ᶠ a ∈ s, f a) ≤ ∑ᶠ a ∈ t, g a :=
  le_trans (sgt_finsum_mem_mono hs hfg) (sgt_finsum_mem_le_of_subset hst ht hg)

theorem Sstar_GamMix_Tmix_le_S1ball (d n : ℕ) (x y : Fin (n + 1) → ℤ) (Q : ℕ) (A α : ℝ) :
    Sstar d n 1 (GamMix d n x y Q) (TmixSet d n y A α) ≤ S1ball d n x A := by
  classical
  rw [Sstar, S1ball]
  refine sgt_finsum_le_of_subset_terms
    ((MDBasic.finite_eNorm_le (ι := Mon d n) A).subset (fun a ha => ha.2.2.1))
    ((MDBasic.finite_eNorm_le (ι := Mon d n) A).subset (fun a ha => ha.2.2)) ?_ ?_ ?_
  · intro a ha
    exact ⟨(Submodule.mem_inf.mp ha.1).1, sgt_isPrim_ne_zero ha.2.1, ha.2.2.1⟩
  · intro a _
    rw [pow_one]
  · intro a
    exact div_nonneg zero_le_one (eNorm_nonneg a)

end Work.HP.MM2

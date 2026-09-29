import Mathlib
import Submission.Work.TMC14Core.RatRot

namespace Work.TMC14Core

/-- An open, order-connected subset of `ℝ` that is nonempty and bounded is exactly the open
interval spanned by its infimum and supremum. -/
theorem eq_Ioo_of_isOpen_ordConnected (s : Set ℝ) (hopen : IsOpen s) (hord : s.OrdConnected)
    (hne : s.Nonempty) (hbd : BddBelow s) (hba : BddAbove s) :
    s = Set.Ioo (sInf s) (sSup s) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun y hy => ?_)
  · rw [Set.mem_Ioo]
    obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hx)
    constructor
    · have hmid : (l + x) / 2 ∈ s := hsub ⟨by linarith [hlu.1], by linarith [hlu.1, hlu.2]⟩
      have hle := csInf_le hbd hmid
      linarith [hlu.1]
    · have hmid : (x + u) / 2 ∈ s := hsub ⟨by linarith [hlu.1, hlu.2], by linarith [hlu.2]⟩
      have hle := le_csSup hba hmid
      linarith [hlu.2]
  · rw [Set.mem_Ioo] at hy
    obtain ⟨x1, hx1, hx1y⟩ := (csInf_lt_iff hbd hne).mp hy.1
    obtain ⟨x2, hx2, hyx2⟩ := (lt_csSup_iff hba hne).mp hy.2
    exact hord.out hx1 hx2 ⟨le_of_lt hx1y, le_of_lt hyx2⟩

/-- The set of energies `E` lying in the window `(a,c)` and whose image `Δ E` under a continuous
map strictly monotone on `(a,c)` lies in `(α,β)` is an open interval `(u,v)`.  This is the
"preimage of an interval intersected with an interval" fact used to locate spectral gaps. -/
theorem preimage_Ioo_inter_eq_Ioo (Δ : ℝ → ℝ) (hcont : Continuous Δ) (a c α β : ℝ)
    (hmono : StrictMonoOn Δ (Set.Ioo a c)) :
    ∃ u v : ℝ, {E : ℝ | E ∈ Set.Ioo a c ∧ Δ E ∈ Set.Ioo α β} = Set.Ioo u v := by
  set S : Set ℝ := {E : ℝ | E ∈ Set.Ioo a c ∧ Δ E ∈ Set.Ioo α β} with hS
  have hSeq : S = Set.Ioo a c ∩ Δ ⁻¹' Set.Ioo α β := by
    rw [hS]; ext E; simp
  have hopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_Ioo.inter (hcont.isOpen_preimage (Set.Ioo α β) isOpen_Ioo)
  have hord : S.OrdConnected := by
    rw [hS]
    apply Set.ordConnected_of_Ioo
    intro x hx z hz hxz y hy
    rw [Set.mem_Ioo] at hy
    have hyac : y ∈ Set.Ioo a c := ⟨lt_trans hx.1.1 hy.1, lt_trans hy.2 hz.1.2⟩
    refine ⟨hyac, ?_⟩
    have h1 : Δ x < Δ y := hmono hx.1 hyac hy.1
    have h2 : Δ y < Δ z := hmono hyac hz.1 hy.2
    exact ⟨lt_trans hx.2.1 h1, lt_trans h2 hz.2.2⟩
  have hbd : BddBelow S := by
    refine ⟨a, ?_⟩
    intro x hx
    rw [hS] at hx
    exact le_of_lt hx.1.1
  have hba : BddAbove S := by
    refine ⟨c, ?_⟩
    intro x hx
    rw [hS] at hx
    exact le_of_lt hx.1.2
  by_cases hne : S.Nonempty
  · exact ⟨sInf S, sSup S, eq_Ioo_of_isOpen_ordConnected S hopen hord hne hbd hba⟩
  · refine ⟨0, 0, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.Ioo_self]

end Work.TMC14Core

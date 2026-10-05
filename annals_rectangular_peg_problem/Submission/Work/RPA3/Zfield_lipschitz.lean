import Mathlib
import Submission.Work.RPA3.follow_family_defs

/-!
# RPA3: `Zfield` is Lipschitz

`Zfield L H c τ q = (chi τ * bump c q) • Yfield L H τ q` is the cut-off tangential field: the time
cut-off `chi` is supported in `[-2,3]` and the spatial bump `bump c` is supported in the disc
`q₁² + q₂² < c`.  Hence `Zfield` is a `C¹` function with compact support, so it is Lipschitz.  This
is the form in which the global Picard–Lindelöf theorem consumes the field.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- If `chi t ≠ 0` then `t` lies in the support interval `[-2,3]`. -/
theorem chi_ne_zero_mem (t : ℝ) (h : chi t ≠ 0) : t ∈ Set.Icc (-2 : ℝ) 3 := by
  have h1 : 0 < t + 2 := by
    by_contra hc
    rw [not_lt] at hc
    apply h
    show Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t) = 0
    rw [Real.smoothTransition.zero_of_nonpos hc, zero_mul]
  have h2 : 0 < 3 - t := by
    by_contra hc
    rw [not_lt] at hc
    apply h
    show Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t) = 0
    rw [Real.smoothTransition.zero_of_nonpos hc, mul_zero]
  exact ⟨by linarith, by linarith⟩

/-- If `bump c q ≠ 0` then `q₁² + q₂² < c`, i.e. `q` lies in the open disc on which the bump is
supported. -/
theorem bump_ne_zero_sq_lt (c : ℝ) (q : ℝ × ℝ) (h : bump c q ≠ 0) :
    q.1 ^ 2 + q.2 ^ 2 < c := by
  have hpos : 0 < c - (q.1 ^ 2 + q.2 ^ 2) := by
    by_contra hc
    rw [not_lt] at hc
    apply h
    show Real.smoothTransition (c - (q.1 ^ 2 + q.2 ^ 2)) = 0
    exact Real.smoothTransition.zero_of_nonpos hc
  linarith

theorem Zfield_lipschitz (L : LagFamilyAll) (H : ℝ → PS → ℝ) (c : ℝ)
    (hYcd : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => Yfield L H z.1 z.2)) :
    ∃ K : NNReal, LipschitzWith K (fun z : ℝ × (ℝ × ℝ) => Zfield L H c z.1 z.2) := by
  set R : ℝ := Real.sqrt (max c 0) with hRdef
  have hR2 : R ^ 2 = max c 0 := Real.sq_sqrt (le_max_right c 0)
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  -- `Zfield` is `C¹` ...
  have hcd : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => Zfield L H c z.1 z.2) := by
    have hscal : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => chi z.1 * bump c z.2) := by
      have h1 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => chi z.1) :=
        chi_contDiff.comp (by fun_prop)
      have h2 : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ) => bump c z.2) :=
        (bump_contDiff c).comp (by fun_prop)
      exact h1.mul h2
    have hm : ContDiff ℝ 1
        (fun z : ℝ × (ℝ × ℝ) => (chi z.1 * bump c z.2) • Yfield L H z.1 z.2) :=
      hscal.smul hYcd
    simpa only [Zfield_apply] using hm
  -- ... and supported in the compact set `[-2,3] × ([-R,R] × [-R,R])`.
  have hsupp : Function.support (fun z : ℝ × (ℝ × ℝ) => Zfield L H c z.1 z.2)
      ⊆ Set.Icc (-2 : ℝ) 3 ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
    intro z hz
    rw [Function.mem_support] at hz
    have hne : chi z.1 * bump c z.2 ≠ 0 := by
      intro hzero
      exact hz (by rw [Zfield_apply, hzero, zero_smul])
    obtain ⟨hchi, hbump⟩ := mul_ne_zero_iff.mp hne
    have hmem_chi : z.1 ∈ Set.Icc (-2 : ℝ) 3 := chi_ne_zero_mem z.1 hchi
    have hsq := bump_ne_zero_sq_lt c z.2 hbump
    have hlt1 : |z.2.1| < |R| := by
      rw [← sq_lt_sq, hR2]
      exact lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg _))
        (lt_of_lt_of_le hsq (le_max_left c 0))
    have hlt1' : |z.2.1| < R := by rwa [abs_of_nonneg hRnn] at hlt1
    have hlt2 : |z.2.2| < |R| := by
      rw [← sq_lt_sq, hR2]
      exact lt_of_le_of_lt (le_add_of_nonneg_left (sq_nonneg _))
        (lt_of_lt_of_le hsq (le_max_left c 0))
    have hlt2' : |z.2.2| < R := by rwa [abs_of_nonneg hRnn] at hlt2
    refine Set.mem_prod.mpr ⟨hmem_chi, Set.mem_prod.mpr ⟨?_, ?_⟩⟩
    · exact Set.mem_Icc.mpr
        ⟨by linarith [(abs_lt.mp hlt1').1], by linarith [(abs_lt.mp hlt1').2]⟩
    · exact Set.mem_Icc.mpr
        ⟨by linarith [(abs_lt.mp hlt2').1], by linarith [(abs_lt.mp hlt2').2]⟩
  have hKc : IsCompact (Set.Icc (-2 : ℝ) 3 ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcomp : HasCompactSupport (fun z : ℝ × (ℝ × ℝ) => Zfield L H c z.1 z.2) :=
    HasCompactSupport.of_support_subset_isCompact hKc hsupp
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp hcd one_ne_zero
  exact ⟨C, hC⟩

end Work.RPA3

import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusPartitionDefs
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSmooth_of_dilate

namespace Work.BourgainPlan.Maximal

/-- The complex lift of `annAtom`, i.e. the fixed symbol whose dyadic dilates are the partition
atoms `annAtomC m`. -/
noncomputable def annAtomLift (x : ℝ) : ℂ := ((annAtom x : ℝ) : ℂ)

@[simp]
lemma annAtomLift_apply (x : ℝ) : annAtomLift x = ((annAtom x : ℝ) : ℂ) := rfl

lemma annAtomLift_ne_zero_iff {x : ℝ} : annAtomLift x ≠ 0 ↔ annAtom x ≠ 0 := by
  simp [annAtomLift, Complex.ofReal_eq_zero]

/-- `annAtomC m` is the dyadic dilate of the fixed symbol `annAtomLift`. -/
lemma annAtomC_eq_dilate :
    annAtomC = fun m ξ => annAtomLift ((2 : ℝ) ^ m * ξ) := by
  funext m ξ
  simp [annAtomC, annAtomZ, annAtomLift]

/-- **Boundedness of the derivatives of the lifted atom.**  The `k`-th derivative of the complex
lift of `annAtom` is continuous (because `annAtom` is `C^∞`) and is supported in the compact
`tsupport annAtom ⊆ [-3/2,3/2]`, hence bounded.  This is the only input to
`annulusSymbolSmooth_of_dilate` which is not already available in `annulusPartitionDefs`. -/
lemma exists_bound_iteratedDeriv_annAtomLift (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖iteratedDeriv k annAtomLift ξ‖ ≤ C := by
  -- the support of the lift is contained in the fixed compact interval `[-3/2, 3/2]`
  have hsupp_sub : Function.support annAtomLift ⊆ Set.Icc (-(3/2)) (3/2) := by
    intro x hx
    have hx' : annAtom x ≠ 0 := by
      intro h; exact hx (by simp [annAtomLift, h])
    obtain ⟨-, h2⟩ := annAtom_support hx'
    obtain ⟨h1, h2'⟩ := abs_lt.mp h2
    exact ⟨le_of_lt h1, le_of_lt h2'⟩
  have htsupp_sub : tsupport annAtomLift ⊆ Set.Icc (-(3/2)) (3/2) :=
    closure_minimal hsupp_sub isClosed_Icc
  have hcs : HasCompactSupport annAtomLift :=
    (isCompact_Icc : IsCompact (Set.Icc (-((3 : ℝ) / 2)) (3 / 2))).of_isClosed_subset
      (isClosed_tsupport _) htsupp_sub
  -- every iterated derivative is supported inside the `tsupport` of the lift
  have hiter : ∀ n : ℕ, tsupport (iteratedDeriv n annAtomLift) ⊆ tsupport annAtomLift := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih
  have hcsc : HasCompactSupport (iteratedDeriv k annAtomLift) :=
    hcs.mono' (subset_closure.trans (hiter k))
  have hcont : Continuous (iteratedDeriv k annAtomLift) :=
    ContDiff.continuous_iteratedDeriv' k
      (Complex.ofRealCLM.contDiff.comp (annAtom_contDiff (n := (k : ℕ∞))))
  obtain ⟨C, hC⟩ := hcsc.exists_bound_of_continuous hcont
  exact ⟨max C 0, le_max_right _ _, fun ξ => (hC ξ).trans (le_max_left _ _)⟩

/-- The fixed symbol `annAtomLift` vanishes off the annulus `2⁻¹ < |ξ| < 2`. -/
lemma annAtomLift_support {ξ : ℝ} (h : annAtomLift ξ ≠ 0) :
    (2 : ℝ)⁻¹ < |ξ| ∧ |ξ| < 2 := by
  obtain ⟨h1, h2⟩ := annAtom_support (annAtomLift_ne_zero_iff.mp h)
  exact ⟨by norm_num at h1 ⊢; linarith, by linarith⟩

/-- **The partition atom is an annulus symbol.**  `annAtomC` is
`Work.BourgainPlan.Maximal.AnnulusSymbolSmooth`: its members are supported in the dyadic annuli
(`annAtomC_ne_zero_iff` + `annAtomZ_support`) and its `k`-th derivatives are bounded by
`C_k · 2^{m k}`.

Route.  This is `Work.BourgainPlan.Maximal.annulusSymbolSmooth_of_dilate` applied to the complex
lift `ψ := fun x : ℝ => ((Work.BourgainPlan.Maximal.annAtom x : ℝ) : ℂ)` (indeed
`annAtomC m = fun ξ => ψ ((2:ℝ)^m * ξ)`): its support condition is `annAtom_support` (which gives
`1/2 < |x| < 3/2 ⊂ (1/2, 2)`), and its bounded-derivative condition
`∀ k, ∃ C ≥ 0, ∀ ξ, ‖iteratedDeriv k ψ ξ‖ ≤ C` is the *only* new input: prove it as a helper from
the facts that `ψ` is `C^∞` with support in `[-3/2,3/2]` (so `iteratedDeriv k ψ` is continuous with
compact support, hence bounded — use `annAtom_contDiff`, `annAtom_eq_zero_of_three_halves_le_abs`,
that the `tsupport` of the `k`-th derivative is contained in the `tsupport` of `ψ`, and that a
continuous function with compact support is bounded). -/
theorem annulusSymbolSmooth_annAtomC :
    Work.BourgainPlan.Maximal.AnnulusSymbolSmooth Work.BourgainPlan.Maximal.annAtomC := by
  rw [annAtomC_eq_dilate]
  exact annulusSymbolSmooth_of_dilate annAtomLift
    (fun ξ h => annAtomLift_support h) exists_bound_iteratedDeriv_annAtomLift

end Work.BourgainPlan.Maximal

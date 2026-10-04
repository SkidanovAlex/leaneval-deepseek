import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.BNorm_J_le
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.D.bump_smul_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/- Route: this is `Work.Diff.STE.B3.bump_expansion` (in `Diff/STE/B3/BNorm_J_le`) with the transition
`tMapFun D i j` left FIXED (no bump on the transition, hence no `[T2Space M]` needed and the
regularised map is literally the chart transition).  Proof: for each `(c,d)` apply
`Work.Diff.STE.D.bump_smul_smooth` with `K := tsupport (coeffFun D i j a b c d)` (compact by
`isCompact_tsupport_coeffFun`), `U := goodSet D i j` (open, `hopen`), `K ⊆ U` (from `hgood` and
`support_coeffFun_subset_Omega`), and the `ContDiffOn` `hsmC` (post-composed with
`Complex.ofRealCLM`); set `G c d z := φ z • ((coeffFun ... z : ℝ) : ℂ)`.  The support and compactness
statements follow from `support_coeffFun_subset_cube` / `tsupport_coeffFun_subset_closedBall`, and
the pointwise identity from `Work.Diff.STE.B3.R_Rstar_expansion_pointwise_noT2` termwise (`φ = 1` on
`tsupport (coeffFun ...)`). -/
theorem bump_expansion_fixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E))
    (hgood : closure (Work.Diff.STE.D.Omega (I := I) (M := M) D i j) ⊆
      Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
    (hopen : IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j))
    (hsmC : ∀ c d : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)) :
    ∃ (G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
      (∀ c d, ContDiff ℝ (⊤ : ℕ∞) (G c d)) ∧
      (∀ c d, Function.support (G c d) ⊆
        Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) ∧
      (∀ c d, IsCompact (tsupport (G c d))) ∧
      (∀ c d, tsupport (G c d) ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) ∧
      (∀ (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ),
        ((D.R j (D.Rstar i u) a b z : ℝ) : ℂ)
          = ∑ c, ∑ d, G c d z *
              ((u c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ)) := by
  classical
  set K : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    Set.iUnion (fun c : Fin (Module.finrank ℝ E) =>
      Set.iUnion (fun d : Fin (Module.finrank ℝ E) =>
        tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d))) with hKdef
  have hKmem : ∀ c d : Fin (Module.finrank ℝ E),
      tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) ⊆ K := by
    intro c d z hz
    rw [hKdef]
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨d, hz⟩⟩
  have hKcomp : IsCompact K := by
    rw [hKdef]
    exact isCompact_iUnion (fun c => isCompact_iUnion
      (fun d => isCompact_tsupport_coeffFun D i j a b c d))
  have hKsub : K ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j := by
    refine Set.iUnion_subset (fun c => Set.iUnion_subset (fun d => ?_))
    exact (closure_mono (support_coeffFun_subset_Omega D i j a b c d)).trans hgood
  obtain ⟨K', hK'comp, hKK', hK'U⟩ := exists_isCompact_between hKcomp hopen hKsub
  -- the bumps on the coefficients
  have hbump : ∀ c d : Fin (Module.finrank ℝ E),
      ∃ φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ ∧
        (∀ z ∈ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d), φ z = 1) ∧
        tsupport φ ⊆ interior K' ∧
        ContDiff ℝ (⊤ : ℕ∞) (fun z =>
          φ z * ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) := by
    intro c d
    refine Work.Diff.STE.D.bump_smul_smooth
      (tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d)) (interior K')
      (isCompact_tsupport_coeffFun D i j a b c d) isOpen_interior ?_
      (fun z => ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ?_
    · exact (hKmem c d).trans hKK'
    · refine (Complex.ofRealCLM.contDiff.comp_contDiffOn ?_)
      exact (hsmC c d).mono (interior_subset.trans hK'U)
  choose φ hφsm hφ1 hφsup hφsm2 using hbump
  -- the bumped coefficient equals the coefficient itself, pointwise
  have hG_eq : ∀ (c d : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      φ c d z * ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)
        = ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) := by
    intro c d z
    by_cases hcd : Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z = 0
    · rw [hcd, Complex.ofReal_zero, mul_zero]
    · have hzmem : z ∈ tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) :=
        subset_closure (Function.mem_support.mpr hcd)
      rw [hφ1 c d z hzmem, Complex.ofReal_one, one_mul]
  -- the support of the bumped coefficient is inside `interior K'`
  have hG_tsup : ∀ c d : Fin (Module.finrank ℝ E),
      tsupport (fun z => φ c d z *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ⊆
        interior K' := by
    intro c d
    have hsub : Function.support (fun z => φ c d z *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ⊆
        Function.support (φ c d) ∪
          Function.support (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) := by
      intro z hz
      have h1 : ((φ c d z : ℝ) : ℂ) ≠ 0 :=
        (mul_ne_zero_iff.mp (Function.mem_support.mp hz)).1
      exact Or.inl (Function.mem_support.mpr
        (fun h => h1 (by rw [h, Complex.ofReal_zero])))
    have h1 : tsupport (fun z => φ c d z *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ)) ⊆
        tsupport (φ c d) ∪
          tsupport (Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d) := by
      rw [tsupport, tsupport, tsupport]
      exact (closure_mono hsub).trans (le_of_eq closure_union)
    exact h1.trans (Set.union_subset (hφsup c d) ((hKmem c d).trans hKK'))
  refine ⟨fun c d z => φ c d z *
      ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro c d; exact hφsm2 c d
  · -- the support lies in the open cube
    intro c d z hz
    have hz' : φ c d z *
        ((Work.Diff.STE.D.coeffFun (I := I) (M := M) D i j a b c d z : ℝ) : ℂ) ≠ 0 := hz
    exact support_coeffFun_subset_cube D i j a b c d
      (fun h0 => hz' (by rw [hG_eq c d z, h0, Complex.ofReal_zero]))
  · -- compact support
    intro c d
    exact IsCompact.of_isClosed_subset hK'comp (isClosed_tsupport _)
      ((hG_tsup c d).trans interior_subset)
  · -- support inside `goodSet`
    intro c d
    exact (hG_tsup c d).trans (interior_subset.trans hK'U)
  · -- the pointwise identity
    intro u z
    rw [R_Rstar_expansion_pointwise_noT2 D i j a b u z]
    push_cast
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hG_eq c d z]

end Work.Diff.STE.B3

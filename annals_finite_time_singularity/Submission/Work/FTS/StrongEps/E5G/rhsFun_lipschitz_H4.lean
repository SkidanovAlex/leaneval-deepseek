import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongEps.EpsLimitDefsG
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.HQo_mixed_abs_le_on_compact
import Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The limiting right-hand side at a slice is the profile right-hand side

`rhsFun α Φs E g τ = dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ` depends on the family `g`
only through its slice `slice g τ`, and once `g` is replaced by the constant family generated
by that slice, the two definitions `Galerkin.dynLin`/`Galerkin.dynRHS` and
`StrongPersist.linPart`/`StrongPersist.rhsOf` (`= Construction.gRHS`) agree.  So the limiting
right-hand side *is* `EpsLocalPStar.profRHS` evaluated at the slice — definitionally. -/

/-- `rhsFun α Φs E g τ = profRHS α Φs E (slice g τ)`, by `rfl` (`profRHS` is the same
expression written as a function of the single profile). -/
theorem rhsFun_eq_profRHS (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (τ : ℝ) :
    Work.FTS.StrongEps.rhsFun α Φs E g τ
      = Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice g τ) := rfl

/-- `rhsFun` is Lipschitz in the slice, in the `ℋ⁴`-metric against the `ℋ⁵`-metric of the slice
difference, on the class-`C` small ball where `MuLamOK` forces `|μ| ≤ 1/2`.

This is the *limiting* (mollifier-free) counterpart of the Lipschitz gate of the projected
`ε`-scheme (`EpsLocalPStar.EpsRHSPLipX`): its content is the `ℋ⁴`-difference estimate
`EpsRLX.DeltaXnBound` for the profile right-hand side `profRHS`, transported to `rhsFun`
along the definitional identity `rhsFun_eq_profRHS` above, with the two `ℋ⁵`-sizes of the
slices dominated by their `ℋ⁶`-sizes via the given uniform `ℋ⁶`-bound `B`. -/
theorem rhsFun_lipschitz_H4 {α C₀ Ce Cs B T α₄ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα₄ : 0 < α₄) (hα₄1 : α₄ ≤ 1) (hα : α ∈ Set.Ioc (0 : ℝ) α₄)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (g₁ g₂ : Work.FTS.Galerkin.Fam),
      (∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g₁ τ) ∧
        Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g₁ τ) ∧
        Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice g₁ τ) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g₁ τ) ≤ C₀ * α ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g₁ τ) ≤ B) →
      (∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g₂ τ) ∧
        Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g₂ τ) ∧
        Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice g₂ τ) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g₂ τ) ≤ C₀ * α ^ 2 ∧
        Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g₂ τ) ≤ B) →
      ∀ τ ∈ Set.Icc (0 : ℝ) T,
        Work.Spaces.HkNorm α 4 (fun z θ => Work.FTS.StrongEps.rhsFun α Φs E g₁ τ z θ
            - Work.FTS.StrongEps.rhsFun α Φs E g₂ τ z θ)
          ≤ L * Work.Spaces.HkNorm α 5 (fun z θ =>
              Work.FTS.Galerkin.slice g₁ τ z θ - Work.FTS.Galerkin.slice g₂ τ z θ) := by
  -- `α` lies in the range of `DeltaXnBound`
  have hα1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα.1, le_trans hα.2 hα₄1⟩
  -- the `ℋ⁴`-difference estimate for the profile right-hand side
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα1 hEll hstar hml
  refine ⟨K * (1 + (1 + 2 * B) ^ 2), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 + (1 + 2 * B) ^ 2 := by positivity
    exact mul_pos hKpos h1
  · intro g₁ g₂ h₁ h₂ τ hτ
    -- the slice data at `τ`
    have hm1 : Work.Spaces.HkMem α 6 (slice g₁ τ) := (h₁ τ hτ).2.1
    have hm2 : Work.Spaces.HkMem α 6 (slice g₂ τ) := (h₂ τ hτ).2.1
    have hC1 : Work.FTS.ClassC.ClassC α (slice g₁ τ) := (h₁ τ hτ).2.2.1
    have hC2 : Work.FTS.ClassC.ClassC α (slice g₂ τ) := (h₂ τ hτ).2.2.1
    have hX1 : Work.FTS.Nonlin.Xn α (slice g₁ τ) ≤ C₀ * α ^ 2 := (h₁ τ hτ).2.2.2.1
    have hX2 : Work.FTS.Nonlin.Xn α (slice g₂ τ) ≤ C₀ * α ^ 2 := (h₂ τ hτ).2.2.2.1
    have hb1 : Work.Spaces.HkNorm α 5 (slice g₁ τ) ≤ B :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hm1)
        (h₁ τ hτ).2.2.2.2
    have hb2 : Work.Spaces.HkNorm α 5 (slice g₂ τ) ≤ B :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) hm2)
        (h₂ τ hτ).2.2.2.2
    -- the profile right-hand side difference bound
    have hbd := (hK hC1 hC2 hX1 hX2).2.2
    -- `rhsFun` agrees with `profRHS` at the slice, so the `ℋ⁴`-norms agree
    have hfun : (fun z θ => Work.FTS.StrongEps.rhsFun α Φs E g₁ τ z θ
          - Work.FTS.StrongEps.rhsFun α Φs E g₂ τ z θ)
        = fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice g₁ τ) z θ
            - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice g₂ τ) z θ := by
      funext z θ
      rw [rhsFun_eq_profRHS α Φs E g₁ τ, rhsFun_eq_profRHS α Φs E g₂ τ]
    rw [hfun]
    -- the two `ℋ⁵`-sizes are dominated by `B`
    have hZ : 0 ≤ Work.Spaces.HkNorm α 5 (fun z θ => slice g₁ τ z θ - slice g₂ τ z θ) :=
      Work.Spaces.HkNorm_nonneg α 5 _
    have hP : (1 : ℝ) + Work.Spaces.HkNorm α 5 (slice g₁ τ) + Work.Spaces.HkNorm α 5 (slice g₂ τ)
        ≤ 1 + 2 * B := by linarith
    have hP0 : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 (slice g₁ τ)
        + Work.Spaces.HkNorm α 5 (slice g₂ τ) := by
      have h1 := Work.Spaces.HkNorm_nonneg α 5 (slice g₁ τ)
      have h2 := Work.Spaces.HkNorm_nonneg α 5 (slice g₂ τ)
      linarith
    have hsq : ((1 : ℝ) + Work.Spaces.HkNorm α 5 (slice g₁ τ)
          + Work.Spaces.HkNorm α 5 (slice g₂ τ)) ^ 2 ≤ (1 + 2 * B) ^ 2 :=
      pow_le_pow_left₀ hP0 hP 2
    have hsq' : ((1 : ℝ) + Work.Spaces.HkNorm α 5 (slice g₁ τ)
          + Work.Spaces.HkNorm α 5 (slice g₂ τ)) ^ 2 ≤ 1 + (1 + 2 * B) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (1 + 2 * B) ^ 2 := sq_nonneg _
      linarith
    refine le_trans hbd ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq' hKpos.le) hZ

end Work.FTS.StrongEps.E5G

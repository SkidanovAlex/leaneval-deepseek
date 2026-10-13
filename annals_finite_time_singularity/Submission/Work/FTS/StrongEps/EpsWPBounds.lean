/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsWPBounds.lean` — the last four hypotheses of
# `epsWP_sup_le_of_classC`, discharged from the interface data

`Work.FTS.StrongEps.epsWP_sup_le_of_classC` (proved) turns sup bounds on `epsWP`'s *input
blocks* into the uniform sup bound

  `∃ B' > 0, ∀ s ∈ Icc 0 T, ∀ p ∈ K, |epsWP α ρ ε Φs E g s p.1 p.2| ≤ B'`

on a compact `K ⊆ Q0` (uniform in the fake time `s`).  Its four remaining hypotheses are the
`z`-uniform (and `s`-uniform) bounds on the four *scalar* quantities of the right-hand side:

* `L₁₂(·)(z)` of the slice — a radial field, bounded by `L12_abs_le_Xn` (behaviour in `z`) below;
* `L₁₂(Transport ·)(0)` — the transport zero mode, bounded by `Transport_L12_zero_le`
  (`StrongPersist/L3Aux`, the sharp `|L₁₂(Transport g)(0)| ≤ C‖g‖_{ℋ⁴}` estimate);
* `FK(·)(z)` for `z > 0` — bounded by `FK_abs_le_of_classC`;
* `mubar (N₀) (N)` — the two ℋ⁴-zero modes, bounded by `OpenPkg.l12zero_field` from the ℋ⁴-sizes
  produced by `ClassCRHS.HkMemXnN0` / `ClassCRHS.HkMemXnN` (the `ℋ⁴`-honesty and size of the two
  nonlinear blocks) and the smoothness of `ClassCRHS.SmoothOpenRHS`.

Everything is driven by the two interface hypotheses about the *projected* slices
(`ClassC α (slice (JfamP …) s)`, `Xn ≤ C₀α²`, `Xn6 ≤ Ce`), so this module makes the sup bound on
`epsWP` conditional only on the interface and the `hEll`/`hstar`/`hml` packages — no per-`z`
hypothesis appears.

**What is *not* here.**  The *slot-wise* version (`|mixed j i (epsWP … s) p| ≤ C` for `j + i ≤ 4`),
which is the `hwin` input of `EpsProfileLip_of_epsWP_corr` and the `hsup` input of
`EpsRHSP_slotSup_corr`, needs `HQo α 6 (epsWP … s)` plus a uniform `ℋ⁶`-size: Morrey on the open
quadrant (`HQo_mixed_abs_le_on_compact`) prices the slots `≤ 4` by the *level-6* norm.  The level-6
algebra of the right-hand side is the `StrongPersist` `H6Rows`/`H6Pair6` chapter (`L6Ctx`,
`row_muAK`, `N0pair6`, …), not the `ℋ⁴` chapter consumed here; see `NOTES_session14.md` §2 for the
precise route and the interface consequence.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.epsWP_sup_le_of_classC
import Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz
import Submission.Work.FTS.StrongEps.FK_abs_le_of_classC
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Galerkin.Inhabit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The uniform sup bound of the `L₁₂`-mode -/

/-- **A sup bound for `L₁₂(·)(z)` on the whole domain, from the `ℋ⁴`-size of the profile.**
`|L₁₂ f z| ≤ C |f|_{ℋ⁴}` for every `z ≥ 0`, with a universal `C`: the `ℋ⁴`-Lipschitz property of
`L₁₂(·)(z)` (`Work.FTS.StrongEps.L12.L12_z_lipschitz`, with `C/√(1+z) ≤ C`) applied against the
zero profile. -/
theorem L12_abs_le_Xn : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f : Fn,
    Work.FTS.VocabO.HQo α 4 f → ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hkey⟩ := Work.FTS.StrongEps.L12.L12_z_lipschitz
  refine ⟨C, hCpos, fun α hα f hf z hz => ?_⟩
  have hzero_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => (0 : ℝ)) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun _ _ : ℝ => (0 : ℝ)))
      Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  have hzero : Work.FTS.VocabO.HQo α 4 (fun _ _ : ℝ => (0 : ℝ)) :=
    ⟨hzero_sm, Work.FTS.Galerkin.Inhabit.HkMem_zeroF α 4⟩
  have hdiff : (fun z θ : ℝ => f z θ - 0) = f := by
    funext z θ; rw [sub_zero]
  have h := hkey α hα f (fun _ _ : ℝ => (0 : ℝ)) hf hzero (by rw [hdiff]; exact hf) z hz
  rw [hdiff, Work.FTS.Galerkin.L12_zero_fun z, sub_zero] at h
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hden : 0 < Real.sqrt (1 + z) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + z) := by
    have h1 : (1 : ℝ) ≤ 1 + z := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + z) := Real.sqrt_le_sqrt h1
  have hle : C / Real.sqrt (1 + z) ≤ C := by
    rw [div_le_iff₀ hden]
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Real.sqrt (1 + z) := mul_le_mul_of_nonneg_left hsqrt1 hCpos.le
  calc |Work.Construction.L12 f z| ≤ C / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α f := h
    _ ≤ C * Work.FTS.Nonlin.Xn α f := mul_le_mul_of_nonneg_right hle hX

/-! ## The four scalar bounds of `epsWP_sup_le_of_classC` -/

/-- **The four `z`-uniform (and `s`-uniform) scalar bounds of `epsWP_sup_le_of_classC`, from the
interface data.**  All four are bounded by constants depending only on `α, C₀, Ce, Cs` — not on
the family `g`, the scale `ε` or the fake time `s`. -/
theorem epsWP_hyp_bounds {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s) ≤ Ce) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz,
        |Work.Construction.L12 (slice (JfamP ρ ε g) s) z| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T,
        |Work.Coercivity.L12f (Work.Coercivity.Transport (slice (JfamP ρ ε g) s)) 0| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Construction.FK (slice (JfamP ρ ε g) s) z| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T,
        |Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftau α (JfamP ρ ε g) s)
            (slice (JfamP ρ ε g) s))
          (Work.Construction.N α (Work.Construction.Ftau α (JfamP ρ ε g) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) s))| ≤ B) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨CL, hCLpos, hCL⟩ := L12_abs_le_Xn
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  obtain ⟨CF, hCF0, hCF⟩ := Work.FTS.StrongEps.FK_abs_le_of_classC
  obtain ⟨CZ, hCZpos, hCZ⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨K0, hK0pos, hN0z⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K1, hK1pos, hN1z⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce) (Cs := Cs)
      (Φs := Φs)
  have hX0 : 0 ≤ max (C₀ * α ^ 2) 0 := le_max_right _ _
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  refine ⟨⟨CL * max (C₀ * α ^ 2) 0 + 1, by positivity, ?_⟩,
    ⟨CT * max (C₀ * α ^ 2) 0 + 1, by positivity, ?_⟩,
    ⟨CF * max Ce 0 + 1, by positivity, ?_⟩,
    ⟨CZ * (K0 + K1) + 1, by positivity, ?_⟩⟩
  · -- `L₁₂` of the slice
    intro s hs z hz
    have hCw := hC s hs
    have hf : Work.FTS.VocabO.HQo α 4 (slice (JfamP ρ ε g) s) :=
      ⟨hCw.reg, Work.FTS.OpenPkg.HkMem_mono_open hCw.reg 4 (by norm_num) hCw.mem⟩
    have h1 := hCL α hα0 _ hf z hz
    have h2 : Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ max (C₀ * α ^ 2) 0 :=
      le_trans (hb4 s hs) (le_max_left _ _)
    have h3 := mul_le_mul_of_nonneg_left h2 hCLpos.le
    have h4 : 0 ≤ CL * max (C₀ * α ^ 2) 0 := mul_nonneg hCLpos.le hX0
    linarith
  · -- `L₁₂(Transport ·)(0)` of the slice
    intro s hs
    have hCw := hC s hs
    have hm4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) s) :=
      Work.FTS.OpenPkg.HkMem_mono_open hCw.reg 4 (by norm_num) hCw.mem
    have h1 := hCT α _ hα0 hα1 hm4
    have h2 : Work.Spaces.HkNorm α 4 (slice (JfamP ρ ε g) s) ≤ max (C₀ * α ^ 2) 0 :=
      le_trans (hb4 s hs) (le_max_left _ _)
    have h3 := mul_le_mul_of_nonneg_left h2 hCTpos.le
    have h4 : 0 ≤ CT * max (C₀ * α ^ 2) 0 := mul_nonneg hCTpos.le hX0
    linarith
  · -- `FK` of the slice
    intro s hs z hz
    have h1 := hCF α (max Ce 0) hα (hC s hs)
      (le_trans (hb6 s hs) (le_max_left _ _)) z hz
    have h2 : 0 ≤ CF * max Ce 0 := mul_nonneg hCF0 hCe0
    linarith
  · -- `mubar` of the slice
    intro s hs
    set w : Fn := slice (JfamP ρ ε g) s with hw
    have hCw : Work.FTS.ClassC.ClassC α w := hC s hs
    have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 s hs
    have hBw : Work.Spaces.HkNorm α 6 w ≤ Ce := hb6 s hs
    have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hCw).1
    have hsmo := Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hCw hellw hstar
    obtain ⟨hmemN0, hbndN0⟩ := hN0z hCw hXw hBw
    obtain ⟨hmemN1, hbndN1⟩ := hN1z hCw hXw hBw hellw hstar
    -- the two blocks, in the `Ftot α w` / `Φs + E w` form of `HkMemXnN0` / `HkMemXnN`
    have hN0Q : Work.FTS.VocabO.HQo α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
      ⟨hsmo.2.2.2.1, hmemN0⟩
    have hN1Q : Work.FTS.VocabO.HQo α 4
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
      ⟨hsmo.2.2.2.2, hmemN1⟩
    have hL0 := hCZ α hα0 hα1 _ hN0Q
    have hL1 := hCZ α hα0 hα1 _ hN1Q
    -- identify the blocks of the statement with the `Ftot`/`Φs + E w` ones
    have hF : Work.Construction.Ftau α (JfamP ρ ε g) s = Work.Construction.Ftot α w := by
      funext z θ
      rw [hw]
      rfl
    have hPhi : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) s
        = fun z θ => Φs z θ + E w z θ := by
      funext z θ
      rw [hw]
      rfl
    rw [hF, hPhi]
    have hmb : Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ))
        = Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0 := rfl
    rw [hmb]
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hXn1 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    refine le_trans (abs_add_le _ _) ?_
    have hstep : |Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
          + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0|
        ≤ CZ * K0 + CZ * K1 := by
      refine add_le_add (le_trans hL0 (mul_le_mul_of_nonneg_left hbndN0 hCZpos.le))
        (le_trans hL1 (mul_le_mul_of_nonneg_left hbndN1 hCZpos.le))
    have hfin : CZ * K0 + CZ * K1 ≤ CZ * (K0 + K1) + 1 := by
      nlinarith [hCZpos.le, hK0pos.le, hK1pos.le]
    linarith

/-! ## The sup bound on `epsWP`, from the interface data alone -/

/-- **The uniform sup bound of `epsWP` on a compact, from the interface.**  This is
`epsWP_sup_le_of_classC` with its four scalar hypotheses discharged by `epsWP_hyp_bounds`. -/
theorem epsWP_sup_le_of_mem {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : ε ∈ Set.Ioc 0 1) (hT : 0 ≤ T)
    (hc1 : 1 / 10 ≤ Work.Spaces.c α) (hc2 : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s) ≤ Ce)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ s ∈ Set.Icc 0 T, ∀ z θ : ℝ, (z, θ) ∈ K →
      |epsWP α ρ ε Φs E g s z θ| ≤ B' := by
  obtain ⟨h1, h2, h3, h4⟩ := epsWP_hyp_bounds hα hEll hstar hC hb4 hb6
  exact epsWP_sup_le_of_classC hα hρ hε hT hc1 hc2 hEll hstar hml hC hb4 hb6 h1 h2 h3 h4 hK hKQ

end Work.FTS.StrongEps

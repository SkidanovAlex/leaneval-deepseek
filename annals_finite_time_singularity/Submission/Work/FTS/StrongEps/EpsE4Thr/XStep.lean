/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/XStep.lean` — the local-step chapter from an **X-ball**
# invariant (the corrected reduction)

`EpsE4Thr.E4R3.LocalStepChapter3 Ce Cs C₀ ρ` (the registered target of the E4 node,
`Submission/Work/FTS/StrongEps/EpsE4Thr.lean`) is `LocalStepP α ρ ε Φs E C₀` for every admissible
`E4Data`, every `ε ∈ (0,1]` and every `α` below a threshold.  `E4R3/LocalStepChapterOfEngine.lean`
reduces it to `E4R3.EngineResiduals`, which runs the Volterra–Picard engine at the class

  `EpsClass α ρ ε (2 C₀) M' = SmoothOpen ∧ HkMem α 6 ∧ HkNorm α 6 ≤ M' ∧ ClassC (P_z J_ε ·) ∧ Xn ≤ 2C₀α²`

with the **datum bound `M'` and the invariant bound `M'` the same number**.  That is unprovable:
the Picard slice is `h₀ + ∫₀^τ F(w_s) ds`, so its `ℋ⁶`-size is `≤ HkNorm α 6 h₀ + τ · (size of F)`
and *grows* along the iteration (`HkSq α 6 (Feps 0) > 0` in every non-degenerate instance), so no
`δ > 0` keeps `HkNorm α 6 (slice (iter … (n+1)) τ) ≤ M'` for a datum of size exactly `M'`.  The
correct invariant — the one the sibling node `EpsLocalPStar` established (`NOTES_route_crux.md`
§2′) and the one the engine's `exists_sol_of_engine_xball` runs at — is the **`X`-ball**

  `XBall α ρ ε R C₀ u = SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R ∧ ClassC α (P_z (J_ε u))
      ∧ Xn α (P_z (J_ε u)) ≤ C₀ α²`,

whose metric clause sees `h₀` separately from the increment (so the datum's size `R₀` and the ball
`R` are *different* numbers, with the room `2 R₀ + 2 (τ √L)² ≤ R`), and the `ℋ⁶`-size of the datum
enters only through the a-priori bound `EpsMem α h₀ ∧ EpsSq α h₀ ≤ R`.

This module fixes the residual bundle `XStepInvariant` of that route and proves the reduction

  `localStepChapter3_of_XStepInvariant : (∀ C₀ ≥ 2, ∃ α₀ > 0, ∀ α ∈ (0,α₀], XStepInvariant Ce Cs C₀ ρ)
      ⟹ ∃ C, ∀ C₀ ≥ C, LocalStepChapter3 Ce Cs C₀ ρ`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq
import Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriFourthLevel
import Submission.Work.FTS.StrongEps.E4R3.Chapters

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XStep

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false

/-- **The residual bundle of the local-step chapter on the `X`-ball route.**

For every `α ∈ (0,1]`, every `ε ∈ (0,1]`, every admissible `(Φs, E)` (the elliptic/star packages)
*with the class radius `2 C₀`* and every `ℋ⁶`-size bound `M'` there are a positive horizon `δ` and a
positive ball radius `R` such that, for every datum `h₀` of the class

  `SmoothOpen h₀ ∧ HkMem α 6 h₀ ∧ HkSq α 6 h₀ ≤ M' ∧ ClassC α (P_z (J_ε h₀)) ∧ Xn α (P_z (J_ε h₀)) ≤ C₀ α²`

the datum is honest (`EpsMem α h₀`) with `EpsSq α h₀ ≤ R`, every Picard iterate's slice and the
limit family's slice lie in `XBall α ρ ε R (2 C₀)`, the limit family is jointly `C¹` on the slab
`(0,∞) × (0,π/2) × [0,δ]`, and every limit slice is an `EpsDatumP`.

The two numbers `M'` (the *datum's* `ℋ⁶`-size, which is what the local step's datum hypothesis gives)
and `R` (the *invariant* `X`-ball, chosen after `M'`) are deliberately different: this is exactly the
room that the `ℋ⁶`-ball invariant `E4R3.EngineResiduals` lacks. -/
def XStepInvariant (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 → ∀ {Φs : Fn} {E : Fn → Fn},
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    MuLamOK α (2 * C₀) Φs E →
    ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, 0 < R ∧
      ∀ h₀ : Fn,
        Work.FTS.EllipticEst.SmoothOpen h₀ → Work.Spaces.HkMem α 6 h₀ →
        Work.Spaces.HkSq α 6 h₀ ≤ M' →
        Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε h₀)) →
        Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2 →
        EpsMem α h₀ ∧ EpsSq α h₀ ≤ R ∧
        (∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ)) ∧
        (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          XBall α ρ ε R (2 * C₀) (slice (limFam (Feps α ρ ε Φs E) h₀) τ)) ∧
        (ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => limFam (Feps α ρ ε Φs E) h₀ p.1 p.2.1 p.2.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ)) ∧
        (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          EpsDatumP α ρ ε (slice (limFam (Feps α ρ ε Φs E) h₀) τ))

/-- **The local step from the `X`-ball residual bundle**, at the class radius `2 C₀` (the room for
the class-`C` ball clause) and with the gates produced internally from `EpsRHSPLipX_Sq` +
`profRHS_sub_sup_le_Sq`. -/
theorem localStepP_of_XStepInvariant {α C₀ Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α (2 * C₀) Φs E) (hC₀ : 0 ≤ C₀)
    (hX : XStepInvariant Ce Cs C₀ ρ) :
    LocalStepP α ρ ε Φs E C₀ := by
  intro M' hM'
  -- the residual bundle at the datum's *squared* size
  obtain ⟨δ, hδpos, R, hRpos, hdat⟩ := hX α hα ε ⟨hε, hε1⟩ hEll hstar hml (M' ^ 2) (sq_nonneg M')
  -- the two gates, at the class radius `2 C₀`
  obtain ⟨L, hLpos, hLmem, hLlip⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
      (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hRpos.le
  obtain ⟨Cpt, hCptpos, hCpt⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml
      hRpos.le
  have hCpt0 : 0 ≤ Cpt := hCptpos.le
  -- shrink the horizon so that the engine's contraction condition `δ √L < 1` holds
  set δ' : ℝ := min δ (1 / (1 + Real.sqrt L)) with hδ'def
  have hden : 0 < 1 + Real.sqrt L := by positivity
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hδ'L : δ' * Real.sqrt L < 1 := by
    have hle : δ' ≤ 1 / (1 + Real.sqrt L) := min_le_right _ _
    have h1 : (1 / (1 + Real.sqrt L)) * Real.sqrt L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hden]
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hsL) h1
  have hIcc : Set.Icc (0 : ℝ) δ' ⊆ Set.Icc (0 : ℝ) δ := Set.Icc_subset_Icc le_rfl hδ'le
  refine ⟨δ', hδ'pos, ?_⟩
  intro h₀ hd hball h6
  have hsm : Work.FTS.EllipticEst.SmoothOpen h₀ := hd.1
  have hmem6 : Work.Spaces.HkMem α 6 h₀ := hd.2.1
  have hcl : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε h₀)) := hd.2.2
  have hXn : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2 := hball
  -- the datum's `ℋ⁶`-size in the `HkSq` normalisation
  have hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M' ^ 2 := by
    have h1 : Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M' := h6
    have h2 : Real.sqrt (Work.Spaces.HkSq α 6 h₀) ≤ M' := h1
    have h3 : Real.sqrt (Work.Spaces.HkSq α 6 h₀) ^ 2 ≤ M' ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rwa [Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 h₀)] at h3
  obtain ⟨hmem₀, hsq₀, hkeep, hlim, hreg, hdP⟩ := hdat h₀ hsm hmem6 hM6 hcl hXn
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  have hP₀ : XBall α ρ ε R (2 * C₀) h₀ :=
    ⟨hsm, hmem₀, hsq₀, hcl, le_trans hXn (mul_le_mul_of_nonneg_right (by linarith) hα2)⟩
  -- the two gates in the `Feps`-normalisation of the engine
  have hbd : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L := by
    intro u hu
    obtain ⟨hm, hb⟩ := hLmem u hu.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
    rw [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u] at hm hb
    exact ⟨hm, hb⟩
  have hlip : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ) := by
    intro u v hu hv huv
    have h := hLlip u v hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
      hv.mem hv.sq_le hv.classC hv.ball huv
    rwa [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h
  have hpt : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)) := by
    intro u v hu hv z θ hz hθ0 hθ2
    have h := hCpt hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le hu.classC hv.classC
      hu.ball hv.ball z θ hz hθ0 hθ2
    rwa [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h
  obtain ⟨h, hsol, hregP⟩ :=
    Work.FTS.EpsEngine.exists_sol_of_engine_xball (α := α) (C₀ := 2 * C₀) (R := R)
      (Ce := Ce) (Cs := Cs) (Cpt := Cpt) (L := L) (δ := δ') (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (h₀ := h₀) hα hρ hε hEll hstar hδ'pos hLpos hδ'L hCpt0 hP₀ hbd hlip hpt
      (fun n τ hτ => hkeep n τ (hIcc hτ)) (fun τ hτ => hlim τ (hIcc hτ))
      (hreg.mono fun p hp => ⟨hp.1, hp.2.1, hIcc hp.2.2⟩) (fun τ hτ => hdP τ (hIcc hτ))
  exact ⟨h, hsol, hregP⟩

/-- **The local-step chapter `E4R3.LocalStepChapter3` from the `X`-ball residual bundle.**

Above the `C₀`-threshold `2`, the chapter holds as soon as `XStepInvariant` holds below an
`α`-threshold (which, as in `localStepChapter3_of_engine`, is chosen after `C₀` so that the class
radius `2 C₀` of the engine is met by the `MuLamOK`-radius produced by
`MuLamOK_of_hEll_hstar`). -/
theorem localStepChapter3_of_XStepInvariant {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hX : ∀ C₀ : ℝ, 2 ≤ C₀ → ∃ α₀ : ℝ, 0 < α₀ ∧ α₀ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₀, XStepInvariant Ce Cs C₀ ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → E4R3.LocalStepChapter3 Ce Cs C₀ ρ := by
  refine ⟨2, fun C₀ hC₀ => ?_⟩
  have hC₀0 : 0 ≤ C₀ := le_trans (by norm_num) hC₀
  obtain ⟨α₀, hα₀0, hα₀1, hres⟩ := hX C₀ hC₀
  obtain ⟨α₁, hα₁0, hml'⟩ :=
    MuLamOK_of_hEll_hstar (Ce := Ce) (Cs := Cs) (K := 2 * C₀) (by linarith)
  refine ⟨min α₀ α₁, lt_min hα₀0 hα₁0, le_trans (min_le_left _ _) hα₀1, ?_⟩
  intro α hα K Φs E g₀ hdata ε hε
  have hα0 : α ∈ Set.Ioc 0 α₀ := ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩
  have hα1 : α ∈ Set.Ioc 0 α₁ := ⟨hα.1, le_trans hα.2 (min_le_right _ _)⟩
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) hα₀1)⟩
  have hEll := hdata.2.2.1
  have hstar := hdata.2.2.2.1
  have hml : MuLamOK α (2 * C₀) Φs E := hml' α hα1 hEll hstar
  exact localStepP_of_XStepInvariant (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
    (E := E) (ε := ε) hαIoc hρ hε.1 hε.2 hEll hstar hml hC₀0 (hres α hα0)

end Work.FTS.StrongEps.EpsE4Thr.XStep

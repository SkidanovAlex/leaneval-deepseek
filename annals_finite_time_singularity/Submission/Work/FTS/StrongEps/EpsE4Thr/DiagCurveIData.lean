/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/DiagCurveIData.lean` — the level-four `hdata` from the
# single-slot producer

`EnergyDeriv_IP4_of_DiagCurveI` (the `hderiv` of `apriori_fourth_of_barrier`) consumes, for every
slot `(j,i)` with `j + i ≤ 3`, four `DiagCurveI` bundles:

  `rhoEta` on the slot `mixed j i`, `rhoW` on `mixed j i`,
  `rhoEta` on `D_z (mixed j i)`, `rhoGam α` on `D_θ (mixed j i)`,

for the family `x s = slice (JfamP ρ ε g) s` and the derivative family
`ẋ σ = Pz (J_ε (epsRHSP α ρ ε Φs E g σ))`.

This module assembles those four from the *single-slot* producer `DiagCurveI_JfamP`, whose weight is
the one-parameter family `ρ_c = w²σ^c`:

* `rhoEta = w²σ^{-η}` and `rhoGam α = w²σ^{-γ(α)}` are definitional instances;
* `rhoW = w²` is obtained by `DiagCurveIRho.DiagCurveI_congr_rhoW` (`Real.rpow_zero`);
* the `D_z`-slot is the definitional index shift `D_z ∘ mixed j i = mixed (j+1) i`
  (`DzIter_succ` is `rfl`);
* the `D_θ`-slot needs the commutation `D_θ (mixed j i F) = mixed j (i+1) F` on the open quadrant
  (`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen`, the non-analytic
  analogue of the `SmoothNbhd` version in `Spaces/mixed_comm.lean` — the latter is analyticity and
  unusable), followed by `DiagCurveI_congr` (the *horizon-restricted* version: the families are only
  known on `Icc 0 T`).

**The exponent bookkeeping matters, and is why this is not a one-liner.**  The domination
`w²σ^c (D_z^jD_θ^i g)² ≤ HkIntegrand` needs `c ≥ -η` for a pure `D_z`-slot (`i = 0`) but only
`c ≥ -γ(α)` for a mixed slot (`i ≥ 1`); since `-γ(α) < -η`, the `rhoGam α = w²σ^{-γ(α)}` bundle —
whose slot is `D_θ (mixed j i)`, of `D_θ`-order `i + 1 ≥ 1` — is *outside* the reach of the
original `c ≥ -η` formulation.  `DiagCurveI_JfamP` therefore now carries the two conditions
separately (`hc : -γ(α) ≤ c`, `hcη : b = 0 → -η ≤ c`) and branches internally, using
`SlotHkGen.slot_L2_uniform_le_mixed` / `SlotHkGen.integrable_cross_slot_rpow_mixed` in the mixed
case.  The `rhoEta`/`rhoW`/`D_z`-slots satisfy both conditions with `c = -η` or `c = 0`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveI_JfamP
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIRho
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveI_congr
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The four `DiagCurveI` bundles of one slot of the level-four energy**, from the single-slot
producer `DiagCurveI_JfamP`. -/
theorem DiagCurveI_data_of_JfamP {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ} {j i : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hreg : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad))
    (hregR : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) =>
      epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad))
    (hmem0 : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice g s))
    (hmem0R : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsRHSP α ρ ε Φs E g s))
    (hbdU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |epsRHSP α ρ ε Φs E g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hsliceU : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |slice g s (Work.FTS.StrongEps.zShift r p.1)
          (Work.FTS.StrongEps.thShift θ' p.2)| ≤ C)
    (hdom : ∃ G : ℝ → ℝ, IntegrableOn G (Set.Ioi 0) ∧
      ∀ r ∈ Set.Ioi 0, ∀ s ∈ Set.Icc 0 T,
        |Work.FM.L12dens Work.Spaces.K
          (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g s)) r| ≤ G r)
    (hbdJepsAll : ∀ a b : ℕ, a + b ≤ 4 → ∀ (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ ε → ∀ s ∈ Set.Icc 0 T,
        |Work.Spaces.mixed a b (epsRHSP α ρ ε Φs E g s)
          (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| ≤ C)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 4
      (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ))) ≤ R)
    (hcontUAll : ∀ a b : ℕ, a + b ≤ 4 → ∀ c : ℝ, -(Work.Spaces.gam α) ≤ c →
      Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (Work.Spaces.mixed a b (Pz (Work.FTS.StrongEps.Jeps ρ ε
            (epsRHSP α ρ ε Φs E g σ))) p.1 p.2
          - Work.Spaces.mixed a b (Pz (Work.FTS.StrongEps.Jeps ρ ε
            (epsRHSP α ρ ε Φs E g τ))) p.1 p.2) ^ 2
          * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c) ∂mup) (nhds τ) (nhds 0))
    (hji : j + i ≤ 3) :
    DiagCurveI Work.FTS.StrongPersist.rhoEta
        (fun s => Work.Spaces.mixed j i (slice (JfamP ρ ε g) s))
        (fun σ => Work.Spaces.mixed j i
          (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ)))) τ T ∧
    DiagCurveI Work.FTS.StrongPersist.rhoW
        (fun s => Work.Spaces.mixed j i (slice (JfamP ρ ε g) s))
        (fun σ => Work.Spaces.mixed j i
          (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ)))) τ T ∧
    DiagCurveI Work.FTS.StrongPersist.rhoEta
        (fun s => Work.Spaces.Dz (Work.Spaces.mixed j i (slice (JfamP ρ ε g) s)))
        (fun σ => Work.Spaces.Dz (Work.Spaces.mixed j i
          (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ))))) τ T ∧
    DiagCurveI (Work.FTS.StrongPersist.rhoGam α)
        (fun s => Work.Spaces.Dth (Work.Spaces.mixed j i (slice (JfamP ρ ε g) s)))
        (fun σ => Work.Spaces.Dth (Work.Spaces.mixed j i
          (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ))))) τ T := by
  have hηγ : -(Work.Spaces.gam α) ≤ -(Work.Spaces.eta) := by
    have h1 : (1 : ℝ) < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    have h2 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
    linarith
  -- the single-slot producer, in the shape of a `∀ a b c`-family
  have hbase : ∀ (a b : ℕ) (c : ℝ), a + b ≤ 4 → -(Work.Spaces.gam α) ≤ c →
      (b = 0 → -(Work.Spaces.eta) ≤ c) →
      DiagCurveI (fun z θ : ℝ => Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ c)
        (fun s => Work.Spaces.mixed a b (slice (JfamP ρ ε g) s))
        (fun σ => Work.Spaces.mixed a b
          (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ)))) τ T :=
    fun a b c hab hc hcη => DiagCurveI_JfamP (ρ := ρ) (α := α) (T := T) (ε := ε) (c := c)
      (Φs := Φs) (E := E) (g₀ := g₀) (g := g) (τ := τ) (a := a) (b := b)
      hρ hα hα1 hε hab hc hcη hτIoo hsol hreg hregR hmem0 hmem0R hbdU hsliceU hdom
      (hbdJepsAll a b hab) hR (hcontUAll a b hab c hc)
  -- the `D_θ`/`mixed` commutation on the open quadrant
  have hsm : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0 :=
    fun s hs n => smoothOn_slice_of_joint_smooth hs (hreg n)
  have hsmR : ∀ s ∈ Set.Icc 0 T, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (epsRHSP α ρ ε Φs E g s)) Work.FTS.EllipticEst.Q0 :=
    fun s hs n => smoothOn_slice_of_joint_smooth
      (g := fun z θ σ => epsRHSP α ρ ε Φs E g σ z θ) hs (hregR n)
  have hsmx : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ ε g) s) :=
    fun s hs => Work.FTS.StrongEps.EpsSqTools.LinAux.smoothOpen_Pz
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsm s hs))
  have hsmd : ∀ σ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen
      (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ))) :=
    fun σ hσ => Work.FTS.StrongEps.EpsSqTools.LinAux.smoothOpen_Pz
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε (hsmR σ hσ))
  have hshift : ∀ (F : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0) →
      ∀ p ∈ Work.FTS.EllipticEst.Q0,
        Work.Spaces.Dth (Work.Spaces.mixed j i F) p.1 p.2
          = Work.Spaces.mixed j (i + 1) F p.1 p.2 := by
    intro F hF p hp
    have hsmF : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter i F) :=
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr hF).DthIter i
    exact (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmF) (j := j) (i := 1)) hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hbase j i (-(Work.Spaces.eta)) (by omega) hηγ (fun _ => le_rfl)
  · refine DiagCurveI_congr_rhoW (hbase j i 0 (by omega) ?_ ?_)
    · have h1 : (0 : ℝ) < Work.Spaces.gam α := Work.Spaces.gam_pos hα
      linarith
    · intro _
      have h1 : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
      linarith
  · exact hbase (j + 1) i (-(Work.Spaces.eta)) (by omega) hηγ (fun _ => le_rfl)
  · refine DiagCurveI_congr (hbase j (i + 1) (-(Work.Spaces.gam α)) (by omega) le_rfl
      (fun hb => absurd hb (by omega))) hτIoo ?_ ?_
    · intro s hs p hp
      exact (hshift (slice (JfamP ρ ε g) s)
        (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmx s hs) n) p hp).symm
    · intro σ hσ p hp
      exact (hshift (Pz (Work.FTS.StrongEps.Jeps ρ ε (epsRHSP α ρ ε Φs E g σ)))
        (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmd σ hσ) n) p hp).symm

end Work.FTS.StrongEps.EpsE4Thr

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.aestronglyMeasurable_L12dens
import Submission.Work.FTS.StrongEps.E5Aux.dens_tendsto_of_slot_tendsto
import Submission.Work.FTS.StrongEps.L12_tendsto_of_dominated
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe
import Submission.Work.FTS.StrongEps.E5Aux2.continuousOn_uncurry_transport
import Submission.Work.FTS.StrongEps.E5Aux2.l12dens_transport_tendsto_at
import Submission.Work.FTS.StrongEps.E5Aux2.L12dens_transport_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-zero-mode convergence of the transport block

`Work.Coercivity.Transport f = 3 D_θ f/(1+z)`, and the paper's `L₁₂`-zero-mode of the
transport block of the right-hand side is the *radial* functional
`L₁₂(Transport f)(0) = ∫_0^∞ L12dens K (Transport f)(z) dz`.

This module proves that `L₁₂(Transport (P₀ J_ε G_n)(s))(0) → L₁₂(Transport g(s))(0)` for the
approximating sequence of the `E5` extraction, by **dominated convergence in `z`**
(`L12_tendsto_of_dominated` with the measure `volume.restrict (Ioi 0)`):

* the pointwise convergence of the density at every `z > 0` is
  `l12dens_transport_tendsto_at` (a `θ`-DCT, fed by the slot convergence
  `mixed_JfamP_tendsto` at `(j,i) = (0,1)`);
* the domination `|L12dens K (Transport f_n) z| ≤ 6 Maj z / z` is
  `L12dens_transport_abs_le`, fed by the `SlotMaj 1` clause of `EpsDecay`; the majorant
  `z ↦ Maj z/z` is integrable by hypothesis (`hMajint`);
* the a.e. strong measurability of the densities comes from a.e. strong measurability of the
  uncurried `Transport`-profiles, which is joint continuity on the open quadrant
  (`MuHGlue.aesm_L12dens_of_contOn`), which in turn is
  `continuousOn_uncurry_transport` applied to the `SmoothOpen` clause of `ClassC`.
-/

namespace Work.FTS.StrongEps.E5Aux2

open MeasureTheory Set Filter

theorem l12Transport_JfamP_tendsto {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Work.Coercivity.L12f
      (Work.Coercivity.Transport (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice g s)) 0)) := by
  -- **(0)** Joint continuity on the open quadrant of the approximating transport profiles,
  -- from the `SmoothOpen` clause of the class `ClassC`.
  have hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (Work.Coercivity.Transport
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)))
      Work.FTS.EllipticEst.Q0 :=
    fun n => continuousOn_uncurry_transport ((hC n).reg)
  -- **(1)** A.e. strong measurability of every density `z ↦ L12dens K (Transport f_n) z`.
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun z => Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    fun n => aesm_L12dens_of_contOn (hcont n)
  -- **(2)** Pointwise convergence of the density at every `z > 0` (`θ`-DCT), hence a.e.
  have hconvae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z)
      Filter.atTop (nhds (Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice g s)) z)) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro z hz
    exact l12dens_transport_tendsto_at hρ hε hε0 hsm hconv hcont hDec hl12 hz
  -- **(3)** Domination by the integrable majorant `6 Maj z / z`, uniformly in `n`.
  have hbdd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), ∀ n : ℕ,
      ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z‖
      ≤ 6 * Maj z / z := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro z hz n
    rw [Real.norm_eq_abs]
    exact L12dens_transport_abs_le (fun r => (hDec n).1 r)
      (fun r hr θ j i hji => (hDec n).2.2.2.1 r hr θ j i hji) hz
  -- **(4)** The majorant is integrable, by hypothesis (`Maj z / z ∈ L¹(0,∞)`).
  have hM : MeasureTheory.Integrable (fun z : ℝ => 6 * Maj z / z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (MeasureTheory.Integrable.const_mul hMajint 6).congr
      (Filter.Eventually.of_forall (fun z => by ring))
  -- **(5)** Dominated convergence in `z`.
  have h := Work.FTS.StrongEps.L12_tendsto_of_dominated (ρ := (0 : ℝ))
    (f := fun n => Work.Coercivity.Transport
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (g := Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s))
    (M := fun z => 6 * Maj z / z) hmeas hconvae hbdd hM
  simpa only [Work.Coercivity.L12f, Work.Construction.L12] using h

end Work.FTS.StrongEps.E5Aux2

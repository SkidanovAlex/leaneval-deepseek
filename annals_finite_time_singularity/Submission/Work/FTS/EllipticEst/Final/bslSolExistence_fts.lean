/-
Copyright: work module for the Elgindi finite-time singularity project.

# `bslSolExistenceFts` — existence of a solution of (PolarBSL)

The target `Work.FTS.EllipticEst.bslSolExistenceFts` (Elgindi §7): for `0 < α ≤ 1` and a source
`F` with vanishing angular moment (`OrthCond`), `C^∞` on the open quadrant, square-integrable
there and decaying in `z`, there is `Ψ`, `C^∞` on the open quadrant, with `bslOp α Ψ = F` on
`Q0`, the two Dirichlet values `Ψ(z,0) = Ψ(z,π/2) = 0` (for every real `z`) and the pointwise
decay `Ψ(z,θ) → 0`.

The proof assembles two inputs, both `sorry`-free:

* `Work.FTS.H2.ModalSolR.weakSolExists_slice` — the explicit (modal) weak solution of
  `bslOp α Ψ = F` with the Dirichlet values, the decay and the a.e. `θ`-slice continuity;
* `Work.EllipticEst.InteriorRegularity.Q0.interiorSmoothQ0` (proved in
  `Submission/Work/FTS/EllipticEst/Final/InteriorSmoothQ0_fts.lean`) — interior regularity of
  the elliptic operator: a weak solution with a `C^∞` source agrees a.e. on `Q0` with a `C^∞`
  function.

The remaining steps are formal:

* the fundamental lemma of the calculus of variations
  (`Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth`) upgrades the weak identity of the
  smooth representative to the pointwise equation;
* `Work.FTS.H2.PhiStarE5.smoothRep_decay` transfers the pointwise decay of the weak solution to
  its smooth representative (a.e.-equality plus the a.e.-slice continuity);
* redefining the representative off `Q0`, using the locality of `bslOp`
  (`Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq`), gives the two Dirichlet values.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.exists_bslSol_fts
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.DivSinHardy
import Submission.Work.FTS.H2.ModalSolR.weakSolExists_slice
import Submission.Work.FTS.EllipticEst.Final.InteriorSmoothQ0_fts
import Submission.Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth
import Submission.Work.FTS.H2.PhiStarE5.Decay
import Submission.Work.FTS.H2.PhiStarE5.Locality

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Final

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
noncomputable section

/-- **The existence of a solution of (PolarBSL)** in the paper's source class, in the form the
chapter consumes. -/
theorem bslSolExistence_fts : Work.FTS.EllipticEst.bslSolExistenceFts := by
  intro α F hα hα1 horth hsm hL2 hdec
  -- the explicit weak solution
  obtain ⟨Ψ, hΨli, hΨweak, hΨ0, hΨ1, hΨdec, hΨslice⟩ :=
    Work.FTS.H2.ModalSolR.weakSolExists_slice hα hα1 horth hsm hL2 hdec
  -- its smooth representative
  obtain ⟨Φ, hΦsm, hΦae⟩ :=
    Work.EllipticEst.InteriorRegularity.Q0.interiorSmoothQ0_fts hα hsm hΨli hΨweak
  -- the two functions agree a.e.
  have hae : (fun p : ℝ × ℝ => Φ p.1 p.2)
      =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0]
        (fun p : ℝ × ℝ => Ψ p.1 p.2) := hΦae.symm
  -- the pointwise equation for the smooth representative
  have hΦeq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = F z θ := by
    refine Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth hα hΦsm hsm ?_
    intro φ hφ hcφ hsub
    rw [← hΨweak φ hφ hcφ hsub]
    refine MeasureTheory.setIntegral_congr_ae
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet ?_
    rw [← MeasureTheory.ae_restrict_iff'
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
    refine hae.mono (fun p hp => ?_)
    show Φ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
      = Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    rw [show Φ p.1 p.2 = Ψ p.1 p.2 from hp]
  -- the decay of the smooth representative
  have hΦdec : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Tendsto (fun z => Φ z θ) atTop (nhds 0) :=
    Work.FTS.H2.PhiStarE5.smoothRep_decay hΦsm hae hΨslice hΨdec
  -- redefine off the open quadrant to force the two Dirichlet values
  refine ⟨fun z θ => if θ ∈ Set.Ioo 0 (Real.pi / 2) then Φ z θ else 0, ?_, ?_⟩
  · -- `C^∞` on the open quadrant (agreement with `Φ` on `Q0`)
    refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
    refine (Work.FTS.EllipticEst.SmoothOpen.forall hΦsm n).congr (fun p hp => ?_)
    obtain ⟨_, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (if p.2 ∈ Set.Ioo 0 (Real.pi / 2) then Φ p.1 p.2 else 0) = Φ p.1 p.2
    rw [if_pos ⟨h1, h2⟩]
  · -- the Dirichlet values, the equation and the decay
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ hθ0 hθ2
      have hev : ∀ᶠ q in 𝓝 (z, θ),
          (if q.2 ∈ Set.Ioo 0 (Real.pi / 2) then Φ q.1 q.2 else 0) = Φ q.1 q.2 := by
        have hnb : ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) ∈ 𝓝 (z, θ) :=
          (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ0, hθ2⟩
        exact Filter.mem_of_superset hnb (fun q hq => if_pos hq.2)
      rw [Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq α hev,
        hΦeq z hz θ hθ0 hθ2]
    · intro z
      exact if_neg (by simp)
    · intro z
      exact if_neg (by simp [Real.pi_pos])
    · intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h | h
      · -- `θ = 0`
        subst h
        have hz : (fun z : ℝ => (if (0 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) then Φ z 0 else 0))
            = fun _ => 0 := by
          funext z
          exact if_neg (by simp)
        rw [hz]
        exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · -- `θ = π/2`
          subst h2
          have hz : (fun z : ℝ =>
              (if Real.pi / 2 ∈ Set.Ioo 0 (Real.pi / 2) then Φ z (Real.pi / 2) else 0))
              = fun _ => 0 := by
            funext z
            exact if_neg (by simp)
          rw [hz]
          exact tendsto_const_nhds
        · -- `θ ∈ (0, π/2)`: the decay of `Φ`
          have hif : ∀ z : ℝ,
              (if θ ∈ Set.Ioo 0 (Real.pi / 2) then Φ z θ else 0) = Φ z θ :=
            fun z => if_pos ⟨h, h2⟩
          exact Tendsto.congr' (Eventually.of_forall (fun z => (hif z).symm))
            (hΦdec θ ⟨h, h2⟩)

end

end Work.FTS.EllipticEst.Final

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false

/-! ## Almost-everywhere strong measurability of `T1Hard` in the interior class

`Work.FTS.H2.T1HardAesm` proves this for `Work.Spaces.SmoothNbhd` data (analyticity on a
neighbourhood of the closed quadrant).  The localisation chapter works instead with genuine
`C^∞` on the open quadrant, `Work.FTS.LocData.SmoothQuad` (`ContDiffOn ℝ smoothOrder`), which a
cut-off can satisfy.  The proof is the same one: every factor of

`T1Hard α f g z θ = f z θ · w(z)² · ( D_θ(D_z^4 g) · D_z^4 g · sin(2θ)^{-η}
  + (∑_{(j,i)} D_θ(D_z^jD_θ^i g) · D_z^jD_θ^i g) · sin(2θ)^{-γ} )`

is continuous on the open quadrant `(0,∞) × (0,π/2)`: `SmoothQuad` gives `C^∞`-continuity of
`f`, of `g` and of all its `D`-derivatives on the larger set `quadU = (-1,∞) × (0,π/2)`,
`w` is continuous off the axis `z = 0`, and `sin(2θ)^{-p}` is continuous where `sin(2θ) > 0`.
Since the product measure `(volume.restrict Iz).prod (volume.restrict Iθ)` is the planar
Lebesgue measure restricted to the quadrant up to a null set, continuity there gives
`AEStronglyMeasurable`. -/

/-- The open quadrant `(0,∞) × (0,π/2)`, on which all the factors of `T1Hard` are continuous. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma mem_Qd {p : ℝ × ℝ} : p ∈ Qd ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 := by
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

private lemma Qd_subset_quadU : Qd ⊆ Work.Spaces.quadU := by
  intro p hp
  rw [mem_Qd] at hp
  simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩

private lemma sin_two_pos_of_mem_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The individual factors -/

/-- Every `SmoothQuad` function is continuous on the open quadrant. -/
private lemma contOn_uncurry_of_smoothQuad {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.LocData.SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd :=
  hF.continuousOn.mono Qd_subset_quadU

/-- The radial weight `w` is continuous on the open quadrant. -/
private lemma contOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  rw [mem_Qd] at hp
  exact pow_ne_zero 2 (ne_of_gt hp.1)

/-- Every real power of `sin(2θ)` is continuous on the open quadrant, where `sin(2θ) > 0`. -/
private lemma contOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_Qd (mem_Qd.mp hp).2)))

/-- A mixed derivative `D_z^jD_θ^i g` of a `SmoothQuad` function is continuous on the open
quadrant. -/
private lemma contOn_mixed_Qd (g : ℝ → ℝ → ℝ) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Qd :=
  contOn_uncurry_of_smoothQuad (hsmg.mixed j i)

/-- A `D_z`-iterate of a `SmoothQuad` function is continuous on the open quadrant. -/
private lemma contOn_DzIter_Qd (g : ℝ → ℝ → ℝ) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j g p.1 p.2) Qd :=
  contOn_uncurry_of_smoothQuad (hsmg.DzIter j)

/-- `D_θ` of a `SmoothQuad` function is continuous on the open quadrant. -/
private lemma contOn_Dth_Qd (G : ℝ → ℝ → ℝ) (hG : Work.FTS.LocData.SmoothQuad G) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth G p.1 p.2) Qd :=
  ((Work.FTS.LocData.contDiffOn_Dth Work.FTS.LocData.isOpen_quadU hG).continuousOn).mono
    Qd_subset_quadU

/-- `D_θ` of a mixed derivative of a `SmoothQuad` function is continuous on the open
quadrant. -/
private lemma contOn_Dth_mixed_Qd (g : ℝ → ℝ → ℝ) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.mixed j i g) p.1 p.2) Qd :=
  contOn_Dth_Qd _ (hsmg.mixed j i)

/-! ## Joint continuity of `T1Hard` on the open quadrant -/

private lemma contOn_T1Hard (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.T1Hard α f g p.1 p.2) Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Qd := contOn_uncurry_of_smoothQuad hsmf
  have hD4 : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.DzIter 4 g) p.1 p.2) Qd :=
    contOn_Dth_Qd _ (hsmg.DzIter 4)
  have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 4 g p.1 p.2) Qd :=
    contOn_DzIter_Qd g hsmg 4
  have hsinη : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)) Qd :=
    contOn_sinpow_Qd (-Work.Spaces.eta)
  have hsinγ : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.gam α)) Qd :=
    contOn_sinpow_Qd (-Work.Spaces.gam α)
  have hB1 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2
        * Work.Spaces.mixed 3 1 g p.1 p.2) Qd :=
    (contOn_Dth_mixed_Qd g hsmg 3 1).mul (contOn_mixed_Qd g hsmg 3 1)
  have hB2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2
        * Work.Spaces.mixed 2 2 g p.1 p.2) Qd :=
    (contOn_Dth_mixed_Qd g hsmg 2 2).mul (contOn_mixed_Qd g hsmg 2 2)
  have hB3 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2
        * Work.Spaces.mixed 1 3 g p.1 p.2) Qd :=
    (contOn_Dth_mixed_Qd g hsmg 1 3).mul (contOn_mixed_Qd g hsmg 1 3)
  have hB4 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2
        * Work.Spaces.mixed 0 4 g p.1 p.2) Qd :=
    (contOn_Dth_mixed_Qd g hsmg 0 4).mul (contOn_mixed_Qd g hsmg 0 4)
  have hB : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2 * Work.Spaces.mixed 3 1 g p.1 p.2
        + Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2 * Work.Spaces.mixed 2 2 g p.1 p.2
        + Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2 * Work.Spaces.mixed 1 3 g p.1 p.2
        + Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2
          * Work.Spaces.mixed 0 4 g p.1 p.2)) Qd :=
    ((hB1.add hB2).add hB3).add hB4
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      f p.1 p.2 * (Work.Spaces.w p.1) ^ 2 *
        (Work.Spaces.Dth (Work.Spaces.DzIter 4 g) p.1 p.2 * Work.Spaces.DzIter 4 g p.1 p.2
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta)
          + (Work.Spaces.Dth (Work.Spaces.mixed 3 1 g) p.1 p.2
              * Work.Spaces.mixed 3 1 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 2 2 g) p.1 p.2
              * Work.Spaces.mixed 2 2 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 1 3 g) p.1 p.2
              * Work.Spaces.mixed 1 3 g p.1 p.2
            + Work.Spaces.Dth (Work.Spaces.mixed 0 4 g) p.1 p.2
              * Work.Spaces.mixed 0 4 g p.1 p.2)
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.gam α))) Qd :=
    (hf.mul (contOn_w_Qd.pow 2)).mul
      (((hD4.mul h4).mul hsinη).add (hB.mul hsinγ))
  simpa only [Work.FTS.H2.T1Hard] using key

/-! ## The measurability statement -/

theorem T1HardAesmQ (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.H2.T1Hard α f g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (by simpa only [Qd] using contOn_T1Hard α f g hsmf hsmg)

end Work.H2.T1Q

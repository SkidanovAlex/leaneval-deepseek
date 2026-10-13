import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.StrongEps.E5Aux.clmPairAPI
import Submission.Work.FTS.StrongEps.E5Aux.iterSmooth
import Submission.Work.FTS.StrongEps.E5Aux.slotIdents.pz_pz_eq
import Submission.Work.FTS.StrongEps.E5Aux.slotIdents.pz_pth_eq
import Submission.Work.FTS.StrongEps.E5Aux.slotIdents.pth_pth_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The slots `D_zⁱD_θ^j` of a curried function, as functions on the quadrant -/

/-- The `(j,i)`-slot `D_z^j D_θ^i u` of `u`, as a function on `ℝ × ℝ`. -/
private def slot (j i : ℕ) (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.mixed j i u p.1 p.2

/-- The `z`-partial derivative of `u`, uncurried. -/
private def pzf (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => Work.Spaces.pz u p.1 p.2

/-- The `θ`-partial derivative of `u`, uncurried. -/
private def pthf (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => Work.Spaces.pth u p.1 p.2

/-- The first jet of `u` as a continuous linear map. -/
private def jet (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun p => clmPair (pzf u p, pthf u p)

/-- Candidate limit of `∂_z F n`, expressed through the slot `D_z F` of the limit. -/
private def limA (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => slot 1 0 f p / p.1

/-- Candidate limit of `∂_θ F n`. -/
private def limB (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => slot 0 1 f p / Real.sin (2 * p.2)

/-- Candidate limit of the first jet. -/
private def limJet (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun p => clmPair (limA f p, limB f p)

/-- Candidate limit of `∂_z ∂_z F n`. -/
private def limA1 (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (slot 2 0 f p - slot 1 0 f p) / p.1 ^ 2

/-- Candidate limit of the mixed second derivative `∂_θ ∂_z F n = ∂_z ∂_θ F n`. -/
private def limM (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => slot 1 1 f p / (p.1 * Real.sin (2 * p.2))

/-- Candidate limit of `∂_θ ∂_θ F n`. -/
private def limB1 (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (slot 0 2 f p - 2 * Real.sin (2 * p.2) * Real.cos (2 * p.2)
      * (slot 0 1 f p / Real.sin (2 * p.2))) / (Real.sin (2 * p.2)) ^ 2

/-- Candidate limit of the first jet of `∂_z F n`. -/
private def limJetA (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun p => clmPair (limA1 f p, limM f p)

/-- Candidate limit of the first jet of `∂_θ F n`. -/
private def limJetB (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
  fun p => clmPair (limM f p, limB1 f p)

/-! ## The theorem -/

theorem contDiffOn_two_of_locUnif_slots {F : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ 2 (Function.uncurry (F n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ (j i : ℕ), j + i ≤ 2 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i (F n) p.1 p.2)
        (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K) :
    ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := by
  have hQ : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz0 : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → p.1 ≠ 0 := fun p hp =>
    ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hsn0 : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hsin_cont : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  -- ### Step 1: the slots converge locally uniformly on `Q0`
  have hslot : ∀ (j i : ℕ), j + i ≤ 2 →
      TendstoLocallyUniformlyOn (fun n : ℕ => slot j i (F n)) (slot j i f) atTop
        Work.FTS.EllipticEst.Q0 := by
    intro j i hji
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hQ]
    intro K hK hKc
    exact hconv j i hji K hKc hK
  -- ### Step 2: continuity of the slots of the approximants and of the limit
  have hcontFn : ∀ n (j i : ℕ), j + i ≤ 2 →
      ContinuousOn (slot j i (F n)) Work.FTS.EllipticEst.Q0 := fun n j i hji =>
    (contDiffOn_zero_mixed (hsm n) hji).continuousOn
  have hcont : ∀ (j i : ℕ), j + i ≤ 2 →
      ContinuousOn (slot j i f) Work.FTS.EllipticEst.Q0 := fun j i hji =>
    (hslot j i hji).continuousOn (Eventually.of_forall fun n => hcontFn n j i hji).frequently
  -- ### Step 3: the level-zero approximants
  have hA : TendstoLocallyUniformlyOn (fun n : ℕ => pzf (F n)) (limA f) atTop
      Work.FTS.EllipticEst.Q0 := by
    have h := (hslot 1 0 (by norm_num)).div₀
      (tlu_const (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0)
      (hcont 1 0 (by norm_num)) continuous_fst.continuousOn (fun p hp => hpz0 p hp)
    refine h.congr fun n => ?_
    intro p hp
    have hp1 : p.1 ≠ 0 := hpz0 p hp
    show slot 1 0 (F n) p / p.1 = Work.Spaces.pz (F n) p.1 p.2
    simp only [slot, Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    field_simp
  have hB : TendstoLocallyUniformlyOn (fun n : ℕ => pthf (F n)) (limB f) atTop
      Work.FTS.EllipticEst.Q0 := by
    have h := (hslot 0 1 (by norm_num)).div₀
      (tlu_const (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0)
      (hcont 0 1 (by norm_num)) hsin_cont (fun p hp => hsn0 p hp)
    refine h.congr fun n => ?_
    intro p hp
    have hs : Real.sin (2 * p.2) ≠ 0 := hsn0 p hp
    show slot 0 1 (F n) p / Real.sin (2 * p.2) = Work.Spaces.pth (F n) p.1 p.2
    simp only [slot, Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth]
    field_simp
  have hdiffF : ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (F n)) p := fun n p hp =>
    ((hsm n).differentiableOn (n := 2) (by norm_num)).differentiableAt (hQ.mem_nhds hp)
  have hJet : TendstoLocallyUniformlyOn (fun n : ℕ => jet (F n)) (limJet f) atTop
      Work.FTS.EllipticEst.Q0 := tendstoLocallyUniformlyOn_clmPair hA hB
  have hJet' : TendstoLocallyUniformlyOn (fun n : ℕ => fderiv ℝ (Function.uncurry (F n)))
      (limJet f) atTop Work.FTS.EllipticEst.Q0 :=
    hJet.congr fun n => fun p hp => (fderiv_uncurry_eq_clmPair (hdiffF n p hp)).symm
  have hptc : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      Tendsto (fun n : ℕ => Function.uncurry (F n) p) atTop (𝓝 (Function.uncurry f p)) := by
    intro p hp
    have h := (hslot 0 0 (by norm_num)).tendsto_at hp
    exact h
  -- ### Step 4: the limit of the uncurried `F n` is differentiable with the candidate jet
  have hd0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, HasFDerivAt (Function.uncurry f) (limJet f p) p :=
    fun p hp => hasFDerivAt_of_tendstoLocallyUniformlyOn hQ hJet'
      (fun n q hq => (hdiffF n q hq).hasFDerivAt) hptc hp
  have hfd_lim : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      fderiv ℝ (Function.uncurry f) p = limJet f p := fun p hp => (hd0 p hp).fderiv
  have hdiff_f : DifferentiableOn ℝ (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    fun p hp => (hd0 p hp).differentiableAt.differentiableWithinAt
  -- ### Step 5: the level-one approximants
  have hdiffPz : ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz (F n))) p := fun n p hp =>
    ((Work.Spaces.uncurry_partial_c1 hQ (hsm n)).1.differentiableOn (by norm_num)).differentiableAt
      (hQ.mem_nhds hp)
  have hdiffPth : ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth (F n))) p := fun n p hp =>
    ((Work.Spaces.uncurry_partial_c1 hQ (hsm n)).2.differentiableOn (by norm_num)).differentiableAt
      (hQ.mem_nhds hp)
  have hA1 : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (F n)) p.1 p.2)
      (limA1 f) atTop Work.FTS.EllipticEst.Q0 := by
    have hnum := (hslot 2 0 (by norm_num)).sub (hslot 1 0 (by norm_num))
    have hcn : ContinuousOn (fun p : ℝ × ℝ => slot 2 0 f p - slot 1 0 f p)
        Work.FTS.EllipticEst.Q0 :=
      (hcont 2 0 (by norm_num)).sub (hcont 1 0 (by norm_num))
    have hcd : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0 :=
      (continuous_fst.pow 2).continuousOn
    have h := hnum.div₀ (tlu_const (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0)
      hcn hcd (fun p hp => pow_ne_zero 2 (hpz0 p hp))
    refine h.congr fun n => ?_
    intro p hp
    have hp1 : p.1 ≠ 0 := hpz0 p hp
    have hd : ContDiffAt ℝ 2 (Function.uncurry (F n)) p := (hsm n).contDiffAt (hQ.mem_nhds hp)
    show (slot 2 0 (F n) p - slot 1 0 (F n) p) / p.1 ^ 2
      = Work.Spaces.pz (Work.Spaces.pz (F n)) p.1 p.2
    simp only [slot, Work.Spaces.mixed_zero_right]
    rw [← Work.FTS.StrongEps.E5Aux.slotIdents.pz_pz_eq hd hp1]
  have hM : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz (F n)) p.1 p.2)
      (limM f) atTop Work.FTS.EllipticEst.Q0 := by
    have hcd : ContinuousOn (fun p : ℝ × ℝ => p.1 * Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 := (continuous_fst.continuousOn).mul hsin_cont
    have h := (hslot 1 1 (by norm_num)).div₀
      (tlu_const (fun p : ℝ × ℝ => p.1 * Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0)
      (hcont 1 1 (by norm_num)) hcd (fun p hp => mul_ne_zero (hpz0 p hp) (hsn0 p hp))
    refine h.congr fun n => ?_
    intro p hp
    have hp1 : p.1 ≠ 0 := hpz0 p hp
    have hs : Real.sin (2 * p.2) ≠ 0 := hsn0 p hp
    have hd : ContDiffAt ℝ 2 (Function.uncurry (F n)) p := (hsm n).contDiffAt (hQ.mem_nhds hp)
    show slot 1 1 (F n) p / (p.1 * Real.sin (2 * p.2))
      = Work.Spaces.pth (Work.Spaces.pz (F n)) p.1 p.2
    rw [← Work.Spaces.pz_pth_comm hd,
      Work.FTS.StrongEps.E5Aux.slotIdents.pz_pth_eq hd hp1 hs]
    simp only [slot]
  have hM' : TendstoLocallyUniformlyOn (fun n : ℕ => pzf (Work.Spaces.pth (F n))) (limM f)
      atTop Work.FTS.EllipticEst.Q0 :=
    hM.congr fun n => fun p hp =>
      (Work.Spaces.pz_pth_comm ((hsm n).contDiffAt (hQ.mem_nhds hp))).symm
  have hB1 : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth (F n)) p.1 p.2)
      (limB1 f) atTop Work.FTS.EllipticEst.Q0 := by
    have h01div : TendstoLocallyUniformlyOn
        (fun n : ℕ => fun p : ℝ × ℝ => slot 0 1 (F n) p / Real.sin (2 * p.2))
        (fun p : ℝ × ℝ => slot 0 1 f p / Real.sin (2 * p.2)) atTop
        Work.FTS.EllipticEst.Q0 :=
      (hslot 0 1 (by norm_num)).div₀
        (tlu_const (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0)
        (hcont 0 1 (by norm_num)) hsin_cont (fun p hp => hsn0 p hp)
    have hd01 : ContinuousOn (fun p : ℝ × ℝ => slot 0 1 f p / Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      (hcont 0 1 (by norm_num)).div hsin_cont (fun p hp => hsn0 p hp)
    have hccont : ContinuousOn
        (fun p : ℝ × ℝ => 2 * Real.sin (2 * p.2) * Real.cos (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      ((continuous_const.continuousOn).mul hsin_cont).mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn)
    have hprod := (tlu_const (fun p : ℝ × ℝ => 2 * Real.sin (2 * p.2) * Real.cos (2 * p.2))
      Work.FTS.EllipticEst.Q0).mul₀ h01div hccont hd01
    have hnum := (hslot 0 2 (by norm_num)).sub hprod
    have hcnum : ContinuousOn (fun p : ℝ × ℝ => slot 0 2 f p
        - 2 * Real.sin (2 * p.2) * Real.cos (2 * p.2)
          * (slot 0 1 f p / Real.sin (2 * p.2))) Work.FTS.EllipticEst.Q0 :=
      (hcont 0 2 (by norm_num)).sub (hccont.mul hd01)
    have hcd : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ 2)
        Work.FTS.EllipticEst.Q0 := (hsin_cont.pow 2)
    have h := hnum.div₀
      (tlu_const (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ 2) Work.FTS.EllipticEst.Q0)
      hcnum hcd (fun p hp => pow_ne_zero 2 (hsn0 p hp))
    refine h.congr fun n => ?_
    intro p hp
    have hs : Real.sin (2 * p.2) ≠ 0 := hsn0 p hp
    have hd : ContDiffAt ℝ 2 (Function.uncurry (F n)) p := (hsm n).contDiffAt (hQ.mem_nhds hp)
    show (slot 0 2 (F n) p - 2 * Real.sin (2 * p.2) * Real.cos (2 * p.2)
        * (slot 0 1 (F n) p / Real.sin (2 * p.2))) / (Real.sin (2 * p.2)) ^ 2
      = Work.Spaces.pth (Work.Spaces.pth (F n)) p.1 p.2
    simp only [slot]
    rw [← Work.FTS.StrongEps.E5Aux.slotIdents.pth_pth_eq hd hs]
  -- ### Step 6: the limits of the level-one approximants
  have hJetA : TendstoLocallyUniformlyOn (fun n : ℕ => jet (Work.Spaces.pz (F n))) (limJetA f)
      atTop Work.FTS.EllipticEst.Q0 := tendstoLocallyUniformlyOn_clmPair hA1 hM
  have hJetB : TendstoLocallyUniformlyOn (fun n : ℕ => jet (Work.Spaces.pth (F n))) (limJetB f)
      atTop Work.FTS.EllipticEst.Q0 := tendstoLocallyUniformlyOn_clmPair hM' hB1
  have hJetA' : TendstoLocallyUniformlyOn
      (fun n : ℕ => fderiv ℝ (Function.uncurry (Work.Spaces.pz (F n)))) (limJetA f) atTop
      Work.FTS.EllipticEst.Q0 :=
    hJetA.congr fun n => fun p hp => (fderiv_uncurry_eq_clmPair (hdiffPz n p hp)).symm
  have hJetB' : TendstoLocallyUniformlyOn
      (fun n : ℕ => fderiv ℝ (Function.uncurry (Work.Spaces.pth (F n)))) (limJetB f) atTop
      Work.FTS.EllipticEst.Q0 :=
    hJetB.congr fun n => fun p hp => (fderiv_uncurry_eq_clmPair (hdiffPth n p hp)).symm
  have hdA : ∀ p ∈ Work.FTS.EllipticEst.Q0, HasFDerivAt (limA f) (limJetA f p) p := by
    intro p hp
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn hQ hJetA'
      (fun n q hq => (hdiffPz n q hq).hasFDerivAt) ?_ hp
    intro q hq
    exact hA.tendsto_at hq
  have hdB : ∀ p ∈ Work.FTS.EllipticEst.Q0, HasFDerivAt (limB f) (limJetB f p) p := by
    intro p hp
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn hQ hJetB'
      (fun n q hq => (hdiffPth n q hq).hasFDerivAt) ?_ hp
    intro q hq
    exact hB.tendsto_at hq
  have hfdA : ∀ p ∈ Work.FTS.EllipticEst.Q0, fderiv ℝ (limA f) p = limJetA f p :=
    fun p hp => (hdA p hp).fderiv
  have hfdB : ∀ p ∈ Work.FTS.EllipticEst.Q0, fderiv ℝ (limB f) p = limJetB f p :=
    fun p hp => (hdB p hp).fderiv
  have hdiffA : DifferentiableOn ℝ (limA f) Work.FTS.EllipticEst.Q0 :=
    fun p hp => (hdA p hp).differentiableAt.differentiableWithinAt
  have hdiffB : DifferentiableOn ℝ (limB f) Work.FTS.EllipticEst.Q0 :=
    fun p hp => (hdB p hp).differentiableAt.differentiableWithinAt
  have hcontPzJet : ∀ n, ContinuousOn (jet (Work.Spaces.pz (F n))) Work.FTS.EllipticEst.Q0 := by
    intro n
    have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (F n)))
        Work.FTS.EllipticEst.Q0 := (Work.Spaces.uncurry_partial_c1 hQ (hsm n)).1
    refine (h1.continuousOn_fderiv_of_isOpen hQ (by norm_num)).congr fun p hp => ?_
    exact (fderiv_uncurry_eq_clmPair (hdiffPz n p hp)).symm
  have hcontPthJet : ∀ n, ContinuousOn (jet (Work.Spaces.pth (F n))) Work.FTS.EllipticEst.Q0 := by
    intro n
    have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (F n)))
        Work.FTS.EllipticEst.Q0 := (Work.Spaces.uncurry_partial_c1 hQ (hsm n)).2
    refine (h1.continuousOn_fderiv_of_isOpen hQ (by norm_num)).congr fun p hp => ?_
    exact (fderiv_uncurry_eq_clmPair (hdiffPth n p hp)).symm
  have hcontJetA : ContinuousOn (limJetA f) Work.FTS.EllipticEst.Q0 :=
    hJetA.continuousOn (Eventually.of_forall hcontPzJet).frequently
  have hcontJetB : ContinuousOn (limJetB f) Work.FTS.EllipticEst.Q0 :=
    hJetB.continuousOn (Eventually.of_forall hcontPthJet).frequently
  have hCdA : ContDiffOn ℝ 1 (limA f) Work.FTS.EllipticEst.Q0 := by
    rw [← show ((0 : ℕ∞ω) + 1) = 1 from by norm_num]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hQ).mpr ⟨hdiffA, ?_, ?_⟩
    · intro h; exact absurd h (by norm_num)
    · rw [contDiffOn_zero]
      exact hcontJetA.congr (fun p hp => hfdA p hp)
  have hCdB : ContDiffOn ℝ 1 (limB f) Work.FTS.EllipticEst.Q0 := by
    rw [← show ((0 : ℕ∞ω) + 1) = 1 from by norm_num]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hQ).mpr ⟨hdiffB, ?_, ?_⟩
    · intro h; exact absurd h (by norm_num)
    · rw [contDiffOn_zero]
      exact hcontJetB.congr (fun p hp => hfdB p hp)
  -- ### Step 7: assemble
  have hCdJet : ContDiffOn ℝ 1 (limJet f) Work.FTS.EllipticEst.Q0 := by
    have hpair : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (limA f p, limB f p))
        Work.FTS.EllipticEst.Q0 := hCdA.prodMk hCdB
    have hclm : ContDiffOn ℝ 1 (clmPair : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℝ)) Set.univ :=
      (ContinuousLinearMap.contDiff clmPair).contDiffOn
    have hcomp := hclm.comp hpair (fun p _ => Set.mem_univ p)
    exact hcomp.congr (fun p _ => by simp only [limJet, Function.comp_apply])
  have hCdFderiv : ContDiffOn ℝ 1 (fderiv ℝ (Function.uncurry f)) Work.FTS.EllipticEst.Q0 :=
    hCdJet.congr (fun p hp => hfd_lim p hp)
  rw [show (2 : ℕ∞ω) = 1 + 1 from by norm_num]
  exact (contDiffOn_succ_iff_fderiv_of_isOpen hQ).mpr
    ⟨hdiff_f, (fun h => absurd h (by norm_num)), hCdFderiv⟩

end Work.FTS.StrongEps.E5Aux

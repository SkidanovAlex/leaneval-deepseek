import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.LWP.VorticityAPI
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.ConstructionInstance.selfSimNoLG_of_data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

theorem selfSimNoLG_of_data {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlwp : Work.LWP.LWPInputs α) (hv : Work.ConstructionInstance.SelfSimVorticityEquation α P)
    (hG : Work.ConstructionInstance.SelfSimLGClass α P)
    (hsm : Work.ConstructionInstance.SelfSimVortSmooth P) :
    Work.ConstructionInstance.SelfSimNoLG P := by
  -- an `LGClass` solution of the datum past the blow-up time is contradictory
  intro T' hT' ⟨p', u', hLG⟩
  obtain ⟨hsol', _hodd', hst'⟩ := hLG
  -- the ansatz is an Euler solution of the same datum on `[0,P.T)`
  obtain ⟨p, hpc, hpe⟩ := hlwp.pressure (ansatzV P) (solVort P) P.T
      ((selfSimLGClass_iff_spaceTimeHolder P).mp hG)
      (fun t ht x => vorticity_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩ x)
      (fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩) hv
  have hsol : IsLocalEulerEquationSolution p
      (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) P.T (ansatzV P) :=
    { solContDiff := hsm.mono (fun q hq => ⟨trivial, ⟨by linarith [hq.2.1], hq.2.2⟩⟩)
      pressureContDiff := hpc
      eq := hpe
      div_free := fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩
      init := ansatzV_zero P }
  -- uniqueness in the Lichtenstein–Gunther class
  have huniq : ∀ x t, t ∈ Set.Ico 0 P.T → ansatzV P x t = u' x t :=
    hlwp.uniqueness _ P.T p p' (ansatzV P) u' hsol
      (isLocalEulerEquationSolution_mono hsol' (le_of_lt hT'))
      (fun S hS => hG S hS)
      (fun S hS => hst' S ⟨hS.1, lt_trans hS.2 hT'⟩)
  -- the strip `[0,(P.T+T')/2]` lies past the blow-up time: the LG class bounds `∇×u'` there
  have hTS : P.T < (P.T + T') / 2 := by linarith
  have hSmem : (P.T + T') / 2 ∈ Set.Ioo (0 : ℝ) T' :=
    ⟨by linarith [P.hT, hT'], by linarith [hT']⟩
  obtain ⟨K, hK0, hK⟩ := vorticity_bound_of_strip (α := α) (u := u') (S := (P.T + T') / 2)
    (T := P.T) hTS (hst' _ hSmem)
  -- hence `bkm u'` is bounded on `[0,P.T)`
  have hbound : ∀ t ∈ Set.Ico 0 P.T, Work.LWP.bkm u' t ≤ K * P.T := by
    intro t ht
    rw [← bkm_congr_of_eqOn_Ico huniq t ht]
    refine bkm_le_of_vortLInf_bound P.hT.le hK0
      (intervalIntegrable_vortLInf_ansatzV P hlwp.law) ?_ t ht
    intro s hs
    apply ciSup_le
    intro x
    have heq : (fun y => ansatzV P y s) = (fun y => u' y s) :=
      funext (fun y => huniq y s hs)
    rw [heq]
    exact hK s hs x
  -- whereas `bkm (ansatzV P)` diverges at `P.T`
  have hdiv := bkm_divergence_of_st5 P hlwp.law
  haveI : NeBot (𝓝[<] P.T) := nhdsWithin_Iio_neBot le_rfl
  have hev : ∀ᶠ t in 𝓝[<] P.T, K * P.T + 1 < Work.LWP.bkm (ansatzV P) t :=
    hdiv.eventually (eventually_gt_atTop _)
  have hevIco : ∀ᶠ t in 𝓝[<] P.T, t ∈ Set.Ico 0 P.T :=
    Work.StabilityFar.BKM.eventually_mem_Ico_nhdsLT P.T P.hT
  obtain ⟨t, hgt, htIco⟩ := (hev.and hevIco).exists
  have h1 := hbound t htIco
  have h2 : Work.LWP.bkm (ansatzV P) t = Work.LWP.bkm u' t :=
    bkm_congr_of_eqOn_Ico huniq t htIco
  linarith

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## The profile and its `D_θ`-iterates -/

/-- The angular profile `θ ↦ -sin²θ`, as a function of one variable. -/
private def G : ℝ → ℝ := fun θ => -((Real.sin θ) ^ 2)

/-- The first iterate `D_θ (θ ↦ -sin²θ) = -sin²(2θ)`. -/
private def L1 : ℝ → ℝ := fun θ => -((Real.sin (2 * θ)) ^ 2)

/-- The second iterate `-4 sin²(2θ) cos(2θ)`. -/
private def L2 : ℝ → ℝ := fun θ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)

/-- The third iterate `-16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)`. -/
private def L3 : ℝ → ℝ :=
  fun θ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
    + 8 * (Real.sin (2 * θ)) ^ 4

/-- The fourth iterate `-64 sin²(2θ) cos³(2θ) + 128 sin⁴(2θ) cos(2θ)`. -/
private def L4 : ℝ → ℝ :=
  fun θ => -64 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
    + 128 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)

/-! ## `SmoothInt` of the profile -/

/-- The profile `θ ↦ -sin²θ` is `SmoothInt`. -/
private lemma smoothInt_G : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => G θ) := by
  constructor
  · have h : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => -((Real.sin p.2) ^ 2)) := by fun_prop
    exact h.contDiffOn
  · intro θ _
    exact contDiffOn_const

/-! ## Elementary facts about `Iθ` -/

/-- On `Iθ` the number `sin(2θ)` lies in `[0,1]`. -/
private lemma sin_two_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 := by
  have h0 : 0 ≤ θ := hθ.1
  have h1 : θ ≤ Real.pi / 2 := hθ.2
  have h2 : 0 ≤ 2 * θ := by linarith
  have h3 : 2 * θ ≤ Real.pi := by linarith [Real.pi_pos]
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h2 h3, Real.sin_le_one _⟩


/-- The monomial bound with a constant factor, in the shape `(C s^a) c^b`. -/
private lemma const_mono_le {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : |c| ≤ 1)
    (C : ℝ) {a b : ℕ} (ha : 1 ≤ a) : |(C * s ^ a) * c ^ b| ≤ |C| * s := by
  have hcb : |c| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg c) hc
  have hsa : s ^ a ≤ s := by simpa using pow_le_pow_of_le_one hs0 hs1 ha
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs0 a), abs_pow]
  calc (|C| * s ^ a) * |c| ^ b ≤ (|C| * s ^ a) * 1 :=
        mul_le_mul_of_nonneg_left hcb (mul_nonneg (abs_nonneg C) (pow_nonneg hs0 a))
    _ = |C| * s ^ a := by ring
    _ ≤ |C| * s := mul_le_mul_of_nonneg_left hsa (abs_nonneg C)

/-! ## Derivatives of the iterates -/

/-- `d/dθ sin(2θ) = 2cos(2θ)`. -/
private lemma hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ := by
  have hlin : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa using hlin.sin

/-- `d/dθ cos(2θ) = -2sin(2θ)`. -/
private lemma hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-Real.sin (2 * θ) * 2) θ := by
  have hlin : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  simpa using hlin.cos

/-- `deriv G θ = -sin(2θ)`. -/
private lemma deriv_G (θ : ℝ) : deriv G θ = -(Real.sin (2 * θ)) := by
  have hsin : HasDerivAt (fun θ : ℝ => Real.sin θ) (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have h : HasDerivAt (fun θ : ℝ => Real.sin θ * Real.sin θ)
      (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ) θ := hsin.mul hsin
  have h2 : HasDerivAt G (-(Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ)) θ := by
    convert h.neg using 1 <;> (try funext x) <;>
      (try simp only [G, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h2.deriv, Real.sin_two_mul]
  ring

/-- `deriv (-sin²(2θ)) = -4 sin(2θ) cos(2θ)`, in raw form. -/
private lemma deriv_L1 (θ : ℝ) :
    deriv (fun θ : ℝ => -((Real.sin (2 * θ)) ^ 2)) θ
      = -((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
          + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) := by
  have hS := hasDerivAt_sin_two θ
  have h : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ))
      ((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
        + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) θ := hS.mul hS
  have h2 : HasDerivAt (fun θ : ℝ => -((Real.sin (2 * θ)) ^ 2))
      (-((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
          + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2))) θ := by
    convert h.neg using 1 <;> (try funext x) <;>
      (try simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h2.deriv]

/-- `deriv (-4 sin²(2θ) cos(2θ)) = -16 sin(2θ) cos²(2θ) + 8 sin³(2θ)`. -/
private lemma deriv_L2 (θ : ℝ) :
    deriv (fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) θ
      = -16 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 3 := by
  have hS := hasDerivAt_sin_two θ
  have hC := hasDerivAt_cos_two θ
  have hSS : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ))
      ((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
        + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) θ := hS.mul hS
  have hSSC := hSS.mul hC
  have h4 := hSSC.const_mul (-4)
  have h5 : HasDerivAt (fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ))
      (-16 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 3) θ := by
    convert h4 using 1 <;> (try funext x) <;>
      (try simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h5.deriv]

/-- `deriv (-16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)) = -64 sin(2θ) cos³(2θ) + 128 sin³(2θ) cos(2θ)`. -/
private lemma deriv_L3 (θ : ℝ) :
    deriv (fun θ : ℝ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 4) θ
      = -64 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 3 * Real.cos (2 * θ) := by
  have hS := hasDerivAt_sin_two θ
  have hC := hasDerivAt_cos_two θ
  have hSS : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ))
      ((Real.cos (2 * θ) * 2) * Real.sin (2 * θ)
        + Real.sin (2 * θ) * (Real.cos (2 * θ) * 2)) θ := hS.mul hS
  have hCC : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ) * Real.cos (2 * θ))
      ((-Real.sin (2 * θ) * 2) * Real.cos (2 * θ)
        + Real.cos (2 * θ) * (-Real.sin (2 * θ) * 2)) θ := hC.mul hC
  have hA := (hSS.mul hCC).const_mul (-16)
  have hB := (hSS.mul hSS).const_mul 8
  have hsum := hA.add hB
  have h5 : HasDerivAt (fun θ : ℝ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 4)
      (-64 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 3 * Real.cos (2 * θ)) θ := by
    convert hsum using 1 <;> (try funext x) <;>
      (try simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply, pow_two]) <;>
      (first | ring | ring_nf)
  rw [h5.deriv]

/-! ## The iterate identities -/

/-- `Lop G = -sin²(2θ)`. -/
private lemma Lop_G : Work.Spaces.Lop G = L1 := by
  funext θ
  show Real.sin (2 * θ) * deriv G θ = -((Real.sin (2 * θ)) ^ 2)
  rw [deriv_G θ]
  ring

/-- `Lop (-sin²(2θ)) = -4 sin²(2θ) cos(2θ)`. -/
private lemma Lop_L1 : Work.Spaces.Lop L1 = L2 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -((Real.sin (2 * θ)) ^ 2)) θ
      = -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)
  rw [deriv_L1 θ]
  ring

/-- `Lop (-4 sin²(2θ) cos(2θ)) = -16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)`. -/
private lemma Lop_L2 : Work.Spaces.Lop L2 = L3 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)) θ
      = -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 + 8 * (Real.sin (2 * θ)) ^ 4
  rw [deriv_L2 θ]
  ring

/-- `Lop (-16 sin²(2θ) cos²(2θ) + 8 sin⁴(2θ)) = -64 sin²(2θ) cos³(2θ) + 128 sin⁴(2θ) cos(2θ)`. -/
private lemma Lop_L3 : Work.Spaces.Lop L3 = L4 := by
  funext θ
  show Real.sin (2 * θ) * deriv (fun θ : ℝ => -16 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
        + 8 * (Real.sin (2 * θ)) ^ 4) θ
      = -64 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
        + 128 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
  rw [deriv_L3 θ]
  ring

/-- The first iterate of `Lop` on `G`. -/
private lemma iter_one : Work.Spaces.Lop^[1] G = L1 := by
  rw [Function.iterate_one]
  exact Lop_G

/-- The second iterate of `Lop` on `G`. -/
private lemma iter_two : Work.Spaces.Lop^[2] G = L2 := by
  have h : Work.Spaces.Lop^[2] G = Work.Spaces.Lop (Work.Spaces.Lop^[1] G) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_one, Lop_L1]

/-- The third iterate of `Lop` on `G`. -/
private lemma iter_three : Work.Spaces.Lop^[3] G = L3 := by
  have h : Work.Spaces.Lop^[3] G = Work.Spaces.Lop (Work.Spaces.Lop^[2] G) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_two, Lop_L2]

/-- The fourth iterate of `Lop` on `G`. -/
private lemma iter_four : Work.Spaces.Lop^[4] G = L4 := by
  have h : Work.Spaces.Lop^[4] G = Work.Spaces.Lop (Work.Spaces.Lop^[3] G) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply']
  rw [h, iter_three, Lop_L3]

/-! ## The bounds on `Iθ` -/

/-- `|G θ| ≤ 192` on `Iθ`. -/
private lemma bound_G {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |G θ| ≤ 192 := by
  have h0 : 0 ≤ θ := hθ.1
  have h1 : θ ≤ Real.pi / 2 := hθ.2
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h : |G θ| = (Real.sin θ) ^ 2 := by
    simp only [G, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  rw [h]
  calc (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀ hsin0 hsin1
    _ ≤ 192 := by norm_num

/-- `|L1 θ| ≤ 192 sin(2θ)` on `Iθ`. -/
private lemma bound_L1 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |L1 θ| ≤ 192 * Real.sin (2 * θ) := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hsq : (Real.sin (2 * θ)) ^ 2 ≤ Real.sin (2 * θ) := by
    have h := mul_le_mul_of_nonneg_left hs1 hs0
    simpa [pow_two] using h
  have h : |L1 θ| ≤ Real.sin (2 * θ) := by
    simp only [L1, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
    exact hsq
  calc |L1 θ| ≤ Real.sin (2 * θ) := h
    _ ≤ 192 * Real.sin (2 * θ) := le_mul_of_one_le_left hs0 (by norm_num)

/-- `|L2 θ| ≤ 192 sin(2θ)` on `Iθ`. -/
private lemma bound_L2 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |L2 θ| ≤ 192 * Real.sin (2 * θ) := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h : |L2 θ| ≤ 4 * Real.sin (2 * θ) := by
    have heq : L2 θ = ((-4 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 1 := by
      simp only [L2, pow_one]
    rw [heq]
    have hthis := const_mono_le hs0 hs1 hc (-4) (a := 2) (b := 1) (by norm_num)
    have hc4 : |-4| = (4 : ℝ) := by
      rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rwa [hc4] at hthis
  calc |L2 θ| ≤ 4 * Real.sin (2 * θ) := h
    _ ≤ 192 * Real.sin (2 * θ) := mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 192) hs0

/-- `|L3 θ| ≤ 192 sin(2θ)` on `Iθ`. -/
private lemma bound_L3 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |L3 θ| ≤ 192 * Real.sin (2 * θ) := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hA : |((-16 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 2|
      ≤ 16 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (-16) (a := 2) (b := 2) (by norm_num)
    have hc16 : |-16| = (16 : ℝ) := by
      rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
    rwa [hc16] at hthis
  have hB : |(8 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 0|
      ≤ 8 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (8) (a := 4) (b := 0) (by norm_num)
    have hc8 : |(8 : ℝ)| = 8 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    rwa [hc8] at hthis
  have heq : L3 θ = ((-16 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 2
      + (8 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 0 := by
    simp only [L3]
    ring
  rw [heq]
  calc |((-16 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 2
        + (8 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 0|
      ≤ |((-16 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 2|
        + |(8 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 0| := abs_add_le _ _
    _ ≤ 16 * Real.sin (2 * θ) + 8 * Real.sin (2 * θ) := add_le_add hA hB
    _ = 24 * Real.sin (2 * θ) := by ring
    _ ≤ 192 * Real.sin (2 * θ) :=
        mul_le_mul_of_nonneg_right (by norm_num : (24 : ℝ) ≤ 192) hs0

/-- `|L4 θ| ≤ 192 sin(2θ)` on `Iθ`. -/
private lemma bound_L4 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |L4 θ| ≤ 192 * Real.sin (2 * θ) := by
  obtain ⟨hs0, hs1⟩ := sin_two_mem hθ
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hA : |((-64 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 3|
      ≤ 64 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (-64) (a := 2) (b := 3) (by norm_num)
    have hc64 : |-64| = (64 : ℝ) := by
      rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 64)]
    rwa [hc64] at hthis
  have hB : |((128 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 1|
      ≤ 128 * Real.sin (2 * θ) := by
    have hthis := const_mono_le hs0 hs1 hc (128) (a := 4) (b := 1) (by norm_num)
    have hc128 : |(128 : ℝ)| = 128 := by
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 128)]
    rwa [hc128] at hthis
  have heq : L4 θ = ((-64 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 3
      + ((128 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 1 := by
    simp only [L4]
    ring
  rw [heq]
  calc |((-64 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 3
        + ((128 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 1|
      ≤ |((-64 : ℝ) * (Real.sin (2 * θ)) ^ 2) * (Real.cos (2 * θ)) ^ 3|
        + |((128 : ℝ) * (Real.sin (2 * θ)) ^ 4) * (Real.cos (2 * θ)) ^ 1| := abs_add_le _ _
    _ ≤ 64 * Real.sin (2 * θ) + 128 * Real.sin (2 * θ) := add_le_add hA hB
    _ = 192 * Real.sin (2 * θ) := by ring

/-! ## The row -/

theorem angProfile_sinSq :
    ∃ B : ℝ, 0 < B ∧
      Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ)^2)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ)^2))| ≤ B) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ|
          ≤ B * Real.sin (2*θ)) := by
  refine ⟨192, by norm_num, smoothInt_G, ?_, ?_⟩
  · intro θ hθ
    exact bound_G hθ
  · intro i hi1 hi4 θ hθ
    have hit : Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ
        = Work.Spaces.Lop^[i] G θ := by
      have hf : (fun θ : ℝ => (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ) = G := by
        funext x
        rfl
      rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop i
        (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0) θ, hf]
    rw [hit]
    interval_cases i
    · rw [iter_one]; exact bound_L1 hθ
    · rw [iter_two]; exact bound_L2 hθ
    · rw [iter_three]; exact bound_L3 hθ
    · rw [iter_four]; exact bound_L4 hθ

end Work.FTS.Nonlinear.Pieces.RNP.RNP24
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzdIter_FK_eq_qang =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24


end Work.FTS.Nonlinear.Pieces.RNP.RNP24
end
end

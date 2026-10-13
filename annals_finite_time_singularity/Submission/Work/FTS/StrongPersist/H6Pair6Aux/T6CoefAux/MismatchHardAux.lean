import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotAmgm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.slotArith
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.cs_sqrt_int
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.zProdIntLe
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# Auxiliary lemmas for the `b = 5` crux of `T6CoefAux/mismatchCaseHard`

The elementary `sin(2θ)`-power identities, the `η`-slot weight domination, the `z`-marginal of
the pure-`z` slot `D_z⁵f` at the `η`-weight, and the slice Agmon bound for `D_z⁵f`
(the `H2.T1Q.SliceSupOpen` instance).
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-- `sin(2θ)² · sin(2θ)^{-γ} = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_sin_sq_neg {γ s : ℝ} (hs : 0 < s) : s ^ (2 : ℕ) * s ^ (-γ) = s ^ (2 - γ) := by
  have h : s ^ (2 : ℕ) = s ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast s 2).symm
  rw [h, ← Real.rpow_add hs ((2 : ℕ) : ℝ) (-γ)]
  congr 1

/-- `sin(2θ)^{-γ} · sin(2θ) = sin(2θ)^{1-γ}` at an interior angle. -/
theorem mh_neg_gam_mul {γ s : ℝ} (hs : 0 < s) : s ^ (-γ) * s = s ^ (1 - γ) := by
  have h := Real.rpow_add hs (-γ) (1 : ℝ)
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1
  ring

/-- `sin(2θ)^{1-γ} · sin(2θ) = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_one_sub_gam_mul {γ s : ℝ} (hs : 0 < s) : s ^ (1 - γ) * s = s ^ (2 - γ) := by
  have h := Real.rpow_add hs (1 - γ) (1 : ℝ)
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1
  ring

/-- `sin(2θ)^{-γ} · sin(2θ)² = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_neg_gam_mul_sq {γ s : ℝ} (hs : 0 < s) : s ^ (-γ) * s ^ (2 : ℕ) = s ^ (2 - γ) := by
  have h : s ^ (-γ) * s ^ (2 : ℕ) = s ^ (-γ) * (s * s) := by ring
  rw [h, ← mul_assoc, mh_neg_gam_mul hs, mh_one_sub_gam_mul hs]

/-- `sin(2θ)² · sin(2θ)^{-γ} = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_sq_mul_neg_gam {γ s : ℝ} (hs : 0 < s) : s ^ (2 : ℕ) * s ^ (-γ) = s ^ (2 - γ) := by
  rw [mul_comm, mh_neg_gam_mul_sq hs]

/-- `w(z)² X² ≤ (X·(w z / sin(2θ)^{η/2}))²` for `z > 0`, `0 < θ < π/2` (the `ℋ⁶`-slot weight
`w/σ^{η/2}` dominates `w` because `w ≥ 1` and `σ ≤ 1`). -/
theorem mh_w_le_slotWeight {z θ X : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.w z) ^ 2 * X ^ 2
      ≤ (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw
  have hση : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hσ.le (Real.sin_le_one _) Work.Spaces.eta_nonneg
  have hpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hσ _
  have hinv : 1 ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹ := (one_le_inv₀ hpos).mpr hση
  have hp : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [show ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ ((2 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hσ.le]
    norm_num
  calc (Work.Spaces.w z) ^ 2 * X ^ 2 = X ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ X ^ 2 * ((Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (sq_nonneg _) hinv) (sq_nonneg X)
    _ = (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow, div_pow, div_eq_mul_inv, hp]

/-- `X² ≤ (X·(w z / sin(2θ)^{η/2}))²` for `z > 0`, `0 < θ < π/2` (the weight factor is `≥ 1`). -/
theorem mh_le_slotWeight {z θ X : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    X ^ 2 ≤ (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw
  have hση : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hσ.le (Real.sin_le_one _) Work.Spaces.eta_nonneg
  have hpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hσ _
  have hinv : 1 ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹ := (one_le_inv₀ hpos).mpr hση
  have hp : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [show ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ ((2 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hσ.le]
    norm_num
  have hkey : (1 : ℝ) ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, div_eq_mul_inv, hp]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹ :=
          mul_le_mul hw2 hinv (by norm_num) (sq_nonneg _)
  calc X ^ 2 = X ^ 2 * 1 := by ring
    _ ≤ X ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg X)
    _ = (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]

/-- **The pure-`z` slot `D_z⁵f` at the `η`-weight, sliced in `z`.**  For `f` of class
`SmoothOpen` with honest `HkMem α 6 f`, `∫_z w(z)² ∫_θ (D_z⁵f)² ≤ |f|²_{ℋ⁶}`, with membership
of the `z`-marginal. -/
theorem mh_pureZ_eta_slot_l2 : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (f : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      ≤ Work.Spaces.HkSq α 6 f := by
  intro α hα f hfsm hf6
  obtain ⟨hbase, hbaseval⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := 6) hfsm hf6
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 5 f p.1 p.2) ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact contOn_w.mul
      ((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.DzIter 5)).pow 2)
  have hnn : ∀ z θ : ℝ,
      0 ≤ (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2 :=
    fun z θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpt : ∀ᵐ p ∂pm, (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 5 f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    exact le_trans (mh_w_le_slotWeight (X := Work.Spaces.DzIter 5 f z θ) hz hθ0 hθ1)
      (Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 5 (by norm_num))
  have hWint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 5 f p.1 p.2) ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' hbase haesm ?_
    filter_upwards [hpt] with p hp
    rwa [Real.norm_eq_abs, abs_of_nonneg (hnn p.1 p.2)]
  -- the `z`-marginal of the *joint* integrand
  have hOuter : MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (((MeasureTheory.integrable_prod_iff haesm).mp hWint).2).congr
      (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ y in Work.Spaces.Iθ, ‖(Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z y) ^ 2‖)
      = ∫ y in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z y) ^ 2
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => Real.norm_of_nonneg (hnn z y)))
  have hMarg : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hOuter.congr (Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
        (fun θ : ℝ => (Work.Spaces.DzIter 5 f z θ) ^ 2)))
  refine ⟨hMarg, ?_⟩
  obtain ⟨hjoint, hjointval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2)
    hnn haesm ((MeasureTheory.integrable_prod_iff haesm).mp hWint).1 hOuter
  rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2 from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z =>
      (MeasureTheory.integral_const_mul _ _).symm))]
  rw [← hjointval, ← hbaseval]
  exact MeasureTheory.integral_mono_ae hjoint hbase hpt

/-- **The slice Agmon bound for `D_z⁵f`** (the `H2.T1Q.SliceSupOpen` instance, whose two `θ`-slice
integrals are the `η`-slot mean and the γ-weighted `(5,1)`-slot). -/
theorem mh_agmon {α : ℝ} {f : ℝ → ℝ → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f) (hf6 : Work.Spaces.HkMem α 6 f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 f z θ) ^ 2
        ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ, (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ' ^ 2
                * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) := by
    intro z θ hz hθ0 hθ1
    have hmean : MeasureTheory.IntegrableOn
        (fun θ' : ℝ => (Work.Spaces.DzIter 5 f z θ') ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hf6.1 z (Set.mem_Ici.mpr hz.le))
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
            (hfsm.DzIter 5)).pow 2) hz) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ' hθ'0 hθ'1 => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_trans (mh_le_slotWeight (X := Work.Spaces.DzIter 5 f z θ') hz hθ'0 hθ'1)
        (Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ' 5 (by norm_num))
    have hder : MeasureTheory.IntegrableOn
        (fun θ' : ℝ => (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.congr
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
          (α := α) (f := f) (b := 5) (a := 1) hα0 hfsm hf6 (by norm_num) (by norm_num) hz) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ' hθ'0 hθ'1 => ?_)
      show Real.sin (2 * θ') ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ') ^ 2
        = (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)
      have hdw : (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)
          = (Work.Spaces.mixed 5 1 f z θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)) :=
        Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hfsm 5 0 hz ⟨hθ'0, hθ'1⟩
      calc Real.sin (2 * θ') ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ') ^ 2
          = (Work.Spaces.mixed 5 1 f z θ') ^ 2 * Real.sin (2 * θ') ^ (-(Work.Spaces.gam α)) := by ring
        _ = (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
              * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α) := hdw.symm
    have h := Work.H2.T1Q.SliceSupOpen α (fun θ' : ℝ => Work.Spaces.DzIter 5 f z θ') hα0 hα1
      (((hfsm.DzIter 5).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder]))
      hmean hder θ ⟨hθ0, hθ1⟩
    exact h

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

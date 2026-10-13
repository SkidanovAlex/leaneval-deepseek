import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `topSlotZLe`: the top (`D_z^6`) slot of the `ℋ⁶`-norm

The `ℋ⁶`-integrand of `Work.Spaces.HkIntegrand` contains, for the index `i = 6` of its pure
`D_z`-sum, the summand

  `(D_z^6 f z θ · w z / sin(2θ)^{η/2})² = (w z)² · sin(2θ)^{-η} · (D_z^6 f z θ)²`

(`Work.Spaces.sq_mul_div_rpow`).  Pulling the radial factor `(w z)²` out of the angular
integral shows that the `η`-weighted angular mass of the top radial derivative, against the
radial weight `w²`, is exactly that summand integrated in `θ`; it is therefore dominated
pointwise in `z` by the whole `ℋ⁶`-integrand, and its `z`-integral by `HkSq α 6 f`.  That is
the first conjunct of `topSlotZLe`.  The second conjunct is the same statement without the
angular weight `sin(2θ)^{-η}`; since `sin(2θ) ∈ (0,1]` on the interior of `Iθ` we have
`sin(2θ)^{-η} ≥ 1` there, so the unweighted mass is dominated by the η-weighted one (the two
endpoints of `Iθ` are null), which is the case `q = 0` of the general slot statement below.

Everything is proved for the general slot `∫_θ w(z)² sin(2θ)^{-q} (D_z^j f)²` with
`0 ≤ q ≤ η` and `j ≤ k`, of which the two required instances are `(q,j,k) = (η,6,6)` and
`(0,6,6)`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The a.e. angular domination of a pure `D_z`-slot by the `ℋ^k`-integrand -/

/-- **A.e. pointwise domination of the `q`-weighted `D_z^j`-slot by the `ℋ^k`-integrand.**
For `0 ≤ q ≤ η`, `j ≤ k` and every `z`, almost every `θ ∈ Iθ` satisfies

  `canonW q z θ · (D_z^j f z θ)² ≤ HkIntegrand α k f z θ`.

On the open interval we have `0 < sin(2θ) ≤ 1`, hence `sin(2θ)^{-q} ≤ sin(2θ)^{-η}` (the
exponent `-q` is the larger one), and the identity `sq_mul_div_rpow` rewrites the `i = j`
pure `D_z`-summand of the `ℋ^k`-integrand.  The two endpoints of `Iθ` are null; there the
comparison only holds a.e. (`sin(2θ)^{-q}` is `0` for `q > 0` but `1` for `q = 0`). -/
theorem canonW_mul_DzIter_le_HkIntegrand {α q : ℝ} {f : ℝ → ℝ → ℝ} {k j : ℕ}
    (hq : q ≤ Work.Spaces.eta) (hj : j ≤ k) (z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.Iθ,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hmono : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hkey := Work.Spaces.sq_mul_div_rpow (Work.Spaces.DzIter j f z θ) (Work.Spaces.w z)
    (Real.sin (2 * θ)) Work.Spaces.eta hs.le (ne_of_gt Work.Spaces.eta_pos)
  rw [Work.FTS.TransportS.SlotT2.canonW]
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.DzIter j f z θ) ^ 2
      = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter j f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by ring
    _ ≤ (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter j f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)) (sq_nonneg _)
    _ = (Work.Spaces.DzIter j f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [hkey]; ring
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := Work.Spaces.sq_le_HkIntegrand_z α k f z θ j hj

/-! ## Pulling the radial weight out of the angular integral -/

/-- `∫_θ canonW q z θ · X θ = (w z)² · ∫_θ sin(2θ)^{-q} · X θ`: the angular integral of the
canonical slot weight is the radial factor `(w z)²` times the `sin(2θ)^{-q}`-weighted angular
mass of `X`. -/
theorem canonW_integral_eq (q z : ℝ) (X : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW q z θ * X θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-q) * X θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [Work.FTS.TransportS.SlotT2.canonW]
  ring

/-- The `q = 0` case of `canonW_integral_eq`: since `x^0 = 1` for every real `x`, the
unweighted angular mass is exactly the value at `q = 0`. -/
theorem canonW_zero_integral_eq (z : ℝ) (X : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.TransportS.SlotT2.canonW 0 z θ * X θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, X θ := by
  rw [canonW_integral_eq]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  simp only [neg_zero, Real.rpow_zero, one_mul]

/-! ## The marginal slot estimate -/

/-- **The general pure-`D_z` slot estimate.**  For `q ≤ η`, `j ≤ k`, an open-quadrant
smooth datum `f ∈ ℋ^k` has

* `z ↦ ∫_θ canonW q z θ · (D_z^j f z θ)²` integrable on `Iz`, and
* `∫_z ∫_θ canonW q z θ · (D_z^j f z θ)² ≤ HkSq α k f`.

The proof is the pointwise (`θ`-a.e.) domination `canonW_mul_DzIter_le_HkIntegrand`, monotone
integration in `θ` against the integrable `θ ↦ HkIntegrand α k f z θ` (from `HkMem`), and
monotone integration in `z` against `HkMem.2`; integrability of the marginal is the same
bound together with the a.e. strong measurability of the marginal
(`Work.FTS.TransportS.SlotT2.zslot_marginal_aesm`). -/
theorem canonW_DzIter_marginal {α q : ℝ} {k j : ℕ} {f : ℝ → ℝ → ℝ}
    (hq : q ≤ Work.Spaces.eta)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) (hj : j ≤ k) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2)
      ≤ Work.Spaces.HkSq α k f := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem hIθ
        (fun θ hθ => mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθ) (sq_nonneg _))
    · exact canonW_mul_DzIter_le_HkIntegrand hq hj z
  have hnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ ∫ θ in Work.Spaces.Iθ,
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j f z θ) ^ 2 :=
    fun z hz => MeasureTheory.setIntegral_nonneg hIθ
      (fun θ hθ => mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθ) (sq_nonneg _))
  constructor
  · refine Integrable.mono' hmem.2
      (Work.FTS.TransportS.SlotT2.zslot_marginal_aesm (q := q) hsm j) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => by rw [Real.norm_of_nonneg (hnn z hz)]; exact hslice z hz)
  · rw [Work.Spaces.HkSq]
    exact MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hnn) hmem.2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslice)

/-! ## The requested statement -/

theorem topSlotZLe {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    (MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter 6 f z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter 6 f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f) ∧
    (MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 6 f z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 6 f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f) := by
  obtain ⟨hintη, hboundη⟩ :=
    canonW_DzIter_marginal (α := α) (q := Work.Spaces.eta) (k := 6) (j := 6)
      le_rfl hsm hmem le_rfl
  obtain ⟨hint0, hbound0⟩ :=
    canonW_DzIter_marginal (α := α) (q := 0) (k := 6) (j := 6)
      Work.Spaces.eta_pos.le hsm hmem le_rfl
  -- the η-weighted slot, identified with the `canonW η` marginal
  have hfunη : (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter 6 f z θ) ^ 2)
      = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
            * (Work.Spaces.DzIter 6 f z θ) ^ 2 := by
    funext z
    exact (canonW_integral_eq Work.Spaces.eta z
      (fun θ => (Work.Spaces.DzIter 6 f z θ) ^ 2)).symm
  -- the unweighted slot, identified with the `canonW 0` marginal
  have hfun0 : (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 6 f z θ) ^ 2)
      = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW 0 z θ
            * (Work.Spaces.DzIter 6 f z θ) ^ 2 := by
    funext z
    exact (canonW_zero_integral_eq z (fun θ => (Work.Spaces.DzIter 6 f z θ) ^ 2)).symm
  rw [hfunη, hfun0]
  exact ⟨⟨hintη, hboundη⟩, hint0, hbound0⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

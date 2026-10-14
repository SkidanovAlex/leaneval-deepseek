import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyDefs
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFam_expansion_L2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution

open MeasureTheory


end Work.EllipticEst.ModalSolution
end
-- ===== merged: Submission.Work.FTS.ClassCHon.radGreen_modeEnergy_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon

/-- **Integrability on `(0,∞)` from continuity and compact support.**

If `f` is continuous on `(0,∞)` and vanishes off an interval `[a,b]` with `0 < a ≤ b` (so that
`[a,b] ⊆ (0,∞)` and `f` is supported in the compact set `[a,b]`), then `f` is integrable on
`(0,∞)`.  The proof splits `(0,∞) = (0,a) ∪ [a,b] ∪ (b,∞)`; on the two open pieces `f ≡ 0`, and on
`[a,b]` it is continuous on a compact set. -/
theorem integrableOn_Ioi_of_contOn_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Ioi 0)) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha (Set.mem_Icc.mp hz).1
  have hIcc : MeasureTheory.IntegrableOn f (Set.Icc a b) :=
    (hf.mono hsub).integrableOn_compact isCompact_Icc
  have hleft : MeasureTheory.IntegrableOn f (Set.Ioo 0 a) :=
    MeasureTheory.integrableOn_zero.congr_fun
      (fun z hz => by
        rw [hsupp z (fun h => absurd (Set.mem_Icc.mp h).1 (not_le.mpr hz.2))])
      measurableSet_Ioo
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi b) :=
    MeasureTheory.integrableOn_zero.congr_fun
      (fun z hz => by
        rw [hsupp z (fun h => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hz))])
      measurableSet_Ioi
  have hU : MeasureTheory.IntegrableOn f (Set.Ioo 0 a ∪ Set.Icc a b ∪ Set.Ioi b) :=
    (hleft.union hIcc).union hright
  have hset : Set.Ioo 0 a ∪ Set.Icc a b ∪ Set.Ioi b = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro ((⟨h1, _⟩ | ⟨h2, _⟩) | h3) <;> linarith
    · intro hx
      rcases lt_or_ge x a with h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · rcases le_or_gt x b with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
  rwa [hset] at hU

/-- **The decay of a source supported in `[a,b]` at `∞`:** `|c t| ≤ K/t` for `t ≥ 1`. -/
theorem decay_of_support {c : ℝ → ℝ} {a b : ℝ} {M : ℝ} (hMnn : 0 ≤ M)
    (hMb : ∀ t : ℝ, |c t| ≤ M) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t := by
  refine ⟨M * max b 1 + 1, by positivity, ?_⟩
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rcases lt_or_ge b t with hbt | hbt
  · rw [hsupp t (fun h => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hbt)), abs_zero]
    positivity
  · have htle : t ≤ max b 1 := le_trans hbt (le_max_left b 1)
    have hMul : M * t ≤ M * max b 1 := mul_le_mul_of_nonneg_left htle hMnn
    have h1 : M ≤ (M * max b 1) / t := by
      rw [le_div_iff₀ ht0]
      linarith
    have h2 : (M * max b 1) / t ≤ (M * max b 1 + 1) / t :=
      div_le_div_of_nonneg_right (by linarith) ht0.le
    linarith [hMb t]

/-- **The vanishing rate of a source supported in `[a,b]` near `0`:** `|c t| ≤ K t^p` on `(0,1]`
for some `p > 3/2`.  Since `c` vanishes on `(0,a)`, `p = 2` and `K = M/a² + 1` suffice. -/
theorem vanishing_of_support {c : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) {M : ℝ} (hMnn : 0 ≤ M)
    (hMb : ∀ t : ℝ, |c t| ≤ M) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p := by
  refine ⟨M / a ^ 2 + 1, 2, by positivity, by norm_num, ?_⟩
  intro t _ht0 _ht1
  by_cases hta : t < a
  · rw [hsupp t (fun h => absurd (Set.mem_Icc.mp h).1 (not_le.mpr hta)), abs_zero]
    positivity
  · have hge : a ≤ t := le_of_not_gt hta
    have hcoef : 0 ≤ M / a ^ 2 + 1 := by positivity
    have hK : (M / a ^ 2 + 1) * a ^ 2 = M + a ^ 2 := by
      field_simp
    rw [Real.rpow_two]
    calc |c t| ≤ M := hMb t
      _ ≤ M + a ^ 2 := by linarith [sq_nonneg a]
      _ = (M / a ^ 2 + 1) * a ^ 2 := hK.symm
      _ ≤ (M / a ^ 2 + 1) * t ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hge 2) hcoef



end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.farRegionLHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ### Elementary reflection facts

Everything below is the bookkeeping needed to transfer the *near*-region estimate
(`nearRegionLHS_i`) to the *far* region through the reflection `ρ θ = π/2 - θ`.

The reflection preserves `sin(2θ)`, is measure preserving on `Iθ = [0,π/2]` (which it maps to
itself), and conjugates `D_θ = sin(2θ)∂_θ` to `-D_θ`, so `D_θ^m` picks up the sign `(-1)^m`. -/

/-- The derivative of the reflected slice is minus the reflected derivative. -/
lemma far_deriv_reflSlice_eq (h : ℝ → ℝ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => h (Real.pi / 2 - θ')) θ = -deriv h (Real.pi / 2 - θ) := by
  have hmem : Real.pi / 2 - θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hdh : HasDerivAt h (deriv h (Real.pi / 2 - θ)) (Real.pi / 2 - θ) :=
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp)).hasDerivAt
  have hr : HasDerivAt (fun θ' : ℝ => Real.pi / 2 - θ') (-1) θ := by
    have h0 := (hasDerivAt_const (x := θ) (c := Real.pi / 2)).sub (hasDerivAt_id θ)
    have hf : ((fun _ : ℝ => Real.pi / 2) - (id : ℝ → ℝ)) = fun θ' : ℝ => Real.pi / 2 - θ' := by
      funext θ'; simp
    rw [hf] at h0
    simpa using h0
  have hcomp : deriv (fun θ' : ℝ => h (Real.pi / 2 - θ')) θ
      = deriv h (Real.pi / 2 - θ) * (-1) := by
    simpa [Function.comp_def] using (hdh.comp θ hr).deriv
  rw [hcomp]; ring

lemma far_neg_one_pow_sq (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- `D_θ^m` depends only on the germ: functions that agree on an open set have `D_θ^m`
agreeing there as well. -/
lemma far_Dth1Iter_congr_of_isOpen (m : ℕ) {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : Set.EqOn f g s) :
    Set.EqOn (Work.Elliptic.Dth1Iter m f) (Work.Elliptic.Dth1Iter m g) s := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      intro θ hθ
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
      simp only [Work.Elliptic.Dth1]
      congr 1
      exact (Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hθ, ih⟩).deriv_eq

/-- `D_θ^m` is linear: `D_θ^m(-f) = -(D_θ^m f)` globally. -/
lemma far_Dth1Iter_neg_eq (m : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter m (fun θ => -f θ)
      = fun θ => -(Work.Elliptic.Dth1Iter m f θ) := by
  induction m with
  | zero => funext θ; simp
  | succ m ih =>
      ext θ
      rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
      simp only [Work.Elliptic.Dth1]
      rw [ih]
      have h1 : (fun x : ℝ => -(Work.Elliptic.Dth1Iter m f x))
          =ᶠ[𝓝 θ] (fun x => (-1 : ℝ) * Work.Elliptic.Dth1Iter m f x) :=
        Filter.Eventually.of_forall (fun x => by ring)
      rw [h1.deriv_eq, deriv_const_mul_field]
      ring

/-- Reflection of `D_θ^m(∂_θ ·)`: the `m`-th angular derivative of the derivative of the
reflected slice is `(-1)^{m+1}` times the reflected `m`-th angular derivative of `∂_θh`. -/
lemma far_Dth1Iter_deriv_reflSlice_eq (m : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ
        = (-1 : ℝ) ^ (m + 1) * Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ) := by
  have hder : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by simp)
  have hrefl := (reflSlice_facts m (h := deriv h) hder).1
  intro θ hθ
  rw [far_Dth1Iter_congr_of_isOpen m isOpen_Ioo
    (fun θ' hθ' => far_deriv_reflSlice_eq h hsm hθ') hθ]
  rw [far_Dth1Iter_neg_eq m (fun θ' => deriv h (Real.pi / 2 - θ'))]
  change -(Work.Elliptic.Dth1Iter m (fun θ' => deriv h (Real.pi / 2 - θ')) θ)
      = (-1 : ℝ) ^ (m + 1) * Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)
  rw [hrefl θ hθ, pow_succ]
  ring

lemma far_sq_Dth1Iter_deriv_reflSlice_eq (m : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        = (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2 := by
  intro θ hθ
  rw [far_Dth1Iter_deriv_reflSlice_eq m hsm θ hθ, mul_pow, far_neg_one_pow_sq (m + 1),
    one_mul]

/-- Reflection of `D_θ^i(·/sin(2·))` on the quotient slice. -/
lemma far_Dth1Iter_divSin_reflSlice_eq (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ
        = (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i
          (fun θ' => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ) := by
  have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hsmF : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h θ / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.div hsin (fun θ hθ =>
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])))
  have hfun : (fun θ : ℝ => h (Real.pi / 2 - θ) / Real.sin (2 * θ))
      = (fun θ : ℝ => (fun θ' : ℝ => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ)) := by
    funext θ
    simp only []
    rw [sin_two_reflSlice]
  have hrefl := (reflSlice_facts i (h := fun θ' : ℝ => h θ' / Real.sin (2 * θ')) hsmF).1
  intro θ hθ
  rw [hfun]
  exact hrefl θ hθ

lemma far_sq_Dth1Iter_divSin_reflSlice_eq (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
        = (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ)) ^ 2 := by
  intro θ hθ
  rw [far_Dth1Iter_divSin_reflSlice_eq i hsm θ hθ, mul_pow, far_neg_one_pow_sq i, one_mul]

/-! ### Measure-theoretic reflection facts on `Iθ` -/

lemma far_measurePreserving_reflθ :
    MeasureTheory.MeasurePreserving (fun θ : ℝ => Real.pi / 2 - θ) volume volume := by
  have h := (measurePreserving_add_left volume (Real.pi / 2)).comp
    (Measure.measurePreserving_neg volume)
  convert h using 1
  ext x
  simp [sub_eq_add_neg]

lemma far_measurableEmbedding_reflθ : MeasurableEmbedding (fun θ : ℝ => Real.pi / 2 - θ) := by
  have h := (Homeomorph.subLeft (Real.pi / 2) : ℝ ≃ₜ ℝ).measurableEmbedding
  convert h using 1
  ext x
  simp

/-- The reflection maps `Iθ` to itself. -/
lemma far_preimage_Iθ : (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' Work.Spaces.Iθ = Work.Spaces.Iθ := by
  ext x
  simp only [Set.mem_preimage, Work.Spaces.Iθ, Set.mem_Icc]
  constructor <;> intro hx <;> constructor <;> linarith [Real.pi_pos, hx.1, hx.2]

/-- Reflection invariance of `IntegrableOn` on `Iθ`. -/
lemma far_integrableOn_reflθ (F : ℝ → ℝ) :
    IntegrableOn (fun θ => F (Real.pi / 2 - θ)) Work.Spaces.Iθ ↔ IntegrableOn F Work.Spaces.Iθ := by
  have h := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage far_measurePreserving_reflθ
    far_measurableEmbedding_reflθ (f := F) (s := Work.Spaces.Iθ)
  rw [far_preimage_Iθ] at h
  exact h

/-- Reflection invariance of the integral over `Iθ`. -/
lemma far_integral_reflθ (F : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, F (Real.pi / 2 - θ)) = ∫ θ in Work.Spaces.Iθ, F θ := by
  have hpp : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h1 : (∫ θ in Work.Spaces.Iθ, F (Real.pi / 2 - θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), F (Real.pi / 2 - θ) := by
    rw [Work.Spaces.Iθ, intervalIntegral.integral_of_le hpp,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h2 : (∫ θ in Work.Spaces.Iθ, F θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
    rw [Work.Spaces.Iθ, intervalIntegral.integral_of_le hpp,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h1, h2]
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
    (d := Real.pi / 2) (f := F)
  simpa using h

/-- Equality on the open interval upgrades to almost-everywhere equality on `Iθ`
(the two endpoints form a null set). -/
lemma far_ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Ioo 0 (Real.pi / 2))) :
    f =ᵐ[volume.restrict Work.Spaces.Iθ] g := by
  have hnull : volume (Work.Spaces.Iθ \ Set.Ioo 0 (Real.pi / 2)) = 0 := by
    have hsub : Work.Spaces.Iθ \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      obtain ⟨hxI, hxO⟩ := hx
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
      simp only [Set.mem_Ioo, not_and_or] at hxO
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hxO with h' | h'
      · left; linarith [hxI.1]
      · right; linarith [hxI.2]
    refine measure_mono_null hsub ?_
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by ext x; simp [or_comm]]
    rw [measure_union_null_iff]
    exact ⟨measure_singleton 0, measure_singleton (Real.pi / 2)⟩
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc,
    MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_ofPred_eq, not_imp] at hx
  exact ⟨hx.1, fun hxO => hx.2 (h hxO)⟩

/-! ### The data integrals of the reflected slice -/

lemma far_integrand_ae (m : ℕ) (c : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (fun θ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
    (fun θ => (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - θ))) ^ c) := by
  refine far_ae_eq_of_eqOn_Ioo ?_
  intro θ hθ
  change (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c
      = (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - θ))) ^ c
  rw [far_sq_Dth1Iter_deriv_reflSlice_eq m hsm θ hθ, sin_two_reflSlice]

lemma far_integrand_integrable (m : ℕ) (c : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ c)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c) Work.Spaces.Iθ := by
  have hbase : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) (Real.pi / 2 - θ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - θ))) ^ c) Work.Spaces.Iθ :=
    (far_integrableOn_reflθ
      (fun θ' : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ') ^ 2 * (Real.sin (2 * θ')) ^ c)).2 hint
  exact hbase.congr_fun_ae (far_integrand_ae m c hsm).symm

lemma far_integrand_integral_eq (m : ℕ) (c : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c)
      = ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ c := by
  rw [MeasureTheory.setIntegral_congr_ae (s := Work.Spaces.Iθ) measurableSet_Icc
    ((MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc).mp
      (far_integrand_ae m c hsm))]
  exact far_integral_reflθ
    (fun θ' : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ') ^ 2 * (Real.sin (2 * θ')) ^ c)

lemma far_data_eta_integrable {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDen : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun θ' => h (Real.pi / 2 - θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  simpa using far_integrand_integrable 0 (-(Work.Spaces.eta)) hsm hDen

lemma far_data_gam_integrable (m : ℕ) (α : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hDen : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
  far_integrand_integrable m (-(Work.Spaces.gam α)) hsm hDen

lemma far_data_eta_integral_eq {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => h (Real.pi / 2 - θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  simpa using far_integrand_integral_eq 0 (-(Work.Spaces.eta)) hsm

lemma far_data_gam_integral_eq (m : ℕ) (α : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  far_integrand_integral_eq m (-(Work.Spaces.gam α)) hsm

/-! ### Transport of the left-hand side to the near region -/

/-- The far-region integral of the level-`i` quotient slice equals the near-region integral of
the level-`i` quotient slice of the *reflected* slice. -/
lemma far_nearLHS_eq (i : ℕ) (α : ℝ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2),
        (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in (0 : ℝ)..(Real.pi / 8),
        (Work.Elliptic.Dth1Iter i (fun θ => h (Real.pi / 2 - θ) / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hcv := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 8)
    (d := Real.pi / 2)
    (f := fun θ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
  rw [show Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 by ring, sub_zero] at hcv
  rw [← hcv]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x hx
  have hxIoo : x ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 8)] at hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  change (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - x)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - x))) ^ (-(Work.Spaces.gam α))
      = (Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) x) ^ 2
        * (Real.sin (2 * x)) ^ (-(Work.Spaces.gam α))
  rw [← far_sq_Dth1Iter_divSin_reflSlice_eq i hsm x hxIoo, sin_two_reflSlice]

/-- **The far-region bound for the left-hand side of `DivisionBySin`** (the mirror image of
`nearRegionLHS_i` under `θ ↦ π/2 - θ`).

There is a universal constant `C` such that: for every `0 < α ≤ 1` and every slice `h` of class
`C^∞` on `(0,π/2)` with `h(θ) → 0` at both endpoints and with `∫_{Iθ}(∂_θh)² sin(2θ)^{-η}` honest
(`η = 99/100`, `γ = 1+α/10`, `Iθ = [0,π/2]`, `D_θ^m = Work.Elliptic.Dth1Iter m`), and for every
`1 ≤ i ≤ 4` such that `∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ}` is honest for all `1 ≤ m ≤ i`:

  `∫_{3π/8}^{π/2} (D_θ^i (fun θ => h θ / sin(2θ)) θ)² sin(2θ)^{-γ} dθ
      ≤ C (∫_{Iθ}(∂_θh)² sin(2θ)^{-η} + Σ_{1≤m≤i} ∫_{Iθ}(D_θ^m(∂_θh))² sin(2θ)^{-γ})`.

ROUTE.  Apply **`nearRegionLHS_i`** (same workspace, `Submission/Work/FTS/H2/DivQ/nearRegionLHS_i.lean`,
whose data hypothesis is `∀ m ≤ i` — the strengthened `nearRegionLHS` is *not* applicable here) to
the reflected slice `g := fun θ => h (π/2 - θ)`, using `reflSlice_facts`
(`Submission/Work/FTS/H2/DivQ/reflSlice_facts.lean`):

* `sin(2(π/2-θ)) = sin(2θ)`, and `∫_{3π/8}^{π/2}F = ∫_0^{π/8}F∘refl` by the change of variables
  `θ ↦ π/2 - θ` (`intervalIntegral.integral_comp_sub_left`);
* `g/sin(2·) = (h/sin(2·)) ∘ refl`, and `D_θ^i (u ∘ refl) = (-1)^i (D_θ^i u) ∘ refl`
  (`reflSlice_facts`), so the two squared integrands agree under the substitution;
* the data of `g` are those of `h` (`D_θ^m(∂_θg) = -(D_θ^m(∂_θh)) ∘ refl`, from `reflSlice_facts`
  at `i = 1` divided by `sin(2θ) ≠ 0` on `(0,π/2)` and then iterated), and
  `∫_{Iθ} G (π/2-θ) dθ = ∫_{Iθ} G θ dθ` by the second conjunct of `reflSlice_facts`, so the data
  integrals of `g` equal those of `h`;
* `g(θ) → 0` at `0⁺` is the hypothesis `h(θ) → 0` at `(π/2)⁻`. -/
theorem farRegionLHS :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2),
            (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨Cn, hCnpos, hnear⟩ := nearRegionLHS_i
  refine ⟨Cn, hCnpos, ?_⟩
  intro α h hα0 hα1 hsm hT0 hTpi hDenη i hi hDenγ
  -- smoothness of the reflected slice
  have hsmG : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h (Real.pi / 2 - θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.pi / 2 - θ)
        (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const.sub contDiffOn_id
    exact hsm.comp h2 (fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩)
  -- the reflected slice tends to `0` at `0⁺`
  have hG0 : Filter.Tendsto (fun θ : ℝ => h (Real.pi / 2 - θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0) (𝓝 (Real.pi / 2)) := by
          have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0)
              (𝓝 (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
          simpa using h3
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        simp only [Set.mem_Ioi] at hθ
        exact sub_lt_self _ hθ
    simpa [Function.comp_def] using hTpi.comp h1
  -- integrability of the reflected data
  have hGη := far_data_eta_integrable hsm hDenη
  have hGγ : ∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    fun m hm => far_data_gam_integrable m α hsm (hDenγ m hm)
  have hnearG := hnear α (fun θ : ℝ => h (Real.pi / 2 - θ)) hα0 hα1 hsmG hG0 hGη i hi hGγ
  -- transfer of the left-hand side and of the data integrals
  have hLHS := far_nearLHS_eq i α hsm
  have hη := far_data_eta_integral_eq hsm
  have hγ : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter m (deriv (fun θ' => h (Real.pi / 2 - θ'))) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
      = ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    Finset.sum_congr rfl (fun m _ => far_data_gam_integral_eq m α hsm)
  calc (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2),
        (Work.Elliptic.Dth1Iter i (fun θ => h θ / Real.sin (2 * θ)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = ∫ θ in (0 : ℝ)..(Real.pi / 8),
          (Work.Elliptic.Dth1Iter i (fun θ => h (Real.pi / 2 - θ) / Real.sin (2 * θ)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hLHS
    _ ≤ Cn * ((∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Elliptic.Dth1Iter m (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ'))) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := hnearG
    _ = Cn * ((∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        rw [hη, hγ]

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf1dW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

/-! ## The weighted radial self-pairing with a multiplier

This file proves `dzSelf1dW`: for the radial weight `w z = (1+z)²/z²` and a multiplier `ψ`
with `|ψ| ≤ A`, `|z ψ'| ≤ B` on `(0,∞)`, one has

`|∫_0^∞ w² ψ (z Y') Y| ≤ (3A+B) ∫_0^∞ w² Y²`.

The proof follows `dzSelf1d` (the case `ψ ≡ 1`, constant `2`): the exact identity
`s = z w²` (so `s t = (1+t)⁴/t³`),

`(ψ s Y²)' = (ψ s)' Y² + 2 w² ψ (z Y') Y`, with `(ψ s)' = ψ' s + ψ s'`,

integrated over `[ε, M] ⊂ (0,∞)`, gives the truncated bound `truncBoundW_aux` below; passing
to the limit along the dyadic minimisers of `H = w² Y²` at `0` and the minimisers on
`[k+1, 2k+2]` at `∞` (as furnished by `boundarySeqs`) kills the boundary terms, and the
pointwise bounds `|ψ| ≤ A`, `|z ψ'| ≤ B`, `|s'| ≤ 4 w²` give the constants. -/

/-- The integrand `w(z)² ψ(z) (z ∂_z Y(z)) Y(z)` of the weighted self-pairing. -/
def psiSelfFW (ψ Y : ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)

/-- The truncated form of the weighted self-pairing bound: on `[a,b] ⊂ (0,∞)` one has
`|∫_a^b w² ψ (z Y') Y| ≤ (A/2) (w(b)²Y(b)²b + w(a)²Y(a)²a) + ((B+4A)/2) ∫_a^b w² Y²`,
from the exact derivative `(ψ t (t w(t)²) Y(t)²)' = (ψ' t (t w t²) + ψ t (t w t²)') Y t²
+ 2 w t² ψ t (z Y') Y`, the FTC on `[a,b]`, and `|t w t²'| ≤ 4 w t²`, `|ψ| ≤ A`, `|t ψ'| ≤ B`. -/
theorem truncBoundW_aux {ψ Y : ℝ → ℝ} {A B : ℝ}
    (hψsm : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hψA : ∀ z ∈ Set.Ioi (0 : ℝ), |ψ z| ≤ A)
    (hψB : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ B)
    (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
      ≤ (A / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
            + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + ((B + 4 * A) / 2) * ∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have hA0 : 0 ≤ A := by
    have h1 : |ψ 1| ≤ A := hψA 1 (by norm_num)
    have h2 : (0 : ℝ) ≤ |ψ 1| := abs_nonneg _
    linarith
  have hB0 : 0 ≤ B := by
    have h1 : |(1 : ℝ) * deriv ψ 1| ≤ B := hψB 1 (by norm_num)
    have h2 : (0 : ℝ) ≤ |(1 : ℝ) * deriv ψ 1| := abs_nonneg _
    linarith
  have hIoc1 : (∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z) :=
    (intervalIntegral.integral_of_le hab).symm
  have hIoc2 : (∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    (intervalIntegral.integral_of_le hab).symm
  rw [hIoc1, hIoc2]
  have huI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hYd : ∀ z ∈ Set.Icc a b, HasDerivAt Y (deriv Y z) z := fun z hz =>
    ((hY.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hz))).hasDerivAt
  have hψd : ∀ z ∈ Set.Icc a b, HasDerivAt ψ (deriv ψ z) z := fun z hz =>
    ((hψsm.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hz))).hasDerivAt
  have hYc : ContinuousOn Y (Set.Icc a b) := (hY.continuousOn).mono hsub
  have hψc : ContinuousOn ψ (Set.Icc a b) := (hψsm.continuousOn).mono hsub
  have hYdc : ContinuousOn (deriv Y) (Set.Icc a b) :=
    (hY.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hψdc : ContinuousOn (deriv ψ) (Set.Icc a b) :=
    (hψsm.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b)
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hW'c : ContinuousOn (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hInt : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → IntervalIntegrable f volume a b :=
    fun f hf => (show ContinuousOn f (Set.uIcc a b) from by rw [huI]; exact hf).intervalIntegrable
  have habsW' : ∀ z ∈ Set.Icc a b,
      |((1 + z) ^ 3 * (z - 3)) / z ^ 4| ≤ 4 * (Work.Spaces.w z) ^ 2 :=
    fun z hz => abs_deriv_tmul_w_sq_le (hsub hz)
  have hWd : ∀ z ∈ Set.Icc a b, HasDerivAt (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      (((1 + z) ^ 3 * (z - 3)) / z ^ 4) z := fun z hz => deriv_tmul_w_sq (hsub hz)
  -- the derivative of `t ↦ ψ t * (t (w t)²) * (Y t)²`
  have hGd : ∀ z ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2) * (Y t) ^ 2)
        ((ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
            + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2
          + 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))) z := by
    intro z hz
    rw [huI] at hz
    have h1 : HasDerivAt (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2))
        (deriv ψ z * (z * (Work.Spaces.w z) ^ 2)
          + ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)) z :=
      (hψd z hz).mul (hWd z hz)
    have h2 := (hYd z hz).pow 2
    have h3 := h1.mul h2
    have hfun : (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2) * (Y t) ^ 2)
        = (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2)) * (fun t : ℝ => (Y t) ^ 2) :=
      rfl
    rw [hfun]
    convert h3 using 1
    simp only [Pi.pow_apply]
    ring
  have hcont1 : ContinuousOn (fun z : ℝ => (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
      + deriv ψ z * (z * (Work.Spaces.w z) ^ 2))) (Set.Icc a b) :=
    (hψc.mul hW'c).add (hψdc.mul (continuousOn_id.mul (hw.pow 2)))
  have hcont2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ψ z
      * ((z * deriv Y z) * Y z)) (Set.Icc a b) :=
    ((hw.pow 2).mul hψc).mul ((continuousOn_id.mul hYdc).mul hYc)
  have hIntI1 : IntervalIntegrable
      (fun z : ℝ => (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2) volume a b :=
    hInt _ (hcont1.mul (hYc.pow 2))
  have hIntI2 : IntervalIntegrable
      (fun z : ℝ => 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))) volume a b :=
    hInt _ (continuousOn_const.mul hcont2)
  have hFTC : ∫ z in a..b, ((ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)))
      = ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
        - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro z hz; exact hGd z hz
    · exact hIntI1.add hIntI2
  have hsplit : (∫ z in a..b, ((ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))))
      = (∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2)
        + 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)) := by
    rw [intervalIntegral.integral_add hIntI1 hIntI2, intervalIntegral.integral_const_mul]
  have hI1 : |∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
        + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2|
      ≤ (B + 4 * A) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
    calc |∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2|
        ≤ ∫ z in a..b, |(ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ z in a..b, |(ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2))| * (Y z) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro z _
          dsimp only
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Y z))]
      _ ≤ ∫ z in a..b, (B + 4 * A) * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          apply intervalIntegral.integral_mono_on hab
          · exact hInt _ (hcont1.abs.mul (hYc.pow 2))
          · exact hInt _ (continuousOn_const.mul ((hw.pow 2).mul (hYc.pow 2)))
          · intro z hz
            have hzpos : z ∈ Set.Ioi (0 : ℝ) := hsub hz
            have h1 : |ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                ≤ A * (4 * (Work.Spaces.w z) ^ 2) := by
              rw [abs_mul]
              calc |ψ z| * |((1 + z) ^ 3 * (z - 3)) / z ^ 4|
                  ≤ A * |((1 + z) ^ 3 * (z - 3)) / z ^ 4| :=
                    mul_le_mul_of_nonneg_right (hψA z hzpos) (abs_nonneg _)
                _ ≤ A * (4 * (Work.Spaces.w z) ^ 2) :=
                    mul_le_mul_of_nonneg_left (habsW' z hz) hA0
            have h2 : |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|
                ≤ B * (Work.Spaces.w z) ^ 2 := by
              have hwz : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
              calc |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|
                  = |z * deriv ψ z| * (Work.Spaces.w z) ^ 2 := by
                    rw [show deriv ψ z * (z * (Work.Spaces.w z) ^ 2)
                        = (z * deriv ψ z) * (Work.Spaces.w z) ^ 2 from by ring]
                    rw [abs_mul, abs_of_nonneg hwz]
                _ ≤ B * (Work.Spaces.w z) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hψB z hzpos) hwz
            have hsum : |ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                + |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|
                ≤ (B + 4 * A) * (Work.Spaces.w z) ^ 2 := by
              linarith [h1, h2]
            calc |ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
                    + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)| * (Y z) ^ 2
                ≤ (|ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                    + |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|) * (Y z) ^ 2 :=
                  mul_le_mul_of_nonneg_right (abs_add_le _ _) (sq_nonneg (Y z))
              _ ≤ (B + 4 * A) * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
                  calc (|ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                        + |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|) * (Y z) ^ 2
                      ≤ ((B + 4 * A) * (Work.Spaces.w z) ^ 2) * (Y z) ^ 2 :=
                        mul_le_mul_of_nonneg_right hsum (sq_nonneg (Y z))
                    _ = (B + 4 * A) * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by ring
      _ = (B + 4 * A) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
  have hkey : 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))
      = (ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
          - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
        - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
            + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2 := by
    linarith [hFTC, hsplit]
  have hI2 : (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))
      = (1 / 2) * ((ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
          - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2) := by
    linarith [hkey]
  rw [hI2]
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hBb : |ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2|
      ≤ A * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b) := by
    have h1 : |ψ b| ≤ A := hψA b hbpos
    have h2 : (0 : ℝ) ≤ ((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b := by positivity
    have h3 : |ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2|
        = |ψ b| * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Y b)),
        abs_of_nonneg (mul_nonneg hbpos.le (sq_nonneg (Work.Spaces.w b)))]
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 h2
  have hBa : |ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2|
      ≤ A * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a) := by
    have h1 : |ψ a| ≤ A := hψA a ha
    have h2 : (0 : ℝ) ≤ ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a := by positivity
    have h3 : |ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2|
        = |ψ a| * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Y a)),
        abs_of_nonneg (mul_nonneg ha.le (sq_nonneg (Work.Spaces.w a)))]
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 h2
  have habstri : ∀ u v : ℝ, |u - v| ≤ |u| + |v| := by
    intro u v
    have h := abs_add_le u (-v)
    simpa [sub_eq_add_neg, abs_neg] using h
  have hBd : |(ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
        - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)|
      ≤ A * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b)
        + A * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a) := by
    have hxb := abs_le.mp hBb
    have hxa := abs_le.mp hBa
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hxb.1, hxb.2, hxa.1, hxa.2]
  calc |(1 / 2) * ((ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
          - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2)|
      = (1 / 2) * |(ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
          - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2) * (|(ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)|
          + |∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2|) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply habstri
    _ ≤ (1 / 2) * ((A * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b)
            + A * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a))
          + (B + 4 * A) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hBd, hI1]
    _ = (A / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
          + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + ((B + 4 * A) / 2) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by ring

theorem dzSelf1dW {ψ Y : ℝ → ℝ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hψsm : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hψA : ∀ z ∈ Set.Ioi (0 : ℝ), |ψ z| ≤ A)
    (hψB : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ B)
    (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0))
    (hF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0))
    (hD : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
      (Set.Ioi 0)) :
    |∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
      ≤ (3 * A + B) * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have hHint : IntegrableOn (selfH Y) (Set.Ioi 0) := by
    change IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0)
    exact hF
  have hHnn : ∀ z, 0 ≤ selfH Y z := by
    intro z
    change 0 ≤ (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
    positivity
  have hHnnI : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun z _ => by positivity)
  change |∫ z in Set.Ioi (0 : ℝ), psiSelfFW ψ Y z|
      ≤ (3 * A + B) * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
  by_cases hint : IntegrableOn (psiSelfFW ψ Y) (Set.Ioi 0)
  · obtain ⟨ε, M, hεpos, hεM, hε0, hMtop, hHε, hHM⟩ :=
      boundarySeqs (selfH Y) hHint hHnn
        (fun k => continuousOn_selfH hY (by positivity))
        (fun k => continuousOn_selfH hY (by positivity))
    have hL1 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), psiSelfFW ψ Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, psiSelfFW ψ Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (psiSelfFW ψ Y) hint hεpos hε0 hMtop
    have hL2 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, selfH Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (selfH Y) hHint hεpos hε0 hMtop
    have hk : ∀ k : ℕ, |∫ z in Set.Ioc (ε k) (M k), psiSelfFW ψ Y z|
        ≤ (A / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + ((B + 4 * A) / 2) * ∫ z in Set.Ioc (ε k) (M k), selfH Y z := by
      intro k
      have htb := truncBoundW_aux (ψ := ψ) (Y := Y) (A := A) (B := B)
        hψsm hψA hψB hY (hεpos k) (hεM k)
      simpa only [psiSelfFW, selfH] using htb
    have hbound : Tendsto
        (fun k => (A / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + ((B + 4 * A) / 2) * ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z)) := by
      have hmid : Tendsto
          (fun k => (A / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)) atTop (𝓝 0) := by
        have h := (hHM.add hHε).const_mul (A / 2)
        simpa using h
      have h2 : Tendsto (fun k => ((B + 4 * A) / 2) * ∫ z in Set.Ioc (ε k) (M k), selfH Y z)
          atTop (𝓝 (((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z)) :=
        hL2.const_mul _
      simpa using hmid.add h2
    have hmain : |∫ z in Set.Ioi 0, psiSelfFW ψ Y z|
        ≤ ((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z :=
      le_of_tendsto_of_tendsto' hL1.abs hbound hk
    have hcoef : (B + 4 * A) / 2 ≤ 3 * A + B := by linarith
    calc |∫ z in Set.Ioi 0, psiSelfFW ψ Y z|
        ≤ ((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z := hmain
      _ = ((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
          simp only [selfH]
      _ ≤ (3 * A + B) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hHnnI
  · rw [integral_undef hint, abs_zero]
    exact mul_nonneg (by linarith) hHnnI

end

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The left half `(0, π/4]` -/

/-- **The weighted Hardy inequality on the left half `(0,π/4]`.**

For `0 < β ≤ 1`, `f` of class `C¹` on `(0,π/2)` whose `sin(2·)`-weighted squared derivative is
integrable on `(0,π/4]`:

`∫_{(0,π/4]} f² sin(2θ)^{β-1} ≤ (4/β²)(π/4)² ∫_{(0,π/4]} (f')² sin(2θ)^{1-β} + π/(2β) f(π/4)²`,

and the left-hand integrand is integrable. -/
theorem hardy_half_left_open {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
      (Set.Ioc (0 : ℝ) (Real.pi / 4))) :
    IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        (Set.Ioc (0 : ℝ) (Real.pi / 4)) ∧
      (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hqpos : (0 : ℝ) < Real.pi / 4 := by linarith
  have hqle : Real.pi / 4 ≤ Real.pi / 2 := by linarith
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  -- `sin (2θ) > 0` on `[δ, π/4]` for `0 < δ`
  have hsinpos : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), ∀ θ ∈ Set.Icc δ (Real.pi / 4),
      0 < Real.sin (2 * θ) := by
    intro δ hδ θ hθ
    exact sin_two_pos_of_lt_half (by linarith [hδ.1, hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  -- continuity of `f` and of `deriv f` on `[δ, π/4]`
  have hfcont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), ContinuousOn f (Set.Icc δ (Real.pi / 4)) :=
    fun δ hδ => hsm.continuousOn.mono (fun x hx =>
      ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 hπ4lt⟩)
  have hdfcont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (deriv f) (Set.Icc δ (Real.pi / 4)) :=
    fun δ hδ => (hsm.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
      (fun x hx => ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 hπ4lt⟩)
  have hsincont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (β - 1)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos δ hδ θ hθ)))
  have hsincont' : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - β)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos δ hδ θ hθ)))
  have hthcont : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => θ ^ (β - 1)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact continuousOn_id.rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (lt_of_lt_of_le hδ.1 hθ.1)))
  have hthcont' : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      ContinuousOn (fun θ : ℝ => θ ^ (β + 1)) (Set.Icc δ (Real.pi / 4)) := by
    intro δ hδ
    exact continuousOn_id.rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (lt_of_lt_of_le hδ.1 hθ.1)))
  -- interval integrability of the four integrands on `[δ, π/4]`
  have hIIF : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        volume δ (Real.pi / 4) :=
    fun δ hδ => (((hfcont δ hδ).pow 2).mul (hsincont δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  have hIIFp : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (f θ) ^ 2 * θ ^ (β - 1)) volume δ (Real.pi / 4) :=
    fun δ hδ => (((hfcont δ hδ).pow 2).mul (hthcont δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  have hIIG : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        volume δ (Real.pi / 4) :=
    fun δ hδ => (((hdfcont δ hδ).pow 2).mul (hsincont' δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  have hIIGp : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      IntervalIntegrable (fun θ : ℝ => (deriv f θ) ^ 2 * θ ^ (β + 1))
        volume δ (Real.pi / 4) :=
    fun δ hδ => (((hdfcont δ hδ).pow 2).mul (hthcont' δ hδ)).intervalIntegrable_of_Icc hδ.2.le
  -- ## the per-`δ` bound
  have hdelta : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (∫ θ in Set.Ioc δ (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc δ (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
    intro δ hδ
    have hδle : δ ≤ Real.pi / 4 := hδ.2.le
    have hsub : Set.Icc δ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 hπ4lt⟩
    -- the power-weight Hardy inequality on `[δ, π/4]`
    have hA := power_hardy_interval (c := β - 1) (ε := δ) (b := Real.pi / 4) (f := f)
      (by linarith) hδ.1 hδ.2 (hsm.mono hsub)
    rw [show β - 1 + 1 = β from by ring, show β - 1 + 2 = β + 1 from by ring] at hA
    -- in interval-integral form
    have hA' : (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1))
        ≤ 4 / β ^ 2 * (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
          + 2 / β * (f (Real.pi / 4)) ^ 2 * (Real.pi / 4) ^ β := by
      simpa only [intervalIntegral.integral_of_le hδle] using hA
    -- comparison 1 : `sin(2θ)^{β-1} ≤ (4/π)^{β-1} θ^{β-1}`
    have hc1 : (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ (4 / Real.pi) ^ (β - 1) * (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1)) := by
      have h := intervalIntegral.integral_mono_on_of_le_Ioo hδle (hIIF δ hδ)
        ((hIIFp δ hδ).const_mul ((4 / Real.pi) ^ (β - 1))) (fun θ hθ => ?_)
      · rwa [intervalIntegral.integral_const_mul] at h
      · have hpt := Work.FTS.H2.Transport3Aux.sin_rpow_sub_le_theta (β := β) hβ1
          (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) from
            ⟨lt_trans hδ.1 hθ.1, hθ.2⟩)
        calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1)
            ≤ (f θ) ^ 2 * ((4 / Real.pi) ^ (β - 1) * θ ^ (β - 1)) :=
              mul_le_mul_of_nonneg_left hpt (sq_nonneg _)
          _ = (4 / Real.pi) ^ (β - 1) * ((f θ) ^ 2 * θ ^ (β - 1)) := by ring
    -- comparison 2 : `θ^{β+1} ≤ (π/4)^{β+1} sin(2θ)^{1-β}`
    have hc2 : (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
        ≤ (Real.pi / 4) ^ (β + 1)
            * (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by
      have h := intervalIntegral.integral_mono_on_of_le_Ioo hδle (hIIGp δ hδ)
        ((hIIG δ hδ).const_mul ((Real.pi / 4) ^ (β + 1))) (fun θ hθ => ?_)
      · rwa [intervalIntegral.integral_const_mul] at h
      · have hpt := Work.FTS.H2.Transport3Aux.theta_rpow_le_sin_rpow (β := β) hβ.le
          (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) from
            ⟨lt_trans hδ.1 hθ.1, hθ.2⟩)
        calc (deriv f θ) ^ 2 * θ ^ (β + 1)
            ≤ (deriv f θ) ^ 2 * ((Real.pi / 4) ^ (β + 1) * (Real.sin (2 * θ)) ^ (1 - β)) :=
              mul_le_mul_of_nonneg_left hpt (sq_nonneg _)
          _ = (Real.pi / 4) ^ (β + 1)
                * ((deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) := by ring
    -- the constants
    have hcpos : (0 : ℝ) ≤ (4 / Real.pi) ^ (β - 1) := Real.rpow_nonneg (by positivity) _
    have hdpos : (0 : ℝ) ≤ 4 / β ^ 2 := by positivity
    have hcomb : (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in δ..(Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
      have hdpos2 : (0 : ℝ) ≤ 4 / β ^ 2 := by positivity
      calc (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
          ≤ (4 / Real.pi) ^ (β - 1)
              * (∫ θ in δ..(Real.pi / 4), (f θ) ^ 2 * θ ^ (β - 1)) := hc1
        _ ≤ (4 / Real.pi) ^ (β - 1)
              * (4 / β ^ 2 * (∫ θ in δ..(Real.pi / 4), (deriv f θ) ^ 2 * θ ^ (β + 1))
                + 2 / β * (f (Real.pi / 4)) ^ 2 * (Real.pi / 4) ^ β) :=
              mul_le_mul_of_nonneg_left hA' hcpos
        _ ≤ (4 / Real.pi) ^ (β - 1)
              * (4 / β ^ 2 * ((Real.pi / 4) ^ (β + 1)
                  * (∫ θ in δ..(Real.pi / 4),
                      (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)))
                + 2 / β * (f (Real.pi / 4)) ^ 2 * (Real.pi / 4) ^ β) := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hcpos
              exact mul_le_mul_of_nonneg_left hc2 hdpos2
        _ = (4 / Real.pi) ^ (β - 1) * (4 / β ^ 2) * (Real.pi / 4) ^ (β + 1)
              * (∫ θ in δ..(Real.pi / 4),
                  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + (4 / Real.pi) ^ (β - 1) * (2 / β) * (Real.pi / 4) ^ β
              * (f (Real.pi / 4)) ^ 2 := by ring
        _ = 4 / β ^ 2 * (Real.pi / 4) ^ 2
              * (∫ θ in δ..(Real.pi / 4),
                  (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
              rw [Work.FTS.H2.Transport3Aux.quarter_const_mul β,
                Work.FTS.H2.Transport3Aux.bdry_const_mul hβne]
    simpa only [intervalIntegral.integral_of_le hδle] using hcomb
  -- ## integrability of the left-hand integrand
  have hFcont_Ioo : ContinuousOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    ((hsm.continuousOn.mono (fun x hx =>
        ⟨hx.1, lt_trans hx.2 hπ4lt⟩)).pow 2).mul
      ((Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_lt_half hθ.1 (lt_trans hθ.2 hπ4lt)))))
  have hGnn : ∀ x ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      0 ≤ (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) := fun x hx =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2, Real.pi_pos])) _)
  have hunif : ∀ δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      (∫ θ in Set.Ioc δ (Real.pi / 4), (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
        ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2
            * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
          + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2 := by
    intro δ hδ
    have hmono : (∫ θ in Set.Ioc δ (Real.pi / 4),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        ≤ ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
            (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β) :=
      setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hGnn))
        (Ioc_subset_Ioc_left hδ.1.le).eventuallyLE
    have h1 := mul_le_mul_of_nonneg_left hmono
      (by positivity : (0 : ℝ) ≤ 4 / β ^ 2 * (Real.pi / 4) ^ 2)
    linarith [hdelta δ hδ, h1]
  have hFint_Ioo : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    refine Work.FTS.EllSol.VthAux.traceAux.integrableOn_of_forall_Ioc_le
      (C := 4 / β ^ 2 * (Real.pi / 4) ^ 2
        * (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4),
            (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
        + Real.pi / (2 * β) * (f (Real.pi / 4)) ^ 2) hqpos ?_ hFcont_Ioo ?_ hunif
    · intro δ hδ
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.2.le).mp (hIIF δ hδ)
    · exact Filter.Eventually.of_forall (fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
            (by linarith [hx.2, Real.pi_pos])) _))
  have hFint_Ioc : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (β - 1))
      (Set.Ioc (0 : ℝ) (Real.pi / 4)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hFint_Ioo
  refine ⟨hFint_Ioc, ?_⟩
  -- ## pass to the limit `δ → 0⁺`
  exact setIntegral_Ioc_le_of_uniform_bound hqpos hFint_Ioc hint (fun δ hδ => hdelta δ hδ)

end

end Work.FTS.StrongPersist.N6Trans.SixRoute
end

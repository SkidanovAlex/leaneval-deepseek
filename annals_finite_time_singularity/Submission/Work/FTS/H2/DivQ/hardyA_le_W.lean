import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.DivQ.divSinPrimitive
import Submission.Work.FTS.H2.DivQ.rpowSq_ibp
import Submission.Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc
import Submission.Work.FTS.H2.DivQ.primitiveDerivData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

/-! ## Elementary helpers -/

/-- `x ^ p * (x ^ m * A) ^ 2 = x ^ (p + 2m) * A ^ 2` for `x > 0` and a natural power `m`. -/
private lemma rpow_natpow_mul_sq {x A : ℝ} (hx : 0 < x) (p : ℝ) (m : ℕ) :
    x ^ p * (x ^ m * A) ^ 2 = x ^ (p + 2 * (m : ℝ)) * A ^ 2 := by
  have hm : (x ^ m) ^ 2 = x ^ (2 * (m : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast x (m * 2)]
    congr 1
    push_cast
    ring
  rw [mul_pow, hm, Real.rpow_add hx]
  ring

/-- The rpow rearrangement used at the top level `k + 1`. -/
private lemma rpow_shift1 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ - 2) * (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ - 2) (k + 1)
  have e : -γ - 2 + 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - γ := by push_cast; ring
  rw [e] at h
  exact h

/-- The rpow rearrangement of the boundary term `ε ^ (-γ-1) G(ε)²`. -/
private lemma rpow_shift2 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ - 1) * (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ - 1) (k + 1)
  have e : -γ - 1 + 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 - γ := by push_cast; ring
  rw [e] at h
  exact h

/-- The rpow rearrangement of the weight `t ^ (-γ) * ψ(t)²`. -/
private lemma rpow_shift3 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ) * (x ^ k * A) ^ 2 = x ^ (2 * (k : ℝ) - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ) k
  have e : -γ + 2 * ((k : ℕ) : ℝ) = 2 * (k : ℝ) - γ := by ring
  rw [e] at h
  exact h

/-- Pointwise AM–GM with the Hardy weights: for `x > 0` and `1 + γ > 0`,
`2 x^{-γ-1} A B ≤ ((1+γ)/2) x^{-γ-2} A² + (2/(1+γ)) x^{-γ} B²`. -/
private lemma amgm_hardy {γ x A B : ℝ} (hx : 0 < x) (hc : 0 < 1 + γ) :
    2 * (x ^ (-γ - 1) * A * B)
      ≤ (1 + γ) / 2 * (x ^ (-γ - 2) * A ^ 2) + (2 / (1 + γ)) * (x ^ (-γ) * B ^ 2) := by
  have h1 : (x ^ ((-γ - 2) / 2) * A) ^ 2 = x ^ (-γ - 2) * A ^ 2 := by
    rw [mul_pow, pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have h2 : (x ^ (-γ / 2) * B) ^ 2 = x ^ (-γ) * B ^ 2 := by
    rw [mul_pow, pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have hdiv : ((x ^ (-γ / 2) * B) ^ 2) / ((1 + γ) / 2)
      = (2 / (1 + γ)) * (x ^ (-γ) * B ^ 2) := by
    rw [h2]
    field_simp
  have hxx : x ^ ((-γ - 2) / 2) * x ^ (-γ / 2) = x ^ (-γ - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hL : 2 * ((x ^ ((-γ - 2) / 2) * A) * (x ^ (-γ / 2) * B))
      = 2 * (x ^ (-γ - 1) * A * B) := by
    rw [← hxx]
    ring
  have ham := two_mul_le_mul_sq_add_div_sq (a := (1 + γ) / 2)
    (u := x ^ ((-γ - 2) / 2) * A) (v := x ^ (-γ / 2) * B) (by linarith)
  rw [hL, h1, hdiv] at ham
  exact ham

/-- Every iterated derivative of a function of class `C^∞` on the open interval `(0,x₁)` is
continuous there. -/
private theorem iteratedDeriv_continuousOn_Ioo' {g : ℝ → ℝ} {x₁ : ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioo 0 x₁)) (m : ℕ) :
    ContinuousOn (fun x : ℝ => iteratedDeriv m g x) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have hcont : ContinuousOn (iteratedDerivWithin m g (Set.Ioo (0 : ℝ) x₁)) (Set.Ioo 0 x₁) :=
    hg.continuousOn_iteratedDerivWithin (by simp) hs
  exact hcont.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- Continuity of a weighted product on a compact subinterval. -/
private lemma contOn_rpow_mul {a b p : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc a b)) :
    ContinuousOn (fun t : ℝ => t ^ p * F t) (Set.Icc a b) :=
  (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1))).mul hF

/-! ## The truncated Hardy bound -/

/-- **The core estimate.** -/
private theorem hardyA_trunc_bound (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hf0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x,
          t ^ (2 * (k : ℝ) - γ) * (iteratedDeriv k (fun z : ℝ => f z / z) t) ^ 2)
        ≤ 6 * (∫ t in (0 : ℝ)..x₁,
            t ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f t) ^ 2) / (1 + γ) ^ 2 := by
  intro y x hy hyx hxx₁
  set v : ℝ → ℝ := fun s => iteratedDeriv k (fun z : ℝ => f z / z) s with hv
  set ψ : ℝ → ℝ := fun s => s ^ k * iteratedDeriv (k + 1) f s with hψ
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ψ s with hG
  set u : ℝ → ℝ := fun s => s ^ (2 * (k : ℝ) - γ) * v s ^ 2 with hu
  set w : ℝ → ℝ := fun s => s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hw
  set Btot : ℝ := ∫ t in (0 : ℝ)..x₁, w t with hBtot
  have hc : 0 < 1 + γ := by linarith
  -- § continuity of `v` and `ψ` on the open interval
  have hgm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).div contDiffOn_id fun z hz => ne_of_gt hz.1
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact iteratedDeriv_continuousOn_Ioo' hgm k
  have hψcont : ContinuousOn ψ (Set.Ioo 0 x₁) := by
    rw [hψ]
    exact (continuousOn_id.pow k).mul
      (iteratedDeriv_continuousOn_Ioo' (hf.mono Set.Ioo_subset_Ioc_self) (k + 1))
  -- § primitive data
  obtain ⟨_, hGcont, hGderiv⟩ := primitiveDerivData k γ x₁ hx₁ hγ f hf hB
  have hGcont' : ContinuousOn G (Set.Icc 0 x₁) := hGcont
  have hGderiv' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, HasDerivAt G (ψ t) t := hGderiv
  -- § the two ingredients coming from `divSinPrimitive`
  obtain ⟨hident, hbnd⟩ := divSinPrimitive k γ x₁ hx₁ hγ f hf hf0 hB
  have hident' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, t ^ (k + 1) * v t = G t :=
    fun t ht => hident t ht
  have hbnd' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁,
      t ^ (2 * (k : ℝ) + 1 - γ) * v t ^ 2 ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..t, w s) :=
    fun t ht => hbnd t ht
  -- § continuity of the integrands on `[y,x]`
  have hGcx : ContinuousOn G (Set.Icc y x) :=
    hGcont'.mono fun t ht => ⟨le_trans (le_of_lt hy) ht.1, le_trans ht.2 (le_of_lt hxx₁)⟩
  have hψcx : ContinuousOn ψ (Set.Icc y x) :=
    hψcont.mono fun t ht => ⟨lt_of_lt_of_le hy ht.1, lt_of_le_of_lt ht.2 hxx₁⟩
  have hdG : ∀ t ∈ Set.Ioo y x, HasDerivAt G (ψ t) t :=
    fun t ht => hGderiv' t ⟨lt_trans hy ht.1, lt_trans ht.2 hxx₁⟩
  -- § the integration by parts
  have hibp := rpowSq_ibp (γ := γ) hy hyx.le hGcx hdG hψcx
  -- § identification of the left-hand integral
  have hEq1 : (∫ t in y..x, t ^ (-γ - 2) * G t ^ 2) = ∫ t in y..x, u t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hyx.le] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
    have htI : t ∈ Set.Ioo (0 : ℝ) x₁ := ⟨ht0, lt_of_le_of_lt ht.2 hxx₁⟩
    rw [← hident' t htI]
    simp only [hu]
    exact rpow_shift1 k ht0
  rw [hEq1] at hibp
  -- § AM–GM
  have hAM1 : 2 * (∫ t in y..x, t ^ (-γ - 1) * G t * ψ t)
      ≤ (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) := by
    have hpt : ∀ t ∈ Set.Icc y x,
        2 * (t ^ (-γ - 1) * G t * ψ t)
          ≤ (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
            + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2) :=
      fun t ht => amgm_hardy (lt_of_lt_of_le hy ht.1) hc
    have hca : ContinuousOn (fun t : ℝ => t ^ (-γ - 2) * G t ^ 2) (Set.Icc y x) :=
      contOn_rpow_mul hy (hGcx.pow 2)
    have hcb : ContinuousOn (fun t : ℝ => t ^ (-γ) * ψ t ^ 2) (Set.Icc y x) :=
      contOn_rpow_mul hy (hψcx.pow 2)
    have hcf : ContinuousOn (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t)) (Set.Icc y x) :=
      ((contOn_rpow_mul hy (hGcx.mul hψcx)).const_mul 2).congr fun t _ => by
        simp only [Pi.mul_apply]
        ring
    have hcg : ContinuousOn
        (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
          + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2)) (Set.Icc y x) :=
      (hca.const_mul _).add (hcb.const_mul _)
    have hif : IntervalIntegrable (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t))
        volume y x := hcf.intervalIntegrable_of_Icc hyx.le
    have hig : IntervalIntegrable
        (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
          + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2)) volume y x :=
      hcg.intervalIntegrable_of_Icc hyx.le
    have hmono := intervalIntegral.integral_mono_on hyx.le hif hig hpt
    have hif1 : IntervalIntegrable (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2))
        volume y x := (hca.const_mul _).intervalIntegrable_of_Icc hyx.le
    have hif2 : IntervalIntegrable (fun t : ℝ => (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2))
        volume y x := (hcb.const_mul _).intervalIntegrable_of_Icc hyx.le
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hif1 hif2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    rw [hEq1] at hmono
    exact hmono
  -- § the `ψ²` integral is dominated by `Btot`
  have hK : (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) ≤ Btot := by
    have heq : (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) = ∫ t in y..x, w t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hψ, hw]
      exact rpow_shift3 k ht0
    rw [heq, hBtot, intervalIntegral.integral_of_le hx₁.le,
      intervalIntegral.integral_of_le hyx.le]
    refine setIntegral_mono_set hB ?_ ?_
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        simp only [hw]
        exact mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _)
    · exact Eventually.of_forall fun t ht =>
        ⟨lt_trans hy ht.1, le_of_lt (lt_of_le_of_lt ht.2 hxx₁)⟩
  -- § the boundary bound at `y`
  have hybd : y ^ (-γ - 1) * G y ^ 2 ≤ Btot / (1 + γ) := by
    have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := ⟨hy, lt_trans hyx hxx₁⟩
    have hb := hbnd' y hyI
    have hInt : (∫ s in (0 : ℝ)..y, w s) ≤ Btot := by
      rw [hBtot, intervalIntegral.integral_of_le hx₁.le,
        intervalIntegral.integral_of_le hy.le]
      refine setIntegral_mono_set hB ?_ ?_
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun t ht => by
          simp only [hw]
          exact mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _)
      · exact Eventually.of_forall fun t ht =>
          ⟨ht.1, le_trans ht.2 (le_of_lt (lt_trans hyx hxx₁))⟩
    rw [← hident' y hyI, rpow_shift2 k hy]
    calc y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2
        ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..y, w s) := hb
      _ ≤ 1 / (1 + γ) * Btot := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = Btot / (1 + γ) := by ring
  -- § assembling
  have hxterm : 0 ≤ x ^ (-γ - 1) * G x ^ 2 :=
    mul_nonneg (Real.rpow_pos_of_pos (lt_trans hy hyx) _).le (sq_nonneg _)
  have hAM1' : 2 * (∫ t in y..x, t ^ (-γ - 1) * G t * ψ t)
      ≤ (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) := hAM1
  have hK' : (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2)
      ≤ (2 / (1 + γ)) * Btot := mul_le_mul_of_nonneg_left hK (by positivity)
  have hstep : (1 + γ) * (∫ t in y..x, u t)
      ≤ y ^ (-γ - 1) * G y ^ 2 + (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * Btot := by
    linarith [hibp, hAM1', hK', hxterm]
  -- § final arithmetic
  have hmult := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 2 * (1 + γ))
  have eL : 2 * (1 + γ) * ((1 + γ) * (∫ t in y..x, u t))
      = 2 * (1 + γ) ^ 2 * (∫ t in y..x, u t) := by ring
  have e4 : 2 * (1 + γ) * (2 / (1 + γ) * Btot) = 4 * Btot := by
    field_simp
    ring
  have eR : 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2 + (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * Btot)
      = 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2) + (1 + γ) ^ 2 * (∫ t in y..x, u t)
        + 4 * Btot := by
    rw [mul_add, mul_add, e4]
    ring
  rw [eL, eR] at hmult
  have hP2 : 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2) ≤ 2 * Btot := by
    have h3 := mul_le_mul_of_nonneg_left hybd (by positivity : (0 : ℝ) ≤ 2 * (1 + γ))
    have e : 2 * (1 + γ) * (Btot / (1 + γ)) = 2 * Btot := by
      field_simp
    rwa [e] at h3
  have h4 : (1 + γ) ^ 2 * (∫ t in y..x, u t) ≤ 6 * Btot := by
    linarith [hmult, hP2]
  have hgoal : (∫ t in y..x, u t)
      ≤ 6 * Btot / (1 + γ) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + γ) ^ 2)]
    linarith [h4]
  exact hgoal

/-- The target theorem (development copy). -/
theorem hardyA_le_W :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (γ x₁ : ℝ), 0 < x₁ → -1 < γ → ∀ f : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2) (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ)
          * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2) (Set.Ioc 0 x₁) ∧
      (∫ x in (0 : ℝ)..x₁,
          x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2)
        ≤ C / (1 + γ) ^ 2 *
          (∫ x in (0 : ℝ)..x₁,
            x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro k γ x₁ hx₁ hγ f hf hf0 hB
  set v : ℝ → ℝ := fun x => iteratedDeriv k (fun y : ℝ => f y / y) x with hv
  set u : ℝ → ℝ := fun x => x ^ (2 * (k : ℝ) - γ) * v x ^ 2 with hu
  set ua : ℝ → ℝ := fun x => |u x| with hua
  set w : ℝ → ℝ := fun x => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2 with hw
  set Btot : ℝ := ∫ x in (0 : ℝ)..x₁, w x with hBtot
  have hgm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).div contDiffOn_id fun z hz => ne_of_gt hz.1
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact iteratedDeriv_continuousOn_Ioo' hgm k
  have hucont : ContinuousOn u (Set.Ioo 0 x₁) := by
    rw [hu]
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hvcont.pow 2)
  have huacont : ContinuousOn ua (Set.Ioo 0 x₁) := by
    rw [hua]
    exact hucont.abs
  have htrunc0 := hardyA_trunc_bound k γ x₁ hx₁ hγ f hf hf0 hB
  have htrunc : ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x, ua t) ≤ 6 * Btot / (1 + γ) ^ 2 := by
    intro y x hy hyx hxx₁
    have heq : (∫ t in y..x, ua t) = ∫ t in y..x, u t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hua]
      exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
    rw [heq]
    exact htrunc0 y x hy hyx hxx₁
  obtain ⟨hua_int, hua_bound⟩ :=
    integrableOn_Ioc_of_trunc hx₁ (fun t => abs_nonneg (u t)) huacont htrunc
  have hu_int : MeasureTheory.IntegrableOn u (Set.Ioc 0 x₁) := by
    refine hua_int.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · exact hu_int
  · have heq_final : (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t
      intro ht
      rw [Set.uIoc_of_le hx₁.le] at ht
      simp only [hua]
      exact (abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _))).symm
    calc (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := heq_final
      _ ≤ 6 * Btot / (1 + γ) ^ 2 := hua_bound
      _ = 6 / (1 + γ) ^ 2 * Btot := by ring

end Work.FTS.H2.DivQ

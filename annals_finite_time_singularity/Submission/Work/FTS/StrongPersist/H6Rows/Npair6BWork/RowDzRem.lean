import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzTerms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Leibniz remainder of the `A · D_z f` flat row

The expansion of `D_z^bD_θ^a(A·D_zf)` with the transport summand deleted, its (a.e.) strong
measurability, and its pointwise bound against the `ℋ⁶`-integrand plus the angular Hardy slot.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

/-- **The Leibniz expansion with the transport term deleted.** -/
theorem rowDz_leib {A f : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        - A z θ * Work.Spaces.mixed (b + 1) a f z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j + 1) (a - i) f z θ)) := by
  intro z θ hz hθ hθ2
  have h := Work.FTS.TransportS.mixed_mul_Dz_open b a A f hA hf z θ hz hθ hθ2
  have h00 : (a.choose 0 : ℝ) * (b.choose 0 : ℝ)
      * (Work.Spaces.mixed 0 0 A z θ * Work.Spaces.mixed (b - 0 + 1) (a - 0) f z θ)
      = A z θ * Work.Spaces.mixed (b + 1) a f z θ := by
    simp only [Nat.choose_zero_right, Nat.sub_zero, Work.Spaces.mixed_zero_left,
      Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero]
    ring
  have hkey : Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
      = A z θ * Work.Spaces.mixed (b + 1) a f z θ
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then (0 : ℝ)
              else (a.choose i : ℝ) * (b.choose j : ℝ)
                * (Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j + 1) (a - i) f z θ)) := by
    rw [h]
    rw [rowDz_dsum_split a b (fun i j => (a.choose i : ℝ) * (b.choose j : ℝ)
      * (Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j + 1) (a - i) f z θ))]
    rw [h00]
  linarith [hkey]

/-- A.e. strong measurability of the mixed derivative of `A·D_zf`. -/
theorem rowDz_Uf_aesm {A f : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hScont : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (a + 1),
      ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ)
          else (a.choose i : ℝ) * (b.choose j : ℝ)
            * (Work.Spaces.mixed j i A p.1 p.2
                * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2)))
      Work.FTS.EllipticEst.Q0 := by
    refine continuousOn_finsetSum _ fun i hi => continuousOn_finsetSum _ fun j hj => ?_
    by_cases h00 : i = 0 ∧ j = 0
    · refine ContinuousOn.congr
        (continuousOn_const (c := (0 : ℝ)) :
          ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0) fun p hp => ?_
      rw [if_pos h00]
    · refine ContinuousOn.congr (ContinuousOn.const_mul
        ((Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hA j i).mul
          (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf (b - j + 1) (a - i)))
        ((a.choose i : ℝ) * (b.choose j : ℝ))) fun p hp => ?_
      rw [if_neg h00]
      rfl
  set pm : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hpm
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2
      * Work.Spaces.mixed (b + 1) a f p.1 p.2) pm := by
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hA.continuousOn
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed (b + 1) a f p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf (b + 1) a)
    exact h2.mul h3
  have hsum : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2
      * Work.Spaces.mixed (b + 1) a f p.1 p.2
      + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A p.1 p.2
                  * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2))) pm :=
    h1.add (Work.Spaces.aesm_of_continuousOn_Qd _ hScont)
  refine hsum.congr ?_
  filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
  have h := rowDz_leib hA hf b a p.1 p.2 hp.1 hp.2.1 hp.2.2
  show A p.1 p.2 * Work.Spaces.mixed (b + 1) a f p.1 p.2
      + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A p.1 p.2
                  * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2))
      = Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
  linarith [h]

/-- The pointwise bound of the Leibniz remainder. -/
theorem rowDz_rem_pt : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K Kf : ℝ) (a b : ℕ) (q : ℝ) (HH : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K → 0 ≤ Kf →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dz (Work.Spaces.pth A) z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf) →
      Work.FTS.EllipticEst.SmoothOpen f →
      a + b ≤ 6 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      (q = Work.Spaces.eta ∨ q = 0 ∨ q = Work.Spaces.gam α) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ k : ℕ, k ≤ 5 →
        canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 ≤ HH z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ HH z θ) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |canonW q z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            - A z θ * Work.Spaces.mixed (b + 1) a f z θ) * Work.Spaces.mixed b a f z θ|
          ≤ C * (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
  obtain ⟨Ct, hCtpos, hterm⟩ := rowDz_term_bound
  refine ⟨64 * Ct + 1, by linarith [hCtpos], ?_⟩
  intro α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hfsm hab hq0 hqγ hqη0
    hqcases hHH hHHnn z θ hz hθ hθ2
  have hKnn : 0 ≤ K :=
    le_trans (Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hAwl) hAK
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHHz : 0 ≤ HH z θ := hHHnn z θ hz hθ hθ2
  have hleib := rowDz_leib hAsm hfsm b a z θ hz hθ hθ2
  have hsplit : canonW q z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        - A z θ * Work.Spaces.mixed (b + 1) a f z θ) * Work.Spaces.mixed b a f z θ
      = canonW q z θ * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j + 1) (a - i) f z θ)))
        * Work.Spaces.mixed b a f z θ := by
    rw [hleib]
  rw [hsplit, abs_mul, abs_mul, abs_of_nonneg hcw]
  have htri : |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ)
          else (a.choose i : ℝ) * (b.choose j : ℝ)
            * (Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j + 1) (a - i) f z θ))|
      ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases h00 : i = 0 ∧ j = 0
    · rw [if_pos h00, if_pos h00, abs_zero]
    · rw [if_neg h00, if_neg h00]
      simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose i : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose j : ℝ))]
      exact le_of_eq (by ring)
  have hcoef : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
      ((a.choose i : ℝ) * (b.choose j : ℝ))) ≤ 64 := by
    have h1 : (∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ))) = 2 ^ a := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; norm_num
    have h2 : (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℝ))) = 2 ^ b := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; norm_num
    have h3 : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ)))
        = (∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ)))
          * (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℝ))) :=
      (Finset.sum_mul_sum (Finset.range (a + 1)) (Finset.range (b + 1))
        (fun i => (a.choose i : ℝ)) (fun j => (b.choose j : ℝ))).symm
    rw [h3, h1, h2, ← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  have hmove : canonW q z θ * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|))
        * |Work.Spaces.mixed b a f z θ|
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          canonW q z θ * ((if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|))
            * |Work.Spaces.mixed b a f z θ| := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    ring
  refine le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htri hcw) (abs_nonneg _)) ?_
  rw [hmove]
  have hX : 0 ≤ Ct * (1 + K + Kf)
      * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) :=
    mul_nonneg (mul_nonneg hCtpos.le (by linarith [hKnn, hKfnn]))
      (by linarith [hHknn, hHHz])
  have hper : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
      canonW q z θ * ((if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|))
          * |Work.Spaces.mixed b a f z θ|
        ≤ ((a.choose i : ℝ) * (b.choose j : ℝ))
          * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)) := by
    intro i hi j hj
    have hia : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hjb : j ≤ b := by have := Finset.mem_range.mp hj; omega
    by_cases h00 : i = 0 ∧ j = 0
    · rw [if_pos h00, mul_zero, zero_mul]
      exact mul_nonneg (by positivity) hX
    · rw [if_neg h00]
      have hh : canonW q z θ * |Work.Spaces.mixed j i A z θ|
            * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) :=
        hterm α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hab hq0 hqγ hqη0
          hqcases hHH hHHnn i j hia hjb (by omega) z θ hz hθ hθ2
      calc canonW q z θ * (((a.choose i : ℝ) * (b.choose j : ℝ))
            * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|)
            * |Work.Spaces.mixed b a f z θ|
          = ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (canonW q z θ * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
        _ ≤ ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
  refine le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hper i hi j hj) ?_
  simp only [← Finset.sum_mul]
  calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (a.choose i : ℝ) * (b.choose j : ℝ))
        * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ))
      ≤ 64 * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)) :=
        mul_le_mul_of_nonneg_right hcoef hX
    _ ≤ (64 * Ct + 1) * (1 + K + Kf)
        * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
        have h1 : 0 ≤ (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
          refine mul_nonneg (by linarith) ?_
          linarith [hHknn, hHHz]
        nlinarith [h1, hCtpos.le, hKfnn, hKnn]

/-- The `ℋ⁶`-domination of the datum slot `D_z^bD_θ^a f`. -/
theorem rowDz_Z_maj {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q : ℝ}
    (hqγ : q ≤ Work.Spaces.gam α) (hqη0 : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  rcases Nat.eq_zero_or_pos a with ha0 | ha
  · subst ha0
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α) (q := q)
        (h := f) (hqη0 rfl) hθI b (by omega)
  · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q)
      (h := f) hqγ hθI b a ha (by omega)

/-- The `ℋ⁷`-domination of the top datum slot `D_z^{b+1}D_θ^a f`. -/
theorem rowDz_DZ_maj {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q : ℝ}
    (hqγ : q ≤ Work.Spaces.gam α) (hqη0 : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hσp : 0 < Real.sin (2 * θ) := rowDz_sin2_pos hθI
  rcases Nat.eq_zero_or_pos a with ha0 | ha
  · subst ha0
    rw [Work.Spaces.mixed_zero_right]
    have hqη : q ≤ Work.Spaces.eta := hqη0 rfl
    have h := Work.Spaces.sq_le_HkIntegrand_z α 7 f z θ (b + 1) (by omega)
    have h1 : canonW q z θ
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      have h2 : canonW q z θ ≤ canonW Work.Spaces.eta z θ :=
        Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_le_int hqη hθI
      have h3 : canonW Work.Spaces.eta z θ
          = (Work.FTS.H2.Whz z θ) ^ 2 :=
        Work.FTS.TransportS.SlotT2.canonW_eta_eq z θ ⟨le_of_lt hθ, le_of_lt hθ2⟩
      exact le_trans h2 (le_of_eq h3)
    calc canonW q z θ * (Work.Spaces.DzIter (b + 1) f z θ) ^ 2
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter (b + 1) f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (Work.Spaces.DzIter (b + 1) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 7 f z θ := h
  · have h := Work.FTS.StrongPersist.N6Trans.T1SixAux.mixed_sq_w_rpow_le_HkIntegrand_gen
      α 7 f (z := z) (θ := θ) (c := q) hσp hqγ a (b + 1) ha (by omega)
    rw [rowDz_canonW_eq]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork

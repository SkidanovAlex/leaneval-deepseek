import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.summable_shift_latVec
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KfrU_sub_uvSmear_norm_le`

The `univ`-summed `k`-frame `KfrU` is the clean periodisation of the smoothed weight
(`PCFU.KfrU_periodisation`):

    `KfrU v h μ fu N z = ℓ³ Σ'_d uvSmear fu (uvRad ℓ N) W₁ (z + ℓ • latVec d)`   (`ℓ = ellH v μ`).

The estimate of this file is the *error made by dropping the `d = 0` term*: the deviation of `KfrU`
from `ℓ³ • uvSmear (· u)` is bounded by the full lattice tail

    `‖KfrU … u − ℓ³ uvSmear … u‖ ≤ ℓ³ Σ'_{m ≠ 0} ‖uvSmear … (u + ℓ • latVec m)‖` .

This is exactly the statement that the periodisation of the *smooth* weight has no wrap-around
error beyond the lattice translates themselves (the telescoping error of the `d = 0` cell against
the unperiodised weight).

## Route

* `uvSmear_rapidDecay` (`= (1 + ‖·‖)^{-4}` decay, from `f ∈ L¹` + compact support) feeds
  `summable_shift_latVec`, so the whole lattice series `m ↦ uvSmear … (u + ℓ • latVec m)` is
  summable;
* `PCFU.KfrU_periodisation` rewrites `KfrU` as `ℓ³` times that series;
* the elementary `norm_mul_tsum_sub_single_le` extracts the `m = 0` term from an absolutely
  convergent series and bounds the norm of the remainder by the sum of the norms of the `m ≠ 0`
  terms (`Summable.tsum_eq_add_tsum_ite` + `norm_tsum_le_tsum_norm`).
-/

namespace Work.BoseBoxFock

/-- **Extracting one term from an absolutely convergent series.**  For `c ≥ 0`,

    `‖c³ (Σ'_i G_i) − c³ G_a‖ ≤ c³ Σ'_i ‖(if i = a then 0 else G_i)‖` .

The point is that the `a`-term is *removed* from the bound and does not reappear (the
triangle-inequality bound `‖Σ' G‖ + ‖G a‖` of the cruder split would be too lossy). -/
private lemma norm_mul_tsum_sub_single_le {ι : Type*} [DecidableEq ι] {c : ℝ} (hc : 0 ≤ c)
    {G : ι → ℂ} (hG : Summable G) (a : ι) :
    ‖(c : ℂ) ^ 3 * (∑' i, G i) - (c : ℂ) ^ 3 * G a‖
      ≤ c ^ 3 * ∑' i, (if i = a then (0 : ℝ) else ‖G i‖) := by
  classical
  have hsplit : (∑' i, G i) = G a + ∑' i, (if i = a then 0 else G i) := hG.tsum_eq_add_tsum_ite a
  have hP : Summable (fun i => if i = a then G a else 0) :=
    (hasSum_single a (f := fun i => if i = a then G a else 0) (fun b hb => by simp [hb])).summable
  have hite : Summable (fun i => if i = a then (0 : ℂ) else G i) :=
    (hG.sub hP).congr (fun i => by by_cases h : i = a <;> simp [h])
  have hnorm : Summable (fun i => ‖(if i = a then (0 : ℂ) else G i)‖) := hite.norm
  have hc3 : ‖((c : ℂ)) ^ 3‖ = c ^ 3 := by
    rw [← Complex.ofReal_pow, show ‖((c ^ 3 : ℝ) : ℂ)‖ = |c ^ 3| by simp,
      abs_of_nonneg (pow_nonneg hc 3)]
  calc ‖(c : ℂ) ^ 3 * (∑' i, G i) - (c : ℂ) ^ 3 * G a‖
      = ‖(c : ℂ) ^ 3 * (∑' i, (if i = a then (0 : ℂ) else G i))‖ := by
        rw [hsplit]; congr 1; ring
    _ = c ^ 3 * ‖∑' i, (if i = a then (0 : ℂ) else G i)‖ := by rw [norm_mul, hc3]
    _ ≤ c ^ 3 * ∑' i, ‖(if i = a then (0 : ℂ) else G i)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (by positivity)
    _ = c ^ 3 * ∑' i, (if i = a then (0 : ℝ) else ‖G i‖) := by
        congr 1
        apply tsum_congr
        intro i
        by_cases h : i = a <;> simp [h]

-- the goal's statement carries the (large) `uvSmear`/`uvRad`/`KfrU` expressions several times over,
-- so the unification of the `calc` chain needs more than the default heartbeat budget
set_option maxHeartbeats 1000000 in
theorem KfrU_sub_uvSmear_norm_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    (hN1 : 1 ≤ N) (u : EuclideanSpace ℝ (Fin 3)) :
    ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N u
        - ((((Work.BoseBoxFock.ellH v μ) : ℂ) ^ 3) *
          Complex.ofReal (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) u))‖
      ≤ (Work.BoseBoxFock.ellH v μ) ^ 3 *
          (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ)
            else ‖Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m)‖)) := by
  classical
  have hℓ : (0 : ℝ) < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN1
    exact_mod_cast this
  have hΛ : (0 : ℝ) < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N := by
    rw [Work.BoseBoxFock.uvRad]; positivity
  obtain ⟨C, hCnn, hC⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛ hI hcs 4
  have hCΦ : ∀ q : EuclideanSpace ℝ (Fin 3),
      ‖((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) q : ℝ) : ℂ)‖
        ≤ C * (1 + ‖q‖) ^ (-(4 : ℤ)) := fun q => by simpa using hC q
  have hsum : Summable (fun m : Fin 3 → ℤ =>
      ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
        (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) :=
    Work.BoseBoxFock.summable_shift_latVec
      (Φ := fun q => ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) q : ℝ) : ℂ)) hCnn hCΦ hℓ u
  have hper := Work.BoseBoxFock.PCFU.KfrU_periodisation (v := v) (h := h) (μ := μ) (fu := fu)
    (N := N) hℓ0 hI hcs hev hN1 u
  have hlat : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : EuclideanSpace ℝ (Fin 3)) := by
    ext i; simp [Work.BoseBoxFock.latVec]
  have hzero : u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = u := by
    rw [hlat, smul_zero, add_zero]
  have hG0 : ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) u : ℝ) : ℂ)
      = ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
        (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
        (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ)) : ℝ) : ℂ) := by
    rw [hzero]
  calc ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N u
        - ((((Work.BoseBoxFock.ellH v μ) : ℂ) ^ 3) *
          Complex.ofReal (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) u))‖
      = ‖(((Work.BoseBoxFock.ellH v μ) : ℂ) ^ 3) *
            (∑' d : Fin 3 → ℤ,
              ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          - ((Work.BoseBoxFock.ellH v μ) : ℂ) ^ 3 *
            ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ)) : ℝ) : ℂ)‖ := by
        rw [hper, hG0]
    _ ≤ (Work.BoseBoxFock.ellH v μ) ^ 3 *
          (∑' i : Fin 3 → ℤ, (if i = 0 then (0 : ℝ)
            else ‖((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec i) : ℝ) : ℂ)‖)) :=
        norm_mul_tsum_sub_single_le hℓ.le hsum 0
    _ = (Work.BoseBoxFock.ellH v μ) ^ 3 *
          (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ)
            else ‖Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (u + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m)‖)) := by
        congr 1
        apply tsum_congr
        intro m
        by_cases hm : m = 0
        · simp [hm]
        · simp [hm]

end Work.BoseBoxFock

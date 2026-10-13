import Mathlib
import Submission.Work.WilC4aRW.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Filter Topology
open scoped Topology BigOperators ComplexConjugate

namespace Work.WilC4aRW

open ClassicalComplexWPT

/-! ## Elementary algebra of coordinatewise conjugation

We collect the basic facts about `conjVec` and `conjAmb` needed to reindex a
formal power series along conjugation: additivity, conjugate-linearity, and the
fact that conjugation is an isometry. -/

theorem conjVec_add {N : ℕ} (u v : Fin N → ℂ) : conjVec (u + v) = conjVec u + conjVec v := by
  ext i; simp [conjVec, map_add]

theorem conjVec_smul {N : ℕ} (c : ℂ) (v : Fin N → ℂ) : conjVec (c • v) = (star c) • conjVec v := by
  ext i; simp [conjVec, map_mul]

theorem conjVec_neg {N : ℕ} (v : Fin N → ℂ) : conjVec (-v) = -conjVec v := by
  ext i; simp [conjVec]

theorem conjVec_sub {N : ℕ} (u v : Fin N → ℂ) : conjVec (u - v) = conjVec u - conjVec v := by
  ext i; simp [conjVec, map_sub]

theorem conjAmb_add {n : ℕ} (x y : Ambient n) : conjAmb (x + y) = conjAmb x + conjAmb y := by
  ext <;> simp [conjAmb, conjVec_add, map_add]

theorem conjAmb_smul {n : ℕ} (c : ℂ) (x : Ambient n) : conjAmb (c • x) = (star c) • conjAmb x := by
  ext <;> simp [conjAmb, conjVec_smul, map_mul]

theorem conjAmb_neg {n : ℕ} (x : Ambient n) : conjAmb (-x) = -conjAmb x := by
  ext <;> simp [conjAmb, conjVec_neg]

theorem conjAmb_sub {n : ℕ} (x y : Ambient n) : conjAmb (x - y) = conjAmb x - conjAmb y := by
  ext <;> simp [conjAmb, conjVec_sub, map_sub]

theorem norm_conjVec {N : ℕ} (v : Fin N → ℂ) : ‖conjVec v‖ = ‖v‖ := by
  have : conjVec v = star v := by ext i; simp [conjVec]
  rw [this]; simp

theorem norm_conjAmb {n : ℕ} (x : Ambient n) : ‖conjAmb x‖ = ‖x‖ := by
  have h1 : ‖conjVec x.1‖ = ‖x.1‖ := norm_conjVec x.1
  simp [conjAmb, Prod.norm_def, h1]

/-- Reindexing a function along an arbitrary map commutes with `Function.update`. -/
theorem update_comp {α β γ : Type*} [DecidableEq α] (C : β → γ) (m : α → β) (i : α) (x : β) :
    (fun j => C (Function.update m i x j)) = Function.update (fun j => C (m j)) i (C x) := by
  funext j; rw [Function.update_apply]; by_cases h : j = i <;> simp [Function.update, h]

theorem star_smul_star (c w : ℂ) : star ((star c) • w) = c • star w := by
  rw [smul_eq_mul, smul_eq_mul, star_mul, star_star, mul_comm]

/-! ## The conjugate formal power series

Given a formal power series `p` on `Ambient n`, we build the power series `conjSeries p`
whose `k`-th term is `m ↦ star (p k (fun i => conjAmb (m i)))`.  This is `ℂ`-multilinear
because `p k` is `ℂ`-multilinear, `conjAmb` is conjugate-linear in each variable and `star`
is conjugate-linear in the value. -/

noncomputable def conjSeries {n : ℕ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Ambient n) ℂ :=
  MultilinearMap.mkContinuous
    (MultilinearMap.mk' (fun m : Fin k → Ambient n => star (p k (fun i => conjAmb (m i))))
      (by
        intro m i x y
        calc star (p k (fun j => conjAmb (Function.update m i (x + y) j)))
            = star (p k (Function.update (fun j => conjAmb (m j)) i
                (conjAmb x + conjAmb y))) := by rw [update_comp, conjAmb_add]
          _ = star (p k (Function.update (fun j => conjAmb (m j)) i (conjAmb x))
                + p k (Function.update (fun j => conjAmb (m j)) i (conjAmb y))) := by
                rw [(p k).map_update_add]
          _ = star (p k (Function.update (fun j => conjAmb (m j)) i (conjAmb x)))
                + star (p k (Function.update (fun j => conjAmb (m j)) i (conjAmb y))) := by
                rw [star_add]
          _ = star (p k (fun j => conjAmb (Function.update m i x j)))
                + star (p k (fun j => conjAmb (Function.update m i y j))) := by
                rw [update_comp, update_comp])
      (by
        intro m i c x
        calc star (p k (fun j => conjAmb (Function.update m i (c • x) j)))
            = star (p k (Function.update (fun j => conjAmb (m j)) i
                (star c • conjAmb x))) := by rw [update_comp, conjAmb_smul]
          _ = star ((star c) • p k (Function.update (fun j => conjAmb (m j)) i
                (conjAmb x))) := by rw [(p k).map_update_smul]
          _ = c • star (p k (Function.update (fun j => conjAmb (m j)) i (conjAmb x))) :=
                star_smul_star _ _
          _ = c • star (p k (fun j => conjAmb (Function.update m i x j))) := by
                rw [update_comp]))
    ‖p k‖
    (by
      intro m
      calc ‖star (p k (fun i => conjAmb (m i)))‖
          = ‖p k (fun i => conjAmb (m i))‖ := by simp
        _ ≤ ‖p k‖ * ∏ i, ‖conjAmb (m i)‖ := ContinuousMultilinearMap.le_opNorm (p k) _
        _ = ‖p k‖ * ∏ i, ‖m i‖ := by
              congr 1
              exact Finset.prod_congr rfl (fun i _ => norm_conjAmb (m i)))

@[simp] theorem conjSeries_apply {n : ℕ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ)
    (m : Fin k → Ambient n) : conjSeries p k m = star (p k (fun i => conjAmb (m i))) := rfl

/-- The conjugate series has operator norms bounded by those of the original series. -/
theorem norm_conjSeries_le {n : ℕ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) :
    ‖conjSeries p k‖ ≤ ‖p k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) (fun m => ?_)
  calc ‖conjSeries p k m‖ = ‖p k (fun i => conjAmb (m i))‖ := by simp
    _ ≤ ‖p k‖ * ∏ i, ‖conjAmb (m i)‖ := ContinuousMultilinearMap.le_opNorm (p k) _
    _ = ‖p k‖ * ∏ i, ‖m i‖ := by
          congr 1
          exact Finset.prod_congr rfl (fun i _ => norm_conjAmb (m i))

/-- Evaluation of the conjugate series on a constant tuple. -/
@[simp] theorem conjSeries_apply_const {n : ℕ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (k : ℕ) (y : Ambient n) :
    conjSeries p k (fun _ : Fin k => y) = star (p k (fun _ : Fin k => conjAmb y)) := by
  simp [conjSeries_apply]

end Work.WilC4aRW

namespace Work.WilC4aRW.Conj

open ClassicalComplexWPT

/-- Complex conjugation of a complex-analytic function: if `F` is complex-analytic at `0` then so
is `z ↦ star (F (conjAmb z))`.  The witness power series is obtained from a power series of `F`
by conjugating its `k`-th term coefficientwise. -/
theorem conj_analytic_ambient {n : ℕ} {F : ClassicalComplexWPT.Ambient n → ℂ}
    (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (fun z : ClassicalComplexWPT.Ambient n =>
      star (F (Work.WilC4aRW.conjAmb z))) 0 := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨r, hr⟩ := hp
  refine ⟨Work.WilC4aRW.conjSeries p, r, ?_, hr.r_pos, ?_⟩
  · -- the radius bound
    have hle := FormalMultilinearSeries.radius_le_of_le
      (p := Work.WilC4aRW.conjSeries p) (q := p)
      (fun k => Work.WilC4aRW.norm_conjSeries_le p k)
    exact hr.r_le.trans hle
  · -- the convergence of the reindexed series
    intro y hy
    have hy' : Work.WilC4aRW.conjAmb y ∈ Metric.eball (0 : ClassicalComplexWPT.Ambient n) r := by
      simp only [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero] at hy ⊢
      rw [Work.WilC4aRW.norm_conjAmb]
      exact hy
    have hsum : HasSum (fun k : ℕ => p k (fun _ : Fin k => Work.WilC4aRW.conjAmb y))
        (F (0 + Work.WilC4aRW.conjAmb y)) := hr.hasSum hy'
    have hmap := hsum.map (starRingEnd ℂ) continuous_star
    have hfun : (fun k : ℕ => Work.WilC4aRW.conjSeries p k (fun _ : Fin k => y))
        = ⇑(starRingEnd ℂ) ∘ (fun k : ℕ =>
            p k (fun _ : Fin k => Work.WilC4aRW.conjAmb y)) := by
      funext k; rfl
    have hval : starRingEnd ℂ (F (0 + Work.WilC4aRW.conjAmb y))
        = (fun z : ClassicalComplexWPT.Ambient n =>
            star (F (Work.WilC4aRW.conjAmb z))) (0 + y) := by
      simp only [starRingEnd_apply, zero_add]
    rw [← hfun, hval] at hmap
    exact hmap

end Work.WilC4aRW.Conj

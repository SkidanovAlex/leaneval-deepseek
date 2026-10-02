import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.splitPair_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Polynomial Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-- The fixed-point polynomial `Hp c` of `splitPair_exists` and the polynomial `Qpoly c` of
`ParWall` agree: both evaluate to `F c z - z`. -/
theorem Qpoly_eq_Hp (c : ℂ) : Qpoly c = Hp c := by
  apply Polynomial.funext
  intro z
  rw [Qpoly_eval, Hp_eval]

/-- A polynomial divisible by `(X - C a)²` has vanishing derivative at `a`. -/
theorem derivative_eval_eq_zero_of_sq_dvd {p : ℂ[X]} {a : ℂ}
    (h : (X - C a) ^ 2 ∣ p) : p.derivative.eval a = 0 := by
  obtain ⟨T, rfl⟩ := h
  rw [Polynomial.derivative_mul]
  have h1 : (((X - C a) ^ 2).derivative).eval a = 0 := by
    have hd : (X - C a) ^ 2 = (X - C a) * (X - C a) := by ring
    rw [hd, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_one]
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have h2 : ((X - C a) ^ 2).eval a = 0 := by
    simp [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, h1, h2, zero_mul, add_zero]

/-- **The collision locus is a double-root locus.**  On a small ball around the root-parabolic
parameter `c₀`, every parameter `c` at which the two split fixed points coincide (`S.E c = 0`)
has `S.m c` as a *multiple* root of the fixed-point polynomial `Qpoly c`; equivalently the
multiplier of the second return map at `S.m c` is `1`. -/
theorem Hp_double_root_count {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      S.E c = 0 → (Work.PARIMPL.ParSplit.Qpoly c).derivative.eval (S.m c) = 0 := by
  -- A radius around `z₁` in which `Hp c₀` has no root other than `z₁`.
  obtain ⟨r₀, hr₀, hno₀⟩ := exists_radius d
  -- Shrink it so that the disc also stays inside `ball z₁ S.R` (where `S.unique` holds).
  set r : ℝ := min (r₀ / 2) (S.R / 2) with hr_def
  have hr : 0 < r := by
    rw [hr_def]; exact lt_min (by linarith) (by linarith [S.hR])
  have hr_r₀ : r ≤ r₀ := by
    rw [hr_def]; exact le_trans (min_le_left _ _) (by linarith)
  have hr_R : r ≤ S.R := by
    rw [hr_def]; exact le_trans (min_le_right _ _) (by linarith [S.hR])
  have hno₀' : ∀ z ∈ Metric.closedBall d.z₁ r, (Hp c₀).eval z = 0 → z = d.z₁ := by
    intro z hz hz0
    exact hno₀ z (Metric.closedBall_subset_closedBall hr_r₀ hz) hz0
  have hsph : ∀ z ∈ Metric.sphere d.z₁ r, (Hp c₀).eval z ≠ 0 := by
    intro z hz hz0
    have hzmem : z ∈ Metric.closedBall d.z₁ r :=
      Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hz))
    have hz1 : z = d.z₁ := hno₀' z hzmem hz0
    have hdist : dist z d.z₁ = r := Metric.mem_sphere.mp hz
    rw [hz1, dist_self] at hdist
    linarith
  -- A parameter ball on which no root of `Hp c` lies on the circle `|z - z₁| = r`.
  obtain ⟨ρ, hρ, hno⟩ := exists_param_ball_no_root hr hsph
  -- At `c₀` the count of roots in the disc `ball z₁ r` (with multiplicity) is `2`.
  have hc0 : rootFilt d.z₁ r c₀ = 2 • ({d.z₁} : Multiset ℂ) := by
    obtain ⟨S', hS', hSeval⟩ := Hp_c0_double_root d
    have hSne : S' ≠ 0 := fun h => hSeval (by rw [h]; simp)
    have hqne : ((X - C d.z₁) ^ 2 : ℂ[X]) ≠ 0 :=
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero d.z₁)
    have hSroots : ∀ a ∈ S'.roots, a ∉ Metric.ball d.z₁ r := by
      intro a ha hball
      have heval : S'.eval a = 0 := (Polynomial.mem_roots hSne).mp ha
      have hHp : (Hp c₀).eval a = 0 := by
        rw [hS', Polynomial.eval_mul, Polynomial.eval_pow, heval, mul_zero]
      have haz : a = d.z₁ := hno₀' a (Metric.ball_subset_closedBall hball) hHp
      rw [haz] at heval
      exact hSeval heval
    have hfilterS : S'.roots.filter (fun a => a ∈ Metric.ball d.z₁ r) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro a ha
      exact hSroots a ha
    have htarget : (((X - C d.z₁) ^ 2 : ℂ[X]).roots.filter
        (fun a => a ∈ Metric.ball d.z₁ r)) = 2 • ({d.z₁} : Multiset ℂ) := by
      rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C]
      rw [Multiset.filter_eq_self.mpr]
      intro a ha
      rw [Multiset.nsmul_singleton, Multiset.mem_replicate] at ha
      rw [ha.2]
      exact Metric.mem_ball_self hr
    rw [rootFilt, hS', Polynomial.roots_mul (mul_ne_zero hqne hSne), Multiset.filter_add,
      htarget, hfilterS, add_zero]
  have hcard0 : (rootFilt d.z₁ r c₀).card = 2 := by
    rw [hc0, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
  have hcard := rootFilt_card_eq_two hr hρ hno hcard0
  -- A ball on which `S.m c` stays in `ball z₁ r`.
  have hc0_mem : c₀ ∈ Metric.ball c₀ S.ρ := Metric.mem_ball_self S.hρ
  have hmc : ContinuousAt S.m c₀ := S.cont_m.continuousAt (isOpen_ball.mem_nhds hc0_mem)
  have hcont : ContinuousAt (fun c => dist (S.m c) d.z₁) c₀ := hmc.dist continuousAt_const
  have hlt : {x : ℝ | x < r} ∈ 𝓝 (dist (S.m c₀) d.z₁) :=
    (isOpen_lt continuous_id continuous_const).mem_nhds (by rw [S.m₀, dist_self]; exact hr)
  have hmem : {c : ℂ | dist (S.m c) d.z₁ < r} ∈ 𝓝 c₀ := hcont hlt
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp hmem
  set ρ' : ℝ := min ε (min ρ S.ρ) with hρ'_def
  have hρ' : 0 < ρ' := by
    rw [hρ'_def]; exact lt_min hε (lt_min hρ S.hρ)
  have hρ'_S : ρ' ≤ S.ρ := by
    rw [hρ'_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ', hρ', hρ'_S, ?_⟩
  intro c hc hE
  have hcε : c ∈ Metric.ball c₀ ε :=
    Metric.ball_subset_ball (by rw [hρ'_def]; exact min_le_left _ _) hc
  have hcρ : c ∈ Metric.ball c₀ ρ :=
    Metric.ball_subset_ball
      (by rw [hρ'_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)) hc
  have hcS : c ∈ Metric.ball c₀ S.ρ := Metric.ball_subset_ball hρ'_S hc
  have hdist : dist (S.m c) d.z₁ < r := hεb hcε
  have hmemball : S.m c ∈ Metric.ball d.z₁ r := Metric.mem_ball.mpr hdist
  have hcardc : (rootFilt d.z₁ r c).card = 2 := hcard c hcρ
  -- Every root of `Hp c` inside `ball z₁ r` equals `S.m c`.
  have hall : ∀ x ∈ rootFilt d.z₁ r c, S.m c = x := by
    intro x hx
    rw [rootFilt, Multiset.mem_filter] at hx
    obtain ⟨hxroot, hxball⟩ := hx
    have hxeval : (Hp c).eval x = 0 :=
      (Polynomial.mem_roots (Hp_ne_zero c)).mp hxroot
    have hxfix : Work.EL.F c x = x := by
      rw [Hp_eval] at hxeval; exact sub_eq_zero.mp hxeval
    have hxS : x ∈ Metric.ball d.z₁ S.R := Metric.ball_subset_ball hr_R hxball
    rcases (S.unique c hcS x hxS).mp hxfix with h | h
    · rw [h, hE]; ring
    · rw [h, hE]; ring
  have hcount : Multiset.count (S.m c) (rootFilt d.z₁ r c) = 2 := by
    rw [Multiset.count_eq_card.mpr hall, hcardc]
  have hle : rootFilt d.z₁ r c ≤ (Hp c).roots := by
    rw [rootFilt]; exact Multiset.filter_le _ _
  have hcnt := (Multiset.le_iff_count.mp hle) (S.m c)
  rw [hcount] at hcnt
  have hrm : 2 ≤ Polynomial.rootMultiplicity (S.m c) (Hp c) := by
    rw [← Polynomial.count_roots (p := Hp c) (a := S.m c)]
    exact hcnt
  have hdvd : (X - C (S.m c)) ^ 2 ∣ Hp c :=
    (Polynomial.le_rootMultiplicity_iff (Hp_ne_zero c)).mp hrm
  rw [← Qpoly_eq_Hp c] at hdvd
  exact derivative_eval_eq_zero_of_sq_dvd hdvd

end Work.PARIMPL.ParSplit

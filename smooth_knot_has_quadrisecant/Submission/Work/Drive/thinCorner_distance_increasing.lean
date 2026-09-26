import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs

namespace Work.Drive

set_option maxHeartbeats 4000000

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-!
## Helpers for `Work.Drive.thinCorner_distance_increasing`

The whole reduction is a `C⁰` argument: the *reference* knot `r` satisfies a uniform
"distance-growth" estimate
`‖r (x + ρ₀) - r x‖ + η ≤ ‖r s - r x‖` for every `s` at circular distance `≥ 2 ρ₀` from `x`,
and every `C⁰`-`ε₂`-close knot with `4 ε₂ < η` inherits the strict inequality.
-/

/-- The canonical representative of `u` in `[0, period)`. -/
def thinCorner_red (u : ℝ) : ℝ := u - (⌊u / period⌋ : ℝ) * period

lemma thinCorner_red_mem (u : ℝ) : thinCorner_red u ∈ Set.Ico (0 : ℝ) period := by
  have hp : 0 < period := period_pos
  have h1 : (⌊u / period⌋ : ℝ) ≤ u / period := Int.floor_le _
  have h2 : u / period < (⌊u / period⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊u / period⌋ : ℝ) * period ≤ u := by
    have h := mul_le_mul_of_nonneg_right h1 hp.le
    rwa [div_mul_cancel₀ u hp.ne'] at h
  have h4 : u < (⌊u / period⌋ : ℝ) * period + period := by
    have h := mul_lt_mul_of_pos_right h2 hp
    rw [add_mul, one_mul, div_mul_cancel₀ u hp.ne'] at h
    linarith
  exact ⟨by simp only [thinCorner_red]; linarith, by simp only [thinCorner_red]; linarith⟩

lemma thinCorner_red_coe (u : ℝ) :
    ((thinCorner_red u : ℝ) : AddCircle period) = (u : AddCircle period) := by
  have hk : (((⌊u / period⌋ : ℝ) * period : ℝ) : AddCircle period) = 0 := by
    have h : ((⌊u / period⌋ : ℝ) * period : ℝ) = ⌊u / period⌋ • period := by
      simp [zsmul_eq_mul]
    rw [h, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  rw [thinCorner_red, sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, hk, neg_zero, add_zero]

/-- Equal classes on the parameter circle give equal points of the knot. -/
lemma thinCorner_r_eq_of_coe_eq {r : ℝ → Space} (hr : IsSmoothKnot r) {y y' : ℝ}
    (h : (y : AddCircle period) = (y' : AddCircle period)) : r y = r y' := by
  rw [← knotMap_eq_r hr y, ← knotMap_eq_r hr y', h]

lemma thinCorner_r_red {r : ℝ → Space} (hr : IsSmoothKnot r) (u : ℝ) :
    r (thinCorner_red u) = r u :=
  thinCorner_r_eq_of_coe_eq hr (thinCorner_red_coe u)

lemma thinCorner_r_red_add {r : ℝ → Space} (hr : IsSmoothKnot r) (u h : ℝ) :
    r (thinCorner_red u + h) = r (u + h) :=
  thinCorner_r_eq_of_coe_eq hr (by
    rw [AddCircle.coe_add, AddCircle.coe_add, thinCorner_red_coe])

/-- The canonical representative of a parameter with circular separation `≥ 2 ρ` from `0` is at
least `2 ρ` away from both ends of the period interval. -/
lemma thinCorner_red_bounds {ρ u : ℝ} (hρ : 0 < ρ) (hP : 4 * ρ < period)
    (hsep : 2 * ρ ≤ ‖(u : AddCircle period)‖) :
    2 * ρ ≤ thinCorner_red u ∧ 2 * ρ ≤ period - thinCorner_red u := by
  have hp : 0 < period := period_pos
  set h := thinCorner_red u with hh
  have hhIco : h ∈ Set.Ico (0 : ℝ) period := thinCorner_red_mem u
  have hhnorm : ‖(h : AddCircle period)‖ = ‖(u : AddCircle period)‖ := by
    rw [hh, thinCorner_red_coe]
  have hsep' : 2 * ρ ≤ ‖(h : AddCircle period)‖ := by rw [hhnorm]; exact hsep
  rcases le_or_gt h (period / 2) with hle | hgt
  · have habs : |h| ≤ |period| / 2 := by
      rw [abs_of_nonneg hhIco.1, abs_of_pos hp]; linarith
    have hnorm : ‖(h : AddCircle period)‖ = |h| :=
      (AddCircle.norm_coe_eq_abs_iff period hp.ne').mpr habs
    have hge : 2 * ρ ≤ h := by rw [hnorm, abs_of_nonneg hhIco.1] at hsep'; exact hsep'
    exact ⟨hge, by linarith [hhIco.2]⟩
  · have hcoe : (((h - period : ℝ)) : AddCircle period) = (h : AddCircle period) := by
      rw [sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, AddCircle.coe_period, neg_zero,
        add_zero]
    have hlt : (h - period : ℝ) < 0 := by linarith [hhIco.2]
    have habs : |(h - period : ℝ)| ≤ |period| / 2 := by
      rw [abs_of_neg hlt, abs_of_pos hp]; linarith
    have hnorm : ‖(((h - period : ℝ)) : AddCircle period)‖ = |(h - period : ℝ)| :=
      (AddCircle.norm_coe_eq_abs_iff period hp.ne').mpr habs
    have hge : 2 * ρ ≤ period - h := by
      rw [← hcoe, hnorm, abs_of_neg hlt] at hsep'
      linarith
    exact ⟨by linarith, hge⟩

/-! ### Estimates for the shifted curve -/

lemma thinCorner_hasDerivAt_shiftMap {f : ℝ → Space} (hf : Differentiable ℝ f) (a v : ℝ) :
    HasDerivAt (fun w : ℝ => f (a + w)) (deriv f (a + v)) v :=
  ((hf (a + v)).hasDerivAt).comp_const_add a v

/-- **Taylor estimate.**  A curve whose velocity is `C`-Lipschitz satisfies, for `σ ≥ 0`,
`r (b + σ) = r b + σ • v b + O (C σ²)`; the three consequences used below are the third-order
bound on the remainder and the two one-sided bounds of `‖r (b + σ) - r b‖` by `σ ‖v b‖`. -/
theorem thinCorner_shift_sub_le {r : ℝ → Space} (hrd : Differentiable ℝ r)
    {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ t t' : ℝ, ‖deriv r t - deriv r t'‖ ≤ C * |t' - t|)
    {b σ : ℝ} (hσ : 0 ≤ σ) :
    ‖r (b + σ) - r b - σ • deriv r b‖ ≤ C * σ ^ 2 ∧
      ‖r (b + σ) - r b‖ ≤ σ * (‖deriv r b‖ + C * σ) ∧
      σ * (‖deriv r b‖ - C * σ) ≤ ‖r (b + σ) - r b‖ := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u : ℝ => r (b + u) - r b - u • deriv r b)
      (deriv r (b + x) - deriv r b) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => r (b + u) - r b) (deriv r (b + x)) x :=
      (thinCorner_hasDerivAt_shiftMap hrd b x).sub_const (r b)
    have h2 : HasDerivAt (fun u : ℝ => u • deriv r b) (deriv r b) x := by
      simpa using (hasDerivAt_id x).smul_const (deriv r b)
    have h3 := h1.sub h2
    have hfun : ((fun u : ℝ => r (b + u) - r b) - fun u : ℝ => u • deriv r b)
        = fun u : ℝ => r (b + u) - r b - u • deriv r b := rfl
    rw [hfun] at h3
    exact h3
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun u : ℝ => r (b + u) - r b - u • deriv r b)
      (f' := fun x : ℝ => deriv r (b + x) - deriv r b)
      (a := 0) (b := σ) (C := C * σ)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => by
        have hx0 : 0 ≤ x := hx.1
        have hxσ : x ≤ σ := le_of_lt hx.2
        calc ‖deriv r (b + x) - deriv r b‖ ≤ C * |b - (b + x)| := hlip (b + x) b
          _ = C * |x| := by
              have h : b - (b + x) = -x := by ring
              rw [h, abs_neg]
          _ = C * x := by rw [abs_of_nonneg hx0]
          _ ≤ C * σ := mul_le_mul_of_nonneg_left hxσ hC)
      σ ⟨hσ, le_rfl⟩
  have hg : ‖r (b + σ) - r b - σ • deriv r b‖ ≤ C * σ ^ 2 := by
    have h1 : ‖r (b + σ) - r b - σ • deriv r b‖ ≤ C * σ * (σ - 0) := by
      simpa using hmain
    rw [sub_zero] at h1
    calc ‖r (b + σ) - r b - σ • deriv r b‖ ≤ C * σ * σ := h1
      _ = C * σ ^ 2 := by ring
  refine ⟨hg, ?_, ?_⟩
  · have htri : ‖r (b + σ) - r b‖
        ≤ ‖r (b + σ) - r b - σ • deriv r b‖ + ‖σ • deriv r b‖ := by
      have h := norm_add_le (r (b + σ) - r b - σ • deriv r b) (σ • deriv r b)
      have heq : (r (b + σ) - r b - σ • deriv r b) + σ • deriv r b = r (b + σ) - r b := by
        abel
      rwa [heq] at h
    calc ‖r (b + σ) - r b‖
        ≤ ‖r (b + σ) - r b - σ • deriv r b‖ + ‖σ • deriv r b‖ := htri
      _ ≤ C * σ ^ 2 + σ * ‖deriv r b‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
          linarith
      _ = σ * (‖deriv r b‖ + C * σ) := by ring
  · have hstep : ‖(r (b + σ) - r b) - (r (b + σ) - r b - σ • deriv r b)‖
        ≤ ‖r (b + σ) - r b‖ + ‖r (b + σ) - r b - σ • deriv r b‖ := norm_sub_le _ _
    have hEq : (r (b + σ) - r b) - (r (b + σ) - r b - σ • deriv r b)
        = σ • deriv r b := by abel
    have h2 : σ * ‖deriv r b‖
        ≤ ‖r (b + σ) - r b‖ + ‖r (b + σ) - r b - σ • deriv r b‖ := by
      calc σ * ‖deriv r b‖ = ‖σ • deriv r b‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
        _ = ‖(r (b + σ) - r b) - (r (b + σ) - r b - σ • deriv r b)‖ := by rw [hEq]
        _ ≤ _ := hstep
    have hgoal : σ * (‖deriv r b‖ - C * σ) = σ * ‖deriv r b‖ - C * σ ^ 2 := by ring
    rw [hgoal]
    linarith
/-- A chord of parameter length `σ ≥ 0` is at most `M σ` when the speed is bounded by `M`. -/
lemma thinCorner_sub_le_speed {r : ℝ → Space} (hrd : Differentiable ℝ r) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ t : ℝ, ‖deriv r t‖ ≤ M) {b σ : ℝ} (hσ : 0 ≤ σ) :
    ‖r (b + σ) - r b‖ ≤ M * σ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := r) (s := Set.Icc b (b + σ))
    (x := b) (y := b + σ) (C := M)
    (fun t _ => hrd t) (fun t _ => hbound t) (convex_Icc _ _)
    (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  rwa [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hσ] at h

/-- **The gap at small parameter distances.**  If `|a - b| ≤ δ`, `0 < ρ ≤ δ` and `2 ρ ≤ τ ≤ δ`
then the chord of length `τ` based at `b` exceeds the chord of length `ρ` based at `a` by at
least `ρ (m - 4 C δ)`, where `m` is a lower bound for the speed and `C` a Lipschitz constant for
the velocity. -/
theorem thinCorner_local_gap {r : ℝ → Space} (hrd : Differentiable ℝ r)
    {m C δ : ℝ} (hm : 0 < m) (hC : 0 ≤ C) (hδC : C * δ ≤ m / 8)
    (hspeed : ∀ t : ℝ, m ≤ ‖deriv r t‖)
    (hlip : ∀ t t' : ℝ, ‖deriv r t - deriv r t'‖ ≤ C * |t' - t|)
    {a b ρ τ : ℝ} (hab : |a - b| ≤ δ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ) (hτρ : 2 * ρ ≤ τ)
    (hτδ : τ ≤ δ) :
    ‖r (a + ρ) - r a‖ + ρ * (m - 4 * (C * δ)) ≤ ‖r (b + τ) - r b‖ := by
  obtain ⟨-, hub, -⟩ := thinCorner_shift_sub_le hrd hC hlip (b := a) (σ := ρ) hρ.le
  have hva : ‖deriv r a‖ ≤ ‖deriv r b‖ + C * |a - b| := by
    have h1 : ‖deriv r a - deriv r b‖ ≤ C * |a - b| := by
      have h := hlip a b
      rwa [abs_sub_comm] at h
    have h2 : ‖deriv r a‖ ≤ ‖deriv r b‖ + ‖deriv r a - deriv r b‖ := by
      have h := norm_add_le (deriv r b) (deriv r a - deriv r b)
      have heq : deriv r b + (deriv r a - deriv r b) = deriv r a := by abel
      rwa [heq] at h
    linarith
  have hupper : ‖r (a + ρ) - r a‖ ≤ ρ * (‖deriv r b‖ + 2 * (C * δ)) := by
    calc ‖r (a + ρ) - r a‖ ≤ ρ * (‖deriv r a‖ + C * ρ) := hub
      _ ≤ ρ * (‖deriv r b‖ + 2 * (C * δ)) := by
          apply mul_le_mul_of_nonneg_left _ hρ.le
          have h3 : C * |a - b| ≤ C * δ := mul_le_mul_of_nonneg_left hab hC
          have h4 : C * ρ ≤ C * δ := mul_le_mul_of_nonneg_left hρδ hC
          linarith
  obtain ⟨-, -, hlow⟩ := thinCorner_shift_sub_le hrd hC hlip (b := b) (σ := τ)
    (by linarith [hρ.le])
  have hlow2 : 2 * ρ * (‖deriv r b‖ - C * δ) ≤ ‖r (b + τ) - r b‖ := by
    have h4 : 2 * ρ * (‖deriv r b‖ - C * δ) ≤ τ * (‖deriv r b‖ - C * τ) :=
      mul_le_mul hτρ (by linarith [mul_le_mul_of_nonneg_left hτδ hC])
        (by have := hspeed b; linarith) (by linarith [hρ.le])
    linarith
  have hkey : ρ * (‖deriv r b‖ + 2 * (C * δ)) + ρ * (m - 4 * (C * δ))
      ≤ 2 * ρ * (‖deriv r b‖ - C * δ) := by
    have h1 : m ≤ ‖deriv r b‖ := hspeed b
    nlinarith [h1, hρ.le]
  linarith

/-! ### Separation of far parameters -/

/-- **Uniform separation.**  For `0 < d` with `2 d < period`, parameters separated by at least `d`
on one period give points of the knot at distance at least some `μ > 0`. -/
theorem thinCorner_separation {r : ℝ → Space} (hr : IsSmoothKnot r) {d : ℝ}
    (hd : 0 < d) (hdP : 2 * d < period) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ Set.Icc (0 : ℝ) period, ∀ h ∈ Set.Icc d (period - d),
      μ ≤ ‖r (x + h) - r x‖ := by
  have hp : 0 < period := period_pos
  have hcont : Continuous (fun p : ℝ × ℝ => ‖r (p.1 + p.2) - r p.1‖) := by
    have h1 : Continuous fun p : ℝ × ℝ => r (p.1 + p.2) :=
      hr.continuous.comp (continuous_fst.add continuous_snd)
    have h2 : Continuous fun p : ℝ × ℝ => r p.1 := hr.continuous.comp continuous_fst
    exact (h1.sub h2).norm
  have hK : IsCompact (Set.Icc (0 : ℝ) period ×ˢ Set.Icc d (period - d)) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) period ×ˢ Set.Icc d (period - d)).Nonempty :=
    ⟨(0, d), ⟨⟨le_rfl, hp.le⟩, ⟨le_rfl, by linarith⟩⟩⟩
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hp1 : p.1 ∈ Set.Icc (0 : ℝ) period := (Set.mem_prod.mp hpK).1
  have hp2mem : p.2 ∈ Set.Icc d (period - d) := (Set.mem_prod.mp hpK).2
  have hpos : 0 < ‖r (p.1 + p.2) - r p.1‖ := by
    rw [norm_pos_iff]
    intro heq
    have heq' : r (p.1 + p.2) = r p.1 := sub_eq_zero.mp heq
    have hcls : ((p.1 + p.2 : ℝ) : AddCircle period) = (p.1 : AddCircle period) := by
      apply knotMap_injective hr
      rw [knotMap_eq_r hr (p.1 + p.2), knotMap_eq_r hr p.1]
      exact heq'
    have h0 : ((p.2 : ℝ) : AddCircle period) = 0 := by
      have h2 : (p.1 : AddCircle period) + (p.2 : AddCircle period)
          = (p.1 : AddCircle period) + 0 := by
        rw [← AddCircle.coe_add, add_zero]
        exact hcls
      exact add_left_cancel h2
    haveI : Fact (0 < period) := ⟨hp⟩
    have hp2Ico : p.2 ∈ Set.Ico (0 : ℝ) period :=
      ⟨by linarith [hd, hp2mem.1], by linarith [hp2mem.2, hd]⟩
    have hp2z : p.2 = 0 := (AddCircle.coe_eq_zero_iff_of_mem_Ico hp2Ico).mp h0
    linarith [hp2mem.1, hp2z]
  refine ⟨‖r (p.1 + p.2) - r p.1‖, hpos, ?_⟩
  intro x hx h hh
  have hmem : (x, h) ∈ Set.Icc (0 : ℝ) period ×ˢ Set.Icc d (period - d) := ⟨hx, hh⟩
  have hle := hpmin hmem
  exact hle

/-! ### Speed bounds of an analytic knot -/

/-- **Speed bounds.**  For a smooth knot there are positive lower and upper bounds for the speed
together with a global Lipschitz constant for the velocity. -/
theorem thinCorner_speed_bounds {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ m M C : ℝ, 0 < m ∧ 0 < M ∧ 0 < C ∧
      (∀ t : ℝ, m ≤ ‖deriv r t‖) ∧ (∀ t : ℝ, ‖deriv r t‖ ≤ M) ∧
      (∀ t t' : ℝ, ‖deriv r t - deriv r t'‖ ≤ C * |t' - t|) := by
  have hp : 0 < period := period_pos
  have hvcont : Continuous (deriv r) := hr.smooth.continuous_deriv (by simp)
  have hvper : Function.Periodic (deriv r) period := fun t => by
    simpa [velocity] using hr.velocity_periodic t
  have hne : (Set.Icc (0 : ℝ) period).Nonempty := ⟨0, le_rfl, hp.le⟩
  obtain ⟨t₀, _, hmin₀⟩ := isCompact_Icc.exists_isMinOn hne hvcont.norm.continuousOn
  obtain ⟨t₁, _, hmax₀⟩ := isCompact_Icc.exists_isMaxOn hne hvcont.norm.continuousOn
  have hmpos : 0 < ‖deriv r t₀‖ := by
    simpa [velocity] using norm_pos_iff.mpr (hr.regular t₀)
  have hMpos : 0 < ‖deriv r t₁‖ + 1 := by positivity
  have hvd : Differentiable ℝ (deriv r) := by
    have h1 : ContDiff ℝ ⊤ (deriv r) := hr.smooth.deriv'
    exact h1.differentiable (by simp)
  have hwcont : Continuous (deriv (deriv r)) := by
    have h1 : ContDiff ℝ ⊤ (deriv r) := hr.smooth.deriv'
    have h2 : ContDiff ℝ ⊤ (deriv (deriv r)) := h1.deriv'
    exact h2.continuous
  have hwper : Function.Periodic (deriv (deriv r)) period := by
    intro t
    have h := periodic_velocity (r := deriv r) hvper hvd t
    simpa [velocity] using h
  obtain ⟨t₂, _, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hwcont.norm.continuousOn
  set C : ℝ := ‖deriv (deriv r) t₂‖ + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCbound : ∀ t : ℝ, ‖deriv (deriv r) t‖ ≤ C := by
    intro t
    obtain ⟨y, hy, hty⟩ := hwper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖deriv (deriv r) t‖ = ‖deriv (deriv r) y‖ := by rw [hty]
      _ ≤ ‖deriv (deriv r) t₂‖ := hmax₂ hy'
      _ ≤ C := by rw [hCdef]; linarith
  have hlip : ∀ t t' : ℝ, ‖deriv r t - deriv r t'‖ ≤ C * |t' - t| := by
    intro t t'
    rcases le_total t t' with hle | hle
    · have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv r) (f' := fun x : ℝ => deriv (deriv r) x) (a := t) (b := t') (C := C)
        (fun x _ => (hvd x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hCbound x) t' ⟨hle, le_rfl⟩
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t' - t), norm_sub_rev]
      exact h
    · have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv r) (f' := fun x : ℝ => deriv (deriv r) x) (a := t') (b := t) (C := C)
        (fun x _ => (hvd x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hCbound x) t ⟨hle, le_rfl⟩
      rw [abs_of_nonpos (by linarith : t' - t ≤ 0), neg_sub]
      exact h
  refine ⟨‖deriv r t₀‖, ‖deriv r t₁‖ + 1, C, hmpos, hMpos, hCpos, ?_, ?_, hlip⟩
  · intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖deriv r t₀‖ ≤ ‖deriv r y‖ := hmin₀ hy'
      _ = ‖deriv r t‖ := by rw [hty]
  · intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖deriv r t‖ = ‖deriv r y‖ := by rw [hty]
      _ ≤ ‖deriv r t₁‖ := hmax₀ hy'
      _ ≤ ‖deriv r t₁‖ + 1 := by linarith


/-! ### The distance-growth estimate for the reference knot -/

/-- **The core estimate.**  For a smooth knot `r` there are `ρ₀ > 0` with `4 ρ₀ < period` and
`η > 0` such that for every `x` and every parameter `s` at circular distance `≥ 2 ρ₀` from `x`, the
point at parameter distance `ρ₀` from `x` is closer to `r x` than `r s` is, with margin `η`. -/
theorem thinCorner_core {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ 4 * ρ₀ < period ∧ ∃ η : ℝ, 0 < η ∧
      ∀ x s : ℝ, 2 * ρ₀ ≤ circSep s x → ‖r (x + ρ₀) - r x‖ + η ≤ ‖r s - r x‖ := by
  obtain ⟨m, M, C, hm, hM, hC, hslow, hfast, hlip⟩ := thinCorner_speed_bounds hr
  have hC0 : 0 ≤ C := hC.le
  have hrd : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hp : 0 < period := period_pos
  set δ : ℝ := min 1 (m / (8 * C)) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : C * δ ≤ m / 8 := by
    have h := min_le_right (1 : ℝ) (m / (8 * C))
    have h8 : C * (m / (8 * C)) = m / 8 := by field_simp
    calc C * δ = C * min 1 (m / (8 * C)) := by rw [hδdef]
      _ ≤ C * (m / (8 * C)) := mul_le_mul_of_nonneg_left h hC0
      _ = m / 8 := h8
  have h2δ : 2 * δ < period := by
    have hpi : (2 : ℝ) < period := by
      unfold period
      have := Real.pi_gt_three
      linarith
    linarith
  obtain ⟨μ, hμpos, hμ⟩ := thinCorner_separation hr hδpos h2δ
  set ρ₀ : ℝ := min (δ / 2) (min (μ / (2 * M)) (period / 8)) with hρdef
  have hρpos : 0 < ρ₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρδ : ρ₀ ≤ δ := by
    have h1 : ρ₀ ≤ δ / 2 := min_le_left _ _
    linarith
  have hρμ : ρ₀ ≤ μ / (2 * M) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρP : ρ₀ ≤ period / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  have h4ρ : 4 * ρ₀ < period := by linarith [hρP, hp]
  have hmargin : 0 < m - 4 * (C * δ) := by nlinarith [hδC, hm]
  set η : ℝ := min (ρ₀ * (m - 4 * (C * δ))) (μ - M * ρ₀) with hηdef
  have hηpos : 0 < η := by
    apply lt_min
    · exact mul_pos hρpos hmargin
    · have h1 : M * ρ₀ ≤ μ / 2 := by
        have h2 := mul_le_mul_of_nonneg_left hρμ hM.le
        have h3 : M * (μ / (2 * M)) = μ / 2 := by field_simp
        linarith [h2, h3]
      linarith
  refine ⟨ρ₀, hρpos, h4ρ, η, hηpos, ?_⟩
  intro x s hsep
  have hcse : circSep s x = ‖((s - x : ℝ) : AddCircle period)‖ := by
    rw [circSep, dist_eq_norm, ← AddCircle.coe_sub]
  set h : ℝ := thinCorner_red (s - x) with hhdef
  have hbnd := thinCorner_red_bounds hρpos h4ρ (u := s - x) (by rw [← hcse]; exact hsep)
  have hh2ρ : 2 * ρ₀ ≤ h := hbnd.1
  have hh2ρ' : 2 * ρ₀ ≤ period - h := hbnd.2
  have hrs : r (x + h) = r s := thinCorner_r_eq_of_coe_eq hr (by
    rw [AddCircle.coe_add, thinCorner_red_coe, AddCircle.coe_sub]
    abel)
  have hrew : ‖r s - r x‖ = ‖r (x + h) - r x‖ := by rw [hrs]
  rw [hrew]
  rcases le_or_gt h δ with hcase | hcase
  · have hloc := thinCorner_local_gap hrd hm hC0 hδC hslow hlip (a := x) (b := x) (ρ := ρ₀)
      (τ := h) (by rw [sub_self, abs_zero]; linarith [hδpos]) hρpos hρδ hh2ρ hcase
    have hηle : η ≤ ρ₀ * (m - 4 * (C * δ)) := min_le_left _ _
    linarith
  · rcases lt_or_ge h (period - δ) with hcase2 | hcase2
    · have hxr : thinCorner_red x ∈ Set.Icc (0 : ℝ) period :=
        Set.Ico_subset_Icc_self (thinCorner_red_mem x)
      have hμ' : μ ≤ ‖r (thinCorner_red x + h) - r (thinCorner_red x)‖ :=
        hμ (thinCorner_red x) hxr h ⟨le_of_lt hcase, le_of_lt hcase2⟩
      have heq : ‖r (thinCorner_red x + h) - r (thinCorner_red x)‖ = ‖r (x + h) - r x‖ := by
        rw [thinCorner_r_red_add hr x h, thinCorner_r_red hr x]
      rw [heq] at hμ'
      have hupper : ‖r (x + ρ₀) - r x‖ ≤ M * ρ₀ :=
        thinCorner_sub_le_speed hrd hM.le hfast hρpos.le
      have hηle : η ≤ μ - M * ρ₀ := min_le_right _ _
      linarith
    · have htδ : period - h ≤ δ := by linarith
      have hab : |x - (x - (period - h))| ≤ δ := by
        have h1 : x - (x - (period - h)) = period - h := by ring
        rw [h1, abs_of_nonneg (by linarith [hh2ρ'])]
        exact htδ
      have hloc := thinCorner_local_gap hrd hm hC0 hδC hslow hlip (a := x)
        (b := x - (period - h)) (ρ := ρ₀) (τ := period - h) hab hρpos hρδ hh2ρ' htδ
      have hxsub : r (x - (period - h)) = r (x + h) := thinCorner_r_eq_of_coe_eq hr (by
        rw [AddCircle.coe_sub, AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period]
        abel)
      have hsimp : x - (period - h) + (period - h) = x := by ring
      rw [hsimp, hxsub] at hloc
      have hRHS : ‖r x - r (x + h)‖ = ‖r (x + h) - r x‖ := norm_sub_rev _ _
      rw [hRHS] at hloc
      have hηle : η ≤ ρ₀ * (m - 4 * (C * δ)) := min_le_left _ _
      linarith

open LeanEval.KnotTheory.Quadrisecant in
/-- E2(iii) of the lead's `OFat` route (`NOTES_LEAD_OFat.md`, 2026-09-26 01:40): for a smooth knot
`r` without inflection points there are `ε₂ > 0` and `ρ₀ > 0` with `4 * ρ₀ < period` such that for
every knot `r'` within the `C²`-`ε₂`-ball of `r`, the point of `r'` at parameter distance `ρ₀` from
`x` is strictly closer to `r' x` than every point of `r'` whose parameter is at circular distance at
least `2 ρ₀` from `x`.
This is the "thin corner" distance-growth estimate consumed by the `perpChamfer_disjoint` step of
that route.  (The reviewers note that `hinfl` and the `C¹`/`C²` clauses are not needed — `C⁰`
closeness suffices — but they are harmless and keep the `E2` interface uniform.) -/
theorem thinCorner_distance_increasing {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ 4 * ρ₀ < period ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε₂ ∧ ‖velocity r' t - velocity r t‖ < ε₂ ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₂) →
        ∀ x s : ℝ, 2 * ρ₀ ≤ circSep s x →
          ‖r' (x + ρ₀) - r' x‖ < ‖r' s - r' x‖ := by
  obtain ⟨ρ₀, hρ, h4ρ, η, hη, hgap⟩ := thinCorner_core hr
  refine ⟨η / 8, by linarith, ρ₀, hρ, h4ρ, ?_⟩
  intro r' hr' hclose x s hsep
  have hUp : ‖r' (x + ρ₀) - r' x‖ ≤ ‖r (x + ρ₀) - r x‖ + η / 4 := by
    have h1 : r' (x + ρ₀) - r' x
        = (r' (x + ρ₀) - r (x + ρ₀)) + (r (x + ρ₀) - r x) + (r x - r' x) := by abel
    have h2 : ‖r' (x + ρ₀) - r (x + ρ₀)‖ < η / 8 := (hclose (x + ρ₀)).1
    have h3 : ‖r x - r' x‖ < η / 8 := by
      have h := (hclose x).1
      rwa [norm_sub_rev] at h
    rw [h1]
    calc ‖(r' (x + ρ₀) - r (x + ρ₀)) + (r (x + ρ₀) - r x) + (r x - r' x)‖
        ≤ ‖(r' (x + ρ₀) - r (x + ρ₀)) + (r (x + ρ₀) - r x)‖ + ‖r x - r' x‖ :=
          norm_add_le _ _
      _ ≤ (‖r' (x + ρ₀) - r (x + ρ₀)‖ + ‖r (x + ρ₀) - r x‖) + ‖r x - r' x‖ := by
          linarith [norm_add_le (r' (x + ρ₀) - r (x + ρ₀)) (r (x + ρ₀) - r x)]
      _ ≤ η / 8 + ‖r (x + ρ₀) - r x‖ + η / 8 := by linarith
      _ = ‖r (x + ρ₀) - r x‖ + η / 4 := by ring
  have hDp : ‖r s - r x‖ - η / 4 ≤ ‖r' s - r' x‖ := by
    have h1 : r s - r x = (r s - r' s) + (r' s - r' x) + (r' x - r x) := by abel
    have h2 : ‖r s - r' s‖ < η / 8 := by
      have h := (hclose s).1
      rwa [norm_sub_rev] at h
    have h3 : ‖r' x - r x‖ < η / 8 := (hclose x).1
    have h4 : ‖r s - r x‖ ≤ ‖r' s - r' x‖ + η / 4 := by
      rw [h1]
      calc ‖(r s - r' s) + (r' s - r' x) + (r' x - r x)‖
          ≤ ‖(r s - r' s) + (r' s - r' x)‖ + ‖r' x - r x‖ := norm_add_le _ _
        _ ≤ (‖r s - r' s‖ + ‖r' s - r' x‖) + ‖r' x - r x‖ := by
            linarith [norm_add_le (r s - r' s) (r' s - r' x)]
        _ ≤ η / 8 + ‖r' s - r' x‖ + η / 8 := by linarith
        _ = ‖r' s - r' x‖ + η / 4 := by ring
    linarith
  have hg := hgap x s hsep
  linarith

end

end Work.Drive

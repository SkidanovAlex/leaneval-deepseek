import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_wsup_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp Halász crossover integral, and the integrability of the `Wsup` weight

`Work.BMF.halasz_crossover` proves the crossover bound with a spurious additive `1`; here we prove
the sharp form (no `+1`), which is what the assembly `Work.BMF.halasz_majm_of_pieces` consumes, and
the interval-integrability of `α ↦ exp (Wsup f x α T)/α`.

This file deliberately imports `Work.BMF.halasz_wsup_bound` (rather than
`Work.BMF.halasz_crossover`, whose `Wsup_le_Zrcp` would clash) and therefore repeats, under primed
names, the measurability ingredients `continuous_vF`, `Wsup_eq_ciSup_rat` and `measurable_Wsup`.
-/

namespace Work.BMF

open MeasureTheory Real

/-! ## Measurability of `α ↦ Wsup f x α T` -/

/-- Any point `a` of `[-T, T]` is approximated to within `r > 0` by a rational `q` with
`|q| ≤ T`. -/
lemma exists_rat_abs_le_abs_sub_ltX {T a r : ℝ} (ha : |a| ≤ T) (hr : 0 < r) :
    ∃ q : ℚ, |(q:ℝ)| ≤ T ∧ |(q:ℝ) - a| < r := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg a) ha
  rcases lt_or_eq_of_le hT0 with hTpos | hTzero
  · have ha1 := (abs_le.mp ha).1
    have ha2 := (abs_le.mp ha).2
    set A := max (-T) (a - r/2) with hA
    set B := min T (a + r/2) with hB
    have hA1 : -T ≤ A := le_max_left _ _
    have hA2 : a - r/2 ≤ A := le_max_right _ _
    have hB1 : B ≤ T := min_le_left _ _
    have hB2 : B ≤ a + r/2 := min_le_right _ _
    have hAB : A < B := by
      rw [hA, hB]
      apply max_lt
      · exact lt_min (by linarith) (by linarith)
      · exact lt_min (by linarith) (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hAB
    refine ⟨q, ?_, ?_⟩
    · rw [abs_le]; exact ⟨by linarith, by linarith⟩
    · rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
  · have ha0 : a = 0 := by
      have : |a| = 0 := le_antisymm (by linarith [hTzero ▸ ha]) (abs_nonneg a)
      exact abs_eq_zero.mp this
    subst ha0
    exact ⟨0, by simp [← hTzero], by simpa using hr⟩

/-! ## Continuity of the prime sum -/

/-- The prime sum `vF f x s` is continuous as a function of `s : ℂ`. -/
lemma continuous_vFX (f : ℕ → ℂ) (x : ℝ) : Continuous (fun s : ℂ => vF f x s) := by
  unfold vF
  apply continuous_finsetSum
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp0 : (p : ℂ) ≠ 0 := by
    simp [Nat.cast_eq_zero]
    exact hpp.ne_zero
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by simp
  have hc : Continuous (fun s : ℂ => (p : ℂ) ^ (-s)) := by
    have : (fun s : ℂ => (p : ℂ) ^ (-s))
        = fun s : ℂ => Complex.exp ((Real.log p : ℂ) * (-s)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero hp0, hlog]
    rw [this]
    fun_prop
  exact hc.const_mul (f p)

/-! ## `Wsup` as a supremum over rationals -/

/-- `Wsup f x α T` is the supremum of the same expression over the *countable* index set
`{q : ℚ // |q| ≤ T}`. -/
lemma Wsup_eq_ciSup_ratX (f : ℕ → ℂ) (x α T : ℝ) :
    Wsup f x α T = ⨆ (q : {q : ℚ // |(q:ℝ)| ≤ T}),
      (vF f x ((1 + α : ℝ) + (q:ℝ) * Complex.I)).re := by
  have hvF : Continuous (fun s : ℂ => vF f x s) := continuous_vFX f x
  have hcontK : Continuous (fun t : {t : ℝ // |t| ≤ T} =>
      (vF f x ((1 + α : ℝ) + (t:ℝ) * Complex.I)).re) := by
    apply (Complex.continuous_re.comp hvF).comp
    fun_prop
  let g : {q : ℚ // |(q:ℝ)| ≤ T} → {t : ℝ // |t| ≤ T} := fun q => ⟨(q:ℝ), q.2⟩
  have hdens : Dense (Set.range g) := by
    rw [Metric.dense_iff]
    intro t r hr
    obtain ⟨q, hq1, hq2⟩ := exists_rat_abs_le_abs_sub_ltX t.2 hr
    refine ⟨g ⟨q, hq1⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      simpa [g] using hq2
    · exact Set.mem_range_self (⟨q, hq1⟩ : {q : ℚ // |(q:ℝ)| ≤ T})
  have hkey := hdens.ciSup' hcontK
  have hinj : Function.Injective g :=
    fun a b h => Subtype.ext (by simpa [g] using congrArg Subtype.val h)
  let e : {q : ℚ // |(q:ℝ)| ≤ T} ≃ ↥(Set.range g) := Equiv.ofInjective g hinj
  have hkey2 : (⨆ (q : {q : ℚ // |(q:ℝ)| ≤ T}),
        (vF f x ((1 + α : ℝ) + (q:ℝ) * Complex.I)).re)
      = ⨆ (s : ↥(Set.range g)),
          (vF f x ((1 + α : ℝ) + (s: {t:ℝ // |t| ≤ T}).1 * Complex.I)).re :=
    Equiv.iSup_congr e (fun q => by simp [e, g, Equiv.ofInjective])
  unfold Wsup
  rw [← hkey, hkey2]

/-! ## Measurability of `α ↦ Wsup f x α T` -/

theorem Wsup_measurableX (f : ℕ → ℂ) (x T : ℝ) :
    Measurable (fun α : ℝ => Wsup f x α T) := by
  have hvF : Continuous (fun s : ℂ => vF f x s) := continuous_vFX f x
  have hmeas : Measurable (fun α : ℝ => ⨆ (q : {q : ℚ // |(q:ℝ)| ≤ T}),
      (vF f x ((1 + α : ℝ) + (q:ℝ) * Complex.I)).re) := by
    apply Measurable.iSup
    intro q
    have hc : Continuous (fun α : ℝ => ((1 + α : ℝ):ℂ) + (q.1:ℝ) * Complex.I) := by
      fun_prop
    exact ((Complex.continuous_re.comp hvF).comp hc).measurable
  have heq : (fun α : ℝ => Wsup f x α T) = (fun α : ℝ =>
      ⨆ (q : {q : ℚ // |(q:ℝ)| ≤ T}),
        (vF f x ((1 + α : ℝ) + (q:ℝ) * Complex.I)).re) := by
    funext α
    exact Wsup_eq_ciSup_ratX f x α T
  rw [heq]
  exact hmeas

/-! ## The trivial bound `Wsup f x α T ≤ Zrcp x` -/

/-- `∫_a^b x⁻¹ dx = log b - log a` for `0 < a ≤ b`. -/
lemma integral_inv_eq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, x⁻¹) = Real.log b - Real.log a := by
  have hne : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    have hxa : a ≤ x := (Set.uIcc_of_le hab ▸ hx).1
    exact ne_of_gt (lt_of_lt_of_le ha hxa)
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    exact hne x hx
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt Real.log (x⁻¹) x := fun x hx =>
    Real.hasDerivAt_log (hne x hx)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- `∫_c^1 (x^2)⁻¹ dx = c⁻¹ - 1` for `0 < c ≤ 1`. -/
lemma integral_inv_sq_eq (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ x in c..1, (x ^ 2)⁻¹) = c⁻¹ - 1 := by
  have hne : ∀ x ∈ Set.uIcc c 1, x ≠ 0 := by
    intro x hx
    have hxc : c ≤ x := (Set.uIcc_of_le hc1 ▸ hx).1
    exact ne_of_gt (lt_of_lt_of_le hc hxc)
  have hcont : ContinuousOn (fun α : ℝ => (α ^ 2)⁻¹) (Set.uIcc c 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact pow_ne_zero 2 (hne x hx)
  have hderiv : ∀ x ∈ Set.uIcc c 1, HasDerivAt (fun y : ℝ => -(y⁻¹)) ((x ^ 2)⁻¹) x := by
    intro x hx
    have h := (hasDerivAt_inv (hne x hx)).neg
    simpa [Pi.neg_def] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  rw [inv_one]
  ring

/-- **Sharp crossover integral** (no additive `1`): if `g α ≤ Z - m + C₁` and
`g α ≤ Z - log (α * L) + C₁` on `[1/L, 1]` and `α ↦ exp (g α)/α` is interval-integrable there, then
`∫_{1/L}^{1} exp (g α)/α dα ≤ 2 exp (Z + C₁) (1+m) e^{-m}`. -/
theorem sharp_crossover :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ) (L Z m C₁ : ℝ), 1 ≤ L → 0 ≤ m → 0 ≤ C₁ →
        IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) MeasureTheory.volume (1 / L) 1 →
        (∀ α : ℝ, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - m + C₁) →
        (∀ α : ℝ, 1 / L ≤ α → α ≤ 1 → g α ≤ Z - Real.log (α * L) + C₁) →
        (∫ α in (1 / L)..1, Real.exp (g α) / α)
          ≤ C * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro g L Z m C₁ hL hm hC₁ hint h1 h2
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hab : 1 / L ≤ 1 := by rw [div_le_one hLpos]; linarith
  have h1Lpos : 0 < 1 / L := by positivity
  have hexpnn : (0:ℝ) < Real.exp (Z + C₁) := Real.exp_pos _
  rcases le_or_gt (Real.log L) m with hcase | hcase
  · -- `log L ≤ m`: use `h1` on the whole interval
    have hle : ∀ α ∈ Set.Icc (1 / L) 1,
        Real.exp (g α) / α ≤ Real.exp (Z - m + C₁) * α⁻¹ := by
      intro α hα
      have hαpos : 0 < α := lt_of_lt_of_le h1Lpos hα.1
      calc Real.exp (g α) / α ≤ Real.exp (Z - m + C₁) / α :=
            div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (h1 α hα.1 hα.2)) (le_of_lt hαpos)
        _ = Real.exp (Z - m + C₁) * α⁻¹ := by rw [div_eq_mul_inv]
    have hIntG : IntervalIntegrable (fun α : ℝ => Real.exp (Z - m + C₁) * α⁻¹)
        volume (1 / L) 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ continuousOn_id
      intro x hx
      have hx1 : (1:ℝ) / L ≤ x := (Set.uIcc_of_le hab ▸ hx).1
      exact ne_of_gt (lt_of_lt_of_le h1Lpos hx1)
    have hstep := intervalIntegral.integral_mono_on hab hint hIntG hle
    have hval : (∫ α in (1 / L)..1, Real.exp (Z - m + C₁) * α⁻¹)
        = Real.exp (Z - m + C₁) * Real.log L := by
      rw [intervalIntegral.integral_const_mul, integral_inv_eq (1 / L) 1 h1Lpos hab]
      rw [Real.log_div one_ne_zero (ne_of_gt hLpos), Real.log_one]
      ring
    rw [hval] at hstep
    refine hstep.trans ?_
    have hlogLm : Real.log L ≤ m := hcase
    have h5 : Real.exp (Z - m + C₁) * Real.log L
        = Real.exp (Z + C₁) * (Real.log L * Real.exp (-m)) := by
      rw [show Z - m + C₁ = (Z + C₁) + (-m) by ring, Real.exp_add, Real.exp_neg]
      ring
    rw [h5]
    have h7 : Real.log L * Real.exp (-m) ≤ 2 * ((1 + m) * Real.exp (-m)) := by
      have := Real.exp_pos (-m)
      nlinarith
    calc Real.exp (Z + C₁) * (Real.log L * Real.exp (-m))
        ≤ Real.exp (Z + C₁) * (2 * ((1 + m) * Real.exp (-m))) :=
          mul_le_mul_of_nonneg_left h7 hexpnn.le
      _ = 2 * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)) := by ring
  · -- `m < log L`: split at `α₀ = e^m / L`
    set α₀ : ℝ := Real.exp m / L with hα₀
    have hα₀pos : 0 < α₀ := div_pos (Real.exp_pos m) hLpos
    have hα₀L : α₀ * L = Real.exp m := by
      rw [hα₀, div_mul_cancel₀ _ (ne_of_gt hLpos)]
    have hα₀ge : 1 / L ≤ α₀ := by
      rw [hα₀, div_le_div_iff_of_pos_right hLpos]
      simpa using Real.one_le_exp hm
    have hα₀le : α₀ ≤ 1 := by
      rw [hα₀, div_le_one hLpos]
      have h1' : Real.exp m < L := by
        calc Real.exp m < Real.exp (Real.log L) := Real.exp_lt_exp.mpr hcase
          _ = L := Real.exp_log hLpos
      exact h1'.le
    -- integrability of the two halves
    have hintA : IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) volume (1 / L) α₀ := by
      rw [intervalIntegrable_iff] at hint ⊢
      refine hint.mono_set ?_
      intro x hx
      rw [Set.mem_uIoc] at hx ⊢
      rcases hx with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact Or.inl ⟨h1', le_trans h2' hα₀le⟩
      · exfalso; linarith
    have hintB : IntervalIntegrable (fun α : ℝ => Real.exp (g α) / α) volume α₀ 1 := by
      rw [intervalIntegrable_iff] at hint ⊢
      refine hint.mono_set ?_
      intro x hx
      rw [Set.mem_uIoc] at hx ⊢
      rcases hx with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact Or.inl ⟨lt_of_le_of_lt hα₀ge h1', h2'⟩
      · exact Or.inl ⟨lt_of_le_of_lt hab h1', le_trans h2' hα₀le⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hintA hintB]
    -- part 1
    have hpart1 : (∫ α in (1 / L)..α₀, Real.exp (g α) / α) ≤ Real.exp (Z - m + C₁) * m := by
      have hle1 : ∀ α ∈ Set.Icc (1 / L) α₀,
          Real.exp (g α) / α ≤ Real.exp (Z - m + C₁) * α⁻¹ := by
        intro α hα
        have hαpos : 0 < α := lt_of_lt_of_le h1Lpos hα.1
        have hα1 : α ≤ 1 := le_trans hα.2 hα₀le
        calc Real.exp (g α) / α ≤ Real.exp (Z - m + C₁) / α :=
              div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (h1 α hα.1 hα1)) (le_of_lt hαpos)
          _ = Real.exp (Z - m + C₁) * α⁻¹ := by rw [div_eq_mul_inv]
      have hIntG : IntervalIntegrable (fun α : ℝ => Real.exp (Z - m + C₁) * α⁻¹)
          volume (1 / L) α₀ := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.inv₀ continuousOn_id
        intro x hx
        have hx1 : (1:ℝ) / L ≤ x := (Set.uIcc_of_le hα₀ge ▸ hx).1
        exact ne_of_gt (lt_of_lt_of_le h1Lpos hx1)
      have hstep := intervalIntegral.integral_mono_on hα₀ge hintA hIntG hle1
      have hval : (∫ α in (1 / L)..α₀, Real.exp (Z - m + C₁) * α⁻¹)
          = Real.exp (Z - m + C₁) * m := by
        rw [intervalIntegral.integral_const_mul, integral_inv_eq (1 / L) α₀ h1Lpos hα₀ge]
        have hlogα₀ : Real.log α₀ = m - Real.log L := by
          rw [hα₀, Real.log_div (ne_of_gt (Real.exp_pos m)) (ne_of_gt hLpos), Real.log_exp]
        rw [hlogα₀, Real.log_div one_ne_zero (ne_of_gt hLpos), Real.log_one]
        ring
      exact hstep.trans_eq hval
    -- part 2
    have hpart2 : (∫ α in α₀..1, Real.exp (g α) / α) ≤ Real.exp (Z + C₁) * Real.exp (-m) := by
      have hle2 : ∀ α ∈ Set.Icc α₀ 1,
          Real.exp (g α) / α ≤ (Real.exp (Z + C₁) / L) * (α ^ 2)⁻¹ := by
        intro α hα
        have hαpos : 0 < α := lt_of_lt_of_le hα₀pos hα.1
        have hαLpos : 0 < α * L := mul_pos hαpos hLpos
        have hexp : Real.exp (g α) ≤ Real.exp (Z - Real.log (α * L) + C₁) :=
          Real.exp_le_exp.mpr (h2 α (le_trans hα₀ge hα.1) hα.2)
        have hval : Real.exp (Z - Real.log (α * L) + C₁) = Real.exp (Z + C₁) * (α * L)⁻¹ := by
          rw [show Z - Real.log (α * L) + C₁ = (Z + C₁) - Real.log (α * L) by ring, Real.exp_sub,
            Real.exp_log hαLpos, div_eq_mul_inv]
        calc Real.exp (g α) / α ≤ (Real.exp (Z + C₁) * (α * L)⁻¹) / α :=
              div_le_div_of_nonneg_right hexp (le_of_lt hαpos) |>.trans_eq (by rw [hval])
          _ = (Real.exp (Z + C₁) / L) * (α ^ 2)⁻¹ := by
                rw [div_eq_mul_inv, div_eq_mul_inv, pow_two, mul_inv_rev, mul_inv_rev]
                ring
      have hIntG : IntervalIntegrable (fun α : ℝ => (Real.exp (Z + C₁) / L) * (α ^ 2)⁻¹)
          volume α₀ 1 := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.inv₀ (by fun_prop)
        intro x hx
        have hx1 : α₀ ≤ x := (Set.uIcc_of_le hα₀le ▸ hx).1
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hα₀pos hx1))
      have hstep := intervalIntegral.integral_mono_on hα₀le hintB hIntG hle2
      rw [intervalIntegral.integral_const_mul, integral_inv_sq_eq α₀ hα₀pos hα₀le] at hstep
      refine hstep.trans ?_
      have hα₀inv : α₀⁻¹ = L * Real.exp (-m) := by
        rw [hα₀, inv_div, Real.exp_neg, div_eq_mul_inv, mul_comm]
      have hkey : (Real.exp (Z + C₁) / L) * (α₀⁻¹ - 1) ≤ (Real.exp (Z + C₁) / L) * α₀⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      refine hkey.trans ?_
      rw [hα₀inv]
      apply le_of_eq
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hLpos)]
    refine (add_le_add hpart1 hpart2).trans ?_
    have hsum : Real.exp (Z - m + C₁) * m + Real.exp (Z + C₁) * Real.exp (-m)
        = Real.exp (Z + C₁) * ((m + 1) * Real.exp (-m)) := by
      rw [show Z - m + C₁ = (Z + C₁) + (-m) by ring, Real.exp_add, Real.exp_neg]
      ring
    rw [hsum]
    have h8 : ((m + 1) * Real.exp (-m)) ≤ 2 * ((1 + m) * Real.exp (-m)) := by
      have := Real.exp_pos (-m)
      nlinarith
    calc Real.exp (Z + C₁) * ((m + 1) * Real.exp (-m))
        ≤ Real.exp (Z + C₁) * (2 * ((1 + m) * Real.exp (-m))) :=
          mul_le_mul_of_nonneg_left h8 hexpnn.le
      _ = 2 * Real.exp (Z + C₁) * ((1 + m) * Real.exp (-m)) := by ring

/-- `α ↦ exp (Wsup f x α T)/α` is interval-integrable on `[1/log x, 1]` whenever `x ≥ 3`:
`Wsup` is measurable and bounded by `Zrcp x`, and `1/α ≤ log x` on the interval. -/
theorem wsup_intervalIntegrable (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x T : ℝ)
    (hx : 3 ≤ x) (hT : 2 ≤ T) :
    IntervalIntegrable (fun α : ℝ => Real.exp (Wsup f x α T) / α) volume (1 / Real.log x) 1 := by
  rw [intervalIntegrable_iff]
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := le_trans hlog3 (Real.log_le_log (by norm_num) hx)
  have hle : 1 / Real.log x ≤ 1 := by
    rw [div_le_one hlogx]; exact hlogx1
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ ?_ ?_
  · rw [Set.uIoc_of_le hle]; exact measure_Ioc_lt_top
  · exact ((Real.continuous_exp.measurable.comp (Wsup_measurableX f x T)).div measurable_id).aestronglyMeasurable
  · exact Real.exp (Zrcp x) * Real.log x
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun α hα => ?_
    rw [Set.uIoc_of_le hle] at hα
    obtain ⟨hα1, hα2⟩ := hα
    have hαpos : 0 < α := lt_of_lt_of_le (by positivity : (0:ℝ) < 1 / Real.log x) hα1.le
    have hnorm : ‖Real.exp (Wsup f x α T) / α‖ = Real.exp (Wsup f x α T) / α :=
      Real.norm_of_nonneg (by positivity)
    rw [hnorm]
    have hW : Real.exp (Wsup f x α T) ≤ Real.exp (Zrcp x) :=
      Real.exp_le_exp.mpr (Wsup_le_Zrcp f hb x α T (le_of_lt hαpos) (by linarith))
    have hthis : 1 ≤ α * Real.log x := by
      have h := hα1
      rw [div_lt_iff₀ hlogx] at h
      simpa [mul_comm] using h.le
    calc Real.exp (Wsup f x α T) / α ≤ Real.exp (Zrcp x) / α :=
          div_le_div_of_nonneg_right hW (le_of_lt hαpos)
      _ ≤ Real.exp (Zrcp x) * Real.log x := by
          rw [div_le_iff₀ hαpos]
          nlinarith [Real.exp_pos (Zrcp x)]

end Work.BMF

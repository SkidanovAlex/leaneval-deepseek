import Mathlib
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.DhRepel.extremalPackage
import Submission.Work.LinnikAreas.DhRepel.thetaTwo
import Submission.Work.LinnikAreas.DhRepel.extCosFbasic
import Submission.Work.LinnikAreas.DhRepel.laplaceAnalytic
import Submission.Work.LinnikAreas.DhRepel.laplaceDecay
import Submission.Work.LinnikAreas.DhRepel.extCosF_boundaryRe
import Submission.Commons.Analysis.Complex.re_ge_norm_of_boundary
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.ZeroFreeTables.Table4.ThetaNumeric
import Submission.Work.ZeroFreeTables.Table4.HB64Repeated
import Submission.Work.ZeroFreeTables.Table4.HB64LocalGen
import Submission.Work.LinnikAreas.charSum_of_moment_all_k
import Submission.Work.LinnikAreas.moment_cubefree_all_r
import Submission.Work.NumberTheory.DirichletCharacter.quarterBurgess
import Submission.Work.LinnikAreas.DhRepel.extCosFtestProps
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

set_option maxHeartbeats 2000000

open DirichletCharacter Complex
open MeasureTheory intervalIntegral
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Table4

/-- A non-principal character of level `q` forces `2 ≤ q`. -/
private lemma two_le_level_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ ≠ 1) : 2 ≤ q := by
  by_contra hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : q = 1 := by omega
  exact h (DirichletCharacter.level_one' χ hq1)

/-- A non-principal character has level at least `3`. -/
private lemma three_le_level_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  rcases hχne with ⟨a, hne⟩
  have hs : Subsingleton (ZMod N)ˣ := by
    interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

/-! ## The `φ = 1/4` bound for real characters -/

/-- HB Lemma 2.1 (cube-free moduli), copied from `Work.LinnikAreas.cubefree_charSum_all_k` with
narrower imports. -/
theorem cubefree_charSum_all_k_aux (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) :=
  Work.LinnikAreas.charSum_of_moment_all_k
    (fun r hr ε' hε' => Work.LinnikAreas.moment_cubefree_all_r r (by omega) ε' hε') hε k hk

/-- HB Lemma 2.5 with `φ = 1/4` for real characters. -/
theorem quarterBoundReal_aux (k : ℕ) (hk : 3 ≤ k) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
          σ ≤ 1 + Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Cb * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by
  obtain ⟨CB, hCB, hB0⟩ := cubefree_charSum_all_k_aux (ε' / 4) (by positivity) k (by omega)
  have hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε' / 4)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    intro u _ ψ hp hψ hcf N H hN hH hHu
    exact hB0 hcf ψ hp hψ hN hH hHu
  obtain ⟨C, hC, hbound⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_bound_quarter_of_bounded_order
      hε' k hk 2 (by norm_num) hCB hB
  refine ⟨C, hC, ?_⟩
  intro N _inst χ hχ hsq σ t hσlo hσhi
  have hord : orderOf χ ≤ 2 := by
    have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    exact Nat.le_of_dvd (by norm_num) hdvd
  exact hbound χ hχ hord σ t hσlo hσhi

/-! ## The `L52Hyp` provider for real characters with `c = 1/8` -/

/-- For a real character the primitive character inducing it is again real. -/
private theorem primitiveCharacter_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
      (χ.primitiveCharacter ^ 2) = 1 := by
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]
  exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
    (by rw [hmap, DirichletCharacter.changeLevel_one])

/-- HB Lemma 3.1 with `φ = 1/4` (i.e. the constant `1/8`) for **real** characters, in the
`L52Hyp` form used by `§6`, with a window radius `δ` and threshold `q₀` independent of `ε`. -/
theorem l52HypRealQuarter : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 8 + 1 / 1000000 ∧
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
        χ ≠ 1 → χ ^ 2 = 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          Commons.NumberTheory.Linnik.L52Hyp χ c ε δ := by
  have hbound : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
          σ ≤ 1 + Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            Cb * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => quarterBoundReal_aux k hk hε'
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := (1 : ℝ) / 4) (by norm_num)
      (ε := 1 / 1000000) (by norm_num) hbound
  refine ⟨1 / 8 + 1 / 1000000, by norm_num, by norm_num, δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ1 hχ2 ε hε _hε1
  intro s hs1 hs2 hs3
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith only [hδ0, hδ1]
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith only [h1, h2, h3]
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hlogNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hχstar : χ.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ1
  have hcon : 3 ≤ χ.conductor :=
    three_le_level_of_ne_one χ.primitiveCharacter hχstar
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (primitiveCharacter_sq_one χ hχ2)
    (L := Real.log (q : ℝ)) hL₀le hlogNle s hs1 hs2 hs3
  refine hmain'.trans ?_
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith only [hε]

/-! ## Maximality transfer -/

open Work.LinnikContract in
/-- A zero of `L(·, χ.primitiveCharacter)` in `|Im| ≤ 1` is either to the left of the strip, or a
divisor zero of `χ`, or off the critical strip (where `L` does not vanish). -/
private theorem LFunction_zero_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) [NeZero χ.conductor] {u : ℂ}
    (hu : DirichletCharacter.LFunction χ.primitiveCharacter u = 0) (him : |u.im| ≤ 1) :
    u.re ≤ 0 ∨ Work.LinnikContract.zeroMult χ u ≠ 0 ∨ u.re ≤ 0 := by
  by_cases hre : u.re ≤ 0
  · exact Or.inl hre
  · push Not at hre
    by_cases hre1 : u.re < 1
    · exact Or.inr (Or.inl ((Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ hχ).2.2 u hu hre hre1))
    · push Not at hre1
      exact absurd hu (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter
        (Or.inl (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ)) hre1)

open Work.LinnikContract in
/-- If `ρ₀` is a zero of `χ₁` of minimal `λ` among the zeros of the working region other than
`ρ₁`, then every zero of `L(·, χ₁.primitiveCharacter)` in `|Im| ≤ 1` is either `ρ₁` or has real
part at most `Re ρ₀`. -/
theorem maxOfMinOr {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ : χ₁ ≠ 1)
    [NeZero χ₁.conductor] (ρ₁ ρ₀ : ℂ)
    (hmin : ∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ)
    (hρ₀ : IsZ χ₁ ρ₀) :
    ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ 1 →
      u = ρ₁ ∨ u.re ≤ ρ₀.re := by
  have hLpos : 0 < Real.log q := by
    refine Real.log_pos ?_
    have hq2 : 2 ≤ q := two_le_level_of_ne_one hχ
    exact_mod_cast (by omega : 1 < q)
  have hχstar : χ₁.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ
  have hzero₀ : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₀ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hρ₀.2.1)
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hzero₀
  have hρ₀pos : 0 < ρ₀.re := hstrip.1
  intro u hu him
  rcases LFunction_zero_split χ₁ hχ hu him with h | h | h
  · exact Or.inr (le_trans h hρ₀pos.le)
  · by_cases huu : u = ρ₁
    · exact Or.inl huu
    · have hZ : IsZ χ₁ u := ⟨hχ, h, him⟩
      have hle := hmin u hZ huu
      rw [lamOf, lamOf] at hle
      exact Or.inr (by nlinarith only [hle, hLpos])
  · exact Or.inr (le_trans h hρ₀pos.le)

open Work.LinnikContract in
/-- If `ρ₁` is a zero of `χ₁` of minimal `λ` among all zeros of the working region, then every
zero of `L(·, χ₁.primitiveCharacter)` in `|Im| ≤ 1` has real part at most `Re ρ₁`. -/
theorem maxOfMinLe {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ : χ₁ ≠ 1)
    [NeZero χ₁.conductor] (ρ₁ : ℂ)
    (hmin : ∀ ρ : ℂ, IsZ χ₁ ρ → lamOf q ρ₁ ≤ lamOf q ρ)
    (hρ₁ : IsZ χ₁ ρ₁) :
    ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ 1 →
      u.re ≤ ρ₁.re := by
  have hLpos : 0 < Real.log q := by
    refine Real.log_pos ?_
    have hq2 : 2 ≤ q := two_le_level_of_ne_one hχ
    exact_mod_cast (by omega : 1 < q)
  have hχstar : χ₁.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ
  have hzero₁ : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₁ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hρ₁.2.1)
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hzero₁
  have hρ₁pos : 0 < ρ₁.re := hstrip.1
  intro u hu him
  rcases LFunction_zero_split χ₁ hχ hu him with h | h | h
  · exact le_trans h hρ₁pos.le
  · have hZ : IsZ χ₁ u := ⟨hχ, h, him⟩
    have hle := hmin u hZ
    rw [lamOf, lamOf] at hle
    nlinarith only [hle, hLpos]
  · exact le_trans h hρ₁pos.le

open Work.LinnikContract in
/-- A real zero `ρ` of `χ₁` (in the sense of `zeroMult`) lies in the critical strip, equals its real
part, has positive `λ`, and its divisor in the ball of radius `2` is its multiplicity. -/
theorem realZeroData {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ : χ₁ ≠ 1)
    [NeZero χ₁.conductor] {ρ : ℂ} (him : ρ.im = 0) (hzm : Work.LinnikContract.zeroMult χ₁ ρ ≠ 0) :
    (0 < ρ.re ∧ ρ.re < 1) ∧ ρ = ((ρ.re : ℝ) : ℂ) ∧
      Work.LinnikContract.lamOf q ρ = (1 - ρ.re) * Real.log q ∧
      0 < Work.LinnikContract.lamOf q ρ ∧
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2)) ρ = (Work.LinnikContract.zeroMult χ₁ ρ : ℤ) := by
  have hχstar : χ₁.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ
  have hzero : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hzm)
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hzero
  have hLpos : 0 < Real.log q := by
    refine Real.log_pos ?_
    have hq2 : 2 ≤ q := two_le_level_of_ne_one hχ
    exact_mod_cast (by omega : 1 < q)
  have heq : ρ = ((ρ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 2)) ρ = (Work.LinnikContract.zeroMult χ₁ ρ : ℤ) := by
    rw [heq]
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχstar).analyticAt z
    have hmem : ((ρ.re : ℝ) : ℂ) ∈ Metric.closedBall (0:ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hstrip.1]
      linarith only [hstrip.2, hstrip]
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem]
    rfl
  exact ⟨hstrip, heq, rfl, mul_pos (by linarith only [hstrip.2, hstrip]) hLpos, hdiv⟩

/-! ## The five-term monotonicity -/

/-- The five-term combination `∫ e^{bt} f − ∫ e^{(b−a)t} f − ∫ f` is monotone in its parameters
for `f ≥ 0`. -/
theorem fiveTerm_mono {x₀ : ℝ} (hx₀ : 0 ≤ x₀) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t) (hcont : ContinuousOn f (Set.Ici 0))
    {a b L : ℝ} (hab : a ≤ b) (hbL : b ≤ L) :
    (∫ t in (0:ℝ)..x₀, Real.exp (b * t) * f t)
      - (∫ t in (0:ℝ)..x₀, Real.exp ((b - a) * t) * f t)
      - (∫ t in (0:ℝ)..x₀, f t)
    ≤ (∫ t in (0:ℝ)..x₀, Real.exp (L * t) * f t) - 2 * (∫ t in (0:ℝ)..x₀, f t) := by
  have hint : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (c * t) * f t)
      volume (0:ℝ) x₀ := by
    intro c
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx₀]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hcont.mono (fun t ht => ht.1))
  have h1 : (∫ t in (0:ℝ)..x₀, Real.exp (b * t) * f t)
      ≤ (∫ t in (0:ℝ)..x₀, Real.exp (L * t) * f t) := by
    refine integral_mono_on hx₀ (hint b) (hint L) (fun t ht => ?_)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [ht.1, hbL, ht])) (hf t ht)
  have h2' : (∫ t in (0:ℝ)..x₀, Real.exp (0 * t) * f t)
      ≤ (∫ t in (0:ℝ)..x₀, Real.exp ((b - a) * t) * f t) := by
    refine integral_mono_on hx₀ (by simpa using hint 0) (hint (b - a)) (fun t ht => ?_)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [ht.1, hab, ht])) (hf t ht)
  have h2 : (∫ t in (0:ℝ)..x₀, f t) ≤ (∫ t in (0:ℝ)..x₀, Real.exp ((b - a) * t) * f t) := by
    rw [show (∫ t in (0:ℝ)..x₀, f t) = ∫ t in (0:ℝ)..x₀, Real.exp (0 * t) * f t from by
      apply intervalIntegral.integral_congr
      intro t _
      simp]
    exact h2'
  linarith only [h1, h2]

/-! ## The assembly -/

theorem HB82 : Work.ZeroFreeTables.HBLemma8_2 := by
  obtain ⟨c, hcpos, hcle, δ, hδ0, hδ1, qc, hc⟩ := l52HypRealQuarter
  obtain ⟨θ, hθ34, hθ1, heq⟩ := Work.LinnikAreas.DhRepel.thetaTwo
  have hθ0 : 0 < θ := by linarith only [hcpos, hcle, hθ34]
  have hκge : (29 / 100 : ℝ) ≤ Real.cos θ ^ 2 := ThetaNumeric θ hθ34 hθ1 heq
  set lamS : ℝ := 2293 / 1000 with hlamSdef
  have hlamSpos : 0 < lamS := by rw [hlamSdef]; norm_num
  set eps : ℝ := 1 / 1000000 with hepsdef
  have hepspos : 0 < eps := by rw [hepsdef]; norm_num
  have hepsle : eps ≤ 1 := by rw [hepsdef]; norm_num
  set f : ℝ → ℝ := fun t => Commons.NumberTheory.Linnik.extCosF θ lamS t with hfdef
  set x₀ : ℝ := 2 * Work.LinnikAreas.DhRepel.gammaF θ lamS with hx₀def
  have hx₀pos : 0 < x₀ := by
    rw [hx₀def]
    have := Work.LinnikAreas.DhRepel.gammaF_pos hθ0 hθ1 hlamSpos
    linarith only [this]
  have hx₀nn : 0 ≤ x₀ := le_of_lt hx₀pos
  have hf0 : 0 < f 0 :=
    Work.LinnikAreas.DhRepel.extCosF_zero_pos hθ0 hθ1 hlamSpos hθ34 heq
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by
    intro t
    by_cases ht : 0 ≤ t
    · exact Work.LinnikAreas.DhRepel.extCosF_nonneg_of_nonneg hθ0 hθ1 hlamSpos ht
    · push Not at ht
      have h1 : ¬ (0 ≤ t ∧ t ≤ 2 * (θ / (lamS * Real.tan θ))) :=
        fun h => absurd h.1 (not_le.mpr ht)
      show 0 ≤ Commons.NumberTheory.Linnik.extCosF θ lamS t
      rw [Commons.NumberTheory.Linnik.extCosF, if_neg h1]
  have hcont : ContinuousOn f (Set.Ici 0) :=
    Work.LinnikAreas.DhRepel.continuousOn_extCosF hθ0 hθ1 hlamSpos
  have hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0 := by
    intro t ht
    exact Work.LinnikAreas.DhRepel.extCosF_eq_zero_of_ge hθ0 hθ1 hlamSpos ht
  have hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀) := by
    have hcf : ContDiff ℝ 2 (Work.LinnikAreas.DhRepel.closedForm θ lamS) :=
      Work.LinnikAreas.DhRepel.contDiff_closedForm hθ0 hθ1 hlamSpos
    refine hcf.contDiffOn.congr (fun t ht => ?_)
    show f t = Work.LinnikAreas.DhRepel.closedForm θ lamS t
    exact Work.LinnikAreas.DhRepel.extCosF_eq_closedForm hθ0 hθ1 hlamSpos
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  obtain ⟨B, hBnn, hBnd⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B := by
    obtain ⟨B₀, hB₀⟩ :=
      Work.LinnikAreas.DhRepel.exists_iteratedDeriv_two_bound_extCosF hθ0 hθ1 hlamSpos
    refine ⟨max B₀ 0, le_max_right _ _, fun t ht => ?_⟩
    have h := hB₀ t ht
    rw [Commons.NumberTheory.Linnik.iteratedDeriv_ofReal_comp, Complex.norm_real] at h
    rw [Real.norm_eq_abs]
    exact le_trans h (le_max_left _ _)
  have hFnn : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re := by
    intro z hz
    have hx₀' : 0 < 2 * Work.LinnikAreas.DhRepel.gammaF θ lamS := by
      have := Work.LinnikAreas.DhRepel.gammaF_pos hθ0 hθ1 hlamSpos
      linarith only [this]
    have hcont' : ContinuousOn
        (fun t : ℝ => ((Commons.NumberTheory.Linnik.extCosF θ lamS t : ℝ) : ℂ))
        (Set.Icc 0 (2 * Work.LinnikAreas.DhRepel.gammaF θ lamS)) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((Work.LinnikAreas.DhRepel.continuousOn_extCosF hθ0 hθ1 hlamSpos).mono
          (fun x hx => hx.1))
    have hvan : ∀ t : ℝ, 2 * Work.LinnikAreas.DhRepel.gammaF θ lamS ≤ t →
        ((Commons.NumberTheory.Linnik.extCosF θ lamS t : ℝ) : ℂ) = 0 := by
      intro t ht
      rw [Work.LinnikAreas.DhRepel.extCosF_eq_zero_of_ge hθ0 hθ1 hlamSpos
        (by simpa [Work.LinnikAreas.DhRepel.gammaF] using ht)]
      simp
    have hana := Work.LinnikAreas.DhRepel.laplaceAnalytic
      (x₀ := 2 * Work.LinnikAreas.DhRepel.gammaF θ lamS) hx₀' hcont'
    have hdecc := Work.LinnikAreas.DhRepel.laplaceDecay
      (x₀ := 2 * Work.LinnikAreas.DhRepel.gammaF θ lamS) hx₀' hcont'
      (Work.LinnikAreas.DhRepel.contDiffOn_extCosF hθ0 hθ1 hlamSpos)
      (Work.LinnikAreas.DhRepel.exists_iteratedDeriv_two_bound_extCosF hθ0 hθ1 hlamSpos) hvan
    have hbd : ∀ y : ℝ, 0 ≤ ((fun w : ℂ =>
          ∫ t in (0:ℝ)..(2 * (θ / (lamS * Real.tan θ))),
            Complex.exp (-(w * (t : ℂ))) *
              ((Commons.NumberTheory.Linnik.extCosF θ lamS t : ℝ) : ℂ))
          (Complex.I * (y : ℂ))).re
        - ‖(fun _ : ℂ => (0 : ℂ)) (Complex.I * (y : ℂ))‖ := by
      intro y
      have h := Work.LinnikAreas.DhRepel.extCosF_boundaryRe hθ0 hθ1 hlamSpos y
      simpa using h
    have hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, 0 ≤ w.re → R ≤ ‖w‖ →
        ‖(fun w : ℂ => ∫ t in (0:ℝ)..(2 * (θ / (lamS * Real.tan θ))),
          Complex.exp (-(w * (t : ℂ))) *
            ((Commons.NumberTheory.Linnik.extCosF θ lamS t : ℝ) : ℂ)) w‖ < ε
        ∧ ‖(fun _ : ℂ => (0 : ℂ)) w‖ < ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := hdecc ε hε
      exact ⟨R, fun w hw hRw => ⟨hR w hw hRw, by simpa using hε⟩⟩
    have hPL := Commons.Analysis.Complex.re_ge_norm_of_boundary
      (F1 := fun w : ℂ => ∫ t in (0:ℝ)..(2 * (θ / (lamS * Real.tan θ))),
        Complex.exp (-(w * (t : ℂ))) *
          ((Commons.NumberTheory.Linnik.extCosF θ lamS t : ℝ) : ℂ))
      (F2 := fun _ : ℂ => (0 : ℂ)) hana.1 (differentiableOn_const (0 : ℂ)) hana.2
      continuousOn_const hbd hdec
    have h := hPL z hz
    simpa only [hfdef, hx₀def, Work.LinnikAreas.DhRepel.gammaF, norm_zero] using h
  have key : ∀ (lam1 lam2 : ℝ), 0 ≤ lam1 → lam1 ≤ lam2 → lam2 ≤ lamS →
      (0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp (lam2 * t) * f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp ((lam2 - lam1) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 2 * eps)) → False := by
    intro lam1 lam2 h1 h2 h3 hineq
    have hmono := fiveTerm_mono hx₀nn (fun t _ => hfnn t) hcont h2 h3
    have hineq' : 0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp (lamS * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 2 * eps) := by linarith only [hineq, hmono]
    have hzero : (∫ t in (0:ℝ)..(2 * Work.LinnikAreas.DhRepel.gammaF θ lamS),
        Real.exp ((lamS - lamS) * t) * Commons.NumberTheory.Linnik.extCosF θ lamS t)
        = (∫ t in (0:ℝ)..(2 * Work.LinnikAreas.DhRepel.gammaF θ lamS),
            Commons.NumberTheory.Linnik.extCosF θ lamS t) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp
    have hconv : (∫ t in (0:ℝ)..(2 * Work.LinnikAreas.DhRepel.gammaF θ lamS),
            Real.exp (lamS * t) * Commons.NumberTheory.Linnik.extCosF θ lamS t)
        - (∫ t in (0:ℝ)..(2 * Work.LinnikAreas.DhRepel.gammaF θ lamS),
            Real.exp ((lamS - lamS) * t) * Commons.NumberTheory.Linnik.extCosF θ lamS t)
        - (∫ t in (0:ℝ)..(2 * Work.LinnikAreas.DhRepel.gammaF θ lamS),
            Commons.NumberTheory.Linnik.extCosF θ lamS t)
        = (∫ t in (0:ℝ)..x₀, Real.exp (lamS * t) * f t) - 2 * (∫ t in (0:ℝ)..x₀, f t) := by
      rw [hzero]
      simp only [hfdef]
      ring
    have hκ := Work.LinnikAreas.DhRepel.cos_sq_le_of_five_term (lam1 := lamS) (lam2 := lamS)
      (A := c + 2 * eps) hθ0 hθ1 heq hlamSpos (le_of_lt hlamSpos) (le_refl lamS) hf0 (by
        rw [hconv]
        exact hineq')
    have hA' : lamS * (c + 2 * eps) < 29 / 100 := by
      rw [hepsdef] at hcle
      rw [hlamSdef, hepsdef]
      linarith only [hcle, hcpos]
    exact absurd (lt_of_le_of_lt hκ hA') (not_lt.mpr hκge)
  obtain ⟨qRep, hRep⟩ := HB64Repeated x₀ B c hx₀pos hBnn (f := f) hcont hsupp hf2 hBnd hf0
    hfnn hFnn hepspos hδ0 hδ1
  obtain ⟨qLoc, hLoc⟩ := HB64LocalGen x₀ B c hx₀pos hBnn (f := f) hcont hsupp hf2 hBnd hf0
    hfnn hFnn hepspos hδ0 hδ1
  set Lneed : ℝ := max (lamS / δ) (Real.exp (lamS ^ 2)) with hLneeddef
  refine ⟨max (max (max qc qRep) (max qLoc (Nat.ceil (Real.exp Lneed) + 1))) 3, ?_⟩
  intro q hq _inst χ₁ ρ₁ hminw hsq hne1 hρ₁im hρ₁Z
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hsq' : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq
  have hq1 : qc ≤ q := by omega
  have hqRep : qRep ≤ q := by omega
  have hqLoc : qLoc ≤ q := by omega
  have hqbig : Nat.ceil (Real.exp Lneed) + 1 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hLpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL : Lneed ≤ Real.log q := by
    have h1 : Real.exp Lneed ≤ (Nat.ceil (Real.exp Lneed) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp Lneed) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp Lneed) ≤ q)
    calc Lneed = Real.log (Real.exp Lneed) := (Real.log_exp Lneed).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos Lneed) (le_trans h1 h2)
  have hLgeδ : lamS / δ ≤ Real.log q := le_trans (le_max_left _ _) hL
  have hLgeexp : Real.exp (lamS ^ 2) ≤ Real.log q := le_trans (le_max_right _ _) hL
  have hδL : lamS ≤ Real.log q * δ := by
    have h := hLgeδ
    rw [div_le_iff₀ hδ0] at h
    linarith only [h]
  have hloglog : lamS ^ 2 ≤ Real.log (Real.log q) := by
    have h := Real.log_le_log (Real.exp_pos (lamS ^ 2)) hLgeexp
    simpa [Real.log_exp] using h
  have hsqrt : lamS ≤ Real.sqrt (Real.log (Real.log q)) := by
    have h1 : Real.sqrt (lamS ^ 2) ≤ Real.sqrt (Real.log (Real.log q)) :=
      Real.sqrt_le_sqrt hloglog
    rwa [Real.sqrt_sq (le_of_lt hlamSpos)] at h1
  have hmin1 : Work.LinnikContract.IsMin1 χ₁ ρ₁ := hminw.1
  have hbnd : ∀ {β : ℝ} {lam : ℝ}, lam = (1 - β) * Real.log q → 0 ≤ lam → lam ≤ lamS →
      |1 - β| ≤ δ := by
    intro β lam hlam hnn hle
    have h1 : 1 - β = lam / Real.log q := by
      rw [hlam]
      exact (mul_div_cancel_right₀ (1 - β) (ne_of_gt hLpos)).symm
    rw [h1, abs_of_nonneg (div_nonneg hnn (le_of_lt hLpos))]
    rw [div_le_iff₀ hLpos]
    linarith only [hle, hδL]
  have hpt : ∀ {β : ℝ} {lam : ℝ}, lam = (1 - β) * Real.log q → 0 ≤ lam → lam ≤ lamS →
      |1 - β| ≤ Real.sqrt (Real.log (Real.log q)) / Real.log q := by
    intro β lam hlam hnn hle
    have h1 : 1 - β = lam / Real.log q := by
      rw [hlam]
      exact (mul_div_cancel_right₀ (1 - β) (ne_of_gt hLpos)).symm
    rw [h1, abs_of_nonneg (div_nonneg hnn (le_of_lt hLpos))]
    rw [div_le_div_iff_of_pos_right hLpos]
    linarith only [hle, hsqrt]
  constructor
  · -- ### first conjunct: the zero `ρ₁` is repeated
    intro hmult
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h0β, h1β⟩, hβeq, hlam₁, hlam₁pos, hdiv₁⟩ := realZeroData χ₁ hne1 hρ₁im hρ₁Z.2.1
    have hle : Work.LinnikContract.lamOf q ρ₁ ≤ lamS := le_of_lt hcon
    have hb₁ : |1 - ρ₁.re| ≤ δ := hbnd hlam₁ (le_of_lt hlam₁pos) hle
    have hb₁pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log q)) / Real.log q :=
      hpt hlam₁ (le_of_lt hlam₁pos) hle
    have hb₁le : ρ₁.re ≤ 1 := le_of_lt h1β
    have hdiv₁' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2)) ((ρ₁.re : ℝ) : ℂ) ≠ 0 := by
      rw [show ((ρ₁.re : ℝ) : ℂ) = ρ₁ from hβeq.symm, hdiv₁]
      exact_mod_cast hρ₁Z.2.1
    have hmult₁' : 2 ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2)) ((ρ₁.re : ℝ) : ℂ) := by
      rw [show ((ρ₁.re : ℝ) : ℂ) = ρ₁ from hβeq.symm, hdiv₁]
      exact_mod_cast hmult
    have hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
        |u.im| ≤ 1 → u.re ≤ ρ₁.re :=
      maxOfMinLe χ₁ hne1 ρ₁ (fun ρ hZ => hmin1.2 χ₁ ρ hZ) hρ₁Z
    have hineq := hRep (q := q) (β₁ := ρ₁.re) hqRep χ₁ hne1 hsq' hb₁ hb₁le hb₁pt hdiv₁' hmult₁' hmax
      (hc q hq1 χ₁ hne1 hsq eps hepspos hepsle)
    have harg : Real.log q * (1 - ρ₁.re) = Work.LinnikContract.lamOf q ρ₁ := by
      rw [hlam₁]; ring
    rw [harg] at hineq
    have hineq2 : 0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 2 * eps) := by
      linarith only [hineq, hf0, hepspos, hcpos]
    refine key (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₁)
      (le_of_lt hlam₁pos) le_rfl hle ?_
    have hz : (∫ t in (0:ℝ)..x₀,
        Real.exp ((Work.LinnikContract.lamOf q ρ₁ - Work.LinnikContract.lamOf q ρ₁) * t) * f t)
        = (∫ t in (0:ℝ)..x₀, f t) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp
    rw [hz]
    linarith only [hineq2, hineq]
  · -- ### second conjunct: a second real zero `ρ₀`
    intro ρ₀ hZ₀ hne₀ hρ₀im hminρ₀
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h0ρ, h1ρ⟩, hρ₀eq, hlam₀, hlam₀pos, hdiv₀⟩ := realZeroData χ₁ hne1 hρ₀im hZ₀.2.1
    have hle : Work.LinnikContract.lamOf q ρ₀ ≤ lamS := le_of_lt hcon
    have hb' : |1 - ρ₀.re| ≤ δ := hbnd hlam₀ (le_of_lt hlam₀pos) hle
    have hb'pt : |1 - ρ₀.re| ≤ Real.sqrt (Real.log (Real.log q)) / Real.log q :=
      hpt hlam₀ (le_of_lt hlam₀pos) hle
    have hb'le : ρ₀.re ≤ 1 := le_of_lt h1ρ
    have hdiv₀' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2)) ((ρ₀.re : ℝ) : ℂ) ≠ 0 := by
      rw [show ((ρ₀.re : ℝ) : ℂ) = ρ₀ from hρ₀eq.symm, hdiv₀]
      exact_mod_cast hZ₀.2.1
    have hmult₀' : (1 : ℤ) ≤ (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2)) ((ρ₀.re : ℝ) : ℂ) := by
      rw [show ((ρ₀.re : ℝ) : ℂ) = ρ₀ from hρ₀eq.symm, hdiv₀]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hZ₀.2.1
    have hlamle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
      hmin1.2 χ₁ ρ₀ hZ₀
    have hβ'β₁ : ρ₀.re ≤ ρ₁.re := by
      rw [hlam₀, Work.LinnikContract.lamOf] at hlamle
      nlinarith only [hlamle, hLpos]
    obtain ⟨⟨h0β, h1β⟩, hβeq, hlam₁, hlam₁pos, hdiv₁⟩ := realZeroData χ₁ hne1 hρ₁im hρ₁Z.2.1
    have hb₁ : |1 - ρ₁.re| ≤ δ := hbnd hlam₁ (le_of_lt hlam₁pos) (le_trans hlamle hle)
    have hb₁le : ρ₁.re ≤ 1 := le_of_lt h1β
    have hneβ : ((ρ₀.re : ℝ) : ℂ) ≠ ((ρ₁.re : ℝ) : ℂ) := by
      intro h
      exact hne₀ (by rw [hρ₀eq, h]; exact hβeq.symm)
    have hdiv₁' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 2)) ((ρ₁.re : ℝ) : ℂ) ≠ 0 := by
      rw [show ((ρ₁.re : ℝ) : ℂ) = ρ₁ from hβeq.symm, hdiv₁]
      exact_mod_cast hρ₁Z.2.1
    have hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
        |u.im| ≤ 1 → u = ((ρ₁.re : ℝ) : ℂ) ∨ u.re ≤ ρ₀.re := by
      intro u hu him
      rcases maxOfMinOr χ₁ hne1 ρ₁ ρ₀ (fun ρ hZ hne => hminρ₀ ρ hZ hne) hZ₀ u hu him with h | h
      · exact Or.inl (h.trans hβeq)
      · exact Or.inr h
    have hineq := hLoc (q := q) (β₁ := ρ₁.re) (β' := ρ₀.re) hqLoc χ₁ hne1 hsq' hb₁ hb' hβ'β₁
      hb₁le hb'le hb'pt hneβ hdiv₁' hdiv₀' hmult₀' hmax
      (hc q hq1 χ₁ hne1 hsq eps hepspos hepsle)
    have harg₁ : Real.log q * (1 - ρ₁.re) = Work.LinnikContract.lamOf q ρ₁ := by
      rw [hlam₁]; ring
    have harg₀ : Real.log q * (1 - ρ₀.re) = Work.LinnikContract.lamOf q ρ₀ := by
      rw [hlam₀]; ring
    have harg₂ : -((Real.log q * (1 - ρ₁.re)) - (Real.log q * (1 - ρ₀.re)))
        = Work.LinnikContract.lamOf q ρ₀ - Work.LinnikContract.lamOf q ρ₁ := by
      rw [harg₁, harg₀]; ring
    rw [harg₂, harg₀] at hineq
    have hineq2 : 0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp (Work.LinnikContract.lamOf q ρ₀ * t) * f t)
        - (∫ t in (0:ℝ)..x₀,
            Real.exp ((Work.LinnikContract.lamOf q ρ₀ - Work.LinnikContract.lamOf q ρ₁) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t) + f 0 * (c + 2 * eps) := by
      linarith only [hineq, hf0, hepspos, hcpos]
    exact key (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀)
      (le_of_lt hlam₁pos) hlamle hle hineq2

end Work.ZeroFreeTables.Table4

import Mathlib

noncomputable section

namespace Work.TMLECore

open MeasureTheory Filter Topology Set

/-!
## Weyl equidistribution / uniform convergence of Birkhoff averages of an irrational rotation

This file proves that for an irrational `β` and a continuous `1`-periodic function `f`,
the Birkhoff averages `(1/n) ∑_{j<n} f (x + jβ)` converge uniformly to the mean `∫_0^1 f`.

The proof proceeds by Fourier analysis: the trigonometric polynomials are uniformly dense
among continuous `1`-periodic functions (Stone-Weierstrass on the circle), and the averages
of a single trigonometric monomial `x ↦ exp (2πi m x)` are explicitly bounded by a geometric
series which tends to `0` for `m ≠ 0`.
-/

/-- The trigonometric monomial `x ↦ exp (2 * π * I * m * x)`. -/
def trigMon (m : ℤ) (x : ℝ) : ℂ := Complex.exp (↑x * (2 * ↑Real.pi * ↑m * Complex.I))

lemma trigMon_zero_apply (x : ℝ) : trigMon 0 x = 1 := by simp [trigMon]

lemma trigMon_add (m : ℤ) (x y : ℝ) : trigMon m (x + y) = trigMon m x * trigMon m y := by
  simp only [trigMon, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma trigMon_nat_mul (m : ℤ) (n : ℕ) (x : ℝ) :
    trigMon m ((n : ℝ) * x) = (trigMon m x) ^ n := by
  simp only [trigMon, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma norm_trigMon (m : ℤ) (x : ℝ) : ‖trigMon m x‖ = 1 := by
  rw [trigMon, show ↑x * (2 * ↑Real.pi * ↑m * Complex.I) =
    ↑(x * (2 * Real.pi * m)) * Complex.I from by push_cast; ring_nf]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_trigMon (m : ℤ) : Continuous (trigMon m) := by
  unfold trigMon
  fun_prop

lemma trigMon_eq_fourier (m : ℤ) (x : ℝ) : trigMon m x = fourier m (x : UnitAddCircle) := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one, trigMon]
  congr 1
  ring

/-- For irrational `β`, the trigonometric monomial `x ↦ exp (2πi m x)` does not return to its
initial value at `x = β` when `m ≠ 0`. -/
lemma trigMon_ne_one (β : ℝ) (hβ : Irrational β) (m : ℤ) (hm : m ≠ 0) :
    trigMon m β ≠ 1 := by
  intro h
  rw [trigMon, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hI : (↑(2 * Real.pi * m * β) : ℂ) = ↑(2 * Real.pi * n) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [show (↑(2 * Real.pi * m * β) : ℂ) * Complex.I =
        ↑β * (2 * ↑Real.pi * ↑m * Complex.I) from by push_cast; ring_nf,
      show (↑(2 * Real.pi * n) : ℂ) * Complex.I =
        ↑n * (2 * ↑Real.pi * Complex.I) from by push_cast; ring_nf]
    exact hn
  have hR : 2 * Real.pi * m * β = 2 * Real.pi * n := Complex.ofReal_injective hI
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have h3 : (m : ℝ) * β = (n : ℝ) := by
    have hr : (2 * Real.pi) * ((m : ℝ) * β) = (2 * Real.pi) * (n : ℝ) := by
      rw [← mul_assoc]; exact hR
    exact mul_left_cancel₀ hπ hr
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h4 : β = (n : ℝ) / (m : ℝ) := by
    rw [eq_div_iff hmR, mul_comm]
    exact h3
  refine Irrational.ne_rat hβ ((n : ℚ) / (m : ℚ)) ?_
  rw [h4]
  push_cast
  ring

/-- The geometric sum bound: for `z` on the unit circle, `z ≠ 1`,
`‖∑_{j<n} z^j‖ ≤ 2 / ‖z - 1‖`. -/
lemma norm_geom_sum_le {z : ℂ} (hz : z ≠ 1) (hzn : ‖z‖ = 1) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hz1pos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
  have key : (∑ j ∈ Finset.range n, z ^ j) * (z - 1) = z ^ n - 1 := by
    rw [Finset.sum_mul]
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have h2 : ‖∑ j ∈ Finset.range n, z ^ j‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, key]
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖1‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, hzn, one_pow, norm_one]
      _ = 2 := by norm_num
  rw [le_div_iff₀ hz1pos]
  exact h2

/-- The integral of a trigonometric monomial over a period. -/
lemma integral_trigMon (m : ℤ) :
    ∫ x in (0 : ℝ)..1, trigMon m x = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [trigMon_zero_apply]
  · simp only [hm, if_false]
    set c : ℂ := 2 * ↑Real.pi * ↑m * Complex.I with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      have hmC : (↑m : ℂ) ≠ 0 := by exact_mod_cast hm
      have hpiC : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpiC) hmC) Complex.I_ne_zero
    have hexp : Complex.exp c = 1 := Complex.exp_eq_one_iff.mpr ⟨m, by rw [hc]; ring⟩
    have hderiv : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => Complex.exp (↑y * c) / c) (Complex.exp (↑x * c)) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℂ => y * c) c (↑x) := by
        simpa using (hasDerivAt_id (↑x : ℂ)).mul_const c
      have h2 : HasDerivAt (fun y : ℝ => ↑y * c) c x := h1.comp_ofReal
      have h3 : HasDerivAt (fun y : ℝ => Complex.exp (↑y * c))
          (Complex.exp (↑x * c) * c) x :=
        (Complex.hasDerivAt_exp (↑x * c)).comp x h2
      have h4 := h3.div_const c
      rwa [mul_div_cancel_right₀ _ hcne] at h4
    have hint : IntervalIntegrable (fun y : ℝ => Complex.exp (↑y * c)) volume (0 : ℝ) 1 :=
      (by fun_prop : Continuous fun y : ℝ => Complex.exp (↑y * c)).intervalIntegrable _ _
    have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun x _ => hderiv x) hint
    have hcongr : ∫ x in (0 : ℝ)..1, trigMon m x = ∫ x in (0 : ℝ)..1, Complex.exp (↑x * c) :=
      rfl
    rw [hcongr, hmain]
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      hexp]
    rw [sub_self]

/-- A finite complex linear combination of trigonometric monomials, evaluated at `x`. -/
def trigEval (l : ℤ →₀ ℂ) (x : ℝ) : ℂ := l.sum fun m c => c * trigMon m x

lemma trigEval_add (l l' : ℤ →₀ ℂ) (x : ℝ) :
    trigEval (l + l') x = trigEval l x + trigEval l' x := by
  rw [trigEval, Finsupp.sum_add_index']
  · rw [trigEval, trigEval]
  · intro m; simp
  · intro m a b; ring

lemma trigEval_zero (x : ℝ) : trigEval 0 x = 0 := by
  simp [trigEval]

lemma trigEval_single (m : ℤ) (c : ℂ) (x : ℝ) :
    trigEval (Finsupp.single m c) x = c * trigMon m x := by
  rw [trigEval, Finsupp.sum_single_index]
  simp

lemma continuous_trigEval (l : ℤ →₀ ℂ) : Continuous (trigEval l) := by
  induction l using Finsupp.induction_linear with
  | zero =>
      have h : trigEval 0 = fun _ : ℝ => (0 : ℂ) := by
        funext x; exact trigEval_zero x
      rw [h]; exact continuous_const
  | add l₁ l₂ ih₁ ih₂ =>
      have h : trigEval (l₁ + l₂) = trigEval l₁ + trigEval l₂ := by
        funext x; exact trigEval_add l₁ l₂ x
      rw [h]; exact ih₁.add ih₂
  | single m c =>
      have h : trigEval (Finsupp.single m c) = fun x : ℝ => c * trigMon m x := by
        funext x; exact trigEval_single m c x
      rw [h]; exact (continuous_trigMon m).const_mul c

/-- `Good β g` means: `g` is continuous and its Birkhoff averages along the rotation by `β`
converge uniformly to the mean `∫_0^1 g`. -/
def Good (β : ℝ) (g : ℝ → ℂ) : Prop :=
  Continuous g ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
    dist (∫ y in (0 : ℝ)..1, g y)
      ((∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ)) < ε


lemma good_zero (β : ℝ) : Good β (fun _ : ℝ => (0 : ℂ)) := by
  refine ⟨continuous_const, fun ε hε => ⟨1, fun n hn x => ?_⟩⟩
  simpa using hε

lemma good_add {β : ℝ} {f g : ℝ → ℂ} (hf : Good β f) (hg : Good β g) :
    Good β (f + g) := by
  refine ⟨hf.1.add hg.1, fun ε hε => ?_⟩
  obtain ⟨Nf, hNf⟩ := hf.2 (ε / 2) (by linarith)
  obtain ⟨Ng, hNg⟩ := hg.2 (ε / 2) (by linarith)
  refine ⟨max Nf Ng, fun n hn x => ?_⟩
  have hfn := hNf n (le_trans (le_max_left _ _) hn) x
  have hgn := hNg n (le_trans (le_max_right _ _) hn) x
  have hInt : ∫ y in (0 : ℝ)..1, (f + g) y =
      (∫ y in (0 : ℝ)..1, f y) + ∫ y in (0 : ℝ)..1, g y :=
    intervalIntegral.integral_add (hf.1.intervalIntegrable _ _) (hg.1.intervalIntegrable _ _)
  have hSum : (∑ j ∈ Finset.range n, (f + g) (x + (j : ℝ) * β)) / (n : ℂ) =
      (∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℂ) +
        (∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ) := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]
  rw [hInt, hSum]
  calc dist ((∫ y in (0 : ℝ)..1, f y) + ∫ y in (0 : ℝ)..1, g y)
        ((∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℂ) +
          (∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ))
      ≤ dist (∫ y in (0 : ℝ)..1, f y) ((∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℂ)) +
        dist (∫ y in (0 : ℝ)..1, g y)
          ((∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ)) :=
        dist_add_add_le _ _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfn hgn
    _ = ε := by ring

lemma good_const_mul {β : ℝ} {f : ℝ → ℂ} (c : ℂ) (hf : Good β f) :
    Good β (fun x => c * f x) := by
  refine ⟨hf.1.const_mul c, fun ε hε => ?_⟩
  have hpos : 0 < ε / (‖c‖ + 1) := div_pos hε (by linarith [norm_nonneg c])
  obtain ⟨N, hN⟩ := hf.2 (ε / (‖c‖ + 1)) hpos
  refine ⟨N, fun n hn x => ?_⟩
  have h := hN n hn x
  have hInt : ∫ y in (0 : ℝ)..1, c * f y = c * ∫ y in (0 : ℝ)..1, f y :=
    intervalIntegral.integral_const_mul c f
  have hSum : (∑ j ∈ Finset.range n, c * f (x + (j : ℝ) * β)) / (n : ℂ) =
      c * ((∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℂ)) := by
    rw [← Finset.mul_sum, mul_div_assoc]
  change dist (∫ y in (0 : ℝ)..1, c * f y)
    ((∑ j ∈ Finset.range n, c * f (x + (j : ℝ) * β)) / (n : ℂ)) < ε
  rw [hInt, hSum]
  rw [dist_eq_norm] at h
  rw [dist_eq_norm]
  rw [show c * (∫ y in (0 : ℝ)..1, f y) -
      c * ((∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℂ)) =
      c * ((∫ y in (0 : ℝ)..1, f y) -
        (∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℂ)) from by ring, norm_mul]
  have hle : ‖c‖ * (ε / (‖c‖ + 1)) ≤ ε := by
    have h4 : ‖c‖ / (‖c‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg c]
    calc ‖c‖ * (ε / (‖c‖ + 1)) = ε * (‖c‖ / (‖c‖ + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h4 hε.le
      _ = ε := by ring
  rcases eq_or_lt_of_le (norm_nonneg c) with hc0 | hcpos
  · rw [← hc0, zero_mul]
    exact hε
  · exact lt_of_lt_of_le (mul_lt_mul_of_pos_left h hcpos) hle

lemma good_of_zero_bound {β : ℝ} {g : ℝ → ℂ} (hg : Continuous g) (C : ℝ)
    (hint : ∫ y in (0 : ℝ)..1, g y = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
      ‖(∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ)‖ ≤ C / n) :
    Good β g := by
  refine ⟨hg, fun ε hε => ?_⟩
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in atTop, C / (n : ℝ) < ε := (tendsto_order.1 hlim).2 ε hε
  have h2 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨N, fun n hn x => ?_⟩
  obtain ⟨hlt, hge⟩ := hN n hn
  rw [dist_eq_norm, hint, zero_sub, norm_neg]
  exact lt_of_le_of_lt (hb n hge x) hlt

lemma good_trigMon (β : ℝ) (hβ : Irrational β) (m : ℤ) : Good β (trigMon m) := by
  by_cases hm : m = 0
  · subst hm
    refine ⟨continuous_trigMon 0, fun ε hε => ⟨1, fun n hn x => ?_⟩⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hInt : ∫ y in (0 : ℝ)..1, trigMon 0 y = 1 := by rw [integral_trigMon]; simp
    have hS : (∑ j ∈ Finset.range n, trigMon 0 (x + (j : ℝ) * β)) = (n : ℂ) := by
      simp [trigMon_zero_apply, Finset.sum_const, nsmul_eq_mul]
    rw [dist_eq_norm, hInt, hS, div_self hn0, sub_self, norm_zero]
    exact hε
  · have hz : trigMon m β ≠ 1 := trigMon_ne_one β hβ m hm
    have hzn : ‖trigMon m β‖ = 1 := norm_trigMon m β
    have hInt : ∫ y in (0 : ℝ)..1, trigMon m y = 0 := by rw [integral_trigMon]; simp [hm]
    refine good_of_zero_bound (continuous_trigMon m) (2 / ‖trigMon m β - 1‖) hInt ?_
    intro n hn x
    have hsum : (∑ j ∈ Finset.range n, trigMon m (x + (j : ℝ) * β)) =
        trigMon m x * ∑ j ∈ Finset.range n, (trigMon m β) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [trigMon_add, trigMon_nat_mul]
    rw [hsum, norm_div, norm_mul, norm_trigMon, one_mul, Complex.norm_natCast]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (norm_geom_sum_le hz hzn n) hnpos.le

lemma good_trigEval (β : ℝ) (hβ : Irrational β) (l : ℤ →₀ ℂ) : Good β (trigEval l) := by
  induction l using Finsupp.induction_linear with
  | zero =>
      have h : trigEval 0 = fun _ : ℝ => (0 : ℂ) := by
        funext x; exact trigEval_zero x
      rw [h]; exact good_zero β
  | add l₁ l₂ ih₁ ih₂ =>
      have h : trigEval (l₁ + l₂) = trigEval l₁ + trigEval l₂ := by
        funext x; exact trigEval_add l₁ l₂ x
      rw [h]; exact good_add ih₁ ih₂
  | single m c =>
      have h : trigEval (Finsupp.single m c) = fun x : ℝ => c * trigMon m x := by
        funext x; exact trigEval_single m c x
      rw [h]; exact good_const_mul c (good_trigMon β hβ m)

/-- The evaluation at `(x : UnitAddCircle)` of a finite linear combination of the Fourier
monomials `fourier m` is `trigEval l x`. -/
lemma linearCombination_fourier_apply (l : ℤ →₀ ℂ) (x : ℝ) :
    (Finsupp.linearCombination ℂ (fun m : ℤ => (fourier m : C(UnitAddCircle, ℂ))) l)
      (x : UnitAddCircle) = trigEval l x := by
  rw [trigEval]
  set ev : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => F (x : UnitAddCircle)
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl } with hev
  have h1 := LinearMap.map_finsupp_linearCombination (f := ev)
    (g := fun m : ℤ => (fourier m : C(UnitAddCircle, ℂ))) l
  have h2 : ev (Finsupp.linearCombination ℂ
      (fun m : ℤ => (fourier m : C(UnitAddCircle, ℂ))) l) =
      (Finsupp.linearCombination ℂ
        (fun m : ℤ => (fourier m : C(UnitAddCircle, ℂ))) l) (x : UnitAddCircle) := rfl
  rw [← h2, h1, Finsupp.linearCombination_apply]
  apply Finsupp.sum_congr
  intro m hm
  show (l m) • (ev (fourier m)) = (l m) • (trigMon m x)
  congr 1
  rw [trigMon]
  change (fourier m) (x : UnitAddCircle) = Complex.exp (↑x * (2 * ↑Real.pi * ↑m * Complex.I))
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  congr 1
  ring_nf

/-- Any continuous `1`-periodic complex function is uniformly close to a finite linear
combination of trigonometric monomials. This is the density of the span of the Fourier
monomials in `C(AddCircle 1, ℂ)` (`span_fourier_closure_eq_top`), transported to `ℝ` through
the quotient map `ℝ → AddCircle 1`. -/
lemma exists_trigEval_close (g : ℝ → ℂ) (hg : Continuous g) (hper : ∀ x : ℝ, g (x + 1) = g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ l : ℤ →₀ ℂ, ∀ x : ℝ, ‖g x - trigEval l x‖ < ε := by
  have hp : Function.Periodic g 1 := hper
  have hcont : Continuous hp.lift := by
    have hq := QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))
    rw [hq.continuous_iff]
    have : hp.lift ∘ QuotientAddGroup.mk = g := by
      ext x; exact Function.Periodic.lift_coe hp x
    rw [this]; exact hg
  let G : C(UnitAddCircle, ℂ) := ⟨hp.lift, hcont⟩
  have hGeval : ∀ x : ℝ, G (x : UnitAddCircle) = g x :=
    fun x => Function.Periodic.lift_coe hp x
  have hmem : G ∈ (Submodule.span ℂ
      (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; exact Submodule.mem_top
  have hmem' : G ∈ closure (((Submodule.span ℂ
      (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ)))) : Set (C(UnitAddCircle, ℂ)))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  rw [Metric.mem_closure_iff] at hmem'
  obtain ⟨P, hP, hdist⟩ := hmem' ε hε
  obtain ⟨l, -, hl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ
    (v := (fourier : ℤ → C(UnitAddCircle, ℂ))) (s := Set.univ)).mp (by simpa using hP)
  refine ⟨l, fun x => ?_⟩
  have hd := ContinuousMap.dist_apply_le_dist (f := G) (g := P) (x := (x : UnitAddCircle))
  rw [hGeval x, ← hl, linearCombination_fourier_apply l x, dist_eq_norm] at hd
  rw [← hl] at hdist
  exact lt_of_le_of_lt hd hdist

/-- Uniform convergence to a constant, in metric `ε`-`N` form. -/
lemma tendstoUniformly_atTop_iff {α E : Type*} [PseudoMetricSpace E]
    (F : ℕ → α → E) (G : α → E) :
    TendstoUniformly F G atTop ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : α,
      dist (G x) (F n x) < ε := by
  rw [HasBasis.tendstoUniformly_iff_of_uniformity Metric.uniformity_basis_dist]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
    exact ⟨N, fun n hn x => hN n hn x⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact eventually_atTop.mpr ⟨N, fun n hn x => hN n hn x⟩

lemma good_iff_tendstoUniformly (β : ℝ) (g : ℝ → ℂ) :
    Good β g ↔ Continuous g ∧ TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ))
      (fun _ => ∫ y in (0 : ℝ)..1, g y) atTop := by
  rw [tendstoUniformly_atTop_iff, Good]

/-- Weyl's equidistribution theorem, complex valued version. -/
theorem weyl_uniform_complex (β : ℝ) (hβ : Irrational β) (g : ℝ → ℂ) (hg : Continuous g)
    (hper : ∀ x : ℝ, g (x + 1) = g x) :
    TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ))
      (fun _ => ∫ y in (0 : ℝ)..1, g y) atTop := by
  rw [tendstoUniformly_atTop_iff]
  intro ε hε
  obtain ⟨l, hl⟩ := exists_trigEval_close g hg hper (ε / 4) (by linarith)
  have hPl : Good β (trigEval l) := good_trigEval β hβ l
  obtain ⟨N, hN⟩ := hPl.2 (ε / 2) (by linarith)
  refine ⟨max N 1, fun n hn x => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 := hN n hnN x
  have t1 : dist (∫ y in (0 : ℝ)..1, g y) (∫ y in (0 : ℝ)..1, trigEval l y) ≤ ε / 4 := by
    rw [dist_eq_norm, ← intervalIntegral.integral_sub (hg.intervalIntegrable _ _)
      (hPl.1.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := fun y : ℝ => g y - trigEval l y) (C := ε / 4)
      (fun y _ => le_of_lt (hl y))
    simpa using this
  have t3 : dist ((∑ j ∈ Finset.range n, trigEval l (x + (j : ℝ) * β)) / (n : ℂ))
      ((∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ)) ≤ ε / 4 := by
    rw [dist_eq_norm, ← sub_div, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
    have h1 : ‖∑ j ∈ Finset.range n,
        (trigEval l (x + (j : ℝ) * β) - g (x + (j : ℝ) * β))‖ ≤ (n : ℝ) * (ε / 4) := by
      calc ‖∑ j ∈ Finset.range n,
            (trigEval l (x + (j : ℝ) * β) - g (x + (j : ℝ) * β))‖
          ≤ ∑ j ∈ Finset.range n,
              ‖trigEval l (x + (j : ℝ) * β) - g (x + (j : ℝ) * β)‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.range n, (ε / 4) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_sub_rev]
            exact le_of_lt (hl _)
        _ = (n : ℝ) * (ε / 4) := by simp [Finset.sum_const, nsmul_eq_mul]
    have hdiv := div_le_div_of_nonneg_right h1 hnpos.le
    rwa [mul_div_cancel_left₀ _ (ne_of_gt hnpos)] at hdiv
  calc dist (∫ y in (0 : ℝ)..1, g y)
        ((∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ))
      ≤ dist (∫ y in (0 : ℝ)..1, g y) (∫ y in (0 : ℝ)..1, trigEval l y) +
          dist (∫ y in (0 : ℝ)..1, trigEval l y)
            ((∑ j ∈ Finset.range n, trigEval l (x + (j : ℝ) * β)) / (n : ℂ)) +
          dist ((∑ j ∈ Finset.range n, trigEval l (x + (j : ℝ) * β)) / (n : ℂ))
            ((∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ)) := by
        have h1 := dist_triangle (∫ y in (0 : ℝ)..1, g y)
          ((∑ j ∈ Finset.range n, trigEval l (x + (j : ℝ) * β)) / (n : ℂ))
          ((∑ j ∈ Finset.range n, g (x + (j : ℝ) * β)) / (n : ℂ))
        have h2 := dist_triangle (∫ y in (0 : ℝ)..1, g y)
          (∫ y in (0 : ℝ)..1, trigEval l y)
          ((∑ j ∈ Finset.range n, trigEval l (x + (j : ℝ) * β)) / (n : ℂ))
        linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by linarith
    _ = ε := by ring

theorem weyl_uniform (β : ℝ) (hβ : Irrational β) (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ x : ℝ, f (x + 1) = f x) :
    TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℝ))
      (fun _ => ∫ x in (0 : ℝ)..1, f x) atTop := by
  have hc := weyl_uniform_complex β hβ (fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp hf) (fun x => by rw [hper x])
  rw [tendstoUniformly_atTop_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have h := hN n hn x
  rw [dist_eq_norm] at h
  rw [dist_eq_norm, ← Complex.norm_real, Complex.ofReal_sub,
    show (↑((∑ j ∈ Finset.range n, f (x + (j : ℝ) * β)) / (n : ℝ)) : ℂ) =
      (∑ j ∈ Finset.range n, (f (x + (j : ℝ) * β) : ℂ)) / (n : ℂ) from by
        rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast],
    ← intervalIntegral.integral_ofReal]
  exact h

end Work.TMLECore

import Mathlib

/-!
# Helper lemmas for one-dimensional Poisson summation with a periodic weight

This file collects the analytic and algebraic ingredients used in
`Work.FIArea5.S16.poisson_periodic_1d`.
-/

open Filter Asymptotics
open scoped FourierTransform Real

namespace Work.FIArea5.S16

noncomputable def intResEquiv (q : ℕ) (hq : 0 < q) : ℤ ≃ Fin q × ℤ where
  toFun n := (⟨(n % (q:ℤ)).toNat, by
      have h1 : 0 ≤ n % (q:ℤ) := Int.emod_nonneg n (by exact_mod_cast hq.ne')
      exact (Int.toNat_lt h1).2 (Int.emod_lt_of_pos n (by exact_mod_cast hq))⟩,
    n / (q:ℤ))
  invFun p := (q:ℤ) * p.2 + ((p.1 : ℕ) : ℤ)
  left_inv n := by
    have h2 : ((n % (q:ℤ)).toNat : ℤ) = n % (q:ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hq.ne'))
    have h3 := Int.emod_add_mul_ediv n (q:ℤ)
    simp only
    omega
  right_inv p := by
    obtain ⟨a, m⟩ := p
    have hq' : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have h0 : (0:ℤ) ≤ ((a:ℕ):ℤ) := by positivity
    have hlt : ((a:ℕ):ℤ) < (q:ℤ) := by exact_mod_cast a.isLt
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have hmod : ((q:ℤ) * m + ((a:ℕ):ℤ)) % (q:ℤ) = ((a:ℕ):ℤ) := by
        rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 hlt]
      show (((q:ℤ) * m + ((a:ℕ):ℤ)) % (q:ℤ)).toNat = (a:ℕ)
      rw [hmod, Int.toNat_natCast]
    · show ((q:ℤ) * m + ((a:ℕ):ℤ)) / (q:ℤ) = m
      rw [add_comm, Int.add_mul_ediv_left ((a:ℕ):ℤ) m hq',
        Int.ediv_eq_zero_of_lt h0 hlt, zero_add]

/-- Reindex a sum over `ℤ` as a sum over the `q` residue classes. -/
lemma tsum_int_eq_sum_residues {q : ℕ} (hq : 0 < q) (F : ℤ → ℂ) (hF : Summable F) :
    ∑' n : ℤ, F n = ∑' a : Fin q, ∑' m : ℤ, F ((q:ℤ) * m + ((a:ℕ):ℤ)) := by
  set φ : Fin q × ℤ ≃ ℤ := (intResEquiv q hq).symm with hφ
  have hsumm : Summable (fun p : Fin q × ℤ => F (φ p)) := (Equiv.summable_iff φ).2 hF
  rw [← Equiv.tsum_eq φ F, Summable.tsum_prod hsumm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro c
  rw [hφ]
  rfl

/-- Fourier transform of an affinely rescaled function. -/
lemma fourier_affine (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => f (Q * x + a)) ξ
      = (Q : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (a * ξ) / Q) *
          𝓕 f (ξ / Q) := by
  have hQc : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  have h1 : (∫ (v : ℝ), Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * f (Q * v + a))
      = (Q:ℂ)⁻¹ * ∫ (y : ℝ), Complex.exp (↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I) * f (y + a) := by
    set ψ : ℝ → ℂ := fun y => Complex.exp (↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I) * f (y + a) with hψ
    have hφ : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * f (Q * v + a))
        = fun v : ℝ => ψ (Q * v) := by
      funext v
      simp only [hψ]
      congr 1
      congr 1
      push_cast
      field_simp
    rw [hφ, MeasureTheory.Measure.integral_comp_mul_left]
    rw [hψ]
    simp only [abs_of_pos (inv_pos.mpr hQ), Complex.real_smul, Complex.ofReal_inv]
  have h2 : (∫ (y : ℝ), Complex.exp (↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I) * f (y + a))
      = Complex.exp (2 * Real.pi * Complex.I * (a * ξ) / Q) *
          ∫ (y : ℝ), Complex.exp (↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I) * f y := by
    set θ : ℝ → ℂ := fun y => Complex.exp (↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I) * f y with hθ
    have hpt : ∀ y : ℝ, Complex.exp (↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I) * f (y + a)
        = Complex.exp (2 * Real.pi * Complex.I * (a * ξ) / Q) * θ (y + a) := by
      intro y
      have hAD : ↑(-2 * Real.pi * y * (ξ / Q)) * Complex.I
          = (2 * Real.pi * Complex.I * (a * ξ) / Q) + (↑(-2 * Real.pi * (y + a) * (ξ / Q)) * Complex.I) := by
        push_cast
        field_simp
        ring
      simp only [hθ]
      rw [hAD, Complex.exp_add, mul_assoc]
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [hθ]
    exact MeasureTheory.integral_add_right_eq_self (fun t : ℝ => Complex.exp (↑(-2 * Real.pi * t * (ξ / Q)) * Complex.I) * f t) a
  rw [h1, h2]
  ring

/-- The affine rescaling of a function decaying like `|x|^{-b}` also decays like `|x|^{-b}`. -/
lemma isBigO_abs_affine_rpow {b Q a : ℝ} (hb : 0 < b) (hQ : 0 < Q) :
    (fun x : ℝ => |Q*x+a|^(-b)) =O[Filter.cocompact ℝ] (fun x : ℝ => |x|^(-b)) := by
  have hX : (0:ℝ) ≤ 2*|a|/Q := by positivity
  refine Asymptotics.IsBigO.of_bound ((Q/2)^(-b)) ?_
  have key : ∀ x : ℝ, (2*|a|/Q) ≤ |x| → |Q*x+a|^(-b) ≤ (Q/2)^(-b) * |x|^(-b) := by
    intro x hx
    rcases eq_or_ne |x| 0 with hx0 | hx0
    · have hx' : x = 0 := abs_eq_zero.mp hx0
      have ha0 : a = 0 := by
        have h2 : 2*|a| ≤ |x| * Q := (div_le_iff₀ hQ).mp hx
        rw [hx0, zero_mul] at h2
        exact abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg a))
      subst hx'; subst ha0
      simp [Real.zero_rpow, hb.ne']
    · have hxpos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm hx0)
      have h1 : Q * |x| / 2 ≤ |Q*x+a| := by
        have h2 : |Q*x| - |a| ≤ |Q*x+a| := by
          have hh := abs_abs_sub_abs_le_abs_sub (Q*x) (-a)
          rw [abs_neg] at hh
          calc |Q*x| - |a| ≤ abs (|Q*x| - |a|) := le_abs_self _
            _ ≤ |Q*x - (-a)| := hh
            _ = |Q*x+a| := by ring_nf
        have h3 : |a| ≤ Q*|x|/2 := by
          have h4 : 2*|a| ≤ |x| * Q := (div_le_iff₀ hQ).mp hx
          nlinarith [abs_nonneg a]
        have hthis : |Q*x| = Q*|x| := by rw [abs_mul, abs_of_pos hQ]
        linarith [h2, h3, hthis]
      have h4 : 0 < Q*|x|/2 := by nlinarith [hQ, hxpos]
      calc |Q*x+a|^(-b) ≤ (Q*|x|/2)^(-b) := Real.rpow_le_rpow_of_nonpos h4 h1 (by linarith)
        _ = (Q/2 * |x|)^(-b) := by ring_nf
        _ = (Q/2)^(-b) * |x|^(-b) := Real.mul_rpow (by linarith) (abs_nonneg x)
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup]
  constructor
  · rw [Filter.eventually_atBot]
    refine ⟨-(2*|a|/Q), fun x hx => ?_⟩
    rw [show ‖|Q*x+a|^(-b)‖ = |Q*x+a|^(-b) from Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        show ‖|x|^(-b)‖ = |x|^(-b) from Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    refine key x ?_
    rw [show |x| = -x from abs_of_nonpos (by linarith)]
    linarith
  · rw [Filter.eventually_atTop]
    refine ⟨2*|a|/Q, fun x hx => ?_⟩
    rw [show ‖|Q*x+a|^(-b)‖ = |Q*x+a|^(-b) from Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        show ‖|x|^(-b)‖ = |x|^(-b) from Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    refine key x ?_
    rw [show |x| = x from abs_of_nonneg (by linarith)]
    exact hx

/-- The map `x ↦ Q * x + a` tends to the cocompact filter for `Q > 0`. -/
lemma tendsto_affine_cocompact {Q a : ℝ} (hQ : 0 < Q) :
    Filter.Tendsto (fun x : ℝ => Q*x+a) (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
  exact ⟨(tendsto_atBot_add_const_right atBot a (Filter.Tendsto.const_mul_atBot hQ tendsto_id)).mono_right le_sup_left,
         (tendsto_atTop_add_const_right atTop a (Filter.Tendsto.const_mul_atTop hQ tendsto_id)).mono_right le_sup_right⟩

/-- Decay is preserved by affine rescaling of the argument. -/
lemma isBigO_comp_affine {f : ℝ → ℂ} {b : ℝ} (hb : 0 < b)
    (hf : f =O[Filter.cocompact ℝ] fun x : ℝ => |x|^(-b)) {Q a : ℝ} (hQ : 0 < Q) :
    (fun x : ℝ => f (Q*x+a)) =O[Filter.cocompact ℝ] fun x : ℝ => |x|^(-b) := by
  have h1 := hf.comp_tendsto (tendsto_affine_cocompact (Q := Q) (a := a) hQ)
  simp only [Function.comp_def] at h1
  exact h1.trans (isBigO_abs_affine_rpow hb hQ)

/-- Decay is preserved by rescaling the argument by `x ↦ x / Q`, `Q > 0`. -/
lemma isBigO_comp_div {f : ℝ → ℂ} {b : ℝ}
    (hf : f =O[Filter.cocompact ℝ] fun x : ℝ => |x|^(-b)) {Q : ℝ} (hQ : 0 < Q) :
    (fun ξ : ℝ => f (ξ/Q)) =O[Filter.cocompact ℝ] fun ξ : ℝ => |ξ|^(-b) := by
  have heq : (fun ξ : ℝ => |ξ/Q|^(-b)) = fun ξ => (Q^b) * |ξ|^(-b) := by
    funext ξ
    rw [abs_div, abs_of_pos hQ, Real.div_rpow (abs_nonneg ξ) hQ.le, Real.rpow_neg hQ.le,
        div_inv_eq_mul, mul_comm]
  have ht : Filter.Tendsto (fun ξ : ℝ => ξ/Q) (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · refine Filter.Tendsto.mono_right ?_ le_sup_left
      have := Filter.Tendsto.atBot_mul_const (inv_pos.mpr hQ) (tendsto_id : Tendsto (fun ξ:ℝ => ξ) atBot atBot)
      simpa [div_eq_mul_inv] using this
    · refine Filter.Tendsto.mono_right ?_ le_sup_right
      have := Filter.Tendsto.atTop_mul_const (inv_pos.mpr hQ) (tendsto_id : Tendsto (fun ξ:ℝ => ξ) atTop atTop)
      simpa [div_eq_mul_inv] using this
  have h1 := hf.comp_tendsto ht
  simp only [Function.comp_def] at h1
  rw [heq] at h1
  exact h1.trans (isBigO_const_mul_self (Q^b) (fun ξ : ℝ => |ξ|^(-b)) (Filter.cocompact ℝ))

/-- Poisson summation applied to one residue class: the sum of `f` over the lattice
`{q m + a}` equals the transformed sum over the dual lattice. -/
lemma poisson_lattice_sum (q : ℕ) (hq : 0 < q) {b : ℝ} (hb : 1 < b)
    {f : ℝ → ℂ} (hc : Continuous f)
    (hf : f =O[Filter.cocompact ℝ] fun x => |x|^(-b))
    (hFf : 𝓕 f =O[Filter.cocompact ℝ] fun x => |x|^(-b)) (a : ℤ) :
    ∑' m : ℤ, f ((q:ℝ) * (m:ℝ) + (a:ℝ)) =
      (q:ℂ)⁻¹ * ∑' k : ℤ,
        Complex.exp (2*Real.pi*Complex.I*((a*k : ℤ):ℂ)/(q:ℂ)) * 𝓕 f ((k:ℝ)/(q:ℝ)) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hcont : Continuous (fun x : ℝ => f ((q:ℝ)*x + (a:ℝ))) := hc.comp (by fun_prop)
  have hd1 : (fun x : ℝ => f ((q:ℝ)*x + (a:ℝ))) =O[Filter.cocompact ℝ] (fun x => |x|^(-b)) :=
    isBigO_comp_affine (by linarith) hf hqR
  have hFh : 𝓕 (fun x : ℝ => f ((q:ℝ)*x + (a:ℝ)))
      = fun ξ : ℝ => ((q:ℂ)⁻¹ * Complex.exp (2*Real.pi*Complex.I*((a:ℝ)*ξ)/(q:ℝ))) * 𝓕 f (ξ/(q:ℝ)) := by
    funext ξ
    rw [fourier_affine (q:ℝ) hqR (a:ℝ) f ξ]
    push_cast
    ring
  have hexp1 : ∀ ξ : ℝ, Complex.exp (2*Real.pi*Complex.I*((a:ℝ)*ξ)/(q:ℝ))
      = Complex.exp (↑(2*Real.pi*((a:ℝ)*ξ)/(q:ℝ)) * Complex.I) := by
    intro ξ; congr 1; push_cast; ring
  have hbdd : (fun ξ : ℝ => ((q:ℂ)⁻¹ * Complex.exp (2*Real.pi*Complex.I*((a:ℝ)*ξ)/(q:ℝ))) * 𝓕 f (ξ/(q:ℝ)))
      =O[Filter.cocompact ℝ] (fun ξ : ℝ => 𝓕 f (ξ/(q:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound ‖(q:ℂ)⁻¹‖ ?_
    filter_upwards with ξ
    simp only [norm_mul, hexp1 ξ, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have hd2 : (𝓕 (fun x : ℝ => f ((q:ℝ)*x + (a:ℝ)))) =O[Filter.cocompact ℝ] (fun x => |x|^(-b)) := by
    rw [hFh]
    exact hbdd.trans (isBigO_comp_div (f := 𝓕 f) hFf hqR)
  have hpois : ∑' m : ℤ, f ((q:ℝ)*(m:ℝ)+(a:ℝ))
      = ∑' k : ℤ, 𝓕 (fun x : ℝ => f ((q:ℝ)*x + (a:ℝ))) k := by
    have := Real.tsum_eq_tsum_fourier_of_rpow_decay hcont hb hd1 hd2 (0:ℝ)
    simpa using this
  rw [hpois]
  have hA : ∀ k : ℤ, 𝓕 (fun x : ℝ => f ((q:ℝ)*x + (a:ℝ))) k
      = (q:ℂ)⁻¹ * (Complex.exp (2*↑Real.pi*Complex.I*↑(a*k)/↑q) * 𝓕 f (↑k/↑q)) := by
    intro k
    rw [hFh]
    simp only []
    rw [mul_assoc]
    congr 1
    congr 1
    congr 1
    push_cast
    ring
  simp_rw [hA]
  rw [← tsum_mul_left]

/-- A `q`-periodic function on `ℤ` is bounded. -/
lemma exists_norm_bound_of_periodic {q : ℕ} (hq : 0 < q) {g : ℤ → ℂ}
    (hg : ∀ n k : ℤ, (q : ℤ) ∣ (n - k) → g n = g k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ‖g n‖ ≤ C := by
  refine ⟨∑ a ∈ Finset.range q, ‖g (a:ℤ)‖, by positivity, fun n => ?_⟩
  have hqZ : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdvd : (q:ℤ) ∣ n - (n % (q:ℤ)) := by
    refine ⟨n / (q:ℤ), ?_⟩
    have h := Int.emod_add_mul_ediv n (q:ℤ)
    ring_nf
    linarith [h]
  have hge : g n = g (n % (q:ℤ)) := hg n (n % (q:ℤ)) hdvd
  have h0 : 0 ≤ n % (q:ℤ) := Int.emod_nonneg n hqZ
  have hlt : n % (q:ℤ) < q := Int.emod_lt_of_pos n (by exact_mod_cast hq)
  have hcast : n % (q:ℤ) = ((n % (q:ℤ)).toNat : ℤ) := (Int.toNat_of_nonneg h0).symm
  rw [hge, hcast]
  exact Finset.single_le_sum (s := Finset.range q) (fun i _ => norm_nonneg (g (i:ℤ)))
    (Finset.mem_range.mpr ((Int.toNat_lt h0).mpr hlt))

/-- The product of a `q`-periodic function with a decaying function is summable. -/
lemma summable_g_mul_f {q : ℕ} (hq : 0 < q) {b : ℝ} (hb : 1 < b) {g : ℤ → ℂ}
    (hg : ∀ n k : ℤ, (q : ℤ) ∣ (n - k) → g n = g k) {f : ℝ → ℂ}
    (hf : f =O[Filter.cocompact ℝ] fun x => |x|^(-b)) :
    Summable (fun n : ℤ => g n * f (n:ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_bound_of_periodic hq hg
  refine summable_of_isBigO (Real.summable_abs_int_rpow hb) ?_
  have h1 : (fun n : ℤ => g n * f (n:ℝ)) =O[Filter.cofinite] (fun n : ℤ => ‖f (n:ℝ)‖) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards with n
    rw [norm_mul, Real.norm_of_nonneg (norm_nonneg (f (n:ℝ)))]
    exact mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)
  have h2 : (fun n : ℤ => ‖f (n:ℝ)‖) =O[Filter.cofinite] (fun n : ℤ => |(n:ℝ)|^(-b)) := by
    have hh := hf.comp_tendsto Int.tendsto_coe_cofinite
    simp only [Function.comp_def] at hh
    exact hh.norm_left
  exact h1.trans h2

/-- The Fourier transform sampled on the dual lattice `{k/q}` is summable. -/
lemma summable_fourier_div {q : ℕ} (hq : 0 < q) {b : ℝ} (hb : 1 < b) {f : ℝ → ℂ}
    (hFf : 𝓕 f =O[Filter.cocompact ℝ] fun x => |x|^(-b)) :
    Summable (fun k : ℤ => 𝓕 f ((k:ℝ)/(q:ℝ))) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hh : (fun k : ℤ => 𝓕 f ((k:ℝ)/(q:ℝ))) =O[Filter.cofinite] (fun k : ℤ => |(k:ℝ)|^(-b)) := by
    have h2 := (isBigO_comp_div (f := 𝓕 f) hFf hqR).comp_tendsto Int.tendsto_coe_cofinite
    simpa only [Function.comp_def] using h2
  exact summable_of_isBigO (Real.summable_abs_int_rpow hb) hh

end Work.FIArea5.S16

import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Kser_gp_bounds
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of `τ ↦ ‖Ψ₁(a+iτ)‖²` and `τ ↦ ‖Ψ₂(a+iτ)‖²` for `a > 1`

The Dirichlet-logarithm functions of `Submission.Work.BMF.halasz_series_aux` are

* `Ψ₁ f s = -Σ_p f(p) log p · p^{-s}` (the prime part of `Ψ`),
* `Ψ₂ f s = Ψ f s - Ψ₁ f s` where `Ψ f s = Σ_p g_p'(s)/g_p(s)`.

On a vertical line `Re s = a > 1` both are locally uniformly convergent series of continuous
functions (the summands are bounded by `C_a · (log p) p^{-a}`, which is summable over the
primes), so their norms squared are continuous in `τ`.

Everything is proved from the estimates in `Work.BMF.mrlas.Psi2_defs`:
`‖u p s‖ = p^{-Re s}`, the power series form `deriv (gp f p) s = -(log p) Σ_e e f(p^e) u^e`,
and `‖gp f p s‖ ≥ (1-2‖u‖)/(1-‖u‖)`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.BMF.mrlas

noncomputable section

/-- `Σ_p (log p) p^{-σ}` converges for `σ > 1`. -/
theorem Psi_nsc_summable_log_prime_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) * (p : ℝ) ^ (-σ)) := by
  set ε : ℝ := (σ - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set c : ℝ := (σ + 1) / 2 with hcdef
  have hc : 1 < c := by rw [hcdef]; linarith
  have hbase : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-c)) :=
    Work.BMF.summable_prime_rpow_neg c hc
  have hmul : Summable (fun p : Nat.Primes => (1 / ε) * (p : ℝ) ^ (-c)) := hbase.mul_left (1 / ε)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmul
  · have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast Nat.Prime.one_le p.2
    exact mul_nonneg (Real.log_nonneg hp1) (Real.rpow_nonneg (by positivity) _)
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.Prime.two_le p.2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlog : Real.log (p : ℝ) ≤ (p : ℝ) ^ ε / ε := Real.log_le_rpow_div hp0.le hεpos
    have h1 : Real.log (p : ℝ) * (p : ℝ) ^ (-σ) ≤ ((p : ℝ) ^ ε / ε) * (p : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hp0.le _)
    have hexp : ε + (-σ) = -c := by rw [hεdef, hcdef]; ring
    have h2 : ((p : ℝ) ^ ε / ε) * (p : ℝ) ^ (-σ) = (1 / ε) * (p : ℝ) ^ (-c) := by
      rw [div_mul_eq_mul_div, one_div_mul_eq_div, ← Real.rpow_add hp0 ε (-σ), hexp]
    exact le_trans h1 (le_of_eq h2)

/-- The local Euler factor `s ↦ gp f p s` is continuous on the half-plane `Re s ≥ a` (`a > 1`). -/
theorem Psi_nsc_continuousOn_gp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    (a : ℝ) (ha : 1 < a) :
    ContinuousOn (fun s : ℂ => Work.BMF.gp f p s) {s : ℂ | a ≤ s.re} := by
  have hra : (2 : ℝ) ^ (-a) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) (show -a < (0:ℝ) by linarith)
    rwa [Real.rpow_zero] at h
  have hrnn : 0 ≤ (2 : ℝ) ^ (-a) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable (fun e : ℕ => ((2 : ℝ) ^ (-a)) ^ e) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_of_nonneg hrnn]; exact hra)
  have hu_cont : Continuous (fun s : ℂ => u p s) := by unfold u; fun_prop
  have hcont : ContinuousOn (fun s : ℂ => ∑' e : ℕ, f (p^e) * (u p s)^e) {s : ℂ | a ≤ s.re} := by
    refine continuousOn_tsum (u := fun e : ℕ => ((2 : ℝ) ^ (-a)) ^ e) ?_ hsum ?_
    · intro e
      exact ((hu_cont.pow e).const_mul (f (p^e))).continuousOn
    · intro e s hs
      have hs' : a ≤ s.re := hs
      have hu_le : ‖u p s‖ ≤ (2 : ℝ) ^ (-a) := by
        rw [norm_u hp.pos]
        calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-a) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)
          _ ≤ (2 : ℝ) ^ (-a) :=
              Work.BMF.rpow_neg_anti (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
      rw [norm_mul, norm_pow]
      calc ‖f (p ^ e)‖ * ‖u p s‖ ^ e ≤ 1 * ((2 : ℝ) ^ (-a)) ^ e :=
            mul_le_mul (hb _) (pow_le_pow_left₀ (norm_nonneg _) hu_le e)
              (pow_nonneg (norm_nonneg _) e) (by norm_num)
        _ = ((2 : ℝ) ^ (-a)) ^ e := one_mul _
  refine ContinuousOn.congr hcont ?_
  intro s _
  exact gp_eq f hp s

/-- `s ↦ deriv (gp f p) s` is continuous on the half-plane `Re s ≥ a` (`a > 1`). -/
theorem Psi_nsc_continuousOn_deriv_gp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    (a : ℝ) (ha : 1 < a) :
    ContinuousOn (fun s : ℂ => deriv (Work.BMF.gp f p) s) {s : ℂ | a ≤ s.re} := by
  have hra : (2 : ℝ) ^ (-a) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) (show -a < (0:ℝ) by linarith)
    rwa [Real.rpow_zero] at h
  have hrnn : 0 ≤ (2 : ℝ) ^ (-a) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable (fun e : ℕ => (e : ℝ) * ((2 : ℝ) ^ (-a)) ^ e) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (2:ℝ)^(-a))
      (by rw [Real.norm_of_nonneg hrnn]; exact hra)
    simpa using h
  have hu_cont : Continuous (fun s : ℂ => u p s) := by unfold u; fun_prop
  have hcont : ContinuousOn (fun s : ℂ => ∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e)
      {s : ℂ | a ≤ s.re} := by
    refine continuousOn_tsum (u := fun e : ℕ => (e : ℝ) * ((2 : ℝ) ^ (-a)) ^ e) ?_ hsum ?_
    · intro e
      exact (((continuous_const : Continuous fun _ : ℂ => (e : ℂ)).mul
        (continuous_const : Continuous fun _ : ℂ => f (p^e))).mul (hu_cont.pow e)).continuousOn
    · intro e s hs
      have hs' : a ≤ s.re := hs
      have hu_le : ‖u p s‖ ≤ (2 : ℝ) ^ (-a) := by
        rw [norm_u hp.pos]
        calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-a) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)
          _ ≤ (2 : ℝ) ^ (-a) :=
              Work.BMF.rpow_neg_anti (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      calc (e : ℝ) * ‖f (p ^ e)‖ * ‖u p s‖ ^ e
          ≤ (e : ℝ) * 1 * ((2 : ℝ) ^ (-a)) ^ e :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hb _) (Nat.cast_nonneg e))
              (pow_le_pow_left₀ (norm_nonneg _) hu_le e)
              (pow_nonneg (norm_nonneg _) e) (by positivity)
        _ = (e : ℝ) * ((2 : ℝ) ^ (-a)) ^ e := by ring
  have hcont2 : ContinuousOn
      (fun s : ℂ => -((Real.log (p:ℝ)) : ℂ) * (∑' e : ℕ, (e : ℂ) * f (p ^ e) * (u p s) ^ e))
      {s : ℂ | a ≤ s.re} := hcont.const_mul _
  refine ContinuousOn.congr hcont2 ?_
  intro s hs
  exact deriv_gp f hb hp (lt_of_lt_of_le ha hs)

/-- `τ ↦ Ψ₁ f (a + iτ)` is continuous for `a > 1`. -/
theorem Psi_nsc_Psi1_continuous (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    (a : ℝ) (ha : 1 < a) :
    Continuous (fun τ : ℝ => Work.BMF.Psi1 f ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
  have hsum : Summable (fun p : Nat.Primes => Real.log (p:ℝ) * (p:ℝ)^(-a)) :=
    Psi_nsc_summable_log_prime_rpow_neg a ha
  have hmain : Continuous (fun τ : ℝ => ∑' p : Nat.Primes,
      -(f (p:ℕ) * (Real.log (p:ℕ) : ℂ) * ((p:ℕ) : ℂ) ^ (-(((a:ℂ) + (τ:ℂ)*Complex.I))))) := by
    refine continuous_tsum (u := fun p : Nat.Primes => Real.log (p:ℝ) * (p:ℝ)^(-a)) ?_ hsum ?_
    · intro p
      have hp0 : ((p:ℕ) : ℂ) ≠ 0 := by
        have h : (p:ℕ) ≠ 0 := (p.2).ne_zero
        exact_mod_cast h
      have hco : Continuous (fun τ : ℝ => -(((a:ℂ) + (τ:ℂ)*Complex.I))) := by fun_prop
      have hcp : Continuous (fun τ : ℝ => ((p:ℕ):ℂ) ^ (-(((a:ℂ) + (τ:ℂ)*Complex.I)))) :=
        hco.const_cpow (Or.inl hp0)
      exact ((continuous_const : Continuous fun _ : ℝ => f (p:ℕ) * (Real.log (p:ℕ) : ℂ)).mul hcp).neg
    · intro p τ
      have hsre : (((a:ℂ) + (τ:ℂ)*Complex.I)).re = a := by simp
      have hnegre : (-(((a:ℂ) + (τ:ℂ)*Complex.I))).re = -a := by
        rw [Complex.neg_re, hsre]
      have hnp : ‖((p:ℕ):ℂ) ^ (-(((a:ℂ) + (τ:ℂ)*Complex.I)))‖ = (p:ℝ)^(-a) := by
        rw [Complex.norm_natCast_cpow_of_re_ne_zero (p:ℕ) (by rw [hnegre]; linarith), hnegre]
      have hlog : 0 ≤ Real.log (p:ℕ) := Real.log_nonneg (by exact_mod_cast (p.2).one_le)
      simp only [norm_neg, norm_mul, hnp, Complex.norm_real, Real.norm_of_nonneg hlog]
      calc ‖f (p:ℕ)‖ * Real.log (p:ℕ) * (p:ℝ)^(-a)
          ≤ 1 * Real.log (p:ℕ) * (p:ℝ)^(-a) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hb _) hlog)
              (Real.rpow_nonneg (by positivity) _)
        _ = Real.log (p:ℝ) * (p:ℝ)^(-a) := by ring
  simpa [Work.BMF.Psi1] using hmain

/-- `τ ↦ Ψ f (a + iτ)` is continuous for `a > 1`. -/
theorem Psi_nsc_Psi_continuous (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    (a : ℝ) (ha : 1 < a) :
    Continuous (fun τ : ℝ => Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)) := by
  set r : ℝ := (2:ℝ)^(-a) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hr2 : r < 1/2 := by
    rw [hrdef]
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) (show -a < (-1:ℝ) by linarith)
    rw [Real.rpow_neg_one] at h
    have h2' : (2:ℝ)⁻¹ = 1/2 := by norm_num
    rwa [h2'] at h
  have hden1 : 0 < 1 - r := by linarith
  have hden2 : 0 < 1 - 2*r := by linarith
  have hden1ne : (1 - r) ≠ 0 := ne_of_gt hden1
  set δ : ℝ := (1 - 2*r)/(1 - r) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set C : ℝ := 1/((1-r)^2 * δ) with hCdef
  have hsum := Psi_nsc_summable_log_prime_rpow_neg a ha
  have hu : Summable (fun p : Nat.Primes => C * (Real.log (p:ℝ) * (p:ℝ)^(-a))) := hsum.mul_left C
  have key_lb : ∀ {x : ℝ}, x ≤ r → δ ≤ (1 - 2*x)/(1 - x) := by
    intro x hx
    have hx1 : 0 < 1 - x := by linarith [hx, hr2]
    have key : (1 - 2*x)/(1 - x) - δ = (r - x)/((1-x)*(1-r)) := by
      rw [hδdef]
      field_simp
      ring
    have hrx : 0 ≤ r - x := by linarith
    have hd : 0 < (1-x)*(1-r) := by positivity
    have : 0 ≤ (1 - 2*x)/(1 - x) - δ := by rw [key]; exact div_nonneg hrx hd.le
    linarith
  have hmain : Continuous (fun τ : ℝ => ∑' p : Nat.Primes,
      deriv (Work.BMF.gp f (p:ℕ)) ((a:ℂ)+(τ:ℂ)*Complex.I) / Work.BMF.gp f (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)) := by
    refine continuous_tsum (u := fun p : Nat.Primes => C * (Real.log (p:ℝ) * (p:ℝ)^(-a))) ?_ hu ?_
    · intro p
      have hp : (p:ℕ).Prime := p.2
      have hlin : Continuous (fun τ : ℝ => ((a:ℂ) + (τ:ℂ)*Complex.I)) := by fun_prop
      have hmem : ∀ τ : ℝ, ((a:ℂ) + (τ:ℂ)*Complex.I) ∈ {s : ℂ | a ≤ s.re} := by intro τ; simp
      have hnum : Continuous (fun τ : ℝ => deriv (Work.BMF.gp f (p:ℕ)) ((a:ℂ)+(τ:ℂ)*Complex.I)) :=
        (Psi_nsc_continuousOn_deriv_gp f hb hp a ha).comp_continuous hlin hmem
      have hden : Continuous (fun τ : ℝ => Work.BMF.gp f (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)) :=
        (Psi_nsc_continuousOn_gp f hb hp a ha).comp_continuous hlin hmem
      refine hnum.div hden ?_
      intro τ
      have hsre : (((a:ℂ)+(τ:ℂ)*Complex.I)).re = a := by simp
      have hs : 0 < (((a:ℂ)+(τ:ℂ)*Complex.I)).re := by rw [hsre]; linarith
      have hg := gp_lower_bound f hf1 hb hp hs
      have hx : ‖u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)‖ ≤ r := by
        rw [norm_u (p.2).pos, hrdef, hsre]
        exact Work.BMF.rpow_neg_anti (by norm_num) (by exact_mod_cast (p.2).two_le) (by linarith)
      have hpos : 0 < ‖Work.BMF.gp f (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)‖ :=
        lt_of_lt_of_le hδpos (le_trans (key_lb hx) hg)
      exact norm_pos_iff.mp hpos
    · intro p τ
      have hp : (p:ℕ).Prime := p.2
      have hsre : (((a:ℂ)+(τ:ℂ)*Complex.I)).re = a := by simp
      have hs1 : 1 < (((a:ℂ)+(τ:ℂ)*Complex.I)).re := by rw [hsre]; linarith
      have hρ0 : 0 ≤ (p:ℝ)^(-a) := Real.rpow_nonneg (by positivity) _
      have hρlt1 : (p:ℝ)^(-a) < 1 := by
        have h2p : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
        have h := Real.rpow_lt_rpow_of_exponent_lt h2p (show -a < (0:ℝ) by linarith)
        rwa [Real.rpow_zero] at h
      have hρle : (p:ℝ)^(-a) ≤ r := by
        rw [hrdef]
        exact Work.BMF.rpow_neg_anti (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
      have hgeom : Summable (fun e : ℕ => (e:ℝ) * ((p:ℝ)^(-a))^e) := by
        have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (p:ℝ)^(-a))
          (by rw [Real.norm_of_nonneg hρ0]; exact hρlt1)
        simpa using h
      have hu_eq : ‖u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)‖ = (p:ℝ)^(-a) := by
        rw [norm_u (p.2).pos, hsre]
      have hpt : ∀ e : ℕ, ‖(e:ℂ) * f (p^e) * (u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I))^e‖
          ≤ (e:ℝ) * ((p:ℝ)^(-a))^e := by
        intro e
        simp only [norm_mul, norm_pow, Complex.norm_natCast, hu_eq]
        calc (e:ℝ) * ‖f (p^e)‖ * ((p:ℝ)^(-a))^e
            ≤ (e:ℝ) * 1 * ((p:ℝ)^(-a))^e :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hb _) (Nat.cast_nonneg e)) (le_refl _)
                (pow_nonneg hρ0 e) (by positivity)
          _ = (e:ℝ) * ((p:ℝ)^(-a))^e := by ring
      have hinner : Summable (fun e : ℕ => ‖(e:ℂ) * f (p^e) * (u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I))^e‖) := by
        refine Summable.of_norm_bounded hgeom (fun e => ?_)
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt e
      have hts : ‖∑' e : ℕ, (e:ℂ) * f (p^e) * (u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I))^e‖
          ≤ (p:ℝ)^(-a) / (1 - (p:ℝ)^(-a))^2 := by
        calc ‖∑' e : ℕ, (e:ℂ) * f (p^e) * (u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I))^e‖
            ≤ ∑' e : ℕ, ‖(e:ℂ) * f (p^e) * (u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I))^e‖ :=
              norm_tsum_le_tsum_norm hinner
          _ ≤ ∑' e : ℕ, (e:ℝ) * ((p:ℝ)^(-a))^e :=
              Summable.tsum_le_tsum hpt hinner hgeom
          _ = (p:ℝ)^(-a) / (1 - (p:ℝ)^(-a))^2 := by
              have h := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (p:ℝ)^(-a))
                (by rw [Real.norm_of_nonneg hρ0]; exact hρlt1)
              simpa using h
      have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
      have hderiv_bound : ‖deriv (Work.BMF.gp f (p:ℕ)) ((a:ℂ)+(τ:ℂ)*Complex.I)‖
          ≤ Real.log (p:ℝ) * ((p:ℝ)^(-a) / (1 - (p:ℝ)^(-a))^2) := by
        rw [deriv_gp f hb hp hs1, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog]
        exact mul_le_mul_of_nonneg_left hts hlog
      have hfrac : (p:ℝ)^(-a) / (1 - (p:ℝ)^(-a))^2 ≤ (p:ℝ)^(-a) / (1 - r)^2 := by
        have h1ρ : 1 - r ≤ 1 - (p:ℝ)^(-a) := by linarith
        have hA : (1-r)^2 ≤ (1-(p:ℝ)^(-a))^2 := by nlinarith [hden1, h1ρ]
        exact div_le_div_of_nonneg_left hρ0 (by positivity : (0:ℝ) < (1-r)^2) hA
      have hderiv_bound' : ‖deriv (Work.BMF.gp f (p:ℕ)) ((a:ℂ)+(τ:ℂ)*Complex.I)‖
          ≤ Real.log (p:ℝ) * ((p:ℝ)^(-a) / (1 - r)^2) :=
        le_trans hderiv_bound (mul_le_mul_of_nonneg_left hfrac hlog)
      have hg := gp_lower_bound f hf1 hb hp (by rw [hsre]; linarith : 0 < (((a:ℂ)+(τ:ℂ)*Complex.I)).re)
      have hx : ‖u (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)‖ ≤ r := by
        rw [norm_u (p.2).pos, hrdef, hsre]
        exact Work.BMF.rpow_neg_anti (by norm_num) (by exact_mod_cast (p.2).two_le) (by linarith)
      have hgnorm : δ ≤ ‖Work.BMF.gp f (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)‖ := le_trans (key_lb hx) hg
      rw [norm_div]
      calc ‖deriv (Work.BMF.gp f (p:ℕ)) ((a:ℂ)+(τ:ℂ)*Complex.I)‖
              * (‖Work.BMF.gp f (p:ℕ) ((a:ℂ)+(τ:ℂ)*Complex.I)‖)⁻¹
          ≤ (Real.log (p:ℝ) * ((p:ℝ)^(-a) / (1 - r)^2)) * δ⁻¹ :=
            mul_le_mul hderiv_bound' (inv_anti₀ hδpos hgnorm) (by positivity)
              (mul_nonneg hlog (div_nonneg hρ0 (by positivity)))
        _ = C * (Real.log (p:ℝ) * (p:ℝ)^(-a)) := by
            rw [hCdef]
            field_simp
  simpa [Work.BMF.Psi] using hmain

theorem Psi_norm_sq_continuous (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    (a : ℝ) (ha : 1 < a) :
    Continuous (fun τ : ℝ => ‖Work.BMF.Psi1 f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) ∧
    Continuous (fun τ : ℝ => ‖Work.BMF.Psi2 f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
  have h1 := Psi_nsc_Psi1_continuous f hf1 hb a ha
  have h2 := Psi_nsc_Psi_continuous f hf1 hb a ha
  constructor
  · convert (h1.norm.pow 2) using 1
  · show Continuous (fun τ : ℝ =>
        ‖Work.BMF.Psi f ((a:ℂ)+(τ:ℂ)*Complex.I) - Work.BMF.Psi1 f ((a:ℂ)+(τ:ℂ)*Complex.I)‖ ^ 2)
    convert ((h2.sub h1).norm.pow 2) using 1

end

end Work.BMF.mrlas

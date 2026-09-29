/-
# The uniform form of Lemma `lcm-2` of Calegari–Dimitrov–Tang

`Submission.CDT.LcmGe` proves Lemma `lcm-2` (part 1) with the scale parameter `γ` fixed: for
`k, l` with `γn ≤ k, l ≤ n` the cutoff window product `L^{≥l}_{n,k}` is asymptotic to its model,
with an error `o(n)` that depends on `γ`.  The paper's Lemma `lcm-2` needs this **uniformly** in
`γ ∈ [γ₀, 1]` (`γ₀ > 0` fixed) — equivalently, uniformly in `k, l` over the region
`γ₀ n ≤ k, l ≤ n`.  This module supplies that uniform form:

* `bad_sum_model_error_uniform` — the prime-number-theorem error in the gap decomposition is
  `< εn` for all `k, l ≥ γ₀ n` (the number of gaps is `≤ 1/γ₀`, and every argument of `θ` is
  `≥ γ₀ n`, so the pointwise relative PNT gives a `γ₀`-dependent, `k,l`-independent constant);
* `lcm_ge_model_uniform` — the model form `log L^{≥l}_{n,k} = n − l − Σ_{a ≤ h}((n-k-1)/a −
  max(n/(a+1), l)) + O(εn)`;
* `lcm_ge_harmonic_uniform` — its closed form
  `(k+1)H + n/(h+1) − l + C + O(εn)` with `h = (n-k-1)/max(k,l)`, `H = Σ_{a≤h} 1/a` and
  `C = Σ_{a≤h} max(l − n/(a+1), 0)`.
-/
import Submission.CDT.LcmGe

open Finset Filter
open Submission.CDT.LcmGe
open scoped BigOperators Topology

namespace Submission.CDT.LcmGeUniform

/-- **The analytic step of Lemma `lcm-2`, uniformly in `k, l ≥ γ₀ n`.**  For `γ₀ > 0` and every
`ε > 0`, for all sufficiently large `n` and all `k, l` with `γ₀n ≤ k, l ≤ n`, the
prime-number-theorem error in the cutoff decomposition is at most `εn`. -/
theorem bad_sum_model_error_uniform (γ₀ : ℝ) (hγ₀ : 0 < γ₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k l : ℕ, γ₀ * (n : ℝ) ≤ (k : ℝ) → k ≤ n → γ₀ * (n : ℝ) ≤ (l : ℝ) → l ≤ n →
      |(∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
        - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))|
        ≤ ε * (n : ℝ) := by
  intro ε hε
  set δ : ℝ := ε * γ₀ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  -- the PNT estimate, uniformly
  have hθ : (fun y : ℝ => Chebyshev.theta y - y) =o[Filter.atTop] (fun y : ℝ => y) :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO
  have hb : ∀ᶠ y : ℝ in Filter.atTop, |Chebyshev.theta y - y| ≤ δ * y := by
    have h := hθ.bound hδpos
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with y hy hy0
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
  rw [Filter.eventually_atTop] at hb
  obtain ⟨Y, hY⟩ := hb
  -- the threshold on `n`
  have hγn : ∀ᶠ n : ℕ in Filter.atTop, max Y 1 ≤ γ₀ * (n : ℝ) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hlim : Filter.Tendsto (fun n : ℕ => γ₀ * (n : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hγ₀ hcast
    exact hlim.eventually (Filter.eventually_ge_atTop (max Y 1))
  filter_upwards [hγn] with n hn k l hk hkn hl hln
  set h : ℕ := (n - k - 1) / max k l with hhdef
  have hγn' : γ₀ * (n : ℝ) ≤ (max k l : ℝ) := by
    have hmax := max_le_max hk hl
    rwa [max_self] at hmax
  have hn1 : (1 : ℝ) ≤ γ₀ * (n : ℝ) := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by nlinarith [hγ₀, hn1]
  have hYle : Y ≤ γ₀ * (n : ℝ) := le_trans (le_max_left _ _) hn
  -- every argument is `≥ γ₀n`
  have harg1 : ∀ a ∈ Finset.Icc 1 h,
      γ₀ * (n : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) / (a : ℝ) := by
    intro a ha
    obtain ⟨ha1, hah⟩ := Finset.mem_Icc.mp ha
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
    rw [le_div_iff₀ hapos]
    have hstep : a * max k l ≤ n - k - 1 :=
      le_trans (Nat.mul_le_mul_right _ hah) (Nat.div_mul_le_self _ _)
    have hstep' : ((a * max k l : ℕ) : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) := by exact_mod_cast hstep
    have hle : γ₀ * (n : ℝ) * (a : ℝ) ≤ (a : ℝ) * (max k l : ℝ) := by
      have := mul_le_mul_of_nonneg_left hγn' (by positivity : (0 : ℝ) ≤ (a : ℝ))
      linarith
    push_cast at hstep'
    linarith
  have harg2 : ∀ a ∈ Finset.Icc 1 h,
      γ₀ * (n : ℝ) ≤ max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ) :=
    fun a _ => le_trans hl (le_max_right _ _)
  -- the two auxiliary sums are `≤ h·n`
  have hyle : ∀ a ∈ Finset.Icc 1 h, ((n - k - 1 : ℕ) : ℝ) / (a : ℝ) ≤ (n : ℝ) := by
    intro a ha
    obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp ha
    have ha1' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have hn0 : (0 : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) := by positivity
    have hnkc : ((n - k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : n - k - 1 ≤ n := by omega
      exact_mod_cast this
    exact le_trans (div_le_self hn0 ha1') hnkc
  have hzle : ∀ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ) ≤ (n : ℝ) := by
    intro a _
    refine max_le ?_ (by exact_mod_cast hln)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)]
    nlinarith [hnpos]
  have hcard : ((Finset.Icc 1 h).card : ℝ) = (h : ℝ) := by
    rw [Nat.card_Icc]; simp
  -- `h ≤ 1/γ₀`
  have hhle : (h : ℝ) ≤ 1 / γ₀ := by
    have hmul : (h : ℝ) * (max k l : ℝ) ≤ (n : ℝ) := by
      have h1 : h * max k l ≤ n := le_trans (Nat.div_mul_le_self _ _) (by omega)
      have h2 : ((h * max k l : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have h3 : (h : ℝ) * (γ₀ * (n : ℝ)) ≤ (h : ℝ) * (max k l : ℝ) :=
      mul_le_mul_of_nonneg_left hγn' (by positivity : (0 : ℝ) ≤ (h : ℝ))
    rw [le_div_iff₀ hγ₀]
    nlinarith [hmul, h3, hnpos, hγ₀]
  -- assemble
  rw [← Finset.sum_sub_distrib]
  calc |∑ a ∈ Finset.Icc 1 h,
        ((Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))
          - ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))|
      ≤ ∑ a ∈ Finset.Icc 1 h,
          |(Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))
            - ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 h,
          (δ * (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            + δ * max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)) := by
        apply Finset.sum_le_sum
        intro a ha
        set y : ℝ := ((n - k - 1 : ℕ) : ℝ) / (a : ℝ) with hydef
        set z : ℝ := max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ) with hzdef
        have h1 : |Chebyshev.theta y - y| ≤ δ * y := hY y (le_trans hYle (harg1 a ha))
        have h2 : |Chebyshev.theta z - z| ≤ δ * z := hY z (le_trans hYle (harg2 a ha))
        have h3 : |(Chebyshev.theta y - Chebyshev.theta z) - (y - z)|
            = |(Chebyshev.theta y - y) - (Chebyshev.theta z - z)| := by
          congr 1; ring
        rw [h3]
        have h4 := abs_sub (Chebyshev.theta y - y) (Chebyshev.theta z - z)
        simp only [hydef, hzdef] at h1 h2 h4 ⊢
        linarith
    _ = δ * (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
          + δ * (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ δ * ((h : ℝ) * (n : ℝ)) + δ * ((h : ℝ) * (n : ℝ)) := by
        have hy : (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
            ≤ (h : ℝ) * (n : ℝ) := by
          calc (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
              ≤ ∑ _a ∈ Finset.Icc 1 h, (n : ℝ) := Finset.sum_le_sum hyle
            _ = ((Finset.Icc 1 h).card : ℝ) * (n : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = (h : ℝ) * (n : ℝ) := by rw [hcard]
        have hz : (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
            ≤ (h : ℝ) * (n : ℝ) := by
          calc (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
              ≤ ∑ _a ∈ Finset.Icc 1 h, (n : ℝ) := Finset.sum_le_sum hzle
            _ = ((Finset.Icc 1 h).card : ℝ) * (n : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = (h : ℝ) * (n : ℝ) := by rw [hcard]
        nlinarith [hy, hz, hδpos]
    _ ≤ ε * (n : ℝ) := by
        have hstep : 2 * δ * (h : ℝ) ≤ ε := by
          have hγinv : γ₀ * (1 / γ₀) = 1 := by field_simp
          have hkey : γ₀ * (h : ℝ) ≤ 1 := by
            have := mul_le_mul_of_nonneg_left hhle hγ₀.le
            rwa [hγinv] at this
          have hrew : 2 * (ε * γ₀ / 2) * (h : ℝ) = ε * (γ₀ * (h : ℝ)) := by ring
          rw [hδdef, hrew]
          nlinarith [hkey, hε]
        have := mul_le_mul_of_nonneg_right hstep hnpos.le
        linarith [this]

/-- **The model form of Lemma `lcm-2` (part 1), uniform in `k, l ≥ γ₀ n`.**  For `0 < γ₀ ≤ 1` and
every `ε > 0`, for all sufficiently large `n` and all `k, l` with `γ₀n ≤ k, l ≤ n`,

`|log L^{≥ l}_{n,k} − (n − l − Σ_{a ≤ h} ((n-k-1)/a − max(n/(a+1), l)))| ≤ εn`,
`h = (n-k-1)/max(k,l)`. -/
theorem lcm_ge_model_uniform (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (hγ₀1 : γ₀ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k l : ℕ, γ₀ * (n : ℝ) ≤ (k : ℝ) → k ≤ n → γ₀ * (n : ℝ) ≤ (l : ℝ) → l ≤ n →
      |Real.log ((Lge l n k : ℕ) : ℝ)
        - ((n : ℝ) - (l : ℝ)
            - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
              ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
                - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))|
        ≤ ε * (n : ℝ) := by
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hε3 : 0 < ε / 3 := by linarith
  have hθ : (fun y : ℝ => Chebyshev.theta y - y) =o[Filter.atTop] (fun y : ℝ => y) :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_isLittleO
  have hb : ∀ᶠ y : ℝ in Filter.atTop, |Chebyshev.theta y - y| ≤ δ * y := by
    have h := hθ.bound hδpos
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with y hy hy0
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy0] at hy
  rw [Filter.eventually_atTop] at hb
  obtain ⟨Y, hY⟩ := hb
  have hγn : ∀ᶠ n : ℕ in Filter.atTop, max (max Y 1) 1 ≤ γ₀ * (n : ℝ) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hlim : Filter.Tendsto (fun n : ℕ => γ₀ * (n : ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hγ₀ hcast
    exact hlim.eventually (Filter.eventually_ge_atTop (max (max Y 1) 1))
  filter_upwards [hγn, bad_sum_model_error_uniform γ₀ hγ₀ (ε / 3) hε3] with n hn hmodel k l hk hkn hl hln
  have hn1 : (1 : ℝ) ≤ γ₀ * (n : ℝ) := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by nlinarith [hγ₀, hn1]
  have hYle : Y ≤ γ₀ * (n : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := le_trans hn1 hl
  have hlpos : (0 : ℕ) < l := by exact_mod_cast (show (0 : ℝ) < (l : ℝ) by linarith)
  have hM : 0 < max k l := lt_of_lt_of_le hlpos (le_max_right _ _)
  have hlog := log_Lge l n k hM hkn hln
  have hγnn : γ₀ * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hnpos, hγ₀1]
  have hA : |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤ δ * (n : ℝ) := hY n (le_trans hYle hγnn)
  have hB : |Chebyshev.theta (l : ℝ) - (l : ℝ)| ≤ δ * (l : ℝ) := hY l (le_trans hYle hl)
  have hC := hmodel k l hk hkn hl hln
  have hEq : Chebyshev.theta (n : ℝ) - Chebyshev.theta (l : ℝ)
      - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
          (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
            - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      - ((n : ℝ) - (l : ℝ)
          - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      = (Chebyshev.theta (n : ℝ) - (n : ℝ)) - (Chebyshev.theta (l : ℝ) - (l : ℝ))
        - ((∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
          - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
            ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
              - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))) := by ring
  rw [hlog, hEq]
  have h5 := abs_sub ((Chebyshev.theta (n : ℝ) - (n : ℝ)) - (Chebyshev.theta (l : ℝ) - (l : ℝ)))
    ((∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
        (Chebyshev.theta (((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
          - Chebyshev.theta (max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
      - (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
        ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ))
          - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))))
  have h6 := abs_sub (Chebyshev.theta (n : ℝ) - (n : ℝ)) (Chebyshev.theta (l : ℝ) - (l : ℝ))
  have hfin : δ * (n : ℝ) + δ * (l : ℝ) + (ε / 3) * (n : ℝ) ≤ ε * (n : ℝ) := by
    have hln' : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
    rw [hδdef]
    nlinarith [hε, hnpos, hln']
  linarith [h5, h6, hA, hB, hC, hfin]

/-- **The closed form of the model of Lemma `lcm-2` (part 1), uniform in `k, l ≥ γ₀ n`.**  With
`h = (n-k-1)/max(k,l)`, `H = Σ_{a ≤ h} 1/a` and `C = Σ_{a ≤ h} max(l - n/(a+1), 0)`,

`log L^{≥l}_{n,k} = (k+1)·H + n/(h+1) - l + C + O(εn)`,

uniformly in `k, l` with `γ₀ n ≤ k, l ≤ n` (`0 < γ₀ ≤ 1`). -/
theorem lcm_ge_harmonic_uniform (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (hγ₀1 : γ₀ ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∀ k l : ℕ, γ₀ * (n : ℝ) ≤ (k : ℝ) → k ≤ n → γ₀ * (n : ℝ) ≤ (l : ℝ) → l ≤ n →
      |Real.log ((Lge l n k : ℕ) : ℝ)
        - (((k : ℝ) + 1) * (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l), (1 : ℝ) / (a : ℝ))
            + (n : ℝ) / ((((n - k - 1) / max k l : ℕ) : ℝ) + 1) - (l : ℝ)
            + (∑ a ∈ Finset.Icc 1 ((n - k - 1) / max k l),
                max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0))|
        ≤ ε * (n : ℝ) := by
  intro ε hε
  filter_upwards [lcm_ge_model_uniform γ₀ hγ₀ hγ₀1 ε hε] with n hn k l hk hkn hl hln
  have hmodel := hn k l hk hkn hl hln
  set h : ℕ := (n - k - 1) / max k l with hhdef
  have hmax : ∀ a : ℕ, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)
      = (n : ℝ) / ((a : ℝ) + 1) + max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0 :=
    fun a => max_eq_self_add_max_sub _ _
  have hsum : (∑ a ∈ Finset.Icc 1 h, max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ))
      = (n : ℝ) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ))
        - (n : ℝ) + (n : ℝ) / ((h : ℝ) + 1)
        + (∑ a ∈ Finset.Icc 1 h, max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0) := by
    rw [Finset.sum_congr rfl (fun a _ => hmax a), Finset.sum_add_distrib]
    have hsplit : (∑ a ∈ Finset.Icc 1 h, (n : ℝ) / ((a : ℝ) + 1))
        = (n : ℝ) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / ((a : ℝ) + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [hsplit, sum_Icc_one_div_add_one]
    ring
  have hysum : (∑ a ∈ Finset.Icc 1 h, (((n - k - 1 : ℕ) : ℝ) / (a : ℝ)))
      = ((n - k - 1 : ℕ) : ℝ) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hW : ((n : ℝ) - ((n - k - 1 : ℕ) : ℝ)) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ))
      = ((k : ℝ) + 1) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ)) := by
    by_cases hk' : k + 1 ≤ n
    · have hcast : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub hkn]
        push_cast
        ring
      rw [hcast]; ring
    · have hkn' : k = n := by omega
      have hh0 : h = 0 := by rw [hhdef]; simp [hkn']
      rw [hh0]; simp
  have hkey : (n : ℝ) - (l : ℝ)
      - (∑ a ∈ Finset.Icc 1 h,
          ((((n - k - 1 : ℕ) : ℝ) / (a : ℝ)) - max ((n : ℝ) / ((a : ℝ) + 1)) (l : ℝ)))
      = ((k : ℝ) + 1) * (∑ a ∈ Finset.Icc 1 h, (1 : ℝ) / (a : ℝ))
        + (n : ℝ) / ((h : ℝ) + 1) - (l : ℝ)
        + (∑ a ∈ Finset.Icc 1 h, max ((l : ℝ) - (n : ℝ) / ((a : ℝ) + 1)) 0) := by
    rw [Finset.sum_sub_distrib, hysum, hsum]
    nlinarith [hW]
  rw [hkey] at hmodel
  exact hmodel

end Submission.CDT.LcmGeUniform

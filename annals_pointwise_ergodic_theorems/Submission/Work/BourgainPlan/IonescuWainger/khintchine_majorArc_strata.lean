import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_sigmaStrata_mul_conj_eq_zero_of_nonce
import Submission.Work.BourgainPlan.IonescuWainger.summable_powerset_rpow_strata

/-!
# The Khintchine/square-function inequality for band-limited major-arc systems, strata form

This is `khintchine_majorArc` / `khintchine_majorArc_real` with the exact-denominator sets
`sigmaAFinset` replaced by Tao's strata `sigmaStrataFinset`: for `k, r ≥ 1` there is `C = C(k,r)`
such that for every finite set `S` of pairwise coprime integers `≥ 2`, every band-limited system
`f : 𝕋 → ℓ²(ℤ)` and every `ε` satisfying the nonce smallness hypothesis,

`Σ_x ‖Σ_{A ∈ binom(S,≤k)} f_{Σ_A}(x)‖^{2r} ≤ C^{kr} Σ_x (Σ_A ‖f_{Σ_A}(x)‖²)^r`,

with `f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BourgainPlan.IonescuWainger

/-- **The `ℝ≥0∞` (`lintegral`) form of the Khintchine inequality for the strata.** -/
theorem khintchine_majorArc_strata (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmall : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)),
      ∫⁻ x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (∑ α ∈ sigmaStrataFinset A, f α x)‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ (k * r)) *
            ∫⁻ x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
                ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ₑ ^ 2) ^ r ∂MeasureTheory.Measure.count := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  obtain ⟨C, hCpos, hC⟩ :=
    superorthogonal_khintchine_hypersystem (X := ℤ) (α := ℕ) k (n + 1) (by omega) hk
  refine ⟨C, hCpos, ?_⟩
  intro S h2 hS f hf ε hF hsmall
  have hint : ∀ A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ,
      (∀ i, A i ⊆ S ∧ (A i).card ≤ k) →
      Integrable (fun x : ℤ => ∏ i : Fin (n + 1),
        ‖∑ α ∈ sigmaStrataFinset (A (Sum.inl i)), f α x‖ *
        ‖∑ α ∈ sigmaStrataFinset (A (Sum.inr i)), f α x‖) Measure.count := by
    intro A _
    exact integrable_prod_norm_prod (by omega)
      (fun j x => ∑ α ∈ sigmaStrataFinset (A j), f α x)
      (fun j => Memℓp.finsetSum (sigmaStrataFinset (A j)) (fun α _ => hf α))
  have horth : ∀ A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ,
      (∀ i, A i ⊆ S ∧ (A i).card ≤ k) → HasNonce A →
      ∫ x, (∏ i : Fin (n + 1),
        star (∑ α ∈ sigmaStrataFinset (A (Sum.inl i)), f α x) *
        (∑ β ∈ sigmaStrataFinset (A (Sum.inr i)), f β x)) ∂Measure.count = 0 := by
    intro A hA hnonce
    rw [integral_count_eq_tsum _ (integrable_prod_star_mul
      (G := fun j x => ∑ α ∈ sigmaStrataFinset (A j), f α x) (hint A hA))]
    exact tsum_prod_sigmaStrata_mul_conj_eq_zero_of_nonce h2 hS hf hF (fun j => (hA j).1) hnonce
      (hsmall A hA hnonce)
  have hm : ∀ A : Finset ℕ, A ⊆ S → A.card ≤ k →
      AEMeasurable (fun x : ℤ => ∑ α ∈ sigmaStrataFinset A, f α x) Measure.count :=
    fun A _ _ => (measurable_of_countable _).aemeasurable
  have hkey := hC Measure.count S (fun A x => ∑ α ∈ sigmaStrataFinset A, f α x) hm hint horth
  simpa using hkey

/-- **The Khintchine/square-function inequality for the strata, `tsum` (real) form.** -/
theorem khintchine_majorArc_real_strata (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmall : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r)
        ≤ C ^ (k * r) * ∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r := by
  classical
  obtain ⟨C, hCpos, hC⟩ := khintchine_majorArc_strata k r hr hk
  refine ⟨C, hCpos, ?_⟩
  intro S h2 hS f hf ε hF hsmall
  set Hf : ℤ → ℝ := fun x => ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2 with hHf
  set Gf : ℤ → ℝ := fun x => Hf x ^ r with hGf
  set Ff : ℤ → ℝ := fun x => ‖(∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r) with hFf
  show ∑' x, Ff x ≤ C ^ (k * r) * ∑' x, Gf x
  have hlin : (∑' x, ENNReal.ofReal (Ff x))
      ≤ ENNReal.ofReal (C ^ (k * r)) * (∑' x, ENNReal.ofReal (Gf x)) := by
    have h := hC h2 hS hf hF hsmall
    have hl1 : ∫⁻ x, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑ α ∈ sigmaStrataFinset A, f α x‖ₑ ^ (2 * (r : ℝ)) ∂Measure.count
        = ∑' x, ENNReal.ofReal (Ff x) := by
      simpa only [Ff] using lintegral_count_enorm_rpow (fun x : ℤ =>
        ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ∑ α ∈ sigmaStrataFinset A, f α x) r
    have hl2 : ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖∑ α ∈ sigmaStrataFinset A, f α x‖ₑ ^ 2) ^ r ∂Measure.count
        = ∑' x, ENNReal.ofReal (Gf x) := by
      simpa only [Gf, Hf] using lintegral_count_sum_enorm_rpow
        (S.powerset.filter (fun A => A.card ≤ k)) (fun A x => ∑ α ∈ sigmaStrataFinset A, f α x) r
    calc (∑' x, ENNReal.ofReal (Ff x))
        = ∫⁻ x, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ α ∈ sigmaStrataFinset A, f α x‖ₑ ^ (2 * (r : ℝ)) ∂Measure.count := hl1.symm
      _ ≤ ENNReal.ofReal (C ^ (k * r)) * (∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖∑ α ∈ sigmaStrataFinset A, f α x‖ₑ ^ 2) ^ r ∂Measure.count) := h
      _ = ENNReal.ofReal (C ^ (k * r)) * (∑' x, ENNReal.ofReal (Gf x)) := by rw [hl2]
  have hGsum : Summable Gf := summable_powerset_rpow_strata (S := S) (f := f) hf k r hr
  have hGnonneg : ∀ x, 0 ≤ Gf x :=
    fun x => pow_nonneg (Finset.sum_nonneg (fun A _ => sq_nonneg _)) r
  have hRHS : ENNReal.ofReal (C ^ (k * r)) * (∑' x, ENNReal.ofReal (Gf x))
      = ENNReal.ofReal (C ^ (k * r) * ∑' x, Gf x) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hGnonneg hGsum, ← ENNReal.ofReal_mul (by positivity)]
  rw [hRHS] at hlin
  have hnf_ne_top : (∑' x, ENNReal.ofReal (Ff x)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  have hFnonneg : ∀ x, 0 ≤ Ff x := fun x => pow_nonneg (norm_nonneg _) (2 * r)
  have hFsum : Summable Ff := summable_of_tsum_ofReal_ne_top hFnonneg hnf_ne_top
  have hnf : (∑' x, ENNReal.ofReal (Ff x)) = ENNReal.ofReal (∑' x, Ff x) :=
    (ENNReal.ofReal_tsum_of_nonneg hFnonneg hFsum).symm
  have hmain : ENNReal.ofReal (∑' x, Ff x) ≤ ENNReal.ofReal (C ^ (k * r) * ∑' x, Gf x) := by
    rw [← hnf]
    exact hlin
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (tsum_nonneg hGnonneg))] at hmain
  exact hmain

end Work.BourgainPlan.IonescuWainger

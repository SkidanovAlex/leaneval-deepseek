import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_majorArc

/-!
# The real (`tsum`) form of the Khintchine/square-function inequality for major arcs

`khintchine_majorArc` (in the sibling file) states the Ionescu–Wainger denominator-orthogonality
square function estimate as an inequality of Lebesgue integrals against the counting measure on
`ℤ`.  Here we extract the equivalent `tsum` form used by the multiplier theorem: converting the
`lintegral` of the `ENNReal`-valued integrands back into a series of the corresponding real
quantities.  The two analytic inputs are

* the finiteness of `∑' (Σ_A ‖Σ_{α∈Σ_A} f_α‖²)^r` (a finite sum of `ℓ²` norms is `ℓ¹`, hence
  bounded, hence its `r`-th power is still `ℓ¹`), which shows that the `ENNReal` `tsum` is finite,
  so the `ofReal`/`toReal` bookkeeping applies; and
* the monotonicity of `ENNReal.toReal` on the resulting finite values.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BourgainPlan.IonescuWainger

/-- A square-summable sequence (`ℓ²`) has summable squared norms (`ℓ¹`). -/
private lemma summable_norm_sq_of_memℓp {g : ℤ → ℂ} (hg : Memℓp g 2) :
    Summable fun x => ‖g x‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp hg
  simpa [Real.rpow_natCast] using h

/-- The `lintegral` against the counting measure on `ℤ` of `‖g‖ₑ ^ (2r)` is the `tsum` of
`ENNReal.ofReal` applied to the `2r`-th powers of the norms. -/
lemma lintegral_count_enorm_rpow (g : ℤ → ℂ) (r : ℕ) :
    ∫⁻ x, ‖g x‖ₑ ^ (2 * (r : ℝ)) ∂Measure.count
      = ∑' x, ENNReal.ofReal (‖g x‖ ^ (2 * r)) := by
  rw [MeasureTheory.lintegral_count]
  refine tsum_congr fun x => ?_
  rw [← ofReal_norm]
  rw [show (2 : ℝ) * (r : ℝ) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
  rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The `lintegral` against the counting measure on `ℤ` of `(Σ_A ‖g_A‖ₑ²)^r` is the `tsum` of
`ENNReal.ofReal` applied to `(Σ_A ‖g_A‖²)^r`. -/
lemma lintegral_count_sum_enorm_rpow (T : Finset (Finset ℕ)) (g : Finset ℕ → ℤ → ℂ) (r : ℕ) :
    ∫⁻ x, (∑ A ∈ T, ‖g A x‖ₑ ^ 2) ^ r ∂Measure.count
      = ∑' x, ENNReal.ofReal ((∑ A ∈ T, ‖g A x‖ ^ 2) ^ r) := by
  rw [MeasureTheory.lintegral_count]
  refine tsum_congr fun x => ?_
  have hterm : ∀ A, ‖g A x‖ₑ ^ 2 = ENNReal.ofReal (‖g A x‖ ^ 2) := by
    intro A
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (∑ A ∈ T, ‖g A x‖ₑ ^ 2) = ∑ A ∈ T, ENNReal.ofReal (‖g A x‖ ^ 2)
      from Finset.sum_congr rfl (fun A _ => hterm A)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun A _ => sq_nonneg _)]
  rw [← ENNReal.ofReal_pow (Finset.sum_nonneg (fun A _ => sq_nonneg _)) r]

/-- If `F ≥ 0` and `∑' x, ENNReal.ofReal (F x) ≠ ⊤` then `F` is summable. -/
lemma summable_of_tsum_ofReal_ne_top {F : ℤ → ℝ} (hF : ∀ x, 0 ≤ F x)
    (h : ∑' x, ENNReal.ofReal (F x) ≠ ⊤) : Summable F := by
  have hnn : Summable fun x : ℤ => (F x).toNNReal := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [ENNReal.ofReal] using h
  have hcoe : Summable fun x : ℤ => ((F x).toNNReal : ℝ) := NNReal.summable_coe.mpr hnn
  refine hcoe.congr fun x => ?_
  rw [Real.coe_toNNReal', max_eq_left (hF x)]

/-- For `r ≥ 1`, the `r`-th power of `Σ_A ‖Σ_{α ∈ Σ_A} f_α‖²` is summable in `x`: the sum of the
squared norms is `ℓ¹` (a finite sum of `ℓ²` sequences), hence bounded, so its `r`-th power stays
`ℓ¹`. -/
lemma summable_powerset_rpow {S : Finset ℕ} {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2)
    (k r : ℕ) (hr : 1 ≤ r) :
    Summable fun x : ℤ => (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) ^ r := by
  have hw_mem : ∀ A, Memℓp (fun x => ∑ α ∈ sigmaAFinset A, f α x) 2 :=
    fun A => Memℓp.finsetSum (sigmaAFinset A) (fun α _ => hf α)
  have hsq : ∀ A, Summable (fun x => ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) :=
    fun A => summable_norm_sq_of_memℓp (hw_mem A)
  have hHsum : Summable (fun x => ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) :=
    summable_sum (L := SummationFilter.unconditional ℤ)
      (f := fun A x => ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2)
      (s := S.powerset.filter (fun A => A.card ≤ k)) (fun A _ => hsq A)
  set M : ℝ := max 1 (∑' x, ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) with hM
  refine Summable.of_nonneg_of_le
    (f := fun x : ℤ => M ^ (r - 1) * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2)) (fun x => ?_) (fun x => ?_)
    (hHsum.mul_left (M ^ (r - 1)))
  · exact pow_nonneg (Finset.sum_nonneg (fun A _ => sq_nonneg _)) r
  · have hnn : 0 ≤ ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2 := Finset.sum_nonneg (fun A _ => sq_nonneg _)
    have hle : (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) ≤ M := by
      rw [hM]
      exact le_trans (Summable.le_tsum hHsum x
        (fun j _ => Finset.sum_nonneg (fun A _ => sq_nonneg _))) (le_max_right _ _)
    have hpow : (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) ^ r
        = (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) ^ (r - 1)
          * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) := by
      conv_lhs => rw [show r = (r - 1) + 1 from (Nat.sub_add_cancel hr).symm]
      rw [pow_succ]
    calc (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) ^ r
        = (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
              ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) ^ (r - 1)
            * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) :=
          hpow
      _ ≤ M ^ (r - 1) * (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖∑ α ∈ sigmaAFinset A, f α x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hle (r - 1)) hnn

theorem khintchine_majorArc_real (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmall : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (∑ α ∈ sigmaAFinset A, f α x)‖ ^ (2 * r)
        ≤ C ^ (k * r) * ∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖(∑ α ∈ sigmaAFinset A, f α x)‖ ^ 2) ^ r := by
  classical
  obtain ⟨C, hCpos, hC⟩ := khintchine_majorArc k r hr hk
  refine ⟨C, hCpos, ?_⟩
  intro S h2 hS f hf ε hF hsmall
  set Hf : ℤ → ℝ := fun x => ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖(∑ α ∈ sigmaAFinset A, f α x)‖ ^ 2 with hHf
  set Gf : ℤ → ℝ := fun x => Hf x ^ r with hGf
  set Ff : ℤ → ℝ := fun x => ‖(∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ∑ α ∈ sigmaAFinset A, f α x)‖ ^ (2 * r) with hFf
  show ∑' x, Ff x ≤ C ^ (k * r) * ∑' x, Gf x
  have hlin : (∑' x, ENNReal.ofReal (Ff x))
      ≤ ENNReal.ofReal (C ^ (k * r)) * (∑' x, ENNReal.ofReal (Gf x)) := by
    have h := hC h2 hS hf hF hsmall
    have hl1 : ∫⁻ x, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑ α ∈ sigmaAFinset A, f α x‖ₑ ^ (2 * (r : ℝ)) ∂Measure.count
        = ∑' x, ENNReal.ofReal (Ff x) := by
      simpa only [Ff] using lintegral_count_enorm_rpow (fun x : ℤ =>
        ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ∑ α ∈ sigmaAFinset A, f α x) r
    have hl2 : ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖∑ α ∈ sigmaAFinset A, f α x‖ₑ ^ 2) ^ r ∂Measure.count
        = ∑' x, ENNReal.ofReal (Gf x) := by
      simpa only [Gf, Hf] using lintegral_count_sum_enorm_rpow
        (S.powerset.filter (fun A => A.card ≤ k)) (fun A x => ∑ α ∈ sigmaAFinset A, f α x) r
    calc (∑' x, ENNReal.ofReal (Ff x))
        = ∫⁻ x, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ α ∈ sigmaAFinset A, f α x‖ₑ ^ (2 * (r : ℝ)) ∂Measure.count := hl1.symm
      _ ≤ ENNReal.ofReal (C ^ (k * r)) * (∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖∑ α ∈ sigmaAFinset A, f α x‖ₑ ^ 2) ^ r ∂Measure.count) := h
      _ = ENNReal.ofReal (C ^ (k * r)) * (∑' x, ENNReal.ofReal (Gf x)) := by rw [hl2]
  have hGsum : Summable Gf := summable_powerset_rpow (S := S) (f := f) hf k r hr
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

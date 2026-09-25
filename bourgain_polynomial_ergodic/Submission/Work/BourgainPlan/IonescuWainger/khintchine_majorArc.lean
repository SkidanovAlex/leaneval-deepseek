import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.superorthogonal_khintchine_hypersystem
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.summable_norm_prod_of_freqSupport

/-!
# The Khintchine/square-function inequality for band-limited major-arc systems

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Theorem `sys-ortho`(ii) applied to the major-arc system `f_{Σ_A} = Σ_{α ∈ Σ_A} f_α` of a
band-limited system `(f_α)_{α ∈ 𝕋}` (Lemma `ortho`(ii)/(iii) supplies the orthogonality
hypothesis).

**Statement.** For `k, r ∈ ℕ`, `k, r ≥ 1`, there is a constant `C = C(k,r) > 0` such that for every
finite set `S` of pairwise coprime integers `≥ 2`, every band-limited system
`f : 𝕋 → ℓ²(ℤ)` with `f_δ` Fourier-supported in the arc `arcSet δ ε`, and every scale `ε`
satisfying the separation condition

`2r·ε < 1 / ∏_j Q_{A_j}`

on every nonce family `A : Fin r ⊕ Fin r → Finset ℕ` of `k`-bounded subsets of `S`, one has

`∫⁻ ‖Σ_{A ∈ binom(S,≤k)} f_{Σ_A}‖^{2r} ≤ C^{kr} ∫⁻ (Σ_{A ∈ binom(S,≤k)} ‖f_{Σ_A}‖²)^r.`

This is the Ionescu–Wainger "denominator orthogonality" square-function estimate in the form in
which the multiplier theorem consumes it: the constant is uniform in `S` (it depends only on
`k, r`), which is exactly what the `ℓ²`-based trivial Cauchy–Schwarz estimate cannot give.

**Proof.** Apply the hypersystem Khintchine inequality `superorthogonal_khintchine_hypersystem`
(Tao `sys-ortho`(ii)) on `X = ℤ` with the counting measure to the major-arc systems
`A ↦ f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`, whose nonce-orthogonality is
`tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce` (Tao Lemma `ortho`(ii)).  The two analytic
hypotheses of the hypersystem are supplied here: measurability is automatic for the (discrete)
counting measure on `ℤ`, and integrability of the products of the `2r` square-summable
major-arc systems is the finiteness §(`integrable_prod_norm_prod`), proved by absorbing one
factor at a time into an `ℓ¹` weight (`summable_mul_finset_prod` of
`summable_norm_prod_of_freqSupport.lean`) — any finite product of at least two `ℓ²(ℤ)`
sequences is `ℓ¹`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.BourgainPlan.IonescuWainger

/-- **The Bochner integral against the counting measure on `ℤ` is the sum.**  `Measure.count` on
`ℤ` is the sum of the Dirac masses, so `∫ x, f x ∂count = Σ'_x f x` for integrable `f`. -/
lemma integral_count_eq_tsum (f : ℤ → ℂ) (hf : Integrable f Measure.count) :
    ∫ x, f x ∂Measure.count = ∑' x, f x := by
  have h := hasSum_integral_measure (μ := fun i : ℤ => Measure.dirac i) (f := f) hf
  simp only [integral_dirac] at h
  exact h.tsum_eq.symm

/-- **A product of `2r ≥ 2` square-summable sequences is summable.**  This is
`summable_norm_prod_of_freqSupport` re-indexed: the `2r` factors are presented as the two halves
`G (inl i)`, `G (inr i)` of a family indexed by `Fin r ⊕ Fin r`.

Proof: the AM–GM bound `2‖a‖‖b‖ ≤ ‖a‖² + ‖b‖²` inserts two factors at a time into an `ℓ¹` weight
(`summable_mul_finset_prod`). -/
lemma summable_norm_prod_sum_type {r : ℕ} (hr : 1 ≤ r) (G : Fin r ⊕ Fin r → ℤ → ℂ)
    (hG : ∀ i, Memℓp (G i) 2) : Summable fun x => ∏ i, ‖G i x‖ := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  have hsq : ∀ i : Fin r ⊕ Fin r, Summable fun x => ‖G i x‖ ^ 2 := by
    intro i
    have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (hG i)
    simpa [Real.rpow_natCast] using h
  have hmain := summable_mul_finset_prod
    (fun x : ℤ => (‖G (Sum.inl 0) x‖ ^ 2 + ‖G (Sum.inr 0) x‖ ^ 2) / 2)
    (fun x => by positivity)
    (((hsq (Sum.inl 0)).add (hsq (Sum.inr 0))).div_const 2)
    (fun i : Fin r ⊕ Fin r => fun x => ‖G i x‖)
    (fun i x => norm_nonneg _) hsq
    ((Finset.univ.erase (Sum.inl (0 : Fin r))).erase (Sum.inr (0 : Fin r)))
  refine Summable.of_nonneg_of_le (fun x => Finset.prod_nonneg fun i _ => norm_nonneg _)
    (fun x => ?_) hmain
  have h0 : (∏ i ∈ Finset.univ.erase (Sum.inl (0 : Fin r)), ‖G i x‖)
        * ‖G (Sum.inl (0 : Fin r)) x‖ = ∏ i, ‖G i x‖ :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ _)
  have h1 : (∏ i ∈ (Finset.univ.erase (Sum.inl (0 : Fin r))).erase (Sum.inr (0 : Fin r)),
        ‖G i x‖) * ‖G (Sum.inr (0 : Fin r)) x‖
      = ∏ i ∈ Finset.univ.erase (Sum.inl (0 : Fin r)), ‖G i x‖ :=
    Finset.prod_erase_mul _ _ (by simp)
  have hle : ‖G (Sum.inl (0 : Fin r)) x‖ * ‖G (Sum.inr (0 : Fin r)) x‖
      ≤ (‖G (Sum.inl 0) x‖ ^ 2 + ‖G (Sum.inr 0) x‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖G (Sum.inl 0) x‖ - ‖G (Sum.inr 0) x‖)]
  have hR : 0 ≤ ∏ i ∈ (Finset.univ.erase (Sum.inl (0 : Fin r))).erase
      (Sum.inr (0 : Fin r)), ‖G i x‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [← h0, ← h1]
  calc ((∏ i ∈ (Finset.univ.erase (Sum.inl (0 : Fin r))).erase (Sum.inr (0 : Fin r)), ‖G i x‖)
          * ‖G (Sum.inr (0 : Fin r)) x‖) * ‖G (Sum.inl (0 : Fin r)) x‖
      = (∏ i ∈ (Finset.univ.erase (Sum.inl (0 : Fin r))).erase (Sum.inr (0 : Fin r)), ‖G i x‖)
          * (‖G (Sum.inl (0 : Fin r)) x‖ * ‖G (Sum.inr (0 : Fin r)) x‖) := by ring
    _ ≤ (∏ i ∈ (Finset.univ.erase (Sum.inl (0 : Fin r))).erase (Sum.inr (0 : Fin r)), ‖G i x‖)
          * ((‖G (Sum.inl 0) x‖ ^ 2 + ‖G (Sum.inr 0) x‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hle hR
    _ = ((‖G (Sum.inl 0) x‖ ^ 2 + ‖G (Sum.inr 0) x‖ ^ 2) / 2)
          * ∏ i ∈ (Finset.univ.erase (Sum.inl (0 : Fin r))).erase (Sum.inr (0 : Fin r)),
              ‖G i x‖ := by ring

/-- **The real product of the norms of `2r` square-summable sequences is integrable against the
counting measure on `ℤ`** — i.e. it is `ℓ¹`. -/
lemma integrable_prod_norm_prod {r : ℕ} (hr : 1 ≤ r) (G : Fin r ⊕ Fin r → ℤ → ℂ)
    (hG : ∀ i, Memℓp (G i) 2) :
    Integrable (fun x : ℤ => ∏ i : Fin r, ‖G (Sum.inl i) x‖ * ‖G (Sum.inr i) x‖)
      Measure.count := by
  have hsum := summable_norm_prod_sum_type hr G hG
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_count_iff]
  have hfun : (fun x : ℤ => ‖∏ i : Fin r, ‖G (Sum.inl i) x‖ * ‖G (Sum.inr i) x‖‖)
      = (fun x : ℤ => ∏ j : Fin r ⊕ Fin r, ‖G j x‖) := by
    funext x
    rw [Real.norm_of_nonneg
        (Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      Finset.prod_mul_distrib, ← Fintype.prod_sum_type (f := fun j : Fin r ⊕ Fin r => ‖G j x‖)]
  rw [hfun]
  exact hsum

/-- **The complex product of the two halves of a `2r`-tuple of square-summable sequences is
integrable** (the integrand of the orthogonality identity).  This follows from the integrability
of the product of the norms, because the norm of a product is the product of the norms. -/
lemma integrable_prod_star_mul {r : ℕ} {G : Fin r ⊕ Fin r → ℤ → ℂ}
    (hint : Integrable (fun x : ℤ => ∏ i : Fin r, ‖G (Sum.inl i) x‖ * ‖G (Sum.inr i) x‖)
      Measure.count) :
    Integrable (fun x : ℤ => ∏ i : Fin r, star (G (Sum.inl i) x) * G (Sum.inr i) x)
      Measure.count := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_count_iff]
  have h := (hasFiniteIntegral_count_iff.mp hint.2)
  have hfun : (fun x : ℤ => ‖∏ i : Fin r, star (G (Sum.inl i) x) * G (Sum.inr i) x‖)
      = (fun x : ℤ => ‖∏ i : Fin r, ‖G (Sum.inl i) x‖ * ‖G (Sum.inr i) x‖‖) := by
    funext x
    rw [norm_prod, Real.norm_of_nonneg
      (Finset.prod_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact Finset.prod_congr rfl fun i _ => by rw [norm_mul, norm_star]
  rw [hfun]
  exact h

theorem khintchine_majorArc (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmall : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)),
      ∫⁻ x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (∑ α ∈ sigmaAFinset A, f α x)‖ₑ ^ (2 * (r : ℝ)) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ (k * r)) *
            ∫⁻ x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
                ‖(∑ α ∈ sigmaAFinset A, f α x)‖ₑ ^ 2) ^ r ∂MeasureTheory.Measure.count := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  obtain ⟨C, hCpos, hC⟩ :=
    superorthogonal_khintchine_hypersystem (X := ℤ) (α := ℕ) k (n + 1) (by omega) hk
  refine ⟨C, hCpos, ?_⟩
  intro S h2 hS f hf ε hF hsmall
  have hint : ∀ A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ,
      (∀ i, A i ⊆ S ∧ (A i).card ≤ k) →
      Integrable (fun x : ℤ => ∏ i : Fin (n + 1),
        ‖∑ α ∈ sigmaAFinset (A (Sum.inl i)), f α x‖ *
        ‖∑ α ∈ sigmaAFinset (A (Sum.inr i)), f α x‖) Measure.count := by
    intro A _
    exact integrable_prod_norm_prod (by omega)
      (fun j x => ∑ α ∈ sigmaAFinset (A j), f α x)
      (fun j => Memℓp.finsetSum (sigmaAFinset (A j)) (fun α _ => hf α))
  have horth : ∀ A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ,
      (∀ i, A i ⊆ S ∧ (A i).card ≤ k) → HasNonce A →
      ∫ x, (∏ i : Fin (n + 1),
        star (∑ α ∈ sigmaAFinset (A (Sum.inl i)), f α x) *
        (∑ β ∈ sigmaAFinset (A (Sum.inr i)), f β x)) ∂Measure.count = 0 := by
    intro A hA hnonce
    rw [integral_count_eq_tsum _ (integrable_prod_star_mul
      (G := fun j x => ∑ α ∈ sigmaAFinset (A j), f α x) (hint A hA))]
    exact tsum_prod_sigmaA_mul_conj_eq_zero_of_nonce h2 hS hf hF (fun j => (hA j).1) hnonce
      (hsmall A hA hnonce)
  have hm : ∀ A : Finset ℕ, A ⊆ S → A.card ≤ k →
      AEMeasurable (fun x : ℤ => ∑ α ∈ sigmaAFinset A, f α x) Measure.count :=
    fun A _ _ => (measurable_of_countable _).aemeasurable
  have hkey := hC Measure.count S (fun A x => ∑ α ∈ sigmaAFinset A, f α x) hm hint horth
  simpa using hkey

end Work.BourgainPlan.IonescuWainger

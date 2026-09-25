import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT
import Submission.Work.BourgainPlan.IonescuWainger.sigmaSubA_add
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_add_mem

/-!
# (A0)/(A3) Quantitative separation of the Ionescu–Wainger major arcs

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Definition `major-arc` and Lemma `ortho`(i)(ii) (§4); local copy
`REFS/Tao_2008.05066_IonescuWainger.tex`.

This file supplies the *quantitative* arithmetic that `ortho`(i) (separation) and `ortho`(ii)
(denominator orthogonality) of Tao's Ionescu–Wainger argument are made of, in the 1-dimensional
vocabulary of `ArcDefs.lean` / `ArcCRT.lean`:

* `norm_circle_coe_le_abs`, `arcPt_eq_zero_iff_dvd`, `norm_arcPt_ge` — the circle norm of a
  rational point: `c/Q ∈ 𝕋 = ℝ/ℤ` is either `0` (exactly when `Q ∣ c`) or at distance at least
  `1/Q` from `0`;
* `arcPt_commonDenom`, `sum_smul_arcPt_eq_arcPt` — putting a signed sum
  `Σ_i ±(a_i/Q_i) ∈ 𝕋` over the common denominator `∏_i Q_i`;
* `sigmaA_nonce_sum_norm_ge` — **the quantitative nonce lemma**: if the family `(A i)` carries a
  nonce, the signed sum of the points `a_i/Q_{A i}` of exact denominator is at distance at least
  `1/∏_i Q_{A i}` from `0` (upgrading `sigmaA_nonce_sum_ne_zero` of `ArcCRT.lean`, which gives only
  non-vanishing);
* `sigmaA_nonce_sum_perturbed_ne_zero` and `sigmaA_nonce_sum_perturbed_ne_zero_of_good` — the
  `ε`-perturbed form actually used in `ortho`(ii): the *thetas* `θ_i ∈ [-ε,ε]` cannot destroy the
  non-vanishing, by the `(r,c)`-good smallness `ε < c/(2r q_max^{2rk})`;
* `sigmaA_separation`, `sigmaLe_separation`, `sigmaLe_separation_of_good` — Tao's `ortho`(i): two
  distinct arc centres `a/Q_A ≠ b/Q_B` of `Σ_{≤k}` are at distance at least `1/q_max^{2k}`, hence
  (by `(r,c)`-goodness) at distance at least `2ε/c`, so the arcs `α + [-ε,ε]` are pairwise disjoint;
* `sigmaComp_add_mem_sigmaLe` — Tao's (sigma-include): `Σ_{A₀} + Σ_{(A₀)} ⊆ Σ_{≤ k}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## The circle norm of a rational point -/

/-- **The norm of a real number in `𝕋 = ℝ/ℤ` is at most its absolute value.** -/
lemma norm_circle_coe_le_abs (θ : ℝ) : ‖(θ : Circle)‖ ≤ |θ| := by
  by_cases h : |θ| ≤ 1 / 2
  · rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero (x := θ)).mpr (by simpa using h)]
  · have h2 : ‖(θ : Circle)‖ ≤ (1 : ℝ) / 2 := by
      simpa using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := (θ : Circle))
    linarith [not_le.mp h, h2]

/-- **`arcPt Q c = 0` exactly when `Q ∣ c`** (for `Q ≥ 1`). -/
lemma arcPt_eq_zero_iff_dvd {Q : ℕ} (hQ : Q ≠ 0) (c : ℤ) :
    arcPt Q c = 0 ↔ (Q : ℤ) ∣ c := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  constructor
  · intro h
    rw [arcPt, AddCircle.coe_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    rw [zsmul_one] at hn
    refine ⟨n, ?_⟩
    have h2 : (c : ℝ) = (n : ℝ) * (Q : ℝ) := by rw [hn, div_mul_cancel₀ _ hQr]
    have h3 : ((c : ℤ) : ℝ) = (((n * (Q : ℤ) : ℤ)) : ℝ) := by push_cast; exact h2
    have h4 : c = n * (Q : ℤ) := Int.cast_injective h3
    rw [h4, mul_comm]
  · rintro ⟨n, rfl⟩
    rw [arcPt]
    have h4 : ((((Q : ℤ) * n : ℤ)) : ℝ) / (Q : ℝ) = (n : ℝ) := by
      push_cast
      field_simp
    rw [h4]
    exact coe_int_circle_eq_zero n

/-- **Quantitative non-vanishing of a rational point**: if `c/Q ∈ 𝕋` is not `0` (`Q ≥ 1`) then it
is at distance at least `1/Q` from `0`. -/
lemma norm_arcPt_ge {Q : ℕ} (hQ : 1 ≤ Q) {c : ℤ} (h : arcPt Q c ≠ 0) :
    1 / (Q : ℝ) ≤ ‖arcPt Q c‖ := by
  have hQ0 : Q ≠ 0 := by omega
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQr : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have hndvd : ¬ ((Q : ℤ) ∣ c) := fun hd => h ((arcPt_eq_zero_iff_dvd hQ0 c).mpr hd)
  rw [arcPt, UnitAddCircle.norm_eq]
  set m : ℤ := round ((c : ℝ) / (Q : ℝ)) with hm
  have hkey : (c : ℤ) - m * (Q : ℤ) ≠ 0 := by
    intro hzero
    exact hndvd ⟨m, by rw [mul_comm]; exact sub_eq_zero.mp hzero⟩
  have h1 : (1 : ℤ) ≤ |(c : ℤ) - m * (Q : ℤ)| := Int.one_le_abs hkey
  have hsplit : (c : ℝ) / (Q : ℝ) - (m : ℝ)
      = (((c : ℤ) - m * (Q : ℤ) : ℤ) : ℝ) / (Q : ℝ) := by
    rw [show (m : ℝ) = (m : ℝ) * (Q : ℝ) / (Q : ℝ) by field_simp, ← sub_div]
    congr 1
    push_cast
    ring
  rw [hsplit, abs_div, abs_of_pos hQpos]
  rw [div_le_div_iff_of_pos_right hQpos]
  exact_mod_cast h1

/-! ## Sums of arc points over a common denominator -/

/-- The additive-group homomorphism `ℤ → 𝕋`, `n ↦ n/Q`. -/
noncomputable def arcPtHom (Q : ℕ) : ℤ →+ Circle where
  toFun := arcPt Q
  map_zero' := arcPt_zero Q
  map_add' a b := (arcPt_add Q a b).symm

/-- `a/Q = (a·(L/Q))/L` in `𝕋` when `Q ∣ L` (same point, common denominator). -/
lemma arcPt_commonDenom {Q L : ℕ} (hQ : 1 ≤ Q) (hL : 1 ≤ L) (hdvd : Q ∣ L) (a : ℤ) :
    arcPt Q a = arcPt L (a * (((L / Q : ℕ)) : ℤ)) := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  rw [arcPt, arcPt]
  congr 1
  have h1 : ((L / Q : ℕ) : ℝ) = (L : ℝ) / (Q : ℝ) := Nat.cast_div hdvd hQr
  have hLa : ((a * (((L / Q : ℕ)) : ℤ) : ℤ) : ℝ) = (a : ℝ) * ((L : ℝ) / (Q : ℝ)) := by
    rw [Int.cast_mul, Int.cast_natCast, h1]
  rw [hLa]
  field_simp

/-- **A signed sum of rational points over a common denominator**: the sum `Σ_i ±(a_i/Q_i)` can be
written, in the circle, as a single rational point of denominator `∏_i Q_i`. -/
lemma sum_smul_arcPt_eq_arcPt {ι : Type*} [Fintype ι] {Q : ι → ℕ} (hQ : ∀ i, 1 ≤ Q i)
    (a : ι → ℤ) (sgn : ι → ℤ) :
    (∑ i, sgn i • arcPt (Q i) (a i))
      = arcPt (∏ i, Q i) (∑ i, sgn i * a i * (((∏ j, Q j) / Q i : ℕ) : ℤ)) := by
  have hL1 : 1 ≤ ∏ i, Q i := Finset.one_le_prod₀ fun i _ => hQ i
  have hdvd : ∀ i, Q i ∣ ∏ j, Q j := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hstep : ∀ i, sgn i • arcPt (Q i) (a i)
      = arcPt (∏ j, Q j) (sgn i * a i * (((∏ j, Q j) / Q i : ℕ) : ℤ)) := by
    intro i
    rw [← arcPt_commonDenom (hQ i) hL1 (hdvd i) (sgn i * a i), zsmul_arcPt, arcPt]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  have hmap := map_sum (arcPtHom (∏ j, Q j))
    (fun i => sgn i * a i * (((∏ j, Q j) / Q i : ℕ) : ℤ)) (Finset.univ : Finset ι)
  simpa only [arcPtHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hmap.symm

/-! ## The quantitative nonce lemma -/

/-- **Quantitative denominator orthogonality (Tao's `ortho`(ii), sharp form).**  With the notation
and hypotheses of `sigmaA_nonce_sum_ne_zero` (`ArcCRT.lean`), the signed sum of points of exact
denominator is not merely non-zero but at distance at least `1/∏_i Q_{A i}` from `0` in `𝕋`. -/
theorem sigmaA_nonce_sum_norm_ge {ι : Type*} [Fintype ι]
    {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : ι → Finset ℕ} (hA : ∀ i, A i ⊆ S)
    {sgn : ι → ℤ} (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    {a : ι → ℤ} (ha : ∀ i, Nat.Coprime (a i).natAbs (QA (A i)))
    (hnonce : ∃ j : ι, ∃ q ∈ A j, ∀ i, i ≠ j → q ∉ A i) :
    1 / ((∏ i, QA (A i) : ℕ) : ℝ) ≤ ‖∑ i, sgn i • arcPt (QA (A i)) (a i)‖ := by
  have hne := sigmaA_nonce_sum_ne_zero h2 hS hA hsgn ha hnonce
  have hpos : ∀ i, 1 ≤ QA (A i) := fun i => by
    show 1 ≤ ∏ q ∈ A i, q
    exact Finset.one_le_prod₀ fun q hq => by have := h2 q (hA i hq); omega
  have hne' := hne
  rw [sum_smul_arcPt_eq_arcPt hpos a sgn] at hne'
  rw [sum_smul_arcPt_eq_arcPt hpos a sgn]
  exact norm_arcPt_ge (Finset.one_le_prod₀ fun i _ => hpos i) hne'

/-! ## The `ε`-perturbed form (`ortho`(ii) as used) -/

/-- **The `ε`-perturbed quantitative nonce lemma.**  Perturbing the arc points by real numbers
`θ_i` with `|θ_i| ≤ ε` cannot produce a vanishing signed sum, as long as
`#ι · ε < 1/∏_i Q_{A i}` — the perturbation is smaller than the separation guaranteed by
`sigmaA_nonce_sum_norm_ge`.  This is the arithmetic content of Tao's Fourier-transform verification
of `ortho`(ii) (arXiv:2008.05066, §4). -/
theorem sigmaA_nonce_sum_perturbed_ne_zero {ι : Type*} [Fintype ι]
    {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : ι → Finset ℕ} (hA : ∀ i, A i ⊆ S)
    {sgn : ι → ℤ} (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    {a : ι → ℤ} (ha : ∀ i, Nat.Coprime (a i).natAbs (QA (A i)))
    (hnonce : ∃ j : ι, ∃ q ∈ A j, ∀ i, i ≠ j → q ∉ A i)
    {θ : ι → ℝ} {ε : ℝ} (hθ : ∀ i, |θ i| ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) * ε < 1 / ((∏ i, QA (A i) : ℕ) : ℝ)) :
    (∑ i, sgn i • (arcPt (QA (A i)) (a i) + (θ i : Circle))) ≠ 0 := by
  have hbase : 1 / ((∏ i, QA (A i) : ℕ) : ℝ) ≤ ‖∑ i, sgn i • arcPt (QA (A i)) (a i)‖ :=
    sigmaA_nonce_sum_norm_ge h2 hS hA hsgn ha hnonce
  have hsplit : (∑ i, sgn i • (arcPt (QA (A i)) (a i) + (θ i : Circle)))
      = (∑ i, sgn i • arcPt (QA (A i)) (a i)) + ∑ i, sgn i • (θ i : Circle) := by
    rw [Finset.sum_congr rfl (fun i _ => smul_add (sgn i) _ _), Finset.sum_add_distrib]
  have hnorm : ‖∑ i, sgn i • (θ i : Circle)‖ ≤ (Fintype.card ι : ℝ) * ε := by
    calc ‖∑ i, sgn i • (θ i : Circle)‖ ≤ ∑ i, ‖sgn i • (θ i : Circle)‖ := norm_sum_le _ _
      _ = ∑ i, ‖(θ i : Circle)‖ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rcases hsgn i with h | h <;> simp [h]
      _ ≤ ∑ i, |θ i| := Finset.sum_le_sum fun i _ => norm_circle_coe_le_abs (θ i)
      _ ≤ ∑ i, ε := Finset.sum_le_sum fun i _ => hθ i
      _ = (Fintype.card ι : ℝ) * ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  intro hzero
  have hsum0 : (∑ i, sgn i • arcPt (QA (A i)) (a i)) + ∑ i, sgn i • (θ i : Circle) = 0 := by
    rw [← hsplit]; exact hzero
  have hle : ‖(∑ i, sgn i • arcPt (QA (A i)) (a i))‖
      ≤ ‖(∑ i, sgn i • arcPt (QA (A i)) (a i)) + ∑ i, sgn i • (θ i : Circle)‖
        + ‖∑ i, sgn i • (θ i : Circle)‖ := by
    have h := norm_add_le ((∑ i, sgn i • arcPt (QA (A i)) (a i)) + ∑ i, sgn i • (θ i : Circle))
      (-(∑ i, sgn i • (θ i : Circle)))
    rw [norm_neg] at h
    have h2' : ((∑ i, sgn i • arcPt (QA (A i)) (a i)) + ∑ i, sgn i • (θ i : Circle))
        + -(∑ i, sgn i • (θ i : Circle)) = ∑ i, sgn i • arcPt (QA (A i)) (a i) := by abel
    rwa [h2'] at h
  rw [hsum0, norm_zero, zero_add] at hle
  linarith [hbase, hnorm, hle]

/-- **The `(r,c)`-good form of the perturbed nonce lemma.**  This is `ortho`(ii)'s verification in
exactly Tao's parameterisation: `A : ι → Finset ℕ` with `#ι = 2r`, every `|A i| ≤ k`, all elements
of `S` bounded by `q_max`, and the goodness condition `ε < c/(2r q_max^{2rk})` with `c < 1`. -/
theorem sigmaA_nonce_sum_perturbed_ne_zero_of_good {ι : Type*} [Fintype ι]
    {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : ι → Finset ℕ} (hA : ∀ i, A i ⊆ S)
    {sgn : ι → ℤ} (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    {a : ι → ℤ} (ha : ∀ i, Nat.Coprime (a i).natAbs (QA (A i)))
    (hnonce : ∃ j : ι, ∃ q ∈ A j, ∀ i, i ≠ j → q ∉ A i)
    {θ : ι → ℝ} {ε c : ℝ} {r k qmax : ℕ} (hr : 1 ≤ r)
    (hcard : Fintype.card ι = 2 * r) (hAcard : ∀ i, (A i).card ≤ k)
    (hmax : ∀ q ∈ S, q ≤ qmax) (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * r * (qmax : ℝ) ^ (2 * r * k))) (hθ : ∀ i, |θ i| ≤ ε) :
    (∑ i, sgn i • (arcPt (QA (A i)) (a i) + (θ i : Circle))) ≠ 0 := by
  refine sigmaA_nonce_sum_perturbed_ne_zero h2 hS hA hsgn ha hnonce hθ ?_
  -- `∏_i Q_{A i} ≤ q_max^{k·#ι} = q_max^{2rk}`
  have hqmax1 : 1 ≤ qmax := by
    rcases hnonce with ⟨j, q, hq, -⟩
    exact le_trans (by have := h2 q (hA j hq); omega) (hmax q (hA j hq))
  have hQle : ∀ i, QA (A i) ≤ qmax ^ k := by
    intro i
    calc QA (A i) = ∏ q ∈ A i, q := rfl
      _ ≤ ∏ _q ∈ A i, qmax := by
            refine Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) fun q hq => hmax q (hA i hq)
      _ = qmax ^ (A i).card := by rw [Finset.prod_const]
      _ ≤ qmax ^ k := Nat.pow_le_pow_right hqmax1 (hAcard i)
  have hProd : (∏ i, QA (A i)) ≤ qmax ^ (2 * r * k) := by
    calc (∏ i, QA (A i)) ≤ ∏ _i : ι, qmax ^ k :=
          Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) fun i _ => hQle i
      _ = (qmax ^ k) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
      _ = qmax ^ (k * Fintype.card ι) := by rw [← pow_mul]
      _ = qmax ^ (2 * r * k) := by rw [hcard]; congr 1; ring
  have hQpos : (0 : ℝ) < ((∏ i, QA (A i) : ℕ) : ℝ) := by
    have hp : 0 < ∏ i, QA (A i) := Finset.prod_pos fun i _ => by
      have h1 : 1 ≤ QA (A i) := by
        show 1 ≤ ∏ q ∈ A i, q
        exact Finset.one_le_prod₀ fun q hq => by have := h2 q (hA i hq); omega
      omega
    exact_mod_cast hp
  have hcast : (((qmax ^ (2 * r * k) : ℕ)) : ℝ) = (qmax : ℝ) ^ (2 * r * k) := Nat.cast_pow _ _
  have hQleR : ((∏ i, QA (A i) : ℕ) : ℝ) ≤ (qmax : ℝ) ^ (2 * r * k) := by
    rw [← hcast]; exact_mod_cast hProd
  have hqp : (0 : ℝ) < (qmax : ℝ) ^ (2 * r * k) := by
    have : (0 : ℝ) < (qmax : ℝ) := by exact_mod_cast hqmax1
    positivity
  have hrr : (0 : ℝ) < (2 : ℝ) * (r : ℝ) := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    linarith
  have hstep1 : (2 : ℝ) * (r : ℝ) * ε < c / (qmax : ℝ) ^ (2 * r * k) := by
    have h := mul_lt_mul_of_pos_left hgood hrr
    have hden : (2 : ℝ) * (r : ℝ) * (c / ((2 : ℝ) * (r : ℝ) * (qmax : ℝ) ^ (2 * r * k)))
        = c / (qmax : ℝ) ^ (2 * r * k) := by
      field_simp
    rwa [hden] at h
  have hcard' : ((Fintype.card ι : ℕ) : ℝ) = (2 : ℝ) * (r : ℝ) := by
    rw [hcard]; push_cast; ring
  rw [hcard']
  refine lt_of_lt_of_le hstep1 ?_
  calc c / (qmax : ℝ) ^ (2 * r * k) ≤ 1 / (qmax : ℝ) ^ (2 * r * k) :=
        div_le_div_of_nonneg_right (le_of_lt hc1) (le_of_lt hqp)
    _ ≤ 1 / ((∏ i, QA (A i) : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hQpos hQleR

/-! ## Separation of the arcs (`ortho`(i)) -/

/-- `-a/Q = (-a)/Q` in the circle. -/
lemma arcPt_neg (Q : ℕ) (a : ℤ) : arcPt Q (-a) = -arcPt Q a := by
  rw [arcPt, arcPt, ← AddCircle.coe_neg]
  congr 1
  push_cast
  ring

/-- Subtraction of two arc points over a common denominator. -/
lemma arcPt_sub_denom {Q R : ℕ} (hQ : Q ≠ 0) (hR : R ≠ 0) (a b : ℤ) :
    arcPt Q a - arcPt R b = arcPt (Q * R) (a * (R : ℤ) - b * (Q : ℤ)) := by
  rw [sub_eq_add_neg, ← arcPt_neg R b, arcPt_add_denom hQ hR]
  congr 1
  ring

/-- **Two distinct points of exact denominators `Q_A`, `Q_B` are `1/(Q_A Q_B)`-separated.** -/
theorem sigmaA_separation {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hAS : A ⊆ S) (hBS : B ⊆ S) {x y : Circle}
    (hx : x ∈ sigmaA A) (hy : y ∈ sigmaA B) (hne : x ≠ y) :
    1 / ((QA A * QA B : ℕ) : ℝ) ≤ ‖x - y‖ := by
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, rfl⟩ := hy
  have hAz : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hAS hq)
  have hBz : QA B ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hBS hq)
  have hZp : 1 ≤ QA A := Finset.one_le_prod₀ fun q hq => by have := h2 q (hAS hq); omega
  have hZp' : 1 ≤ QA B := Finset.one_le_prod₀ fun q hq => by have := h2 q (hBS hq); omega
  rw [arcPt_sub_denom hAz hBz]
  refine norm_arcPt_ge (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hAz hBz)) ?_
  intro h0
  have h1 : arcPt (QA A) a - arcPt (QA B) b = 0 := by
    rw [arcPt_sub_denom hAz hBz]; exact h0
  exact hne (sub_eq_zero.mp h1)

/-- **Tao's `ortho`(i), quantitative form.**  Two distinct arc centres `a/Q_A`, `b/Q_B` of the arc
set `Σ_{≤ k}` (so `A, B ⊆ S` with `|A|, |B| ≤ k`) are `q_max^{-2k}`-separated: their distance in `𝕋`
is at least `1/q_max^{2k}`. -/
theorem sigmaLe_separation {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (_hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A B : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) {k : ℕ} (hkA : A.card ≤ k) (hkB : B.card ≤ k)
    {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax) {a b : ℤ}
    (hne : arcPt (QA A) a ≠ arcPt (QA B) b) :
    1 / (qmax : ℝ) ^ (2 * k) ≤ ‖arcPt (QA A) a - arcPt (QA B) b‖ := by
  have hAz : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA hq)
  have hBz : QA B ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hB hq)
  have hqmax1 : 1 ≤ qmax := by
    have hne' : ¬ (A = ∅ ∧ B = ∅) := by
      rintro ⟨rfl, rfl⟩
      exact hne (by rw [show QA (∅ : Finset ℕ) = 1 from rfl, arcPt_one, arcPt_one])
    rcases Finset.eq_empty_or_nonempty A with hAe | hAne
    · have hBne : B.Nonempty := by
        rcases Finset.eq_empty_or_nonempty B with hBe | h
        · exact absurd ⟨hAe, hBe⟩ hne'
        · exact h
      obtain ⟨q', hq'⟩ := hBne
      exact le_trans (by have := h2 q' (hB hq'); omega) (hmax q' (hB hq'))
    · obtain ⟨q, hq⟩ := hAne
      exact le_trans (by have := h2 q (hA hq); omega) (hmax q (hA hq))
  have hsub := arcPt_sub_denom hAz hBz a b
  have hne0 : arcPt (QA A * QA B) (a * (QA B : ℤ) - b * (QA A : ℤ)) ≠ 0 := by
    rw [← hsub]; exact sub_ne_zero.mpr hne
  have hmain : 1 / ((QA A * QA B : ℕ) : ℝ) ≤ ‖arcPt (QA A) a - arcPt (QA B) b‖ := by
    rw [hsub]
    exact norm_arcPt_ge (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hAz hBz)) hne0
  refine le_trans ?_ hmain
  have hle : QA A * QA B ≤ qmax ^ (2 * k) := by
    have h1 : QA A ≤ qmax ^ k := by
      calc QA A = ∏ q ∈ A, q := rfl
        _ ≤ ∏ _q ∈ A, qmax := by
              refine Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) fun q hq => hmax q (hA hq)
        _ = qmax ^ A.card := by rw [Finset.prod_const]
        _ ≤ qmax ^ k := Nat.pow_le_pow_right hqmax1 hkA
    have h2' : QA B ≤ qmax ^ k := by
      calc QA B = ∏ q ∈ B, q := rfl
        _ ≤ ∏ _q ∈ B, qmax := by
              refine Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) fun q hq => hmax q (hB hq)
        _ = qmax ^ B.card := by rw [Finset.prod_const]
        _ ≤ qmax ^ k := Nat.pow_le_pow_right hqmax1 hkB
    calc QA A * QA B ≤ qmax ^ k * qmax ^ k := Nat.mul_le_mul h1 h2'
      _ = qmax ^ (k + k) := (pow_add qmax k k).symm
      _ = qmax ^ (2 * k) := by congr 1; ring
  have hpos : (0 : ℝ) < ((QA A * QA B : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.pos_of_ne_zero hAz) (Nat.pos_of_ne_zero hBz))
  have hcast : (((qmax ^ (2 * k) : ℕ)) : ℝ) = (qmax : ℝ) ^ (2 * k) := Nat.cast_pow _ _
  have hR : ((QA A * QA B : ℕ) : ℝ) ≤ (qmax : ℝ) ^ (2 * k) := by
    rw [← hcast]; exact_mod_cast hle
  exact one_div_le_one_div_of_le hpos hR

/-- **Tao's `ortho`(i) in the `(r,c)`-good parameterisation.**  Under the goodness condition
`ε < c/(2r q_max^{2rk})` the `q_max^{-2k}`-separation of `sigmaLe_separation` is at least `2ε/c`, so
the arcs `α + [-ε,ε]` with `α ∈ Σ_{≤ k}` are pairwise disjoint. -/
theorem sigmaLe_separation_of_good {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A B : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) {k r qmax : ℕ} (hr : 1 ≤ r)
    (hkA : A.card ≤ k) (hkB : B.card ≤ k)
    (hmax : ∀ q ∈ S, q ≤ qmax) {c ε : ℝ} (hc : 0 < c)
    (hgood : ε < c / (2 * r * (qmax : ℝ) ^ (2 * r * k))) {a b : ℤ}
    (hne : arcPt (QA A) a ≠ arcPt (QA B) b) :
    2 * ε / c ≤ ‖arcPt (QA A) a - arcPt (QA B) b‖ := by
  have hsep : 1 / (qmax : ℝ) ^ (2 * k) ≤ ‖arcPt (QA A) a - arcPt (QA B) b‖ :=
    sigmaLe_separation h2 hS hA hB hkA hkB hmax hne
  have hqmax1 : 1 ≤ qmax := by
    have hne' : ¬ (A = ∅ ∧ B = ∅) := by
      rintro ⟨rfl, rfl⟩
      exact hne (by rw [show QA (∅ : Finset ℕ) = 1 from rfl, arcPt_one, arcPt_one])
    rcases Finset.eq_empty_or_nonempty A with hAe | hAne
    · have hBne : B.Nonempty := by
        rcases Finset.eq_empty_or_nonempty B with hBe | h
        · exact absurd ⟨hAe, hBe⟩ hne'
        · exact h
      obtain ⟨q', hq'⟩ := hBne
      exact le_trans (by have := h2 q' (hB hq'); omega) (hmax q' (hB hq'))
    · obtain ⟨q, hq⟩ := hAne
      exact le_trans (by have := h2 q (hA hq); omega) (hmax q (hA hq))
  have hqmax0 : (0 : ℝ) < (qmax : ℝ) := by exact_mod_cast hqmax1
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < (r : ℝ) * (qmax : ℝ) ^ (2 * r * k) := by positivity
  -- Step 1: `2ε/c < 1/(r qmax^{2rk})`, which is exactly the goodness condition
  have hstep1 : 2 * ε / c < 1 / ((r : ℝ) * (qmax : ℝ) ^ (2 * r * k)) := by
    rw [div_lt_div_iff₀ hc hden]
    have h := hgood
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * k))] at h
    nlinarith [h]
  -- Step 2: `1/(r qmax^{2rk}) ≤ 1/qmax^{2k}` since `r ≥ 1`
  have hstep2 : 1 / ((r : ℝ) * (qmax : ℝ) ^ (2 * r * k))
      ≤ 1 / (qmax : ℝ) ^ (2 * k) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : (qmax : ℝ) ^ (2 * k) ≤ (qmax : ℝ) ^ (2 * r * k) :=
      pow_le_pow_right₀ (by exact_mod_cast hqmax1) (by
        have : (2 : ℕ) ≤ 2 * r := by omega
        calc 2 * k ≤ 2 * r * k := Nat.mul_le_mul_right k this
          _ = 2 * r * k := rfl)
    have h2 : (0 : ℝ) ≤ (qmax : ℝ) ^ (2 * r * k) := le_of_lt (by positivity)
    have h3 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith [h1, h2, h3]
  linarith [hstep1, hstep2, hsep]

/-! ## Tao's (sigma-include) -/

/-- **Tao's (sigma-include)** (arXiv:2008.05066, §4): `Σ_{A₀} + Σ_{(A₀)} ⊆ Σ_{≤ k}`. -/
theorem sigmaComp_add_mem_sigmaLe {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) (hk₀ : A₀.card ≤ k) {α₀ α : Circle}
    (h₀ : α₀ ∈ sigmaA A₀) (hα : α ∈ sigmaComp S k A₀) :
    α₀ + α ∈ sigmaLe S k := by
  rw [sigmaComp] at hα
  simp only [Set.mem_iUnion] at hα
  obtain ⟨A₁, hA₁mem, hαA₁⟩ := hα
  rw [Finset.mem_filter, Finset.mem_powerset] at hA₁mem
  obtain ⟨hA₁sub, hA₁card⟩ := hA₁mem
  have hA₁S : A₁ ⊆ S := hA₁sub.trans (Finset.sdiff_subset)
  have hdisj : Disjoint A₀ A₁ := by
    rw [Finset.disjoint_left]
    intro q hq₀ hq₁
    exact (Finset.mem_sdiff.mp (hA₁sub hq₁)).2 hq₀
  have hmem : α₀ + α ∈ sigmaA (A₀ ∪ A₁) :=
    sigmaA_add_mem h2 hS hA₀ hA₁S hdisj h₀ hαA₁
  have hunionS : A₀ ∪ A₁ ⊆ S := Finset.union_subset hA₀ hA₁S
  have hcard : (A₀ ∪ A₁).card ≤ k := by
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  rw [sigmaLe]
  simp only [Set.mem_iUnion]
  exact ⟨A₀ ∪ A₁, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hunionS, hcard⟩,
    sigmaA_subset_sigmaSubA _ hmem⟩

/-! ## The `2^k` counting set of `ortho-apply`(i) -/

/-- The finite set of `A₀ ⊆ S` with `A₀.card ≤ k` for which the point `β` of the circle has a
decomposition `β = α₀ + α` with `α₀ ∈ Σ_{A₀}` (exact denominator `Q_{A₀}`) and
`α ∈ Σ_{(A₀)} = ⋃_{A₁ ⊆ S \ A₀, A₁.card ≤ k - A₀.card} Σ_{A₁}`.

Tao's counting bound (arXiv:2008.05066, proof of Theorem `ortho-apply`(i)) is that this set has at
most `2^k` elements; see `sigmaComp_repr_count`. -/
noncomputable def sigmaCompDecompSet (S : Finset ℕ) (k : ℕ) (β : Circle) : Finset (Finset ℕ) := by
  classical
  exact (S.powerset.filter (fun A₀ => A₀.card ≤ k)).filter
    (fun A₀ => ∃ α ∈ sigmaComp S k A₀, β - α ∈ sigmaA A₀)

end Work.BourgainPlan.IonescuWainger

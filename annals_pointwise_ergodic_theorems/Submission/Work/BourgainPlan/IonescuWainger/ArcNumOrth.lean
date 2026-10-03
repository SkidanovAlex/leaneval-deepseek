import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep

/-!
# (A3)(iii) Numerator orthogonality of the Ionescu–Wainger major arcs: the arithmetic core

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Lemma `ortho`(iii) (§4) and the proof of Theorem `ortho-apply`(i).

Tao's numerator orthogonality says that for a sunflower `A_1, …, A_r` with core `A₀` and pairwise
disjoint petals `P_i = A_i \ A₀`, the functions `∏_{i=1}^r f_{Σ_{A₀} + α_i}`, indexed by tuples
`(α_1, …, α_r) ∈ ∏_i Σ_{P_i}`, are pairwise orthogonal; inspecting Fourier transforms, the point
to be checked is that

`Σ_{j≤r}(α_{0,j} + α_j + θ_j) − Σ_{j>r}(α_{0,j} + α_j + θ_j) ≠ 0`

whenever the two tuples `(α_1,…,α_r) ≠ (α_{r+1},…,α_{2r})` differ.

Multiplying by `Q_{A₀}` kills the `α_{0,j}` (they lie in the torsion subgroup `Σ_{⊆ A₀}`), so the
arithmetic core is the following statement about **pairwise disjoint** index sets `P : ι → Finset ℕ`
(the petals): if `α_i, β_i ∈ Σ_{P_i}` and `α_i ≠ β_i` for at least one `i`, then `Σ_i (α_i − β_i)`
does not vanish in `𝕋`; quantitatively, the sum is at distance at least `1/∏_i Q_{P_i}` from `0`,
and the `ε`-perturbations `θ_i, θ'_i` cannot destroy the non-vanishing under the smallness
condition `2 · #ι · ε < 1/∏_i Q_{P_i}`.

The proof is the same "multiply by the denominators of the other terms" argument as in the nonce
lemma of `ArcSep.lean`: with `i₀` a coordinate where `α_{i₀} ≠ β_{i₀}`, multiplication by
`L = ∏_{j ≠ i₀} Q_{P_j}` kills every term except the `i₀`-th, and `L` is coprime to `Q_{P_{i₀}}`,
so the surviving term `L • (α_{i₀} − β_{i₀})` is a non-zero rational point of denominator
`Q_{P_{i₀}}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Scaling a rational point by a unit of its denominator -/

/-- `N · (a/Q) = (N a)/Q` in the circle. -/
lemma zsmul_arcPt' (N : ℤ) (Q : ℕ) (a : ℤ) : N • arcPt Q a = arcPt Q (N * a) := by
  rw [zsmul_arcPt]
  congr 1
  push_cast
  ring

/-- **A non-zero rational point of exact denominator `Q` stays non-zero after multiplication by an
integer coprime to `Q`.** -/
lemma zsmul_arcPt_ne_zero_of_coprime {N : ℤ} {Q : ℕ} {c : ℤ} (hQ : Q ≠ 0)
    (hcop : Nat.Coprime N.natAbs Q) (h : arcPt Q c ≠ 0) : N • arcPt Q c ≠ 0 := by
  rw [zsmul_arcPt']
  intro h0
  refine h ((arcPt_eq_zero_iff_dvd hQ c).mpr ?_)
  have hdvd : (Q : ℤ) ∣ N * c := (arcPt_eq_zero_iff_dvd hQ (N * c)).mp h0
  have hI : IsCoprime (Q : ℤ) N := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop.symm
  exact hI.dvd_of_dvd_mul_left hdvd

/-- The natural-number form of `zsmul_arcPt_ne_zero_of_coprime`. -/
lemma zsmul_arcPt_ne_zero_of_coprime_nat {N Q : ℕ} {c : ℤ} (hQ : Q ≠ 0)
    (hcop : Nat.Coprime N Q) (h : arcPt Q c ≠ 0) : (N : ℤ) • arcPt Q c ≠ 0 :=
  zsmul_arcPt_ne_zero_of_coprime hQ (by simpa using hcop) h

/-- Subtraction of two points with the same denominator. -/
lemma arcPt_sub_same (Q : ℕ) (a b : ℤ) : arcPt Q a - arcPt Q b = arcPt Q (a - b) := by
  have h : a + -b = a - b := by ring
  rw [sub_eq_add_neg, ← arcPt_neg, arcPt_add, h]

/-- **Two distinct points of the same exact denominator stay distinct after scaling by a unit of
that denominator.** -/
lemma zsmul_arcPt_ne_of_ne {N : ℤ} {Q : ℕ} (hQ : Q ≠ 0) (hcop : Nat.Coprime N.natAbs Q)
    {a b : ℤ} (hab : arcPt Q a ≠ arcPt Q b) : N • arcPt Q a ≠ N • arcPt Q b := by
  intro h0
  rw [zsmul_arcPt', zsmul_arcPt'] at h0
  have h1 : arcPt Q (N * a - N * b) = 0 := by
    rw [← arcPt_sub_same, h0, sub_self]
  have hdvd : (Q : ℤ) ∣ N * a - N * b := (arcPt_eq_zero_iff_dvd hQ _).mp h1
  have hdvd' : (Q : ℤ) ∣ N * (a - b) := by rwa [← mul_sub] at hdvd
  have hI : IsCoprime (Q : ℤ) N := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop.symm
  refine hab (sub_eq_zero.mp ?_)
  rw [arcPt_sub_same, (arcPt_eq_zero_iff_dvd hQ (a - b)).mpr (hI.dvd_of_dvd_mul_left hdvd')]

/-! ## Killing torsion points -/

/-- **A point of `Σ_{⊆ A} = 𝕋[Q_A]` is killed by every multiple of `Q_A`.** -/
lemma zsmul_eq_zero_of_dvd_QA {A : Finset ℕ} (hA : ∀ q ∈ A, q ≠ 0) {N : ℕ}
    (hdvd : QA A ∣ N) {x : Circle} (hx : x ∈ sigmaSubA A) : (N : ℤ) • x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  rw [zsmul_arcPt']
  exact (arcPt_eq_zero_iff_dvd (QA_ne_zero hA) _).mpr
    (dvd_mul_of_dvd_left (by exact_mod_cast hdvd : (QA A : ℤ) ∣ (N : ℤ)) a)

/-! ## The sum of the differences over pairwise disjoint petals -/

/-- **The arithmetic core of Tao's `ortho`(iii).**  Let `S` be a finite set of pairwise coprime
integers `≥ 2`, let `P : ι → Finset ℕ` be *pairwise disjoint* subsets of `S` (the petals of a
sunflower) and let `α i, β i ∈ Σ_{P i}` be points of exact denominators `Q_{P i}`.  If `α` and `β`
differ in at least one coordinate, then

`Σ_i (α i − β i) ≠ 0`   in `𝕋 = ℝ/ℤ`. -/
theorem sigmaA_petal_sum_ne_zero {ι : Type*} [Fintype ι] {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S) (hdisj : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) :
    (∑ i, (α i - β i)) ≠ 0 := by
  classical
  obtain ⟨i₀, hne₀⟩ := hne
  have hQz : ∀ i, QA (P i) ≠ 0 := fun i =>
    QA_ne_zero fun q hq => by have := h2 q (hP i hq); omega
  -- the `Q_{P i}` are pairwise coprime
  have hcopQ : ∀ i j : ι, i ≠ j → Nat.Coprime (QA (P i)) (QA (P j)) := fun i j hij =>
    Nat.Coprime.prod_left fun q hq =>
      Nat.Coprime.prod_right fun q' hq' =>
        hS q (hP i hq) q' (hP j hq')
          (fun he => (Finset.disjoint_left.mp (hdisj i j hij) hq) (he ▸ hq'))
  -- `L = ∏_{j ≠ i₀} Q_{P j}` is coprime to `Q_{P i₀}`
  have hcopL : Nat.Coprime (∏ j ∈ Finset.univ.erase i₀, QA (P j)) (QA (P i₀)) :=
    Nat.Coprime.prod_left fun j hj => hcopQ j i₀ (Finset.mem_erase.mp hj).1
  intro hzero
  have h1 : ((∏ j ∈ Finset.univ.erase i₀, QA (P j) : ℕ) : ℤ) • (∑ i, (α i - β i)) = 0 := by
    rw [hzero, smul_zero]
  rw [Finset.smul_sum] at h1
  have hsingle : (∑ i, ((∏ j ∈ Finset.univ.erase i₀, QA (P j) : ℕ) : ℤ) • (α i - β i))
      = ((∏ j ∈ Finset.univ.erase i₀, QA (P j) : ℕ) : ℤ) • (α i₀ - β i₀) := by
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_)
      (fun h => absurd (Finset.mem_univ i₀) h)
    have hdvd : QA (P i) ∣ ∏ j ∈ Finset.univ.erase i₀, QA (P j) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    have hmem : α i - β i ∈ sigmaSubA (P i) := by
      obtain ⟨c₁, -, hc₁⟩ := hα i
      obtain ⟨c₂, -, hc₂⟩ := hβ i
      exact ⟨c₁ - c₂, by rw [← arcPt_sub_same, ← hc₁, ← hc₂]⟩
    rw [zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hP i hq); omega) hdvd hmem]
  rw [hsingle] at h1
  -- the surviving term is non-zero
  obtain ⟨c₁, -, hc₁⟩ := hα i₀
  obtain ⟨c₂, -, hc₂⟩ := hβ i₀
  have hab : arcPt (QA (P i₀)) c₁ ≠ arcPt (QA (P i₀)) c₂ := by
    intro h
    exact hne₀ (by rw [hc₁, hc₂, h])
  have hne' : ((∏ j ∈ Finset.univ.erase i₀, QA (P j) : ℕ) : ℤ) •
      (arcPt (QA (P i₀)) c₁ - arcPt (QA (P i₀)) c₂) ≠ 0 := by
    rw [arcPt_sub_same]
    refine zsmul_arcPt_ne_zero_of_coprime_nat (hQz i₀) hcopL ?_
    intro h0
    exact hab (sub_eq_zero.mp (by rw [arcPt_sub_same]; exact h0))
  rw [hc₁, hc₂] at h1
  exact hne' h1

/-- **The quantitative form of `sigmaA_petal_sum_ne_zero`**: the sum of the differences is at
distance at least `1/∏_i Q_{P i}` from `0`. -/
theorem sigmaA_petal_sum_norm_ge {ι : Type*} [Fintype ι] {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S) (hdisj : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) :
    1 / ((∏ i, QA (P i) : ℕ) : ℝ) ≤ ‖∑ i, (α i - β i)‖ := by
  classical
  have hpos : ∀ i, 1 ≤ QA (P i) := fun i =>
    Finset.one_le_prod₀ fun q hq => by have := h2 q (hP i hq); omega
  have hαmem := hα
  have hβmem := hβ
  choose a ha using hα
  choose b hb using hβ
  have hsum : (∑ i, (α i - β i))
      = arcPt (∏ i, QA (P i))
          (∑ i, (a i - b i) * (((∏ j, QA (P j)) / QA (P i) : ℕ) : ℤ)) := by
    have h1 : (∑ i, (α i - β i)) = ∑ i, arcPt (QA (P i)) (a i - b i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(ha i).2, (hb i).2, arcPt_sub_same]
    rw [h1]
    have h2' := sum_smul_arcPt_eq_arcPt (Q := fun i => QA (P i)) hpos
      (fun i => a i - b i) (fun _ => (1 : ℤ))
    simpa using h2'
  rw [hsum]
  refine norm_arcPt_ge (Finset.one_le_prod₀ fun i _ => hpos i) ?_
  rw [← hsum]
  exact sigmaA_petal_sum_ne_zero h2 hS hP hdisj hαmem hβmem hne

/-- **The `ε`-perturbed form of `sigmaA_petal_sum_ne_zero`** — the arithmetic verification of Tao's
`ortho`(iii).  Adding the real perturbations `θ_i` to the first group and `θ'_i` to the second
cannot create a vanishing sum, as long as the total perturbation `2 · #ι · ε` is smaller than the
separation `1/∏_i Q_{P i}`. -/
theorem sigmaA_petal_sum_perturbed_ne_zero {ι : Type*} [Fintype ι] {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S) (hdisj : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i)
    {θ θ' : ι → ℝ} {ε : ℝ} (hθ : ∀ i, |θ i| ≤ ε) (hθ' : ∀ i, |θ' i| ≤ ε)
    (hsmall : 2 * (Fintype.card ι : ℝ) * ε < 1 / ((∏ i, QA (P i) : ℕ) : ℝ)) :
    (∑ i, ((α i + (θ i : Circle)) - (β i + (θ' i : Circle)))) ≠ 0 := by
  have hbase : 1 / ((∏ i, QA (P i) : ℕ) : ℝ) ≤ ‖∑ i, (α i - β i)‖ :=
    sigmaA_petal_sum_norm_ge h2 hS hP hdisj hα hβ hne
  have hsplit : (∑ i, ((α i + (θ i : Circle)) - (β i + (θ' i : Circle))))
      = (∑ i, (α i - β i)) + ∑ i, ((θ i : Circle) - (θ' i : Circle)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  have hnorm : ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖ ≤ 2 * (Fintype.card ι : ℝ) * ε := by
    calc ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖
        ≤ ∑ i, ‖(θ i : Circle) - (θ' i : Circle)‖ := norm_sum_le _ _
      _ ≤ ∑ i, (|θ i| + |θ' i|) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc ‖(θ i : Circle) - (θ' i : Circle)‖
                ≤ ‖(θ i : Circle)‖ + ‖(θ' i : Circle)‖ := norm_sub_le _ _
              _ ≤ |θ i| + |θ' i| := add_le_add (norm_circle_coe_le_abs _)
                    (norm_circle_coe_le_abs _)
      _ ≤ ∑ _i : ι, (ε + ε) := Finset.sum_le_sum fun i _ => add_le_add (hθ i) (hθ' i)
      _ = 2 * (Fintype.card ι : ℝ) * ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
  intro hzero
  have hsum0 : (∑ i, (α i - β i)) + ∑ i, ((θ i : Circle) - (θ' i : Circle)) = 0 := by
    rw [← hsplit]; exact hzero
  have hle : ‖(∑ i, (α i - β i))‖
      ≤ ‖(∑ i, (α i - β i)) + ∑ i, ((θ i : Circle) - (θ' i : Circle))‖
        + ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖ := by
    have h := norm_add_le ((∑ i, (α i - β i)) + ∑ i, ((θ i : Circle) - (θ' i : Circle)))
      (-(∑ i, ((θ i : Circle) - (θ' i : Circle))))
    rw [norm_neg] at h
    have h2' : ((∑ i, (α i - β i)) + ∑ i, ((θ i : Circle) - (θ' i : Circle)))
        + -(∑ i, ((θ i : Circle) - (θ' i : Circle))) = ∑ i, (α i - β i) := by abel
    rwa [h2'] at h
  rw [hsum0, norm_zero, zero_add] at hle
  linarith [hbase, hnorm, hle]

/-- **`ortho`(iii) in Tao's `(r,c)`-good parameterisation.**  If the petals `P i` satisfy
`|P i| ≤ k'`, `#ι = r`, all the elements of `S` are bounded by `q_max`, and the goodness condition
`ε < c/(2r q_max^{2rk'})` holds with `0 < c < 1`, then the `ε`-perturbations cannot create a
vanishing signed sum: this is the arithmetic verification of Tao's numerator orthogonality
(arXiv:2008.05066, §4, after multiplying the identity there by `Q_{A₀}`). -/
theorem sigmaA_petal_sum_perturbed_ne_zero_of_good {ι : Type*} [Fintype ι] {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S) (hdisj : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i)
    {θ θ' : ι → ℝ} {ε c : ℝ} {r k' qmax : ℕ} (hcard : Fintype.card ι = r)
    (hPcard : ∀ i, (P i).card ≤ k') (hmax : ∀ q ∈ S, q ≤ qmax) (hc : 0 < c) (hc1 : c < 1)
    (hgood : ε < c / (2 * r * (qmax : ℝ) ^ (2 * r * k')))
    (hθ : ∀ i, |θ i| ≤ ε) (hθ' : ∀ i, |θ' i| ≤ ε) :
    (∑ i, ((α i + (θ i : Circle)) - (β i + (θ' i : Circle)))) ≠ 0 := by
  refine sigmaA_petal_sum_perturbed_ne_zero h2 hS hP hdisj hα hβ hne hθ hθ' ?_
  -- `q_max ≥ 2`, since some petal is non-empty
  obtain ⟨i₀, hne₀⟩ := hne
  have hne_pet : P i₀ ≠ ∅ := by
    intro hPemp
    have h1 : ∀ x ∈ sigmaA (P i₀), x = 0 := by
      rintro x ⟨a, -, rfl⟩
      rw [hPemp] at ⊢
      show arcPt (QA (∅ : Finset ℕ)) a = 0
      rw [show QA (∅ : Finset ℕ) = 1 from rfl, arcPt_one]
    exact hne₀ (by rw [h1 _ (hα i₀), h1 _ (hβ i₀)])
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne_pet
  have hqmax2 : 2 ≤ qmax := le_trans (h2 q₀ (hP i₀ hq₀)) (hmax q₀ (hP i₀ hq₀))
  have hqmax1 : 1 ≤ qmax := by omega
  have hqmax0 : (0 : ℝ) < (qmax : ℝ) := by exact_mod_cast hqmax1
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have : 1 ≤ r := by
      rw [← hcard]
      exact Fintype.card_pos_iff.mpr ⟨i₀⟩
    exact_mod_cast this
  have hrr : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  -- `∏_i Q_{P i} ≤ q_max^{r k'} ≤ q_max^{2 r k'}`
  have hQle : ∀ i, QA (P i) ≤ qmax ^ k' := by
    intro i
    calc QA (P i) = ∏ q ∈ P i, q := rfl
      _ ≤ ∏ _q ∈ P i, qmax := by
            refine Finset.prod_le_prod₀ (fun q _ => Nat.zero_le q) fun q hq => hmax q (hP i hq)
      _ = qmax ^ (P i).card := by rw [Finset.prod_const]
      _ ≤ qmax ^ k' := Nat.pow_le_pow_right hqmax1 (hPcard i)
  have hProd : (∏ i, QA (P i)) ≤ qmax ^ (r * k') := by
    calc (∏ i, QA (P i)) ≤ ∏ _i : ι, qmax ^ k' :=
          Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) fun i _ => hQle i
      _ = (qmax ^ k') ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
      _ = qmax ^ (k' * Fintype.card ι) := by rw [← pow_mul]
      _ = qmax ^ (r * k') := by rw [hcard]; congr 1; ring
  have hQpos : (0 : ℝ) < ((∏ i, QA (P i) : ℕ) : ℝ) := by
    have hp : 0 < ∏ i, QA (P i) := Finset.prod_pos fun i _ => by
      have h1 : 1 ≤ QA (P i) := by
        show 1 ≤ ∏ q ∈ P i, q
        exact Finset.one_le_prod₀ fun q hq => by have := h2 q (hP i hq); omega
      omega
    exact_mod_cast hp
  have hcast : (((qmax ^ (r * k') : ℕ)) : ℝ) = (qmax : ℝ) ^ (r * k') := Nat.cast_pow _ _
  have hQleR : ((∏ i, QA (P i) : ℕ) : ℝ) ≤ (qmax : ℝ) ^ (r * k') := by
    rw [← hcast]; exact_mod_cast hProd
  have hqp : (0 : ℝ) < (qmax : ℝ) ^ (2 * r * k') := by positivity
  -- `2 · #ι · ε = 2r ε < 1/∏_i Q_{P i}`
  have hcardR : ((Fintype.card ι : ℕ) : ℝ) = (r : ℝ) := by rw [hcard]
  have hstep1 : (2 : ℝ) * (r : ℝ) * ε < c / (qmax : ℝ) ^ (2 * r * k') := by
    have h := mul_lt_mul_of_pos_left hgood hrr
    rw [show 2 * (r : ℝ) * (c / (2 * (r : ℝ) * (qmax : ℝ) ^ (2 * r * k')))
        = c / (qmax : ℝ) ^ (2 * r * k') by field_simp] at h
    exact h
  have hstep2 : c / (qmax : ℝ) ^ (2 * r * k') ≤ 1 / (qmax : ℝ) ^ (r * k') := by
    rw [div_le_div_iff₀ hqp (by positivity)]
    have h1 : (1 : ℝ) ≤ (qmax : ℝ) ^ (r * k') := one_le_pow₀ (by exact_mod_cast hqmax1)
    have h2 : (qmax : ℝ) ^ (r * k') ≤ (qmax : ℝ) ^ (2 * r * k') := by
      refine pow_le_pow_right₀ (by exact_mod_cast hqmax1) ?_
      rw [show 2 * r * k' = 2 * (r * k') by ring]
      exact Nat.le_mul_of_pos_left _ (by norm_num)
    nlinarith [h1, h2, hc1.le]
  have hstep3 : 1 / (qmax : ℝ) ^ (r * k') ≤ 1 / ((∏ i, QA (P i) : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hQpos hQleR
  calc 2 * (Fintype.card ι : ℝ) * ε = 2 * (r : ℝ) * ε := by rw [hcardR]
    _ < c / (qmax : ℝ) ^ (2 * r * k') := hstep1
    _ ≤ 1 / (qmax : ℝ) ^ (r * k') := hstep2
    _ ≤ 1 / ((∏ i, QA (P i) : ℕ) : ℝ) := hstep3

end Work.BourgainPlan.IonescuWainger

import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcNumOrth

/-!
# Petal non-vanishing with a core shift and `ε`-perturbations

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Lemma `ortho`(iii) and the proof of Theorem `ortho-apply`(i).

`ArcNumOrth.lean` proves the arithmetic core of Tao's numerator orthogonality for pairwise
disjoint petals `P : ι → Finset ℕ` of a pairwise coprime set `S` of integers `≥ 2`:
if `α i, β i ∈ Σ_{P i}` (points of *exact* denominator `Q_{P i}`) and `α i ≠ β i` for at least one
`i`, then `Σ_i (α i − β i) ≠ 0` in `𝕋 = AddCircle 1`, quantitatively at distance at least
`1/∏_i Q_{P i}` from `0`; and the `ε`-perturbations `θ i, θ' i` cannot destroy the non-vanishing
under the smallness condition `2 · #ι · ε < 1/∏_i Q_{P i}`.

In the actual application (Tao's `ortho-apply`) each term also carries a **core shift**
`γ i − δ i ∈ Σ_{⊆ A₀} = 𝕋[Q_{A₀}]`, where `A₀ ⊆ S` is the core of the sunflower and is disjoint
from every petal.  Those shifts are killed by any multiple of `Q_{A₀}`, so the "multiply by the
denominators of the other terms" argument that proves the petal statement survives verbatim; but
the quantitative separation becomes `1/(Q_{A₀} · ∏_i Q_{P i})`, because the sum now lives in the
larger torsion group `𝕋[Q_{A₀} · ∏_i Q_{P i}]`.  This file provides exactly that statement:

* `sum_arcPt_commonDenom` — a sum of arc points with varying denominators written over a common
  denominator;
* `coprime_QA_of_pairwise` — `Q_A ⟂ Q_B` for disjoint `A, B ⊆ S`;
* `sigmaA_petal_sum_shift_norm_ge` — the quantitative separation;
* **`sigmaA_petal_sum_shift_perturbed_ne_zero`** — the `ε`-perturbed non-vanishing, which is the
  arithmetic verification needed for the `(r,c)`-good multiplier estimates.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Elementary consequences of pairwise coprimality -/

/-- `Q_A ≥ 1` when every element of `A` is at least `2`. -/
lemma one_le_QA {A : Finset ℕ} (hA : ∀ q ∈ A, 2 ≤ q) : 1 ≤ QA A :=
  Finset.one_le_prod₀ fun q hq => by have := hA q hq; omega

/-- **`Q_A` and `Q_B` are coprime for disjoint subsets `A, B` of a pairwise coprime set `S`.** -/
lemma coprime_QA_of_pairwise {S A B : Finset ℕ}
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A B) : Nat.Coprime (QA A) (QA B) :=
  coprime_QA_of_disjoint fun q hq q' hq' =>
    hS q (hA hq) q' (hB hq') (fun he => (Finset.disjoint_left.mp hdisj hq) (he ▸ hq'))

/-- **A sum of arc points with varying denominators, over a common denominator.**  If `R i ∣ L`
for every `i`, then `Σ_i (a_i/R_i) = (Σ_i a_i (L/R_i))/L` in `𝕋`. -/
lemma sum_arcPt_commonDenom {ι : Type*} [Fintype ι] {R : ι → ℕ} {L : ℕ} (hR : ∀ i, 1 ≤ R i)
    (hL : 1 ≤ L) (hdvd : ∀ i, R i ∣ L) (a : ι → ℤ) :
    (∑ i, arcPt (R i) (a i)) = arcPt L (∑ i, a i * (((L / R i : ℕ)) : ℤ)) := by
  rw [Finset.sum_congr rfl (fun i _ => arcPt_commonDenom (hR i) hL (hdvd i) (a i))]
  exact (map_sum (arcPtHom L) (fun i => a i * (((L / R i : ℕ)) : ℤ)) Finset.univ).symm

/-! ## The quantitative separation with a core shift -/

/-- **Quantitative petal separation with a core shift.**  Let `S` be a finite set of pairwise
coprime integers `≥ 2`, let `A₀ ⊆ S` (the core) and let `P : ι → Finset ℕ` be pairwise disjoint
subsets of `S`, each disjoint from `A₀` (the petals).  If `α i, β i ∈ Σ_{P i}` differ in at least
one coordinate and `γ i, δ i ∈ Σ_{⊆ A₀}`, then

`1/(Q_{A₀} · ∏_i Q_{P i}) ≤ ‖Σ_i (γ i + α i) − Σ_i (δ i + β i)‖`

in `𝕋 = AddCircle 1`.

The proof is the same "kill everything else" argument as in `sigmaA_petal_sum_ne_zero`: pick `j`
with `α j ≠ β j` and multiply by `M = Q_{A₀} · ∏_{i ≠ j} Q_{P i}`, which kills every term except
the `j`-th petal difference; that difference lies in `Σ_{P j}` (exact denominator `Q_{P j}`), and
`M` is coprime to `Q_{P j}`, so it survives.  For the quantitative bound we write the whole sum
over the common denominator `Q = Q_{A₀} · ∏_i Q_{P i}` and use that a non-zero point of `𝕋` of
denominator dividing `Q` is at distance at least `1/Q` from `0`. -/
theorem sigmaA_petal_sum_shift_norm_ge {ι : Type*} [Fintype ι] {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i)
    {γ δ : ι → Circle} (hγ : ∀ i, γ i ∈ sigmaSubA A₀) (hδ : ∀ i, δ i ∈ sigmaSubA A₀) :
    1 / ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) ≤
      ‖(∑ i, (γ i + α i)) - (∑ i, (δ i + β i))‖ := by
  classical
  obtain ⟨j, hnej⟩ := hne
  have hA₀2 : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀ hq)
  have hP2 : ∀ i, ∀ q ∈ P i, 2 ≤ q := fun i q hq => h2 q (hP i hq)
  have hQA₀1 : 1 ≤ QA A₀ := one_le_QA hA₀2
  have hQAi1 : ∀ i, 1 ≤ QA (P i) := fun i => one_le_QA (hP2 i)
  set Q : ℕ := QA A₀ * ∏ i, QA (P i) with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_mul hQA₀1 (Finset.one_le_prod₀ fun i _ => hQAi1 i)
  have hdvd₀ : QA A₀ ∣ Q := by rw [hQ]; exact dvd_mul_right _ _
  have hdvdP : ∀ i, QA (P i) ∣ Q := by
    intro i
    rw [hQ]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  -- representations of the four families of arc points
  have hα' : ∀ i, ∃ a : ℤ, Nat.Coprime a.natAbs (QA (P i)) ∧ α i = arcPt (QA (P i)) a :=
    fun i => hα i
  have hβ' : ∀ i, ∃ a : ℤ, Nat.Coprime a.natAbs (QA (P i)) ∧ β i = arcPt (QA (P i)) a :=
    fun i => hβ i
  have hγ' : ∀ i, ∃ z : ℤ, arcPt (QA A₀) z = γ i := fun i => hγ i
  have hδ' : ∀ i, ∃ z : ℤ, arcPt (QA A₀) z = δ i := fun i => hδ i
  choose a _ hαeq using hα'
  choose b _ hβeq using hβ'
  choose c hceq using hγ'
  choose d hdeq using hδ'
  -- the sum, split into the core part and the petal part
  have hsplit : (∑ i, (γ i + α i)) - (∑ i, (δ i + β i))
      = (∑ i, (γ i - δ i)) + (∑ i, (α i - β i)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  have hrep₁ : (∑ i, (γ i - δ i)) = arcPt Q (∑ i, (c i - d i) * (((Q / QA A₀ : ℕ)) : ℤ)) := by
    have h1 : (∑ i, (γ i - δ i)) = ∑ i, arcPt (QA A₀) (c i - d i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hceq i, ← hdeq i, arcPt_sub_same]
    rw [h1]
    exact sum_arcPt_commonDenom (fun _ => hQA₀1) hQ1 (fun _ => hdvd₀) _
  have hrep₂ : (∑ i, (α i - β i)) = arcPt Q (∑ i, (a i - b i) * (((Q / QA (P i) : ℕ)) : ℤ)) := by
    have h1 : (∑ i, (α i - β i)) = ∑ i, arcPt (QA (P i)) (a i - b i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hαeq i, hβeq i, arcPt_sub_same]
    rw [h1]
    exact sum_arcPt_commonDenom hQAi1 hQ1 hdvdP _
  have hrep : (∑ i, (γ i + α i)) - (∑ i, (δ i + β i))
      = arcPt Q ((∑ i, (c i - d i) * (((Q / QA A₀ : ℕ)) : ℤ))
          + (∑ i, (a i - b i) * (((Q / QA (P i) : ℕ)) : ℤ))) := by
    rw [hsplit, hrep₁, hrep₂, arcPt_add]
  -- the sum is non-zero: multiply by the denominators of all terms except the `j`-th petal
  have hWne : (∑ i, (γ i + α i)) - (∑ i, (δ i + β i)) ≠ 0 := by
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = QA A₀ * (∏ i ∈ Finset.univ.erase j, QA (P i)) := ⟨_, rfl⟩
    have hdvdM₀ : QA A₀ ∣ M := by rw [hM]; exact dvd_mul_right _ _
    have hdvdMi : ∀ i, i ≠ j → QA (P i) ∣ M := by
      intro i hij
      rw [hM]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)) _
    have hkill₀ : ∀ {x : Circle}, x ∈ sigmaSubA A₀ → (M : ℤ) • x = 0 := fun hx =>
      zsmul_eq_zero_of_dvd_QA (fun q hq => by have := hA₀2 q hq; omega) hdvdM₀ hx
    have hkillP : ∀ i, i ≠ j → ∀ {x : Circle}, x ∈ sigmaSubA (P i) → (M : ℤ) • x = 0 :=
      fun i hij x hx =>
        zsmul_eq_zero_of_dvd_QA (fun q hq => by have := hP2 i q hq; omega) (hdvdMi i hij) hx
    intro hW
    have h1 : (M : ℤ) • ((∑ i, (γ i + α i)) - (∑ i, (δ i + β i))) = 0 := by rw [hW, smul_zero]
    rw [smul_sub, Finset.smul_sum, Finset.smul_sum] at h1
    have hsumA : (∑ i, (M : ℤ) • (γ i + α i)) = (M : ℤ) • (γ j + α j) := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_)
        (fun hj => absurd (Finset.mem_univ j) hj)
      rw [smul_add, hkill₀ (hγ i),
        hkillP i hij (sigmaA_subset_sigmaSubA (P i) (hα i)), add_zero]
    have hsumB : (∑ i, (M : ℤ) • (δ i + β i)) = (M : ℤ) • (δ j + β j) := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_)
        (fun hj => absurd (Finset.mem_univ j) hj)
      rw [smul_add, hkill₀ (hδ i),
        hkillP i hij (sigmaA_subset_sigmaSubA (P i) (hβ i)), add_zero]
    have h2M : (M : ℤ) • (α j - β j) = 0 := by
      rw [hsumA, hsumB, smul_add, smul_add, hkill₀ (hγ j), hkill₀ (hδ j),
        zero_add, zero_add] at h1
      rwa [← smul_sub] at h1
    have hcopM : Nat.Coprime M (QA (P j)) := by
      rw [hM]
      refine Nat.Coprime.mul_left ?_ ?_
      · exact coprime_QA_of_pairwise (A := A₀) (B := P j) hS hA₀ (hP j) (hdisjA j)
      · exact Nat.Coprime.prod_left fun i hi =>
          coprime_QA_of_pairwise (A := P i) (B := P j) hS (hP i) (hP j)
            (hdisjP i j (Finset.mem_erase.mp hi).1)
    have hnePt : arcPt (QA (P j)) (a j - b j) ≠ 0 := by
      intro h0
      refine hnej ?_
      have h1 : arcPt (QA (P j)) (a j) - arcPt (QA (P j)) (b j) = 0 := by
        rw [arcPt_sub_same]; exact h0
      rw [hαeq j, hβeq j]
      exact sub_eq_zero.mp h1
    have hnonzero : (M : ℤ) • (α j - β j) ≠ 0 := by
      rw [hαeq j, hβeq j, arcPt_sub_same]
      exact zsmul_arcPt_ne_zero_of_coprime_nat (QA_ne_zero_of_two_le (hP2 j)) hcopM hnePt
    exact hnonzero h2M
  -- conclusion: the sum is a non-zero point of denominator dividing `Q`
  rw [hrep]
  refine norm_arcPt_ge hQ1 ?_
  rw [← hrep]
  exact hWne

/-! ## The `ε`-perturbed form -/

/-- **The `ε`-perturbed petal non-vanishing with a core shift** — the arithmetic verification of
Tao's `ortho`(iii) in the presence of the core `Σ_{⊆ A₀}`.  Adding real perturbations `θ i` to the
first group and `θ' i` to the second cannot create a vanishing sum, as long as the total
perturbation `2 · #ι · ε` is smaller than the separation `1/(Q_{A₀} · ∏_i Q_{P i})` supplied by
`sigmaA_petal_sum_shift_norm_ge`. -/
theorem sigmaA_petal_sum_shift_perturbed_ne_zero {ι : Type*} [Fintype ι] {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i)
    {γ δ : ι → Circle} (hγ : ∀ i, γ i ∈ sigmaSubA A₀) (hδ : ∀ i, δ i ∈ sigmaSubA A₀)
    {θ θ' : ι → ℝ} {ε : ℝ} (hθ : ∀ i, |θ i| ≤ ε) (hθ' : ∀ i, |θ' i| ≤ ε)
    (hsmall : 2 * (Fintype.card ι : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    (∑ i, ((γ i + α i + (θ i : Circle)) - (δ i + β i + (θ' i : Circle)))) ≠ 0 := by
  have hQpos : (0 : ℝ) < ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) := by
    have h1 : 1 ≤ QA A₀ * ∏ i, QA (P i) :=
      one_le_mul (one_le_QA fun q hq => h2 q (hA₀ hq))
        (Finset.one_le_prod₀ fun i _ => one_le_QA fun q hq => h2 q (hP i hq))
    exact_mod_cast (by omega : 0 < QA A₀ * ∏ i, QA (P i))
  have hbase : 1 / ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) ≤
      ‖(∑ i, (γ i + α i)) - (∑ i, (δ i + β i))‖ :=
    sigmaA_petal_sum_shift_norm_ge h2 hS hA₀ hP hdisjP hdisjA hα hβ hne hγ hδ
  have hsmall' : 2 * (Fintype.card ι : ℝ) * ε <
      1 / ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hQpos]
    exact hsmall
  have hsplit : (∑ i, ((γ i + α i + (θ i : Circle)) - (δ i + β i + (θ' i : Circle))))
      = ((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
        + ∑ i, ((θ i : Circle) - (θ' i : Circle)) := by
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
  have hsum0 : ((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
      + ∑ i, ((θ i : Circle) - (θ' i : Circle)) = 0 := by
    rw [← hsplit]; exact hzero
  have hle : ‖(∑ i, (γ i + α i)) - (∑ i, (δ i + β i))‖
      ≤ ‖((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
          + ∑ i, ((θ i : Circle) - (θ' i : Circle))‖
        + ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖ := by
    have h := norm_add_le
      (((∑ i, (γ i + α i)) - (∑ i, (δ i + β i))) + ∑ i, ((θ i : Circle) - (θ' i : Circle)))
      (-(∑ i, ((θ i : Circle) - (θ' i : Circle))))
    rw [norm_neg] at h
    have h2' : (((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
        + ∑ i, ((θ i : Circle) - (θ' i : Circle)))
        + -(∑ i, ((θ i : Circle) - (θ' i : Circle))) = (∑ i, (γ i + α i)) - (∑ i, (δ i + β i)) := by
      abel
    rwa [h2'] at h
  rw [hsum0, norm_zero, zero_add] at hle
  linarith [hbase, hnorm, hle, hsmall']

end Work.BourgainPlan.IonescuWainger

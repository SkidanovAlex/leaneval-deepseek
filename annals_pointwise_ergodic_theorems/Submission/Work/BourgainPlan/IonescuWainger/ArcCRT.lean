import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

/-!
# (A0) The arithmetic core of Tao's denominator orthogonality

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Lemma `ortho`(ii) (denominator orthogonality), and the arithmetic paragraph at its end:

> "As the `A_1, …, A_{2r}` contain a nonce, there exists an `A ⊆ S` which contains all but exactly
> one of the `A_1, …, A_{2r}`.  Recalling that `Q_A = ∏_{q ∈ A} q` and that the elements of `S` are
> pairwise coprime, we conclude that `Q_A(α_1 + … + α_r − α_{r+1} − … − α_{2r})` has precisely one
> non-zero term in `𝕋^d`, and hence the point `α_1 + … + α_r − α_{r+1} − … − α_{2r} ∈ 𝕋^d` is
> non-zero."

This file formalises that arithmetic statement, in the 1-dimensional vocabulary of `ArcDefs.lean`
(`Circle = 𝕋`, `QA A = Q_A`, `arcPt Q a = a/Q`, `sigmaA A = Σ_A`):

* `QA_ne_zero`, `dvd_QA_iff`, `QA_dvd_QA_iff`, `coprime_QA` — the divisibility of `Q_A` in a
  pairwise coprime set `S`;
* `zsmul_arcPt`, `zsmul_arcPt_eq_zero`, `zsmul_arcPt_ne_zero` — the effect of multiplying a point
  `a/Q ∈ 𝕋` by an integer `N`: it vanishes exactly when `Q | N` (for `a` coprime to `Q`);
* **`sigmaA_nonce_sum_ne_zero`** — the target: if the family `(A i)` of subsets of `S` has a
  **nonce** (some `q ∈ S` lies in exactly one of the `A i`), then no signed sum `Σ_i ±(a_i/Q_{A i})`
  of points of *exact* denominator `Q_{A i}` vanishes in `𝕋`.

The proof of the last statement is the argument quoted above: with `A₀` the union of all the `A i`
except the one containing the nonce, multiplication by `Q_{A₀}` kills every term except that one,
and the surviving term `±a_j Q_{A₀}/Q_{A_j}` is not an integer because `Q_{A_j}` has the prime power
`q` (with `q ∉ A₀`) that `Q_{A₀}` lacks, while `a_j` is coprime to `Q_{A_j}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Divisibility of `Q_A` -/

/-- `Q_A ≠ 0` when every element of `A` is nonzero. -/
lemma QA_ne_zero {A : Finset ℕ} (hA : ∀ q ∈ A, q ≠ 0) : QA A ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr hA

/-- `Q_A ≠ 0` when every element of `A` is at least `2`. -/
lemma QA_ne_zero_of_two_le {A : Finset ℕ} (hA : ∀ q ∈ A, 2 ≤ q) : QA A ≠ 0 :=
  QA_ne_zero fun q hq => by have := hA q hq; omega

/-- **In a pairwise coprime set `S`, an element `q ∈ S` divides `Q_A` (`A ⊆ S`) exactly when
`q ∈ A`.**  (If `q ∉ A` then `q` is coprime to `Q_A`, so `q ∣ Q_A` forces `q = 1`.) -/
lemma dvd_QA_iff {S A : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) {q : ℕ} (hq : q ∈ S) : q ∣ QA A ↔ q ∈ A := by
  refine ⟨fun h => ?_, fun h => Finset.dvd_prod_of_mem (fun q => q) h⟩
  by_contra hqA
  have hcop : Nat.Coprime q (QA A) :=
    Nat.Coprime.prod_right fun r hr => hS q hq r (hA hr) (fun he => hqA (he ▸ hr))
  have h1 : q ∣ 1 := hcop.dvd_of_dvd_mul_left (by simpa using h)
  have h3 : 2 ≤ q := h2 q hq
  have := Nat.dvd_one.mp h1
  omega

/-- **In a pairwise coprime set, `Q_A ∣ Q_B` exactly when `A ⊆ B`** (for `A, B ⊆ S`). -/
lemma QA_dvd_QA_iff {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) : QA A ∣ QA B ↔ A ⊆ B := by
  refine ⟨fun h q hq => ?_, fun h => Finset.prod_dvd_prod_of_subset A B (fun i => i) h⟩
  by_contra hqB
  have hqdvd : q ∣ QA B :=
    dvd_trans (Finset.dvd_prod_of_mem (fun q => q) hq) h
  exact hqB ((dvd_QA_iff h2 hS hB (hA hq)).mp hqdvd)

/-- An element of `S` outside `A` is coprime to `Q_A`. -/
lemma coprime_QA {S A : Finset ℕ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) {q : ℕ} (hq : q ∈ S) (hqA : q ∉ A) : Nat.Coprime q (QA A) :=
  Nat.Coprime.prod_right fun r hr => hS q hq r (hA hr) (fun he => hqA (he ▸ hr))

/-! ## Multiples of an arc point -/

/-- Multiplying the point `a/Q ∈ 𝕋` by an integer `N`. -/
lemma zsmul_arcPt (N : ℤ) (Q : ℕ) (a : ℤ) :
    N • arcPt Q a = (((N : ℝ) * (a : ℝ) / (Q : ℝ) : ℝ) : Circle) := by
  rw [arcPt, ← AddCircle.coe_zsmul]
  congr 1
  rw [zsmul_eq_mul]
  ring

/-- **`N · (a/Q) = 0` in `𝕋` when `Q ∣ N`.** -/
lemma zsmul_arcPt_eq_zero {N Q : ℕ} {a : ℤ} (hQ : Q ≠ 0) (hdvd : Q ∣ N) :
    (N : ℤ) • arcPt Q a = 0 := by
  rw [zsmul_arcPt, AddCircle.coe_eq_zero_iff]
  refine ⟨(N / Q : ℕ) * a, ?_⟩
  rw [zsmul_one]
  have h1 : (N : ℝ) * (a : ℝ) / (Q : ℝ) = (((N / Q : ℕ) * a : ℤ) : ℝ) := by
    rw [show (((N / Q : ℕ) * a : ℤ) : ℝ) = ((N / Q : ℕ) : ℝ) * (a : ℝ) by
      rw [Int.cast_mul, Int.cast_natCast]]
    rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr hQ)]
    ring
  exact h1.symm

/-- **`N · (a/Q) ≠ 0` in `𝕋` when `Q ∤ N` and `gcd(a, Q) = 1`.** -/
lemma zsmul_arcPt_ne_zero {N Q : ℕ} {a : ℤ} (hQ : Q ≠ 0) (hN : ¬ (Q ∣ N))
    (ha : Nat.Coprime a.natAbs Q) : (N : ℤ) • arcPt Q a ≠ 0 := by
  rw [zsmul_arcPt]
  intro hzero
  rw [AddCircle.coe_eq_zero_iff] at hzero
  obtain ⟨k, hk⟩ := hzero
  rw [zsmul_one] at hk
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have heq : k * (Q : ℤ) = (N : ℤ) * a := by
    have h1 : (k : ℝ) * (Q : ℝ) = (N : ℝ) * (a : ℝ) := by
      rw [hk, div_mul_cancel₀ _ hQr]
      simp only [Int.cast_natCast]
    have h1' : ((k * (Q : ℤ) : ℤ) : ℝ) = (((N : ℤ) * a : ℤ) : ℝ) := by
      simp only [Int.cast_mul, Int.cast_natCast]
      exact h1
    exact Int.cast_injective h1'
  have habs : k.natAbs * Q = N * a.natAbs := by
    have h2 : (k * (Q : ℤ)).natAbs = ((N : ℤ) * a).natAbs := by rw [heq]
    rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h2
  have hdvd : Q ∣ N * a.natAbs := ⟨k.natAbs, by rw [← habs, Nat.mul_comm]⟩
  exact hN (ha.symm.dvd_of_dvd_mul_right hdvd)

/-! ## The nonce lemma -/

/-- **The arithmetic heart of Tao's denominator orthogonality (`ortho`(ii)).**

Let `S` be a finite set of pairwise coprime integers `≥ 2`, let `(A i)_{i ∈ ι}` be finitely many
subsets of `S`, let `sgn i = ±1` and let `a i` be coprime to `Q_{A i}`.  If the family `(A i)` has
a **nonce** — an element `q ∈ S` belonging to exactly one of the `A i` — then the signed sum of the
arc points `a i / Q_{A i}` does not vanish in `𝕋 = Circle`:

`∑_i sgn i • (a i / Q_{A i}) ≠ 0` in `AddCircle 1`.

(For Tao's use, `ι = {1, …, 2r}`, `sgn i = 1` for `i ≤ r` and `-1` otherwise, and `a i / Q_{A i}` is
a point of `Σ_{A i}`, i.e. of *exact* denominator `Q_{A i}`.) -/
theorem sigmaA_nonce_sum_ne_zero {ι : Type*} [Fintype ι]
    {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : ι → Finset ℕ} (hA : ∀ i, A i ⊆ S)
    {sgn : ι → ℤ} (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    {a : ι → ℤ} (ha : ∀ i, Nat.Coprime (a i).natAbs (QA (A i)))
    (hnonce : ∃ j : ι, ∃ q ∈ A j, ∀ i, i ≠ j → q ∉ A i) :
    (∑ i, sgn i • arcPt (QA (A i)) (a i)) ≠ 0 := by
  classical
  obtain ⟨j, q, hqAj, hqout⟩ := hnonce
  have hqS : q ∈ S := hA j hqAj
  set A₀ : Finset ℕ := Finset.univ.biUnion fun i => if i = j then ∅ else A i with hA₀def
  have hA₀sub : A₀ ⊆ S := by
    intro x hx
    rw [hA₀def, Finset.mem_biUnion] at hx
    obtain ⟨i, -, hxi⟩ := hx
    by_cases hi : i = j
    · rw [if_pos hi] at hxi; exact absurd hxi (Finset.notMem_empty x)
    · rw [if_neg hi] at hxi; exact hA i hxi
  have hqA₀ : q ∉ A₀ := by
    intro hx
    rw [hA₀def, Finset.mem_biUnion] at hx
    obtain ⟨i, -, hxi⟩ := hx
    by_cases hi : i = j
    · rw [if_pos hi] at hxi; exact Finset.notMem_empty q hxi
    · rw [if_neg hi] at hxi; exact hqout i hi hxi
  have hQAj_ne : QA (A j) ≠ 0 := QA_ne_zero_of_two_le fun r hr => h2 r (hA j hr)
  have hnotdvd : ¬ (QA (A j) ∣ QA A₀) := fun h =>
    hqA₀ ((dvd_QA_iff h2 hS hA₀sub hqS).mp
      (dvd_trans (Finset.dvd_prod_of_mem (fun q => q) hqAj) h))
  have hkey : (QA A₀ : ℤ) • arcPt (QA (A j)) (a j) ≠ 0 :=
    zsmul_arcPt_ne_zero hQAj_ne hnotdvd (ha j)
  have hAi_sub : ∀ i, i ≠ j → A i ⊆ A₀ := by
    intro i hi x hx
    rw [hA₀def, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, by rw [if_neg hi]; exact hx⟩
  have hother : ∀ i, i ≠ j → (QA A₀ : ℤ) • arcPt (QA (A i)) (a i) = 0 := by
    intro i hi
    refine zsmul_arcPt_eq_zero (Q := QA (A i))
      (QA_ne_zero_of_two_le fun r hr => h2 r (hA i hr)) ?_
    exact Finset.prod_dvd_prod_of_subset (A i) A₀ (fun x => x) (hAi_sub i hi)
  intro hsum
  have hzero : (QA A₀ : ℤ) • (∑ i, sgn i • arcPt (QA (A i)) (a i)) = 0 := by
    rw [hsum, smul_zero]
  rw [Finset.smul_sum] at hzero
  have hsingle : (∑ i, (QA A₀ : ℤ) • (sgn i • arcPt (QA (A i)) (a i)))
      = (QA A₀ : ℤ) • (sgn j • arcPt (QA (A j)) (a j)) := by
    refine Finset.sum_eq_single j (fun i _ hi => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
    rw [smul_comm, hother i hi, smul_zero]
  rw [hsingle, smul_comm] at hzero
  rcases hsgn j with h1 | h1
  · exact hkey (by simpa [h1] using hzero)
  · have hneg : -(↑(QA A₀) • arcPt (QA (A j)) (a j)) = 0 := by simpa [h1] using hzero
    exact hkey (neg_eq_zero.mp hneg)

/-! ## The subgroups `Σ_{⊆ A}` and the non-vanishing of `Σ_A` -/

/-- `Σ_A ⊆ Σ_{⊆ A}`. -/
lemma sigmaA_subset_sigmaSubA (A : Finset ℕ) : sigmaA A ⊆ sigmaSubA A := by
  rintro x ⟨a, -, rfl⟩
  exact ⟨a, rfl⟩

/-- **`Σ_{⊆ A} = 𝕋[Q_A]` is `Q_A`-torsion**: every point of `Σ_{⊆ A}` is killed by `Q_A`. -/
lemma sigmaSubA_zsmul_eq_zero {A : Finset ℕ} (hA : ∀ q ∈ A, 2 ≤ q) {x : Circle}
    (hx : x ∈ sigmaSubA A) : (QA A : ℤ) • x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  exact zsmul_arcPt_eq_zero (QA_ne_zero_of_two_le hA) dvd_rfl

/-- **The primitive point of `Σ_A`**: `1/Q_A` has exact denominator `Q_A`, so `Σ_A` is nonempty
(this is Tao's "the primitive points of `Σ_{⊆ A}` lie in `Σ_A`"). -/
lemma sigmaA_nonempty (A : Finset ℕ) : (sigmaA A).Nonempty :=
  ⟨arcPt (QA A) 1, ⟨1, Nat.coprime_one_left (QA A), rfl⟩⟩

/-! ## Disjointness of the exact-denominator sets `Σ_A` -/

/-- The converse of `zsmul_arcPt_ne_zero`: if `N • (a/Q) = 0` with `gcd(a,Q) = 1` then `Q ∣ N`. -/
lemma dvd_of_zsmul_arcPt_eq_zero {N Q : ℕ} {a : ℤ} (hQ : Q ≠ 0)
    (ha : Nat.Coprime a.natAbs Q) (h : (N : ℤ) • arcPt Q a = 0) : Q ∣ N := by
  by_contra hN
  exact zsmul_arcPt_ne_zero hQ hN ha h

/-- `Q_{A ∪ B} = Q_A · Q_B` for disjoint `A, B`. -/
lemma QA_union {A B : Finset ℕ} (h : Disjoint A B) : QA (A ∪ B) = QA A * QA B :=
  Finset.prod_union h

/-- **The sets `Σ_A` of points of *exact* denominator `Q_A` are pairwise disjoint** (for distinct
subsets `A` of a pairwise coprime set `S` with elements `≥ 2`).  Indeed `a/Q_A` has additive order
exactly `Q_A`, and `Q_A = Q_B` forces `A = B`.  This is the fact behind Tao's "each `β ∈ Σ_{≤ k}`
has at most `2^k` representations". -/
lemma sigmaA_disjoint {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hAB : A ≠ B) : Disjoint (sigmaA A) (sigmaA B) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hxb⟩
  have hQAsub : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA hq)
  have hQBsub : QA B ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hB hq)
  -- `(Q_B) • (a/Q_A) = 0`, so `Q_A ∣ Q_B`
  have hB0 : (QA B : ℤ) • arcPt (QA A) a = 0 := by
    rw [hxb]
    exact zsmul_arcPt_eq_zero hQBsub dvd_rfl
  have hdvd₁ : QA A ∣ QA B := dvd_of_zsmul_arcPt_eq_zero hQAsub ha hB0
  -- `(Q_A) • (b/Q_B) = 0`, so `Q_B ∣ Q_A`
  have hA0 : (QA A : ℤ) • arcPt (QA B) b = 0 := by
    rw [← hxb]
    exact zsmul_arcPt_eq_zero hQAsub dvd_rfl
  have hdvd₂ : QA B ∣ QA A := dvd_of_zsmul_arcPt_eq_zero hQBsub hb hA0
  have hAB' : A = B := Finset.Subset.antisymm
    ((QA_dvd_QA_iff h2 hS hA hB).mp hdvd₁) ((QA_dvd_QA_iff h2 hS hB hA).mp hdvd₂)
  exact hAB hAB'

/-- **`Q_A` determines `A`**: for `A, B ⊆ S`, `Q_A = Q_B` forces `A = B`. -/
lemma QA_injective {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (h : QA A = QA B) : A = B :=
  Finset.Subset.antisymm
    ((QA_dvd_QA_iff h2 hS hA hB).mp (by rw [← h]))
    ((QA_dvd_QA_iff h2 hS hB hA).mp (by rw [h]))

/-- **The subgroups `Σ_{⊆ A}` and `Σ_{⊆ B}` intersect trivially when `Q_A` and `Q_B` are
coprime** (e.g. for disjoint `A, B ⊆ S`): a point of `𝕋` killed by both `Q_A` and `Q_B` is `0`.
(Bezout: `1 = u Q_A + v Q_B`, so `x = 1 • x = u • (Q_A • x) + v • (Q_B • x) = 0`.) -/
lemma eq_zero_of_mem_sigmaSubA_inter {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hcop : Nat.Coprime (QA A) (QA B))
    {x : Circle} (hx : x ∈ sigmaSubA A) (hy : x ∈ sigmaSubA B) : x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, hxb⟩ := hy
  have hAne : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hAS hq)
  have hBne : QA B ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hBS hq)
  have hA0 : (QA A : ℤ) • arcPt (QA A) a = 0 := zsmul_arcPt_eq_zero hAne dvd_rfl
  have hB0 : (QA B : ℤ) • arcPt (QA A) a = 0 := by
    rw [← hxb]
    exact zsmul_arcPt_eq_zero hBne dvd_rfl
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  calc arcPt (QA A) a = (1 : ℤ) • arcPt (QA A) a := (one_zsmul _).symm
    _ = (u * (QA A : ℤ) + v * (QA B : ℤ)) • arcPt (QA A) a := by rw [← huv]
    _ = u • ((QA A : ℤ) • arcPt (QA A) a) + v • ((QA B : ℤ) • arcPt (QA A) a) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by rw [hA0, hB0, smul_zero, smul_zero, add_zero]

end Work.BourgainPlan.IonescuWainger

import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs

/-!
# Denominator orthogonality for Tao's *strata* `Σ_A` in `ZMod Q_S`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Lemma `ortho`(ii); see `ZModArcs.lean` for the dictionary between the arc points `a/Q_A ∈ 𝕋` and the
elements of `ZMod Q_S`, and `sigmaAQ_sum_ne_zero.lean` for the exact-denominator case.

The sets `sigmaAQ Q A` (points of *exact* denominator `Q_A`) do not cover the torsion subgroup
`Σ_{⊆ A} = 𝕋[Q_A]` when the elements of `S` are composite: e.g. `S = {4}`, `A = {4}` gives
`Σ_{⊆ A} = {1/4, 1/2, 3/4}` while `Σ_A = {1/4, 3/4}`.  Tao's *stratum* `Σ_A` of `sigmaStrataQ Q A`
is the correct notion: the points of `𝕋[Q_A]` that do not lie in any strictly smaller subgroup
`𝕋[Q_B]`, `B ⊊ A`, i.e. (after lifting to `ZMod Q_S`) the elements whose additive order divides
`Q_A` but does not divide any `Q_B`, `B ⊊ A`.

This file proves that the denominator orthogonality of the nonce argument survives for these larger
strata.  The key observation is the *annihilator* description of the torsion subgroup

`sigmaSubAQ Q A = {x : ZMod Q | (QA A) • x = 0}`   (for `QA A ∣ Q`),

so that a stratum point `x ∈ sigmaStrataQ Q A` is an element of `ZMod Q` whose order divides `QA A`
but no `QA B` with `B ⊊ A`.  The arithmetic of the nonce then works exactly as for `sigmaAQ`:
multiplying the signed sum by `Q_{A₀}` (`A₀` = union of all the `A j`, `j ≠ j₀`, where `j₀` carries
the nonce `q`) kills every term but the `j₀`-th one, so `(Q_{A₀}) • α(j₀) = 0`; combined with
`(Q_{A j₀}) • α(j₀) = 0` this shows the order of `α(j₀)` divides
`gcd(Q_{A₀}, Q_{A j₀}) = Q_{A j₀ ∩ A₀}`, contradicting the stratum condition because
`q ∈ A j₀ \ A₀` makes `A j₀ ∩ A₀` a *proper* subset of `A j₀`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.BourgainPlan.IonescuWainger

variable {Q : ℕ}

/-! ## The torsion subgroup `Σ_{⊆ A}` as an annihilator -/

section Annihilator

variable [NeZero Q]

/-- **A point of `Σ_{⊆ A} = 𝕋[Q_A]` is killed by `Q_A`** (in the finite group `ZMod Q`, for
`Q_A ∣ Q`): `(QA A) • x = 0`. -/
lemma nsmul_QA_eq_zero_of_mem_sigmaSubAQ {A : Finset ℕ} (hQA : QA A ∣ Q)
    {x : ZMod Q} (hx : x ∈ sigmaSubAQ Q A) : (QA A) • x = 0 := by
  rw [sigmaSubAQ, Finset.mem_image] at hx
  obtain ⟨a, -, rfl⟩ := hx
  rw [arcLift, nsmul_eq_mul]
  rw [show ((a : ℤ) : ZMod Q) = (a : ZMod Q) from Int.cast_natCast a,
    show (((Q / QA A : ℕ) : ℤ) : ZMod Q) = ((Q / QA A : ℕ) : ZMod Q) from
      Int.cast_natCast (Q / QA A)]
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  have hkey : QA A * (a * (Q / QA A)) = a * Q := by
    calc QA A * (a * (Q / QA A)) = a * (QA A * (Q / QA A)) := by ring
      _ = a * Q := by rw [Nat.mul_div_cancel' hQA]
  rw [hkey, Nat.cast_mul, ZMod.natCast_self, mul_zero]

/-- **The converse**: an element of `ZMod Q` killed by `Q_A` (`Q_A ∣ Q`) lies in `Σ_{⊆ A}`. -/
lemma mem_sigmaSubAQ_of_nsmul_eq_zero {A : Finset ℕ} (hQA : QA A ∣ Q)
    {x : ZMod Q} (hx : (QA A) • x = 0) : x ∈ sigmaSubAQ Q A := by
  have hQAne : QA A ≠ 0 := fun h => NeZero.ne Q (zero_dvd_iff.mp (h ▸ hQA))
  have hQApos : 0 < QA A := Nat.pos_of_ne_zero hQAne
  have hQAdivpos : 0 < Q / QA A := Nat.pos_of_ne_zero (fun h => by
    have h2 := Nat.mul_div_cancel' hQA
    rw [h, mul_zero] at h2
    exact NeZero.ne Q h2.symm)
  have hval : ((QA A * x.val : ℕ) : ZMod Q) = 0 := by
    have h := hx
    rw [nsmul_eq_mul] at h
    rw [← ZMod.natCast_zmod_val x] at h
    rwa [← Nat.cast_mul] at h
  have hdvd : Q ∣ QA A * x.val := by
    have h2 : ((Q : ℤ) ∣ ((QA A * x.val : ℕ) : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((QA A * x.val : ℕ) : ℤ) Q).mp (by
        rw [Int.cast_natCast]; exact hval)
    exact_mod_cast h2
  have hmul : (Q / QA A) ∣ x.val := by
    have hdvd' : QA A * (Q / QA A) ∣ QA A * x.val := by
      rw [Nat.mul_div_cancel' hQA]; exact hdvd
    exact (Nat.mul_dvd_mul_iff_left hQApos).mp hdvd'
  obtain ⟨a, ha⟩ := hmul
  rw [sigmaSubAQ, Finset.mem_image]
  refine ⟨a, Finset.mem_range.mpr ?_, ?_⟩
  · have hlt := ZMod.val_lt x
    rw [ha] at hlt
    have hlt' : Q / QA A * a < Q / QA A * QA A := by
      calc Q / QA A * a < Q := hlt
        _ = QA A * (Q / QA A) := (Nat.mul_div_cancel' hQA).symm
        _ = Q / QA A * QA A := Nat.mul_comm _ _
    exact (Nat.mul_lt_mul_left hQAdivpos).mp hlt'
  · rw [arcLift, ← ZMod.natCast_zmod_val x, ha, Int.cast_natCast, Int.cast_natCast,
        ← Nat.cast_mul, Nat.mul_comm]

/-- **The annihilator description of `Σ_{⊆ A}`** in the finite group `ZMod Q` (for `Q_A ∣ Q`). -/
lemma mem_sigmaSubAQ_iff {A : Finset ℕ} (hQA : QA A ∣ Q) (x : ZMod Q) :
    x ∈ sigmaSubAQ Q A ↔ (QA A) • x = 0 :=
  ⟨nsmul_QA_eq_zero_of_mem_sigmaSubAQ hQA, mem_sigmaSubAQ_of_nsmul_eq_zero hQA⟩

end Annihilator

/-! ## The gcd of two `Q`-products -/

/-- **`gcd (Q_A) (Q_B) = Q_{A ∩ B}`** for two *cross-coprime* index sets: if distinct elements
`p ∈ A`, `q ∈ B` are coprime, then `Q_A` and `Q_B` have exactly the common factor `Q_{A ∩ B}`.
Proof: `A = (A ∩ B) ⊔ (A \ B)` and `B = (A ∩ B) ⊔ (B \ A)` with `Q_{A\B}` coprime to `Q_{B\A}`. -/
lemma gcd_QA_inter_of_coprime {A B : Finset ℕ}
    (hcop : ∀ p ∈ A, ∀ q ∈ B, p ≠ q → Nat.Coprime p q) :
    Nat.gcd (QA A) (QA B) = QA (A ∩ B) := by
  have hAC : A = (A ∩ B) ∪ (A \ B) := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hBC : B = (A ∩ B) ∪ (B \ A) := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hdisj1 : Disjoint (A ∩ B) (A \ B) := by
    rw [Finset.disjoint_left]; intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).2
  have hdisj2 : Disjoint (A ∩ B) (B \ A) := by
    rw [Finset.disjoint_left]; intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).1
  have hqA : QA A = QA (A ∩ B) * QA (A \ B) := by
    conv_lhs => rw [hAC]
    rw [QA_union hdisj1]
  have hqB : QA B = QA (A ∩ B) * QA (B \ A) := by
    conv_lhs => rw [hBC]
    rw [QA_union hdisj2]
  have hcp : Nat.Coprime (QA (A \ B)) (QA (B \ A)) := by
    rw [QA, QA]
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    obtain ⟨hpA, hpB⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hqB, _⟩ := Finset.mem_sdiff.mp hq
    exact hcop p hpA q hqB (fun h => hpB (h ▸ hqB))
  rw [hqA, hqB, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcp, mul_one]

/-! ## The main theorem -/

/-- **Denominator orthogonality of the strata `Σ_A` in `ZMod Q_S`** (the arithmetic heart of Tao's
Lemma `ortho`(ii) for the strata of `sigmaStrataQ`).

Let `S` be a finite set of pairwise coprime integers `≥ 2`, let `A : Fin r ⊕ Fin r → Finset ℕ` be a
family of subsets of `S` carrying a **nonce**, and let `α j ∈ sigmaStrataQ (QA S) (A j)`.  Then the
signed sum `Σ_{i<r} α_{inl i} − Σ_{i<r} α_{inr i}` is never `0` in `ZMod (QA S)`. -/
theorem sigmaStrataQ_sum_ne_zero {r : ℕ} {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin r ⊕ Fin r → Finset ℕ} (hA : ∀ j, A j ⊆ S)
    (hnonce : HasNonce A)
    (α : Fin r ⊕ Fin r → ZMod (QA S))
    (hα : ∀ j, α j ∈ sigmaStrataQ (QA S) (A j)) :
    (∑ i : Fin r, α (Sum.inl i)) - (∑ i : Fin r, α (Sum.inr i)) ≠ 0 := by
  classical
  obtain ⟨q₀, j₀, hq₀j₀, huniq⟩ := hnonce
  let sgn : Fin r ⊕ Fin r → ℤ := Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))
  have hsgn : ∀ j, sgn j = 1 ∨ sgn j = -1 := by rintro (i | i) <;> simp [sgn]
  set A₀ : Finset ℕ := Finset.univ.biUnion (fun j : Fin r ⊕ Fin r => if j = j₀ then ∅ else A j)
    with hA₀def
  have hA₀sub : A₀ ⊆ S := by
    intro x hx
    rw [hA₀def, Finset.mem_biUnion] at hx
    obtain ⟨j, -, hxj⟩ := hx
    by_cases hj : j = j₀
    · rw [if_pos hj] at hxj; exact absurd hxj (Finset.notMem_empty x)
    · rw [if_neg hj] at hxj; exact hA j hxj
  have hq₀A₀ : q₀ ∉ A₀ := by
    intro hx
    rw [hA₀def, Finset.mem_biUnion] at hx
    obtain ⟨j, -, hxj⟩ := hx
    by_cases hj : j = j₀
    · rw [if_pos hj] at hxj; exact Finset.notMem_empty q₀ hxj
    · rw [if_neg hj] at hxj; exact absurd (huniq j hxj) hj
  have hAjsub : ∀ j, j ≠ j₀ → A j ⊆ A₀ := by
    intro j hj x hx
    rw [hA₀def, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ j, by rw [if_neg hj]; exact hx⟩
  have hsub : ∀ j, α j ∈ sigmaSubAQ (QA S) (A j) := fun j => (Finset.mem_filter.mp (hα j)).1
  have hkill : ∀ j, (QA (A j)) • α j = 0 := fun j =>
    nsmul_QA_eq_zero_of_mem_sigmaSubAQ (Q := QA S)
      (Finset.prod_dvd_prod_of_subset (A j) S (fun i => i) (hA j)) (hsub j)
  have hother : ∀ j, j ≠ j₀ → (QA A₀) • (sgn j • α j) = 0 := by
    intro j hj
    obtain ⟨m, hm⟩ := Finset.prod_dvd_prod_of_subset (A j) A₀ (fun i => i) (hAjsub j hj)
    have hm' : QA A₀ = QA (A j) * m := hm
    rw [hm', mul_nsmul, smul_comm (QA (A j)) (sgn j), hkill j, smul_zero, smul_zero]
  intro hsum
  have hsum1 : (∑ j : Fin r ⊕ Fin r, sgn j • α j) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [sgn, Sum.elim_inl, Sum.elim_inr, one_smul, neg_one_smul, Finset.sum_neg_distrib]
    rw [sub_eq_add_neg] at hsum
    exact hsum
  have hkey : (QA A₀) • α j₀ = 0 := by
    have h0 : (QA A₀) • (∑ j : Fin r ⊕ Fin r, sgn j • α j) = 0 := by
      rw [hsum1, smul_zero]
    rw [Finset.smul_sum] at h0
    have hsingle : (∑ j : Fin r ⊕ Fin r, (QA A₀) • (sgn j • α j))
        = (QA A₀) • (sgn j₀ • α j₀) :=
      Finset.sum_eq_single j₀ (fun j _ hj => hother j hj)
        (fun h => absurd (Finset.mem_univ j₀) h)
    rw [hsingle] at h0
    rcases hsgn j₀ with h | h
    · rw [h, one_smul] at h0; exact h0
    · rw [h, smul_comm, neg_one_smul] at h0; exact neg_eq_zero.mp h0
  have hBmem : α j₀ ∈ sigmaSubAQ (QA S) (A j₀ ∩ A₀) := by
    have hd1 : addOrderOf (α j₀) ∣ QA (A j₀) :=
      (addOrderOf_dvd_iff_nsmul_eq_zero).mpr (hkill j₀)
    have hd2 : addOrderOf (α j₀) ∣ QA A₀ :=
      (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hkey
    have hgcd : Nat.gcd (QA (A j₀)) (QA A₀) = QA (A j₀ ∩ A₀) :=
      gcd_QA_inter_of_coprime (fun p hp q hq hpq => hS p (hA j₀ hp) q (hA₀sub hq) hpq)
    have hd : addOrderOf (α j₀) ∣ QA (A j₀ ∩ A₀) := by
      rw [← hgcd]; exact Nat.dvd_gcd hd1 hd2
    exact mem_sigmaSubAQ_of_nsmul_eq_zero (Q := QA S)
      (Finset.prod_dvd_prod_of_subset (A j₀ ∩ A₀) S (fun i => i)
        (Finset.inter_subset_left.trans (hA j₀)))
      ((addOrderOf_dvd_iff_nsmul_eq_zero).mp hd)
  have hstrat := (Finset.mem_filter.mp (hα j₀)).2
  exact hstrat (A j₀ ∩ A₀)
    (by
      rw [Finset.mem_erase, Finset.mem_powerset]
      exact ⟨fun h => hq₀A₀ (Finset.mem_inter.mp (h ▸ hq₀j₀)).2, Finset.inter_subset_left⟩)
    hBmem

end Work.BourgainPlan.IonescuWainger

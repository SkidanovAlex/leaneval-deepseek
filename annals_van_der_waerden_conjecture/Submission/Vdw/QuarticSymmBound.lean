import Mathlib
import Submission.Vdw.QuarticResolventCount
import Submission.Vdw.QuarticImprimitive
import Submission.Commons.NumberTheory.Int.ncard_sq_close_le
import Submission.Commons.NumberTheory.Int.ncard_two_mul_residue_le
import Submission.Commons.NumberTheory.Nat.radical_dvd_of_dvd_pow
import Submission.Commons.NumberTheory.Nat.sum_inv_radical_le_sqrt
import Submission.Commons.Analysis.Sum.sum_Icc_symm
import Submission.Commons.NumberTheory.Int.ncard_sq_le_sqrt
import Submission.Commons.NumberTheory.Int.ncard_sq_close_le_abs
import Submission.Commons.NumberTheory.Nat.sum_recip_sqrt_mul_radical_le
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow

open Polynomial Filter Asymptotics
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Bounding `#symmBox H` by `O(H^3)` — the `n = 4` imprimitive count

`QuarticResolventCount` reduced `#ImprimitiveBad 4 H` to `#resBox H ≤ #symmBox H`, where
`symmBox H` is the set of `(x,a,c,d,e)` with `|x| ≤ 4H`, `|a|,|c|,|d| ≤ H`, `|e| ≤ 5H` and
the *symmetry equation* `(x² - 4d)(a² - 4e) = (xa - 2c)²`.

This module proves `#symmBox H = O(H^3)`, by splitting off the **diagonal** `xa = 2c`
(where the equation factors) and counting the **off-diagonal** through the radical of the
integer `A = x² - 4d`:

* diagonal: `xa = 2c` forces `x² = 4d` or `a² = 4e`, so one variable is determined and the
  number of remaining `(x,a,c,e)` or `(x,a,c,d)` is `≤ 300 (H+1)^3`;
* off-diagonal: `A = x² - 4d ≠ 0` and `A ∣ (xa-2c)²`, so `rad A ∣ xa - 2c`; for each
  `(x,d)` the admissible `c` lie in one residue class mod `rad A` (at most `4H/rad A + 1`
  of them), and `a` is free (`2H+1` values).  The key arithmetic input is
  `∑_{A ≤ N} 1/rad A ≪ √N` (and the companion `∑ 1/(√A rad A) = O(1)`), which makes the
  total sum `∑_{x,d} 4H/rad(x²-4d)` of size `O(H)`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## The diagonal / off-diagonal split -/

/-- The **diagonal part** of `symmBox`: `x * a = 2 * c`. -/
def symmDiag (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | t ∈ symmBox H ∧ t.1 * t.2.1 = 2 * t.2.2.1}

/-- The **off-diagonal part** of `symmBox`: `x * a ≠ 2 * c`. -/
def symmOff (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | t ∈ symmBox H ∧ t.1 * t.2.1 ≠ 2 * t.2.2.1}

theorem symmBox_subset_diag_union_off (H : ℕ) :
    symmBox H ⊆ symmDiag H ∪ symmOff H := by
  intro t ht
  by_cases h : t.1 * t.2.1 = 2 * t.2.2.1
  · exact Or.inl ⟨ht, h⟩
  · exact Or.inr ⟨ht, h⟩

/-- The diagonal part splits into `x² = 4d` and `a² = 4e`. -/
theorem symmDiag_eq_union (H : ℕ) :
    symmDiag H ⊆
      {t | t ∈ symmDiag H ∧ t.1 ^ 2 = 4 * t.2.2.2.1} ∪
      {t | t ∈ symmDiag H ∧ t.1 ^ 2 ≠ 4 * t.2.2.2.1} := by
  intro t ht
  by_cases h : t.1 ^ 2 = 4 * t.2.2.2.1
  · exact Or.inl ⟨ht, h⟩
  · exact Or.inr ⟨ht, h⟩

/-- **On the diagonal, `x² ≠ 4d` forces `a² = 4e`** (the symmetry equation factors). -/
theorem symmDiag_sq_a (H : ℕ) {t : ℤ × ℤ × ℤ × ℤ × ℤ} (ht : t ∈ symmDiag H)
    (h : t.1 ^ 2 ≠ 4 * t.2.2.2.1) : t.2.1 ^ 2 = 4 * t.2.2.2.2 := by
  obtain ⟨htb, hdiag⟩ := ht
  have hs := htb.2.2.2.2.2
  have h0 : (t.1 ^ 2 - 4 * t.2.2.2.1) * (t.2.1 ^ 2 - 4 * t.2.2.2.2) = 0 := by
    have h2 : (t.1 * t.2.1 - 2 * t.2.2.1) = 0 := by
      have : t.1 * t.2.1 - 2 * t.2.2.1 = 0 := by rw [hdiag]; ring
      exact this
    rw [show (t.1 ^ 2 - 4 * t.2.2.2.1) * (t.2.1 ^ 2 - 4 * t.2.2.2.2)
        = (t.1 * t.2.1 - 2 * t.2.2.1) ^ 2 from hs]
    rw [h2]; ring
  rcases mul_eq_zero.mp h0 with h1 | h2
  · exact absurd (by linarith : t.1 ^ 2 = 4 * t.2.2.2.1) h
  · linarith

/-! ## The diagonal bound -/

/-- The diagonal part with `x² = 4d`. -/
def symmDiagA (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | t ∈ symmDiag H ∧ t.1 ^ 2 = 4 * t.2.2.2.1}

/-- The diagonal part with `x² ≠ 4d` (hence `a² = 4e`). -/
def symmDiagB (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | t ∈ symmDiag H ∧ t.1 ^ 2 ≠ 4 * t.2.2.2.1}

theorem symmDiag_subset_union (H : ℕ) : symmDiag H ⊆ symmDiagA H ∪ symmDiagB H := by
  intro t ht
  by_cases h : t.1 ^ 2 = 4 * t.2.2.2.1
  · exact Or.inl ⟨ht, h⟩
  · exact Or.inr ⟨ht, h⟩

/-- A crude bound for the cardinality of a box of bounded integers. -/
theorem ncard_box3_le (A B C : ℕ) :
    (({p : ℤ × ℤ × ℤ | |p.1| ≤ (A : ℤ) ∧ |p.2.1| ≤ (B : ℤ) ∧ |p.2.2| ≤ (C : ℤ)} :
      Set (ℤ × ℤ × ℤ))).ncard ≤ (2 * A + 1) * ((2 * B + 1) * (2 * C + 1)) := by
  have hsub : ({p : ℤ × ℤ × ℤ | |p.1| ≤ (A : ℤ) ∧ |p.2.1| ≤ (B : ℤ) ∧ |p.2.2| ≤ (C : ℤ)} :
      Set (ℤ × ℤ × ℤ)) ⊆
      ↑(Finset.Icc (-(A : ℤ)) (A : ℤ) ×ˢ
        (Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ Finset.Icc (-(C : ℤ)) (C : ℤ))) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
      Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩,
      ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩, ⟨(abs_le.mp h3).1, (abs_le.mp h3).2⟩⟩
  refine le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _)) ?_
  rw [Set.ncard_coe_finset, Finset.card_product, Finset.card_product, Int.card_Icc, Int.card_Icc,
    Int.card_Icc]
  have h1 : (((A : ℤ) + 1 - (-(A : ℤ))).toNat) = 2 * A + 1 := by
    rw [show (A : ℤ) + 1 - (-(A : ℤ)) = ((2 * A + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  have h2 : (((B : ℤ) + 1 - (-(B : ℤ))).toNat) = 2 * B + 1 := by
    rw [show (B : ℤ) + 1 - (-(B : ℤ)) = ((2 * B + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  have h3 : (((C : ℤ) + 1 - (-(C : ℤ))).toNat) = 2 * C + 1 := by
    rw [show (C : ℤ) + 1 - (-(C : ℤ)) = ((2 * C + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h1, h2, h3]

/-- The box describing the image of `symmDiagA` under `(x,a,c,d,e) ↦ (x,a,e)`. -/
def diagABox (H : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | |p.1| ≤ ((4 * H : ℕ) : ℤ) ∧ |p.2.1| ≤ (H : ℤ) ∧ |p.2.2| ≤ ((5 * H : ℕ) : ℤ)}

/-- The box describing the image of `symmDiagB` under `(x,a,c,d,e) ↦ (x,a,d)`. -/
def diagBBox (H : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | |p.1| ≤ ((4 * H : ℕ) : ℤ) ∧ |p.2.1| ≤ (H : ℤ) ∧ |p.2.2| ≤ (H : ℤ)}

theorem diagABox_ncard_le (H : ℕ) : (diagABox H).ncard ≤ 300 * (H + 1) ^ 3 := by
  refine le_trans (ncard_box3_le (4 * H) H (5 * H)) ?_
  have h1 : 2 * (4 * H) + 1 ≤ 9 * (H + 1) := by omega
  have h2 : 2 * H + 1 ≤ 3 * (H + 1) := by omega
  have h3 : 2 * (5 * H) + 1 ≤ 11 * (H + 1) := by omega
  calc (2 * (4 * H) + 1) * ((2 * H + 1) * (2 * (5 * H) + 1))
      ≤ (9 * (H + 1)) * ((3 * (H + 1)) * (11 * (H + 1))) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    _ = 297 * (H + 1) ^ 3 := by ring
    _ ≤ 300 * (H + 1) ^ 3 := by nlinarith [Nat.zero_le ((H+1)^3)]

theorem diagBBox_ncard_le (H : ℕ) : (diagBBox H).ncard ≤ 100 * (H + 1) ^ 3 := by
  refine le_trans (ncard_box3_le (4 * H) H H) ?_
  have h1 : 2 * (4 * H) + 1 ≤ 9 * (H + 1) := by omega
  have h2 : 2 * H + 1 ≤ 3 * (H + 1) := by omega
  calc (2 * (4 * H) + 1) * ((2 * H + 1) * (2 * H + 1))
      ≤ (9 * (H + 1)) * ((3 * (H + 1)) * (3 * (H + 1))) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h2)
    _ = 81 * (H + 1) ^ 3 := by ring
    _ ≤ 100 * (H + 1) ^ 3 := by nlinarith [Nat.zero_le ((H+1)^3)]

theorem symmDiagA_ncard_le (H : ℕ) : (symmDiagA H).ncard ≤ 300 * (H + 1) ^ 3 := by
  have hfin : (diagABox H).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet
      (Finset.Icc (-((4 * H : ℕ) : ℤ)) ((4 * H : ℕ) : ℤ) ×ˢ
        (Finset.Icc (-(H : ℤ)) (H : ℤ) ×ˢ
          Finset.Icc (-((5 * H : ℕ) : ℤ)) ((5 * H : ℕ) : ℤ)))) ?_
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
      Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩,
      ⟨(abs_le.mp h3).1, (abs_le.mp h3).2⟩⟩
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (f := fun t : ℤ × ℤ × ℤ × ℤ × ℤ => (t.1, t.2.1, t.2.2.2.2)) ?_ ?_ hfin) (diagABox_ncard_le H)
  · rintro ⟨x, a, c, d, e⟩ ht
    obtain ⟨⟨hmem, -⟩, -⟩ := ht
    obtain ⟨hx, ha, hc, hd, he, -⟩ := hmem
    exact ⟨hx, ha, he⟩
  · rintro ⟨x, a, c, d, e⟩ h1 ⟨x', a', c', d', e'⟩ h2 h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, ha, he⟩ := h
    obtain ⟨⟨-, hdiag1⟩, hsq1⟩ := h1
    obtain ⟨⟨-, hdiag2⟩, hsq2⟩ := h2
    have hd : d = d' := by rw [hx] at hsq1; linarith
    have hc : c = c' := by rw [hx, ha] at hdiag1; linarith
    subst hx; subst ha; subst he; subst hd; subst hc
    rfl

theorem symmDiagB_ncard_le (H : ℕ) : (symmDiagB H).ncard ≤ 100 * (H + 1) ^ 3 := by
  have hsq : ∀ t ∈ symmDiagB H, t.2.1 ^ 2 = 4 * t.2.2.2.2 := fun t ht => symmDiag_sq_a H ht.1 ht.2
  have hfin : (diagBBox H).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet
      (Finset.Icc (-((4 * H : ℕ) : ℤ)) ((4 * H : ℕ) : ℤ) ×ˢ
        (Finset.Icc (-(H : ℤ)) (H : ℤ) ×ˢ
          Finset.Icc (-(H : ℤ)) (H : ℤ)))) ?_
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
      Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩,
      ⟨(abs_le.mp h3).1, (abs_le.mp h3).2⟩⟩
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (f := fun t : ℤ × ℤ × ℤ × ℤ × ℤ => (t.1, t.2.1, t.2.2.2.1)) ?_ ?_ hfin) (diagBBox_ncard_le H)
  · rintro ⟨x, a, c, d, e⟩ ht
    obtain ⟨⟨hmem, -⟩, -⟩ := ht
    obtain ⟨hx, ha, hc, hd, he, -⟩ := hmem
    exact ⟨hx, ha, hd⟩
  · rintro ⟨x, a, c, d, e⟩ h1 ⟨x', a', c', d', e'⟩ h2 h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, ha, hd⟩ := h
    have he : e = e' := by
      have h1' := hsq ⟨x, a, c, d, e⟩ h1
      have h2' := hsq ⟨x', a', c', d', e'⟩ h2
      rw [← ha] at h2'
      linarith
    have hc : c = c' := by
      have hd1 := h1.1.2
      have hd2 := h2.1.2
      rw [hx, ha] at hd1
      linarith
    subst hx; subst ha; subst hd; subst he; subst hc
    rfl

/-- **The diagonal bound**: `#symmDiag H ≤ 400 (H+1)^3`. -/
theorem symmDiag_ncard_le (H : ℕ) : (symmDiag H).ncard ≤ 400 * (H + 1) ^ 3 := by
  have hfin : (symmDiagA H ∪ symmDiagB H).Finite :=
    (symmBox_finite H).subset (by
      rintro t (ht | ht) <;> exact (ht.1.1 : t ∈ symmBox H))
  have h1 : (symmDiag H).ncard ≤ (symmDiagA H).ncard + (symmDiagB H).ncard :=
    le_trans (Set.ncard_le_ncard (symmDiag_subset_union H) hfin) (Set.ncard_union_le _ _)
  have h2 := symmDiagA_ncard_le H
  have h3 := symmDiagB_ncard_le H
  nlinarith [h1, h2, h3]

/-! ## The off-diagonal count: foundations -/

/-- The radical of (the absolute value of) an integer: `∏_{p | |A|} p`. -/
noncomputable def radZ (A : ℤ) : ℕ := A.natAbs.primeFactors.prod id

theorem radZ_pos (A : ℤ) : 0 < radZ A :=
  Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem radZ_one_le (A : ℤ) : 1 ≤ radZ A := radZ_pos A

theorem radZ_neg (A : ℤ) : radZ (-A) = radZ A := by
  rw [radZ, radZ, Int.natAbs_neg]

theorem radZ_natCast (n : ℕ) : radZ (n : ℤ) = n.primeFactors.prod id := by
  rw [radZ, Int.natAbs_natCast]

/-- `1/rad(A)`, with the value `0` at `A = 0` (a harmless convention: `A = 0` never
contributes in the off-diagonal count). -/
noncomputable def gZ (A : ℤ) : ℝ := if A = 0 then 0 else 1 / (radZ A : ℝ)

theorem gZ_nonneg (A : ℤ) : 0 ≤ gZ A := by
  rw [gZ]; split
  · norm_num
  · exact div_nonneg zero_le_one (Nat.cast_nonneg _)

theorem gZ_eq (A : ℤ) (hA : A ≠ 0) : gZ A = 1 / (radZ A : ℝ) := by rw [gZ, if_neg hA]

theorem gZ_neg (A : ℤ) : gZ (-A) = gZ A := by
  rw [gZ, gZ, radZ_neg]
  by_cases h : A = 0
  · subst h; simp
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h]

theorem gZ_zero : gZ 0 = 0 := rfl

/-- `rad(n)` as a real number (for `n : ℕ`). -/
noncomputable def radF (n : ℕ) : ℝ := (((n.primeFactors.prod id : ℕ)) : ℝ)

theorem gZ_le_one (A : ℤ) : gZ A ≤ 1 := by
  rw [gZ]; split
  · norm_num
  · rw [div_le_one (Nat.cast_pos.mpr (radZ_pos A))]
    exact_mod_cast radZ_one_le A

/-- **Finiteness of the radical-divisibility input.** -/
theorem radZ_dvd_of_dvd_sq {A m : ℤ} (h : A ∣ m ^ 2) : (radZ A : ℤ) ∣ m := by
  have h1 : A.natAbs ∣ m.natAbs ^ 2 := by
    obtain ⟨k, hk⟩ := h
    refine ⟨k.natAbs, ?_⟩
    have h2 : m.natAbs ^ 2 = (m ^ 2).natAbs := by rw [Int.natAbs_pow]
    rw [h2, hk, Int.natAbs_mul]
  have h2 : A.natAbs.primeFactors.prod id ∣ m.natAbs :=
    Commons.NumberTheory.Nat.radical_dvd_of_dvd_pow (by norm_num) h1
  have h3 : (radZ A : ℤ) ∣ (m.natAbs : ℤ) := by exact_mod_cast h2
  exact h3.trans (Int.natAbs_dvd.mpr (dvd_refl m))

/-! ### A generic "sum over fibres" bound -/

theorem ncard_le_sum_fiber {α β : Type*} (P : Set (α × β)) (hPfin : P.Finite) (s : Finset α)
    (f : α → ℕ) (hs : ∀ p ∈ P, p.1 ∈ s)
    (hf : ∀ a ∈ s, (({b : β | (a, b) ∈ P} : Set β)).ncard ≤ f a) :
    P.ncard ≤ ∑ a ∈ s, f a := by
  classical
  have himg : (hPfin.toFinset).image Prod.fst ⊆ s := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact hs q (hPfin.mem_toFinset.mp hq)
  have hfib : ∀ a ∈ (hPfin.toFinset).image Prod.fst,
      ((hPfin.toFinset).filter (fun q => q.1 = a)).card ≤ f a := by
    intro a ha
    have hfin : ({b : β | (a, b) ∈ P} : Set β).Finite :=
      (hPfin.image Prod.snd).subset (by
        rintro b hb
        exact ⟨(a, b), hb, rfl⟩)
    have heq : hfin.toFinset.image (fun b => (a, b))
        = (hPfin.toFinset).filter (fun q => q.1 = a) := by
      ext q
      constructor
      · intro hq
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
        rw [Finset.mem_filter]
        exact ⟨hPfin.mem_toFinset.mpr (hfin.mem_toFinset.mp hb), rfl⟩
      · intro hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        rw [Finset.mem_image]
        refine ⟨q.2, ?_, Prod.ext hq2.symm rfl⟩
        rw [hfin.mem_toFinset, Set.mem_setOf_eq, ← hq2]
        exact hPfin.mem_toFinset.mp hq1
    have hcard : ((hPfin.toFinset).filter (fun q => q.1 = a)).card
        = ({b : β | (a, b) ∈ P} : Set β).ncard := by
      rw [← heq, Finset.card_image_of_injective _ (fun b b' h => ((Prod.mk.injEq a b a b').mp h).2)]
      exact (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [hcard]
    exact hf a (himg ha)
  calc P.ncard = (hPfin.toFinset).card := Set.ncard_eq_toFinset_card P hPfin
    _ = ∑ a ∈ (hPfin.toFinset).image Prod.fst, ((hPfin.toFinset).filter (fun q => q.1 = a)).card :=
        Finset.card_eq_sum_card_fiberwise (by
          intro q hq
          exact Finset.mem_image_of_mem _ hq)
    _ ≤ ∑ a ∈ (hPfin.toFinset).image Prod.fst, f a := Finset.sum_le_sum hfib
    _ ≤ ∑ a ∈ s, f a := Finset.sum_le_sum_of_subset_of_nonneg himg (fun a _ _ => Nat.zero_le _)

/-! ### The `(a,c)` fibre bound -/

/-- For fixed `(x,d)` with `A = x² - 4d` the pairs `(a,c)` in the box with `A ∣ (xa-2c)²`
number at most `(2H+1) * (4H/rad(A) + 1)`: for each `a`, the admissible `c` lie in one
residue class modulo `rad(A)`. -/
theorem ac_ncard_le (A x : ℤ) (H : ℕ) :
    (({q : ℤ × ℤ | |q.1| ≤ (H : ℤ) ∧ |q.2| ≤ (H : ℤ) ∧ A ∣ (x * q.1 - 2 * q.2) ^ 2} :
      Set (ℤ × ℤ))).ncard ≤ (2 * H + 1) * (4 * H / radZ A + 1) := by
  classical
  set P : Set (ℤ × ℤ) :=
    {q : ℤ × ℤ | |q.1| ≤ (H : ℤ) ∧ |q.2| ≤ (H : ℤ) ∧ A ∣ (x * q.1 - 2 * q.2) ^ 2} with hP
  have hfin : P.Finite := by
    refine Set.Finite.subset
      (Finset.finite_toSet (Finset.Icc (-(H : ℤ)) (H : ℤ) ×ˢ Finset.Icc (-(H : ℤ)) (H : ℤ))) ?_
    intro q hq
    obtain ⟨h1, h2, -⟩ := hq
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩⟩
  have h1 : P.ncard ≤ ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), (4 * H / radZ A + 1) := by
    refine ncard_le_sum_fiber P hfin (Finset.Icc (-(H : ℤ)) (H : ℤ))
      (fun _ => 4 * H / radZ A + 1) ?_ ?_
    · intro q hq
      rw [hP] at hq
      rw [Finset.mem_Icc]
      exact ⟨(abs_le.mp hq.1).1, (abs_le.mp hq.1).2⟩
    · intro a ha
      have hsub : ({b : ℤ | (a, b) ∈ P} : Set ℤ) ⊆
          {c : ℤ | |c| ≤ (H : ℤ) ∧ (radZ A : ℤ) ∣ (x * a - 2 * c)} := by
        intro c hc
        rw [hP] at hc
        exact ⟨hc.2.1, radZ_dvd_of_dvd_sq hc.2.2⟩
      refine le_trans (Set.ncard_le_ncard hsub ?_)
        (Commons.NumberTheory.Int.ncard_two_mul_residue_le (radZ A) H (radZ_one_le A) (x * a))
      refine Set.Finite.subset
        (Finset.finite_toSet (Finset.Icc (-(H : ℤ)) (H : ℤ))) ?_
      intro c hc
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨(abs_le.mp hc.1).1, (abs_le.mp hc.1).2⟩
  refine h1.trans ?_
  rw [Finset.sum_const, Int.card_Icc]
  have hcard : (((H : ℤ) + 1 - (-(H : ℤ))).toNat) = 2 * H + 1 := by
    have hh : (H : ℤ) + 1 - (-(H : ℤ)) = ((2 * H + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hh, Int.toNat_natCast]
  rw [hcard, smul_eq_mul]

/-! ### The key sum `S = ∑_{x,d} 1/rad(x² - 4d) = O(H)` -/

/-- The range of `x` (`|x| ≤ 4H`). -/
def xRange (H : ℕ) : Finset ℤ := Finset.Icc (-((4 * H : ℕ) : ℤ)) ((4 * H : ℕ) : ℤ)

/-- The range of `d` (`|d| ≤ H`). -/
def dRange (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ)

/-- The range of the possible values `y = x² - 4d`: `-4H ≤ y ≤ 16H² + 4H`. -/
def yRange (H : ℕ) : Finset ℤ := Finset.Icc (-((4 * H : ℕ) : ℤ)) (((16 * H ^ 2 + 4 * H : ℕ)) : ℤ)

/-- The auxiliary `(x,d)`-sum of `1/rad(x²-4d)`. -/
def Ssum (H : ℕ) : ℝ := ∑ x ∈ xRange H, ∑ d ∈ dRange H, gZ (x ^ 2 - 4 * d)

theorem xRange_card (H : ℕ) : (xRange H).card = 8 * H + 1 := by
  rw [xRange, Int.card_Icc]
  have h : (((4 * H : ℕ) : ℤ) + 1 - (-(((4 * H : ℕ) : ℤ)))) = ((8 * H + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

theorem dRange_card (H : ℕ) : (dRange H).card = 2 * H + 1 := by
  rw [dRange, Int.card_Icc]
  have h : ((H : ℤ) + 1 - (-(H : ℤ))) = ((2 * H + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

theorem mem_xRange {H : ℕ} {x : ℤ} : x ∈ xRange H ↔ |x| ≤ ((4 * H : ℕ) : ℤ) := by
  rw [xRange, Finset.mem_Icc, abs_le]

/-- Step 1: reindexing the inner `d`-sum by `y = x² - 4d`. -/
theorem Ssum_step1 (H : ℕ) {x : ℤ} (hx : x ∈ xRange H) :
    (∑ d ∈ dRange H, gZ (x ^ 2 - 4 * d)) ≤
      ∑ y ∈ yRange H, (if |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ) then gZ y else 0) := by
  have hx4 : |x| ≤ ((4 * H : ℕ) : ℤ) := mem_xRange.mp hx
  have hinj : Set.InjOn (fun d : ℤ => x ^ 2 - 4 * d) (↑(dRange H) : Set ℤ) := by
    intro d _ d' _ h
    linarith
  rw [← Finset.sum_image (f := gZ) hinj]
  have hsub : (Finset.image (fun d : ℤ => x ^ 2 - 4 * d) (dRange H)) ⊆
      (yRange H).filter (fun y => |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)) := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    rw [dRange, Finset.mem_Icc] at hd
    rw [Finset.mem_filter, yRange, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h4H : ((4 * H : ℕ) : ℤ) = 4 * (H : ℤ) := by push_cast; ring
      rw [h4H]
      nlinarith [hd.1, sq_nonneg x]
    · have hcast : ((16 * H ^ 2 + 4 * H : ℕ) : ℤ) = 16 * (H : ℤ) ^ 2 + 4 * (H : ℤ) := by
        push_cast; ring
      rw [hcast]
      have h3 : x * x ≤ ((4 * H : ℕ) : ℤ) * ((4 * H : ℕ) : ℤ) := by
        nlinarith [(abs_le.mp hx4).1, (abs_le.mp hx4).2]
      have h4 : ((4 * H : ℕ) : ℤ) * ((4 * H : ℕ) : ℤ) = 16 * (H : ℤ) ^ 2 := by push_cast; ring
      nlinarith [hd.2]
    · have hkey : (x ^ 2 - 4 * d) - x ^ 2 = -(4 * d) := by ring
      rw [hkey, abs_neg, abs_mul]
      have h4H : ((4 * H : ℕ) : ℤ) = 4 * (H : ℤ) := by push_cast; ring
      rw [h4H]
      have hdabs : |d| ≤ (H : ℤ) := abs_le.mpr hd
      have : |(4 : ℤ)| * |d| ≤ 4 * (H : ℤ) := by
        rw [show |(4 : ℤ)| = 4 from by norm_num]
        nlinarith
      exact this
  calc ∑ y ∈ Finset.image (fun d : ℤ => x ^ 2 - 4 * d) (dRange H), gZ y
      ≤ ∑ y ∈ (yRange H).filter (fun y => |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)), gZ y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => gZ_nonneg i)
    _ = ∑ y ∈ yRange H, (if |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ) then gZ y else 0) :=
        Finset.sum_filter _ _

/-- Step 2: swapping the sums and counting the `x`-fibres. -/
theorem Ssum_le_y (H : ℕ) :
    Ssum H ≤ ∑ y ∈ yRange H, gZ y *
      ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ) := by
  calc Ssum H
      = ∑ x ∈ xRange H, ∑ d ∈ dRange H, gZ (x ^ 2 - 4 * d) := rfl
    _ ≤ ∑ x ∈ xRange H, ∑ y ∈ yRange H,
          (if |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ) then gZ y else 0) :=
        Finset.sum_le_sum (fun x hx => Ssum_step1 H hx)
    _ = ∑ y ∈ yRange H, ∑ x ∈ xRange H,
          (if |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ) then gZ y else 0) := Finset.sum_comm
    _ = ∑ y ∈ yRange H, gZ y *
          ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ) := by
        apply Finset.sum_congr rfl
        intro y _
        have hset : ({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)
            = ↑((xRange H).filter (fun x => |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ))) := by
          ext x
          simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
        rw [hset, Set.ncard_coe_finset, ← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]


/-- The number of `x ∈ xRange H` with `|y - x²| ≤ 4H`, when `|y| ≤ 8H`. -/
theorem Ny_le_small (H : ℕ) {y : ℤ} (hy : |y| ≤ ((8 * H : ℕ) : ℤ)) :
    (({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard
      ≤ 2 * Nat.sqrt (12 * H) + 1 := by
  have hcast12 : ((12 * H : ℕ) : ℤ) = 12 * (H : ℤ) := by push_cast; ring
  have hcast8 : ((8 * H : ℕ) : ℤ) = 8 * (H : ℤ) := by push_cast; ring
  have hcast4 : ((4 * H : ℕ) : ℤ) = 4 * (H : ℤ) := by push_cast; ring
  have hsub : ({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ) ⊆
      {x : ℤ | x ^ 2 ≤ ((12 * H : ℕ) : ℤ)} := by
    intro x hx
    obtain ⟨-, h2⟩ := hx
    rw [hcast4] at h2
    have h4 : x ^ 2 - y ≤ 4 * (H : ℤ) := by linarith [(abs_le.mp h2).1]
    have hy' : |y| ≤ 8 * (H : ℤ) := by rw [hcast8] at hy; exact hy
    have h5 : y ≤ |y| := le_abs_self y
    have hgoal : x ^ 2 ≤ 12 * (H : ℤ) := by linarith
    rw [hcast12]
    exact hgoal
  have hfin : ({x : ℤ | x ^ 2 ≤ ((12 * H : ℕ) : ℤ)} : Set ℤ).Finite := by
    refine (Set.finite_Icc (-(((Nat.sqrt (12 * H) : ℕ)) : ℤ)) (((Nat.sqrt (12 * H) : ℕ)) : ℤ)).subset ?_
    intro x hx
    rw [Set.mem_Icc]
    have h1 : x.natAbs ^ 2 ≤ 12 * H := by
      have h2 : ((x.natAbs : ℤ)) ^ 2 ≤ ((12 * H : ℕ) : ℤ) := by
        have h3 : |x| ^ 2 ≤ ((12 * H : ℕ) : ℤ) := by rw [sq_abs x]; exact hx
        simpa only [Int.natCast_natAbs] using h3
      exact_mod_cast h2
    have h2 : x.natAbs ≤ Nat.sqrt (12 * H) :=
      Nat.le_sqrt.mpr (by simpa [pow_two] using h1)
    have h4 : ((x.natAbs : ℕ) : ℤ) ≤ ((Nat.sqrt (12 * H) : ℕ) : ℤ) := by exact_mod_cast h2
    refine ⟨?_, ?_⟩
    · have h3 : -((x.natAbs : ℤ)) ≤ x := by rw [Int.natCast_natAbs]; exact neg_abs_le x
      linarith
    · have h3 : x ≤ (x.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self x
      linarith
  exact le_trans (Set.ncard_le_ncard hsub hfin) (Commons.NumberTheory.Int.ncard_sq_le_sqrt (12 * H))

/-! ### The `y`-sums -/

theorem sqrt12_mul_sqrt8_le (H : ℕ) :
    Real.sqrt ((12 * H : ℕ) : ℝ) * Real.sqrt ((8 * H : ℕ) : ℝ) ≤ 10 * (H : ℝ) := by
  have h1 : (0 : ℝ) ≤ ((12 * H : ℕ) : ℝ) := by positivity
  rw [← Real.sqrt_mul h1]
  have h3 : ((12 * H : ℕ) : ℝ) * ((8 * H : ℕ) : ℝ) = 96 * (H : ℝ) ^ 2 := by push_cast; ring
  have h4 : Real.sqrt (96 * (H : ℝ) ^ 2) = Real.sqrt 96 * (H : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 96)]
    rw [Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [h3, h4]
  have h5 : Real.sqrt 96 ≤ (10 : ℝ) := by rw [Real.sqrt_le_iff]; norm_num
  calc Real.sqrt 96 * (H : ℝ) ≤ 10 * (H : ℝ) :=
        mul_le_mul_of_nonneg_right h5 (Nat.cast_nonneg H)
    _ = 10 * (H : ℝ) := rfl

theorem sqrt8H_le (H : ℕ) : Real.sqrt ((8 * H : ℕ) : ℝ) ≤ 3 * ((H : ℝ) + 1) := by
  have h1 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
  have h0 : ((8 * H : ℕ) : ℝ) = 8 * (H : ℝ) := by push_cast; ring
  have h4 : Real.sqrt (8 * (H : ℝ)) = Real.sqrt 8 * Real.sqrt (H : ℝ) := Real.sqrt_mul h1 _
  rw [h0, h4]
  have h2 : Real.sqrt 8 ≤ 3 := by rw [Real.sqrt_le_iff]; norm_num
  have h3 : Real.sqrt (H : ℝ) ≤ (H : ℝ) + 1 := by
    have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  calc Real.sqrt 8 * Real.sqrt (H : ℝ) ≤ 3 * Real.sqrt (H : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (H : ℝ))
    _ ≤ 3 * ((H : ℝ) + 1) := by linarith

/-- `∑_{|y| ≤ N} gZ y = 2 ∑_{n ≤ N} 1/rad(n)`. -/
theorem sum_gZ_Icc_eq (N : ℕ) :
    (∑ y ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), gZ y)
      = 2 * (∑ n ∈ Finset.Icc 1 N, 1 / radF n) := by
  rw [Commons.Analysis.Sum.sum_Icc_symm N gZ, gZ_zero, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  have h1 : gZ (n : ℤ) = 1 / radF n := by
    rw [gZ_eq _ (by exact_mod_cast hn0), radZ_natCast, radF]
  rw [h1, gZ_neg, h1]
  ring

/-- `∑_{y ∈ Y} gZ y ≤ 2 ∑_{n ≤ N} 1/rad(n)` for `Y ⊆ [-N,N]`. -/
theorem sum_gZ_le_of_subset (N : ℕ) (Y : Finset ℤ)
    (hY : Y ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    (∑ y ∈ Y, gZ y) ≤ 2 * (∑ n ∈ Finset.Icc 1 N, 1 / radF n) := by
  rw [← sum_gZ_Icc_eq N]
  exact Finset.sum_le_sum_of_subset_of_nonneg hY (fun i _ _ => gZ_nonneg i)

/-- The `|y| ≤ 8H` part of the `y`-sum. -/
theorem sum_gZ_small_le (H : ℕ) :
    (∑ y ∈ (yRange H).filter (fun y => |y| ≤ ((8 * H : ℕ) : ℤ)), gZ y)
      ≤ 2 * (∑ n ∈ Finset.Icc 1 (8 * H), 1 / radF n) := by
  refine sum_gZ_le_of_subset (8 * H) _ ?_
  intro y hy
  rw [Finset.mem_filter] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [Finset.mem_Icc]
  exact ⟨(abs_le.mp hy2).1, (abs_le.mp hy2).2⟩

/-- `∑_{|y| ≤ N} gZ y / √|y| = 2 ∑_{n ≤ N} 1/(√n · rad n)`. -/
theorem sum_F_Icc_eq (N : ℕ) :
    (∑ y ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ))
      = 2 * (∑ n ∈ Finset.Icc 1 N,
          1 / (Real.sqrt (n : ℝ) * radF n)) := by
  rw [Commons.Analysis.Sum.sum_Icc_symm N (fun y => gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ))]
  have h0 : gZ 0 / Real.sqrt (((0 : ℤ).natAbs : ℕ) : ℝ) = 0 := by simp [gZ]
  rw [h0, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  have h1 : gZ (n : ℤ) / Real.sqrt (((n : ℤ).natAbs : ℕ) : ℝ)
      = 1 / (Real.sqrt (n : ℝ) * radF n) := by
    rw [Int.natAbs_natCast, gZ_eq _ (by exact_mod_cast hn0), radZ_natCast, radF]
    ring
  have h2 : gZ (-(n : ℤ)) / Real.sqrt (((-(n : ℤ)).natAbs : ℕ) : ℝ)
      = 1 / (Real.sqrt (n : ℝ) * radF n) := by
    rw [Int.natAbs_neg, Int.natAbs_natCast, gZ_neg]
    exact h1
  rw [h1, h2]
  ring

/-- The `8H < |y|` part of the `y`-sum, in the form needed for the `1/√|y|` estimate. -/
theorem sum_gZ_big_sqrt_le (H : ℕ) :
    (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))),
        gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ))
      ≤ 2 * (∑ n ∈ (Finset.Icc 1 (16 * H ^ 2 + 4 * H) : Finset ℕ),
          1 / (Real.sqrt (n : ℝ) * radF n)) := by
  have hsub : (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))) ⊆
      Finset.Icc (-(((16 * H ^ 2 + 4 * H : ℕ)) : ℤ)) (((16 * H ^ 2 + 4 * H : ℕ)) : ℤ) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hy1, -⟩ := hy
    rw [yRange, Finset.mem_Icc] at hy1
    rw [Finset.mem_Icc]
    have h4H : ((4 * H : ℕ) : ℤ) ≤ (((16 * H ^ 2 + 4 * H : ℕ)) : ℤ) := by
      have : (4 * H : ℕ) ≤ 16 * H ^ 2 + 4 * H := by nlinarith
      exact_mod_cast this
    exact ⟨by linarith [hy1.1], hy1.2⟩
  calc (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))),
        gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ))
      ≤ ∑ y ∈ Finset.Icc (-(((16 * H ^ 2 + 4 * H : ℕ)) : ℤ))
          (((16 * H ^ 2 + 4 * H : ℕ)) : ℤ), gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => div_nonneg (gZ_nonneg i) (Real.sqrt_nonneg _))
    _ = 2 * (∑ n ∈ (Finset.Icc 1 (16 * H ^ 2 + 4 * H) : Finset ℕ),
          1 / (Real.sqrt (n : ℝ) * radF n)) := sum_F_Icc_eq _

/-- The `gZ`-mass of the `8H < |y|` part (no `√` weight). -/
theorem sum_gZ_big_le (H : ℕ) :
    (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))), gZ y)
      ≤ 2 * (∑ n ∈ (Finset.Icc 1 (16 * H ^ 2 + 4 * H) : Finset ℕ), 1 / radF n) := by
  refine sum_gZ_le_of_subset (16 * H ^ 2 + 4 * H) _ ?_
  intro y hy
  rw [Finset.mem_filter] at hy
  obtain ⟨hy1, -⟩ := hy
  rw [yRange, Finset.mem_Icc] at hy1
  rw [Finset.mem_Icc]
  have h4H : ((4 * H : ℕ) : ℤ) ≤ (((16 * H ^ 2 + 4 * H : ℕ)) : ℤ) := by
    have : (4 * H : ℕ) ≤ 16 * H ^ 2 + 4 * H := by nlinarith
    exact_mod_cast this
  exact ⟨by linarith [hy1.1], hy1.2⟩

/-- The number of `x ∈ xRange H` with `|y - x²| ≤ 4H`, when `8H < |y|`. -/
theorem Ny_le_big (H : ℕ) {y : ℤ} (hy : ((8 * H : ℕ) : ℤ) < |y|) :
    ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ)
      ≤ 16 * (H : ℝ) / Real.sqrt (y.natAbs) + 4 := by
  have hsub : ({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ) ⊆
      {x : ℤ | |x ^ 2 - y| ≤ ((4 * H : ℕ) : ℤ)} := by
    intro x hx
    show |x ^ 2 - y| ≤ ((4 * H : ℕ) : ℤ)
    rw [abs_sub_comm]
    exact hx.2
  have hfin : ({x : ℤ | |x ^ 2 - y| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ).Finite := by
    refine (Set.finite_Icc (-(((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ))
      (((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ)).subset ?_
    intro x hx
    rw [Set.mem_Icc]
    have hx2 : x ^ 2 ≤ |y| + ((4 * H : ℕ) : ℤ) := by
      have hx' : |x ^ 2 - y| ≤ ((4 * H : ℕ) : ℤ) := hx
      have h1 := (abs_le.mp hx').2
      have h2 : y ≤ |y| := le_abs_self y
      linarith
    have hs : (((Nat.sqrt y.natAbs : ℕ) : ℤ)) ^ 2 ≤ ((y.natAbs : ℕ) : ℤ) := by
      rw [pow_two]; exact_mod_cast Nat.sqrt_le y.natAbs
    have hlt : ((y.natAbs : ℕ) : ℤ) < (((Nat.sqrt y.natAbs : ℕ) : ℤ) + 1) ^ 2 := by
      have h1 := Nat.lt_succ_sqrt y.natAbs
      have h2 : (((Nat.sqrt y.natAbs).succ : ℕ) : ℤ)
          = (((Nat.sqrt y.natAbs : ℕ) : ℤ) + 1) := by push_cast; ring
      have h3 : (((y.natAbs : ℕ) : ℤ))
          < (((Nat.sqrt y.natAbs).succ : ℕ) : ℤ) * (((Nat.sqrt y.natAbs).succ : ℕ) : ℤ) := by
        exact_mod_cast h1
      rw [h2] at h3
      rw [pow_two]
      exact h3
    have habs : |y| = ((y.natAbs : ℕ) : ℤ) := (Int.natCast_natAbs y).symm
    have hN : (((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ)
        = ((Nat.sqrt y.natAbs : ℕ) : ℤ) + ((4 * H : ℕ) : ℤ) + 1 := by push_cast; ring
    have hkey : x ^ 2 ≤ (((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ) ^ 2 := by
      rw [hN]
      have hsnn : (0 : ℤ) ≤ ((Nat.sqrt y.natAbs : ℕ) : ℤ) := Nat.cast_nonneg _
      have hLnn : (0 : ℤ) ≤ ((4 * H : ℕ) : ℤ) := Nat.cast_nonneg _
      have hsp1 : (0 : ℤ) ≤ ((Nat.sqrt y.natAbs : ℕ) : ℤ) + 1 := by linarith
      nlinarith [hs, hlt, habs, hx2, hsnn, hLnn, hsp1, sq_nonneg (((4 * H : ℕ) : ℤ) + 1),
        mul_nonneg hsnn hsp1, mul_nonneg hsnn hLnn]
    have hxa : |x| ≤ (((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ) := by
      have h2 : |x| ^ 2 ≤ (((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ) ^ 2 := by
        rw [sq_abs]; exact hkey
      have h3 : |(|x| : ℤ)| ≤ |(((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ)| := sq_le_sq.mp h2
      have hNn : (0 : ℤ) ≤ (((Nat.sqrt y.natAbs + 4 * H + 1 : ℕ)) : ℤ) :=
        Nat.cast_nonneg (Nat.sqrt y.natAbs + 4 * H + 1)
      rw [abs_of_nonneg (abs_nonneg x), abs_of_nonneg hNn] at h3
      exact h3
    rw [abs_le] at hxa
    exact hxa
  refine le_trans (Nat.cast_le (α := ℝ).mpr (Set.ncard_le_ncard hsub hfin)) ?_
  have h8 : 2 * (4 * H) ≤ y.natAbs := by
    have h1 : ((8 * H : ℕ) : ℤ) < (y.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact hy
    have h2 : 8 * H ≤ y.natAbs := by exact_mod_cast Int.le_of_lt h1
    omega
  have h := Commons.NumberTheory.Int.ncard_sq_close_le_abs y (4 * H) (by simpa using h8)
  have hc : 4 * ((4 * H : ℕ) : ℝ) = 16 * (H : ℝ) := by push_cast; ring
  rw [hc] at h
  exact h

/-- **The key estimate `S = ∑_{x,d} 1/rad(x²-4d) ≤ 500 H + 100`.** -/
theorem Ssum_le (H : ℕ) : Ssum H ≤ 500 * (H : ℝ) + 100 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (yRange H)
    (fun y => |y| ≤ ((8 * H : ℕ) : ℤ))
    (fun y => gZ y * ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ))
  have hsm : (∑ y ∈ (yRange H).filter (fun y => |y| ≤ ((8 * H : ℕ) : ℤ)),
        gZ y * ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ))
      ≤ 138 * (H : ℝ) + 18 := by
    have h1 : ∀ y ∈ (yRange H).filter (fun y => |y| ≤ ((8 * H : ℕ) : ℤ)),
        gZ y * ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ)
          ≤ gZ y * (2 * Real.sqrt ((12 * H : ℕ) : ℝ) + 1) := by
      intro y hy
      have hy8 : |y| ≤ ((8 * H : ℕ) : ℤ) := (Finset.mem_filter.mp hy).2
      have hny := Ny_le_small H hy8
      have hcast : (((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℕ) : ℝ)
          ≤ 2 * ((Nat.sqrt (12 * H) : ℕ) : ℝ) + 1 := by exact_mod_cast hny
      have hsqrt : ((Nat.sqrt (12 * H) : ℕ) : ℝ) ≤ Real.sqrt ((12 * H : ℕ) : ℝ) := by
        have hs' : ((Nat.sqrt (12 * H) : ℕ) : ℝ) * ((Nat.sqrt (12 * H) : ℕ) : ℝ)
            ≤ ((12 * H : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le (12 * H)
        have := Real.sqrt_le_sqrt (show ((Nat.sqrt (12 * H) : ℕ) : ℝ) ^ 2 ≤ ((12 * H : ℕ) : ℝ) by
          simpa [pow_two] using hs')
        rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at this
      exact mul_le_mul_of_nonneg_left (by linarith) (gZ_nonneg y)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.sum_mul]
    have h3 : (∑ y ∈ (yRange H).filter (fun y => |y| ≤ ((8 * H : ℕ) : ℤ)), gZ y)
        ≤ 2 * (3 * Real.sqrt ((8 * H : ℕ) : ℝ)) := by
      refine le_trans (sum_gZ_small_le H) ?_
      have hbase : (∑ n ∈ (Finset.Icc 1 (8 * H) : Finset ℕ), 1 / radF n)
          ≤ 3 * Real.sqrt ((8 * H : ℕ) : ℝ) := by
        have := Commons.NumberTheory.Nat.sum_inv_radical_le_sqrt (8 * H)
        simpa [radF] using this
      linarith
    have h4 : (0 : ℝ) ≤ 2 * Real.sqrt ((12 * H : ℕ) : ℝ) + 1 := by positivity
    have h5 := sqrt12_mul_sqrt8_le H
    have h6 := sqrt8H_le H
    calc (∑ y ∈ (yRange H).filter (fun y => |y| ≤ ((8 * H : ℕ) : ℤ)), gZ y)
          * (2 * Real.sqrt ((12 * H : ℕ) : ℝ) + 1)
        ≤ (2 * (3 * Real.sqrt ((8 * H : ℕ) : ℝ))) * (2 * Real.sqrt ((12 * H : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = 12 * (Real.sqrt ((8 * H : ℕ) : ℝ) * Real.sqrt ((12 * H : ℕ) : ℝ))
            + 6 * Real.sqrt ((8 * H : ℕ) : ℝ) := by ring
      _ ≤ 12 * (10 * (H : ℝ)) + 6 * (3 * ((H : ℝ) + 1)) := by
          have h5' : Real.sqrt ((8 * H : ℕ) : ℝ) * Real.sqrt ((12 * H : ℕ) : ℝ) ≤ 10 * (H : ℝ) := by
            rw [mul_comm]; exact h5
          have h5'' : 12 * (Real.sqrt ((8 * H : ℕ) : ℝ) * Real.sqrt ((12 * H : ℕ) : ℝ))
              ≤ 12 * (10 * (H : ℝ)) := mul_le_mul_of_nonneg_left h5' (by norm_num)
          have h6'' : 6 * Real.sqrt ((8 * H : ℕ) : ℝ) ≤ 6 * (3 * ((H : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h6 (by norm_num)
          linarith
      _ = 138 * (H : ℝ) + 18 := by ring
  have hbg : (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))),
        gZ y * ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ))
      ≤ 288 * (H : ℝ) + 24 := by
    have h1 : ∀ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))),
        gZ y * ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ)
          ≤ 16 * (H : ℝ) * (gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ)) + 4 * gZ y := by
      intro y hy
      have hy8 : ((8 * H : ℕ) : ℤ) < |y| := not_le.mp (Finset.mem_filter.mp hy).2
      have hny := Ny_le_big H hy8
      have hnn : (0 : ℝ) ≤ gZ y := gZ_nonneg y
      calc gZ y * ((({x : ℤ | x ∈ xRange H ∧ |y - x ^ 2| ≤ ((4 * H : ℕ) : ℤ)} : Set ℤ)).ncard : ℝ)
          ≤ gZ y * (16 * (H : ℝ) / Real.sqrt (y.natAbs) + 4) :=
            mul_le_mul_of_nonneg_left hny hnn
        _ = 16 * (H : ℝ) * (gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ)) + 4 * gZ y := by ring
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h3 : (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))),
          gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ)) ≤ 2 * 6 := by
      refine le_trans (sum_gZ_big_sqrt_le H) ?_
      have hbase := Commons.NumberTheory.Nat.sum_recip_sqrt_mul_radical_le (16 * H ^ 2 + 4 * H)
      have hbase' : (∑ n ∈ (Finset.Icc 1 (16 * H ^ 2 + 4 * H) : Finset ℕ),
          1 / (Real.sqrt (n : ℝ) * radF n)) ≤ 6 := by simpa [radF] using hbase
      linarith
    have h4 : (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))), gZ y)
        ≤ 2 * (3 * (4 * (H : ℝ) + 1)) := by
      refine le_trans (sum_gZ_big_le H) ?_
      have hbase := Commons.NumberTheory.Nat.sum_inv_radical_le_sqrt (16 * H ^ 2 + 4 * H)
      have hbase' : (∑ n ∈ (Finset.Icc 1 (16 * H ^ 2 + 4 * H) : Finset ℕ), 1 / radF n)
          ≤ 3 * Real.sqrt (((16 * H ^ 2 + 4 * H : ℕ)) : ℝ) := by simpa [radF] using hbase
      have hsq : Real.sqrt (((16 * H ^ 2 + 4 * H : ℕ)) : ℝ) ≤ 4 * (H : ℝ) + 1 := by
        have hle : (((16 * H ^ 2 + 4 * H : ℕ)) : ℝ) ≤ (4 * (H : ℝ) + 1) ^ 2 := by
          have h1 : (((16 * H ^ 2 + 4 * H : ℕ)) : ℝ) = 16 * (H : ℝ) ^ 2 + 4 * (H : ℝ) := by
            push_cast; ring
          have h2 : (4 * (H : ℝ) + 1) ^ 2 = 16 * (H : ℝ) ^ 2 + 8 * (H : ℝ) + 1 := by ring
          rw [h1, h2]
          have hh : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
          linarith
        rw [Real.sqrt_le_iff]
        exact ⟨by have hh : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H; linarith, hle⟩
      linarith
    have hA : 16 * (H : ℝ) * (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))),
          gZ y / Real.sqrt ((y.natAbs : ℕ) : ℝ)) ≤ 16 * (H : ℝ) * (2 * 6) :=
      mul_le_mul_of_nonneg_left h3 (by have hh : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H; linarith)
    have hB : 4 * (∑ y ∈ (yRange H).filter (fun y => ¬ (|y| ≤ ((8 * H : ℕ) : ℤ))), gZ y)
        ≤ 4 * (2 * (3 * (4 * (H : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    linarith [hA, hB]
  refine le_trans (Ssum_le_y H) ?_
  rw [← hsplit]
  linarith

/-! ### The off-diagonal bound -/

/-- The set of `(x, d, a, c)`-tuples into which `symmOff` injects. -/
def qSet (H : ℕ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {q | |q.1| ≤ ((4 * H : ℕ) : ℤ) ∧ |q.2.1| ≤ (H : ℤ) ∧ |q.2.2.1| ≤ (H : ℤ) ∧
    |q.2.2.2| ≤ (H : ℤ) ∧ (q.1 ^ 2 - 4 * q.2.1) ≠ 0 ∧
    (q.1 ^ 2 - 4 * q.2.1) ∣ (q.1 * q.2.2.1 - 2 * q.2.2.2) ^ 2}

theorem qSet_finite (H : ℕ) : (qSet H).Finite := by
  refine Set.Finite.subset
    (Finset.finite_toSet (xRange H ×ˢ (dRange H ×ˢ (dRange H ×ˢ dRange H)))) ?_
  intro q hq
  obtain ⟨h1, h2, h3, h4, -⟩ := hq
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product, Finset.mem_product,
    mem_xRange, dRange, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  obtain ⟨h4a, h4b⟩ := abs_le.mp h4
  exact ⟨h1, ⟨⟨h2a, h2b⟩, ⟨⟨h3a, h3b⟩, ⟨h4a, h4b⟩⟩⟩⟩

/-- The off-diagonal solutions inject into `qSet H` via `(x,a,c,d,e) ↦ (x,d,a,c)`. -/
theorem symmOff_ncard_le_qSet (H : ℕ) : (symmOff H).ncard ≤ (qSet H).ncard := by
  refine Set.ncard_le_ncard_of_injOn
    (f := fun t : ℤ × ℤ × ℤ × ℤ × ℤ => (t.1, t.2.2.2.1, t.2.1, t.2.2.1)) ?_ ?_ (qSet_finite H)
  · rintro ⟨x, a, c, d, e⟩ ht
    obtain ⟨hmem, hne⟩ := ht
    obtain ⟨hx, ha, hc, hd, he, hsymm⟩ := hmem
    have hA : x ^ 2 - 4 * d ≠ 0 := by
      intro h0
      have h1 : (x * a - 2 * c) ^ 2 = 0 := by rw [← hsymm]; rw [h0, zero_mul]
      have h2 : x * a - 2 * c = 0 := pow_eq_zero_iff (by norm_num) |>.mp h1
      exact hne (by linarith)
    exact ⟨hx, hd, ha, hc, hA, ⟨a ^ 2 - 4 * e, hsymm.symm⟩⟩
  · rintro ⟨x, a, c, d, e⟩ h1 ⟨x', a', c', d', e'⟩ h2 h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hx, hd, ha, hc⟩ := h
    obtain ⟨hmem1, hne1⟩ := h1
    obtain ⟨-, -, -, -, -, hsymm1⟩ := hmem1
    obtain ⟨-, -, -, -, -, hsymm2⟩ := h2.1
    have hsymm1' : (x ^ 2 - 4 * d) * (a ^ 2 - 4 * e) = (x * a - 2 * c) ^ 2 := hsymm1
    have hsymm2' : (x' ^ 2 - 4 * d') * (a' ^ 2 - 4 * e') = (x' * a' - 2 * c') ^ 2 := hsymm2
    have hA : x ^ 2 - 4 * d ≠ 0 := by
      intro h0
      have h3 : (x * a - 2 * c) ^ 2 = 0 := by rw [← hsymm1']; rw [h0, zero_mul]
      have h4 : x * a - 2 * c = 0 := pow_eq_zero_iff (by norm_num) |>.mp h3
      exact hne1 (by linarith)
    have he : e = e' := by
      have h2'' : (x ^ 2 - 4 * d) * (a ^ 2 - 4 * e') = (x * a - 2 * c) ^ 2 := by
        rw [← hx, ← hd, ← ha, ← hc] at hsymm2'
        exact hsymm2'
      have h5 : (x ^ 2 - 4 * d) * (a ^ 2 - 4 * e) = (x ^ 2 - 4 * d) * (a ^ 2 - 4 * e') := by
        rw [hsymm1', h2'']
      have h6 := mul_left_cancel₀ hA h5
      linarith
    subst hx; subst hd; subst ha; subst hc; subst he
    rfl

/-- One level of the `qSet`-bound: the `(a,c)`-fibres over `(x,d)`. -/
theorem qSet_fiber_le (H : ℕ) (x : ℤ) :
    (({p : ℤ × ℤ × ℤ | (x, p.1, p.2.1, p.2.2) ∈ qSet H} : Set (ℤ × ℤ × ℤ))).ncard
      ≤ ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
          (2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1) := by
  classical
  have hfin : ({p : ℤ × ℤ × ℤ | (x, p.1, p.2.1, p.2.2) ∈ qSet H} : Set (ℤ × ℤ × ℤ)).Finite := by
    refine Set.Finite.subset
      (Finset.finite_toSet (dRange H ×ˢ (dRange H ×ˢ dRange H))) ?_
    intro p hp
    obtain ⟨-, h2, h3, h4, -⟩ := hp
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product, dRange, Finset.mem_Icc,
      Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩,
      ⟨⟨(abs_le.mp h3).1, (abs_le.mp h3).2⟩, ⟨(abs_le.mp h4).1, (abs_le.mp h4).2⟩⟩⟩
  refine ncard_le_sum_fiber _ hfin ((dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0))
    (fun d => (2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1)) ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, dRange, Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp hp.2.1).1, (abs_le.mp hp.2.1).2⟩, hp.2.2.2.2.1⟩
  · intro d _
    have hsub : ({q : ℤ × ℤ | (d, q) ∈ {p : ℤ × ℤ × ℤ | (x, p.1, p.2.1, p.2.2) ∈ qSet H}} : Set (ℤ × ℤ))
        ⊆ {q : ℤ × ℤ | |q.1| ≤ (H : ℤ) ∧ |q.2| ≤ (H : ℤ) ∧
            (x ^ 2 - 4 * d) ∣ (x * q.1 - 2 * q.2) ^ 2} := by
      intro q hq
      obtain ⟨-, -, h3, h4, -, h6⟩ := hq
      exact ⟨h3, h4, h6⟩
    refine le_trans (Set.ncard_le_ncard hsub ?_) (ac_ncard_le (x ^ 2 - 4 * d) x H)
    refine Set.Finite.subset
      (Finset.finite_toSet (dRange H ×ˢ dRange H)) ?_
    intro q hq
    obtain ⟨h1, h2, -⟩ := hq
    rw [Finset.mem_coe, Finset.mem_product, dRange, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩⟩

/-- **The off-diagonal bound**: `#symmOff H ≤ 8000 (H+1)^3`. -/
theorem symmOff_ncard_le (H : ℕ) : ((symmOff H).ncard : ℝ) ≤ 8000 * ((H : ℝ) + 1) ^ 3 := by
  have h1 : (symmOff H).ncard ≤ (qSet H).ncard := symmOff_ncard_le_qSet H
  have h2 : (qSet H).ncard ≤ ∑ x ∈ xRange H,
      ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
        (2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1) := by
    refine ncard_le_sum_fiber (qSet H) (qSet_finite H) (xRange H)
      (fun x => ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
        (2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1)) ?_ ?_
    · intro p hp
      rw [mem_xRange]
      exact hp.1
    · intro x _
      exact qSet_fiber_le H x
  have hq : (∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
        ((4 * H / radZ (x ^ 2 - 4 * d) : ℕ) : ℝ)) ≤ 4 * (H : ℝ) * Ssum H := by
    calc (∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
          ((4 * H / radZ (x ^ 2 - 4 * d) : ℕ) : ℝ))
        ≤ ∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
            4 * (H : ℝ) * gZ (x ^ 2 - 4 * d) := by
          apply Finset.sum_le_sum; intro x _
          apply Finset.sum_le_sum; intro d hd
          rw [Finset.mem_filter] at hd
          have h4H : (((4 * H : ℕ) / radZ (x ^ 2 - 4 * d) : ℕ) : ℝ)
              ≤ ((4 * H : ℕ) : ℝ) / ((radZ (x ^ 2 - 4 * d) : ℕ) : ℝ) := Nat.cast_div_le
          have hcast : ((4 * H : ℕ) : ℝ) = 4 * (H : ℝ) := by push_cast; ring
          rw [hcast] at h4H
          rw [gZ_eq _ hd.2]
          refine h4H.trans (le_of_eq ?_)
          ring
      _ ≤ ∑ x ∈ xRange H, ∑ d ∈ dRange H, 4 * (H : ℝ) * gZ (x ^ 2 - 4 * d) := by
          apply Finset.sum_le_sum; intro x _
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro i _ _
          exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg H)) (gZ_nonneg (x ^ 2 - 4 * i))
      _ = 4 * (H : ℝ) * Ssum H := by
          rw [Ssum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x _
          rw [Finset.mul_sum]
  have hc : (∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0), (1 : ℝ))
      ≤ (((8 * H + 1) * (2 * H + 1) : ℕ) : ℝ) := by
    calc (∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0), (1 : ℝ))
        ≤ ∑ x ∈ xRange H, ((2 * H + 1 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum; intro x _
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) ?_
          rw [dRange_card]
      _ = (((8 * H + 1) * (2 * H + 1) : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, xRange_card]
          push_cast; ring
  have h3 : ((∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
        (2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1) : ℕ) : ℝ)
      ≤ (2 * (H : ℝ) + 1) *
        (4 * (H : ℝ) * (500 * (H : ℝ) + 100) + (((8 * H + 1) * (2 * H + 1) : ℕ) : ℝ)) := by
    have hcast2 : ((2 * H + 1 : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
    have step1 : ((∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
          (2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1) : ℕ) : ℝ)
        ≤ (2 * (H : ℝ) + 1) * (∑ x ∈ xRange H,
            ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
            (((4 * H / radZ (x ^ 2 - 4 * d) : ℕ) : ℝ) + 1)) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_le_sum; intro d _
      have hpt : (((2 * H + 1) * (4 * H / radZ (x ^ 2 - 4 * d) + 1) : ℕ) : ℝ)
          = ((2 * H + 1 : ℕ) : ℝ) * (((4 * H / radZ (x ^ 2 - 4 * d) : ℕ) : ℝ) + 1) := by
        push_cast; ring
      rw [hpt, hcast2]
    have step2 : (∑ x ∈ xRange H, ∑ d ∈ (dRange H).filter (fun d => x ^ 2 - 4 * d ≠ 0),
            (((4 * H / radZ (x ^ 2 - 4 * d) : ℕ) : ℝ) + 1))
        ≤ 4 * (H : ℝ) * Ssum H + (((8 * H + 1) * (2 * H + 1) : ℕ) : ℝ) := by
      simp only [Finset.sum_add_distrib]
      linarith [hq, hc]
    refine le_trans step1 ?_
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hS : 4 * (H : ℝ) * Ssum H ≤ 4 * (H : ℝ) * (500 * (H : ℝ) + 100) :=
      mul_le_mul_of_nonneg_left (Ssum_le H) (by positivity)
    linarith [step2, hS]
  have h4 : (2 * (H : ℝ) + 1) *
        (4 * (H : ℝ) * (500 * (H : ℝ) + 100) + (((8 * H + 1) * (2 * H + 1) : ℕ) : ℝ))
      ≤ 8000 * ((H : ℝ) + 1) ^ 3 := by
    have hh : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hcast : (((8 * H + 1) * (2 * H + 1) : ℕ) : ℝ) = (8 * (H:ℝ) + 1) * (2 * (H:ℝ) + 1) := by
      push_cast; ring
    rw [hcast]
    have h1 : 2 * (H:ℝ) + 1 ≤ 3 * ((H:ℝ) + 1) := by linarith
    have h2 : 4 * (H:ℝ) * (500 * (H:ℝ) + 100) + (8 * (H:ℝ) + 1) * (2 * (H:ℝ) + 1)
        ≤ 2427 * ((H:ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (H:ℝ), hh]
    have h3' : (0:ℝ) ≤ 4 * (H:ℝ) * (500 * (H:ℝ) + 100) + (8 * (H:ℝ) + 1) * (2 * (H:ℝ) + 1) := by
      nlinarith [hh]
    calc (2 * (H:ℝ) + 1) * (4 * (H:ℝ) * (500 * (H:ℝ) + 100) + (8 * (H:ℝ) + 1) * (2 * (H:ℝ) + 1))
        ≤ (3 * ((H:ℝ) + 1)) * (2427 * ((H:ℝ) + 1) ^ 2) := by
          apply mul_le_mul h1 h2 h3' (by positivity)
      _ = 7281 * ((H:ℝ) + 1) ^ 3 := by ring
      _ ≤ 8000 * ((H:ℝ) + 1) ^ 3 := by
          have h0 : (0:ℝ) ≤ ((H:ℝ) + 1) ^ 3 := by positivity
          linarith
  have h5 : ((qSet H).ncard : ℝ) ≤ 8000 * ((H : ℝ) + 1) ^ 3 :=
    le_trans (Nat.cast_le.mpr h2) (le_trans h3 h4)
  exact le_trans (Nat.cast_le.mpr h1) h5

/-- **The `symmBox` bound**: `#symmBox H ≤ 8400 (H+1)^3`. -/
theorem symmBox_ncard_le (H : ℕ) : ((symmBox H).ncard : ℝ) ≤ 8400 * ((H : ℝ) + 1) ^ 3 := by
  have h1 : (symmBox H).ncard ≤ (symmDiag H).ncard + (symmOff H).ncard := by
    have hfin : (symmDiag H ∪ symmOff H).Finite :=
      (symmBox_finite H).subset (by
        rintro t (ht | ht) <;> exact (ht.1 : t ∈ symmBox H))
    exact le_trans (Set.ncard_le_ncard (symmBox_subset_diag_union_off H) hfin)
      (Set.ncard_union_le _ _)
  have h2 : ((symmDiag H).ncard : ℝ) ≤ 400 * ((H : ℝ) + 1) ^ 3 := by
    have hh := symmDiag_ncard_le H
    have h2' : ((400 * (H + 1) ^ 3 : ℕ) : ℝ) = 400 * ((H : ℝ) + 1) ^ 3 := by push_cast; ring
    calc ((symmDiag H).ncard : ℝ) ≤ ((400 * (H + 1) ^ 3 : ℕ) : ℝ) := Nat.cast_le.mpr hh
      _ = 400 * ((H : ℝ) + 1) ^ 3 := h2'
  have h3 := symmOff_ncard_le H
  have h1' : ((symmBox H).ncard : ℝ) ≤ ((symmDiag H).ncard : ℝ) + ((symmOff H).ncard : ℝ) := by
    have hh := Nat.cast_le (α := ℝ).mpr h1
    push_cast at hh
    exact hh
  linarith [h1', h2, h3]

/-- **`#symmBox H = O(H^3)`.** -/
theorem symmBox_isBigO :
    (fun H : ℕ => ((symmBox H).ncard : ℝ)) =O[atTop] (fun H : ℕ => (H : ℝ) ^ 3) := by
  have h := Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow 3 67200
    (fun H => (symmBox H).ncard) ?_
  · simpa using h
  · filter_upwards [Filter.eventually_ge_atTop 1] with H hH
    have h3 := symmBox_ncard_le H
    have h1H : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hcube : ((H : ℝ) + 1) ^ 3 ≤ 8 * (H : ℝ) ^ 3 := by
      nlinarith [h1H, sq_nonneg (H : ℝ), mul_nonneg (by linarith : (0:ℝ) ≤ (H:ℝ)) (sq_nonneg (H:ℝ))]
    have hgoal : ((symmBox H).ncard : ℝ) ≤ ((67200 * H ^ 3 : ℕ) : ℝ) := by
      have hcast : ((67200 * H ^ 3 : ℕ) : ℝ) = (67200 : ℝ) * (H : ℝ) ^ 3 := by push_cast; ring
      rw [hcast]
      linarith
    exact (Nat.cast_le (α := ℝ)).mp hgoal

/-! ### The `n = 4` imprimitive input -/

/-- **Every imprimitive quartic in the box contributes to `symmBox`**: the injection sends `f`
to `(z, coeff 3, coeff 1, coeff 0, coeff 2 - z)`, where `z` is an integer root of the cubic
resolvent. -/
theorem ImprimitiveBad_four_le_symmBox (H : ℕ) :
    (ImprimitiveBad 4 H).ncard ≤ (symmBox H).ncard := by
  classical
  let Z : ℤ[X] → ℤ := fun f => if hf : f ∈ ImprimitiveBad 4 H then
    Classical.choose (quartic_imprimitive_resolvent_root H f hf) else 0
  have hZmem : ∀ f (hf : f ∈ ImprimitiveBad 4 H), |Z f| ≤ 4 * (H : ℤ) := by
    intro f hf
    have hz : Z f = Classical.choose (quartic_imprimitive_resolvent_root H f hf) := by
      simp only [Z]; rw [dif_pos hf]
    rw [hz]
    exact (Classical.choose_spec (quartic_imprimitive_resolvent_root H f hf)).1
  have hZres : ∀ f (hf : f ∈ ImprimitiveBad 4 H),
      (resolventCubic (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)).eval (Z f) = 0 := by
    intro f hf
    have hz : Z f = Classical.choose (quartic_imprimitive_resolvent_root H f hf) := by
      simp only [Z]; rw [dif_pos hf]
    rw [hz]
    exact (Classical.choose_spec (quartic_imprimitive_resolvent_root H f hf)).2
  refine Set.ncard_le_ncard_of_injOn
    (f := fun f : ℤ[X] => (Z f, f.coeff 3, f.coeff 1, f.coeff 0, f.coeff 2 - Z f)) ?_ ?_
    (symmBox_finite H)
  · intro f hf
    obtain ⟨hm, hdeg, hcoef⟩ := (Bad_subset_Box 4 H (irreducibleBad_subset_Bad 4 H hf.1))
    refine ⟨hZmem f hf, hcoef 3 (by norm_num), hcoef 1 (by norm_num), hcoef 0 (by norm_num),
      ?_, ?_⟩
    · have h1 : |Z f| ≤ 4 * (H : ℤ) := hZmem f hf
      have h2 : |f.coeff 2| ≤ (H : ℤ) := hcoef 2 (by norm_num)
      calc |f.coeff 2 - Z f| ≤ |f.coeff 2| + |Z f| := abs_sub _ _
        _ ≤ (H : ℤ) + 4 * (H : ℤ) := add_le_add h2 h1
        _ = 5 * (H : ℤ) := by ring
    · have h := four_mul_resolventCubic_eval (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (Z f)
      rw [hZres f hf, mul_zero] at h
      show (Z f ^ 2 - 4 * f.coeff 0) * (f.coeff 3 ^ 2 - 4 * (f.coeff 2 - Z f))
          = (Z f * f.coeff 3 - 2 * f.coeff 1) ^ 2
      linarith [h]
  · rintro f hf f' hf' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hz', h3, h1, h0, h2⟩ := heq
    have h2' : f.coeff 2 = f'.coeff 2 := by linarith
    obtain ⟨hm, hdegD, -⟩ := (Bad_subset_Box 4 H (irreducibleBad_subset_Bad 4 H hf.1))
    obtain ⟨hm', hdegD', -⟩ := (Bad_subset_Box 4 H (irreducibleBad_subset_Bad 4 H hf'.1))
    have hdeg : f.natDegree = 4 := Polynomial.natDegree_eq_of_degree_eq_some hdegD
    have hdeg' : f'.natDegree = 4 := Polynomial.natDegree_eq_of_degree_eq_some hdegD'
    refine Polynomial.ext fun k => ?_
    rcases lt_or_ge k 4 with hk | hk
    · interval_cases k
      · exact h0
      · exact h1
      · exact h2'
      · exact h3
    · rcases eq_or_lt_of_le hk with hk4 | hk5
      · rw [← hk4]
        have e1 : f.coeff 4 = 1 := by rw [← hdeg]; exact hm.coeff_natDegree
        have e2 : f'.coeff 4 = 1 := by rw [← hdeg']; exact hm'.coeff_natDegree
        rw [e1, e2]
      · have hlt : f.natDegree < k := by rw [hdeg]; omega
        have hlt' : f'.natDegree < k := by rw [hdeg']; omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt']

/-- **The `n = 4` imprimitive input is a theorem**: `#ImprimitiveBad 4 H = O(H^3)`. -/
theorem ImprimitiveBad_four_isBigO :
    (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ)) =O[atTop] (fun H : ℕ => (H : ℝ) ^ 3) := by
  have h1 : (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((symmBox H).ncard : ℝ)) :=
    Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _
      (Filter.Eventually.of_forall fun H => ImprimitiveBad_four_le_symmBox H)
  exact h1.trans symmBox_isBigO

end

end Submission.Vdw

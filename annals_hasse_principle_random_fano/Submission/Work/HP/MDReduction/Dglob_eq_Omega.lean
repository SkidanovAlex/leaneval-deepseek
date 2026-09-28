/-
# The reduction `Dglob = ¼ Σ_Ω S*₀`

For a family `f_a(x) = ⟨a, ν_{d,n}(x)⟩` of degree-`d` forms and a height parameter `B`,
let

* `NV a B = ½ · #{x ∈ Ξ_{d,n}(B) : f_a(x) = 0}`  be the (projective) count of zeros of `f_a`
  of height at most `B`;
* `Dglob A B = Σ_{a ∈ primSet A} (NV a B ^ 2 - NV a B)` be the "diagonal-removed" second
  moment of that count over primitive coefficient vectors of norm at most `A`.

The lemma proved here is the elementary double-counting identity

  `Dglob A B = ¼ · Σ_{(x,y) ∈ Ω(B)} #{a ∈ primSet A : f_a(x) = 0 ∧ f_a(y) = 0}`

where `Ω(B)` is the set of *ordered pairs* `(x,y)` of primitive vectors of height `≤ B` with
`x ≠ y` and `x ≠ -y`.

The reason behind the factor `1/4`: for a fixed `a` let `Z = Z(a) ⊆ Ξ(B)` be its set of zeros
and `k = #Z`.  Since `Ξ` (hence `Z`) is stable under `x ↦ -x` and `0 ∉ Ξ`, the ordered pairs
`(x,y) ∈ Z × Z` split into the diagonal `x = y` (`k` pairs), the anti-diagonal `x = -y`
(`k` pairs) and the rest, so

  `#{p ∈ Ω(B) : f_a(p₁) = f_a(p₂) = 0} = k^2 - 2k = (2·NV a B)^2 - 2·(2·NV a B)`,

which gives `NV a B ^ 2 - NV a B = ¼ · #(…)`.  Summing over `a` and exchanging the order of
summation (a finite Fubini argument) yields the statement.

## Main declarations

* `Work.HP.MDReduction.not_IsPrim_zero` : `0` is not primitive.
* `Work.HP.MDReduction.neg_mem_Xi_iff` : `Ξ` is stable under `x ↦ -x`.
* `Work.HP.MDReduction.card_pairs_ne_pm` : the pair count `k² = k + k + #{(x,y) : x ≠ ±y}`.
* `Work.HP.MDReduction.sum_ncard_filter_comm` : finite Fubini for `ncard` of filter sets.
* `Work.HP.MDReduction.NV_sq_sub_NV` : the per-`a` identity above.
* `Work.HP.MDReduction.Dglob_eq_Omega` : the reduction.
-/

import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDReduction.formEval_neg

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.MDReduction

open Work.HP

/-! ## Elementary helpers -/

/-- The zero vector is never primitive. -/
theorem not_IsPrim_zero (n : ℕ) : ¬ IsPrim (0 : Fin (n + 1) → ℤ) := by
  have hzero : (Finset.univ : Finset (Fin (n + 1))).gcd (0 : Fin (n + 1) → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (by simp)
  intro h
  unfold IsPrim at h
  rw [hzero] at h
  exact zero_ne_one h

/-- The height ball `Ξ_{d,n}(B)` is stable under `x ↦ -x`. -/
theorem neg_mem_Xi_iff (d n : ℕ) (B : ℝ) (x : Fin (n + 1) → ℤ) :
    -x ∈ Xi d n B ↔ x ∈ Xi d n B := by
  simp only [Xi, Set.mem_ofPred_eq, IsPrim_neg, eNorm_neg]

/-- For a negation-stable finite set `s` not containing `0`, the ordered pairs from `s` that
avoid both the diagonal and the anti-diagonal are `#s ^ 2 - 2 * #s` in number. -/
theorem card_pairs_ne_pm {ι : Type*} [Fintype ι] (s : Finset (ι → ℤ))
    (hsym : ∀ x ∈ s, -x ∈ s) (h0 : (0 : ι → ℤ) ∉ s) :
    ((s ×ˢ s).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card + 2 * s.card = s.card ^ 2 := by
  classical
  have hdisj : Disjoint ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = p.2))
      ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = -p.2)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_product] at ha hb
    have h2 : a.2 = -a.2 := by
      have h1 : a.2 = a.1 := ha.2.symm
      have h3 : a.1 = b.1 := by rw [hab]
      have h4 : b.1 = -b.2 := hb.2
      have h5 : -b.2 = -a.2 := by rw [hab]
      exact h1.trans (h3.trans (h4.trans h5))
    have hz : a.2 = 0 := by
      funext i
      have hi : a.2 i = -(a.2 i) := congrFun h2 i
      simp only [Pi.zero_apply]
      linarith
    exact h0 (hz ▸ ha.1.2)
  have hA1 : ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = p.2)).card = s.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p hp q hq heq
      simp only [Finset.mem_filter, Finset.mem_product] at hp hq
      rw [Prod.ext_iff]
      exact ⟨heq, neg_inj.mp (by rw [← hp.2, heq, hq.2])⟩
    · intro x hx
      exact ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩, rfl⟩
  have hA2 : ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = -p.2)).card = s.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p hp q hq heq
      simp only [Finset.mem_filter, Finset.mem_product] at hp hq
      rw [Prod.ext_iff]
      exact ⟨heq, neg_inj.mp (by rw [← hp.2, heq, hq.2])⟩
    · intro x hx
      exact ⟨(x, -x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hsym x hx⟩,
        by simp⟩, rfl⟩
  have hbad : ((s ×ˢ s).filter
        (fun p : (ι → ℤ) × (ι → ℤ) => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2))).card
      = ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = p.2)).card
        + ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = -p.2)).card := by
    have heq : ((s ×ˢ s).filter
          (fun p : (ι → ℤ) × (ι → ℤ) => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2)))
        = ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = p.2 ∨ p.1 = -p.2)) := by
      ext p
      simp only [Finset.mem_filter]
      tauto
    rw [heq, Finset.filter_or, Finset.card_union_of_disjoint hdisj]
  have htotal : ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card
      + (((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = p.2)).card
        + ((s ×ˢ s).filter (fun p : (ι → ℤ) × (ι → ℤ) => p.1 = -p.2)).card)
      = s.card * s.card := by
    rw [← hbad, Finset.card_filter_add_card_filter_not (s := s ×ˢ s)
      (p := fun p : (ι → ℤ) × (ι → ℤ) => p.1 ≠ p.2 ∧ p.1 ≠ -p.2), Finset.card_product]
  rw [hA1, hA2] at htotal
  rw [pow_two, two_mul]
  exact htotal

/-- Finite Fubini for `ncard` of filtered sets. -/
theorem sum_ncard_filter_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) (R : α → β → Prop) :
    ∑ a ∈ hs.toFinset, (({b ∈ t | R a b} : Set β).ncard : ℝ)
      = ∑ b ∈ ht.toFinset, (({a ∈ s | R a b} : Set α).ncard : ℝ) := by
  classical
  have hmem1 : ∀ a, ({b ∈ t | R a b} : Set β) = ↑(ht.toFinset.filter (R a)) := by
    intro a
    ext b
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
  have hmem2 : ∀ b, ({a ∈ s | R a b} : Set α) = ↑(hs.toFinset.filter (fun a => R a b)) := by
    intro b
    ext a
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
  have e1 : (∑ a ∈ hs.toFinset, (({b ∈ t | R a b} : Set β).ncard : ℝ))
      = ∑ a ∈ hs.toFinset, ∑ b ∈ ht.toFinset, (if R a b then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [hmem1 a, Set.ncard_coe_finset]
    exact Finset.natCast_card_filter (R a) ht.toFinset
  have e2 : (∑ a ∈ hs.toFinset, ∑ b ∈ ht.toFinset, (if R a b then (1 : ℝ) else 0))
      = ∑ b ∈ ht.toFinset, ∑ a ∈ hs.toFinset, (if R a b then (1 : ℝ) else 0) :=
    Finset.sum_comm
  have e3 : (∑ b ∈ ht.toFinset, ∑ a ∈ hs.toFinset, (if R a b then (1 : ℝ) else 0))
      = ∑ b ∈ ht.toFinset, (({a ∈ s | R a b} : Set α).ncard : ℝ) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hmem2 b, Set.ncard_coe_finset]
    exact (Finset.natCast_card_filter (fun a => R a b) hs.toFinset).symm
  exact e1.trans (e2.trans e3)

/-! ## The per-form identity -/

/-- For a single form `f_a`: `NV^2 - NV = ¼ · #{pairs (x,y) ∈ Ω with f_a(x) = f_a(y) = 0}`. -/
theorem NV_sq_sub_NV (d n : ℕ) (B : ℝ) (a : Mon d n → ℤ) :
    NV d n a B ^ 2 - NV d n a B =
      (1 / 4) * (({p ∈ Omega d n B | formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
        Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).ncard : ℝ) := by
  classical
  have hXfin : (Xi d n B).Finite := (Work.HP.MDBasic.finite_sets d n 0 B (fun _ => True)).2.1
  have hNV : NV d n a B = (1 / 2) * (({x ∈ Xi d n B | formEval d n a x = 0} :
      Set (Fin (n + 1) → ℤ)).ncard : ℝ) := rfl
  rw [hNV]
  have hZeq : ({x ∈ Xi d n B | formEval d n a x = 0} : Set (Fin (n + 1) → ℤ))
      = ↑(hXfin.toFinset.filter (fun x => formEval d n a x = 0)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
  simp only [hZeq, Set.ncard_coe_finset]
  set Zf : Finset (Fin (n + 1) → ℤ) := hXfin.toFinset.filter (fun x => formEval d n a x = 0)
    with hZf
  have hZfmem : ∀ x, x ∈ Zf ↔ x ∈ Xi d n B ∧ formEval d n a x = 0 := by
    intro x
    simp only [hZf, Finset.mem_filter, Set.Finite.mem_toFinset]
  have hsym : ∀ x ∈ Zf, -x ∈ Zf := by
    intro x hx
    simp only [hZfmem] at hx ⊢
    exact ⟨(neg_mem_Xi_iff d n B x).mpr hx.1, by
      simp only [formEval_neg d n a x, hx.2, mul_zero]⟩
  have h0 : (0 : Fin (n + 1) → ℤ) ∉ Zf := by
    simp only [hZfmem, Xi, Set.mem_ofPred_eq]
    rintro ⟨h, -⟩
    exact not_IsPrim_zero n h.1
  have hQncard : ({p ∈ Omega d n B | formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
        Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).ncard
      = ((Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card := by
    have hset : ({p ∈ Omega d n B | formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
        Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)))
        = ↑((Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)) := by
      ext p
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        hZfmem, Omega]
      tauto
    simp only [hset, Set.ncard_coe_finset]
  have hcard : ((Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card
      + 2 * Zf.card = Zf.card ^ 2 := card_pairs_ne_pm Zf hsym h0
  have hc : (((Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card : ℝ)
      = (Zf.card : ℝ) ^ 2 - 2 * (Zf.card : ℝ) := by
    have hcast : (((Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card : ℝ)
        + 2 * (Zf.card : ℝ) = (Zf.card : ℝ) ^ 2 := by
      exact_mod_cast hcard
    linarith
  simp only [hQncard, hc]
  ring

/-! ## The main reduction -/

theorem Dglob_eq_Omega (d n : ℕ) (A B : ℝ) :
    Dglob d n A B = (1 / 4) * ∑ᶠ p ∈ Omega d n B,
      (({a ∈ primSet d n A (fun _ => True) |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} : Set (Mon d n → ℤ)).ncard : ℝ) := by
  classical
  obtain ⟨hPfin, -, hOfin⟩ := Work.HP.MDBasic.finite_sets d n A B (fun _ => True)
  have hDglob : Dglob d n A B
      = ∑ᶠ a ∈ primSet d n A (fun _ => True), (NV d n a B ^ 2 - NV d n a B) := rfl
  have hstep2 : (∑ᶠ a ∈ primSet d n A (fun _ => True), (NV d n a B ^ 2 - NV d n a B))
      = ∑ a ∈ hPfin.toFinset, (NV d n a B ^ 2 - NV d n a B) :=
    finsum_mem_eq_finite_toFinset_sum _ hPfin
  have hstep3 : (∑ a ∈ hPfin.toFinset, (NV d n a B ^ 2 - NV d n a B))
      = ∑ a ∈ hPfin.toFinset, (1 / 4) * (({p ∈ Omega d n B |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
          Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).ncard : ℝ) :=
    Finset.sum_congr rfl (fun a _ => NV_sq_sub_NV d n B a)
  have hstep4 : (∑ a ∈ hPfin.toFinset, (1 / 4) * (({p ∈ Omega d n B |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
          Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).ncard : ℝ))
      = (1 / 4) * ∑ a ∈ hPfin.toFinset, (({p ∈ Omega d n B |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
          Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).ncard : ℝ) :=
    (Finset.mul_sum _ _ _).symm
  have hstep5 : ((1 / 4) * ∑ a ∈ hPfin.toFinset, (({p ∈ Omega d n B |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} :
          Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).ncard : ℝ))
      = (1 / 4) * ∑ p ∈ hOfin.toFinset, (({a ∈ primSet d n A (fun _ => True) |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} : Set (Mon d n → ℤ)).ncard : ℝ) :=
    congrArg (fun x => (1 / 4) * x)
      (sum_ncard_filter_comm (s := primSet d n A (fun _ => True)) (t := Omega d n B)
        (R := fun a p => formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0) hPfin hOfin)
  have hstep6 : ((1 / 4) * ∑ p ∈ hOfin.toFinset, (({a ∈ primSet d n A (fun _ => True) |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} : Set (Mon d n → ℤ)).ncard : ℝ))
      = (1 / 4) * ∑ᶠ p ∈ Omega d n B, (({a ∈ primSet d n A (fun _ => True) |
          formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} : Set (Mon d n → ℤ)).ncard : ℝ) :=
    congrArg (fun x => (1 / 4) * x) (finsum_mem_eq_finite_toFinset_sum _ hOfin).symm
  exact hDglob.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans hstep6))))

end Work.HP.MDReduction

import Mathlib
import Submission.Work.BMF.kdr_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VU

open Finset
open scoped BigOperators
open Work.BMF

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000

/-- The index shift `i ↦ i + 1` from `Fin P` into `{1, …, P}`, on pairs. -/
private def shiftPair (P : ℕ) : Fin P × Fin P → ℕ × ℕ :=
  fun p => ((p.1:ℕ)+1, (p.2:ℕ)+1)

private lemma shiftPair_injective (P : ℕ) : Function.Injective (shiftPair P) := by
  intro a b hab
  simp only [shiftPair, Prod.mk.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  have e1 : a.1 = b.1 := by
    apply Fin.ext
    have : (a.1 : ℕ) = (b.1 : ℕ) := by omega
    exact this
  have e2 : a.2 = b.2 := by
    apply Fin.ext
    have : (a.2 : ℕ) = (b.2 : ℕ) := by omega
    exact this
  exact Prod.ext e1 e2

/-- Turning the `Fin (k-1)`-indexed agreement condition (indices `1, …, k-1`) into the
`ℕ`-indexed one used in `Nset`. -/
private lemma nset_bridge_fin_to_nat {k : ℕ} (_hk : 1 ≤ k) {a b : ℕ} {f : ℝ → ℝ} {H : ℝ}
    (h : ∀ j : Fin (k - 1), ∃ z : ℤ,
      |iteratedDeriv ((j:ℕ)+1) f (a:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
       - iteratedDeriv ((j:ℕ)+1) f (b:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) - (z:ℝ)|
        ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) :
    ∃ z : ℤ,
      |iteratedDeriv j f (a:ℝ) / (Nat.factorial j : ℝ)
       - iteratedDeriv j f (b:ℝ) / (Nat.factorial j : ℝ) - (z:ℝ)|
        ≤ 2 * H ^ (-(j : ℝ)) := by
  obtain ⟨z, hz⟩ := h ⟨j - 1, by omega⟩
  refine ⟨z, ?_⟩
  have hjeq : (↑(⟨j - 1, by omega⟩ : Fin (k - 1)) : ℕ) + 1 = j := by
    rw [Fin.val_mk]; omega
  simpa [hjeq] using hz

/-- Membership of an explicit pair `(a,b)` with `a,b ∈ {1,…,P}` in `Nset k P f H`, from the
`Fin (k-1)`-indexed agreement condition. -/
private lemma mem_nset_pair {k P : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ} {H : ℝ} {a b : ℕ}
    (ha : a ∈ Finset.Icc 1 P) (hb : b ∈ Finset.Icc 1 P)
    (h : ∀ j : Fin (k - 1), ∃ z : ℤ,
      |iteratedDeriv ((j:ℕ)+1) f (a:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
       - iteratedDeriv ((j:ℕ)+1) f (b:ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) - (z:ℝ)|
        ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ))) :
    (a, b) ∈ Nset k P f H := by
  simp only [Nset, Set.mem_ofPred_eq]
  exact ⟨ha, hb, fun j hj1 hjk => nset_bridge_fin_to_nat hk h j hj1 hjk⟩

/-- Core counting statement for an arbitrary set `S` of pairs satisfying the agreement
condition; the map `p ↦ (p.1+1, p.2+1)` injects `S` into `Nset k P f H`. -/
private lemma nset_count_bridge_aux (k P : ℕ) (hk : 2 ≤ k) (f : ℝ → ℝ) (H : ℝ)
    (S : Finset (Fin P × Fin P))
    (hS : ∀ p ∈ S, ∀ j : Fin (k-1), ∃ z : ℤ,
        |iteratedDeriv ((j:ℕ)+1) f ((p.1:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
         - iteratedDeriv ((j:ℕ)+1) f ((p.2:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) - (z:ℝ)|
          ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ))) :
    (S.card : ℝ) ≤ ((Nset k P f H).ncard : ℝ) := by
  have hmem : ∀ p ∈ S, shiftPair P p ∈ Nset k P f H := by
    intro p hp
    show ((p.1:ℕ)+1, (p.2:ℕ)+1) ∈ Nset k P f H
    refine mem_nset_pair (k := k) (P := P) (by omega) (f := f) (H := H)
      (Finset.mem_Icc.mpr ⟨by omega, by have := p.1.isLt; omega⟩)
      (Finset.mem_Icc.mpr ⟨by omega, by have := p.2.isLt; omega⟩) ?_
    intro j
    obtain ⟨z, hz⟩ := hS p hp j
    exact ⟨z, by simpa only [Nat.cast_add, Nat.cast_one] using hz⟩
  have hsub : ((S.image (shiftPair P) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) ⊆ Nset k P f H := by
    intro mn hmn
    rw [Finset.mem_coe, Finset.mem_image] at hmn
    obtain ⟨p, hp, rfl⟩ := hmn
    exact hmem p hp
  have hfin : (Nset k P f H).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc 1 P ×ˢ Finset.Icc 1 P)) ?_
    intro mn hmn
    simp only [Nset, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_product,
      Finset.mem_Icc] at hmn ⊢
    exact ⟨hmn.1, hmn.2.1⟩
  have hle : ((S.image (shiftPair P) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).ncard
      ≤ (Nset k P f H).ncard := Set.ncard_le_ncard hsub hfin
  have hcard : ((S.image (shiftPair P) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).ncard = S.card := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (shiftPair_injective P)]
  have hnat : S.card ≤ (Nset k P f H).ncard := by
    rw [← hcard]
    exact hle
  exact_mod_cast hnat

/-- **Counting bridge.** The number of pairs of indices `i, i' ∈ {1,…,P}`, indexed here by
`Fin P` through `i ↦ i + 1`, whose normalised derivatives `f^{(j)}(·)/j!` agree within `2 H^{-j}`
modulo `1` for all `1 ≤ j ≤ k-1`, is at most the cardinality of Heath-Brown's set
`Nset k P f H`: the map `(i,i') ↦ (i+1, i'+1)` is an injection into `Nset`, which is finite as a
subset of `Icc 1 P × Icc 1 P` (`Set.ncard_le_ncard`). Note `(j : Fin (k-1))` has
`(j : ℕ) + 1 ∈ {1, …, k-1}` and the two side conditions have literally the same formula.
All auxiliary lemmas you introduce must be marked `private` (or given a name unique to this file)
so that they cannot clash with sibling files. -/
theorem nset_count_bridge (k P : ℕ) (hk : 2 ≤ k) (f : ℝ → ℝ) (H : ℝ) :
    ((Finset.univ.filter (fun p : Fin P × Fin P =>
        ∀ j : Fin (k-1), ∃ z : ℤ,
          |iteratedDeriv ((j:ℕ)+1) f ((p.1:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
           - iteratedDeriv ((j:ℕ)+1) f ((p.2:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) - (z:ℝ)|
            ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)))).card : ℝ)
      ≤ ((Nset k P f H).ncard : ℝ) := by
  refine nset_count_bridge_aux k P hk f H
    (Finset.univ.filter (fun p : Fin P × Fin P =>
      ∀ j : Fin (k-1), ∃ z : ℤ,
        |iteratedDeriv ((j:ℕ)+1) f ((p.1:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ)
         - iteratedDeriv ((j:ℕ)+1) f ((p.2:ℕ)+1 : ℝ) / (Nat.factorial ((j:ℕ)+1) : ℝ) - (z:ℝ)|
          ≤ 2 * H ^ (-(((j:ℕ)+1 : ℕ) : ℝ)))) ?_
  intro p hp
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp

end Work.BMF.VU

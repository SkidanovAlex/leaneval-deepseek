/-
# AREA COPR — Bender 1981, 1.1(i) in the ambient-group formulation

For a `p`-group `P` acting coprimely on a `p'`-group `K` (all subgroups of one finite group `G`,
action by conjugation, `P ≤ N_G(K)`):

* `commutator_iterated_eq` : `[[K,P],P] = [K,P]`;
* `commutator_sup_fixed_eq_top` : `[P,K] ⊔ C_K(P) = K`;
* `coprime11i_iterated`, `coprime11i_split` : the two conjuncts of `Work.GW2.Coprime11iProp`.

Both are transported from the FT-closure theorems
`OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one_of_coprime` (Isaacs Lemma 4.29, the
unconditional coprime form `[G,A,A] = [G,A]`) and
`OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top` (Isaacs Lemma 4.28,
`G = C_G(A)·[G,A]`; solvability of `A` is supplied by `P` being a `p`-group) via the bridges of
`Submission.Work.COPR.Glue`.
-/
import Submission.Work.COPR.Glue

namespace Work.COPR

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Bender 1981, 1.1(i), first part, ambient form: `[[K,P],P] = [K,P]`. -/
theorem commutator_iterated_eq (p : ℕ) [Fact p.Prime] (P K : Subgroup G) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card K)) (hN : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  have hcard : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K) := coprime_card_of_isPGroup p hP hcop
  have h := OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_two_eq_one_of_coprime
      (A := ↥P) (G := ↥K) (φ := conjAct P K hN) hcard
  have hmap := congrArg (Subgroup.map (semidirectToAmbient P K hN)) h
  rw [iterCommutator_map_semidirectToAmbient P K hN 2,
      iterCommutator_two,
      iterCommutator_map_semidirectToAmbient P K hN 1,
      iterCommutator_one] at hmap
  exact hmap

/-- Bender 1981, 1.1(i), second part, ambient form: `[P,K] ⊔ C_K(P) = K`. -/
theorem commutator_sup_fixed_eq_top (p : ℕ) [Fact p.Prime] (P K : Subgroup G) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card K)) (hN : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅P, K⁆ ⊔ (K ⊓ Subgroup.centralizer (P : Set G)) = K := by
  have hcard : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K) := coprime_card_of_isPGroup p hP hcop
  have hsolv : Group.IsSolvable ↥P := isSolvable_of_isPGroup p hP
  have h := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      (A := ↥P) (G := ↥K) (φ := conjAct P K hN) hcard (Or.inl hsolv)
  have hmap := congrArg (Subgroup.map K.subtype) h
  rw [Subgroup.map_sup, fixedPoints_conjAct_map P K hN, actionCommutator_conjAct_map P K hN,
    show (⊤ : Subgroup ↥K).map K.subtype = K from by
      rw [← MonoidHom.range_eq_map K.subtype, Subgroup.range_subtype]] at hmap
  rw [← Subgroup.commutator_comm P K, sup_comm] at hmap
  exact hmap

/-- Bender 1981, 1.1(i) in Bender's own orientation: `[P, [P, K]] = [P, K]`. -/
theorem coprime11i_iterated (p : ℕ) [Fact p.Prime] (P K : Subgroup G) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card K)) (hN : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅P, ⁅P, K⁆⁆ = ⁅P, K⁆ := by
  have h2 : ⁅P, ⁅P, K⁆⁆ = ⁅⁅K, P⁆, P⁆ := by
    rw [Subgroup.commutator_comm P K, Subgroup.commutator_comm P ⁅K, P⁆]
  rw [h2, commutator_iterated_eq p P K hP hcop hN, Subgroup.commutator_comm K P]

/-- Bender 1981, 1.1(i), second part: `K = [P,K]·C_K(P)`. -/
theorem coprime11i_split (p : ℕ) [Fact p.Prime] (P K : Subgroup G) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card K)) (hN : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅P, K⁆ ⊔ (K ⊓ Subgroup.centralizer (P : Set G)) = K :=
  commutator_sup_fixed_eq_top p P K hP hcop hN

end Work.COPR

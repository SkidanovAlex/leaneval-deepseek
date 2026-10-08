/-
# AREA COPR — glue between the ambient-subgroup formulation and the coprime-action API of the
Feit–Thompson closure

The Bender 1.1/1.3/1.5 statements of area COPR are formulated with subgroups of an ambient group
`G` (`P ≤ N_G(K)`, action by conjugation), whereas the FT-closure library
(`Submission/OddOrder/Isaacs/Ch04_Commutators`, `.../Ch06_FrobeniusActions`) works with an abstract
action `φ : A →* MulAut G`.  This file provides the bridge:

* `Work.COPR.conjAct` — the conjugation action `↥P →* MulAut ↥K` for `P ≤ N_G(K)`, and the
  associated `MulDistribMulAction ↥P ↥K`;
* `actionCommutator_conjAct_map`, `fixedPoints_conjAct_map` — the FT lemmas
  `actionCommutator_conj_map_subtype` / `fixedPointsOfMulAut_conj_map_subtype`, restated for
  `conjAct`;
* `coprime_card_of_isPGroup`, `isSolvable_of_isPGroup` — the two `p`-group facts that turn
  «`P` is a `p`-group, `p ∤ |K|`» into the hypotheses of the coprime-action theorems;
* `semidirectToAmbient` — the homomorphism `K ⋊[conjAct] P →* G` (`k p ↦ k p`), with its behaviour
  on `inl`/`inr` and the resulting transport of iterated commutators
  (`iterCommutator_map_semidirectToAmbient`).  This is what converts the FT statement
  `[K,A,A] = [K,A]` inside `↥K ⋊ ↥P` into the ambient `[[K,P],P] = [K,P]`.
-/
import Submission.Work.COPR.Defs
import Submission.OddOrder.Isaacs.Ch04_Commutators.Main
import Submission.OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

namespace Work.COPR

open Subgroup

variable {G : Type*} [Group G]

/-! ## The conjugation action -/

/-- The conjugation action `↥P →* MulAut ↥K`, for `P ≤ N_G(K)`. -/
def conjAct (P K : Subgroup G) (h : P ≤ Subgroup.normalizer (K : Set G)) : ↥P →* MulAut ↥K :=
  (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion h)

/-- The same action, as an `↥P`-action on the group `↥K`. -/
@[instance_reducible]
def conjMulDistribMulAction (P K : Subgroup G) (h : P ≤ Subgroup.normalizer (K : Set G)) :
    MulDistribMulAction ↥P ↥K :=
  MulDistribMulAction.compHom ↥K (conjAct P K h)

/-- Evaluating the conjugation action in the ambient group. -/
theorem conjAct_apply_coe (P K : Subgroup G) (h : P ≤ Subgroup.normalizer (K : Set G))
    (p : ↥P) (x : ↥K) :
    ((conjAct P K h p x : ↥K) : G) = (p : G) * (x : G) * (p : G)⁻¹ := rfl

/-- The `conjMulDistribMulAction`-action is the `conjAct`-action. -/
theorem conjMulDistribMulAction_smul (P K : Subgroup G)
    (h : P ≤ Subgroup.normalizer (K : Set G)) (p : ↥P) (x : ↥K) :
    letI := conjMulDistribMulAction P K h
    (p • x : ↥K) = conjAct P K h p x := rfl

/-! ## Bridges to the coprime-action API of the FT closure -/

/-- The `actionCommutator` of the conjugation action is the ambient commutator `⁅K, P⁆`. -/
theorem actionCommutator_conjAct_map (P K : Subgroup G)
    (h : P ≤ Subgroup.normalizer (K : Set G)) :
    (OddOrder.Isaacs.Ch04.actionCommutator (conjAct P K h)).map K.subtype = ⁅K, P⁆ :=
  OddOrder.Isaacs.Ch04.actionCommutator_conj_map_subtype (P := K) (K := P) h

/-- The fixed points of the conjugation action are `K ⊓ C_G(P)`. -/
theorem fixedPoints_conjAct_map (P K : Subgroup G)
    (h : P ≤ Subgroup.normalizer (K : Set G)) :
    (Subgroup.fixedPointsOfMulAut (conjAct P K h)).map K.subtype =
      K ⊓ Subgroup.centralizer (P : Set G) := by
  have hb : Subgroup.fixedPointsOfMulAut (conjAct P K h) =
      Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion h)) := rfl
  rw [hb, OddOrder.Isaacs.Ch04.fixedPointsOfMulAut_conj_map_subtype (P := K) (K := P) h,
    inf_comm]

/-! ## `p`-group facts -/

/-- If `P` is a `p`-group and `p ∤ |K|`, then `|P|` and `|K|` are coprime; in particular the
conjugation action of `P` on `K` is a coprime action. -/
theorem coprime_card_of_isPGroup (p : ℕ) [Fact p.Prime] {P K : Subgroup G} [Finite G]
    (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card K)) :
    Nat.Coprime (Nat.card P) (Nat.card K) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥P)).mp hP
  rw [hn]
  exact Nat.Coprime.pow_left n hcop

/-- A finite `p`-group is solvable. -/
theorem isSolvable_of_isPGroup (p : ℕ) [Fact p.Prime] {P : Subgroup G} [Finite G]
    (hP : IsPGroup p P) : Group.IsSolvable ↥P :=
  @IsNilpotent.to_isSolvable ↥P _ (hP.isNilpotent)

/-! ## The internal semidirect product `K ⋊[conjAct] P →* G` -/

/-- The homomorphism `↥K ⋊[conjAct P K h] ↥P →* G`, `(k, p) ↦ k * p`.  It realises the internal
product `⟨K, P⟩ ≤ G`; it is used to transport the FT-closure iterated-commutator identities into
the ambient group. -/
def semidirectToAmbient (P K : Subgroup G) (h : P ≤ Subgroup.normalizer (K : Set G)) :
    (↥K ⋊[conjAct P K h] ↥P) →* G :=
  SemidirectProduct.lift K.subtype P.subtype (by
    intro p
    ext x
    simp [conjAct_apply_coe, MulAut.conj_apply])

@[simp]
theorem semidirectToAmbient_inl (P K : Subgroup G) (h : P ≤ Subgroup.normalizer (K : Set G))
    (x : ↥K) : semidirectToAmbient P K h (SemidirectProduct.inl x) = (x : G) := by
  simp [semidirectToAmbient]

@[simp]
theorem semidirectToAmbient_inr (P K : Subgroup G) (h : P ≤ Subgroup.normalizer (K : Set G))
    (p : ↥P) : semidirectToAmbient P K h (SemidirectProduct.inr p) = (p : G) := by
  simp [semidirectToAmbient]

theorem semidirectToAmbient_inl_range (P K : Subgroup G)
    (h : P ≤ Subgroup.normalizer (K : Set G)) :
    (SemidirectProduct.inl : ↥K →* (↥K ⋊[conjAct P K h] ↥P)).range.map
      (semidirectToAmbient P K h) = K := by
  rw [MonoidHom.map_range]
  rw [show (semidirectToAmbient P K h).comp
        (SemidirectProduct.inl : ↥K →* (↥K ⋊[conjAct P K h] ↥P)) = K.subtype from by
      ext x; simp]
  exact Subgroup.range_subtype K

theorem semidirectToAmbient_inr_range (P K : Subgroup G)
    (h : P ≤ Subgroup.normalizer (K : Set G)) :
    (SemidirectProduct.inr : ↥P →* (↥K ⋊[conjAct P K h] ↥P)).range.map
      (semidirectToAmbient P K h) = P := by
  rw [MonoidHom.map_range]
  rw [show (semidirectToAmbient P K h).comp
        (SemidirectProduct.inr : ↥P →* (↥K ⋊[conjAct P K h] ↥P)) = P.subtype from by
      ext x; simp]
  exact Subgroup.range_subtype P

/-- The transport of iterated commutators along `K ⋊[conjAct] P →* G`:
`[K, P, P, …]` inside the semidirect product maps onto the ambient iterated commutator. -/
theorem iterCommutator_map_semidirectToAmbient (P K : Subgroup G)
    (h : P ≤ Subgroup.normalizer (K : Set G)) (n : ℕ) :
    (OddOrder.Isaacs.Ch04.iterCommutator
        (SemidirectProduct.inl : ↥K →* (↥K ⋊[conjAct P K h] ↥P)).range
        (SemidirectProduct.inr : ↥P →* (↥K ⋊[conjAct P K h] ↥P)).range n).map
      (semidirectToAmbient P K h) =
    OddOrder.Isaacs.Ch04.iterCommutator K P n := by
  induction n with
  | zero =>
      rw [OddOrder.Isaacs.Ch04.iterCommutator_zero, OddOrder.Isaacs.Ch04.iterCommutator_zero]
      exact semidirectToAmbient_inl_range P K h
  | succ n ih =>
      rw [OddOrder.Isaacs.Ch04.iterCommutator_succ,
        OddOrder.Isaacs.Ch04.iterCommutator_succ,
        Subgroup.map_commutator, ih, semidirectToAmbient_inr_range P K h]

/-- `iterCommutator E F 1 = ⁅E, F⁆`. -/
@[simp]
theorem iterCommutator_one (E F : Subgroup G) :
    OddOrder.Isaacs.Ch04.iterCommutator E F 1 = ⁅E, F⁆ := by
  show OddOrder.Isaacs.Ch04.iterCommutator E F (0 + 1) = ⁅E, F⁆
  rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, OddOrder.Isaacs.Ch04.iterCommutator_zero]

/-- `iterCommutator E F 2 = ⁅⁅E, F⁆, F⁆`. -/
@[simp]
theorem iterCommutator_two (E F : Subgroup G) :
    OddOrder.Isaacs.Ch04.iterCommutator E F 2 = ⁅⁅E, F⁆, F⁆ := by
  show OddOrder.Isaacs.Ch04.iterCommutator E F (1 + 1) = ⁅⁅E, F⁆, F⁆
  rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, iterCommutator_one]

end Work.COPR

import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.zetaStar_aux
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.Clifford.Basic
import Submission.Work.Clifford.FunAPI
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Clifford.Classes
import Submission.Work.Clifford.card_Irr_eq_card_conjClasses
import Submission.Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Orbit data for Feit's Lemma 3.5 (the class/character count of `Work.ZassenhausTwoGroup`)

Vocabulary for `card_H_classes_eq_card_induced`: the conjugation action of `N = N_G(Q)` on the
irreducible characters of `Q` and on the conjugacy classes of `Q`, the conj ugation of a function
on `Q` by an element of `N`, and the setoid/quotient bookkeeping needed to count orbits.

The action of `N_G(Q)` (rather than of `D = twoPoint H t`) is used for the counting: it is defined
without reference to the rank-one hypothesis `IsSplitRankOne H Q t`, so that the corresponding
`MulAction` instances are global and can be found by type class search in statements.  The two
actions have the same orbits on `Irr Q` and on `ConjClasses Q` (see the main file).

## Contents

* `conjClasses_map_id`, `conjClasses_map_comp` — composition of `ConjClasses.map`;
* `charCore_mem_iff_clifford`, `instFintypeCliffordIrr` — the finset `Work.CharCore.Irr` and the
  set `Work.Clifford.Irr` agree, so the latter is finite;
* `normalizerConjFun Q g` — the conjugation action of `g ∈ N_G(Q)` on functions on `Q`;
* `conjAutD h d`, `conjIrrD h d` — the conjugation action of `d ∈ D = twoPoint H t`, expressed
  through the homomorphism `D →* N_G(Q)`;
* `instMAConjClasses`, `instMAIrr`, `instMAIrrNeOne` — the actions of `N_G(Q)` on `ConjClasses Q`,
  on `Irr Q` and on the non-trivial irreducible characters;
* `fixedBy_conjClasses`, `fixedBy_irr` — their fixed points are the `IsFixedClass`- and
  `IsFixedIrr`-fixed points of `Subgroup.normalizerMonoidHom`;
* `card_quotient_classes_eq_card_quotient_irr` — Burnside's lemma plus Brauer's permutation
  lemma: `N_G(Q)` has the same number of orbits on the classes and on the irreducible characters
  of `Q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G]

/-! ## Composition of `ConjClasses.map` -/

section ConjClassesMap

attribute [local instance] IsConj.setoid

theorem conjClasses_map_id {α : Type*} [Monoid α] :
    ConjClasses.map (MonoidHom.id α) = id := by
  funext C
  induction C using Quotient.ind
  rfl

theorem conjClasses_map_comp {α β γ : Type*} [Monoid α] [Monoid β] [Monoid γ]
    (f : β →* γ) (g : α →* β) :
    ConjClasses.map (f.comp g) = ConjClasses.map f ∘ ConjClasses.map g := by
  funext C
  induction C using Quotient.ind
  rfl

end ConjClassesMap

/-- `Work.CharCore.Irr` and `Work.Clifford.Irr` agree. -/
theorem charCore_mem_iff_clifford {G : Type} [Group G] [Fintype G] (χ : G → ℂ) :
    χ ∈ Work.CharCore.Irr G ↔ χ ∈ Work.Clifford.Irr G := by
  rw [Work.Clifford.mem_Irr]
  exact Work.Clifford.mem_Irr_iff_fdrep_aux χ

/-- `Work.Clifford.Irr G` is finite, being the finite set `Work.CharCore.Irr G`. -/
noncomputable instance instFintypeCliffordIrr {G : Type} [Group G] [Fintype G] :
    Fintype {ζ : G → ℂ // ζ ∈ Work.Clifford.Irr G} :=
  Fintype.ofEquiv {ζ : G → ℂ // ζ ∈ Work.CharCore.Irr G}
    (Equiv.subtypeEquivRight (fun ζ => charCore_mem_iff_clifford ζ))

/-! ## The conjugation action of the normaliser -/

section Normalizer

variable {Q : Subgroup G}

/-- The conjugation of a function on `Q` by an element `g` of the normaliser of `Q`:
`(g • f) (q) = f (g⁻¹ q g)`.  This is `Work.Clifford.autChar (normalizerMonoidHom Q g) f`. -/
noncomputable def normalizerConjFun (Q : Subgroup G) (g : ↥(Subgroup.normalizer (Q : Set G)))
    (f : ↥Q → ℂ) : ↥Q → ℂ := Work.Clifford.autChar (Subgroup.normalizerMonoidHom Q g) f

theorem normalizerConjFun_apply (Q : Subgroup G) (g : ↥(Subgroup.normalizer (Q : Set G)))
    (f : ↥Q → ℂ) (q : ↥Q) :
    normalizerConjFun Q g f q = f ((Subgroup.normalizerMonoidHom Q g).symm q) := rfl

theorem normalizerConjFun_one (Q : Subgroup G) (f : ↥Q → ℂ) :
    normalizerConjFun Q 1 f = f := by
  unfold normalizerConjFun
  rw [map_one, MulAut.one_def]
  ext q
  rw [Work.Clifford.autChar, MulEquiv.refl_symm, MulEquiv.refl_apply]

theorem normalizerConjFun_mul (Q : Subgroup G) [Fintype ↥Q]
    (g h : ↥(Subgroup.normalizer (Q : Set G))) (f : ↥Q → ℂ) :
    normalizerConjFun Q g (normalizerConjFun Q h f) = normalizerConjFun Q (g * h) f := by
  unfold normalizerConjFun
  rw [map_mul, ← Work.Clifford.autChar_mul_apply]

theorem normalizerConjFun_inv (Q : Subgroup G) [Fintype ↥Q]
    (g : ↥(Subgroup.normalizer (Q : Set G))) (f : ↥Q → ℂ) :
    normalizerConjFun Q g⁻¹ (normalizerConjFun Q g f) = f := by
  rw [normalizerConjFun_mul, inv_mul_cancel, normalizerConjFun_one]

theorem normalizerConjFun_const_one (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) :
    normalizerConjFun Q g (1 : ↥Q → ℂ) = 1 := by
  ext q
  rw [normalizerConjFun_apply]
  simp

theorem normalizerConjFun_eq_one_iff (Q : Subgroup G) [Fintype ↥Q]
    (g : ↥(Subgroup.normalizer (Q : Set G))) (f : ↥Q → ℂ) :
    normalizerConjFun Q g f = 1 ↔ f = 1 := by
  constructor
  · intro hf
    have h := congrArg (normalizerConjFun Q g⁻¹) hf
    rw [normalizerConjFun_inv, normalizerConjFun_const_one] at h
    exact h
  · rintro rfl
    exact normalizerConjFun_const_one Q g

theorem normalizerConjFun_mem_Irr (Q : Subgroup G) [Fintype ↥Q]
    (g : ↥(Subgroup.normalizer (Q : Set G))) {ζ : ↥Q → ℂ} (hζ : ζ ∈ Work.Clifford.Irr ↥Q) :
    normalizerConjFun Q g ζ ∈ Work.Clifford.Irr ↥Q :=
  Work.Clifford.autChar_mem_Irr (Subgroup.normalizerMonoidHom Q g) hζ

@[simp] theorem normalizerConjFun_isFixedIrr (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (f : ↥Q → ℂ) :
    Work.Clifford.IsFixedIrr (Subgroup.normalizerMonoidHom Q g) f ↔
      normalizerConjFun Q g f = f := Iff.rfl

end Normalizer

/-! ## Conjugation by elements of `D` -/

section ConjugationD

variable {H Q : Subgroup G} {t : G}

theorem twoPoint_le_normalizer (h : IsSplitRankOne H Q t) :
    twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
  le_trans (twoPoint_le_H h) h.normal

/-- `D = twoPoint H t` viewed as a subgroup of `N_G(Q)`. -/
noncomputable def dToNormalizer (h : IsSplitRankOne H Q t) :
    ↥(twoPoint H t) →* ↥(Subgroup.normalizer (Q : Set G)) where
  toFun d := ⟨(d : G), twoPoint_le_normalizer h d.2⟩
  map_one' := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl

/-- The conjugation homomorphism `D →* Aut Q`. -/
noncomputable def conjAutDHom (h : IsSplitRankOne H Q t) : ↥(twoPoint H t) →* MulAut ↥Q :=
  (Subgroup.normalizerMonoidHom Q).comp (dToNormalizer h)

/-- Conjugation by `d ∈ D = twoPoint H t`, as an automorphism of `Q`. -/
noncomputable def conjAutD (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) : ↥Q ≃* ↥Q :=
  conjAutDHom h d

/-- The conjugate of a function on `Q` by `d ∈ D`: `ζ^d (q) = ζ (d⁻¹ q d)`. -/
noncomputable def conjIrrD (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t))
    (ζ : ↥Q → ℂ) : ↥Q → ℂ :=
  normalizerConjFun Q (dToNormalizer h d) ζ

theorem conjIrrD_eq_normalizerConjFun (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t))
    (ζ : ↥Q → ℂ) : conjIrrD h d ζ = normalizerConjFun Q (dToNormalizer h d) ζ := rfl

theorem conjAutD_apply (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) (q : ↥Q) :
    conjAutD h d q = conjQD h d q := rfl

theorem conjIrrD_apply (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t))
    (ζ : ↥Q → ℂ) (q : ↥Q) : conjIrrD h d ζ q = ζ (conjQD h d⁻¹ q) := rfl

theorem conjAutD_one (h : IsSplitRankOne H Q t) : conjAutD h 1 = 1 := map_one _

theorem conjAutD_mul (h : IsSplitRankOne H Q t) (d₁ d₂ : ↥(twoPoint H t)) :
    conjAutD h (d₁ * d₂) = conjAutD h d₁ * conjAutD h d₂ := map_mul _ _ _

theorem conjIrrD_one (h : IsSplitRankOne H Q t) (ζ : ↥Q → ℂ) : conjIrrD h 1 ζ = ζ := by
  rw [conjIrrD_eq_normalizerConjFun, map_one]
  exact normalizerConjFun_one Q ζ

theorem conjIrrD_mul (h : IsSplitRankOne H Q t) [Fintype ↥Q] (d₁ d₂ : ↥(twoPoint H t))
    (ζ : ↥Q → ℂ) : conjIrrD h d₁ (conjIrrD h d₂ ζ) = conjIrrD h (d₁ * d₂) ζ := by
  rw [conjIrrD_eq_normalizerConjFun, conjIrrD_eq_normalizerConjFun, conjIrrD_eq_normalizerConjFun,
    map_mul]
  exact normalizerConjFun_mul Q _ _ ζ

theorem conjIrrD_inv_conjIrrD (h : IsSplitRankOne H Q t) [Fintype ↥Q]
    (d : ↥(twoPoint H t)) (ζ : ↥Q → ℂ) : conjIrrD h d⁻¹ (conjIrrD h d ζ) = ζ := by
  rw [conjIrrD_mul, inv_mul_cancel, conjIrrD_one]

theorem conjIrrD_mem_Irr (h : IsSplitRankOne H Q t) [Fintype ↥Q] (d : ↥(twoPoint H t))
    {ζ : ↥Q → ℂ} (hζ : ζ ∈ Work.Clifford.Irr ↥Q) : conjIrrD h d ζ ∈ Work.Clifford.Irr ↥Q :=
  normalizerConjFun_mem_Irr Q _ hζ

theorem conjIrrD_const_one (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) :
    conjIrrD h d (1 : ↥Q → ℂ) = 1 :=
  normalizerConjFun_const_one Q _

theorem conjIrrD_eq_one_iff (h : IsSplitRankOne H Q t) [Fintype ↥Q]
    (d : ↥(twoPoint H t)) (ζ : ↥Q → ℂ) : conjIrrD h d ζ = 1 ↔ ζ = 1 := by
  rw [conjIrrD_eq_normalizerConjFun]
  exact normalizerConjFun_eq_one_iff Q _ ζ

end ConjugationD

/-! ## The actions of `N_G(Q)` -/

section Actions

variable {Q : Subgroup G}

/-- The conjugation action of `N_G(Q)` on the conjugacy classes of `Q`. -/
@[instance_reducible]
noncomputable instance instMAConjClasses (Q : Subgroup G) :
    MulAction ↥(Subgroup.normalizer (Q : Set G)) (ConjClasses ↥Q) where
  smul g C := ConjClasses.map ((Subgroup.normalizerMonoidHom Q g) : ↥Q →* ↥Q) C
  one_smul C := by
    change ConjClasses.map ((Subgroup.normalizerMonoidHom Q 1 : MulAut ↥Q) : ↥Q →* ↥Q) C = C
    rw [map_one]
    have h1 : ((1 : MulAut ↥Q) : ↥Q →* ↥Q) = MonoidHom.id ↥Q := by
      ext q
      rfl
    rw [h1, conjClasses_map_id]
    rfl
  mul_smul g h C := by
    change ConjClasses.map ((Subgroup.normalizerMonoidHom Q (g * h) : MulAut ↥Q) : ↥Q →* ↥Q) C
      = ConjClasses.map ((Subgroup.normalizerMonoidHom Q g : MulAut ↥Q) : ↥Q →* ↥Q)
          (ConjClasses.map ((Subgroup.normalizerMonoidHom Q h : MulAut ↥Q) : ↥Q →* ↥Q) C)
    rw [map_mul]
    have h1 : ((Subgroup.normalizerMonoidHom Q g * Subgroup.normalizerMonoidHom Q h : MulAut ↥Q)
          : ↥Q →* ↥Q)
        = ((Subgroup.normalizerMonoidHom Q g : MulAut ↥Q) : ↥Q →* ↥Q).comp
          ((Subgroup.normalizerMonoidHom Q h : MulAut ↥Q) : ↥Q →* ↥Q) := by
      ext q
      rfl
    rw [h1, conjClasses_map_comp]
    rfl

@[simp] theorem instMAConjClasses_smul (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (C : ConjClasses ↥Q) :
    g • C = ConjClasses.map ((Subgroup.normalizerMonoidHom Q g) : ↥Q →* ↥Q) C := rfl

/-- The conjugation action of `N_G(Q)` on the irreducible characters of `Q`. -/
@[instance_reducible]
noncomputable instance instMAIrr (Q : Subgroup G) [Fintype ↥Q] :
    MulAction ↥(Subgroup.normalizer (Q : Set G)) {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q} where
  smul g ζ := ⟨normalizerConjFun Q g ζ.1, normalizerConjFun_mem_Irr Q g ζ.2⟩
  one_smul ζ := Subtype.ext (normalizerConjFun_one Q ζ.1)
  mul_smul g h ζ := by
    apply Subtype.ext
    change normalizerConjFun Q (g * h) ζ.1 = normalizerConjFun Q g (normalizerConjFun Q h ζ.1)
    exact (normalizerConjFun_mul Q g h ζ.1).symm

@[simp] theorem instMAIrr_smul_val (Q : Subgroup G) [Fintype ↥Q]
    (g : ↥(Subgroup.normalizer (Q : Set G))) (ζ : {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q}) :
    (g • ζ).1 = normalizerConjFun Q g ζ.1 := rfl

/-- The conjugation action of `N_G(Q)` on the non-trivial irreducible characters of `Q`. -/
@[instance_reducible]
noncomputable instance instMAIrrNeOne (Q : Subgroup G) [Fintype ↥Q] :
    MulAction ↥(Subgroup.normalizer (Q : Set G))
      {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q ∧ ζ ≠ 1} where
  smul g ζ := ⟨normalizerConjFun Q g ζ.1,
    ⟨normalizerConjFun_mem_Irr Q g ζ.2.1,
      fun hc => ζ.2.2 ((normalizerConjFun_eq_one_iff Q g ζ.1).mp hc)⟩⟩
  one_smul ζ := Subtype.ext (normalizerConjFun_one Q ζ.1)
  mul_smul g h ζ := by
    apply Subtype.ext
    change normalizerConjFun Q (g * h) ζ.1 = normalizerConjFun Q g (normalizerConjFun Q h ζ.1)
    exact (normalizerConjFun_mul Q g h ζ.1).symm

/-- Fixed points of the action on classes are the classes fixed by the conjugation automorphism:
this is `Work.Clifford.IsFixedClass`. -/
theorem fixedBy_conjClasses (Q : Subgroup G) (g : ↥(Subgroup.normalizer (Q : Set G))) :
    MulAction.fixedBy (ConjClasses ↥Q) g
      = {C | Work.Clifford.IsFixedClass (Subgroup.normalizerMonoidHom Q g) C} := by
  ext C
  rw [MulAction.mem_fixedBy, Set.mem_setOf_eq, instMAConjClasses_smul]
  rfl

/-- Fixed points of the action on characters are the characters fixed by the conjugation
automorphism: this is `Work.Clifford.IsFixedIrr`. -/
theorem fixedBy_irr (Q : Subgroup G) [Fintype ↥Q]
    (g : ↥(Subgroup.normalizer (Q : Set G))) :
    MulAction.fixedBy {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q} g
      = {ζ | Work.Clifford.IsFixedIrr (Subgroup.normalizerMonoidHom Q g) ζ.1} := by
  ext ζ
  constructor
  · intro hd
    exact congrArg Subtype.val (MulAction.mem_fixedBy.mp hd)
  · intro hd
    rw [MulAction.mem_fixedBy]
    exact Subtype.ext hd

end Actions

/-! ## Burnside's lemma and Brauer's permutation lemma -/

section Counting

variable {Q : Subgroup G}

/-- Burnside's lemma, in the form used below. -/
theorem natCard_quotient_mul_card {G' X : Type*} [Group G'] [Fintype G'] [MulAction G' X]
    [Fintype X] :
    Nat.card (Quotient (MulAction.orbitRel G' X)) * Nat.card G'
      = ∑ g : G', Nat.card (MulAction.fixedBy X g) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Finset.sum_congr rfl (fun g _ => Nat.card_eq_fintype_card)]
  exact (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G' X).symm

/-- **Burnside + Brauer's permutation lemma.**  The normaliser of `Q` has as many orbits on the
conjugacy classes of `Q` as on the irreducible characters of `Q`. -/
theorem card_quotient_classes_eq_card_quotient_irr (Q : Subgroup G) [Fintype G] [Fintype ↥Q] :
    Nat.card (Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G))
        (ConjClasses ↥Q)))
      = Nat.card (Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G))
          {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q})) := by
  have hclasses : Nat.card (Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G))
        (ConjClasses ↥Q))) * Nat.card ↥(Subgroup.normalizer (Q : Set G))
      = ∑ g : ↥(Subgroup.normalizer (Q : Set G)),
          Nat.card {C : ConjClasses ↥Q //
            Work.Clifford.IsFixedClass (Subgroup.normalizerMonoidHom Q g) C} := by
    rw [natCard_quotient_mul_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [fixedBy_conjClasses]
    rfl
  have hirr : Nat.card (Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G))
        {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q})) * Nat.card ↥(Subgroup.normalizer (Q : Set G))
      = ∑ g : ↥(Subgroup.normalizer (Q : Set G)),
          Nat.card {C : ConjClasses ↥Q //
            Work.Clifford.IsFixedClass (Subgroup.normalizerMonoidHom Q g) C} := by
    rw [natCard_quotient_mul_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [fixedBy_irr]
    have he : {ζ : {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q} |
          Work.Clifford.IsFixedIrr (Subgroup.normalizerMonoidHom Q g) ζ.1}
        ≃ {χ : ↥Q → ℂ // χ ∈ Work.Clifford.Irr ↥Q ∧
            Work.Clifford.IsFixedIrr (Subgroup.normalizerMonoidHom Q g) χ} :=
      { toFun := fun ζ => ⟨ζ.1.1, ζ.1.2, ζ.2⟩
        invFun := fun χ => ⟨⟨χ.1, χ.2.1⟩, χ.2.2⟩
        left_inv := fun ζ => rfl
        right_inv := fun χ => rfl }
    rw [Nat.card_congr he]
    exact Work.Clifford.card_fixed_Irr_eq_card_fixed_conjClasses
      (Subgroup.normalizerMonoidHom Q g)
  have hcard : 0 < Nat.card ↥(Subgroup.normalizer (Q : Set G)) := Nat.card_pos
  exact Nat.mul_right_cancel hcard (hclasses.trans hirr.symm)

end Counting

end Work.ZassenhausTwoGroup

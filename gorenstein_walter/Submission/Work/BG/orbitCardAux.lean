import Mathlib
import Submission.Work.BG.lemma36Defs

/-!
# `Work.BG.orbitCardAux` — vocabulary for `Work.BG.orbitCardMul`

Definitions and elementary counting lemmas used to state the pieces of
`Work.BG.orbitCardMul` (`|S·a| · |Λ(a)| = 2 · D.n`, the orbit product of the repaired route to
BG Lemma 3.6).

* `S0sub D` — the cyclic maximal subgroup `S₀` viewed inside the Sylow `2`-subgroup `↥D.S`;
* `sStab D C hDC a` — the stabilizer of a class function `a` of `U` in `↥D.S`, for the
  conjugation action `L33D.phiS`;
* `smulClassFunction`, `sStabOp` — the same action of `↥D.S` on the class functions of `U`,
  packaged as a `MulAction` of `(↥D.S)ᵐᵒᵖ` (the action on class functions is a *right* action of
  `↥D.S`, so it is a left action of the opposite group), with
  `sOrbitU_card_mul_sStab_card` — Mathlib's orbit–stabiliser theorem;
* `S0in D C hDC` — `S₀` viewed inside `↥C.P.H0 = H₀`;
* `S0in_sup_Uin` — `H₀ = U S₀` inside `↥C.P.H0`;
* `S0in_inf_Uin` — `U ∩ S₀ = 1` inside `↥C.P.H0`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Elementary `ClassFunction.compHom` calculus -/

/-- `compHom` along an inverse automorphism undoes `compHom` along the automorphism. -/
theorem compHom_inv_of_fixed {X : Type} [Group X] (e : MulAut X) (a : ClassFunction X ℂ)
    (ha : ClassFunction.compHom e.toMonoidHom a = a) :
    ClassFunction.compHom (e⁻¹).toMonoidHom a = a := by
  have h1 : ClassFunction.compHom (e⁻¹).toMonoidHom (ClassFunction.compHom e.toMonoidHom a)
      = ClassFunction.compHom ((e.toMonoidHom).comp (e⁻¹).toMonoidHom) a :=
    ClassFunction.compHom_comp e.toMonoidHom (e⁻¹).toMonoidHom a
  have h2 : (e.toMonoidHom).comp (e⁻¹).toMonoidHom = MonoidHom.id X := by
    ext u
    change (e * e⁻¹) u = u
    rw [mul_inv_cancel, MulAut.one_apply]
  rw [ha, h2, compHom_id] at h1
  exact h1

/-- The monoid hom underlying a product of automorphisms. -/
theorem toMonoidHom_mul {X : Type} [Group X] (e₁ e₂ : MulAut X) :
    (e₁ * e₂).toMonoidHom = (e₁.toMonoidHom).comp e₂.toMonoidHom := by
  ext u; rfl

/-! ## 2. `S₀` inside `S`, the stabilizer `S_a`, its character-function model -/

/-- `S₀`, viewed as a subgroup of the Sylow `2`-subgroup `↥D.S`. -/
def S0sub (D : BGData G) : Subgroup ↥(D.S : Subgroup G) :=
  D.S0.subgroupOf (D.S : Subgroup G)

@[simp] theorem mem_S0sub (D : BGData G) (s : ↥(D.S : Subgroup G)) :
    s ∈ S0sub D ↔ (s : G) ∈ D.S0 := by
  rw [S0sub, Subgroup.mem_subgroupOf]

/-- The stabilizer in `S` of a class function `a` of `U = ↥(Uin C)`, for the conjugation
action `L33D.phiS` of `D.S` on `U`. -/
noncomputable def sStab (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) : Subgroup ↥(D.S) where
  carrier := {s | ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom a = a}
  one_mem' := by
    show ClassFunction.compHom (L33D.phiS D C hDC 1).toMonoidHom a = a
    rw [map_one]
    exact compHom_id a
  mul_mem' := by
    intro s t hs ht
    show ClassFunction.compHom (L33D.phiS D C hDC (s * t)).toMonoidHom a = a
    rw [map_mul, toMonoidHom_mul]
    conv_lhs => rw [← ClassFunction.compHom_comp]
    rw [hs, ht]
  inv_mem' := by
    intro s hs
    show ClassFunction.compHom (L33D.phiS D C hDC s⁻¹).toMonoidHom a = a
    rw [map_inv]
    exact compHom_inv_of_fixed _ a hs

@[simp] theorem mem_sStab (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) (s : ↥(D.S)) :
    s ∈ sStab D C hDC a ↔ ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom a = a :=
  Iff.rfl

/-- The conjugation action of `↥D.S` on the class functions of `U = ↥(Uin C)`, in the
`MulAction` form: since `a ↦ a ∘ φS s` is a *right* action of `↥D.S`, this is a left action
of the opposite group. -/
noncomputable def smulClassFunction (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    MulAction (MulOpposite ↥(D.S)) (ClassFunction ↥(Uin C) ℂ) where
  smul s a := ClassFunction.compHom (L33D.phiS D C hDC (MulOpposite.unop s)).toMonoidHom a
  one_smul a := by
    show ClassFunction.compHom
        (L33D.phiS D C hDC (MulOpposite.unop (1 : MulOpposite ↥(D.S)))).toMonoidHom a = a
    rw [MulOpposite.unop_one, map_one]
    exact compHom_id a
  mul_smul s t a := by
    show ClassFunction.compHom (L33D.phiS D C hDC (MulOpposite.unop (s * t))).toMonoidHom a
      = ClassFunction.compHom (L33D.phiS D C hDC (MulOpposite.unop s)).toMonoidHom
          (ClassFunction.compHom (L33D.phiS D C hDC (MulOpposite.unop t)).toMonoidHom a)
    rw [MulOpposite.unop_mul, map_mul, toMonoidHom_mul]
    conv_rhs => rw [ClassFunction.compHom_comp]

/-- The stabilizer of the opposite-group action, as a subgroup of `(↥D.S)ᵐᵒᵖ`. -/
def sStabOp (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) : Subgroup (MulOpposite ↥(D.S)) :=
  { carrier := {x | MulOpposite.unop x ∈ sStab D C hDC a}
    one_mem' := by
      show MulOpposite.unop (1 : MulOpposite ↥(D.S)) ∈ sStab D C hDC a
      rw [MulOpposite.unop_one]
      exact (sStab D C hDC a).one_mem
    mul_mem' := by
      intro x y hx hy
      have hxy : MulOpposite.unop (x * y)
          = MulOpposite.unop y * MulOpposite.unop x := rfl
      rw [Set.mem_ofPred_eq, hxy]
      exact (sStab D C hDC a).mul_mem hy hx
    inv_mem' := by
      intro x hx
      exact (sStab D C hDC a).inv_mem hx }

theorem stabilizer_eq_sStabOp (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) :
    letI := smulClassFunction D C hDC
    MulAction.stabilizer (MulOpposite ↥(D.S)) a = sStabOp D C hDC a := by
  ext x
  rfl

theorem orbit_eq_sOrbitU (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) :
    letI := smulClassFunction D C hDC
    MulAction.orbit (MulOpposite ↥(D.S)) a = sOrbitU D C hDC a := by
  ext b
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨MulOpposite.unop s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨MulOpposite.op s, rfl⟩

/-- The cardinality of the opposite-group stabilizer is that of `sStab`. -/
theorem card_sStabOp (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) :
    Nat.card ↥(sStabOp D C hDC a) = Nat.card ↥(sStab D C hDC a) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨MulOpposite.unop x.1, x.2⟩
      invFun := fun s => ⟨MulOpposite.op s.1, s.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun s => by ext; rfl }

/-- **Orbit–stabiliser for the `S`-action on `Irr(U)`**:
`|S·a| · |S_a| = |S|`. -/
theorem sOrbitU_card_mul_sStab_card (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) :
    (sOrbitU D C hDC a).ncard * Nat.card ↥(sStab D C hDC a) = Nat.card ↥(D.S : Subgroup G) := by
  letI := smulClassFunction D C hDC
  have horb := orbit_eq_sOrbitU D C hDC a
  have hstab := stabilizer_eq_sStabOp D C hDC a
  have h := MulAction.index_stabilizer (MulOpposite ↥(D.S)) a
  rw [hstab, horb] at h
  rw [← h, ← card_sStabOp, Subgroup.index_mul_card]
  exact (Nat.card_congr MulOpposite.opEquiv).symm

/-! ## 3. `S₀` inside `H₀`, the products `U S₀ = H₀` and `U ∩ S₀ = 1` -/

/-- `S₀`, viewed inside `H₀ = ↥C.P.H0`. -/
def S0in (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) : Subgroup ↥C.P.H0 :=
  D.S0.subgroupOf C.P.H0

@[simp] theorem mem_S0in (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (x : ↥C.P.H0) : x ∈ S0in D C hDC ↔ (x : G) ∈ D.S0 := by
  rw [S0in, Subgroup.mem_subgroupOf]

/-- `H₀ = U S₀` inside the group `↥C.P.H0`. -/
theorem S0in_sup_Uin (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    Uin C ⊔ S0in D C hDC = ⊤ := by
  have hUle : D.U ≤ C.P.H0 := by rw [hDC.H0_eq]; exact le_sup_left
  have hS0le : D.S0 ≤ C.P.H0 := by rw [hDC.H0_eq]; exact le_sup_right
  have hsup := Subgroup.subgroupOf_sup (A := D.U) (A' := D.S0) (B := C.P.H0) hUle hS0le
  have h : Uin C ⊔ S0in D C hDC = (D.U ⊔ D.S0).subgroupOf C.P.H0 := by
    rw [Uin, hDC.U_eq, S0in]
    exact hsup.symm
  have hH : D.U ⊔ D.S0 = C.P.H0 := by
    rw [hDC.H0_eq]
    rfl
  rw [h, hH, Subgroup.subgroupOf_self]

/-- `U ∩ S₀ = 1` inside the group `↥C.P.H0`. -/
theorem S0in_inf_Uin (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) :
    (Uin C) ⊓ (S0in D C hDC) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hxU : (x : G) ∈ D.U := by
    have h := hx.1
    rw [Uin, hDC.U_eq, Subgroup.mem_subgroupOf] at h
    exact h
  have hxS0 : (x : G) ∈ D.S0 := by
    have h := hx.2
    rw [S0in, Subgroup.mem_subgroupOf] at h
    exact h
  have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← rem31UinfS0 D]
    exact ⟨hxU, hxS0⟩
  exact Subtype.ext (Subgroup.mem_bot.mp hbot)

end Work.BG

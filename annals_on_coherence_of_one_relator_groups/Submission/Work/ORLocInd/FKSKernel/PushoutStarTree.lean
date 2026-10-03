/-
# The Bass--Serre "star" tree of a pushout of groups (`Monoid.PushoutI`)

Let `φ : (i : ι) → H →* G i` be a family of group homomorphisms and let
`P = Monoid.PushoutI φ` be the pushout.  This file constructs the graph on which `P` acts whose
vertices are the cosets of the "vertex groups" `of i` and of the base subgroup `base φ`, and whose
edges join a centre (a coset of `base φ`) with the corresponding leaf (a coset of `of i`).

The model is the "star" model of the Bass--Serre tree of the graph of groups which is a star with
central vertex group `H` (edge maps the identity into the centre) and leaf vertex groups `G i`
(edge maps `φ i`).

* `Vtx φ` : the vertices,
* `ctr φ c` : the centre vertex of the coset `c` of the base subgroup,
* `lf φ i c` : the leaf vertex of `c` in the `i`-th vertex group,
* `Arrow φ x y` : the arrows (a subtype of `ι × (P ⧸ base)`),

together with the reversal of arrows, the `MulAction` of `P` on `Vtx φ` and the compatible
`GraphAction`.
-/
import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Action.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.FKSKernel

open Quiver

variable {ι : Type u} {H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]

/-- The pushout underlying the tree. -/
abbrev Psh (φ : ∀ i, H →* G i) : Type u := Monoid.PushoutI φ

/-- The base subgroup of the pushout (the image of `H`). -/
abbrev baseSub (φ : ∀ i, H →* G i) : Subgroup (Psh φ) := (Monoid.PushoutI.base φ).range

/-- The image of the `i`-th group in the pushout. -/
abbrev ofSub (φ : ∀ i, H →* G i) (i : ι) : Subgroup (Psh φ) :=
  (Monoid.PushoutI.of (φ := φ) i).range

theorem baseSub_le_ofSub (φ : ∀ i, H →* G i) (i : ι) : baseSub φ ≤ ofSub φ i := by
  rintro x ⟨h, rfl⟩
  exact ⟨φ i h, Monoid.PushoutI.of_apply_eq_base φ i h⟩

/-- The vertices of the star tree: centres (cosets of the base subgroup) and leaves
(cosets of the `i`-th vertex group). -/
abbrev Vtx (φ : ∀ i, H →* G i) : Type u :=
  (Psh φ ⧸ baseSub φ) ⊕ (Σ i : ι, Psh φ ⧸ ofSub φ i)

/-- The change of coset map from the base subgroup to the `i`-th vertex group. -/
def cosetMap (φ : ∀ i, H →* G i) (i : ι) :
    Psh φ ⧸ baseSub φ → Psh φ ⧸ ofSub φ i :=
  Quotient.map' id (fun _ _ hab =>
    QuotientGroup.leftRel_apply.mpr (baseSub_le_ofSub φ i (QuotientGroup.leftRel_apply.mp hab)))

@[simp]
theorem cosetMap_mk (φ : ∀ i, H →* G i) (i : ι) (g : Psh φ) :
    cosetMap φ i (Quotient.mk'' g) = Quotient.mk'' g :=
  Quotient.map'_mk'' id _ g

/-- The centre vertex attached to a coset of the base subgroup. -/
def ctr (φ : ∀ i, H →* G i) (c : Psh φ ⧸ baseSub φ) : Vtx φ := Sum.inl c

/-- The leaf vertex attached to a coset of the base subgroup (in the `i`-th vertex group). -/
def lf (φ : ∀ i, H →* G i) (i : ι) (c : Psh φ ⧸ baseSub φ) : Vtx φ :=
  Sum.inr ⟨i, cosetMap φ i c⟩

@[simp]
theorem ctr_inj {φ : ∀ i, H →* G i} {c c' : Psh φ ⧸ baseSub φ} (h : ctr φ c = ctr φ c') :
    c = c' := Sum.inl.inj h

theorem ctr_ne_lf (φ : ∀ i, H →* G i) (c c' : Psh φ ⧸ baseSub φ) (i : ι) :
    ctr φ c ≠ lf φ i c' := by
  simp [ctr, lf]

theorem lf_ne_ctr (φ : ∀ i, H →* G i) (c c' : Psh φ ⧸ baseSub φ) (i : ι) :
    lf φ i c ≠ ctr φ c' := by
  simp [ctr, lf]

/-- An arrow of the star tree: the data of a type `i` and a coset of the base subgroup, with the
endpoint conditions. -/
abbrev Arrow (φ : ∀ i, H →* G i) (x y : Vtx φ) : Type u :=
  { e : ι × (Psh φ ⧸ baseSub φ) //
      (x = ctr φ e.2 ∧ y = lf φ e.1 e.2) ∨ (x = lf φ e.1 e.2 ∧ y = ctr φ e.2) }

instance instQuiverVtx (φ : ∀ i, H →* G i) : Quiver (Vtx φ) := ⟨Arrow φ⟩

/-- The type of an arrow. -/
abbrev Arrow.idx {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) : ι := e.1.1

/-- The coset label of an arrow. -/
abbrev Arrow.lbl {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) : Psh φ ⧸ baseSub φ := e.1.2

theorem Arrow.endpoints {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) :
    (x = ctr φ e.lbl ∧ y = lf φ e.idx e.lbl) ∨
      (x = lf φ e.idx e.lbl ∧ y = ctr φ e.lbl) := e.2

/-- The reversed arrow. -/
def arrowReverse {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) : y ⟶ x :=
  ⟨e.1, e.2.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩

@[simp]
theorem arrowReverse_val {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) :
    (arrowReverse e).1 = e.1 := rfl

theorem arrowReverse_arrowReverse {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) :
    arrowReverse (arrowReverse e) = e := Subtype.ext rfl

instance instHasReverseVtx (φ : ∀ i, H →* G i) : Quiver.HasReverse (Vtx φ) where
  reverse' := arrowReverse

instance instHasInvolutiveReverseVtx (φ : ∀ i, H →* G i) :
    Quiver.HasInvolutiveReverse (Vtx φ) :=
  { instHasReverseVtx φ with inv' := fun e => arrowReverse_arrowReverse e }

@[simp]
theorem reverse_val {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) :
    (Quiver.reverse e).1 = e.1 := rfl

/-! ## The action of the pushout on the tree -/

/-- Left multiplication on the cosets of the base subgroup. -/
def smulCtr (φ : ∀ i, H →* G i) (g : Psh φ) : Psh φ ⧸ baseSub φ → Psh φ ⧸ baseSub φ :=
  Quotient.map' (fun h => g * h) (by
    intro a b hab
    exact QuotientGroup.leftRel_apply.mpr
      (by simpa [mul_assoc] using (QuotientGroup.leftRel_apply.mp hab)))

/-- Left multiplication on the cosets of the `i`-th vertex group. -/
def smulLf (φ : ∀ i, H →* G i) (g : Psh φ) (i : ι) :
    Psh φ ⧸ ofSub φ i → Psh φ ⧸ ofSub φ i :=
  Quotient.map' (fun h => g * h) (by
    intro a b hab
    exact QuotientGroup.leftRel_apply.mpr
      (by simpa [mul_assoc] using (QuotientGroup.leftRel_apply.mp hab)))

@[simp]
theorem smulCtr_mk (φ : ∀ i, H →* G i) (g h : Psh φ) :
    smulCtr φ g (Quotient.mk'' h) = Quotient.mk'' (g * h) :=
  Quotient.map'_mk'' _ _ h

theorem smulLf_mk (φ : ∀ i, H →* G i) (g h : Psh φ) (i : ι) :
    smulLf φ g i (Quotient.mk'' h) = Quotient.mk'' (g * h) :=
  Quotient.map'_mk'' _ _ h

theorem smulCtr_one (φ : ∀ i, H →* G i) (c : Psh φ ⧸ baseSub φ) : smulCtr φ 1 c = c := by
  induction c using Quotient.inductionOn' with
  | h a => rw [smulCtr_mk]; exact Quotient.sound (by simp)

theorem smulCtr_mul (φ : ∀ i, H →* G i) (g h : Psh φ) (c : Psh φ ⧸ baseSub φ) :
    smulCtr φ (g * h) c = smulCtr φ g (smulCtr φ h c) := by
  induction c using Quotient.inductionOn' with
  | h a => rw [smulCtr_mk, smulCtr_mk, smulCtr_mk]; exact Quotient.sound (by simp [mul_assoc])

theorem smulLf_one (φ : ∀ i, H →* G i) (i : ι) (c : Psh φ ⧸ ofSub φ i) : smulLf φ 1 i c = c := by
  induction c using Quotient.inductionOn' with
  | h a => rw [smulLf_mk]; exact Quotient.sound (by simp)

theorem smulLf_mul (φ : ∀ i, H →* G i) (g h : Psh φ) (i : ι) (c : Psh φ ⧸ ofSub φ i) :
    smulLf φ (g * h) i c = smulLf φ g i (smulLf φ h i c) := by
  induction c using Quotient.inductionOn' with
  | h a => rw [smulLf_mk, smulLf_mk, smulLf_mk]; exact Quotient.sound (by simp [mul_assoc])

theorem cosetMap_smul (φ : ∀ i, H →* G i) (g : Psh φ) (i : ι) (c : Psh φ ⧸ baseSub φ) :
    cosetMap φ i (smulCtr φ g c) = smulLf φ g i (cosetMap φ i c) := by
  induction c using Quotient.inductionOn' with
  | h a => simp only [smulCtr_mk, cosetMap_mk, smulLf_mk]

/-- The action of the pushout on the vertices of the star tree. -/
def smulVtx (φ : ∀ i, H →* G i) (g : Psh φ) : Vtx φ → Vtx φ :=
  Sum.map (smulCtr φ g) (fun c => ⟨c.1, smulLf φ g c.1 c.2⟩)

@[simp]
theorem smulVtx_ctr (φ : ∀ i, H →* G i) (g : Psh φ) (c : Psh φ ⧸ baseSub φ) :
    smulVtx φ g (ctr φ c) = ctr φ (smulCtr φ g c) := rfl

@[simp]
theorem smulVtx_lf (φ : ∀ i, H →* G i) (g : Psh φ) (i : ι) (c : Psh φ ⧸ baseSub φ) :
    smulVtx φ g (lf φ i c) = lf φ i (smulCtr φ g c) := by
  simp only [lf, ctr, smulVtx, Sum.map_inr, cosetMap_smul]

theorem smulVtx_apply_inl (φ : ∀ i, H →* G i) (g : Psh φ) (c : Psh φ ⧸ baseSub φ) :
    smulVtx φ g (Sum.inl c) = Sum.inl (smulCtr φ g c) := rfl

theorem smulVtx_apply_inr (φ : ∀ i, H →* G i) (g : Psh φ) (i : ι) (c : Psh φ ⧸ ofSub φ i) :
    smulVtx φ g (Sum.inr ⟨i, c⟩) = Sum.inr ⟨i, smulLf φ g i c⟩ := rfl

instance instMulActionVtx (φ : ∀ i, H →* G i) : MulAction (Psh φ) (Vtx φ) where
  smul := smulVtx φ
  one_smul x := by
    rcases x with c | ⟨i, c⟩
    · show smulVtx φ 1 (Sum.inl c) = Sum.inl c
      rw [smulVtx_apply_inl, smulCtr_one]
    · show smulVtx φ 1 (Sum.inr ⟨i, c⟩) = Sum.inr ⟨i, c⟩
      rw [smulVtx_apply_inr, smulLf_one]
  mul_smul g h x := by
    rcases x with c | ⟨i, c⟩
    · show smulVtx φ (g * h) (Sum.inl c) = smulVtx φ g (smulVtx φ h (Sum.inl c))
      rw [smulVtx_apply_inl, smulVtx_apply_inl, smulVtx_apply_inl, smulCtr_mul]
    · show smulVtx φ (g * h) (Sum.inr ⟨i, c⟩) =
        smulVtx φ g (smulVtx φ h (Sum.inr ⟨i, c⟩))
      rw [smulVtx_apply_inr, smulVtx_apply_inr, smulVtx_apply_inr, smulLf_mul]

/-- The translate of an arrow. -/
def smulArrow (φ : ∀ i, H →* G i) (g : Psh φ) {x y : Vtx φ} (e : x ⟶ y) :
    (g • x) ⟶ (g • y) :=
  ⟨(e.idx, smulCtr φ g e.lbl), by
    obtain ⟨⟨j, c'⟩, he⟩ := e
    rcases he with h | h
    · refine Or.inl ⟨?_, ?_⟩
      · show g • x = ctr φ (smulCtr φ g c')
        rw [h.1]
        exact smulVtx_ctr φ g c'
      · show g • y = lf φ j (smulCtr φ g c')
        rw [h.2]
        exact smulVtx_lf φ g j c'
    · refine Or.inr ⟨?_, ?_⟩
      · show g • x = lf φ j (smulCtr φ g c')
        rw [h.1]
        exact smulVtx_lf φ g j c'
      · show g • y = ctr φ (smulCtr φ g c')
        rw [h.2]
        exact smulVtx_ctr φ g c'⟩

@[simp]
theorem smulArrow_val (φ : ∀ i, H →* G i) (g : Psh φ) {x y : Vtx φ} (e : x ⟶ y) :
    (smulArrow φ g e).1 = (e.idx, smulCtr φ g e.lbl) := rfl

/-- Total arrows with equal endpoints and equal data are equal. -/
theorem Total.ext' {φ : ∀ i, H →* G i} {a a' b b' : Vtx φ}
    (ha : a = a') (hb : b = b') (f : a ⟶ b) (f' : a' ⟶ b') (hl : f.1 = f'.1) :
    Quiver.Total.mk a b f = Quiver.Total.mk a' b' f' := by
  subst ha
  subst hb
  exact congrArg (Quiver.Total.mk a b) (Subtype.ext hl)

instance instGraphActionVtx (φ : ∀ i, H →* G i) :
    Work.ORBassSerre.GraphAction (Psh φ) (Vtx φ) where
  smulTotal g e := Quiver.Total.mk (g • e.left) (g • e.right) (smulArrow φ g e.hom)
  smulTotal_mul g h e := by
    obtain ⟨l, r, f⟩ := e
    exact Total.ext' (mul_smul g h l) (mul_smul g h r) _ _
      (Prod.ext rfl (smulCtr_mul φ g h f.1.2))
  smulTotal_one e := by
    obtain ⟨l, r, f⟩ := e
    exact Total.ext' (one_smul _ l) (one_smul _ r) _ _
      (Prod.ext rfl (smulCtr_one φ f.1.2))
  smul_left g e := rfl
  smul_right g e := rfl
  smul_reverse g e := by
    obtain ⟨l, r, f⟩ := e
    exact Total.ext' rfl rfl _ _ rfl

/-! ## Basic structure of arrows and paths

Every vertex is a centre or a leaf, and arrows always join a centre and a leaf. -/

/-- Casting a term along an index equality, from `HEq`. -/
theorem heq_cast {α : Sort _} {β : α → Sort _} {a b : α} {x : β a} {y : β b} (h : a = b)
    (hxy : HEq x y) : (h ▸ x : β b) = y := by
  cases h
  exact eq_of_heq hxy

/-- The two components of an equality of leaves. -/
theorem leaf_eq_components {φ : ∀ i, H →* G i} {i j : ι} {c d : Psh φ ⧸ baseSub φ}
    (h : lf φ i c = lf φ j d) : i = j ∧ HEq (cosetMap φ i c) (cosetMap φ j d) :=
  Sigma.mk.inj_iff.mp (Sum.inr.inj h)

/-- An arrow out of a centre is determined by its label. -/
theorem arrow_ctr_left {φ : ∀ i, H →* G i} {c : Psh φ ⧸ baseSub φ} {y : Vtx φ}
    (e : ctr φ c ⟶ y) : e.lbl = c ∧ y = lf φ e.idx c := by
  obtain ⟨⟨j, c'⟩, he⟩ := e
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hc : c = (j, c').2 := ctr_inj h1
    subst hc
    exact ⟨rfl, h2⟩
  · exact absurd h1 (ctr_ne_lf φ _ _ _)

/-- An arrow into a centre is determined by its label. -/
theorem arrow_ctr_right {φ : ∀ i, H →* G i} {c : Psh φ ⧸ baseSub φ} {x : Vtx φ}
    (e : x ⟶ ctr φ c) : e.lbl = c ∧ x = lf φ e.idx c := by
  obtain ⟨⟨j, c'⟩, he⟩ := e
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h2 (ctr_ne_lf φ _ _ _)
  · have hc : c = (j, c').2 := ctr_inj h2
    subst hc
    exact ⟨rfl, h1⟩

/-- An arrow out of a leaf `lf i c` has type `i` and its label `c'` satisfies `lf i c' = lf i c`. -/
theorem arrow_lf_left {φ : ∀ i, H →* G i} {i : ι} {c : Psh φ ⧸ baseSub φ} {y : Vtx φ}
    (e : lf φ i c ⟶ y) : e.idx = i ∧ lf φ i e.lbl = lf φ i c ∧ y = ctr φ e.lbl := by
  obtain ⟨⟨j, c'⟩, he⟩ := e
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h1 (lf_ne_ctr φ _ _ _)
  · obtain ⟨hij, hhe⟩ := leaf_eq_components h1
    subst hij
    have hc : cosetMap φ i c' = cosetMap φ i c := eq_of_heq hhe.symm
    exact ⟨rfl, by simp only [lf, hc], h2⟩

/-- An arrow into a leaf `lf i c` has type `i` and its label `c'` satisfies `lf i c' = lf i c`. -/
theorem arrow_lf_right {φ : ∀ i, H →* G i} {i : ι} {c : Psh φ ⧸ baseSub φ} {x : Vtx φ}
    (e : x ⟶ lf φ i c) : e.idx = i ∧ lf φ i e.lbl = lf φ i c ∧ x = ctr φ e.lbl := by
  obtain ⟨⟨j, c'⟩, he⟩ := e
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hji, hhe⟩ := leaf_eq_components h2
    subst hji
    have hc : cosetMap φ i c' = cosetMap φ i c := eq_of_heq hhe.symm
    exact ⟨rfl, by simp only [lf, hc], h1⟩
  · exact absurd h2 (lf_ne_ctr φ _ _ _)

end Work.ORLocInd.FKSKernel

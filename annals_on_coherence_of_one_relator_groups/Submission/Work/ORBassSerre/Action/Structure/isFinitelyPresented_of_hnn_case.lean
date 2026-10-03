import Mathlib
import Submission.Work.ORBassSerre.Action.fg_of_isCocompact_tree
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.FP.hnn_isFinitelyPresented
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Seg.exists_finset_arrows
-- import Submission.Work.ORBassSerre.Tree.geodesic_length_walk
import Submission.Work.ORBassSerre.Action.exists_invariant_cocompact_subtree

namespace Work.ORBassSerre.Action.Structure

open Quiver

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ## The data attached to the HNN situation -/

/-- The fundamental edge `v ⟶ t • v` of the HNN description, as an element of `Quiver.Total V`. -/
def hnnEdge (v : V) (t : G) (e : v ⟶ t • v) : Quiver.Total V := Quiver.Total.mk v (t • v) e

/-- The conjugate `t⁻¹e` of the fundamental edge, reversed, so that its source is `v`. -/
def hnnBack (v : V) (t : G) (e : v ⟶ t • v) : Quiver.Total V :=
  (t⁻¹ • hnnEdge v t e).reverse

/-- The step of the walk attached to the exponent `u : ℤˣ`. -/
def hnnStep (v : V) (t : G) (e : v ⟶ t • v) (u : ℤˣ) : Quiver.Total V :=
  if u = 1 then hnnEdge v t e else hnnBack v t e

/-- The vertex group. -/
abbrev hnnH (G : Type*) [Group G] [MulAction G V] (v : V) : Subgroup G :=
  MulAction.stabilizer G v

/-- The associated subgroup `A = Stab(t⁻¹e)`, viewed inside `Stab(v)`. -/
def hnnA (v : V) (t : G) (e : v ⟶ t • v) : Subgroup ↥(hnnH (G := G) v) :=
  Subgroup.comap (hnnH (G := G) v).subtype (MulAction.stabilizer G (hnnBack v t e))

/-- The associated subgroup `B = Stab(e)`, viewed inside `Stab(v)`. -/
def hnnB (v : V) (t : G) (e : v ⟶ t • v) : Subgroup ↥(hnnH (G := G) v) :=
  Subgroup.comap (hnnH (G := G) v).subtype (MulAction.stabilizer G (hnnEdge v t e))

lemma units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg (fun u : ℤˣ => (u : ℤ)) h
  simp at h'

lemma units_one_ne_neg_one : (1 : ℤˣ) ≠ -1 := fun h => units_neg_one_ne_one h.symm

@[simp] lemma hnnStep_one (v : V) (t : G) (e : v ⟶ t • v) : hnnStep v t e 1 = hnnEdge v t e := by
  simp [hnnStep]

@[simp] lemma hnnStep_neg_one (v : V) (t : G) (e : v ⟶ t • v) :
    hnnStep v t e (-1) = hnnBack v t e := by
  rw [hnnStep]; exact if_neg units_neg_one_ne_one

lemma heq_of_homOfEq_eq {X Y X' Y' : V} {f : X ⟶ Y} (hX : X = X') (hY : Y = Y')
    {g : X' ⟶ Y'} (h : Quiver.homOfEq f hX hY = g) : HEq f g := by
  rw [← h]
  exact (Quiver.homOfEq_heq hX hY f).symm

lemma total_reverse_inj {X Y : Quiver.Total V} : X.reverse = Y.reverse ↔ X = Y := by
  constructor
  · intro h
    have h2 := congrArg Quiver.Total.reverse h
    simpa only [Quiver.Total.reverse_reverse] using h2
  · intro h; rw [h]

/-- Projection of the action on arrows (a form rewriting can use syntactically). -/
lemma total_smul_left (g : G) (X : Quiver.Total V) : (g • X).left = g • X.left :=
  Work.ORBassSerre.GraphAction.smul_left g X

/-- Projection of the action on arrows (a form rewriting can use syntactically). -/
lemma total_smul_right (g : G) (X : Quiver.Total V) : (g • X).right = g • X.right :=
  Work.ORBassSerre.GraphAction.smul_right g X

lemma stabilizer_reverse (X : Quiver.Total V) :
    MulAction.stabilizer G X.reverse = MulAction.stabilizer G X := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    Work.ORBassSerre.GraphAction.smul_reverse_apply, total_reverse_inj]

lemma mem_hnnH (v : V) (c : ↥(hnnH (G := G) v)) : (c : G) • v = v :=
  MulAction.mem_stabilizer_iff.mp (show (c : G) ∈ MulAction.stabilizer G v from c.2)

/-! ## The reduced-word condition has no two-step return -/

/-- **Key geometric input.**  If `(u, c)` and `u'` are consecutive entries of a reduced HNN word
(so that `c ∈ toSubgroup A B u` forces `u = u'`), then `t^u c t^{u'}` does not fix `v`.  This
rules out a two-step return of the walk attached to the word. -/
lemma hnn_two_step_ne (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V) {v : V} {t : G} {e : v ⟶ t • v}
    (u u' : ℤˣ) (c : ↥(hnnH (G := G) v))
    (hchain : c ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) u → u = u') :
    (t ^ (u : ℤ) * (c : G) * t ^ (u' : ℤ)) • v ≠ v := by
  intro h
  have hcv : (c : G) • v = v := mem_hnnH v c
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or u' with rfl | rfl
  · -- u = u' = 1 : `t c t` fixes `v`, so `t c` inverts the fundamental edge
    simp only [show ((1 : ℤˣ) : ℤ) = 1 from rfl, zpow_one] at h
    have h1 : ((t * (c : G)) • hnnEdge v t e).left = t • v := by
      rw [total_smul_left]
      show (t * (c : G)) • v = t • v
      rw [mul_smul, hcv]
    have h2 : ((t * (c : G)) • hnnEdge v t e).right = v := by
      rw [total_smul_right]
      show (t * (c : G)) • (t • v) = v
      rw [← mul_smul]
      exact h
    have harrow : Quiver.homOfEq ((t * (c : G)) • hnnEdge v t e).hom h1 h2 =
        Quiver.reverse e :=
      Work.ORBassSerre.Tree.Seg.arrow_unique (hT := hT) (t • v) v _ _
    have hhom : HEq (((t * (c : G)) • hnnEdge v t e).hom) (Quiver.reverse e) :=
      heq_of_homOfEq_eq h1 h2 harrow
    have hlt : ((t * (c : G)) • hnnEdge v t e).left = (hnnEdge v t e).reverse.left := by
      rw [h1, Quiver.Total.reverse_left]; simp only [hnnEdge]
    have hrt : ((t * (c : G)) • hnnEdge v t e).right = (hnnEdge v t e).reverse.right := by
      rw [h2, Quiver.Total.reverse_right]; simp only [hnnEdge]
    have htot : (t * (c : G)) • hnnEdge v t e = (hnnEdge v t e).reverse :=
      Quiver.Total.ext hlt hrt hhom
    exact hninv (t * (c : G)) (hnnEdge v t e) htot
  · -- u = 1, u' = -1 : `t c t⁻¹` fixes `v` and `t v`, so it fixes the edge
    simp only [show ((1 : ℤˣ) : ℤ) = 1 from rfl, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
      zpow_one, zpow_neg_one] at h
    have h1 : ((t * (c : G) * t⁻¹) • hnnEdge v t e).left = v := by
      rw [total_smul_left]
      show (t * (c : G) * t⁻¹) • v = v
      exact h
    have h2 : ((t * (c : G) * t⁻¹) • hnnEdge v t e).right = t • v := by
      rw [total_smul_right]
      show (t * (c : G) * t⁻¹) • (t • v) = t • v
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul, hcv]
    have harrow : Quiver.homOfEq ((t * (c : G) * t⁻¹) • hnnEdge v t e).hom h1 h2 = e :=
      Work.ORBassSerre.Tree.Seg.arrow_unique (hT := hT) v (t • v) _ _
    have hhom : HEq (((t * (c : G) * t⁻¹) • hnnEdge v t e).hom) e :=
      heq_of_homOfEq_eq h1 h2 harrow
    have hlt : ((t * (c : G) * t⁻¹) • hnnEdge v t e).left = (hnnEdge v t e).left := by
      rw [h1]; simp only [hnnEdge]
    have hrt : ((t * (c : G) * t⁻¹) • hnnEdge v t e).right = (hnnEdge v t e).right := by
      rw [h2]; simp only [hnnEdge]
    have htot : (t * (c : G) * t⁻¹) • hnnEdge v t e = hnnEdge v t e :=
      Quiver.Total.ext hlt hrt hhom
    -- hence `c` fixes `t⁻¹ • hnnEdge`
    have hcback : (c : G) • (t⁻¹ • hnnEdge v t e) = t⁻¹ • hnnEdge v t e := by
      have h3 : (t * (c : G) * t⁻¹) • hnnEdge v t e = hnnEdge v t e := htot
      calc (c : G) • (t⁻¹ • hnnEdge v t e)
          = (t⁻¹ * (t * (c : G) * t⁻¹)) • hnnEdge v t e := by
            rw [show (t⁻¹ * (t * (c : G) * t⁻¹)) = ((c : G) * t⁻¹) by group, mul_smul]
          _ = t⁻¹ • ((t * (c : G) * t⁻¹) • hnnEdge v t e) := by rw [mul_smul]
          _ = t⁻¹ • hnnEdge v t e := by rw [h3]
    have hcA : c ∈ hnnA v t e := by
      rw [hnnA, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      change ((c : G) • hnnBack v t e) = hnnBack v t e
      rw [hnnBack, Work.ORBassSerre.GraphAction.smul_reverse_apply, hcback]
    exact units_one_ne_neg_one (hchain hcA)
  · -- u = -1, u' = 1 : `t⁻¹ c t` fixes `v` and `t v`, so `c` fixes the edge
    simp only [show ((1 : ℤˣ) : ℤ) = 1 from rfl, show ((-1 : ℤˣ) : ℤ) = -1 from rfl,
      zpow_one, zpow_neg_one] at h
    have h1 : ((t⁻¹ * (c : G)) • hnnEdge v t e).left = (t⁻¹ • hnnEdge v t e).left := by
      rw [total_smul_left, total_smul_left]
      show (t⁻¹ * (c : G)) • v = t⁻¹ • v
      rw [mul_smul, hcv]
    have h2 : ((t⁻¹ * (c : G)) • hnnEdge v t e).right = (t⁻¹ • hnnEdge v t e).right := by
      rw [total_smul_right, total_smul_right]
      show (t⁻¹ * (c : G)) • (t • v) = t⁻¹ • (t • v)
      rw [← mul_smul, inv_smul_smul]
      exact h
    have harrow : Quiver.homOfEq ((t⁻¹ * (c : G)) • hnnEdge v t e).hom h1 h2 =
        (t⁻¹ • hnnEdge v t e).hom :=
      Work.ORBassSerre.Tree.Seg.arrow_unique (hT := hT) _ _ _ _
    have hhom : HEq (((t⁻¹ * (c : G)) • hnnEdge v t e).hom) ((t⁻¹ • hnnEdge v t e).hom) :=
      heq_of_homOfEq_eq h1 h2 harrow
    have htot : (t⁻¹ * (c : G)) • hnnEdge v t e = t⁻¹ • hnnEdge v t e :=
      Quiver.Total.ext h1 h2 hhom
    have hce : (c : G) • hnnEdge v t e = hnnEdge v t e := by
      have h3 : (t⁻¹ * (c : G)) • hnnEdge v t e = t⁻¹ • hnnEdge v t e := htot
      calc (c : G) • hnnEdge v t e
          = (t * (t⁻¹ * (c : G))) • hnnEdge v t e := by rw [mul_inv_cancel_left]
          _ = t • ((t⁻¹ * (c : G)) • hnnEdge v t e) := by rw [mul_smul]
          _ = t • (t⁻¹ • hnnEdge v t e) := by rw [h3]
          _ = hnnEdge v t e := by rw [← mul_smul, mul_inv_cancel, one_smul]
    have hcB : c ∈ hnnB v t e := by
      rw [hnnB, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      exact hce
    exact units_neg_one_ne_one (hchain hcB)
  · -- u = u' = -1 : `t⁻¹ c t⁻¹` fixes `v`, so `c t⁻¹` inverts the fundamental edge
    simp only [show ((-1 : ℤˣ) : ℤ) = -1 from rfl, zpow_neg_one] at h
    have h1 : ((t⁻¹ * (c : G)) • hnnBack v t e).left = (t⁻¹ • hnnEdge v t e).left := by
      rw [hnnBack, total_smul_left, Quiver.Total.reverse_left, total_smul_right, total_smul_left]
      show (t⁻¹ * (c : G)) • (t⁻¹ • (t • v)) = t⁻¹ • v
      rw [inv_smul_smul, mul_smul, hcv]
    have h2 : ((t⁻¹ * (c : G)) • hnnBack v t e).right = (t⁻¹ • hnnEdge v t e).right := by
      rw [hnnBack, total_smul_right, Quiver.Total.reverse_right, total_smul_left,
        total_smul_right]
      show (t⁻¹ * (c : G)) • (t⁻¹ • v) = t⁻¹ • (t • v)
      rw [← mul_smul, h, inv_smul_smul]
    have harrow : Quiver.homOfEq ((t⁻¹ * (c : G)) • hnnBack v t e).hom h1 h2 =
        (t⁻¹ • hnnEdge v t e).hom :=
      Work.ORBassSerre.Tree.Seg.arrow_unique (hT := hT) _ _ _ _
    have hhom : HEq (((t⁻¹ * (c : G)) • hnnBack v t e).hom) ((t⁻¹ • hnnEdge v t e).hom) :=
      heq_of_homOfEq_eq h1 h2 harrow
    have htot : (t⁻¹ * (c : G)) • hnnBack v t e = t⁻¹ • hnnEdge v t e :=
      Quiver.Total.ext h1 h2 hhom
    have hce : (c : G) • hnnBack v t e = hnnEdge v t e := by
      have h3 : (t⁻¹ * (c : G)) • hnnBack v t e = t⁻¹ • hnnEdge v t e := htot
      calc (c : G) • hnnBack v t e
          = (t * (t⁻¹ * (c : G))) • hnnBack v t e := by rw [mul_inv_cancel_left]
          _ = t • ((t⁻¹ * (c : G)) • hnnBack v t e) := by rw [mul_smul]
          _ = t • (t⁻¹ • hnnEdge v t e) := by rw [h3]
          _ = hnnEdge v t e := by rw [← mul_smul, mul_inv_cancel, one_smul]
    have h4 : (c * t⁻¹ : G) • hnnEdge v t e = (hnnEdge v t e).reverse := by
      have h5 : (c : G) • ((t⁻¹ • hnnEdge v t e).reverse) = hnnEdge v t e := by
        rw [← hnnBack]; exact hce
      rw [Work.ORBassSerre.GraphAction.smul_reverse_apply] at h5
      have h6 := congrArg Quiver.Total.reverse h5
      rw [Quiver.Total.reverse_reverse] at h6
      rw [← h6, mul_smul]
    exact hninv (c * t⁻¹) (hnnEdge v t e) h4


/-! ## The walk attached to a reduced word -/

/-- The vertex list of the walk attached to a reduced HNN word, starting at `g • v`. -/
def hnnWalkVerts (v : V) (t : G) :
    List (ℤˣ × ↥(hnnH (G := G) v)) → G → List V
  | [], g => [g • v]
  | (u, c) :: rest, g => (g • v) :: hnnWalkVerts v t rest (g * t ^ (u : ℤ) * (c : G))

lemma hnnWalkVerts_length (v : V) (t : G) (l : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) :
    (hnnWalkVerts v t l g).length = l.length + 1 := by
  induction l generalizing g with
  | nil => rfl
  | cons hd tl ih => obtain ⟨u, c⟩ := hd; simp [hnnWalkVerts, ih]

/-- The `k`-th vertex of the walk. -/
def hnnWalkVert (v : V) (t : G) (l : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G)
    (k : Fin (l.length + 1)) : V :=
  (hnnWalkVerts v t l g).get ⟨k.val, by rw [hnnWalkVerts_length]; exact k.isLt⟩

/-- The product of the group elements attached to a reduced word. -/
def hnnWalkProd (t : G) (v : V) (l : List (ℤˣ × ↥(hnnH (G := G) v))) : G :=
  (l.map (fun x => t ^ (x.1 : ℤ) * (x.2 : G))).prod


/-! ## The HNN extension and the canonical comparison map -/

/-- The isomorphism `A → B` given by conjugation by `t`. -/
noncomputable def hnnPhi (v : V) (t : G) (e : v ⟶ t • v) :
    ↥(hnnA v t e) ≃* ↥(hnnB v t e) where
  toFun a := by
    have ha : (a : G) • (t⁻¹ • hnnEdge v t e) = t⁻¹ • hnnEdge v t e := by
      have h := a.2
      unfold hnnA at h
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at h
      unfold hnnBack at h
      rw [Work.ORBassSerre.GraphAction.smul_reverse_apply, total_reverse_inj] at h
      exact h
    have hge : (t * (a : G) * t⁻¹) • hnnEdge v t e = hnnEdge v t e := by
      calc (t * (a : G) * t⁻¹) • hnnEdge v t e
          = t • ((a : G) • (t⁻¹ • hnnEdge v t e)) := by rw [mul_smul, mul_smul]
        _ = t • (t⁻¹ • hnnEdge v t e) := by rw [ha]
        _ = hnnEdge v t e := by rw [← mul_smul, mul_inv_cancel, one_smul]
    refine ⟨⟨t * (a : G) * t⁻¹, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      have h := congrArg Quiver.Total.left hge
      rw [total_smul_left] at h
      simpa only [hnnEdge] using h
    · unfold hnnB
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      exact hge
  invFun b := by
    have hb : (b : G) • hnnEdge v t e = hnnEdge v t e := by
      have h := b.2
      unfold hnnB at h
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at h
      exact h
    have hge : (t⁻¹ * (b : G) * t) • hnnBack v t e = hnnBack v t e := by
      unfold hnnBack
      rw [Work.ORBassSerre.GraphAction.smul_reverse_apply, total_reverse_inj,
        ← mul_smul, mul_assoc, mul_inv_cancel, mul_one, mul_smul, hb]
    refine ⟨⟨t⁻¹ * (b : G) * t, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      have h1 : (b : G) • (t • v) = t • v := by
        have h2 := congrArg Quiver.Total.right hb
        rw [total_smul_right] at h2
        simpa only [hnnEdge] using h2
      calc (t⁻¹ * (b : G) * t) • v = t⁻¹ • ((b : G) • (t • v)) := by rw [mul_smul, mul_smul]
        _ = t⁻¹ • (t • v) := by rw [h1]
        _ = v := by rw [inv_smul_smul]
    · unfold hnnA
      rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      exact hge
  left_inv a := by
    ext
    group
  right_inv b := by
    ext
    group
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    group

/-- The comparison map from the HNN extension of the vertex group to `G`. -/
noncomputable def hnnMap (v : V) (t : G) (e : v ⟶ t • v) :
    HNNExtension ↥(hnnH (G := G) v) (hnnA v t e) (hnnB v t e) (hnnPhi v t e) →* G :=
  HNNExtension.lift (hnnH (G := G) v).subtype t (by
    intro a
    change t * ((a : ↥(hnnH (G := G) v)) : G) =
      (t * ((a : ↥(hnnH (G := G) v)) : G) * t⁻¹) * t
    group)

@[simp] lemma hnnMap_of (v : V) (t : G) (e : v ⟶ t • v) (h : ↥(hnnH (G := G) v)) :
    hnnMap v t e (HNNExtension.of h) = (h : G) :=
  HNNExtension.lift_of _ _ _ h

@[simp] lemma hnnMap_t (v : V) (t : G) (e : v ⟶ t • v) :
    hnnMap v t e HNNExtension.t = t :=
  HNNExtension.lift_t _ _ _


/-! ## The walk is a geodesic, and closed walks are impossible -/
/-- Vertices of the walk, as a function of the list and the starting element. -/
lemma hnnWalkVert_zero (v : V) (t : G) (l : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) :
    hnnWalkVert v t l g 0 = g • v := by
  cases l with
  | nil => simp [hnnWalkVert, hnnWalkVerts]
  | cons hd tl =>
      obtain ⟨u, c⟩ := hd
      simp [hnnWalkVert, hnnWalkVerts]

/-- The source of a step of the walk. -/
lemma hnnStep_left (v : V) (t : G) (e : v ⟶ t • v) (u : ℤˣ) :
    (hnnStep v t e u).left = v := by
  rcases Int.units_eq_one_or u with h | h <;> subst h
  · simp [hnnStep, hnnEdge]
  · simp [hnnStep, hnnBack, hnnEdge]

/-- The target of a step of the walk. -/
lemma hnnStep_right (v : V) (t : G) (e : v ⟶ t • v) (u : ℤˣ) :
    (hnnStep v t e u).right = t ^ (u : ℤ) • v := by
  rcases Int.units_eq_one_or u with h | h <;> subst h
  · simp [hnnStep, hnnEdge]
  · rw [show (((-1 : ℤˣ) : ℤ)) = -1 from rfl, zpow_neg_one]
    simp [hnnStep, hnnBack, hnnEdge]

/-- The first vertex of a walk beginning with the letter `(u, c)`. -/
lemma hnnWalkVert_cons_zero (v : V) (t : G) (u : ℤˣ) (c : ↥(hnnH (G := G) v))
    (tl : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) :
    hnnWalkVert v t ((u, c) :: tl) g ⟨0, by simp only [List.length_cons]; omega⟩ = g • v := by
  simp [hnnWalkVert, hnnWalkVerts]

/-- The successor step of the walk. -/
lemma hnnWalkVert_cons_succ (v : V) (t : G) (u : ℤˣ) (c : ↥(hnnH (G := G) v))
    (tl : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) (j : Fin (tl.length + 1)) :
    hnnWalkVert v t ((u, c) :: tl) g j.succ =
      hnnWalkVert v t tl (g * t ^ (u : ℤ) * (c : G)) j := by
  show (hnnWalkVerts v t ((u, c) :: tl) g).get _ =
    (hnnWalkVerts v t tl (g * t ^ (u : ℤ) * (c : G))).get _
  simp only [hnnWalkVerts]
  exact List.get_cons_succ

/-- The second vertex of a walk beginning with the letter `(u, c)`. -/
lemma hnnWalkVert_one (v : V) (t : G) (u : ℤˣ) (c : ↥(hnnH (G := G) v))
    (tl : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) :
    hnnWalkVert v t ((u, c) :: tl) g ⟨1, by simp only [List.length_cons]; omega⟩ =
      (g * t ^ (u : ℤ) * (c : G)) • v :=
  (hnnWalkVert_cons_succ v t u c tl g ⟨0, by omega⟩).trans
    (hnnWalkVert_zero v t tl (g * t ^ (u : ℤ) * (c : G)))

/-- The third vertex of a walk beginning with the letters `(u, c)` and `(u', c')`. -/
lemma hnnWalkVert_two (v : V) (t : G) (u u' : ℤˣ) (c c' : ↥(hnnH (G := G) v))
    (tl : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) :
    hnnWalkVert v t ((u, c) :: (u', c') :: tl) g
        ⟨2, by simp only [List.length_cons]; omega⟩ =
      g • ((t ^ (u : ℤ) * (c : G) * t ^ (u' : ℤ)) • v) := by
  have h1 : hnnWalkVert v t ((u, c) :: (u', c') :: tl) g
        ⟨2, by simp only [List.length_cons]; omega⟩ =
      hnnWalkVert v t ((u', c') :: tl) (g * t ^ (u : ℤ) * (c : G))
        ⟨1, by simp only [List.length_cons]; omega⟩ :=
    hnnWalkVert_cons_succ v t u c ((u', c') :: tl) g
      ⟨1, by simp only [List.length_cons]; omega⟩
  have h2 : hnnWalkVert v t ((u', c') :: tl) (g * t ^ (u : ℤ) * (c : G))
        ⟨1, by simp only [List.length_cons]; omega⟩ =
      hnnWalkVert v t tl ((g * t ^ (u : ℤ) * (c : G)) * t ^ (u' : ℤ) * (c' : G))
        ⟨0, by omega⟩ :=
    hnnWalkVert_cons_succ v t u' c' tl (g * t ^ (u : ℤ) * (c : G))
      ⟨0, by omega⟩
  have h3 : hnnWalkVert v t tl ((g * t ^ (u : ℤ) * (c : G)) * t ^ (u' : ℤ) * (c' : G))
        ⟨0, by omega⟩ =
      ((g * t ^ (u : ℤ) * (c : G)) * t ^ (u' : ℤ) * (c' : G)) • v :=
    hnnWalkVert_zero v t tl _
  rw [h1, h2, h3,
    show (g * t ^ (u : ℤ) * (c : G)) * t ^ (u' : ℤ) * (c' : G)
        = g * (t ^ (u : ℤ) * (c : G) * t ^ (u' : ℤ)) * (c' : G) from by group,
    mul_smul, mem_hnnH v c', mul_smul]

/-- Consecutive vertices of the walk are joined by an arrow (numerically indexed form). -/
lemma hnnWalkVert_adjN (v : V) (t : G) (e : v ⟶ t • v) :
    ∀ (l : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) (k : ℕ) (hk : k + 1 ≤ l.length),
      Nonempty (hnnWalkVert v t l g ⟨k, by omega⟩ ⟶
        hnnWalkVert v t l g ⟨k + 1, by omega⟩) := by
  intro l
  induction l with
  | nil => intro g k hk; simp at hk
  | cons hd tl ih =>
    obtain ⟨u, c⟩ := hd
    intro g k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      refine ⟨Quiver.homOfEq
        (Work.ORBassSerre.GraphAction.smulArrow g (hnnStep v t e u).hom) ?_ ?_⟩
      · rw [hnnStep_left, hnnWalkVert_cons_zero]
      · have h1 : hnnWalkVert v t ((u, c) :: tl) g ⟨0 + 1, by omega⟩ =
            (g * t ^ (u : ℤ) * (c : G)) • v :=
          hnnWalkVert_one v t u c tl g
        rw [hnnStep_right, h1, ← mul_smul,
          mul_smul (g * t ^ (u : ℤ)) (c : G) v, mem_hnnH v c]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hk' : j + 1 ≤ tl.length := by
        simp only [List.length_cons] at hk
        omega
      have h1 : hnnWalkVert v t ((u, c) :: tl) g ⟨j + 1, by omega⟩ =
          hnnWalkVert v t tl (g * t ^ (u : ℤ) * (c : G)) ⟨j, by omega⟩ :=
        hnnWalkVert_cons_succ v t u c tl g ⟨j, by omega⟩
      have h2 : hnnWalkVert v t ((u, c) :: tl) g ⟨j + 1 + 1, by omega⟩ =
          hnnWalkVert v t tl (g * t ^ (u : ℤ) * (c : G)) ⟨j + 1, by omega⟩ :=
        hnnWalkVert_cons_succ v t u c tl g ⟨j + 1, by omega⟩
      rw [h1, h2]
      exact ih (g * t ^ (u : ℤ) * (c : G)) j hk'

/-- Consecutive vertices of the walk are joined by an arrow. -/
lemma hnnWalkVert_adj' (v : V) (t : G) (e : v ⟶ t • v)
    (l : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G) (k : Fin l.length) :
    Nonempty (hnnWalkVert v t l g k.castSucc ⟶ hnnWalkVert v t l g k.succ) :=
  hnnWalkVert_adjN v t e l g k.val k.isLt

/-- The last vertex of the walk is the translate of `v` by the accumulated product. -/
lemma hnnWalkVert_last' (v : V) (t : G) :
    ∀ (l : List (ℤˣ × ↥(hnnH (G := G) v))) (g : G),
      hnnWalkVert v t l g ⟨l.length, by omega⟩ = (g * hnnWalkProd t v l) • v := by
  intro l
  induction l with
  | nil =>
    intro g
    exact (hnnWalkVert_zero v t [] g).trans (by simp [hnnWalkProd])
  | cons hd tl ih =>
    obtain ⟨u, c⟩ := hd
    intro g
    have h1 : hnnWalkVert v t ((u, c) :: tl) g ⟨((u, c) :: tl).length, by omega⟩ =
        hnnWalkVert v t tl (g * t ^ (u : ℤ) * (c : G)) ⟨tl.length, by omega⟩ :=
      hnnWalkVert_cons_succ v t u c tl g ⟨tl.length, by omega⟩
    rw [h1, ih (g * t ^ (u : ℤ) * (c : G))]
    have hP : hnnWalkProd t v ((u, c) :: tl)
        = (t ^ (u : ℤ) * (c : G)) * hnnWalkProd t v tl := by
      simp only [hnnWalkProd, List.map_cons, List.prod_cons]
    rw [hP]
    congr 1
    group

/-- The walk attached to a reduced word never immediately backtracks (numerically indexed). -/
lemma hnnWalkVert_noReturnN (v : V) (t : G) (e : v ⟶ t • v)
    (hT : Work.ORBassSerre.IsTree V) (hninv : Work.ORBassSerre.ActsWithoutInversions G V) :
    ∀ (l : List (ℤˣ × ↥(hnnH (G := G) v)))
      (hchain : l.IsChain (fun a b =>
        a.2 ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) a.1 → a.1 = b.1))
      (g : G) (k : ℕ) (hk : k + 2 ≤ l.length),
      hnnWalkVert v t l g ⟨k, by omega⟩ ≠ hnnWalkVert v t l g ⟨k + 2, by omega⟩ := by
  intro l
  induction l with
  | nil => intro hchain g k hk; simp at hk
  | cons hd tl ih =>
    obtain ⟨u, c⟩ := hd
    intro hchain g k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      cases tl with
      | nil => simp at hk
      | cons hd' tl' =>
        obtain ⟨u', c'⟩ := hd'
        have hR : c ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) u → u = u' :=
          (List.isChain_cons.mp hchain).1 (u', c') (by simp)
        have hne := hnn_two_step_ne hT hninv u u' c hR
        intro heq
        have e1 : hnnWalkVert v t ((u, c) :: (u', c') :: tl') g ⟨0, by omega⟩ = g • v :=
          hnnWalkVert_cons_zero v t u c ((u', c') :: tl') g
        have e2 : hnnWalkVert v t ((u, c) :: (u', c') :: tl') g ⟨0 + 2, by omega⟩ =
            g • ((t ^ (u : ℤ) * (c : G) * t ^ (u' : ℤ)) • v) :=
          hnnWalkVert_two v t u u' c c' tl' g
        rw [e1, e2] at heq
        exact hne (MulAction.injective g heq.symm)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hk' : j + 2 ≤ tl.length := by
        simp only [List.length_cons] at hk
        omega
      have hchain' : tl.IsChain (fun a b =>
          a.2 ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) a.1 → a.1 = b.1) :=
        (List.isChain_cons.mp hchain).2
      have h1 : hnnWalkVert v t ((u, c) :: tl) g ⟨j + 1, by omega⟩ =
          hnnWalkVert v t tl (g * t ^ (u : ℤ) * (c : G)) ⟨j, by omega⟩ :=
        hnnWalkVert_cons_succ v t u c tl g ⟨j, by omega⟩
      have h2 : hnnWalkVert v t ((u, c) :: tl) g ⟨j + 1 + 2, by omega⟩ =
          hnnWalkVert v t tl (g * t ^ (u : ℤ) * (c : G)) ⟨j + 2, by omega⟩ :=
        hnnWalkVert_cons_succ v t u c tl g ⟨j + 2, by omega⟩
      rw [h1, h2]
      exact ih hchain' (g * t ^ (u : ℤ) * (c : G)) j hk'

/-- The walk attached to a reduced word never immediately backtracks. -/
lemma hnnWalkVert_noReturn' (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    {v : V} {t : G} {e : v ⟶ t • v} (l : List (ℤˣ × ↥(hnnH (G := G) v)))
    (hchain : l.IsChain (fun a b =>
      a.2 ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) a.1 → a.1 = b.1))
    (g : G) (k : ℕ) (hk : k + 2 ≤ l.length) :
    hnnWalkVert v t l g ⟨k, by omega⟩ ≠ hnnWalkVert v t l g ⟨k + 2, by omega⟩ :=
  hnnWalkVert_noReturnN v t e hT hninv l hchain g k hk

/-- **Combinatorial core of the geodesic statement.**  A walk of length `m` in which no vertex
repeats at distance two yields a reduced path of length `m` between its endpoints, whose last
arrow is the last arrow of the walk. -/
private lemma geodesic_aux :
    ∀ (m : ℕ) (z : Fin (m + 1) → V)
      (hadj : ∀ k : Fin m, Nonempty (z k.castSucc ⟶ z k.succ))
      (hnoret : ∀ (k : ℕ) (hk : k + 2 ≤ m), z ⟨k, by omega⟩ ≠ z ⟨k + 2, by omega⟩),
      ∃ p : Quiver.Path (z 0) (z ⟨m, by omega⟩),
        p.IsReduced ∧ p.length = m ∧
          (m = 0 ∨ ∃ (p' : Quiver.Path (z 0) (z ⟨m - 1, by omega⟩))
              (g : z ⟨m - 1, by omega⟩ ⟶ z ⟨m, by omega⟩), p = p'.cons g) := by
  intro m
  induction m with
  | zero =>
    intro z hadj hnoret
    exact ⟨Quiver.Path.nil, Quiver.Path.IsReduced.nil _, rfl, Or.inl rfl⟩
  | succ m ih =>
    intro z hadj hnoret
    let z' : Fin (m + 1) → V := fun i => z i.castSucc
    have hadj' : ∀ k : Fin m, Nonempty (z' k.castSucc ⟶ z' k.succ) :=
      fun k => hadj ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
    have hnoret' : ∀ (k : ℕ) (hk : k + 2 ≤ m), z' ⟨k, by omega⟩ ≠ z' ⟨k + 2, by omega⟩ :=
      fun k hk => hnoret k (by omega)
    obtain ⟨p, hp_red, hp_len, hp_dec⟩ := ih z' hadj' hnoret'
    let f : z (⟨m, by omega⟩ : Fin (m + 1)).castSucc ⟶ z (⟨m, by omega⟩ : Fin (m + 1)).succ :=
      (hadj ⟨m, by omega⟩).some
    have hred : (p.cons f).IsReduced := by
      have hf_red : f.toPath.IsReduced := Quiver.Path.IsReduced.of_length_lt_two (by simp)
      intro w hw
      rw [← Quiver.Path.comp_toPath_eq_cons] at hw
      obtain ⟨x, g, u', v', hu'_eq, hv'_eq, -⟩ :=
        Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_comp_junction hp_red hf_red hw
      have hv_len : v'.length = 0 := by
        have h := congrArg Quiver.Path.length hv'_eq
        rw [Quiver.Path.length_comp, Quiver.Path.length_toPath,
          Quiver.Path.length_toPath] at h
        omega
      have hx2 : x = z ⟨m + 1, by omega⟩ := Quiver.Path.eq_of_length_zero v' hv_len
      have hu_len : m = u'.length + 1 := by
        have h := congrArg Quiver.Path.length hu'_eq
        rw [Quiver.Path.length_cons] at h
        omega
      rcases hp_dec with hm0 | ⟨p_dec, g_dec, hp_dec_eq⟩
      · omega
      · have hf2 : u'.cons g = p_dec.cons g_dec := hu'_eq.symm.trans hp_dec_eq
        have hx1 : x = z' ⟨m - 1, by omega⟩ := Quiver.Path.obj_eq_of_cons_eq_cons hf2
        have hx1' : x = z ⟨m - 1, by omega⟩ := hx1
        have hfin : (⟨(m - 1) + 2, by omega⟩ : Fin (m + 2)) = ⟨m + 1, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        have hne := hnoret (m - 1) (by omega)
        rw [hfin] at hne
        exact hne (hx1'.symm.trans hx2)
    have hlen : (p.cons f).length = m + 1 := by
      rw [Quiver.Path.length_cons, hp_len]
    exact ⟨p.cons f, hred, hlen, Or.inr ⟨p, f, rfl⟩⟩

/-- In a tree, a walk that never immediately backtracks has vertex `k` at distance exactly `k`
from the first vertex. -/
lemma geodesic_length_walk' (hT : Work.ORBassSerre.IsTree V) {n : ℕ} (z : Fin (n + 1) → V)
    (hadj : ∀ k : Fin n, Nonempty (z k.castSucc ⟶ z k.succ))
    (hnoret : ∀ (k : ℕ) (hk : k + 2 ≤ n), z ⟨k, by omega⟩ ≠ z ⟨k + 2, by omega⟩) :
    ∀ k : Fin (n + 1), (hT.geodesic (z 0) (z k)).length = k.val := by
  intro k
  let zk : Fin (k.val + 1) → V := fun i => z ⟨i.val, by omega⟩
  have hadjk : ∀ j : Fin k.val, Nonempty (zk j.castSucc ⟶ zk j.succ) :=
    fun j => hadj ⟨j.val, by omega⟩
  have hnoretk : ∀ (j : ℕ) (hj : j + 2 ≤ k.val), zk ⟨j, by omega⟩ ≠ zk ⟨j + 2, by omega⟩ :=
    fun j hj => hnoret j (by omega)
  obtain ⟨p, hp_red, hp_len, -⟩ := geodesic_aux k.val zk hadjk hnoretk
  have hpk : p = hT.geodesic (z 0) (z k) := hT.eq_geodesic hp_red
  exact (congrArg Quiver.Path.length hpk).symm.trans hp_len


/-- A closed walk attached to a reduced word is trivial. -/
theorem hnnWalk_closed_impossible (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    {v : V} {t : G} {e : v ⟶ t • v}
    (l : List (ℤˣ × ↥(hnnH (G := G) v)))
    (hchain : l.IsChain (fun a b =>
      a.2 ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) a.1 → a.1 = b.1))
    (g : G) (hg : g • v = v)
    (hclosed : (g * hnnWalkProd t v l) • v = v) :
    l = [] := by
  by_contra hnil
  have hadj : ∀ k : Fin l.length, Nonempty
      (hnnWalkVert v t l g k.castSucc ⟶ hnnWalkVert v t l g k.succ) :=
    fun k => hnnWalkVert_adj' v t e l g k
  have hnoret : ∀ (k : ℕ) (hk : k + 2 ≤ l.length),
      hnnWalkVert v t l g ⟨k, by omega⟩ ≠ hnnWalkVert v t l g ⟨k + 2, by omega⟩ :=
    fun k hk => hnnWalkVert_noReturn' hT hninv l hchain g k hk
  have hgeo : ∀ k : Fin (l.length + 1),
      (hT.geodesic (hnnWalkVert v t l g 0) (hnnWalkVert v t l g k)).length = k.val :=
    geodesic_length_walk' hT (fun k => hnnWalkVert v t l g k) hadj hnoret
  have hz0 : hnnWalkVert v t l g 0 = v := by
    rw [hnnWalkVert_zero]
    exact hg
  have hzlast : hnnWalkVert v t l g ⟨l.length, by omega⟩ = v := by
    rw [hnnWalkVert_last']
    exact hclosed
  have hlen0 : l.length = 0 := by
    have h := hgeo ⟨l.length, by omega⟩
    rw [hzlast, hz0] at h
    have h2 : (hT.geodesic v v).length = l.length := by simpa using h
    rw [IsTree.geodesic_self] at h2
    simpa using h2.symm
  exact hnil (List.eq_nil_of_length_eq_zero hlen0)

set_option maxHeartbeats 1000000 in
/-- **Key step.**  An element of the HNN extension whose image in `G` fixes `v` lies in the image
of the vertex group. -/
theorem hnnMap_mem_range_of_mem_stabilizer (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    {v : V} {t : G} {e : v ⟶ t • v}
    (x : HNNExtension ↥(hnnH (G := G) v) (hnnA v t e) (hnnB v t e) (hnnPhi v t e))
    (hx : hnnMap v t e x ∈ hnnH (G := G) v) :
    x ∈ HNNExtension.of.range := by
  classical
  obtain ⟨d⟩ := HNNExtension.NormalWord.TransversalPair.nonempty ↥(hnnH (G := G) v)
    (hnnA v t e) (hnnB v t e)
  let w : HNNExtension.NormalWord d := (HNNExtension.NormalWord.equiv (hnnPhi v t e) d) x
  have hxw : HNNExtension.NormalWord.ReducedWord.prod (hnnPhi v t e) w.toReducedWord = x :=
    (HNNExtension.NormalWord.equiv (hnnPhi v t e) d).left_inv x
  have hprod : hnnMap v t e x =
      ((w.head : ↥(hnnH (G := G) v)) : G) * hnnWalkProd t v w.toList := by
    rw [← hxw, HNNExtension.NormalWord.ReducedWord.prod, map_mul, MonoidHom.map_list_prod,
      List.map_map, hnnWalkProd]
    rw [hnnMap_of]
    congr 1
    apply congrArg List.prod
    apply List.map_congr_left
    intro z _
    simp only [Function.comp_apply, map_mul, map_zpow, hnnMap_of, hnnMap_t]
  have hchainW : w.toList.IsChain (fun a b =>
      a.2 ∈ HNNExtension.toSubgroup (hnnA v t e) (hnnB v t e) a.1 → a.1 = b.1) :=
    w.toReducedWord.chain
  have hg0 : ((w.head : ↥(hnnH (G := G) v)) : G) • v = v := mem_hnnH v w.head
  have hclosed : (((w.head : ↥(hnnH (G := G) v)) : G) * hnnWalkProd t v w.toList) • v = v := by
    have hmem : ((w.head : ↥(hnnH (G := G) v)) : G) * hnnWalkProd t v w.toList ∈
        hnnH (G := G) v := by rw [← hprod]; exact hx
    exact MulAction.mem_stabilizer_iff.mp hmem
  have hnil := hnnWalk_closed_impossible hT hninv w.toList hchainW
    ((w.head : ↥(hnnH (G := G) v)) : G) hg0 hclosed
  refine ⟨w.head, ?_⟩
  rw [← hxw, HNNExtension.NormalWord.ReducedWord.prod, hnil]
  simp

/-- **Injectivity of the comparison map.** -/
theorem hnnMap_injective (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    {v : V} {t : G} {e : v ⟶ t • v} :
    Function.Injective (hnnMap v t e) := by
  intro x y hxy
  have h1 : hnnMap v t e (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 : x * y⁻¹ ∈ HNNExtension.of.range :=
    hnnMap_mem_range_of_mem_stabilizer hT hninv (x * y⁻¹) (by rw [h1]; exact one_mem _)
  obtain ⟨h, hh⟩ := h2
  have h3 : (h : G) = 1 := by
    have h4 := h1
    rw [← hh, hnnMap_of] at h4
    exact h4
  have h5 : h = 1 := Subtype.ext h3
  have h6 : x * y⁻¹ = 1 := by rw [← hh, h5, map_one]
  rwa [mul_inv_eq_one] at h6


/-- The stabiliser of the fundamental edge, viewed inside the vertex stabiliser. -/
lemma stabilizer_hnnEdge_le (v : V) (t : G) (e : v ⟶ t • v) :
    MulAction.stabilizer G (hnnEdge v t e) ≤ hnnH (G := G) v := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [hnnH, MulAction.mem_stabilizer_iff]
  have h := congrArg Quiver.Total.left hg
  rw [total_smul_left] at h
  simpa only [hnnEdge] using h

/-- The stabiliser of the conjugated reversed edge, viewed inside the vertex stabiliser. -/
lemma stabilizer_hnnBack_le (v : V) (t : G) (e : v ⟶ t • v) :
    MulAction.stabilizer G (hnnBack v t e) ≤ hnnH (G := G) v := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [hnnH, MulAction.mem_stabilizer_iff]
  have h := congrArg Quiver.Total.left hg
  rw [total_smul_left] at h
  unfold hnnBack at h
  rw [Quiver.Total.reverse_left, total_smul_right] at h
  simpa only [hnnEdge, inv_smul_smul] using h

/-- The two associated subgroups of the HNN description are finitely generated. -/
lemma hnnAB_fg' (v : V) (t : G) (e : v ⟶ t • v)
    (hedge : ∀ f : Quiver.Total V, Group.FG (MulAction.stabilizer G f)) :
    Group.FG ↥(hnnA v t e) ∧ Group.FG ↥(hnnB v t e) := by
  constructor
  · haveI : Group.FG ↥(MulAction.stabilizer G (hnnBack v t e)) := hedge (hnnBack v t e)
    let g : ↥(MulAction.stabilizer G (hnnBack v t e)) →* ↥(hnnA v t e) :=
      { toFun := fun k => ⟨⟨(k : G), stabilizer_hnnBack_le v t e k.2⟩, k.2⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
    have hsurj : Function.Surjective g := by
      intro a
      exact ⟨⟨(a : G), a.2⟩, by ext; rfl⟩
    exact Group.fg_of_surjective hsurj
  · haveI : Group.FG ↥(MulAction.stabilizer G (hnnEdge v t e)) := hedge (hnnEdge v t e)
    let g : ↥(MulAction.stabilizer G (hnnEdge v t e)) →* ↥(hnnB v t e) :=
      { toFun := fun k => ⟨⟨(k : G), stabilizer_hnnEdge_le v t e k.2⟩, k.2⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
    have hsurj : Function.Surjective g := by
      intro a
      exact ⟨⟨(a : G), a.2⟩, by ext; rfl⟩
    exact Group.fg_of_surjective hsurj

lemma smul_hnnEdge_left (v : V) (t : G) (e : v ⟶ t • v) (g : G) :
    (g • hnnEdge v t e).left = g • v := by
  rw [total_smul_left]; rfl

lemma smul_hnnEdge_right (v : V) (t : G) (e : v ⟶ t • v) (g : G) :
    (g • hnnEdge v t e).right = g • (t • v) := by
  rw [total_smul_right]; rfl

lemma smul_hnnEdge_reverse_left (v : V) (t : G) (e : v ⟶ t • v) (g : G) :
    (g • (hnnEdge v t e).reverse).left = g • (t • v) := by
  rw [Work.ORBassSerre.GraphAction.smul_reverse_apply, Quiver.Total.reverse_left,
    total_smul_right]
  rfl

lemma smul_hnnEdge_reverse_right (v : V) (t : G) (e : v ⟶ t • v) (g : G) :
    (g • (hnnEdge v t e).reverse).right = g • v := by
  rw [Work.ORBassSerre.GraphAction.smul_reverse_apply, Quiver.Total.reverse_right,
    total_smul_left]
  rfl

set_option maxHeartbeats 1000000 in
/-- `G` is generated by the vertex group and `t`. -/
lemma closure_stabilizer_hnn' [Nonempty V] (hT : Work.ORBassSerre.IsTree V)
    (v : V) (t : G) (e : v ⟶ t • v)
    (hcover : ∀ x : V, ∃ g : G, g • v = x)
    (hedges : ∀ (x y : V) (f : x ⟶ y),
      (∃ g : G, g • hnnEdge v t e = Quiver.Total.mk x y f) ∨
      (∃ g : G, g • (hnnEdge v t e).reverse = Quiver.Total.mk x y f)) :
    Subgroup.closure ((hnnH (G := G) v : Set G) ∪ {t}) = ⊤ := by
  classical
  set K : Subgroup G := Subgroup.closure ((hnnH (G := G) v : Set G) ∪ {t}) with hK
  have hHle : hnnH (G := G) v ≤ K := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl hx)
  have htK : t ∈ K := Subgroup.subset_closure (Or.inr (Set.mem_singleton_iff.mpr rfl))
  set S : Set V := {x | ∃ k : G, k ∈ K ∧ k • v = x} with hS
  have hSclosed : ∀ ⦃a b : V⦄, a ∈ S → (a ⟶ b) → b ∈ S := by
    intro a b ha f
    obtain ⟨k, hkK, hka⟩ := ha
    rcases hedges a b f with ⟨g, hg⟩ | ⟨g, hg⟩
    · -- `f` is a translate of the fundamental edge
      have hleft : g • v = a := by
        have h := congrArg Quiver.Total.left hg
        rw [smul_hnnEdge_left] at h
        exact h
      have hb : (g • hnnEdge v t e).right = b := congrArg Quiver.Total.right hg
      have hright : (g • hnnEdge v t e).right = (g * t) • v := by
        rw [smul_hnnEdge_right, ← mul_smul]
      have hgK : g ∈ K := by
        have hmem : k⁻¹ * g ∈ hnnH (G := G) v := by
          rw [MulAction.mem_stabilizer_iff, mul_smul, hleft, ← hka, inv_smul_smul]
        have h2 : k * (k⁻¹ * g) ∈ K := K.mul_mem hkK (hHle hmem)
        rwa [mul_inv_cancel_left] at h2
      exact ⟨g * t, K.mul_mem hgK htK, by rw [← hright]; exact hb⟩
    · -- `f` is a translate of the reverse of the fundamental edge
      have hleft : (g * t) • v = a := by
        have h := congrArg Quiver.Total.left hg
        rw [smul_hnnEdge_reverse_left, ← mul_smul] at h
        exact h
      have hb : (g • (hnnEdge v t e).reverse).right = b := congrArg Quiver.Total.right hg
      have hright : (g • (hnnEdge v t e).reverse).right = g • v :=
        smul_hnnEdge_reverse_right v t e g
      have hgK : g ∈ K := by
        have hmem : (g * t)⁻¹ * k ∈ hnnH (G := G) v := by
          rw [MulAction.mem_stabilizer_iff, mul_smul, hka, ← hleft, inv_smul_smul]
        have hmemK : (g * t)⁻¹ * k ∈ K := hHle hmem
        have h2 : k * ((g * t)⁻¹ * k)⁻¹ ∈ K := K.mul_mem hkK (K.inv_mem hmemK)
        have h3 : g * t ∈ K := by
          rwa [show k * ((g * t)⁻¹ * k)⁻¹ = g * t by group] at h2
        have h4 : g ∈ K := by
          have h5 := K.mul_mem h3 (K.inv_mem htK)
          rwa [show (g * t) * t⁻¹ = g by group] at h5
        exact h4
      exact ⟨g, hgK, by rw [← hright]; exact hb⟩
  have hSV : S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨p⟩ := hT.1 v x
    have hmem : ∀ {a b : V}, a ∈ S → Quiver.Path a b → b ∈ S := by
      intro a b ha p
      induction p with
      | nil => exact ha
      | cons p f ih => exact hSclosed ih f
    exact hmem ⟨1, K.one_mem, by rw [one_smul]⟩ p
  rw [eq_top_iff]
  intro g _
  have hgv : g • v ∈ S := by rw [hSV]; trivial
  obtain ⟨k, hkK, hkv⟩ := hgv
  have hmem : k⁻¹ * g ∈ hnnH (G := G) v := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hkv, inv_smul_smul]
  have h2 : k * (k⁻¹ * g) ∈ K := K.mul_mem hkK (hHle hmem)
  rwa [mul_inv_cancel_left] at h2

set_option maxHeartbeats 1000000 in
/-- The comparison map from the HNN extension onto `G` is surjective. -/
lemma hnnMap_surjective' [Nonempty V] (hT : Work.ORBassSerre.IsTree V)
    (v : V) (t : G) (e : v ⟶ t • v)
    (hcover : ∀ x : V, ∃ g : G, g • v = x)
    (hedges : ∀ (x y : V) (f : x ⟶ y),
      (∃ g : G, g • Quiver.Total.mk v (t • v) e = Quiver.Total.mk x y f) ∨
      (∃ g : G, g • (Quiver.Total.mk v (t • v) e).reverse = Quiver.Total.mk x y f)) :
    Function.Surjective (hnnMap v t e) := by
  have hgen := closure_stabilizer_hnn' hT v t e hcover (by
    intro x y f
    rcases hedges x y f with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Or.inl ⟨g, hg⟩
    · exact Or.inr ⟨g, hg⟩)
  have hle : Subgroup.closure ((hnnH (G := G) v : Set G) ∪ {t}) ≤ (hnnMap v t e).range := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact ⟨HNNExtension.of ⟨x, hx⟩, hnnMap_of v t e ⟨x, hx⟩⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨HNNExtension.t, by rw [hnnMap_t, hx]⟩
  have htop : (hnnMap v t e).range = ⊤ := le_antisymm le_top (hgen ▸ hle)
  intro y
  have : y ∈ (hnnMap v t e).range := by rw [htop]; trivial
  exact this

open Quiver

/-- **The HNN (loop) case of the Bass--Serre structure theorem.**
Let `G` act on a tree `V` without inversions, with finitely presented vertex stabilisers and
finitely generated edge stabilisers.  Suppose the action is transitive on vertices, realised by
`v`, and that there is exactly one orbit of *geometric* edges, realised by an arrow `e : v ⟶ t • v`
whose two endpoints lie in the same vertex orbit (so the quotient graph `V/G` is a rose with one
petal, and every arrow is a translate of `e` or of its reverse).  Then `G` is generated by
`Stab(v)` and `t`, with the HNN relations coming from `Stab(e)` and its conjugate by `t`, hence
finitely presented. -/
theorem isFinitelyPresented_of_hnn_case {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    [Nonempty V] (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (hstab : ∀ x : V, Group.IsFinitelyPresented (MulAction.stabilizer G x))
    (hedge : ∀ f : Quiver.Total V, Group.FG (MulAction.stabilizer G f))
    (v : V) (t : G) (e : v ⟶ t • v)
    (hcover : ∀ x : V, ∃ g : G, g • v = x)
    (hedges : ∀ (x y : V) (f : x ⟶ y),
      (∃ g : G, g • Quiver.Total.mk v (t • v) e = Quiver.Total.mk x y f) ∨
      (∃ g : G, g • (Quiver.Total.mk v (t • v) e).reverse = Quiver.Total.mk x y f)) :
    Group.IsFinitelyPresented G := by
  haveI : Group.IsFinitelyPresented ↥(hnnH (G := G) v) := hstab v
  obtain ⟨hA, hB⟩ := hnnAB_fg' v t e hedge
  haveI : Group.FG ↥(hnnA v t e) := hA
  haveI : Group.FG ↥(hnnB v t e) := hB
  haveI : Group.IsFinitelyPresented
      (HNNExtension ↥(hnnH (G := G) v) (hnnA v t e) (hnnB v t e) (hnnPhi v t e)) :=
    Work.ORBassSerre.FP.hnn_isFinitelyPresented (hnnA v t e) (hnnB v t e) (hnnPhi v t e)
  have hsurj : Function.Surjective (hnnMap v t e) := hnnMap_surjective' hT v t e hcover hedges
  have hinj : Function.Injective (hnnMap v t e) := hnnMap_injective hT hninv
  have hker : (hnnMap v t e).ker.IsFinitelyNormallyGenerated := by
    rw [(MonoidHom.ker_eq_bot_iff (hnnMap v t e)).mpr hinj]
    exact ⟨∅, Set.finite_empty, Subgroup.normalClosure_empty⟩
  exact Group.IsFinitelyPresented.of_surjective (hnnMap v t e) hsurj hker

end Work.ORBassSerre.Action.Structure

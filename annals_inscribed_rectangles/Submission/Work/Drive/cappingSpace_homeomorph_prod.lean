import Mathlib
import Submission.Work.Drive.CappingSpace

namespace Work.Drive

noncomputable section

open scoped Topology

/-!
# The four-dimensional capping space is `(0,∞) × LensSpace`

This file proves `Work.Drive.cappingSpace_homeomorph_prod`: the gluing `cappingRel` of the
four-dimensional capping space never changes the radial coordinate, so `CappingSpace` is the product
of the open half-line `(0,∞)` with the three-dimensional glued slice `LensSpace`.

The homeomorphism is exhibited explicitly: `Φ` sends a configuration point `(r, u, η)` to
`(r, [u, η]) : (0,∞) × LensSpace` and a cap point `(r, θ, z)` to `(r, [θ, z])`, and `Ψ` is induced by
the slice identification `lensRel`.
-/

/-! ### Elementary facts about the closed unit disk of `ℂ` -/


lemma mem_closedBall_of_norm_le_one {z : ℂ} (h : ‖z‖ ≤ 1) : z ∈ Metric.closedBall (0:ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]; exact h

lemma norm_le_one_of_mem_closedBall {z : ℂ} (h : z ∈ Metric.closedBall (0:ℂ) 1) : ‖z‖ ≤ 1 := by
  rw [Metric.mem_closedBall, dist_zero_right] at h; exact h

/-! ### The two pieces as `(0,∞)` times a solid torus

`confTorusOf` and `capTorusOf` forget the boundary parameter of a configuration, respectively cap,
point of the capping space and read it as a point of the configuration, respectively cap, solid torus.
-/

/-- The configuration point `(r, z, η)` of the capping space seen as the `(0,∞) × (D² × S¹)` point
with the same coordinates: the radial coordinate `r` and the point `(z, η)` of the configuration solid
torus. -/
def confTorusOf (p : ConfigPiece) : ConfTorus :=
  (⟨p.1.2.1, mem_closedBall_of_norm_le_one p.2.2⟩, p.1.2.2)

/-- The cap point `(r, θ, z)` of the capping space seen as the `(0,∞) × (S¹ × D²)` point with the
same coordinates. -/
def capTorusOf (p : CapPiece) : CapTorus :=
  (p.1.2.1, ⟨p.1.2.2, mem_closedBall_of_norm_le_one p.2.2⟩)

lemma continuous_confTorusOf : Continuous confTorusOf := by unfold confTorusOf; fun_prop

lemma continuous_capTorusOf : Continuous capTorusOf := by unfold capTorusOf; fun_prop

/-! ### The map `CappingSpace → (0,∞) × LensSpace` -/

/-- The map on the configuration piece: `(r, z, η) ↦ (r, [z, η])`, where the class is taken in the
configuration solid torus. -/
def toProdConfig (p : ConfigPiece) : Set.Ioi (0:ℝ) × LensSpace :=
  (⟨p.1.1, p.2.1⟩, Quotient.mk'' (Sum.inr (confTorusOf p)))

/-- The map on the cap piece: `(r, θ, w) ↦ (r, [θ, w])`, where the class is taken in the cap solid
torus. -/
def toProdCap (p : CapPiece) : Set.Ioi (0:ℝ) × LensSpace :=
  (⟨p.1.1, p.2.1⟩, Quotient.mk'' (Sum.inl (capTorusOf p)))

/-- The map `ConfigPiece ⊕ CapPiece → (0,∞) × LensSpace`. -/
def toProd : (ConfigPiece ⊕ CapPiece) → Set.Ioi (0:ℝ) × LensSpace :=
  Sum.elim toProdConfig toProdCap

lemma continuous_toProdConfig : Continuous toProdConfig := by
  unfold toProdConfig
  exact Continuous.prodMk (by fun_prop)
    (continuous_lensMk.comp (continuous_inr.comp continuous_confTorusOf))

lemma continuous_toProdCap : Continuous toProdCap := by
  unfold toProdCap
  exact Continuous.prodMk (by fun_prop)
    (continuous_lensMk.comp (continuous_inl.comp continuous_capTorusOf))

lemma continuous_toProd : Continuous toProd :=
  Continuous.sumElim continuous_toProdConfig continuous_toProdCap

/-! ### `lensRel` recalled: it only relates the two summands along the gluing

These four lemmas unpack the relation `lensRel` of `Submission.Work.Drive.CappingSpace`: within one
summand it is equality, and across the two summands it is exactly the boundary identification. -/

lemma lensRel_inl_inl {a b : CapTorus} (h : lensRel (Sum.inl a) (Sum.inl b)) : a = b := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · exact Sum.inl.inj h
  · exact absurd h.2 (by simp)
  · exact absurd h.2 (by simp)

lemma lensRel_inr_inr {a b : ConfTorus} (h : lensRel (Sum.inr a) (Sum.inr b)) : a = b := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · exact Sum.inr.inj h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

lemma lensRel_inr_inl {a : ConfTorus} {b : CapTorus} (h : lensRel (Sum.inr a) (Sum.inl b)) :
    ∃ θ φ : UnitAddCircle, b = (θ, bdy φ) ∧ a = (bdy φ, θ + 2 • φ) := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · exact absurd h (by simp)
  · exact absurd h.2 (by simp)
  · obtain ⟨hy, hx⟩ := h
    exact ⟨θ, φ, Sum.inl.inj hy, Sum.inr.inj hx⟩

lemma lensRel_inl_inr {a : CapTorus} {b : ConfTorus} (h : lensRel (Sum.inl a) (Sum.inr b)) :
    ∃ θ φ : UnitAddCircle, a = (θ, bdy φ) ∧ b = (bdy φ, θ + 2 • φ) := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · exact absurd h (by simp)
  · obtain ⟨hx, hy⟩ := h
    exact ⟨θ, φ, Sum.inl.inj hx, Sum.inr.inj hy⟩
  · exact absurd h.2 (by simp)

/-! ### `toProd` descends to `CappingSpace`

The two boundary points glued by `cappingRel` have the same `toProd` image, because their torus
coordinates are glued by `lensRel`. -/

lemma confTorusOf_confBdy (r : ℝ) (hr : 0 < r) (φ η : UnitAddCircle) :
    confTorusOf (confBdy r hr φ η) = (bdy φ, η) := by
  unfold confTorusOf
  refine Prod.ext ?_ rfl
  exact Subtype.ext rfl

lemma capTorusOf_capBdy (r : ℝ) (hr : 0 < r) (θ φ : UnitAddCircle) :
    capTorusOf (capBdy r hr θ φ) = (θ, bdy φ) := by
  unfold capTorusOf
  refine Prod.ext rfl ?_
  exact Subtype.ext rfl

lemma toProd_eq_of_cappingRel :
    ∀ {x y : ConfigPiece ⊕ CapPiece}, cappingRel x y → toProd x = toProd y := by
  intro x y h
  rcases h with hxy | ⟨r, hr, θ, φ, h | h⟩
  · rw [hxy]
  · obtain ⟨hx, hy⟩ := h
    rw [hx, hy]
    simp only [toProd, Sum.elim_inl, Sum.elim_inr, toProdConfig, toProdCap,
      confTorusOf_confBdy, capTorusOf_capBdy]
    refine Prod.ext rfl ?_
    exact Quotient.sound (Or.inr ⟨θ, φ, Or.inr ⟨rfl, rfl⟩⟩)
  · obtain ⟨hy, hx⟩ := h
    rw [hx, hy]
    simp only [toProd, Sum.elim_inl, Sum.elim_inr, toProdConfig, toProdCap,
      confTorusOf_confBdy, capTorusOf_capBdy]
    refine Prod.ext rfl ?_
    exact Quotient.sound (Or.inr ⟨θ, φ, Or.inl ⟨rfl, rfl⟩⟩)

/-! ### Injectivity of `toProd` modulo `cappingRel`

Conversely, points with the same `toProd` image are identified by `cappingRel`: on each piece
`toProd` remembers all coordinates, and across the two pieces it holds exactly at the glued boundary
points. -/

set_option maxHeartbeats 1000000 in
lemma toProd_eq_imp_cappingRel {x y : ConfigPiece ⊕ CapPiece} (h : toProd x = toProd y) :
    cappingRel x y := by
  rcases x with p | p <;> rcases y with q | q
  · -- two configuration points
    have hfst : (⟨p.1.1, p.2.1⟩ : Set.Ioi (0:ℝ)) = ⟨q.1.1, q.2.1⟩ := by
      simpa only [toProd, Sum.elim_inl, toProdConfig] using congrArg Prod.fst h
    have hsnd : (Quotient.mk'' (Sum.inr (confTorusOf p)) : LensSpace)
        = Quotient.mk'' (Sum.inr (confTorusOf q)) := by
      simpa only [toProd, Sum.elim_inl, toProdConfig] using congrArg Prod.snd h
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hfst
    have h2 : confTorusOf p = confTorusOf q := lensRel_inr_inr (Quotient.exact hsnd)
    have h3 : p.1.2.1 = q.1.2.1 := by
      have := congrArg (fun z : Metric.closedBall (0:ℂ) 1 => (z : ℂ)) (congrArg Prod.fst h2)
      simpa [confTorusOf] using this
    have h4 : p.1.2.2 = q.1.2.2 := by
      have := congrArg Prod.snd h2
      simpa [confTorusOf] using this
    have hpq : p = q := Subtype.ext (Prod.ext h1 (Prod.ext h3 h4))
    rw [hpq]
    exact cappingRel_refl _
  · -- a configuration point and a cap point
    have hfst : (⟨p.1.1, p.2.1⟩ : Set.Ioi (0:ℝ)) = ⟨q.1.1, q.2.1⟩ := by
      simpa only [toProd, Sum.elim_inl, Sum.elim_inr, toProdConfig, toProdCap] using
        congrArg Prod.fst h
    have hsnd : (Quotient.mk'' (Sum.inr (confTorusOf p)) : LensSpace)
        = Quotient.mk'' (Sum.inl (capTorusOf q)) := by
      simpa only [toProd, Sum.elim_inl, Sum.elim_inr, toProdConfig, toProdCap] using
        congrArg Prod.snd h
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hfst
    obtain ⟨θ, φ, hb, ha⟩ := lensRel_inr_inl (Quotient.exact hsnd)
    have hz : p.1.2.1 = circleOf φ := by
      have := congrArg (fun z : Metric.closedBall (0:ℂ) 1 => (z : ℂ)) (congrArg Prod.fst ha)
      simpa [confTorusOf] using this
    have hη : p.1.2.2 = θ + 2 • φ := by
      have := congrArg Prod.snd ha
      simpa [confTorusOf] using this
    have hθ : q.1.2.1 = θ := by
      have := congrArg Prod.fst hb
      simpa [capTorusOf] using this
    have hw : q.1.2.2 = circleOf φ := by
      have := congrArg (fun z : Metric.closedBall (0:ℂ) 1 => (z : ℂ)) (congrArg Prod.snd hb)
      simpa [capTorusOf] using this
    refine Or.inr ⟨p.1.1, p.2.1, θ, φ, Or.inl ⟨?_, ?_⟩⟩
    · refine congrArg Sum.inl (Subtype.ext ?_)
      refine Prod.ext rfl (Prod.ext hz hη)
    · refine congrArg Sum.inr (Subtype.ext ?_)
      refine Prod.ext h1.symm (Prod.ext hθ hw)
  · -- a cap point and a configuration point
    have hfst : (⟨p.1.1, p.2.1⟩ : Set.Ioi (0:ℝ)) = ⟨q.1.1, q.2.1⟩ := by
      simpa only [toProd, Sum.elim_inl, Sum.elim_inr, toProdConfig, toProdCap] using
        congrArg Prod.fst h
    have hsnd : (Quotient.mk'' (Sum.inl (capTorusOf p)) : LensSpace)
        = Quotient.mk'' (Sum.inr (confTorusOf q)) := by
      simpa only [toProd, Sum.elim_inl, Sum.elim_inr, toProdConfig, toProdCap] using
        congrArg Prod.snd h
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hfst
    obtain ⟨θ, φ, ha, hb⟩ := lensRel_inl_inr (Quotient.exact hsnd)
    have hθ : p.1.2.1 = θ := by
      have := congrArg Prod.fst ha
      simpa [capTorusOf] using this
    have hw : p.1.2.2 = circleOf φ := by
      have := congrArg (fun z : Metric.closedBall (0:ℂ) 1 => (z : ℂ)) (congrArg Prod.snd ha)
      simpa [capTorusOf] using this
    have hz : q.1.2.1 = circleOf φ := by
      have := congrArg (fun z : Metric.closedBall (0:ℂ) 1 => (z : ℂ)) (congrArg Prod.fst hb)
      simpa [confTorusOf] using this
    have hη : q.1.2.2 = θ + 2 • φ := by
      have := congrArg Prod.snd hb
      simpa [confTorusOf] using this
    refine Or.inr ⟨p.1.1, p.2.1, θ, φ, Or.inr ⟨?_, ?_⟩⟩
    · refine congrArg Sum.inl (Subtype.ext ?_)
      refine Prod.ext h1.symm (Prod.ext hz hη)
    · refine congrArg Sum.inr (Subtype.ext ?_)
      refine Prod.ext rfl (Prod.ext hθ hw)
  · -- two cap points
    have hfst : (⟨p.1.1, p.2.1⟩ : Set.Ioi (0:ℝ)) = ⟨q.1.1, q.2.1⟩ := by
      simpa only [toProd, Sum.elim_inr, toProdCap] using congrArg Prod.fst h
    have hsnd : (Quotient.mk'' (Sum.inl (capTorusOf p)) : LensSpace)
        = Quotient.mk'' (Sum.inl (capTorusOf q)) := by
      simpa only [toProd, Sum.elim_inr, toProdCap] using congrArg Prod.snd h
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hfst
    have h2 : capTorusOf p = capTorusOf q := lensRel_inl_inl (Quotient.exact hsnd)
    have h3 : p.1.2.1 = q.1.2.1 := by
      have := congrArg Prod.fst h2
      simpa [capTorusOf] using this
    have h4 : p.1.2.2 = q.1.2.2 := by
      have := congrArg (fun z : Metric.closedBall (0:ℂ) 1 => (z : ℂ)) (congrArg Prod.snd h2)
      simpa [capTorusOf] using this
    have hpq : p = q := Subtype.ext (Prod.ext h1 (Prod.ext h3 h4))
    rw [hpq]
    exact cappingRel_refl _

/-! ### The homeomorphism `Φ : CappingSpace → (0,∞) × LensSpace` -/

lemma toProd_compat (a b : ConfigPiece ⊕ CapPiece) (h : cappingRel a b) : toProd a = toProd b :=
  toProd_eq_of_cappingRel h

/-- The continuous bijection `CappingSpace → (0,∞) × LensSpace`, induced by `toProd`. -/
def Φ : CappingSpace → Set.Ioi (0:ℝ) × LensSpace := Quotient.lift toProd toProd_compat

lemma continuous_Φ : Continuous Φ :=
  continuous_toProd.quotient_lift toProd_compat

lemma injective_Φ : Function.Injective Φ := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      exact Quotient.sound (toProd_eq_imp_cappingRel hxy)

lemma surjective_toProd : Function.Surjective toProd := by
  rintro ⟨r, q⟩
  induction q using Quotient.inductionOn with
  | h a =>
    cases a with
    | inl c =>
      refine ⟨Sum.inr ⟨(r.1, c.1, c.2.1), ⟨r.2, norm_le_one_of_mem_closedBall c.2.2⟩⟩, ?_⟩
      rfl
    | inr c =>
      refine ⟨Sum.inl ⟨(r.1, c.1.1, c.2), ⟨r.2, norm_le_one_of_mem_closedBall c.1.2⟩⟩, ?_⟩
      rfl

lemma surjective_Φ : Function.Surjective Φ := by
  intro y
  obtain ⟨x, hx⟩ := surjective_toProd y
  exact ⟨Quotient.mk'' x, hx⟩

/-! ### The inverse map `Ψ : (0,∞) × LensSpace → CappingSpace`

`Ψ` is induced by the slice identification `lensRel`: the product with the radial coordinate `r` is
trivial, so a class in `LensSpace` is lifted into whichever piece contains the interior part of its
disk coordinate.
-/

/-- The lift of a cap solid torus point at radius `r`: `(θ, w) ↦ [(r, θ, w)]` in the cap piece. -/
def fromTorusCap (r : Set.Ioi (0:ℝ)) (q : CapTorus) : CappingSpace :=
  Quotient.mk'' (Sum.inr
    (⟨(r.1, q.1, q.2.1), ⟨r.2, norm_le_one_of_mem_closedBall q.2.2⟩⟩ : CapPiece))

/-- The lift of a configuration solid torus point at radius `r`: `(z, η) ↦ [(r, z, η)]` in the
configuration piece. -/
def fromTorusConf (r : Set.Ioi (0:ℝ)) (q : ConfTorus) : CappingSpace :=
  Quotient.mk'' (Sum.inl
    (⟨(r.1, q.1.1, q.2), ⟨r.2, norm_le_one_of_mem_closedBall q.1.2⟩⟩ : ConfigPiece))

/-- The lift of a point of the disjoint union of the two solid tori at radius `r`. -/
def fromTorus (r : Set.Ioi (0:ℝ)) : (CapTorus ⊕ ConfTorus) → CappingSpace :=
  Sum.elim (fromTorusCap r) (fromTorusConf r)

/-- The two images of a glued pair of boundary points agree in the capping space: this is exactly
`cappingRel`, the relation defining `CappingSpace`. -/
lemma fromTorus_cap_conf (r : Set.Ioi (0:ℝ)) (θ φ : UnitAddCircle) :
    fromTorus r (Sum.inl (θ, bdy φ)) = fromTorus r (Sum.inr (bdy φ, θ + 2 • φ)) := by
  refine Quotient.sound (Or.inr ⟨r.1, r.2, θ, φ, Or.inr ⟨?_, ?_⟩⟩)
  · refine congrArg Sum.inl (Subtype.ext ?_)
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · rfl
    · rfl
  · refine congrArg Sum.inr (Subtype.ext ?_)
    refine Prod.ext rfl (Prod.ext rfl rfl)

lemma fromTorus_eq_of_lensRel {a b : CapTorus ⊕ ConfTorus} (h : lensRel a b) (r : Set.Ioi (0:ℝ)) :
    fromTorus r a = fromTorus r b := by
  rcases h with h | ⟨θ, φ, h | h⟩
  · rw [h]
  · obtain ⟨hx, hy⟩ := h; rw [hx, hy]; exact fromTorus_cap_conf r θ φ
  · obtain ⟨hy, hx⟩ := h; rw [hx, hy]; exact (fromTorus_cap_conf r θ φ).symm

/-- The inverse map, as a function of a class in `LensSpace` and a radius. -/
def g (p : LensSpace × Set.Ioi (0:ℝ)) : CappingSpace :=
  Quotient.liftOn p.1 (fun a => fromTorus p.2 a) (fun _ _ h => fromTorus_eq_of_lensRel h p.2)

/-! #### Continuity of the inverse map -/

lemma continuous_fromTorusCap_pair :
    Continuous (fun p : CapTorus × Set.Ioi (0:ℝ) => fromTorusCap p.2 p.1) := by
  unfold fromTorusCap
  exact continuous_cappingMk.comp (continuous_inr.comp
    (Continuous.subtype_mk (by fun_prop)
      (fun p => ⟨p.2.2, norm_le_one_of_mem_closedBall p.1.2.2⟩)))

lemma continuous_fromTorusConf_pair :
    Continuous (fun p : ConfTorus × Set.Ioi (0:ℝ) => fromTorusConf p.2 p.1) := by
  unfold fromTorusConf
  exact continuous_cappingMk.comp (continuous_inl.comp
    (Continuous.subtype_mk (by fun_prop)
      (fun p => ⟨p.2.2, norm_le_one_of_mem_closedBall p.1.1.2⟩)))

/-- The lift, spread over the distributivity homeomorphism `(A ⊕ B) × C ≅ A × C ⊕ B × C`. -/
def gSum : ((CapTorus × Set.Ioi (0:ℝ)) ⊕ (ConfTorus × Set.Ioi (0:ℝ))) → CappingSpace :=
  Sum.elim (fun p : CapTorus × Set.Ioi (0:ℝ) => fromTorusCap p.2 p.1)
    (fun p : ConfTorus × Set.Ioi (0:ℝ) => fromTorusConf p.2 p.1)

lemma continuous_gSum : Continuous gSum := by
  unfold gSum
  exact Continuous.sumElim continuous_fromTorusCap_pair continuous_fromTorusConf_pair

lemma continuous_fromTorus_uncurried :
    Continuous (fun p : (CapTorus ⊕ ConfTorus) × Set.Ioi (0:ℝ) => fromTorus p.2 p.1) := by
  have hcomp : Continuous (gSum ∘ (Homeomorph.sumProdDistrib).toFun) :=
    Continuous.comp (f := (Homeomorph.sumProdDistrib).toFun) (g := gSum) continuous_gSum
      Homeomorph.sumProdDistrib.continuous_toFun
  refine Continuous.congr hcomp ?_
  rintro ⟨a, r⟩
  cases a with
  | inl q => rfl
  | inr q => rfl

lemma continuous_g : Continuous g := by
  have : LocallyCompactSpace (Set.Ioi (0:ℝ)) := isOpen_Ioi.locallyCompactSpace
  refine Topology.IsQuotientMap.continuous_lift_prod_left
    (f := (Quotient.mk'' : CapTorus ⊕ ConfTorus → LensSpace)) isQuotientMap_quotient_mk' ?_
  simpa only [g, Quotient.liftOn_mk] using continuous_fromTorus_uncurried

/-- The inverse map `(0,∞) × LensSpace → CappingSpace`. -/
def Ψ : Set.Ioi (0:ℝ) × LensSpace → CappingSpace :=
  fun p => g (Homeomorph.prodComm (Set.Ioi (0:ℝ)) LensSpace p)

lemma continuous_Ψ : Continuous Ψ :=
  Continuous.comp (f := (Homeomorph.prodComm (Set.Ioi (0:ℝ)) LensSpace).toFun) (g := g)
    continuous_g (Homeomorph.prodComm (Set.Ioi (0:ℝ)) LensSpace).continuous_toFun

/-! ### `Φ` and `Ψ` are mutually inverse -/

lemma Ψ_Φ (x : CappingSpace) : Ψ (Φ x) = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    cases a with
    | inl p => rfl
    | inr p => rfl

lemma Φ_Ψ (y : Set.Ioi (0:ℝ) × LensSpace) : Φ (Ψ y) = y := by
  obtain ⟨r, q⟩ := y
  induction q using Quotient.inductionOn with
  | h a =>
    cases a with
    | inl c => rfl
    | inr c => rfl

/-! ### The main statement -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The four-dimensional capping space is the product of the radial direction with the slice.**  The
boundary identification `cappingRel` of `Submission.Work.Drive.CappingSpace` glues the configuration
boundary point `(r, φ, θ + 2φ)` to the cap boundary point `(r, θ, φ)`, so it never changes the radial
coordinate `r = ‖(midpoint, length)‖`: the four-dimensional capping space `CappingSpace` of
Hugelmeyer's fifth auxiliary result is therefore the product of the open half-line `(0,∞)` (the radial
direction; its two *ends* are the `±λ` ends of the model `ℝ × ℝP³`) with the three-dimensional glued
slice `LensSpace`.  Together with `Work.Drive.lensSpace_homeomorph_projective`
(`LensSpace ≃ₜ ℝP³`) this gives Hugelmeyer's `Y ≅ ℝ × ℝP³`.

Proof route: at a fixed `r` the identification `cappingRel` is exactly `lensRel` of the slice (with the
two summands swapped, which is a homeomorphism of the disjoint union), so the map
`CappingSpace → (0,∞) × LensSpace` sending a configuration point `(r, u, η)` to `(r, [u, η])` and a cap
point `(r, θ, z)` to `(r, [θ, z])` is well defined (the two images agree on glued points, by the
definition of `lensRel`), is continuous (each leg is continuous on its summand and the quotient topology
is final; alternatively `IsQuotientMap.continuous_lift_prod_left`, since `(0,∞)` is locally compact and
`σ`-compact), and is a bijection with inverse induced by the slice identification, using that a slice
point has a unique lift into the summand containing the interior part of its disk coordinate. -/
theorem cappingSpace_homeomorph_prod :
    Nonempty (Work.Drive.CappingSpace ≃ₜ (Set.Ioi (0 : ℝ)) × Work.Drive.LensSpace) :=
  ⟨Homeomorph.mk ⟨Φ, Ψ, Ψ_Φ, Φ_Ψ⟩ continuous_Φ continuous_Ψ⟩

end

end Work.Drive

import Mathlib
import Submission.Work.Stems.Cone
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

/-!
# Homotopy groups of a contractible space are trivial

For a contractible space `X` and *every* index type `N` (no finiteness, no separation hypothesis),
the `n`-th homotopy group `HomotopyGroup N X x` is a subsingleton.

The proof goes through the cone `C X = (X × I)/(X × {1})`, whose two relevant properties are
proved here:

* `C X` is contractible *with the apex fixed*: pushing the `I`-coordinate towards `1` deforms the
  identity to the constant map at the apex without moving the apex, so every generalized loop at
  the apex is null-homotopic relative to the boundary (`cone_apex_subsingleton`);
* `X` is a *retract* of `C X`: given any homotopy `H` from `id X` to the constant map at `x`
  (which is constructed from `ContractibleSpace X` in `exists_homotopy_id_const`), the map
  `r [a, t] = H (t, a)` is well defined and retracts the cone onto its base
  (`coneRetract`, `coneRetract_coneIncl`).  Postcomposition with `r` transports a homotopy
  relative to the boundary in `C X` back to `X` (`Work.Stems.subsingleton_of_retract`).

The base point is moved from the apex to the image of `x` in the cone along the path
`t ↦ [x, t]`, using `Work.Stems.subsingleton_homotopyGroup_change_basepoint` (which holds for
every index type).
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems

/-! ## A homotopy from the identity of a contractible space to a constant map -/

/-- Every contractible space admits a homotopy from the identity to the constant map at any
given point, written in "uncurried" form for convenience. -/
theorem exists_homotopy_id_const {X : Type*} [TopologicalSpace X] [ContractibleSpace X] (x : X) :
    ∃ H : C(I × X, X), (∀ a, H (0, a) = a) ∧ (∀ a, H (1, a) = x) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  have hconst : e.invFun.comp e.toFun = ContinuousMap.const X (e.invFun ()) := by
    ext a; exact congrArg e.invFun (Subsingleton.elim _ _)
  have h1 : (ContinuousMap.const X (e.invFun ())).Homotopic (ContinuousMap.id X) := by
    rw [← hconst]; exact e.left_inv
  obtain ⟨γ⟩ : Nonempty (Path (e.invFun ()) x) := ⟨PathConnectedSpace.somePath _ _⟩
  have h2 : (ContinuousMap.const X (e.invFun ())).Homotopic (ContinuousMap.const X x) :=
    ⟨ContinuousMap.Homotopy.mk ⟨fun p : I × X => γ p.1, γ.continuous.comp continuous_fst⟩
      (fun a => γ.source) (fun a => γ.target)⟩
  obtain ⟨H⟩ : Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X x)) :=
    h1.symm.trans h2
  exact ⟨H.toContinuousMap, fun a => H.map_zero_left a, fun a => H.map_one_left a⟩

/-! ## The cone is contractible with the apex fixed -/

/-- The linear path on the unit interval from `t` to `1` at parameter `s`: `(1 - s) * t + s`. -/
noncomputable def conePt (s t : I) : I :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ), by
    constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

lemma conePt_zero (t : I) : conePt 0 t = t := by ext; simp [conePt]

lemma conePt_one_eq (t : I) : conePt 1 t = 1 := by ext; simp [conePt]

lemma conePt_right_one (s : I) : conePt s 1 = 1 := by ext; simp [conePt]

/-- The contraction of the cone, on representatives: `(s, [a, t]) ↦ [a, (1-s)*t+s]`. -/
noncomputable def coneContrFun {X : Type*} [TopologicalSpace X] (p : I × Cone X) : Cone X :=
  Quotient.liftOn p.2 (fun q : X × I => Quotient.mk'' (q.1, conePt p.1 q.2)) (by
    intro a b hab
    rcases hab with hab | ⟨ha, hb⟩
    · subst hab; rfl
    · exact Quotient.sound
        (Or.inr ⟨by rw [ha]; exact conePt_right_one p.1, by rw [hb]; exact conePt_right_one p.1⟩))

/-- The cone is contractible: a continuous map `I × Cone X → Cone X` deforming the identity
(`s = 0`) to the constant map at the apex (`s = 1`), and fixing the apex. -/
noncomputable def coneContr {X : Type*} [TopologicalSpace X] : C(I × Cone X, Cone X) where
  toFun := coneContrFun
  continuous_toFun := by
    apply Topology.IsQuotientMap.continuous_lift_prod_right
      (f := @Quotient.mk (X × I) (coneSetoid X)) isQuotientMap_quotient_mk'
    simp only [coneContrFun, Quotient.liftOn_mk]
    refine continuous_quotient_mk'.comp (Continuous.prodMk ?_ ?_)
    · fun_prop
    · apply Continuous.subtype_mk
      fun_prop

lemma coneContr_zero {X : Type*} [TopologicalSpace X] (z : Cone X) : coneContr (0, z) = z := by
  induction z using Quotient.inductionOn with
  | h q =>
    change coneContrFun (0, Quotient.mk'' q) = Quotient.mk'' q
    simp only [coneContrFun, Quotient.liftOn_mk, conePt_zero]

lemma coneContr_one {X : Type*} [TopologicalSpace X] (x : X) (z : Cone X) :
    coneContr (1, z) = coneApex x := by
  induction z using Quotient.inductionOn with
  | h q =>
    change coneContrFun (1, Quotient.mk'' q) = coneApex x
    simp only [coneContrFun, Quotient.liftOn_mk, conePt_one_eq]
    exact coneApex_eq q.1 x

lemma coneContr_apex {X : Type*} [TopologicalSpace X] (x : X) (s : I) :
    coneContr (s, coneApex x) = coneApex x := by
  change coneContrFun (s, Quotient.mk'' (x, (1 : I))) = coneApex x
  simp only [coneContrFun, Quotient.liftOn_mk, conePt_right_one]
  rfl

/-- Every generalized loop in the cone at the apex is null-homotopic relative to the boundary. -/
theorem coneLoop_nullhomotopic {N X : Type*} [TopologicalSpace X] (x : X)
    (p : Ω^ N (Cone X) (coneApex x)) :
    GenLoop.Homotopic p (GenLoop.const : Ω^ N (Cone X) (coneApex x)) := by
  refine ⟨{ toFun := fun q => coneContr (q.1, p.1 q.2),
            continuous_toFun := ?_,
            map_zero_left := ?_,
            map_one_left := ?_,
            prop' := ?_ }⟩
  · exact coneContr.continuous.comp
      (continuous_fst.prodMk (p.1.continuous.comp continuous_snd))
  · intro y; exact coneContr_zero (p.1 y)
  · intro y; exact coneContr_one x (p.1 y)
  · intro t y hy
    show coneContr (t, p.1 y) = p.1 y
    rw [p.2 y hy]
    exact coneContr_apex x t

/-- The homotopy group of the cone at its apex is trivial, for every index type. -/
theorem cone_apex_subsingleton {N X : Type*} [TopologicalSpace X] (x : X) :
    Subsingleton (HomotopyGroup N (Cone X) (coneApex x)) := by
  change Subsingleton (Quotient (GenLoop.Homotopic.setoid N (coneApex x)))
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      exact Quotient.sound (GenLoop.Homotopic.trans (coneLoop_nullhomotopic x p)
        (GenLoop.Homotopic.symm (coneLoop_nullhomotopic x q)))

/-! ## The retraction of the cone onto its base -/

/-- The retraction `r [a, t] = H (t, a)` of the cone onto its base, induced by a homotopy `H`
from `id X` to the constant map at `x`. -/
noncomputable def coneRetract {X : Type*} [TopologicalSpace X] (H : C(I × X, X)) (x : X)
    (h1 : ∀ a, H (1, a) = x) : C(Cone X, X) :=
  ContinuousMap.mk (Quotient.lift (fun p : X × I => H (p.2, p.1)) (by
      rintro a b (hab | ⟨ha, hb⟩)
      · subst hab; rfl
      · rw [ha, hb, h1, h1]))
    (Continuous.quotient_lift (by fun_prop) (by
      rintro a b (hab | ⟨ha, hb⟩)
      · subst hab; rfl
      · rw [ha, hb, h1, h1]))

/-- The retraction fixes the base: `r (coneIncl a) = a`. -/
theorem coneRetract_coneIncl {X : Type*} [TopologicalSpace X] (H : C(I × X, X)) (x : X)
    (h0 : ∀ a, H (0, a) = a) (h1 : ∀ a, H (1, a) = x) (a : X) :
    coneRetract H x h1 (coneIncl a) = a := h0 a

/-- The inclusion of the base into the cone is continuous. -/
theorem continuous_coneIncl {X : Type*} [TopologicalSpace X] : Continuous (coneIncl (X := X)) :=
  continuous_quotient_mk'.comp (by fun_prop)

/-- A path from the inclusion of `x` into the cone to the apex. -/
noncomputable def conePath {X : Type*} [TopologicalSpace X] (x : X) :
    Path (coneIncl x) (coneApex x) where
  toFun t := Quotient.mk'' (x, t)
  continuous_toFun := continuous_quotient_mk'.comp (by fun_prop)
  source' := rfl
  target' := rfl

/-! ## The main theorem -/

/-- **Homotopy groups of a contractible space are trivial.** -/
theorem subsingleton_of_contractible {N X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (x : X) : Subsingleton (HomotopyGroup N X x) := by
  obtain ⟨H, h0, h1⟩ := exists_homotopy_id_const x
  refine subsingleton_of_retract (N := N) (x := x)
    ⟨coneIncl, continuous_coneIncl⟩ (coneRetract H x h1) ?_ ?_
  · ext a; exact coneRetract_coneIncl H x h0 h1 a
  · exact subsingleton_homotopyGroup_change_basepoint (conePath x).symm
      (cone_apex_subsingleton x)

end Work.Stems

import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.PathSpaceTorsor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.Serre

open Work.StemsB

theorem pathSpaceAaction {X : Type} [TopologicalSpace X] (pt : X) [PathConnectedSpace X]
    (hvan : ∀ i : ℕ, 2 ≤ i → Subsingleton (HomotopyGroup (Fin i) X pt))
    (A : Type) [AddCommGroup A] [Fintype A]
    (φ : HomotopyGroup (Fin 1) X pt ≃* Multiplicative A) :
    ∃ act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt),
      (∀ a : A, (Work.StemsB.evalOne X pt).comp (act a) = Work.StemsB.evalOne X pt) ∧
      (∀ (a b : A) (e : Work.StemsB.PathSpace X pt),
        (∃ H : C(unitInterval × unitInterval, X),
          (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
          (∀ t : unitInterval, H (1, t) = (act b e).1 t) ∧
          (∀ s : unitInterval, H (s, 0) = pt) ∧
          (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)) ↔ a = b) ∧
      (∀ (e e' : Work.StemsB.PathSpace X pt),
        (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
        ∃ a : A, ∃ H : C(unitInterval × unitInterval, X),
          (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
          (∀ t : unitInterval, H (1, t) = e'.1 t) ∧
          (∀ s : unitInterval, H (s, 0) = pt) ∧
          (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)) := by
  classical
  -- the isomorphism `π₁(X, pt) ≃* π₁(X, pt)` with the fundamental group, whose product is `trans`
  let Φ : HomotopyGroup (Fin 1) X pt ≃* FundamentalGroup X pt :=
    HomotopyGroup.pi1MulEquivFundamentalGroup
  -- the class of the loop attached to `a`
  let g : A → Path.Homotopic.Quotient pt pt := fun a => Φ (φ.symm (Multiplicative.ofAdd a))
  -- a chosen representative loop for each `a`
  let loopOf : A → Path pt pt := fun a => Quotient.out (g a)
  have loopOf_spec : ∀ a, Path.Homotopic.Quotient.mk (loopOf a) = g a :=
    fun a => Quotient.out_eq _
  have g_inj : Function.Injective g := by
    intro a b h
    have h1 : φ.symm (Multiplicative.ofAdd a) = φ.symm (Multiplicative.ofAdd b) := Φ.injective h
    exact Multiplicative.ofAdd.injective (φ.symm.injective h1)
  refine ⟨fun a => psConcatMap pt (loopOf a), ?_, ?_, ?_⟩
  · -- the action preserves the endpoint
    intro a
    exact psEvalOne_psConcatMap pt (loopOf a)
  · -- the action is free on the homotopy classes of the fibres
    intro a b e
    have hiff : (∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (psConcatMap pt (loopOf a) e).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (psConcatMap pt (loopOf b) e).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)) ↔
        (psActPath pt (loopOf a) e).Homotopic (psActPath pt (loopOf b) e) :=
      ps_exists_homotopy_iff_homotopic pt _ _
    rw [hiff]
    constructor
    · intro h
      have h' : (loopOf a).trans (psToPath pt e) |>.Homotopic
          ((loopOf b).trans (psToPath pt e)) := by
        rw [← psActPath_eq_trans pt (loopOf a) e, ← psActPath_eq_trans pt (loopOf b) e]
        exact h
      have h1 : Path.Homotopic.Quotient.mk (loopOf a) = Path.Homotopic.Quotient.mk (loopOf b) :=
        ps_eq_of_trans_homotopic pt (loopOf a) (loopOf b) (psToPath pt e) h'
      rw [loopOf_spec a, loopOf_spec b] at h1
      exact g_inj h1
    · intro hab
      subst hab
      exact Path.Homotopic.refl _
  · -- the action is transitive on the homotopy classes of the fibres
    intro e e' heq
    let q : Path pt ((Work.StemsB.evalOne X pt) e) := (psToPath pt e').cast rfl heq
    let w : Path.Homotopic.Quotient pt pt :=
      (Path.Homotopic.Quotient.mk (psToPath pt e')).cast rfl heq |>.trans
        (Path.Homotopic.Quotient.mk (psToPath pt e)).symm
    refine ⟨Multiplicative.toAdd (φ (Φ.symm w)), ?_⟩
    have ha : g (Multiplicative.toAdd (φ (Φ.symm w))) = w := by
      show Φ (φ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (φ (Φ.symm w))))) = w
      simp
    have hq : Path.Homotopic.Quotient.mk q
        = (Path.Homotopic.Quotient.mk (psToPath pt e')).cast rfl heq :=
      Path.Homotopic.Quotient.mk_cast (psToPath pt e') rfl heq
    have hHom : (psActPath pt (loopOf (Multiplicative.toAdd (φ (Φ.symm w)))) e).Homotopic q := by
      rw [psActPath_eq_trans]
      refine ps_homotopic_of_trans_eq pt _ (psToPath pt e) q ?_
      rw [loopOf_spec, ha, hq]
    obtain ⟨H, h0, h1, hs0, hs1⟩ :=
      (ps_exists_homotopy_iff_homotopic pt _ q).mpr hHom
    exact ⟨H, h0, h1, hs0, hs1⟩

end Work.Serre

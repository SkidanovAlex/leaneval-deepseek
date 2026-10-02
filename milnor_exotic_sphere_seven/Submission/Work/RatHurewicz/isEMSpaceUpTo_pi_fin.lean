import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.isEMSpaceUpTo_prod
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Finite products (in the shape `Fin r → X`) of range models of Eilenberg–MacLane spaces

`Work.RatHurewicz.isEMSpaceUpTo_prod` proves that the product of two range models is a range model.
This file iterates it to the `r`-fold product, spelled `Fin r → X` (the shape in which the free part
of `hfg`, the finitely generated case of `Work.RatHurewicz.RangeModelRatAcyclic`, needs it: the model
of `K(ℤ^r ⊕ F, k)` is `(Fin r → L) × T`).

The transports used are proved here as well: `IsEMSpaceUpTo` depends only on the isomorphism class
of the coefficient group (`isEMSpaceUpTo_of_addEquiv`) and is a homeomorphism invariant
(`isEMSpaceUpTo_of_homeomorph`, the `k`-part through `Work.Stems.mulEquiv_of_homotopyEquiv` and the
`π₀`-part through the path components).
-/

open CategoryTheory Limits

namespace Work.RatHurewicz

noncomputable section

/-- **Change of the coefficient group along an additive isomorphism.** -/
theorem isEMSpaceUpTo_of_addEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B] {k N : ℕ}
    (hk : 0 < k) {X : Type} [TopologicalSpace X] (pt : X)
    (h : Work.Serre.IsEMSpaceUpTo A k hk N X pt) (e : A ≃+ B) :
    Work.Serre.IsEMSpaceUpTo B k hk N X pt := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨iso⟩ := h.1
  exact ⟨⟨iso.trans (AddEquiv.toMultiplicative e)⟩, fun i hi hc => h.2 i hi hc⟩

/-- A homotopy group of a subsingleton space is trivial. -/
theorem subsingleton_homotopyGroup_of_subsingleton_type {N : Type} {X : Type} [TopologicalSpace X]
    (hX : Subsingleton X) (x : X) : Subsingleton (HomotopyGroup N X x) :=
  ⟨fun a b => by
    haveI : Subsingleton X := hX
    refine Quotient.inductionOn a fun p => Quotient.inductionOn b fun q => ?_
    exact congrArg (Quotient.mk _) (Subsingleton.elim p q)⟩

/-- **`IsEMSpaceUpTo` is a homeomorphism invariant.** -/
theorem isEMSpaceUpTo_of_homeomorph {A : Type} [AddCommGroup A] {k N : ℕ} (hk : 0 < k)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X)
    (h : Work.Serre.IsEMSpaceUpTo A k hk N X x) :
    Work.Serre.IsEMSpaceUpTo A k hk N Y (e x) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  constructor
  · obtain ⟨iso⟩ := h.1
    obtain ⟨eiso⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin k) e.toHomotopyEquiv x
    exact ⟨eiso.symm.trans iso⟩
  · intro i hi hc
    by_cases h0 : i = 0
    · subst h0
      haveI : Subsingleton (HomotopyGroup (Fin 0) X x) := h.2 0 (by omega) (Or.inl hk)
      have hZx : Subsingleton (ZerothHomotopy X) :=
        ⟨fun a b => by
          have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x))
            (Subsingleton.elim
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm a)
              ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).symm b))
          simpa using h1⟩
      have hZy : Subsingleton (ZerothHomotopy Y) :=
        Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv e.toHomotopyEquiv.symm hZx
      haveI := hZy
      exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := e x)).injective
        (Subsingleton.elim _ _)⟩
    · haveI : Nonempty (Fin i) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
      obtain ⟨eiso⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin i) e.toHomotopyEquiv x
      haveI : Subsingleton (HomotopyGroup (Fin i) X x) := h.2 i hi hc
      exact ⟨fun a b => eiso.symm.injective
        (Subsingleton.elim (eiso.symm a) (eiso.symm b))⟩

/-- **The space reshuffle** `(Fin (r+1) → X) ≃ₜ (Fin r → X) × X`, assembled from
`Fin (r+1) ≃ Fin r ⊕ PUnit` (`finSuccEquiv` composed with `Equiv.optionEquivSumPUnit`), the
homeomorphism `Homeomorph.sumArrowHomeomorphProdArrow : (ι ⊕ ι' → X) ≃ₜ (ι → X) × (ι' → X)`
(`Topology/Homeomorph/Lemmas.lean`) and `Homeomorph.funUnique : (PUnit → X) ≃ₜ X`. -/
def piConsHomeo (r : ℕ) (X : Type) [TopologicalSpace X] :
    ((Fin (r + 1)) → X) ≃ₜ (Fin r → X) × X :=
  (Homeomorph.piCongrLeft (Y := fun _ : Fin r ⊕ PUnit.{1} => X)
      ((finSuccEquiv r).trans (Equiv.optionEquivSumPUnit (Fin r)))).trans
    ((Homeomorph.sumArrowHomeomorphProdArrow (X := X) (ι := Fin r) (ι' := PUnit.{1})).trans
      (Homeomorph.prodCongr (Homeomorph.refl (Fin r → X))
        (Homeomorph.funUnique PUnit.{1} X)))

/-- **The group reshuffle** `(Fin r → A) × A ≃+ (Fin (r+1) → A)`. -/
def consAddEquiv (r : ℕ) (A : Type) [AddCommGroup A] :
    ((Fin r → A) × A) ≃+ (Fin (r + 1) → A) where
  toFun p := fun j => Fin.cases p.2 p.1 j
  invFun f := (fun i => f i.succ, f 0)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      simp [Fin.cases_succ]
    · simp [Fin.cases_zero]
  right_inv f := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cases_zero, Fin.cases_succ]
  map_add' p q := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp [Fin.cases_zero, Fin.cases_succ]

/-- **The `Fin r`-fold product of range models is a range model.** -/
theorem isEMSpaceUpTo_pi_fin {A : Type} [AddCommGroup A] {k N : ℕ} (hk : 0 < k) :
    ∀ (r : ℕ) {X : Type} [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo A k hk N X pt →
      Work.Serre.IsEMSpaceUpTo (Fin r → A) k hk N (Fin r → X) (fun _ => pt) := by
  intro r
  induction r with
  | zero =>
    intro X _ pt h
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    haveI hX : Subsingleton (Fin 0 → X) := ⟨fun f g => funext fun i => i.elim0⟩
    haveI hA : Subsingleton (Fin 0 → A) := ⟨fun f g => funext fun i => i.elim0⟩
    haveI hpi : Subsingleton (HomotopyGroup (Fin k) (Fin 0 → X) (fun _ => pt)) :=
      subsingleton_homotopyGroup_of_subsingleton_type hX _
    refine ⟨⟨MulEquiv.ofBijective
      (f := (1 : HomotopyGroup (Fin k) (Fin 0 → X) (fun _ => pt) →*
        Multiplicative (Fin 0 → A)))
      ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨1, Subsingleton.elim _ b⟩⟩⟩,
      fun i hi hc => subsingleton_homotopyGroup_of_subsingleton_type hX _⟩
  | succ r ih =>
    intro X _ pt h
    have hprod : Work.Serre.IsEMSpaceUpTo ((Fin r → A) × A) k hk N ((Fin r → X) × X)
        ((fun _ => pt), pt) :=
      isEMSpaceUpTo_prod hk (fun _ => pt) pt (ih (X := X) pt h) h
    have h1 : Work.Serre.IsEMSpaceUpTo ((Fin r → A) × A) k hk N (Fin (r + 1) → X)
        ((piConsHomeo r X).symm ((fun _ => pt), pt)) :=
      isEMSpaceUpTo_of_homeomorph hk (piConsHomeo r X).symm ((fun _ => pt), pt) hprod
    have hpt : (piConsHomeo r X).symm ((fun _ => pt), pt) = (fun _ => pt) := by
      ext i
      simp [piConsHomeo]
      generalize hw : (Equiv.optionEquivSumPUnit (Fin r)) ((finSuccEquiv r) i) = w
      cases w <;> simp
    rw [hpt] at h1
    exact isEMSpaceUpTo_of_addEquiv hk (fun _ => pt) h1 (consAddEquiv r A)

end

end Work.RatHurewicz

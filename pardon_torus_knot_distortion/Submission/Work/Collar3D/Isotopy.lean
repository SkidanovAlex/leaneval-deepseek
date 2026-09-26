import Submission.Work.Collar3D.Defs

/-!
# Ambient isotopies of `ℝ³`, and their supports

The chapter's local moves are *ambient*: a collar-supported isotopy has to be realised by an
isotopy of the whole space, fixed outside the collar (`Work.Collar3D.ambientOfChart`).  This file
fixes the vocabulary of ambient isotopies in the topological category:

* `Work.Collar3D.AmbientIsotopy` — a one-parameter family `t ↦ H t` of homeomorphisms of `ℝ³`
  whose evaluation map `(t,x) ↦ H t x` and its inverse are continuous;
* `Work.Collar3D.AmbientIsotopy.isFixedOn H S` — `H t` fixes `S` pointwise for every `t`;
* `Work.Collar3D.AmbientIsotopy.supportedIn H S` — `H t` is the identity outside `S` for every
  `t` (the shape in which the collar-supported moves are stated);
* `Work.Collar3D.IsotopicSets A B` — the existence of an ambient isotopy starting at the identity
  and carrying `A` onto `B`.

The elementary calculus of these (composition, inversion, reparametrisation, conjugation,
monotonicity of the fixed/support sets) is the API used by every theorem below.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

/-- **An ambient isotopy of `ℝ³`**: a one-parameter family of homeomorphisms of `ℝ³` whose
evaluation `(t,x) ↦ H t x` and inverse evaluation are continuous. -/
structure AmbientIsotopy where
  /-- the family of homeomorphisms -/
  toHomeomorph : ℝ → R3 ≃ₜ R3
  /-- joint continuity of the evaluation -/
  continuous_toFun : Continuous (fun p : ℝ × R3 => toHomeomorph p.1 p.2)
  /-- joint continuity of the inverse evaluation -/
  continuous_invFun : Continuous (fun p : ℝ × R3 => (toHomeomorph p.1).symm p.2)

instance : CoeFun AmbientIsotopy (fun _ => ℝ → R3 → R3) :=
  ⟨fun H t x => H.toHomeomorph t x⟩

@[simp] theorem AmbientIsotopy.coe_apply (H : AmbientIsotopy) (t : ℝ) (x : R3) :
    H t x = H.toHomeomorph t x := rfl

/-- The homeomorphism at time `t` of an ambient isotopy. -/
def AmbientIsotopy.homeo (H : AmbientIsotopy) (t : ℝ) : R3 ≃ₜ R3 := H.toHomeomorph t

@[simp] theorem AmbientIsotopy.homeo_apply (H : AmbientIsotopy) (t : ℝ) (x : R3) :
    H.homeo t x = H t x := rfl

/-- The identity isotopy. -/
def AmbientIsotopy.refl : AmbientIsotopy where
  toHomeomorph := fun _ => Homeomorph.refl R3
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_snd

@[simp] theorem AmbientIsotopy.refl_apply (t : ℝ) (x : R3) : AmbientIsotopy.refl t x = x := rfl

namespace AmbientIsotopy

variable (H : AmbientIsotopy)

/-- **`H` fixes `S` pointwise** at every time. -/
def isFixedOn (S : Set R3) : Prop := ∀ (t : ℝ) (x : R3), x ∈ S → H t x = x

/-- **`H` is supported in `S`**: it is the identity outside `S` at every time. -/
def supportedIn (S : Set R3) : Prop := ∀ (t : ℝ) (x : R3), x ∉ S → H t x = x

theorem isFixedOn_iff (S : Set R3) : H.isFixedOn S ↔ ∀ (t : ℝ), ∀ x ∈ S, H t x = x := Iff.rfl
theorem supportedIn_iff (S : Set R3) : H.supportedIn S ↔ ∀ (t : ℝ), ∀ x ∉ S, H t x = x := Iff.rfl

theorem supportedIn_of_isFixedOn {S : Set R3} (h : H.isFixedOn Sᶜ) : H.supportedIn S :=
  fun t x hx => h t x hx

theorem isFixedOn_of_supportedIn {S : Set R3} (h : H.supportedIn S) : H.isFixedOn Sᶜ :=
  fun t x hx => h t x hx

theorem supportedIn_mono {S T : Set R3} (h : H.supportedIn S) (hST : S ⊆ T) : H.supportedIn T :=
  fun t x hx => h t x fun hxS => hx (hST hxS)

theorem isFixedOn_mono {S T : Set R3} (h : H.isFixedOn S) (hTS : T ⊆ S) : H.isFixedOn T :=
  fun t x hx => h t x (hTS hx)

end AmbientIsotopy

/-- The inverse isotopy. -/
def AmbientIsotopy.symm (H : AmbientIsotopy) : AmbientIsotopy where
  toHomeomorph := fun t => (H.toHomeomorph t).symm
  continuous_toFun := H.continuous_invFun
  continuous_invFun := H.continuous_toFun

@[simp] theorem AmbientIsotopy.symm_apply (H : AmbientIsotopy) (t : ℝ) (x : R3) :
    H.symm t x = (H.toHomeomorph t).symm x := rfl

@[simp] theorem AmbientIsotopy.symm_symm (H : AmbientIsotopy) : H.symm.symm = H := rfl

/-- Composition of ambient isotopies: first `H`, then `K`. -/
def AmbientIsotopy.trans (H K : AmbientIsotopy) : AmbientIsotopy where
  toHomeomorph := fun t => (H.toHomeomorph t).trans (K.toHomeomorph t)
  continuous_toFun := (K.continuous_toFun.comp (continuous_fst.prodMk H.continuous_toFun)).congr
    (fun p => rfl)
  continuous_invFun := (H.continuous_invFun.comp (continuous_fst.prodMk K.continuous_invFun)).congr
    (fun p => rfl)

@[simp] theorem AmbientIsotopy.trans_apply (H K : AmbientIsotopy) (t : ℝ) (x : R3) :
    (H.trans K) t x = K t (H t x) := by
  show ((H.toHomeomorph t).trans (K.toHomeomorph t)) x = K.toHomeomorph t (H.toHomeomorph t x)
  rw [Homeomorph.trans_apply]

/-- **Reparametrisation** of an ambient isotopy along a continuous map of the parameter. -/
def AmbientIsotopy.reparam (H : AmbientIsotopy) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    AmbientIsotopy where
  toHomeomorph := fun t => H.toHomeomorph (φ t)
  continuous_toFun :=
    H.continuous_toFun.comp ((hφ.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun :=
    H.continuous_invFun.comp ((hφ.comp continuous_fst).prodMk continuous_snd)

@[simp] theorem AmbientIsotopy.reparam_apply (H : AmbientIsotopy) (φ : ℝ → ℝ)
    (hφ : Continuous φ) (t : ℝ) (x : R3) : (H.reparam φ hφ) t x = H (φ t) x := rfl

/-- Conjugation of a homeomorphism of `ℝ³` by another one. -/
def homeoConj (g e : R3 ≃ₜ R3) : R3 ≃ₜ R3 where
  toFun := fun x => g (e (g.symm x))
  invFun := fun x => g (e.symm (g.symm x))
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  continuous_toFun := g.continuous.comp (e.continuous.comp g.symm.continuous)
  continuous_invFun := g.continuous.comp (e.symm.continuous.comp g.symm.continuous)

@[simp] theorem homeoConj_apply (g e : R3 ≃ₜ R3) (x : R3) :
    homeoConj g e x = g (e (g.symm x)) := rfl

/-- **Conjugation** of an ambient isotopy by a homeomorphism of `ℝ³`. -/
def AmbientIsotopy.conj (H : AmbientIsotopy) (g : R3 ≃ₜ R3) : AmbientIsotopy where
  toHomeomorph := fun t => homeoConj g (H.toHomeomorph t)
  continuous_toFun := by
    have hgs : Continuous (fun p : ℝ × R3 => g.symm p.2) := g.symm.continuous.comp continuous_snd
    have hmid : Continuous (fun p : ℝ × R3 => H.toHomeomorph p.1 (g.symm p.2)) :=
      (H.continuous_toFun.comp (continuous_fst.prodMk hgs)).congr (fun p => rfl)
    have hout : Continuous (fun p : ℝ × R3 => g (H.toHomeomorph p.1 (g.symm p.2))) :=
      g.continuous.comp hmid
    exact hout.congr (fun p => by simp [homeoConj])
  continuous_invFun := by
    have hgs : Continuous (fun p : ℝ × R3 => g.symm p.2) := g.symm.continuous.comp continuous_snd
    have hmid : Continuous (fun p : ℝ × R3 => (H.toHomeomorph p.1).symm (g.symm p.2)) :=
      (H.continuous_invFun.comp (continuous_fst.prodMk hgs)).congr (fun p => rfl)
    have hout : Continuous (fun p : ℝ × R3 => g ((H.toHomeomorph p.1).symm (g.symm p.2))) :=
      g.continuous.comp hmid
    exact hout.congr (fun p => by simp [homeoConj, Homeomorph.symm_apply_apply])

@[simp] theorem AmbientIsotopy.conj_apply (H : AmbientIsotopy) (g : R3 ≃ₜ R3) (t : ℝ)
    (x : R3) : (H.conj g) t x = g (H t (g.symm x)) := rfl

/-- **Two sets are isotopic** if some ambient isotopy starting at the identity carries one onto
the other. -/
def IsotopicSets (A B : Set R3) : Prop :=
  ∃ H : AmbientIsotopy, (∀ x : R3, H 0 x = x) ∧ H 1 '' A = B

theorem IsotopicSets.refl (A : Set R3) : IsotopicSets A A :=
  ⟨AmbientIsotopy.refl, fun _ => rfl, by simp⟩

end

end Work.Collar3D

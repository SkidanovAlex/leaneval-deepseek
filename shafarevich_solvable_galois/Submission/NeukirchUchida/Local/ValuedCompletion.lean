import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_of_valuation_comp_eq
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_of_withVal_valuation_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Extending valuation-preserving automorphisms to completions

If `σ` is a ring automorphism of a valued field `(R, v)` which preserves the valuation
(`v (σ x) = v x` for all `x`), then `σ` is uniformly continuous for the valuation uniformity,
hence extends to a ring automorphism of the completion `v.Completion`.  The extension is
functorial and faithful: the map `σ ↦ σ̂` is an injective group homomorphism from the group of
valuation-preserving automorphisms into the automorphism group of the completion.

This is the elementary half of the statement that the decomposition group of a place is the
Galois group of the corresponding local extension.
-/

open UniformSpace

namespace Submission.NeukirchUchida.Local

variable {R : Type*} [Field R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A ring endomorphism of the valued ring `(R, v)` preserving `v` is uniformly continuous for
the uniformity induced by `v`.  (Commons form, for `WithVal`.) -/
theorem uniformContinuous_of_withVal_valuation_eq (v : Valuation R Γ₀)
    (f : WithVal v ≃+* WithVal v)
    (hf : ∀ x : WithVal v, WithVal.valuation v (f x) = WithVal.valuation v x) :
    UniformContinuous (f : WithVal v → WithVal v) :=
  Commons.Topology.Algebra.Valued.uniformContinuous_of_withVal_valuation_eq v f hf

section Conj

variable {A B : Type*} [Ring A] [Ring B]

/-- Conjugation by a ring isomorphism `e : A ≃+* B` identifies the automorphism group of `B`
with the automorphism group of `A`. -/
noncomputable def ringEquivConj (e : A ≃+* B) : (B ≃+* B) ≃* (A ≃+* A) where
  toFun φ := e.trans (φ.trans e.symm)
  invFun ψ := e.symm.trans (ψ.trans e)
  left_inv φ := by ext x; simp [RingEquiv.trans_apply]
  right_inv ψ := by ext x; simp [RingEquiv.trans_apply]
  map_mul' φ ψ := by ext x; simp [RingEquiv.trans_apply]

@[simp]
theorem ringEquivConj_apply (e : A ≃+* B) (φ : B ≃+* B) (x : A) :
    ringEquivConj e φ x = e.symm (φ (e x)) := rfl

end Conj

/-- The ring equivalence of `WithVal v` obtained by conjugating `σ : R ≃+* R` by the tautological
identification `WithVal v ≃+* R`. -/
noncomputable def withValConj (v : Valuation R Γ₀) (σ : R ≃+* R) : WithVal v ≃+* WithVal v :=
  (WithVal.equiv v).trans (σ.trans (WithVal.equiv v).symm)

theorem withValConj_apply (v : Valuation R Γ₀) (σ : R ≃+* R) (x : WithVal v) :
    withValConj v σ x = (WithVal.equiv v).symm (σ ((WithVal.equiv v) x)) := rfl

theorem withValConj_mul (v : Valuation R Γ₀) (σ τ : R ≃+* R) :
    withValConj v (σ * τ) = withValConj v σ * withValConj v τ := by
  ext x
  simp only [withValConj_apply]
  rfl

theorem withValConj_one (v : Valuation R Γ₀) : withValConj v 1 = 1 := by
  ext x
  simp only [withValConj_apply]
  rfl

theorem withVal_valuation_withValConj (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) (x : WithVal v) :
    WithVal.valuation v (withValConj v σ x) = WithVal.valuation v x := by
  have h : (WithVal.equiv v) (withValConj v σ x) = σ ((WithVal.equiv v) x) := rfl
  rw [show WithVal.valuation v (withValConj v σ x)
        = v ((WithVal.equiv v) (withValConj v σ x)) from rfl, h, hσ,
    show v ((WithVal.equiv v) x) = WithVal.valuation v x from rfl]

theorem withVal_valuation_withValConj_symm (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) (x : WithVal v) :
    WithVal.valuation v ((withValConj v σ).symm x) = WithVal.valuation v x := by
  have h := withVal_valuation_withValConj v σ hσ ((withValConj v σ).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- **A valuation-preserving ring automorphism of a valued field extends to its completion.** -/
noncomputable def completionRingEquiv (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) : v.Completion ≃+* v.Completion :=
  Completion.mapRingEquiv (withValConj v σ)
    (uniformContinuous_of_withVal_valuation_eq v _ (withVal_valuation_withValConj v σ hσ)).continuous
    (uniformContinuous_of_withVal_valuation_eq v _
      (withVal_valuation_withValConj_symm v σ hσ)).continuous

@[simp]
theorem completionRingEquiv_coe (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) (x : R) :
    completionRingEquiv v σ hσ (x : v.Completion) = (σ x : v.Completion) := by
  rw [completionRingEquiv, UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe (uniformContinuous_of_withVal_valuation_eq v _
      (withVal_valuation_withValConj v σ hσ))]
  rfl

/-- The group of ring automorphisms of `R` preserving the valuation `v`. -/
def valuationPreservingSubgroup (v : Valuation R Γ₀) : Subgroup (R ≃+* R) where
  carrier := {σ | ∀ x : R, v (σ x) = v x}
  mul_mem' := by
    intro σ τ hσ hτ x
    change v (σ (τ x)) = v x
    rw [hσ, hτ]
  one_mem' := by intro x; rfl
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ.symm x)
    rw [RingEquiv.apply_symm_apply] at h
    exact h.symm

@[simp]
theorem mem_valuationPreservingSubgroup {v : Valuation R Γ₀} {σ : R ≃+* R} :
    σ ∈ valuationPreservingSubgroup v ↔ ∀ x : R, v (σ x) = v x := Iff.rfl

theorem withVal_valuation_withValConj_of_mem (v : Valuation R Γ₀) {σ : R ≃+* R}
    (hσ : σ ∈ valuationPreservingSubgroup v) (x : WithVal v) :
    WithVal.valuation v (withValConj v σ x) = WithVal.valuation v x :=
  withVal_valuation_withValConj v σ hσ x

section MonoidHom

/-- The underlying function of `completionRingEquiv`. -/
theorem completionRingEquiv_apply (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) :
    (completionRingEquiv v σ hσ : v.Completion → v.Completion) =
      Completion.map (withValConj v σ : WithVal v → WithVal v) := by
  funext x
  show Completion.mapRingEquiv (withValConj v σ) _ _ x = _
  rw [Completion.mapRingEquiv_apply]

theorem continuous_completionRingEquiv (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) :
    Continuous (completionRingEquiv v σ hσ : v.Completion → v.Completion) := by
  rw [completionRingEquiv_apply]
  exact Completion.continuous_map

@[simp]
theorem completionRingEquiv_mapWithVal (v : Valuation R Γ₀) (σ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) (a : WithVal v) :
    completionRingEquiv v σ hσ (a : v.Completion) =
      (withValConj v σ a : v.Completion) := by
  rw [completionRingEquiv_apply]
  exact Completion.map_coe
    (uniformContinuous_of_withVal_valuation_eq v _ (withVal_valuation_withValConj v σ hσ)) a

theorem completionRingEquiv_mul (v : Valuation R Γ₀) (σ τ : R ≃+* R)
    (hσ : ∀ x : R, v (σ x) = v x) (hτ : ∀ x : R, v (τ x) = v x)
    (hστ : ∀ x : R, v ((σ * τ) x) = v x) :
    completionRingEquiv v (σ * τ) hστ =
      completionRingEquiv v σ hσ * completionRingEquiv v τ hτ := by
  have hcontσ := uniformContinuous_of_withVal_valuation_eq v (withValConj v σ)
    (withVal_valuation_withValConj v σ hσ)
  have hcontτ := uniformContinuous_of_withVal_valuation_eq v (withValConj v τ)
    (withVal_valuation_withValConj v τ hτ)
  ext x
  change Completion.map (withValConj v (σ * τ) : WithVal v → WithVal v) x =
    Completion.map (withValConj v σ : WithVal v → WithVal v)
      (Completion.map (withValConj v τ : WithVal v → WithVal v) x)
  have hc : Completion.map (withValConj v σ : WithVal v → WithVal v)
        (Completion.map (withValConj v τ : WithVal v → WithVal v) x) =
      Completion.map ((withValConj v σ : WithVal v → WithVal v) ∘
        (withValConj v τ : WithVal v → WithVal v)) x :=
    congr_fun (Completion.map_comp (f := (withValConj v τ : WithVal v → WithVal v))
      (g := (withValConj v σ : WithVal v → WithVal v)) hcontσ hcontτ) x
  rw [hc]
  rw [show (withValConj v (σ * τ) : WithVal v → WithVal v) =
      ((withValConj v σ : WithVal v → WithVal v) ∘
        (withValConj v τ : WithVal v → WithVal v)) from by
    rw [withValConj_mul]
    rfl]

theorem completionRingEquiv_one (v : Valuation R Γ₀)
    (h : ∀ x : R, v ((1 : R ≃+* R) x) = v x) :
    completionRingEquiv v 1 h = 1 := by
  ext x
  change Completion.map (withValConj v (1 : R ≃+* R) : WithVal v → WithVal v) x =
    (1 : v.Completion ≃+* v.Completion) x
  have hid : (withValConj v (1 : R ≃+* R) : WithVal v → WithVal v) = id := by
    rw [withValConj_one]
    rfl
  rw [hid, Completion.map_id]
  rfl

/-- **The extension of valuation-preserving automorphisms to the completion is a group
homomorphism.** -/
noncomputable def completionMonoidHom (v : Valuation R Γ₀) :
    valuationPreservingSubgroup v →* (v.Completion ≃+* v.Completion) where
  toFun σ := completionRingEquiv v σ σ.2
  map_one' := completionRingEquiv_one v _
  map_mul' σ τ := completionRingEquiv_mul v σ τ σ.2 τ.2 (σ * τ).2

@[simp]
theorem completionMonoidHom_apply (v : Valuation R Γ₀) (σ : valuationPreservingSubgroup v) :
    completionMonoidHom v σ = completionRingEquiv v σ σ.2 := rfl

@[simp]
theorem completionMonoidHom_coe (v : Valuation R Γ₀) (σ : valuationPreservingSubgroup v)
    (x : R) :
    completionMonoidHom v σ (x : v.Completion) = ((σ : R ≃+* R) x : v.Completion) :=
  completionRingEquiv_coe v σ σ.2 x

end MonoidHom

end Submission.NeukirchUchida.Local

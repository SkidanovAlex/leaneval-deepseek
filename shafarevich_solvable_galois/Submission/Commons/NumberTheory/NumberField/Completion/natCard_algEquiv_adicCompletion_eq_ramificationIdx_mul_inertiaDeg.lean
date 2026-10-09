import Mathlib
import Submission.Commons.FieldTheory.Galois.card_algEquiv_le_finrank
import Submission.Commons.FieldTheory.Galois.natCard_algEquiv_le_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.liesOver_map_galRestrict
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_of_valuation_comp_eq
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_of_withVal_valuation_eq

/-!
# The order of the local Galois group of an adic completion

This file proves

`Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) = e · f`

for a finite Galois extension `L / K` of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height one prime of `𝓞 L` lying over `Q`, where `e` is the ramification index and `f` the inertia
degree of `q` over `Q`.

The argument is the classical one:  the decomposition group `D_q ≤ Gal(L/K)` of `q` (the group of
elements of `Gal(L/K)` which preserve the prime `q`) has `e · f` elements, and it acts faithfully on
the local field `L_q` by `K_Q`-algebra automorphisms.  Hence `e · f ≤ Nat.card Gal(L_q / K_Q)`,
while the general inequality `Nat.card Gal(E/F) ≤ [E : F]` for a finite field extension together
with the local fundamental identity `[L_q : K_Q] = e · f` gives the reverse inequality.

The supporting material is developed here from scratch on top of Mathlib and the shared commons:
extending valuation-preserving automorphisms to completions, the action of the decomposition group
on the `q`-adic completion, and the identification of the decomposition group with the local
Galois group.
-/

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

namespace Commons.NumberTheory.NumberField.Completion

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

end Commons.NumberTheory.NumberField.Completion

/-!
# Decomposition groups act on the completion

Let `L / K` be a finite Galois extension of number fields and `w` a finite place of `L`
(a height one prime of `𝓞 L`).  The *decomposition group* of `w` is the stabiliser of `w`
under the natural action of `Gal(L/K)` on the places of `L`.

The main results of this file are

* `decompositionSubgroup_preserves_valuation` : every `σ` in the decomposition group of `w`
  preserves the `w`-adic valuation on `L`;
* `decompositionSubgroup_preserves_adicAbv` : and therefore the `w`-adic absolute value;
* `decompositionToCompletion` : the resulting group homomorphism from the decomposition group to
  the automorphism group of the completion of `L` at `w`;
* `decompositionToCompletion_injective` : this homomorphism is faithful.

These are the ingredients of the identification of the decomposition group with the Galois group
of the corresponding local extension.
-/

open scoped NumberField

set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.NumberField.Completion

/-! ## Places under ring automorphisms -/

/-- The image of a height one prime of a Dedekind domain under a ring automorphism. -/
noncomputable def HeightOneSpectrum.mapRingEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (v : IsDedekindDomain.HeightOneSpectrum R) :
    IsDedekindDomain.HeightOneSpectrum R where
  asIdeal := v.asIdeal.map (e : R →+* R)
  isPrime := Ideal.map_isPrime_of_equiv e
  ne_bot := by
    intro h
    exact v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)

@[simp]
theorem HeightOneSpectrum.mapRingEquiv_asIdeal {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (v : IsDedekindDomain.HeightOneSpectrum R) :
    (HeightOneSpectrum.mapRingEquiv e v).asIdeal = v.asIdeal.map (e : R →+* R) := rfl

theorem HeightOneSpectrum.mapRingEquiv_mul {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e f : R ≃+* R) (v : IsDedekindDomain.HeightOneSpectrum R) :
    HeightOneSpectrum.mapRingEquiv (e * f) v =
      HeightOneSpectrum.mapRingEquiv e (HeightOneSpectrum.mapRingEquiv f v) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show v.asIdeal.map ((e * f) : R →+* R) =
    (v.asIdeal.map (f : R →+* R)).map (e : R →+* R)
  rw [show ((e * f) : R →+* R) = (e : R →+* R).comp (f : R →+* R) from by ext x; rfl,
    Ideal.map_map]

theorem HeightOneSpectrum.mapRingEquiv_one {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    HeightOneSpectrum.mapRingEquiv (1 : R ≃+* R) v = v := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show v.asIdeal.map ((1 : R ≃+* R) : R →+* R) = v.asIdeal
  rw [show ((1 : R ≃+* R) : R →+* R) = (1 : R →+* R) from rfl]
  exact Ideal.map_id v.asIdeal

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The action of `Gal(L/K)` on the finite places of `L`: the place `σ • w` is the image of `w`
under the ring automorphism of `𝓞 L` induced by `σ`. -/
noncomputable def placeSmul (σ : Gal(L/K)) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.mapRingEquiv (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) w

@[simp]
theorem placeSmul_asIdeal (σ : Gal(L/K)) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    (placeSmul σ w).asIdeal =
      w.asIdeal.map (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) := rfl

theorem placeSmul_mul (σ τ : Gal(L/K)) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    placeSmul (σ * τ) w = placeSmul σ (placeSmul τ w) := by
  have h : (galRestrict (𝓞 K) K L (𝓞 L) (σ * τ) : 𝓞 L ≃+* 𝓞 L) =
      (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) *
        (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L ≃+* 𝓞 L) := by
    rw [map_mul]
    rfl
  simp only [placeSmul, h, HeightOneSpectrum.mapRingEquiv_mul]

theorem placeSmul_one (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    placeSmul (1 : Gal(L/K)) w = w := by
  have h : (galRestrict (𝓞 K) K L (𝓞 L) (1 : Gal(L/K)) : 𝓞 L ≃+* 𝓞 L) = 1 := by
    rw [map_one]
    rfl
  simp only [placeSmul, h, HeightOneSpectrum.mapRingEquiv_one]

/-- The Galois action on places preserves the place `p` of `K` below. -/
theorem liesOver_placeSmul (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver p.asIdeal]
    (σ : Gal(L/K)) : (placeSmul σ w).asIdeal.LiesOver p.asIdeal := by
  rw [placeSmul_asIdeal]
  exact Commons.NumberTheory.NumberField.liesOver_map_galRestrict p w σ

/-- The decomposition group of a finite place `w` of `L` over `K`: the stabiliser of `w` in
`Gal(L/K)`. -/
noncomputable def decompositionSubgroup (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    Subgroup Gal(L/K) where
  carrier := {σ | placeSmul σ w = w}
  mul_mem' := by
    intro σ τ hσ hτ
    change placeSmul (σ * τ) w = w
    rw [placeSmul_mul, hτ, hσ]
  one_mem' := by
    change placeSmul (1 : Gal(L/K)) w = w
    rw [placeSmul_one]
  inv_mem' := by
    intro σ hσ
    change placeSmul σ⁻¹ w = w
    have h : placeSmul σ⁻¹ w = placeSmul σ⁻¹ (placeSmul σ w) :=
      congrArg (placeSmul σ⁻¹) hσ.symm
    rw [h, ← placeSmul_mul, inv_mul_cancel, placeSmul_one]

@[simp]
theorem mem_decompositionSubgroup {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    {σ : Gal(L/K)} : σ ∈ decompositionSubgroup w ↔ placeSmul σ w = w := Iff.rfl

open scoped Pointwise in
/-- The decomposition group of `w` is the stabiliser of `w.asIdeal` for the action of `Gal(L/K)`
on the ideals of `𝓞 L` induced by `galRestrict`. -/
theorem mem_decompositionSubgroup_iff_smul
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K)) :
    letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
      IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    (σ ∈ decompositionSubgroup (K := K) w ↔ σ • w.asIdeal = w.asIdeal) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  rw [mem_decompositionSubgroup]
  constructor
  · intro h
    have h' := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
    rw [placeSmul_asIdeal] at h'
    rwa [show σ • w.asIdeal =
      Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) w.asIdeal from rfl]
  · intro h
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [placeSmul_asIdeal]
    rwa [show σ • w.asIdeal =
      Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) w.asIdeal from rfl] at h

/-- A decomposition group element fixes the height one prime underlying the place. -/
theorem decompositionSubgroup_map_eq {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    {σ : Gal(L/K)} (hσ : σ ∈ decompositionSubgroup w) :
    w.asIdeal.map (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) = w.asIdeal :=
  congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hσ

/-- **Elements of the decomposition group preserve the `w`-adic valuation.** -/
theorem decompositionSubgroup_preserves_valuation
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ decompositionSubgroup w) (x : L) :
    IsDedekindDomain.HeightOneSpectrum.valuation L w (σ x) =
      IsDedekindDomain.HeightOneSpectrum.valuation L w x := by
  have hmap := decompositionSubgroup_map_eq hσ
  have hσ' : ∀ r : 𝓞 L, σ.toRingEquiv (algebraMap (𝓞 L) L r) =
      algebraMap (𝓞 L) L ((galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv r) :=
    fun r => (algebraMap_galRestrict_apply (𝓞 K) σ r).symm
  exact Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    ((galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv) σ.toRingEquiv hσ' w w hmap.symm x

/-- Decomposition group elements preserve the `w`-adic absolute value. -/
theorem decompositionSubgroup_preserves_adicAbv
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ decompositionSubgroup w) (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L w (σ x) =
      NumberField.HeightOneSpectrum.adicAbv L w x := by
  simp only [NumberField.HeightOneSpectrum.adicAbv_def,
    decompositionSubgroup_preserves_valuation hσ x]

/-! ## The action on the completion -/

/-- The decomposition group, regarded as a subgroup of the group of valuation-preserving ring
automorphisms of `L` (for the `w`-adic valuation). -/
noncomputable def decompositionToValuationPreserving
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    decompositionSubgroup (K := K) w →* valuationPreservingSubgroup (w.valuation L) where
  toFun σ := ⟨σ.1.toRingEquiv, fun x => decompositionSubgroup_preserves_valuation σ.2 x⟩
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl

/-- **The decomposition group acts on the completion.**  This is the composite of the inclusion
of the decomposition group into the valuation-preserving automorphisms of `L` with the extension
map `completionMonoidHom`. -/
noncomputable def decompositionToCompletion (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    decompositionSubgroup (K := K) w →*
      ((w.valuation L).Completion ≃+* (w.valuation L).Completion) :=
  (completionMonoidHom (w.valuation L)).comp (decompositionToValuationPreserving w)

theorem decompositionToCompletion_apply (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K := K) w) :
    decompositionToCompletion (K := K) w σ =
      completionRingEquiv (w.valuation L) σ.1.toRingEquiv
        (fun x => decompositionSubgroup_preserves_valuation σ.2 x) := rfl

/-- The class of `x : L` in the completion is injective. -/
theorem coe_completion_injective {R : Type*} [Field R] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) :
    Function.Injective ((↑) : R → v.Completion) := by
  intro x y hxy
  have h : ((WithVal.equiv v).symm x : v.Completion) =
      ((WithVal.equiv v).symm y : v.Completion) := hxy
  have h' := UniformSpace.Completion.coe_injective (WithVal v) h
  exact (WithVal.equiv v).symm.injective h'

/-- **The action of the decomposition group on the completion is faithful.** -/
theorem decompositionToCompletion_injective (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    Function.Injective (decompositionToCompletion (K := K) w) := by
  intro σ τ h
  have h2 : decompositionToCompletion (K := K) w σ = decompositionToCompletion (K := K) w τ := h
  have h3 : ∀ x : L, σ.1.toRingEquiv x = τ.1.toRingEquiv x := by
    intro x
    have hx := congrArg (fun f : (w.valuation L).Completion ≃+*
      (w.valuation L).Completion => f (x : (w.valuation L).Completion)) h2
    simp only [decompositionToCompletion_apply, completionRingEquiv_coe] at hx
    exact coe_completion_injective (w.valuation L) hx
  ext x
  exact h3 x

/-! ## The action on the adic completion -/

/-- **The decomposition group acts on the `w`-adic completion of `L`.** -/
noncomputable def decompositionToAdicCompletion (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    decompositionSubgroup (K := K) w →* (w.adicCompletion L ≃+* w.adicCompletion L) :=
  (ringEquivConj (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w)).toMonoidHom.comp
    (decompositionToCompletion (K := K) w)

/-- **The action of the decomposition group on the `w`-adic completion is faithful.** -/
theorem decompositionToAdicCompletion_injective
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    Function.Injective (decompositionToAdicCompletion (K := K) w) := by
  rw [decompositionToAdicCompletion, MonoidHom.coe_comp]
  exact (ringEquivConj
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w)).injective.comp
      (decompositionToCompletion_injective (K := K) w)

theorem continuous_decompositionToCompletion (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K := K) w) :
    Continuous (decompositionToCompletion (K := K) w σ :
      (w.valuation L).Completion → (w.valuation L).Completion) := by
  rw [decompositionToCompletion_apply]
  exact continuous_completionRingEquiv _ _ _

/-- The image of `x : L` in the `w`-adic completion. -/
@[simp]
theorem decompositionToAdicCompletion_coe (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K := K) w) (x : L) :
    decompositionToAdicCompletion (K := K) w σ (x : w.adicCompletion L) =
      (σ.1 x : w.adicCompletion L) := by
  rw [decompositionToAdicCompletion, MonoidHom.coe_comp]
  change (ringEquivConj (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w))
      (decompositionToCompletion (K := K) w σ) (x : w.adicCompletion L) = _
  rw [ringEquivConj_apply]
  have h1 : (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w)
      (x : w.adicCompletion L) = (x : (w.valuation L).Completion) := rfl
  rw [h1, decompositionToCompletion_apply, completionRingEquiv_coe]
  rfl

/-- The action of the decomposition group on the `w`-adic completion is continuous. -/
theorem continuous_decompositionToAdicCompletion
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K := K) w) :
    Continuous (decompositionToAdicCompletion (K := K) w σ :
      w.adicCompletion L → w.adicCompletion L) := by
  have hfun : (decompositionToAdicCompletion (K := K) w σ : w.adicCompletion L → w.adicCompletion L)
      = fun x => (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm
          (decompositionToCompletion (K := K) w σ
            ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w) x)) := by
    funext x
    rw [decompositionToAdicCompletion, MonoidHom.coe_comp]
    rfl
  rw [hfun]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    ((continuous_decompositionToCompletion w σ).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion L w))

/-- The `K_p`-algebra structure on the `w`-adic completion of `L`, given by the natural
embedding `K_p → L_w` induced by the inclusion `K → L`. -/
noncomputable def adicCompletionAlgebra (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    Algebra (p.adicCompletion K) (w.adicCompletion L) :=
  (Commons.RingTheory.Henselian.adicCompletionMap p w h).toAlgebra

theorem adicCompletionAlgebra_algebraMap (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    (algebraMap (p.adicCompletion K) (w.adicCompletion L) :
        p.adicCompletion K →+* w.adicCompletion L) =
      Commons.RingTheory.Henselian.adicCompletionMap p w h := rfl

/-- **The decomposition group acts by `K_p`-algebra automorphisms**: every element of the
decomposition group of `w` fixes the image of the completion `K_p` inside `L_w`. -/
theorem decompositionToAdicCompletion_adicCompletionMap
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : decompositionSubgroup (K := K) w) (y : p.adicCompletion K) :
    decompositionToAdicCompletion (K := K) w σ
        (Commons.RingTheory.Henselian.adicCompletionMap p w h y) =
      Commons.RingTheory.Henselian.adicCompletionMap p w h y := by
  have hdense : DenseRange (algebraMap K (p.adicCompletion K)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K p
  have hcont :=
    (continuous_decompositionToAdicCompletion (K := K) w σ).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous p w h)
  have hEq : (⇑(decompositionToAdicCompletion (K := K) w σ) ∘
        ⇑(Commons.RingTheory.Henselian.adicCompletionMap p w h)) =
      ⇑(Commons.RingTheory.Henselian.adicCompletionMap p w h) :=
    DenseRange.equalizer hdense hcont
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous p w h) (funext fun x => by
        have hx : (algebraMap K (p.adicCompletion K)) x = (x : p.adicCompletion K) := by
          rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
          rfl
        simp only [Function.comp_apply]
        rw [hx, Commons.RingTheory.Henselian.adicCompletionMap_apply p w h x,
          decompositionToAdicCompletion_coe, AlgEquiv.commutes σ.1 x])
  exact congr_fun hEq y

/-- The same statement, phrased with the `K_p`-algebra structure on `L_w`. -/
theorem decompositionToAdicCompletion_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : decompositionSubgroup (K := K) w) (y : p.adicCompletion K) :
    letI := adicCompletionAlgebra p w h
    decompositionToAdicCompletion (K := K) w σ
        (algebraMap (p.adicCompletion K) (w.adicCompletion L) y) =
      algebraMap (p.adicCompletion K) (w.adicCompletion L) y :=
  letI := adicCompletionAlgebra p w h
  decompositionToAdicCompletion_adicCompletionMap p w h σ y

end Commons.NumberTheory.NumberField.Completion

/-!
# The decomposition group is the local Galois group

Let `L / K` be a finite Galois extension of number fields, `p` a finite place of `K` and `w` a
finite place of `L` lying over `p`.  The decomposition group `D_w ≤ Gal(L/K)` of `w` acts on the
`w`-adic completion `L_w` by `K_p`-algebra automorphisms, and this action identifies `D_w` with
the local Galois group `Gal(L_w / K_p)`.

This is Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter II, and the key input of
the local-global bridge used in Chapter XII (the description of the decomposition group as the
stabiliser of a place, `(12.1.9)`).

## Main results

* `card_decompositionSubgroup` : `Nat.card D_w = e(w|p) * f(w|p)`;
* `finrank_adicCompletion_eq_ef` : `[L_w : K_p] = e(w|p) * f(w|p)`;
* `decompositionToLocalGalois` : the monoid homomorphism `D_w →* Gal(L_w / K_p)`;
* `decompositionSubgroupMulEquivLocalGalois` : `D_w ≃* Gal(L_w / K_p)`.

The proof compares cardinalities: `D_w` has `e·f` elements, `Gal(L_w/K_p)` is a finite group of
cardinality at most `[L_w : K_p] = e·f`, and the natural map between them is injective.
-/

open scoped Pointwise NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Characteristic and embeddability of the adic completion -/

/-- The canonical embedding of a number field into its `p`-adic completion is injective. -/
theorem injective_algebraMap_adicCompletion {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Function.Injective (algebraMap K (p.adicCompletion K)) := by
  have h : ⇑(algebraMap K (p.adicCompletion K)) = ((↑) : K → p.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [h]
  intro x y hxy
  have hxy' : ((WithVal.equiv (p.valuation K)).symm x : (p.valuation K).Completion) =
      ((WithVal.equiv (p.valuation K)).symm y : (p.valuation K).Completion) :=
    congrArg (fun z : p.adicCompletion K => z.toCompletion) hxy
  exact (WithVal.equiv (p.valuation K)).symm.injective
    (UniformSpace.Completion.coe_injective (WithVal (p.valuation K)) hxy')

/-- **The `p`-adic completion of a number field has characteristic zero.** -/
theorem charZero_adicCompletion {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : CharZero (p.adicCompletion K) :=
  CharZero.of_addMonoidHom (algebraMap K (p.adicCompletion K)).toAddMonoidHom (by simp)
    (fun x y h => injective_algebraMap_adicCompletion p (by simpa using h))

section cardDecomposition

/-- **The order of the decomposition group is `e · f`.** -/
theorem card_decompositionSubgroup
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    Nat.card (decompositionSubgroup (K := K) w) =
      p.asIdeal.ramificationIdxIn (𝓞 L) * p.asIdeal.inertiaDegIn (𝓞 L) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGal : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  haveI : PerfectField p.asIdeal.ResidueField := by
    haveI : Finite (𝓞 K ⧸ p.asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum p
    infer_instance
  haveI := h
  have hEq : decompositionSubgroup (K := K) w = MulAction.stabilizer Gal(L/K) w.asIdeal := by
    ext σ
    rw [mem_decompositionSubgroup_iff_smul, MulAction.mem_stabilizer_iff]
  rw [hEq, Ideal.card_stabilizer_eq p.asIdeal w.asIdeal]

/-- **The local degree `[L_w : K_p]` equals `e · f`.** -/
theorem finrank_adicCompletion_eq_ef
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    @Module.finrank (p.adicCompletion K) (w.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap p w h)).toModule =
      p.asIdeal.ramificationIdxIn (𝓞 L) * p.asIdeal.inertiaDegIn (𝓞 L) := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGal : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  haveI := h
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal w.asIdeal
        Gal(L/K),
      Ideal.inertiaDegIn_eq_inertiaDeg (A := 𝓞 K) (B := 𝓞 L) p.asIdeal w.asIdeal Gal(L/K)]
  exact (Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    p w h).symm

/-- The number of `K_p`-algebra automorphisms of `L_w` is at most the local degree `[L_w : K_p]`. -/
theorem natCard_localAlgEquiv_le_finrank
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    Nat.card (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L) ≤
      Module.finrank (p.adicCompletion K) (w.adicCompletion L) := by
  letI := adicCompletionAlgebra p w h
  haveI : Module.Finite (p.adicCompletion K) (w.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p w h
  exact Commons.FieldTheory.Galois.natCard_algEquiv_le_finrank

/-- The local degree expressed through the `K_p`-algebra structure of `adicCompletionAlgebra`. -/
theorem finrank_adicCompletion_eq_ef'
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    Module.finrank (p.adicCompletion K) (w.adicCompletion L) =
      p.asIdeal.ramificationIdxIn (𝓞 L) * p.asIdeal.inertiaDegIn (𝓞 L) :=
  finrank_adicCompletion_eq_ef p w h

end cardDecomposition

/-- **The extension of local fields `L_w / K_p` is separable** (it is a finite extension of fields
of characteristic zero). -/
theorem isSeparable_adicCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    Algebra.IsSeparable (p.adicCompletion K) (w.adicCompletion L) := by
  letI := adicCompletionAlgebra p w h
  haveI : CharZero (p.adicCompletion K) := charZero_adicCompletion p
  haveI : Module.Finite (p.adicCompletion K) (w.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p w h
  haveI : Algebra.IsIntegral (p.adicCompletion K) (w.adicCompletion L) :=
    ⟨fun x => IsIntegral.of_finite (p.adicCompletion K) x⟩
  exact Algebra.IsSeparable.of_integral _ _

section localGalois

/-- The decomposition group acts on `L_w` by `K_p`-algebra automorphisms. -/
noncomputable def decompositionToLocalGaloisFun
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : decompositionSubgroup (K := K) w) :
    letI := adicCompletionAlgebra p w h
    w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L :=
  letI := adicCompletionAlgebra p w h
  AlgEquiv.ofRingEquiv (f := decompositionToAdicCompletion (K := K) w σ)
    (fun y => decompositionToAdicCompletion_adicCompletionMap p w h σ y)

@[simp]
theorem decompositionToLocalGaloisFun_apply
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : decompositionSubgroup (K := K) w) :
    letI := adicCompletionAlgebra p w h
    (⇑(decompositionToLocalGaloisFun p w h σ) : w.adicCompletion L → w.adicCompletion L) =
      ⇑(decompositionToAdicCompletion (K := K) w σ) := rfl

/-- **The decomposition group acts on the local field `L_w` by `K_p`-automorphisms.** -/
noncomputable def decompositionToLocalGalois
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    decompositionSubgroup (K := K) w →*
      (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L) :=
  letI := adicCompletionAlgebra p w h
  { toFun := decompositionToLocalGaloisFun p w h
    map_one' := by
      apply AlgEquiv.ext
      intro x
      rw [decompositionToLocalGaloisFun_apply]
      exact congrArg (fun f => f x) (map_one (decompositionToAdicCompletion (K := K) w))
    map_mul' := by
      intro σ τ
      apply AlgEquiv.ext
      intro x
      rw [decompositionToLocalGaloisFun_apply, AlgEquiv.mul_apply,
        decompositionToLocalGaloisFun_apply, decompositionToLocalGaloisFun_apply]
      exact congrArg (fun f => f x)
        (map_mul (decompositionToAdicCompletion (K := K) w) σ τ) }

/-- **The action of the decomposition group on `L_w` is faithful.** -/
theorem decompositionToLocalGalois_injective
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    Function.Injective (decompositionToLocalGalois p w h) := by
  letI := adicCompletionAlgebra p w h
  intro σ τ hστ
  apply decompositionToAdicCompletion_injective (K := K) w
  have h' : (⇑(decompositionToLocalGaloisFun p w h σ) : w.adicCompletion L → w.adicCompletion L) =
      ⇑(decompositionToLocalGaloisFun p w h τ) :=
    congrArg (fun f : w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L =>
      (f : w.adicCompletion L → w.adicCompletion L)) hστ
  rw [decompositionToLocalGaloisFun_apply, decompositionToLocalGaloisFun_apply] at h'
  exact RingEquiv.ext (congrFun h')

/-- **The decomposition group is the local Galois group.**

For a finite Galois extension `L/K` of number fields and places `w | p`, the natural action of the
decomposition group `D_w` on the `w`-adic completion `L_w` is a group isomorphism
`D_w ≃* Gal(L_w / K_p)`. -/
noncomputable def decompositionSubgroupMulEquivLocalGalois
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    decompositionSubgroup (K := K) w ≃*
      (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L) :=
  letI := adicCompletionAlgebra p w h
  haveI : Module.Finite (p.adicCompletion K) (w.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p w h
  haveI : Finite (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L) := inferInstance
  MulEquiv.ofBijective (decompositionToLocalGalois p w h)
    (Function.Injective.bijective_of_nat_card_le (decompositionToLocalGalois_injective p w h) (by
      calc Nat.card (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L)
          ≤ Module.finrank (p.adicCompletion K) (w.adicCompletion L) :=
            natCard_localAlgEquiv_le_finrank p w h
        _ = p.asIdeal.ramificationIdxIn (𝓞 L) * p.asIdeal.inertiaDegIn (𝓞 L) :=
            finrank_adicCompletion_eq_ef' p w h
        _ = Nat.card (decompositionSubgroup (K := K) w) :=
            (card_decompositionSubgroup p w h).symm))

/-- **The order of the local Galois group is the local degree.** -/
theorem natCard_algEquiv_adicCompletion_eq_finrank
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    Nat.card (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L) =
      Module.finrank (p.adicCompletion K) (w.adicCompletion L) := by
  letI := adicCompletionAlgebra p w h
  haveI : Module.Finite (p.adicCompletion K) (w.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p w h
  have e : decompositionSubgroup (K := K) w ≃*
      (w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L) :=
    decompositionSubgroupMulEquivLocalGalois p w h
  rw [← Nat.card_congr e.toEquiv]
  rw [card_decompositionSubgroup p w h, finrank_adicCompletion_eq_ef' p w h]

/-- **The completion of a Galois extension of number fields at a place is Galois over the
completion of the base field.** -/
theorem isGalois_adicCompletion
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra p w h
    IsGalois (p.adicCompletion K) (w.adicCompletion L) := by
  letI := adicCompletionAlgebra p w h
  haveI : Module.Finite (p.adicCompletion K) (w.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p w h
  exact IsGalois.of_card_aut_eq_finrank (F := p.adicCompletion K) (E := w.adicCompletion L)
    (natCard_algEquiv_adicCompletion_eq_finrank p w h)

end localGalois

end Commons.NumberTheory.NumberField.Completion


namespace Commons.NumberTheory.NumberField.Completion

theorem natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg {K L : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  have h1 : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    natCard_algEquiv_adicCompletion_eq_finrank Q q hq
  have h2 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq
  rw [h1, ← h2]

end Commons.NumberTheory.NumberField.Completion

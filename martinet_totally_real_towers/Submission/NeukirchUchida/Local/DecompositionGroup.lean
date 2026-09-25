import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.FieldTheory.Galois.Infinite
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.liesOver_map_galRestrict
import Submission.NeukirchUchida.Local.ValuedCompletion

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

namespace Submission.NeukirchUchida.Local

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

end Submission.NeukirchUchida.Local

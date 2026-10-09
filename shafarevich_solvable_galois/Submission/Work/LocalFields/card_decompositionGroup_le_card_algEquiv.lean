import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer

namespace Work.LocalFields

open scoped NumberField Valued WithZero Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The decomposition group embeds into the local Galois group

For a finite Galois extension `L/K` of number fields, a finite prime `w` of `L` lying over the
finite prime `v` of `K`, and any `K_v`-algebra structure on `L_w` satisfying the scalar tower,
the decomposition group `D_w ≤ Gal(L/K)` acts on `L_w` by `K_v`-algebra automorphisms.

The action is constructed by extending `σ ∈ D_w` from the dense subfield `L ⊆ L_w` to the
completion; the extension exists because `σ` preserves the `w`-adic valuation
(`valuation_smul_of_mem_stabilizer`), hence is uniformly continuous for the `w`-adic uniformity.
The map `σ ↦ σ̂` is injective because `L` is dense in `L_w`, whence

`Nat.card D_w ≤ Nat.card (L_w ≃ₐ[K_v] L_w)`.
-/

section Extension

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The automorphism of `WithVal (w.valuation L)` induced by `τ : Gal(L/K)`, i.e. `τ` viewed as a
ring automorphism of the value-field associated to the `w`-adic valuation. -/
noncomputable def galWithVal (w : FinitePrime L) (τ : Gal(L/K)) :
    WithVal (w.valuation L) ≃+* WithVal (w.valuation L) :=
  WithVal.congr (w.valuation L) (w.valuation L) (MulSemiringAction.toRingEquiv Gal(L/K) L τ)

@[simp]
theorem galWithVal_apply (w : FinitePrime L) (τ : Gal(L/K)) (x : WithVal (w.valuation L)) :
    galWithVal w τ x = WithVal.toVal (w.valuation L) (τ • x.ofVal) :=
  WithVal.congr_apply _ _ _ _

theorem galWithVal_apply_inv (w : FinitePrime L) (τ : Gal(L/K)) (x : WithVal (w.valuation L)) :
    galWithVal w τ⁻¹ (galWithVal w τ x) = x := by
  rw [galWithVal_apply, galWithVal_apply]
  simp

theorem galWithVal_inv_apply (w : FinitePrime L) (τ : Gal(L/K)) (x : WithVal (w.valuation L)) :
    galWithVal w τ (galWithVal w τ⁻¹ x) = x := by
  rw [galWithVal_apply, galWithVal_apply]
  simp

/-- The `w`-adic valuation on `WithVal (w.valuation L)` is invariant under `galWithVal τ` for
`τ ∈ D_w`. -/
theorem galWithVal_valued (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) (x : WithVal (w.valuation L)) :
    Valued.v (galWithVal w τ x) = Valued.v x := by
  rw [galWithVal_apply, WithVal.valued_toVal]
  show w.valuation L (τ • x.ofVal) = Valued.v x
  rw [show τ • x.ofVal = τ x.ofVal from rfl,
    valuation_smul_of_mem_stabilizer w τ hτ x.ofVal]
  rfl

theorem restrict_galWithVal (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) (x : WithVal (w.valuation L)) :
    Valued.v.restrict (galWithVal w τ x) = Valued.v.restrict x := by
  apply MonoidWithZeroHom.ValueGroup₀.embedding_inj.mp
  simp only [Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
  exact galWithVal_valued w hτ x

/-- `galWithVal τ` is continuous (indeed an isometry) for the `w`-adic topology. -/
theorem continuous_galWithVal (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) :
    Continuous (galWithVal w τ : WithVal (w.valuation L) → WithVal (w.valuation L)) := by
  refine continuous_of_continuousAt_zero (galWithVal w τ) ?_
  rw [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero (WithVal (w.valuation L)) ℤᵐ⁰).tendsto_iff
      (Valued.hasBasis_nhds_zero (WithVal (w.valuation L)) ℤᵐ⁰)]
  intro γ _
  exact ⟨γ, trivial, fun x hx => by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rwa [restrict_galWithVal w hτ x]⟩

/-- The endomorphism of the completion `(L_w, w)` induced by `τ ∈ D_w`, as a continuous extension
of `galWithVal τ` from the dense subring `WithVal (w.valuation L)`. -/
noncomputable def localEnd (w : FinitePrime L) (τ : Gal(L/K))
    (hτ : τ ∈ decompositionGroup K w) :
    (w.valuation L).Completion →+* (w.valuation L).Completion :=
  UniformSpace.Completion.extensionHom
    ((UniformSpace.Completion.coeRingHom).comp (galWithVal w τ).toRingHom)
    ((UniformSpace.Completion.continuous_coeRingHom).comp (continuous_galWithVal w hτ))

theorem localEnd_coe (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) (c : WithVal (w.valuation L)) :
    localEnd w τ hτ (c : (w.valuation L).Completion) =
      (galWithVal w τ c : (w.valuation L).Completion) := by
  rw [localEnd, UniformSpace.Completion.extensionHom_coe]
  rfl

theorem continuous_localEnd (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) : Continuous (localEnd w τ hτ) :=
  UniformSpace.Completion.continuous_extension

theorem localEnd_comp_inv (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) (x : (w.valuation L).Completion) :
    localEnd w τ⁻¹ (inv_mem hτ) (localEnd w τ hτ x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((continuous_localEnd w (inv_mem hτ)).comp (continuous_localEnd w hτ)) continuous_id
  | ih c =>
    rw [localEnd_coe w hτ c, localEnd_coe w (inv_mem hτ) (galWithVal w τ c)]
    exact congrArg _ (galWithVal_apply_inv w τ c)

theorem localEnd_inv_comp (w : FinitePrime L) {τ : Gal(L/K)}
    (hτ : τ ∈ decompositionGroup K w) (x : (w.valuation L).Completion) :
    localEnd w τ hτ (localEnd w τ⁻¹ (inv_mem hτ) x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((continuous_localEnd w hτ).comp (continuous_localEnd w (inv_mem hτ))) continuous_id
  | ih c =>
    rw [localEnd_coe w (inv_mem hτ) c, localEnd_coe w hτ (galWithVal w τ⁻¹ c)]
    exact congrArg _ (galWithVal_inv_apply w τ c)

/-- The completion of `galWithVal τ` is a ring equivalence. -/
noncomputable def localEndEquiv (w : FinitePrime L) (τ : Gal(L/K))
    (hτ : τ ∈ decompositionGroup K w) :
    (w.valuation L).Completion ≃+* (w.valuation L).Completion where
  toFun := localEnd w τ hτ
  invFun := localEnd w τ⁻¹ (inv_mem hτ)
  left_inv := fun x => localEnd_comp_inv w hτ x
  right_inv := fun x => localEnd_inv_comp w hτ x
  map_mul' := (localEnd w τ hτ).map_mul
  map_add' := (localEnd w τ hτ).map_add

end Extension

section CompletionEnd

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The ring automorphism of the completion `L_w` induced by `τ ∈ D_w`. -/
noncomputable def localRingEquiv (w : FinitePrime L) (τ : Gal(L/K))
    (hτ : τ ∈ decompositionGroup K w) : Completion L w ≃+* Completion L w :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).trans
    ((localEndEquiv w τ hτ).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L w).symm)

theorem localRingEquiv_apply (w : FinitePrime L) (τ : Gal(L/K))
    (hτ : τ ∈ decompositionGroup K w) (x : Completion L w) :
    localRingEquiv w τ hτ x =
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
        (localEnd w τ hτ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion x)) := by
  simp only [localRingEquiv, RingEquiv.trans_apply]
  rfl

theorem continuous_localRingEquiv (w : FinitePrime L) (τ : Gal(L/K))
    (hτ : τ ∈ decompositionGroup K w) :
    Continuous (localRingEquiv w τ hτ : Completion L w → Completion L w) := by
  rw [show (localRingEquiv w τ hτ : Completion L w → Completion L w) =
      fun x => IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
        (localEnd w τ hτ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion x)) from
    funext (fun x => localRingEquiv_apply w τ hτ x)]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    ((continuous_localEnd w hτ).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion L w))

/-- `τ ∈ D_w` acts on the image of `L` in `L_w` as `τ` itself. -/
theorem localRingEquiv_algebraMap (w : FinitePrime L) (τ : Gal(L/K))
    (hτ : τ ∈ decompositionGroup K w) (x : L) :
    localRingEquiv w τ hτ (algebraMap L (Completion L w) x) =
      algebraMap L (Completion L w) (τ x) := by
  have hx : algebraMap L (Completion L w) x =
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
        (WithVal.toVal (w.valuation L) x : (w.valuation L).Completion)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  rw [hx, localRingEquiv_apply,
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion, localEnd_coe,
    galWithVal_apply]
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

end CompletionEnd

section LocalGalois

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal]
  [Algebra (Completion K v) (Completion L w)]
  [ContinuousSMul (Completion K v) (Completion L w)]
  [IsScalarTower K (Completion K v) (Completion L w)]

/-- The structural map `K_v → L_w` of the algebra structure is continuous; it is `a ↦ a • 1` and
the scalar multiplication is continuous by hypothesis. -/
theorem continuous_algebraMap_completion :
    Continuous (algebraMap (Completion K v) (Completion L w)) := by
  rw [Algebra.algebraMap_eq_smul_one']
  exact continuous_id.smul continuous_const

/-- The `K_v`-algebra automorphism of `L_w` induced by `τ ∈ D_w`. -/
noncomputable def localAlgEquiv (τ : Gal(L/K)) (hτ : τ ∈ decompositionGroup K w) :
    Completion L w ≃ₐ[Completion K v] Completion L w :=
  AlgEquiv.ofRingEquiv (f := localRingEquiv w τ hτ) (fun a => by
    have hcont_alg : Continuous (algebraMap (Completion K v) (Completion L w)) :=
      continuous_algebraMap_completion v w
    have hcontF : Continuous (fun a : Completion K v =>
        localRingEquiv w τ hτ (algebraMap (Completion K v) (Completion L w) a)) :=
      (continuous_localRingEquiv w τ hτ).comp hcont_alg
    have heq : (fun a : Completion K v =>
        localRingEquiv w τ hτ (algebraMap (Completion K v) (Completion L w) a))
        = algebraMap (Completion K v) (Completion L w) :=
      DenseRange.equalizer
        (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v)
        hcontF hcont_alg (funext (fun k => by
          simp only [Function.comp_apply]
          have h1 : algebraMap (Completion K v) (Completion L w)
                (algebraMap K (Completion K v) k) = algebraMap K (Completion L w) k :=
            (IsScalarTower.algebraMap_apply K (Completion K v) (Completion L w) k).symm
          have h2 : algebraMap K (Completion L w) k
              = algebraMap L (Completion L w) (algebraMap K L k) :=
            (IsScalarTower.algebraMap_apply K L (Completion L w) k).symm
          rw [h1, h2, localRingEquiv_algebraMap w τ hτ (algebraMap K L k),
            AlgEquiv.commutes τ k]))
    exact congrFun heq a)

end LocalGalois

/-- **The decomposition group injects into the local Galois group.**

Each `σ ∈ D_w` extends canonically to a `K_v`-algebra automorphism of `L_w`, and the resulting map
`D_w → (L_w ≃ₐ[K_v] L_w)` is injective (an automorphism of `L_w` trivial on the dense subfield
`L` is trivial).  Hence `#D_w ≤ #(L_w ≃ₐ[K_v] L_w)`. -/
theorem card_decompositionGroup_le_card_algEquiv {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Nat.card (Work.LocalFields.decompositionGroup K w) ≤
      Nat.card ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) := by
  have hinj : Function.Injective (fun s : decompositionGroup K w =>
      localAlgEquiv v w (s : Gal(L/K)) s.2) := by
    intro s t hst
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have h2 := congrArg (fun e : Completion L w ≃ₐ[Completion K v] Completion L w =>
        e (algebraMap L (Completion L w) x)) hst
    have h3 : algebraMap L (Completion L w) ((s : Gal(L/K)) x)
        = algebraMap L (Completion L w) ((t : Gal(L/K)) x) := by
      simp only [localAlgEquiv, AlgEquiv.ofRingEquiv_apply, localRingEquiv_algebraMap] at h2
      exact h2
    exact emb_injective h3
  exact Nat.card_le_card_of_injective _ hinj

end Work.LocalFields

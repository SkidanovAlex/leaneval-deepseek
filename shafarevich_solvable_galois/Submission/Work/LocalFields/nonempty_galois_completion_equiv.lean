/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The decomposition group is the local Galois group

For a finite Galois extension `L/K` of number fields, a finite prime `w` of `L` lying over the
finite prime `v` of `K`, this file proves

`(Completion L w ≃ₐ[Completion K v] Completion L w) ≃* decompositionGroup K w`,

i.e. the group of `K_v`-linear automorphisms of the completion `L_w` is the decomposition group
of `w`.  This is the `Work.LocalFields.DecompositionGroupIsLocalGaloisGroup` input.

## Main declarations

* `Work.LocalFields.completionRingHom` : the canonical ring homomorphism `K_v →+* L_w`.
* `Work.LocalFields.completionAlgebra` : the induced `K_v`-algebra structure on `L_w`, with
  `Work.LocalFields.completion_isScalarTower` and `Work.LocalFields.completion_continuousSMul`.
* `Work.LocalFields.nonempty_galois_completion_equiv` : the main theorem.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.LocalFieldAPI
import Submission.Work.LocalFields.Hensel
import Submission.Work.LocalFields.exists_pow_eq_of_one_sub_lt_one
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer
import Submission.Work.LocalFields.card_decompositionGroup_le_card_algEquiv
import Submission.Work.LocalFields.card_algEquiv_le_card_decompositionGroup
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.LocalFields.exists_algebra_completion
import Submission.Work.LocalFields.valuation_eq_one_of_val_eq_one
import Submission.Work.LocalFields.isEquiv_valued_of_unit_of_exists
import Submission.Work.LocalFields.nonempty_algEquiv_equiv_decompositionGroup

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

set_option linter.unusedSectionVars false

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]


/-! ## The main theorem

The canonical ring homomorphism `CompletionHom.ringHom v w : K_v →+* L_w` and the algebra
structure it induces are constructed above.  The remaining input is the classical theorem that
the decomposition group is the local Galois group,
`(L_w ≃ₐ[K_v] L_w) ≃* D_w`, together with the fact that *any* algebra structure satisfying the
scalar tower has the same image (`LocalFields/completion_algebra_range_eq`), so that the group
does not depend on the choice of structure. -/

namespace CompletionHom

variable (v : FinitePrime K) (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal]

open IsDedekindDomain.HeightOneSpectrum in
/-- The ring homomorphism `WithVal v →+* L_w` given by the composite of `K → L`, the inclusion
of `L` into its completion at `w` and the identification of `WithVal w` with `L`. -/
noncomputable def step1 : WithVal (v.valuation K) →+* Completion L w :=
  ((adicCompletion.equiv L w).symm : (w.valuation L).Completion →+* Completion L w).comp
    ((UniformSpace.Completion.coeRingHom :
        WithVal (w.valuation L) →+* (w.valuation L).Completion).comp
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))))

open IsDedekindDomain.HeightOneSpectrum in
lemma step1_continuous : Continuous (step1 v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp
    ((UniformSpace.Completion.continuous_coeRingHom).comp
      (IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
        (A := 𝓞 K) (B := 𝓞 L) (K := K) (L := L) v w).continuous)

open IsDedekindDomain.HeightOneSpectrum in
lemma step1_apply (x : WithVal (v.valuation K)) :
    step1 v w x = algebraMap K (Completion L w) x.ofVal := by
  rw [step1, RingHom.comp_apply, RingHom.comp_apply]
  rw [WithVal.algebraMap_left_apply]
  rw [WithVal.algebraMap_right_apply]
  rfl

open IsDedekindDomain.HeightOneSpectrum in
/-- **The canonical ring homomorphism `K_v →+* L_w`**, obtained by extending the uniformly
continuous map `K → L_w` to the completion `K_v` of `K`. -/
noncomputable def ringHom : Completion K v →+* Completion L w :=
  (UniformSpace.Completion.extensionHom (step1 v w) (step1_continuous v w)).comp
    (adicCompletion.equiv K v).toRingHom

open IsDedekindDomain.HeightOneSpectrum in
lemma ringHom_apply_coe (x : WithVal (v.valuation K)) :
    ringHom v w (adicCompletion.ofCompletion (x : (v.valuation K).Completion)) =
      step1 v w x := by
  show (UniformSpace.Completion.extensionHom (step1 v w) (step1_continuous v w))
      ((adicCompletion.equiv K v) (adicCompletion.ofCompletion (x : (v.valuation K).Completion))) = _
  rw [adicCompletion.equiv_apply, adicCompletion.toCompletion_ofCompletion]
  exact UniformSpace.Completion.extensionHom_coe _ _ x

open IsDedekindDomain.HeightOneSpectrum in
/-- The canonical map `K_v → L_w` extends the map `K → L_w`.  This is the compatibility
that makes `L_w` a `K_v`-algebra. -/
lemma ringHom_algebraMap (x : K) :
    ringHom v w (algebraMap K (Completion K v) x) = algebraMap K (Completion L w) x := by
  have h1 : algebraMap K (Completion K v) x =
      adicCompletion.ofCompletion (((WithVal.equiv (v.valuation K)).symm x : WithVal (v.valuation K))
        : (v.valuation K).Completion) := by
    rw [algebraMap_adicCompletion]
    rfl
  rw [h1, ringHom_apply_coe, step1_apply]
  simp

open IsDedekindDomain.HeightOneSpectrum in
lemma continuous_ringHom : Continuous (ringHom v w) := by
  rw [ringHom]
  exact (UniformSpace.Completion.continuous_extension).comp
    (adicCompletion.continuous_toCompletion K v)

open IsDedekindDomain.HeightOneSpectrum in
/-- The **canonical `K_v`-algebra structure** on `L_w`, induced by the canonical ring homomorphism
`K_v →+* L_w`. -/
noncomputable instance completionAlgebra : Algebra (Completion K v) (Completion L w) :=
  (ringHom v w).toAlgebra

open IsDedekindDomain.HeightOneSpectrum in
/-- The canonical algebra structure on `L_w` over `K_v` is compatible with `K ⊆ L`. -/
instance completionIsScalarTower : IsScalarTower K (Completion K v) (Completion L w) :=
  IsScalarTower.of_algebraMap_eq (fun x => (ringHom_algebraMap v w x).symm)

open IsDedekindDomain.HeightOneSpectrum in
/-- The scalar multiplication of `K_v` on `L_w` (through the canonical structure) is
continuous. -/
instance completionContinuousSMul : ContinuousSMul (Completion K v) (Completion L w) := by
  refine ContinuousSMul.mk ?_
  have h : (fun p : Completion K v × Completion L w => p.1 • p.2) =
      fun p => ringHom v w p.1 * p.2 := by
    funext p
    rw [Algebra.smul_def]
    rfl
  rw [h]
  exact ((continuous_ringHom v w).comp continuous_fst).mul continuous_snd

open IsDedekindDomain.HeightOneSpectrum in
/-- `L_w` is a finite-dimensional `K_v`-vector space (the local degree is finite). -/
instance completionModuleFinite : Module.Finite (Completion K v) (Completion L w) :=
  inferInstance

end CompletionHom


/-! ## Rigidity of the `K_v`-algebra structure on `L_w`

The main theorem is stated for an *arbitrary* `K_v`-algebra structure on `L_w` which is
compatible with the `K`-structure.  The point of this section is that such a structure is unique:
its structure map `K_v →+* L_w` is necessarily the canonical map `CompletionHom.ringHom v w`.
Consequently its scalar multiplication is continuous, and the theorem reduces to the
already-proved statement for the canonical structure. -/

open IsDedekindDomain.HeightOneSpectrum in
/-- **The structure map of a `K`-compatible ring homomorphism `K_v →+* L_w` is the canonical
one.**

Let `σ : K_v →+* L_w` be a ring homomorphism whose restriction to `K` is the canonical map
`K → L_w`.  Then `σ` agrees with the canonical continuous extension
`CompletionHom.ringHom v w` of that map.

Indeed, `ν := Valued.v ∘ σ` is a valuation on `K_v` which agrees with `Valued.v` on the units
(`valuation_eq_one_of_val_eq_one`) and is nontrivial on small elements (evaluate at the image of a
uniformizer of `v`), so `ν` is equivalent to `Valued.v` (`isEquiv_valued_of_unit_of_exists`).
Hence `σ` maps the unit ball `𝒪[K_v]` into `𝒪[L_w]` and, since `σ` is multiplicative and
`Valued.v (σ z) < 1` for a uniformizer `z` of `K_v`, `σ` is continuous.  As `σ` and
`CompletionHom.ringHom v w` are both continuous and agree on the dense subfield `K ⊆ K_v`, they
are equal. -/
theorem eq_ringHom_of_comp_eq (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    (σ : Completion K v →+* Completion L w)
    (hσ : σ.comp (algebraMap K (Completion K v)) = algebraMap K (Completion L w)) :
    σ = CompletionHom.ringHom v w := by
  set ν : Valuation (Completion K v) (WithZero (Multiplicative ℤ)) :=
    (Valued.v (R := Completion L w)).comap σ with hνdef
  have hν_apply : ∀ x : Completion K v, ν x = Valued.v (σ x) := fun x => by
    rw [hνdef]; exact Valuation.comap_apply σ (Valued.v (R := Completion L w)) x
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer' K v
  set z : Completion K v := algebraMap K (Completion K v) (π : K) with hzdef
  have hzval : Valued.v z = WithZero.exp (-1) := by
    rw [hzdef, algebraMap_adicCompletion]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply]
    rw [adicCompletion.valued_coe K v (π : K)]
    exact hπ
  have hz0 : z ≠ 0 := by
    intro h
    have h1 : Valued.v z = 0 := by rw [h, map_zero]
    rw [hzval] at h1
    exact WithZero.exp_ne_zero h1
  have hzlt : Valued.v z < 1 := by
    rw [hzval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hσz : σ z = algebraMap K (Completion L w) (π : K) := by
    rw [hzdef]
    exact RingHom.congr_fun hσ (π : K)
  have hνz : ν z < 1 := by
    rw [hν_apply, hσz]
    have h1 : Valued.v (algebraMap K (Completion L w) (π : K)) =
        w.valuation L (algebraMap K L (π : K)) := by
      rw [IsScalarTower.algebraMap_apply K L (Completion L w) (π : K)]
      rw [algebraMap_adicCompletion]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply]
      rw [adicCompletion.valued_coe L w]
    rw [h1]
    have heq := valuation_isEquiv_of_liesOver v w
    have hv1 : v.valuation K (π : K) < v.valuation K (1 : K) := by
      rw [map_one, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have h2 := (Valuation.IsEquiv.lt_iff_lt heq (x := (π : K)) (y := (1 : K))).mp hv1
    simpa [Valuation.comap_apply] using h2
  have hunit : ∀ x : Completion K v, Valued.v x = 1 → ν x = 1 :=
    fun x hx => valuation_eq_one_of_val_eq_one v ν hx
  have hequiv : ν.IsEquiv (Valued.v (R := Completion K v)) :=
    isEquiv_valued_of_unit_of_exists v ν hunit ⟨z, hz0, hzlt, hνz⟩
  have hcont : Continuous σ := by
    refine continuous_of_continuousAt_zero σ ?_
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro s hs
    rw [Valued.mem_nhds_zero] at hs
    obtain ⟨γ, hγ⟩ := hs
    rw [Valued.mem_nhds_zero]
    set G : WithZero (Multiplicative ℤ) :=
      MonoidWithZeroHom.ValueGroup₀.embedding (f := (Valued.v (R := Completion L w) : Completion L w →*₀ WithZero (Multiplicative ℤ))) (γ : MonoidWithZeroHom.ValueGroup₀
          ((Valued.v (R := Completion L w) : Completion L w →*₀ WithZero (Multiplicative ℤ)))) with hGdef
    have hG0 : G ≠ 0 := by
      rw [hGdef]
      intro h0
      exact Units.ne_zero γ (MonoidWithZeroHom.ValueGroup₀.embedding_injective
        (by rw [h0, map_zero]))
    have hA0 : ν z ≠ 0 := fun h => hz0 ((Valuation.zero_iff ν).mp h)
    have hA1 : WithZero.unzero hA0 < (1 : Multiplicative ℤ) := by
      rw [← WithZero.coe_lt_coe (a := WithZero.unzero hA0) (b := (1 : Multiplicative ℤ)),
        WithZero.coe_unzero hA0, WithZero.coe_one]
      exact hνz
    obtain ⟨N, hN⟩ := exists_pow_lt hA1 (WithZero.unzero hG0)
    have hN' : (ν z) ^ N < G := by
      rw [show (ν z) = ↑(WithZero.unzero hA0) from (WithZero.coe_unzero hA0).symm,
        show G = ↑(WithZero.unzero hG0) from (WithZero.coe_unzero hG0).symm,
        ← WithZero.coe_pow, WithZero.coe_lt_coe]
      exact hN
    refine ⟨Units.mk0 ((MonoidWithZeroHom.ValueGroup₀.restrict₀
        ((Valued.v (R := Completion K v) : Completion K v →*₀ WithZero (Multiplicative ℤ)))) (z ^ N)) ?_,
      fun x hx => ?_⟩
    · intro h
      have h2 : (MonoidWithZeroHom.ValueGroup₀.embedding (f := (Valued.v (R := Completion K v) : Completion K v →*₀ WithZero (Multiplicative ℤ))))
          ((MonoidWithZeroHom.ValueGroup₀.restrict₀ ((Valued.v (R := Completion K v) : Completion K v →*₀ WithZero (Multiplicative ℤ)))) (z ^ N)) = 0 := by
        rw [h, map_zero]
      rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀, map_pow] at h2
      have hzv : ((Valued.v (R := Completion K v) : Completion K v →*₀ WithZero (Multiplicative ℤ))) z ≠ 0 := by
        rw [show ((Valued.v (R := Completion K v) : Completion K v →*₀ WithZero (Multiplicative ℤ))) z = Valued.v z
          from rfl, hzval]
        exact WithZero.exp_ne_zero
      exact pow_ne_zero N hzv h2
    · rw [Set.mem_ofPred_eq] at hx
      apply hγ
      rw [Set.mem_ofPred_eq]
      rw [Valuation.restrict_lt_iff_lt_embedding]
      rw [← hGdef]
      rw [Valuation.restrict_lt_iff_lt_embedding] at hx
      rw [Units.val_mk0] at hx
      rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀] at hx
      try rw [MonoidWithZeroHom.coe_ofClass] at hx
      have hx₁ : ν x < ν (z ^ N) := (Valuation.IsEquiv.lt_iff_lt hequiv).mpr hx
      calc Valued.v (σ x) = ν x := (hν_apply x).symm
        _ < ν (z ^ N) := hx₁
        _ = (ν z) ^ N := map_pow ν z N
        _ < G := hN'
  exact RingHom.ext fun x => congrFun (DenseRange.equalizer (denseRange_algebraMap K v) hcont
    (CompletionHom.continuous_ringHom v w) (funext fun k => by
      rw [Function.comp_apply, Function.comp_apply]
      exact (RingHom.congr_fun hσ k).trans (CompletionHom.ringHom_algebraMap v w k).symm)) x

open IsDedekindDomain.HeightOneSpectrum in
theorem nonempty_galois_completion_equiv {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Nonempty (((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) ≃* Work.LocalFields.decompositionGroup K w) := by
  have hσ : (algebraMap (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)) =
      CompletionHom.ringHom v w :=
    eq_ringHom_of_comp_eq v w _ (IsScalarTower.algebraMap_eq K (Completion K v) (Completion L w)).symm
  have hcont : Continuous
      (algebraMap (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)) := by
    rw [hσ]
    exact CompletionHom.continuous_ringHom v w
  haveI : ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w) := by
    refine ContinuousSMul.mk ?_
    have h : (fun p : Completion K v × Completion L w => p.1 • p.2) =
        fun p => algebraMap (Completion K v) (Completion L w) p.1 * p.2 := by
      funext p
      rw [Algebra.smul_def]
    rw [h]
    exact (hcont.comp continuous_fst).mul continuous_snd
  exact nonempty_algEquiv_equiv_decompositionGroup v w

end Work.LocalFields

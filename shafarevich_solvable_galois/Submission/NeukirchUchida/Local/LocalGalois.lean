import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.Galois.natCard_algEquiv_le_finrank
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.NeukirchUchida.Local.DecompositionGroup

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

namespace Submission.NeukirchUchida.Local

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

end Submission.NeukirchUchida.Local

import Mathlib
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom

/-!
# The order of the local Galois group at an infinite place

Let `L / K` be an extension of number fields, `v` an infinite place of `K` and `w` an infinite
place of `L` lying over `v`.  The completion `L_w = w.Completion` is an algebra over
`K_v = v.Completion` (this is the content of `NumberField.LiesOver.completionMap`), and, since an
infinite place is either real or complex, this extension is one of `ℝ/ℝ`, `ℂ/ℝ` or `ℂ/ℂ`.

The main result of this file is

`Nat.card (L_w ≃ₐ[K_v] L_w) = Module.finrank K_v L_w`,

i.e. **the local Galois group at an infinite place has as many elements as the local degree**.
Equivalently (Neukirch–Schmidt–Wingberg, Chapter XII, the archimedean part of `(12.1.9)`): an
archimedean place is either unramified, with local group of order one, or ramified, with local
group of order two.

The proof transports the corresponding statement for the models `ℝ/ℝ`, `ℂ/ℝ` and `ℂ/ℂ` (where it
is `IsGalois.card_aut_eq_finrank`) along the canonical ring isomorphisms
`v.Completion ≃+* ℝ`/`v.Completion ≃+* ℂ` supplied by
`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` and
`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped NumberField.LiesOver

namespace NK.GlobalCFTdeep.Herbrand

open NumberField NumberField.InfinitePlace

/-! ## Transporting the order of a group of algebra automorphisms

We first record the general transport statement: an isomorphism of `R`-algebras `S` with
`R'`-algebras `S'`, given as a compatible pair of ring isomorphisms `R ≃+* R'`, `S ≃+* S'`,
induces a bijection on `R`- resp. `R'`-algebra automorphisms, hence an equality of cardinalities.
The corresponding statement for the dimension is `Algebra.finrank_eq_of_equiv_equiv`. -/

/-- A compatible pair of ring isomorphisms `i : R ≃+* R'`, `j : S ≃+* S'` induces a bijection
between the `R`-algebra automorphisms of `S` and the `R'`-algebra automorphisms of `S'`. -/
theorem natCard_algEquiv_eq_of_ringEquiv {R S R' S' : Type*}
    [CommSemiring R] [Semiring S] [Algebra R S]
    [CommSemiring R'] [Semiring S'] [Algebra R' S']
    (i : R ≃+* R') (j : S ≃+* S')
    (hc : ∀ x : R, j (algebraMap R S x) = algebraMap R' S' (i x)) :
    Nat.card (S ≃ₐ[R] S) = Nat.card (S' ≃ₐ[R'] S') := by
  have key1 : ∀ r : R', j (algebraMap R S (i.symm r)) = algebraMap R' S' r := by
    intro r; rw [hc (i.symm r), i.apply_symm_apply]
  have key2 : ∀ r : R', j.symm (algebraMap R' S' r) = algebraMap R S (i.symm r) := by
    intro r; rw [← key1 r, RingEquiv.symm_apply_apply]
  refine Nat.card_congr ?_
  refine
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := j.symm.trans (σ.toRingEquiv.trans j)) (fun r => ?_)
      invFun := fun τ => AlgEquiv.ofRingEquiv (f := j.trans (τ.toRingEquiv.trans j.symm)) (fun r => ?_)
      left_inv := fun σ => ?_
      right_inv := fun τ => ?_ }
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, key2 r]
    change j (σ (algebraMap R S (i.symm r))) = algebraMap R' S' r
    rw [σ.commutes (i.symm r), key1 r]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
    change j.symm (τ (j (algebraMap R S r))) = algebraMap R S r
    rw [hc r, τ.commutes (i r), key2 (i r), i.symm_apply_apply]
  · ext x
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply]
    simp
  · ext x
    simp only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply]
    simp

/-! ## The main statement -/

/-- **The archimedean local Galois group has order the local degree.**  For an extension of number
fields `L/K`, an infinite place `w` of `L` lying over the infinite place `v` of `K`, the group of
`v.Completion`-algebra automorphisms of `w.Completion` has as many elements as the dimension
`[w.Completion : v.Completion]` (which is `1` or `2`). -/
theorem natCard_algEquiv_completion_eq_finrank {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [hw : w.LiesOver v] :
    Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion)
      = Module.finrank v.Completion w.Completion := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · rcases InfinitePlace.isReal_or_isComplex w with hwR | hwC
    · -- `v` and `w` are both real: the model is `ℝ/ℝ`.
      have hLies := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
      have hcomp : ∀ x : v.Completion,
          Completion.extensionEmbedding w (algebraMap v.Completion w.Completion x)
            = Completion.extensionEmbedding v x := fun x => RingHom.congr_fun hLies.over x
      have hc : ∀ x : v.Completion, (Completion.ringEquivRealOfIsReal hwR)
          (algebraMap v.Completion w.Completion x)
          = algebraMap ℝ ℝ ((Completion.ringEquivRealOfIsReal hv) x) := by
        intro x
        apply Complex.ofReal_injective
        rw [show algebraMap ℝ ℝ ((Completion.ringEquivRealOfIsReal hv) x)
              = (Completion.ringEquivRealOfIsReal hv) x from rfl]
        rw [Completion.ringEquivRealOfIsReal_apply, Completion.ringEquivRealOfIsReal_apply,
          Completion.extensionEmbeddingOfIsReal_apply, Completion.extensionEmbeddingOfIsReal_apply,
          hcomp x]
      rw [natCard_algEquiv_eq_of_ringEquiv (Completion.ringEquivRealOfIsReal hv)
          (Completion.ringEquivRealOfIsReal hwR) hc,
        Algebra.finrank_eq_of_equiv_equiv (Completion.ringEquivRealOfIsReal hv)
          (Completion.ringEquivRealOfIsReal hwR) (RingHom.ext fun x => (hc x).symm)]
      exact IsGalois.card_aut_eq_finrank ℝ ℝ
    · -- `v` is real and `w` is complex: the model is `ℂ/ℝ`.
      have hLies := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
      have hcomp : ∀ x : v.Completion,
          Completion.extensionEmbedding w (algebraMap v.Completion w.Completion x)
            = Completion.extensionEmbedding v x := fun x => RingHom.congr_fun hLies.over x
      haveI : IsGalois ℝ ℂ := isGalois_iff.mpr ⟨inferInstance,
        { Algebra.IsAlgebraic.of_finite ℝ ℂ with splits' := fun _ => IsAlgClosed.splits _ }⟩
      have hc : ∀ x : v.Completion, (Completion.ringEquivComplexOfIsComplex hwC)
          (algebraMap v.Completion w.Completion x)
          = algebraMap ℝ ℂ ((Completion.ringEquivRealOfIsReal hv) x) := by
        intro x
        rw [Completion.ringEquivComplexOfIsComplex_apply, hcomp x,
          ← Completion.extensionEmbeddingOfIsReal_apply hv x,
          ← Completion.ringEquivRealOfIsReal_apply hv x]
        rfl
      rw [natCard_algEquiv_eq_of_ringEquiv (Completion.ringEquivRealOfIsReal hv)
          (Completion.ringEquivComplexOfIsComplex hwC) hc,
        Algebra.finrank_eq_of_equiv_equiv (Completion.ringEquivRealOfIsReal hv)
          (Completion.ringEquivComplexOfIsComplex hwC) (RingHom.ext fun x => (hc x).symm)]
      exact IsGalois.card_aut_eq_finrank ℝ ℂ
  · -- `v` is complex, hence so is `w`: the model is `ℂ/ℂ`.
    have hwC : w.IsComplex := LiesOver.isComplex_of_isComplex_under w hv
    rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
    · -- `w.embedding` itself lies over `v.embedding`.
      have hLies : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨h⟩
      have hlies := Completion.liesOver_extensionEmbedding w v
      have hcomp : ∀ x : v.Completion,
          Completion.extensionEmbedding w (algebraMap v.Completion w.Completion x)
            = Completion.extensionEmbedding v x := fun x => RingHom.congr_fun hlies.over x
      have hc : ∀ x : v.Completion, (Completion.ringEquivComplexOfIsComplex hwC)
          (algebraMap v.Completion w.Completion x)
          = algebraMap ℂ ℂ ((Completion.ringEquivComplexOfIsComplex hv) x) := by
        intro x
        rw [Completion.ringEquivComplexOfIsComplex_apply, hcomp x,
          ← Completion.ringEquivComplexOfIsComplex_apply hv x]
        rfl
      rw [natCard_algEquiv_eq_of_ringEquiv (Completion.ringEquivComplexOfIsComplex hv)
          (Completion.ringEquivComplexOfIsComplex hwC) hc,
        Algebra.finrank_eq_of_equiv_equiv (Completion.ringEquivComplexOfIsComplex hv)
          (Completion.ringEquivComplexOfIsComplex hwC) (RingHom.ext fun x => (hc x).symm)]
      exact IsGalois.card_aut_eq_finrank ℂ ℂ
    · -- `conjugate w.embedding` lies over `v.embedding`; the identification of `w.Completion` with
      -- `ℂ` is then the conjugate one.
      have hLies : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w.embedding)
          v.embedding := ⟨h⟩
      have hlies := Completion.liesOver_conjugate_extensionEmbedding w v
      have hcomp : ∀ x : v.Completion,
          ComplexEmbedding.conjugate (Completion.extensionEmbedding w)
            (algebraMap v.Completion w.Completion x)
            = Completion.extensionEmbedding v x := fun x => RingHom.congr_fun hlies.over x
      have hj : ∀ y : ℂ, Complex.conjAe.toRingEquiv y = starRingEnd ℂ y := fun _ => rfl
      have hc : ∀ x : v.Completion,
          ((Completion.ringEquivComplexOfIsComplex hwC).trans Complex.conjAe.toRingEquiv)
          (algebraMap v.Completion w.Completion x)
          = algebraMap ℂ ℂ ((Completion.ringEquivComplexOfIsComplex hv) x) := by
        intro x
        rw [RingEquiv.trans_apply, Completion.ringEquivComplexOfIsComplex_apply, hj,
          ← ComplexEmbedding.conjugate_coe_eq, hcomp x,
          ← Completion.ringEquivComplexOfIsComplex_apply hv x]
        rfl
      rw [natCard_algEquiv_eq_of_ringEquiv (Completion.ringEquivComplexOfIsComplex hv)
          ((Completion.ringEquivComplexOfIsComplex hwC).trans Complex.conjAe.toRingEquiv) hc,
        Algebra.finrank_eq_of_equiv_equiv (Completion.ringEquivComplexOfIsComplex hv)
          ((Completion.ringEquivComplexOfIsComplex hwC).trans Complex.conjAe.toRingEquiv)
          (RingHom.ext fun x => (hc x).symm)]
      exact IsGalois.card_aut_eq_finrank ℂ ℂ

end NK.GlobalCFTdeep.Herbrand

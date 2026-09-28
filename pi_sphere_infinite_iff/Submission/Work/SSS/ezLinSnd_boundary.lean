import Mathlib
import Submission.Work.SSS.ezGen_snd_sum_zero
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSS.iotaF_chainMap

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

/-! ## Auxiliary rewrites for the linearised Eilenberg–Zilber boundary formula

The proof of `Work.SSS.ezLinSnd_boundary` evaluates the two sides of the identity on the
generators `ι_τ` of the `(q+1)`-chains of `Y`.  The following four small lemmas perform that
evaluation: on a generator, `ezLinSnd n q X Y σ` becomes the shuffle chain `ezGen n q X Y σ τ`,
and the differential `d` of `Y` becomes the alternating sum of its faces. -/

/-- On the generators of the chain complex, `ezLinSnd` is the Eilenberg–Zilber shuffle chain,
spelled with `eltHom`: the two are the same morphism up to unfolding `eltHom`. -/
lemma ezLinSnd_ι_eltHom (n q : ℕ) (X Y : SSet) (σ : X _⦋n⦌) (τ : Y _⦋q⦌) :
    Y.ιChainComplex (R := ezR) τ ≫ ezLinSnd n q X Y σ
      = eltHom (Work.Cohomology.Crux33.ezGen n q X Y σ τ) :=
  ezLinSnd_ι n q X Y σ τ

/-- `eltHom` is additive, hence takes sums of elements to sums of morphisms. -/
lemma eltHom_add {M : ModuleCat ℤ} (a b : M) : eltHom a + eltHom b = eltHom (a + b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_add, ModuleCat.hom_ofHom, eltHom, LinearMap.toSpanSingleton_apply_one,
    LinearMap.add_apply]

/-- Evaluating a composite `ι_τ ≫ (ezLinSnd n q X Y σ ≫ f)` on the generator `1`: the source
`ι_τ` turns `ezLinSnd` into the shuffle chain, and `eltHom (−)` records postcomposition with
`f`. -/
lemma ι_comp_ezLinSnd_comp (n q : ℕ) (X Y : SSet) (σ : X _⦋n⦌) (τ : Y _⦋q⦌)
    {M : ModuleCat ℤ} (f : ((X ⊗ Y).chainComplex ezR).X (n + q) ⟶ M) :
    Y.ιChainComplex (R := ezR) τ ≫ (ezLinSnd n q X Y σ ≫ f)
      = eltHom (f (Work.Cohomology.Crux33.ezGen n q X Y σ τ)) := by
  rw [← Category.assoc, ezLinSnd_ι_eltHom, eltHom_comp]

/-- Evaluating `ι_τ ≫ (d_Y ≫ f)` on the generator `1`: the differential of `Y` sends `ι_τ` to the
alternating sum of the generators of the faces of `τ`. -/
lemma ι_comp_d_comp (q : ℕ) (Y : SSet) (τ : Y _⦋q+1⦌)
    {M : ModuleCat ℤ} (f : (Y.chainComplex ezR).X q ⟶ M) :
    Y.ιChainComplex (R := ezR) τ ≫ ((Y.chainComplex ezR).d (q+1) q ≫ f)
      = ∑ j : Fin (q+2), (-1:ℤ)^(j:ℕ) • (Y.ιChainComplex (R := ezR) (Y.δ j τ) ≫ f) := by
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  exact Finset.sum_congr rfl (fun j _ => by rw [Preadditive.zsmul_comp])

/-- **The Eilenberg–Zilber boundary formula on a single pair of simplices, in the bidegree
`(n+1) + q`.**  This is `Work.SSS.ezGen_boundary_succ` together with the `Sh23`-reindexing
`Work.KunnethEZ.ez23_eq_ezGen` (for the `X`-face terms) and `Work.SSS.yChain_eq_ezGen` (for the
`Y`-face terms), with the degree transport `n + (q+1) = (n+1) + q` made explicit. -/
lemma ezGen_boundary_target (n q : ℕ) (X Y : SSet) (σ : X _⦋n+1⦌) (τ : Y _⦋q+1⦌) :
    (((X ⊗ Y).chainComplex ezR).d ((n+1)+(q+1)) ((n+1)+q)).hom
        (Work.Cohomology.Crux33.ezGen (n+1) (q+1) X Y σ τ)
      = (∑ i : Fin (n+2), (-1 : ℤ)^((i:ℕ)) •
            ((eqToHom (congrArg (fun k : ℕ => ((X ⊗ Y).chainComplex ezR).X k)
              (by omega : n + (q+1) = (n+1) + q))).hom
              (Work.Cohomology.Crux33.ezGen n (q+1) X Y (X.δ i σ) τ)))
        + (-1 : ℤ)^(n+1) • (∑ j : Fin (q+2), (-1 : ℤ)^((j:ℕ)) •
              Work.Cohomology.Crux33.ezGen (n+1) q X Y σ (Y.δ j τ)) := by
  rw [show (((X ⊗ Y).chainComplex ezR).d ((n+1)+(q+1)) ((n+1)+q)).hom
        (Work.Cohomology.Crux33.ezGen (n+1) (q+1) X Y σ τ)
      = xChain n q X Y σ τ + ((-1:ℤ)^(n+1)) • yChain (n+1) q X Y σ τ
      from ezGen_boundary_succ n q X Y σ τ]
  simp only [xChain, yChain_eq_ezGen]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  congr 1
  exact Work.KunnethEZ.ez23_eq_ezGen (n+1) (q+1) (by omega) X Y (by omega) (X.δ i σ) τ

/-- **The Eilenberg–Zilber boundary formula, linearised in the second variable.**  For a simplex
`σ : X _⦋n+1⦌` and an arbitrary CHAIN `z` of `Y` in degree `q+1` (no cyclicity hypothesis — this
is what makes the statement usable, cf. `REFS/NOTES_SESSION5.md`), the boundary of the shuffle
chain `ezLinSnd (n+1) (q+1) X Y σ z` is the sum of the `X`-faces of `σ` (with the same `z`) and
the `Y`-face term with `∂z`.  This linearises `Work.SSS.ezGen_boundary_succ` together with
`Work.SSS.yChain_eq_ezGen` and the `Sh23`-reindexing `Work.KunnethEZ.ez23_eq_ezGen`. -/
theorem ezLinSnd_boundary (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n+1⦌) :
    Work.SSS.ezLinSnd (n+1) (q+1) X Y σ ≫
        ((X ⊗ Y).chainComplex Work.SSS.ezR).d ((n+1)+(q+1)) ((n+1)+q)
      = (∑ i : Fin (n+2), (-1 : ℤ)^((i : ℕ)) •
            (Work.SSS.ezLinSnd n (q+1) X Y (X.δ i σ) ≫
              eqToHom (congrArg (fun k : ℕ => ((X ⊗ Y).chainComplex Work.SSS.ezR).X k)
                (by omega : n + (q+1) = (n+1) + q))))
        + (-1 : ℤ)^(n+1) •
            (((Y.chainComplex Work.SSS.ezR).d (q+1) q) ≫ Work.SSS.ezLinSnd (n+1) q X Y σ) := by
  apply SSet.chainComplex_hom_ext
  intro τ
  -- The two sides are evaluated on the generator `ι_τ`; by the colimit property of the
  -- `(q+1)`-chains of `Y` it suffices to compare these evaluations.
  have hA : ((((X ⊗ Y).chainComplex ezR).d ((n+1)+(q+1)) ((n+1)+q))
        (Work.Cohomology.Crux33.ezGen (n+1) (q+1) X Y σ τ))
      = (∑ i : Fin (n+2), (-1 : ℤ)^((i:ℕ)) •
            ((eqToHom (congrArg (fun k : ℕ => ((X ⊗ Y).chainComplex ezR).X k)
              (by omega : n + (q+1) = (n+1) + q))).hom
              (Work.Cohomology.Crux33.ezGen n (q+1) X Y (X.δ i σ) τ)))
        + (-1 : ℤ)^(n+1) • (∑ j : Fin (q+2), (-1 : ℤ)^((j:ℕ)) •
              Work.Cohomology.Crux33.ezGen (n+1) q X Y σ (Y.δ j τ)) :=
    ezGen_boundary_target n q X Y σ τ
  have hL : Y.ιChainComplex (R := ezR) τ ≫
        (ezLinSnd (n+1) (q+1) X Y σ ≫
          ((X ⊗ Y).chainComplex ezR).d ((n+1)+(q+1)) ((n+1)+q))
      = eltHom ((((X ⊗ Y).chainComplex ezR).d ((n+1)+(q+1)) ((n+1)+q))
          (Work.Cohomology.Crux33.ezGen (n+1) (q+1) X Y σ τ)) :=
    ι_comp_ezLinSnd_comp (n+1) (q+1) X Y σ τ _
  have hR : Y.ιChainComplex (R := ezR) τ ≫
        ((∑ i : Fin (n+2), (-1 : ℤ)^((i : ℕ)) •
              (ezLinSnd n (q+1) X Y (X.δ i σ) ≫
                eqToHom (congrArg (fun k : ℕ => ((X ⊗ Y).chainComplex ezR).X k)
                  (by omega : n + (q+1) = (n+1) + q))))
          + (-1 : ℤ)^(n+1) •
              (((Y.chainComplex ezR).d (q+1) q) ≫ ezLinSnd (n+1) q X Y σ))
      = eltHom ((((X ⊗ Y).chainComplex ezR).d ((n+1)+(q+1)) ((n+1)+q))
          (Work.Cohomology.Crux33.ezGen (n+1) (q+1) X Y σ τ)) := by
    rw [Preadditive.comp_add]
    have hS : Y.ιChainComplex (R := ezR) τ ≫
          (∑ i : Fin (n+2), (-1 : ℤ)^((i : ℕ)) •
              (ezLinSnd n (q+1) X Y (X.δ i σ) ≫
                eqToHom (congrArg (fun k : ℕ => ((X ⊗ Y).chainComplex ezR).X k)
                  (by omega : n + (q+1) = (n+1) + q))))
        = ∑ i : Fin (n+2), (-1 : ℤ)^((i : ℕ)) •
              eltHom ((eqToHom (congrArg (fun k : ℕ => ((X ⊗ Y).chainComplex ezR).X k)
                  (by omega : n + (q+1) = (n+1) + q)))
                (Work.Cohomology.Crux33.ezGen n (q+1) X Y (X.δ i σ) τ)) := by
      rw [Preadditive.comp_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Preadditive.comp_zsmul, ι_comp_ezLinSnd_comp]
    have hT : Y.ιChainComplex (R := ezR) τ ≫
          ((-1 : ℤ)^(n+1) • (((Y.chainComplex ezR).d (q+1) q) ≫ ezLinSnd (n+1) q X Y σ))
        = (-1 : ℤ)^(n+1) • (∑ j : Fin (q+2), (-1 : ℤ)^((j:ℕ)) •
              eltHom (Work.Cohomology.Crux33.ezGen (n+1) q X Y σ (Y.δ j τ))) := by
      rw [Preadditive.comp_zsmul, ι_comp_d_comp]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [ezLinSnd_ι_eltHom]
    rw [hS, hT]
    rw [eltHom_sum, eltHom_sum, eltHom_zsmul, eltHom_add]
    rw [hA]
  rw [hL, hR]

end Work.SSS

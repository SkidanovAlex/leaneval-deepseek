import Mathlib
import Submission.Work.Cohomology.Crux33.EzGen
import Submission.Work.Cohomology.Crux33.ShuffleIndex
import Submission.Work.Cohomology.Crux33.EzGenAux

/-!
# The Eilenberg–Zilber shuffle chain of two cycles is a cycle

This file proves `Work.Cohomology.Crux33.ezGen_isCycle`: for `3`-simplices `σ` of `X` and `τ` of
`Y` with vanishing boundary, the Eilenberg–Zilber shuffle chain `ezC X Y σ τ` (the alternating sum
over the twenty `(3,3)`-shuffles of the corresponding `6`-simplices of `X ⊗ Y`) is a cycle.

The proof has two halves:

* the *chain-map* half: `∂ (ezC X Y σ τ)` is expanded with `SSet.ιChainComplex_d` into the `140`
  faces of the twenty shuffle cells, reindexed by `Work.Cohomology.Crux33.ezIdxL`/`ezCoefL`, and
  rewritten with the finite shuffle identity `Work.Cohomology.Crux33.ezLfun_eq_ezRfun` into the
  `80` faces of the two boundary shuffle chains `ezGen(2,3)(δ_i σ, τ)` and `ezGen(3,2)(σ, δ_i τ)`
  (this is the prism cancellation);
* the *linearity* half: those boundary sums are the values of the linear extensions
  `ezLin23`, `ezLin32` of the shuffles on the boundaries `∂σ`, `∂τ`, which vanish by hypothesis.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Crux33

noncomputable section

/-- The coefficient ring, pinned. -/
abbrev ezR : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The generator of the `5`-chains attached to a `5`-simplex. -/
abbrev gen5 (Z : SSet) (z : Z _⦋5⦌) : Cn Z 5 := (Z.ιChainComplex (R := ezR) z).hom 1

/-- The generator of the `6`-chains attached to a `6`-simplex. -/
abbrev gen6 (Z : SSet) (z : Z _⦋6⦌) : Cn Z 6 := (Z.ιChainComplex (R := ezR) z).hom 1

/-- The generic summand `gen5 (X ⊗ Y) (σ ∘ a, τ ∘ b)` of the shuffle computations. -/
def ezG (X Y : SSet) (σ : S3 X) (τ : S3 Y) (p : EzIdx) : Tn X Y 5 :=
  gen5 (X ⊗ Y) (X.map p.1.op σ, Y.map p.2.op τ)

/-- The face maps of the tensor product of two simplicial sets act componentwise. -/
lemma tensor_delta (X Y : SSet) (j : Fin 7) (x : X _⦋6⦌) (y : Y _⦋6⦌) :
    (X ⊗ Y).δ j (x, y) = (X.δ j x, Y.δ j y) := rfl

/-- A face of a simplex which has been pulled back along a monotone map. -/
lemma map_delta (X : SSet) (j : Fin 7) (a : ⦋6⦌ ⟶ ⦋3⦌) (x : X _⦋3⦌) :
    X.δ j (X.map a.op x) = X.map (SimplexCategory.δ j ≫ a).op x := by
  unfold SimplicialObject.δ
  rw [← Functor.map_comp_apply, ← op_comp]

/-- The case `p = 2` of `map_delta`. -/
lemma delta_map (X : SSet) (j : Fin 4) (a : ⦋5⦌ ⟶ ⦋2⦌) (x : X _⦋3⦌) :
    X.map a.op (X.δ j x) = X.map (a ≫ SimplexCategory.δ j).op x := by
  unfold SimplicialObject.δ
  rw [← Functor.map_comp_apply, ← op_comp]

/-- The boundary of the generator attached to a `6`-simplex. -/
lemma d65_apply_gen6 (Z : SSet) (z : Z _⦋6⦌) :
    (((Z.chainComplex ezR).d 6 5).hom) (gen6 Z z)
      = ∑ j : Fin 7, ((-1 : ℤ) ^ (j : ℕ)) • gen5 Z (Z.δ j z) := by
  have h2 := congrArg (fun (f : ezR ⟶ (Z.chainComplex ezR).X 5) => f.hom (1 : ℤ))
    (SSet.ιChainComplex_d Z ezR (n := 5) z)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.comp_apply] at h2
  exact h2

/-- The linear extension of the `(2,3)`-shuffle, in its first variable. -/
def ezLin23 (X Y : SSet) (τ : S3 Y) :
    (X.chainComplex ezR).X 2 ⟶ ((X ⊗ Y).chainComplex ezR).X 5 :=
  (X.isColimitChainComplexXCofan ezR 2).desc
    (Cofan.mk (((X ⊗ Y).chainComplex ezR).X 5)
      (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(((X ⊗ Y).chainComplex ezR).X 5)
        (ezGen 2 3 X Y x τ))))

theorem ezLin23_ι (X Y : SSet) (τ : S3 Y) (x : X _⦋2⦌) :
    (X.ιChainComplex (R := ezR) x) ≫ ezLin23 X Y τ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(((X ⊗ Y).chainComplex ezR).X 5)
        (ezGen 2 3 X Y x τ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `ezLin23` on a generator. -/
lemma ezLin23_apply (X Y : SSet) (τ : S3 Y) (x : X _⦋2⦌) :
    (ezLin23 X Y τ).hom ((X.ιChainComplex (R := ezR) x).hom 1) = ezGen 2 3 X Y x τ := by
  have h2 := congrArg (fun (f : ezR ⟶ ((X ⊗ Y).chainComplex ezR).X 5) => f.hom (1 : ℤ))
    (ezLin23_ι X Y τ x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The linear extension of the `(3,2)`-shuffle, in its second variable. -/
def ezLin32 (X Y : SSet) (σ : S3 X) :
    (Y.chainComplex ezR).X 2 ⟶ ((X ⊗ Y).chainComplex ezR).X 5 :=
  (Y.isColimitChainComplexXCofan ezR 2).desc
    (Cofan.mk (((X ⊗ Y).chainComplex ezR).X 5)
      (fun y => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(((X ⊗ Y).chainComplex ezR).X 5)
        (ezGen 3 2 X Y σ y))))

theorem ezLin32_ι (X Y : SSet) (σ : S3 X) (y : Y _⦋2⦌) :
    (Y.ιChainComplex (R := ezR) y) ≫ ezLin32 X Y σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(((X ⊗ Y).chainComplex ezR).X 5)
        (ezGen 3 2 X Y σ y)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `ezLin32` on a generator. -/
lemma ezLin32_apply (X Y : SSet) (σ : S3 X) (y : Y _⦋2⦌) :
    (ezLin32 X Y σ).hom ((Y.ιChainComplex (R := ezR) y).hom 1) = ezGen 3 2 X Y σ y := by
  have h2 := congrArg (fun (f : ezR ⟶ ((X ⊗ Y).chainComplex ezR).X 5) => f.hom (1 : ℤ))
    (ezLin32_ι X Y σ y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- **The Eilenberg–Zilber shuffle chain of two cycle simplices is a cycle** (`p = q = 3`).

`ezC X Y σ τ` is the Eilenberg–Zilber shuffle chain in the tensor product `X ⊗ Y` of simplicial
sets: the sum over the twenty `(3,3)`-shuffles `S` of `shufSign S • (σ ∘ a_S, τ ∘ b_S)`, with the
shuffle combinatorics of `Work.Cohomology.Crux33.ShuffleIndex` (the sign is
`shufSign S = (-1)^{#(N-steps before E-steps)}`, computed by `invCount`) and the pinned spellings
`S3`, `Cn`, `d32`, `d65`, `gen3`, `Tn`, `ezC`, `Td65` of `Work.Cohomology.Crux33.EzGen`.

Claim (the prism/cancellation property in the only case needed by the chain-level cup-product
witness): if the cyclic simplices `σ`, `τ` have vanishing boundary (`∂σ = 0`, `∂τ = 0` in the chain
complex, i.e. `d32 X (gen3 X σ) = 0`), then `∂ (ezC X Y σ τ) = 0`.

Equivalently the chain-map property `∂ ∘ ezGen = ezGen ∘ (∂ ⊗ 1) + ezGen ∘ (1 ⊗ ∂)`; for cycles the
right hand side vanishes, so the `(2,3)`- and `(3,2)`-shuffle chains need not be materialised.

Proof shape: expand `∂` of the twenty generators with `SSet.ιChainComplex_d`; each face is
`(σ ∘ (a_S ∘ δ_j), τ ∘ (b_S ∘ δ_j))`, so group the resulting `5`-simplices of `X ⊗ Y` by the pair of
monotone maps `(a_S ∘ δ_j, b_S ∘ δ_j)` (distinct pairs give distinct simplices, since the two
projections recover them) and show each total coefficient vanishes using `∂σ = 0`, `∂τ = 0`.  The
finite content is the `20 × 7` term computation over the shuffle data.  Sanity checks that fix the
sign convention and should be used while proving: for the one-point simplicial set the statement is
equivalent to `∑_{S} shufSign S = 0` (the Gaussian binomial at `-1`), and the good shuffle
`E E E N N N` (`S = {3,4,5}`) has `shufSign = +1`. -/
theorem ezGen_isCycle (X Y : SSet) (σ : Work.Cohomology.Crux33.S3 X)
    (τ : Work.Cohomology.Crux33.S3 Y)
    (hσ : Work.Cohomology.Crux33.d32 X (Work.Cohomology.Crux33.gen3 X σ) = 0)
    (hτ : Work.Cohomology.Crux33.d32 Y (Work.Cohomology.Crux33.gen3 Y τ) = 0) :
    Work.Cohomology.Crux33.Td65 X Y (Work.Cohomology.Crux33.ezC X Y σ τ) = 0 := by
  have h1 : Td65 X Y (ezC X Y σ τ) = ∑ t : EzTL, ezCoefL t • ezG X Y σ τ (ezIdxL t) := by
    rw [ezC, ezGen, map_sum]
    rw [Fintype.sum_prod_type (f := fun t : EzTL => ezCoefL t • ezG X Y σ τ (ezIdxL t))]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_zsmul, d65_apply_gen6, ← Finset.sum_zsmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ezCoefL, mul_smul]
    congr 1
    rw [tensor_delta, map_delta X j (aHom (p := 3) (q := 3) S.1 S.2) σ,
      map_delta Y j (bHom (p := 3) (q := 3) S.1 S.2) τ]
    simp only [ezG, ezIdxL]
  have h2 : (∑ t : EzTL, ezCoefL t • ezG X Y σ τ (ezIdxL t))
      = ∑ y ∈ ezSupp, ezLfun y • ezG X Y σ τ y := by
    simpa only [ezLfun] using (ezSum_reindex ezIdxL ezCoefL (ezG X Y σ τ) ezSupp
      (fun t => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
  have h3 : (∑ y ∈ ezSupp, ezLfun y • ezG X Y σ τ y)
      = ∑ y ∈ ezSupp, ezRfun y • ezG X Y σ τ y := by
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [ezLfun_eq_ezRfun y hy]
  have h4 : (∑ y ∈ ezSupp, ezRfun y • ezG X Y σ τ y)
      = ∑ t : EzTR, ezCoefR t • ezG X Y σ τ (ezIdxR t) := by
    simpa only [ezRfun] using (ezSum_reindex ezIdxR ezCoefR (ezG X Y σ τ) ezSupp
      (fun t => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)))).symm
  have h5 : (∑ t : EzTR, ezCoefR t • ezG X Y σ τ (ezIdxR t))
      = (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 2 3 X Y (X.δ i σ) τ)
        + ((-1 : ℤ) ^ 3) • (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 3 2 X Y σ (Y.δ i τ)) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ezGen, ← Finset.sum_zsmul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      simp only [ezCoefR, ezIdxR, ezG, Sum.elim_inl]
      rw [mul_smul, delta_map X i (aHom (p := 2) (q := 3) S.1 S.2) σ]
    · rw [← Finset.sum_zsmul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ezGen, ← Finset.sum_zsmul, ← Finset.sum_zsmul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      simp only [ezCoefR, ezIdxR, ezG, Sum.elim_inr]
      rw [mul_smul, mul_smul, delta_map Y i (bHom (p := 3) (q := 2) S.1 S.2) τ]
  have hL : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 2 3 X Y (X.δ i σ) τ) = 0 := by
    have hgen : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • (X.ιChainComplex (R := ezR) (X.δ i σ)).hom 1)
        = d32 X (gen3 X σ) := by
      have h2 := congrArg (fun (f : ezR ⟶ (X.chainComplex ezR).X 2) => f.hom (1 : ℤ))
        (SSet.ιChainComplex_d X ezR (n := 2) σ)
      simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
        LinearMap.comp_apply] at h2
      exact h2.symm
    have key : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 2 3 X Y (X.δ i σ) τ)
        = (ezLin23 X Y τ).hom (d32 X (gen3 X σ)) := by
      rw [← hgen, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_zsmul, ezLin23_apply]
    rw [key, hσ, map_zero]
  have hR : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 3 2 X Y σ (Y.δ i τ)) = 0 := by
    have hgen : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • (Y.ιChainComplex (R := ezR) (Y.δ i τ)).hom 1)
        = d32 Y (gen3 Y τ) := by
      have h2 := congrArg (fun (f : ezR ⟶ (Y.chainComplex ezR).X 2) => f.hom (1 : ℤ))
        (SSet.ιChainComplex_d Y ezR (n := 2) τ)
      simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
        LinearMap.comp_apply] at h2
      exact h2.symm
    have key : (∑ i : Fin 4, ((-1 : ℤ) ^ (i : ℕ)) • ezGen 3 2 X Y σ (Y.δ i τ))
        = (ezLin32 X Y σ).hom (d32 Y (gen3 Y τ)) := by
      rw [← hgen, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_zsmul, ezLin32_apply]
    rw [key, hτ, map_zero]
  rw [h1, h2, h3, h4, h5, hL, hR]
  simp

end

end Work.Cohomology.Crux33

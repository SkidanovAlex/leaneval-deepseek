import Mathlib
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.asM_mul_asMinv
import Submission.Work.MotAS.asMinv_mul_asM
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `twistFieldAS_zero`: the AS twist field of the trivial class is the Klein field

Node of the AS subproject: for `𝕜` of characteristic `5` and Klein data `D` with
`Work.MotV5.KleinData.ASGood D`, the Artin–Schreier twist field of the *trivial* class `g = 0`
coincides with the function field `K(E)` of the Klein curve,

`twistFieldAS D 0 = kleinField D`.

## Proof

`asRoot 0` is a root of `X⁵ - X`, hence a constant: `asRoot 0 = ↑m` for some `m : Fin 5`
(`asRoot_zero_eq_natCast`, from the identity `∏_{i<5}(x - i) = x⁵ - x` in characteristic `5`).
Therefore the Lagrange matrix `asM (asRoot 0)` (the Vandermonde matrix on the nodes
`m, m+1, …, m+4`) has entries in the prime field `𝔽₅`, so the twisted coordinates
`y = asM(asRoot 0)⁻¹ · κ` are obtained from the Klein coordinates `κ` by an invertible matrix
with entries in `K = RatFunc 𝕜`:

* `y_j = Σ_i d_{ji} κ_i` (`d` the entries of `asMinv (asRoot 0)`, in `K`) and
* `κ_i = Σ_j e_{ij} y_j` (`e` the entries of `asM (asRoot 0)`, in `K`).

Since `κ_0 ≠ 0`, dividing by it exhibits the generators `y_j/y_0` as `K`-linear combinations of
the `κ_i/κ_0`; and dividing by `y_0` (nonzero by `Work.MotAS.asTwY_zero_ne_zero`) exhibits the
`κ_i/κ_0` as `K`-linear combinations of the `y_j/y_0`. Hence the two `IntermediateField`s
coincide.
-/

set_option autoImplicit false

namespace Work.MotAS

/-- In characteristic `5`, the polynomial `∏_{i<5}(x - i)` equals `x⁵ - x`. -/
private lemma prod_five_sub_eq_pow_sub {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (x : R) :
    (∏ i : Fin 5, (x - ((i : ℕ) : R))) = x ^ 5 - x := by
  rw [Fin.prod_univ_five]
  norm_num
  ring_nf
  linear_combination (norm := first | refl_ring1 | ring1) (5 * x - 10 * x ^ 2 + 7 * x ^ 3 - 2 * x ^ 4) * h5

/-- `Work.MotV5.asRoot 0`, a root of the split polynomial `X⁵ - X`, is one of the five
constants `0, 1, 2, 3, 4`. -/
private lemma asRoot_zero_eq_natCast (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    ∃ m : Fin 5, Work.MotV5.asRoot (0 : RatFunc 𝕜) = ((m : ℕ) : Work.MotV.Kb 𝕜) := by
  have h5 : (5 : Work.MotV.Kb 𝕜) = 0 := CharP.cast_eq_zero _ _
  have hspec : (Work.MotV5.asRoot (0 : RatFunc 𝕜)) ^ 5 = Work.MotV5.asRoot (0 : RatFunc 𝕜) := by
    have h := Work.MotV5.asRoot_spec (𝕜 := 𝕜) (0 : RatFunc 𝕜)
    rwa [map_zero, sub_eq_zero] at h
  have hprod : (∏ i : Fin 5, (Work.MotV5.asRoot (0 : RatFunc 𝕜)
      - ((i : ℕ) : Work.MotV.Kb 𝕜))) = 0 := by
    rw [prod_five_sub_eq_pow_sub h5, hspec, sub_self]
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  exact ⟨i, sub_eq_zero.mp hi⟩

theorem twistFieldAS_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Work.MotAS.twistFieldAS D 0 = Work.MotV5.kleinField D := by
  classical
  have hGood : D.Good := hD.1
  obtain ⟨m, hwm⟩ := asRoot_zero_eq_natCast (𝕜 := 𝕜)
  have h5K : (5 : Work.MotV.Kb 𝕜) = 0 := CharP.cast_eq_zero _ _
  -- the entries of the Lagrange matrix and of the Vandermonde matrix, as elements of `K`
  let dk : Fin 5 → Fin 5 → RatFunc 𝕜 := fun j i =>
    (if (j:ℕ) = 0 then 1 else 0) - (((m:ℕ) : RatFunc 𝕜) + ((i:ℕ):RatFunc 𝕜)) ^ (4 - (j:ℕ))
  let em : Fin 5 → Fin 5 → RatFunc 𝕜 := fun i j =>
    (((m:ℕ) : RatFunc 𝕜) + ((i:ℕ):RatFunc 𝕜)) ^ (j:ℕ)
  let kap : Fin 5 → Work.MotV.Om D := fun i => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i
  let y : Fin 5 → Work.MotV.Om D := Work.MotAS.asTwY D 0
  let M : Matrix (Fin 5) (Fin 5) (Work.MotV.Om D) :=
    (Work.MotAS.asM (Work.MotV5.asRoot (0 : RatFunc 𝕜))).map
      (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D))
  let N : Matrix (Fin 5) (Fin 5) (Work.MotV.Om D) :=
    ((Work.MotAS.asM (Work.MotV5.asRoot (0 : RatFunc 𝕜)))⁻¹).map
      (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D))
  have hinv : (Work.MotAS.asM (Work.MotV5.asRoot (0 : RatFunc 𝕜)))⁻¹
      = Work.MotAS.asMinv (Work.MotV5.asRoot (0 : RatFunc 𝕜)) :=
    Matrix.inv_eq_right_inv
      (Work.MotAS.asM_mul_asMinv h5K (Work.MotV5.asRoot (0 : RatFunc 𝕜)))
  have hdk : ∀ j i : Fin 5, Work.MotAS.asMinv (Work.MotV5.asRoot (0 : RatFunc 𝕜)) j i
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (dk j i) := by
    intro j i
    simp only [dk, Work.MotAS.asMinv, Matrix.of_apply, hwm, map_sub, map_pow, map_add,
      map_natCast]
    congr 1
    by_cases h : (j:ℕ) = 0 <;> simp [h]
  have hem : ∀ i j : Fin 5, Work.MotAS.asM (Work.MotV5.asRoot (0 : RatFunc 𝕜)) i j
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (em i j) := by
    intro i j
    simp only [em, Work.MotAS.asM, Matrix.of_apply, hwm, map_pow, map_add, map_natCast]
  have hN : ∀ j i : Fin 5, N j i = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (dk j i) := by
    intro j i
    have h1 : N j i = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (dk j i)) := by
      simp only [N, Matrix.map_apply, hinv, hdk j i]
    rw [h1, IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)]
  have hM : ∀ i j : Fin 5, M i j = algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (em i j) := by
    intro i j
    have h1 : M i j = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
        (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (em i j)) := by
      simp only [M, Matrix.map_apply, hem i j]
    rw [h1, IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D)]
  have hMN : M * N = 1 := by
    simp only [M, N]
    rw [← Matrix.map_mul, hinv,
      Work.MotAS.asM_mul_asMinv h5K (Work.MotV5.asRoot (0 : RatFunc 𝕜))]
    exact Matrix.map_one (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D))
      (map_zero _) (map_one _)
  have hy : y = Matrix.mulVec N kap := by
    funext j
    simp only [y, Work.MotAS.asTwY, N, kap, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hyM : Matrix.mulVec M y = kap := by
    rw [hy, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  have hkap : ∀ i : Fin 5, kap i = ∑ j : Fin 5, M i j * y j := by
    intro i
    have h := congrFun hyM i
    simpa only [Matrix.mulVec, dotProduct] using h.symm
  have hy0 : y 0 ≠ 0 := Work.MotAS.asTwY_zero_ne_zero D 0 hGood
  have hkap0 : kap 0 ≠ 0 := hGood.coord0_ne (Work.MotV.Kb 𝕜)
  -- `twistFieldAS D 0 ≤ kleinField D`
  have hle1 : Work.MotAS.twistFieldAS D 0 ≤ Work.MotV5.kleinField D := by
    rw [Work.MotAS.twistFieldAS, IntermediateField.adjoin_le_iff]
    rintro x ⟨j, rfl⟩
    change Work.MotAS.asTwY D 0 j / Work.MotAS.asTwY D 0 0 ∈ Work.MotV5.kleinField D
    let s : Fin 5 → Work.MotV.Om D := fun j =>
      ∑ i : Fin 5, algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (dk j i) * (kap i / kap 0)
    have hs_mem : ∀ j, s j ∈ Work.MotV5.kleinField D := by
      intro j
      refine IntermediateField.sum_mem _ (fun i _ => ?_)
      exact mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
    have hyj : ∀ j, y j = s j * kap 0 := by
      intro j
      have h1 : y j = (Matrix.mulVec N kap) j := by rw [hy]
      rw [h1]
      simp only [Matrix.mulVec, dotProduct, hN, s, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_assoc, div_mul_cancel₀ (kap i) hkap0]
    have heq : Work.MotAS.asTwY D 0 j / Work.MotAS.asTwY D 0 0 = s j / s 0 := by
      show y j / y 0 = s j / s 0
      rw [hyj j, hyj 0, mul_div_mul_right _ _ hkap0]
    rw [heq]
    exact div_mem (hs_mem j) (hs_mem 0)
  -- `kleinField D ≤ twistFieldAS D 0`
  have hle2 : Work.MotV5.kleinField D ≤ Work.MotAS.twistFieldAS D 0 := by
    rw [Work.MotV5.kleinField, IntermediateField.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    change kap i / kap 0 ∈ Work.MotAS.twistFieldAS D 0
    have hA : ∀ i : Fin 5, kap i / y 0 ∈ Work.MotAS.twistFieldAS D 0 := by
      intro i
      rw [hkap i, Finset.sum_div]
      refine IntermediateField.sum_mem _ (fun j _ => ?_)
      rw [mul_div_assoc]
      refine mul_mem ?_ ?_
      · rw [hM i j]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)
    have heq : kap i / kap 0 = (kap i / y 0) / (kap 0 / y 0) :=
      (div_div_div_cancel_right₀ hy0 (kap i) (kap 0)).symm
    rw [heq]
    exact div_mem (hA i) (hA 0)
  exact le_antisymm hle1 hle2

end Work.MotAS

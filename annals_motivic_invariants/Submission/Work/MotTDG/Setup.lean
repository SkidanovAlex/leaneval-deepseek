import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.tenMon_linearIndependent
import Submission.Work.MotC2.TransAux.CoordExt

set_option linter.unusedVariables false -- v435-speed

/-!
# TDG, the auxiliary results of the main node

This file collects the `spans`-matrix bookkeeping and the two "extensionality" results that node
TDG-M (`Work.MotTDG.projAut_of_kleinEq_spans`) needs on top of the dispatched leaves.

* `basE_linearIndependent` — the Klein basis `1, x, y, x², xy` is `L`-independent (from node
  TDG-a, `Work.MotTDG.tenMon_linearIndependent`, restricted to the first five indices).
* `matMul` / `matOne` — the `5 × 5` matrix product and identity written with explicit sums on the
  *function* type `Matrix (Fin 5) (Fin 5) L`.  (The `*` notation is avoided on purpose: for a function
  type it binds to the pointwise product, not the matrix product.)
* `lmulVec E M` — the action `v ↦ (i ↦ ∑ j, M i j • v j)` of a matrix with coefficients in `L` on
  a vector of function-field elements, with `lmulVec_matMul` and `lmulVec_matOne`.
* `eL_matMul_cL` / `cL_matMul_eL` — the `spans` witness matrix `eL` is the inverse of the Klein
  matrix `cL`, so that `κ = cL · basE` and `basE = eL · κ` can be inverted.
* `kleinCoord_ne_zero` / `kleinCoord_linearIndependent` — the Klein coordinates are nonzero and
  `L`-independent.
* `algHom_ext_of_genX_genY` — two `L`-algebra endomorphisms of `L(E)` agreeing on `x` and `y`
  are equal.
* `algHom_eq_id_of_kleinCoord_ratio` — an `L`-algebra endomorphism of `L(E)` fixing all the Klein
  ratios `κ_i/κ_0` is the identity.

The last result is what makes the two half-constructions of TDG-M mutually inverse: applying the
construction to `M` and to `M'` gives two endomorphisms whose composites fix the ratios.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotTDG
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 The Klein basis is independent -/

/-- The Klein basis `1, x, y, x², xy` is `L`-linearly independent: it is the restriction of the
ten monomials of node TDG-a along `Fin.castLE (by norm_num : 5 ≤ 10)`. -/
theorem basE_linearIndependent {L : Type*} [Field L] (E : WeierstrassCurve L) :
    LinearIndependent L (basE E) := by
  have h : (fun m : Fin 5 => tenMon E (Fin.castLE (by norm_num : 5 ≤ 10) m)) = basE E := by
    funext m
    fin_cases m <;> simp [tenMon, goodMon, basE]
  rw [← h]
  exact (tenMon_linearIndependent E).comp _ (Fin.castLE_injective _)

/-! ## §2 The matrix product and its action on vectors of function-field elements -/

section Basic

variable {L : Type*} [Field L]

/-- The product of two `5 × 5` matrices over `L`, written with explicit sums.  This is the matrix
product, stated on the function type so that no instance ambiguity between the matrix product and
the pointwise product can arise. -/
def matMul (M N : Matrix (Fin 5) (Fin 5) L) : Matrix (Fin 5) (Fin 5) L := fun i j => ∑ k, M i k * N k j

/-- The identity matrix. -/
def matOne : Matrix (Fin 5) (Fin 5) L := fun i j => if i = j then 1 else 0

/-- The action of a matrix over `L` on a vector of function-field elements:
`(lmulVec E M v) i = ∑ j, M i j • v j`. -/
def lmulVec (E : WeierstrassCurve L) (M : Matrix (Fin 5) (Fin 5) L)
    (v : Fin 5 → FunctionField E) : Fin 5 → FunctionField E := fun i => ∑ j, M i j • v j

@[simp] theorem matMul_apply (M N : Matrix (Fin 5) (Fin 5) L) (i j : Fin 5) :
    matMul M N i j = ∑ k, M i k * N k j := rfl

@[simp] theorem matOne_apply (i j : Fin 5) :
    (matOne : Matrix (Fin 5) (Fin 5) L) i j = if i = j then 1 else 0 := rfl

theorem matMul_assoc (M N P : Matrix (Fin 5) (Fin 5) L) :
    matMul (matMul M N) P = matMul M (matMul N P) := by
  funext i j
  simp only [matMul_apply]
  calc ∑ k, (∑ l, M i l * N l k) * P k j
      = ∑ k, ∑ l, (M i l * N l k) * P k j := by
          exact Finset.sum_congr rfl fun k _ => Finset.sum_mul ..
    _ = ∑ l, ∑ k, (M i l * N l k) * P k j := Finset.sum_comm
    _ = ∑ l, M i l * ∑ k, N l k * P k j := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring

theorem matMul_one (M : Matrix (Fin 5) (Fin 5) L) : matMul M matOne = M := by
  funext i j
  simp only [matMul_apply, matOne_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [if_neg hb, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem one_matMul (M : Matrix (Fin 5) (Fin 5) L) : matMul matOne M = M := by
  funext i j
  simp only [matMul_apply, matOne_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

@[simp] theorem lmulVec_apply (E : WeierstrassCurve L) (M : Matrix (Fin 5) (Fin 5) L)
    (v : Fin 5 → FunctionField E) (i : Fin 5) :
    lmulVec E M v i = ∑ j, M i j • v j := rfl

/-- `lmulVec` turns the matrix product into composition. -/
theorem lmulVec_matMul (E : WeierstrassCurve L) (M N : Matrix (Fin 5) (Fin 5) L)
    (v : Fin 5 → FunctionField E) :
    lmulVec E (matMul M N) v = lmulVec E M (lmulVec E N v) := by
  funext i
  simp only [lmulVec_apply, matMul_apply]
  calc ∑ j, (∑ k, M i k * N k j) • v j
      = ∑ j, ∑ k, (M i k * N k j) • v j := by
          exact Finset.sum_congr rfl fun j _ => Finset.sum_smul ..
    _ = ∑ k, ∑ j, (M i k * N k j) • v j := Finset.sum_comm
    _ = ∑ k, M i k • ∑ j, N k j • v j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _

/-- `lmulVec` of the identity matrix is the identity. -/
theorem lmulVec_matOne (E : WeierstrassCurve L) (v : Fin 5 → FunctionField E) :
    lmulVec E matOne v = v := by
  funext i
  simp only [lmulVec_apply, matOne_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [if_neg (Ne.symm hb), zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end Basic

/-! ## §3 The `spans` matrix is the inverse of the Klein matrix -/

section Spans

variable {𝕜 : Type*} [Field 𝕜]

/-- The Klein coordinates are the Klein matrix applied to the Klein basis. -/
theorem kleinCoord_eq_lmulVec (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord D L
      = lmulVec (D.E.baseChange L) (cL D L) (basE (D.E.baseChange L)) := by
  funext i
  rw [kleinCoord_eq_cL]
  exact Finset.sum_congr rfl fun m _ => (Algebra.smul_def _ _).symm

/-- A `spans` witness says that the Klein basis is the witness matrix applied to the Klein
coordinates. -/
theorem basE_eq_lmulVec (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    basE (D.E.baseChange L)
      = lmulVec (D.E.baseChange L) (eL D L e) (Work.MotV.kleinCoord D L) := by
  funext m
  rw [basE_eq_eL_kleinCoord D L e he m]
  exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

/-- **The `spans` witness matrix is a left inverse of the Klein matrix**: `eL * cL = 1`.  This is
`spans` (`bas = eL · κ`) combined with `kleinCoord_eq_lmulVec` (`κ = cL · bas`) and the
independence of the Klein basis (`basE_linearIndependent`). -/
theorem eL_matMul_cL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    matMul (eL D L e) (cL D L) = matOne := by
  have hbas := basE_linearIndependent (D.E.baseChange L)
  have hz : lmulVec (D.E.baseChange L) (matMul (eL D L e) (cL D L))
      (basE (D.E.baseChange L)) = basE (D.E.baseChange L) := by
    rw [lmulVec_matMul, ← kleinCoord_eq_lmulVec D L, basE_eq_lmulVec D L e he]
  ext m l
  have hzz : (∑ l', matMul (eL D L e) (cL D L) m l' • basE (D.E.baseChange L) l')
      = basE (D.E.baseChange L) m := congrFun hz m
  have hsum1 : (∑ l', matOne m l' • basE (D.E.baseChange L) l')
      = basE (D.E.baseChange L) m := congrFun (lmulVec_matOne (D.E.baseChange L) _) m
  exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hbas
    (fun l' => matMul (eL D L e) (cL D L) m l' - matOne m l'))
    (by
      show (∑ l', (matMul (eL D L e) (cL D L) m l' - matOne m l')
        • basE (D.E.baseChange L) l') = 0
      rw [Finset.sum_congr rfl (fun l' _ => sub_smul _ _ _), Finset.sum_sub_distrib, hzz, hsum1,
        sub_self]) l)

/-- The `Matrix` form of `eL_matMul_cL`: `eL * cL = 1` for the multiplication of Mathlib's
`Matrix` instances. -/
theorem eL_mul_cL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    (eL D L e : Matrix (Fin 5) (Fin 5) L) * (cL D L) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  show matMul (eL D L e) (cL D L) i j = matOne i j
  rw [eL_matMul_cL D L e he]

/-- Consequently `cL * eL = 1` (square matrices over a field). -/
theorem cL_mul_eL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    (cL D L : Matrix (Fin 5) (Fin 5) L) * (eL D L e) = 1 :=
  mul_eq_one_comm.mp (eL_mul_cL D L e he)

/-- **The Klein matrix is a left inverse of the `spans` witness matrix**: `cL * eL = 1`, in the
explicit-sum form used throughout this file. -/
theorem cL_matMul_eL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    matMul (cL D L) (eL D L e) = matOne := by
  have h := cL_mul_eL D L e he
  funext i j
  have h2 : (cL D L * eL D L e) i j = (1 : Matrix (Fin 5) (Fin 5) L) i j :=
    congrFun (congrFun h i) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, matMul_apply, matOne_apply] using h2

/-- The Klein coordinates are `L`-linearly independent: a dependence of the `κ_i` pushes to a
dependence of `basE` (which is independent), and the resulting row is killed by `eL`. -/
theorem kleinCoord_linearIndependent (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L]
    [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    LinearIndependent L (Work.MotV.kleinCoord D L) := by
  have hbas := basE_linearIndependent (D.E.baseChange L)
  have hce := cL_matMul_eL D L e he
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : (∑ m, (∑ j, g j * cL D L j m) • basE (D.E.baseChange L) m) = 0 := by
    have h2 : (∑ j, g j • Work.MotV.kleinCoord D L j)
        = ∑ m, (∑ j, g j * cL D L j m) • basE (D.E.baseChange L) m := by
      calc ∑ j, g j • Work.MotV.kleinCoord D L j
          = ∑ j, g j • (∑ m, cL D L j m • basE (D.E.baseChange L) m) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              congr 1
              rw [kleinCoord_eq_cL]
              exact Finset.sum_congr rfl fun m _ => (Algebra.smul_def _ _).symm
        _ = ∑ j, ∑ m, (g j * cL D L j m) • basE (D.E.baseChange L) m := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun m _ => (mul_smul _ _ _).symm
        _ = ∑ m, ∑ j, (g j * cL D L j m) • basE (D.E.baseChange L) m := Finset.sum_comm
        _ = ∑ m, (∑ j, g j * cL D L j m) • basE (D.E.baseChange L) m := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [← Finset.sum_smul]
    rw [← h2, hg]
  have h2 : ∀ m, (∑ j, g j * cL D L j m) = 0 := fun m =>
    (Fintype.linearIndependent_iff.mp hbas (fun m => ∑ j, g j * cL D L j m)) h1 m
  have h4 : (∑ m, (∑ j, g j * cL D L j m) * eL D L e m i) = g i := by
    calc ∑ m, (∑ j, g j * cL D L j m) * eL D L e m i
        = ∑ m, ∑ j, g j * (cL D L j m * eL D L e m i) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, ∑ m, g j * (cL D L j m * eL D L e m i) := Finset.sum_comm
      _ = ∑ j, g j * (∑ m, cL D L j m * eL D L e m i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ j, g j * matOne j i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hce]
            rfl
      _ = g i := by
            rw [Finset.sum_eq_single i]
            · rw [matOne_apply, if_pos rfl, mul_one]
            · intro b _ hb; rw [matOne_apply, if_neg hb, mul_zero]
            · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [← h4, Finset.sum_eq_zero (fun m _ => by rw [h2 m, zero_mul])]

/-- Each Klein coordinate is nonzero. -/
theorem kleinCoord_ne_zero (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (i : Fin 5) : Work.MotV.kleinCoord D L i ≠ 0 := by
  have hbas := basE_linearIndependent (D.E.baseChange L)
  have hce := cL_matMul_eL D L e he
  intro h0
  have hrow : (∑ m, cL D L i m • basE (D.E.baseChange L) m) = 0 := by
    rw [← h0, kleinCoord_eq_cL]
    exact Finset.sum_congr rfl fun m _ => Algebra.smul_def _ _
  have hzero : ∀ m, cL D L i m = 0 := fun m =>
    (Fintype.linearIndependent_iff.mp hbas (fun m => cL D L i m)) hrow m
  have h1 : matMul (cL D L) (eL D L e) i i = 1 := by
    rw [hce, matOne_apply, if_pos rfl]
  rw [matMul_apply, Finset.sum_eq_zero (fun m _ => by rw [hzero m, zero_mul])] at h1
  exact one_ne_zero h1.symm

end Spans

/-! ## §4 Extensionality for algebra endomorphisms of `L(E)` -/

/-- Two `L`-algebra endomorphisms of the function field of a Weierstrass curve agreeing on the
two coordinates `x, y` are equal. -/
theorem algHom_ext_of_genX_genY {L : Type*} [Field L] (E : WeierstrassCurve L)
    (f g : FunctionField E →ₐ[L] FunctionField E)
    (hx : f (Work.MotV.genX E) = g (Work.MotV.genX E))
    (hy : f (Work.MotV.genY E) = g (Work.MotV.genY E)) : f = g := by
  have h1 : ∀ r : CoordinateRing E,
      f (algebraMap (CoordinateRing E) (FunctionField E) r)
        = g (algebraMap (CoordinateRing E) (FunctionField E) r) := by
    have hcomp : (f.comp (IsScalarTower.toAlgHom L (CoordinateRing E) (FunctionField E)))
        = (g.comp (IsScalarTower.toAlgHom L (CoordinateRing E) (FunctionField E))) := by
      refine Work.MotC2.TransAux.CoordExt E _ _ ?_ ?_
      · show f (algebraMap (CoordinateRing E) (FunctionField E) (Work.MotC2.coordX E))
          = g (algebraMap (CoordinateRing E) (FunctionField E) (Work.MotC2.coordX E))
        rw [Work.MotC2.coordX_eq_mk]
        change f (Work.MotV.genX E) = g (Work.MotV.genX E)
        exact hx
      · show f (algebraMap (CoordinateRing E) (FunctionField E) (Work.MotC2.coordY E))
          = g (algebraMap (CoordinateRing E) (FunctionField E) (Work.MotC2.coordY E))
        rw [Work.MotC2.coordY_eq_mk]
        change f (Work.MotV.genY E) = g (Work.MotV.genY E)
        exact hy
    exact fun r => AlgHom.congr_fun hcomp r
  apply AlgHom.coe_ringHom_injective
  exact IsFractionRing.ringHom_ext (A := CoordinateRing E) h1

section Ratio

variable {𝕜 : Type*} [Field 𝕜]

/-- An `L`-algebra endomorphism of `L(E)` fixing all the Klein ratios `κ_i/κ_0` is the
identity.  Indeed it fixes `κ_0` (from `∑ i, eL 0 i κ_i = bas 0 = 1`), hence every `κ_i`, hence
`x` and `y`. -/
theorem algHom_eq_id_of_kleinCoord_ratio (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L]
    [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (τ : FunctionField (D.E.baseChange L) →ₐ[L] FunctionField (D.E.baseChange L))
    (hτ : ∀ i, τ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
      = Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) :
    τ = AlgHom.id L (FunctionField (D.E.baseChange L)) := by
  have hκ0ne := kleinCoord_ne_zero D L e he 0
  have hκ : ∀ i, τ (Work.MotV.kleinCoord D L i)
      = (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
        * τ (Work.MotV.kleinCoord D L 0) := by
    intro i
    have h1 : Work.MotV.kleinCoord D L i
        = (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
          * Work.MotV.kleinCoord D L 0 := (div_mul_cancel₀ _ hκ0ne).symm
    calc τ (Work.MotV.kleinCoord D L i)
        = τ ((Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
            * Work.MotV.kleinCoord D L 0) := congrArg τ h1
      _ = τ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
            * τ (Work.MotV.kleinCoord D L 0) := map_mul _ _ _
      _ = (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
            * τ (Work.MotV.kleinCoord D L 0) := by rw [hτ i]
  have hdiv : τ (Work.MotV.kleinCoord D L 0) / Work.MotV.kleinCoord D L 0 = 1 := by
    have hone : (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
        * Work.MotV.kleinCoord D L i) = 1 := by
      have h := basE_eq_eL_kleinCoord D L e he 0
      rw [basE_zero] at h
      exact h.symm
    have happ : (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
        * τ (Work.MotV.kleinCoord D L i)) = 1 := by
      have h := congrArg τ hone
      simpa only [map_sum, map_mul, AlgHom.commutes, map_one] using h
    have happ2 : (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
        * (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0))
        * τ (Work.MotV.kleinCoord D L 0) = 1 := by
      calc (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
            * (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0))
            * τ (Work.MotV.kleinCoord D L 0)
          = ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
              * ((Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)
                * τ (Work.MotV.kleinCoord D L 0)) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
              * τ (Work.MotV.kleinCoord D L i) :=
              Finset.sum_congr rfl fun i _ => by rw [hκ i]
        _ = 1 := happ
    have hsumr : (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i)
        * (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0))
        = (Work.MotV.kleinCoord D L 0)⁻¹ := by
      rw [Finset.sum_congr rfl (fun i _ => (mul_div_assoc _ _ _).symm), ← Finset.sum_div, hone,
        one_div]
    rw [hsumr] at happ2
    rw [div_eq_mul_inv, mul_comm]
    exact happ2
  have hτ0 : τ (Work.MotV.kleinCoord D L 0) = Work.MotV.kleinCoord D L 0 :=
    (div_eq_one_iff_eq hκ0ne).mp hdiv
  have hfix : ∀ i, τ (Work.MotV.kleinCoord D L i) = Work.MotV.kleinCoord D L i := by
    intro i
    rw [hκ i, hτ0]
    exact div_mul_cancel₀ _ hκ0ne
  have hset : ∀ m : Fin 5, τ (basE (D.E.baseChange L) m) = basE (D.E.baseChange L) m := by
    intro m
    have hb := basE_eq_eL_kleinCoord D L e he m
    have hsum : τ (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e m i)
        * Work.MotV.kleinCoord D L i)
        = ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e m i)
          * Work.MotV.kleinCoord D L i := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, AlgHom.commutes, hfix i]
    simpa [hb] using hsum
  refine algHom_ext_of_genX_genY (D.E.baseChange L) τ (AlgHom.id L _) ?_ ?_
  · show τ (basE (D.E.baseChange L) 1) = basE (D.E.baseChange L) 1
    exact hset 1
  · show τ (basE (D.E.baseChange L) 2) = basE (D.E.baseChange L) 2
    exact hset 2

end Ratio

end

end Work.MotTDG

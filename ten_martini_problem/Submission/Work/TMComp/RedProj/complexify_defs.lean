import Mathlib

/-!
# Complexifying a formal power series in two real variables

Given a formal multilinear series `p` over `ℝ × ℝ` with values in `ℂ` (i.e. the Taylor
coefficients of a real-analytic function of two real variables), we build its *complexification*
`cplxify p` over `ℂ × ℂ`.

The `n`-th coefficient `cplxify p n` is the unique `ℂ`-multilinear extension of the `ℝ`-multilinear
map `p n`.  It is written out in the real basis `(1,0), (0,1)` of `ℝ × ℝ` (identified with the
classical basis `1, i` of `ℂ`):

`cplxify p n v = ∑_{r : Fin n → Fin 2} (∏ i, (v i)_{r i}) • p n (fun i ↦ basisVec (r i))`.

Because every coordinate of `v` appears exactly once in each summand, this is visibly continuous
`ℂ`-multilinear, and on tuples of *real* vectors it reduces to the usual expansion of `p n` in the
basis, so that `cplxify p n` restricts to `p n`.
-/

namespace Work.TMComp.RedProj

open FormalMultilinearSeries

noncomputable section

/-- The two basis vectors of `ℝ × ℝ`, mirroring the real basis `1, i` of `ℂ`. -/
def basisVec : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- The two coordinate projections `ℝ × ℝ → ℝ`. -/
def coordR : Fin 2 → (ℝ × ℝ) →L[ℝ] ℝ :=
  ![ContinuousLinearMap.fst ℝ ℝ ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ]

/-- The two coordinate projections `ℂ × ℂ → ℂ`. -/
def coordC : Fin 2 → (ℂ × ℂ) →L[ℂ] ℂ :=
  ![ContinuousLinearMap.fst ℂ ℂ ℂ, ContinuousLinearMap.snd ℂ ℂ ℂ]

@[simp] theorem coordR_zero (z : ℝ × ℝ) : coordR 0 z = z.1 := rfl
@[simp] theorem coordR_one (z : ℝ × ℝ) : coordR 1 z = z.2 := rfl
@[simp] theorem coordC_zero (z : ℂ × ℂ) : coordC 0 z = z.1 := rfl
@[simp] theorem coordC_one (z : ℂ × ℂ) : coordC 1 z = z.2 := rfl

/-- The coordinate functionals read off the basis `basisVec`. -/
theorem coordR_basisVec (j k : Fin 2) :
    coordR j (basisVec k) = if j = k then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> simp [coordR, basisVec]

/-- Expansion of a vector of `ℝ × ℝ` in the basis `basisVec`. -/
theorem sum_coordR_smul_basisVec (z : ℝ × ℝ) :
    (∑ j : Fin 2, coordR j z • basisVec j) = z := by
  have h : (∑ j : Fin 2, coordR j z • basisVec j) = (z.1, z.2) := by
    rw [Fin.sum_univ_two]
    simp [coordR, basisVec]
  simpa using h

/-- The tautological real-linear embedding `ℝ × ℝ ↪ ℂ × ℂ`. -/
def toCplx (z : ℝ × ℝ) : ℂ × ℂ := ((z.1 : ℂ), (z.2 : ℂ))

@[simp] theorem toCplx_fst (z : ℝ × ℝ) : (toCplx z).1 = (z.1 : ℂ) := rfl
@[simp] theorem toCplx_snd (z : ℝ × ℝ) : (toCplx z).2 = (z.2 : ℂ) := rfl
@[simp] theorem toCplx_zero : toCplx 0 = 0 := by ext <;> simp [toCplx]
@[simp] theorem toCplx_add (a b : ℝ × ℝ) : toCplx (a + b) = toCplx a + toCplx b := by
  ext <;> simp [toCplx]
@[simp] theorem toCplx_sub (a b : ℝ × ℝ) : toCplx (a - b) = toCplx a - toCplx b := by
  ext <;> simp [toCplx]

/-- Complexification of a formal multilinear series: the `n`-th coefficient is the unique
`ℂ`-multilinear extension of `p n`, expanded in the basis `basisVec`. -/
def cplxify (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) :
    FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ :=
  fun n => ∑ r : Fin n → Fin 2,
    (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (p n fun i => basisVec (r i))).compContinuousLinearMap
      (fun i => coordC (r i))

/-- Evaluation formula for `cplxify`. -/
theorem cplxify_apply (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) (n : ℕ)
    (v : Fin n → ℂ × ℂ) :
    cplxify p n v = ∑ r : Fin n → Fin 2,
      (∏ i, coordC (r i) (v i)) • p n (fun i => basisVec (r i)) := by
  simp [cplxify]

end

end Work.TMComp.RedProj

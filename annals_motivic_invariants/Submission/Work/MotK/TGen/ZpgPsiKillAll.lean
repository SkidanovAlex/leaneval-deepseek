import Mathlib
import Submission.Work.MotK.TGen.ZpgPsiDefs
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotK.TGen.ZpgPsiKillAll`

The graph map `ψ` of `Submission/Work/MotK/TGen/ZpgPsiDefs.lean` (the inverse of the projection
`(y₁,y₂,y₃,y₄) ↦ (y₁,y₃)` from the chart `y₀ = 1` of the twisted Klein curve `C_{h²}` to the plane
model `V(zpgE)` of the residual curve) kills the five chart quadrics `zpgQ a b h k`.

Two of the five are immediate rational identities in `y₁,y₃` (`k = 0` and `k = 3`, the latter is
`Work.MotK.TGen.zpgPsi_zpgQ3`, which defines `y₂`).  The other three (`k = 1, 2, 4`) are killed only
*modulo the eliminant* `zpgE` of the plane model; they are proved in the cleared form

* `ψ(zpgQ 1) · h²W² = −b·y₁·zpgE`,
* `ψ(zpgQ 2) · h²W² = −b·zpgE`,
* `ψ(zpgQ 4) · W²  = −a·y₃·zpgE`

with `W = b⁴y₁ − a⁴h²y₃²`; each of these is a polynomial identity in the two plane coordinates, so it
is discharged by `field_simp` + `ring` after the eliminant is observed to vanish in
`ZPF K a b h = Frac (K[X₀,X₁] ⦸ (zpgE))`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-! ## Reading `K[X₀,X₁]` in the function field -/

/-- The class of a constant of `K` in the function field, read through `K[X₀,X₁]`. -/
lemma zpg_alg_C (K : Type) [Field K] (a b h : K) (r : K) :
    algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C r) = algebraMap K (ZPF K a b h) r := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K) (ZPF K a b h)]
  rfl

/-- The class of `X 0` in the function field is `zpgx`. -/
lemma zpg_alg_X0 (K : Type) [Field K] (a b h : K) :
    algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (X 0) = zpgx K a b h := by
  rw [zpgx, IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (ZP K a b h) (ZPF K a b h)]
  rfl

/-- The class of `X 1` in the function field is `zpgz`. -/
lemma zpg_alg_X1 (K : Type) [Field K] (a b h : K) :
    algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (X 1) = zpgz K a b h := by
  rw [zpgz, IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (ZP K a b h) (ZPF K a b h)]
  rfl

/-- The eliminant vanishes in the function field of the plane model: it is the modulus. -/
lemma zpgE_algebraMap_eq_zero (K : Type) [Field K] (a b h : K) :
    algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgE a b h) = 0 := by
  have h1 : Ideal.Quotient.mk (Ideal.span {zpgE a b h}) (zpgE a b h) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have h2 : algebraMap (MvPolynomial (Fin 2) K) (ZP K a b h) (zpgE a b h) = 0 := h1
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) K) (ZP K a b h) (ZPF K a b h), h2,
    map_zero]

/-- `zpgWbar` is the image of `W = b⁴y₁ − a⁴h²y₃²` in the function field. -/
lemma zpgWbar_eq_algebraMap (K : Type) [Field K] (a b h : K) :
    zpgWbar K a b h = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgW a b h) := by
  rw [zpgW, zpgWbar]
  simp only [map_sub, map_mul, map_pow, zpg_alg_C, zpg_alg_X0, zpg_alg_X1]

/-! ## The five cases -/

section Model

variable {K : Type} [Field K] (a b h : K) [IsDomain (ZP K a b h)]

/-- `algebraMap K (ZPF …) r ≠ 0` for `r ≠ 0`. -/
private lemma zpg_alg_ne_zero {r : K} (hr : r ≠ 0) :
    algebraMap K (ZPF K a b h) r ≠ 0 := by
  intro hz
  exact hr (RingHom.injective (algebraMap K (ZPF K a b h)) (by rw [hz, map_zero]))

/-- `W = b⁴y₁ − a⁴h²y₃²`, written in the atoms of the function field. -/
private lemma zpg_Wnz (hWbar : zpgWbar K a b h ≠ 0) :
    algebraMap K (ZPF K a b h) b ^ 4 * zpgx K a b h
      - algebraMap K (ZPF K a b h) a ^ 4 * algebraMap K (ZPF K a b h) h ^ 2
        * zpgz K a b h ^ 2 ≠ 0 := by
  simpa only [zpgWbar, map_mul, map_pow] using hWbar

/-- `ψ` kills the zeroth chart quadric. -/
private lemma zpgPsi_zpgQ0 (hb : (b : K) ≠ 0) (hh : (h : K) ≠ 0)
    (hWbar : zpgWbar K a b h ≠ 0) :
    zpgPsi K a b h (zpgQ a b h 0) = 0 := by
  rw [show zpgQ a b h 0 =
    - C (a*b) + C (a^2*h^2) * X 1 * X 2 - C (b^2*h^2) * X 0 * X 3 from rfl]
  have hb' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hb
  have hh' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hh
  have hWnz := zpg_Wnz a b h hWbar
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, zpgPsi_X1, zpgPsi_X3,
    zpgPsi_X0, zpgPsi_X2, zpgPsi_C, zpgf2, zpgCc, zpgCbar, zpgWbar]
  field_simp [hWnz]
  refl_ring1

/-- `ψ(zpgQ 1) · h²W² = −b·y₁·zpgE`. -/
private lemma zpgPsi_zpgQ1_mul (hb : (b : K) ≠ 0) (hh : (h : K) ≠ 0)
    (hWbar : zpgWbar K a b h ≠ 0) :
    zpgPsi K a b h (zpgQ a b h 1)
        * algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (h^2) * zpgW a b h ^ 2)
      = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (-b) * X 0 * zpgE a b h) := by
  rw [show zpgQ a b h 1 =
    -(C (a*b)) * (X 1)^2 + C (a^2) * X 3 - C (b^2) * X 0 * X 2 from rfl]
  have hb' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hb
  have hh' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hh
  have hWnz := zpg_Wnz a b h hWbar
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, zpgPsi_X1, zpgPsi_X3,
    zpgPsi_X0, zpgPsi_X2, zpgPsi_C, zpgf2, zpgCc, zpgCbar, zpgWbar, zpgE, zpgW, zpg_alg_C,
    zpg_alg_X0, zpg_alg_X1]
  field_simp [hWnz]
  refl_ring1

/-- `ψ(zpgQ 2) · h²W² = −b·zpgE`. -/
private lemma zpgPsi_zpgQ2_mul (hb : (b : K) ≠ 0) (hh : (h : K) ≠ 0)
    (hWbar : zpgWbar K a b h ≠ 0) :
    zpgPsi K a b h (zpgQ a b h 2)
        * algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (h^2) * zpgW a b h ^ 2)
      = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (-b) * zpgE a b h) := by
  rw [show zpgQ a b h 2 =
    -(C (a*b*h^2)) * (X 3)^2 + C (a^2) * X 0 * X 1 - C (b^2) * X 2 from rfl]
  have hb' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hb
  have hh' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hh
  have hWnz := zpg_Wnz a b h hWbar
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, zpgPsi_X1, zpgPsi_X3,
    zpgPsi_X0, zpgPsi_X2, zpgPsi_C, zpgf2, zpgCc, zpgCbar, zpgWbar, zpgE, zpgW, zpg_alg_C,
    zpg_alg_X0, zpg_alg_X1]
  field_simp [hWnz]
  refl_ring1

/-- `ψ(zpgQ 4) · W² = −a·y₃·zpgE`. -/
private lemma zpgPsi_zpgQ4_mul (hb : (b : K) ≠ 0) (hh : (h : K) ≠ 0)
    (hWbar : zpgWbar K a b h ≠ 0) :
    zpgPsi K a b h (zpgQ a b h 4)
        * algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgW a b h ^ 2)
      = algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (-a) * X 1 * zpgE a b h) := by
  rw [show zpgQ a b h 4 =
    -(C (a*b*h^2)) * (X 2)^2 + C (a^2) * X 0 - C (b^2*h^2) * X 1 * X 3 from rfl]
  have hb' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hb
  have hh' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hh
  have hWnz := zpg_Wnz a b h hWbar
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, zpgPsi_X1, zpgPsi_X3,
    zpgPsi_X0, zpgPsi_X2, zpgPsi_C, zpgf2, zpgCc, zpgCbar, zpgWbar, zpgE, zpgW, zpg_alg_C,
    zpg_alg_X0, zpg_alg_X1]
  field_simp [hWnz]
  refl_ring1

end Model

theorem ZpgPsiKillAll (K : Type) [Field K] (a b h : K) [IsDomain (Work.MotK.TGen.ZP K a b h)] (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (hW : algebraMap (MvPolynomial (Fin 2) K) (Work.MotK.TGen.ZPF K a b h) (Work.MotK.TGen.zpgW a b h) ≠ 0) : ∀ k : Fin 5, Work.MotK.TGen.zpgPsi K a b h (Work.MotK.TGen.zpgQ a b h k) = 0 := by
  have hWbar : zpgWbar K a b h ≠ 0 := by
    rw [zpgWbar_eq_algebraMap]; exact hW
  have hh' := zpg_alg_ne_zero (K := K) (a := a) (b := b) (h := h) hh
  -- the two multiplicands that clear the denominators of `ψ(zpgQ k)`, `k = 1, 2, 4`
  have hmult12 : algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h)
        (C (h ^ 2) * zpgW a b h ^ 2) ≠ 0 := by
    simp only [map_mul, map_pow, zpg_alg_C]
    exact mul_ne_zero (pow_ne_zero 2 hh') (pow_ne_zero 2 hW)
  have hmult4 : algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgW a b h ^ 2) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 2 hW
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact zpgPsi_zpgQ0 a b h hb hh hWbar
  · have hkey := zpgPsi_zpgQ1_mul a b h hb hh hWbar
    have hzero : zpgPsi K a b h (zpgQ a b h 1)
        * algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (h ^ 2) * zpgW a b h ^ 2) = 0 := by
      rw [hkey, map_mul, zpgE_algebraMap_eq_zero, mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_right hmult12
  · have hkey := zpgPsi_zpgQ2_mul a b h hb hh hWbar
    have hzero : zpgPsi K a b h (zpgQ a b h 2)
        * algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (C (h ^ 2) * zpgW a b h ^ 2) = 0 := by
      rw [hkey, map_mul, zpgE_algebraMap_eq_zero, mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_right hmult12
  · exact zpgPsi_zpgQ3 K a b h hb
  · have hkey := zpgPsi_zpgQ4_mul a b h hb hh hWbar
    have hzero : zpgPsi K a b h (zpgQ a b h 4)
        * algebraMap (MvPolynomial (Fin 2) K) (ZPF K a b h) (zpgW a b h ^ 2) = 0 := by
      rw [hkey, map_mul, zpgE_algebraMap_eq_zero, mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_right hmult4

end Work.MotK.TGen

import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.ker_zPsi_eq_saturation
import Submission.Work.MotK.TGen.rad_sat_aux
import Submission.Work.MotK.TGen.zG3Defs
import Submission.Work.MotK.TGen.zIdealMem
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `ker zPsi ≤ √(ZI)`

The missing direction of `ZI = ker zPsi` (the "geometric input" of `ZPlaneModel`); see
`GUIDE_ker_zPsi.md` and `NOTE_rad_sat.md`.

## Structure found (machine-verified with a CAS over `ℚ(a,b,h)`)

With `A₁ = zA = b³h·x₁ − a³h·x₂²`, `C₁ = zC = a²b − ab²h·x₁²x₂`,
`B = zB = A₁·x₀ − C₁`, `g = zg = ZElim`, and

* `e := a⁹h·x₂⁵ − a⁴b⁵`,
* `R := a⁸b x₂³ − a⁷b²h x₁²x₂⁴ + 2a⁵b⁴x₁x₂ − a⁴b⁵h x₁³x₂² − a³b⁶x₂³ − ab⁸h x₁⁴ + b⁹x₁x₂`,
* `G₃ := e·x₀ + R`,  `G₁ := a²b⁴h x₀² − a⁶h x₀x₂³ − a⁵b x₂ + a⁴b²h x₁²x₂² + ab⁵h x₁³ − b⁶x₂`,

one has

* **the identity** `A₁·G₃ − e·B = −b⁴·g` (proved here as `zA_mul_zG3_sub`), whence `g ∈ (B, G₃)`;
* `ZI = (Zcub) = (B, G₁, G₃)`: a Gröbner basis of `ZI` in lex order `x₀ > x₁ > x₂` is
  `[G₁, B, G₃, g]`;
* `A₁·G₁ ∈ (B, G₃)` (explicit certificate);
* `ker zPsi = (B, g) : A₁^∞` (proved by a colleague as `ker_zPsi_eq_saturation`; this is the
  "clear denominators" statement `S[1/A₁]/(B,g) ≅ ZD[1/a₁]`).

The only missing input is `radical_zA_saturation` (delegated as `rad_sat_aux`): `A₁` is a
non-zero-divisor modulo `radical (ZI)`, i.e. no irreducible component of the residual curve
`Z = V(ZI)` lies in `{A₁ = 0}` (the finitely many extra points of `Z` with `A₁ = 0` are limits of
the graph of `(C₁/A₁, x₁, x₂)`, so `Z` is the closure of the graph).

A useful equivalent form: since `√(ZI) : zA^∞ = √(ZI : zA^∞) = √(ker zPsi) = ker zPsi`
(using `ker_zPsi_eq_saturation`), the input is exactly `ker zPsi ⊆ √(ZI)`.
-/


set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The first Gröbner generator `G₁` of `ZI`. -/
noncomputable def zG1 (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a^2*b^4*h) * (X 0)^2 - C (a^6*h) * X 0 * (X 2)^3 - C (a^5*b) * X 2
    + C (a^4*b^2*h) * (X 1)^2 * (X 2)^2 + C (a*b^5*h) * (X 1)^3 - C (b^6) * X 2

/-- **The key explicit identity**: `A₁·G₃ − e·B = −b⁴·g`. -/
theorem zA_mul_zG3_sub (a b h : K) :
    zA K a b h * zG3 a b h - zE a b h * zB K a b h
      = -(C (b^4) : MvPolynomial (Fin 3) K) * zg K a b h := by
  rw [zG3, zE, zR3, zB, zA, zC, zg_eq_ZElim, Work.MotK.TwCensus.ZElim]
  simp only [C_mul, C_pow, C_add, map_ofNat]
  first | refl_ring1 | ring

/-- `g = zg` lies in `(zB, zG3)`. -/
theorem zg_mem_zB_zG3 (a b h : K) (hb : b ≠ 0) :
    zg K a b h ∈ Ideal.span {zB K a b h, zG3 a b h} := by
  have hkey := zA_mul_zG3_sub (K := K) a b h
  have hmem : (C (b^4) : MvPolynomial (Fin 3) K) * zg K a b h
      ∈ Ideal.span {zB K a b h, zG3 a b h} := by
    have heq : (C (b^4) : MvPolynomial (Fin 3) K) * zg K a b h
        = -(zA K a b h * zG3 a b h - zE a b h * zB K a b h) := by
      rw [hkey]; ring
    rw [heq]
    exact neg_mem (Ideal.sub_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
  have hinv : (C (b⁻¹) : MvPolynomial (Fin 3) K) ^ 4 * C (b^4)
      = 1 := by
    rw [← C_pow, ← C_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 4 hb), C_1]
  have := Ideal.mul_mem_left _ ((C (b⁻¹) : MvPolynomial (Fin 3) K) ^ 4) hmem
  rwa [← mul_assoc, hinv, one_mul] at this

theorem ker_zPsi_le_radical_aux (K : Type) [Field K] (a b h : K)
    [IsDomain (Work.MotK.TGen.ZD K a b h)] (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    RingHom.ker (Work.MotK.TGen.zPsi K a b h)
      ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) := by
  intro f hf
  obtain ⟨n, hn⟩ := (ker_zPsi_eq_saturation K a b h ha hb hh f).mp hf
  have hle : Ideal.span {zg K a b h, zB K a b h}
      ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.le_radical (zg_mem_ZI a b h ha)
    · exact Ideal.le_radical (zB_mem_ZI a b h hb)
  exact rad_sat_aux K a b h ha hb hh f ⟨n, hle hn⟩

end Work.MotK.TGen

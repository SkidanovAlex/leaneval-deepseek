import Mathlib
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.MotV5.census_G_alt

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! `Work.MotA.spreadMap 𝕜 n : 𝕜[t,x₁,…,xₙ] →ₐ[𝕜] K[x₁,…,xₙ]` (`K = RatFunc 𝕜`) is the
localization at the submonoid `M := (nonZeroDivisors 𝕜[t]).map (tPoly 𝕜 n)` of "vertical" elements,
for the `𝕜[t,x]`-algebra structure on `K[x]` given by `RingHom.toAlgebra`.

An identical proof already exists as the PRIVATE declaration `cg_isLocalization_spreadMap` in
`Submission/Work/MotV5/census_G_alt.lean` (around lines 27–60), and again in
`census_F_alt.lean` as `cf_isLocalization_spreadMap`: copy one of those proof bodies here (rename/
inline the private helper declarations it uses), via `isLocalization_iff` and its three clauses:
(1) `Work.MotA.spreadMap_tPoly` + `isUnit_iff_ne_zero` + `Work.MotA.algebraMap_ne_zero`;
(2) `Work.MotA.exists_clearing`; (3) `Work.MotA.spreadMap_injective`. -/
namespace Work.MotV5.SpreadLoc

theorem isLocalization_spreadMap (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜)) :=
      RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 n).toRingHom
    IsLocalization ((nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 n))
      (MvPolynomial (Fin n) (RatFunc 𝕜)) := by
  letI : Algebra (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜)) :=
    RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 n).toRingHom
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- every element of the monoid becomes a unit: it is the nonzero constant `C c`
    rintro ⟨y, hy⟩
    rw [Submonoid.mem_map] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
    have hmap : algebraMap (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))
        (Work.MotA.tPoly 𝕜 n c) =
        MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) :=
      Work.MotA.spreadMap_tPoly 𝕜 n c
    rw [hmap]
    exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr (Work.MotA.algebraMap_ne_zero hc0))
  · -- clearing denominators: `Work.MotA.exists_clearing`
    intro z
    obtain ⟨c, hc, b, hb⟩ := Work.MotA.exists_clearing 𝕜 n z
    refine ⟨(b, ⟨Work.MotA.tPoly 𝕜 n c,
        Submonoid.mem_map.mpr ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc, rfl⟩⟩), ?_⟩
    show z * Work.MotA.spreadMap 𝕜 n (Work.MotA.tPoly 𝕜 n c) =
      Work.MotA.spreadMap 𝕜 n b
    rw [Work.MotA.spreadMap_tPoly, hb, mul_comm]
  · -- the spread map is injective
    intro x y hxy
    exact ⟨1, by rw [Work.MotA.spreadMap_injective 𝕜 n hxy]⟩

end Work.MotV5.SpreadLoc

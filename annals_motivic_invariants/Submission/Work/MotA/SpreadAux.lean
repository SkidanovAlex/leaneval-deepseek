import Mathlib
import ChallengeDeps
import Submission.Work.MotA.Defs
import Submission.Work.MotA.Spread
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Auxiliary lemmas for node `S1` (spreading out)

`Work.MotA.spreadMap 𝕜 n : 𝕜[t, x₁,…,xₙ] →ₐ[𝕜] MvPolynomial (Fin n) (RatFunc 𝕜)` sends `t` to the
indeterminate of `K = RatFunc 𝕜` and `xᵢ` to `xᵢ`; its image is the subring `𝕜[t][x₁,…,xₙ]` of
polynomials whose coefficients are polynomials in `t`.

This file collects the small structural lemmas used by the `S1` development:

* `Work.MotA.tPoly 𝕜 n : 𝕜[t] →ₐ[𝕜] 𝕜[t,x₁,…,xₙ]` is the copy of the `t`-axis;
* `Work.MotA.spreadMap_tPoly`: `spreadMap 𝕜 n` sends the `t`-polynomial `c` to the constant
  polynomial `C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c)`, i.e. the subring of coefficients is
  exactly `𝕜[t]`;
* `Work.MotA.awayMap 𝕜 n G : 𝕜[t,x₁,…,xₙ] →ₐ[𝕜] Localization.Away G` is the same map composed with
  the localisation map `K[x] → K[x]_{(G)}`.
-/

noncomputable section

namespace Work.MotA

open MvPolynomial

/-- The copy of `𝕜[t]` inside `𝕜[t, x₁,…,xₙ]`, as a `𝕜`-algebra map. -/
def tPoly (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) :
    Polynomial 𝕜 →ₐ[𝕜] MvPolynomial (Fin (n + 1)) 𝕜 :=
  Polynomial.aeval (MvPolynomial.X 0)

@[simp]
theorem tPoly_X (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) :
    tPoly 𝕜 n Polynomial.X = MvPolynomial.X (0 : Fin (n + 1)) :=
  Polynomial.aeval_X _

theorem tPoly_C (𝕜 : Type) [CommSemiring 𝕜] (n : ℕ) (a : 𝕜) :
    tPoly 𝕜 n (Polynomial.C a) = MvPolynomial.C a := by
  rw [tPoly, Polynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- **`S1`, the coefficient subring.**  `spreadMap 𝕜 n` sends the `t`-polynomial `c` (viewed as a
polynomial in `t, x₁,…,xₙ` not involving the `x`'s) to the constant polynomial `C c` of `K[x]`. -/
theorem spreadMap_tPoly (𝕜 : Type) [Field 𝕜] (n : ℕ) (c : Polynomial 𝕜) :
    spreadMap 𝕜 n (tPoly 𝕜 n c) =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) := by
  have hbase : Polynomial.aeval (RatFunc.X : RatFunc 𝕜) =
      IsScalarTower.toAlgHom 𝕜 (Polynomial 𝕜) (RatFunc 𝕜) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X, IsScalarTower.toAlgHom_apply, RatFunc.algebraMap_X]
  have h1 : (spreadMap 𝕜 n).comp (tPoly 𝕜 n)
      = Polynomial.aeval (MvPolynomial.C (RatFunc.X) : MvPolynomial (Fin n) (RatFunc 𝕜)) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, Polynomial.aeval_X, tPoly_X, spreadMap_X_zero]
  have h2 : Polynomial.aeval (MvPolynomial.C (RatFunc.X) : MvPolynomial (Fin n) (RatFunc 𝕜)) c
      = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) := by
    have h3 : (MvPolynomial.C (RatFunc.X) : MvPolynomial (Fin n) (RatFunc 𝕜)) =
        (IsScalarTower.toAlgHom 𝕜 (RatFunc 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))) RatFunc.X := by
      rw [IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq]
    rw [h3, Polynomial.aeval_algHom_apply, congrFun (congrArg DFunLike.coe hbase) c]
    rw [IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq]
  rw [← AlgHom.comp_apply, h1, h2]

/-- Multiplication by a `t`-polynomial inside `𝕜[t,x₁,…,xₙ]` is, after `spreadMap 𝕜 n`,
multiplication by the corresponding constant of `K[x]`. -/
theorem spreadMap_tPoly_mul (𝕜 : Type) [Field 𝕜] (n : ℕ) (c : Polynomial 𝕜)
    (b : MvPolynomial (Fin (n + 1)) 𝕜) :
    spreadMap 𝕜 n (tPoly 𝕜 n c * b) =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) * spreadMap 𝕜 n b := by
  rw [map_mul, spreadMap_tPoly]

/-- The map `𝕜[t,x₁,…,xₙ] →ₐ[𝕜] Localization.Away G` obtained from `spreadMap 𝕜 n` by applying the
localisation map `K[x₁,…,xₙ] → K[x₁,…,xₙ]_{(G)}`. -/
def awayMap (𝕜 : Type) [Field 𝕜] (n : ℕ) (G : MvPolynomial (Fin n) (RatFunc 𝕜)) :
    MvPolynomial (Fin (n + 1)) 𝕜 →ₐ[𝕜] Localization.Away G :=
  (Algebra.algHom 𝕜 (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)).comp
    (spreadMap 𝕜 n)

@[simp]
theorem awayMap_apply (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (G : MvPolynomial (Fin n) (RatFunc 𝕜)) (b : MvPolynomial (Fin (n + 1)) 𝕜) :
    awayMap 𝕜 n G b = algebraMap _ (Localization.Away G) (spreadMap 𝕜 n b) := rfl

/-- **`S1`, clearing denominators.**  Every element of `K[x₁,…,xₙ]` (`K = RatFunc 𝕜`) acquires
polynomial (`𝕜[t]`-)coefficients after multiplication by a nonzero `t`-polynomial, and the product is
then in the image of `spreadMap 𝕜 n`.  Explicitly: for `a ∈ K[x]` there are `c ∈ 𝕜[t]`, `c ≠ 0`, and
`b ∈ 𝕜[t,x]` with `spreadMap 𝕜 n b = C (algebraMap c) * a`. -/
theorem exists_clearing (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (a : MvPolynomial (Fin n) (RatFunc 𝕜)) :
    ∃ (c : Polynomial 𝕜) (_ : c ≠ 0) (b : MvPolynomial (Fin (n + 1)) 𝕜),
      spreadMap 𝕜 n b = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) * a := by
  induction a using MvPolynomial.induction_on with
  | C k =>
    obtain ⟨⟨num, den, hden⟩, hsurj⟩ :=
      IsLocalization.surj (nonZeroDivisors (Polynomial 𝕜)) k
    refine ⟨den, mem_nonZeroDivisors_iff_ne_zero.mp hden, tPoly 𝕜 n num, ?_⟩
    rw [spreadMap_tPoly, ← MvPolynomial.C_mul,
      show (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) den * k =
          (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) num from by rw [mul_comm]; exact hsurj]
  | add p q hp hq =>
    obtain ⟨cp, hcp, bp, hbp⟩ := hp
    obtain ⟨cq, hcq, bq, hbq⟩ := hq
    refine ⟨cp * cq, mul_ne_zero hcp hcq, tPoly 𝕜 n cq * bp + tPoly 𝕜 n cp * bq, ?_⟩
    rw [map_add, map_mul, map_mul, spreadMap_tPoly, spreadMap_tPoly, hbp, hbq]
    have hcqcp : (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cp * cq)) :
        MvPolynomial (Fin n) (RatFunc 𝕜)) =
        MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cp) *
          MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cq) := by
      rw [map_mul, MvPolynomial.C_mul]
    rw [hcqcp]
    first | refl_ring1 | ring
  | mul_X p i hp =>
    obtain ⟨cp, hcp, bp, hbp⟩ := hp
    refine ⟨cp, hcp, bp * MvPolynomial.X i.succ, ?_⟩
    rw [map_mul, spreadMap_X_succ, hbp]
    first | refl_ring1 | ring

theorem self_mem_powers {R : Type*} [Monoid R] (F : R) : F ∈ Submonoid.powers F := ⟨1, by simp⟩

/-- The element inverted by `IsLocalization.Away x` is a unit. -/
theorem isUnit_algebraMap_self (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    (F : R) [IsLocalization.Away F S] : IsUnit (algebraMap R S F) :=
  IsLocalization.map_units S ⟨F, self_mem_powers F⟩

/-- `algebraMap (Polynomial 𝕜) (RatFunc 𝕜)` is injective, so it sends nonzero polynomials to nonzero
elements. -/
theorem algebraMap_ne_zero {𝕜 : Type} [Field 𝕜] {c : Polynomial 𝕜} (hc : c ≠ 0) :
    algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c ≠ 0 :=
  fun h => hc (RatFunc.algebraMap_injective 𝕜 (by simpa using h))

theorem awayMap_tPoly (𝕜 : Type) [Field 𝕜] (n : ℕ) (G : MvPolynomial (Fin n) (RatFunc 𝕜))
    (c : Polynomial 𝕜) :
    awayMap 𝕜 n G (tPoly 𝕜 n c) =
      algebraMap (RatFunc 𝕜) (Localization.Away G) (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) := by
  rw [awayMap_apply, spreadMap_tPoly, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))
      (Localization.Away G) (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c)]

/-- The image in `K[x]_{(G)}` of a nonzero constant of `K` is a unit. -/
theorem isUnit_algebraMap_C_away (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (G : MvPolynomial (Fin n) (RatFunc 𝕜)) (c : Polynomial 𝕜) (hc : c ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)
      (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c))) := by
  rw [← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))
      (Localization.Away G) (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c)]
  exact IsUnit.map (algebraMap (RatFunc 𝕜) (Localization.Away G))
    (isUnit_iff_ne_zero.mpr (algebraMap_ne_zero hc))

/-- The constant polynomial `C c` of `MvPolynomial (Fin n) (RatFunc 𝕜)` is the image of the
`t`-polynomial `c`. -/
theorem C_eq_algebraMap_apply (𝕜 : Type) [Field 𝕜] (n : ℕ) (c : Polynomial 𝕜) :
    (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) :
        MvPolynomial (Fin n) (RatFunc 𝕜)) =
      algebraMap (RatFunc 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))
        (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c) :=
  congrFun (congrArg DFunLike.coe
    (MvPolynomial.algebraMap_eq (σ := Fin n) (R := RatFunc 𝕜)).symm) _

end Work.MotA

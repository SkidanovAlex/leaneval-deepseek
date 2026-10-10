import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotV.PlaceDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier descent layer for `Work.MotV5.hurwitz_AS`

In characteristic `5` over an algebraically closed field `N`, the Frobenius map `a ↦ a ^ 5` is
bijective, so every polynomial `A` has a coefficientwise "fifth root" `rootPoly A` with

  `(aeval x (rootPoly A)) ^ 5 = aeval (x ^ 5) A`

for `x` in every `N`-algebra.  Consequently the Artin–Schreier solvability condition

  `Hyp E A r : ∀ v (trivial on N), 1 < v r → ∃ u, v (A(r) - (u ^ 5 - u)) ≤ 1`

descends along the Frobenius: from `r = s ^ 5` and `Hyp E A r` one gets `Hyp E (rootPoly A) s`,
because `(rootPoly A)(s) - (w ^ 5 - w) = A(r) - (u ^ 5 - u)` for `w = u - (rootPoly A)(s)`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV5

noncomputable section

variable {N : Type*} [Field N]

/-- Coefficientwise fifth root of a polynomial over an algebraically closed field of
characteristic `5`. -/
theorem exists_rootPoly [IsAlgClosed N] [CharP N 5] {R : Type*} [CommRing R] [Algebra N R]
    (A : Polynomial N) (x : R) :
    ∃ A₀ : Polynomial N, A₀.natDegree = A.natDegree ∧
      (Polynomial.aeval x A₀) ^ 5 = Polynomial.aeval (x ^ 5) A := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : ExpChar N 5 := inferInstance
  haveI : PerfectRing N 5 :=
    PerfectRing.ofSurjective N 5 fun y => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 5)
      exact ⟨z, by rw [frobenius_def, hz]⟩
  let φ : N →+* N := (frobeniusEquiv N 5).symm
  have hcomp : (φ : N →+* N).comp (frobenius N 5) = RingHom.id N :=
    frobeniusEquiv_symm_comp_frobenius N 5
  have hpoly : (A.map φ) ^ 5 = Polynomial.expand N 5 A := by
    have h1 : Polynomial.map (frobenius N 5) (Polynomial.expand N 5 A) = A ^ 5 :=
      Polynomial.map_frobenius_expand 5 A
    have h2 := congrArg (Polynomial.map φ) h1
    rw [Polynomial.map_map, Polynomial.map_pow, hcomp, Polynomial.map_id] at h2
    exact h2.symm
  refine ⟨A.map φ, Polynomial.natDegree_map_eq_of_injective φ.injective A, ?_⟩
  rw [show (Polynomial.aeval x (A.map φ)) ^ 5 = Polynomial.aeval x ((A.map φ) ^ 5) by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval₂_pow],
    hpoly, Polynomial.expand_aeval]

/-- The Artin–Schreier solvability hypothesis of `Work.MotV5.hurwitz_AS`. -/
def Hyp (E : WeierstrassCurve N) (A : Polynomial N) (r : MotC2.Func E) : Prop :=
  ∀ v : Valuation (MotC2.Func E) (WithZero (Multiplicative ℤ)),
    MotV.TrivOn N v → 1 < v r →
      ∃ u, v (Polynomial.aeval r A - (u ^ 5 - u)) ≤ 1

/-- The Artin–Schreier condition descends along the Frobenius: from `r = s ^ 5` one gets the
condition for `s` and the coefficientwise fifth root of `A`. -/
theorem hyp_descend [IsAlgClosed N] [CharP N 5] (E : WeierstrassCurve N) (A A₀ : Polynomial N)
    (r s : MotC2.Func E)
    (hA : (Polynomial.aeval s A₀) ^ 5 = Polynomial.aeval (s ^ 5) A)
    (h : Hyp E A r) (hr : r = s ^ 5) : Hyp E A₀ s := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : CharP (MotC2.Func E) 5 :=
    charP_of_injective_algebraMap (algebraMap N (MotC2.Func E)).injective 5
  intro v hv hvs
  have hvr : 1 < v r := by
    rw [hr, map_pow]
    exact one_lt_pow₀ hvs (by norm_num)
  obtain ⟨u, hu⟩ := h v hv hvr
  refine ⟨u - Polynomial.aeval s A₀, ?_⟩
  have hG : (Polynomial.aeval s A₀) ^ 5 = Polynomial.aeval r A := by
    rw [hA, hr]
  have hsub : (u - Polynomial.aeval s A₀) ^ 5 = u ^ 5 - (Polynomial.aeval s A₀) ^ 5 :=
    sub_pow_char_of_commute 5 (Commute.all u _)
  have key : Polynomial.aeval s A₀
      - ((u - Polynomial.aeval s A₀) ^ 5 - (u - Polynomial.aeval s A₀))
      = Polynomial.aeval r A - (u ^ 5 - u) := by
    rw [hsub, hG]; ring
  rw [key]
  exact hu

end

end Work.MotV5

import Mathlib
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TwCensus.STClass
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwCensus

open MvPolynomial

/-
**Node K6 for the T-twisted Crauder--Katz link: the function field of the residual curve.**

`Work.MotK.TwCensus.Zcub a b h k` (in `Submission/Work/MotK/TwCensus/Defs.lean`) are the five
cubics of the inverse map `kleinTwR a b h` evaluated in the affine chart
`chart3 = (0,x₀,x₁,x₂,1)`; `ZI a b h` is the ideal they generate in `K[x₀,x₁,x₂]`.  Their zero
locus is the chart part of the residual curve `C' = V(kleinTwR) ∩ H` (`H = {z₀ = 0}`) of the
T-twisted link.  Both sides below are fields of transcendence degree 2 over `K`
(`FractionRing (Polynomial R)` is the function field of `C' × 𝔸¹`; `RatFunc = F₂(T)`).

Claim: `RatFunc (κ(C')) = RatFunc (twistFieldTG K D (h^2))`, i.e. `C'` is the twist of the Klein
curve by `h²` (the paper's `C' = Jac²(C)`, whose twist class is `2T`, cf. `MOTIVIC_S45_LEAD.md`
§2.3).

Known input (all in the workspace):
* `C'` is a section of the ruling `S = Sym²(C_h) → Pic²(C_h) = Jac²(C_h)` of the secant surface,
  hence `C' ≅ Jac²(C_h)`; the T'-action on `C'` is translation by `2T`, so `C'` is the `E`-torsor
  whose class is `2 * c_h`, `c_h` the class of the twisted Klein curve `C_h`.
* `twistFieldTG K D h'` is by definition the function field of the twisted Klein curve with Kummer
  class `h'` (`twistFieldTG K D h' = K(twCoordG K D h' i)`, `TwCoordGKleinTw` gives the equations);
  for `h' = h^2` this is the curve `C_{h^2}`, and it is the `E`-torsor with class `2 * c_h` too.
* Numerical check over `𝔽₁₃` with `(a,b,h) = (2,3,5)`: the chart zero locus has `19` points (`20`
  on `ℙ³`), the count of a genus-one curve, and it is *not* the source Klein curve `C` (nor `C_h`).
* Reading of the classical construction (Crauder--Katz, as in `GUIDE_K5K6.md` §2b): for `c' ∈ C'`
  the ruling line `{y : (kleinTwM a b h y) *ᵥ c' = 0}` (see `KleinTwFibre_eq_ker`, sorry-free) meets
  the twisted Klein curve `C_h` in two points `c₁, c₂`, and `c' ↦ c₁ + c₂ ∈ Pic²(C_h)` is the
  identification `C' ≅ Jac²(C_h)`; one then compares the `E`-torsor classes (`2c_h` for both).

Two observations recorded by the reviewers / the area notes (they are *not* defects of the
statement, but the proof has to handle them):
* The chart ideal `radical (ZI a b h)` must be prime (i.e. `Z` irreducible); over `𝔽₁₃` its zero
  locus has `19` points, a genus-one count, and a lex Gröbner basis of the substituted ideal is
  one-dimensional.
* When `h^2` happens to be a fifth power in `K` (e.g. `h = t^5`), the twist by `h^2` is trivial;
  then `twistFieldTG K D (h^2)` is *K-isomorphic* to `twistFieldTG K D 1` (the two twisted
  coordinate systems differ by the `K̄`-linear automorphism `y_i ↦ ζ^i y_i` supplied by
  `Work.MotV.KleinData.Good.T_diag`), so its constants are `K` and the statement is consistent.
  This does *not* require an extra hypothesis, but the case does have to be handled.

The statement is exactly the `hZtwist` input of `Work.MotK.TwCensus.STClassNondeg` (its
`STClassNondeg_of_pieces`).

## Honest state of this file (report of the stretch that added the lemmas below)

The target is *not* proved here.  It needs two genuinely hard inputs; the **elimination** half of
the first is reduced below to explicit polynomial identities which *are* proved.

* **(E) elimination for `Z`.**  Put
  `B = (b³h·x₁ − a³h·x₂²)·x₀ − (a²b − ab²h·x₁²x₂)`,
  `g = ab⁷h²x₁⁵ − b³h(3a⁵+b⁵)x₁²x₂ + a³h(a⁵+2b⁵)x₁x₂³ − a⁶b²hx₂⁵ + a⁶b²`.
  Then `Zcub a b h 3 = −b·B` (`Zcub_three`), so `b·B ∈ ZI`, and `a·g ∈ ZI` with the explicit
  certificate `eliminant_cert` (computed over `ℚ(a,b,h)` by CAS).  Hence, for `a b ≠ 0` (which holds
  under `D.Good`), `B, g ∈ ZI` (`eliminant_relation`, `eliminant_mem_ZI`), so in `Frac` the class of
  `x₀` is the rational function `(a²b − ab²h·x₁²x₂)/(b³h·x₁ − a³h·x₂²)`, `κ(Z)` is generated over
  `K` by `x₁, x₂`, and `κ(Z) ≅ Frac (K[x₁,x₂]/(g))` **provided** `g` is irreducible (verified by
  CAS over `ℚ(a,b,h)`; a formal irreducibility proof is not in the workspace).
* **(T) the twist identification.**  `κ(Z) ≅ ↥(twistFieldTG K D (h²))` as `K`-algebras: the residual
  curve of the `h`-twisted link is the `h²`-twist of the Klein curve.  This is the genuinely
  geometric input (Crauder--Katz: `C' ≅ Jac²(C_h)`, a torsor of class `2c_h`) and it is *not*
  available in the workspace.  `Submission/Work/MotK/TwCensus/TwCompanion.lean` records the key
  structural fact (the twisted data is the diagonal translate of the split data over `K̄`), showing
  that (T) can be proved once in the split case and transported; but the `K`-structure (the twist
  class) still has to be compared, and neither Mathlib nor the workspace has the torsor/Jacobian
  theory this needs.

Numerical evidence recorded while working on (T) (all consistent with the statement):
* `#Z̄(𝔽_p) = #E_{a,b}(𝔽_p)` for `(a,b) = (2,3)` and every good prime `7 ≤ p ≤ 47` (`Z̄` = the
  projective closure of `Z` in `H`; `E_{a,b}` = the Klein curve) — necessary, since over a finite
  field every twist of `E_{a,b}` is isomorphic to `E_{a,b}`;
* `5 ∣ #E_{2,3}(𝔽_p)` for all those `p`, i.e. `E_{2,3}` has a `ℚ`-rational 5-isogeny; consequently
  several Kummer twists `C_d` coincide over `ℚ`, so point-count tests of the *exponent* `2` in the
  twist class are inconclusive;
* the plane model `g` of `Z̄` is irreducible over `ℚ` at `(a,b,h) = (2,3,1)`, `(2,3,5)`, `(1,1,1)`.
-/

section Chart

variable {K : Type*} [Field K]

/-- The components of the affine chart `chart3 = ![0, X0, X1, X2, 1]`. -/
theorem chart3_zero : (Work.MotK.chart3 K) 0 = (0 : MvPolynomial (Fin 3) K) := rfl

theorem chart3_one : (Work.MotK.chart3 K) 1 = (X 0 : MvPolynomial (Fin 3) K) := rfl

theorem chart3_two : (Work.MotK.chart3 K) 2 = (X 1 : MvPolynomial (Fin 3) K) := rfl

theorem chart3_three : (Work.MotK.chart3 K) 3 = (X 2 : MvPolynomial (Fin 3) K) := rfl

theorem chart3_four : (Work.MotK.chart3 K) 4 = (1 : MvPolynomial (Fin 3) K) := rfl

/-- **The third cubic of the chart ideal is the elimination relation.**  With
`B = (b³h·x₁ − a³h·x₂²)·x₀ − (a²b − ab²h·x₁²x₂)` one has `Zcub a b h 3 = −b·B`; in particular
`b·B ∈ ZI`, so for `b ≠ 0` the class of `x₀` in `Frac` is the rational function
`(a²b − ab²h·x₁²x₂)/(b³h·x₁ − a³h·x₂²)`. -/
theorem Zcub_three (a b h : K) :
    Zcub a b h 3 = -(C b) *
      ((C (b^3*h) * X 1 - C (a^3*h) * (X 2)^2) * X 0
        - (C (a^2*b) - C (a*b^2*h) * (X 1)^2 * X 2)) := by
  rw [show Zcub a b h 3 = Work.MotK.kleinTwR3 (C a) (C b) (C h) (Work.MotK.chart3 K)
    from rfl]
  rw [Work.MotK.kleinTwR3]
  simp only [chart3_zero, chart3_one, chart3_two, chart3_three, chart3_four,
    C_mul, C_pow, C_add, C_neg]
  first | refl_ring1 | ring

/-- The elimination relation `B` lies in `ZI a b h` (the `b ≠ 0` form, which is the one used,
since `D.Good` gives `D.b ≠ 0`). -/
theorem eliminant_relation (a b h : K) (hb : b ≠ 0) :
    ((C (b^3*h) * X 1 - C (a^3*h) * (X 2)^2) * X 0
        - (C (a^2*b) - C (a*b^2*h) * (X 1)^2 * X 2)) ∈ ZI a b h := by
  have h3 := Zcub_three (K := K) a b h
  have hb1 : (C (b⁻¹) : MvPolynomial (Fin 3) K) * C b = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hb, C_1]
  have hkey : (C (b⁻¹) : MvPolynomial (Fin 3) K) * Zcub a b h 3 =
      -(((C (b^3*h) * X 1 - C (a^3*h) * (X 2)^2) * X 0
        - (C (a^2*b) - C (a*b^2*h) * (X 1)^2 * X 2))) := by
    rw [h3, neg_mul, mul_neg, ← mul_assoc, hb1, one_mul]
  have hmem : (C (b⁻¹) : MvPolynomial (Fin 3) K) * Zcub a b h 3 ∈ ZI a b h :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩)
  rw [hkey] at hmem
  exact neg_mem_iff.mp hmem

/-- The plane model (eliminant) `g = ab⁷h²x₁⁵ − b³h(3a⁵+b⁵)x₁²x₂ + a³h(a⁵+2b⁵)x₁x₂³ − a⁶b²hx₂⁵
+ a⁶b²` of the chart ideal `ZI a b h`: the elimination ideal `ZI ∩ K[x₁,x₂]` is generated by it
(the membership `a·g ∈ ZI` is proved below; the generation statement is the missing irreducibility
input). -/
noncomputable def ZElim (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a*b^7*h^2) * (X 1)^5 - C (b^3*h*(3*a^5+b^5)) * (X 1)^2 * X 2
    + C (a^3*h*(a^5+2*b^5)) * X 1 * (X 2)^3 - C (a^6*b^2*h) * (X 2)^5 + C (a^6*b^2)

/-- The same plane model, as a polynomial in the two variables `x₁, x₂` (the input of
`Work.MotK.TwCensus.ZElim2_irreducible`).  Verified with CAS: `g` is irreducible in
`ℚ[a,b,h][x₁,x₂]`, hence in `ℚ(a,b,h)[x₁,x₂]`, and in all tested specialisations. -/
noncomputable def ZElim2 (a b h : K) : MvPolynomial (Fin 2) K :=
  C (a*b^7*h^2) * (X 0)^5 - C (b^3*h*(3*a^5+b^5)) * (X 0)^2 * X 1
    + C (a^3*h*(a^5+2*b^5)) * X 0 * (X 1)^3 - C (a^6*b^2*h) * (X 1)^5 + C (a^6*b^2)

/-- **The plane model of the *twisted* Klein curve** `C_H = V(kleinTwP a b H) ⊂ ℙ⁴`: the
eliminant of its coordinate ring in the variables `(y₂,y₃,y₄)` (CAS, Gröbner basis over
`ℚ(a,b,H)`, lex):
`a⁶b³y₂⁵ + Ha⁴(3b⁵−a⁵)y₂²y₃y₄² + Hb⁴(2a⁵−b⁵)y₂y₃³y₄ − Hab⁸y₃⁵ + H²a⁶b³y₄⁵`.
Its fraction ring is the second plane model used in the comparison of `(T)`
(`Work.MotK.TwCensus.ZTwPlane_fractionRing`). -/
noncomputable def ZTwPlane (a b H : K) : MvPolynomial (Fin 3) K :=
  C (a^6*b^3) * (X 0)^5 + C (H*a^4*(3*b^5-a^5)) * (X 0)^2 * X 1 * (X 2)^2
    + C (H*b^4*(2*a^5-b^5)) * X 0 * (X 1)^3 * X 2 - C (H*a*b^8) * (X 1)^5
    + C (H^2*a^6*b^3) * (X 2)^5

/-- The explicit certificate `a·g = (−a³b²x₁x₂)·Zcub₀ + (a²b³x₁ − a⁵x₂²)·Zcub₁ + a⁵·Zcub₃ +
(b⁵h·x₁²)·Zcub₄` (computed by CAS over `ℚ(a,b,h)`). -/
theorem eliminant_cert (a b h : K) :
    C a * ZElim a b h =
      (C (-(a^3*b^2)) * X 1 * X 2) * Zcub a b h 0
        + (C (a^2*b^3) * X 1 - C (a^5) * (X 2)^2) * Zcub a b h 1
        + C (a^5) * Zcub a b h 3
        + (C (b^5*h) * (X 1)^2) * Zcub a b h 4 := by
  rw [ZElim,
    show Zcub a b h 0 = Work.MotK.kleinTwR0 (C a) (C b) (C h) (Work.MotK.chart3 K)
      from rfl,
    show Zcub a b h 1 = Work.MotK.kleinTwR1 (C a) (C b) (C h) (Work.MotK.chart3 K)
      from rfl,
    show Zcub a b h 3 = Work.MotK.kleinTwR3 (C a) (C b) (C h) (Work.MotK.chart3 K)
      from rfl,
    show Zcub a b h 4 = Work.MotK.kleinTwR4 (C a) (C b) (C h) (Work.MotK.chart3 K)
      from rfl]
  simp only [Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4,
    chart3_zero, chart3_one, chart3_two, chart3_three, chart3_four,
    C_mul, C_pow, C_add, C_neg, map_ofNat]
  first | refl_ring1 | ring

/-- The eliminant lies in `ZI a b h` (up to the unit `a`; the `a ≠ 0` form, which is the one used,
since `D.Good` gives `D.a ≠ 0`). -/
theorem eliminant_mem_ZI (a b h : K) (ha : a ≠ 0) : ZElim a b h ∈ ZI a b h := by
  have hc := eliminant_cert (K := K) a b h
  have ha1 : (C a⁻¹ : MvPolynomial (Fin 3) K) * C a = 1 := by
    rw [← C_mul, inv_mul_cancel₀ ha, C_1]
  have hmem : C a * ZElim a b h ∈ ZI a b h := by
    rw [hc]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩))
  have : (C a⁻¹ : MvPolynomial (Fin 3) K) * (C a * ZElim a b h) ∈ ZI a b h :=
    Ideal.mul_mem_left _ _ hmem
  rwa [← mul_assoc, ha1, one_mul] at this

end Chart

-- NOTE (2026-10-05): the theorem that used to sit here (`Work.MotK.TwCensus.ZTwist`, the K6
-- base-curve identification in its `Polynomial R` form) was **removed**: it was never used (its
-- only occurrences in the workspace were in comments), and its content is the theorem
-- `Work.MotK.TGen.ZTwistDiv` of `Submission/Work/MotK/TGen/ZTwistDiv.lean`, which cannot be
-- imported here (it imports this module for `ZElim2`, `ZI`, …).

end Work.MotK.TwCensus

import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.E11Model
import Submission.Work.MotK.E11Arith
import Submission.Work.MotK.E11Spans
import Submission.Work.MotK.E11KleinEq
import Submission.Work.MotK.e11_T_diag
import Submission.Work.MotV5.exists_kleinData5
import Submission.Work.MotT.exists_kleinData_kleinParam

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.ExistsKleinData`

Target (unchanged, as requested by the requester):

```
theorem ExistsKleinData (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] :
    ∃ D : Work.MotV.KleinData 𝕜, D.Good
```

## The construction

The explicit Klein (Fisher) model of the Tate normal form is
`kleinDataCandidate` of `Submission/Work/MotK/E11Model.lean`
(the definitions `E11`, `kleinCoordInt`, `kleinDataCandidate` used to live in this file; they were
moved to `E11Model.lean` so that this file can import the lemmas that are *about* them without an
import cycle, and the copies `E11Arith/E11Spans/E11KleinEq` of the corresponding child lemmas
likewise):

* `E : y² - 10xy - 11y = x³ - 11x²` (the Tate normal form `E_b` with `b = 11`; `T = (0,0)` has
  order `5`), `Δ = -11⁵`, `c₄ = 496`, `j = -2^12·31^3/11^5 = -122023936/161051`;
* Klein parameters `a = b = 1`;
* `coord` = the integral matrix `kleinCoordInt` (rows `κ_0,…,κ_4` in the basis `1,x,y,x²,xy`),
  with `det coord = 11^5`.

The eight fields of `Good` for this datum are supplied by

* `e11_Arith` (`Submission/Work/MotK/E11Arith.lean`): `elliptic`, `j_ne_zero`, `j_ne` — the
  hypotheses are `(2:𝕜) ≠ 0`, `(31:𝕜) ≠ 0`, `(11:𝕜) ≠ 0` and `(400320064:𝕜) ≠ 0` (where
  `400320064 = 2^6·41^2·61^2 = 496^3 + 1728·11^5`), so the bad characteristics are
  `2, 11, 31, 41, 61` (note `j = 0` iff `31 = 0`, `j = 1728` iff `400320064 = 0`, and `E₁₁` is
  singular iff `11 = 0`);
* `e11_KleinEq` (`Submission/Work/MotK/E11KleinEq.lean`): `klein_eq` — in *every* characteristic;
* `e11_Spans` (`Submission/Work/MotK/E11Spans.lean`): `coord0_ne` and `spans`, for `(11:𝕜) ≠ 0`;
* `e11_T_diag` (`Submission/Work/MotK/e11_T_diag.lean`): the `T_diag` field, for `(5:L) ≠ 0` and
  `(11:L) ≠ 0`.  The automorphism is the translation by the explicit `5`-torsion point
  `Q(ζ) = (11(ζ²+ζ³−2)/5, (77ζ³+66ζ²+33ζ−66)/5)`, and the eigen-identity
  `τ_{Q(ζ)}^*(κ_i/κ_0) = ζ^i·(κ_i/κ_0)` is a polynomial identity modulo `Φ₅(ζ)` and the
  Weierstrass relation whose only denominators are powers of `5`; see
  `Submission/Work/MotK/GUIDE_TDiagE11.md`.

## The characteristic-`5` case

In characteristic `5` the datum `E₁₁` degenerates to `E₁` and the field `T_diag` is vacuous; that
case is supplied by `Work.MotV5.exists_kleinData5` (proved in
`Submission/Work/MotV5/exists_kleinData5.lean`).

## Remaining cases

`characteristic ∈ {2, 11, 31, 41, 61}` is not covered by `E₁₁`:
* `2`: `j(E₁₁) = 0`, so `j_ne_zero` fails (everything else, including `T_diag`, holds);
* `11`: `E₁₁` is singular;
* `31`: `j(E₁₁) = 0`;
* `41`, `61`: `j(E₁₁) = 1728`.
In each of these characteristics the same recipe applies with another Tate normal form `E_b`
(`b ∈ 𝕜` avoiding a finite bad set, so `[Infinite 𝕜]` suffices); the Klein data and the `T_diag`
identity have to be recomputed for that `b`.  See `HANDOFF.md` for the detailed analysis.
-/

namespace Work.MotK

/-- A primitive `5`-th root of unity only exists when `5 ≠ 0`. -/
lemma e11_five_ne_zero {L : Type*} [Field L] {ζ : L} (h : IsPrimitiveRoot ζ 5) : (5 : L) ≠ 0 := by
  intro h5
  have hdiff : (ζ - 1) ^ 5 - (ζ ^ 5 - 1) = 0 := by
    rw [show (ζ - 1) ^ 5 - (ζ ^ 5 - 1) = 5 * (-(ζ ^ 4) + 2 * ζ ^ 3 - 2 * ζ ^ 2 + ζ) by ring,
      h5, zero_mul]
  have hone : (ζ - 1) ^ 5 = 0 := by
    rw [h.pow_eq_one, sub_self, sub_zero] at hdiff
    exact hdiff
  have hz : ζ - 1 = 0 := (pow_eq_zero_iff (by norm_num : 5 ≠ 0)).mp hone
  exact h.ne_one (by norm_num) (sub_eq_zero.mp hz)

/-- `(11 : L) ≠ 0` from `(11 : 𝕜) ≠ 0` along an injective algebra map. -/
lemma e11_eleven_ne_zero (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L]
    (h11 : (11 : 𝕜) ≠ 0) : (11 : L) ≠ 0 := by
  rw [show (11 : L) = algebraMap 𝕜 L (11 : 𝕜) from (map_ofNat (algebraMap 𝕜 L) 11).symm]
  exact fun h => h11 ((algebraMap 𝕜 L).injective (by rw [h, map_zero]))

/-- If `(p : 𝕜) = 0` for a prime `p`, then `𝕜` has characteristic `p`.  This converts the case
analysis of `ExistsKleinData` below into the `CharP 𝕜 p` form in which the delegated
characteristic-wise constructions (`Work.MotV5.exists_kleinData5`,
`Work.MotK.exists_good_mod5_one`) are stated. -/
lemma charP_of_prime_eq_zero (𝕜 : Type) [Field 𝕜] {p : ℕ} (hp : p.Prime) (h : (p : 𝕜) = 0) :
    CharP 𝕜 p := by
  have hdvd : ringChar 𝕜 ∣ p := (ringChar.spec 𝕜 p).mp h
  have hne1 : ringChar 𝕜 ≠ 1 := by
    intro h1
    have h10 : ((1 : ℕ) : 𝕜) = 0 := (ringChar.spec 𝕜 1).mpr (h1 ▸ dvd_rfl)
    rw [Nat.cast_one] at h10
    exact one_ne_zero h10
  exact ringChar.of_eq ((hp.dvd_iff_eq hne1).mp hdvd).symm

/-- The explicit Klein datum `kleinDataCandidate 𝕜` is good whenever `2, 11, 31, 400320064` are
nonzero in `𝕜`. -/
theorem good_e11 (𝕜 : Type) [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) (h11 : (11 : 𝕜) ≠ 0)
    (h31 : (31 : 𝕜) ≠ 0) (h1728 : (400320064 : 𝕜) ≠ 0) :
    (kleinDataCandidate 𝕜).Good := by
  obtain ⟨hEll, hj0, hj1728⟩ := e11_Arith 𝕜 h2 h31 h11 h1728
  haveI := hEll
  refine ⟨hEll, ?_, hj0, hj1728, ?_, ?_, ?_, ?_⟩
  · show (1 : 𝕜) * 1 ≠ 0
    norm_num
  · intro L _ _ k
    exact e11_KleinEq 𝕜 L k
  · intro L _ _
    exact (e11_Spans 𝕜 h11).1 L
  · intro L _ _ ζ hζ
    exact e11_T_diag 𝕜 L ζ hζ (e11_five_ne_zero hζ) (e11_eleven_ne_zero 𝕜 L h11)
  · exact (e11_Spans 𝕜 h11).2

/-- **Every infinite field of characteristic `≠ 5` carries a `Good` Klein datum.**

This uses the parametric Hesse family `(a,b) = (u,1)` of
`Work.MotT.exists_kleinData_kleinParam` (built from the flex `(0 : 1 : u⁻¹ : -u⁻¹ : -1)` of the
Hesse model `C_{u,1}`, Fisher, *Invariant theory for the elliptic normal quintic I*).  The only
excluded parameters are `u = 0`, the zeros of `u¹⁰ - 11u⁵ - 1` (where the model is singular) and
the finite "bad" set of that theorem (poles `2u⁵ = 1` of the Weierstrass coefficients, zeros of
`c₄`, and the solutions of `j = 1728`); since `𝕜` is infinite, some `u` avoids all of them.
Note that this covers characteristic `2`: there `w = 2u⁵ - 1 ≡ 1` and all the identities of the
family remain valid (they are integer polynomial identities proved for every field with
`ringChar ≠ 5`). -/
theorem exists_good_of_ringChar_ne_five (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (hk : ringChar 𝕜 ≠ 5) : ∃ D : Work.MotV.KleinData 𝕜, D.Good := by
  classical
  obtain ⟨bad, hbad⟩ := Work.MotT.exists_kleinData_kleinParam (K := 𝕜) hk
  -- the discriminant polynomial `u¹⁰ - 11u⁵ - 1`
  set p : Polynomial 𝕜 := Polynomial.X ^ 10 - 11 * Polynomial.X ^ 5 - 1 with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    intro h
    have h1 := congrArg (fun q : Polynomial 𝕜 => q.eval 0) h
    simp at h1
  -- the finitely many forbidden parameters
  set bad' : Finset 𝕜 := bad ∪ {0} ∪ p.roots.toFinset with hbad'
  obtain ⟨u, -, hu⟩ := (Set.infinite_univ (α := 𝕜)).exists_notMem_finset bad'
  have hmem : ∀ x : 𝕜, x ∈ bad' ↔ x ∈ bad ∨ x = 0 ∨ p.IsRoot x := by
    intro x
    simp only [hbad', Finset.mem_union, Finset.mem_singleton, Multiset.mem_toFinset,
      Polynomial.mem_roots hp0]
    tauto
  have hu_bad : u ∉ bad := fun h => hu ((hmem u).mpr (Or.inl h))
  have hu0 : u ≠ 0 := fun h => hu ((hmem u).mpr (Or.inr (Or.inl h)))
  have huΔ : u ^ 10 - 11 * u ^ 5 - 1 ≠ 0 := by
    intro h
    refine hu ((hmem u).mpr (Or.inr (Or.inr ?_)))
    show p.eval u = 0
    rw [hp]
    simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one] using h
  obtain ⟨D, hD, -, -⟩ := hbad u hu_bad hu0 huΔ
  exact ⟨D, hD⟩

theorem ExistsKleinData (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] :
    ∃ D : Work.MotV.KleinData 𝕜, D.Good := by
  by_cases hchar : ringChar 𝕜 = 5
  · -- characteristic `5`, supplied by the `Work.MotV5` area
    haveI : CharP 𝕜 5 := ringChar.eq_iff.mp hchar
    obtain ⟨D, hD, -⟩ := Work.MotV5.exists_kleinData5 𝕜
    exact ⟨D, hD⟩
  · -- every other characteristic: the parametric Hesse family `(a,b) = (u,1)`
    exact exists_good_of_ringChar_ne_five 𝕜 hchar

end Work.MotK

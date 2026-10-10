/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Arithmetic
-/
import Submission.Work.Arithmetic.Defs
import Submission.Work.Arithmetic.Torsor
import Submission.Work.Arithmetic.period_eq_five_iff
import Submission.Work.Arithmetic.jacSq_not_iso

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Genus-one curves of period five

The arithmetic content of Part B, beyond the definitions: for a genus-one curve of period `5`
(equivalently: no rational point and a rational divisor of degree `5`, which is the output of
Clark–Lacy's Theorem 1.10 / Lang–Tate's Theorem 7, see `Submission/Work/Arithmetic/Classes.lean`),

* the curve is pointless (`Torsor.pointless_of_period_five`),
* it carries a rational divisor of degree `5` (`Torsor.divisorOfDegree_five_of_period_five`),
* its index is `5` (`Torsor.index_eq_five_of_period_five`),
* and it is *not* isomorphic to `Jac²C` (`Torsor.notIsoJacSq_of_period_five`, which is
  Shinder–Zhang, Lemma 2.7; the proof is `Work.Arithmetic.jacSq_not_iso`),

together with the same statements at the geometric (`GenOneCurve`) level, phrased directly in
terms of the scheme `X.C`: `HasRatDivisorOfDegree 𝕜 X.C 5` and `¬ HasRatPoint 𝕜 X.C`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Order

namespace Work.Arithmetic

noncomputable section

namespace Torsor

variable {𝕜 : Type} [Field 𝕜]

/-- A curve of period `5` has no rational point (the paper's "torsors of index 5" have
`C(𝕜) = ∅`). -/
theorem pointless_of_period_five (T : Torsor 𝕜) (h : T.period = 5) : T.Pointless :=
  ((period_eq_five_iff T).mp h).2

/-- A curve of period `5` carries a `𝕜`-rational divisor of degree `5`. -/
theorem divisorOfDegree_five_of_period_five (T : Torsor 𝕜) (h : T.period = 5) :
    T.DivisorOfDegree 5 :=
  ((period_eq_five_iff T).mp h).1

/-- The index of a curve of period `5` is `5` (for genus-one curves period and index agree;
here `index := orderOf cls = period`). -/
theorem index_eq_five_of_period_five (T : Torsor 𝕜) (h : T.period = 5) : T.index = 5 := by
  rw [index_eq_period, h]

/-- **Shinder–Zhang, Lemma 2.7**: a genus-one curve of period `5` with `j ≠ 1728` is not
isomorphic to `Jac²C`; equivalently, the class of `Jac²C` is not in the `Aut(E)`-orbit of the
class of `C`. -/
theorem notIsoJacSq_of_period_five (T : Torsor 𝕜) (h : T.period = 5) : T.NotIsoJacSq :=
  jacSq_not_iso T h

/-- The same, in the form "`C` is not isomorphic to `Jac²C`", with the orbit criterion
spelled out. -/
theorem not_exists_aut_jacSq (T : Torsor 𝕜) (h : T.period = 5) :
    ¬ ∃ σ : Aut 𝕜 T.E, T.act σ T.cls = T.cls ^ (2 : ℤ) :=
  jacSq_not_iso T h

end Torsor

namespace GenOneCurve

variable {𝕜 : Type} [Field 𝕜]

/-- `C(𝕜) ≠ ∅`, in terms of the torsor class (the bridge field of `GenOneCurve`). -/
theorem hasPoint_iff (X : GenOneCurve 𝕜) : X.torsor.HasPoint ↔ HasRatPoint 𝕜 X.C :=
  X.cls_eq_one_iff

/-- `C` has a `𝕜`-rational point of degree `n` iff `Jac^nC ≅ E` (the bridge field of
`GenOneCurve`). -/
theorem hasDivisorOfDegree_iff (X : GenOneCurve 𝕜) (n : ℕ) :
    X.HasDivisorOfDegree n ↔ HasRatDivisorOfDegree 𝕜 X.C n :=
  (X.divisorOfDegree_iff n).symm

/-- `C(𝕜) = ∅`, in terms of the scheme `X.C`. -/
theorem pointless_iff (X : GenOneCurve 𝕜) : X.Pointless ↔ ¬ HasRatPoint 𝕜 X.C := by
  rw [GenOneCurve.Pointless, Torsor.pointless_iff, ← X.cls_eq_one_iff]

/-- Period `5` for a genus-one curve: no rational point and a rational divisor of degree `5`
(the form in which the paper's Lemma `lem:torsors` states the existence). -/
theorem period_eq_five_iff (X : GenOneCurve 𝕜) :
    X.period = 5 ↔ X.HasDivisorOfDegree 5 ∧ X.Pointless :=
  Work.Arithmetic.period_eq_five_iff X.torsor

/-- `C(𝕜) = ∅`, in terms of the torsor class. -/
theorem pointless_of_period_five (X : GenOneCurve 𝕜) (h : X.period = 5) : X.Pointless :=
  Torsor.pointless_of_period_five X.torsor h

/-- `C` carries a `𝕜`-rational divisor of degree `5`, in terms of the torsor class. -/
theorem hasDivisorOfDegree_five_of_period_five (X : GenOneCurve 𝕜) (h : X.period = 5) :
    X.HasDivisorOfDegree 5 :=
  Torsor.divisorOfDegree_five_of_period_five X.torsor h

/-- `C` carries a `𝕜`-rational divisor of degree `5`, in terms of the scheme `X.C`: this is
the degree-five divisor that Riemann–Roch turns into the degree-five embedding `C ⊂ ℙ⁴`
used by the Crauder–Katz L-link (Lin–Shinder, Proposition `prop:elliptic`). -/
theorem hasRatDivisorOfDegree_five (X : GenOneCurve 𝕜) (h : X.period = 5) :
    HasRatDivisorOfDegree 𝕜 X.C 5 :=
  (X.divisorOfDegree_iff 5).mpr (X.hasDivisorOfDegree_five_of_period_five h)

/-- `C(𝕜) = ∅`, in terms of the scheme `X.C`. -/
theorem not_hasRatPoint (X : GenOneCurve 𝕜) (h : X.period = 5) :
    ¬ HasRatPoint 𝕜 X.C := by
  rw [← X.cls_eq_one_iff]
  exact X.pointless_of_period_five h

/-- `j(Jac⁰C) ≠ 1728`, the hypothesis of Shinder–Zhang, Lemma 2.7. -/
theorem j_ne_1728 (X : GenOneCurve 𝕜) : X.j ≠ 1728 := X.torsor.j_ne

/-- The index of `C` is `5`. -/
theorem index_eq_five (X : GenOneCurve 𝕜) (h : X.period = 5) : X.index = 5 :=
  Torsor.index_eq_five_of_period_five X.torsor h

/-- `C ≇ Jac²C` (Shinder–Zhang, Lemma 2.7). -/
theorem notIsoJacSq_of_period_five (X : GenOneCurve 𝕜) (h : X.period = 5) : X.NotIsoJacSq :=
  Torsor.notIsoJacSq_of_period_five X.torsor h

/-- **(TORS)** for a genus-one curve of period `5` over `𝕜`, always with `j ≠ 1728`: `C` has
no rational point, carries a rational divisor of degree `5`, has index `5`, and is not
isomorphic to `Jac²C`.  This is the shape of the conclusion of the paper's Theorem
`thm:ell-curves` that the L-link construction consumes. -/
theorem tors_of_period_five (X : GenOneCurve 𝕜) (h : X.period = 5) :
    HasRatDivisorOfDegree 𝕜 X.C 5 ∧ ¬ HasRatPoint 𝕜 X.C ∧ X.j ≠ 1728 ∧
      X.index = 5 ∧ X.NotIsoJacSq :=
  ⟨X.hasRatDivisorOfDegree_five h, X.not_hasRatPoint h, X.j_ne_1728,
    X.index_eq_five h, X.notIsoJacSq_of_period_five h⟩

/-- **(TORS)**, existentially: every genus-one curve of period `5` over `𝕜` satisfies the
conclusion of the paper's Theorem `thm:ell-curves`, with `C ≇ Jac²C` added. -/
theorem exists_tors_of_period_five (h : GenOneCurveFive 𝕜) :
    ∃ X : GenOneCurve 𝕜, HasRatDivisorOfDegree 𝕜 X.C 5 ∧ ¬ HasRatPoint 𝕜 X.C ∧
      X.j ≠ 1728 ∧ X.index = 5 ∧ X.NotIsoJacSq := by
  obtain ⟨X, hX⟩ := h
  exact ⟨X, X.tors_of_period_five hX⟩

end GenOneCurve

end

end Work.Arithmetic

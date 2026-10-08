import Submission.Work.ZJB.Defs

/-!
# ZJB — subquotients of the D-class, and Theorem 5.2's hypothesis (a)

Glauberman's Theorem 5.2 (p. 1121) is applied in the proof of Theorem B to the ambient group `X`,
and its hypothesis (a) is about **every subquotient** `Q` of `X`:

> if `C(O_p(Q)) ≤ O_p(Q)` then `Z(J(Q_p)) ⊴ Q` for every Sylow `p`-subgroup `Q_p` of `Q`.

For the groups this development is applied to, `Q` is a subquotient of a group with dihedral or
cyclic Sylow 2-subgroups, hence again of that class (`DihOrCycHeredProp`, applied twice), hence
`Qd(p)`-free for `p` odd and therefore `p`-stable (`PStableProp`, Glauberman's Lemma 6.3); so
(a) is exactly `ZJAProp` (Glauberman's Theorem A) applied to `Q`.  This file turns that
observation into lemmas, so that the final assembly can discharge (a) mechanically:

* `dihOrCycSylow_subquotient` — the Sylow 2-shape passes to `Y ⧸ N` for `Y ≤ X`, `N ⊴ Y`;
* `isPStable'_subquotient` — `p`-stability of `Y ⧸ N` from `PStableProp`;
* `zj_normal_of_subquotient` — hypothesis (a) for `Y ⧸ N` from `ZJAProp`.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

variable {X : Type} [Group X] [Finite X]

/-- A subquotient `Y ⧸ N` (`Y ≤ X`, `N ⊴ Y`) of a group with dihedral or cyclic Sylow
2-subgroups again has dihedral or cyclic Sylow 2-subgroups: apply `DihOrCycHeredProp` to `X`
(for the subgroup `Y`) and then to `Y` (for the quotient). -/
theorem dihOrCycSylow_subquotient (h : DihOrCycHeredProp) (hX : DihOrCycSylow X)
    (Y : Subgroup X) (N : Subgroup Y) [N.Normal] : DihOrCycSylow (Y ⧸ N) :=
  (h Y ((h X hX).1 Y)).2 N

/-- `p`-stability of a subquotient of the D-class, straight from `PStableProp`
(Glauberman's Lemma 6.3 (a) ⇒ (b)). -/
theorem isPStable'_subquotient (hPS : PStableProp) (h : DihOrCycHeredProp) (hX : DihOrCycSylow X)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (Y : Subgroup X) (N : Subgroup Y) [N.Normal] :
    IsPStable' p (Y ⧸ N) :=
  hPS (Y ⧸ N) p Fact.out hp2 (dihOrCycSylow_subquotient h hX Y N)

/-- **Hypothesis (a) of Glauberman's Theorem 5.2** for a subquotient `Y ⧸ N` of a group of the
D-class: if `C(O_p(Y ⧸ N)) ≤ O_p(Y ⧸ N)` then `Z(J(Q_p))` is normal in `Y ⧸ N` for every Sylow
`p`-subgroup `Q_p`.  This is `ZJAProp` (Theorem A) applied to `Y ⧸ N`. -/
theorem zj_normal_of_subquotient (hZA : ZJAProp) (h : DihOrCycHeredProp) (hX : DihOrCycSylow X)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (Y : Subgroup X) (N : Subgroup Y) [N.Normal]
    (hconstr : centralizer (pCore p (Y ⧸ N) : Set (Y ⧸ N)) ≤ pCore p (Y ⧸ N)) :
    ∀ Q : Sylow p (Y ⧸ N), (ZJ (Q : Subgroup (Y ⧸ N))).Normal :=
  hZA (Y ⧸ N) p hp2 (dihOrCycSylow_subquotient h hX Y N) hconstr

end Work.ZJB

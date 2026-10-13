import Mathlib
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.Deg.iftP_totalDegree_le
import Submission.Work.WilE9.Defs
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Extend.semipf_deg_extend
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.E2.star_of_semipf
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.SubPfAux.unionSet_set
import Submission.Work.WilE5.Basic

set_option maxHeartbeats 1000000
noncomputable section

namespace Work.WilE9.Ift
open WilkiesDesign WilkiesDesign.E

/-! ## The one-shot construction of BNZ §3 (step 3): vocabulary

Fix `n, m, r`, a chain `c : EAChain (n + (1+m)) r`, equations `F : Fin (1+m) → EAPoly … r`
and a derivative order `L : List (Fin n)`.  The ambient dimension of the construction is
`K = n + 1 + (1+m)`: the new coordinate `z` sits at position `n`, between the `n` base
coordinates and the `(1+m)`-block `(τ, w)` of `Y`.

Since the equations of the piece live over the chain `c` while `Y` lives over its own chain
`Y.c`, the semi-Pfaffian set of the construction is built over the *concatenation* of the two
chains (`Work.WilE7.EAChain.cat`), the `Y`-polynomials being included on the left (`EAPoly.inl`)
and the new equation on the right (`EAPoly.inr`).  The new basic condition is conjoined to
every basic condition of `Y` (`Work.WilE5.conj`), so that the point set of the construction is
the *intersection* of the lifted `Y` with the graph of the new equation. -/

/-- The injection inserting the new coordinate: `Fin (n + (1+m)) → Fin (n + 1 + (1+m))`. -/
abbrev oneShotInj (n m : ℕ) : Fin (n + (1 + m)) → Fin (n + 1 + (1 + m)) :=
  Work.WilE8.skipInj n (1 + m)

/-- The new coordinate: position `n` of `Fin (n + 1 + (1 + m))`. -/
abbrev oneShotNew (n m : ℕ) : Fin (n + 1 + (1 + m)) := Fin.castAdd (1 + m) (Fin.last n)

/-- The single new equation `z * Q^(2|L|) - P_L = 0` of the one-shot construction, over the
chain `c` (`z` is the new coordinate). -/
def oneShotEq {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) :
    EAPoly (n + 1 + (1 + m)) r :=
  MvPolynomial.X (Sum.inl (oneShotNew n m)) *
      (Work.WilE8.EAPoly.extend (oneShotInj n m) (jQ c F)) ^ (2 * L.length) -
    Work.WilE8.EAPoly.extend (oneShotInj n m) (iftP c F (0 : Fin (1 + m)) L)

/-- The single new basic condition of the one-shot construction. -/
def oneShotBasic {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) :
    Basic (n + 1 + (1 + m)) r := ⟨[oneShotEq c F L], []⟩

/-- The chain of the one-shot construction: the chain of `Y` and the chain `c`, both extended
along the injection, concatenated. -/
def oneShotChain {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (Y : SemiPf (n + (1 + m))) :
    EAChain (n + 1 + (1 + m)) (Y.r + r) :=
  Work.WilE7.EAChain.cat (Work.WilE8.EAChain.extend (oneShotInj n m) Y.c)
    (Work.WilE8.EAChain.extend (oneShotInj n m) c)

/-- The semi-Pfaffian set of the one-shot construction. -/
def oneShotSet {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : SemiPf (n + (1 + m))) : SemiPf (n + 1 + (1 + m)) :=
  Work.WilE5.mkSemiPf (oneShotChain c Y)
    (Y.basics.map (fun B =>
      Work.WilE5.conj
        (Work.WilE7.Basic.inl (Work.WilE8.Basic.extend (oneShotInj n m) B))
        (Work.WilE7.Basic.inr (oneShotBasic c F L))))

/-- The target set of the one-shot construction: the pairs `(x, z)` with `|z| ≤ 1` attached to
a point `Z` of `Y` whose `n` base coordinates are `x` and which satisfies the new equation. -/
def oneShotTarget {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : SemiPf (n + (1 + m))) : Set (Fin (n + 1) → ℝ) :=
  {z : Fin (n + 1) → ℝ | |z (Fin.last n)| ≤ 1 ∧
    ∃ Z : Fin (n + (1 + m)) → ℝ,
      Z ∈ Y.set ∧
      (∀ i : Fin n, Z (Fin.castAdd (1 + m) i) = Fin.init z i) ∧
      z (Fin.last n) *
        (eaEval c (jQ c F) Z) ^ (2 * L.length) =
        eaEval c (iftP c F (0 : Fin (1 + m)) L) Z}

@[simp] theorem oneShotSet_fmt {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : SemiPf (n + (1 + m))) :
    (oneShotSet c F L Y).fmt = (n + 1 + (1 + m)) + (Y.r + r) := rfl

/-- The value of the new coordinate. -/
@[simp] theorem oneShotNew_val (n m : ℕ) : ((oneShotNew n m : Fin (n + 1 + (1 + m))) : ℕ) = n :=
  Fin.val_castAdd _ _

/-- The injection is injective. -/
theorem oneShotInj_injective (n m : ℕ) : Function.Injective (oneShotInj n m) :=
  Work.WilE8.Star.skipInj_injective n (1 + m)

end Work.WilE9.Ift

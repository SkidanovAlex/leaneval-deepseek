/-
# The flip certificate of the fold classes

The Voronoi pieces `Dvor i r` of the fold chart of the class `i` are indexed by the sign indices
`r : Fin (foldCodim i) → Bool`, and the identification `actX (wallSum i Δ)` carries `Dvor i r` onto
`Dvor i (flipSet r Δ)`.  The certificate in this file is the *single-step* form of that statement:
flipping `r` at the `t`-th wall is the same as adding the group element `foldGen i t` to the
"state" `(toG (foldKr i ·), foldCr i ·)` of the representative.

The two remaining certificates are the combinatorial facts that make the pieces pairwise disjoint
(`foldWallAt_injective`: the `c` walls of a representative are distinct; `foldWalls_inj`: two
representatives in the same copy with the same wall set coincide).

Everything here is a finite check on the tables of `Submission.Work.FoldInst.Data`; all proofs are
`decide` on small integer / `ZMod 2` computations.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

noncomputable section

namespace Work.FoldInst

/-! ### The root representative -/

theorem cert_fold_root :
    (∀ i : Fin 98, foldKr i (fun _ => false) = 1 ∧ foldDr i (fun _ => false) = 1) := by
  decide

/-- **The representative of the root sign index** (`r = fun _ => false`, the "positive orthant"
piece) is the root representative of the class: the identity developing matrix and the trivial
Klein diagonal. -/
theorem fold_root (i : Fin 98) :
    foldKr i (fun _ => false) = 1 ∧ foldDr i (fun _ => false) = 1 :=
  cert_fold_root i

/-! ### The walls of a representative -/

theorem cert_foldWallAt_injective :
    (∀ i : Fin 98, Function.Injective (foldWallAt i)) := by
  decide

/-- **The `c` walls of a representative are pairwise distinct.** -/
theorem foldWallAt_injective (i : Fin 98) : Function.Injective (foldWallAt i) :=
  cert_foldWallAt_injective i

/-- The side permutation is injective. -/
theorem sidePerm_injective (g : Fin 4 → ZMod 2) : Function.Injective (sidePerm g) :=
  fun S T h => by
    have h2 := congrArg (sidePerm g) h
    simpa [sidePerm_invol] using h2

/-- The walls of a representative are distinct, as a map `Fin (foldCodim i) → Fin 24`. -/
theorem foldWalls_apply_injective (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    Function.Injective (foldWalls i r) :=
  fun _ _ h => foldWallAt_injective i (sidePerm_injective (toG (foldKr i r)) (by simpa [foldWalls] using h))

theorem cert_foldWalls_inj :
    (∀ (i : Fin 98) (r s : Fin (foldCodim i) → Bool), foldCr i r = foldCr i s →
      (∀ t : Fin (foldCodim i), ∃ u : Fin (foldCodim i), foldWalls i s u = foldWalls i r t) →
      r = s) := by
  decide

/-- **If two representatives lie in the same copy and every wall of the first is a wall of the
second, then they are the same sign index.** -/
theorem foldWalls_inj (i : Fin 98) (r s : Fin (foldCodim i) → Bool)
    (hc : foldCr i r = foldCr i s)
    (h : ∀ t : Fin (foldCodim i), ∃ u : Fin (foldCodim i), foldWalls i s u = foldWalls i r t) :
    r = s :=
  cert_foldWalls_inj i r s hc h

/-! ### The single flip step -/

theorem cert_fold_state_flip :
    (∀ (i : Fin 98) (t : Fin (foldCodim i)) (r : Fin (foldCodim i) → Bool),
      ((toG (foldKr i (flipSet r {t})), foldCr i (flipSet r {t})) : Gg) =
        foldGen i t + ((toG (foldKr i r), foldCr i r) : Gg)) := by
  decide

/-- **The flip step.**  Flipping the sign index at the `t`-th wall translates the state
`(toG (foldKr i ·), foldCr i ·)` by the group element `foldGen i t` of that wall. -/
theorem fold_state_flip (i : Fin 98) (t : Fin (foldCodim i)) (r : Fin (foldCodim i) → Bool) :
    ((toG (foldKr i (flipSet r {t})), foldCr i (flipSet r {t})) : Gg) =
      foldGen i t + ((toG (foldKr i r), foldCr i r) : Gg) :=
  cert_fold_state_flip i t r

/-! ### The wall positions of a class -/

theorem cert_wallPos_spec :
    (∀ (i : Fin 98) (t : Fin (foldCodim i)),
      foldPosIsWall i (foldWallPosAt i t) = 1 ∧
        (foldPosToWall i (foldWallPosAt i t) : ℕ) < foldCodim i) := by
  decide

theorem cert_wallPos_toWall :
    (∀ (i : Fin 98) (t : Fin (foldCodim i)),
      (foldPosToWall i (foldWallPosAt i t)).val = t.val) := by
  decide

theorem cert_wallPos_exists :
    (∀ (i : Fin 98) (j : Fin 3), foldPosIsWall i j = 1 →
      (foldPosToWall i j : ℕ) < foldCodim i →
      ∃ t : Fin (foldCodim i), foldWallPosAt i t = j) := by
  decide

theorem cert_foldPattern_pm :
    (∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (j : Fin 3),
      foldPattern i r j = 1 ∨ foldPattern i r j = -1) := by
  decide

/-! ### The sign pattern and sign vector of the flipped index -/

theorem cert_foldEr_flipSet_wall :
    (∀ (i : Fin 98) (t : Fin (foldCodim i)) (r : Fin (foldCodim i) → Bool)
      (Δ : Finset (Fin (foldCodim i))),
      foldEr i (flipSet r Δ) (foldWallPosAt i t) * foldEr i r (foldWallPosAt i t) =
        (if t ∈ Δ then -1 else 1)) := by
  decide

/-- The factor by which the sign vector of the flipped representative differs from the original
one, at the position of a wall: `-1` exactly at the walls in `Δ`. -/
theorem foldEr_flipSet_wall (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) (t : Fin (foldCodim i)) :
    foldEr i (flipSet r Δ) (foldWallPosAt i t) * foldEr i r (foldWallPosAt i t) =
      if t ∈ Δ then -1 else 1 :=
  cert_foldEr_flipSet_wall i t r Δ

theorem cert_foldEr_flipSet_off :
    (∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (Δ : Finset (Fin (foldCodim i))) (j : Fin 3),
      (∀ t : Fin (foldCodim i), foldWallPosAt i t ≠ j) →
      foldEr i (flipSet r Δ) j * foldEr i r j = 1) := by
  decide

/-- The factor by which the sign vector of the flipped representative differs from the original
one, away from the positions of the walls: `+1`. -/
theorem foldEr_flipSet_off (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    (Δ : Finset (Fin (foldCodim i))) (j : Fin 3)
    (h : ∀ t : Fin (foldCodim i), foldWallPosAt i t ≠ j) :
    foldEr i (flipSet r Δ) j * foldEr i r j = 1 :=
  cert_foldEr_flipSet_off i r Δ j h

end Work.FoldInst

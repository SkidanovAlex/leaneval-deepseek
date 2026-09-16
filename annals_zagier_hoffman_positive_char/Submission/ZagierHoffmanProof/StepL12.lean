import Submission.ZagierHoffmanProof.StepL11

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L12: the (2.11) leading-ζ identification closed

`zeta_leading_after_iter` ties the whole tracking chain together: take the Lemma-2.9
relation (`lemma_2_9_rel`, whose distinguished `a`-output `u` has coefficient `1` and
tuple `(q+w1) :: B`), iterate `BC_q` `n` times; then the distinguished member's
ζ_A-value is exactly the ζ_A of the `n`-`q`-prepend of `(q+w1) :: B`:
  ζ_A((BCqIter n (toData R)).cA (iterIdx n (toData R) u)) = ζ_A(qsTuple n (k+1) (consVec⟨q+w1⟩B)).
The proof substitutes the depth equality `R.depA u = k+1` (hdep) and the tuple conjunct
(`hc hdep`) into `qsTuple n (R.depA u) (R.cA u)` via a value-argument function
equality over `Fin (R.depA u + n)` (`value_qsTuple` + `hc` at the transported index),
then the `ζ_A`-reindex bridge (`zeta_reindex_eq` over `R.depA u + n = k+1+n`).
This is paper (2.11)'s leading term, ready for `B*_{s_j}` and the prefix prepends.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The (2.11)-leading ζ-value after `n` `BC_q`-steps of the Lemma-2.9 relation:
the distinguished `a`-output keeps coefficient `1` and its ζ-value equals the ζ_A of
the `n`-`q`-prepend of the merged head tuple `(q+w1) :: B`. -/
theorem zeta_leading_after_iter (k : ℕ) (w1 : ℕ+) (B : Fin k → ℕ+) (n : ℕ) :
    ∃ (R : BinaryRel F) (u : R.ιA),
      R.aA u = 1 ∧
      ζ_A F ((RelData.BCqIter F n (toData F R)).cA (RelData.iterIdx F n (toData F R) u)) =
        ζ_A F (qsTuple F n (k + 1)
          (consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B)) := by
  classical
  rcases lemma_2_9_rel F k w1 B with ⟨R, u, hdep, ha, hc, hleA, hleB, hvalid⟩
  let T0 : Fin (k + 1) → ℕ+ :=
    consVec ⟨(qExp F : ℕ) + (w1 : ℕ), Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ B
  refine ⟨R, u, ha, ?_⟩
  have hz := zeta_iter_leading F n R u
  have hdepadd : R.depA u + n = k + 1 + n := by omega
  -- hfun : the tuple qsTuple n (R.depA u) (R.cA u) equals T0-based qsTuple transported
  have hfun : qsTuple F n (R.depA u) (R.cA u) =
      (fun x : Fin (R.depA u + n) => qsTuple F n (k + 1) T0 (Fin.cast hdepadd x)) := by
    apply _root_.funext
    intro x
    have v1 := value_qsTuple F n (R.depA u) (R.cA u) x
    have v2 := value_qsTuple F n (k + 1) T0 (Fin.cast hdepadd x)
    rw [v1, v2]
    by_cases hx : (x : ℕ) < n
    · have hxc : (Fin.cast hdepadd x : ℕ) < n := by simpa using hx
      simp [hx, hxc]
    · have hxc : ¬ (Fin.cast hdepadd x : ℕ) < n := by simpa using hx
      simp [hx, hxc]
      -- goal: R.cA u ⟨x−n, _⟩ = T0 ⟨x−n, _⟩   (else branches)
      have hc0 := congrFun (hc hdep) (Fin.cast hdep ⟨(x : ℕ) - n, by
        have hxlt : (x : ℕ) < R.depA u + n := x.isLt
        omega⟩)
      -- hc0 : R.cA u (Fin.cast hdep.symm (Fin.cast hdep ⟨x−n, _⟩)) = T0 (Fin.cast hdep ⟨x−n, _⟩)
      have hrt : Fin.cast hdep.symm (Fin.cast hdep ⟨(x : ℕ) - n, (by omega : (x : ℕ) - n < R.depA u)⟩) =
          ⟨(x : ℕ) - n, (by omega : (x : ℕ) - n < R.depA u)⟩ := by
        apply Fin.ext
        simp
      -- simplify hc0's LHS
      have hc1 : R.cA u ⟨(x : ℕ) - n, (by omega : (x : ℕ) - n < R.depA u)⟩ = T0 ⟨(x : ℕ) - n, (by omega : (x : ℕ) - n < k + 1)⟩ := by
        -- T0 (Fin.cast hdep ⟨x−n, _⟩) : Fin(k+1)-element with value x−n
        rw [show Fin.cast hdep.symm (Fin.cast hdep ⟨(x : ℕ) - n, (by omega : (x : ℕ) - n < R.depA u)⟩) =
            ⟨(x : ℕ) - n, (by omega : (x : ℕ) - n < R.depA u)⟩ from hrt] at hc0
        -- hc0 : R.cA u ⟨x−n, _⟩ = T0 (Fin.cast hdep ⟨x−n, _⟩)
        rw [hc0]
        congr 1
      -- now rewrite the goal with hc1
      simpa using hc1
  have hgoal : ζ_A F (qsTuple F n (R.depA u) (R.cA u)) =
      ζ_A F (qsTuple F n (k + 1) T0) := by
    calc
      ζ_A F (qsTuple F n (R.depA u) (R.cA u))
          = ζ_A F (fun x : Fin (R.depA u + n) => qsTuple F n (k + 1) T0 (Fin.cast hdepadd x)) := by
            rw [hfun]
      _ = ζ_A F (qsTuple F n (k + 1) T0) := by
            exact zeta_reindex_eq F hdepadd (qsTuple F n (k + 1) T0)
  rw [hz]
  exact hgoal

end ZagierHoffmanPositiveChar

import Mathlib
import Submission.Work.Stems.Hurewicz
import Submission.Work.Stems.hurewiczChain_eq_of_homotopic
import Submission.Work.Stems.hurewiczChain_transAt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Hurewicz map `πₙ(X,x₀) → Hₙ(X;ℤ)`

`Work.Stems.hurewiczChain` attaches to a cube `p : Ω^ (Fin n) X x₀` the Hurewicz class of its
descent to the sphere; `Work.Stems.hurewiczChain_eq_of_homotopic` shows that this is constant on
homotopy classes relative to the boundary.  Here we descend it to the homotopy group.

* `Work.Stems.hurewiczMap` — the Hurewicz map;
* `Work.Stems.hurewiczMap_mk` — its value on a class, and
* `Work.Stems.hurewiczMap_mul` — it is a group homomorphism, `h(α·β) = h(α) + h(β)`
  (from `Work.Stems.hurewiczChain_transAt`, delegated: this is the pinch computation).
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **The Hurewicz map** `πₙ(X,x₀) → Hₙ(X;ℤ)`: the descent of `hurewiczChain`. -/
def hurewiczMap (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X) :
    HomotopyGroup (Fin n) X x₀ → (chains (TopCat.of X)).homology n :=
  Quotient.lift (fun p => hurewiczChain n hn x₀ p)
    (fun _ _ h => hurewiczChain_eq_of_homotopic n hn h)

/-- `hurewiczMap` of the class of a cube is the Hurewicz class of that cube. -/
theorem hurewiczMap_mk (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (p : Ω^ (Fin n) X x₀) :
    hurewiczMap n hn x₀ ⟦p⟧ = hurewiczChain n hn x₀ p := rfl

/-- **The Hurewicz map is a group homomorphism** in degrees `n + 1 ≥ 1`. -/
theorem hurewiczMap_mul (n : ℕ) {X : Type} [TopologicalSpace X] {x₀ : X}
    (a b : HomotopyGroup (Fin (n + 1)) X x₀) :
    hurewiczMap (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ (a * b) =
      hurewiczMap (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a +
        hurewiczMap (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      simp only [HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))), hurewiczMap_mk]
      exact hurewiczChain_transAt (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (0 : Fin (n + 1))
        p q

end

end Work.Stems

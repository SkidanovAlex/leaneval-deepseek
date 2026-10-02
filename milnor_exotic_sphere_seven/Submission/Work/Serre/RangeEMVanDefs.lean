import Mathlib
import Submission.Work.Serre.Consumers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two range-form inputs of the assembly `SerreC0 → SerreC3 → SerreE3a → SerreS1`

`Work.Serre.RangeEMVanOne` is the range form of `SerreC3` at `n = 1` (`K(A,1)` for abelian torsion
`A`: only models *in a range* are available from the truncation tower, and the range form of the
acyclicity is what the consumer needs), and `Work.Serre.RangeEMVanAll` is the same statement in
general degree, obtained from the `1`-type case by the path–loop fibration (`ΩW` has the same shape
with `a ↦ a-1`, `N ↦ N-1`, so the range loses `2` per step; the consumer's tower range is a free
parameter, so the loss is harmless).  The definitions live here, rather than in the target file,
so that the modules proving the two statements may import them without a cycle.

`π_1(W)` is assumed **abelian** in both statements: the applications only meet abelian groups
(`π_1` of the relevant fibre is `π_j` of a space with `j ≥ 2`), and `SerreC0`/`SerreC3` provide
models and acyclicity for abelian coefficient groups only.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **The `1`-type case of the range form of C3.**  Let `W` be a space which is connected
(`π_0` trivial), whose `π_1` is a *torsion* group, and whose homotopy groups vanish in degrees
`2 ≤ i ≤ N`.  Then `H_t(W;ℚ) = 0` for `0 < t ≤ N-1`.

This is the range form of `SerreC3` for `n = 1` (`K(A,1)`: lens spaces, the transfer of a finite
covering), stated for spaces which are models of `K(A,1)` *in a range* only.  The genuine statement
is `SerreC3`; the comparison of a range model with a genuine one is the content of this lemma.
`π_1(W)` is assumed **abelian**, which is the case in every application (`π_1` of the fibre is
`π_j` of a space with `j ≥ 2`); `SerreC0`/`SerreC3` give models and acyclicity for abelian
coefficient groups only. -/
def RangeEMVanOne : Prop :=
  ∀ (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    (∀ α : HomotopyGroup (Fin 1) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) →
    (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 → IsZero (ratH (TopCat.of W) t)

/-- The same statement with the range parameter `N` and the loss `2a` of the loop-space induction
made explicit; `RangeEMVanAll` below is this with `a = 0`. -/
def RangeEMVanAllAux (a N : ℕ) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    (∀ i : ℕ, 1 ≤ i → i ≤ N → i ≠ a + 1 → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    (∀ α : HomotopyGroup (Fin (a + 1)) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 - 2 * a → IsZero (ratH (TopCat.of W) t)

/-- **The range form of C3, general degree.**  Let `W` be connected, let `a ≥ 0`, suppose that
`π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ a+1`, and that `π_{a+1}(W)` is a *torsion* group.  Then
`H_t(W;ℚ) = 0` for `0 < t ≤ N - 1 - 2*a`.

The loss `2a` in the range is the honest one for the path–loop induction: `SerreE3a` concludes an
isomorphism in degrees `< N''` when the fibre is rationally acyclic in degrees `≤ N''` (so one
degree is lost per step), and the loop space of `W` has the same shape with `a ↦ a-1`, `N ↦ N-1`
(so a second degree is lost per step).  The case `a = 0` is `RangeEMVanOne`; the general case
follows from it by induction on `a`, using `ΩW` (with `π_i(ΩW) = π_{i+1}(W)`) and `E3a` on the
path–loop fibration `ΩW → PW → W` (whose total space is contractible).  For the consumer (the
`m`-connected cover of `Y` at level `m`, where the fibre is a range model of `K(A,m-1)`) the range
`N` is a free parameter of the tower, so the loss is harmless. -/
def RangeEMVanAll : Prop :=
  ∀ (a N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    (∀ i : ℕ, 1 ≤ i → i ≤ N → i ≠ a + 1 → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    (∀ α : HomotopyGroup (Fin (a + 1)) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 - 2 * a → IsZero (ratH (TopCat.of W) t)

end

end Work.Serre

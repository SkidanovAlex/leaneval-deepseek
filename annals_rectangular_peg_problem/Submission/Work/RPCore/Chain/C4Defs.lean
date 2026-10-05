import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Chain.ChainDefs

/-!
# C4: the reference chain action and its quadratic form

The CORE assembly decomposes `Φ_1^{-1} τ_θ Φ_1` (`Φ_1` the time-`1` flow of a compactly supported
periodic Hamiltonian, `0 < θ < π`) into `3N` near-identity (or elementary rotation) steps:
`N` steps for `Φ_1`, `N` steps of the rotation `τ_δ` with `δ = θ/N` and `N` steps for `Φ_1^{-1}`.
Writing `W : Fin (3N) → PS → ℝ` for the type-2 generating functions of the steps and
`n = 3N - 1`, the broken-geodesic action `chainAction n W` is

  `W_j = Wrot δ` on the **middle block** `N ≤ j < 2N` (the rotation steps),

and `W_j - 0` is compactly supported in the slab on the other two blocks.

This file contains the *reference* data used to split the action: the linear part of the action is
a bounded perturbation of

* `BvForm n N δ` — the (explicit) polar bilinear form of the quadratic part of the reference
  action `chainAction n (refGF N δ)`, and
* `Lav n N δ` — the (explicit) linear part of that reference action.

The key structural facts (proved in the sibling modules) are

* `ref_action_quadratic` : `chainAction n (refGF N δ) z = BvForm n N δ z z / 2 + Lav n N δ z`,
* `refForm_kernel` : the kernel of `BvForm n N δ` is the line `ℝ ∙ diagVec n` (the diagonal
  direction shifting all the angular coordinates `q₂` simultaneously), provided
  `cos δ ≠ 0` and `sin (N δ) ≠ 0`.

Since `Lav` vanishes on `diagVec n` and the form is symmetric with kernel `ℝ ∙ diagVec n`, the
linear part can be removed by a translation (`ChainSp n = ℝ ∙ diagVec n ⊕ W` with
`W = {q₀'s angular coordinate = 0}`), leaving a genuine quadratic model whose polar form is
non-degenerate on `W`: this is what the saddle-point theorem `saddle_point_periodic` is applied to.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

/-- The chain space of `n + 1` maps: positions `q : Fin (n+1) → ℝ²` and momenta `P : Fin n → ℝ²`. -/
abbrev ChainSp (n : ℕ) := (Fin (n + 1) → ℝ × ℝ) × (Fin n → ℝ × ℝ)

/-- The "middle block" of rotation steps: `N ≤ j < 2N`. -/
abbrev midBlock (N j : ℕ) : Prop := N ≤ j ∧ j < 2 * N

instance (N j : ℕ) : Decidable (midBlock N j) := by unfold midBlock; infer_instance

/-- The reference generating functions: `Wrot δ` on the middle block, `0` on the other two blocks
(where the reference map is the identity). -/
def refGF (N : ℕ) (δ : ℝ) (j : ℕ) (x : PS) : ℝ := if midBlock N j then Wrot δ x else 0

/-- The explicit polar bilinear form of the quadratic part of the reference action
`chainAction n (refGF N δ)`.  With `z = (q, P)`, `z' = (q', P')` it is

`∑_j ⟨P_j, q'_{j+1} - q'_j⟩ + ⟨P'_j, q_{j+1} - q_j⟩
  - (1/cos δ - 1) ∑_{j ∈ mid} (q¹_j P'¹_j + q'¹_j P¹_j)
  + tan δ ∑_{j ∈ mid} (q¹_j q'¹_j + P¹_j P'¹_j)`,

the first (resp. second, third) sum running over `Fin n` (resp. the middle block). -/
def BvForm (n N : ℕ) (δ : ℝ) (z z' : ChainSp n) : ℝ :=
  (∑ j : Fin n,
      ((z.2 j).1 * ((z'.1 j.succ).1 - (z'.1 j.castSucc).1) +
       (z'.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
       (z.2 j).2 * ((z'.1 j.succ).2 - (z'.1 j.castSucc).2) +
       (z'.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2)))
  - (1 / Real.cos δ - 1) *
      (∑ j : Fin n, if midBlock N (j : ℕ) then
        ((z.1 j.castSucc).1 * (z'.2 j).1 + (z'.1 j.castSucc).1 * (z.2 j).1) else 0)
  + Real.tan δ *
      (∑ j : Fin n, if midBlock N (j : ℕ) then
        ((z.1 j.castSucc).1 * (z'.1 j.castSucc).1 + (z.2 j).1 * (z'.2 j).1) else 0)

/-- The explicit linear part of the reference action `chainAction n (refGF N δ)`:
`-δ ∑_{j ∈ mid} P²_j`. -/
def Lav (n N : ℕ) (δ : ℝ) (z : ChainSp n) : ℝ :=
  -δ * ∑ j : Fin n, if midBlock N (j : ℕ) then (z.2 j).2 else 0

/-- The diagonal direction: shift every angular coordinate `q₂` by the same amount and leave the
momenta alone.  It spans the kernel of `BvForm n N δ`. -/
def diagVec (n : ℕ) : ChainSp n := (fun _ => ((0 : ℝ), 1), fun _ => 0)

@[simp] theorem diagVec_fst (n : ℕ) (j : Fin (n + 1)) : (diagVec n).1 j = (0, 1) := rfl
@[simp] theorem diagVec_snd (n : ℕ) (j : Fin n) : (diagVec n).2 j = 0 := rfl

end

end Work.RPCore.Chain

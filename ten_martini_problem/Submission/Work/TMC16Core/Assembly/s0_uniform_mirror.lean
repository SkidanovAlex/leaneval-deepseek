import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.S0
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Core.Uniform_equiv

/-!
# Mirror symmetry of the `s = 0` uniformity statement

`Assembly.S0Uniform.s0_uniform` produces `Uniform ε` for the phase family
`θ + (j + (H-2)/2) α` indexed by the `s = 0` windows `W1s0 a U ∪ W2s0 a U H M`.
The glue also needs the *mirrored* windows `W1s0L`, `W2s0L` (the case `y < M = m qₙ`),
which are the images of `W1s0`, `W2s0` under the involution `φ x = -x - (H-2)`.

`Uniform` depends only on the numbers `cos (2π z_j)`, and the reflected phase family is the
*negation* of the original one:
`θ + (φ j + (H-2)/2) α = -(-θ + (j + (H-2)/2) α)`.
Since `cos` is even, the two families are `Uniform` with the same `ε`; this file records that
transfer (`Uniform_of_cos_eq`) and applies it.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

noncomputable section

/-- The reflection `x ↦ -x - (H-2)` of the integer line, as an involution. -/
def mirrorZ (H : ℕ) : ℤ ≃ ℤ where
  toFun x := -x - ((H : ℤ) - 2)
  invFun x := -x - ((H : ℤ) - 2)
  left_inv x := by ring
  right_inv x := by ring

/-- `Uniform` depends only on the cosines `cos (2 π z j)`: it transfers along any bijection of
the index sets that preserves the cosines.  (Specialised form of the definition; it covers in
particular the involution `z ↦ -z` of the phase, since `cos` is even.) -/
theorem Uniform_of_cos_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {ε : ℝ} {z : ι → ℝ} {w : κ → ℝ} (e : κ ≃ ι)
    (h : ∀ k, Real.cos (2 * Real.pi * w k) = Real.cos (2 * Real.pi * (z (e k))))
    (hz : Work.TMC16Core.Uniform ε z) : Work.TMC16Core.Uniform ε w := by
  rw [Work.TMC16Core.Uniform] at hz ⊢
  refine ⟨?_, ?_⟩
  · intro k l hkl
    rw [h k, h l]
    exact hz.1 (e k) (e l) (fun hh => hkl (e.injective hh))
  · intro j x hx
    have key : (∏ i ∈ Finset.univ.erase j,
          (x - Real.cos (2 * Real.pi * w i)) /
            (Real.cos (2 * Real.pi * w j) - Real.cos (2 * Real.pi * w i)))
        = (∏ i ∈ Finset.univ.erase (e j),
          (x - Real.cos (2 * Real.pi * z i)) /
            (Real.cos (2 * Real.pi * z (e j)) - Real.cos (2 * Real.pi * z i))) := by
      refine Finset.prod_equiv e ?_ ?_
      · intro i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hi hh
          exact hi (e.injective hh)
        · intro hi hh
          exact hi (by rw [hh])
      · intro i hi
        rw [h i, h j]
    rw [key, Fintype.card_congr e]
    exact hz.2 (e j) x hx

theorem s0_uniform_mirror {α θ ε : ℝ} {H U : ℕ} {a M : ℤ}
    (h : Work.TMC16Core.Uniform ε
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
          Work.TMC16Core.Assembly.W2s0 a U H (-M)} =>
        -θ + (((j : ℤ) : ℝ) + (((H : ℝ) - 2) / 2)) * α)) :
    Work.TMC16Core.Uniform ε
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0L a U H ∪
          Work.TMC16Core.Assembly.W2s0L a U H M} =>
        θ + (((j : ℤ) : ℝ) + (((H : ℝ) - 2) / 2)) * α) := by
  have hiff : ∀ x : ℤ, (x ∈ Work.TMC16Core.Assembly.W1s0L a U H ∪
        Work.TMC16Core.Assembly.W2s0L a U H M) ↔
      (mirrorZ H x ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
        Work.TMC16Core.Assembly.W2s0 a U H (-M)) := by
    intro x
    simp only [mirrorZ, Equiv.coe_fn_mk]
    rw [Finset.mem_union, Finset.mem_union,
      Work.TMC16Core.Assembly.mem_W1s0L_iff, Work.TMC16Core.Assembly.mem_W2s0L_iff]
  let e : {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0L a U H ∪
      Work.TMC16Core.Assembly.W2s0L a U H M} ≃
      {j : ℤ // j ∈ Work.TMC16Core.Assembly.W1s0 a U ∪
        Work.TMC16Core.Assembly.W2s0 a U H (-M)} :=
    Equiv.subtypeEquiv (mirrorZ H) hiff
  refine Uniform_of_cos_eq e ?_ h
  intro k
  have hk : ((e k).1 : ℝ) = -((k : ℤ) : ℝ) - ((H : ℝ) - 2) := by
    show ((mirrorZ H (k : ℤ)) : ℝ) = _
    simp only [mirrorZ, Equiv.coe_fn_mk]
    push_cast
    ring
  rw [hk]
  have harg : 2 * Real.pi * (-θ + (-((k : ℤ) : ℝ) - ((H : ℝ) - 2) + (((H : ℝ) - 2) / 2)) * α)
      = -(2 * Real.pi * (θ + (((k : ℤ) : ℝ) + (((H : ℝ) - 2) / 2)) * α)) := by ring
  rw [harg, Real.cos_neg]

end

end Work.TMC16Core.Assembly

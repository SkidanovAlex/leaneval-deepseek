import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0SpectralDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0IterFibPresB1`

The slot-`i` **fibration**

`Ψ x = 1_A(x i) · Ψ(x[i ↦ c₀])`,   `c₀ ∈ A`,

is preserved by the whole slot-wise iteration `n0Iter`: it is preserved by each single-slot factor
(`P_{B,j}` — `boxPInd_fibPresB1` below — and also by the complement `1 − P_{B,j}`), hence by any
finite composition of them.  The general iteration statement is `n0Iter_fibPresB1`; the requested
statement `n0IterFibPresB1` is the specialisation `Ψ := Ψ`.

Note that `n0Iter` is a *composition* of the slot operators (see the module docstring of
`n0SpectralDefs`), so this is a genuinely iterated statement, not a pointwise product identity: the
fibre hypothesis has to be transported through the intermediate functions
`λ y, (P_{B,j}Ψ)(y)` / `λ y, Ψ y − (P_{B,j}Ψ)(y)` at every step of the list.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open Submission.BoseGases

/-- **The fibre of `boxPInd` over the slot `i`.**  If `Ψ` is concentrated on the fibre
`x i = c₀` in the sense `Ψ x = 1_A(x i)·Ψ(x[i ↦ c₀])`, then so is `P_{B,j}Ψ`, for every slot `j`:

* `j = i`: the slot-`i` box indicator `1_A(x i)` factors out of the `z`-integral (the integral is
  over the same configuration `x[i ↦ z]` on both sides, and the indicator at `c₀` is `1` because
  `c₀ ∈ A`);
* `j ≠ i`: the `z`-integral in slot `j` sees the fibration at the configuration `x[j ↦ z]`, whose
  `i`-th coordinate is still `x i`; the two updates commute (`Function.update_comm`), so the
  constant `1_A(x i)` factors out of the integral. -/
lemma boxPInd_fibPresB1 {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N} {c₀ : EuclideanSpace ℝ (Fin 3)}
    (hc₀ : c₀ ∈ A) {Ψ : X N → ℝ}
    (hΨ : ∀ x : X N,
      Ψ x = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ (Function.update x i c₀)) :
    ∀ j : Fin N, ∀ x : X N,
      Work.UBBInputs8.boxPInd volA A j Ψ x
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * Work.UBBInputs8.boxPInd volA A j Ψ (Function.update x i c₀) := by
  intro j x
  by_cases hji : j = i
  · -- `j = i`: both sides integrate the same configuration `x[i ↦ z]`; the indicator at `c₀` is `1`
    subst hji
    simp only [Work.UBBInputs8.boxPInd, Function.update_idem, Function.update_self,
      Set.indicator_of_mem hc₀, mul_one]
    ring
  · -- `j ≠ i`: the fibration at `x[j ↦ z]` supplies the constant `1_A(x i)`, pulled out of the integral
    have hij : i ≠ j := fun h => hji h.symm
    have hPj : (Function.update x i c₀) j = x j := Function.update_of_ne hji c₀ x
    have hpt : ∀ z, Ψ (Function.update x j z)
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * Ψ (Function.update (Function.update x i c₀) j z) := by
      intro z
      rw [hΨ (Function.update x j z)]
      have h1 : (Function.update x j z) i = x i :=
        Function.update_of_ne (fun h : i = j => hji h.symm) z x
      have h2 : Function.update (Function.update x j z) i c₀
          = Function.update (Function.update x i c₀) j z := by
        rw [Function.update_comm hij]
      rw [h1, h2]
    have hint : (∫ z in A, Ψ (Function.update x j z))
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in A, Ψ (Function.update (Function.update x i c₀) j z)) := by
      rw [show (fun z => Ψ (Function.update x j z))
            = (fun z => A.indicator (fun _ => (1 : ℝ)) (x i)
                * Ψ (Function.update (Function.update x i c₀) j z)) from funext hpt]
      rw [MeasureTheory.integral_const_mul]
    simp only [Work.UBBInputs8.boxPInd]
    rw [hint, hPj]
    ring

/-- **The fibre is preserved by the slot-wise iteration `n0Iter`.**  Induction on the list of slots:
the tail is an instance of the induction hypothesis applied to the intermediate function
`λ y, (P_{B,j}Ψ)(y)` (case `b j = true`) or `λ y, Ψ y − (P_{B,j}Ψ)(y)` (case `b j = false`), and
each of those two functions carries the fibre by `boxPInd_fibPresB1` together with `hΨ`. -/
lemma n0Iter_fibPresB1 {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N} {c₀ : EuclideanSpace ℝ (Fin 3)}
    (hc₀ : c₀ ∈ A) (b : Fin N → Bool) (l : List (Fin N)) {Ψ : X N → ℝ}
    (hΨ : ∀ x : X N,
      Ψ x = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ (Function.update x i c₀)) :
    ∀ x : X N,
      Work.BoseFixB1S.n0Iter volA A b l Ψ x
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * Work.BoseFixB1S.n0Iter volA A b l Ψ (Function.update x i c₀) := by
  have key : ∀ l : List (Fin N), ∀ Ψ : X N → ℝ,
      (∀ x : X N,
        Ψ x = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ (Function.update x i c₀)) →
      ∀ x : X N,
        Work.BoseFixB1S.n0Iter volA A b l Ψ x
          = A.indicator (fun _ => (1 : ℝ)) (x i)
            * Work.BoseFixB1S.n0Iter volA A b l Ψ (Function.update x i c₀) := by
    intro l
    induction l with
    | nil => intro Ψ hΨ x; simpa [Work.BoseFixB1S.n0Iter] using hΨ x
    | cons j l ih =>
      intro Ψ hΨ x
      have hstep : Work.BoseFixB1S.n0Iter volA A b (j :: l) Ψ
          = (if b j then
              Work.BoseFixB1S.n0Iter volA A b l
                (fun y => Work.UBBInputs8.boxPInd volA A j Ψ y)
            else
              Work.BoseFixB1S.n0Iter volA A b l
                (fun y => Ψ y - Work.UBBInputs8.boxPInd volA A j Ψ y)) := rfl
      rw [hstep]
      by_cases hbj : b j
      · rw [if_pos hbj]
        exact ih (fun y => Work.UBBInputs8.boxPInd volA A j Ψ y)
          (fun y => boxPInd_fibPresB1 hc₀ hΨ j y) x
      · rw [if_neg hbj]
        refine ih (fun y => Ψ y - Work.UBBInputs8.boxPInd volA A j Ψ y) ?_ x
        intro y
        rw [hΨ y, boxPInd_fibPresB1 hc₀ hΨ j y]
        ring
  exact key l Ψ hΨ

theorem n0IterFibPresB1 {N : ℕ} {volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N} {c₀ : EuclideanSpace ℝ (Fin 3)}
    (hc₀ : c₀ ∈ A) (b : Fin N → Bool) (l : List (Fin N))
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x : Submission.BoseGases.X N,
      Ψ x = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ (Function.update x i c₀)) :
    ∀ x : Submission.BoseGases.X N,
      Work.BoseFixB1S.n0Iter volA A b l Ψ x
        = A.indicator (fun _ => (1 : ℝ)) (x i)
          * Work.BoseFixB1S.n0Iter volA A b l Ψ (Function.update x i c₀) :=
  n0Iter_fibPresB1 hc₀ b l hΨ

end Work.BoseFixB1S

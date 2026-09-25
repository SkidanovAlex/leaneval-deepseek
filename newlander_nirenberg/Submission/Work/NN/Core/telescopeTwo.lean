/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The coordinate-by-coordinate telescoping for the `(0,2)` `∂̄`-problem on a polydisc

This module defines the explicit linear operator which solves the flat `(0,2)`-equation
`∂̄_j ω_l - ∂̄_l ω_j = ζ_{jl}` on a polydisc of `ℂⁿ = Fin n → ℂ`, by processing the coordinates one
at a time with the *fixed-disc fibre Cauchy potential*

  `fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w) / (w - z j) dw`

(`Submission.Work.NN.Core.fiberPot`), which is a right inverse of `∂̄_j` *without* any support
hypothesis (`Work.NN.Core.fiberPot_Work.CR.Flat.dbarCoord_self`).

Given data `ζ : Fin n → Fin n → Cn n → ℂ` and a radius `R > 0`, put `D⁽⁰⁾ := ζ` and, for
`m = 0, …, n-1`,

* `ψ⁽ᵐ⁾_l := fiberPot R m (D⁽ᵐ⁾_{m l})`           (the `m`-th fibre potential of the `m`-th row),
* `D⁽ᵐ⁺¹⁾_{ij} := D⁽ᵐ⁾_{ij} - (∂̄_i ψ⁽ᵐ⁾_j - ∂̄_j ψ⁽ᵐ⁾_i)`.

All the operations are linear in `ζ`, and the *invariants*

  `D⁽ᵐ⁾_{ij} = 0` whenever `i < m` or `j < m`,   `∂̄D⁽ᵐ⁾ = 0` (closedness of the defect)

hold identically for antisymmetric, closed data, so that `D⁽ⁿ⁻¹⁾ = 0` and the *telescoping*

  `telTwo R ζ := Σ_{m=0}^{n-2} ψ⁽ᵐ⁾`

satisfies `∂̄_j (telTwo R ζ)_l - ∂̄_l (telTwo R ζ)_j = ζ_{jl}` on `polydisc 0 (fun _ => R)`.
The main structural theorems are proved in the companion modules
`Work.NN.Core.telTwo_solves`, `Work.NN.Core.telTwo_bound` and `Work.NN.Core.telTwo_smooth`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.fiberPot_dbarCoord
import Submission.Work.NN.Core.fiberPot_dbarCoord_self
import Submission.Work.NN.Core.contDiff_fiberPot

noncomputable section

open scoped NNReal ENNReal
open Set
open Work.CR.Flat


namespace Work.NN.Core

variable {n : ℕ}

/-- The `(0,2)`-form is *antisymmetric*, i.e. `ζ j l = - ζ l j` pointwise. -/
def IsAntisymmTwo (ζ : Fin n → Fin n → Cn n → ℂ) : Prop :=
  ∀ j l z, ζ j l z = - ζ l j z

/-- The `(0,2)`-form is *closed*: `∂̄_j ζ_{lm} - ∂̄_l ζ_{jm} + ∂̄_m ζ_{jl} = 0`. -/
def IsClosedTwo (ζ : Fin n → Fin n → Cn n → ℂ) : Prop :=
  ∀ j l m z,
    Work.CR.Flat.dbarCoord j (ζ l m) z - Work.CR.Flat.dbarCoord l (ζ j m) z + Work.CR.Flat.dbarCoord m (ζ j l) z = 0

/-- The `(0,2)`-form is closed on the polydisc `polydisc 0 r`. -/
def IsClosedTwoOn (r : Fin n → ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) : Prop :=
  ∀ j l m z, z ∈ polydisc 0 r →
    Work.CR.Flat.dbarCoord j (ζ l m) z - Work.CR.Flat.dbarCoord l (ζ j m) z + Work.CR.Flat.dbarCoord m (ζ j l) z = 0

/-- The pair `(ψ⁽ᵐ⁾, D⁽ᵐ⁾)` of the `m`-th stage: `D⁽⁰⁾ = ζ`, `ψ⁽ᵐ⁾_l = fiberPot R m (D⁽ᵐ⁾_{m l})`
and `D⁽ᵐ⁺¹⁾_{ij} = D⁽ᵐ⁾_{ij} - (∂̄_i ψ⁽ᵐ⁾_j - ∂̄_j ψ⁽ᵐ⁾_i)`. -/
noncomputable def telPair (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) :
    ℕ → ((Fin n → Cn n → ℂ) × (Fin n → Fin n → Cn n → ℂ))
  | 0 => (fun l z => if h : 0 < n then fiberPot R ⟨0, h⟩ (ζ ⟨0, h⟩ l) z else 0, ζ)
  | m + 1 =>
      let p := telPair R ζ m
      let D' : Fin n → Fin n → Cn n → ℂ :=
        fun i j z => p.2 i j z - (Work.CR.Flat.dbarCoord i (p.1 j) z - Work.CR.Flat.dbarCoord j (p.1 i) z)
      let P' : Fin n → Cn n → ℂ :=
        fun l z => if h : m + 1 < n then fiberPot R ⟨m + 1, h⟩ (D' ⟨m + 1, h⟩ l) z else 0
      (P', D')

/-- The `m`-th stage potential `ψ⁽ᵐ⁾`. -/
noncomputable def telPsi (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) (m : ℕ) : Fin n → Cn n → ℂ :=
  (telPair R ζ m).1

/-- The `m`-th stage defect `D⁽ᵐ⁾`. -/
noncomputable def telD (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) (m : ℕ) :
    Fin n → Fin n → Cn n → ℂ :=
  (telPair R ζ m).2

/-- **The telescoping solution operator** for the `(0,2)`-problem, `telTwo R ζ = Σ_{m<n-1} ψ⁽ᵐ⁾`. -/
noncomputable def telTwo (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) : Fin n → Cn n → ℂ :=
  fun j z => ∑ m ∈ Finset.range (n - 1), telPsi R ζ m j z

@[simp] lemma telD_zero (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) : telD R ζ 0 = ζ := rfl

lemma telD_succ (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) (m : ℕ) :
    telD R ζ (m + 1)
      = fun i j z => telD R ζ m i j z
          - (Work.CR.Flat.dbarCoord i (telPsi R ζ m j) z - Work.CR.Flat.dbarCoord j (telPsi R ζ m i) z) := rfl

lemma telPsi_succ (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) (m : ℕ) :
    telPsi R ζ (m + 1)
      = fun l z => if h : m + 1 < n then fiberPot R ⟨m + 1, h⟩ (telD R ζ (m + 1) ⟨m + 1, h⟩ l) z
          else 0 := rfl

lemma telPsi_zero (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) :
    telPsi R ζ 0
      = fun l z => if h : 0 < n then fiberPot R ⟨0, h⟩ (telD R ζ 0 ⟨0, h⟩ l) z else 0 := rfl

@[simp] lemma telTwo_apply (R : ℝ) (ζ : Fin n → Fin n → Cn n → ℂ) (j : Fin n) (z : Cn n) :
    telTwo R ζ j z = ∑ m ∈ Finset.range (n - 1), telPsi R ζ m j z := rfl

end Work.NN.Core

/-
# The sharp (density-free) mass form of the dual--difference interchange

This module sets up the *sharp* form of Peluse's Lemma 7.4 (the "dual--difference interchange"):
the cube of the average controls the average of the cubes, with **no** `(D/L)`-loss in the
constants.

## The objects

For a finite family `G : Z → ℤ → ℂ` of `1`-bounded functions, each supported (up to a translation)
in `symIcc L`, a set `H` of shift pairs with coordinates in `[1,D]`, a phase function `φ` on the
pairs, a level `σ ≥ 1` and a normaliser `B ≥ L + σ * D`:

* `hypoMass σ B G H φ` is the **hypothesis mass**: the sum over `p ∈ H` of the squared moduli of
  the `B⁻¹`-normalised correlations of the level-`σ` cube term of the *average* `E_z G z` at the
  phase `φ p`;
* `concMass σ D B G H φ` is the **conclusion mass**: the sum over `k ∈ □_σ(H) = ThetaSet σ D H` of
  the squared moduli of the `B⁻¹`-normalised correlations of the average (over `z`) of the level-`σ`
  cube terms of the *slices* `G z`, at the cube-difference phase `ψ(k) = mixedPhase φ k`.

## The statement

`SharpMassDDI σ` says: there is `C > 0` (depending only on `σ`) with

  `(hypoMass)^(2^σ) / (C * D^(σ * (2^(σ+1) - 3))) ≤ concMass`.

The exponent `2^σ` on the hypothesis mass and the `D`-exponent `σ * (2^(σ+1) - 3)` are *sharp*:
they are exactly what the `σ`-fold Cauchy--Schwarz chain produces, and they are exactly what is
needed to pass from the mass form to the pointwise form `HasInterchangeEnergy`
(`Work.Peluse.Ulower.StepLe.blindInterchangeEnergy`), whose concluding constant is a power of
`η * γ` only.

The statement is proved by induction on `σ`:
* `σ = 1` is the Gram/energy argument (`ddiSharp_one`), giving `d_1 = 1`;
* the step `σ → σ+1` (`ddiSharp/step`) peels the first coordinate, applies the `σ`-instance to the
  row families and the `1`-instance to the column families, and bookkeeps the exponents:
  `d_{σ+1} = 2 d_σ + 2^(σ+2) + 3σ - 3`, whose solution is `d_σ = σ * (2^(σ+1) - 3)`.

## Pointers for the `σ = 1` case (`ddiSharp_one`)

The argument is the Gram/energy ("Frobenius") argument in a Hilbert space, and it is already
carried out twice in this workspace:

* `Work.Peluse.Ulower.StepLe.energyStepLe` (`StepLe/denseAvgInterchangeMachinery.lean`) is the
  abstract inequality `(∑_i ‖⟪v_i,w⟫‖^2)^2 ≤ (∑_{i,j}‖⟪v_i,v_j⟫‖^2) * ‖w‖^4`;
* `Work.Peluse.Tools.energy_lemma_fd` is the same inequality in a slightly different packaging;
* `Submission/Work/Peluse/Ulower/rowGram_bound.lean` (`rowGram_bound`, `rowGram_gen'`) is the
  level-`1` row Gram bound already written in the `cubeTerm`/`∑'` vocabulary of this file;
* `Submission/Work/Peluse/Ulower/dualDiffInterchange_one.lean` is a complete (sorry-free) proof of
  the *same* `σ = 1` statement in the `L`-normalised form with the averaged hypothesis — its
  internal chain gives exactly the mass inequality `concMass ≥ (hypoMass)^2 / (9 * D)` (see the
  step `hGlb : η^2 * |H|^2 * L^2 / (D * (2L+1)^2) ≤ gramMass` together with
  `η * |H| ≤ rowMass`).  Adapting it to the `B`-normalisation of this file (where `B ≥ L + D`,
  so that `(2L+1)^2 / B^2 ≤ 9`) is the recommended route.

The row decomposition is `H = ⊔_{a ∈ [1,D]} {a} × R_a` with `R_a = thetaFibre D H a`,
`ThetaSet 1 D H = ⊔_a {a} × R_a × R_a`, the per-row energy inequality is
`(∑_{b ∈ R_a} ‖c_b‖^2)^2 ≤ 9 * ∑_{u,v ∈ R_a × R_a} ‖d_{a,u,v}‖^2` (with `‖w_a‖^2 ≤ 3` for the
test vector `w_a = B⁻¹ * conj (E_z G z (· + a))`), and Cauchy--Schwarz over the rows
(`(∑_a m_a)^2 ≤ D * ∑_a m_a^2`) gives `hypoMass^2 ≤ 9 * D * concMass`.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindInterchangeDefs
import Submission.Work.Peluse.Ulower.thetaDefs
import Submission.Work.Peluse.Ulower.sliceDef
import Submission.Work.Peluse.Tools.energy_lemma_fd
import Submission.Work.Peluse.Ulower.cubeTerm_tail

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

open Work.Peluse


/-- The **row fibre** of a level-`(σ+1)` set of shift pairs at the first coordinates `(a,b)`: the
level-`σ` pairs `(h,h')` with `(Fin.cons a h, Fin.cons b h') ∈ H`. -/
def rowFibre (σ D : ℕ) (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ))) (a b : ℤ) :
    Finset ((Fin σ → ℤ) × (Fin σ → ℤ)) :=
  (Work.Peluse.Ulower.thetaBox σ D ×ˢ Work.Peluse.Ulower.thetaBox σ D).filter
    (fun p => (Fin.cons a p.1, Fin.cons b p.2) ∈ H)

/-- The **column fibre** of a level-`(σ+1)` set of shift pairs at a level-`σ` triple `k'`: the
one-dimensional pairs `(c,u)` with `k' ∈ □_σ(rowFibre H c u)`. -/
def colFibre (σ D : ℕ) (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    (k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :
    Finset ((Fin 1 → ℤ) × (Fin 1 → ℤ)) :=
  (Work.Peluse.Ulower.thetaBox 1 D ×ˢ Work.Peluse.Ulower.thetaBox 1 D).filter
    (fun ab => k' ∈ Work.Peluse.Ulower.ThetaSet σ D
      (rowFibre σ D H (ab.1 0) (ab.2 0)))

/-- The **hypothesis mass** of the level-`σ` interchange: the sum over `p ∈ H` of the squared
moduli of the `B⁻¹`-normalised correlations of the level-`σ` cube term of the average `E_z G z`
at the phase `φ p.1 p.2`. -/
def hypoMass (σ B : ℕ) {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)))
    (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) : ℝ :=
  ∑ p ∈ H, ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
      Work.Peluse.cubeTerm p.1 p.2
        (fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) x *
      Complex.exp (2 * Real.pi * Complex.I * (φ p.1 p.2 : ℂ) * (x : ℂ))‖ ^ 2

/-- The **conclusion mass** of the level-`σ` interchange: the sum over the cube set
`□_σ(H) = ThetaSet σ D H` of the squared moduli of the `B⁻¹`-normalised correlations of the
average over `z` of the level-`σ` cube terms of the slices, at the cube-difference phase
`mixedPhase φ k`. -/
def concMass (σ D B : ℕ) {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ)
    (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)))
    (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) : ℝ :=
  ∑ k ∈ Work.Peluse.Ulower.ThetaSet σ D H, ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
      ((Fintype.card Z : ℂ))⁻¹ * ∑ z, Work.Peluse.cubeTerm k.2.1 k.2.2 (G z) x *
      Complex.exp (2 * Real.pi * Complex.I * ((mixedPhase φ k : ℝ) : ℂ) * (x : ℂ))‖ ^ 2

/-- The **sharp mass form of the dual--difference interchange** at level `σ`: there is a constant
`C > 0` with `(hypoMass)^(2^σ) ≤ C * D^(σ(2^(σ+1)-3)) * concMass` for all data. -/
def SharpMassDDI (σ : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {L D B : ℕ}, 1 ≤ L → 1 ≤ D → L + σ * D ≤ B →
    ∀ {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ),
      (∀ z x, ‖G z x‖ ≤ 1) →
      (∀ z, ∃ c₀ : ℤ, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → G z (x + c₀) = 0) →
    ∀ (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)))
      (φ : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ),
      (∀ p ∈ H, ∀ i : Fin σ, p.1 i ∈ Finset.Icc (1 : ℤ) (D : ℤ) ∧
        p.2 i ∈ Finset.Icc (1 : ℤ) (D : ℤ)) →
      C⁻¹ * (hypoMass σ B G H φ) ^ (2 ^ σ) / ((D : ℝ) ^ (σ * (2 ^ (σ + 1) - 3)))
        ≤ concMass σ D B G H φ

end

end Work.Peluse.Ulower.StepLe

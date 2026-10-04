import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.pdVec_pair_eq_lambda

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the operator `Q_k` — the `k`-th power of the *flat* Laplacian lifted to sections

`D.Rper i h a b` is the periodisation of the localised component `D.R i h a b = ψ i · √dens i · mat`,
and `D.ENormB_pair k h h'` is the `Hᵏ` pairing

  `Σ_i Σ_{ab} Σ_{l : Fin k → Fin n} L2re (∂^l (Rper i h a b)) (∂^l (Rper i h' a b))`.

By the Parseval identity `Work.Diff.STE.B3.pdVec_pair_eq_lambda` this is

  `Σ_i Σ_{ab} L2re (Λ^k (Rper i h a b)) (Rper i h' a b)`,   `Λ^k` = multiplier with symbol
  `λ(m)^k`, `λ(m) = Σᵢ (2π mᵢ)²`,

i.e. the single pairing against the *flat* Laplacian power, instead of the sum over the `k`-fold
multi-indices.

`Qk D k h` is that multiplier lifted back to a section: the section whose `i`-th component function
is `Λ^k (R i h)`, namely `Σ_i Rstar i (Λ^k (R i h))`.  Its role is that

  `D.ENormB_pair k h h' = D.BPair (Qk D k h) h'`

(proved in `Submission/Work/Diff/STE/B3/ENormB_eq_BPair_Qk.lean`): by the adjunction
`BPair_Rstar`, `D.BPair (D.Rstar i u) h' = CPair i u (D.R i h')`, so the pairing of `Qk D k h` with
`h'` sees exactly the components `Λ^k (R i h)` — *not* the components of `Qk D k h` itself, which
are `Σ_j L_{ij} (Λ^k (R j h))` and are different in general (`L_{ij} = R i ∘ Rstar j` is the chart
transfer; the identity `BPair_Rstar` bypasses components).  With `D.J ρ ε = Σ_i Rstar i (S_ε (R i ·))`
the estimate of `Work.Diff.STE.B3.ENormB_pair_J_commutator` therefore becomes the *commutator*
statement

  `|D.BPair ([Qk D k, D.J ρ ε] f) u| ≤ C √(ENormB (k-1) f + ENormB 0 f) √(ENormB k u)`,

`Qk` being of order `2k` and `D.J ρ ε` of order `0`.
-/

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The symbol of the flat Laplacian**, `λ(m) = Σᵢ (2π mᵢ)²`. -/
noncomputable def lamSym (m : Fin (Module.finrank ℝ E) → ℤ) : ℝ :=
  ∑ j, (2 * Real.pi * (m j : ℝ)) ^ 2

/-- **The `k`-th power of the flat Laplacian, lifted to sections**: the section whose `i`-th
component function is `Λ^k (R i h)`, i.e. the Fourier multiplier with symbol `λ(m)^k` applied to
the periodisation `D.Rper i h a b`. -/
noncomputable def Qk (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Bil (I := I) (M := M)) : Bil (I := I) (M := M) :=
  ∑ i : ι₀, D.Rstar i (fun (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) =>
    (Work.Diff.STE.seriesFun (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ((lamSym (E := E) m ^ k : ℝ) : ℂ) *
        Work.Diff.STE.fourierCoeff (D.Rper i h a b) m) z).re)

@[simp] lemma lamSym_apply (m : Fin (Module.finrank ℝ E) → ℤ) :
    lamSym (E := E) m = ∑ j, (2 * Real.pi * (m j : ℝ)) ^ 2 := rfl

end Work.Diff.STE.B3

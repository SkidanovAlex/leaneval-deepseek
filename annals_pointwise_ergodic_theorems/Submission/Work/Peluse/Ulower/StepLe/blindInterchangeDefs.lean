/-
# Vocabulary of the exchange step (`Work.Peluse.Ulower.StepLe.blindInterchange`)

## The statement to be proved here (`StepLe/blindInterchange.blindInterchange`)

```
theorem blindInterchange {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    ∀ σ : ℕ, 1 ≤ σ → ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (K₀ : ℝ), 1 ≤ K₀ →
      ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ)
        (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
        (H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) {γ η : ℝ},
        1 ≤ N → 1 ≤ Ns → Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ K₀ * (Ns : ℝ) →
        SupportIn f₀ Ns → SupportIn f₁ Ns →
        (∀ x, ‖f₀ x‖ ≤ 1) → (∀ x, ‖f₁ x‖ ≤ 1) →
        dSup P Ns N + 2 * σ * D ≤ B →
        0 < γ → 0 < η → η ≤ 1 →
        H₁ ⊆ pairBox σ D →
        γ * (D : ℝ) ^ (2 * σ) ≤ (H₁.card : ℝ) →
        (∀ p ∈ H₁, η ≤ cubeAmp B (dualFn N P f₀ f₁) β p.1 p.2) →
        ∃ H₂ ⊆ ThetaSet σ D H₁,
          c * (η * γ) ^ K * ((ThetaSet σ D H₁).card : ℝ) ≤ (H₂.card : ℝ) ∧
          ∀ k ∈ H₂, c * (η * γ) ^ K ≤
            ‖(B : ℂ)⁻¹ * ∑' x, sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
              Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖
```

This is Peluse's Lemma 7.4 (arXiv:1909.00309 §7; = Peluse--Prendiville arXiv:1903.02592 Lemma 6.3)
in the parametrisation of `blindConvertK`, with the *sharp* (density-free) constants: the density
`γ` is measured inside the *shift* box `[1,D]^{2σ}` and the conclusion's level is a power of `ηγ`
only.  That sharpness is essential: in `blindConvertK` the phase `γ` there is this density (up to
constants), and any loss `(D/L)^{c}` in `L =` the support scale of `F` would make the final bound
of `blindConvertK` `c γ^{K'} (D/B)^{c'}` -- not a power of `γ`, which the target's constant may not
depend on.  (The `(D/L)`-losses in the sibling `dualDiffInterchange` / `lemma74_denseSet` are
harmless for the `StepLe` chain -- there `γ` already carries powers of `D/Ns` -- but not here.)

### Route (all of it already built in this directory)

* `σ = 1` is the Gram/energy argument: `Submission/Work/Peluse/Ulower/StepLe/
  denseAvgInterchangeMachinery.energyStepLe` (PROVED) is the abstract inequality
  `(∑_i ‖⟨v_i,w⟩‖²)² ≤ (∑_{i,j}‖⟨v_i,v_j⟩‖²) ‖w‖⁴`; with the slice family `G_z`,
  `v_b(z,x) = e(-β(a,b)x) star (G_z(x+b))`, `W_a(z,x) = star (F(x+a))` (independent of `z`) one has
  `⟨v_b, W_a⟩ = |Z| L ·` (the hypothesis's object at `(a,b)`) and
  `⟨v_u, v_v⟩ = |Z| L ·` (the conclusion's object at `(a,u,v)`), while
  `‖W_a‖² ≤ |Z| (2Nsup+1)`; running `energyStepLe` row by row in the first coordinate `a` and then
  Cauchy--Schwarz over `a` gives `∑_{k ∈ Θ} ‖concl k‖² ≥ (η²|H₁|)²/(4D)` with
  `|Θ_σ(H₁)| ≤ D |H₁|`-type bookkeeping, i.e. an average `≳ (ηγ)^4` over `Θ_1(H₁)`; Markov (with the
  pointwise bound `‖concl‖ ≤ (2B+1)/B`) turns this into the per-element statement.
  The files `denseAvgInterchangeOne{Defs,Basic,Gram,GramHyp,Support,Support2,Trans,Sesq}.lean`
  contain the `σ = 1` vocabulary (`famZ`, `famY`, `famV`, `famW`, `famGramHyp`), and
  `Submission/Work/Peluse/Ulower/dualDiffInterchange.lean` contains the *same* `σ = 1` argument in
  the abstract `□`-form (`absorption_identity`, `energy_lemma_fd`).
* the induction step peels one coordinate (`dualDiffInterchange.cubeTerm_tail`,
  `Submission/Work/Peluse/Ulower/StepLe/blindConvertK_lowrank` has the mixture combinatorics): the
  paper's Cauchy--Schwarz doubling, applied coordinate by coordinate; the *sharp* bookkeeping is
  what has to be redone relative to `lemma74_denseSet`/`dualDiffInterchange`, which compare `|H|`
  with `L^{2σ}` (hence their `(D/L)`-losses) instead of with `D^{2σ}`.


`cubeAmp` is the bare (`B⁻¹`-normalised) correlation of the level-`σ` cube term of `F` at a
shift pair and a phase (`cubeCorr` is its square); `sliceDual` is the dual function of the
*differenced* inputs at a shift pair (the object of the conclusion of Peluse's Lemma 7.4);
`mixedPhase` is the cube difference `∑_ω (-1)^{|ω|} β k.1 (ω ? k.2.1 : k.2.2)` of the phase `β`
at a triple, in the mixture convention of `ThetaSet`/`cubeTerm`.
-/

import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Peluse.Ulower.iterDefs
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_front

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- The bare (`B⁻¹`-normalised) correlation of the level-`σ` cube term of `F` at the pair `(u,v)`
and the phase `β u v` (the modulus of the summand of `cubeCorr`). -/
def cubeAmp {σ : ℕ} (B : ℕ) (F : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) : ℝ :=
  ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
    Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖

lemma cubeAmp_sq {σ : ℕ} (B : ℕ) (F : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) :
    cubeAmp B F β u v ^ 2 = cubeCorr σ B F β u v := rfl

/-- The slice dual function of the exchange: the iterated `Δ'`-difference of the *inputs* `f₀,f₁`
at the shift pair `sh`, fed to `dualFn`. -/
def sliceDual (σ N : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (sh : Fin σ → ℤ × ℤ) : ℤ → ℂ :=
  Work.Peluse.dualFn N P (Work.Peluse.Ulower.iterDelta' σ sh f₀)
    (Work.Peluse.Ulower.iterDelta' σ sh f₁)

/-- The cube difference of the phase `β` at the triple `k = (k.1,k.2.1,k.2.2)`:
`∑_ω (-1)^{|ω|} β k.1 (ω ? k.2.1 : k.2.2)`, the mixture convention of `ThetaSet`/`cubeTerm`. -/
def mixedPhase {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) : ℝ :=
  ∑ ω : Fin σ → Bool, (-1 : ℝ) ^ Work.Peluse.weight ω *
    β k.1 (fun i => if ω i = true then k.2.1 i else k.2.2 i)

end

end Work.Peluse.Ulower.StepLe

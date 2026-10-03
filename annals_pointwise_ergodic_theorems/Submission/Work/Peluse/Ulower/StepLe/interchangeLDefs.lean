/-
# The *lossy* form of the dual--difference interchange (Peluse's Lemma 7.4 with `L = B`)

`blindConvertK` (`Work.Peluse.Ulower.StepLe.blindConvertK`, and the version used by `steple_of`,
`Work.Peluse.Ulower.StepLe.blindConvertK2`) needs an *interchange* input: from a lower bound on the
cube-correlations of the *average* `F = E_z G_z` on a dense set `H₁` of shift pairs, produce a lower
bound on the cube-correlations of the *slices* `G_z` at the mixed phases on a dense subset of
`ThetaSet σ D H₁` (Peluse, arXiv:1909.00309, Lemma 7.4).

The statement consumed by the existing assembly `StepLe/blindConvertK_main.blindConvertK_of` is
`HasInterchange` (`StepLe/blindConvertK_main.lean`), which is the **sharp** form: the conclusion's
level is a power of `η γ` only, with the density `γ` measured in the *shift* box `[1,D]^{2σ}` and
*no* loss.  The paper proves only the **lossy** form — Lemma 7.4 is fed the density
`γ' = |H₁| / L^{2σ}` with `L` the *support* radius, so with `L = B` the level is a power of
`η γ D/B` — and the `(D/L)`-loss is exactly the `(δδ')^{O(1)}`-loss of Peluse's Lemma 3.9.  The
sharp form is a strict strengthening (the `σ = 1` energy argument gives it, but for `σ ≥ 2` the
paper's Cauchy--Schwarz chain carries the loss and the "per-fibre" reorganisation that would remove
it is not proved anywhere).

This module defines the lossy predicate `HasInterchangeL`, so that

* `blindConvertK2` (the version of the middle step with the `(D/Ns)`-loss, which is what
  `steple_of` consumes) can be assembled from `HasInterchangeL` instead of `HasInterchange`, and
* `HasInterchangeL` can be *proved* from the workspace's `Work.Peluse.Ulower.ss74.lemma74Dense`
  (`ss74/lemma74Dense.lean`), i.e. from the paper's Lemma 7.4 as it is actually proved.

The bridge `hasInterchangeL_of_lemma74Dense` is in `StepLe/hasInterchangeL.lean`.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.blindInterchangeDefs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

open Work.Peluse

/-- **The lossy dual--difference interchange.**  Same as `HasInterchange` (Peluse's Lemma 7.4 with
the `B⁻¹`-normalisation and the `cubeAmp`/`sliceDual` vocabulary of `blindInterchangeDefs`), except
that the conclusion's density and level carry the extra factor `(D/B)^{Ki}` — the loss of the
paper's proof, which is fed the *support* density `|H₁|/B^{2σ}` instead of the shift-box density
`|H₁|/D^{2σ}`.  Since `B ≥ dSup P Ns N + 2σD ≥ Ns`, this is weaker than the sharp form and is
exactly what `ss74.lemma74Dense` gives (with `L := B`).

The parameter `K₀` bounds `D/Ns`; the constant `c` may depend on it (which is why it sits before the
existential quantifiers). -/
def HasInterchangeL (P : Polynomial ℤ) : Prop :=
  ∀ σ : ℕ, 1 ≤ σ → ∀ K₀ : ℝ, 1 ≤ K₀ →
  ∃ c : ℝ, 0 < c ∧ ∃ Ki : ℕ, 1 ≤ Ki ∧
    ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ)
      (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
      (H₁ : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) {γ η : ℝ},
      1 ≤ N → 1 ≤ Ns → Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns →
      1 ≤ D → (D : ℝ) ≤ K₀ * (Ns : ℝ) →
      Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
      Work.Peluse.dSup P Ns N + 2 * σ * D ≤ B →
      0 < γ → 0 < η → η ≤ 1 →
      H₁ ⊆ pairBox σ D →
      γ * (D : ℝ) ^ (2 * σ) ≤ (H₁.card : ℝ) →
      (∀ p ∈ H₁, η ≤ cubeAmp B (Work.Peluse.dualFn N P f₀ f₁) β p.1 p.2) →
      ∃ H₂ ⊆ Work.Peluse.Ulower.ThetaSet σ D H₁,
        c * (η * γ * ((D : ℝ) / (B : ℝ))) ^ Ki *
            ((Work.Peluse.Ulower.ThetaSet σ D H₁).card : ℝ) ≤ (H₂.card : ℝ) ∧
        ∀ k ∈ H₂, c * (η * γ * ((D : ℝ) / (B : ℝ))) ^ Ki ≤
          ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
            sliceDual σ N P f₀ f₁ (fun i => (k.2.1 i, k.2.2 i)) x *
              Complex.exp (2 * Real.pi * Complex.I * (mixedPhase β k : ℂ) * (x : ℂ))‖

end

end Work.Peluse.Ulower.StepLe

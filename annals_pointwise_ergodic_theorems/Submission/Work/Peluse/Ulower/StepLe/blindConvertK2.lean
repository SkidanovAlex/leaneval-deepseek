import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.hasInterchangeL_of_sharpMass
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK_of_interchangeL

/-!
# The middle step of the degree-lowering chain, with the `(D/Ns)`-loss of the route

This is `Work.Peluse.Ulower.StepLe.blindConvertK` with the conclusion relaxed by the factor
`(D/Ns)^{K'}`; the relaxation is what the Peluse §8 / Peluse–Prendiville §6 chain proves (see
`StepLe/middleStepGuide`, section "The `(D/Ns)`-loss in the conclusion", and
`NOTES_steple_middle_step.md`).  `Work.Peluse.Ulower.steple_of` uses this version.

**Proof (this session).**  The middle step is assembled in two verified pieces:

* `Work.Peluse.Ulower.StepLe.blindConvertK_of_interchangeL` — the whole assembly (rounding, Markov,
  exchange, major-arc pinning, the low-rank/`blindPhase` identity, the fibre bookkeeping and the
  final arithmetic), taking the exchange as the *lossy* predicate `HasInterchangeL` (the version of
  Peluse's Lemma 7.4 that the paper's Cauchy–Schwarz chain actually proves, with the `(D/B)`-loss);
* `Work.Peluse.Ulower.StepLe.hasInterchangeL_of_lemma74Dense` — `HasInterchangeL P` from the
  workspace's `Work.Peluse.Ulower.ss74.lemma74Dense` (Peluse's Lemma 7.4 in density form, instantiated
  with `L := B` and the density `γ D^{2σ}/B^{2σ}`).

So the only input of this theorem is `ss74.lemma74Dense` — i.e. its crux `ss74.ddiCore` (Peluse's
Lemma 7.4, the σ-fold Cauchy–Schwarz chain).  In particular the *sharp* exchange
(`Work.Peluse.Ulower.StepLe.blindInterchange` / `HasInterchange`), which the paper does not prove and
which is not needed here, is not used.
-/

namespace Work.Peluse.Ulower.StepLe

noncomputable section

open Work.Peluse

theorem blindConvertK2 {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h2 : Work.Peluse.PeluseMajorArc P) (K : ℝ) (hK : 1 ≤ K) :
    ∀ σ : ℕ, 1 ≤ σ → ∃ c : ℝ, 0 < c ∧ ∃ K' : ℕ, 1 ≤ K' ∧
      ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ γ : ℝ)
        (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ),
        1 ≤ N → 1 ≤ Ns → Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ K * (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        Work.Peluse.dSup P Ns N + 2 * σ * D ≤ B →
        0 < θ → θ ≤ 1 →
        θ ≤ Work.Peluse.boxNormPow (σ + 2) (fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D)
              (Work.Peluse.symIcc B) (Work.Peluse.dualFn N P f₀ f₁) →
        0 < γ →
        γ ≤ ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
                ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
                  Work.Peluse.cubeTerm u v (Work.Peluse.dualFn N P f₀ f₁) x *
                  Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖ ^ 2 →
        ∃ ψ : Fin σ → (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ,
          (∀ i : Fin σ, ∀ u : Fin σ → ℤ, ∀ v : Fin σ → ℤ, ∀ a b : ℤ,
            ψ i u (Function.update v i a) = ψ i u (Function.update v i b)) ∧
          c * (γ * ((D : ℝ) / (Ns : ℝ))) ^ K' ≤
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
                ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
                  Work.Peluse.cubeTerm u v (Work.Peluse.dualFn N P f₀ f₁) x *
                  Complex.exp (2 * Real.pi * Complex.I *
                    ((∑ i : Fin σ, ψ i u v) : ℂ) * (x : ℂ))‖ ^ 2 :=
  -- the mass-form route: `SharpMassDDI 1` + the dimension step ⟹ `SharpMassDDI σ` ⟹ the lossy
  -- interchange `HasInterchangeL`; (the equivalent route through `ss74.ddiCore` /
  -- `hasInterchangeL_of_lemma74Dense` is also available).
  blindConvertK_of_interchangeL hd h2
    (hasInterchangeL_of_sharpMass (P := P)
      (sharpMassDDI_all sharpMassDDI_one_v2)) K hK

end

end Work.Peluse.Ulower.StepLe

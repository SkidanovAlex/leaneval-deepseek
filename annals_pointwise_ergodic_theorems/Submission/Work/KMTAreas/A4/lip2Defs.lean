/-
# Shared definitions for Proposition `lip-2` (the alternate inverse theorem for `g`)

This module fixes the vocabulary shared by the main file `Work.KMTAreas.A4.lip2` and the
delegated lemmas about it (the smoothing-window package, the inverse Weyl estimate, the
major-arc extraction, and the Plancherel identity for windowed polynomial averages).

## The objects

* `arcSet α r` — the closed arc of the frequency circle of centre `α` and radius `r`, the
  single-arc version of `majorArc ρ l k`;
* `win M θ` — the *normalized reproducing window*
  `m ↦ (1/M) ψ(m/M) e(-m θ)`, where `ψ = lipSchPsi = 𝓕⁻ lipSchChi` is the inverse Fourier
  transform of the bump `lipSchChi` (equal to `1` on `[-1/2,1/2]` and vanishing off `(-1,1)`).
  Its Fourier transform is `winFT M θ` (see `Work.KMTAreas.A4.lip2Kernel`);
* `winSum M θ s ξ` — the windowed exponential sum `∑_n win M θ (n - s) e(-ξ P(n))` which the
  inverse Weyl estimate of `Work.KMTAreas.A4.lip2Weyl` inverts.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.peluseLipUniform

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Single arcs -/

/-- The closed arc of the frequency circle `ℝ/ℤ` with centre `α` and radius `r`: the set of
frequencies at distance at most `r` from `α`.  `majorArc ρ l k` is the union of the arcs
`arcSet α ((2:ℝ)^k)` over the arithmetic frequencies `α ∈ iwArithFreqs ρ l`. -/
def arcSet (α : FreqCircle) (r : ℝ) : Set FreqCircle :=
  {γ | ∃ θ : ℝ, |θ| ≤ r ∧ γ = α + ((θ : ℝ) : FreqCircle)}

theorem mem_arcSet {α γ : FreqCircle} {r : ℝ} :
    γ ∈ arcSet α r ↔ ∃ θ : ℝ, |θ| ≤ r ∧ γ = α + ((θ : ℝ) : FreqCircle) := Iff.rfl

/-- `arcSet α r` is monotone in the radius. -/
theorem arcSet_mono_radius {α : FreqCircle} {r r' : ℝ} (h : r ≤ r') :
    arcSet α r ⊆ arcSet α r' := by
  rintro γ ⟨θ, hθ, rfl⟩
  exact ⟨θ, hθ.trans h, rfl⟩

/-- Membership of a *coerced real* frequency in an arc around the same real frequency. -/
theorem coe_mem_arcSet {θ r : ℝ} (hr : 0 ≤ r) :
    ((θ : ℝ) : FreqCircle) ∈ arcSet ((θ : ℝ) : FreqCircle) r :=
  ⟨0, by simp only [abs_zero]; linarith, by simp⟩

/-- A single arc around an arithmetic frequency is contained in the major arcs of the
corresponding scales. -/
theorem arcSet_subset_majorArc {ρ : ℝ} {l : ℕ} {k : ℤ} {α : FreqCircle} {r : ℝ}
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) (hr : r ≤ (2 : ℝ) ^ k) :
    arcSet α r ⊆ majorArc ρ l k := by
  rintro γ ⟨θ, hθ, rfl⟩
  exact ⟨α, hα, θ, ⟨by linarith [neg_abs_le θ, abs_le.mp hθ], by linarith [abs_le.mp hθ]⟩, rfl⟩

/-! ## The reproducing window -/

/-- The normalized reproducing window of width `M` and modulation `γ`:
`win M γ m = (1/M) ψ(m/M) e(m γ)`, `ψ = lipSchPsi`.  Its `ℤ`-Fourier transform is `1` on the
arc of radius `1/(2M)` around `γ` and is non-negative everywhere, so it is a reproducing kernel
for functions whose `ℤ`-Fourier transform is supported in an arc of radius `1/(4M)` around
`γ` (see `Work.KMTAreas.A4.lip2Kernel` and `Work.KMTAreas.A4.lip2Reproduce`). -/
noncomputable def win (M : ℝ) (γ : FreqCircle) : ℤ → ℂ :=
  fun m => ((M : ℂ)⁻¹) * lipSchPsi ((m : ℝ) / M) * (fourier m γ : ℂ)

/-- The Fourier transform of the window `win M γ`, as a function of a *real* frequency:
`winFT M s t = ∑_n lipSchChi (M (t - s + n))`, where `s` is a real representative of `γ`. -/
noncomputable def winFT (M s : ℝ) : ℝ → ℂ :=
  fun t => ∑' n : ℤ, lipSchChi (M * (t - s + (n : ℝ)))

/-- The windowed exponential sum `winSum M γ ξ P s = ∑_n win M γ (n - s) e(ξ P(n))` of the
phase `n ↦ ξ P(n)`.  This is the multiplier of the windowed polynomial average
`x ↦ ∑_n win M γ (n - s) g (x + P(n))` (see `Work.KMTAreas.A4.lip2Plancherel`), and the object
inverted by the inverse Weyl estimate of `Work.KMTAreas.A4.lip2Weyl`. -/
noncomputable def winSum (M : ℝ) (γ : FreqCircle) (ξ : ℝ) (P : Polynomial ℤ) (s : ℤ) : ℂ :=
  ∑' n : ℤ, win M γ (n - s) *
    Complex.exp (2 * Real.pi * Complex.I * (ξ * (P.eval n : ℤ) : ℝ))

/-- The same windowed exponential sum, but restricted to an interval `[a,b]` of integers.  The
bilinear average of `Work.Analysis.InverseTheory.AhalfZ` only involves the *upper half*
`Ioc (N/2) N = Icc (N/2+1) N` of the shifts, so the inverse Weyl estimate and the Plancherel
identity have to be available in this interval-restricted form. -/
noncomputable def winSumIcc (M : ℝ) (γ : FreqCircle) (ξ : ℝ) (P : Polynomial ℤ) (s : ℤ)
    (a b : ℤ) : ℂ :=
  ∑ n ∈ Finset.Icc a b, win M γ (n - s) *
    Complex.exp (2 * Real.pi * Complex.I * (ξ * (P.eval n : ℤ) : ℝ))

/-! ## The refined inverse-theorem input for Proposition `lip-2`

`Work.KMTAreas.A4.peluseLipUniform` (Proposition `lip` of §5) reports the Fourier support of its
output as `majorArc ρ l k`.  That set is a union of arcs over `iwArithFreqs ρ l`, a set of
*super-polynomially* many arithmetic frequencies (`iwP ρ l` contains `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`
as a factor), so the support statement is far too coarse to extract a *single* arc from with a
`δ^{-O(1)}` loss, which is what the reproduction step of `lip-2` needs.

The proof of Proposition `lip`, however, establishes the much finer fact that the output is
supported in the union of the `q` arcs of radius `ε/q` around the `q`-torsion points `a/q`, where
`q` is the modulus produced by Peluse's inverse theorem and satisfies `q ≲ δ^{-O(1)}`.  The
predicate below records that finer conclusion (together with the `Summable` conjunct, which
`peluseLipUniform` does not state and which makes the `ℓ¹` bound non-vacuous). -/
def LipL1Fine (P : Polynomial ℤ) : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      ∃ (F : ℤ → ℂ) (k : ℤ) (A : Finset FreqCircle),
        (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
        Summable (fun x : ℤ => ‖F x‖) ∧
        (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
        FourierSupportIn F (⋃ α ∈ (A : Set FreqCircle), arcSet α ((2 : ℝ) ^ k)) ∧
        (A.card : ℝ) ≤ C * δ⁻¹ ^ K ∧
        (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

end Work.KMTAreas.A4

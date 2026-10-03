import Mathlib
import Submission.Work.Peluse.UlowerA.ssHasInterchangeLU
import Submission.Work.Peluse.UlowerA.blindConvertK_of_interchangeLU

/-!
# The middle step of the degree-lowering chain, `A`-version

A namespace-local copy of `Work.Peluse.UlowerA.blindConvertKA2` (same statement), used to with the
balanced scale hypothesis `Scaled Ns N P.natDegree` replaced by the unbalanced relation
`UnbalScale P C Ns N` (both halves with the single constant `C`); the constant `c` of the
conclusion may depend on `C`.  It is the wrapper of `blindConvertK_of_interchangeLU` that supplies
the (scale-agnostic) interchange from `SharpMassDDI`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower.SsA

noncomputable section

theorem ssBlindConvert {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h2 : Work.Peluse.PeluseMajorArc P)
    (K : ℝ) (hK : 1 ≤ K) :
    ∀ C : ℕ, 1 ≤ C → ∀ σ : ℕ, 1 ≤ σ → ∃ c : ℝ, 0 < c ∧ ∃ K' : ℕ, 1 ≤ K' ∧
      ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ γ : ℝ)
        (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ),
        1 ≤ N → 1 ≤ Ns → Work.Peluse.UlowerA.UnbalScale P C Ns N → N ≤ Ns →
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
  Work.Peluse.Ulower.StepLe.blindConvertK_of_interchangeLU hd h2
    (fun C hC => Work.Peluse.UlowerA.hasInterchangeLU
      (Work.Peluse.Ulower.StepLe.sharpMassDDI_all
        Work.Peluse.Ulower.StepLe.sharpMassDDI_one_v2) C hC) K hK

end

end Work.Peluse.Ulower.SsA

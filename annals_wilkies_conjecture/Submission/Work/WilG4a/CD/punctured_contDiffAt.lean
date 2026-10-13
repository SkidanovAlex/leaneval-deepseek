import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.CD.hasDerivAt_of_tendsto_deriv

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace Work.WilG4a.CD

/-- The punctured `ε`-`δ` condition `hcont` of the target statement is exactly continuity at `c`:
the case `x = c` of the standard formulation is trivial. -/
private lemma continuousAt_of_punctured (F : ℝ → ℝ) (c ρ : ℝ)
    (h : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ → |F x - F c| < ε) :
    ContinuousAt F c := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, -, hδp⟩ := h ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hxc : x = c
  · subst hxc; simpa using hε
  · rw [Real.dist_eq] at hx ⊢
    exact hδp x hxc hx

/-- Composing with the linear isometry `ℝ ≃ (ℝ →L[ℝ] ℝ)` given by `v ↦ v • (1 : ℝ →L[ℝ] ℝ)`
preserves `ContDiffAt`; used to turn `ContDiffAt` of `deriv F` into `ContDiffAt` of the derivative
function appearing in the Fréchet formulation of `C^(n+1)`. -/
private lemma contDiffAt_toSpanSingleton (F : ℝ → ℝ) (n : ℕ) (c : ℝ)
    (h : ContDiffAt ℝ n (deriv F) c) :
    ContDiffAt ℝ n (fun x => ContinuousLinearMap.toSpanSingleton ℝ (deriv F x)) c := by
  let e : ℝ ≃ₗᵢ[ℝ] (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
  have hcoe : ⇑e = fun v => ContinuousLinearMap.toSpanSingleton ℝ v := by
    funext v; rw [ContinuousLinearMap.toSpanSingletonLIE_apply]
  have hcmp : (fun x => ContinuousLinearMap.toSpanSingleton ℝ (deriv F x)) = e ∘ deriv F := by
    funext x; rw [Function.comp_apply, hcoe]
  rw [hcmp]
  exact ContDiffAt.comp c (e.contDiff.contDiffAt) h

/-- The statement of the target, with the exponent a variable, proved by strong induction on the
order. Step `j = 0` is continuity; step `j = n+1` uses the mean value theorem to see that `F` is
differentiable at `c` with derivative the limit `L₁` of `deriv F`, applies the induction
hypothesis to `deriv F` (which is the honest derivative of `F` on the punctured neighbourhood),
and then reassembles `C^{n+1}` from `F` differentiable on a neighbourhood together with
`ContDiffAt ℝ n (deriv F) c` via `contDiffAt_succ_iff_hasFDerivAt`. -/
private theorem punctured_contDiffAt_aux (j : ℕ) :
    ∀ (F : ℝ → ℝ) (c : ℝ) (ρ : ℝ), 0 < ρ →
      (∀ x ∈ Set.Ioo (c - ρ) (c + ρ), x ≠ c → ContDiffAt ℝ j F x) →
      (∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ → |F x - F c| < ε) →
      (∀ m : ℕ, 1 ≤ m → m ≤ j → ∃ L : ℝ,
        ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ →
          |iteratedDeriv m F x - L| < ε) →
      ContDiffAt ℝ j F c := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro F c ρ hρ hF hcont hlim
    rcases j with _ | n
    · -- `j = 0`: `F` is continuous on the whole interval, since it is `C^0` at every punctured
      -- point and continuous at `c`.
      rw [show ((0 : ℕ) : ℕ∞ω) = 0 from by simp, contDiffAt_zero]
      refine ⟨Set.Ioo (c - ρ) (c + ρ), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      intro y hy
      rcases eq_or_ne y c with hyc | hyne
      · rw [hyc]; exact (continuousAt_of_punctured F c ρ hcont).continuousWithinAt
      · exact (hF y hy hyne).continuousAt.continuousWithinAt
    · -- `j = n + 1`
      obtain ⟨L1, hL1⟩ := hlim 1 (le_refl 1) (by omega)
      have hL1' : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ →
          |deriv F x - L1| < ε := by
        intro ε hε
        obtain ⟨δ, hδ, hδρ, hδp⟩ := hL1 ε hε
        exact ⟨δ, hδ, hδρ, fun x hx hxd => by
          simpa only [iteratedDeriv_one] using hδp x hx hxd⟩
      -- Step 1: `F` is differentiable at `c`, with derivative `L1`.
      have hHasDeriv : HasDerivAt F L1 c :=
        hasDerivAt_of_tendsto_deriv F c L1 ρ hρ
          (fun x hx hxne => (hF x hx hxne).differentiableAt (by simp))
          hcont hL1'
      -- Step 2: `deriv F` satisfies the induction hypotheses at order `n`.
      have hF' : ∀ x ∈ Set.Ioo (c - ρ) (c + ρ), x ≠ c → ContDiffAt ℝ n (deriv F) x :=
        fun x hx hxne => (hF x hx hxne).derivWithin (by simp)
      have hcont' : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ →
          |deriv F x - deriv F c| < ε := by
        intro ε hε
        obtain ⟨δ, hδ, hδρ, hδp⟩ := hL1' ε hε
        refine ⟨δ, hδ, hδρ, fun x hx hxd => ?_⟩
        simpa [hHasDeriv.deriv] using hδp x hx hxd
      have hlim' : ∀ m : ℕ, 1 ≤ m → m ≤ n → ∃ L : ℝ,
          ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ →
            |iteratedDeriv m (deriv F) x - L| < ε := by
        intro m hm1 hmn
        obtain ⟨L, hL⟩ := hlim (m + 1) (by omega) (by omega)
        refine ⟨L, fun ε hε => ?_⟩
        obtain ⟨δ, hδ, hδρ, hδp⟩ := hL ε hε
        refine ⟨δ, hδ, hδρ, fun x hx hxd => ?_⟩
        have hs : iteratedDeriv m (deriv F) = iteratedDeriv (m + 1) F :=
          (iteratedDeriv_succ' (n := m) (f := F)).symm
        simp only [hs]
        exact hδp x hx hxd
      have hderivCD : ContDiffAt ℝ n (deriv F) c :=
        ih n (by omega) (deriv F) c ρ hρ hF' hcont' hlim'
      -- Step 3: reassemble `C^{n+1}` at `c` from differentiability on a neighbourhood and
      -- `C^n`-ness of the honest derivative.
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 from by norm_num]
      refine (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := F) (x := c) (n := n)).mpr ?_
      refine ⟨fun x => ContinuousLinearMap.toSpanSingleton ℝ (deriv F x), ?_, ?_⟩
      · refine ⟨Set.Ioo (c - ρ) (c + ρ), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
        have hderiv_all : ∀ x ∈ Set.Ioo (c - ρ) (c + ρ), HasDerivAt F (deriv F x) x := by
          intro x hx
          rcases eq_or_ne x c with hxc | hxne
          · rw [hxc]
            rw [hHasDeriv.deriv]; exact hHasDeriv
          · exact ((hF x hx hxne).differentiableAt (by simp)).hasDerivAt
        exact fun x hx => (hderiv_all x hx).hasFDerivAt
      · exact contDiffAt_toSpanSingleton F n c hderivCD

/-- If `F` is `C^j` on a punctured neighbourhood of `c`, tends to `F c` there, and the
`m`-th iterated derivatives (`1 ≤ m ≤ j`) have finite limits along the punctured
neighbourhood, then `F` is `C^j` at `c`. -/
theorem punctured_contDiffAt (F : ℝ → ℝ) (c : ℝ) (j : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hF : ∀ x ∈ Set.Ioo (c - ρ) (c + ρ), x ≠ c → ContDiffAt ℝ j F x)
    (hcont : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ → |F x - F c| < ε)
    (hlim : ∀ m : ℕ, 1 ≤ m → m ≤ j → ∃ L : ℝ,
      ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ →
        |iteratedDeriv m F x - L| < ε) :
    ContDiffAt ℝ j F c :=
  punctured_contDiffAt_aux j F c ρ hρ hF hcont hlim

end Work.WilG4a.CD

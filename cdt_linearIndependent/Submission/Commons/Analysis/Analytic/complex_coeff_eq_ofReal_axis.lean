import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# Taylor coefficients along the real axis

If a complex-analytic function `g : ℂ → ℂ` agrees with a real-analytic
function `f : ℝ → ℝ` on a neighbourhood of `0` (on the real axis), then the
`n`-th Taylor coefficient of `g` at `0` (a complex number) equals the `n`-th
Taylor coefficient of `f` at `0`, viewed as a complex number.

## Proof sketch

Both functions are analytic, so (via `AnalyticAt.hasFPowerSeriesAt`) each is
represented near `0` by the formal multilinear series built from its iterated
derivatives: `g` over `ℂ`, and `f` over `ℝ`.  Restrict scalars of `g`'s series
to `ℝ` and precompose with the real embedding `Complex.ofRealCLM`, and
postcompose `f`'s series with that same embedding.  Both resulting series live
in `FormalMultilinearSeries ℝ ℝ ℂ` and represent (near `0`) the two functions
`x ↦ g x` and `x ↦ f x` taking values in `ℂ`.  Since these two functions agree
in a neighbourhood of `0`, the formal series are equal
(`HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`); comparing their
`n`-th coefficients gives the claim.
-/

noncomputable section

namespace Commons.Analysis.Analytic

open scoped Topology

lemma complex_coeff_eq_ofReal_axis {g : ℂ → ℂ} {f : ℝ → ℝ}
    (hg : AnalyticAt ℂ g 0) (hf : AnalyticAt ℝ f 0)
    (heq : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), g (x : ℂ) = (f x : ℂ)) (n : ℕ) :
    iteratedDeriv (𝕜 := ℂ) n g 0 / (n.factorial : ℂ) =
      (iteratedDeriv (𝕜 := ℝ) n f 0 / (n.factorial : ℝ) : ℂ) := by
  -- Coefficients of `g` (complex) and of `f` (real).
  let c : ℕ → ℂ := fun n => iteratedDeriv (𝕜 := ℂ) n g 0 / (n.factorial : ℂ)
  let b : ℕ → ℝ := fun n => iteratedDeriv (𝕜 := ℝ) n f 0 / (n.factorial : ℝ)
  -- Formal power series of `g` at `0`, from analyticity.
  let p_g : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hp_g : HasFPowerSeriesAt g p_g 0 := by
    simpa [p_g, c] using (AnalyticAt.hasFPowerSeriesAt (𝕜 := ℂ) (f := g) (x := 0) hg)
  -- Restrict scalars to `ℝ` and pull back along the real embedding.
  let p₁ : FormalMultilinearSeries ℝ ℝ ℂ :=
    (p_g.restrictScalars ℝ).compContinuousLinearMap Complex.ofRealCLM
  have hp_gR : HasFPowerSeriesAt g (p_g.restrictScalars ℝ) 0 := by
    exact HasFPowerSeriesAt.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ) hp_g
  have hp₁ : HasFPowerSeriesAt (g ∘ ⇑Complex.ofRealCLM) p₁ 0 := by
    simpa [p₁] using (hp_gR.compContinuousLinearMap (u := Complex.ofRealCLM) (x := (0 : ℝ)))
  -- Formal power series of `f` at `0`, pushed through the real embedding.
  let p_f : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ b
  have hp_f : HasFPowerSeriesAt f p_f 0 := by
    simpa [p_f, b] using (AnalyticAt.hasFPowerSeriesAt (𝕜 := ℝ) (f := f) (x := 0) hf)
  let p₂ : FormalMultilinearSeries ℝ ℝ ℂ :=
    Complex.ofRealCLM.compFormalMultilinearSeries p_f
  have hp₂ : HasFPowerSeriesAt (⇑Complex.ofRealCLM ∘ f) p₂ 0 := by
    rcases hp_f with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa [p₂] using (Complex.ofRealCLM.comp_hasFPowerSeriesOnBall hr)
  -- The two real-valued-in-`ℂ` functions agree near `0`.
  have heq' : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
      (g ∘ ⇑Complex.ofRealCLM) x = (⇑Complex.ofRealCLM ∘ f) x := by
    filter_upwards [heq] with x hx
    simpa using hx
  -- Uniqueness of formal power series: same function, same coefficients.
  have h_eq : p₁ = p₂ := by
    exact HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hp₁ hp₂ heq'
  have heval : p₁ n (fun _ : Fin n => (1 : ℝ)) = p₂ n (fun _ : Fin n => (1 : ℝ)) := by
    rw [h_eq]
  -- The `n`-th coefficient of `p₁` is `c n`.
  have hs1 : p₁ n (fun _ : Fin n => (1 : ℝ)) = c n := by
    change ((p_g.restrictScalars ℝ).compContinuousLinearMap Complex.ofRealCLM) n
      (fun _ : Fin n => (1 : ℝ)) = c n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    change (p_g.restrictScalars ℝ) n (fun _ : Fin n => ⇑Complex.ofRealCLM (1 : ℝ)) = c n
    change p_g n (fun _ : Fin n => ⇑Complex.ofRealCLM (1 : ℝ)) = c n
    change (FormalMultilinearSeries.ofScalars ℂ c) n (fun _ : Fin n => (1 : ℂ)) = c n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp
  -- The `n`-th coefficient of `p₂` is `(b n : ℂ)`.
  have hs2 : p₂ n (fun _ : Fin n => (1 : ℝ)) = (b n : ℂ) := by
    change (Complex.ofRealCLM.compFormalMultilinearSeries p_f) n (fun _ : Fin n => (1 : ℝ)) =
      (b n : ℂ)
    rw [ContinuousLinearMap.compFormalMultilinearSeries_apply']
    change Complex.ofRealCLM
      ((FormalMultilinearSeries.ofScalars ℝ b) n (fun _ : Fin n => (1 : ℝ))) = (b n : ℂ)
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp
  have hfinal : c n = (b n : ℂ) := by
    rw [← hs1, ← hs2]
    exact heval
  simpa [c, b, Complex.ofReal_div] using hfinal

end Commons.Analysis.Analytic

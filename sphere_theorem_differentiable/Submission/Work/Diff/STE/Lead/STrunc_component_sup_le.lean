import Mathlib
import Submission.Work.Diff.STE.Lead.R_abs_le
import Submission.Work.Diff.STE.Lead.STruncR_sup_le
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-- The Friedrichs truncation of a localised component of a section `X` which is pointwise
dominated by `K √(g₀(u,u)) √(g₀(v,v))` is bounded uniformly: for every `ε ∈ (0,1]`, every chart
`i`, every `(a,b)` and every flat coordinate `z`, `|STruncR ρ ε (D.R i X a b) z| ≤ C * K` for a
constant `C ≥ 0` independent of `ε`, `X`, `K`, `i`, `a`, `b`, `z`. -/
theorem STrunc_component_sup_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ENat) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
      (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ) (hK : 0 ≤ K),
      (∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ),
        |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z| ≤ C * K := by
  -- The Friedrichs truncation is bounded on `L^∞` (`STruncR_sup_le`), and the localised component
  -- is bounded by `√Cdens * K` (`R_abs_le`, with the uniform upper bound `Cdens` for the chart
  -- densities provided by `dens_bound_sigma`) and supported in the open unit cube
  -- (`B3Data.R_support`).
  obtain ⟨C₀, hC₀, hstl⟩ := STruncR_sup_le (E := E) ρ hρ hρ0 hρs
  obtain ⟨c, Cd, hc, hCd, hdens⟩ :=
    Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
  refine ⟨C₀ * Real.sqrt Cd, mul_nonneg hC₀ (Real.sqrt_nonneg _), ?_⟩
  intro ε hε X K hK hbound i a b z
  have hR : ∀ w : Fin (Module.finrank ℝ E) → ℝ, |D.R i X a b w| ≤ Real.sqrt Cd * K :=
    R_abs_le D X K Cd hK hCd (fun i z hz => (hdens i z hz).2) hbound i a b
  have hmain := hstl ε hε (D.R i X a b) (Real.sqrt Cd * K)
    (mul_nonneg (Real.sqrt_nonneg _) hK) hR (D.R_support i X a b) z
  calc |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z|
      ≤ C₀ * (Real.sqrt Cd * K) := hmain
    _ = C₀ * Real.sqrt Cd * K := by ring

end Work.Diff.STE.Lead

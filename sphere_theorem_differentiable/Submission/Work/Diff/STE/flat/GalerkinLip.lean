/-
# The nonlinearity composed with the explicit jet is Lipschitz near the initial datum

Since `Φ` is smooth on the open set where the metric matrix is invertible, and the explicit jet
`jetExp` is smooth, the composite `p ↦ Φ (jetExp p.1 p.2)` is `C¹` on the compact convex set
`closedBall a₀ r ×ˢ closedCube n`, hence Lipschitz there (compactness + convexity).  The radius `r`
is the one supplied by `exists_radius_det_ne_zero`, which keeps the jet inside the domain of `Φ`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.flat.GalerkinSmooth
import Submission.Work.Diff.STE.flat.GalerkinJet
import Submission.Work.Diff.STE.flat.exists_radius_det_ne_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

namespace Flat

namespace Galerkin

noncomputable section

open scoped BigOperators Topology NNReal

/-- **Lipschitz property of `Φ ∘ jetExp` near the initial datum.**  There are a radius `r > 0` and
a constant `K` such that `p ↦ Φ (jetExp p.1 p.2)` is `K`-Lipschitz on
`closedBall a₀ r ×ˢ closedCube n`. -/
theorem Phi_jetExp_lipschitz {n N : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}))
    (a₀ : Coeff n N)
    (hdet : ∀ x ∈ closedCube n, (reMat (valExp a₀ x)).det ≠ 0) :
    ∃ K : ℝ≥0, ∃ r : ℝ≥0, 0 < r ∧ LipschitzOnWith K
      (fun p : Coeff n N × (Fin n → ℝ) => Φ (p.2, jetExp p.1 p.2))
      (Metric.closedBall a₀ (r : ℝ) ×ˢ closedCube n) := by
  obtain ⟨r₀, hr₀, hdet'⟩ := Work.Diff.STE.flat.exists_radius_det_ne_zero a₀ hdet
  have hconv : Convex ℝ (Metric.closedBall a₀ r₀ ×ˢ closedCube n) :=
    (convex_closedBall a₀ r₀).prod (convex_pi (fun _ _ => convex_Icc _ _))
  have hcomp : IsCompact (Metric.closedBall a₀ r₀ ×ˢ closedCube n) :=
    (isCompact_closedBall a₀ r₀).prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Coeff n N × (Fin n → ℝ) => (p.2, jetExp p.1 p.2)) :=
    (contDiff_prod_iff (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (f := fun p : Coeff n N × (Fin n → ℝ) => (p.2, jetExp p.1 p.2))).mpr
      ⟨by simpa [Function.comp_def] using (contDiff_snd (𝕜 := ℝ) (E := Coeff n N)
          (F := Fin n → ℝ)),
       by simpa [Function.comp_def] using (contDiff_jetExp (n := n) (N := N)).of_le le_top⟩
  have hmaps : Set.MapsTo (fun p : Coeff n N × (Fin n → ℝ) => (p.2, jetExp p.1 p.2))
      (Metric.closedBall a₀ r₀ ×ˢ closedCube n)
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}) := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and]
    exact hdet' a ha x hx
  have hcomp' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Coeff n N × (Fin n → ℝ) => Φ (p.2, jetExp p.1 p.2))
      (Metric.closedBall a₀ r₀ ×ˢ closedCube n) := by
    have h := hΦ.comp (hpair.contDiffOn
      (s := Metric.closedBall a₀ r₀ ×ˢ closedCube n)) hmaps
    simpa only [Function.comp_def] using h
  obtain ⟨K, hK⟩ := hcomp'.exists_lipschitzOnWith (by simp) hconv hcomp
  exact ⟨K, ⟨r₀, le_of_lt hr₀⟩, NNReal.coe_pos.mp hr₀, hK⟩

end

end Galerkin

end Flat

end Work.Diff.STE

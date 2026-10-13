import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs

namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

/-- The parametrisation `belowPhi s j` of the below cell is continuous on `belowH`, as soon as the
sheet `s j` is continuous on the base cell `C = π_p (connectedComponentIn Z.set u₀)`.

Indeed `belowPhi s j q = belowPt q.1 (s j (π_p q.1)) q.2` is built out of `q.1`, `q.2` and the
composition `s j ∘ π_p ∘ fst` (which is continuous on `belowH` because `belowH` projects into `C`,
hypothesis `hC`).  This is the exact analogue of `continuousOn_bandPhi` for the below cell. -/
theorem belowPhi_continuous {p m k : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hcont : ContinuousOn (s j) C) :
    ContinuousOn (Work.WilE7.BelowAux.belowPhi s j)
      (Work.WilE7.BelowAux.belowH Z s j u₀) := by
  -- the two structural coordinates of the domain
  have hfst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => q.1)
      (belowH Z s j u₀) := continuous_fst.continuousOn
  -- the base projection `q ↦ π_p q.1`
  have hpi : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      projFirst p (m + 1) q.1) (belowH Z s j u₀) :=
    (Work.WilE7.continuous_projFirst p (m + 1)).comp_continuousOn hfst
  -- `belowH` projects into the base cell `C`
  have hmap : ∀ q ∈ belowH Z s j u₀, projFirst p (m + 1) q.1 ∈ C := by
    intro q hq
    rw [belowH] at hq
    rw [hC]
    exact ⟨q.1, hq.1, rfl⟩
  -- hence the sheet `s j`, read through `π_p ∘ fst`, is continuous on `belowH`
  have hsj : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      s j (projFirst p (m + 1) q.1)) (belowH Z s j u₀) :=
    hcont.comp hpi hmap
  -- the second block `Fin.append (π_p q.1) (s j (π_p q.1))`
  have hA : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)))
      (belowH Z s j u₀) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp_continuousOn (hpi.prodMk hsj)
  -- both blocks glued: `Fin.append q.1 (Fin.append (π_p q.1) (s j (π_p q.1)))`
  have hp1 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1))))
      (belowH Z s j u₀) :=
    (Fin.continuous_append (X := ℝ) (p + (m + 1)) (p + (m + 1))).comp_continuousOn
      (hfst.prodMk hA)
  -- the vertical coordinate as a `Fin 1 → ℝ` function of `q`
  have hconst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      (fun _ : Fin 1 => q.2)) (belowH Z s j u₀) :=
    (continuous_pi (fun _ => continuous_snd)).continuousOn
  have hfin := (Fin.continuous_append (X := ℝ) (belowK p m) 1).comp_continuousOn
      (hp1.prodMk hconst)
  show ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
        (s j (projFirst p (m + 1) q.1)))) (fun _ : Fin 1 => q.2)) (belowH Z s j u₀)
  exact hfin

end Work.WilE7.BelowAux

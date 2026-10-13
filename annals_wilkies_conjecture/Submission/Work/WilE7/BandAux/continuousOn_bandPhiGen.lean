import Mathlib
import Submission.Work.WilE7.BandAux.bandCoverTwo_defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

/-- The parametrisation `bandPhiGen g₁ g₂ q = bandPt q.1 (g₁ (π q.1)) (g₂ (π q.1)) q.2` of the
two-strata band is continuous on any `A` whose base projection lies in `C`, as soon as both sheet
maps `g₁`, `g₂` are continuous on `C`.

Indeed `bandPt u v v' t` is a single `Fin.append` of `u`, `v`, `v'` and `t` glued through the base
projection `π = projFirst p (m+1)`, and each of those is either a projection (`q ↦ q.1`, `q ↦ q.2`)
or the composition `g_i ∘ π ∘ fst` (continuous on `A` because `A` projects into `C`, hypothesis
`hA`).  This is the exact two-sheet analogue of `continuousOn_bandPhi`. -/
theorem continuousOn_bandPhiGen {p m : ℕ} {C : Set (Fin p → ℝ)}
    {A : Set ((Fin (p + (m + 1)) → ℝ) × ℝ)}
    (hA : ∀ q ∈ A, WilkiesDesign.E.projFirst p (m + 1) q.1 ∈ C)
    {g₁ g₂ : (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hg₁ : ContinuousOn g₁ C) (hg₂ : ContinuousOn g₂ C) :
    ContinuousOn (Work.WilE7.BandAux.bandPhiGen g₁ g₂) A := by
  -- the two structural coordinates of the domain
  have hfst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => q.1) A :=
    continuous_fst.continuousOn
  -- the base projection `q ↦ π_p q.1`
  have hpi : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      projFirst p (m + 1) q.1) A :=
    (continuous_projFirst p (m + 1)).comp_continuousOn hfst
  -- the two sheet maps, read through `π_p ∘ fst`, are continuous on `A`
  have hg₁' : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      g₁ (projFirst p (m + 1) q.1)) A := hg₁.comp hpi hA
  have hg₂' : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      g₂ (projFirst p (m + 1) q.1)) A := hg₂.comp hpi hA
  -- the second block `Fin.append (π_p q.1) (g₁ (π_p q.1))`
  have hB₁ : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (projFirst p (m + 1) q.1) (g₁ (projFirst p (m + 1) q.1))) A :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp_continuousOn (hpi.prodMk hg₁')
  -- the fourth block `Fin.append (π_p q.1) (g₂ (π_p q.1))`
  have hB₂ : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (projFirst p (m + 1) q.1) (g₂ (projFirst p (m + 1) q.1))) A :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp_continuousOn (hpi.prodMk hg₂')
  -- first + second block: `Fin.append q.1 (Fin.append (π_p q.1) (g₁ (π_p q.1)))`
  have hp1 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
        (g₁ (projFirst p (m + 1) q.1)))) A :=
    (Fin.continuous_append (X := ℝ) (p + (m + 1)) (p + (m + 1))).comp_continuousOn
      (hfst.prodMk hB₁)
  -- third + fourth block: `Fin.append q.1 (Fin.append (π_p q.1) (g₂ (π_p q.1)))`
  have hp2 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
        (g₂ (projFirst p (m + 1) q.1)))) A :=
    (Fin.continuous_append (X := ℝ) (p + (m + 1)) (p + (m + 1))).comp_continuousOn
      (hfst.prodMk hB₂)
  -- the four space blocks glued
  have hfirst4 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append
        (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
          (g₁ (projFirst p (m + 1) q.1))))
        (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
          (g₂ (projFirst p (m + 1) q.1))))) A :=
    (Fin.continuous_append (X := ℝ) ((p + (m + 1)) + (p + (m + 1)))
      ((p + (m + 1)) + (p + (m + 1)))).comp_continuousOn (hp1.prodMk hp2)
  -- the vertical coordinate as a `Fin 1 → ℝ` function of `q`
  have hconst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      (fun _ : Fin 1 => q.2)) A :=
    (continuous_pi (fun _ => continuous_snd)).continuousOn
  -- glue the vertical coordinate to the four space blocks
  have hfin := (Fin.continuous_append (X := ℝ) (bandK p m) 1).comp_continuousOn
    (hfirst4.prodMk hconst)
  -- this is exactly `bandPhiGen g₁ g₂`
  show ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (Fin.append (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
        (g₁ (projFirst p (m + 1) q.1)))) (Fin.append q.1
          (Fin.append (projFirst p (m + 1) q.1) (g₂ (projFirst p (m + 1) q.1)))))
        (fun _ : Fin 1 => q.2)) A
  exact hfin

end Work.WilE7.BandAux

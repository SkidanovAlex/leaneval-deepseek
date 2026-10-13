/-
  WilG3 — the affine interval cover of BNZ (arXiv 2202.05305, §5.1), proved as
  `G3_affine_cover_proved` for the frozen statement `WilkieDesign.CG.G3_affine_cover` in
  `Submission/Work/Wilkies/CG/Spec.lean`.

  Assembly: the witness family is the geometric chart family `Work.WilG3.geoCharts` of
  `Submission/Work/WilG3/Defs.lean`, with the number of scales `Work.WilG3.geoK`.  The three
  conjuncts are the delegated lemmas `GeoChartsCard` (count), `GeoChartsSpec` (chart geometry)
  and `GeoChartsCovers` (covering), the last one using `GeoKReaches` (the scales reach `ε`).
-/
import Submission.Work.WilG3.Defs
import Submission.Work.WilG3.GeoChartsCard
import Submission.Work.WilG3.GeoChartsSpec
import Submission.Work.WilG3.GeoKReaches
import Submission.Work.WilG3.GeoChartsCovers

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign.CG

open WilkiesDesign

/-- **G3b: the Whitney-type affine cover of `[ε, 1-ε]`.** Each interval `[u,v]` has length at
most `dist([u,v], {0,1})/(r+1)`, so G3a applies to every affine chart of it. -/
theorem G3_affine_cover_proved (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
      (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧
        (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧
      Set.Icc ε (1 - ε) ⊆ ⋃ p ∈ s, Set.Icc p.1 p.2 := by
  have hK : 1 ≤ Work.WilG3.geoK r ε := by
    simp only [Work.WilG3.geoK]
    omega
  refine ⟨Work.WilG3.geoCharts r (Work.WilG3.geoK r ε),
    Work.WilG3.GeoChartsCard r ε hε hε1,
    Work.WilG3.GeoChartsSpec r (Work.WilG3.geoK r ε), ?_⟩
  exact Work.WilG3.GeoChartsCovers r (Work.WilG3.geoK r ε) hK hε
    (Work.WilG3.GeoKReaches r ε hε hε1)

end WilkiesDesign.CG

namespace Work.WilG3

/-- Alias of `WilkieDesign.CG.G3_affine_cover_proved`, for callers working in `Work.WilG3`. -/
theorem G3_affine_cover_proved (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
      (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧
        (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧
      Set.Icc ε (1 - ε) ⊆ ⋃ p ∈ s, Set.Icc p.1 p.2 :=
  WilkiesDesign.CG.G3_affine_cover_proved r ε hε hε1

end Work.WilG3

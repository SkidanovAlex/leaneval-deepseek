/-
  WilE7 (`Work.WilE7.isClosed_sheetPart`): each piece of the sheet partition of `G` is closed in
  `G`, provided the sheets `s i` are continuous on the base set `C` and `G` projects into `C`.

  The point is that on the subtype `G` the two maps

  `x ↦ projSnd p q (projSnd (p+q) (p+q) x)`      (`σ`, the fibre coordinate) and
  `x ↦ s i (projFirst p q (projSnd (p+q) (p+q) x))`  (`s i` evaluated at the base coordinate)

  are both continuous: the first as a composition of continuous projections, the second because
  `s i` is continuous on `C` and `hG` puts the base coordinate of every point of `G` inside `C`
  (`ContinuousOn.comp_continuous`).  The piece `sheetPart s G i` is exactly the closed set where
  these two continuous maps agree (`isClosed_eq`).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.SheetComponentDefs

namespace Work.WilE7

open WilkiesDesign.E

theorem isClosed_sheetPart {p q k : ℕ} {C : Set (Fin p → ℝ)}
    {G : Set (Fin ((p + q) + (p + q)) → ℝ)} (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ))
    (hcont : ∀ i, ContinuousOn (s i) C)
    (hG : ∀ z ∈ G, WilkiesDesign.E.projFirst p q (WilkiesDesign.E.projSnd (p + q) (p + q) z) ∈ C)
    (i : Fin k) : IsClosed (sheetPart (p := p) (q := q) s G i) := by
  -- the fibre coordinate `σ` is continuous on `G`
  have hσ : Continuous (fun x : G => projSnd p q (projSnd (p + q) (p + q) x.1)) :=
    (continuous_projSnd p q).comp
      ((continuous_projSnd (p + q) (p + q)).comp continuous_subtype_val)
  -- the base coordinate is continuous on `G`
  have hπ : Continuous (fun x : G => projFirst p q (projSnd (p + q) (p + q) x.1)) :=
    (continuous_projFirst p q).comp
      ((continuous_projSnd (p + q) (p + q)).comp continuous_subtype_val)
  -- hence so is the sheet value at the base coordinate, by continuity of `s i` on `C`
  have hs : Continuous (fun x : G => s i (projFirst p q (projSnd (p + q) (p + q) x.1))) :=
    (hcont i).comp_continuous hπ (fun x => hG x.1 x.2)
  have hset : sheetPart (p := p) (q := q) s G i =
      {x : G | projSnd p q (projSnd (p + q) (p + q) x.1) =
        s i (projFirst p q (projSnd (p + q) (p + q) x.1))} := rfl
  rw [hset]
  exact isClosed_eq hσ hs

end Work.WilE7

import Mathlib
import Submission.Work.Stems.subsingleton_of_contractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Trivial homotopy groups of a space admitting a contraction

If `Y` carries a continuous map `H : Y × I → Y` with `H (y, 0) = y` and `H (y, 1) = b`
for a fixed point `b`, then `Y` is contractible (`ContinuousMap.id Y` is nullhomotopic),
so by `Work.Stems.subsingleton_of_contractible` every homotopy group of `Y` is a
subsingleton.
-/

namespace Work.Stems

/-- A space admitting a contraction to a point has trivial homotopy groups. -/
theorem subsingleton_of_contraction {Y : Type*} [TopologicalSpace Y] (b : Y)
    (H : C(Y × unitInterval, Y)) (h0 : ∀ y, H (y, 0) = y) (h1 : ∀ y, H (y, 1) = b)
    (d : ℕ) : ∀ y : Y, Subsingleton (HomotopyGroup (Fin d) Y y) := by
  haveI : ContractibleSpace Y := by
    refine (contractible_iff_id_nullhomotopic Y).mpr ⟨b, ⟨?_⟩⟩
    refine { toFun := fun p : unitInterval × Y => H (p.2, p.1)
             continuous_toFun := H.continuous.comp (continuous_snd.prodMk continuous_fst)
             map_zero_left := fun y => h0 y
             map_one_left := fun y => h1 y }
  exact fun y => subsingleton_of_contractible (N := Fin d) y

end Work.Stems

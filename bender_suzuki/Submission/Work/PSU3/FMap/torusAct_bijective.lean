import Mathlib
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.FMap

/-- `torusAct a⁻¹` is a left inverse of `torusAct a` on `SZ E`: the two diagonal
factors `a` and `a · σa` involved in `(x,y) ↦ (a x, a·σa · y)` are inverted by
their inverses, which are nonzero in a field.  This is the computational content
of the bijectivity of the torus action. -/
lemma torusAct_inv_torusAct {E : Type*} [Field E] [FrobeniusInvolution E] (a : Eˣ) (p : SZ E) :
    SZ.torusAct a⁻¹ (SZ.torusAct a p) = p := by
  have ha : (↑a : E) ≠ 0 := Units.ne_zero a
  have hsa : σE (↑a : E) ≠ 0 := fun h => ha (σE.injective (by rw [h, map_zero]))
  ext
  · simp only [SZ.torusAct_x, Units.val_inv_eq_inv_val]
    field_simp
  · simp only [SZ.torusAct_y, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp

theorem torusAct_bijective {E : Type*} [Field E] [FrobeniusInvolution E] (a : Eˣ) :
    Function.Bijective (SZ.torusAct a) := by
  refine ⟨fun p q h => ?_, fun q => ?_⟩
  · rw [← torusAct_inv_torusAct a p, h, torusAct_inv_torusAct a q]
  · exact ⟨SZ.torusAct a⁻¹ q, by simpa using torusAct_inv_torusAct a⁻¹ q⟩

end Work.PSU3.FMap

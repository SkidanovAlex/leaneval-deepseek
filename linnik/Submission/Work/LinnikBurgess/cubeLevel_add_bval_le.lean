import Mathlib
import Submission.Work.LinnikBurgess.lf_defs

namespace Work.LinnikBurgess

/-- The capped valuation `vcap p K x` never exceeds the cap `K`. -/
theorem vcap_le (p K x : ℕ) : vcap p K x ≤ K := by
  unfold vcap
  split
  · exact le_refl _
  · exact min_le_right _ _

/-- `bval` is bounded by the cap level. -/
theorem bval_le_capLevel {p e : ℕ} (a b : Fin 3 → ℕ) (y : ℕ) :
    bval p e a b y ≤ capLevel p e :=
  vcap_le p (capLevel p e) (defect2 p e a b y).val

theorem cubeLevel_add_bval_le {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (y : ℕ) :
    cubeLevel p e + bval p e a b y ≤ e := by
  have hb := bval_le_capLevel (p := p) (e := e) a b y
  have h := cubeLevel_add_capLevel' (p := p) (e := e) hp5 he
  omega

end Work.LinnikBurgess

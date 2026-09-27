import Mathlib
import Submission.Work.Surf.grbDefs
import Submission.Work.Surf.goodRayDefs

/-!
# The boundary curve of the difference map of two chords

The pair model `grbDiff a b = (p ↦ eu (a p.1) - eu (b p.2))` of the difference map of two curves, and
the associated boundary curve `grbCurve a b`, read on the circle through the smooth square
parametrisation `sqPar`.
-/

namespace Work.Surf.GRB

open Set

noncomputable section

/-- The pair model of the difference map of two curves. -/
def grbDiff (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ → ℝ × ℝ :=
  fun p => gEu (a p.1) - gEu (b p.2)

lemma grbDiff_contDiff {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : ContDiff ℝ 1 (grbDiff a b) := by
  unfold grbDiff
  exact (gEu.contDiff.comp (ha.comp contDiff_fst)).sub (gEu.contDiff.comp (hb.comp contDiff_snd))

lemma grbDiff_continuous {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : Continuous (grbDiff a b) := (grbDiff_contDiff ha hb).continuous

/-- The boundary curve of the difference map, as a function on the circle. -/
def grbCurve (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : UnitAddCircle → ℝ × ℝ :=
  AddCircle.liftIco 1 0 (fun u : ℝ => grbDiff a b (sqPar u))

lemma sqPar_add_one' (x : ℝ) : sqPar (x + 1) = sqPar x := sqPar_add_one x

lemma grbCurve_period (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    grbDiff a b (sqPar (u + 1)) = grbDiff a b (sqPar u) := by
  rw [sqPar_add_one]

lemma grbCurve_endpoint (a b : ℝ → EuclideanSpace ℝ (Fin 2)) :
    (fun u : ℝ => grbDiff a b (sqPar u)) 0 = (fun u : ℝ => grbDiff a b (sqPar u)) (0 + 1) := by
  show grbDiff a b (sqPar 0) = grbDiff a b (sqPar (0 + 1))
  rw [zero_add, show (1:ℝ) = 0 + 1 by norm_num, sqPar_add_one]

lemma grbCurve_coe (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    grbCurve a b (u : UnitAddCircle) = grbDiff a b (sqPar u) := by
  have hr : u - (⌊u⌋ : ℝ) ∈ Set.Ico (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le u), by linarith [Int.lt_floor_add_one u]⟩
  have hcoe : ((u : ℝ) : UnitAddCircle) = ((u - (⌊u⌋ : ℝ) : ℝ) : UnitAddCircle) := by
    rw [QuotientAddGroup.eq_iff_sub_mem]
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨⌊u⌋, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    ring
  have hlift : grbCurve a b ((u - (⌊u⌋:ℝ) : ℝ) : UnitAddCircle)
      = grbDiff a b (sqPar (u - (⌊u⌋:ℝ))) := by
    rw [grbCurve]
    exact AddCircle.liftIco_coe_apply (a := (0:ℝ)) (p := (1:ℝ)) (by simpa using hr)
  rw [hcoe, hlift]
  conv_rhs => rw [show u = (u - (⌊u⌋:ℝ)) + (⌊u⌋:ℝ) by ring]
  rw [sqPar_add_intCast]

lemma continuous_grbCurve_coe (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : Continuous fun u : ℝ => grbCurve a b (u : UnitAddCircle) := by
  rw [show (fun u : ℝ => grbCurve a b (u : UnitAddCircle))
      = fun u : ℝ => grbDiff a b (sqPar u) from funext (grbCurve_coe a b)]
  exact (grbDiff_continuous ha hb).comp contDiff_sqPar.continuous

lemma contDiff_grbCurve_coe (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : ContDiff ℝ 1 fun u : ℝ => grbCurve a b (u : UnitAddCircle) := by
  rw [show (fun u : ℝ => grbCurve a b (u : UnitAddCircle))
      = fun u : ℝ => grbDiff a b (sqPar u) from funext (grbCurve_coe a b)]
  exact (grbDiff_contDiff ha hb).comp contDiff_sqPar

lemma continuous_grbDiff_sqPar (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : Continuous fun u : ℝ => grbDiff a b (sqPar u) :=
  (grbDiff_continuous ha hb).comp contDiff_sqPar.continuous

lemma continuous_grbCurve (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) : Continuous (grbCurve a b) :=
  AddCircle.liftIco_continuous (grbCurve_endpoint a b)
    (continuous_grbDiff_sqPar a b ha hb).continuousOn

lemma grbCurve_ne_zero {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    {u : ℝ} : grbCurve a b (u : UnitAddCircle) ≠ 0 := by
  rw [grbCurve_coe]
  intro hzero
  have hmem : sqPar u ∈ Work.Drive.sqBoxBdry := sqPar_mem_sqBoxBdry u
  have heq : gEu (a (sqPar u).1) = gEu (b (sqPar u).2) := sub_eq_zero.mp hzero
  have heq' : a (sqPar u).1 = b (sqPar u).2 := gEu_injective heq
  obtain ⟨hs, ht, -⟩ := hint _ _ hmem.1.1 hmem.1.2 heq'
  rcases hmem.2 with h | h | h | h
  · exact absurd h (ne_of_gt hs.1)
  · exact absurd h (ne_of_lt hs.2)
  · exact absurd h (ne_of_gt ht.1)
  · exact absurd h (ne_of_lt ht.2)

end

end Work.Surf.GRB

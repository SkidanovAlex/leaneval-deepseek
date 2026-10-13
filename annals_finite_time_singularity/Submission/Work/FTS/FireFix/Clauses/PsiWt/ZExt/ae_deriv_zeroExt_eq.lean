import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt.ZExt

theorem ae_deriv_zeroExt_eq (Φ : ℝ → ℝ → ℝ) :
    (fun q : ℝ × ℝ =>
        deriv (fun θ' => (if q.1 ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
          then Φ q.1 θ' else 0)) (|q.2|))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))]
    (fun q : ℝ × ℝ => deriv (Φ q.1) (|q.2|)) := by
  -- The "zero extension" agrees with `Φ q.1` on a neighbourhood of `|q.2|` as soon as
  -- `q.1 ∈ Ioi 0` and `|q.2|` lies in the *interior* `(0, π/2)`.  Off that interior the
  -- only obstruction is the hyperplane `q.2 = 0`, which is null.
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) {q | q.2 = 0} = 0 := by
    have hset : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by
      ext q; simp
    rw [hset, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  have hne' : ∀ᵐ q ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)), q.2 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  have hmem :
      ∀ᵐ q ∂(MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
        q ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    MeasureTheory.ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)
  have hne :
      ∀ᵐ q ∂(MeasureTheory.volume.restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
        q.2 ≠ 0 :=
    MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hne'
  filter_upwards [hmem, hne] with q hq hqne
  have hq1mem : q.1 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (le_of_lt hq.1)
  have habs : |q.2| ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨abs_pos.mpr hqne, abs_lt.mpr ⟨hq.2.1, hq.2.2⟩⟩
  have hev : (fun θ' => (if q.1 ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
          then Φ q.1 θ' else 0)) =ᶠ[nhds (|q.2|)] (Φ q.1) := by
    filter_upwards [isOpen_Ioo.mem_nhds habs] with θ' hθ'
    rw [ite_eq_left ⟨hq1mem, ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩⟩]
  exact hev.deriv_eq

end Work.FTS.FireFix.Clauses.PsiWt.ZExt

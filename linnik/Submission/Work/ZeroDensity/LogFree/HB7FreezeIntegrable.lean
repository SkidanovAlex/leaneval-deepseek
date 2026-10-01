import Mathlib

namespace Work.ZeroDensity.LogFree

open Set MeasureTheory

/-- A point of `uIcc A B` is positive when both `A` and `B` are. -/
lemma hb7_pos_of_mem_uIcc {A B y : ℝ} (hA : 0 < A) (hB : 0 < B) (hy : y ∈ uIcc A B) : 0 < y := by
  rcases Set.mem_uIcc.mp hy with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact lt_of_lt_of_le hA h1
  · exact lt_of_lt_of_le hB h1

/-- On an interval of positive reals, `y ↦ (y : ℂ) ^ c` is continuous: the base stays in
`Complex.slitPlane`. -/
lemma hb7_continuousOn_cpow_of_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (c : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (uIcc A B) :=
  Complex.continuous_ofReal.continuousOn.cpow_const
    (fun _ hy => Complex.ofReal_mem_slitPlane.2 (hb7_pos_of_mem_uIcc hA hB hy))

/-- A finite sum of `z i * (y : ℂ) ^ (c i)` is continuous on an interval of positive reals. -/
lemma hb7_continuousOn_sum_cpow {ι : Type*} [Fintype ι] (z c : ι → ℂ) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    ContinuousOn (fun y : ℝ => ∑ i, z i * (y : ℂ) ^ (c i)) (uIcc A B) := by
  refine continuousOn_finsetSum (Finset.univ : Finset ι) (fun i _ => ?_)
  exact (hb7_continuousOn_cpow_of_pos hA hB (c i)).const_mul (z i)

/-- `‖f y‖ ^ 2 / y` is continuous on an interval of positive reals whenever `f` is. -/
lemma hb7_continuousOn_norm_sq_div {A B : ℝ} (hpos : ∀ y ∈ uIcc A B, 0 < y) (f : ℝ → ℂ)
    (hf : ContinuousOn f (uIcc A B)) :
    ContinuousOn (fun y : ℝ => ‖f y‖ ^ 2 / y) (uIcc A B) :=
  (hf.norm.pow 2).div continuousOn_id (fun y hy => ne_of_gt (hpos y hy))

/-- A finite sum of `z i * ((y / Y) ^ (p i) - 1 : ℝ) * (y : ℂ) ^ (d i)` is continuous on an
interval of positive reals, for `Y > 0`. -/
lemma hb7_continuousOn_sum_rpow_cpow {ι : Type*} [Fintype ι] (z : ι → ℂ) (p : ι → ℝ) (d : ι → ℂ)
    {A B Y : ℝ} (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) :
    ContinuousOn (fun y : ℝ => ∑ i, z i * (((y / Y) ^ (p i) - 1 : ℝ) : ℂ) * (y : ℂ) ^ (d i))
      (uIcc A B) := by
  have hG : ∀ i, ContinuousOn (fun y : ℝ => (((y / Y) ^ (p i) - 1 : ℝ) : ℂ)) (uIcc A B) := by
    intro i
    have hbase : ContinuousOn (fun y : ℝ => y / Y) (uIcc A B) :=
      (continuousOn_id (s := uIcc A B)).div
        (continuousOn_const : ContinuousOn (fun _ : ℝ => Y) (uIcc A B)) (fun _ _ => ne_of_gt hY)
    have h1 : ContinuousOn (fun y : ℝ => (y / Y) ^ (p i)) (uIcc A B) :=
      hbase.rpow_const (fun y hy => Or.inl (ne_of_gt (div_pos (hb7_pos_of_mem_uIcc hA hB hy) hY)))
    have h2 : ContinuousOn (fun y : ℝ => (y / Y) ^ (p i) - 1) (uIcc A B) :=
      h1.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (uIcc A B))
    exact Complex.continuous_ofReal.comp_continuousOn h2
  refine continuousOn_finsetSum (Finset.univ : Finset ι) (fun i _ => ?_)
  exact (continuousOn_const.mul (hG i)).mul (hb7_continuousOn_cpow_of_pos hA hB (d i))

/-- The three integrands occurring in the freeze-block are interval-integrable on
`[Y e^{-L}, Y]` (`Y > 0`): they are continuous there (`‖·‖²/y` of a finite sum of
`const * (y:ℂ)^{c i}`-terms, each continuous on `y > 0`, times a real `rpow` factor). -/
theorem HB7FreezeIntegrable {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ) (Y L : ℝ)
    (hY : 0 < Y) :
    IntervalIntegrable (fun y : ℝ => ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
        volume (Y * Real.exp (-L)) Y
    ∧ IntervalIntegrable (fun y : ℝ => ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
        volume (Y * Real.exp (-L)) Y
    ∧ IntervalIntegrable (fun y : ℝ => ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ) * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
        volume (Y * Real.exp (-L)) Y := by
  have hA : 0 < Y * Real.exp (-L) := mul_pos hY (Real.exp_pos _)
  have hpos : ∀ y ∈ uIcc (Y * Real.exp (-L)) Y, 0 < y :=
    fun y hy => hb7_pos_of_mem_uIcc hA hY hy
  refine ⟨?_, ?_, ?_⟩
  · exact (hb7_continuousOn_norm_sq_div hpos _
      (hb7_continuousOn_sum_cpow z (fun i => (a i : ℂ) - (γ i : ℂ) * Complex.I) hA hY)).intervalIntegrable
  · exact (hb7_continuousOn_norm_sq_div hpos _
      (hb7_continuousOn_sum_cpow (fun i => z i * ((Y ^ (a i) : ℝ) : ℂ))
        (fun i => (-(γ i : ℂ)) * Complex.I) hA hY)).intervalIntegrable
  · exact (hb7_continuousOn_norm_sq_div hpos _
      (hb7_continuousOn_sum_rpow_cpow (fun i => z i * ((Y ^ (a i) : ℝ) : ℂ)) a
        (fun i => (-(γ i : ℂ)) * Complex.I) hA hY hY)).intervalIntegrable

end Work.ZeroDensity.LogFree

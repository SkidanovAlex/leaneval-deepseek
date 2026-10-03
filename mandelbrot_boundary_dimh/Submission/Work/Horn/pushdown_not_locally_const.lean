import Mathlib
import Submission.Work.Horn.germF0_base

namespace Work.Horn

open MandelDim Set Metric Filter

/-- Local constancy descends through `pushdown`: if `E` is `T`-equivariant on the `T`-invariant
set `D`, continuous at `w ∈ D`, and `E` is not locally constant at `w`, then the cylinder map
`pushdown E` is not locally constant at `π w`. -/
theorem pushdown_not_locally_const {E : ℂ → ℂ} {D : Set ℂ} (hD : MandelDim.IsTInvariant D)
    (hE : ∀ u ∈ D, u + 1 ∈ D → E (u + 1) = E u + 1) {w : ℂ} (hw : w ∈ D)
    (hDn : D ∈ nhds w) (hcont : ContinuousAt E w)
    (h : ¬ (∀ᶠ u in nhds w, E u = E w)) :
    ¬ (∀ᶠ ζ in nhds (MandelDim.piExp w),
        MandelDim.pushdown E ζ = MandelDim.pushdown E (MandelDim.piExp w)) := by
  intro hcon
  -- The descent identity `pushdown E (π w) = π (E w)` for the `ℤ`-equivariant lift `E`.
  have hpushw : MandelDim.pushdown E (MandelDim.piExp w) = MandelDim.piExp (E w) :=
    MandelDim.pushdown_piExp hD hE hw
  -- `π = piExp` is continuous, so the local-constancy set of `pushdown E` at `π w` pulls back
  -- to a neighbourhood of `w`.
  have hpi_cont : ContinuousAt (MandelDim.piExp) w := by
    unfold MandelDim.piExp; fun_prop
  have hpre : (MandelDim.piExp) ⁻¹'
      {ζ : ℂ | MandelDim.pushdown E ζ = MandelDim.pushdown E (MandelDim.piExp w)} ∈ nhds w :=
    hpi_cont.preimage_mem_nhds hcon
  have hM : (MandelDim.piExp) ⁻¹'
      {ζ : ℂ | MandelDim.pushdown E ζ = MandelDim.pushdown E (MandelDim.piExp w)} ∩ D ∈ nhds w :=
    inter_mem hpre hDn
  -- Continuity of `E` at `w` confines `E u` to a ball of radius `1/2` around `E w`.
  have hcont'' : {u : ℂ | E u ∈ Metric.ball (E w) (1/2)} ∈ nhds w :=
    hcont.preimage_mem_nhds (Metric.ball_mem_nhds (E w) (by norm_num))
  -- It suffices to show `E =ᶠ E w` near `w`, contradicting `h`.
  refine h ?_
  refine Filter.mem_of_superset (Filter.inter_mem hM hcont'') ?_
  intro u hu
  obtain ⟨⟨huS, huD⟩, hball⟩ := hu
  simp only [Set.mem_ofPred_eq] at hball ⊢
  -- Descent identity at `u`, plus the local-constancy membership, gives `π (E u) = π (E w)`.
  have h1 : MandelDim.pushdown E (MandelDim.piExp u) = MandelDim.piExp (E u) :=
    MandelDim.pushdown_piExp hD hE huD
  have hkey : MandelDim.piExp (E u) = MandelDim.piExp (E w) := by
    rw [← h1, huS, hpushw]
  -- Hence `E u = E w + k` for some integer `k`; the `1/2`-closeness forces `k = 0`.
  obtain ⟨k, hk⟩ := MandelDim.piExp_eq_iff.mp hkey
  have hnorm : ‖E u - E w‖ < 1/2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hball
    exact hball
  rw [hk, add_sub_cancel_left] at hnorm
  have hk0 : k = 0 := by
    rw [Complex.norm_intCast] at hnorm
    have h1' : ((|k| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]; linarith
    have h2 : |k| < 1 := by exact_mod_cast h1'
    exact Int.abs_lt_one_iff.mp h2
  rw [hk, hk0, Int.cast_zero, add_zero]

end Work.Horn

import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

open MeasureTheory Set Filter

/-- **Window (sliding-interval) bound.**  For `f ≥ 0` continuous on the window `[a, b+h]`,
the average of the sliding-window integrals `∫_z^{z+h} f` over `z ∈ [a,b]` is at most `h`
times the total mass of `f` over `[a, b+h]`.

Proof: substitute `u = z + v` in the inner integral (`v ∈ [0,h]`), so that the left-hand
side becomes `∫_v (∫_z f (z+v))`; this is a genuine rectangle, so Tonelli applies.  For each
fixed `v ∈ [0,h]` the inner integral is `∫_u in (a+v)..(b+v), f u ≤ ∫_u in a..(b+h), f u`,
because `f ≥ 0` and `[a+v, b+v] ⊆ [a, b+h]`.  Finally `∫_v in 0..h, C = C * h` for a
constant `C`, and `∫ ≤ ‖∫‖` for free. -/
theorem window_bound {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a (b + h))) (hnn : ∀ x, 0 ≤ f x) :
    ∫ z in a..b, ∫ u in z..(z + h), f u ≤ h * ∫ u in a..(b + h), f u := by
  have hahb : a ≤ b + h := by linarith
  have h0h : (0 : ℝ) ≤ h := le_of_lt hh
  -- joint integrability of `(z,v) ↦ f (z+v)` on the rectangle `(a,b] × (0,h]`:
  -- it is continuous on the compact rectangle `[a,b] × [0,h]`.
  have hrect : Set.uIoc a b ×ˢ Set.uIoc (0 : ℝ) h ⊆ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) h := by
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le h0h]
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hx.1.le, hx.2⟩, ⟨hy.1.le, hy.2⟩⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f (p.1 + p.2))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) h) := by
    refine hf.comp ?_ ?_
    · exact (continuous_fst.add continuous_snd).continuousOn
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hint : IntegrableOn (fun p : ℝ × ℝ => f (p.1 + p.2))
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) h) :=
    hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hint' : IntegrableOn (fun p : ℝ × ℝ => f (p.1 + p.2))
      (Set.uIoc a b ×ˢ Set.uIoc (0 : ℝ) h) := hint.mono_set hrect
  -- substitute `u = z + v` in the inner integral
  have hshift : ∀ z : ℝ, ∫ u in z..(z + h), f u = ∫ v in (0 : ℝ)..h, f (z + v) := by
    intro z
    have h := intervalIntegral.integral_comp_add_left (f := f) (a := (0 : ℝ)) (b := h) (d := z)
    rw [add_zero] at h
    exact h.symm
  -- the region is now a rectangle, so Tonelli applies
  have hswap : (∫ z in a..b, ∫ v in (0 : ℝ)..h, f (z + v))
      = ∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v) :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hint'
  have hmain : (∫ z in a..b, ∫ u in z..(z + h), f u)
      = ∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v) := by
    simp_rw [hshift]
    exact hswap
  -- for fixed `v ∈ [0,h]` the inner integral is at most the total mass
  have hbound : ‖∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v)‖
      ≤ h * ∫ u in a..(b + h), f u := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun v => ∫ z in a..b, f (z + v)) (a := (0 : ℝ)) (b := h)
      (C := ∫ u in a..(b + h), f u) ?_
    · simpa [abs_of_pos hh, mul_comm] using h1
    · intro v hv
      rw [Set.uIoc_of_le h0h] at hv
      obtain ⟨hv0, hvh⟩ := hv
      have hshiftv : (∫ z in a..b, f (z + v)) = ∫ u in (a + v)..(b + v), f u :=
        intervalIntegral.integral_comp_add_right (f := f) (a := a) (b := b) (d := v)
      have hle : (∫ z in a..b, f (z + v)) ≤ ∫ u in a..(b + h), f u := by
        rw [hshiftv]
        exact intervalIntegral.integral_mono_interval (f := f) (a := a + v) (b := b + v)
          (c := a) (d := b + h) (by linarith) (by linarith) (by linarith)
          (Eventually.of_forall fun x => hnn x) (hf.intervalIntegrable_of_Icc hahb)
      have hnonneg : 0 ≤ ∫ z in a..b, f (z + v) :=
        intervalIntegral.integral_nonneg hab (fun w _ => hnn (w + v))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hle
  calc ∫ z in a..b, ∫ u in z..(z + h), f u
      = ∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v) := hmain
    _ ≤ ‖∫ v in (0 : ℝ)..h, ∫ z in a..b, f (z + v)‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ h * ∫ u in a..(b + h), f u := hbound

end Work.FTS.StrongEps.LocUnif.D5

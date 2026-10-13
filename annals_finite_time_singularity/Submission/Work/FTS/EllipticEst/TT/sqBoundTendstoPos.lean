import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- For a positive exponent `p`, `x ↦ x ^ p` tends to `0` as `x → 0⁺`. -/
private lemma rpow_tendsto_zero_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Filter.Tendsto (fun x : ℝ => x ^ p) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h := (tendsto_rpow_neg_nhdsGT_zero (y := -p) (by linarith)).inv_tendsto_atTop
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Pi.inv_apply, Real.rpow_neg (le_of_lt hx)]
  exact inv_inv _

/-- Squeeze: if `(g x)^2 ≤ M (b x)^p` eventually, with `M ≥ 0`, `p > 0` and `b x → 0⁺`,
then `g x → 0`.  Indeed `|g x| ≤ √M (b x)^{p/2}` and `(b x)^{p/2} → 0`. -/
private lemma tendsto_of_sq_le {α : Type*} {l : Filter α} {b g : α → ℝ} {M p : ℝ}
    (hM : 0 ≤ M) (hp : 0 < p)
    (hb : Filter.Tendsto b l (nhdsWithin (0:ℝ) (Set.Ioi 0)))
    (h : ∀ᶠ x in l, (g x) ^ 2 ≤ M * (b x) ^ p) :
    Filter.Tendsto g l (nhds 0) := by
  have hbpow : Filter.Tendsto (fun x => (b x) ^ (p/2)) l (nhds 0) :=
    (rpow_tendsto_zero_nhdsGT_zero (by linarith : (0:ℝ) < p/2)).comp hb
  have hbound : ∀ᶠ x in l, |g x| ≤ Real.sqrt M * (b x) ^ (p / 2) := by
    filter_upwards [h, hb.eventually self_mem_nhdsWithin] with x hx hbx
    have hb0 : (0:ℝ) ≤ b x := le_of_lt hbx
    calc |g x| = Real.sqrt ((g x)^2) := (Real.sqrt_sq_eq_abs (g x)).symm
      _ ≤ Real.sqrt (M * (b x)^p) := Real.sqrt_le_sqrt hx
      _ = Real.sqrt M * Real.sqrt ((b x)^p) := Real.sqrt_mul hM _
      _ = Real.sqrt M * (b x)^(p/2) := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hb0]
            ring_nf
  have hg : Filter.Tendsto (fun x => Real.sqrt M * (b x)^(p/2)) l (nhds 0) := by
    simpa using hbpow.const_mul (Real.sqrt M)
  have hs := squeeze_zero' (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) hbound hg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using hs

theorem sqBoundTendstoPos {p : ℝ} (hp : 0 < p) :
    (∀ (f : ℝ → ℝ) (c M : ℝ), 0 ≤ M →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ M * θ ^ p) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c)) ∧
    (∀ (f : ℝ → ℝ) (c M : ℝ), 0 ≤ M →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ M * (Real.pi / 2 - θ) ^ p) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)) := by
  constructor
  · intro f c M hM h
    have hmem : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio (by simpa using Real.pi_div_two_pos))
    have hfilt : nhdsWithin (0:ℝ) (Set.Ioo (0:ℝ) (Real.pi/2)) = nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_inter_of_mem' hmem
    rw [← hfilt]
    have hb : Filter.Tendsto (fun θ : ℝ => θ)
        (nhdsWithin (0:ℝ) (Set.Ioo (0:ℝ) (Real.pi/2))) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨Filter.tendsto_id.mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact hθ.1⟩
    have hsub : Filter.Tendsto (fun θ => f θ - c)
        (nhdsWithin (0:ℝ) (Set.Ioo (0:ℝ) (Real.pi/2))) (nhds 0) :=
      tendsto_of_sq_le hM hp hb (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact h θ hθ)
    have hconst : Filter.Tendsto (fun _ : ℝ => c)
        (nhdsWithin (0:ℝ) (Set.Ioo (0:ℝ) (Real.pi/2))) (nhds c) :=
      tendsto_const_nhds
    have hsum := hsub.add hconst
    simpa using hsum
  · intro f c M hM h
    have hmem : Set.Ioi (0:ℝ) ∈ nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)) :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioi (by simpa using Real.pi_div_two_pos))
    have hfilt : nhdsWithin (Real.pi/2) (Set.Ioo (0:ℝ) (Real.pi/2)) =
        nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)) :=
      nhdsWithin_inter_of_mem hmem
    rw [← hfilt]
    have hb : Filter.Tendsto (fun θ : ℝ => Real.pi/2 - θ)
        (nhdsWithin (Real.pi/2) (Set.Ioo (0:ℝ) (Real.pi/2))) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcont : Filter.Tendsto (fun θ : ℝ => Real.pi/2 - θ) (nhds (Real.pi/2)) (nhds 0) := by
          have h1 : ContinuousAt (fun θ : ℝ => Real.pi/2 - θ) (Real.pi/2) :=
            continuousAt_const.sub continuousAt_id
          simpa using h1.tendsto
        exact hcont.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        exact sub_pos.mpr hθ.2
    have hsub : Filter.Tendsto (fun θ => f θ - c)
        (nhdsWithin (Real.pi/2) (Set.Ioo (0:ℝ) (Real.pi/2))) (nhds 0) :=
      tendsto_of_sq_le hM hp hb (by filter_upwards [self_mem_nhdsWithin] with θ hθ; exact h θ hθ)
    have hconst : Filter.Tendsto (fun _ : ℝ => c)
        (nhdsWithin (Real.pi/2) (Set.Ioo (0:ℝ) (Real.pi/2))) (nhds c) :=
      tendsto_const_nhds
    have hsum := hsub.add hconst
    simpa using hsum

end Work.FTS.EllipticEst.TT

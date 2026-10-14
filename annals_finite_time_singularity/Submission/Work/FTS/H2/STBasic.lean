import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllipticEst.Lop_iter_cos_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-! ## Elementary facts about `L = sin(2θ) ∂_θ` used below

The operator `Work.Spaces.Lop` is the one-dimensional angular operator `L u θ = sin(2θ) u'(θ)`,
whose iterates are `LopIter i u = (L^[i]) u`.  What the proof of `Lop_iter_cos_eq` needs is
(i) that `L` is `ℝ`-homogeneous (unconditionally, via `deriv_const_mul_field`), so that its
iterates are too, and (ii) the explicit value `L (2 cos 2θ) = -4 sin²(2θ)`. -/

/-- `L = sin(2θ) ∂_θ` commutes with multiplication by a constant: this holds for *every*
`f` (no differentiability needed), by the unconditional `deriv_const_mul_field`. -/
theorem Lop_const_mul (c : ℝ) (f : ℝ → ℝ) :
    Work.Spaces.Lop (fun θ : ℝ => c * f θ) = fun θ : ℝ => c * Work.Spaces.Lop f θ := by
  funext θ
  simp only [Work.Spaces.Lop]
  rw [deriv_const_mul_field]
  ring

/-- The iterate `LopIter (j+1) = L^[j] ∘ L` (the successor step applied at the front rather
than at the back, complementing `LopIter_succ`). -/
theorem LopIter_succ_apply (j : ℕ) (u : ℝ → ℝ) :
    LopIter (j + 1) u = LopIter j (Work.Spaces.Lop u) := by
  simp only [LopIter, Function.iterate_succ_apply]

/-- The iterates of `L` are `ℝ`-homogeneous. -/
theorem LopIter_const_mul (i : ℕ) (c : ℝ) :
    ∀ f : ℝ → ℝ, LopIter i (fun θ : ℝ => c * f θ) = fun θ : ℝ => c * LopIter i f θ := by
  induction i with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      rw [LopIter_succ_apply, Lop_const_mul, ih, LopIter_succ_apply]

/-- `L (2 cos 2θ) = -4 sin²(2θ)`: the first iterate of `2 cos(2θ)`. -/
theorem Lop_two_cos :
    Work.Spaces.Lop (fun θ : ℝ => 2 * Real.cos (2 * θ))
      = fun θ : ℝ => -4 * (Real.sin (2 * θ)) ^ 2 := by
  funext θ
  simp only [Work.Spaces.Lop]
  rw [deriv_const_mul_field]
  rw [show (fun θ : ℝ => Real.cos (2 * θ)) = Real.cos ∘ (fun θ : ℝ => 2 * θ) from rfl]
  rw [deriv_comp] <;> try fun_prop
  rw [Real.deriv_cos]
  have h2 : deriv (fun θ : ℝ => 2 * θ) θ = 2 := by
    rw [deriv_const_mul_field]; simp
  rw [h2]
  ring

/-- The iterates of `2 cos(2θ)` under `L = sin(2θ) ∂_θ` are the `L`-iterates of `sin(2θ)²`:
`L^i (2 cos 2θ) = -4 · L^{i-1}(sin²(2θ))` for `i ≥ 1`.

Proof route: `L (2 cos 2θ) = sin(2θ) · deriv (2 cos 2θ) = sin(2θ) · (-4 sin 2θ) = -4 sin²(2θ)`,
and `L^{i} = L^{i-1} ∘ L` together with the linearity of the iterates of `L`
(`L (fun θ => c * f θ) = fun θ => c * L f θ` by `deriv_const_mul_field`); a direct induction on
`i` using `Function.iterate_succ_apply` is enough. -/
theorem Lop_iter_cos_eq (i : ℕ) (hi : 1 ≤ i) :
    Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => 2 * Real.cos (2 * θ))
      = fun θ : ℝ => -4 * Work.FTS.EllipticEst.LopIter (i - 1)
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hi) with ⟨j, rfl⟩
  rw [LopIter_succ_apply]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [Lop_two_cos, LopIter_const_mul]

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SgamBound

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is at least `1` on the interior of `Iθ`
(because `0 < sin(2θ) ≤ 1` and `η ≥ 0`). -/
lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
    (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- Integrability transfer on the angular slice: if `g` is continuous on the open interval
`(0, π/2)` and `g²·sin(2θ)^{-η}` is integrable on `Iθ = [0, π/2]`, then `|g|` is integrable
on `Iθ`.

Since `η = 99/100 > 0` and `0 < sin(2θ) ≤ 1` on `(0,π/2)`, the weight satisfies `1 ≤ sEta`
there (see `one_le_sEta`), so `g² ≤ g²·sEta` a.e. on `Iθ`; hence `g²` is integrable, and
`|g| ≤ g² + 1` pointwise with `g² + 1` integrable on the finite measure space `Iθ`. -/
theorem integrableOn_abs_of_sq_mul_sEta {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |g θ|) Work.Spaces.Iθ := by
  -- ## Step 0: the two endpoints `{0, π/2}` are a null set, so `Iθ = [0,π/2]` agrees with the
  -- open interval `(0, π/2)` almost everywhere, and the integrals coincide.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  have hint' : MeasureTheory.Integrable
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hms]; exact hint
  -- ## Step 1: on `(0, π/2)` the weight satisfies `1 ≤ sEta`, so `g² ≤ g² · sEta` a.e.
  have hsaesm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hint'.mono' (MeasureTheory.AEStronglyMeasurable.pow hsaesm 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta hθ
    have hsq : 0 ≤ (g θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- ## Step 2: `|g| ≤ g² + 1` pointwise, and `g² + 1` is integrable (the slice has finite
  -- measure), so `|g|` is integrable on `(0, π/2)`.
  have habs_int : MeasureTheory.Integrable (fun θ : ℝ => |g θ|)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 + 1)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
    refine hmaj.mono' hsaesm.norm ?_
    filter_upwards with θ
    have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|g θ| - 1 / 2), sq_abs (g θ), abs_nonneg (g θ)]
    simpa only [Real.norm_eq_abs, abs_abs] using h1
  -- ## Step 3: transfer back to `Iθ`, which is `(0, π/2)` a.e.
  change MeasureTheory.Integrable (fun θ : ℝ => |g θ|)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hms]; exact habs_int

end Work.FTS.EllipticEst.SgamBound
end
-- ===== merged: Submission.Work.FTS.H2.STBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `θ`-facts -/

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On `Iθ`, `sin (2θ)` dominates `(4/π) · min θ (π/2 - θ)`. -/
theorem sin_two_ge_min (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (4 / π) * min θ (π / 2 - θ) ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  have hpi := Real.pi_pos
  rcases le_total θ (π / 4) with h | h
  · have hmin : min θ (π / 2 - θ) = θ := by
      refine min_eq_left ?_
      linarith
    rw [hmin]
    have h2 : (2 / π) * (2 * θ) ≤ Real.sin (2 * θ) := by
      refine Real.mul_le_sin (by linarith) ?_
      linarith
    have he : (2 / π) * (2 * θ) = (4 / π) * θ := by ring
    rw [he] at h2; exact h2
  · have hmin : min θ (π / 2 - θ) = π / 2 - θ := by
      refine min_eq_right ?_
      linarith
    rw [hmin]
    have hsin : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
      rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
    rw [hsin]
    have h2 : (2 / π) * (2 * (π / 2 - θ)) ≤ Real.sin (2 * (π / 2 - θ)) := by
      refine Real.mul_le_sin (by linarith) ?_
      linarith
    have he : (2 / π) * (2 * (π / 2 - θ)) = (4 / π) * (π / 2 - θ) := by ring
    rw [he] at h2; exact h2

/-- `sin (2θ)^p` is interval integrable on `[0, π/2]` for `p > -1`. -/
theorem intervalIntegrable_sin_rpow (p : ℝ) (hp : -1 < p) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) volume 0 (π / 2) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (0:ℝ) ≤ π / 2)]
  by_cases hp0 : 0 ≤ p
  · -- nonnegative exponent: bounded by `1`
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrableOn_const
      (s := Set.Icc (0:ℝ) (π/2)) (C := (1:ℝ)) ?_) ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h0 := sin_two_nonneg_Iθ hθ
      rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 p)]
      exact Real.rpow_le_one h0 (Real.sin_le_one _) hp0
  · -- negative exponent: compare with the explicit majorant
    push_neg at hp0
    have hq : 0 < -p := by linarith
    have hmaj := Work.Spaces.integrableOn_majorant_rpow (-p) hq (by linarith)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h0 := sin_two_nonneg_Iθ hθ
      rw [Real.norm_of_nonneg (Real.rpow_nonneg h0 p)]
      have h4 := Work.Spaces.sin_rpow_le_majorant (-p) θ hq hθ
      simpa only [neg_neg] using h4


/-- `sin (2θ)^p → 0` as `θ → 0` from the right, for `p > 0`. -/
theorem tendsto_sin_rpow_zero_right (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h0p : (0 : ℝ) ^ p = 0 := Real.zero_rpow (ne_of_gt hp)
  have h2 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝[>] 0) (𝓝 0) := by
    have h3 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto (fun θ : ℝ => 2 * θ) (𝓝 0) (𝓝 (2 * 0)))
    exact h3.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun θ : ℝ => (2 * θ) ^ p) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.comp h2
    simpa [Function.comp_def, h0p] using hc
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < π / 4 by positivity)]
      with θ hθ hlt
    exact Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hθ, by linarith [hlt.2, Real.pi_pos]⟩) p
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < π / 4 by positivity)]
      with θ hθ hlt
    have hθI : θ ∈ Spaces.Iθ := ⟨le_of_lt hθ, by linarith [hlt.2, Real.pi_pos]⟩
    exact Real.rpow_le_rpow (sin_two_nonneg_Iθ hθI) (Real.sin_le (by linarith [hlt.1])) hp.le

/-- `sin (2θ)^p → 0` as `θ → π/2` from the left, for `p > 0`. -/
theorem tendsto_sin_rpow_zero_left (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hcomp : Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝[<] (π / 2)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h3 : Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝 (π / 2)) (𝓝 0) := by
        simpa using (tendsto_const_nhds.sub tendsto_id :
          Tendsto (fun θ : ℝ => π / 2 - θ) (𝓝 (π / 2)) (𝓝 (π / 2 - π / 2)))
      exact h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      show (0:ℝ) < π / 2 - θ
      have := Set.mem_Iio.mp hθ
      linarith
  have h := (tendsto_sin_rpow_zero_right p hp).comp hcomp
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  simp only [Function.comp_apply]
  rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]

/-- `θ ↦ sin (2θ)^p` is differentiable at `θ ∈ (0, π/2)` with derivative
`2 cos (2θ) · p · sin (2θ)^(p-1)`. -/
theorem hasDerivAt_sin_rpow (p θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ p)
      (2 * Real.cos (2 * θ) * p * (Real.sin (2 * θ)) ^ (p - 1)) θ := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa [Function.comp_def, mul_comm] using h2
  have hne : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos_of_Ioo hθ)
  exact hs.rpow_const (p := p) (Or.inl hne)

/-- The derivative of `θ ↦ sin (2θ)^(-e)` on `(0, π/2)`. -/
theorem hasDerivAt_sin_rpow_neg (e θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-e))
      (2 * Real.cos (2 * θ) * (-e) * (Real.sin (2 * θ)) ^ (-e - 1)) θ :=
  hasDerivAt_sin_rpow (-e) θ hθ

end Work.FTS.H2
end
end

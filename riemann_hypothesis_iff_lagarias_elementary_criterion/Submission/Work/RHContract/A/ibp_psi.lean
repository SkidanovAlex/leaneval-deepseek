import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# Integration by parts for the antiderivative of `ψ` against the kernel `k`

Writing `Ψ(t) = ∫_0^t ψ` and `k = kW`, the claim is

`∫_x^Y (ψ t − t) · k(t) dt
   = [(Ψ(t) − t²/2) k(t)]_x^Y − ∫_x^Y (Ψ(t) − t²/2) · k'(t) dt`,

the standard integration by parts with `(Ψ(t) − t²/2)' = ψ(t) − t` (the derivative of `Ψ` at a
point `t` in the *right* sense is `ψ(t)`, because `ψ` is constant on a right neighbourhood of `t`).

The formalisation uses `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`, which
only needs one-sided (right) derivatives in the interior of the interval.
-/

namespace Work.RHContract.A

open MeasureTheory

noncomputable section

/-- `ψ` is right-continuous: to the right of any `x ≥ 0` it is eventually constant. -/
lemma tendsto_psi_nhdsGT (x : ℝ) (hx : 0 ≤ x) :
    Filter.Tendsto Chebyshev.psi (nhdsWithin x (Set.Ioi x)) (nhds (Chebyshev.psi x)) := by
  have hmem : Set.Ioo x (⌊x⌋₊ + 1) ∈ nhdsWithin x (Set.Ioi x) :=
    Ioo_mem_nhdsGT (Nat.lt_floor_add_one x)
  have hev : (fun t => Chebyshev.psi t) =ᶠ[nhdsWithin x (Set.Ioi x)]
      (fun _ => Chebyshev.psi x) := by
    filter_upwards [hmem] with t ht
    have hfloor : ⌊t⌋₊ = ⌊x⌋₊ :=
      Nat.floor_eq_on_Ico ⌊x⌋₊ t ⟨(Nat.floor_le hx).trans ht.1.le, ht.2⟩
    rw [Chebyshev.psi_eq_psi_coe_floor t, Chebyshev.psi_eq_psi_coe_floor x, hfloor]
  exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

/-- The kernel `k(t) = (log t + 1)/(t² log² t)` is `C¹` on `(1, ∞)`. -/
lemma contDiffOn_kW : ContDiffOn ℝ 1 kW (Set.Ioi 1) := by
  have hlog : ContDiffOn ℝ 1 (fun t : ℝ => Real.log t) (Set.Ioi 1) :=
    Real.contDiffOn_log.mono (fun t ht => by
      have h1 : (1:ℝ) < t := ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)
  have hnum : ContDiffOn ℝ 1 (fun t : ℝ => Real.log t + 1) (Set.Ioi 1) :=
    hlog.add contDiffOn_const
  have hden : ContDiffOn ℝ 1 (fun t : ℝ => t ^ 2 * (Real.log t) ^ 2) (Set.Ioi 1) :=
    (contDiffOn_id.pow 2).mul (hlog.pow 2)
  have hdiv := hnum.div hden (fun t ht => by
    have h1 : (1:ℝ) < t := ht
    exact mul_ne_zero (pow_ne_zero 2 (by linarith : t ≠ 0))
      (pow_ne_zero 2 (ne_of_gt (Real.log_pos h1))))
  refine hdiv.congr ?_
  intro t _
  simp [Work.RHContract.kW]

/-- `deriv k` is continuous on `[x, Y]` as soon as `x > 1`. -/
lemma continuousOn_deriv_kW {x Y : ℝ} (hx : 1 < x) (hxY : x ≤ Y) :
    ContinuousOn (deriv kW) (Set.uIcc x Y) := by
  have h := contDiffOn_kW.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  rw [Set.uIcc_of_le hxY]
  refine h.mono ?_
  intro t ht
  simp only [Set.mem_Ioi]
  linarith [ht.1, hx]

theorem ibp_psi (x Y : ℝ) (hx : 1 < x) (hxY : x ≤ Y) :
    ∫ t in x..Y, (Chebyshev.psi t - t) * Work.RHContract.kW t
      = ((∫ s in (0:ℝ)..Y, Chebyshev.psi s) - Y ^ 2 / 2) * Work.RHContract.kW Y
        - ((∫ s in (0:ℝ)..x, Chebyshev.psi s) - x ^ 2 / 2) * Work.RHContract.kW x
        - ∫ t in x..Y, ((∫ s in (0:ℝ)..t, Chebyshev.psi s) - t ^ 2 / 2) * deriv Work.RHContract.kW t := by
  let F : ℝ → ℝ := fun t => (∫ s in (0:ℝ)..t, Chebyshev.psi s) - t ^ 2 / 2
  -- continuity of `F` and of `k` on the interval
  have hFcont : ContinuousOn F (Set.uIcc x Y) := by
    have hP : Continuous (fun t : ℝ => ∫ s in (0:ℝ)..t, Chebyshev.psi s) :=
      intervalIntegral.continuous_primitive
        (fun a b => Chebyshev.psi_mono.intervalIntegrable) (0 : ℝ)
    have hpoly : Continuous (fun t : ℝ => t ^ 2 / 2) :=
      (continuous_id.pow 2).div_const 2
    have hPc : ContinuousOn (fun t : ℝ => ∫ s in (0:ℝ)..t, Chebyshev.psi s) (Set.uIcc x Y) :=
      hP.continuousOn
    have hpc : ContinuousOn (fun t : ℝ => t ^ 2 / 2) (Set.uIcc x Y) := hpoly.continuousOn
    change ContinuousOn ((fun t : ℝ => ∫ s in (0:ℝ)..t, Chebyshev.psi s)
      - (fun t : ℝ => t ^ 2 / 2)) (Set.uIcc x Y)
    exact hPc.sub hpc
  have hkWcont : ContinuousOn kW (Set.uIcc x Y) := by
    rw [Set.uIcc_of_le hxY]
    refine contDiffOn_kW.continuousOn.mono ?_
    intro t ht
    simp only [Set.mem_Ioi]
    linarith [ht.1, hx]
  -- right derivatives in the interior
  have hFderiv : ∀ t ∈ Set.Ioo (min x Y) (max x Y),
      HasDerivWithinAt F (Chebyshev.psi t - t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxY, max_eq_right hxY] at ht
    have ht1 : (1:ℝ) < t := by linarith [ht.1, hx]
    have hpsi_right : ContinuousWithinAt Chebyshev.psi (Set.Ioi t) t :=
      show ContinuousWithinAt Chebyshev.psi (Set.Ioi t) t from tendsto_psi_nhdsGT t (by linarith)
    have hmeas : StronglyMeasurableAtFilter Chebyshev.psi (nhdsWithin t (Set.Ioi t)) volume :=
      (Chebyshev.psi_mono.measurable.stronglyMeasurable).stronglyMeasurableAtFilter
    have h1 : HasDerivWithinAt (fun u => ∫ s in (0:ℝ)..u, Chebyshev.psi s)
        (Chebyshev.psi t) (Set.Ioi t) t :=
      (intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := t)
        (Chebyshev.psi_mono.intervalIntegrable) hmeas hpsi_right).mono Set.Ioi_subset_Ici_self
    have h2 : HasDerivWithinAt (fun s : ℝ => s ^ 2 / 2) t (Set.Ioi t) t := by
      have h : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
        simpa using (hasDerivAt_pow 2 t).div_const 2
      exact h.hasDerivWithinAt
    change HasDerivWithinAt ((fun u => ∫ s in (0:ℝ)..u, Chebyshev.psi s)
      - (fun s : ℝ => s ^ 2 / 2)) (Chebyshev.psi t - t) (Set.Ioi t) t
    exact h1.sub h2
  have hkWderiv : ∀ t ∈ Set.Ioo (min x Y) (max x Y),
      HasDerivWithinAt kW (deriv kW t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hxY, max_eq_right hxY] at ht
    have ht1 : (1:ℝ) < t := by linarith [ht.1, hx]
    have hd : DifferentiableOn ℝ kW (Set.Ioi 1) :=
      contDiffOn_kW.differentiableOn (by norm_num)
    exact (hd t ht1).differentiableAt (isOpen_Ioi.mem_nhds ht1) |>.hasDerivAt.hasDerivWithinAt
  -- integrability of the two derivative functions
  have hu' : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t - t) volume x Y :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable x Y)
  have hv' : IntervalIntegrable (deriv kW) volume x Y :=
    (continuousOn_deriv_kW hx hxY).intervalIntegrable
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (a := x) (b := Y) (u := F) (v := kW)
    (u' := fun t : ℝ => Chebyshev.psi t - t) (v' := deriv kW)
    hFcont hkWcont hFderiv hkWderiv hu' hv'
  have key : ∫ t in x..Y, (Chebyshev.psi t - t) * kW t
      = F Y * kW Y - F x * kW x - ∫ t in x..Y, F t * deriv kW t := by
    rw [hIBP]; ring
  simpa [F] using key

end

end Work.RHContract.A

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsBasic
import Submission.Work.FTS.StrongEps.Traces.wtZ_shift_mul_le
import Submission.Work.FTS.StrongEps.Traces.sin_rpow_thShift_le
import Submission.Work.FTS.StrongEps.Traces.eventually_thShift_lt
import Submission.Work.FTS.StrongEps.Traces.eventually_thShift_gt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Elementary tools for the boundary-trace transfer

`J_ε` is a weighted average of the shifted values of the profile (`abs_Jeps_le_sup`), so the
boundary traces of `J_ε g` follow from those of `g` as soon as the two weights `z · w z ^ 2` and
`sin (2θ) ^ e` can be compared with their shifted values.  Those comparisons are the content of
`Traces/wtZ_shift_mul_le.lean`, `Traces/sin_rpow_thShift_le.lean` and
`Traces/eventually_thShift_{lt,gt}.lean`; the two `zShift` facts are proved here. -/

/-- A real function which is eventually nonnegative and eventually `≤ ε` for every `ε > 0` tends
to `0`. -/
theorem tendsto_nhds_zero_of_eventually_le {l : Filter ℝ} {F : ℝ → ℝ}
    (hnn : ∀ᶠ x in l, 0 ≤ F x) (h : ∀ ε' > 0, ∀ᶠ x in l, F x ≤ ε') :
    Tendsto F l (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hnn] with x hx using lt_of_lt_of_le ha hx
  · have h2 : 0 < b / 2 := by linarith
    filter_upwards [h (b / 2) h2] with x hx using lt_of_le_of_lt hx (by linarith)

/-- The radial weight is positive on `z > 0`. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- The `z`-shift `z ↦ z e^{-p}` is eventually `< δ` near `z = 0`, uniformly in `|p| ≤ ε`. -/
theorem eventually_zShift_lt (ε δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → zShift z p < δ := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ * Real.exp (-ε) by positivity)] with z hz
  intro p hp
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  calc zShift z p = z * Real.exp (-p) := rfl
    _ ≤ z * Real.exp ε :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hz1.le
    _ < δ * Real.exp (-ε) * Real.exp ε := mul_lt_mul_of_pos_right hz2 (Real.exp_pos _)
    _ = δ := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- The `z`-shift `z ↦ z e^{-p}` is eventually `> Z` near `z = ∞`, uniformly in `|p| ≤ ε`. -/
theorem eventually_zShift_gt (ε Z : ℝ) :
    ∀ᶠ z in atTop, 0 < z ∧ ∀ p : ℝ, |p| ≤ ε → Z < zShift z p := by
  filter_upwards [eventually_gt_atTop (max (Z * Real.exp ε) 0)] with z hz
  have hz1 : 0 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz2 : Z * Real.exp ε < z := lt_of_le_of_lt (le_max_left _ _) hz
  refine ⟨hz1, fun p hp => ?_⟩
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  have h1 : Real.exp (-ε) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  calc Z = Z * Real.exp ε * Real.exp (-ε) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ < z * Real.exp (-ε) := mul_lt_mul_of_pos_right hz2 (Real.exp_pos _)
    _ ≤ z * Real.exp (-p) := mul_le_mul_of_nonneg_left h1 hz1.le
    _ = zShift z p := rfl

theorem BdryTraces_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ} {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hbdd : ∀ a b : ℕ, a + b ≤ k → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed b a f z θ| ≤ M)
    (hz0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
        z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε')
    (hzin : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
        z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε')
    (ht0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (ht1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    Work.FTS.Nonlin.BdryTraces α k (Jeps ρ ε f) := by
  intro a b hab
  set g : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hg
  have hcm : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed b a (Jeps ρ ε f) z θ = Jeps ρ ε g z θ :=
    fun z θ hz hθ => mixed_Jeps ρ hρ.moll hε hsm hz hθ b a
  have hIθ : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  have hIθ' : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) :=
    Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · -- ### `z → 0⁺`
    have hlim : Tendsto (fun z : ℝ => z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIoi] with z hz using mul_nonneg hz.le (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨δ, hδpos, hδ⟩ :=
          hz0 a b hab (ε' / Real.exp (3 * ε)) (div_pos hε' (Real.exp_pos _))
        have hzs : ∀ᶠ z in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → zShift z p < δ :=
          eventually_zShift_lt ε δ hδpos
        filter_upwards [hIoi, hzs] with z hz hzs
        have hzw : 0 < z * Work.Spaces.w z ^ 2 := mul_pos hz (pow_pos (w_pos_of_pos hz) 2)
        set M : ℝ := Real.sqrt (ε' / (z * Work.Spaces.w z ^ 2)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / (z * Work.Spaces.w z ^ 2) :=
          Real.sq_sqrt (div_nonneg hε'.le hzw.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hzδ : zShift z p.1 < δ := hzs p.1 hp1
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hδ (zShift z p.1) hz1 hzδ (thShift θ p.2) hth
          have hwt := Traces.wtZ_shift_mul_le z p.1 ε hz hε.le hp1
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hzw]
            have hhyp' : (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                * (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ ε' / Real.exp (3 * ε) := by
              have h := hhyp
              rw [mul_pow] at h
              calc (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  = zShift z p.1 * ((g (zShift z p.1) (thShift θ p.2)) ^ 2
                      * Work.Spaces.w (zShift z p.1) ^ 2) := by ring
                _ ≤ ε' / Real.exp (3 * ε) := h
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2 * (z * Work.Spaces.w z ^ 2)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (3 * ε)
                        * (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)) :=
                  mul_le_mul_of_nonneg_left hwt (sq_nonneg _)
              _ = Real.exp (3 * ε) * ((zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (3 * ε) * (ε' / Real.exp (3 * ε)) :=
                  mul_le_mul_of_nonneg_left hhyp' (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hz hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2
            = z * Work.Spaces.w z ^ 2 * (Jeps ρ ε g z θ) ^ 2 := by ring
          _ ≤ z * Work.Spaces.w z ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hjsq hzw.le
          _ = z * Work.Spaces.w z ^ 2 * (ε' / (z * Work.Spaces.w z ^ 2)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hzw.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIoi] with z hz
    rw [hcm z θ hz hθ]
  · -- ### `z → ∞`
    have hlim : Tendsto (fun z : ℝ => z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2)
        atTop (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz using
          mul_nonneg hz.le (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨Z, hZ⟩ := hzin a b hab (ε' / Real.exp (3 * ε)) (div_pos hε' (Real.exp_pos _))
        have hzs : ∀ᶠ z in atTop, 0 < z ∧ ∀ p : ℝ, |p| ≤ ε → Z < zShift z p :=
          eventually_zShift_gt ε Z
        filter_upwards [hzs] with z hz
        obtain ⟨hzpos, hzs⟩ := hz
        have hzw : 0 < z * Work.Spaces.w z ^ 2 := mul_pos hzpos (pow_pos (w_pos_of_pos hzpos) 2)
        set M : ℝ := Real.sqrt (ε' / (z * Work.Spaces.w z ^ 2)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / (z * Work.Spaces.w z ^ 2) :=
          Real.sq_sqrt (div_nonneg hε'.le hzw.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hzpos
          have hzZ : Z < zShift z p.1 := hzs p.1 hp1
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hZ (zShift z p.1) hzZ (thShift θ p.2) hth
          have hwt := Traces.wtZ_shift_mul_le z p.1 ε hzpos hε.le hp1
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hzw]
            have hhyp' : (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                * (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ ε' / Real.exp (3 * ε) := by
              have h := hhyp
              rw [mul_pow] at h
              calc (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  = zShift z p.1 * ((g (zShift z p.1) (thShift θ p.2)) ^ 2
                      * Work.Spaces.w (zShift z p.1) ^ 2) := by ring
                _ ≤ ε' / Real.exp (3 * ε) := h
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2 * (z * Work.Spaces.w z ^ 2)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (3 * ε)
                        * (zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)) :=
                  mul_le_mul_of_nonneg_left hwt (sq_nonneg _)
              _ = Real.exp (3 * ε) * ((zShift z p.1 * Work.Spaces.w (zShift z p.1) ^ 2)
                    * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (3 * ε) * (ε' / Real.exp (3 * ε)) :=
                  mul_le_mul_of_nonneg_left hhyp' (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hzpos hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc z * (Jeps ρ ε g z θ * Work.Spaces.w z) ^ 2
            = z * Work.Spaces.w z ^ 2 * (Jeps ρ ε g z θ) ^ 2 := by ring
          _ ≤ z * Work.Spaces.w z ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hjsq hzw.le
          _ = z * Work.Spaces.w z ^ 2 * (ε' / (z * Work.Spaces.w z ^ 2)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hzw.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [hcm z θ hz hθ]
  · -- ### `θ → 0⁺`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Jeps ρ ε g z θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨δ, hδpos, hδ⟩ := ht0 a b hab (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|))
          (div_pos hε' (Real.exp_pos _))
        have hθs : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → thShift θ p < δ :=
          Traces.eventually_thShift_lt ε δ hδpos
        filter_upwards [hIθ, hθs] with θ hθ hθs
        have hsEpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg hε'.le hsEpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hthδ : thShift θ p.2 < δ := hθs p.2 hp2
          have hhyp := hδ (thShift θ p.2) hth.1 hthδ (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α) hθ hε.le hp2
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsEpos]
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                        * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                        * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) :=
                  mul_le_mul_of_nonneg_left hhyp (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hz hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Jeps ρ ε g z θ) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsEpos.le
          _ = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hsEpos.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ] with θ hθ
    rw [hcm z θ hz hθ]
  · -- ### `θ → (π/2)⁻`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Jeps ρ ε g z θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := by
      refine tendsto_nhds_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ'] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε' hε'
        obtain ⟨δ, hδpos, hδ⟩ := ht1 a b hab (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|))
          (div_pos hε' (Real.exp_pos _))
        have hθs : ∀ᶠ θ in 𝓝[<] (π / 2), ∀ p : ℝ, |p| ≤ ε → π / 2 - δ < thShift θ p :=
          Traces.eventually_thShift_gt ε δ hδpos
        filter_upwards [hIθ', hθs] with θ hθ hθs
        have hsEpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg hε'.le hsEpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |g (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hthδ : π / 2 - δ < thShift θ p.2 := hθs p.2 hp2
          have hhyp := hδ (thShift θ p.2) hth.2 hthδ (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α) hθ hε.le hp2
          have hsq : (g (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsEpos]
            calc (g (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (g (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                        * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                        * (g (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ Real.exp (ε * |(1 - Work.Spaces.gam α)|)
                    * (ε' / Real.exp (ε * |(1 - Work.Spaces.gam α)|)) :=
                  mul_le_mul_of_nonneg_left hhyp (Real.exp_pos _).le
              _ = ε' := by rw [mul_div_cancel₀ _ (Real.exp_pos _).ne']
          have hsq' : |g (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hjep : |Jeps ρ ε g z θ| ≤ M := abs_Jeps_le_sup ρ hρ.moll hε hz hθ hMb hMn
        have hjsq : (Jeps ρ ε g z θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hjep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Jeps ρ ε g z θ) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsEpos.le
          _ = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                * (ε' / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) := by rw [hMsq]
          _ = ε' := by rw [mul_div_cancel₀ _ hsEpos.ne']
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ'] with θ hθ
    rw [hcm z θ hz hθ]

end Work.FTS.StrongEps

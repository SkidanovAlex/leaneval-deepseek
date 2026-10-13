import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.FTS.H2.STQ.FBnd
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.Rop_pointwiseU
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.mvt_tendsto_of_deriv_le
import Submission.Work.FTS.H2.Q.WtoWQ_f_bound_mixed
import Submission.Work.Blocks.DivSinHalfCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about `StarPkg` and about the angular functions

The estimates of the target lemma are obtained from `StarPkg` (which bounds `∂_θ𝒰`,
`ℛ` and `𝒱` in the weighted-`L∞` norms) together with

* the pointwise identity `tan θ · 𝒰 = 𝒱 - ℛ` (which converts the `ℛ, 𝒱`-bounds into a
  bound on the *radial* derivatives of `𝒰` — this is where the factor `cos θ/ sin θ`,
  hence `sin(2θ)` for `θ ≥ π/4`, comes from);
* the mean-value theorems in the `θ`-direction (using the `Tendsto` hypothesis) and in
  the `z`-direction (using the vanishing of the `z = 0` slice and the `C^∞`-smoothness
  of the slices on the open quadrant);
* the structural fact that `D_θ^a 𝒰` for `a ≥ 1` carries a factor `sin(2θ)`. -/

/-- `Cs ≥ 0` for any `StarPkg α Cs Φs` with `α > 0`: the norm `WlInf` is nonnegative. -/
theorem Cs_nonneg_of_starPkg {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) : 0 ≤ Cs := by
  have hmem := hS.dU.1
  have hle := hS.dU.2
  have h0 : 0 ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) :=
    Work.FTS.H2.STQ.WlInf_nonneg hmem
  nlinarith [hle, h0, hα]

/-- The mean-value bound in the `z`-direction, from the *value* at `z = 0`. -/
theorem mvt_z_of_value {f : ℝ → ℝ} {B z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn f (Set.Icc 0 z))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo 0 z))
    (h0 : f 0 = 0)
    (hb : ∀ t ∈ Set.Ioo 0 z, |deriv f t| ≤ B) :
    |f z| ≤ B * z := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hz hcont hdiff
  have hz0 : z - 0 ≠ 0 := by linarith
  have h2 : f z - f 0 = (z - 0) * deriv f c := by
    rw [hcd]
    field_simp
  rw [h0, sub_zero, sub_zero] at h2
  rw [h2, abs_mul, abs_of_pos hz]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right (hb c hc) (le_of_lt hz)

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≤ 1`. -/
theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- On the left half of `Iθ`, `θ ≤ (π/4)·sin(2θ)`. -/
theorem theta_le_sin_two {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h4 : θ ≤ π / 4) :
    θ ≤ (π / 4) * Real.sin (2 * θ) := by
  have h := Work.FTS.H2.sin_two_ge_min θ hθ
  have hmin : min θ (π / 2 - θ) = θ := min_eq_left (by linarith [Real.pi_pos, h4])
  rw [hmin] at h
  have hπ4 : 0 < π / 4 := by linarith [Real.pi_pos]
  have hkey : (π / 4) * ((4 / π) * θ) = θ := by field_simp
  calc θ = (π / 4) * ((4 / π) * θ) := hkey.symm
    _ ≤ (π / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h (le_of_lt hπ4)

/-- On the right half of `Iθ`, `cos θ / sin θ ≤ sin(2θ)`. -/
theorem cot_le_sin_two {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (h4 : π / 4 ≤ θ) :
    Real.cos θ / Real.sin θ ≤ Real.sin (2 * θ) := by
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hsin4 : Real.sin (π / 4) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 4) (y := θ)
      (by linarith [Real.pi_pos]) (by linarith [hθ.2]) h4
  have hs2 : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by
    have h1 : Real.sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    rw [h1] at hsin4
    have h2 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    calc (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 := h2.symm
      _ ≤ Real.sin θ ^ 2 := pow_le_pow_left₀ (by positivity) hsin4 2
  have h1 : 1 ≤ 2 * Real.sin θ ^ 2 := by linarith
  rw [Real.sin_two_mul]
  rw [div_le_iff₀ hsinpos]
  have h3 : Real.cos θ ≤ (2 * Real.sin θ * Real.cos θ) * Real.sin θ := by
    have h := mul_le_mul_of_nonneg_right h1 (le_of_lt hcospos)
    nlinarith [h]
  linarith [h3]

/-- `min z 1 ≤ 2 log (1+z)` for `z ≥ 0`. -/
theorem min_one_le_log {z : ℝ} (hz : 0 ≤ z) : min z 1 ≤ 2 * Real.log (1 + z) := by
  have hpos : 0 < 1 + z := by linarith
  have hbase : z / (1 + z) ≤ Real.log (1 + z) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + z) by positivity)
    rw [Real.log_div one_ne_zero hpos.ne'] at h
    simp only [Real.log_one, zero_sub] at h
    have h3 : (1 : ℝ) / (1 + z) - 1 = -(z / (1 + z)) := by
      field_simp
      ring
    rw [h3] at h
    linarith
  rcases le_total z 1 with h | h
  · rw [min_eq_left h]
    have h2 : z / 2 ≤ z / (1 + z) := by
      rw [le_div_iff₀ hpos]
      nlinarith
    linarith
  · rw [min_eq_right h]
    have hlog : Real.log 2 ≤ Real.log (1 + z) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith

/-- `min z 1 ≤ 2 z/(1+z)` for `z ≥ 0`. -/
theorem min_one_le_div {z : ℝ} (hz : 0 ≤ z) : min z 1 ≤ 2 * (z / (1 + z)) := by
  have hpos : 0 < 1 + z := by linarith
  have hswap : (2 : ℝ) * (z / (1 + z)) = 2 * z / (1 + z) := by ring
  rcases le_total z 1 with h | h
  · rw [min_eq_left h, hswap, le_div_iff₀ hpos]
    nlinarith
  · rw [min_eq_right h, hswap, le_div_iff₀ hpos]
    nlinarith

/-! ## Differentiability in `z` of the iterated `z`-derivatives of a smooth slice -/

theorem differentiableAt_pzIter_slice_smooth {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1)))
    (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := by
  have hgen : ∀ j : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.pzIter j h z' θ) (Set.Ioi (-1)) := by
    intro j
    induction j with
    | zero => simpa using hsm
    | succ j ih =>
      have h' : ContDiffOn ℝ Work.Stability.smoothOrder
          (deriv (fun z' => Work.Spaces.pzIter j h z' θ)) (Set.Ioi (-1)) :=
        ih.deriv_of_isOpen isOpen_Ioi (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
      simpa [Work.Spaces.pzIter_succ, Work.Spaces.pz] using h'
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := by
    have := Set.mem_Ioi.mp hz
    exact Set.mem_Ioi.mpr (by linarith)
  exact ((hgen k).contDiffAt (isOpen_Ioi.mem_nhds hz')).differentiableAt
    (by simp)

/-! ## The differentiated form of the identity `tan θ · 𝒰 = 𝒱 - ℛ`

`ℛ(Ψ) - 𝒱(Ψ) = tan θ·(3Ψ + αz∂_zΨ) = - tan θ·𝒰(Ψ)` (`Work.FTS.Nonlinear.Pieces.Rl1.
Rop_sub_Vop_eq_tan`), so `tan θ·𝒰 = 𝒱 - ℛ`.  Differentiating `k` times in `z` gives the
bounds on `∂_z^k𝒰` that the estimates need, since `∂_z^k𝒱` and `∂_z^kℛ` are `𝒲^{4,∞}`-bounded
by `StarPkg`. -/

theorem tan_pzIter_Uop_eq {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ k : ℕ, k ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      Real.tan θ * Work.Spaces.pzIter k
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
        = Work.Spaces.pzIter k (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ
          - Work.Spaces.pzIter k
              (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ := by
  have hsqPsi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hS.smooth
  -- the `z`-slices of `𝒰, 𝒱, ℛ` are `C^∞` on `(-1,∞)` at every interior angle
  have hsliceU : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioi (-1)) := fun θ' hθ' =>
    (Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsqPsi).curry_z hθ'
  have hsliceV : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioi (-1)) := by
    intro θ' hθ'
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z => Work.FTS.Nonlin.PhiTs α Φs z θ') (Set.Ioi (-1)) := hsqPsi.curry_z hθ'
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z => Work.Spaces.pth (Work.FTS.Nonlin.PhiTs α Φs) z θ')
        (Set.Ioi (-1)) :=
      (Work.FTS.H2.STQ.SmoothQuad.pth hsqPsi).curry_z hθ'
    have hc : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => Real.tan θ')
        (Set.Ioi (-1)) := contDiffOn_const
    have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z => Work.Spaces.pth (Work.FTS.Nonlin.PhiTs α Φs) z θ'
          - Real.tan θ' * Work.FTS.Nonlin.PhiTs α Φs z θ') (Set.Ioi (-1)) :=
      h2.sub (hc.mul h1)
    refine h3.congr ?_
    intro z hz
    simp only [Work.Construction.Vop]
  have hsliceR : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ')
      (Set.Ioi (-1)) := fun θ' hθ' =>
    (Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rop_PhiTs_smoothQuad hα hα1 hS.smooth).curry_z hθ'
  intro k
  induction k with
  | zero =>
    intro hk z θ hz hθ
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have h := Work.FTS.Nonlinear.Pieces.Rl1.Rop_sub_Vop_eq_tan α
      (Work.FTS.Nonlin.PhiTs α Φs) (z := z) hc
    have h2 : 3 * Work.FTS.Nonlin.PhiTs α Φs z θ
        + α * z * Work.Spaces.pz (Work.FTS.Nonlin.PhiTs α Φs) z θ
        = - (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
      simp only [Work.Construction.Uop]
      ring
    rw [h2] at h
    have h3 : Real.tan θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        = -(Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            - Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
      rw [h]; ring
    simpa using h3
  | succ k ih =>
    intro hk z θ hz hθ
    have hk' : k ≤ 4 := by omega
    have hev : (fun z' => Real.tan θ * Work.Spaces.pzIter k
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ)
        =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter k
              (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ
            - Work.Spaces.pzIter k
              (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show z ∈ Set.Ioi (0 : ℝ) from hz)] with z' hz'
      exact ih hk' z' θ hz' hθ
    have hderiv := Filter.EventuallyEq.deriv_eq hev
    have hdU := differentiableAt_pzIter_slice_smooth (hsliceU θ hθ) k hz
    have hdV := differentiableAt_pzIter_slice_smooth (hsliceV θ hθ) k hz
    have hdR := differentiableAt_pzIter_slice_smooth (hsliceR θ hθ) k hz
    have hL : deriv (fun z' => Real.tan θ * Work.Spaces.pzIter k
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) z
        = Real.tan θ * Work.Spaces.pzIter (k + 1)
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ := by
      rw [deriv_const_mul _ hdU]
      rfl
    have hR : deriv (fun z' => Work.Spaces.pzIter k
              (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ
            - Work.Spaces.pzIter k
              (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) z
        = Work.Spaces.pzIter (k + 1)
            (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ
          - Work.Spaces.pzIter (k + 1)
            (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ := by
      rw [show (fun z' => Work.Spaces.pzIter k
              (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ
            - Work.Spaces.pzIter k
              (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ)
          = ((fun z' => Work.Spaces.pzIter k
                (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ)
              - fun z' => Work.Spaces.pzIter k
                (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) from rfl]
      rw [deriv_sub hdV hdR]
      rfl
    rw [hL, hR] at hderiv
    simpa only [Work.Spaces.pzIter_succ] using hderiv

/-! ## The Stirling-weighted sum bound -/

/-- `scoef b 0 = 0` for `b ≥ 1`. -/
theorem scoef_zero_of_pos {b : ℕ} (hb : 1 ≤ b) : Work.Spaces.scoef b 0 = 0 := by
  cases b with
  | zero => omega
  | succ b' => rfl

/-- If `|x k| ≤ B r^k` for `k ≤ b` then the Stirling-weighted sum `∑_k S(b,k) x k` is bounded
by `bell b · B · r` (the term `k = 0` drops out because `S(b,0) = 0` for `b ≥ 1`). -/
theorem scoef_weighted_sum_le {b : ℕ} (hb : 1 ≤ b) {B r : ℝ} (hB : 0 ≤ B)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x : ℕ → ℝ) (hx : ∀ k ≤ b, |x k| ≤ B * r ^ k) :
    |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * x k|
      ≤ (Work.Spaces.bell b : ℝ) * B * r := by
  have hsz : Work.Spaces.scoef b 0 = 0 := scoef_zero_of_pos hb
  have h1 : |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * x k|
      ≤ ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (B * r ^ k) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef b k))]
    exact mul_le_mul_of_nonneg_left (hx k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      (Nat.cast_nonneg _)
  have h2 : ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (B * r ^ k)
      ≤ ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (B * r) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp [hsz]
    · have hpow : r ^ k ≤ r := pow_le_of_le_one hr0 hr1 (by omega)
      have hcoef : (0 : ℝ) ≤ (Work.Spaces.scoef b k : ℝ) * B :=
        mul_nonneg (Nat.cast_nonneg _) hB
      calc (Work.Spaces.scoef b k : ℝ) * (B * r ^ k)
          = ((Work.Spaces.scoef b k : ℝ) * B) * r ^ k := by ring
        _ ≤ ((Work.Spaces.scoef b k : ℝ) * B) * r :=
            mul_le_mul_of_nonneg_left hpow hcoef
        _ = (Work.Spaces.scoef b k : ℝ) * (B * r) := by ring
  have h3 : ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (B * r)
      = (Work.Spaces.bell b : ℝ) * (B * r) := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← Work.Spaces.bell]
  linarith [h1, h2, h3.le, h3.ge]

/-- `|D_z^b h| ≤ bell b · B · z/(1+z)` once `|∂_z^k h| ≤ B/(1+z)^k` for all `k ≤ b` (`b ≥ 1`),
on the open quadrant. -/
theorem DzIter_le_of_weighted {h : ℝ → ℝ → ℝ} {b : ℕ} {B : ℝ} (hB : 0 ≤ B) (hb : 1 ≤ b)
    (hsmooth : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1)))
    (hbound : ∀ k ≤ b, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter k h z θ| ≤ B / (1 + z) ^ k) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.DzIter b h z θ| ≤ (Work.Spaces.bell b : ℝ) * B * (z / (1 + z)) := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hr0 : 0 ≤ z / (1 + z) := by positivity
  have hr1 : z / (1 + z) ≤ 1 := by
    rw [div_le_one h1z]
    linarith
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (hsmooth θ hθ) b z hz1]
  refine scoef_weighted_sum_le hb hB hr0 hr1
    (fun k => z ^ k * Work.Spaces.pzIter k h z θ) ?_
  intro k hk
  have hb1 := hbound k hk z hz θ hθ
  have hzk : (0 : ℝ) ≤ z ^ k := by positivity
  rw [abs_mul, abs_of_nonneg hzk]
  have h2 : z ^ k * (B / (1 + z) ^ k) = B * (z / (1 + z)) ^ k := by
    rw [div_pow]
    field_simp
  calc z ^ k * |Work.Spaces.pzIter k h z θ| ≤ z ^ k * (B / (1 + z) ^ k) :=
        mul_le_mul_of_nonneg_left hb1 hzk
    _ = B * (z / (1 + z)) ^ k := h2

/-- The `𝒲^{5,∞}`-norm of `∂_θ𝒰(Φ̃_*)` is bounded by `max Cs 1 · α`. -/
theorem wle_dU {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) ≤ max Cs 1 * α :=
  le_trans hS.dU.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)

/-- `|∂_θ (D_z^b 𝒰(Φ̃_*))| ≤ bell b · max Cs 1 · α · z/(1+z)` on the open quadrant. -/
theorem pth_DzIter_Uop_bound {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ b : ℕ, 1 ≤ b → b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth (Work.Spaces.DzIter b (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ (Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)) := by
  intro b hb hb4 z hz θ hθ
  have hsqPsi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hS.smooth
  have hsqU : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsqPsi
  have hz1 : (-1 : ℝ) < z := by linarith [Set.mem_Ioi.mp hz]
  have hmem : (z, θ) ∈ Work.Spaces.quadU := ⟨hz1, hθ⟩
  have hid := Work.Blocks.DivSinHalf.pth_DzIter_eqOn Work.Spaces.isOpen_quadU hsqU b hmem
  have hkey : Work.Spaces.pth (Work.Spaces.DzIter b (Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTs α Φs))) z θ
      = Work.Spaces.DzIter b (Work.Spaces.pth (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs))) z θ := by
    simpa [Function.uncurry] using hid
  rw [hkey]
  have hBnn : 0 ≤ max Cs 1 * α :=
    mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1))) hα.le
  refine DzIter_le_of_weighted hBnn hb ?_ ?_ z hz θ hθ
  · intro θ' hθ'
    exact (Work.FTS.H2.STQ.SmoothQuad.pth hsqU).curry_z hθ'
  · intro k hk z' hz' θ' hθ'
    have hk5 : k ≤ 5 := by omega
    have h := Work.Spaces.pz_sup_bound α 5 (Work.Spaces.pth (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs))) hS.dU.1 k hk5 z' θ'
        (le_of_lt (Set.mem_Ioi.mp hz')) (Set.mem_Icc.mpr ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
    have h1z : (0 : ℝ) < 1 + z' := by linarith [Set.mem_Ioi.mp hz']
    have hpow : (0 : ℝ) < (1 + z') ^ k := pow_pos h1z k
    have h3 : (z' + 1) ^ k = (1 + z') ^ k := by ring
    calc |Work.Spaces.pzIter k (Work.Spaces.pth (Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTs α Φs))) z' θ'|
        ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTs α Φs))) / (z' + 1) ^ k := h
      _ = Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTs α Φs))) / (1 + z') ^ k := by rw [h3]
      _ ≤ max Cs 1 * α / (1 + z') ^ k :=
          div_le_div_of_nonneg_right (wle_dU hα hS) (le_of_lt hpow)

/-- **The `D_θ`-iterates of `𝒰(Φ̃_*)` carry a factor `sin 2θ`.**  For `1 ≤ a ≤ 4` and
`a + k ≤ 5`,
`|∂_z^k D_θ^a 𝒰(Φ̃_*)| ≤ 1000 · max Cs 1 · α · sin(2θ)(1 + sin(2θ)) / (1+z)^k`. -/
theorem DthIter_Uop_bound {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ a k : ℕ, 1 ≤ a → a ≤ 4 → a + k ≤ 5 → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pzIter k (Work.Spaces.DthIter a
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
            / (1 + z) ^ k := by
  intro a k ha ha4 hak z θ hz hθ
  have hsqPsi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hS.smooth
  have hsqU : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsqPsi
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hb3 : b ≤ 3 := by omega
  have hk4 : k ≤ 4 := by omega
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · -- `θ = 0`
    subst h0
    have hzero : Work.Spaces.pzIter k (Work.Spaces.DthIter (b + 1)
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z 0 = 0 := by
      refine Work.FTS.H2.STQ.pzIter_eq_zero_of_slice_zero (θ₀ := 0) ?_ k z
      intro z'
      exact Work.Spaces.DthIter_apply_zero (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs)) b z'
    rw [hzero, abs_zero]
    simp
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · -- `θ = π/2`
      subst h2
      have hzero : Work.Spaces.pzIter k (Work.Spaces.DthIter (b + 1)
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z (π / 2) = 0 := by
        refine Work.FTS.H2.STQ.pzIter_eq_zero_of_slice_zero (θ₀ := π / 2) ?_ k z
        intro z'
        exact Work.Spaces.DthIter_apply_pi_half (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs)) b z'
      rw [hzero, abs_zero, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
      simp
    · -- interior
      have hθi : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h2⟩
      have hs0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h2])
      have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hz1 : (0 : ℝ) < 1 + z := by linarith
      have hpow : (0 : ℝ) < (1 + z) ^ k := pow_pos hz1 k
      have hMα : 0 ≤ max Cs 1 * α :=
        mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1))) hα.le
      set U : ℝ := (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
        / (1 + z) ^ k with hU
      have hUnn : 0 ≤ U := by
        rw [hU]
        have h1 : (0 : ℝ) < max Cs 1 := lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)
        have h4 : (0 : ℝ) < 1 + Real.sin (2 * θ) := by linarith
        positivity
      rw [Work.FTS.H2.Q.pzIter_DthIter_expand_quad hsqU b k hb3 z (le_of_lt hz) θ hθi]
      have hterm : ∀ i ∈ Finset.range (b + 1),
          |((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
                  (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
            ≤ (b.choose i : ℝ) * (48 * U) := by
        intro i hi
        have hi3 : i ≤ 3 := by
          have := Finset.mem_range.mp hi
          omega
        have hsig : |Work.Elliptic.sigCoeff i θ| ≤ 48 :=
          Work.Elliptic.WtoW_f_sigCoeff_bound i hi3 θ
        have hcoef : (0 : ℝ) ≤ (b.choose i : ℝ) := Nat.cast_nonneg _
        have hsnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hs0
        -- the bound on the `∂_z^k D_θ^{b-i}(∂_θ𝒰)` factor
        have hb1 : |Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
            ≤ max Cs 1 * α * (1 + Real.sin (2 * θ)) / (1 + z) ^ k := by
          rcases Nat.eq_zero_or_pos (b - i) with hm0 | hmpos
          · rw [hm0, Work.Spaces.DthIter_zero]
            have h := Work.Spaces.pz_sup_bound α 5 (Work.Spaces.pth (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs))) hS.dU.1 k (by omega) z θ (le_of_lt hz)
                (Set.mem_Icc.mpr ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩)
            have h3 : (z + 1) ^ k = (1 + z) ^ k := by ring
            have h1s : 1 ≤ 1 + Real.sin (2 * θ) := by linarith
            calc |Work.Spaces.pzIter k (Work.Spaces.pth (Work.Construction.Uop α
                    (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
                ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
                    (Work.FTS.Nonlin.PhiTs α Φs))) / (z + 1) ^ k := h
              _ = Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
                    (Work.FTS.Nonlin.PhiTs α Φs))) / (1 + z) ^ k := by rw [h3]
              _ ≤ max Cs 1 * α / (1 + z) ^ k :=
                  div_le_div_of_nonneg_right (wle_dU hα hS) (le_of_lt hpow)
              _ ≤ max Cs 1 * α * (1 + Real.sin (2 * θ)) / (1 + z) ^ k :=
                  div_le_div_of_nonneg_right (le_mul_of_one_le_right hMα h1s)
                    (le_of_lt hpow)
          · have h := Work.Spaces.pz_Dth_sup_bound α hα 5 (Work.Spaces.pth
                (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) hS.dU.1 (b - i) k
                hmpos (by omega) z θ (le_of_lt hz)
                (Set.mem_Icc.mpr ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩)
            have h3 : (z + 1) ^ k = (1 + z) ^ k := by ring
            have h4 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤
                1 + Real.sin (2 * θ) := by
              have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
                Real.rpow_le_one hsnn hs1 (by linarith)
              have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsnn _
              nlinarith [hr, hr0, hsnn, hs1, hα, hα1]
            calc |Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
                    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
                ≤ Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
                    (Work.FTS.Nonlin.PhiTs α Φs))) / (z + 1) ^ k
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := h
              _ = Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
                    (Work.FTS.Nonlin.PhiTs α Φs))) / (1 + z) ^ k
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by rw [h3]
              _ ≤ max Cs 1 * α / (1 + z) ^ k * (1 + Real.sin (2 * θ)) :=
                  mul_le_mul (div_le_div_of_nonneg_right (wle_dU hα hS) (le_of_lt hpow))
                    h4 (by positivity) (by positivity)
              _ = max Cs 1 * α * (1 + Real.sin (2 * θ)) / (1 + z) ^ k := by ring
        -- factorise the absolute value
        have h1 : |((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
                  (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
            = (b.choose i : ℝ) * (Real.sin (2 * θ) * |Work.Elliptic.sigCoeff i θ|)
              * |Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
                  (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hsnn]
        rw [h1]
        calc (b.choose i : ℝ) * (Real.sin (2 * θ) * |Work.Elliptic.sigCoeff i θ|)
              * |Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
                  (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
            ≤ (b.choose i : ℝ) * (Real.sin (2 * θ) * 48)
              * (max Cs 1 * α * (1 + Real.sin (2 * θ)) / (1 + z) ^ k) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsig hsnn) hcoef) hb1 (abs_nonneg _) ?_
              have h1s : 0 ≤ 1 + Real.sin (2 * θ) := by linarith
              positivity
          _ ≤ (b.choose i : ℝ) * (48 * U) := by
              rw [show (b.choose i : ℝ) * (Real.sin (2 * θ) * 48)
                    * (max Cs 1 * α * (1 + Real.sin (2 * θ)) / (1 + z) ^ k)
                  = (b.choose i : ℝ) * ((Real.sin (2 * θ) * 48)
                    * (max Cs 1 * α * (1 + Real.sin (2 * θ)) / (1 + z) ^ k)) from by ring]
              refine mul_le_mul_of_nonneg_left ?_ hcoef
              rw [hU]
              have heq : Real.sin (2 * θ) * 48 * ((max Cs 1) * α * (1 + Real.sin (2 * θ))
                    / (1 + z) ^ k)
                  = 48 * ((max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                    / (1 + z) ^ k) := by
                ring
              rw [heq]
      calc |∑ i ∈ Finset.range (b + 1),
            ((b.choose i : ℝ) * (Real.sin (2 * θ) * Work.Elliptic.sigCoeff i θ))
              * Work.Spaces.pzIter k (Work.Spaces.DthIter (b - i) (Work.Spaces.pth
                  (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))) z θ|
          ≤ ∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * (48 * U) :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
        _ = (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ)) * (48 * U) := by
            rw [Finset.sum_mul]
        _ ≤ 1000 * U := by
            have hsum : (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ)) ≤ 8 := by
              have h1 : ∑ i ∈ Finset.range (b + 1), b.choose i = 2 ^ b :=
                Nat.sum_range_choose b
              calc (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ))
                  = ((2 ^ b : ℕ) : ℝ) := by rw [← h1, Nat.cast_sum]
                _ ≤ 8 := by
                    have h2 : (2 : ℕ) ^ b ≤ 8 := by
                      calc (2 : ℕ) ^ b ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hb3
                        _ = 8 := by norm_num
                    exact_mod_cast h2
            have h48 : (0 : ℝ) ≤ 48 * U := mul_nonneg (by norm_num) hUnn
            nlinarith [hsum, h48, hUnn]
        _ = 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
              / (1 + z) ^ k := by
            rw [hU]
            ring

theorem Uop_PhiTs_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < z →
      (∀ θ ∈ Work.Spaces.Iθ,
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ = 0) →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      (∀ θ ∈ Work.Spaces.Iθ,
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
          ≤ C * (Cs + 1) * α * Real.sin (2 * θ) * Real.log (1 + z)) ∧
      (∀ b : ℕ, 1 ≤ b → b ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DzIter b (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
          ≤ C * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z))) ∧
      (∀ a b : ℕ, 1 ≤ a → a + b ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DzIter b (Work.Spaces.DthIter a
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
          ≤ C * (Cs + 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
              * (z / (1 + z))) := by
  obtain ⟨KR, hKRpos, hKR⟩ := Work.FTS.Nonlinear.Pieces.RNP.Rop_pointwiseU
  refine ⟨10 ^ 8 * (KR + 1), by nlinarith [hKRpos], ?_⟩
  intro α Cs z Φs hα hα1 hS hz hU0 hTend
  -- ### basic facts
  have hCs : 0 ≤ Cs := Cs_nonneg_of_starPkg hα hS
  have hM1 : (1 : ℝ) ≤ max Cs 1 := le_max_right _ _
  have hMnn : 0 ≤ max Cs 1 := le_of_lt (lt_of_lt_of_le zero_lt_one hM1)
  have hCsM : Cs ≤ max Cs 1 := le_max_left _ _
  have hCsM1 : max Cs 1 ≤ Cs + 1 := by
    rcases le_total Cs 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hMα : 0 ≤ max Cs 1 * α := mul_nonneg hMnn hα.le
  have hA1 : 0 ≤ (Cs + 1) * α := mul_nonneg (by linarith) hα.le
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hlog : (0 : ℝ) ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  have hznn : (0 : ℝ) ≤ z := le_of_lt hz
  have hz1 : (-1 : ℝ) < z := by linarith
  -- ### the angular endpoint values of `𝒰(Φ̃_*)`
  have hUop0 : ∀ z', Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z' 0 = 0 := by
    intro z'
    have hPsi : Work.FTS.Nonlin.PhiTs α Φs z' 0 = 0 := by
      simp only [Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil, Work.Construction.Theta,
        Work.Construction.s2]
      rw [hS.sol.2.1 z', show Real.sin (2 * 0) = 0 by simp]
      ring
    have hslice : (fun z'' => Work.FTS.Nonlin.PhiTs α Φs z'' 0) = fun _ => (0 : ℝ) := by
      funext z''
      simp only [Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil, Work.Construction.Theta,
        Work.Construction.s2]
      rw [hS.sol.2.1 z'', show Real.sin (2 * 0) = 0 by simp]
      ring
    simp only [Work.Construction.Uop]
    rw [hPsi]
    have hpz : Work.Spaces.pz (Work.FTS.Nonlin.PhiTs α Φs) z' 0 = 0 := by
      simp only [Work.Spaces.pz]
      rw [hslice]
      simp
    rw [hpz]
    ring
  have hUopPi : ∀ z', Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z' (π / 2) = 0 := by
    intro z'
    have hsin : Real.sin (2 * (π / 2)) = 0 := by
      rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
    have hPsi : Work.FTS.Nonlin.PhiTs α Φs z' (π / 2) = 0 := by
      simp only [Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil, Work.Construction.Theta,
        Work.Construction.s2]
      rw [hS.sol.2.2.1 z', hsin]
      ring
    have hslice : (fun z'' => Work.FTS.Nonlin.PhiTs α Φs z'' (π / 2)) = fun _ => (0 : ℝ) := by
      funext z''
      simp only [Work.FTS.Nonlin.PhiTs, Work.Construction.PhiTil, Work.Construction.Theta,
        Work.Construction.s2]
      rw [hS.sol.2.2.1 z'', hsin]
      ring
    simp only [Work.Construction.Uop]
    rw [hPsi]
    have hpz : Work.Spaces.pz (Work.FTS.Nonlin.PhiTs α Φs) z' (π / 2) = 0 := by
      simp only [Work.Spaces.pz]
      rw [hslice]
      simp
    rw [hpz]
    ring
  -- ### the `D_z`-iterates of a function vanishing on an angular boundary line
  have hDz_zero : ∀ (F : ℝ → ℝ → ℝ), (∀ z', F z' 0 = 0) →
      ∀ b z', Work.Spaces.DzIter b F z' 0 = 0 := by
    intro F hF b
    induction b with
    | zero => intro z'; exact hF z'
    | succ b ih =>
      intro z'
      have h1 : (fun z'' => Work.Spaces.DzIter b F z'' 0) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [h1]
      simp
  have hDz_pi : ∀ (F : ℝ → ℝ → ℝ), (∀ z', F z' (π / 2) = 0) →
      ∀ b z', Work.Spaces.DzIter b F z' (π / 2) = 0 := by
    intro F hF b
    induction b with
    | zero => intro z'; exact hF z'
    | succ b ih =>
      intro z'
      have h1 : (fun z'' => Work.Spaces.DzIter b F z'' (π / 2)) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [h1]
      simp
  have hDth_z0 : ∀ (F : ℝ → ℝ → ℝ),
      (∀ θ'' ∈ Set.Ioo (0 : ℝ) (π / 2), F 0 θ'' = 0) →
      ∀ (a : ℕ) (θ'' : ℝ), θ'' ∈ Set.Ioo (0 : ℝ) (π / 2) →
        Work.Spaces.DthIter a F 0 θ'' = 0 := by
    intro F hF a
    induction a with
    | zero => intro θ'' hθ''; exact hF θ'' hθ''
    | succ a ih =>
      intro θ'' hθ''
      have hev : (fun θ''' => Work.Spaces.DthIter a F 0 θ''') =ᶠ[𝓝 θ''] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ''] with θ''' hθ'''
        exact ih θ''' hθ'''
      have hpz : Work.Spaces.pth (Work.Spaces.DthIter a F) 0 θ'' = 0 := by
        show deriv (fun θ''' => Work.Spaces.DthIter a F 0 θ''') θ'' = 0
        rw [Filter.EventuallyEq.deriv_eq hev]
        simp
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      rw [hpz, mul_zero]
  have hDth_zero : ∀ (F : ℝ → ℝ → ℝ) (a : ℕ), 1 ≤ a →
      ∀ z', Work.Spaces.DthIter a F z' 0 = 0 := by
    intro F a ha z'
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact Work.Spaces.DthIter_apply_zero F b z'
  have hDth_pi : ∀ (F : ℝ → ℝ → ℝ) (a : ℕ), 1 ≤ a →
      ∀ z', Work.Spaces.DthIter a F z' (π / 2) = 0 := by
    intro F a ha z'
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact Work.Spaces.DthIter_apply_pi_half F b z'
  -- ### the `StarPkg` bounds
  obtain ⟨hRp, hRpz, _, _⟩ := hKR hα hα1 hS
  have hVle : Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
      ≤ max Cs 1 * α :=
    le_trans hS.V.2 (mul_le_mul_of_nonneg_right hCsM hα.le)
  have hVbd : ∀ k ≤ 4, ∀ z' θ', z' ∈ Work.Spaces.Iz → θ' ∈ Work.Spaces.Iθ →
      |Work.Spaces.pzIter k (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'|
        ≤ max Cs 1 * α / (1 + z') ^ k := by
    intro k hk z' θ' hz' hθ'
    have h := Work.Spaces.pz_sup_bound α 4 (Work.Construction.Vop
      (Work.FTS.Nonlin.PhiTs α Φs)) hS.V.1 k hk z' θ' hz' hθ'
    have hz'0 : (0 : ℝ) ≤ z' := Set.mem_Ici.mp hz'
    have hp1 : (0 : ℝ) < 1 + z' := by linarith
    have hpow : (0 : ℝ) < (1 + z') ^ k := pow_pos hp1 k
    have h3 : (z' + 1) ^ k = (1 + z') ^ k := by ring
    calc |Work.Spaces.pzIter k (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'|
        ≤ Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
            / (z' + 1) ^ k := h
      _ = Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
            / (1 + z') ^ k := by rw [h3]
      _ ≤ max Cs 1 * α / (1 + z') ^ k :=
          div_le_div_of_nonneg_right hVle (le_of_lt hpow)
  -- ### the identity `tan θ · ∂_z^k 𝒰 = ∂_z^k 𝒱 - ∂_z^k ℛ` and its consequences
  have hident := tan_pzIter_Uop_eq hα hα1 hS
  have hUpz : ∀ k ≤ 4, ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.pzIter k (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'|
        ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ' / Real.sin θ') / (1 + z') ^ k := by
    intro k hk z' θ' hz' hθ'
    have hsinpos : 0 < Real.sin θ' :=
      Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [Real.pi_pos, hθ'.2])
    have htanpos : 0 < Real.tan θ' :=
      Real.tan_pos_of_pos_of_lt_pi_div_two hθ'.1 hθ'.2
    have hVpt : |Work.Spaces.pzIter k (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
        z' θ'| ≤ max Cs 1 * α / (1 + z') ^ k :=
      hVbd k hk z' θ' (le_of_lt hz')
        (Set.mem_Icc.mpr ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
    have hRpt : |Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))
        z' θ'| ≤ KR * (max Cs 1 * α) / (1 + z') ^ k := hRpz k hk z' hz' θ' hθ'
    have h4 : Real.tan θ' * |Work.Spaces.pzIter k (Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'|
        ≤ (1 + KR) * (max Cs 1 * α) / (1 + z') ^ k := by
      have habs : |Real.tan θ' * Work.Spaces.pzIter k (Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'|
          = Real.tan θ' * |Work.Spaces.pzIter k (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'| := by
        rw [abs_mul, abs_of_pos htanpos]
      rw [← habs, hident k hk z' θ' hz' hθ']
      calc |Work.Spaces.pzIter k (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'
              - Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))
                z' θ'|
          ≤ |Work.Spaces.pzIter k (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'|
            + |Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))
              z' θ'| := Work.FTS.H2.abs_sub_le_abs_add _ _
        _ ≤ max Cs 1 * α / (1 + z') ^ k + KR * (max Cs 1 * α) / (1 + z') ^ k :=
            add_le_add hVpt hRpt
        _ = (1 + KR) * (max Cs 1 * α) / (1 + z') ^ k := by ring
    calc |Work.Spaces.pzIter k (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))
            z' θ'|
        = Real.tan θ' * |Work.Spaces.pzIter k (Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTs α Φs)) z' θ'| / Real.tan θ' := by
          field_simp
      _ ≤ ((1 + KR) * (max Cs 1 * α) / (1 + z') ^ k) / Real.tan θ' :=
          div_le_div_of_nonneg_right h4 (le_of_lt htanpos)
      _ = (1 + KR) * (max Cs 1 * α) * (Real.cos θ' / Real.sin θ') / (1 + z') ^ k := by
          rw [Real.tan_eq_sin_div_cos]
          field_simp
  -- ### the structural bound for the `D_θ`-iterates
  have hDthU := DthIter_Uop_bound hα hα1 hS
  have hpthDzU := pth_DzIter_Uop_bound hα hα1 hS
  -- ### smoothness of the relevant slices
  have hsqPsi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hS.smooth
  have hsqU : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsqPsi
  -- ### the mean-value bound in `θ` (at the fixed `z`), from the `Tendsto` hypothesis
  have hMVTθ : ∀ (F : ℝ → ℝ → ℝ) (B : ℝ), 0 ≤ B →
      DifferentiableOn ℝ (fun θ' => F z θ') (Set.Ioo (0 : ℝ) (π / 2)) →
      Filter.Tendsto (fun θ' => F z θ') (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      (∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.pth F z θ'| ≤ B) →
      ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), |F z θ'| ≤ B * θ' := by
    intro F B hB hdiff htend hder θ' hθ'
    have h := mvt_tendsto_of_deriv_le (f := fun θ'' => F z θ'') (L := 0) (C := B)
      (θ₀ := π / 2) hB (by linarith [Real.pi_pos]) hdiff htend hder
    simpa using h.1 θ' hθ'
  -- ### the mean-value bound in `z` for a slice vanishing at `z = 0`
  have hMVTz : ∀ (F : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad F →
      ∀ (θ' : ℝ), θ' ∈ Set.Ioo (0 : ℝ) (π / 2) → F 0 θ' = 0 → ∀ B, 0 ≤ B →
      (∀ t ∈ Set.Ioo (0 : ℝ) z, |Work.Spaces.pz F t θ'| ≤ B) → |F z θ'| ≤ B * z := by
    intro F hsq θ' hθ' hzero B hB hbd
    have hcont : ContinuousOn (fun t => F t θ') (Set.Icc 0 z) :=
      ((hsq.curry_z hθ').continuousOn).mono (by
        intro t ht
        exact Set.mem_Ioi.mpr (by linarith [hz1, ht.1]))
    have hdiff : DifferentiableOn ℝ (fun t => F t θ') (Set.Ioo 0 z) :=
      ((hsq.curry_z hθ').differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).mono (by
        intro t ht
        exact Set.mem_Ioi.mpr (by linarith [hz1, ht.1]))
    exact mvt_z_of_value hz hcont hdiff hzero hbd
  refine ⟨?_, ?_, ?_⟩
  · -- ## the first conjunct
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hUop0 z, abs_zero, show Real.sin (2 * 0) = 0 by simp]
      simp
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        rw [hUopPi z, abs_zero, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
        simp
      · have hθi : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h2⟩
        have hsnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Iθ hθ
        have hsinpos : 0 < Real.sin θ :=
          Real.sin_pos_of_pos_of_lt_pi hθi.1 (by linarith [Real.pi_pos, hθi.2])
        have hcospos : 0 < Real.cos θ :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθi.1], hθi.2⟩
        have hUUdiff : ∀ (b : ℕ), DifferentiableOn ℝ
            (fun θ' => Work.Spaces.DzIter b (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs)) z θ') (Set.Ioo (0 : ℝ) (π / 2)) := fun b =>
          ((Work.FTS.LocData.SmoothQuad.DzIter hsqU b).curry_θ hz1).differentiableOn
            Work.FTS.LocData.smoothOrder_ne_zero
        -- the `θ`-mean-value bound
        have hder : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            |Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ'|
              ≤ max Cs 1 * α := by
          intro θ' hθ'
          have h := Work.Spaces.pz_sup_bound α 5 (Work.Spaces.pth (Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTs α Φs))) hS.dU.1 0 (by norm_num) z θ' (le_of_lt hz)
            (Set.mem_Icc.mpr ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
          have h' : |Work.Spaces.pzIter 0 (Work.Spaces.pth (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs))) z θ'| ≤ Work.Spaces.WlInf α 5
              (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) := by
            simpa using h
          exact le_trans h' (wle_dU hα hS)
        have hA : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
            ≤ θ * (max Cs 1 * α) := by
          have h := hMVTθ _ _ hMα (by simpa using hUUdiff 0)
            (by simpa using hTend 0 (by norm_num)) hder θ hθi
          simpa [mul_comm] using h
        -- the `z`-bound for `∂_θ𝒰` at the given `z`
        have hzslice : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            |Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ'|
              ≤ z * (max Cs 1 * α) := by
          intro θ' hθ'
          have hpthSlice : ContDiffOn ℝ Work.Stability.smoothOrder
              (fun t => Work.Spaces.pth (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) t θ') (Set.Ioi (-1)) :=
            (Work.FTS.H2.STQ.SmoothQuad.pth hsqU).curry_z hθ'
          have hp0 : Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))
              0 θ' = 0 := by
            have hev : (fun θ'' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ'')
                =ᶠ[𝓝 θ'] fun _ => (0 : ℝ) := by
              filter_upwards [isOpen_Ioo.mem_nhds hθ'] with θ'' hθ''
              exact hU0 θ'' (Set.mem_Icc.mpr ⟨le_of_lt hθ''.1, le_of_lt hθ''.2⟩)
            show deriv (fun θ'' => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)
              0 θ'') θ' = 0
            rw [Filter.EventuallyEq.deriv_eq hev]
            simp
          have hcont : ContinuousOn
              (fun t => Work.Spaces.pth (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) t θ') (Set.Icc 0 z) :=
            hpthSlice.continuousOn.mono (by
              intro t ht
              exact Set.mem_Ioi.mpr (by linarith [hz1, ht.1]))
          have hdiffp : DifferentiableOn ℝ
              (fun t => Work.Spaces.pth (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) t θ') (Set.Ioo 0 z) :=
            (hpthSlice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).mono (by
              intro t ht
              exact Set.mem_Ioi.mpr (by linarith [hz1, ht.1]))
          have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) z,
              |deriv (fun t' => Work.Spaces.pth (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) t' θ') t| ≤ max Cs 1 * α := by
            intro t ht
            show |Work.Spaces.pz (Work.Spaces.pth (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs))) t θ'| ≤ max Cs 1 * α
            have h := Work.Spaces.pz_sup_bound α 5 (Work.Spaces.pth (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs))) hS.dU.1 1 (by norm_num) t θ' (le_of_lt ht.1)
              (Set.mem_Icc.mpr ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩)
            have h1t : (1 : ℝ) ≤ t + 1 := by linarith [ht.1]
            have h2 : Work.Spaces.WlInf α 5 (Work.Spaces.pth (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs))) / (t + 1) ≤ max Cs 1 * α := by
              rw [div_le_iff₀ (by linarith)]
              nlinarith [wle_dU hα hS, h1t]
            exact le_trans (by simpa using h) h2
          simpa [mul_comm] using mvt_z_of_value hz hcont hdiffp hp0 hbd
        have hA2 : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
            ≤ θ * (z * (max Cs 1 * α)) := by
          have h := hMVTθ _ _ (mul_nonneg hznn hMα) (by simpa using hUUdiff 0)
            (by simpa using hTend 0 (by norm_num)) hzslice θ hθi
          simpa [mul_comm] using h
        -- the identity-based bounds
        have hKcot : 0 ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) := by
          have h1 : 0 < 1 + KR := by linarith
          positivity
        have hC1 : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
            ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) := by
          have h := hUpz 0 (by norm_num) z θ hz hθi
          simpa using h
        have hC2 : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
            ≤ z * ((1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ)) := by
          have hbdz : ∀ t ∈ Set.Ioo (0 : ℝ) z,
              |Work.Spaces.pz (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) t θ|
                ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) := by
            intro t ht
            have h := hUpz 1 (by norm_num) t θ ht.1 hθi
            have h1t : (1 : ℝ) ≤ 1 + t := by linarith [ht.1]
            have h2 : (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) / (1 + t)
                ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) := by
              rw [div_le_iff₀ (by linarith)]
              nlinarith [hKcot, h1t]
            have hpz1 : Work.Spaces.pzIter 1 (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) t θ
                = Work.Spaces.pz (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) t θ := rfl
            rw [hpz1, pow_one] at h
            exact le_trans h h2
          simpa [mul_comm] using hMVTz _ hsqU θ hθi (hU0 θ hθ) _ hKcot hbdz
        have hminlog : min z 1 ≤ 2 * Real.log (1 + z) := min_one_le_log hznn
        rcases le_total θ (π / 4) with h4 | h4
        · -- `θ ≤ π/4`
          have hθs : θ ≤ (π / 4) * Real.sin (2 * θ) := theta_le_sin_two hθ h4
          have hkey : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
              ≤ θ * (max Cs 1 * α) * min z 1 := by
            rcases le_total z 1 with hzle | hzge
            · rw [min_eq_left hzle]
              calc |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
                  ≤ θ * (z * (max Cs 1 * α)) := hA2
                _ = θ * (max Cs 1 * α) * z := by ring
            · rw [min_eq_right hzge]
              calc |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
                  ≤ θ * (max Cs 1 * α) := hA
                _ = θ * (max Cs 1 * α) * 1 := by ring
          have hfin : θ * (max Cs 1 * α) * min z 1
              ≤ (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z)) := by
            have h4' : θ * (max Cs 1 * α) ≤ ((π / 4) * Real.sin (2 * θ)) * (max Cs 1 * α) :=
              mul_le_mul_of_nonneg_right hθs hMα
            have h5 : 0 ≤ ((π / 4) * Real.sin (2 * θ)) * (max Cs 1 * α) := by
              have hπ4 : 0 ≤ π / 4 := by linarith [Real.pi_pos]
              positivity
            have h6 : min z 1 ≤ 2 * Real.log (1 + z) := hminlog
            have h7 : 0 ≤ min z 1 := le_min hznn zero_le_one
            calc θ * (max Cs 1 * α) * min z 1
                ≤ (((π / 4) * Real.sin (2 * θ)) * (max Cs 1 * α)) * (2 * Real.log (1 + z)) :=
                  mul_le_mul h4' h6 h7 h5
              _ ≤ (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z)) := by
                have hπ4 : (π / 4) ≤ 1 := by linarith [Real.pi_lt_four]
                have h1 : ((π / 4) * Real.sin (2 * θ)) * (max Cs 1 * α)
                    ≤ Real.sin (2 * θ) * (max Cs 1 * α) := by
                  have h2 : 0 ≤ Real.sin (2 * θ) * (max Cs 1 * α) := mul_nonneg hsnn hMα
                  nlinarith [hπ4, h2, hsnn, hMα]
                have h3 : 0 ≤ 2 * Real.log (1 + z) := by linarith [hlog]
                calc (((π / 4) * Real.sin (2 * θ)) * (max Cs 1 * α)) * (2 * Real.log (1 + z))
                    ≤ (Real.sin (2 * θ) * (max Cs 1 * α)) * (2 * Real.log (1 + z)) :=
                      mul_le_mul_of_nonneg_right h1 h3
                  _ = (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z)) := by ring
          have hstep : (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z))
              ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ) * Real.log (1 + z) := by
            have hK : (max Cs 1 * α) * 2 ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) := by
              have h1 : (2 : ℝ) ≤ 10 ^ 8 * (KR + 1) := by nlinarith [hKRpos]
              have h2 : max Cs 1 * α ≤ (Cs + 1) * α := mul_le_mul_of_nonneg_right hCsM1 hα.le
              have h3 : 0 ≤ max Cs 1 * α := hMα
              calc (max Cs 1 * α) * 2 = 2 * (max Cs 1 * α) := by ring
                _ ≤ 10 ^ 8 * (KR + 1) * (max Cs 1 * α) :=
                    mul_le_mul_of_nonneg_right h1 hMα
                _ ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) :=
                    mul_le_mul_of_nonneg_left h2 (by positivity)
            calc (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z))
                = ((max Cs 1 * α) * 2) * (Real.sin (2 * θ) * Real.log (1 + z)) := by ring
              _ ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α))
                    * (Real.sin (2 * θ) * Real.log (1 + z)) :=
                  mul_le_mul_of_nonneg_right hK (mul_nonneg hsnn hlog)
              _ = 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                    * Real.log (1 + z) := by ring
          linarith [hkey, hfin, hstep]
        · -- `π/4 ≤ θ`
          have hcot : Real.cos θ / Real.sin θ ≤ Real.sin (2 * θ) := cot_le_sin_two hθi h4
          have hkey : |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
              ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) * min z 1 := by
            rcases le_total z 1 with hzle | hzge
            · rw [min_eq_left hzle]
              calc |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
                  ≤ z * ((1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ)) := hC2
                _ = (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) * z := by ring
            · rw [min_eq_right hzge]
              calc |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
                  ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) := hC1
                _ = (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) * 1 := by ring
          have hfin : (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) * min z 1
              ≤ (1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z)) := by
            have h4' : (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ)
                ≤ (1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ) := by
              have h0' : 0 ≤ (1 + KR) * (max Cs 1 * α) := by
                have h1 : (0 : ℝ) < 1 + KR := by linarith
                positivity
              exact mul_le_mul_of_nonneg_left hcot h0'
            have h5 : 0 ≤ (1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ) := by
              have h1 : (0 : ℝ) < 1 + KR := by linarith
              positivity
            have h7 : 0 ≤ min z 1 := le_min hznn zero_le_one
            calc (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) * min z 1
                ≤ ((1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ)) * (2 * Real.log (1 + z)) :=
                  mul_le_mul h4' hminlog h7 h5
              _ = (1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ)
                    * (2 * Real.log (1 + z)) := by ring
          have hstep : (1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z))
              ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ) * Real.log (1 + z) := by
            have hK : (1 + KR) * (max Cs 1 * α) * 2
                ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) := by
              have h1 : (1 + KR) * 2 ≤ 10 ^ 8 * (KR + 1) := by nlinarith [hKRpos]
              have h2 : max Cs 1 * α ≤ (Cs + 1) * α := mul_le_mul_of_nonneg_right hCsM1 hα.le
              calc (1 + KR) * (max Cs 1 * α) * 2 = ((1 + KR) * 2) * (max Cs 1 * α) := by ring
                _ ≤ (10 ^ 8 * (KR + 1)) * (max Cs 1 * α) :=
                    mul_le_mul_of_nonneg_right h1 hMα
                _ ≤ (10 ^ 8 * (KR + 1)) * ((Cs + 1) * α) :=
                    mul_le_mul_of_nonneg_left h2 (by positivity)
            calc (1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ) * (2 * Real.log (1 + z))
                = ((1 + KR) * (max Cs 1 * α) * 2) * (Real.sin (2 * θ) * Real.log (1 + z)) := by
                  ring
              _ ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α))
                    * (Real.sin (2 * θ) * Real.log (1 + z)) :=
                  mul_le_mul_of_nonneg_right hK (mul_nonneg hsnn hlog)
              _ = 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                    * Real.log (1 + z) := by ring
          linarith [hkey, hfin, hstep]

  · -- ## the second conjunct
    intro b hb1 hb4 θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hDz_zero _ hUop0 b z, abs_zero, show Real.sin (2 * 0) = 0 by simp]
      simp
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        rw [hDz_pi _ hUopPi b z, abs_zero, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
        simp
      · have hθi : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h2⟩
        have hsnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Iθ hθ
        have hzf : 0 ≤ z / (1 + z) := div_nonneg hznn (le_of_lt h1z)
        have hzf1 : z / (1 + z) ≤ 1 := by
          rw [div_le_one h1z]
          linarith
        have hBnn : 0 ≤ (Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hMα) hzf
        have hUUdiff : DifferentiableOn ℝ
            (fun θ' => Work.Spaces.DzIter b (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs)) z θ') (Set.Ioo (0 : ℝ) (π / 2)) :=
          ((Work.FTS.LocData.SmoothQuad.DzIter hsqU b).curry_θ hz1).differentiableOn
            Work.FTS.LocData.smoothOrder_ne_zero
        have hderb : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
            |Work.Spaces.pth (Work.Spaces.DzIter b (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs))) z θ'|
              ≤ (Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)) :=
          fun θ' hθ' => hpthDzU b hb1 hb4 z (Set.mem_Ioi.mpr hz) θ' hθ'
        have hsmall := hMVTθ _ _ hBnn hUUdiff (by simpa using hTend b hb4) hderb θ hθi
        have hbell : (Work.Spaces.bell b : ℝ) ≤ 100 := by
          exact_mod_cast Work.Spaces.bell_le b hb4
        rcases le_total θ (π / 4) with h4 | h4
        · have hθs : θ ≤ (π / 4) * Real.sin (2 * θ) := theta_le_sin_two hθ h4
          have hstep : θ * ((Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)))
              ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)) := by
            have h1 : θ * ((Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)))
                ≤ ((π / 4) * Real.sin (2 * θ))
                  * ((Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z))) :=
              mul_le_mul_of_nonneg_right hθs hBnn
            have hKc : (π / 4) * (Work.Spaces.bell b : ℝ) * (max Cs 1 * α)
                ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) := by
              have h1' : (π / 4) * (Work.Spaces.bell b : ℝ) ≤ 10 ^ 8 * (KR + 1) := by
                nlinarith [hKRpos, hbell, Real.pi_pos, Real.pi_le_four]
              have h2' : max Cs 1 * α ≤ (Cs + 1) * α :=
                mul_le_mul_of_nonneg_right hCsM1 hα.le
              calc (π / 4) * (Work.Spaces.bell b : ℝ) * (max Cs 1 * α)
                  ≤ (10 ^ 8 * (KR + 1)) * (max Cs 1 * α) :=
                    mul_le_mul_of_nonneg_right h1' hMα
                _ ≤ (10 ^ 8 * (KR + 1)) * ((Cs + 1) * α) :=
                    mul_le_mul_of_nonneg_left h2' (by positivity)
            have h2 : ((π / 4) * Real.sin (2 * θ))
                  * ((Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)))
                ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)) := by
              calc ((π / 4) * Real.sin (2 * θ))
                    * ((Work.Spaces.bell b : ℝ) * (max Cs 1 * α) * (z / (1 + z)))
                  = ((π / 4) * (Work.Spaces.bell b : ℝ) * (max Cs 1 * α))
                    * (Real.sin (2 * θ) * (z / (1 + z))) := by ring
                _ ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α))
                    * (Real.sin (2 * θ) * (z / (1 + z))) :=
                    mul_le_mul_of_nonneg_right hKc (mul_nonneg hsnn hzf)
                _ = 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                    * (z / (1 + z)) := by ring
            linarith [h1, h2]
          linarith [hsmall, hstep]
        · -- `π/4 ≤ θ`: the identity-based bound
          have hsinpos : 0 < Real.sin θ :=
            Real.sin_pos_of_pos_of_lt_pi hθi.1 (by linarith [Real.pi_pos, hθi.2])
          have hcospos : 0 < Real.cos θ :=
            Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθi.1], hθi.2⟩
          have hcot : Real.cos θ / Real.sin θ ≤ Real.sin (2 * θ) := cot_le_sin_two hθi h4
          have hKcot : 0 ≤ (1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ) := by
            have h1 : (0 : ℝ) < 1 + KR := by linarith
            positivity
          have hkey : |Work.Spaces.DzIter b (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
              ≤ (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                  * (Real.cos θ / Real.sin θ)) * (z / (1 + z)) := by
            rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (hsqU.curry_z hθi) b z hz1]
            refine scoef_weighted_sum_le hb1 hKcot hzf hzf1
              (fun k => z ^ k * Work.Spaces.pzIter k (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) z θ) ?_
            intro k hk
            have hk4 : k ≤ 4 := by omega
            have hpow : (0 : ℝ) ≤ z ^ k := by positivity
            have hb' := hUpz k hk4 z θ hz hθi
            rw [abs_mul, abs_of_nonneg hpow]
            have h2 : z ^ k * ((1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ)
                  / (1 + z) ^ k)
                = ((1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ))
                  * (z / (1 + z)) ^ k := by
              rw [div_pow]
              field_simp
            calc z ^ k * |Work.Spaces.pzIter k (Work.Construction.Uop α
                    (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                ≤ z ^ k * ((1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ)
                    / (1 + z) ^ k) := mul_le_mul_of_nonneg_left hb' hpow
              _ = ((1 + KR) * (max Cs 1 * α) * (Real.cos θ / Real.sin θ))
                    * (z / (1 + z)) ^ k := h2
          have hstep : (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                * (Real.cos θ / Real.sin θ)) * (z / (1 + z))
              ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)) := by
            have h1 : (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                  * (Real.cos θ / Real.sin θ))
                ≤ (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                    * Real.sin (2 * θ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              exact mul_le_mul_of_nonneg_left hcot (by
                have h1 : (0 : ℝ) < 1 + KR := by linarith
                positivity)
            have h2 : (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                  * Real.sin (2 * θ))
                ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α)) * Real.sin (2 * θ) := by
              have hKc : (Work.Spaces.bell b : ℝ) * (1 + KR) * (max Cs 1 * α)
                  ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) := by
                have h1' : (Work.Spaces.bell b : ℝ) * (1 + KR) ≤ 10 ^ 8 * (KR + 1) := by
                  nlinarith [hKRpos, hbell]
                have h2' : max Cs 1 * α ≤ (Cs + 1) * α :=
                  mul_le_mul_of_nonneg_right hCsM1 hα.le
                calc (Work.Spaces.bell b : ℝ) * (1 + KR) * (max Cs 1 * α)
                    ≤ (10 ^ 8 * (KR + 1)) * (max Cs 1 * α) :=
                      mul_le_mul_of_nonneg_right h1' hMα
                  _ ≤ (10 ^ 8 * (KR + 1)) * ((Cs + 1) * α) :=
                      mul_le_mul_of_nonneg_left h2' (by positivity)
              calc (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α) * Real.sin (2 * θ))
                  = ((Work.Spaces.bell b : ℝ) * (1 + KR) * (max Cs 1 * α)) * Real.sin (2 * θ) := by
                    ring
                _ ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α)) * Real.sin (2 * θ) :=
                    mul_le_mul_of_nonneg_right hKc hsnn
            calc (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                  * (Real.cos θ / Real.sin θ)) * (z / (1 + z))
                ≤ (Work.Spaces.bell b : ℝ) * ((1 + KR) * (max Cs 1 * α)
                    * Real.sin (2 * θ)) * (z / (1 + z)) :=
                  mul_le_mul_of_nonneg_right h1 hzf
              _ ≤ ((10 ^ 8 * (KR + 1) * ((Cs + 1) * α)) * Real.sin (2 * θ)) * (z / (1 + z)) :=
                  mul_le_mul_of_nonneg_right h2 hzf
              _ = 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)) := by ring
          linarith [hkey, hstep]

  · -- ## the third conjunct
    intro a b ha1 hab θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hDz_zero _ (fun z' => hDth_zero _ a ha1 z') b z, abs_zero,
        show Real.sin (2 * 0) = 0 by simp]
      simp
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        rw [hDz_pi _ (fun z' => hDth_pi _ a ha1 z') b z, abs_zero,
          show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
        simp
      · have hθi : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h2⟩
        have hsnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Iθ hθ
        have hzf : 0 ≤ z / (1 + z) := div_nonneg hznn (le_of_lt h1z)
        have hzf1 : z / (1 + z) ≤ 1 := by
          rw [div_le_one h1z]
          linarith
        have hB0 : 0 ≤ 1000 * (max Cs 1) * α * Real.sin (2 * θ)
            * (1 + Real.sin (2 * θ)) := by positivity
        have hC1 : 0 ≤ Real.sin (2 * θ) * (1 + Real.sin (2 * θ)) :=
          mul_nonneg hsnn (by linarith)
        have hAA : 0 ≤ (Cs + 1) * α := hA1
        rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · subst hb0
          rw [Work.Spaces.DzIter_zero]
          have hzz : 2 * (z / (1 + z)) = 2 * z / (1 + z) := by ring
          have hstep : 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                * (2 * (z / (1 + z)))
              ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                  * (1 + Real.sin (2 * θ)) * (z / (1 + z)) := by
            have hKc : 2000 * (max Cs 1 * α) ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) := by
              have h1' : (2000 : ℝ) ≤ 10 ^ 8 * (KR + 1) := by nlinarith [hKRpos]
              have h2' : max Cs 1 * α ≤ (Cs + 1) * α := mul_le_mul_of_nonneg_right hCsM1 hα.le
              calc 2000 * (max Cs 1 * α) ≤ (10 ^ 8 * (KR + 1)) * (max Cs 1 * α) :=
                    mul_le_mul_of_nonneg_right h1' hMα
                _ ≤ (10 ^ 8 * (KR + 1)) * ((Cs + 1) * α) :=
                    mul_le_mul_of_nonneg_left h2' (by positivity)
            calc 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                  * (2 * (z / (1 + z)))
                = (2000 * (max Cs 1 * α)) * (Real.sin (2 * θ) * (1 + Real.sin (2 * θ)))
                  * (z / (1 + z)) := by ring
              _ ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α))
                    * (Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * (z / (1 + z)) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hKc hC1) hzf
              _ = 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                    * (1 + Real.sin (2 * θ)) * (z / (1 + z)) := by ring
          rcases le_total z 1 with hzle | hzge
          · have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) z,
                |Work.Spaces.pz (Work.Spaces.DthIter a (Work.Construction.Uop α
                  (Work.FTS.Nonlin.PhiTs α Φs))) t θ|
                  ≤ 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)) := by
              intro t ht
              have h := hDthU a 1 ha1 (by omega) (by omega) t θ ht.1
                (Set.mem_Icc.mpr ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩)
              rw [pow_one] at h
              have h1t : (1 : ℝ) ≤ 1 + t := by linarith [ht.1]
              have h2' : 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                    / (1 + t)
                  ≤ 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)) := by
                rw [div_le_iff₀ (by linarith)]
                nlinarith [hB0, h1t]
              exact le_trans h h2'
            have hM := hMVTz (Work.Spaces.DthIter a (Work.Construction.Uop α
              (Work.FTS.Nonlin.PhiTs α Φs))) (Work.FTS.LocData.SmoothQuad.DthIter hsqU a)
              θ hθi (hDth_z0 (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))
                (fun θ'' hθ'' => hU0 θ'' (Set.mem_Icc.mpr
                  ⟨le_of_lt hθ''.1, le_of_lt hθ''.2⟩)) a θ hθi) _ hB0 hbd
            have h1 : |Work.Spaces.DthIter a (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                ≤ (1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * z := hM
            have hle : z ≤ 2 * (z / (1 + z)) := by
              rw [hzz, le_div_iff₀ h1z]
              nlinarith
            have h2'' : (1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * z
                ≤ (1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)))
                  * (2 * (z / (1 + z))) := mul_le_mul_of_nonneg_left hle hB0
            linarith [h1, h2'', hstep]
          · have h1 : |Work.Spaces.DthIter a (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                ≤ 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)) := by
              have h := hDthU a 0 ha1 (by omega) (by omega) z θ hz hθ
              rw [pow_zero] at h
              simpa using h
            have hge : (1 : ℝ) ≤ 2 * (z / (1 + z)) := by
              rw [hzz, le_div_iff₀ h1z]
              nlinarith
            have h2'' : 1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                ≤ (1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)))
                  * (2 * (z / (1 + z))) := le_mul_of_one_le_right hB0 hge
            linarith [h1, h2'', hstep]
        · -- `1 ≤ b`: the Stirling expansion
          have hkey : |Work.Spaces.DzIter b (Work.Spaces.DthIter a (Work.Construction.Uop α
                (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
              ≤ (Work.Spaces.bell b : ℝ) * (1000 * (max Cs 1) * α * Real.sin (2 * θ)
                  * (1 + Real.sin (2 * θ))) * (z / (1 + z)) := by
            rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth
              ((Work.FTS.LocData.SmoothQuad.DthIter hsqU a).curry_z hθi) b z hz1]
            refine scoef_weighted_sum_le hbpos hB0 hzf hzf1
              (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a
                (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ) ?_
            intro k hk
            have hpow : (0 : ℝ) ≤ z ^ k := by positivity
            have hb' := hDthU a k ha1 (by omega) (by omega) z θ hz hθ
            rw [abs_mul, abs_of_nonneg hpow]
            have h2' : z ^ k * (1000 * (max Cs 1) * α * Real.sin (2 * θ)
                  * (1 + Real.sin (2 * θ)) / (1 + z) ^ k)
                = (1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)))
                  * (z / (1 + z)) ^ k := by
              rw [div_pow]
              field_simp
            calc z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter a
                    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
                ≤ z ^ k * (1000 * (max Cs 1) * α * Real.sin (2 * θ)
                    * (1 + Real.sin (2 * θ)) / (1 + z) ^ k) :=
                  mul_le_mul_of_nonneg_left hb' hpow
              _ = (1000 * (max Cs 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ)))
                    * (z / (1 + z)) ^ k := h2'
          have hbell : (Work.Spaces.bell b : ℝ) ≤ 100 := by
            exact_mod_cast Work.Spaces.bell_le b (by omega)
          have hstep : (Work.Spaces.bell b : ℝ) * (1000 * (max Cs 1) * α
                * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * (z / (1 + z))
              ≤ 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                  * (1 + Real.sin (2 * θ)) * (z / (1 + z)) := by
            have hKc : (Work.Spaces.bell b : ℝ) * 1000 * (max Cs 1 * α)
                ≤ 10 ^ 8 * (KR + 1) * ((Cs + 1) * α) := by
              have h1' : (Work.Spaces.bell b : ℝ) * 1000 ≤ 10 ^ 8 * (KR + 1) := by
                nlinarith [hKRpos, hbell]
              have h2' : max Cs 1 * α ≤ (Cs + 1) * α :=
                mul_le_mul_of_nonneg_right hCsM1 hα.le
              calc (Work.Spaces.bell b : ℝ) * 1000 * (max Cs 1 * α)
                  ≤ (10 ^ 8 * (KR + 1)) * (max Cs 1 * α) :=
                    mul_le_mul_of_nonneg_right h1' hMα
                _ ≤ (10 ^ 8 * (KR + 1)) * ((Cs + 1) * α) :=
                    mul_le_mul_of_nonneg_left h2' (by positivity)
            calc (Work.Spaces.bell b : ℝ) * (1000 * (max Cs 1) * α
                  * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * (z / (1 + z))
                = ((Work.Spaces.bell b : ℝ) * 1000 * (max Cs 1 * α))
                  * (Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * (z / (1 + z)) := by ring
              _ ≤ (10 ^ 8 * (KR + 1) * ((Cs + 1) * α))
                    * (Real.sin (2 * θ) * (1 + Real.sin (2 * θ))) * (z / (1 + z)) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hKc hC1) hzf
              _ = 10 ^ 8 * (KR + 1) * (Cs + 1) * α * Real.sin (2 * θ)
                    * (1 + Real.sin (2 * θ)) * (z / (1 + z)) := by ring
          linarith [hkey, hstep]


end Work.FTS.Nonlinear.Pieces.RNP.row15aux

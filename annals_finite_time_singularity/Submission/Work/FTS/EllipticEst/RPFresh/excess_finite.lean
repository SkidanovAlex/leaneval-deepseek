import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.RPFresh.MixedAGN_finite
import Submission.Work.Blocks.HkMem_of_majorant_aesm

import Submission.Work.FTS.EllipticEst.Alpha4.slice_key
import Submission.Work.FTS.EllipticEst.Alpha4.cut_integration
import Submission.Work.FTS.EllipticEst.Alpha4.radial_ibp_weight
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.Alpha4.ibp_bounds
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_exists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
## The `ℋ⁰`-integrand on the open quadrant

`ℋ⁰` is the *radial* level of the weighted `ℋ^k`-integrands: `HkIntegrand α 0 f z θ` is exactly
the square `(f z θ · w(z)/sin(2θ)^{η/2})²`, and it vanishes identically on the two angular
boundary lines and on the axis `z = 0` (both weights degenerate there).  Hence the `ℋ⁰`-vocabulary
is invariant under changes of the function outside the *open* quadrant
`Q0 = (0,∞) × (0,π/2)`, which is what lets us transfer the `ℋ⁰`-membership along identities that
only hold on `Q0`.
-/

/-- The open quadrant sits inside the neighbourhood defining `SmoothNbhd`. -/
theorem Q0_subset_nbhU :
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) ⊆ Work.Spaces.nbhU := by
  intro p hp
  show (-1 : ℝ) < p.1 ∧ (-1 : ℝ) < p.2 ∧ p.2 < Real.pi / 2 + 1
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩

/-- Smoothness on a neighbourhood of the closed quadrant gives `SmoothOpen`. -/
theorem smoothNbhd_smoothOpen {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    Work.FTS.EllipticEst.SmoothOpen f := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Work.FTS.EllipticEst.Q0
  exact (h.mono Q0_subset_nbhU).of_le le_top

theorem smoothNbhd_contDiffOn_Q0 {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (smoothNbhd_smoothOpen h).forall n

/-- Multiplication of a `SmoothOpen` function by the polynomial `z²` stays `SmoothOpen`. -/
theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ => z ^ 2 * g z θ)
      = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry g := by funext p; rfl
  rw [hfun]
  exact (contDiffOn_fst.pow 2).mul hg

/-! ## The `ℋ⁰`-integrand -/

/-- `HkIntegrand α 0 f` is the weighted square of `f`. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- The `ℋ⁰`-integrand vanishes at `z = 0`. -/
theorem HkIntegrand_zero_zero {α : ℝ} (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f 0 θ = 0 := by
  rw [HkIntegrand_zero_eq]
  simp [Work.Spaces.w]

/-- The `ℋ⁰`-integrand vanishes at `θ = 0`. -/
theorem HkIntegrand_zero_theta_zero {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [HkIntegrand_zero_eq, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- The `ℋ⁰`-integrand vanishes at `θ = π/2`. -/
theorem HkIntegrand_zero_theta_pi {α : ℝ} (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [HkIntegrand_zero_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  simp

/-- The `ℋ⁰`-integrand of a function continuous on the open quadrant is continuous there. -/
theorem continuousOn_HkIntegrand_zero {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      = fun p : ℝ × ℝ => (f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    funext p
    exact HkIntegrand_zero_eq α f p.1 p.2
  rw [hfun]
  exact (hf.mul (Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2

/-! ## `ℋ⁰`-membership: domination, congruence, addition -/

/-- **`ℋ⁰`-membership by a pointwise majorant.**  If `f` is continuous on the open quadrant and
`HkIntegrand α 0 f` is dominated on the closed quadrant by a function whose angular slices are
integrable and whose slice-integral is integrable, then `f ∈ ℋ⁰`. -/
theorem HkMem_zero_of_majorant {α : ℝ} {f M : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMsl : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 f z θ ≤ M z θ) :
    Work.Spaces.HkMem α 0 f := by
  have hC := continuousOn_HkIntegrand_zero (α := α) hf
  refine Work.Blocks.HkMem_of_majorant_aesm (α := α) (k := 0) (f := f) (M := M) ?_ ?_ hMsl hMz hle
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine (MeasureTheory.aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).congr ?_
      filter_upwards with θ
      exact (HkIntegrand_zero_zero (α := α) f θ).symm
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hC hz0
  · exact (Work.Spaces.aesm_of_continuousOn_Qd _ hC).integral_prod_right'

/-- **`ℋ⁰`-membership transfers along an identity on the open quadrant.** -/
theorem HkMem_zero_congr {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.Spaces.HkMem α 0 g) :
    Work.Spaces.HkMem α 0 f := by
  refine HkMem_zero_of_majorant (α := α) (f := f)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 g z θ) hf ?_ ?_ ?_
  · intro z hz
    exact (hg.1 z hz).const_mul 2
  · have h' := hg.2.const_mul 2
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz_eq | hz0
    · rw [← hz_eq, HkIntegrand_zero_zero]
      exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ)
    · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ0
      · rw [← hθ_eq, HkIntegrand_zero_theta_zero]
        exact mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 0 g z 0)
      · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ1
        · rw [hθ_eq, HkIntegrand_zero_theta_pi]
          exact mul_nonneg (by norm_num)
            (Work.Spaces.HkIntegrand_nonneg α 0 g z (Real.pi / 2))
        · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, h z θ hz0 hθ0 hθ1]
          nlinarith [sq_nonneg (g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

/-- **`ℋ⁰`-membership is closed under addition.** -/
theorem HkMem_zero_add {α : ℝ} {g₁ g₂ : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry (fun z θ => g₁ z θ + g₂ z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h₁ : Work.Spaces.HkMem α 0 g₁) (h₂ : Work.Spaces.HkMem α 0 g₂) :
    Work.Spaces.HkMem α 0 (fun z θ => g₁ z θ + g₂ z θ) := by
  refine HkMem_zero_of_majorant (α := α) (f := fun z θ => g₁ z θ + g₂ z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α 0 g₁ z θ
      + 2 * Work.Spaces.HkIntegrand α 0 g₂ z θ) hcont ?_ ?_ ?_
  · intro z hz
    exact ((h₁.1 z hz).const_mul 2).add ((h₂.1 z hz).const_mul 2)
  · have h' := (h₁.2.const_mul 2).add (h₂.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((h₁.1 z hz).const_mul 2)
      ((h₂.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rw [HkIntegrand_zero_eq]
    set a := g₁ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with ha
    set b := g₂ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hb
    have hab : (g₁ z θ + g₂ z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) = a + b := by
      rw [ha, hb]; ring
    rw [hab]
    rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq]
    nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-! ## Single radial summands of an honest `ℋ^k`-integrand -/

/-- **A single radial summand of an honest `ℋ^k`-integrand is honest in `ℋ⁰`.**  For `i ≤ k` the
`i`-th radial summand of `HkIntegrand α k f` is `HkIntegrand α 0 (D_z^i f)`, and it is dominated
by `HkIntegrand α k f`; both honesty requirements transfer. -/
theorem excess_zsummand_mem (α : ℝ) (k i : ℕ) (f : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α k f) (hi : i ≤ k) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f) := by
  refine HkMem_zero_of_majorant (α := α) (f := Work.Spaces.DzIter i f)
    (M := fun z θ => Work.Spaces.HkIntegrand α k f z θ) hcont (fun z hz => hmem.1 z hz)
    hmem.2 ?_
  intro z hz θ hθ
  rw [HkIntegrand_zero_eq]
  exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi

/-! ## The two radial summands at levels `k + 1` and `k + 2` -/

/-- **The decomposition `D_z^{m+1}Ψ = D_z^{m-1}(z²∂_z²Ψ) + D_z^mΨ`** on the open quadrant, for
`m ≥ 1`, from `z²∂_z²Ψ = D_z²Ψ - D_zΨ` and additivity of the iterates of `D_z`. -/
theorem dzIter_succ_decomp {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter (m + 1) Ψ z θ
        = Work.Spaces.DzIter (m - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + Work.Spaces.DzIter m Ψ z θ := by
  intro z θ hz hθ0 hθ1
  have hQ : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.DzIter 2 Ψ z' θ'
        = (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z' θ'
          + Work.Spaces.DzIter 1 Ψ z' θ' := by
    intro z' θ' hz' hθ0' hθ1'
    have h := Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hΨ hz' ⟨hθ0', hθ1'⟩
    have hQop : Work.FTS.EllipticEst.DzAmgm.Qop Ψ z' θ'
        = z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ' := rfl
    show Work.Spaces.DzIter 2 Ψ z' θ'
      = z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ' + Work.Spaces.DzIter 1 Ψ z' θ'
    rw [← hQop]
    linarith [h]
  have e1 : Work.Spaces.DzIter (m + 1) Ψ
      = Work.Spaces.DzIter (m - 1) (Work.Spaces.DzIter 2 Ψ) := by
    have h := Work.Spaces.DzIter_add_right (m - 1) 2 Ψ
    rw [show m - 1 + 2 = m + 1 from by omega] at h
    exact h
  have hQso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul (hΨ.pzIter 2)
  calc Work.Spaces.DzIter (m + 1) Ψ z θ
      = Work.Spaces.DzIter (m - 1) (Work.Spaces.DzIter 2 Ψ) z θ := by rw [e1]
    _ = Work.Spaces.DzIter (m - 1) (fun z θ =>
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + Work.Spaces.DzIter 1 Ψ z θ) z θ :=
        Work.FTS.EllipticEst.SmoothOpen.DzIter_congr hQ (m - 1) z θ hz hθ0 hθ1
    _ = Work.Spaces.DzIter (m - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + Work.Spaces.DzIter (m - 1) (Work.Spaces.DzIter 1 Ψ) z θ :=
        Work.FTS.EllipticEst.SmoothOpen.DzIter_add hQso (hΨ.Dz) (m - 1) z θ hz hθ0 hθ1
    _ = Work.Spaces.DzIter (m - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + Work.Spaces.DzIter m Ψ z θ := by
        rw [← Work.Spaces.DzIter_add_right (m - 1) 1 Ψ, show m - 1 + 1 = m from by omega]

/-- **The decomposition `D_z^{m+2}Ψ = D_z^m(z²∂_z²Ψ) + D_z^{m+1}Ψ`** on the open quadrant. -/
theorem dzIter_succ_succ_decomp {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (m : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter (m + 2) Ψ z θ
        = Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + Work.Spaces.DzIter (m + 1) Ψ z θ := by
  intro z θ hz hθ0 hθ1
  have hQ : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.DzIter 2 Ψ z' θ'
        = (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z' θ'
          + Work.Spaces.DzIter 1 Ψ z' θ' := by
    intro z' θ' hz' hθ0' hθ1'
    have h := Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hΨ hz' ⟨hθ0', hθ1'⟩
    have hQop : Work.FTS.EllipticEst.DzAmgm.Qop Ψ z' θ'
        = z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ' := rfl
    show Work.Spaces.DzIter 2 Ψ z' θ'
      = z' ^ 2 * Work.Spaces.pzIter 2 Ψ z' θ' + Work.Spaces.DzIter 1 Ψ z' θ'
    rw [← hQop]
    linarith [h]
  have e1 : Work.Spaces.DzIter (m + 2) Ψ
      = Work.Spaces.DzIter m (Work.Spaces.DzIter 2 Ψ) :=
    Work.Spaces.DzIter_add_right m 2 Ψ
  have hQso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    smoothOpen_zsq_mul (hΨ.pzIter 2)
  calc Work.Spaces.DzIter (m + 2) Ψ z θ
      = Work.Spaces.DzIter m (Work.Spaces.DzIter 2 Ψ) z θ := by rw [e1]
    _ = Work.Spaces.DzIter m (fun z θ =>
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + Work.Spaces.DzIter 1 Ψ z θ) z θ :=
        Work.FTS.EllipticEst.SmoothOpen.DzIter_congr hQ m z θ hz hθ0 hθ1
    _ = Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + Work.Spaces.DzIter m (Work.Spaces.DzIter 1 Ψ) z θ :=
        Work.FTS.EllipticEst.SmoothOpen.DzIter_add hQso (hΨ.Dz) m z θ hz hθ0 hθ1
    _ = Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + Work.Spaces.DzIter (m + 1) Ψ z θ := by
        rw [← Work.Spaces.DzIter_add_right m 1 Ψ]

/-- **The `ℋ⁰`-memberships of `D_z^{k+1}Ψ` and `D_z^{k+2}Ψ`** for the data of `EllHyp`, from the
fields `HkMem α k Ψ` and `HkMem α k (z²∂_z²Ψ)` and the two pointwise decompositions. -/
theorem EllHyp_dzIter_succ_mem (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hk : 2 ≤ k) (hE : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter (k + 1) Ψ) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter (k + 2) Ψ) := by
  have h1 : 1 ≤ k := by omega
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothInt hE.smooth
  have hQso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq_mul (hso.pzIter 2)
  have hcontQ : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun i => (hQso.DzIter i).continuousOn
  have hcontΨ : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter i Ψ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun i => (hso.DzIter i).continuousOn
  have hA : Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    excess_zsummand_mem α k (k - 1) _ (hcontQ (k - 1)) hE.memZ2 (by omega)
  have hB : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter k Ψ) :=
    excess_zsummand_mem α k k _ (hcontΨ k) hE.memPsi le_rfl
  have hC : Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    excess_zsummand_mem α k k _ (hcontQ k) hE.memZ2 le_rfl
  -- `D_z^{k+1}Ψ = D_z^{k-1}(z²∂²Ψ) + D_z^kΨ`
  have hsum1 : Work.Spaces.HkMem α 0 (fun z θ =>
      Work.Spaces.DzIter (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + Work.Spaces.DzIter k Ψ z θ) :=
    HkMem_zero_add ((hQso.DzIter (k - 1)).continuousOn.add (hso.DzIter k).continuousOn)
      hA hB
  have h1mem : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter (k + 1) Ψ) :=
    HkMem_zero_congr ((hso.DzIter (k + 1)).continuousOn)
      (fun z θ hz hθ0 hθ1 => dzIter_succ_decomp hso k h1 z θ hz hθ0 hθ1) hsum1
  -- `D_z^{k+2}Ψ = D_z^k(z²∂²Ψ) + D_z^{k+1}Ψ`
  have hsum2 : Work.Spaces.HkMem α 0 (fun z θ =>
      Work.Spaces.DzIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + Work.Spaces.DzIter (k + 1) Ψ z θ) :=
    HkMem_zero_add ((hQso.DzIter k).continuousOn.add (hso.DzIter (k + 1)).continuousOn)
      hC h1mem
  have h2mem : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter (k + 2) Ψ) :=
    HkMem_zero_congr ((hso.DzIter (k + 2)).continuousOn)
      (fun z θ hz hθ0 hθ1 => dzIter_succ_succ_decomp hso k z θ hz hθ0 hθ1) hsum2
  exact ⟨h1mem, h2mem⟩

/-! ## The finiteness transfer for the mixed interpolation

`D_z∂_θG` is bounded in `L²(ρ)` (`ρ = w²σ`, `σ = sin(2θ)^{-η}`) by the three quantities
`dInt G = ∫∫(D_zG)²ρ`, `ttInt G = ∫∫(∂_θ²G)²ρ` and `ddInt G = ∫∫(D_z²G)²ρ`:

* the *slicewise* Hardy-type inequality `slice_key` gives, for every `z > 0`,
  `κ ∫_θ (D_z∂_θG)²σ ≤ -∫_θ (D_zG)(∂_θ²G)σ + c₁ ∫_θ (D_zG)²σ`, `κ = (1-η)/(1+η)`;
* the logarithmic cut-off `zc φ k` makes the `z`-integration legitimate
  (`cut_integration`), and the `z`-integration by parts `radial_ibp_weight` rewrites the middle
  term, whose two pieces are bounded by `ibp_bounds`;
* Fatou/monotone convergence lets the cut-off tend to `1`.

The conclusion is the *honesty* of the `D_z∂_θ`-slot, i.e. the finiteness transfer. -/


/-- The `z`-slice of a function smooth on the open strip is smooth on `(0,∞)`. -/
theorem slice_z_contDiffOn {f : ℝ → ℝ → ℝ} {N : ℕ} {θ : ℝ}
    (h : ContDiffOn ℝ N (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    ContDiffOn ℝ N (fun z => f z θ) (Set.Ioi 0) :=
  Work.FTS.EllipticEst.DzAmgm.contDiffOn_slice_z_nat
    (s := Set.Ioi 0) (t := Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) h hθ

/-- **The slicewise inequality** of `slice_key` in the notation of the chapter. -/
theorem excess_slice (G : ℝ → ℝ → ℝ)
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), G z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), G z (Real.pi / 2) = 0) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ)
          + c₁ * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
  obtain ⟨c₁, hc₁, hkey⟩ := Work.FTS.EllipticEst.Alpha4.slice_key
  refine ⟨c₁, hc₁, fun z hz => ?_⟩
  -- the `z`-slice of `D_zG` is `C²` near the closed angular interval
  have hcd : ContDiffOn ℝ 2 (fun θ => Work.Spaces.Dz G z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    ((hG.DzIter 1).sliceSmoothO hz).of_le 2
  -- it vanishes at the two angular endpoints
  have hz0 : (fun θ => Work.Spaces.Dz G z θ) 0 = 0 := by
    show z * deriv (fun z' : ℝ => G z' 0) z = 0
    have hev : (fun z' : ℝ => G z' 0) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact h0 z' hz'
    rw [hev.deriv_eq]; simp
  have hzpi : (fun θ => Work.Spaces.Dz G z θ) (Real.pi / 2) = 0 := by
    show z * deriv (fun z' : ℝ => G z' (Real.pi / 2)) z = 0
    have hev : (fun z' : ℝ => G z' (Real.pi / 2)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact h1 z' hz'
    rw [hev.deriv_eq]; simp
  have h := hkey (fun θ => Work.Spaces.Dz G z θ) hcd hz0 hzpi
  -- identify the three integrals of `hkey` with the chapter's notation
  have e1 : (∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hcl := Work.FTS.EllipticEst.ThetaU.pth_Dz_eq (G := G) (hG.contDiffAt 2 hz hθ')
    show (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ') θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [show deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ') θ
        = Work.Spaces.pth (Work.Spaces.Dz G) z θ from rfl, hcl]
  have e2 : (∫ θ in Work.Spaces.Iθ,
        (fun θ' : ℝ => Work.Spaces.Dz G z θ') θ
          * deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ')) θ
          * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
          * Work.FTS.EllipticEst.thEta θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hcl := Work.FTS.EllipticEst.ThetaU.pth_pth_Dz_eq (G := G) (hG 3) hz hθ'
    show (Work.Spaces.Dz G z θ) * deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ')) θ
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
        * Work.FTS.EllipticEst.thEta θ
    rw [show deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz G z θ')) θ
        = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ from rfl, hcl]
  rw [e1, e2] at h
  exact h

/-- **The two `θ`-profiles of the radial integration by parts are integrable against `σ`.**

The two inner functions are exactly the test functions `Alpha4.ibpF1 φ k G`, `Alpha4.ibpF2 φ k G`
of `Alpha4.ibp_bounds`: the cut-off `deriv ζ` (resp. `ζ`) localises `z` to the compact box
`[1/k², k²]` (`ZCuts.zCut_props`, `Alpha4.deriv_zc_eq_zero_of_notMem`), on which the smooth
slices `D_zG`, `D_z²G`, `∂_θ²G` are bounded (`ThetaU.exists_bound_box`).  Hence
`(z,θ) ↦ w(z)² σ(θ) F(z,θ)` is integrable for the product measure
(`ThetaU.integrable_prod_quad_of_bound`), and Fubini for partial integrals
(`Integrable.integral_prod_right`) turns this into the integrability of the `θ`-profile against
`σ`. -/
theorem excess_ibp_integrable (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ} (hφK : Work.FTS.EllipticEst.IsZCut φ K) :
    MeasureTheory.IntegrableOn (fun θ => (∫ z in Work.Spaces.Iz,
        deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
          * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨hζcd0, hζone, -, -⟩ := Work.FTS.EllipticEst.ZCuts.zCut_props hφK k hk2
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hδ : 0 < 1 / (k : ℝ) ^ 2 := by positivity
  have hδR : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    nlinarith [hk4]
  have hζcd : ContDiffOn ℝ 1 (Work.FTS.EllipticEst.Alpha4.zc φ k) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Alpha4.zc_contDiffOn
      (Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφK.1 hk2)
  have hζsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      Work.FTS.EllipticEst.Alpha4.zc φ k z = 0 :=
    fun z hz => Work.FTS.EllipticEst.Alpha4.zc_eq_zero_of_notMem hk1
      (fun z' hz' hz'' => hζone z' hz' hz'') hz
  have hζ'supp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z = 0 :=
    fun z hz => Work.FTS.EllipticEst.Alpha4.deriv_zc_eq_zero_of_notMem hk2 hφK hz
  -- ## continuity of the four elementary building blocks
  have hder : ContinuousOn (fun p : ℝ × ℝ => deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hζcd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp continuousOn_fst
      (fun p hp => hp.1)
  have hderbox : ContinuousOn (fun p : ℝ × ℝ =>
      deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) p.1)
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
    (hζcd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp continuousOn_fst
      (fun p hp => lt_of_lt_of_le hδ hp.1.1)
  have hzcquad : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hζcd.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have hzcbox : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1)
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
    hζcd.continuousOn.comp continuousOn_fst (fun p hp => lt_of_lt_of_le hδ hp.1.1)
  have hbquad : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Alpha4.bcoef_continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have hbbox : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.Alpha4.bcoef_continuousOn.comp continuousOn_fst
      (fun p hp => lt_of_lt_of_le hδ hp.1.1)
  -- ## the two test functions (those of `Alpha4.ibp_bounds`)
  have hF1c : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.Alpha4.ibpF1 φ k G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hmain : ContinuousOn (fun p : ℝ × ℝ =>
        deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) p.1 * p.1
          * Work.Spaces.Dz G p.1 p.2 * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((hder.mul continuousOn_fst).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_mixed hG 1 0)).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_pthDz hG 0 2)
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, Work.FTS.EllipticEst.Alpha4.ibpF1]
  have hF10 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → ∀ θ,
      Work.FTS.EllipticEst.Alpha4.ibpF1 φ k G z θ = 0 := by
    intro z hz θ
    simp only [Work.FTS.EllipticEst.Alpha4.ibpF1]
    rw [hζ'supp z hz]; ring
  have hF1box : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.Alpha4.ibpF1 φ k G))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) := by
    have hmain : ContinuousOn (fun p : ℝ × ℝ =>
        deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) p.1 * p.1
          * Work.Spaces.Dz G p.1 p.2 * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      ((hderbox.mul continuousOn_fst).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_box_mixed hG 1 0 hδ)).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_box_pthDz hG 0 2 hδ)
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, Work.FTS.EllipticEst.Alpha4.ibpF1]
  obtain ⟨M1, -, hM1⟩ :=
    Work.FTS.EllipticEst.ThetaU.exists_bound_box (R := (k : ℝ) ^ 2) hδ hδR hF1box
  have hF2c : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.Alpha4.ibpF2 φ k G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1
        * (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (hzcquad.mul ((Work.FTS.EllipticEst.Alpha4.continuousOn_quad_mixed hG 2 0).add
        (hbquad.mul (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_mixed hG 1 0)))).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_pthDz hG 0 2)
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, Work.FTS.EllipticEst.Alpha4.ibpF2]
  have hF20 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → ∀ θ,
      Work.FTS.EllipticEst.Alpha4.ibpF2 φ k G z θ = 0 := by
    intro z hz θ
    simp only [Work.FTS.EllipticEst.Alpha4.ibpF2]
    rw [hζsupp z hz]; ring
  have hF2box : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.Alpha4.ibpF2 φ k G))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) := by
    have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1
        * (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      (hzcbox.mul ((Work.FTS.EllipticEst.Alpha4.continuousOn_box_mixed hG 2 0 hδ).add
        (hbbox.mul (Work.FTS.EllipticEst.Alpha4.continuousOn_box_mixed hG 1 0 hδ)))).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_box_pthDz hG 0 2 hδ)
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, Work.FTS.EllipticEst.Alpha4.ibpF2]
  obtain ⟨M2, -, hM2⟩ :=
    Work.FTS.EllipticEst.ThetaU.exists_bound_box (R := (k : ℝ) ^ 2) hδ hδR hF2box
  -- ## Fubini for the partial integrals
  constructor
  · have hint : MeasureTheory.Integrable (fun θ => ∫ z,
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllipticEst.Alpha4.ibpF1 φ k G z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.EllipticEst.ThetaU.integrable_prod_quad_of_bound (δ := 1 / (k : ℝ) ^ 2)
        (R := (k : ℝ) ^ 2) (M := M1) hδ (F := Work.FTS.EllipticEst.Alpha4.ibpF1 φ k G)
        hF1c hF10 hM1).integral_prod_right
    refine hint.congr ?_
    filter_upwards with θ
    rw [show (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllipticEst.Alpha4.ibpF1 φ k G z θ)
        = fun z => (deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
            * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ from by
      funext z; simp only [Work.FTS.EllipticEst.Alpha4.ibpF1]; ring,
      MeasureTheory.integral_mul_const]
  · have hint : MeasureTheory.Integrable (fun θ => ∫ z,
        (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllipticEst.Alpha4.ibpF2 φ k G z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Work.FTS.EllipticEst.ThetaU.integrable_prod_quad_of_bound (δ := 1 / (k : ℝ) ^ 2)
        (R := (k : ℝ) ^ 2) (M := M2) hδ (F := Work.FTS.EllipticEst.Alpha4.ibpF2 φ k G)
        hF2c hF20 hM2).integral_prod_right
    refine hint.congr ?_
    filter_upwards with θ
    rw [show (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllipticEst.Alpha4.ibpF2 φ k G z θ)
        = fun z => (Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ from by
      funext z; simp only [Work.FTS.EllipticEst.Alpha4.ibpF2]; ring,
      MeasureTheory.integral_mul_const]

/-- **The `z`-integration by parts** in the doubly integrated form: with `ζ = zc φ k`
supported in `[a,b] ⊂ (0,∞)`,

  `∫_z ζw²∫_θ (D_zG)(∂_θ²G)σ = -∫_θ(∫_z ∂_zζ·w²z·(D_zG)(∂_θ²G))σ
      - ∫_θ(∫_z ζw²(D_z²G + bD_zG)(∂_θ²G))σ`.

The two terms on the right are integrable in `θ` against `σ` (hypotheses `hEint`, `hFint`); this
is what makes the linearity of the integral at the last step available. -/
theorem excess_ibp (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {k : ℕ} {φ : ℝ → ℝ} {a b Mb : ℝ} (ha : 0 < a) (hab : a < b)
    (hζcd : ContDiffOn ℝ 1 (Work.FTS.EllipticEst.Alpha4.zc φ k) (Set.Ioi 0))
    (hζ0 : ∀ z, (0 < z ∧ z < a) ∨ b < z → Work.FTS.EllipticEst.Alpha4.zc φ k z = 0)
    (hFc : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc a b → ∀ θ, Work.FTS.EllipticEst.Alpha4.zc φ k z
      * (Work.Spaces.Dz G z θ)
      * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ) = 0)
    (hFb : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)| ≤ Mb)
    (hEint : MeasureTheory.IntegrableOn (fun θ => (∫ z in Work.Spaces.Iz,
        deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
          * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn (fun θ => (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
        * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = - (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
            deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
              * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ)
        - (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ) := by
  -- ## Fubini: `∫_z w²·(∫_θ F·σ) = ∫_θ (∫_z w²·F)·σ`
  have hFub : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Alpha4.zc φ k z
            * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
          * Work.FTS.EllipticEst.thEta θ :=
    Work.FTS.EllipticEst.ThetaU.fubini_w_thEta (δ := a) (R := b) ha
      (F := fun z θ => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
      hFc hF0 ⟨Mb, hFb⟩
  -- ## move `ζ` inside the angular integral, so that `hFub` applies
  have hmove : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
        * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Alpha4.zc φ k z
              * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Alpha4.zc φ k z
            * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ)
    rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Alpha4.zc φ k z
          * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
          * Work.FTS.EllipticEst.thEta θ)
        = Work.FTS.EllipticEst.Alpha4.zc φ k z
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ) from by
      rw [show (fun θ => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ)
          = fun θ => Work.FTS.EllipticEst.Alpha4.zc φ k z
              * ((Work.Spaces.Dz G z θ)
                * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
                * Work.FTS.EllipticEst.thEta θ) from by
        funext θ; ring,
        MeasureTheory.integral_const_mul]]
    ring
  -- ## the pointwise (in `θ`) `z`-integration by parts
  have hper : ∀ θ ∈ Work.Spaces.Iθ,
      (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
        = - (∫ z in Work.Spaces.Iz, deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z
              * (Work.Spaces.w z) ^ 2 * z * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
              * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ)) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hzcd : ContDiffOn ℝ 1 (fun z => Work.Spaces.Dz G z θ) (Set.Ioi 0) :=
      slice_z_contDiffOn (f := Work.Spaces.DzIter 1 G) (N := 1) ((hG.DzIter 1) 1) hθ'
    have hzpsi : ContDiffOn ℝ 1 (fun z => Work.Spaces.pth (Work.Spaces.pth G) z θ)
        (Set.Ioi 0) :=
      slice_z_contDiffOn (f := Work.Spaces.pthIter 2 G) (N := 1) ((hG.pthIter 2) 1) hθ'
    have h := Work.FTS.EllipticEst.Alpha4.radial_ibp_weight (a := a) (b := b) ha hab
      (φ := fun z => Work.Spaces.Dz G z θ)
      (ψ := fun z => Work.Spaces.pth (Work.Spaces.pth G) z θ)
      (ζ := Work.FTS.EllipticEst.Alpha4.zc φ k) hzcd hzpsi hζcd hζ0
    simpa only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.Iz,
      MeasureTheory.integral_Ici_eq_integral_Ioi] using h
  -- ## combine
  rw [hmove, hFub]
  rw [show (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
        * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (- ((∫ z in Work.Spaces.Iz,
            deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
              * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ)
        + - ((∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
              * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ)) from by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    have hp := hper θ hθ
    rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
            * (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by ring)]
    rw [hp]; ring]
  have hEn : MeasureTheory.Integrable (fun θ => - ((∫ z in Work.Spaces.Iz,
        deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
          * (Work.Spaces.Dz G z θ) * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hEint.neg
  have hFn : MeasureTheory.Integrable (fun θ => - ((∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hFint.neg
  rw [MeasureTheory.integral_add hEn hFn, MeasureTheory.integral_neg,
    MeasureTheory.integral_neg]
  ring

/-- **The uniform-in-`k` bound for the cut-off quantity.**  The slicewise Hardy inequality
`excess_slice` is integrated against the cut-off weight `ζ_k w²` (`Alpha4.cut_integration`); the
`z`-integration by parts `excess_ibp` rewrites the middle term as the sum of the two pieces `E`
and `F` of `Alpha4.ibp_bounds`, which bounds them by the uncut quantities `dInt`, `ttInt`, `ddInt`.
The two `θ`-profiles are integrable by `excess_ibp_integrable`. -/
theorem excess_zeta_bound (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), G z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), G z (Real.pi / 2) = 0)
    {φ : ℝ → ℝ} {K : ℝ} (hφK : Work.FTS.EllipticEst.IsZCut φ K)
    (hd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (ht : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (hdd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ k : ℕ, 2 ≤ k →
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
              * (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ))
        ≤ K / Real.log k * (1 / 2 * (Work.FTS.EllipticEst.dInt G
              + Work.FTS.EllipticEst.ttInt G))
          + (Work.FTS.EllipticEst.ddInt G + 9 * Work.FTS.EllipticEst.dInt G
              + 1 / 2 * Work.FTS.EllipticEst.ttInt G)
          + c₁ * Work.FTS.EllipticEst.dInt G := by
  obtain ⟨c₁, hc₁, hslice⟩ := excess_slice G hG h0 h1
  refine ⟨c₁, hc₁, fun k hk2 => ?_⟩
  obtain ⟨hζcd0, hζone, -, -⟩ := Work.FTS.EllipticEst.ZCuts.zCut_props hφK k hk2
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hδ : 0 < 1 / (k : ℝ) ^ 2 := by positivity
  have hδR : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    nlinarith [hk4]
  have hζcd : ContDiffOn ℝ 1 (Work.FTS.EllipticEst.Alpha4.zc φ k) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Alpha4.zc_contDiffOn
      (Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφK.1 hk2)
  have hζsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      Work.FTS.EllipticEst.Alpha4.zc φ k z = 0 :=
    fun z hz => Work.FTS.EllipticEst.Alpha4.zc_eq_zero_of_notMem hk1
      (fun z' hz' hz'' => hζone z' hz' hz'') hz
  have hζ0 : ∀ z, (0 < z ∧ z < 1 / (k : ℝ) ^ 2) ∨ (k : ℝ) ^ 2 < z →
      Work.FTS.EllipticEst.Alpha4.zc φ k z = 0 := by
    intro z hz
    refine Work.FTS.EllipticEst.Alpha4.zc_eq_zero_of_notMem hk1
      (fun z' hz' hz'' => hζone z' hz' hz'') ?_
    rcases hz with hz | hz
    · exact fun hmem => absurd hmem.1 (not_le.mpr hz.2)
    · exact fun hmem => absurd hmem.2 (not_le.mpr hz)
  -- ## the test function `ζ·D_zG·D_z∂_θ²G` of the `z`-integration by parts
  have hFc : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hzcc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hζcd.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
    have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1
        * Work.Spaces.Dz G p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (hzcc.mul (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_mixed hG 1 0)).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_pthDz hG 1 2)
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry]
  have hF0 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → ∀ θ,
      Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ) = 0 := by
    intro z hz θ
    rw [hζsupp z hz]
    ring
  have hFbox : ContinuousOn (Function.uncurry (fun z θ =>
      Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.Dz G z θ)
        * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) := by
    have hzcc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      hζcd.continuousOn.comp continuousOn_fst (fun p hp => lt_of_lt_of_le hδ hp.1.1)
    have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.Alpha4.zc φ k p.1
        * Work.Spaces.Dz G p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      (hzcc.mul (Work.FTS.EllipticEst.Alpha4.continuousOn_box_mixed hG 1 0 hδ)).mul
        (Work.FTS.EllipticEst.Alpha4.continuousOn_box_pthDz hG 1 2 hδ)
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry]
  obtain ⟨Mb, -, hMb⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box
    (δ := 1 / (k : ℝ) ^ 2) (R := (k : ℝ) ^ 2) hδ hδR hFbox
  -- ## the three ingredients
  obtain ⟨hEint, hFint⟩ := excess_ibp_integrable G hG hk2 hφK
  have hibp := excess_ibp G hG hδ hδR hζcd hζ0 hFc hF0 hMb hEint hFint
  obtain ⟨hb1, hb2, hb3⟩ := Work.FTS.EllipticEst.Alpha4.ibp_bounds hk2 hφK hG hd ht hdd
  have hcut := Work.FTS.EllipticEst.Alpha4.cut_integration (G := G) hk2 hφK (hG) hslice
  -- ## the arithmetic
  have hneg : - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
        * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ))
      = (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
            deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
              * (Work.Spaces.Dz G z θ)
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
              * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
              * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ) := by
    rw [hibp]; ring
  rw [hneg] at hcut
  have hE := le_abs_self (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
        deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z * (Work.Spaces.w z) ^ 2 * z
          * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      * Work.FTS.EllipticEst.thEta θ)
  have hcZ : c₁ * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.Alpha4.zc φ k z
        * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
      ≤ c₁ * Work.FTS.EllipticEst.dInt G := mul_le_mul_of_nonneg_left hb3 hc₁.le
  linarith [hcut, hE, hb1, hb2, hcZ]

/-- **The finiteness transfer.**  The uniform-in-`k` bound of `excess_zeta_bound`, together with
the support of the cut-off on `[1/(j+2), j+2]` and monotone convergence, gives the finiteness of
the uncut mixed weighted integral `∫_z w(z)² ∫_θ (D_z∂_θG)² σ`. -/
theorem excess_transfer (G : ℝ → ℝ → ℝ) (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), G z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), G z (Real.pi / 2) = 0)
    (hd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (ht : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (hdd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iz := by
  obtain ⟨φ, K, hφK⟩ := Work.FTS.EllipticEst.ZCuts.zCut_exists
  have hK0 : 0 ≤ K := hφK.2.2.2.2.1
  obtain ⟨c₁, hc₁, hbound⟩ := excess_zeta_bound G hG h0 h1 hφK hd ht hdd
  -- ## the quantities
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hA
  set C₀ : ℝ := K / Real.log 2 * (1 / 2 * (Work.FTS.EllipticEst.dInt G
        + Work.FTS.EllipticEst.ttInt G))
      + (Work.FTS.EllipticEst.ddInt G + 9 * Work.FTS.EllipticEst.dInt G
        + 1 / 2 * Work.FTS.EllipticEst.ttInt G)
      + c₁ * Work.FTS.EllipticEst.dInt G with hC₀
  -- ## nonnegativity of the three uncut integrals
  have hA_nn : ∀ z : ℝ, 0 ≤ A z := by
    intro z
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hd_nn : 0 ≤ Work.FTS.EllipticEst.dInt G := by
    rw [Work.FTS.EllipticEst.dInt]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have htt_nn : 0 ≤ Work.FTS.EllipticEst.ttInt G := by
    rw [Work.FTS.EllipticEst.ttInt]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hX : 0 ≤ 1 / 2 * (Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G) := by
    linarith
  -- ## the bound is nondecreasing in `k`
  have hmono : ∀ k : ℕ, 2 ≤ k →
      K / Real.log k * (1 / 2 * (Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G))
        + (Work.FTS.EllipticEst.ddInt G + 9 * Work.FTS.EllipticEst.dInt G
          + 1 / 2 * Work.FTS.EllipticEst.ttInt G) + c₁ * Work.FTS.EllipticEst.dInt G ≤ C₀ := by
    intro k hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlelog : Real.log 2 ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) hkR
    have hfrac : K / Real.log (k : ℝ) ≤ K / Real.log 2 := by
      rw [div_le_div_iff₀ hlogk hlog2]
      nlinarith [hK0, hlelog]
    have hmul := mul_le_mul_of_nonneg_right hfrac hX
    rw [hC₀]
    linarith [hmul]
  -- ## the cut-off sets `[1/(j+2), j+2]`
  have hdir : Directed (· ⊆ ·) (fun j : ℕ => Set.Icc (1 / (((j + 2 : ℕ) : ℝ)))
      (((j + 2 : ℕ) : ℝ))) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩ <;> intro z hz <;> refine ⟨?_, ?_⟩
    · refine le_trans ?_ hz.1
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact_mod_cast (by omega : i + 2 ≤ max i j + 2)
    · exact le_trans hz.2 (by exact_mod_cast (by omega : i + 2 ≤ max i j + 2))
    · refine le_trans ?_ hz.1
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact_mod_cast (by omega : j + 2 ≤ max i j + 2)
    · exact le_trans hz.2 (by exact_mod_cast (by omega : j + 2 ≤ max i j + 2))
  have hunion : (⋃ j : ℕ, Set.Icc (1 / (((j + 2 : ℕ) : ℝ))) (((j + 2 : ℕ) : ℝ)))
      = Set.Ioi (0 : ℝ) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      have hpos : (0 : ℝ) < 1 / (((j + 2 : ℕ) : ℝ)) := by positivity
      exact lt_of_lt_of_le hpos hj.1
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt (max z (1 / z))
      have hnz : z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
      have hnz' : 1 / z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans hz hnz
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine ⟨?_, ?_⟩
      · have h2 : 1 / (((n + 2 : ℕ) : ℝ)) ≤ 1 / (n : ℝ) := by
          refine one_div_le_one_div_of_le hnpos ?_
          exact_mod_cast (by omega : n ≤ n + 2)
        have h3 : 1 / (n : ℝ) ≤ z := (one_div_le hnpos hz).mpr hnz'.le
        linarith
      · exact le_trans hnz.le (by exact_mod_cast (by omega : n ≤ n + 2))
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (⋃ j : ℕ, Set.Icc (1 / (((j + 2 : ℕ) : ℝ)))
          (((j + 2 : ℕ) : ℝ))) := by
    rw [hunion]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  -- ## the Lebesgue-integral bound for the uncut integrand
  set F : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * A z) with hF
  have hcut_int : ∀ k : ℕ, 2 ≤ k → MeasureTheory.Integrable
      (fun z => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2 * A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    fun k hk => (Work.FTS.EllipticEst.Alpha4.cut_slices_integrable hk hφK hG).1
  have hmain : (∫⁻ z in Work.Spaces.Iz, F z) ≤ ENNReal.ofReal (C₀ / ((1 - Work.Spaces.eta)
      / (1 + Work.Spaces.eta))) := by
    have hL : (∫⁻ z in Work.Spaces.Iz, F z)
        = ∫⁻ z in (⋃ j : ℕ, Set.Icc (1 / (((j + 2 : ℕ) : ℝ))) (((j + 2 : ℕ) : ℝ))), F z :=
      congrArg (fun m : MeasureTheory.Measure ℝ => ∫⁻ z, F z ∂m) hmeas
    rw [hL, setLIntegral_iUnion_of_directed F hdir]
    refine iSup_le (fun j => ?_)
    have hsub : Set.Icc (1 / (((j + 2 : ℕ) : ℝ))) (((j + 2 : ℕ) : ℝ)) ⊆ Work.Spaces.Iz := by
      intro z hz
      have hpos : 0 < 1 / (((j + 2 : ℕ) : ℝ)) := by positivity
      exact le_trans hpos.le hz.1
    have hζmem : ∀ z, 0 < z → 1 / (((j + 2 : ℕ) : ℝ)) ≤ z → z ≤ (((j + 2 : ℕ) : ℝ)) →
        Work.FTS.EllipticEst.psiFun φ (j + 2) z = 1 :=
      (Work.FTS.EllipticEst.ZCuts.zCut_props hφK (j + 2) (by omega)).2.2.1
    have hcong : (∫⁻ z in Set.Icc (1 / (((j + 2 : ℕ) : ℝ))) (((j + 2 : ℕ) : ℝ)), F z)
        = ∫⁻ z in Set.Icc (1 / (((j + 2 : ℕ) : ℝ))) (((j + 2 : ℕ) : ℝ)),
            ENNReal.ofReal (Work.FTS.EllipticEst.Alpha4.zc φ (j + 2) z
              * (Work.Spaces.w z) ^ 2 * A z) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
      have hzpos : 0 < z := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (((j + 2 : ℕ) : ℝ)))
        hz.1
      rw [show Work.FTS.EllipticEst.Alpha4.zc φ (j + 2) z = 1 from
        Work.FTS.EllipticEst.Alpha4.zc_eq_one_of_mem (by omega) hζmem hz.1 hz.2, one_mul]
    rw [hcong]
    refine le_trans (MeasureTheory.lintegral_mono_set hsub) ?_
    have hint : MeasureTheory.Integrable (fun z => Work.FTS.EllipticEst.Alpha4.zc φ (j + 2) z
        * (Work.Spaces.w z) ^ 2 * A z) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hcut_int (j + 2) (by omega)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        fun z => Work.FTS.EllipticEst.Alpha4.zc φ (j + 2) z * (Work.Spaces.w z) ^ 2 * A z :=
      Filter.Eventually.of_forall (fun z => mul_nonneg
        (mul_nonneg (Work.FTS.EllipticEst.Alpha4.zc_nonneg
          (fun t => (hφK.2.2.2.1 (Real.log t / Real.log ((j + 2 : ℕ) : ℝ))).1) z)
          (sq_nonneg _)) (hA_nn z))
    rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := hbound (j + 2) (by omega)
    have hm := hmono (j + 2) (by omega)
    rw [le_div_iff₀ (by norm_num [Work.Spaces.eta])]
    linarith [le_trans hb hm]
  -- ## a.e. strong measurability and the finiteness of the integral
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * ((Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thEta p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rw [show (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
          = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 from by
        funext p; simp only [Work.Spaces.w]]
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.div ((continuous_const.add continuous_fst).continuousOn.pow 2)
        (continuous_fst.pow 2).continuousOn ?_
      intro p hp
      exact pow_ne_zero 2 (ne_of_gt hp.1)
    exact hw.mul (((Work.FTS.EllipticEst.Alpha4.continuousOn_quad_pthDz hG 1 1).pow 2).mul
      Work.FTS.EllipticEst.Alpha4.continuousOn_quad_thEta)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * A z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'.congr
      (Filter.Eventually.of_forall fun z => ?_)
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) = (Work.Spaces.w z) ^ 2 * A z
    rw [MeasureTheory.integral_const_mul]
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      fun z => (Work.Spaces.w z) ^ 2 * A z :=
    Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (hA_nn z))
  refine ⟨haesm, (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mpr
    (lt_of_le_of_lt hmain ENNReal.ofReal_lt_top)⟩

/-! ## The pointwise identities of the assembly -/

/-- The `ℋ⁰`-integrand is the `σ`-weighted square: for `θ ∈ Iθ`, `(g·w/σ^{η/2})² = g²·w²·σ`. -/
theorem sq_div_thEta_eq (z θ g : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (g * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = g ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  rw [mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθ z]
  ring

/-- **The angular integral of the `ℋ⁰`-integrand** in the form used by the transfer:
`∫_θ (g θ · w/σ^{η/2})² = ∫_θ (g θ)² w² σ`. -/
theorem integral_hk_ibp (z : ℝ) (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (g θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (g θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => sq_div_thEta_eq z θ (g θ) hθ)

/-- **The same integral with `w²` pulled out of the `θ`-integral.** -/
theorem integral_hk_pull (z : ℝ) (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (g θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  rw [integral_hk_ibp z g,
    show (∫ θ in Work.Spaces.Iθ,
        (g θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          ((g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring),
    MeasureTheory.integral_mul_const]
  ring

/-- **The `D_z`-`∂_θ` commutation at the shifted level**:
`D_z∂_θ(D_z^kΨ) = D_z^{k+1}∂_θΨ` on the half-quadrant, for `Ψ` smooth on a neighbourhood of
the closed quadrant. -/
theorem Dz_pth_DzIter_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.Spaces.SmoothNbhd Ψ) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ
        = Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ := by
  intro z hz θ hθ
  have h1 : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ
      = Work.Spaces.Dz (Work.Spaces.DzIter k (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.Dz_congr (Work.Elliptic.pth_DzIter_eqOn Ψ hΨ k)
      (Work.Spaces.mem_nbhU hz hθ)
  rw [h1, Work.Spaces.DzIter_succ]

/-- **The second `∂_θ`-derivative commutes with `D_z^k`**: `∂_θ²(D_z^kΨ) = D_z^k∂_θ²Ψ` on the
half-quadrant, for `Ψ` smooth on a neighbourhood of the closed quadrant. -/
theorem pth_pth_DzIter_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.Spaces.SmoothNbhd Ψ) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ
        = Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ) z θ := by
  intro z hz θ hθ
  have h1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter k (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.Spaces.isOpen_nbhU
      (Work.Elliptic.pth_DzIter_eqOn Ψ hΨ k) (Work.Spaces.mem_nbhU hz hθ)
  have h2 : Work.Spaces.pth (Work.Spaces.DzIter k (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.DzIter k (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ :=
    Work.Elliptic.pth_DzIter (Work.Spaces.pth Ψ) hΨ.pth k z θ hz hθ
  rw [h1, h2]
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]

theorem excess_finite (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hk : 2 ≤ k) (hE : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      (Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iz := by
  -- ## the smoothness class
  have hsm : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ Ψ := fun n =>
    (hE.smoothNbhd.mono
      (fun p hp => ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) hp.1, hp.2⟩)).of_le le_top
  -- ## vanishing on the two angular boundary lines
  have hvanish : Work.Spaces.VanishTheta Ψ := ⟨fun z => hE.sol.2.1 z, fun z => hE.sol.2.2.1 z⟩
  have hb0 : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.DzIter k Ψ z 0 = 0 :=
    fun z hz => (Work.FTS.EllipticEst.DzIter_boundary_zero hvanish k).1 z
      (lt_trans (by norm_num : (-1 : ℝ) < 0) hz)
  have hb1 : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.DzIter k Ψ z (Real.pi / 2) = 0 :=
    fun z hz => (Work.FTS.EllipticEst.DzIter_boundary_zero hvanish k).2 z
      (lt_trans (by norm_num : (-1 : ℝ) < 0) hz)
  -- ## the three integrability hypotheses of `excess_transfer`
  obtain ⟨hmem1, hmem2⟩ := EllHyp_dzIter_succ_mem α k F Ψ hα hα4 hk hE
  have hmemt : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ)) :=
    excess_zsummand_mem α k k (Work.Spaces.pthIter 2 Ψ)
      (Work.FTS.EllipticEst.Alpha4.continuousOn_quad_pthDz hsm k 2) hE.memDth2 le_rfl
  have hd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.DzIter k Ψ) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz := by
    refine hmem1.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    show (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (k + 1) Ψ) z θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.DzIter k Ψ) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    have hEq : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (k + 1) Ψ) z θ)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.DzIter (k + 1) Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => HkIntegrand_zero_eq α (Work.Spaces.DzIter (k + 1) Ψ) z θ)
    rw [hEq]
    exact integral_hk_ibp z (fun θ => Work.Spaces.Dz (Work.Spaces.DzIter k Ψ) z θ)
  have hdd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter k Ψ)) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz := by
    refine hmem2.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    show (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (k + 2) Ψ) z θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter k Ψ)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    have hEq : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (k + 2) Ψ) z θ)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.DzIter (k + 2) Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => HkIntegrand_zero_eq α (Work.Spaces.DzIter (k + 2) Ψ) z θ)
    rw [hEq]
    exact integral_hk_ibp z
      (fun θ => Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter k Ψ)) z θ)
  have ht : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz := by
    refine hmemt.2.congr_fun (fun z hz => ?_) measurableSet_Ici
    show (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ)) z θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    have hEq : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ)) z θ)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => HkIntegrand_zero_eq α
          (Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ)) z θ)
    rw [hEq]
    rw [integral_hk_ibp z (fun θ => Work.Spaces.DzIter k (Work.Spaces.pthIter 2 Ψ) z θ)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [pth_pth_DzIter_eq hE.smoothNbhd k z hz θ hθ]
  -- ## the transfer
  have htr := excess_transfer (Work.Spaces.DzIter k Ψ) (hsm.DzIter k) hb0 hb1 hd ht hdd
  refine ⟨?_, ?_⟩
  · -- ## the angular slices are integrable for every `z ∈ Iz`
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hpos
    · subst h0
      have hfun : (fun θ => (Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) 0 θ
          * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext θ
        rw [show Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) 0 θ = 0 from by
          rw [Work.Spaces.DzIter_succ]
          simp only [Work.Spaces.Dz]
          ring]
        ring
      rw [hfun]
      exact MeasureTheory.integrableOn_zero
    · have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ)
          Work.Spaces.Iθ :=
        (Work.FTS.EllipticEst.Alpha4.continuousOn_box_pthDz (a := z) (b := z) hsm (k + 1) 1
          hpos).comp ((continuous_const.prodMk continuous_id).continuousOn)
          (fun θ hθ => ⟨⟨le_rfl, le_rfl⟩, hθ⟩)
      have hbase := Work.FTS.EllipticEst.Alpha4.integrable_slice_sq_mul_thEta
        (f := fun θ => Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ) hcont
      have h1 : MeasureTheory.Integrable (fun θ =>
            ((Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hbase.mul_const _
      refine h1.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [sq_div_thEta_eq z θ (Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ) hθ]
      ring
  · -- ## the `z`-integral of the angular slices is finite
    refine htr.congr_fun (fun z hz => ?_) measurableSet_Ici
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter k Ψ)) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    rw [integral_hk_pull z (fun θ => Work.Spaces.DzIter (k + 1) (Work.Spaces.pth Ψ) z θ)]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Dz_pth_DzIter_eq hE.smoothNbhd k z hz θ hθ]
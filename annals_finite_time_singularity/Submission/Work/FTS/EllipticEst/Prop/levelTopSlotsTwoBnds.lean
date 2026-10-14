import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.angularAgmon
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoPlumb
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The pointwise Clairaut identity -/

theorem smoothOpen_pthIter_aux {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) :
    ∀ i : ℕ, SmoothOpen (Work.Spaces.pthIter i F) := by
  intro i
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

theorem smoothOpen_zsq_mul {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => z ^ 2 * g z θ) := by
  refine smoothOpen_of_forall fun n => ?_
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ 2) Q0 :=
    ((contDiffOn_id : ContDiffOn ℝ n (fun p : ℝ × ℝ => p) Q0).fst).pow 2
  have h2 : ContDiffOn ℝ n (Function.uncurry g) Q0 := hg.forall n
  have hmul := h1.mul h2
  refine hmul.congr (fun p hp => ?_)
  rfl

/-- Clairaut: `∂_z` commutes with `∂_θ²` on the open quadrant. -/
private theorem pz_pthIter_two_comm_aux {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) :
    AgreeOnQ (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (isOpen_Q0.mem_nhds (mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp (SmoothOpen.pth hΨ) 2).contDiffAt
      (isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen isOpen_Q0
      (fun p hp => by obtain ⟨z', θ'⟩ := p; exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- Clairaut, twice: `∂_z²` commutes with `∂_θ²` on the open quadrant. -/
private theorem pzIter_two_pthIter_two_comm_aux {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) :
    AgreeOnQ (Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ)) := by
  have h1 := pz_pthIter_two_comm_aux hΨ
  have h2 := h1.pz
  have h3 := pz_pthIter_two_comm_aux hΨ.pz
  intro z θ hz hθ hlt
  exact (h2 z θ hz hθ hlt).trans (h3 z θ hz hθ hlt)

/-- `∂_θ^n` of a product with a `θ`-independent factor. -/
private theorem pthIter_const_mul_aux (n : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      show deriv (fun θ' => c z * Work.Spaces.pthIter k g z θ') θ
        = c z * deriv (fun θ' => Work.Spaces.pthIter k g z θ') θ
      exact deriv_const_mul_field (c z)

/-- `∂_θ²(z²·G) = z²·∂_θ²G` followed by Clairaut. -/
private theorem pthIter_two_zsq_aux {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rw [pthIter_const_mul_aux 2 (fun z => z ^ 2) (Work.Spaces.pzIter 2 Ψ)]
  beta_reduce
  rw [← pzIter_two_pthIter_two_comm_aux hΨ z θ hz hθ.1 hθ.2]

/-- **The Clairaut identity of the `A`-slot**:
`∂_θ²(z²∂_z²Ψ) = D_z²(∂_θ²Ψ) − D_z(∂_θ²Ψ)` on the open quadrant. -/
theorem pthIter_two_Ab_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) :
    AgreeOnQ (Work.Spaces.pthIter 2 (Ab Ψ))
      (fun z θ => Work.Spaces.DzIter 2 (Bb Ψ) z θ - Work.Spaces.DzIter 1 (Bb Ψ) z θ) := by
  intro z θ hz hθ hlt
  have h1 := pthIter_two_zsq_aux hΨ hz ⟨hθ, hlt⟩
  have h2 := Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz
    (g := Work.Spaces.pthIter 2 Ψ) (smoothOpen_pthIter_aux hΨ 2) hz ⟨hθ, hlt⟩
  show Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
  rw [h1]
  exact h2

/-- The `sEta`-weighted square of a function is integrable on the angular slice as soon as the
function is in `ℋ⁰` and `w z ≠ 0`. -/
private theorem integrableOn_sq_sEta_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ}
    (h : Work.Spaces.HkMem α 0 f) (hz : z ∈ Work.Spaces.Iz) (hw : Work.Spaces.w z ≠ 0) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have h1 : (fun θ => (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        fun θ => ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 0 f z θ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [HkIntegrand_zero_eq_mul α f hθ]
    simp only [Work.FTS.EllipticEst.sEta]
    field_simp
  exact ((h.1 z hz).const_mul ((Work.Spaces.w z) ^ 2)⁻¹).congr h1.symm



/-! ## Reusable bounds on the level-`0` slots of the shifted data -/

/-- The `D_z`-slots of `∂_θ²Ψ` are in `ℋ⁰`. -/
theorem HkMem_zero_DzIter_Bb {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) (j : ℕ) (hj : j ≤ 2) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter j (Bb Ψ)) := by
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  have hB : SmoothOpen (Bb Ψ) := smoothOpen_pthIter_aux hΨ 2
  exact HkMem_zero_of_pointwise (c := 1) zero_le_one (hB.DzIter j) h.memB
    (fun z θ hz hθ hlt => by
      rw [HkIntegrand_zero_apply]
      simpa using Work.Spaces.sq_le_HkIntegrand_z α 2 (Bb Ψ) z θ j hj)

/-- The level-`0` slot of `∂_θ²(z²∂_z²Ψ)` is in `ℋ⁰`. -/
theorem HkMem_zero_pthIter2_Ab {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Ab Ψ)) := by
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  have hA : SmoothOpen (Ab Ψ) := smoothOpen_zsq_mul (hΨ.pzIter 2)
  refine HkMem_zero_of_pointwise (c := 4) (by norm_num) ((hA.pth).pth) h.memB
    (fun z θ hz hθ hlt => ?_)
  have hid := pthIter_two_Ab_eq hΨ z θ hz hθ hlt
  have h1 := Work.Spaces.sq_le_HkIntegrand_z α 2 (Bb Ψ) z θ 2 (by norm_num)
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 2 (Bb Ψ) z θ 1 (by norm_num)
  rw [HkIntegrand_zero_apply, hid]
  rw [show (Work.Spaces.DzIter 2 (Bb Ψ) z θ - Work.Spaces.DzIter 1 (Bb Ψ) z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = Work.Spaces.DzIter 2 (Bb Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        - Work.Spaces.DzIter 1 (Bb Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) from by ring]
  nlinarith [h1, h2, sq_nonneg (Work.Spaces.DzIter 2 (Bb Ψ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
    + Work.Spaces.DzIter 1 (Bb Ψ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

/-- The `ℋ⁰`-slot of `∂_θ²(z²∂_z²Ψ)` against the two radial `B`-slots. -/
theorem HkSq_zero_pthIter2_Ab_le {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
      ≤ 2 * (Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Bb Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Bb Ψ))) := by
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  refine HkSq_zero_le_of_ae_slice_le_sum (C := 2) (by norm_num)
    (HkMem_zero_DzIter_Bb h 2 (by norm_num)).2
    (HkMem_zero_DzIter_Bb h 1 (by norm_num)).2 ?_
  filter_upwards [ae_restrict_Iz_pos] with z hz
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Ab Ψ)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Bb Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 (Bb Ψ)) z θ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0θ | h0θ
    · rw [← h0θ, HkIntegrand_zero_eq_zero_of_sin_eq_zero α _ sin_two_zero_at_zero_aux]
      nlinarith [Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 2 (Bb Ψ)) z 0,
        Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 1 (Bb Ψ)) z 0]
    · rcases eq_or_lt_of_le hθ.2 with h1θ | h1θ
      · rw [h1θ, HkIntegrand_zero_eq_zero_of_sin_eq_zero α _ sin_two_zero_at_pi_half_aux]
        nlinarith [Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 2 (Bb Ψ))
            z (Real.pi / 2),
          Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.DzIter 1 (Bb Ψ))
            z (Real.pi / 2)]
      · have hid := pthIter_two_Ab_eq hΨ z θ hz h0θ h1θ
        rw [HkIntegrand_zero_apply α (Work.Spaces.pthIter 2 (Ab Ψ)) z θ, hid,
          HkIntegrand_zero_apply α (Work.Spaces.DzIter 2 (Bb Ψ)) z θ,
          HkIntegrand_zero_apply α (Work.Spaces.DzIter 1 (Bb Ψ)) z θ]
        rw [show (Work.Spaces.DzIter 2 (Bb Ψ) z θ - Work.Spaces.DzIter 1 (Bb Ψ) z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            = Work.Spaces.DzIter 2 (Bb Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
              - Work.Spaces.DzIter 1 (Bb Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            from by ring]
        nlinarith [sq_nonneg (Work.Spaces.DzIter 2 (Bb Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          + Work.Spaces.DzIter 1 (Bb Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
  have hdom : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Bb Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 (Bb Ψ)) z θ)
      Work.Spaces.Iθ :=
    (((HkMem_zero_DzIter_Bb h 2 (by norm_num)).1 z hzI).const_mul 2).add
      (((HkMem_zero_DzIter_Bb h 1 (by norm_num)).1 z hzI).const_mul 2)
  have hthis := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 2 (Ab Ψ)) z θ) hdom
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
  rw [MeasureTheory.integral_add
      (((HkMem_zero_DzIter_Bb h 2 (by norm_num)).1 z hzI).const_mul 2)
      (((HkMem_zero_DzIter_Bb h 1 (by norm_num)).1 z hzI).const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hthis
  linarith [hthis]

/-- The `j`-th radial `B`-slot (`j ≤ 2`) is bounded by `CZ·|F|²_{ℋ²}`. -/
theorem HkSq_zero_DzIter_Bb_le (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ → ∀ j : ℕ, j ≤ 2 →
      Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j (Bb Ψ)) ≤ CZ * Work.Spaces.HkSq α 2 F := by
  obtain ⟨CZ, hCZpos, hZ⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2 h0
  refine ⟨CZ, hCZpos, fun α F Ψ hα hα4 h j hj => ?_⟩
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  have hcomm : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j (Bb Ψ))
      = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) := by
    refine Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ hlt => ?_)
    exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩)).symm
  have hb := hZ α F Ψ hα hα4 h j hj
  have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
  rw [hcomm]
  linarith [hb, hnn]

/-- The `j`-th radial `A`-slot (`j ≤ 2`) is bounded by `CZ·|F|²_{ℋ²}`, with the `α⁴` weight. -/
theorem HkSq_zero_Ab_DzIter_le (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ → ∀ j : ℕ, j ≤ 2 →
      α ^ 4 * Work.Spaces.HkSq α 0 (Ab (Work.Spaces.DzIter j Ψ))
        ≤ CZ * Work.Spaces.HkSq α 2 F := by
  obtain ⟨CZ, hCZpos, hZ⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2 h0
  refine ⟨CZ, hCZpos, fun α F Ψ hα hα4 h j hj => ?_⟩
  have hb := hZ α F Ψ hα hα4 h j hj
  have hnn : 0 ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ)) :=
    Work.Spaces.HkSq_nonneg α 0 _
  linarith [hb, hnn]




/-! ## Term 1 -/


end Work.FTS.EllipticEst.Prop

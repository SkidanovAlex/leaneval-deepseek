import Mathlib
import Submission.Work.NN.Core.bmPotentialHolderNormLeCk
import Submission.Work.CR.Flat.Cauchy.iteratedFDeriv_succ_of_slice_bounds
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic_open
import Submission.Work.CR.Flat.Cauchy.differentiableAt_complex_of_dbarCoord_eq_zero
import Submission.Work.CR.Flat.Cauchy.contDiffOn_of_differentiableAt_complex
import Submission.Work.NN.Core.bmPot_diff_continuous
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_Ck
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.CR.Flat.Cauchy.polydiscCutoff
import Submission.Work.CR.Flat.Cauchy.holderNorm_zero_iteratedFDeriv_apply_le
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Cauchy.dbar_oneshot_estimate
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le

set_option maxHeartbeats 4000000

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set Filter
open Work.CR.Flat
open Work.CR.Flat.Cauchy

/-! ## Pointwise additivity of iterated Fréchet derivatives -/

/-- **Additivity of iterated Fréchet derivatives.**  Let `U` be an open set on which the iterated
derivatives of `f` and of `g` of every order `< M` exist (i.e. are again differentiable at every
point of `U`).  Then

* for every `m ≤ M` the `m`-th iterated derivative of `f + g` agrees on `U` with the sum of the
  `m`-th iterated derivatives of `f` and of `g`, and
* the iterated derivatives of `f + g` of order `< M` are again differentiable at every point
  of `U`.

This is the pointwise form of the sum rule: no continuity of the top derivative is required. -/
lemma iteratedFDeriv_add_of_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {M : ℕ} {U : Set E} (hU : IsOpen U)
    (hf : ∀ m, m < M → ∀ y ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ m f) y)
    (hg : ∀ m, m < M → ∀ y ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ m g) y) :
    (∀ m, m ≤ M → ∀ y ∈ U, iteratedFDeriv ℝ m (f + g) y
        = iteratedFDeriv ℝ m f y + iteratedFDeriv ℝ m g y) ∧
    (∀ m, m < M → ∀ y ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ m (f + g)) y) := by
  induction M with
  | zero =>
    constructor
    · intro m hm y hy
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      rw [hm0]
      ext v
      simp only [Pi.add_apply, iteratedFDeriv_zero_apply, ContinuousMultilinearMap.add_apply]
    · intro m hm
      exact absurd hm (Nat.not_lt_zero m)
  | succ M ih =>
    have hf' : ∀ m, m < M → ∀ y ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ m f) y :=
      fun m hm => hf m (Nat.lt_succ_of_lt hm)
    have hg' : ∀ m, m < M → ∀ y ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ m g) y :=
      fun m hm => hg m (Nat.lt_succ_of_lt hm)
    obtain ⟨ihA, ihB⟩ := ih hf' hg'
    constructor
    · intro m hm y hy
      rcases Nat.eq_or_lt_of_le hm with h | h
      · rw [h]
        have heq : ∀ y' ∈ U, iteratedFDeriv ℝ M (f + g) y'
            = iteratedFDeriv ℝ M f y' + iteratedFDeriv ℝ M g y' := fun y' hy' => ihA M le_rfl y' hy'
        have hev : iteratedFDeriv ℝ M (f + g)
            =ᶠ[𝓝 y] (fun y' => iteratedFDeriv ℝ M f y' + iteratedFDeriv ℝ M g y') :=
          Filter.eventually_of_mem (hU.mem_nhds hy) fun y' hy' => heq y' hy'
        have hfd : fderiv ℝ (iteratedFDeriv ℝ M (f + g)) y
            = fderiv ℝ (iteratedFDeriv ℝ M f) y + fderiv ℝ (iteratedFDeriv ℝ M g) y := by
          rw [hev.fderiv_eq]
          exact fderiv_add (hf M (Nat.lt_succ_self M) y hy) (hg M (Nat.lt_succ_self M) y hy)
        ext v
        rw [iteratedFDeriv_succ_apply_left (f := f + g) (x := y)]
        rw [ContinuousMultilinearMap.add_apply]
        rw [iteratedFDeriv_succ_apply_left (f := f) (x := y)]
        rw [iteratedFDeriv_succ_apply_left (f := g) (x := y)]
        rw [hfd]
        simp only [ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
      · exact ihA m (Nat.lt_succ_iff.mp h) y hy
    · intro m hm y hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · exact ihB m h y hy
      · rw [h]
        have heq : ∀ y' ∈ U, iteratedFDeriv ℝ M (f + g) y'
            = iteratedFDeriv ℝ M f y' + iteratedFDeriv ℝ M g y' := fun y' hy' => ihA M le_rfl y' hy'
        have hsum : DifferentiableAt ℝ
            (fun y' => iteratedFDeriv ℝ M f y' + iteratedFDeriv ℝ M g y') y :=
          (hf M (Nat.lt_succ_self M) y hy).add (hg M (Nat.lt_succ_self M) y hy)
        exact hsum.congr_of_eventuallyEq
          (Filter.eventually_of_mem (hU.mem_nhds hy) fun y' hy' => (heq y' hy'))


/-! ## The localised datum `∂̄(η u)` of a `C^k` function -/

section CutoffData

variable {n : ℕ} {c : Fin n → ℂ} {ρo B mid : Fin n → ℝ}
variable {u : (Fin n → ℂ) → ℂ} {f : Fin n → (Fin n → ℂ) → ℂ} {η : (Fin n → ℂ) → ℝ}

/-- The pointwise formula `∂̄_j(η u) = η ∂̄_j u + u ∂̄_j η` on the polydisc on which the
equation `∂̄ u = f` holds. -/
lemma dbarCutoff_formula {k : ℕ} (hk : 1 ≤ k)
    (hu : ContDiffOn ℝ k u (polydisc c ρo))
    (heq : ∀ j z, z ∈ polydisc c ρo → dbarCoord j u z = f j z)
    (hηsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) :
    ∀ j z, z ∈ polydisc c ρo →
      dbarCoord j (fun y => (η y : ℂ) * u y) z
        = (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z := by
  intro j z hz
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (η y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hηsm
  have hk0 : (((k : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by
    intro h
    rw [WithTop.coe_eq_zero] at h
    exact Nat.one_le_iff_ne_zero.mp hk (by exact_mod_cast h)
  have hdu : DifferentiableAt ℝ u z :=
    (hu.contDiffAt ((isOpen_polydisc c ρo).mem_nhds hz)).differentiableAt hk0
  have hde : DifferentiableAt ℝ (fun y => (η y : ℂ)) z :=
    ((hsm.differentiable (by simp)).differentiableAt)
  have h := Polydisc.dbarCoord_mul (n := n) j (fun y => (η y : ℂ)) u z hde hdu
  rw [h, heq j z hz]
  ring

/-- The components of the localised datum `∂̄(η u)` are `C^k` on all of `ℂⁿ` when `u` is
`C^k` on the polydisc `polydisc c ρo` and `η` vanishes beyond the (strictly smaller)
multi-radius `B < mid < ρo`. -/
lemma dbarCutoff_contDiff {k : ℕ} (hk : 1 ≤ k)
    (hu : ContDiffOn ℝ k u (polydisc c ρo))
    (hf : ∀ j, ContDiffOn ℝ k (f j) (polydisc c ρo))
    (heq : ∀ j z, z ∈ polydisc c ρo → dbarCoord j u z = f j z)
    (hηsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hη0 : ∀ z, (∃ j, B j ≤ ‖z j - c j‖) → η z = 0)
    (hBmid : ∀ j, B j < mid j) (hmidρo : ∀ j, mid j < ρo j) :
    ∀ j, ContDiff ℝ k (fun z => dbarCoord j (fun y => (η y : ℂ) * u y) z) := by
  intro j
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (η y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hηsm
  have hdetsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => dbarCoord j (fun y => (η y : ℂ)) z) :=
    Work.CR.Flat.Cauchy.contDiff_dbarCoord_of_contDiff j hsm
  have hform := dbarCutoff_formula (n := n) (c := c) (ρo := ρo) (u := u) (f := f) (η := η) hk
    hu heq hηsm
  -- the smooth expression
  have hGsm : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun z => (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z)
      (polydisc c ρo) := by
    refine ContDiffOn.add ?_ ?_
    · exact hsm.contDiffOn.of_le (by simp) |>.mul (hf j)
    · exact (hu.mul (hdetsm.contDiffOn.of_le (by simp)))
  -- the region where the datum vanishes identically nearby
  have hVopen : IsOpen {z : Fin n → ℂ | ∃ i, B i < ‖z i - c i‖} := by
    rw [show {z : Fin n → ℂ | ∃ i, B i < ‖z i - c i‖}
        = ⋃ i, {z : Fin n → ℂ | B i < ‖z i - c i‖} from by ext z; simp]
    exact isOpen_iUnion fun i =>
      isOpen_lt continuous_const ((continuous_apply i).sub continuous_const).norm
  have hVzero : ∀ z : Fin n → ℂ, (∃ i, B i < ‖z i - c i‖) →
      (fun y => (η y : ℂ) * u y) =ᶠ[𝓝 z] (fun _ => 0) := by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds z (sub_pos.mpr hi)) fun y hy => ?_
    have hyi : B i ≤ ‖y i - c i‖ := by
      have h1 : ‖y i - z i‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) i
      have h2 : ‖z i - c i‖ ≤ ‖y i - c i‖ + ‖y i - z i‖ := by
        have h4 : ‖z i - c i‖ ≤ ‖z i - y i‖ + ‖y i - c i‖ := by
          calc ‖z i - c i‖ = ‖(z i - y i) + (y i - c i)‖ := by ring_nf
            _ ≤ ‖z i - y i‖ + ‖y i - c i‖ := norm_add_le _ _
        rw [norm_sub_rev (z i) (y i)] at h4
        linarith
      have h3 : ‖y - z‖ < ‖z i - c i‖ - B i := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      linarith
    simp only [Pi.mul_apply, hη0 y ⟨i, hyi⟩, Complex.ofReal_zero, zero_mul]
  have hCov : ∀ z : Fin n → ℂ, z ∈ polydisc c ρo ∨ ∃ i, B i < ‖z i - c i‖ := by
    intro z
    by_cases hz : z ∈ polydisc c ρo
    · exact Or.inl hz
    · refine Or.inr ?_
      by_contra hcon
      exact hz fun i => lt_of_not_ge fun hi =>
        hcon ⟨i, lt_of_lt_of_le (lt_trans (hBmid i) (hmidρo i)) hi⟩
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  rcases hCov z with hz | hz
  · have hev : (fun z => dbarCoord j (fun y => (η y : ℂ) * u y) z)
        =ᶠ[𝓝 z] (fun z => (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z) := by
      refine Filter.eventually_of_mem ((isOpen_polydisc c ρo).mem_nhds hz) fun y hy => ?_
      exact hform j y hy
    exact (hGsm.contDiffAt ((isOpen_polydisc c ρo).mem_nhds hz)).congr_of_eventuallyEq hev
  · have hzero : (fun z => dbarCoord j (fun y => (η y : ℂ) * u y) z) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hVopen.mem_nhds hz] with y hy
      exact Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_eventuallyEq_zero j (hVzero y hy)
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hzero

/-- The localised datum `∂̄(η u)` vanishes whenever some coordinate is strictly beyond the
multi-radius `B` carrying the support of `η`. -/
lemma dbarCutoff_vanishes
    (hη0 : ∀ z, (∃ j, B j ≤ ‖z j - c j‖) → η z = 0) :
    ∀ j z, (∃ i, B i < ‖z i - c i‖) → dbarCoord j (fun y => (η y : ℂ) * u y) z = 0 := by
  intro j z hz
  obtain ⟨i, hi⟩ := hz
  have hVzero : (fun y => (η y : ℂ) * u y) =ᶠ[𝓝 z] (fun _ => 0) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds z (sub_pos.mpr hi)) fun y hy => ?_
    have hyi : B i ≤ ‖y i - c i‖ := by
      have h1 : ‖y i - z i‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) i
      have h2 : ‖z i - c i‖ ≤ ‖y i - c i‖ + ‖y i - z i‖ := by
        have h4 : ‖z i - c i‖ ≤ ‖z i - y i‖ + ‖y i - c i‖ := by
          calc ‖z i - c i‖ = ‖(z i - y i) + (y i - c i)‖ := by ring_nf
            _ ≤ ‖z i - y i‖ + ‖y i - c i‖ := norm_add_le _ _
        rw [norm_sub_rev (z i) (y i)] at h4
        linarith
      have h3 : ‖y - z‖ < ‖z i - c i‖ - B i := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      linarith
    simp only [Pi.mul_apply, hη0 y ⟨i, hyi⟩, Complex.ofReal_zero, zero_mul]
  exact Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_eventuallyEq_zero j hVzero


/-- Congruence for `∂̄`: eventually equal functions have the same `∂̄`-derivative. -/
lemma dbarCoord_congr {n : ℕ} {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (h : f =ᶠ[𝓝 z] g)
    (j : Fin n) : dbarCoord j f z = dbarCoord j g z := by
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, h.fderiv_eq]

/-- **The localised datum is closed.**  If `∂̄u = f` on the polydisc (with `f` closed there) and
`η` is smooth, then the `(0,1)`-form `∂̄(ηu)` is closed on all of `ℂⁿ` (it vanishes identically
outside the support of `η`). -/
lemma dbarCutoff_closed {k : ℕ} (hk : 1 ≤ k)
    (hu : ContDiffOn ℝ k u (polydisc c ρo))
    (hf : ∀ j, ContDiffOn ℝ k (f j) (polydisc c ρo))
    (hfcl : ∀ j l z, z ∈ polydisc c ρo → dbarCoord l (f j) z = dbarCoord j (f l) z)
    (heq : ∀ j z, z ∈ polydisc c ρo → dbarCoord j u z = f j z)
    (hηsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hη0 : ∀ z, (∃ j, B j ≤ ‖z j - c j‖) → η z = 0)
    (hBmid : ∀ j, B j < mid j) (hmidρo : ∀ j, mid j < ρo j) :
    IsClosedForm (fun j z => dbarCoord j (fun y => (η y : ℂ) * u y) z) := by
  have hηsmC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (η y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hηsm
  have hk0 : (((k : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by
    intro h; rw [WithTop.coe_eq_zero] at h
    exact Nat.one_le_iff_ne_zero.mp hk (by exact_mod_cast h)
  have hform := dbarCutoff_formula (n := n) (c := c) (ρo := ρo) (u := u) (f := f) (η := η) hk
    hu heq hηsm
  intro j l z
  by_cases hz : z ∈ polydisc c ρo
  · -- ### inside the polydisc, compute both sides with the Leibniz rule
    have hzf : ∀ i, DifferentiableAt ℝ (f i) z := fun i =>
      ((hf i).contDiffAt ((isOpen_polydisc c ρo).mem_nhds hz)).differentiableAt hk0
    have hzu : DifferentiableAt ℝ u z :=
      (hu.contDiffAt ((isOpen_polydisc c ρo).mem_nhds hz)).differentiableAt hk0
    have hzη : DifferentiableAt ℝ (fun y => (η y : ℂ)) z :=
      (hηsmC.differentiable (by simp)).differentiableAt
    have hzηd : ∀ i, DifferentiableAt ℝ (fun y => dbarCoord i (fun y => (η y : ℂ)) y) z :=
      fun i => ((Work.CR.Flat.Cauchy.contDiff_dbarCoord_of_contDiff i hηsmC).differentiable
        (by simp)).differentiableAt
    -- replace the datum by the explicit expression on `P(ρo)`
    have hcongr1 : dbarCoord l (fun z => dbarCoord j (fun y => (η y : ℂ) * u y) z) z
        = dbarCoord l (fun z => (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z) z := by
      refine dbarCoord_congr ?_ l
      exact Filter.eventually_of_mem ((isOpen_polydisc c ρo).mem_nhds hz) fun y hy => hform j y hy
    have hcongr2 : dbarCoord j (fun z => dbarCoord l (fun y => (η y : ℂ) * u y) z) z
        = dbarCoord j (fun z => (η z : ℂ) * f l z + u z * dbarCoord l (fun y => (η y : ℂ)) z) z := by
      refine dbarCoord_congr ?_ j
      exact Filter.eventually_of_mem ((isOpen_polydisc c ρo).mem_nhds hz) fun y hy => hform l y hy
    rw [hcongr1, hcongr2]
    -- expand both sides
    have h1 : dbarCoord l (fun z => (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z) z
        = (dbarCoord l (fun y => (η y : ℂ)) z * f j z + (η z : ℂ) * dbarCoord l (f j) z)
          + (dbarCoord l u z * dbarCoord j (fun y => (η y : ℂ)) z
              + u z * dbarCoord l (fun y => dbarCoord j (fun y => (η y : ℂ)) y) z) := by
      let A : (Fin n → ℂ) → ℂ := fun y => (η y : ℂ) * f j y
      let Bf : (Fin n → ℂ) → ℂ := fun y => u y * dbarCoord j (fun y => (η y : ℂ)) y
      have hsum : dbarCoord l (fun w => A w + Bf w) z = dbarCoord l A z + dbarCoord l Bf z :=
        Polydisc.dbarCoord_add l A Bf z (hzη.mul (hzf j)) (hzu.mul (hzηd j))
      have hAm : dbarCoord l A z
          = dbarCoord l (fun y => (η y : ℂ)) z * f j z + (η z : ℂ) * dbarCoord l (f j) z :=
        Polydisc.dbarCoord_mul l (fun y => (η y : ℂ)) (f j) z hzη (hzf j)
      have hBm : dbarCoord l Bf z = dbarCoord l u z * dbarCoord j (fun y => (η y : ℂ)) z
            + u z * dbarCoord l (fun y => dbarCoord j (fun y => (η y : ℂ)) y) z :=
        Polydisc.dbarCoord_mul l u (fun y => dbarCoord j (fun y => (η y : ℂ)) y) z hzu (hzηd j)
      rw [show (fun z => (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z)
          = (fun w => A w + Bf w) from rfl]
      rw [hsum, hAm, hBm]
    have h2 : dbarCoord j (fun z => (η z : ℂ) * f l z + u z * dbarCoord l (fun y => (η y : ℂ)) z) z
        = (dbarCoord j (fun y => (η y : ℂ)) z * f l z + (η z : ℂ) * dbarCoord j (f l) z)
          + (dbarCoord j u z * dbarCoord l (fun y => (η y : ℂ)) z
              + u z * dbarCoord j (fun y => dbarCoord l (fun y => (η y : ℂ)) y) z) := by
      let A : (Fin n → ℂ) → ℂ := fun y => (η y : ℂ) * f l y
      let Bf : (Fin n → ℂ) → ℂ := fun y => u y * dbarCoord l (fun y => (η y : ℂ)) y
      have hsum : dbarCoord j (fun w => A w + Bf w) z = dbarCoord j A z + dbarCoord j Bf z :=
        Polydisc.dbarCoord_add j A Bf z (hzη.mul (hzf l)) (hzu.mul (hzηd l))
      have hAm : dbarCoord j A z
          = dbarCoord j (fun y => (η y : ℂ)) z * f l z + (η z : ℂ) * dbarCoord j (f l) z :=
        Polydisc.dbarCoord_mul j (fun y => (η y : ℂ)) (f l) z hzη (hzf l)
      have hBm : dbarCoord j Bf z = dbarCoord j u z * dbarCoord l (fun y => (η y : ℂ)) z
            + u z * dbarCoord j (fun y => dbarCoord l (fun y => (η y : ℂ)) y) z :=
        Polydisc.dbarCoord_mul j u (fun y => dbarCoord l (fun y => (η y : ℂ)) y) z hzu (hzηd l)
      rw [show (fun z => (η z : ℂ) * f l z + u z * dbarCoord l (fun y => (η y : ℂ)) z)
          = (fun w => A w + Bf w) from rfl]
      rw [hsum, hAm, hBm]
    rw [h1, h2]
    -- use the symmetry of the second derivatives of `η`
    have hsym : dbarCoord j (fun y => dbarCoord l (fun y => (η y : ℂ)) y) z
        = dbarCoord l (fun y => dbarCoord j (fun y => (η y : ℂ)) y) z :=
      Polydisc.dbarCoord_comm l j (fun y => (η y : ℂ)) z
        (hηsmC.contDiffAt.of_le (by simp))
    rw [hsym, hfcl j l z hz, heq l z hz, heq j z hz]
    ring
  · -- ### outside the polydisc both sides vanish
    have hzV : ∃ i, B i < ‖z i - c i‖ := by
      by_contra hcon
      exact hz fun i => lt_of_not_ge fun hi =>
        hcon ⟨i, lt_of_lt_of_le (lt_trans (hBmid i) (hmidρo i)) hi⟩
    have hVopen : IsOpen {z : Fin n → ℂ | ∃ i, B i < ‖z i - c i‖} := by
      rw [show {z : Fin n → ℂ | ∃ i, B i < ‖z i - c i‖}
          = ⋃ i, {z : Fin n → ℂ | B i < ‖z i - c i‖} from by ext z; simp]
      exact isOpen_iUnion fun i =>
        isOpen_lt continuous_const ((continuous_apply i).sub continuous_const).norm
    have hzero : ∀ i, (fun z => dbarCoord i (fun y => (η y : ℂ) * u y) z) =ᶠ[𝓝 z] (fun _ => 0) := by
      intro i
      filter_upwards [hVopen.mem_nhds hzV] with y hy
      exact dbarCutoff_vanishes (n := n) (c := c) (η := η) (u := u) (B := B) hη0 i y hy
    rw [dbarCoord_congr (hzero j) l, dbarCoord_congr (hzero l) j]
    simp [Work.CR.Flat.dbarCoord]

end CutoffData


/-- Slice bound: the derivative of the slice `z ↦ D^k f z v` is bounded by the operator norm of
`D^{k+1} f`. -/
lemma slice_fderiv_bound {n : ℕ} {k : ℕ} {f : (Fin n → ℂ) → ℂ} {v : Fin k → (Fin n → ℂ)}
    {z : Fin n → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z)
    (h : ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ K) :
    ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) z‖ ≤ K * (∏ i, ‖v i‖) := by
  let ev : ((Fin n → ℂ) [×k]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ v
  have hfdev : fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) z
      = ev ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) z := by
    have hcomp : HasFDerivAt (fun y => ev (iteratedFDeriv ℝ k f y))
        (ev.comp (fderiv ℝ (iteratedFDeriv ℝ k f) z)) z :=
      ev.hasFDerivAt.comp z hd.hasFDerivAt
    have h1 : (fun y => ev (iteratedFDeriv ℝ k f y)) = (fun y => iteratedFDeriv ℝ k f y v) := by
      funext y
      simp only [ev, ContinuousMultilinearMap.apply_apply]
    rw [h1] at hcomp
    exact hcomp.fderiv
  have hprod : ∀ w : Fin n → ℂ,
      (∏ i : Fin (k+1), ‖(Fin.cons w v : Fin (k+1) → (Fin n → ℂ)) i‖) = ‖w‖ * (∏ i, ‖v i‖) := by
    intro w
    rw [Fin.prod_univ_succ]
    simp
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hK (Finset.prod_nonneg fun i _ => norm_nonneg _)) fun w => ?_
  rw [hfdev]
  simp only [ContinuousLinearMap.comp_apply]
  have hev : ev ((fderiv ℝ (iteratedFDeriv ℝ k f) z) w)
      = ((fderiv ℝ (iteratedFDeriv ℝ k f) z) w) v := by
    simp only [ev, ContinuousMultilinearMap.apply_apply]
  rw [hev]
  have hcons : ((fderiv ℝ (iteratedFDeriv ℝ k f) z) w) v
      = iteratedFDeriv ℝ (k + 1) f z (Fin.cons w v) := by
    rw [iteratedFDeriv_succ_apply_left (f := f) (x := z) (n := k) (Fin.cons w v)]
    simp [Fin.tail_cons, Fin.cons_zero]
  rw [hcons]
  calc ‖iteratedFDeriv ℝ (k + 1) f z (Fin.cons w v)‖
      ≤ ‖iteratedFDeriv ℝ (k + 1) f z‖
          * (∏ i : Fin (k+1), ‖(Fin.cons w v : Fin (k+1) → (Fin n → ℂ)) i‖) :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (k + 1) f z‖ * (‖w‖ * (∏ i, ‖v i‖)) := by rw [hprod]
    _ ≤ K * (‖w‖ * (∏ i, ‖v i‖)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = K * (∏ i, ‖v i‖) * ‖w‖ := by ring

/-- Slice Hölder bound: the Hölder difference of the derivative of the slice `z ↦ D^k f z v`
is bounded by that of `D^{k+1} f`. -/
lemma slice_fderiv_sub_bound {n : ℕ} {k : ℕ} {f : (Fin n → ℂ) → ℂ} {v : Fin k → (Fin n → ℂ)}
    {z z' : Fin n → ℂ} {K α : ℝ} (hK : 0 ≤ K)
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z)
    (hd' : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z')
    (h : ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f z'‖ ≤ K * ‖z - z'‖ ^ α) :
    ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) z'‖
      ≤ K * (∏ i, ‖v i‖) * ‖z - z'‖ ^ α := by
  let ev : ((Fin n → ℂ) [×k]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ v
  have hfdev : ∀ y, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) y →
      fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) y
        = ev ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) y := by
    intro y hy
    have hcomp : HasFDerivAt (fun y => ev (iteratedFDeriv ℝ k f y))
        (ev.comp (fderiv ℝ (iteratedFDeriv ℝ k f) y)) y :=
      ev.hasFDerivAt.comp y hy.hasFDerivAt
    have h1 : (fun y => ev (iteratedFDeriv ℝ k f y)) = (fun y => iteratedFDeriv ℝ k f y v) := by
      funext y
      simp only [ev, ContinuousMultilinearMap.apply_apply]
    rw [h1] at hcomp
    exact hcomp.fderiv
  have hprod : ∀ w : Fin n → ℂ,
      (∏ i : Fin (k+1), ‖(Fin.cons w v : Fin (k+1) → (Fin n → ℂ)) i‖) = ‖w‖ * (∏ i, ‖v i‖) := by
    intro w
    rw [Fin.prod_univ_succ]
    simp
  have hc : ∀ y : Fin n → ℂ, ∀ w : Fin n → ℂ,
      ((fderiv ℝ (iteratedFDeriv ℝ k f) y) w) v
        = iteratedFDeriv ℝ (k + 1) f y (Fin.cons w v) := by
    intro y w
    rw [iteratedFDeriv_succ_apply_left (f := f) (x := y) (n := k) (Fin.cons w v)]
    simp [Fin.tail_cons, Fin.cons_zero]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hK (Finset.prod_nonneg fun i _ => norm_nonneg _))
      (Real.rpow_nonneg (norm_nonneg _) α)) fun w => ?_
  rw [ContinuousLinearMap.sub_apply,
    show (fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) z) w
        = ev ((fderiv ℝ (iteratedFDeriv ℝ k f) z) w) from by rw [hfdev z hd]; rfl,
    show (fderiv ℝ (fun y => iteratedFDeriv ℝ k f y v) z') w
        = ev ((fderiv ℝ (iteratedFDeriv ℝ k f) z') w) from by rw [hfdev z' hd']; rfl]
  have hev : ∀ y, ev ((fderiv ℝ (iteratedFDeriv ℝ k f) y) w)
      = ((fderiv ℝ (iteratedFDeriv ℝ k f) y) w) v := by
    intro y
    simp only [ev, ContinuousMultilinearMap.apply_apply]
  rw [hev z, hev z', hc z w, hc z' w]
  calc ‖(iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f z') (Fin.cons w v)‖
      ≤ ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f z'‖
          * (∏ i : Fin (k+1), ‖(Fin.cons w v : Fin (k+1) → (Fin n → ℂ)) i‖) :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f z'‖ * (‖w‖ * (∏ i, ‖v i‖)) := by
        rw [hprod]
    _ ≤ (K * ‖z - z'‖ ^ α) * (‖w‖ * (∏ i, ‖v i‖)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = K * (∏ i, ‖v i‖) * ‖z - z'‖ ^ α * ‖w‖ := by ring


/-- Evaluation of a `k`-multilinear map on a fixed tuple, as a continuous linear map. -/
noncomputable def evML {n k : ℕ} (v : Fin k → (Fin n → ℂ)) :
    ((Fin n → ℂ) [×k]→L[ℝ] ℂ) →L[ℝ] ℂ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ v

@[simp] lemma evML_apply {n k : ℕ} (v : Fin k → (Fin n → ℂ))
    (φ : (Fin n → ℂ) [×k]→L[ℝ] ℂ) : evML v φ = φ v :=
  ContinuousMultilinearMap.apply_apply

/-- The Hölder norm on a set depends only on the values of the function on that set.

NOTE (localisation session): this is the *same* lemma as `Work.NN.Core.holderNorm_congr` in
`Submission/Work/NN/Core/exists_holderNorm_wirtinger_le.lean`, whose signature differs only in the
binder style (`k`, `α` implicit there).  Two public declarations of the same name made the closures
of the `Ratio`/`recU` solver chain and of the `bmRow`/`telTwo` chain mutually unimportable (see
`Submission/Work/NN/Final/NOTES_uniformDbarL2_session.md` §12).  The declaration here is therefore
*renamed* here to `holderNorm_congr_oneshot`, so that the canonical public name `holderNorm_congr`
is the widely used copy in `exists_holderNorm_wirtinger_le.lean`; `dbarOneshotC0.lean` (the only other
user) sees that canonical declaration through the import added below. -/
lemma holderNorm_congr_oneshot {n : ℕ} {f g : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (h : Set.EqOn f g Ω) (k : ℕ) (α : ℝ) :
    holderNorm k α f Ω = holderNorm k α g Ω := by
  have h1 : ∀ i : ℕ, iterDerivNorm i f Ω = iterDerivNorm i g Ω := by
    intro i
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [(h.iteratedFDerivWithin i) hx]
  have h2 : ∀ i : ℕ, holderSeminorm i α f Ω = holderSeminorm i α g Ω := by
    intro i
    refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
      iSup_congr fun hxy => ?_
    rw [(h.iteratedFDerivWithin i) hx, (h.iteratedFDerivWithin i) hy]
  simp only [holderNorm]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i, h2 i]

theorem dbarOneshotCk {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hlt : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ k u (Work.CR.Flat.polydisc c ρo) →
      (∀ j, ContDiffOn ℝ k (f j) (Work.CR.Flat.polydisc c ρo)) →
      (∀ j l (z : Fin n → ℂ), z ∈ Work.CR.Flat.polydisc c ρo →
        Work.CR.Flat.dbarCoord l (f j) z = Work.CR.Flat.dbarCoord j (f l) z) →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) →
        Work.CR.Flat.dbarCoord j u z = f j z) →
      Work.CR.Flat.holderNorm (k + 1) α u (Work.CR.Flat.polydisc c ρi)
        ≤ ENNReal.ofReal C *
            ((∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc c ρo))
              + Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc c ρo)) := by
  classical
  by_cases hpos : ∀ j, 0 < ρi j
  · -- ##### main case
    set M₀ : Fin n → ℝ := fun j => max (ρi j) 0 with hM₀
    set A : Fin n → ℝ := fun j => M₀ j + (ρo j - M₀ j) / 3 with hA
    set B : Fin n → ℝ := fun j => M₀ j + 2 * (ρo j - M₀ j) / 3 with hB
    set mid : Fin n → ℝ := fun j => (B j + ρo j) / 2 with hmid
    have hM₀lt : ∀ j, M₀ j < ρo j := fun j => max_lt (hlt j) (hρo j)
    have hApos : ∀ j, 0 < A j := fun j => by
      have h1 : 0 ≤ M₀ j := le_max_right _ _
      have h2 : 0 < ρo j - M₀ j := by linarith [hM₀lt j]
      rw [hA]; linarith
    have hρiA : ∀ j, ρi j < A j := fun j => by
      have h1 : ρi j ≤ M₀ j := le_max_left _ _
      have h2 : 0 < ρo j - M₀ j := by linarith [hM₀lt j]
      rw [hA]; linarith
    have hAB : ∀ j, A j < B j := fun j => by
      have h2 : 0 < ρo j - M₀ j := by linarith [hM₀lt j]
      rw [hA, hB]; linarith
    have hAρo : ∀ j, A j < ρo j := fun j => by
      have h1 : 0 ≤ M₀ j := le_max_right _ _
      have h2 : 0 < ρo j - M₀ j := by linarith [hM₀lt j]
      rw [hA]; linarith
    have hBρo : ∀ j, B j < ρo j := fun j => by
      have h1 : 0 ≤ M₀ j := le_max_right _ _
      have h2 : 0 < ρo j - M₀ j := by linarith [hM₀lt j]
      rw [hB]; linarith
    have hBpos : ∀ j, 0 < B j := fun j => lt_trans (hApos j) (hAB j)
    have hBmid : ∀ j, B j < mid j := fun j => by rw [hmid]; linarith [hBρo j]
    have hmidρo : ∀ j, mid j < ρo j := fun j => by rw [hmid]; linarith [hBρo j]
    have hmidpos : ∀ j, 0 < mid j := fun j => lt_trans (hBpos j) (hBmid j)
    have hρimid : ∀ j, ρi j < mid j := fun j => lt_trans (hρiA j) (lt_trans (hAB j) (hBmid j))
    have hAmid : ∀ j, A j < mid j := fun j => lt_trans (hAB j) (hBmid j)
    obtain ⟨η, hηsm, hη01, hη1, hη0, hηcs, hηdsm, hηdcs⟩ :=
      polydiscCutoff (n := n) (c := c) (r₁ := A) (r₂ := B) k hApos hAB
    have hηsmC : ContDiff ℝ (k + 1) (fun z => (η z : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp hηsm).of_le (by simp)
    have hηdC : ∀ j, ContDiff ℝ (k + 1) (fun z => dbarCoord j (fun y => (η y : ℂ)) z) :=
      fun j => (hηdsm j).of_le (by simp)
    have hηdcs' : ∀ j, HasCompactSupport (fun z => dbarCoord j (fun y => (η y : ℂ)) z) := hηdcs
    obtain ⟨C1, hC1pos, hC1⟩ := holderNorm_mul_le_of_hasCompactSupport (Ω := polydisc c ρo)
      (isOpen_polydisc c ρo).uniqueDiffOn (le_of_lt hα) (le_of_lt hα1) hηsmC hηcs
    have hC2ex : ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ f' : (Fin n → ℂ) → ℂ,
        ContDiffOn ℝ (k : ℕ∞) f' (polydisc c ρo) →
        holderNorm k α (fun z => dbarCoord j (fun y => (η y : ℂ)) z * f' z) (polydisc c ρo)
          ≤ ENNReal.ofReal C * holderNorm k α f' (polydisc c ρo) := fun j =>
      holderNorm_mul_le_of_hasCompactSupport (Ω := polydisc c ρo)
        (isOpen_polydisc c ρo).uniqueDiffOn (le_of_lt hα) (le_of_lt hα1) (hηdC j) (hηdcs' j)
    choose C2 hC2pos hC2 using hC2ex
    set C2t : ℝ := (∑ j, C2 j) + 1 with hC2t
    have hC2tpos : 0 < C2t := by
      have hle : (0 : ℝ) ≤ ∑ j, C2 j := Finset.sum_nonneg fun j _ => le_of_lt (hC2pos j)
      rw [hC2t]; linarith
    have hC2le : ∀ j, C2 j ≤ C2t := fun j => by
      have hsum : C2 j ≤ ∑ i, C2 i :=
        Finset.single_le_sum (fun i _ => le_of_lt (hC2pos i)) (Finset.mem_univ j)
      rw [hC2t]; linarith
    set Kmul : ℝ := max C1 C2t with hKmul
    have hKmulpos : 0 < Kmul := lt_of_lt_of_le hC1pos (le_max_left _ _)
    have hC1K : C1 ≤ Kmul := le_max_left _ _
    have hC2tK : C2t ≤ Kmul := le_max_right _ _
    obtain ⟨Cbmi, hCbmipos, hCbmi⟩ := bmPotentialHolderNormLeCk (n := n) hn (c := c)
      (s := mid) (t := ρi) hα hα1 hpos hρimid k
    obtain ⟨CbmA, hCbmApos, hCbmA⟩ := bmPotentialHolderNormLeCk (n := n) hn (c := c)
      (s := mid) (t := A) hα hα1 hApos hAmid k
    obtain ⟨Chol, hCholpos, hChol⟩ := holderNorm_le_sup_of_holomorphic_bound (n := n) hn
      (c := c) (ρi := ρi) (ρo := A) hρiA (le_of_lt hα) (le_of_lt hα1) k
    obtain ⟨Cpot, hCpotpos, hCpot⟩ := bmPot_holder_C0a (n := n) hn (c := c)
      (r := fun j => 2 * mid j) hα hα1 (fun j => by linarith [hmidpos j])
    obtain ⟨γ, hγ, hγsol⟩ := bmPotential_solves_dbar (n := n) hn (c := c)
      (r := fun j => 2 * mid j) (fun j => by linarith [hmidpos j])
    set Cg : ℝ := (n : ℝ) * Kmul + 1 with hCg
    have hCgpos : 0 < Cg := by rw [hCg]; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; nlinarith [hKmulpos]
    have hCgK : Kmul * (n : ℝ) ≤ Cg := by rw [hCg]; linarith
    set Ctot : ℝ := Chol + Chol * ‖(γ⁻¹ : ℂ)‖ * CbmA * Cg + ‖(γ⁻¹ : ℂ)‖ * Cpot * Cg with hCtot
    refine ⟨1 + 2 * Ctot, by positivity, ?_⟩
    intro u f hu hf hfcl heq
    by_cases htop : (∑ j, holderNorm k α (f j) (polydisc c ρo))
        + holderNorm k α u (polydisc c ρo) = ⊤
    · rw [htop, ENNReal.mul_top (by positivity)]
      exact le_top
    · have hSf_lt : (∑ j, holderNorm k α (f j) (polydisc c ρo)) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h
        exact htop (by rw [h, top_add])
      have hSu_lt : holderNorm k α u (polydisc c ρo) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h
        exact htop (by rw [h, add_top])
      set sf : ℝ := (∑ j, holderNorm k α (f j) (polydisc c ρo)).toReal with hsf
      set su : ℝ := (holderNorm k α u (polydisc c ρo)).toReal with hsu
      have hsf_eq : (∑ j, holderNorm k α (f j) (polydisc c ρo)) = ENNReal.ofReal sf :=
        (ENNReal.ofReal_toReal hSf_lt.ne).symm
      have hsu_eq : holderNorm k α u (polydisc c ρo) = ENNReal.ofReal su :=
        (ENNReal.ofReal_toReal hSu_lt.ne).symm
      have hsf0 : 0 ≤ sf := ENNReal.toReal_nonneg
      have hsu0 : 0 ≤ su := ENNReal.toReal_nonneg
      /- ### the localised datum -/
      set g : Fin n → (Fin n → ℂ) → ℂ := fun j z => dbarCoord j (fun y => (η y : ℂ) * u y) z with hg
      have hg_apply : ∀ j z, g j z = dbarCoord j (fun y => (η y : ℂ) * u y) z := by
        intro j z; rw [hg]
      have hg_fun : ∀ j, g j = fun z => dbarCoord j (fun y => (η y : ℂ) * u y) z :=
        fun j => funext fun z => hg_apply j z
      have hg_sm : ∀ j, ContDiff ℝ k (g j) := by
        intro j
        rw [hg_fun j]
        exact dbarCutoff_contDiff (n := n) (c := c) (ρo := ρo) (u := u) (f := f) (η := η) (B := B)
          (mid := mid) hk hu hf heq hηsm hη0 hBmid hmidρo j
      have hg_closed : IsClosedForm g := by
        intro j l z
        rw [hg_fun j, hg_fun l]
        exact dbarCutoff_closed (n := n) (c := c) (ρo := ρo) (u := u) (f := f) (η := η) (B := B)
          (mid := mid) hk hu hf hfcl heq hηsm hη0 hBmid hmidρo j l z
      have hg_van : ∀ j z, (∃ i, B i < ‖z i - c i‖) → g j z = 0 := by
        intro j z hz
        rw [hg_apply j]
        exact dbarCutoff_vanishes (n := n) (c := c) (η := η) (u := u) (B := B) hη0 j z hz
      have hg_van_mid : ∀ j z, (∃ i, mid i ≤ ‖z i - c i‖) → g j z = 0 := fun j z hz =>
        hg_van j z ⟨hz.choose, lt_of_lt_of_le (hBmid hz.choose) hz.choose_spec⟩
      have hg_cs : ∀ j, HasCompactSupport (g j) := fun j =>
        HasCompactSupport.of_support_subset_isCompact
          (Work.CR.Flat.Cauchy.isCompact_closed_polydisc (fun i => (hBpos i).le))
          (fun z hz => by
            by_contra hcon
            simp only [Set.mem_ofPred_eq, not_forall, not_le] at hcon
            exact hz (hg_van j z hcon))
      have hg_form : ∀ j z, z ∈ polydisc c ρo →
          g j z = (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z := by
        intro j z hz
        rw [hg_apply j]
        exact dbarCutoff_formula (n := n) (c := c) (ρo := ρo) (u := u) (f := f) (η := η) hk hu
          heq hηsm j z hz
      -- the datum agrees with `f` on `P(A)`
      have hgA : ∀ j z, z ∈ polydisc c A → g j z = f j z := by
        intro j z hz
        rw [hg_form j z (fun i => lt_trans (hz i) (hAρo i))]
        have h1 : (η z : ℂ) = 1 := by
          rw [hη1 z (fun j => le_of_lt (hz j))]; norm_num
        have h2 : dbarCoord j (fun y => (η y : ℂ)) z = 0 := by
          have hev : (fun y => (η y : ℂ)) =ᶠ[𝓝 z] (fun _ => 1) :=
            Filter.eventually_of_mem ((isOpen_polydisc c A).mem_nhds hz) fun y hy => by
              show (η y : ℂ) = 1
              rw [hη1 y (fun j => le_of_lt (hy j))]; norm_num
          rw [Work.CR.Flat.dbarCoord, hev.fderiv_eq]
          simp
        rw [h1, h2]
        ring
      /- ### the size of the datum -/
      have hgle : ∀ j, holderNorm k α (g j) (polydisc c ρo)
          ≤ ENNReal.ofReal Kmul * (holderNorm k α (f j) (polydisc c ρo)
              + holderNorm k α u (polydisc c ρo)) := by
        intro j
        have hsum : holderNorm k α (g j) (polydisc c ρo)
            ≤ holderNorm k α (fun z => (η z : ℂ) * f j z) (polydisc c ρo)
              + holderNorm k α (fun z => u z * dbarCoord j (fun y => (η y : ℂ)) z)
                  (polydisc c ρo) := by
          rw [holderNorm_congr_oneshot (f := g j)
            (g := fun z => (η z : ℂ) * f j z + u z * dbarCoord j (fun y => (η y : ℂ)) z)
            (fun z hz => hg_form j z hz) k α]
          exact Work.CR.Flat.Holder.holderNorm_add_le
            ((hηsmC.contDiffOn.of_le (by simp)).mul (hf j))
            ((hu.mul ((hηdC j).contDiffOn.of_le (by simp))))
            (isOpen_polydisc c ρo).uniqueDiffOn
        have h4 : holderNorm k α (fun z => u z * dbarCoord j (fun y => (η y : ℂ)) z)
            (polydisc c ρo) ≤ ENNReal.ofReal Kmul * holderNorm k α u (polydisc c ρo) := by
          rw [show (fun z => u z * dbarCoord j (fun y => (η y : ℂ)) z)
              = (fun z => dbarCoord j (fun y => (η y : ℂ)) z * u z) from funext fun z => by ring]
          exact (hC2 j u hu).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (le_trans (hC2le j) hC2tK)) _)
        exact hsum.trans (by
          calc holderNorm k α (fun z => (η z : ℂ) * f j z) (polydisc c ρo)
                + holderNorm k α (fun z => u z * dbarCoord j (fun y => (η y : ℂ)) z) (polydisc c ρo)
              ≤ ENNReal.ofReal C1 * holderNorm k α (f j) (polydisc c ρo)
                + ENNReal.ofReal Kmul * holderNorm k α u (polydisc c ρo) :=
                add_le_add (hC1 (f j) (hf j)) h4
            _ ≤ ENNReal.ofReal Kmul * holderNorm k α (f j) (polydisc c ρo)
                + ENNReal.ofReal Kmul * holderNorm k α u (polydisc c ρo) :=
                add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC1K) _) le_rfl
            _ = ENNReal.ofReal Kmul * (holderNorm k α (f j) (polydisc c ρo)
                + holderNorm k α u (polydisc c ρo)) := by rw [mul_add])
      have hgle2 : ∑ j, holderNorm k α (g j) Set.univ
          ≤ ENNReal.ofReal Kmul * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
              + (n : ℝ≥0∞) * holderNorm k α u (polydisc c ρo)) := by
        calc ∑ j, holderNorm k α (g j) Set.univ
            ≤ ∑ j, holderNorm k α (g j) (polydisc c ρo) := by
              refine Finset.sum_le_sum fun j _ => ?_
              exact holderNorm_univ_le_holderNorm_polydisc_of_vanishing (c := c) (r := mid)
                (r' := ρo) hmidρo (le_of_lt hα) (fun z hz => hg_van_mid j z hz)
          _ ≤ ∑ j, ENNReal.ofReal Kmul * (holderNorm k α (f j) (polydisc c ρo)
                + holderNorm k α u (polydisc c ρo)) := Finset.sum_le_sum fun j _ => hgle j
          _ = ENNReal.ofReal Kmul * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
                + (n : ℝ≥0∞) * holderNorm k α u (polydisc c ρo)) := by
              rw [← Finset.mul_sum]
              congr 1
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
      have hSg_bound : ∑ j, holderNorm k α (g j) Set.univ
          ≤ ENNReal.ofReal Cg * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
              + holderNorm k α u (polydisc c ρo)) := by
        have hCg_ge : Kmul ≤ Cg := by
          rw [hCg]
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith [hKmulpos]
        have hCg_ge2 : Kmul * (n : ℝ) ≤ Cg := by
          rw [hCg]
          have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [hKmulpos]
        have hreal : Kmul * (sf + (n : ℝ) * su) ≤ Cg * (sf + su) := by
          calc Kmul * (sf + (n : ℝ) * su) = Kmul * sf + (Kmul * (n : ℝ)) * su := by ring
            _ ≤ Cg * sf + Cg * su := by
                refine add_le_add ?_ ?_
                · exact mul_le_mul_of_nonneg_right hCg_ge hsf0
                · exact mul_le_mul_of_nonneg_right hCg_ge2 hsu0
            _ = Cg * (sf + su) := by ring
        have h1 : ENNReal.ofReal (Kmul * (sf + (n : ℝ) * su)) ≤ ENNReal.ofReal (Cg * (sf + su)) :=
          ENNReal.ofReal_le_ofReal hreal
        calc ∑ j, holderNorm k α (g j) Set.univ
            ≤ ENNReal.ofReal Kmul * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
                + (n : ℝ≥0∞) * holderNorm k α u (polydisc c ρo)) := hgle2
          _ = ENNReal.ofReal (Kmul * (sf + (n : ℝ) * su)) := by
              rw [hsf_eq, hsu_eq, ← ENNReal.ofReal_natCast n,
                ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
                ← ENNReal.ofReal_add hsf0 (by positivity), ← ENNReal.ofReal_mul hKmulpos.le]
          _ ≤ ENNReal.ofReal (Cg * (sf + su)) := h1
          _ = ENNReal.ofReal Cg * (ENNReal.ofReal sf + ENNReal.ofReal su) := by
              rw [← ENNReal.ofReal_add hsf0 hsu0, ← ENNReal.ofReal_mul hCgpos.le]
          _ = ENNReal.ofReal Cg * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
              + holderNorm k α u (polydisc c ρo)) := by rw [hsf_eq, hsu_eq]
      have hST_eq : (∑ j, holderNorm k α (f j) (polydisc c ρo))
          + holderNorm k α u (polydisc c ρo) = ENNReal.ofReal (sf + su) := by
        rw [hsf_eq, hsu_eq]
        exact (ENNReal.ofReal_add hsf0 hsu0).symm
      have hSg_lt : ∑ j, holderNorm k α (g j) Set.univ < ⊤ := by
        refine lt_of_le_of_lt hSg_bound ?_
        rw [hST_eq]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      /- ### the Bochner--Martinelli potential and the holomorphic correction -/
      set W : (Fin n → ℂ) → ℂ := bmPotential g with hW
      have hWsol : ∀ j z, (∀ i, ‖z i - c i‖ < mid i) → dbarCoord j W z = γ * g j z := by
        intro j z hz
        refine hγsol g (fun j => (hg_sm j).of_le (by exact_mod_cast hk)) (fun j z hz' => ?_)
          hg_closed j z ?_
        · obtain ⟨i, hi⟩ := hz'
          refine hg_van_mid j z ⟨i, ?_⟩
          rw [show (2 * mid i) / 2 = mid i from by ring] at hi
          exact hi
        · intro i
          rw [show (2 * mid i) / 2 = mid i from by ring]
          exact hz i
      have hW_cd : ContDiff ℝ k W := by
        rw [hW]
        exact bmPotential_contDiff_of_hasCompactSupport hn hg_sm hg_cs
      have hW_diff : ∀ z ∈ polydisc c A, DifferentiableAt ℝ W z := by
        intro z hz
        rw [hW]
        refine bmPot_diff_continuous (n := n) hn (c := c) (r := fun j => 2 * mid j)
          hα hα1 (fun j => by linarith [hmidpos j]) (fun j => (hg_sm j).continuous)
          (fun j => ?_) (fun j w hw => ?_) z ?_
        · refine lt_of_le_of_lt (holderNorm_mono_k (Nat.zero_le k) α (g j) Set.univ) ?_
          exact lt_of_le_of_lt (Finset.single_le_sum
            (f := fun i => holderNorm k α (g i) Set.univ) (fun i _ => bot_le)
            (Finset.mem_univ j)) hSg_lt
        · obtain ⟨i, hi⟩ := hw
          refine hg_van_mid j w ⟨i, ?_⟩
          rw [show (2 * mid i) / 2 = mid i from by ring] at hi
          exact hi
        · rw [show (fun j => (2 * mid j) / 2) = mid from funext fun j => by ring]
          exact fun i => lt_trans (hz i) (hAmid i)
      set ww : (Fin n → ℂ) → ℂ := fun z => (γ⁻¹ : ℂ) * W z with hww
      set h : (Fin n → ℂ) → ℂ := fun z => u z - ww z with hh
      have hu_split : h + ww = u := by
        funext z; rw [hh, hww]; simp only [Pi.add_apply]; ring
      have hWhol : ∀ j z, z ∈ polydisc c A → dbarCoord j h z = 0 := by
        intro j z hz
        have hzmid : ∀ i, ‖z i - c i‖ < mid i := fun i => lt_trans (hz i) (hAmid i)
        have hzρo : ∀ i, ‖z i - c i‖ < ρo i := fun i => lt_trans (hz i) (hAρo i)
        have hk0 : (((k : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by
          intro hh0; rw [WithTop.coe_eq_zero] at hh0
          exact Nat.one_le_iff_ne_zero.mp hk (by exact_mod_cast hh0)
        have hdu : DifferentiableAt ℝ u z :=
          (hu.contDiffAt ((isOpen_polydisc c ρo).mem_nhds hzρo)).differentiableAt hk0
        have hdW : DifferentiableAt ℝ W z := hW_diff z hz
        have hdww : DifferentiableAt ℝ ww z := by
          rw [hww]; exact hdW.const_mul _
        rw [hh, Work.CR.Flat.Cauchy.dbarCoord_sub j u ww z hdu hdww,
          Work.CR.Flat.Cauchy.dbarSolution_dbarCoord_const_mul j (γ⁻¹) hdW,
          heq j z hzρo, hWsol j z hzmid]
        rw [← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
        rw [← hgA j z hz]
        ring
      /- ### `h` is holomorphic on `P(A)`, hence `C^{k+1}` there -/
      have hh_cd : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) h (polydisc c A) := by
        refine Work.CR.Flat.Cauchy.contDiffOn_of_differentiableAt_complex (isOpen_polydisc c A)
          (fun z hz => ?_) (k + 1)
        have hk0 : (((k : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by
          intro hh0; rw [WithTop.coe_eq_zero] at hh0
          exact Nat.one_le_iff_ne_zero.mp hk (by exact_mod_cast hh0)
        have hzρo : ∀ i, ‖z i - c i‖ < ρo i := fun i => lt_trans (hz i) (hAρo i)
        have hdu : DifferentiableAt ℝ u z :=
          (hu.contDiffAt ((isOpen_polydisc c ρo).mem_nhds hzρo)).differentiableAt hk0
        have hdww : DifferentiableAt ℝ ww z := by
          rw [hww]; exact (hW_diff z hz).const_mul _
        refine Work.CR.Flat.Cauchy.differentiableAt_complex_of_dbarCoord_eq_zero ?_ ?_
        · rw [hh]
          exact hdu.sub hdww
        · intro j
          exact hWhol j z hz
      /- ### sup bounds on `P(A)` -/
      have hW_bound_A : holderNorm (k + 1) α W (polydisc c A)
          ≤ ENNReal.ofReal (CbmA * Cg) * (ENNReal.ofReal sf + ENNReal.ofReal su) := by
        have h1 : holderNorm (k + 1) α W (polydisc c A)
            ≤ ENNReal.ofReal (CbmA * Cg) * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
                + holderNorm k α u (polydisc c ρo)) := by
          calc holderNorm (k + 1) α W (polydisc c A)
              ≤ ENNReal.ofReal CbmA * ∑ j, holderNorm k α (g j) Set.univ := by
                rw [hW]
                exact hCbmA g hg_sm (fun j z hz => hg_van_mid j z hz)
            _ ≤ ENNReal.ofReal CbmA * (ENNReal.ofReal Cg * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
                  + holderNorm k α u (polydisc c ρo))) :=
                mul_le_mul_of_nonneg_left hSg_bound (by positivity)
            _ = ENNReal.ofReal (CbmA * Cg) * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
                  + holderNorm k α u (polydisc c ρo)) := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul hCbmApos.le]
        rw [hST_eq, ENNReal.ofReal_add hsf0 hsu0] at h1
        exact h1
      have hWu : ∀ z ∈ polydisc c A, ‖W z‖ ≤ CbmA * Cg * (sf + su) := by
        intro z hz
        have h1 : ENNReal.ofReal ‖W z‖
            ≤ ENNReal.ofReal (CbmA * Cg) * ENNReal.ofReal (sf + su) := by
          calc ENNReal.ofReal ‖W z‖ ≤ iterDerivNorm 0 W (polydisc c A) := by
                rw [iterDerivNorm_zero]
                exact le_iSup₂_of_le z hz le_rfl
            _ ≤ holderNorm (k + 1) α W (polydisc c A) :=
                iterDerivNorm_le_holderNorm (k + 1) α W _ (Nat.zero_le _)
            _ ≤ ENNReal.ofReal (CbmA * Cg) * (ENNReal.ofReal sf + ENNReal.ofReal su) := hW_bound_A
            _ = ENNReal.ofReal (CbmA * Cg) * ENNReal.ofReal (sf + su) := by rw [← ENNReal.ofReal_add hsf0 hsu0]
        rw [← ENNReal.ofReal_mul (by positivity)] at h1
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
      have huu : ∀ z ∈ polydisc c A, ‖u z‖ ≤ su := by
        intro z hz
        have hzρo : z ∈ polydisc c ρo := fun i => lt_trans (hz i) (hAρo i)
        have h1 : ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal su := by
          calc ENNReal.ofReal ‖u z‖ ≤ iterDerivNorm 0 u (polydisc c ρo) := by
                rw [iterDerivNorm_zero]
                exact le_iSup₂_of_le z hzρo le_rfl
            _ ≤ holderNorm k α u (polydisc c ρo) := iterDerivNorm_le_holderNorm k α u _ (Nat.zero_le _)
            _ = ENNReal.ofReal su := hsu_eq
        exact (ENNReal.ofReal_le_ofReal_iff hsu0).mp h1
      set Bh : ℝ := su + ‖(γ⁻¹ : ℂ)‖ * (CbmA * Cg * (sf + su)) with hBh
      have hBh0 : 0 ≤ Bh := by
        rw [hBh]
        have h1 : 0 ≤ sf + su := by linarith
        positivity
      have hh_sup : ∀ z ∈ polydisc c A, ‖h z‖ ≤ Bh := by
        intro z hz
        rw [hh, hBh]
        calc ‖u z - ww z‖ ≤ ‖u z‖ + ‖ww z‖ := norm_sub_le _ _
          _ = ‖u z‖ + ‖(γ⁻¹ : ℂ)‖ * ‖W z‖ := by rw [hww, norm_mul]
          _ ≤ su + ‖(γ⁻¹ : ℂ)‖ * (CbmA * Cg * (sf + su)) := by
              refine add_le_add (huu z hz) ?_
              exact mul_le_mul_of_nonneg_left (hWu z hz) (norm_nonneg _)
      have hh_bound : holderNorm (k + 1) α h (polydisc c ρi) ≤ ENNReal.ofReal (Chol * Bh) :=
        hChol h Bh hBh0 hh_cd (fun j z hz => hWhol j z hz) (fun z hz => hh_sup z hz)
      /- ### the differentials of `h` are differentiable on `P(ρi)` -/
      have hh_diff : ∀ m, m ≤ k → ∀ y ∈ polydisc c ρi,
          DifferentiableAt ℝ (iteratedFDeriv ℝ m h) y := by
        intro m hm y hy
        have hyA : y ∈ polydisc c A := fun i => lt_trans (hy i) (hρiA i)
        have h1 : ContDiffWithinAt ℝ ((k + 1 : ℕ) : ℕ∞) h (polydisc c A) y :=
          hh_cd.contDiffWithinAt hyA
        have h2 : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ m h (polydisc c A))
            (polydisc c A) y :=
          h1.differentiableWithinAt_iteratedFDerivWithin (by exact_mod_cast Nat.lt_succ_of_le hm)
            (by rw [Set.insert_eq_of_mem hyA]; exact (isOpen_polydisc c A).uniqueDiffOn)
        have h3 : DifferentiableAt ℝ (iteratedFDerivWithin ℝ m h (polydisc c A)) y :=
          h2.differentiableAt ((isOpen_polydisc c A).mem_nhds hyA)
        refine h3.congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_polydisc c A).mem_nhds hyA] with z hz
        exact (iteratedFDerivWithin_of_isOpen m (isOpen_polydisc c A) hz).symm
      have hw_diff : ∀ m, m < k → ∀ y ∈ polydisc c ρi,
          DifferentiableAt ℝ (iteratedFDeriv ℝ m ww) y := by
        intro m hm y hy
        have h2 : iteratedFDeriv ℝ m ww = fun z => (γ⁻¹ : ℂ) • iteratedFDeriv ℝ m W z := by
          funext z
          rw [hww]
          exact iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (f := W) (a := (γ⁻¹ : ℂ))
            (x := z) (i := m) ((hW_cd.contDiffAt).of_le (by exact_mod_cast hm.le))
        rw [h2]
        have h3 : DifferentiableAt ℝ (fun z => (γ⁻¹ : ℂ) • iteratedFDeriv ℝ m W z) y :=
          ((hW_cd.contDiffAt (x := y)).differentiableAt_iteratedFDeriv (m := m)
            (by exact_mod_cast hm)).const_smul ((γ⁻¹ : ℂ))
        exact h3
      /- ### additivity of the `k`-th derivative -/
      have hADD := (iteratedFDeriv_add_of_diff (f := h) (g := ww) (M := k)
        (U := polydisc c ρi) (isOpen_polydisc c ρi)
        (fun m hm y hy => hh_diff m hm.le y hy) (fun m hm y hy => hw_diff m hm y hy)).1
      have hslice_u : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          (iteratedFDeriv ℝ k u y) v
            = (iteratedFDeriv ℝ k h y) v + (iteratedFDeriv ℝ k ww y) v := by
        intro v y hy
        have h1 : iteratedFDeriv ℝ k u y = iteratedFDeriv ℝ k (h + ww) y := by rw [hu_split]
        rw [h1, hADD k le_rfl y hy, ContinuousMultilinearMap.add_apply]
      /- ### the slice of the potential -/
      have hg_data_van : ∀ j w, (∃ i, (2 * mid i) / 2 ≤ ‖w i - c i‖) → g j w = 0 := by
        intro j w hw
        obtain ⟨i, hi⟩ := hw
        refine hg_van_mid j w ⟨i, ?_⟩
        rw [show (2 * mid i) / 2 = mid i from by ring] at hi
        exact hi
      have hslice_w_eq : ∀ v : Fin k → (Fin n → ℂ),
          (fun z => (iteratedFDeriv ℝ k ww z) v)
            = fun z => (γ⁻¹ : ℂ) * bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z := by
        intro v
        funext z
        have h3 : iteratedFDeriv ℝ k ww z = (γ⁻¹ : ℂ) • iteratedFDeriv ℝ k W z := by
          rw [hww]
          exact iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (f := W) (a := (γ⁻¹ : ℂ))
            (x := z) (i := k) hW_cd.contDiffAt
        rw [h3, ContinuousMultilinearMap.smul_apply]
        show (γ⁻¹ : ℂ) * ((iteratedFDeriv ℝ k W z) v)
          = (γ⁻¹ : ℂ) * bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z
        congr 1
        rw [hW]
        exact bmPotential_iteratedFDeriv (n := n) hn (c := c) (R := fun j => 2 * mid j)
          (fun j => by linarith [hmidpos j]) (G := g) (i := k) hg_sm hg_data_van v z
      have hslice_h_diff : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          DifferentiableAt ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y := by
        intro v y hy
        have h2 : DifferentiableAt ℝ (fun z => evML v (iteratedFDeriv ℝ k h z)) y :=
          (evML v).differentiableAt.comp y (hh_diff k le_rfl y hy)
        simpa only [evML_apply] using h2
      have hgv_van : ∀ j w, (∃ i, B i < ‖w i - c i‖) → ∀ v : Fin k → (Fin n → ℂ),
          (iteratedFDeriv ℝ k (g j) w) v = 0 := by
        intro j w hw v
        have hwo : IsOpen {z : Fin n → ℂ | ∃ i, B i < ‖z i - c i‖} := by
          rw [show {z : Fin n → ℂ | ∃ i, B i < ‖z i - c i‖}
              = ⋃ i, {z : Fin n → ℂ | B i < ‖z i - c i‖} from by ext z; simp]
          exact isOpen_iUnion fun i =>
            isOpen_lt continuous_const ((continuous_apply i).sub continuous_const).norm
        have hev : g j =ᶠ[𝓝 w] (fun _ => 0) :=
          Filter.eventually_of_mem (hwo.mem_nhds hw) fun z hz => hg_van j z hz
        have h2 : iteratedFDeriv ℝ k (g j) w = iteratedFDeriv ℝ k (fun _ => (0 : ℂ)) w :=
          (hev.iteratedFDeriv ℝ k).eq_of_nhds
        rw [h2]
        simp
      have hpot_diff : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          DifferentiableAt ℝ
            (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y := by
        intro v y hy
        refine bmPot_diff_continuous (n := n) hn (c := c) (r := fun j => 2 * mid j) hα hα1
          (fun j => by linarith [hmidpos j]) (fun j => ?_) (fun j => ?_)
          (fun j w hw => ?_) y ?_
        · exact (evML v).continuous.comp ((hg_sm j).continuous_iteratedFDeriv (m := k) le_rfl)
        · refine lt_of_le_of_lt (holderNorm_zero_iteratedFDeriv_apply_le (m := k) le_rfl v) ?_
          refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Finset.single_le_sum
            (f := fun i => holderNorm k α (g i) Set.univ) (fun i _ => bot_le)
            (Finset.mem_univ j)) (by positivity)) ?_
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSg_lt
        · refine hgv_van j w ?_ v
          obtain ⟨i, hi⟩ := hw
          exact ⟨i, lt_of_lt_of_le (hBmid i) (by
            rw [show (2 * mid i) / 2 = mid i from by ring] at hi; exact hi)⟩
        · rw [show (fun j => (2 * mid j) / 2) = mid from funext fun j => by ring]
          exact fun i => lt_trans (hy i) (hρimid i)
      have hslice_w_diff : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          DifferentiableAt ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y := by
        intro v y hy
        rw [hslice_w_eq v]
        exact (hpot_diff v y hy).const_mul _
      /- ### bounds for the slices of `h` -/
      have hDh : ∀ y ∈ polydisc c ρi, ‖iteratedFDeriv ℝ (k + 1) h y‖ ≤ Chol * Bh := by
        intro y hy
        have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ (k + 1) h y‖ ≤ ENNReal.ofReal (Chol * Bh) := by
          calc ENNReal.ofReal ‖iteratedFDeriv ℝ (k + 1) h y‖
              = ENNReal.ofReal ‖iteratedFDerivWithin ℝ (k + 1) h (polydisc c ρi) y‖ := by
                rw [iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_polydisc c ρi) hy]
            _ ≤ iterDerivNorm (k + 1) h (polydisc c ρi) := le_iterDerivNorm (k + 1) h _ hy
            _ ≤ holderNorm (k + 1) α h (polydisc c ρi) :=
                iterDerivNorm_le_holderNorm (k + 1) α h _ le_rfl
            _ ≤ ENNReal.ofReal (Chol * Bh) := hh_bound
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
      have hDh_holder : ∀ y ∈ polydisc c ρi, ∀ y' ∈ polydisc c ρi,
          ‖iteratedFDeriv ℝ (k + 1) h y - iteratedFDeriv ℝ (k + 1) h y'‖
            ≤ (Chol * Bh) * ‖y - y'‖ ^ α := by
        intro y hy y' hy'
        rcases eq_or_ne y y' with rfl | hne
        · have h1 : ‖iteratedFDeriv ℝ (k + 1) h y - iteratedFDeriv ℝ (k + 1) h y‖ = 0 := by
            rw [sub_self, norm_zero]
          have h2 : ‖y - y‖ ^ α = 0 := by
            rw [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hα)]
          rw [h1, h2]
          simp
        · have h1 : ENNReal.ofReal (‖iteratedFDeriv ℝ (k + 1) h y - iteratedFDeriv ℝ (k + 1) h y'‖
              / ‖y - y'‖ ^ α) ≤ ENNReal.ofReal (Chol * Bh) := by
            calc ENNReal.ofReal (‖iteratedFDeriv ℝ (k + 1) h y - iteratedFDeriv ℝ (k + 1) h y'‖
                  / ‖y - y'‖ ^ α)
                = ENNReal.ofReal
                    (‖iteratedFDerivWithin ℝ (k + 1) h (polydisc c ρi) y
                      - iteratedFDerivWithin ℝ (k + 1) h (polydisc c ρi) y'‖ / ‖y - y'‖ ^ α) := by
                  rw [iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_polydisc c ρi) hy,
                    iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_polydisc c ρi) hy']
              _ ≤ holderSeminorm (k + 1) α h (polydisc c ρi) :=
                  le_holderSeminorm (k + 1) α h _ hy hy' hne
              _ ≤ holderNorm (k + 1) α h (polydisc c ρi) :=
                  holderSeminorm_le_holderNorm (k + 1) α h _ le_rfl
              _ ≤ ENNReal.ofReal (Chol * Bh) := hh_bound
          have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
          have hpos : 0 < ‖y - y'‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
          calc ‖iteratedFDeriv ℝ (k + 1) h y - iteratedFDeriv ℝ (k + 1) h y'‖
              = (‖iteratedFDeriv ℝ (k + 1) h y - iteratedFDeriv ℝ (k + 1) h y'‖
                  / ‖y - y'‖ ^ α) * ‖y - y'‖ ^ α := by
                rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
            _ ≤ (Chol * Bh) * ‖y - y'‖ ^ α :=
                mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) α)
      /- ### the `C^{1,α}` bound for the potential of a derived datum -/
      have hC1a : ∀ v : Fin k → (Fin n → ℂ),
          holderNorm 1 α
            (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
            (polydisc c mid) ≤ ENNReal.ofReal (Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su))) := by
        intro v
        have hmain := hCpot (fun j z => (iteratedFDeriv ℝ k (g j) z) v)
          (fun j z hz => ?_) (fun j => ?_)
        · rw [show (fun j : Fin n => (2 * mid j) / 2) = mid from funext fun j => by ring] at hmain
          calc holderNorm 1 α (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
                (polydisc c mid)
              = holderNorm 1 α (fun z => bmPot (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
                (polydisc c mid) := by
                rw [show (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
                    = (fun z => bmPot (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) from
                  funext fun z => bmPotential_eq_bmPot _ z]
            _ ≤ ENNReal.ofReal Cpot
                * ∑ j, holderNorm 0 α (fun z => (iteratedFDeriv ℝ k (g j) z) v) Set.univ := hmain
            _ ≤ ENNReal.ofReal Cpot * ∑ j, ENNReal.ofReal (∏ i, ‖v i‖)
                  * holderNorm k α (g j) Set.univ := by
                refine mul_le_mul_right ?_ _
                exact Finset.sum_le_sum fun j _ =>
                  holderNorm_zero_iteratedFDeriv_apply_le (m := k) le_rfl v
            _ = ENNReal.ofReal Cpot * (ENNReal.ofReal (∏ i, ‖v i‖)
                  * ∑ j, holderNorm k α (g j) Set.univ) := by
                rw [← Finset.mul_sum]
            _ ≤ ENNReal.ofReal Cpot * (ENNReal.ofReal (∏ i, ‖v i‖)
                  * (ENNReal.ofReal Cg * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
                    + holderNorm k α u (polydisc c ρo)))) := by
                refine mul_le_mul_right ?_ (ENNReal.ofReal Cpot)
                exact mul_le_mul_right hSg_bound (ENNReal.ofReal (∏ i, ‖v i‖))
            _ = ENNReal.ofReal (Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su))) := by
                rw [hST_eq, ← ENNReal.ofReal_mul hCgpos.le,
                  ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ∏ i, ‖v i‖),
                  ← ENNReal.ofReal_mul hCpotpos.le]
                congr 1
                ring
        · refine hgv_van j z ?_ v
          obtain ⟨i, hi⟩ := hz
          exact ⟨i, lt_of_lt_of_le (hBmid i) (by
            rw [show (2 * mid i) / 2 = mid i from by ring] at hi; exact hi)⟩
        · refine ne_of_lt (lt_of_le_of_lt (holderNorm_zero_iteratedFDeriv_apply_le (m := k)
            le_rfl v) ?_)
          refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Finset.single_le_sum
            (f := fun i => holderNorm k α (g i) Set.univ) (fun i _ => bot_le)
            (Finset.mem_univ j)) (by positivity)) ?_
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSg_lt
      /- ### bounds for the slices of the potential -/
      have hslice_w_bound : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y‖
            ≤ (‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))) * (∏ i, ‖v i‖) := by
        intro v y hy
        have hc0 : 0 ≤ Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su)) := by positivity
        have hmidmem : y ∈ polydisc c mid := fun i => lt_trans (hy i) (hρimid i)
        have hb1 : ‖fderiv ℝ (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
            y‖ ≤ Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su)) := by
          refine (ENNReal.ofReal_le_ofReal_iff hc0).mp ?_
          calc ENNReal.ofReal ‖fderiv ℝ
                (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y‖
              = ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1
                  (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
                  (polydisc c mid) y‖ := by
                rw [← fderivWithin_of_isOpen (isOpen_polydisc c mid) hmidmem,
                  ← norm_iteratedFDerivWithin_one _
                    ((isOpen_polydisc c mid).uniqueDiffWithinAt hmidmem)]
            _ ≤ iterDerivNorm 1
                  (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
                  (polydisc c mid) := le_iterDerivNorm 1 _ _ hmidmem
            _ ≤ holderNorm 1 α
                  (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z)
                  (polydisc c mid) := iterDerivNorm_le_holderNorm 1 α _ _ le_rfl
            _ ≤ ENNReal.ofReal (Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su))) := hC1a v
            _ = ENNReal.ofReal (Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su))) := rfl
        have hfe : fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y
            = (γ⁻¹ : ℂ) • fderiv ℝ
                (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y := by
          rw [hslice_w_eq v]
          exact fderiv_const_mul (hpot_diff v y hy) (γ⁻¹)
        rw [hfe, norm_smul]
        calc ‖(γ⁻¹ : ℂ)‖ * ‖fderiv ℝ
              (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y‖
            ≤ ‖(γ⁻¹ : ℂ)‖ * (Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su))) :=
              mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
          _ = (‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))) * (∏ i, ‖v i‖) := by ring
      have hslice_w_holder : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          ∀ z ∈ polydisc c ρi,
          ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y
            - fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) z‖
          ≤ (‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))) * (∏ i, ‖v i‖) * ‖y - z‖ ^ α := by
        intro v y hy z hz
        have hc0 : 0 ≤ Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su)) := by positivity
        have hymid : y ∈ polydisc c mid := fun i => lt_trans (hy i) (hρimid i)
        have hzmid : z ∈ polydisc c mid := fun i => lt_trans (hz i) (hρimid i)
        have hb := (holderNorm_one_bounds (isOpen_polydisc c mid) hc0 (hC1a v)).2.2.2 y hymid z hzmid
        have hfe : ∀ y' ∈ polydisc c ρi, fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y'
            = (γ⁻¹ : ℂ) • fderiv ℝ
                (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y' := by
          intro y' hy'
          rw [hslice_w_eq v]
          exact fderiv_const_mul (hpot_diff v y' hy') (γ⁻¹)
        have hfe' : fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y
              - fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) z
            = (γ⁻¹ : ℂ) • (fderiv ℝ
                (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y
              - fderiv ℝ
                (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) z) := by
          rw [hfe y hy, hfe z hz, smul_sub]
        rw [hfe', norm_smul]
        calc ‖(γ⁻¹ : ℂ)‖ * ‖fderiv ℝ
              (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) y
              - fderiv ℝ (fun z => bmPotential (fun j z => (iteratedFDeriv ℝ k (g j) z) v) z) z‖
            ≤ ‖(γ⁻¹ : ℂ)‖ * ((Cpot * (∏ i, ‖v i‖) * (Cg * (sf + su))) * ‖y - z‖ ^ α) :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = (‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))) * (∏ i, ‖v i‖) * ‖y - z‖ ^ α := by ring
      /- ### the total constant and the top-order estimate -/
      have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
      have hKtot_le : Chol * Bh + ‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))
          ≤ Ctot * (sf + su) := by
        have h1 : 0 ≤ sf + su := by linarith
        rw [hBh, hCtot]
        nlinarith [hsf0, hsu0, hCgpos, hCholpos, hCbmApos, hCpotpos, norm_nonneg (γ⁻¹ : ℂ)]
      have hKtot0 : 0 ≤ Ctot * (sf + su) := mul_nonneg hCtot0 (by linarith)
      have hslice_diff : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          DifferentiableAt ℝ (fun z => (iteratedFDeriv ℝ k u z) v) y := by
        intro v y hy
        have hev : (fun z => (iteratedFDeriv ℝ k u z) v) =ᶠ[𝓝 y]
            (fun z => (iteratedFDeriv ℝ k h z) v + (iteratedFDeriv ℝ k ww z) v) :=
          Filter.eventually_of_mem ((isOpen_polydisc c ρi).mem_nhds hy) fun z hz =>
            hslice_u v z hz
        exact ((hslice_h_diff v y hy).add (hslice_w_diff v y hy)).congr_of_eventuallyEq hev
      have hslice_bound : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k u z) v) y‖
            ≤ (Ctot * (sf + su)) * (∏ i, ‖v i‖) := by
        intro v y hy
        have hev : (fun z => (iteratedFDeriv ℝ k u z) v) =ᶠ[𝓝 y]
            (fun z => (iteratedFDeriv ℝ k h z) v + (iteratedFDeriv ℝ k ww z) v) :=
          Filter.eventually_of_mem ((isOpen_polydisc c ρi).mem_nhds hy) fun z hz =>
            hslice_u v z hz
        rw [hev.fderiv_eq]
        rw [show (fun z => (iteratedFDeriv ℝ k h z) v + (iteratedFDeriv ℝ k ww z) v)
            = (fun z => (iteratedFDeriv ℝ k h z) v) + (fun z => (iteratedFDeriv ℝ k ww z) v)
            from rfl]
        rw [fderiv_add (hslice_h_diff v y hy) (hslice_w_diff v y hy)]
        calc ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y
              + fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y‖
            ≤ ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y‖
              + ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y‖ := norm_add_le _ _
          _ ≤ (Chol * Bh) * (∏ i, ‖v i‖)
              + (‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))) * (∏ i, ‖v i‖) :=
              add_le_add (slice_fderiv_bound (f := h) (v := v) (z := y) (K := Chol * Bh)
                (by positivity) (hh_diff k le_rfl y hy) (hDh y hy)) (hslice_w_bound v y hy)
          _ ≤ (Ctot * (sf + su)) * (∏ i, ‖v i‖) := by
              rw [← add_mul]
              exact mul_le_mul_of_nonneg_right hKtot_le (by positivity : (0:ℝ) ≤ ∏ i, ‖v i‖)
      have hslice_holder : ∀ v : Fin k → (Fin n → ℂ), ∀ y ∈ polydisc c ρi,
          ∀ z ∈ polydisc c ρi,
          ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k u z) v) y
            - fderiv ℝ (fun z => (iteratedFDeriv ℝ k u z) v) z‖
            ≤ (Ctot * (sf + su)) * (∏ i, ‖v i‖) * ‖y - z‖ ^ α := by
        intro v y hy z hz
        have hev : (fun z => (iteratedFDeriv ℝ k u z) v) =ᶠ[𝓝 y]
            (fun z => (iteratedFDeriv ℝ k h z) v + (iteratedFDeriv ℝ k ww z) v) :=
          Filter.eventually_of_mem ((isOpen_polydisc c ρi).mem_nhds hy) fun w hw =>
            hslice_u v w hw
        have hev' : (fun z => (iteratedFDeriv ℝ k u z) v) =ᶠ[𝓝 z]
            (fun w => (iteratedFDeriv ℝ k h w) v + (iteratedFDeriv ℝ k ww w) v) :=
          Filter.eventually_of_mem ((isOpen_polydisc c ρi).mem_nhds hz) fun w hw =>
            hslice_u v w hw
        rw [hev.fderiv_eq, hev'.fderiv_eq]
        rw [show (fun w => (iteratedFDeriv ℝ k h w) v + (iteratedFDeriv ℝ k ww w) v)
            = (fun w => (iteratedFDeriv ℝ k h w) v) + (fun w => (iteratedFDeriv ℝ k ww w) v)
            from rfl,
          fderiv_add (hslice_h_diff v y hy) (hslice_w_diff v y hy),
          fderiv_add (hslice_h_diff v z hz) (hslice_w_diff v z hz)]
        have hsub : (fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y
              + fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y)
            - (fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) z
              + fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) z)
            = (fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y
                - fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) z)
              + (fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y
                - fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) z) := by abel
        rw [hsub]
        calc ‖(fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y
                - fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) z)
              + (fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y
                - fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) z)‖
            ≤ ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) y
                - fderiv ℝ (fun z => (iteratedFDeriv ℝ k h z) v) z‖
              + ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) y
                - fderiv ℝ (fun z => (iteratedFDeriv ℝ k ww z) v) z‖ := norm_add_le _ _
          _ ≤ (Chol * Bh) * (∏ i, ‖v i‖) * ‖y - z‖ ^ α
              + (‖(γ⁻¹ : ℂ)‖ * (Cpot * (Cg * (sf + su)))) * (∏ i, ‖v i‖) * ‖y - z‖ ^ α :=
              add_le_add (slice_fderiv_sub_bound (f := h) (v := v) (z := y) (z' := z)
                (K := Chol * Bh) (by positivity) (hh_diff k le_rfl y hy) (hh_diff k le_rfl z hz)
                (hDh_holder y hy z hz)) (hslice_w_holder v y hy z hz)
          _ ≤ (Ctot * (sf + su)) * (∏ i, ‖v i‖) * ‖y - z‖ ^ α := by
              rw [← add_mul, ← add_mul]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKtot_le
                (by positivity : (0:ℝ) ≤ ∏ i, ‖v i‖))
                (Real.rpow_nonneg (norm_nonneg _) α)
      have hslice := iteratedFDeriv_succ_of_slice_bounds (F := u) (k := k) (Ω := polydisc c ρi)
        (isOpen_polydisc c ρi) (Work.NN.Core.convex_polydisc c ρi) (α := α)
        (K := Ctot * (sf + su)) hα hKtot0 hslice_diff hslice_bound hslice_holder
      /- ### the top order bounds -/
      have hu_top1 : iterDerivNorm (k + 1) u (polydisc c ρi)
          ≤ ENNReal.ofReal (Ctot * (sf + su)) := by
        rw [iterDerivNorm]
        refine iSup₂_le fun y hy => ?_
        rw [iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_polydisc c ρi) hy]
        exact ENNReal.ofReal_le_ofReal
          (ContinuousMultilinearMap.opNorm_le_bound hKtot0 (fun w => hslice.1 y hy w))
      have hu_top2 : holderSeminorm (k + 1) α u (polydisc c ρi)
          ≤ ENNReal.ofReal (Ctot * (sf + su)) := by
        rw [holderSeminorm]
        refine iSup₂_le fun y hy => iSup₂_le fun z hz => iSup_le fun hyz => ?_
        rw [iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_polydisc c ρi) hy,
          iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_polydisc c ρi) hz]
        have hpos : 0 < ‖y - z‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) α
        calc ENNReal.ofReal (‖iteratedFDeriv ℝ (k + 1) u y - iteratedFDeriv ℝ (k + 1) u z‖
              / ‖y - z‖ ^ α)
            ≤ ENNReal.ofReal (((Ctot * (sf + su)) * ‖y - z‖ ^ α) / ‖y - z‖ ^ α) :=
              ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hslice.2 y hy z hz) hpos.le)
          _ = ENNReal.ofReal (Ctot * (sf + su)) := by
              rw [mul_div_cancel_right₀ _ (ne_of_gt hpos)]
      have hlow : holderNorm k α u (polydisc c ρi) ≤ ENNReal.ofReal su := by
        calc holderNorm k α u (polydisc c ρi) ≤ holderNorm k α u (polydisc c ρo) :=
              holderNorm_mono_set (isOpen_polydisc c ρo) (isOpen_polydisc c ρi)
                (polydisc_mono (fun i => (hlt i).le)) k α u
          _ = ENNReal.ofReal su := hsu_eq
      /- ### conclusion -/
      have hstep : ENNReal.ofReal su
            + (ENNReal.ofReal (Ctot * (sf + su)) + ENNReal.ofReal (Ctot * (sf + su)))
          ≤ ENNReal.ofReal (1 + 2 * Ctot) * (ENNReal.ofReal sf + ENNReal.ofReal su) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add hsu0 (by positivity),
          ← ENNReal.ofReal_add hsf0 hsu0, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hsf0, hsu0, hCtot0]
      rw [Work.CR.Flat.Cauchy.holderNorm_succ, hsf_eq, hsu_eq]
      calc holderNorm k α u (polydisc c ρi)
            + (iterDerivNorm (k + 1) u (polydisc c ρi)
              + holderSeminorm (k + 1) α u (polydisc c ρi))
          ≤ ENNReal.ofReal su + (ENNReal.ofReal (Ctot * (sf + su))
              + ENNReal.ofReal (Ctot * (sf + su))) :=
            add_le_add hlow (add_le_add hu_top1 hu_top2)
        _ ≤ ENNReal.ofReal (1 + 2 * Ctot) * (ENNReal.ofReal sf + ENNReal.ofReal su) := hstep
  · -- ##### degenerate case: the target polydisc is empty
    refine ⟨1, one_pos, ?_⟩
    intro u f hu hf hfcl heq
    obtain ⟨j₀, hj₀⟩ := not_forall.mp hpos
    have hempty : polydisc c ρi = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false, mem_polydisc]
      intro h
      have h1 : ‖z j₀ - c j₀‖ < ρi j₀ := h j₀
      exact absurd h1 (not_lt.mpr (le_trans (not_lt.mp hj₀) (norm_nonneg _)))
    have hzero : holderNorm (k + 1) α u (polydisc c ρi) = 0 := by
      rw [hempty]
      simp [holderNorm, iterDerivNorm, holderSeminorm]
    rw [hzero]
    exact bot_le
end Work.NN.Core

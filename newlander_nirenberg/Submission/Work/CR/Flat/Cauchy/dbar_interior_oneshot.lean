import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.polydiscCutoff
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.isClosedForm_dbarCoord_cutoff
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_Ck_smooth
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic_open

set_option maxHeartbeats 4000000

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open Set MeasureTheory




/-! ## The one-step interior Schauder estimate for the flat `∂̄`-operator

The proof follows the standard localisation/`∂̄`-solving argument.  Choose concentric
polydiscs with multiradii `ρi < A < B < mid < ρo` (with `M := max ρi 0 < A`), fix a cutoff
`η` with `η = 1` on the closed polydisc of radius `A` and `η = 0` outside the polydisc of
radius `B`, and put `g := ∂̄ (η u)`.  Since `η ≡ 1` on `polydisc c A` the form `g` agrees with
`f` there and is closed; moreover `g` is supported in the polydisc of radius `B ⊂ mid`, so the
compactly supported solver `exists_dbar_solution_polydisc_Ck_smooth` (applied with radius
`2ρo`, whose half is `ρo`) produces `w` with `∂̄w = g` on `polydisc c ρo` and

  `‖w‖_{C^{k+1,α}(polydisc c ρo)} ≤ C · Σ_j ‖g_j‖_{C^{k,α}(univ)} ≤ C · Σ_j ‖g_j‖_{C^{k,α}(polydisc c ρo)}`.

On `polydisc c A` the function `h := u - w` is holomorphic (`∂̄u = f = g = ∂̄(ηu)`), so the
local Cauchy estimate for holomorphic functions bounds `‖h‖_{C^{k+1,α}(polydisc c ρi)}` by
`sup_{polydisc c A} ‖h‖`, which is in turn controlled by `sup_{polydisc c A} ‖u‖ + sup ‖w‖`.
Finally `g_j = η f_j + u ∂̄_j η` is estimated by the Leibniz rule
(`holderNorm_mul_le_of_hasCompactSupport`, applied to the compactly supported factors `η` and
`∂̄_j η`), giving `Σ_j ‖g_j‖_{C^{k,α}(polydisc c ρo)} ≲ Σ_j ‖f_j‖_{C^{k,α}(polydisc c ρo)} + ‖u‖_{C^{k,α}(polydisc c ρo)}`.
Adding `u = h + w` and absorbing the constants yields the claim. -/


/-- `∂̄` is additive in the function, at differentiability points. -/
private lemma dbarCoord_sub {n : ℕ} (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun w => u w - v w) z = dbarCoord j u z - dbarCoord j v z := by
  have hfd : fderiv ℝ (fun w => u w - v w) z = fderiv ℝ u z - fderiv ℝ v z := by
    rw [show (fun w => u w - v w) = u - v from rfl, fderiv_sub hu hv]
  simp only [dbarCoord, hfd, sub_apply]
  ring

/-- If `η` vanishes outside the open polydisc of multiradius `r₁` and `r₁ < ρo` pointwise, then
`∂̄_j η` vanishes at every point outside the open polydisc of multiradius `ρo`. -/
private lemma dbarCoord_zero_of_supp {n : ℕ} {c : Fin n → ℂ} {r₁ ρo : Fin n → ℝ}
    (h : ∀ j, r₁ j < ρo j) {η : (Fin n → ℂ) → ℂ}
    (hη : ∀ z, (∃ j, r₁ j ≤ ‖z j - c j‖) → η z = 0) (j : Fin n) :
    ∀ z, (∃ i, ρo i ≤ ‖z i - c i‖) → dbarCoord j η z = 0 := by
  intro z hz
  obtain ⟨i, hi⟩ := hz
  have hlt : 0 < ρo i - r₁ i := by linarith [h i]
  have hev : η =ᶠ[nhds z] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds z hlt] with y hy
    have hyi : r₁ i ≤ ‖y i - c i‖ := by
      have h1 : ‖y i - z i‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) i
      have h2 : ‖z i - c i‖ ≤ ‖y i - c i‖ + ‖z i - y i‖ := by
        have := norm_add_le (y i - c i) (z i - y i)
        rw [show y i - c i + (z i - y i) = z i - c i from by ring] at this
        exact this
      have h3 : ‖z i - y i‖ = ‖y i - z i‖ := norm_sub_rev _ _
      have h4 : ‖y - z‖ < ρo i - r₁ i := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      linarith [hi]
    exact hη y ⟨i, hyi⟩
  have hfd : fderiv ℝ η z = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp [dbarCoord, hfd]

/-- If `η` vanishes outside the open polydisc of multiradius `r₁` and `r₁ < ρo` pointwise, then
`∂̄_j (η · u)` vanishes at every point outside the open polydisc of multiradius `ρo`. -/
private lemma dbarCoord_mul_zero_of_supp {n : ℕ} {c : Fin n → ℂ} {r₁ ρo : Fin n → ℝ}
    (h : ∀ j, r₁ j < ρo j) {η : (Fin n → ℂ) → ℂ}
    (hη : ∀ z, (∃ j, r₁ j ≤ ‖z j - c j‖) → η z = 0) (u : (Fin n → ℂ) → ℂ) (j : Fin n) :
    ∀ z, (∃ i, ρo i ≤ ‖z i - c i‖) → dbarCoord j (fun y => η y * u y) z = 0 := by
  intro z hz
  obtain ⟨i, hi⟩ := hz
  have hlt : 0 < ρo i - r₁ i := by linarith [h i]
  have hev : (fun y => η y * u y) =ᶠ[nhds z] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds z hlt] with y hy
    have hyi : r₁ i ≤ ‖y i - c i‖ := by
      have h1 : ‖y i - z i‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) i
      have h2 : ‖z i - c i‖ ≤ ‖y i - c i‖ + ‖z i - y i‖ := by
        have := norm_add_le (y i - c i) (z i - y i)
        rw [show y i - c i + (z i - y i) = z i - c i from by ring] at this
        exact this
      have h3 : ‖z i - y i‖ = ‖y i - z i‖ := norm_sub_rev _ _
      have h4 : ‖y - z‖ < ρo i - r₁ i := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      linarith [hi]
    rw [hη y ⟨i, hyi⟩, zero_mul]
  have hfd : fderiv ℝ (fun y => η y * u y) z = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp [dbarCoord, hfd]

/-! The sup form of the local Cauchy estimate for holomorphic functions (order `k+1`). -/
private lemma holderNorm_le_sup_of_holomorphic_open' {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ℕ∞) h (polydisc c ρo) →
      (∀ j, ∀ z ∈ polydisc c ρo, dbarCoord j h z = 0) →
      holderNorm (k+1) α h (polydisc c ρi)
        ≤ ENNReal.ofReal C * (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖) := by
  obtain ⟨C, hCpos, hC⟩ :=
    holderNorm_le_sup_of_holomorphic_bound hn (c := c) (ρi := ρi) (ρo := ρo) hmono hα hα1 k
  refine ⟨C, hCpos, ?_⟩
  intro h hsmooth hhol
  set S : ℝ≥0∞ := ⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖ with hS
  rcases eq_or_ne S ⊤ with htop | hne
  · have hne0 : ENNReal.ofReal C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hCpos)
    rw [htop, ENNReal.mul_top hne0]
    exact le_top
  · have hfin : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hne).symm
    have hbound : ∀ z ∈ polydisc c ρo, ‖h z‖ ≤ S.toReal := by
      intro z hz
      have h1 : ENNReal.ofReal ‖h z‖ ≤ S := le_iSup₂_of_le z hz le_rfl
      rw [hfin] at h1
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
    calc holderNorm (k+1) α h (polydisc c ρi)
        ≤ ENNReal.ofReal (C * S.toReal) :=
          hC h S.toReal ENNReal.toReal_nonneg hsmooth hhol hbound
      _ = ENNReal.ofReal C * S := by rw [ENNReal.ofReal_mul hCpos.le, ← hfin]

/-- **The one-step interior Schauder estimate for the flat `∂̄`-operator on a polydisc.** -/
theorem dbar_interior_oneshot {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hlt : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) → Work.CR.Flat.IsClosedForm f →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) → Work.CR.Flat.dbarCoord j u z = f j z) →
      Work.CR.Flat.holderNorm (k + 1) α u (Work.CR.Flat.polydisc c ρi)
        ≤ ENNReal.ofReal C *
            ((∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc c ρo))
              + Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc c ρo)) := by
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hα1' : α ≤ 1 := le_of_lt hα1
  -- ### intermediate radii: `ρi < A < B < ρo` with `0 < A`
  set M : Fin n → ℝ := fun j => max (ρi j) 0 with hM
  set A : Fin n → ℝ := fun j => M j + (ρo j - M j) / 3 with hA
  set B : Fin n → ℝ := fun j => M j + 2 * (ρo j - M j) / 3 with hB
  have hMlt : ∀ j, M j < ρo j := fun j => max_lt (hlt j) (hρo j)
  have hApos : ∀ j, 0 < A j := by
    intro j
    have h1 : 0 ≤ M j := le_max_right _ _
    have h2 : 0 < ρo j - M j := by linarith [hMlt j]
    simp only [hA]
    linarith
  have hρiA : ∀ j, ρi j < A j := by
    intro j
    have h1 : ρi j ≤ M j := le_max_left _ _
    have h2 : 0 < ρo j - M j := by linarith [hMlt j]
    simp only [hA]
    linarith
  have hAB : ∀ j, A j < B j := by
    intro j
    have h2 : 0 < ρo j - M j := by linarith [hMlt j]
    simp only [hA, hB]
    linarith
  have hAρo : ∀ j, A j < ρo j := by
    intro j
    have h1 : 0 ≤ M j := le_max_right _ _
    have h2 : 0 < ρo j - M j := by linarith [hMlt j]
    simp only [hA]
    linarith
  have hBρo : ∀ j, B j < ρo j := by
    intro j
    have h1 : 0 ≤ M j := le_max_right _ _
    have h2 : 0 < ρo j - M j := by linarith [hMlt j]
    simp only [hB]
    linarith
  set mid : Fin n → ℝ := fun j => (B j + ρo j) / 2 with hmid
  have hBmid : ∀ j, B j < mid j := by
    intro j
    have h2 := hBρo j
    simp only [hmid]
    linarith
  have hmidρo : ∀ j, mid j < ρo j := by
    intro j
    have h2 := hBρo j
    simp only [hmid]
    linarith
  -- ### the cutoff
  obtain ⟨η, hηsm, _hη01, hη1, hη0, hηcs, hηdsm, hηdcs⟩ :=
    polydiscCutoff (n := n) (c := c) (r₁ := A) (r₂ := B) k hApos hAB
  set etaC : (Fin n → ℂ) → ℂ := fun z => (η z : ℂ) with hetaC
  have hηsmCtop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etaC := by
    have h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (η z : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hηsm
    simpa only [hetaC] using h'
  have hηsmC : ContDiff ℝ (k + 1) etaC := hηsmCtop.of_le (by simp)
  have hηcsC : HasCompactSupport etaC := by simpa only [hetaC] using hηcs
  -- ### multiplication estimates
  obtain ⟨C1, hC1pos, hC1⟩ :=
    holderNorm_mul_le_of_hasCompactSupport (Ω := polydisc c ρo)
      (isOpen_polydisc c ρo).uniqueDiffOn hα0 hα1' hηsmC hηcsC
  have hC2ex : ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) f (polydisc c ρo) →
      holderNorm k α (fun z => dbarCoord j etaC z * f z) (polydisc c ρo)
        ≤ ENNReal.ofReal C * holderNorm k α f (polydisc c ρo) := fun j =>
    holderNorm_mul_le_of_hasCompactSupport (Ω := polydisc c ρo)
      (isOpen_polydisc c ρo).uniqueDiffOn hα0 hα1'
      ((by simpa only [hetaC] using hηdsm j : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => dbarCoord j etaC z)).of_le (by simp))
      (by simpa only [hetaC] using hηdcs j)
  choose C2 hC2pos hC2 using hC2ex
  set C2t : ℝ := (∑ j, C2 j) + 1 with hC2t
  have hC2t_pos : 0 < C2t := by
    have hle : (0 : ℝ) ≤ ∑ j, C2 j := Finset.sum_nonneg fun j _ => le_of_lt (hC2pos j)
    simp only [hC2t]
    linarith
  -- ### the two a priori constants
  obtain ⟨Chol, hCholpos, hChol⟩ :=
    holderNorm_le_sup_of_holomorphic_open' hn (c := c) (ρi := ρi) (ρo := A) hρiA hα0 hα1' k
  obtain ⟨Csol, hCsolpos, hCsol⟩ :=
    exists_dbar_solution_polydisc_Ck_smooth hn (c := c) (r := fun j => 2 * ρo j) hα hα1
      (fun j => by linarith [hρo j]) k
  set D : ℝ := max C1 C2t * ((n : ℝ) + 1) with hD
  have hDpos : 0 < D := by
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hD]
    exact mul_pos (lt_of_lt_of_le hC1pos (le_max_left _ _)) h2
  have hC1D : C1 ≤ D := by
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h3 : C1 ≤ max C1 C2t := le_max_left _ _
    have h4 : 0 ≤ max C1 C2t := le_of_lt (lt_of_lt_of_le hC1pos h3)
    simp only [hD]
    nlinarith
  have hC2tD : C2t * (n : ℝ) ≤ D := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : C2t ≤ max C1 C2t := le_max_right _ _
    have h4 : 0 ≤ max C1 C2t := le_of_lt (lt_of_lt_of_le hC2t_pos h3)
    simp only [hD]
    nlinarith
  refine ⟨Chol * (1 + Csol * D) + Csol * D, by positivity, ?_⟩
  intro u f hu hf hfcl heq
  -- ### the data `g = ∂̄(η u)`
  set g : Fin n → (Fin n → ℂ) → ℂ := fun j z => dbarCoord j (fun y => etaC y * u y) z with hg
  have hgdef : ∀ j z, g j z = dbarCoord j (fun y => etaC y * u y) z := fun j z => rfl
  have hgf : ∀ j, g j = fun z => dbarCoord j (fun y => etaC y * u y) z :=
    fun j => funext (hgdef j)
  have hηCzero : ∀ w, (∃ j, B j ≤ ‖w j - c j‖) → etaC w = 0 := by
    intro w hw
    obtain ⟨i, hi⟩ := hw
    simp only [hetaC, hη0 w ⟨i, hi⟩, Complex.ofReal_zero]
  have hηOzero : ∀ w, (∃ j, ρo j ≤ ‖w j - c j‖) → etaC w = 0 := by
    intro w hw
    obtain ⟨i, hi⟩ := hw
    exact hηCzero w ⟨i, le_trans (le_of_lt (hBρo i)) hi⟩
  have hdu : ∀ z, DifferentiableAt ℝ u z := fun z => (hu.differentiable (by simp)).differentiableAt
  have hGet : ∀ z, DifferentiableAt ℝ etaC z :=
    fun z => (hηsmC.differentiable (by simp)).differentiableAt
  have hg_eq : ∀ j, g j = fun z => etaC z * f j z + u z * dbarCoord j etaC z := by
    intro j
    funext z
    by_cases hz : z ∈ polydisc c ρo
    · rw [hgdef j z, Polydisc.dbarCoord_mul j etaC u z (hGet z) (hdu z), heq j z hz]
      ring
    · have hz' : ∃ i, ρo i ≤ ‖z i - c i‖ := by
        by_contra hcon
        exact hz fun j => lt_of_not_ge fun hj => hcon ⟨j, hj⟩
      rw [hgdef j z, dbarCoord_mul_zero_of_supp (η := etaC) (u := u) hBρo hηCzero j z hz']
      have hηz : etaC z = 0 := hηCzero z (by
        obtain ⟨i, hi⟩ := hz'
        exact ⟨i, le_trans (le_of_lt (hBρo i)) hi⟩)
      have hdz : dbarCoord j etaC z = 0 :=
        dbarCoord_zero_of_supp (η := etaC) hBρo hηCzero j z hz'
      rw [hηz, hdz, zero_mul, mul_zero, add_zero]
  have hg_sm : ∀ j, ContDiff ℝ (k + 1) (g j) := by
    intro j
    rw [hg_eq j]
    exact ((hηsmC.mul (hf j))).add
      (hu.mul ((by simpa only [hetaC] using hηdsm j : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => dbarCoord j etaC z)).of_le (by simp)))
  have hg_zeroMid : ∀ j z, (∃ i, mid i ≤ ‖z i - c i‖) → g j z = 0 := by
    intro j z hz
    rw [hgdef j z]
    exact dbarCoord_mul_zero_of_supp (η := etaC) (u := u) hBmid hηCzero j z hz
  have hg_zero : ∀ j z, (∃ i, ρo i ≤ ‖z i - c i‖) → g j z = 0 := by
    intro j z hz
    rw [hg_eq j]
    beta_reduce
    obtain ⟨i, hi⟩ := hz
    have hηz : etaC z = 0 := hηOzero z ⟨i, hi⟩
    have hdz : dbarCoord j etaC z = 0 :=
      dbarCoord_zero_of_supp (η := etaC) hBρo hηCzero j z ⟨i, hi⟩
    rw [hηz, hdz, zero_mul, mul_zero, add_zero]
  have hg_cl : IsClosedForm g := by
    have h : IsClosedForm (fun j => dbarCoord j (fun z => etaC z * u z)) :=
      isClosedForm_dbarCoord_cutoff (c := c) (ρo := ρo) (k := k) (u := u) (f := f) (η := etaC)
        hu hf (hηsmCtop.of_le (by simp)) hfcl heq hηOzero
    intro j k' z
    rw [hgf j, hgf k']
    exact h j k' z
  -- ### solve `∂̄w = g`
  obtain ⟨w, hw_sm, hw_solve, hw_bound⟩ := hCsol g hg_sm
    (fun j z hz => by
      obtain ⟨i, hi⟩ := hz
      exact hg_zero j z ⟨i, by linarith⟩) hg_cl
  have hpolj : ∀ j, 2 * ρo j / 2 = ρo j := fun j => by ring
  have hpol : polydisc c (fun j => 2 * ρo j / 2) = polydisc c ρo := by
    congr 1
    exact funext hpolj
  simp only [hpolj] at hw_solve
  rw [hpol] at hw_bound
  -- ### `h = u - w` is holomorphic on `P(A)`
  set h : (Fin n → ℂ) → ℂ := fun z => u z - w z with hh
  have hdw : ∀ z, DifferentiableAt ℝ w z :=
    fun z => (hw_sm.differentiable (by simp)).differentiableAt
  have hdeta_zero : ∀ j, ∀ z ∈ polydisc c A, dbarCoord j etaC z = 0 := by
    intro j z hz
    have hev : etaC =ᶠ[nhds z] (fun _ => 1) := by
      filter_upwards [(isOpen_polydisc c A).mem_nhds hz] with y hy
      simp only [hetaC, hη1 y (fun j => le_of_lt (hy j)), Complex.ofReal_one]
    have : fderiv ℝ etaC z = 0 := by
      rw [hev.fderiv_eq]
      simp
    simp [dbarCoord, this]
  have hhol : ∀ j, ∀ z ∈ polydisc c A, dbarCoord j h z = 0 := by
    intro j z hz
    have hzO : z ∈ polydisc c ρo := fun i => lt_trans (hz i) (hAρo i)
    have hg_at : g j z = f j z := by
      rw [hg_eq j]
      beta_reduce
      have hηz : etaC z = 1 := by
        simp only [hetaC, hη1 z (fun i => le_of_lt (hz i)), Complex.ofReal_one]
      rw [hηz, hdeta_zero j z hz]
      ring
    rw [hh, dbarCoord_sub j u w z (hdu z) (hdw z), heq j z hzO,
      hw_solve j z (by intro i; exact lt_trans (hz i) (hAρo i)), hg_at, sub_self]
  have hh_sm : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) h (polydisc c A) :=
    (hu.sub hw_sm).contDiffOn
  have hChol' := hChol h hh_sm hhol
  -- ### the bounds
  set Sf : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (polydisc c ρo) with hSf
  set Su : ℝ≥0∞ := holderNorm k α u (polydisc c ρo) with hSu
  set Sg : ℝ≥0∞ := ∑ j, holderNorm k α (g j) (polydisc c ρo) with hSg
  have hSuT : Su ≤ Sf + Su := le_add_left le_rfl
  have hSfT : Sf ≤ Sf + Su := le_add_right le_rfl
  -- per-`j` bound for the data
  have hgj_le : ∀ j, holderNorm k α (g j) (polydisc c ρo)
      ≤ ENNReal.ofReal C1 * holderNorm k α (f j) (polydisc c ρo) + ENNReal.ofReal C2t * Su := by
    intro j
    rw [hg_eq j, hSu]
    calc holderNorm k α (fun z => etaC z * f j z + u z * dbarCoord j etaC z) (polydisc c ρo)
        ≤ holderNorm k α (fun z => etaC z * f j z) (polydisc c ρo)
          + holderNorm k α (fun z => u z * dbarCoord j etaC z) (polydisc c ρo) :=
          Holder.holderNorm_add_le ((hηsmC.mul (hf j)).contDiffOn.of_le (by simp))
            ((hu.mul ((by simpa only [hetaC] using hηdsm j : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun z => dbarCoord j etaC z)).of_le (by simp))).contDiffOn.of_le (by simp))
            (isOpen_polydisc c ρo).uniqueDiffOn
      _ ≤ ENNReal.ofReal C1 * holderNorm k α (f j) (polydisc c ρo)
          + ENNReal.ofReal C2t * holderNorm k α u (polydisc c ρo) := by
          refine add_le_add (hC1 (f j) ((hf j).contDiffOn.of_le (by simp))) ?_
          rw [show (fun z => u z * dbarCoord j etaC z)
              = (fun z => dbarCoord j etaC z * u z) from funext fun z => by ring]
          exact (hC2 j u (hu.contDiffOn.of_le (by simp))).trans
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by
              have hle : C2 j ≤ ∑ i, C2 i :=
                Finset.single_le_sum (fun i _ => le_of_lt (hC2pos i)) (Finset.mem_univ j)
              simp only [hC2t]; linarith)) _)
  -- the sum bound
  have hSg_le : Sg ≤ ENNReal.ofReal D * (Sf + Su) := by
    rw [hSg, hSf]
    calc ∑ j, holderNorm k α (g j) (polydisc c ρo)
        ≤ ∑ j, (ENNReal.ofReal C1 * holderNorm k α (f j) (polydisc c ρo)
            + ENNReal.ofReal C2t * Su) := Finset.sum_le_sum fun j _ => hgj_le j
      _ = ENNReal.ofReal C1 * (∑ j, holderNorm k α (f j) (polydisc c ρo))
            + (n : ℝ≥0∞) * (ENNReal.ofReal C2t * Su) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal D * (∑ j, holderNorm k α (f j) (polydisc c ρo))
            + ENNReal.ofReal D * Su := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hC1D) _
          · rw [← mul_assoc]
            have h2 : (n : ℝ≥0∞) * ENNReal.ofReal C2t ≤ ENNReal.ofReal D := by
              rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
              exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hC2tD)
            exact mul_le_mul_left h2 Su
      _ = ENNReal.ofReal D * ((∑ j, holderNorm k α (f j) (polydisc c ρo)) + Su) := by
          rw [mul_add]
  -- the solution bound
  have hw_le : holderNorm (k + 1) α w (polydisc c ρo) ≤ ENNReal.ofReal (Csol * D) * (Sf + Su) := by
    calc holderNorm (k + 1) α w (polydisc c ρo)
        ≤ ENNReal.ofReal Csol * ∑ j, holderNorm k α (g j) Set.univ := hw_bound
      _ ≤ ENNReal.ofReal Csol * Sg := by
          refine mul_le_mul_right ?_ _
          rw [hSg]
          refine Finset.sum_le_sum fun j _ => ?_
          exact holderNorm_univ_le_holderNorm_polydisc_of_vanishing (c := c) (r := mid)
            (r' := ρo) hmidρo hα0 (fun z hz => hg_zeroMid j z hz)
      _ ≤ ENNReal.ofReal Csol * (ENNReal.ofReal D * (Sf + Su)) :=
          mul_le_mul_right hSg_le _
      _ = ENNReal.ofReal (Csol * D) * (Sf + Su) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCsolpos)]
  -- the sup bound
  have hsup_le : (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖h z‖)
      ≤ ENNReal.ofReal (1 + Csol * D) * (Sf + Su) := by
    have h1 : (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖h z‖)
        ≤ (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖u z‖) + (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖w z‖) := by
      refine iSup₂_le fun z hz => ?_
      have hzO : z ∈ polydisc c ρo := fun i => lt_trans (hz i) (hAρo i)
      calc ENNReal.ofReal ‖h z‖ = ENNReal.ofReal ‖u z - w z‖ := by rw [hh]
        _ ≤ ENNReal.ofReal (‖u z‖ + ‖w z‖) := ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
        _ = ENNReal.ofReal ‖u z‖ + ENNReal.ofReal ‖w z‖ :=
            ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
        _ ≤ _ := add_le_add (le_iSup₂_of_le z hz le_rfl) (le_iSup₂_of_le z hz le_rfl)
    have h2 : (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖u z‖)
          + (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖w z‖)
        ≤ Su + ENNReal.ofReal (Csol * D) * (Sf + Su) := by
      refine add_le_add ?_ ?_
      · have hmono : (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖u z‖)
            ≤ ⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖u z‖ := by
          refine iSup₂_le fun z hz => le_iSup₂_of_le z (fun i => lt_trans (hz i) (hAρo i)) le_rfl
        refine hmono.trans ?_
        rw [hSu, ← iterDerivNorm_zero]
        exact iterDerivNorm_le_holderNorm k α u (polydisc c ρo) (Nat.zero_le k)
      · have hmono : (⨆ z ∈ polydisc c A, ENNReal.ofReal ‖w z‖)
            ≤ ⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖w z‖ := by
          refine iSup₂_le fun z hz => le_iSup₂_of_le z (fun i => lt_trans (hz i) (hAρo i)) le_rfl
        refine hmono.trans ?_
        rw [← iterDerivNorm_zero]
        exact (iterDerivNorm_le_holderNorm k α w (polydisc c ρo) (Nat.zero_le k)).trans
          ((holderNorm_mono_k (Nat.le_succ k) α w _).trans hw_le)
    refine (h1.trans h2).trans ?_
    calc Su + ENNReal.ofReal (Csol * D) * (Sf + Su)
        ≤ (Sf + Su) + ENNReal.ofReal (Csol * D) * (Sf + Su) :=
          add_le_add (le_add_left le_rfl) le_rfl
      _ = (1 + ENNReal.ofReal (Csol * D)) * (Sf + Su) := by rw [add_mul, one_mul]
      _ = ENNReal.ofReal (1 + Csol * D) * (Sf + Su) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
  -- ### assemble
  have hmain : holderNorm (k + 1) α u (polydisc c ρi)
      ≤ ENNReal.ofReal Chol * (ENNReal.ofReal (1 + Csol * D) * (Sf + Su))
        + ENNReal.ofReal (Csol * D) * (Sf + Su) := by
    calc holderNorm (k + 1) α u (polydisc c ρi)
        = holderNorm (k + 1) α (fun z => (u z - w z) + w z) (polydisc c ρi) := by
          rw [show (fun z => (u z - w z) + w z) = u from funext fun z => by ring]
      _ ≤ holderNorm (k + 1) α h (polydisc c ρi) + holderNorm (k + 1) α w (polydisc c ρi) :=
          Holder.holderNorm_add_le ((hu.sub hw_sm).contDiffOn) (hw_sm.contDiffOn)
            (isOpen_polydisc c ρi).uniqueDiffOn
      _ ≤ ENNReal.ofReal Chol * (ENNReal.ofReal (1 + Csol * D) * (Sf + Su))
            + ENNReal.ofReal (Csol * D) * (Sf + Su) := by
          refine add_le_add (hChol'.trans (mul_le_mul_right hsup_le _)) ?_
          exact (holderNorm_mono_set (isOpen_polydisc c ρo) (isOpen_polydisc c ρi)
            (fun z hz i => lt_trans (hz i) (hlt i)) (k + 1) α w).trans hw_le
  refine hmain.trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCholpos), ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity), hSf, hSu]


end Work.CR.Flat.Cauchy

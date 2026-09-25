/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Setup for the Beltrami fixed-point lemma
-/
import Mathlib
import Submission.Work.NN.Core.beltrami_theta_aux
import Submission.Work.NN.Core.beltrami_theta_est
import Submission.Work.NN.Core.bmPot_diff_continuous
import Submission.Work.NN.Core.bmPotential_differentiableAt_holder
import Submission.Work.NN.Final.bmPot_linear
import Submission.Work.CR.Flat.Cauchy.bmPotential_dCoord_holderNorm_le

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

namespace BTheta

variable {n : ℕ}

/-! ## The family norm `Σ_j ‖H j‖_{C^{0,α}}` -/

/-- The `C^{0,α}`-norm of a family of functions. -/
noncomputable def famNorm (α : ℝ) (H : Fin n → (Fin n → ℂ) → ℂ) : ℝ≥0∞ :=
  ∑ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ

@[simp] lemma famNorm_zero (α : ℝ) :
    famNorm α (0 : Fin n → (Fin n → ℂ) → ℂ) = 0 := by
  simp [famNorm]

lemma famNorm_neg {α : ℝ} (H : Fin n → (Fin n → ℂ) → ℂ) :
    famNorm α (-H) = famNorm α H :=
  Finset.sum_congr rfl fun j _ => holderNorm_zero_neg (H j) Set.univ

lemma famNorm_add_le {α : ℝ} (H H' : Fin n → (Fin n → ℂ) → ℂ) :
    famNorm α (H + H') ≤ famNorm α H + famNorm α H' := by
  rw [famNorm, famNorm, famNorm]
  exact (Finset.sum_le_sum fun j _ =>
    holderNorm_zero_add_le (H j) (H' j) Set.univ).trans (le_of_eq Finset.sum_add_distrib)

lemma famNorm_sub_le {α : ℝ} (H H' : Fin n → (Fin n → ℂ) → ℂ) :
    famNorm α (H - H') ≤ famNorm α H + famNorm α H' := by
  simpa only [sub_eq_add_neg] using (famNorm_add_le H (-H')).trans
    (add_le_add le_rfl (le_of_eq (famNorm_neg H')))

lemma famNorm_lt_top {α : ℝ} {H : Fin n → (Fin n → ℂ) → ℂ}
    (h : ∀ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ < ⊤) : famNorm α H < ⊤ := by
  rw [famNorm]
  exact ENNReal.sum_lt_top.mpr fun j _ => h j

lemma famNorm_ne_top {α : ℝ} {H : Fin n → (Fin n → ℂ) → ℂ}
    (h : ∀ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ < ⊤) : famNorm α H ≠ ⊤ :=
  ne_of_lt (famNorm_lt_top h)

lemma famNorm_apply_le {α : ℝ} (H : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n) :
    Work.CR.Flat.holderNorm 0 α (H j) Set.univ ≤ famNorm α H :=
  Finset.single_le_sum (f := fun i => Work.CR.Flat.holderNorm 0 α (H i) Set.univ)
    (fun i _ => zero_le) (Finset.mem_univ j)

lemma famNorm_eq_ofReal_toReal {α : ℝ} {H : Fin n → (Fin n → ℂ) → ℂ}
    (h : famNorm α H < ⊤) : famNorm α H = ENNReal.ofReal (famNorm α H).toReal :=
  (ENNReal.ofReal_toReal (ne_of_lt h)).symm

/-! ## Compact support from vanishing off a polydisc -/

lemma hasCompactSupport_of_vanishing_off_polydisc {ρ : Fin n → ℝ} (hn : 0 < n)
    (hρ : ∀ j, 0 < ρ j) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ z, z ∉ Work.CR.Flat.polydisc 0 ρ → f z = 0) : HasCompactSupport f := by
  have hsumpos : 0 < ∑ j, ρ j :=
    Finset.sum_pos (fun j _ => hρ j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set R : ℝ := ∑ j, ρ j + 1 with hRdef
  refine (isCompact_closedBall (0 : Fin n → ℂ) R).of_isClosed_subset (isClosed_tsupport f) ?_
  rw [tsupport]
  refine closure_minimal (fun z hz => ?_) (Metric.isClosed_closedBall)
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  have hlt : ∑ j, ρ j < ‖z‖ := by
    rw [hRdef] at hcon
    linarith
  obtain ⟨k, hk⟩ := Work.CR.Flat.Cauchy.exists_coord_le_of_sum_le_norm hn hlt.le
  have hk' : ρ k ≤ ‖z k - (0 : Fin n → ℂ) k‖ := by simpa using hk
  exact hz (hf z fun hmem => absurd (hmem k) (not_lt.mpr hk'))

/-! ## Linearity of `bmPotential` -/

lemma bmPotential_sub_fun (hn : 0 < n) {H H' : Fin n → (Fin n → ℂ) → ℂ}
    (hHc : ∀ j, Continuous (H j)) (hHcs : ∀ j, HasCompactSupport (H j))
    (hH'c : ∀ j, Continuous (H' j)) (hH'cs : ∀ j, HasCompactSupport (H' j)) :
    Work.CR.Flat.Cauchy.bmPotential (H - H')
      = Work.CR.Flat.Cauchy.bmPotential H - Work.CR.Flat.Cauchy.bmPotential H' := by
  have hkey : ∀ z, Work.CR.Flat.Cauchy.bmPotential (H - H') z
      = Work.CR.Flat.Cauchy.bmPotential H z - Work.CR.Flat.Cauchy.bmPotential H' z := by
    intro z
    rw [bmPotential_eq_bmPot_fun (H - H'), bmPotential_eq_bmPot_fun H,
      bmPotential_eq_bmPot_fun H']
    have h := Work.NN.Final.bmPot_linear (n := n) hn (a := (1 : ℂ)) (b := (-1 : ℂ))
      (f := H) (g := H') hHc hH'c hHcs hH'cs z
    have hfun : (fun j => fun y => (1 : ℂ) * H j y + (-1 : ℂ) * H' j y) = (H - H') := by
      funext j y
      simp only [Pi.sub_apply, one_mul, neg_one_mul, sub_eq_add_neg]
    rw [hfun] at h
    simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using h
  exact funext hkey

/-! ## Calculus for the operator -/

/-- `∂_j` of a difference. -/
lemma dCoord_sub_local (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dCoord j (u - v) z = Work.CR.Flat.dCoord j u z - Work.CR.Flat.dCoord j v z := by
  have hfd : fderiv ℝ (u - v) z = fderiv ℝ u z - fderiv ℝ v z := fderiv_sub hu hv
  simp only [Work.CR.Flat.dCoord, hfd, sub_apply]
  ring

/-! ## The Beltrami operator -/

/-- The (nonlinear, but linear in the potential) map whose fixed point the Beltrami equation
asks for: `(Θ c H) j z = γ⁻¹ Σ_l c_{jl}(z) ∂_l (bmPotential H)(z)`. -/
noncomputable def beltramiTheta (c : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (H : Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  fun j z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
    ∑ l, c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z

lemma beltramiTheta_apply (c : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (H : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) :
    beltramiTheta c H j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
      ∑ l, c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z := rfl

/-- Component form: `Θ` is built from the one-variable coefficient row `l ↦ c j l`. -/
lemma beltramiTheta_eq_of_row (c : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (H : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n) :
    beltramiTheta c H j = fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
      ∑ l, (fun l => c j l) l z *
        Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z := rfl

/-- `Θ` vanishes on the zero family. -/
@[simp] lemma beltramiTheta_zero (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    beltramiTheta c (0 : Fin n → (Fin n → ℂ) → ℂ) = 0 := by
  have hzero : Work.CR.Flat.Cauchy.bmPotential (0 : Fin n → (Fin n → ℂ) → ℂ) = 0 := by
    funext w
    simp [Work.CR.Flat.Cauchy.bmPotential]
  funext j z
  simp only [beltramiTheta_apply, hzero, Pi.zero_apply]
  have hsum : (∑ x, c j x z * Work.CR.Flat.dCoord x (0 : (Fin n → ℂ) → ℂ) z) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    have hd : Work.CR.Flat.dCoord x (0 : (Fin n → ℂ) → ℂ) z = 0 := by
      simp [Work.CR.Flat.dCoord]
    rw [hd, mul_zero]
  rw [hsum, mul_zero]

/-- `Θ c H` vanishes wherever the coefficients do. -/
lemma beltramiTheta_vanishes {ρ : Fin n → ℝ} {c : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hcsupp : ∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    (H : Fin n → (Fin n → ℂ) → ℂ) :
    ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → beltramiTheta c H j z = 0 := by
  intro j z hz
  have hcz : ∀ l, c j l z = 0 := by
    intro l
    by_contra hc
    exact hz (hcsupp j l z hc)
  simp [beltramiTheta, hcz]

/-- **`Θ` is additive in the argument**: on the polydisc where the potentials are differentiable
(strictly larger than the support of the coefficients) it is the linear operator
`H ↦ γ⁻¹ c · ∂(bmPotential H)`. -/
lemma beltramiTheta_sub_apply {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j)
    {c : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hcsupp : ∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {H H' : Fin n → (Fin n → ℂ) → ℂ}
    (hHfin : ∀ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ < ⊤)
    (hHvan : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → H j z = 0)
    (hH'fin : ∀ j, Work.CR.Flat.holderNorm 0 α (H' j) Set.univ < ⊤)
    (hH'van : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → H' j z = 0)
    (j : Fin n) (z : Fin n → ℂ) :
    beltramiTheta c H j z - beltramiTheta c H' j z = beltramiTheta c (H - H') j z := by
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
  · -- on the polydisc `polydisc 0 τ` all three potentials are differentiable
    have hvanτ : ∀ {W : Fin n → (Fin n → ℂ) → ℂ}, (∀ j w, w ∉ Work.CR.Flat.polydisc 0 ρ → W j w = 0) →
        ∀ j w, w ∉ Work.CR.Flat.polydisc 0 τ → W j w = 0 := by
      intro W hW j w hw
      exact hW j w fun hmem => hw (Work.CR.Flat.polydisc_mono (fun i => (hρτ i).le) hmem)
    have hsubfin : ∀ j, Work.CR.Flat.holderNorm 0 α ((H - H') j) Set.univ < ⊤ := by
      intro j
      refine lt_of_le_of_lt (holderNorm_zero_sub_le (H j) (H' j) Set.univ) ?_
      exact ENNReal.add_lt_top.mpr ⟨hHfin j, hH'fin j⟩
    have hzτ : z ∈ Work.CR.Flat.polydisc 0 τ :=
      Work.CR.Flat.polydisc_mono (fun i => (hρτ i).le) hz
    have hdH := bmPot_diff_continuous (n := n) hn (c := (0 : Fin n → ℂ))
      (r := fun j => 2 * τ j) (α := α) hα0 hα1 (fun j => by linarith [hτ j])
      (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hHfin j))
      hHfin
      (fun j w hw => hvanτ hHvan j w fun hmem => by
        obtain ⟨i, hi⟩ := hw
        rw [show (2 * τ i) / 2 = τ i from by ring] at hi
        exact absurd (hmem i) (not_lt.mpr hi))
      z (by
        rw [show Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => (2 * τ j) / 2)
            = Work.CR.Flat.polydisc 0 τ from by congr 1; funext i; ring]
        exact hzτ)
    have hdH' := bmPot_diff_continuous (n := n) hn (c := (0 : Fin n → ℂ))
      (r := fun j => 2 * τ j) (α := α) hα0 hα1 (fun j => by linarith [hτ j])
      (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hH'fin j))
      hH'fin
      (fun j w hw => hvanτ hH'van j w fun hmem => by
        obtain ⟨i, hi⟩ := hw
        rw [show (2 * τ i) / 2 = τ i from by ring] at hi
        exact absurd (hmem i) (not_lt.mpr hi))
      z (by
        rw [show Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => (2 * τ j) / 2)
            = Work.CR.Flat.polydisc 0 τ from by congr 1; funext i; ring]
        exact hzτ)
    have hdsub := bmPot_diff_continuous (n := n) hn (c := (0 : Fin n → ℂ))
      (r := fun j => 2 * τ j) (α := α) hα0 hα1 (fun j => by linarith [hτ j])
      (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hsubfin j))
      hsubfin
      (fun j w hw => hvanτ (fun j w hw' => by
        have : (H - H') j w = H j w - H' j w := rfl
        rw [this, hHvan j w hw', hH'van j w hw', sub_zero]) j w fun hmem => by
        obtain ⟨i, hi⟩ := hw
        rw [show (2 * τ i) / 2 = τ i from by ring] at hi
        exact absurd (hmem i) (not_lt.mpr hi))
      z (by
        rw [show Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => (2 * τ j) / 2)
            = Work.CR.Flat.polydisc 0 τ from by congr 1; funext i; ring]
        exact hzτ)
    -- the potentials: `bmPotential (H - H') = bmPotential H - bmPotential H'`
    have hlin : Work.CR.Flat.Cauchy.bmPotential (H - H')
        = Work.CR.Flat.Cauchy.bmPotential H - Work.CR.Flat.Cauchy.bmPotential H' :=
      bmPotential_sub_fun hn (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hHfin j))
        (fun j => hasCompactSupport_of_vanishing_off_polydisc hn hρ (hHvan j))
        (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hH'fin j))
        (fun j => hasCompactSupport_of_vanishing_off_polydisc hn hρ (hH'van j))
    -- termwise: `∂_l (bmPotential (H - H')) z = ∂_l (bmPotential H) z - ∂_l (bmPotential H') z`
    have hdc : ∀ l, Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential (H - H')) z
        = Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H) z
          - Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential H') z := by
      intro l
      rw [hlin, dCoord_sub_local l _ _ z hdH hdH']
    simp only [beltramiTheta_apply, hdc]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  · have hcz : ∀ l, c j l z = 0 := by
      intro l
      by_contra hc
      exact hz (hcsupp j l z hc)
    simp [beltramiTheta, hcz]

lemma exists_radius_all_of_hasCompactSupport {G : Fin n → (Fin n → ℂ) → ℂ}
    (h : ∀ j, HasCompactSupport (G j)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j x, R ≤ ‖x‖ → G j x = 0 := by
  choose R hR0 hR using fun j => exists_radius_of_hasCompactSupport (h j)
  refine ⟨∑ j, R j, Finset.sum_nonneg fun j _ => hR0 j, fun j x hx => ?_⟩
  exact hR j x (le_trans (Finset.single_le_sum (f := fun i => R i)
    (fun i _ => hR0 i) (Finset.mem_univ j)) hx)

/-- The Bochner–Martinelli potential of a `C¹` compactly supported family is differentiable. -/
lemma differentiableAt_bmPotential_of_hasCompactSupport (hn : 0 < n)
    {G : Fin n → (Fin n → ℂ) → ℂ} (hG1 : ∀ j, ContDiff ℝ 1 (G j))
    (hGcs : ∀ j, HasCompactSupport (G j)) (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPotential G w) z := by
  obtain ⟨R, hR0, hR⟩ := exists_radius_all_of_hasCompactSupport hGcs
  have h := Work.CR.Flat.Cauchy.bmPotential_contDiff_one (n := n) hn
    (c := (0 : Fin n → ℂ)) (r := fun j => 2 * (R + 1)) (fun j => by linarith)
    hG1
    (fun j w hw => by
      obtain ⟨k, hk⟩ := hw
      rw [show (2 * (R + 1)) / 2 = R + 1 from by ring] at hk
      refine hR j w ?_
      calc R ≤ R + 1 := by linarith
        _ ≤ ‖w k‖ := by simpa using hk
        _ ≤ ‖w‖ := norm_le_pi_norm w k)
  exact (h.differentiable (by norm_num)).differentiableAt

/-- `∂_j` of a sum. -/
lemma dCoord_add_local (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dCoord j (u + v) z = Work.CR.Flat.dCoord j u z + Work.CR.Flat.dCoord j v z := by
  have hfd : fderiv ℝ (u + v) z = fderiv ℝ u z + fderiv ℝ v z := fderiv_add hu hv
  simp only [Work.CR.Flat.dCoord, hfd, add_apply]
  ring

/-- `bmPotential` is additive on continuous compactly supported data. -/
lemma bmPotential_add_fun (hn : 0 < n) {H H' : Fin n → (Fin n → ℂ) → ℂ}
    (hHc : ∀ j, Continuous (H j)) (hHcs : ∀ j, HasCompactSupport (H j))
    (hH'c : ∀ j, Continuous (H' j)) (hH'cs : ∀ j, HasCompactSupport (H' j)) :
    Work.CR.Flat.Cauchy.bmPotential (H + H')
      = Work.CR.Flat.Cauchy.bmPotential H + Work.CR.Flat.Cauchy.bmPotential H' := by
  have hkey : ∀ z, Work.CR.Flat.Cauchy.bmPotential (H + H') z
      = Work.CR.Flat.Cauchy.bmPotential H z + Work.CR.Flat.Cauchy.bmPotential H' z := by
    intro z
    rw [bmPotential_eq_bmPot_fun (H + H'), bmPotential_eq_bmPot_fun H,
      bmPotential_eq_bmPot_fun H']
    have h := Work.NN.Final.bmPot_linear (n := n) hn (a := (1 : ℂ)) (b := (1 : ℂ))
      (f := H) (g := H') hHc hH'c hHcs hH'cs z
    have hfun : (fun j => fun y => (1 : ℂ) * H j y + (1 : ℂ) * H' j y) = (H + H') := by
      funext j y
      simp only [Pi.add_apply, one_mul]
    rw [hfun] at h
    simpa only [one_mul] using h
  exact funext hkey

/-- **Additivity of `Θ` in its argument**, with the second function required to vanish off the
polydisc only (the first, `G`, may be any `C¹` compactly supported family). -/
lemma beltramiTheta_add_apply {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j)
    {c : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hcsupp : ∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {G Y : Fin n → (Fin n → ℂ) → ℂ}
    (hG1 : ∀ j, ContDiff ℝ 1 (G j)) (hGcs : ∀ j, HasCompactSupport (G j))
    (hGfin : ∀ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ < ⊤)
    (hYfin : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤)
    (hYvan : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0)
    (j : Fin n) (z : Fin n → ℂ) :
    beltramiTheta c (G + Y) j z = beltramiTheta c G j z + beltramiTheta c Y j z := by
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
  · have hzτ : z ∈ Work.CR.Flat.polydisc 0 τ :=
      Work.CR.Flat.polydisc_mono (fun i => (hρτ i).le) hz
    -- differentiability of the three potentials at `z`
    have hdG : DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPotential G w) z :=
      differentiableAt_bmPotential_of_hasCompactSupport hn hG1 hGcs z
    have hdY : DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPotential Y w) z :=
      bmPot_diff_continuous (n := n) hn (c := (0 : Fin n → ℂ)) (r := fun j => 2 * τ j)
        (α := α) hα0 hα1 (fun j => by linarith [hτ j])
        (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hYfin j)) hYfin
        (fun j w hw => hYvan j w fun hmem => by
          obtain ⟨i, hi⟩ := hw
          rw [show (2 * τ i) / 2 = τ i from by ring] at hi
          exact absurd (Work.CR.Flat.polydisc_mono (fun k => (hρτ k).le) hmem i)
            (not_lt.mpr hi))
        z (by
          rw [show Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun j => (2 * τ j) / 2)
              = Work.CR.Flat.polydisc 0 τ from by congr 1; funext i; ring]
          exact hzτ)
    have hdGY : DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPotential (G + Y) w) z := by
      have hlin : Work.CR.Flat.Cauchy.bmPotential (G + Y)
          = Work.CR.Flat.Cauchy.bmPotential G + Work.CR.Flat.Cauchy.bmPotential Y :=
        bmPotential_add_fun hn (fun j => (hG1 j).continuous)
          hGcs (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hYfin j))
          (fun j => hasCompactSupport_of_vanishing_off_polydisc hn hρ (hYvan j))
      rw [hlin]
      exact hdG.add hdY
    have hdcoord : ∀ l, Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential (G + Y)) z
        = Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z
          + Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential Y) z := by
      intro l
      have hlin : Work.CR.Flat.Cauchy.bmPotential (G + Y)
          = Work.CR.Flat.Cauchy.bmPotential G + Work.CR.Flat.Cauchy.bmPotential Y :=
        bmPotential_add_fun hn (fun j => (hG1 j).continuous)
          hGcs (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hYfin j))
          (fun j => hasCompactSupport_of_vanishing_off_polydisc hn hρ (hYvan j))
      rw [hlin, dCoord_add_local l _ _ z hdG hdY]
    simp only [beltramiTheta_apply, hdcoord]
    have h2 : (∑ x, c j x z * (Work.CR.Flat.dCoord x
            (Work.CR.Flat.Cauchy.bmPotential G) z
          + Work.CR.Flat.dCoord x (Work.CR.Flat.Cauchy.bmPotential Y) z))
        = (∑ x, c j x z * Work.CR.Flat.dCoord x
              (Work.CR.Flat.Cauchy.bmPotential G) z)
          + ∑ x, c j x z * Work.CR.Flat.dCoord x
              (Work.CR.Flat.Cauchy.bmPotential Y) z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h2, mul_add]
  · have hcz : ∀ l, c j l z = 0 := by
      intro l
      by_contra hc
      exact hz (hcsupp j l z hc)
    simp [beltramiTheta, hcz]

/-! ## The family norm of a finite sum and telescoping -/

lemma famNorm_sum_le {α : ℝ} {ι : Type*} (s : Finset ι)
    (g : ι → Fin n → (Fin n → ℂ) → ℂ) :
    famNorm α (∑ i ∈ s, g i) ≤ ∑ i ∈ s, famNorm α (g i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ i ∈ (∅ : Finset ι), g i) = 0 := Finset.sum_empty
      rw [h0, famNorm_zero, Finset.sum_empty]
  | insert a t ha ih =>
      have hsplit : (∑ i ∈ insert a t, g i) = g a + ∑ i ∈ t, g i := by
        rw [Finset.sum_insert ha]
      rw [hsplit, Finset.sum_insert ha]
      exact (famNorm_add_le (g a) (∑ i ∈ t, g i)).trans (add_le_add le_rfl ih)

/-- Telescoping a difference of a sequence along a range. -/
lemma sub_eq_sum_range {V : Type*} [AddCommGroup V] (f : ℕ → V) (m k : ℕ) :
    f (m + k) - f m = ∑ i ∈ Finset.range k, (f (m + i + 1) - f (m + i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih, Nat.add_succ]
      abel

end BTheta

end Work.NN.Core

import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.PertU.geom
import Submission.Work.PertU.asymp
import Submission.Work.Pert.Dsub_phi_star
import Submission.Work.Pert.fat_discs_subset_QLeft
import Submission.Work.Pert.tau0_approx_transfer_budget

/-! Guidance from the project lead (the requester):

LEAD (phi_star_of_close): PertData items 8–13 (D_sub, φ_inj_up/dn, φ_star_close, φ_star_deriv) for ANY map φ that is εη-close to d.φ on the fattened discs Fat η := closedBall(±iη, 3η/10). This is pert2's way to get those items for the ONE chosen gate coordinate.
Route:
  - Fat η ⊆ QLeft d.ξ₀ for η large: QLeft ξ = {π/3 < |arg(w+ξ)|}, and the worst point 0.3η + 0.7iη has arg ≈ 66.8°.
  - Fat η ⊆ d.Dφ by d.ends_sub (heights ≥ 0.7η > η₀).
  - d.φ_asymp gives ‖τ₀(d.φ w) − w‖ ≤ |a| log(2η) + |b| + 1 ≤ η/140 on Fat η for η ≥ η₂.
  - ‖d.φ w‖ ≈ 1/‖w‖ ∈ [1/(2η), 2/η]. With εη ≤ 1/(10⁴ η³), ‖φ w‖ ≥ 1/(3η) and ‖τ₀(φ w) − τ₀(d.φ w)‖ ≤ ‖φ w − d.φ w‖/(‖φ w‖‖d.φ w‖) ≤ 6η²εη ≤ η/140.
  - So Φc := τ₀ ∘ φ is holomorphic on a neighbourhood of Fat η (φ ≠ 0 there) and ‖Φc − id‖ ≤ η/70 on Fat η.
  - Apply the PROVED Work.Pert.deriv_and_inj_of_close (Pert/Dsub_phi_star.lean) to get the derivative bounds and injectivity of Φc. Injectivity of φ follows from that of τ₀∘φ.
  - φ_star_close: Dsm(±η) ⊆ Fat η, and η/70 ≤ η/40. D_sub: Dsm ⊆ Fat ⊆ U.
Reuse Pert/Dsub_phi_star.lean (deriv_and_inj_of_close, injOn_tau0) and the asymptotics lemmas already used there.
-/

namespace Work.Pert

/-! ## The fattened discs

`Fat η = closedBall (iη) (3η/10) ∪ closedBall (-iη) (3η/10)`: the discs on which `φ` is assumed
to be `εη`-close to `d.φ`. -/

/-- The fattened discs of (4.2.5). -/
def Fat (η : ℝ) : Set ℂ :=
  Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
    Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10)

/-- `Dsm (±η) ⊆ Fat η`: the radius `|η|/4` discs sit inside the radius `3η/10` fattened discs. -/
lemma Dsm_subset_Fat {η : ℝ} (hη : 0 < η) :
    MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆ Fat η := by
  have hrad : |η| / 4 ≤ 3 * η / 10 := by rw [abs_of_pos hη]; linarith
  have hrad2 : |(-η)| / 4 ≤ 3 * η / 10 := by rw [abs_neg, abs_of_pos hη]; linarith
  intro w hw
  rcases hw with hw | hw
  · left
    rw [MandelDim.Dsm] at hw
    exact Metric.closedBall_subset_closedBall hrad hw
  · right
    rw [MandelDim.Dsm] at hw
    have hc : Complex.I * ((-η : ℝ) : ℂ) = -(Complex.I * (η : ℂ)) := by push_cast; ring
    rw [hc] at hw
    exact Metric.closedBall_subset_closedBall hrad2 hw

/-! ## Elementary facts about `τ₀ z = -1/z` -/

/-- `‖τ₀ z‖ = 1/‖z‖` (with the convention `1/0 = 0`). -/
lemma norm_tau0_eq (z : ℂ) : ‖MandelDim.tau0 z‖ = 1 / ‖z‖ := by
  rw [MandelDim.tau0, norm_div, norm_neg, norm_one]

/-- `τ₀ x - τ₀ y = (x - y)/(x y)` for `x, y ≠ 0`. -/
lemma tau0_sub_tau0 {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    MandelDim.tau0 x - MandelDim.tau0 y = (x - y) / (x * y) := by
  simp only [MandelDim.tau0]
  field_simp
  ring

/-- `τ₀ ∘ φ` is differentiable wherever `φ` is differentiable and nonzero. -/
lemma differentiableAt_tau0_comp {φ : ℂ → ℂ} {w : ℂ} (hφ : DifferentiableAt ℂ φ w)
    (hne : φ w ≠ 0) : DifferentiableAt ℂ (fun u => MandelDim.tau0 (φ u)) w := by
  have hτ : DifferentiableAt ℂ MandelDim.tau0 (φ w) := by
    show DifferentiableAt ℂ (fun z : ℂ => -1 / z) (φ w)
    exact (differentiableAt_const (-1)).div differentiableAt_id hne
  exact hτ.comp w hφ

/-! ## The main lemma -/

theorem phi_star_of_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ η : ℝ, η₂ ≤ η →
      (Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
          Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10)) ⊆ d.Dφ ∧
      ∃ εη : ℝ, 0 < εη ∧
      ∀ (φ : ℂ → ℂ) (U : Set ℂ), IsOpen U → DifferentiableOn ℂ φ U →
        (Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
          Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10)) ⊆ U →
        (∀ w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
            Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10), ‖φ w - d.φ w‖ < εη) →
        MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆ U ∧
        Set.InjOn φ (MandelDim.Dsm η) ∧ Set.InjOn φ (MandelDim.Dsm (-η)) ∧
        (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ‖MandelDim.tau0 (φ w) - w‖ ≤ |η| / 40) ∧
        (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
          1 / 2 < ‖deriv (fun u => MandelDim.tau0 (φ u)) w‖ ∧
            ‖deriv (fun u => MandelDim.tau0 (φ u)) w‖ < 2) := by
  obtain ⟨a, b, hasymp⟩ := d.φ_asymp
  obtain ⟨ηA, hηApos, hA⟩ := Work.PertU.asymp hasymp
  obtain ⟨ηG, hηGpos, hG⟩ := fat_discs_subset_QLeft d.ξ₀
  refine ⟨max ηA (max ηG 1), lt_of_lt_of_le hηApos (le_max_left _ _), fun η hη => ?_⟩
  have hηA' : ηA ≤ η := le_trans (le_max_left _ _) hη
  have hηG' : ηG ≤ η :=
    le_trans (le_max_left ηG 1) (le_trans (le_max_right ηA (max ηG 1)) hη)
  have hη1 : (1 : ℝ) ≤ η :=
    le_trans (le_max_right ηG 1) (le_trans (le_max_right ηA (max ηG 1)) hη)
  have hηpos : 0 < η := lt_of_lt_of_le zero_lt_one hη1
  obtain ⟨hGQ, hGn⟩ := hG η hηG'
  obtain ⟨hA1, hA2, hA3⟩ := hA η hηA'
  have hFatDphi : Fat η ⊆ d.Dφ := hGQ.trans d.Q_sub
  refine ⟨hFatDphi, ?_⟩
  refine ⟨(1 : ℝ) / (10 ^ 6 * η ^ 2), ?_, ?_⟩
  · exact one_div_pos.mpr (by positivity)
  intro φ U hU hφdiff hFatU hclose
  -- ## the key estimate on `Fat η`
  have hker : ∀ w ∈ Fat η, ‖φ w‖ ≥ 1 / (3 * η) ∧ ‖MandelDim.tau0 (φ w) - w‖ ≤ η / 70 := by
    intro w hw
    obtain ⟨hl, hu⟩ := hGn w hw
    have hdphi : ‖MandelDim.tau0 (d.φ w) - w‖ ≤ η / 80 :=
      le_trans (hA1 w (hGQ hw) (by linarith) (by linarith)) hA3
    refine tau0_approx_transfer_budget hηpos hl hu hdphi (hclose w hw) ?_ ?_
    · -- `6 η εη ≤ 1`
      have hden : (0 : ℝ) < 10 ^ 6 * η ^ 2 := by positivity
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith [hη1, hηpos]
    · -- `6 η² εη ≤ η/560`
      have heq : 6 * η ^ 2 * ((1 : ℝ) / (10 ^ 6 * η ^ 2)) = 6 / 10 ^ 6 := by
        field_simp
      rw [heq]
      have h1 : (6 : ℝ) / 10 ^ 6 ≤ (1 : ℝ) / 560 := by norm_num
      have h2 : (1 : ℝ) / 560 ≤ η / 560 := by linarith
      linarith
  -- ## `τ₀ ∘ φ` is holomorphic on the fattened discs and within `η/70` of the identity
  have hcl : ∀ w ∈ Fat η, DifferentiableAt ℂ (fun u => MandelDim.tau0 (φ u)) w ∧
      ‖MandelDim.tau0 (φ w) - w‖ ≤ η / 70 := by
    intro w hw
    refine ⟨differentiableAt_tau0_comp ?_ ?_, (hker w hw).2⟩
    · exact hφdiff.differentiableAt (hU.mem_nhds (hFatU hw))
    · have h1 := (hker w hw).1
      intro h0
      rw [h0, norm_zero] at h1
      have h2 : (0 : ℝ) < 1 / (3 * η) := by positivity
      linarith
  obtain ⟨hder, hinj1, hinj2⟩ :=
    deriv_and_inj_of_close (Φc := fun u => MandelDim.tau0 (φ u)) hηpos hcl
  have hDsmFat : MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆ Fat η := Dsm_subset_Fat hηpos
  have hne : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), φ w ≠ 0 := by
    intro w hw
    have h1 := (hker w (hDsmFat hw)).1
    intro h0
    rw [h0, norm_zero] at h1
    have h2 : (0 : ℝ) < 1 / (3 * η) := by positivity
    linarith
  refine ⟨fun w hw => hFatU (hDsmFat hw), ?_, ?_, ?_, hder⟩
  · exact injOn_of_comp_inj injOn_tau0 hinj1 (fun w hw => hne w (Or.inl hw))
  · exact injOn_of_comp_inj injOn_tau0 hinj2 (fun w hw => hne w (Or.inr hw))
  · intro w hw
    have h1 := (hker w (hDsmFat hw)).2
    rw [abs_of_pos hηpos]
    linarith

end Work.Pert

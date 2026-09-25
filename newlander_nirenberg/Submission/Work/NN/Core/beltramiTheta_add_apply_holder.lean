import Mathlib
import Submission.Work.NN.Core.beltrami_theta_setup
import Submission.Work.NN.Core.contDiff_one_bmPotential_of_holder

set_option autoImplicit true

namespace Work.NN.Core

/-- **Additivity of `Θ` in its argument**, with the first family `G` required only to be
continuous (with compact support and finite `C^{0,α}` norm) instead of `C¹`.  The differentiability
of `bmPotential G` at points of the polydisc comes from the `C^{0,α}` Schauder theory
(`bmPot_diff_continuous`), and the potential is additive on continuous compactly supported data. -/
lemma beltramiTheta_add_apply_holder {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j)
    {c : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hcsupp : ∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {G Y : Fin n → (Fin n → ℂ) → ℂ}
    (hGc : ∀ j, Continuous (G j)) (hGcs : ∀ j, HasCompactSupport (G j))
    (hGfin : ∀ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ < ⊤)
    (hYfin : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤)
    (hYvan : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0)
    (j : Fin n) (z : Fin n → ℂ) :
    Work.NN.Core.BTheta.beltramiTheta c (G + Y) j z
      = Work.NN.Core.BTheta.beltramiTheta c G j z + Work.NN.Core.BTheta.beltramiTheta c Y j z := by
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
  · -- On the polydisc the coefficients are generic and the potentials are differentiable.
    -- differentiability of the potential of `Y`
    have hdY : DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPotential Y w) z := by
      refine bmPot_diff_continuous (n := n) (c := (0 : Fin n → ℂ)) (r := fun j => 2 * τ j)
        (α := α) hn hα0 hα1 (fun j => by linarith [hτ j])
        (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hYfin j)) hYfin ?_ z ?_
      · intro j w hw
        obtain ⟨i, hi⟩ := hw
        rw [show (2 * τ i) / 2 = τ i from by ring] at hi
        exact hYvan j w fun hmem =>
          absurd (Work.CR.Flat.polydisc_mono (fun k => (hρτ k).le) hmem i)
            (not_lt.mpr hi)
      · exact Work.CR.Flat.polydisc_mono (fun i => by
          have := hρτ i
          show ρ i ≤ 2 * τ i / 2
          linarith) hz
    -- differentiability of the potential of `G`
    obtain ⟨R, _hR0, hR⟩ := BTheta.exists_radius_all_of_hasCompactSupport hGcs
    have hdG : DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPotential G w) z := by
      refine bmPot_diff_continuous (n := n) (c := (0 : Fin n → ℂ))
        (r := fun j => 2 * (R + ρ j + 1)) (α := α) hn hα0 hα1
        (fun j => by linarith [hρ j]) hGc hGfin ?_ z ?_
      · intro j w hw
        obtain ⟨i, hi⟩ := hw
        rw [show (2 * (R + ρ i + 1)) / 2 = R + ρ i + 1 from by ring] at hi
        simp only [Pi.zero_apply, sub_zero] at hi
        exact hR j w (le_trans (by linarith [hρ i]) (norm_le_pi_norm w i))
      · exact Work.CR.Flat.polydisc_mono (fun i => by
          have := hρ i
          show ρ i ≤ 2 * (R + ρ i + 1) / 2
          linarith) hz
    -- additivity of the potential
    have hlin : Work.CR.Flat.Cauchy.bmPotential (G + Y)
        = Work.CR.Flat.Cauchy.bmPotential G + Work.CR.Flat.Cauchy.bmPotential Y :=
      BTheta.bmPotential_add_fun hn hGc hGcs
        (fun j => continuous_of_holderNorm_zero_lt_top hα0 (hYfin j))
        (fun j => BTheta.hasCompactSupport_of_vanishing_off_polydisc hn hρ (hYvan j))
    have hdcoord : ∀ l, Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential (G + Y)) z
        = Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z
          + Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential Y) z := by
      intro l
      rw [hlin, BTheta.dCoord_add_local l _ _ z hdG hdY]
    simp only [BTheta.beltramiTheta_apply, hdcoord]
    have h2 : (∑ x, c j x z * (Work.CR.Flat.dCoord x (Work.CR.Flat.Cauchy.bmPotential G) z
              + Work.CR.Flat.dCoord x (Work.CR.Flat.Cauchy.bmPotential Y) z))
        = (∑ x, c j x z * Work.CR.Flat.dCoord x (Work.CR.Flat.Cauchy.bmPotential G) z)
          + ∑ x, c j x z * Work.CR.Flat.dCoord x (Work.CR.Flat.Cauchy.bmPotential Y) z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h2, mul_add]
  · -- Off the polydisc the coefficients vanish, hence so does everything.
    have hcz : ∀ l, c j l z = 0 := by
      intro l
      by_contra hc
      exact hz (hcsupp j l z hc)
    simp [BTheta.beltramiTheta, hcz]

end Work.NN.Core

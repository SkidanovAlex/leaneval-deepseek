import Submission.Work.OddRadon.AbelInversion
import Submission.Work.OddRadon.radonProfile_eq_abelTrans
import Submission.Work.OddRadon.sphereArea_pos

/-!
# Inversion of the odd-dimensional Radon profile (`Work.OddRadon`, parts 3c–3d)

* `radonProfile_inv` — on an even profile of class `C¹`, `radonInverse n` inverts the
  one-variable Radon transform `radonProfile (2n+1)`;
* `radonProfile_eqOn_of_eqOn` — the **partial-data principle**: if two even profiles have the
  same Radon transform for all equatorial parameters `c ≤ c₀`, they agree on `c ≤ c₀`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **Inversion of the one-variable Radon transform on even profiles.**
For `d = 2n+1` (`n ≥ 1`) and an even `γ` of class `C¹` on `[-1,1]`,

  `γ u = radonInverse n (radonProfile (2n+1) γ) u`   for `u ∈ (0,1)`. -/
theorem radonProfile_inv (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ}
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc (-1) 1)) (heven : ∀ t, γ (-t) = γ t) {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    γ u = radonInverse n (radonProfile (2 * n + 1) γ) u := by
  have hG : ContDiffOn ℝ 1 γ (Set.Icc 0 1) :=
    hγ.mono (by rintro x ⟨hx0, hx1⟩; exact ⟨by linarith, hx1⟩)
  have hcont : ContinuousOn γ (Set.Icc (-1) 1) := hγ.continuousOn
  have hσ : (0 : ℝ) < sphereArea (2 * n - 2) := sphereArea_pos _
  have hEqOn : Set.EqOn
      (fun c : ℝ => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) *
        radonProfile (2 * n + 1) γ c)
      (abelTrans ((n : ℝ) - 3 / 2) γ) (Set.Ioo 0 1) := by
    intro c hc
    change (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * radonProfile (2 * n + 1) γ c
      = abelTrans ((n : ℝ) - 3 / 2) γ c
    have h := radonProfile_eq_abelTrans n hn hcont heven hc.1
    rw [h]
    have hpow : c ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hc.1)
    field_simp
    try ring
  have hred := abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2) hEqOn
  unfold radonInverse
  rw [abelInvert_congr_of_eqOn hu.1 hu.2 hred]
  exact abel_inversion_odd n hn hG hu

/-- **The partial-data principle.**  Even profiles of class `C¹` with the same Radon transform
on the cap `{c ≤ c₀}` agree on that cap: the inversion at `u` uses the data only on `(0,u)`. -/
theorem radonProfile_eqOn_of_eqOn (n : ℕ) (hn : 1 ≤ n) {γ₁ γ₂ : ℝ → ℝ}
    (h₁ : ContDiffOn ℝ 1 γ₁ (Set.Icc (-1) 1)) (h₂ : ContDiffOn ℝ 1 γ₂ (Set.Icc (-1) 1))
    (he₁ : ∀ t, γ₁ (-t) = γ₁ t) (he₂ : ∀ t, γ₂ (-t) = γ₂ t) {c₀ : ℝ}
    (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h : Set.EqOn (radonProfile (2 * n + 1) γ₁) (radonProfile (2 * n + 1) γ₂)
      (Set.Ioo 0 c₀)) :
    Set.EqOn γ₁ γ₂ (Set.Ioo 0 c₀) := by
  intro u hu
  have hu1 : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu.1, lt_trans hu.2 hc₀.2⟩
  rw [radonProfile_inv n hn h₁ he₁ hu1, radonProfile_inv n hn h₂ he₂ hu1]
  unfold radonInverse
  refine abelInvert_congr_of_eqOn hu1.1 hu.2 ?_
  refine abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2) ?_
  intro c hc
  change (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * radonProfile (2 * n + 1) γ₁ c
    = (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * radonProfile (2 * n + 1) γ₂ c
  rw [h hc]

end Work.OddRadon

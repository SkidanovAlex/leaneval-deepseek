import Mathlib
import Submission.Work.Pert.pert2v2.EfFloor
import Submission.Work.Pert.pert2v2.HornExt
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.Prelim
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.seedP_germ_add_one

namespace Work.Pert.pert2v2.EfFloorDiffV2

open Complex Set Filter
open scoped Topology

noncomputable section

variable {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y : ℝ}

/-- **The value of the floor-based extension through the seed value.**  At a point `w` whose
`⌊Re⌋`-representative `w - ⌊Re w⌋` lies in the gate image, `EfFloor w - w` is the seed value
`Φp (invOn Φm Q ·)` of `MaxDom` at that representative, minus the representative — i.e. it is the
value of `seedP Φp Φm Q - id`. -/
theorem EfFloor_sub_eq_seedP {w : ℂ}
    (h : w - (((Int.floor w.re : ℤ)) : ℂ) ∈ Φm '' Q) :
    EfFloor Φm Φp Q w - w
      = Work.Pert.seedP Φp Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ))
        - (w - (((Int.floor w.re : ℤ)) : ℂ)) := by
  simp only [EfFloor, if_pos h, Work.Pert.seedP]
  ring

theorem EfFloor_sub_id_differentiableOn {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y : ℝ}
    (hQopen : IsOpen Q) (hΦm : DifferentiableOn ℂ Φm Q) (hder : ∀ z ∈ Q, deriv Φm z ≠ 0)
    (hInj : Set.InjOn Φm Q) (hΦp : DifferentiableOn ℂ Φp Q)
    (herb : ∀ w : ℂ, y ≤ w.im → w - (((Int.floor w.re : ℤ)) : ℂ) ∈ Φm '' Q)
    (herb1 : ∀ w : ℂ, y ≤ w.im →
      (w - (((Int.floor w.re : ℤ)) : ℂ)) + 1 ∈ Φm '' Q)
    (hlvl : ∀ w : ℂ, y ≤ w.im → w - (((Int.floor w.re : ℤ)) : ℂ) + 1 ∈ Φm '' Q →
      Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ) + 1))
        = Φp (Work.Pert.invOn Φm Q (w - (((Int.floor w.re : ℤ)) : ℂ))) + 1) :
    DifferentiableOn ℂ (fun w : ℂ => EfFloor Φm Φp Q w - w) {w : ℂ | y ≤ w.im} := by
  intro w₀ hw₀
  have hseed : DifferentiableOn ℂ (Work.Pert.seedP Φp Φm Q) (Φm '' Q) :=
    Work.Pert.seedP_holo hQopen hΦm hΦp hInj hder
  set n : ℤ := ⌊w₀.re⌋ with hn
  -- the canonical (`⌊Re⌋`) representative `u := w₀ - n` of the base point
  have huA : w₀ - (n : ℂ) ∈ Φm '' Q := by rw [hn]; exact herb w₀ hw₀
  have huA1 : (w₀ - (n : ℂ)) + 1 ∈ Φm '' Q := by rw [hn]; exact herb1 w₀ hw₀
  have himu : y ≤ (w₀ - (n : ℂ)).im := by rw [Complex.sub_im, hn]; simpa using hw₀
  have hreu : (w₀ - (n : ℂ)).re ∈ Set.Ico 0 1 := by
    have h : (w₀ - (n : ℂ)).re = w₀.re - (n : ℝ) := by rw [Complex.sub_re]; simp
    rw [h, hn, Set.mem_Ico]
    exact ⟨by linarith [Int.floor_le w₀.re], by linarith [Int.lt_floor_add_one w₀.re]⟩
  -- the periodicity *germ* at the canonical representative
  obtain ⟨δg, hδg, hgerm⟩ :=
    seedP_germ_add_one hQopen hΦm hder hInj hΦp hlvl huA huA1 himu hreu
  -- the gate image is a neighbourhood of `u`, so `seedP` is differentiable there
  have himg : Φm '' Q ∈ 𝓝 (w₀ - (n : ℂ)) := by
    obtain ⟨ζ, hζQ, hζ⟩ := huA
    rw [← hζ]
    exact mem_nhds_image_of_deriv_ne_zero hQopen hΦm hζQ (hder ζ hζQ)
  have hseedAt : DifferentiableAt ℂ (Work.Pert.seedP Φp Φm Q) (w₀ - (n : ℂ)) :=
    (hseed _ huA).differentiableAt himg
  -- the candidate germ `w ↦ seedP (w - n) - (w - n)`
  have hGdiff : DifferentiableAt ℂ
      (fun w : ℂ => Work.Pert.seedP Φp Φm Q (w - (n : ℂ)) - (w - (n : ℂ))) w₀ := by
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Work.Pert.seedP Φp Φm Q z - z)
        (w₀ - (n : ℂ)) := hseedAt.sub differentiableAt_id
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w - (n : ℂ)) w₀ :=
      differentiableAt_id.sub (differentiableAt_const _)
    simpa [Function.comp_def] using h2.comp w₀ h1
  refine hGdiff.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
  · -- the two functions agree on the half plane near `w₀`
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨min δg 1 / 2, ?_, ?_⟩
    · positivity
    · intro w hwd hwS
      have hmin1 : min δg 1 ≤ δg := min_le_left _ _
      have hmin2 : min δg 1 ≤ 1 := min_le_right _ _
      have hδg' : min δg 1 / 2 ≤ δg := by linarith
      have hδ12 : min δg 1 / 2 ≤ 1 / 2 := by linarith
      have ht : ‖w - w₀‖ < min δg 1 / 2 := by
        rwa [dist_eq_norm] at hwd
      have htδg : ‖w - w₀‖ < δg := lt_of_lt_of_le ht hδg'
      have ht12 : ‖w - w₀‖ < 1 / 2 := lt_of_lt_of_le ht hδ12
      -- the floor of `Re w` can only be `n - 1`, `n` or `n + 1`
      have hrew : w.re = w₀.re + (w - w₀).re := by
        conv_lhs => rw [show w = w₀ + (w - w₀) by ring]
        rw [Complex.add_re]
      have hw₀re : w₀.re = (w₀ - (n : ℂ)).re + (n : ℝ) := by
        rw [Complex.sub_re]; simp
      have hlow : ((n : ℤ) : ℝ) - 1 ≤ w.re := by
        have h1 : -|(w - w₀).re| ≤ (w - w₀).re := neg_abs_le _
        have h2 : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
        linarith [hrew, hw₀re, hreu.1]
      have hhigh : w.re < ((n : ℤ) : ℝ) + 2 := by
        have h1 : (w - w₀).re ≤ |(w - w₀).re| := le_abs_self _
        have h2 : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
        linarith [hrew, hw₀re, hreu.2]
      have hfl_le : n - 1 ≤ ⌊w.re⌋ := by
        rw [Int.le_floor]
        push_cast
        exact hlow
      have hfl_ge : ⌊w.re⌋ ≤ n + 1 := by
        have hlt : ⌊w.re⌋ < n + 2 := by
          rw [Int.floor_lt]
          push_cast
          exact hhigh
        omega
      have hthree : ⌊w.re⌋ = n ∨ ⌊w.re⌋ = n + 1 ∨ ⌊w.re⌋ = n - 1 := by omega
      rcases hthree with hk | hk | hk
      · -- `⌊Re w⌋ = n`: the value is the germ value directly
        have hkC : (((Int.floor w.re : ℤ)) : ℂ) = (n : ℂ) := by rw [hk]
        have hval := EfFloor_sub_eq_seedP (Φm := Φm) (Φp := Φp) (Q := Q) (w := w)
          (by simpa [hkC] using herb w hwS)
        rw [hval, hkC]
      · -- `⌊Re w⌋ = n + 1`: the level-one relation at `w` transfers the value back
        have hkC : (((Int.floor w.re : ℤ)) : ℂ) = (n : ℂ) + 1 := by
          rw [hk]; push_cast; ring
        have hprem : w - (((Int.floor w.re : ℤ)) : ℂ) + 1 ∈ Φm '' Q := herb1 w hwS
        have hlvlw := hlvl w hwS hprem
        have hshift : Work.Pert.seedP Φp Φm Q (w - (n : ℂ))
            = Work.Pert.seedP Φp Φm Q (w - (n : ℂ) - 1) + 1 := by
          rw [hkC] at hlvlw
          have e1 : w - ((n : ℂ) + 1) + 1 = w - (n : ℂ) := by ring
          have e2 : w - ((n : ℂ) + 1) = w - (n : ℂ) - 1 := by ring
          rw [e1, e2] at hlvlw
          simpa [Work.Pert.seedP] using hlvlw
        have hval := EfFloor_sub_eq_seedP (Φm := Φm) (Φp := Φp) (Q := Q) (w := w)
          (by simpa [hkC] using herb w hwS)
        rw [hval, hkC]
        rw [show w - ((n : ℂ) + 1) = w - (n : ℂ) - 1 by ring]
        rw [hshift]
        ring
      · -- `⌊Re w⌋ = n - 1`: the germ identity transfers the value back
        have hkC : (((Int.floor w.re : ℤ)) : ℂ) = (n : ℂ) - 1 := by
          rw [hk]; push_cast; ring
        have hg := hgerm (w - w₀) htδg
        have hg' : Work.Pert.seedP Φp Φm Q ((w - (n : ℂ)) + 1)
            = Work.Pert.seedP Φp Φm Q (w - (n : ℂ)) + 1 := by
          have e1 : (w₀ - (n : ℂ)) + 1 + (w - w₀) = (w - (n : ℂ)) + 1 := by ring
          have e2 : (w₀ - (n : ℂ)) + (w - w₀) = w - (n : ℂ) := by ring
          rwa [e1, e2] at hg
        have hval := EfFloor_sub_eq_seedP (Φm := Φm) (Φp := Φp) (Q := Q) (w := w)
          (by simpa [hkC] using herb w hwS)
        rw [hval, hkC]
        rw [show w - ((n : ℂ) - 1) = (w - (n : ℂ)) + 1 by ring]
        rw [hg']
        ring
  · -- at the base point itself the value formula closes with `⌊Re w₀⌋ = n`
    have hval := EfFloor_sub_eq_seedP (Φm := Φm) (Φp := Φp) (Q := Q) (w := w₀)
      (by rw [← hn]; exact huA)
    rw [hval, ← hn]

end

end Work.Pert.pert2v2.EfFloorDiffV2

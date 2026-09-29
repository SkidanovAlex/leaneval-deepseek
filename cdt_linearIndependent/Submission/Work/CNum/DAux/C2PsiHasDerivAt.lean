import Mathlib
import Submission.Work.CNum.Basic
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.AlpBound

namespace Work.CNum.DAux

/-!
# `Work.CNum.DAux.C2PsiHasDerivAt`

`C2Psi t = t - π/2 + arcsin (cos t / C)`, `C = C2C = cos(α/2)`, `α = alpR`.

For `t ∈ (α/2, π - α/2)` we have `sin t > σ = C2σ`, hence `cos² t < C²`, so that
`cos t / C ∈ (-1, 1)`; the chain rule (derivative of `arcsin` composed with
`cos t / C`) yields

  `C2Psi' t = 1 - sin t / √(C² - cos² t)`.

That is the statement proved here.
-/

open Real

private lemma sin_gt_C2σ {t : ℝ}
    (ht : t ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2)) :
    Work.CNum.C2σ < Real.sin t := by
  have h := Work.CNum.C2σ_lt_sin_half (θ := 2 * t)
    (show (2 * t) ∈ Set.Ioo Work.CNum.alpR (2 * Real.pi - Work.CNum.alpR) from
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rwa [show 2 * t / 2 = t from by ring] at h

private lemma cos_sq_lt_C2C_sq {t : ℝ}
    (ht : t ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2)) :
    Real.cos t ^ 2 < Work.CNum.C2C ^ 2 := by
  have hsin := sin_gt_C2σ ht
  have h1 : Work.CNum.C2σ ^ 2 < Real.sin t ^ 2 := by
    nlinarith [Work.CNum.C2σ_pos.le, hsin]
  have h2 : Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by linarith [Real.sin_sq_add_cos_sq t]
  rw [h2, ← Work.CNum.one_sub_C2σ_sq]
  linarith

private lemma sqrt_one_sub_sq {t : ℝ}
    (ht : t ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2)) :
    Real.sqrt (1 - (Real.cos t / Work.CNum.C2C) ^ 2)
      = Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos t ^ 2) / Work.CNum.C2C := by
  have hcos := cos_sq_lt_C2C_sq ht
  have hC2 : (1 - (Real.cos t / Work.CNum.C2C) ^ 2)
      = (Work.CNum.C2C ^ 2 - Real.cos t ^ 2) / Work.CNum.C2C ^ 2 := by
    field_simp [Work.CNum.C2C_ne_zero]
  rw [hC2, Real.sqrt_div (by linarith [hcos]) (Work.CNum.C2C ^ 2),
    Real.sqrt_sq Work.CNum.C2C_pos.le]

private lemma chain_val_eq {t : ℝ}
    (ht : t ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2)) :
    (1 / Real.sqrt (1 - (Real.cos t / Work.CNum.C2C) ^ 2))
        * (-(Real.sin t) / Work.CNum.C2C)
      = -(Real.sin t / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos t ^ 2)) := by
  rw [sqrt_one_sub_sq ht]
  field_simp [Work.CNum.C2C_ne_zero]

theorem C2PsiHasDerivAt {t : ℝ}
    (ht : t ∈ Set.Ioo (Work.CNum.alpR / 2) (Real.pi - Work.CNum.alpR / 2)) :
    HasDerivAt Work.CNum.C2Psi
      (1 - Real.sin t / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos t ^ 2)) t := by
  have hcos := cos_sq_lt_C2C_sq ht
  have hne1 : Real.cos t / Work.CNum.C2C ≠ 1 := by
    intro h
    have h' := (div_eq_one_iff_eq Work.CNum.C2C_ne_zero).mp h
    rw [h'] at hcos; exact absurd hcos (lt_irrefl _)
  have hne_neg1 : Real.cos t / Work.CNum.C2C ≠ -1 := by
    intro h
    have h' : Real.cos t = -Work.CNum.C2C := by
      rw [div_eq_iff Work.CNum.C2C_ne_zero] at h; linarith
    rw [h'] at hcos
    nlinarith [hcos]
  have hid : HasDerivAt (fun s : ℝ => s - Real.pi / 2) 1 t :=
    (hasDerivAt_id t).sub_const (Real.pi / 2)
  have harc : HasDerivAt (fun s : ℝ => Real.arcsin (Real.cos s / Work.CNum.C2C))
      ((1 / Real.sqrt (1 - (Real.cos t / Work.CNum.C2C) ^ 2))
        * (-(Real.sin t) / Work.CNum.C2C)) t := by
    have hcos' : HasDerivAt (fun s : ℝ => Real.cos s / Work.CNum.C2C)
        (-(Real.sin t) / Work.CNum.C2C) t :=
      (Real.hasDerivAt_cos t).div_const _
    have h2 := (Real.hasDerivAt_arcsin hne_neg1 hne1).comp t hcos'
    simpa only [Function.comp_def] using h2
  have h := hid.add harc
  have hval : 1 + (1 / Real.sqrt (1 - (Real.cos t / Work.CNum.C2C) ^ 2))
        * (-(Real.sin t) / Work.CNum.C2C)
      = 1 - Real.sin t / Real.sqrt (Work.CNum.C2C ^ 2 - Real.cos t ^ 2) := by
    rw [chain_val_eq ht]; ring
  rw [hval] at h
  have heq : ((fun s : ℝ => s - Real.pi / 2)
        + (fun s : ℝ => Real.arcsin (Real.cos s / Work.CNum.C2C)))
      =ᶠ[nhds t] Work.CNum.C2Psi := by
    filter_upwards with s
    simp [Work.CNum.C2Psi, Pi.add_apply]
  exact (heq.hasDerivAt_iff).mp h

end Work.CNum.DAux

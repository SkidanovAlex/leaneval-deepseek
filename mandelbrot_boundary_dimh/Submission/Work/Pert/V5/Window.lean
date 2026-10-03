import Mathlib
import Submission.Work.Pert.V5.Basics

/-!
# The window derivative bound

`Work.FatouL1.windowDefectBound` produces, for **every** `x₀ < -Ξ - 3` (and `x₀` to the right of
the left boundary of the gate), a Fatou coordinate `Φ` of `F = liftF u σ α` on `Qm Ξ α` with

`‖deriv Φ z - 1/(F z - z)‖ ≤ 1/150`   for all `z` with `x₀ - 1/8 < z.re < x₀ + 33/32`.

Since any two Fatou coordinates on the gate differ by a constant (`FatouUnique`, a conjunct of
`FatouStatement`), the *derivative* is the same for `Φm`, so the bound transfers:

* `deriv_sub_one_le_window`: for `z ∈ Qm Ξ α` with `(Ξ - 1/α).re + 1 < z.re < -Ξ - 3`,
  `‖deriv Φm z - 1‖ ≤ 1/150 + 1/31`.

The region is a horizontal strip of the gate; in particular it contains the whole band
`[-(Ξ+2M+2^10), -(Ξ+2^10)] × ℝ` used by the assembly (see `band_deriv_sub_one_le`).
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

/-- **Pointwise window bound for the derivative of the Fatou coordinate.**  For `z` in the gate
with `(Ξ - 1/α).re + 1 < z.re < -Ξ - 3` the deviation `Φm' - 1` is bounded by `1/150 + 1/31`. -/
theorem deriv_sub_one_le_window {Ξ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z : ℂ}
    (hF : MandelDim.FatouStatement)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (h1 : ((Ξ : ℂ) - 1 / α).re + 1 < z.re) (h2 : z.re + 3 < -Ξ) :
    ‖deriv Φm z - 1‖ ≤ 1 / 150 + 1 / 31 := by
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    simpa only [Work.Pert.Qm] using
      Work.Fatou.Qreg.isOpen_Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
  set ξ : ℝ := z.re with hξ
  have hw1 : ∀ a ∈ (some ((Ξ : ℂ) - 1 / α) : Option ℂ), a.re + 1 < ξ := by
    intro a ha
    rw [Option.mem_some_iff] at ha
    rw [hξ, ← ha]
    exact h1
  have hw2 : ∀ b ∈ (some (-(Ξ : ℂ)) : Option ℂ), ξ + 3 < b.re := by
    intro b hb
    rw [Option.mem_some_iff] at hb
    rw [hξ, ← hb]
    exact h2
  obtain ⟨Φw, hΦw, hwin⟩ :=
    Work.FatouL1.windowDefectBound (b₁ := some ((Ξ : ℂ) - 1 / α)) (b₂ := some (-(Ξ : ℂ)))
      (F := Work.Pert.liftF u σ α) (x₀ := ξ) hQAdm hNT hw1 hw2
  obtain ⟨c, hc⟩ := hF.2.2.1 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))
    (Work.Pert.liftF u σ α) Φw Φm hQAdm hNT.1 hΦw hΦm
  have hderiv : deriv Φm z = deriv Φw z := by
    have hev : (fun w => Φw w + c) =ᶠ[nhds z] Φm := by
      filter_upwards [hQopen.mem_nhds hz] with w hw
      rw [hc w hw]
    have h1' : deriv (fun w => Φw w + c) z = deriv Φm z := Filter.EventuallyEq.deriv_eq hev
    rw [deriv_add_const] at h1'
    exact h1'.symm
  have hwinz : ‖deriv Φw z - 1 / (Work.Pert.liftF u σ α z - z)‖ ≤ 1 / 150 :=
    hwin z (by rw [hξ]; linarith) (by rw [hξ]; norm_num)
  have hnv : ‖(Work.Pert.liftF u σ α z - z) - 1‖ ≤ 1 / 32 := by
    have h := (hNT.1.2 z hz).1
    have he : Work.Pert.liftF u σ α z - z - 1 = Work.Pert.liftF u σ α z - (z + 1) := by ring
    rwa [he]
  have hinv := inv_sub_one_le_of_close hnv
  calc ‖deriv Φm z - 1‖
      = ‖(deriv Φm z - 1 / (Work.Pert.liftF u σ α z - z))
          + (1 / (Work.Pert.liftF u σ α z - z) - 1)‖ := by ring_nf
    _ ≤ ‖deriv Φm z - 1 / (Work.Pert.liftF u σ α z - z)‖
          + ‖1 / (Work.Pert.liftF u σ α z - z) - 1‖ := norm_add_le _ _
    _ ≤ 1 / 150 + 1 / 31 := by rw [hderiv]; exact add_le_add hwinz hinv

/-- **The same bound on the whole band.**  For every `x` in `[-(Ξ+2^10+2M), -(Ξ+2^10)]` and every
height `s`, `‖deriv Φm (x + i s) - 1‖ ≤ 1/150 + 1/31`. -/
theorem band_deriv_sub_one_le {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    {x s : ℝ} (hx : -(Ξ + 2 ^ 10 + 2 * M) ≤ x) (hx' : x ≤ -(Ξ + 2 ^ 10)) :
    ‖deriv Φm (x + s * Complex.I) - 1‖ ≤ 1 / 150 + 1 / 31 := by
  have hkey : 18 * M + 2 * Ξ + 2 ^ 10 ≤ (1 / α).re := band_Qm_key_bound hΞ hM hInF1 hα
  have hmem : (x + s * Complex.I : ℂ) ∈ Work.Pert.Qm Ξ α :=
    (band_margins hΞ hM hInF1 hα hQAdm x s hx hx').1
  have hre : (x + s * Complex.I : ℂ).re = x := by
    simp [Complex.add_re, Complex.mul_I_re]
  refine deriv_sub_one_le_window hF hQAdm hNT hΦm hmem ?_ ?_
  · rw [hre]
    have h1 : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by
      rw [Complex.sub_re, Complex.ofReal_re]
    rw [h1]
    linarith
  · rw [hre]
    nlinarith [show (3 : ℝ) < 2 ^ 10 by norm_num]

end

end Work.Pert.V5

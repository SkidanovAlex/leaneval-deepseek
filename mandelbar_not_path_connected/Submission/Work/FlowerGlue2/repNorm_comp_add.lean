import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.RepNorm
import Submission.Work.FlowerGlue2.approxCoordRep_woutG_le
import Submission.Work.FlowerGlue2.exists_log_mul_add_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

namespace Work.FlowerGlue2

/-- **`RepNorm` is invariant under translating the argument of `Ψ`.**

Given the repelling normalisation `h : RepNorm P Ψ` with constants `sr, N, K`, fix any shift
`s : ℂ`.  For every `z` of the outgoing window the hypothesis produces a level `v` with
`Ψ v = z` and, crucially, the *quantitative* closeness to the model level
`A = approxCoordRep (P.κ c₀) (w0 P z) + sr`:

  `‖v - A‖ ≤ K (1 + H) (1 + log R) / R`.

The whole point is that this pins `Re v` from above: `Re v ≤ Re A + err`, and the model level is
far to the left, `Re A ≤ -R + ‖P.κ c₀‖ (log 2 + log R + π)` (the window bound
`approxCoordRep_woutG_le`), while `err ≤ (K/8) (1 + log R)`.  Hence for all large `R`

  `Re v ≤ -R/2 + Re s`,

so that the shifted witness `u := v - s` again lies in the far-left half-plane:
`Re u = Re v - Re s < -R/2`.  It also satisfies `Ψ (u + s) = Ψ v = z` and
`‖u - (A - s)‖ = ‖v - A‖ ≤ err`, which is exactly the `RepNorm` conclusion for the shifted
coordinate `sr' = sr - s` and the very same `K`.  The shift of the threshold is supplied by the
elementary eventual estimate `exists_log_mul_add_lt`. -/
theorem repNorm_comp_add {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {Ψ : ℂ → ℂ} (h : Work.PARIMPL2.Lavaurs.RepNorm P Ψ) (s : ℂ) :
    Work.PARIMPL2.Lavaurs.RepNorm P (fun u => Ψ (u + s)) := by
  obtain ⟨sr, N, K, hN, hK, hmain⟩ := h
  have hG : 0 ≤ ‖P.κ c₀‖ + K / 8 := by positivity
  obtain ⟨N₀, _hN₀1, hN₀⟩ := Work.FlowerGlue2.exists_log_mul_add_lt (‖P.κ c₀‖ + K / 8)
    (‖P.κ c₀‖ * (Real.log 2 + Real.pi) + sr.re + K / 8 - s.re) hG
  refine ⟨sr - s, max N (max N₀ 2), K, ?_, hK, ?_⟩
  · exact lt_of_lt_of_le hN (le_max_left _ _)
  · intro R hR H hRH z hz
    have hRN : N ≤ R := le_trans (le_max_left _ _) hR
    have hRN₀ : N₀ ≤ R := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hR)
    have hR2 : (2 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hR)
    obtain ⟨v, _hv1, hv2, hv3⟩ := hmain R hRN H hRH z hz
    set err : ℝ := K * (1 + H) * (1 + Real.log R) / R with herrdef
    set A : ℂ := Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z) + sr with hAdef
    have hv3' : ‖v - A‖ ≤ err := by rw [hAdef, herrdef]; exact hv3
    -- `Re v` is bounded above by the model level plus the (small) error
    have hre_le : v.re ≤ A.re + err := by
      have h1 : |v.re - A.re| ≤ ‖v - A‖ := by
        have h := Complex.abs_re_le_norm (v - A)
        rwa [Complex.sub_re] at h
      have h3 := (abs_le.mp (le_trans h1 hv3')).2
      linarith
    -- the error is at most `(K/8)(1 + log R)`
    have herr : err ≤ K / 8 * (1 + Real.log R) := by
      rw [herrdef]
      have hRpos : 0 < R := by linarith
      have hlogR : 0 ≤ 1 + Real.log R := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ R)
        linarith
      have hratio : (1 + H) / R ≤ 1 / 8 := by
        rw [div_le_iff₀ hRpos]
        linarith
      have hstep : (1 + H) / R * (1 + Real.log R) ≤ 1 / 8 * (1 + Real.log R) :=
        mul_le_mul_of_nonneg_right hratio hlogR
      calc K * (1 + H) * (1 + Real.log R) / R
          = K * ((1 + H) / R * (1 + Real.log R)) := by rw [mul_div_assoc]; ring
        _ ≤ K * (1 / 8 * (1 + Real.log R)) := mul_le_mul_of_nonneg_left hstep hK
        _ = K / 8 * (1 + Real.log R) := by ring
    -- the model level itself is far to the left
    have happ := Work.FlowerGlue2.approxCoordRep_woutG_le P hR2 hRH hz
    have hA : A.re ≤ -R + ‖P.κ c₀‖ * (Real.log 2 + Real.log R + Real.pi) + sr.re := by
      rw [hAdef, Complex.add_re]
      linarith
    have hlog := hN₀ R hRN₀
    refine ⟨v - s, ?_, ?_, ?_⟩
    · -- `Re (v - s) < -R/2`
      rw [Complex.sub_re]
      nlinarith [hre_le, hA, herr, hlog]
    · -- `Ψ ((v - s) + s) = z`
      change Ψ ((v - s) + s) = z
      have hvs : (v - s) + s = v := by ring
      rw [hvs]; exact hv2
    · -- the shifted level is close to the shifted model level
      have heq : (v - s) - (Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z) + (sr - s))
          = v - A := by
        rw [hAdef]; ring
      rw [heq]; exact hv3'

end Work.FlowerGlue2

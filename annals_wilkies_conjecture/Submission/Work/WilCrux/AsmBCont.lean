import Mathlib
import Submission.Work.WilCrux.C1AsmDefs
import Submission.Work.WilCrux.fibreFderivFamFun
import Submission.Work.WilCrux.clm_norm_le_sum_eval

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCrux

/-!
## `Work.WilCrux.AsmBCont`

Given a family `G : ℝ^a → ℝ^b → ℝ` whose uncurried form `famFun G` is `C¹` at every point
`(w, z)` with `w ∈ Q6`, `z ≠ 0`, `‖z‖ < r0` (`hoff`), and given that for `w` near `w₀ ∈ Q6` the
`z`-derivative of the slice `G w` barely moves between `z = 0` and small `z ≠ 0` (`hz`), the map
`w ↦ fderiv ℝ (G w) 0` is continuous within `Q6` at `w₀`.

The proof fixes, for a given `ε`, a small nonzero `z₁` and splits

`B(w) - B(w₀) = (B(w) - A(w)) + (A(w) - A(w₀)) + (A(w₀) - B(w₀))`,

where `A(w) = (fderiv ℝ (G w) z₁) (Pi.single j 1)` and `B(w) = (fderiv ℝ (G w) 0) (Pi.single j 1)`.
The outer two terms are small by `hz`; the middle term is continuous in `w` because, by the chain
rule, `A(w)` is the `j`-th fibre partial of `famFun G` at `(w, z₁)`, and `famFun G` is `C¹` there
(`hoff`), so its derivative depends continuously on `w`.  Assembling the finitely many
components gives continuity of the `ContinuousLinearMap`-valued map, via the norm bound
`‖L‖ ≤ ∑ j ‖L (Pi.single j 1)‖` on `(Fin b → ℝ) →L[ℝ] ℝ`.
-/

theorem AsmBCont {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q6 : Set (Fin a → ℝ)) (r0 : ℝ) (hr0 : 0 < r0)
    (hoff : ∀ w ∈ Q6, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (hz : ∀ w₀ ∈ Q6, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε) :
    ∀ w₀ ∈ Q6, ContinuousWithinAt (fun w => fderiv ℝ (G w) 0) Q6 w₀ := by
  intro w₀ hw₀
  -- Componentwise continuity of the evaluation functionals on the standard basis of `ℝ^b`.
  have hmain : ∀ j : Fin b, Filter.Tendsto (fun w => (fderiv ℝ (G w) 0) (Pi.single j (1:ℝ)))
      (𝓝[Q6] w₀) (𝓝 ((fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ)))) := by
    intro j
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨η, hηpos, hη⟩ := hz w₀ hw₀ (ε/3) (by linarith)
    -- a nonzero fibre direction of length `< η` and `< r0`
    set s : ℝ := min η r0 / 2 with hs
    have hs_pos : 0 < s := by rw [hs]; have := lt_min hηpos hr0; linarith
    have hs_lt_η : s < η := by rw [hs]; have := min_le_left η r0; linarith
    have hs_lt_r0 : s < r0 := by rw [hs]; have := min_le_right η r0; linarith
    set z₁ : Fin b → ℝ := Pi.single j s with hz₁
    have hz₁_ne : z₁ ≠ 0 := by
      rw [hz₁]; intro h
      have hc := congr_fun h j
      rw [Pi.single_eq_same, Pi.zero_apply] at hc
      exact absurd hc (ne_of_gt hs_pos)
    have hz₁_norm : ‖z₁‖ = s := by rw [hz₁, Pi.norm_single, Real.norm_eq_abs, abs_of_pos hs_pos]
    have hz₁_lt_η : ‖z₁‖ < η := by rw [hz₁_norm]; exact hs_lt_η
    have hz₁_lt_r0 : ‖z₁‖ < r0 := by rw [hz₁_norm]; exact hs_lt_r0
    -- continuity in `w` of the off-sheet `j`-th fibre partial, as a function of the point
    have hAz : ContinuousWithinAt (fun w => (fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))) Q6 w₀ := by
      have hcd : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w₀ z₁) :=
        hoff w₀ hw₀ z₁ hz₁_ne hz₁_lt_r0
      have hcfd : ContinuousAt (fderiv ℝ (Work.WilG4c.famFun G)) (Fin.append w₀ z₁) :=
        hcd.continuousAt_fderiv (by norm_num)
      have hφ : ContinuousAt (fun w : Fin a → ℝ => Fin.append w z₁) w₀ := by
        rw [show (fun w : Fin a → ℝ => Fin.append w z₁)
              = fun w => parIncl a b w + fibIncl a b z₁ from
            funext fun w => append_eq_parIncl_add_fibIncl a b w z₁]
        exact ((parIncl a b).continuous.continuousAt).add continuousAt_const
      have hcomp : ContinuousAt (fun w => fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₁)) w₀ :=
        ContinuousAt.comp hcfd hφ
      have hfinal : ContinuousAt (fun w =>
          (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₁)) (Fin.append 0 (Pi.single j (1:ℝ)))) w₀ :=
        hcomp.clm_apply continuousAt_const
      -- the fibre partial of `famFun G` is the slice derivative along `z₁`
      have hev : (fun w => (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₁))
            (Fin.append 0 (Pi.single j (1:ℝ))))
          =ᶠ[𝓝[Q6] w₀] (fun w => (fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))) := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact fibreFderivFamFun G w z₁ (Pi.single j (1:ℝ))
          ((hoff w hw z₁ hz₁_ne hz₁_lt_r0).differentiableAt (by norm_num))
      have hval : (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w₀ z₁))
            (Fin.append 0 (Pi.single j (1:ℝ)))
          = (fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ)) :=
        fibreFderivFamFun G w₀ z₁ (Pi.single j (1:ℝ))
          ((hoff w₀ hw₀ z₁ hz₁_ne hz₁_lt_r0).differentiableAt (by norm_num))
      have hthis : Filter.Tendsto
          (fun w => (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z₁))
            (Fin.append 0 (Pi.single j (1:ℝ))))
          (𝓝[Q6] w₀) (𝓝 ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ)))) := by
        rw [← hval]; exact hfinal.continuousWithinAt
      exact Filter.Tendsto.congr' hev hthis
    have h1 : ∀ᶠ w in 𝓝[Q6] w₀, dist w w₀ < η :=
      nhdsWithin_le_nhds (a := w₀) (s := Q6) (Metric.ball_mem_nhds w₀ hηpos)
    have h2 : ∀ᶠ w in 𝓝[Q6] w₀,
        dist ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)))
          ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ))) < ε/3 := by
      have hAzT : Filter.Tendsto (fun w => (fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))) (𝓝[Q6] w₀)
          (𝓝 ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ)))) := hAz
      exact (Metric.tendsto_nhds).mp hAzT (ε/3) (by linarith)
    have h3 : ‖fderiv ℝ (G w₀) z₁ - fderiv ℝ (G w₀) 0‖ < ε/3 :=
      hη w₀ z₁ (by rw [dist_self]; exact hηpos) hz₁_ne hz₁_lt_η
    filter_upwards [h1, h2] with w hw1 hw2
    have hU : ‖fderiv ℝ (G w) z₁ - fderiv ℝ (G w) 0‖ < ε/3 := hη w z₁ hw1 hz₁_ne hz₁_lt_η
    have hBA : ‖(fderiv ℝ (G w) 0) (Pi.single j (1:ℝ))
        - (fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))‖ < ε/3 := by
      have h1' : (fderiv ℝ (G w) 0) (Pi.single j (1:ℝ))
            - (fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))
          = (fderiv ℝ (G w) 0 - fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)) := by simp
      rw [h1']
      calc ‖(fderiv ℝ (G w) 0 - fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))‖
          ≤ ‖fderiv ℝ (G w) 0 - fderiv ℝ (G w) z₁‖ * ‖(Pi.single j (1:ℝ) : Fin b → ℝ)‖ :=
            (fderiv ℝ (G w) 0 - fderiv ℝ (G w) z₁).le_opNorm _
        _ = ‖fderiv ℝ (G w) 0 - fderiv ℝ (G w) z₁‖ := by
            rw [Pi.norm_single, norm_one, mul_one]
        _ = ‖fderiv ℝ (G w) z₁ - fderiv ℝ (G w) 0‖ := norm_sub_rev _ _
        _ < ε/3 := hU
    have hA0B0 : ‖(fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ))
        - (fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))‖ < ε/3 := by
      have h1' : (fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ))
            - (fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))
          = (fderiv ℝ (G w₀) z₁ - fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ)) := by simp
      rw [h1']
      calc ‖(fderiv ℝ (G w₀) z₁ - fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))‖
          ≤ ‖fderiv ℝ (G w₀) z₁ - fderiv ℝ (G w₀) 0‖ * ‖(Pi.single j (1:ℝ) : Fin b → ℝ)‖ :=
            (fderiv ℝ (G w₀) z₁ - fderiv ℝ (G w₀) 0).le_opNorm _
        _ = ‖fderiv ℝ (G w₀) z₁ - fderiv ℝ (G w₀) 0‖ := by
            rw [Pi.norm_single, norm_one, mul_one]
        _ < ε/3 := h3
    have hBAd : dist ((fderiv ℝ (G w) 0) (Pi.single j (1:ℝ)))
        ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ))) < ε/3 := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hBA
    have hA0B0d : dist ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ)))
        ((fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))) < ε/3 := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hA0B0
    calc dist ((fderiv ℝ (G w) 0) (Pi.single j (1:ℝ)))
          ((fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ)))
        ≤ dist ((fderiv ℝ (G w) 0) (Pi.single j (1:ℝ)))
            ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)))
          + dist ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)))
            ((fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))) := dist_triangle _ _ _
      _ ≤ dist ((fderiv ℝ (G w) 0) (Pi.single j (1:ℝ)))
            ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)))
          + (dist ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)))
              ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ)))
            + dist ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ)))
              ((fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ)))) := by
          linarith [dist_triangle ((fderiv ℝ (G w) z₁) (Pi.single j (1:ℝ)))
            ((fderiv ℝ (G w₀) z₁) (Pi.single j (1:ℝ))) ((fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ)))]
      _ < ε/3 + (ε/3 + ε/3) := by linarith
      _ = ε := by ring
  -- Assemble: the norm of a functional is controlled by its values on the standard basis.
  have hf : ∀ j : Fin b, Filter.Tendsto
      (fun w => ‖(fderiv ℝ (G w) 0 - fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))‖)
      (𝓝[Q6] w₀) (𝓝 0) := by
    intro j
    have := (tendsto_iff_norm_sub_tendsto_zero).mp (hmain j)
    simpa using this
  have hsum : Filter.Tendsto
      (fun w => ∑ j : Fin b, ‖(fderiv ℝ (G w) 0 - fderiv ℝ (G w₀) 0) (Pi.single j (1:ℝ))‖)
      (𝓝[Q6] w₀) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin b)) (fun j _ => hf j)
    simpa using h
  have hsqueeze : Filter.Tendsto (fun w => ‖fderiv ℝ (G w) 0 - fderiv ℝ (G w₀) 0‖)
      (𝓝[Q6] w₀) (𝓝 0) :=
    squeeze_zero (fun w => norm_nonneg _) (fun w => clm_norm_le_sum_eval b _) hsum
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hsqueeze

end Work.WilCrux

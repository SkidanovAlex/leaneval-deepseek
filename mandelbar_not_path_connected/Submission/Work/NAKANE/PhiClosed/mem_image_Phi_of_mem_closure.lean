import Mathlib
import Submission.Work.NAKANE.PotentialTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.PhiClosed

open Classical Filter Set
open scoped Topology ComplexConjugate

/-- **`Φ '' Mbᶜ` is closed inside the exterior disc.** Here `Mb` is the mandelbar, `Mbᶜ = {c | c ∉ Mb}`, and `Φ = Work.ParamRays.Phi`, with `‖Φ c‖ = exp (2 * G_c 0)` off the mandelbar.

The proof is an elementary compactness argument.  Let `w` be a limit point of `Φ '' Mbᶜ` with
`1 < ‖w‖` and pick `cₙ ∉ Mb` with `Φ cₙ → w`.  Since `‖Φ c‖ ≥ ‖c‖/2` for `‖c‖` large
(`Work.NAKANE.Phi_lower_bound_atTop`), the sequence `cₙ` is bounded; a bounded sequence in `ℂ`
has a convergent subsequence `c_{φ(k)} → a`.  If `a ∈ Mb` then `‖Φ c‖ → 1` along `c → a` outside
`Mb` (`Work.NAKANE.tendsto_norm_Phi_near_Mb`), contradicting `‖Φ c_{φ(k)}‖ → ‖w‖ > 1`; hence
`a ∉ Mb`, and continuity of `Φ` on `Mbᶜ` (`Work.NAKANE.continuousOn_Phi`) gives `Φ a = w`. -/
theorem mem_image_Phi_of_mem_closure {w : ℂ}
    (hw : w ∈ closure (Work.ParamRays.Phi '' {c : ℂ | c ∉ LeanEval.ComplexAnalysis.Mandelbar}))
    (hw1 : 1 < ‖w‖) :
    w ∈ Work.ParamRays.Phi '' {c : ℂ | c ∉ LeanEval.ComplexAnalysis.Mandelbar} := by
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.mp hw
  choose c hcmb hPhi using huS
  -- the cocompact lower bound on `‖Φ‖`
  have hcob : ∀ᶠ x : ℂ in cocompact ℂ, ‖x‖ / 2 ≤ ‖Work.ParamRays.Phi x‖ :=
    Work.NAKANE.Phi_lower_bound_atTop
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.mp hcob
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  have hbound : ∀ x : ℂ, R < ‖x‖ → ‖x‖ / 2 ≤ ‖Work.ParamRays.Phi x‖ := by
    intro x hx
    apply hKsub
    simp only [Set.mem_compl_iff]
    intro hmem
    have := hR x hmem
    linarith
  -- eventually `‖u n - w‖ < 1`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hu.eventually (Metric.ball_mem_nhds w one_pos))
  have hN' : ∀ n ≥ N, ‖u n - w‖ < 1 := by
    intro n hn
    have := hN n hn
    rwa [dist_eq_norm] at this
  -- the tail of `(c n)` is bounded
  let d : ℕ → ℂ := fun n => c (n + N)
  have hdmem : ∀ n, d n ∈ Metric.closedBall 0 (max R (2 * (‖w‖ + 1))) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖d n‖ ≤ max R (2 * (‖w‖ + 1))
    by_cases hRn : ‖d n‖ ≤ R
    · exact le_trans hRn (le_max_left _ _)
    · rw [not_le] at hRn
      have hb := hbound (d n) hRn
      have hphid : Work.ParamRays.Phi (d n) = u (n + N) := hPhi (n + N)
      rw [hphid] at hb
      have huN := hN' (n + N) (Nat.le_add_left N n)
      have hnorm : ‖u (n + N)‖ < ‖w‖ + 1 := by
        have h1 := norm_sub_norm_le (u (n + N)) w
        linarith
      have : ‖d n‖ < 2 * (‖w‖ + 1) := by linarith
      exact le_trans this.le (le_max_right _ _)
  -- extract a convergent subsequence
  obtain ⟨a, hamem, φ, hφmono, hφtend⟩ :=
    (isCompact_closedBall (0 : ℂ) (max R (2 * (‖w‖ + 1)))).tendsto_subseq hdmem
  have hφN : Tendsto (fun k => φ k + N) atTop atTop :=
    (tendsto_add_atTop_nat N).comp hφmono.tendsto_atTop
  have hsub : Tendsto (fun k => u (φ k + N)) atTop (nhds w) := hu.comp hφN
  have hlimPhi : Tendsto (fun k => Work.ParamRays.Phi ((d ∘ φ) k)) atTop (nhds w) :=
    hsub.congr' (Filter.Eventually.of_forall fun k => (hPhi (φ k + N)).symm)
  -- the limit point is outside the mandelbar
  have haMb : a ∉ LeanEval.ComplexAnalysis.Mandelbar := by
    intro ha
    have hε : 0 < (‖w‖ - 1) / 2 := by linarith
    obtain ⟨δ, hδpos, hδ'⟩ := Work.NAKANE.tendsto_norm_Phi_near_Mb ha hε
    have hev1 : ∀ᶠ k in atTop, dist ((d ∘ φ) k) a < δ :=
      hφtend.eventually (Metric.ball_mem_nhds a hδpos)
    have hev2 : ∀ᶠ k in atTop, (d ∘ φ) k ∉ LeanEval.ComplexAnalysis.Mandelbar :=
      Filter.Eventually.of_forall fun k => hcmb (φ k + N)
    have hev3 : ∀ᶠ k in atTop, ‖Work.ParamRays.Phi ((d ∘ φ) k)‖ < 1 + (‖w‖ - 1) / 2 := by
      filter_upwards [hev1, hev2] with k hk1 hk2
      exact hδ' ((d ∘ φ) k) hk1 hk2
    have hev4 : ∀ᶠ k in atTop, 1 + (‖w‖ - 1) / 2 < ‖Work.ParamRays.Phi ((d ∘ φ) k)‖ :=
      hlimPhi.norm.eventually
        (isOpen_Ioi.mem_nhds (show 1 + (‖w‖ - 1) / 2 < ‖w‖ by linarith))
    obtain ⟨k, hk3, hk4⟩ := (hev3.and hev4).exists
    linarith
  -- continuity on `Mbᶜ` identifies the limit
  have hca : ContinuousAt Work.ParamRays.Phi a :=
    Work.NAKANE.continuousOn_Phi.continuousAt
      ((Work.ParamRays.isClosed_mandelbar).isOpen_compl.mem_nhds haMb)
  have hcomp : Tendsto (fun k => Work.ParamRays.Phi ((d ∘ φ) k)) atTop
      (nhds (Work.ParamRays.Phi a)) := hca.tendsto.comp hφtend
  exact ⟨a, haMb, tendsto_nhds_unique hcomp hlimPhi⟩

end Work.NAKANE.PhiClosed

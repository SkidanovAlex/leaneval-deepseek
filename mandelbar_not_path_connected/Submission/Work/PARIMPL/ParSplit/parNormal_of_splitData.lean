/-
# `Work.PARIMPL.ParSplit.parNormal_of_splitData` — assembling the parameter normal form

The assembly of `NOTES_ASSEMBLY.md` §4 and `NOTES_WALL.md`: from a `SplitData d`
(`ParSplit.Split`, the splitting of the parabolic fixed point of the second return map
`F c = (T_c)^[10]` into two simple fixed points `S.m c ± S.E c/2`) it produces the parameter normal
form `ParNormal d` of Hubbard–Schleicher Prop. 4.1, uniform in `c` on a ball around `c₀`.

The fields of `ParNormal` are filled as follows.

* `m := S.m`, `s := parS S`, `a := parA S`, `a2 := parA2 S`, `h := parHgerm S`, `h1 := parH1 S`,
  `κ := parKappa S`, `lam := parLamReal S`, and `A`, `r` from `parHgerm_bounds`; the parameter
  ball `ρ₀` is the minimum of all the balls produced by the individual lemmas.
* `s_ne`/`a_sq`/`m₀`/`a2₀`/`κ_eq` come from `parChart_algebra` (`m₀` is `SplitData.m₀`, `a2₀` from
  `Gc S c₀ = (S.E c₀ / 2)² = 0`); `conj` from `parGerm_conj`; `a_eq`/`lam_pos`/`swap`/`fix` from
  `parExchange`; `bounds` from `parHgerm_bounds`.
* The continuity fields come from the *component* lemmas of `parChart_continuity`
  (`continuousOn_parS`, `continuousOn_parA2`, `continuousOn_parH1`, `continuousOn_parKappa`,
  `continuousOn_parHgerm_zero`, `continuousOn_parHgerm`), applied with the branch margin
  `0 < (chartF S c).re`, which is supplied here directly as follows: off the collision locus
  `E c = 0` the phase inequality gives `17/32 ≤ (parU0 S c)².re = (chartF S c).re`
  (`parU0_sq_re_lower`, from `phase_of_split`), while *on* the collision locus the chart constant
  is exactly one, `parU0 S c = 1` (`parU0_eq_one_of_wall`, fed by the double-root count
  `Hp_double_root_count`), so that `chartF S c = 1`.
-/
import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.ParSplit.Split
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.parChartSq
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parGerm_conj
import Submission.Work.PARIMPL.ParSplit.parExchange
import Submission.Work.PARIMPL.ParSplit.parChart_continuity
import Submission.Work.PARIMPL.ParSplit.parU0_sq_re_lower
import Submission.Work.PARIMPL.ParSplit.parU0_eq_one_of_wall
import Submission.Work.PARIMPL.ParSplit.Hp_double_root_count
import Submission.Work.PARIMPL.ParSplit.parHgerm_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

theorem parNormal_of_splitData {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    Nonempty (Work.PARIMPL.ParNormal d) := by
  obtain ⟨ρa, hρa0, hρaρ, halg⟩ := parChart_algebra S
  obtain ⟨ρg, hρg0, hρgρ, hgerm⟩ := parGerm_conj S
  obtain ⟨ρe, hρe0, hρeρ, he⟩ := parExchange S
  obtain ⟨ρb, hρb0, hρbρ, r, hr0, A, hA0, hbnd⟩ := parHgerm_bounds S
  obtain ⟨ρr, hρr0, hρrρ, hrho⟩ := parRho_ne_zero S
  obtain ⟨ρl, hρl0, hρlρ, hlam⟩ := parLam_ne_zero S
  obtain ⟨ρw, hρw0, hρwρ, hwall⟩ := parLam_sigma_norm_Gc S
  obtain ⟨ρq, hρq0, hρqρ, hsq⟩ := parU0_sq_re_lower S
  obtain ⟨ρn, hρn0, hρnρ, hcount⟩ := Hp_double_root_count S
  obtain ⟨ρu, hρu0, hρuρ, hwallval⟩ := parU0_eq_one_of_wall S
  -- the parameter ball is the minimum of all the balls above
  set ρ₀ : ℝ := min ρa (min ρg (min ρe (min ρb (min ρr (min ρl (min ρw (min ρq (min ρn ρu))))))))
    with hρ₀
  have hρ₀pos : 0 < ρ₀ :=
    lt_min hρa0 (lt_min hρg0 (lt_min hρe0 (lt_min hρb0 (lt_min hρr0 (lt_min hρl0
      (lt_min hρw0 (lt_min hρq0 (lt_min hρn0 hρu0))))))))
  have hle_a : ρ₀ ≤ ρa := min_le_left _ _
  have hle_g : ρ₀ ≤ ρg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hle_e : ρ₀ ≤ ρe :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle_b : ρ₀ ≤ ρb :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hle_r : ρ₀ ≤ ρr :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hle_l : ρ₀ ≤ ρl :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hle_w : ρ₀ ≤ ρw :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _))))))
  have hle_q : ρ₀ ≤ ρq :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))))
  have hle_n : ρ₀ ≤ ρn :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))))
  have hle_u : ρ₀ ≤ ρu :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))))))
  have hρ₀ρ : ρ₀ ≤ S.ρ := le_trans hle_a hρaρ
  -- the branch-cut margin for the principal square root
  have hre : ∀ c ∈ Metric.ball c₀ ρ₀, 0 < (chartF S c).re := by
    intro c hc
    by_cases hE : S.E c = 0
    · have h1 : parU0 S c = 1 :=
        hwallval c (Metric.ball_subset_ball hle_u hc) hE
          (hcount c (Metric.ball_subset_ball hle_n hc) hE)
      have h2 : chartF S c = 1 := by rw [chartF_eq_parU0_sq, h1]; norm_num
      rw [h2]; norm_num
    · have h3 := hsq c (Metric.ball_subset_ball hle_q hc) hE
      rw [← chartF_eq_parU0_sq] at h3
      linarith
  have hrho' : ∀ c ∈ Metric.ball c₀ ρ₀, parRho S c ≠ 0 :=
    fun c hc => hrho c (Metric.ball_subset_ball hle_r hc)
  have hlam' : ∀ c ∈ Metric.ball c₀ ρ₀, parLam S c ≠ 0 :=
    fun c hc => hlam c (Metric.ball_subset_ball hle_l hc)
  have hwall' : ∀ c ∈ Metric.ball c₀ ρ₀,
      parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c :=
    fun c hc => hwall c (Metric.ball_subset_ball hle_w hc)
  have hS : ContinuousOn (parS S) (Metric.ball c₀ ρ₀) :=
    continuousOn_parS S hρ₀ρ hrho' hre
  have hA2 : ContinuousOn (parA2 S) (Metric.ball c₀ ρ₀) :=
    continuousOn_parA2 S hρ₀ρ hlam' hwall'
  refine ⟨{ ρ₀ := ρ₀
            hρ₀ := hρ₀pos
            r := r
            hr := hr0
            m := S.m
            s := parS S
            a := parA S
            a2 := parA2 S
            h := parHgerm S
            h1 := parH1 S
            κ := parKappa S
            lam := parLamReal S
            A := A
            hA := hA0
            cont_m := S.cont_m.mono (Metric.ball_subset_ball hρ₀ρ)
            cont_s := hS
            cont_a2 := hA2
            cont_h1 := continuousOn_parH1 S hρ₀ρ hS
            cont_κ := continuousOn_parKappa S hρ₀ρ hS hrho' hre
            cont_τ := continuousOn_parHgerm_zero S hρ₀ρ hS
            cont_h := (continuousOn_parHgerm S hρ₀ρ hS).mono
              (Set.prod_mono Subset.rfl (Set.subset_univ _))
            s_ne := fun c hc => (halg c (Metric.ball_subset_ball hle_a hc)).1
            a_sq := fun c hc => (halg c (Metric.ball_subset_ball hle_a hc)).2.2.1
            m₀ := S.m₀
            a2₀ := by simp [parA2, Gc, S.E₀]
            κ_eq := ?_
            conj := ?_
            bounds := fun c hc => hbnd c (Metric.ball_subset_ball hle_b hc)
            a_eq := fun c hc h2 => (he c (Metric.ball_subset_ball hle_e hc)).1 h2
            lam_pos := fun c hc h2 => (he c (Metric.ball_subset_ball hle_e hc)).2.1 h2
            swap := fun c hc h2 => (he c (Metric.ball_subset_ball hle_e hc)).2.2.1 h2
            fix := fun c hc h2 => (he c (Metric.ball_subset_ball hle_e hc)).2.2.2 h2 }⟩
  · -- `κ_eq`
    intro c hc
    have hτ : ‖parHgerm S c 0‖ = 1 := (hbnd c (Metric.ball_subset_ball hle_b hc)).2.1
    refine ⟨fun h0 => by rw [h0, norm_zero] at hτ; norm_num at hτ, rfl⟩
  · -- `conj`
    intro c hc ζ hζ
    have h := hgerm c (Metric.ball_subset_ball hle_g hc) ζ
    simpa only [Ft, Work.Implosion.normalForm] using h

end Work.PARIMPL.ParSplit

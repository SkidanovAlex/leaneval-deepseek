/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.swap_fix_open` — the swap locus and the fix locus are open

Let `S : SplitData d` be a splitting datum at a root-parabolic parameter `c₀`: the two split fixed
points of the second return map `Work.EL.F c = (T_c)^[10]` are `S.m c ± S.E c/2`, and they are the
only fixed points of `Work.EL.F c` in the dynamical disc `ball d.z₁ S.R`.  Let `ρ' ≤ S.ρ` be a
radius on which the midpoint `S.m` and the half-difference `S.E/2` stay well inside that disc
(`hsmall`).

The antiholomorphic square root `gtc c = (T_c)^[5]` of `Work.EL.F c` permutes the two split fixed
points (`SplitData.swap_or_fix_of_split`); the *character* of that permutation — **swap**
(`gtc c (m c + E c/2) = m c - E c/2`) or **fix** (`gtc c (m c + E c/2) = m c + E c/2`) — is
therefore locally constant off the collision locus `{E = 0}`, where the two points coincide.  This
module proves that the two loci

  `{c ∈ ball c₀ ρ' : E c ≠ 0, gtc c (m c + E c/2) = m c - E c/2}`   (swap)  and
  `{c ∈ ball c₀ ρ' : E c ≠ 0, gtc c (m c + E c/2) = m c + E c/2}`   (fix)

are **open**.  Hence the sign of the dichotomy is a locally constant function
`σ : ball c₀ ρ' \ {E = 0} → {±1}`, which is what the assembly of `ParNormal` uses (`swap` on the
implosion side `a₂ < 0`, `fix` on the other side).

The statement does *not* assume that the image `gtc c (m c + E c/2)` lies in the disc
`ball z₁ S.R` for *every* `c` of the ball (that is the global smallness statement
`ParSplit.g_mem_of_split`, available near `c₀`).  Openness is a *local* statement: at a point `c`
of one of the two loci the image is a split fixed point *inside* the disc, so — the disc being
open and `c ↦ gtc c (m c + E c/2)` continuous — the same is true on a neighbourhood of `c`, and
there the dichotomy is available.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.ParSplit.Split
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.splitPair_exists
import Submission.Work.PARIMPL.ParSplit.BuildSplit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## The local swap/fix dichotomy -/

/-- **The dichotomy is local.**  If the image `Ψ c = gtc c (m c + E c/2)` of the first split point
is one of the two split fixed points (i.e. `Ψ c = m c - E c/2` or `Ψ c = m c + E c/2`) and the
midpoint and half-difference are small (`hsmall`, so that both split points lie in the dynamical
disc `ball d.z₁ S.R`), then *the same alternative holds on a whole ball of parameters around
`c`*: the image stays in the open disc, hence is a fixed point of `F c'` inside the disc, hence is
one of the two split points there.

This is the only place where the local constancy of the character of `gtc` is used. -/
theorem gtc_split_local_dichotomy {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) {ρ' : ℝ} (hρ'ρ : ρ' ≤ S.ρ)
    (hsmall : ∀ c ∈ Metric.ball c₀ ρ', dist (S.m c) d.z₁ + ‖S.E c‖ / 2 < S.R)
    {c : ℂ} (hc : c ∈ Metric.ball c₀ ρ')
    (hcase : gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = 0 ∨
      gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = S.E c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c' ∈ Metric.ball c₀ ρ', dist c' c < ε →
      (gtc c' (S.m c' + S.E c' / 2) - (S.m c' - S.E c' / 2) = 0 ∨
        gtc c' (S.m c' + S.E c' / 2) - (S.m c' - S.E c' / 2) = S.E c') := by
  have hUsub : Metric.ball c₀ ρ' ⊆ Metric.ball c₀ S.ρ := Metric.ball_subset_ball hρ'ρ
  have hcm : ContinuousOn S.m (Metric.ball c₀ ρ') := S.cont_m.mono hUsub
  have hcE : ContinuousOn S.E (Metric.ball c₀ ρ') := S.cont_E.mono hUsub
  have hpair : ContinuousOn (fun c : ℂ => (c, S.m c + S.E c / 2)) (Metric.ball c₀ ρ') :=
    (continuous_id.continuousOn).prodMk (hcm.add (hcE.div_const 2))
  have hΨcont : ContinuousOn (fun c : ℂ => gtc c (S.m c + S.E c / 2)) (Metric.ball c₀ ρ') :=
    continuous_gtc_prod.comp_continuousOn
      (f := fun c : ℂ => (c, S.m c + S.E c / 2)) hpair
  have hΨmem : gtc c (S.m c + S.E c / 2) ∈ Metric.ball d.z₁ S.R := by
    rcases hcase with h | h
    · have h' : gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := sub_eq_zero.mp h
      rw [h']; exact S.fixed_sub_mem (hsmall c hc)
    · have h' : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 := by
        rw [sub_eq_iff_eq_add] at h
        rw [h]; ring
      rw [h']; exact S.fixed_add_mem (hsmall c hc)
  have hcont : ContinuousAt (fun c : ℂ => gtc c (S.m c + S.E c / 2)) c :=
    hΨcont.continuousAt (isOpen_ball.mem_nhds hc)
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp
    (hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hΨmem))
  refine ⟨ε, hε0, fun c' hc' hd => ?_⟩
  have hmem' : gtc c' (S.m c' + S.E c' / 2) ∈ Metric.ball d.z₁ S.R := hε hd
  rcases S.swap_or_fix_of_split (hUsub hc') hmem' with h | h
  · right; rw [h]; ring
  · left; rw [h]; ring

/-! ## The swap locus and the fix locus are open -/

theorem swap_fix_open {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (S : Work.PARIMPL.ParSplit.SplitData d) {ρ' : ℝ} (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ S.ρ)
    (hsmall : ∀ c ∈ Metric.ball c₀ ρ',
      dist (S.m c) d.z₁ + ‖S.E c‖ / 2 < S.R) :
    IsOpen (({c : ℂ | c ∈ Metric.ball c₀ ρ' ∧ S.E c ≠ 0}) ∩
        {c : ℂ | gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2}) ∧
      IsOpen (({c : ℂ | c ∈ Metric.ball c₀ ρ' ∧ S.E c ≠ 0}) ∩
        {c : ℂ | gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2}) := by
  have hUsub : Metric.ball c₀ ρ' ⊆ Metric.ball c₀ S.ρ := Metric.ball_subset_ball hρ'ρ
  have hcm : ContinuousOn S.m (Metric.ball c₀ ρ') := S.cont_m.mono hUsub
  have hcE : ContinuousOn S.E (Metric.ball c₀ ρ') := S.cont_E.mono hUsub
  have hpair : ContinuousOn (fun c : ℂ => (c, S.m c + S.E c / 2)) (Metric.ball c₀ ρ') :=
    (continuous_id.continuousOn).prodMk (hcm.add (hcE.div_const 2))
  have hΨcont : ContinuousOn (fun c : ℂ => gtc c (S.m c + S.E c / 2)) (Metric.ball c₀ ρ') :=
    continuous_gtc_prod.comp_continuousOn
      (f := fun c : ℂ => (c, S.m c + S.E c / 2)) hpair
  have hfcont : ContinuousOn (fun c : ℂ => gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2))
      (Metric.ball c₀ ρ') := hΨcont.sub (hcm.sub (hcE.div_const 2))
  have hgcont : ContinuousOn
      (fun c : ℂ => (gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2)) - S.E c)
      (Metric.ball c₀ ρ') := hfcont.sub hcE
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro c hc
    obtain ⟨⟨hcU, hcEne⟩, hΨeq⟩ := hc
    -- `Ψ c` is the *minus* split point
    have hsplit : gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := hΨeq
    have hcase : gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = 0 ∨
        gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = S.E c := by
      left; rw [hsplit]; ring
    obtain ⟨ε, hε0, hε⟩ := gtc_split_local_dichotomy S hρ'ρ hsmall hcU hcase
    have hΦ0 : gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = 0 := by
      rw [hsplit]; ring
    have hne : (gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2)) - S.E c ≠ 0 := by
      rw [hΦ0]
      simpa using hcEne
    have hN : ((Metric.ball c₀ ρ' ∩ Metric.ball c ε) ∩
        (Metric.ball c₀ ρ' ∩ S.E ⁻¹' {0}ᶜ) ∩
        (Metric.ball c₀ ρ' ∩
          (fun c' : ℂ => (gtc c' (S.m c' + S.E c' / 2) - (S.m c' - S.E c' / 2)) - S.E c')
            ⁻¹' {0}ᶜ)) ∈ 𝓝 c := by
      refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
      · exact (isOpen_ball.inter isOpen_ball).mem_nhds ⟨hcU, mem_ball_self hε0⟩
      · exact (hcE.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds
          ⟨hcU, by simpa using hcEne⟩
      · exact (hgcont.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds
          ⟨hcU, by simpa using hne⟩
    refine Filter.mem_of_superset hN ?_
    · rintro c' ⟨⟨⟨hc'U, hc'ball⟩, ⟨hc'U2, hc'E⟩⟩, ⟨hc'U3, hc'ne⟩⟩
      have hc'E' : S.E c' ≠ 0 := by simpa using hc'E
      have hc'ne' : (gtc c' (S.m c' + S.E c' / 2) - (S.m c' - S.E c' / 2)) - S.E c' ≠ 0 := by
        simpa using hc'ne
      rcases hε c' hc'U hc'ball with h | h
      · exact ⟨⟨hc'U2, hc'E'⟩, sub_eq_zero.mp h⟩
      · exact absurd (show (gtc c' (S.m c' + S.E c' / 2) -
            (S.m c' - S.E c' / 2)) - S.E c' = 0 by rw [h]; ring) hc'ne'
  · rw [isOpen_iff_mem_nhds]
    intro c hc
    obtain ⟨⟨hcU, hcEne⟩, hΨeq⟩ := hc
    -- `Ψ c` is the *plus* split point
    have hsplit : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 := hΨeq
    have hcase : gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = 0 ∨
        gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = S.E c := by
      right; rw [hsplit]; ring
    obtain ⟨ε, hε0, hε⟩ := gtc_split_local_dichotomy S hρ'ρ hsmall hcU hcase
    have hΦE : gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = S.E c := by
      rw [hsplit]; ring
    have hne : gtc c (S.m c + S.E c / 2) - (S.m c - S.E c / 2) ≠ 0 := by
      rw [hΦE]
      exact hcEne
    have hN : ((Metric.ball c₀ ρ' ∩ Metric.ball c ε) ∩
        (Metric.ball c₀ ρ' ∩ S.E ⁻¹' {0}ᶜ) ∩
        (Metric.ball c₀ ρ' ∩
          (fun c' : ℂ => gtc c' (S.m c' + S.E c' / 2) - (S.m c' - S.E c' / 2))
            ⁻¹' {0}ᶜ)) ∈ 𝓝 c := by
      refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
      · exact (isOpen_ball.inter isOpen_ball).mem_nhds ⟨hcU, mem_ball_self hε0⟩
      · exact (hcE.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds
          ⟨hcU, by simpa using hcEne⟩
      · exact (hfcont.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds
          ⟨hcU, by simpa using hne⟩
    refine Filter.mem_of_superset hN ?_
    · rintro c' ⟨⟨⟨hc'U, hc'ball⟩, ⟨hc'U2, hc'E⟩⟩, ⟨hc'U3, hc'f⟩⟩
      have hc'E' : S.E c' ≠ 0 := by simpa using hc'E
      have hc'f' : gtc c' (S.m c' + S.E c' / 2) - (S.m c' - S.E c' / 2) ≠ 0 := by
        simpa using hc'f
      rcases hε c' hc'U hc'ball with h | h
      · exact absurd h hc'f'
      · refine ⟨⟨hc'U2, hc'E'⟩, ?_⟩
        show gtc c' (S.m c' + S.E c' / 2) = S.m c' + S.E c' / 2
        rw [sub_eq_iff_eq_add] at h
        rw [h]; ring

end Work.PARIMPL.ParSplit

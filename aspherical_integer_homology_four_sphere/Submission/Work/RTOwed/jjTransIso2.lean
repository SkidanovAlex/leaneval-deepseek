/-
# The transition of two junction charts of one cusp is a smooth isometry of the polar model

`Work.RTOwed.jjTransIso2`: the transition of two junction charts `jChart a D v P`, `jChart a D v Q`
of the *same* cusp `v` is smooth and preserves the warped filling model `jLayer v`.

## The mathematics

Both charts have as value the *polar coordinate* `Θ_v` of the point of `M̂`: on the target of the
chart the inverse chart is the coordinate inclusion `jCoordM` (`jjTI_jChart_symm_apply`), and
`jCoordM` does not depend on the pinning data `(cU,k,W,kx,δ)` beyond the box conditions: on the
inner branch it is `a.incW v ∘ cuspInvInner` and on the collar branch `cuspCoordMTop ∘ polarToUHS`.
Consequently, for `q` in the source of the transition,

  `jCoordM (P) q = jCoordM (Q) (t q)`  (`jjTI_key`),

i.e. `q` and `t q` are two polar coordinates of the *same* point of the filling piece.  The fibres
of `jCoordM` are the orbits of the displacement lattice `jlVec v n m`
(`Work.RTOWed.jCoordM_fiber_inner`, `Work.RTOWed.jCoordM_fiber_outer` and the disjointness
`Work.RTOWed.jCoordM_fiber_mixed`), so `t q = q + jlVec v n m`.  Since `jlVec v N M` is bounded
below in the sup norm by `1/2000` unless `N = M = 0`
(`Work.RTOWed.jlVec_wOf_sq_bound`), the displacement `t q - q` is *locally constant*: `t` is, near
every point of its source, a translation, hence smooth with derivative the identity, and it
preserves the first coordinate `q 0` — which is all that the warped filling model `warpedModelA`
sees.

This file is self-contained: it proves the statement directly (the helper lemmas below are
deliberately local, so that the module depends only on the pinned fibre computations of
`Work.RTOWed`).
-/
import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.jCoordM_fiber_outer
import Submission.Work.RTOwed.jCoordM_fiber_inner
import Submission.Work.RTOwed.jCoordM_fiber_mixed
import Submission.Work.RTOwed.jlVec_wOf_sq_bound
import Submission.Work.RTOwed.cuspCoordMTop_fibre
import Submission.Work.RTOwed.jTransCollAux
import Submission.Work.RTOwed.polarToUHS_isOpenEmbedding

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function
open scoped Real InnerProductSpace

theorem jjTI_rCut_lt_jTop : Work.RTOwed.rCut < Work.RTOWed.jTop := by
  have h := Work.RTOwed.log_three_halves_lt
  rw [Work.RTOWed.jTop, Work.RTOwed.rCut, Work.Cusp.R0, Work.Cusp.betaMax]
  linarith

/-! ### The value of a junction chart -/

/-- **The target of a junction chart**: the box cut at the radius `rCut`. -/
theorem jjTI_jChart_target (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (R : Work.RTOwed.JPin a v) :
    (Work.RTOwed.jChart a D v R).target = Work.RTOwed.jBoxR a v R := by
  rw [Work.RTOwed.jChart, OpenPartialHomeomorph.trans_target,
    Work.RTOwed.jChartOf_target, OpenPartialHomeomorph.ofSet_target]
  ext y
  constructor
  · rintro ⟨hy, -⟩
    exact hy
  · intro hy
    refine ⟨hy, ?_⟩
    rw [Set.mem_preimage, OpenPartialHomeomorph.ofSet_symm]
    rw [congrFun (OpenPartialHomeomorph.ofSet_apply _ _) y]
    exact hy.1

/-- **The value of a junction chart is the polar coordinate of the point**: on the target `jBoxR` of
the chart, the inverse chart is the coordinate inclusion `jCoordM`. -/
theorem jjTI_jChart_symm_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (R : Work.RTOwed.JPin a v) (x : Work.Cusp.E4)
    (hx : x ∈ Work.RTOwed.jBoxR a v R)
    (hb : x ∈ Work.RTOwed.jBox v R.cU R.k R.W R.kx R.δ) :
    (Work.RTOwed.jChart a D v R).symm x
      = Work.RTOwed.jCoordM a v (D v) R.cU R.k R.W R.kx R.δ ⟨x, hb⟩ := by
  have hsrc : Work.RTOwed.jCoordM a v (D v) R.cU R.k R.W R.kx R.δ ⟨x, hb⟩
      ∈ (Work.RTOwed.jChart a D v R).source := by
    rw [Work.RTOwed.jChart_source]
    exact ⟨⟨x, hb⟩, hx, rfl⟩
  have hxmem : x ∈ (Work.RTOwed.jChart a D v R).target := by
    rwa [jjTI_jChart_target a D v R]
  have h1 : (Work.RTOwed.jChart a D v R) ((Work.RTOwed.jChart a D v R).invFun x) = x :=
    (Work.RTOwed.jChart a D v R).right_inv' hxmem
  have h2 : (Work.RTOwed.jChart a D v R)
      (Work.RTOwed.jCoordM a v (D v) R.cU R.k R.W R.kx R.δ ⟨x, hb⟩) = x :=
    Work.RTOwed.jChart_apply a D v R x hx
  exact (Work.RTOwed.jChart a D v R).injOn ((Work.RTOwed.jChart a D v R).map_target' hxmem)
    hsrc (by rw [h1, h2])

/-- **The two junction charts of one cusp describe the same point**: on the source of their
transition, the two coordinates are the values of the coordinate inclusion at the two points. -/
theorem jjTI_key (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : Work.RTOwed.JPin a v) {q : Work.Cusp.E4}
    (hq : q ∈ Work.RTOwed.jjTransSrc a D v P Q)
    (hqP : q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
    (hqQ : Work.RTOwed.jjTransMap a D v P Q q ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ) :
    Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hqP⟩
      = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ
          ⟨Work.RTOwed.jjTransMap a D v P Q q, hqQ⟩ := by
  have hsrc := hq
  rw [Work.RTOwed.jjTransSrc, OpenPartialHomeomorph.trans_source] at hsrc
  have hqR : q ∈ Work.RTOwed.jBoxR a v P := by
    rw [← jjTI_jChart_target a D v P]
    rw [← OpenPartialHomeomorph.symm_source]
    exact hsrc.1
  have hsymmP : (Work.RTOwed.jChart a D v P).symm q
      = Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hqP⟩ :=
    jjTI_jChart_symm_apply a D v P q hqR hqP
  have hsrcQ : (Work.RTOwed.jChart a D v P).symm q
      ∈ (Work.RTOwed.jChart a D v Q).source := hsrc.2
  have htgtQ : Work.RTOwed.jjTransMap a D v P Q q ∈ (Work.RTOwed.jChart a D v Q).target :=
    (Work.RTOwed.jChart a D v Q).map_source' hsrcQ
  have hqRQ : Work.RTOwed.jjTransMap a D v P Q q ∈ Work.RTOwed.jBoxR a v Q := by
    rwa [← jjTI_jChart_target a D v Q]
  have hsymmQ : (Work.RTOwed.jChart a D v Q).symm (Work.RTOwed.jjTransMap a D v P Q q)
      = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ
          ⟨Work.RTOwed.jjTransMap a D v P Q q, hqQ⟩ :=
    jjTI_jChart_symm_apply a D v Q _ hqRQ hqQ
  have hleft : (Work.RTOwed.jChart a D v Q).symm (Work.RTOwed.jjTransMap a D v P Q q)
      = (Work.RTOwed.jChart a D v P).symm q := by
    have h : (Work.RTOwed.jChart a D v Q) ((Work.RTOwed.jChart a D v P).symm q)
        = Work.RTOwed.jjTransMap a D v P Q q := by
      simp only [Work.RTOwed.jjTransMap]
    rw [← h]
    exact (Work.RTOwed.jChart a D v Q).left_inv' hsrcQ
  rw [← hsymmP, ← hsymmQ, hleft]

theorem jjTransIso2 (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : Work.RTOwed.JPin a v) :
    Work.RTOwed.TransIso2 (Work.RTOwed.jLayer v).model (Work.RTOwed.jLayer v).model
      (Work.RTOwed.jjTransMap a D v P Q) (Work.RTOwed.jjTransSrc a D v P Q) := by
  classical
  set t : Work.Cusp.E4 → Work.Cusp.E4 := Work.RTOwed.jjTransMap a D v P Q with ht
  set S : Set Work.Cusp.E4 := Work.RTOwed.jjTransSrc a D v P Q with hS
  have hte : ∀ q, t q = (Work.RTOwed.jChart a D v Q) ((Work.RTOwed.jChart a D v P).symm q) := by
    intro q
    rw [ht]
    rfl
  have hSe : S = ((Work.RTOwed.jChart a D v P).symm.trans (Work.RTOwed.jChart a D v Q)).source := by
    rw [hS]
    rfl
  have hcont : ContinuousOn t S := by
    rw [hSe]
    exact (((Work.RTOwed.jChart a D v P).symm).trans (Work.RTOwed.jChart a D v Q)).continuousOn_toFun
  have hopen : IsOpen S := by
    rw [hSe]
    exact OpenPartialHomeomorph.open_source _
  -- the chart at `q` and the chart at `t q` are the same point
  have hmemT : ∀ q ∈ S, q ∈ (Work.RTOwed.jChart a D v P).target ∧
      (Work.RTOwed.jChart a D v P).symm q ∈ (Work.RTOwed.jChart a D v Q).source := by
    intro q hq
    rw [hSe, OpenPartialHomeomorph.trans_source] at hq
    refine ⟨?_, hq.2⟩
    rw [← OpenPartialHomeomorph.symm_source]
    exact hq.1
  have hboxRP : ∀ q ∈ S, q ∈ Work.RTOwed.jBoxR a v P := by
    intro q hq
    rw [← jjTI_jChart_target a D v P]
    exact (hmemT q hq).1
  have hboxP : ∀ q ∈ S, q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ :=
    fun q hq => (hboxRP q hq).1
  have hboxRQ : ∀ q ∈ S, t q ∈ Work.RTOwed.jBoxR a v Q := by
    intro q hq
    have h : (Work.RTOwed.jChart a D v Q) ((Work.RTOwed.jChart a D v P).symm q)
        ∈ (Work.RTOwed.jChart a D v Q).target :=
      (Work.RTOwed.jChart a D v Q).map_source' (hmemT q hq).2
    rw [hte q, ← jjTI_jChart_target a D v Q]
    exact h
  have hboxQ : ∀ q ∈ S, t q ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ :=
    fun q hq => (hboxRQ q hq).1
  have hkeyval : ∀ q (hq : q ∈ S),
      Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hboxP q hq⟩
        = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨t q, hboxQ q hq⟩ :=
    fun q hq => jjTI_key a D v P Q hq (hboxP q hq) (hboxQ q hq)
  -- the four fibre computations of the coordinate inclusion
  have hfib_inner : ∀ (q r : Work.Cusp.E4)
      (hq : q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
      (hr : r ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ)
      (h0 : q 0 ≤ Work.Cusp.rJ) (h0' : r 0 ≤ Work.Cusp.rJ),
      Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
        = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hr⟩ →
      ∃ (n : ℤ) (m : Fin 2 → ℤ), r = q + Work.RTOwed.jlVec v n m := by
    intro q r hq hr h0 h0' h
    exact _root_.Work.RTOWed.jCoordM_fiber_inner a D v P Q hq hr h0 h0' h
  have hfib_outer_use : ∀ (q r : Work.Cusp.E4)
      (hqR : q ∈ Work.RTOwed.jBoxR a v P) (hrR : r ∈ Work.RTOwed.jBoxR a v Q)
      (h0 : Work.Cusp.rJ < q 0) (h0' : Work.Cusp.rJ < r 0),
      Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hqR.1⟩
        = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hrR.1⟩ →
      ∃ (n : ℤ) (m : Fin 2 → ℤ), r = q + Work.RTOwed.jlVec v n m := by
    intro q r hqR hrR h0 h0' h
    exact _root_.Work.RTOWed.jCoordM_fiber_outer a D v P Q hqR.1 hrR.1 h0 h0'
      (lt_trans hqR.2 jjTI_rCut_lt_jTop) (lt_trans hrR.2 jjTI_rCut_lt_jTop) h
  have hfib_mixed : ∀ (q r : Work.Cusp.E4)
      (hq : q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
      (hr : r ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ)
      (h0 : q 0 ≤ Work.Cusp.rJ) (h0' : Work.Cusp.rJ < r 0),
      Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
        ≠ Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hr⟩ := by
    intro q r hq hr h0 h0' h
    exact _root_.Work.RTOWed.jCoordM_fiber_mixed a D v P Q hq hr h0 h0' h
  have hfib_mixed' : ∀ (q r : Work.Cusp.E4)
      (hq : q ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ)
      (hr : r ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
      (h0 : q 0 ≤ Work.Cusp.rJ) (h0' : Work.Cusp.rJ < r 0),
      Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨q, hq⟩
        ≠ Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨r, hr⟩ := by
    intro q r hq hr h0 h0' h
    exact _root_.Work.RTOWed.jCoordM_fiber_mixed a D v Q P hq hr h0 h0' h
  -- the displacement of the transition is a lattice vector
  have hdisp : ∀ q ∈ S, ∃ (n : ℤ) (m : Fin 2 → ℤ), t q = q + Work.RTOwed.jlVec v n m := by
    intro q hq
    have hval := hkeyval q hq
    by_cases h0 : q 0 ≤ Work.Cusp.rJ
    · by_cases h0' : (t q) 0 ≤ Work.Cusp.rJ
      · exact hfib_inner q (t q) (hboxP q hq) (hboxQ q hq) h0 h0' hval
      · exact absurd hval (hfib_mixed q (t q) (hboxP q hq) (hboxQ q hq) h0 (not_le.mp h0'))
    · by_cases h0' : (t q) 0 ≤ Work.Cusp.rJ
      · exact absurd hval.symm
          (hfib_mixed' (t q) q (hboxQ q hq) (hboxP q hq) h0' (not_le.mp h0))
      · exact hfib_outer_use q (t q) (hboxRP q hq) (hboxRQ q hq) (not_le.mp h0)
          (not_le.mp h0') hval
  -- the lattice is discrete: a small lattice vector vanishes
  have hbound : ∀ (N : ℤ) (M : Fin 2 → ℤ),
      (∀ i : Fin 4, |(Work.RTOwed.jlVec v N M) i| < 1 / 2000) → N = 0 ∧ M = 0 := by
    intro N M h
    have h2 : |(Work.RTOwed.jlVec v N M) 2| < 1 / 2000 := h 2
    have h3 : |(Work.RTOwed.jlVec v N M) 3| < 1 / 2000 := h 3
    rw [Work.RTOwed.jlVec_apply_two] at h2
    rw [Work.RTOwed.jlVec_apply_three] at h3
    have hM0 : M = 0 := by
      by_contra hMne
      have hb : 1 / 10 ^ 6 ≤ (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 0 ^ 2
          + (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 1 ^ 2 :=
        _root_.Work.RTOWed.jlVec_wOf_sq_bound v M hMne
      have h2' : (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 0 ^ 2 < (1 / 2000 : ℝ) ^ 2 :=
        sq_lt_sq.mpr (by rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2000)])
      have h3' : (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 1 ^ 2 < (1 / 2000 : ℝ) ^ 2 :=
        sq_lt_sq.mpr (by rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2000)])
      have hsum : (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 0 ^ 2
          + (Work.Cusp.wOf v (Work.RTOwed.jLreal M)) 1 ^ 2 < 1 / 10 ^ 6 := by
        nlinarith [h2', h3']
      linarith [hb, hsum]
    have hN0 : N = 0 := by
      have h1 : |(Work.RTOwed.jlVec v N M) 1| < 1 / 2000 := h 1
      rw [hM0] at h1
      rw [Work.RTOwed.jlVec_apply_one, Work.RTOwed.jLreal_zero, Work.RTOwed.cuspY_zero] at h1
      simp only [inner_zero_left, zero_div, add_zero] at h1
      have hπ : (3 : ℝ) < π := Real.pi_gt_three
      have hpos : (0 : ℝ) < 2 * π := by positivity
      rw [abs_mul, abs_of_pos hpos] at h1
      have hNR : |(N : ℝ)| < 1 / 2 := by
        have h6 : (6 : ℝ) ≤ 2 * π := by linarith
        nlinarith [h1, h6, abs_nonneg (N : ℝ)]
      have hZi : |N| < 1 := by
        have hcast : ((|N| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
          rw [Int.cast_abs]
          push_cast
          linarith
        exact_mod_cast hcast
      exact Int.abs_lt_one_iff.mp hZi
    exact ⟨hN0, hM0⟩
  -- the displacement is locally constant: `t` is locally a translation
  have hloc : ∀ q ∈ S, t =ᶠ[𝓝 q] (fun q' => q' + (t q - q)) := by
    intro q hq
    obtain ⟨n, m, hnm⟩ := hdisp q hq
    have hc : t q - q = Work.RTOwed.jlVec v n m := by
      rw [hnm]
      abel
    have hε : (0 : ℝ) < 1 / 64000 := by norm_num
    have hball1 : ∀ᶠ q' in 𝓝 q, t q' ∈ Metric.ball (t q) (1 / 64000) :=
      (hcont.continuousAt (hopen.mem_nhds hq)).eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    have hball2 : ∀ᶠ q' in 𝓝 q, q' ∈ Metric.ball q (1 / 64000) :=
      IsOpen.mem_nhds Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hS' : ∀ᶠ q' in 𝓝 q, q' ∈ S := hopen.mem_nhds hq
    filter_upwards [hball1, hball2, hS'] with q' h1 h2 h3
    obtain ⟨n', m', hn'm'⟩ := hdisp q' h3
    have hd1 : ‖t q' - t q‖ < 1 / 64000 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp h1
    have hd2 : ‖q' - q‖ < 1 / 64000 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp h2
    have hsub : t q' - q' - (t q - q) = Work.RTOwed.jlVec v (n' - n) (m' - m) := by
      have e1 : t q' - q' = Work.RTOwed.jlVec v n' m' := by rw [hn'm']; abel
      have e2 : t q - q = Work.RTOwed.jlVec v n m := hc
      have e3 : Work.RTOwed.jlVec v n' m' - Work.RTOwed.jlVec v n m
          = Work.RTOwed.jlVec v (n' - n) (m' - m) := Work.RTOwed.jlVec_sub v n' n m' m
      rw [e1, e2, e3]
    have hsmall : ∀ i : Fin 4, |(Work.RTOwed.jlVec v (n' - n) (m' - m)) i| < 1 / 2000 := by
      intro i
      rw [← hsub]
      have hcoord : |(t q' - q' - (t q - q)) i| ≤ ‖t q' - q' - (t q - q)‖ := by
        simpa using PiLp.norm_apply_le (t q' - q' - (t q - q)) i
      have hsplit : t q' - q' - (t q - q) = (t q' - t q) - (q' - q) := by abel
      calc |(t q' - q' - (t q - q)) i|
          ≤ ‖t q' - q' - (t q - q)‖ := hcoord
        _ = ‖(t q' - t q) - (q' - q)‖ := by rw [hsplit]
        _ ≤ ‖t q' - t q‖ + ‖q' - q‖ := norm_sub_le _ _
        _ < 1 / 64000 + 1 / 64000 := by linarith
        _ < 1 / 2000 := by norm_num
    obtain ⟨hn, hm⟩ := hbound (n' - n) (m' - m) hsmall
    have hzero : Work.RTOwed.jlVec v (n' - n) (m' - m) = 0 :=
      (Work.RTOwed.jlVec_eq_zero_iff v (n' - n) (m' - m)).mpr ⟨hn, hm⟩
    have hz : t q' - q' - (t q - q) = 0 := by rw [hsub, hzero]
    have hlast : t q' - q' = t q - q := sub_eq_zero.mp hz
    rw [← hlast]
    abel
  -- smoothness: `t` agrees locally with a translation
  have hcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) t S := by
    refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
    have hev : ∀ᶠ y in 𝓝 q, t y = y + (t q - q) := hloc q hq
    obtain ⟨U₀, hU₀mem, hU₀⟩ := Filter.Eventually.exists_mem hev
    have hU₀' : ∀ y ∈ U₀, t y = y + (t q - q) := hU₀
    obtain ⟨U, hUsub, hUo, hqU⟩ := mem_nhds_iff.mp hU₀mem
    refine ⟨U, hUo, hqU, ?_⟩
    refine (((contDiff_id (𝕜 := ℝ) (E := Work.Cusp.E4)).add
      (contDiff_const (c := t q - q))).contDiffOn).congr ?_
    intro q' hq'
    exact hU₀' q' (hUsub hq'.2)
  have hfd : ∀ q ∈ S, fderiv ℝ t q = ContinuousLinearMap.id ℝ Work.Cusp.E4 := by
    intro q hq
    rw [(hloc q hq).fderiv_eq]
    rw [fderiv_add_const]
    exact fderiv_id
  constructor
  · exact hcd
  · intro q hq u w
    obtain ⟨n, m, hnm⟩ := hdisp q hq
    have h0 : (t q) 0 = q 0 := by
      rw [hnm]
      simp
    have hd := hfd q hq
    rw [hd]
    simp only [Work.RTOwed.jLayer, Work.RTInstance.ChartLayer.model,
      Work.RTInstance.warpedModelA_apply, ContinuousLinearMap.id_apply, h0]

end Work.RTOwed

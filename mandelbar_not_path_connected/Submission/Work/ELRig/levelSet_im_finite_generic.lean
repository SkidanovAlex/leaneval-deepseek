/-
# ELRig — the generic finite level set of `Im γ₁` (`levelSet_im_finite_generic`)

`Work.ELRig.levelSet_im_finite_generic`: for a `RayCylLift` `L` whose first lift is *pinned* to the
inverse branch of `Ψ` on the window `[N, N+1]` (`hpin`, the form produced by
`Work.ELRig.rayCylLift_far_left_pin` / `Work.ELRig.pointwise_pin`), and for every `y : ℝ`, there
is `η ∈ (0,1)` such that the level sets `{s ∈ [N, N+1) | Im (γᵢ s) = y + η}` are finite, for `i = 1`
and `i = 2`.

## Route

Write `S = {Re < -L.R}`, `Γ t = rayPt α₁ t`, `G = invFunOn Ψ S` and `Φ t = (G (Γ t)).im`.
`hpin` reads `γ₁ u = G (Γ (τ u))` on `[N, N+1]`, hence

  `Im (γ₁ u) = Φ (τ u)`   for `u ∈ [N, N+1]`,                                          (†)

and `Φ` is real-analytic on the (open) set where `Γ t ∈ Ψ '' S`; off it, `Φ` is the *constant*
value `(Classical.choice _).im` (the fall-back branch of `invFunOn` does not depend on its
argument), so the set of values `v` for which the level set `{Im γ₁ = v}` can be infinite is
contained in

  `C := {v | Φ ≡ v on some nondegenerate interval}`  ∪  `W := {Φ t | Γ t ∉ Ψ '' S}`,

both countable (`C` by `levelSetIm_countable_setOf_interval_constant`: the witnessing intervals of distinct
values are disjoint, so each contains a distinct rational; `W` is a subsingleton).  For
`v ∉ C ∪ W` the level set `{u ∈ Icc N (N+1) | Im (γ₁ u) = v}` is compact and every one of its
points is *isolated* in it: at `u` in the level set, `τ u ∈ Ψ '' S`, `Φ` is analytic at `τ u`, and
`Φ ≡ v` near `τ u` would put `v` in `C`; hence `Φ - v` is nonzero on a punctured neighbourhood of
`τ u`, which — by continuity of `τ` — pulls back to a punctured neighbourhood of `u` avoiding the
level set.  Compact + codiscrete (isolated) is finite
(`IsCompact.finite_sdiff_of_mem_codiscreteWithin`).  Finally `Im γ₂ = -Im γ₁` turns the second
claim into the level set of `Im γ₁` at `-(y + η)`, so the choice of `η` must avoid the countable
set `(C ∪ W) - y` together with its negative, which is possible on `(0,1)`
(`levelSetIm_exists_eta_shifted_notMem_countable`).

## Remark (for the consumer)

The proof actually shows more than the statement: the set of *bad* levels `v` (those for which
`{u ∈ Icc N (N+1) | Im (γ₁ u) = v}` is infinite) is contained in `C ∪ W`, where `W` is a
*single* value and `C` is countable.  Note that a countable set may accumulate at `y`, so this
argument gives **nothing** in the direction of "one may take `η < ε` for arbitrarily small `ε`"
(the sibling statement `levelSet_im_finite_small`): that strengthening needs `y` to be outside the
closure of the bad set, which does not follow from the pinning hypothesis `hpin` alone.
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.Cyl.continuous_tau
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.ELRig.analyticOnNhd_invFunOn
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic
import Submission.Work.ELRig.rayCylLift_far_left_pin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Two elementary auxiliary facts -/

/-- **The fall-back branch of `Function.invFunOn` does not depend on the argument.**  If `y` and
`y'` are both outside the image of `f` on `s`, then `invFunOn f s` takes the same (arbitrary but
fixed) value at `y` and at `y'`. -/
theorem levelSetIm_invFunOn_eq_of_not_exists {α β : Type*} [Nonempty α] {f : α → β} {s : Set α} {y y' : β}
    (hy : ¬∃ a ∈ s, f a = y) (hy' : ¬∃ a ∈ s, f a = y') :
    Function.invFunOn f s y = Function.invFunOn f s y' := by
  rw [Function.invFunOn, dif_neg hy, Function.invFunOn, dif_neg hy']

/-- **The values on which a function is constant on a nondegenerate open interval form a
countable set.**  For distinct values the witnessing intervals are disjoint (an intersection point
would carry both values), so each contains a distinct rational. -/
theorem levelSetIm_countable_setOf_interval_constant (f : ℝ → ℝ) :
    {v : ℝ | ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Ioo a b, f t = v}.Countable := by
  classical
  set C : Set ℝ := {v : ℝ | ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Ioo a b, f t = v} with hC
  have hex : ∀ v ∈ C, ∃ q : ℚ, ∃ a b : ℝ, a < b ∧ (q : ℝ) ∈ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo a b, f t = v := by
    intro v hv
    obtain ⟨a, b, hab, hfab⟩ := hv
    obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
    exact ⟨q, a, b, hab, ⟨by exact_mod_cast haq, by exact_mod_cast hqb⟩, hfab⟩
  let ι : ℝ → ℚ := fun v => if h : v ∈ C then Classical.choose (hex v h) else 0
  have hιspec : ∀ v ∈ C, ∃ a b : ℝ, a < b ∧ ((ι v : ℚ) : ℝ) ∈ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo a b, f t = v := by
    intro v hv
    have hval : ι v = Classical.choose (hex v hv) := by
      simp only [ι]; exact dif_pos hv
    obtain ⟨a, b, hab, hqab, hfab⟩ := Classical.choose_spec (hex v hv)
    exact ⟨a, b, hab, by rwa [hval], hfab⟩
  have hinj : Set.InjOn ι C := by
    intro v hv v' hv' heq
    obtain ⟨a, b, hab, hqab, hfv⟩ := hιspec v hv
    obtain ⟨a', b', ha'b', hqa'b', hfv'⟩ := hιspec v' hv'
    have hqq : ((ι v : ℚ) : ℝ) = ((ι v' : ℚ) : ℝ) := by rw [heq]
    have hmem' : ((ι v : ℚ) : ℝ) ∈ Set.Ioo a' b' := by rw [hqq]; exact hqa'b'
    exact (hfv _ hqab).symm.trans (hfv' _ hmem')
  exact Function.Injective.countable (f := fun v : ↥C => ι v.1)
    (fun u u' h => Subtype.ext (hinj u.2 u'.2 h))

/-- **Choice of the generic shift.**  For a countable `W ⊆ ℝ` and any `y : ℝ` there is
`η ∈ (0,1)` with both `y + η` and `-(y + η)` outside `W`: the forbidden set of `η` is the union of
the two countable sets `W - y` and `-W - y`, while `(0,1)` is uncountable. -/
theorem levelSetIm_exists_eta_shifted_notMem_countable (W : Set ℝ) (hW : W.Countable) (y : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ y + η ∉ W ∧ -(y + η) ∉ W := by
  have hcount : (W ∪ (fun x : ℝ => -x) '' W).Countable := hW.union (hW.image _)
  have hex : ∃ t ∈ Set.Ioo y (y + 1), t ∉ W ∪ (fun x : ℝ => -x) '' W := by
    by_contra h
    push_neg at h
    have hsub : Set.Ioo y (y + 1) ⊆ W ∪ (fun x : ℝ => -x) '' W := fun t ht => h t ht
    have hc : (Set.Ioo y (y + 1)).Countable := hcount.mono hsub
    have h1 : Cardinal.mk ↥(Set.Ioo y (y + 1)) ≤ Cardinal.aleph0 :=
      Cardinal.mk_le_aleph0_iff.mpr hc
    rw [Cardinal.mk_Ioo_real (lt_add_one y)] at h1
    exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)
  obtain ⟨t, htIoo, htW⟩ := hex
  refine ⟨t - y, by linarith [htIoo.1], by linarith [htIoo.2], ?_, ?_⟩
  · rw [show y + (t - y) = t from by ring]
    exact fun h => htW (Or.inl h)
  · rw [show y + (t - y) = t from by ring]
    intro hmem
    exact htW (Or.inr ⟨-t, hmem, by ring⟩)

/-- **Real analyticity of the pinned curve in the level.**  If the ray point `rayPt α₁ t` has a
`Ψ`-preimage in the half plane `S = {Re < -L.R}`, then `t ↦ Im (invFunOn Ψ S (rayPt α₁ t))` is
real analytic at `t`, for `t > 1`.  (`AnalyticOnNhd ℂ (invFunOn Ψ S) (Ψ '' S)` composed with the
real-analytic `t ↦ rayPt α₁ t` and `Im`.) -/
theorem levelSetIm_analyticAt_im_invFunOn_rayPt {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {t : ℝ} (ht : 1 < t)
    (hmem : Work.EL.rayPt d.hN Work.EL.alpha1 t ∈ fl.Ψ '' {w : ℂ | w.re < -L.R}) :
    AnalyticAt ℝ (fun s : ℝ => (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 s)).im) t := by
  have hSopen : IsOpen {w : ℂ | w.re < -L.R} := isOpen_lt Complex.continuous_re continuous_const
  have hΨan : AnalyticOnNhd ℂ fl.Ψ {w : ℂ | w.re < -L.R} :=
    (fl.Ψ_diff.differentiableOn).analyticOnNhd hSopen
  have hGan : AnalyticOnNhd ℂ (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R})
      (fl.Ψ '' {w : ℂ | w.re < -L.R}) := analyticOnNhd_invFunOn hSopen hΨan L.hinj
  have hΓan : AnalyticOn ℝ (fun s : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 s) (Set.Ioi 1) :=
    analyticOn_rayPt_of_analytic d.hN (analyticOnNhd_dynBottcher d.bottcher) Work.EL.alpha1
  have h1 : AnalyticAt ℝ (fun s : ℝ => Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 s)) t :=
    AnalyticAt.comp (g := Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R})
      (f := fun s : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 s)
      ((hGan _ hmem).restrictScalars) (hΓan.analyticAt (Ioi_mem_nhds ht))
  have h2 : AnalyticAt ℝ (fun s : ℝ => (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 s)).im) t := by
    have h3 := AnalyticAt.comp (g := Complex.imCLM)
      (f := fun s : ℝ => Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 s)) (Complex.imCLM.analyticAt _) h1
    simpa only [Function.comp_def, Complex.imCLM_apply] using h3
  exact h2

/-! ## The main lemma -/

theorem levelSet_im_finite_generic {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (N : ℝ)
    (hpin : ∀ u : ℝ, u ∈ Set.Icc N (N + 1) → L.γ₁ u = Function.invFunOn fl.Ψ
      {w : ℂ | w.re < -L.R} (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)))
    (y : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₁ s).im = y + η}).Finite ∧
      ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ (L.γ₂ s).im = y + η}).Finite := by
  classical
  set Γ : ℝ → ℂ := fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t with hΓ
  set Φ : ℝ → ℝ := fun t : ℝ =>
    (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R} (Γ t)).im with hΦ
  -- (†): the pinning identifies `Im γ₁` with `Φ ∘ τ` on the window
  have him : ∀ u ∈ Set.Icc N (N + 1), (L.γ₁ u).im = Φ (L.τ u) := by
    intro u hu
    have h1 : Φ (L.τ u) = (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u))).im := by
      simp only [hΦ, hΓ]
    rw [h1, ← hpin u hu]
  -- the two countable sets of bad values
  have hCcount : {v : ℝ | ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Ioo a b, Φ t = v}.Countable :=
    levelSetIm_countable_setOf_interval_constant Φ
  have hWcount : {v : ℝ | ∃ t : ℝ,
      (¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t) ∧ Φ t = v}.Countable := by
    have hconst : ∀ t t' : ℝ, (¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t) →
        (¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t') → Φ t = Φ t' := by
      intro t t' ht ht'
      have h1 : Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R} (Γ t)
          = Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R} (Γ t') :=
        levelSetIm_invFunOn_eq_of_not_exists ht ht'
      simp only [hΦ]
      rw [h1]
    rcases Set.eq_empty_or_nonempty ({t : ℝ | ¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t} : Set ℝ) with
      hemp | ⟨t₀, ht₀⟩
    · have hemp' : {v : ℝ | ∃ t : ℝ,
          (¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t) ∧ Φ t = v} = ∅ := by
        ext v
        constructor
        · rintro ⟨t, ht, -⟩
          exact absurd (show t ∈ ({t : ℝ | ¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t} : Set ℝ)
            from ht) (by rw [hemp]; exact Set.notMem_empty t)
        · intro h; exact absurd h (Set.notMem_empty v)
      rw [hemp']
      exact Set.countable_empty
    · refine Set.Subsingleton.countable (fun v hv v' hv' => ?_)
      obtain ⟨t, ht, rfl⟩ := hv
      obtain ⟨t', ht', rfl⟩ := hv'
      exact hconst t t' ht ht'
  -- the level set of `Im γ₁` is finite away from those sets
  have hkey : ∀ v : ℝ, v ∉ {v : ℝ | ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Ioo a b, Φ t = v} →
      v ∉ {v : ℝ | ∃ t : ℝ,
        (¬∃ a ∈ {w : ℂ | w.re < -L.R}, fl.Ψ a = Γ t) ∧ Φ t = v} →
      ({u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v}).Finite := by
    intro v hvC hvW
    have hlev : {u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v}
        = {u : ℝ | (L.γ₁ u).im = v} ∩ Set.Icc N (N + 1) := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    have hcomp : IsCompact {u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v} := by
      rw [hlev]
      exact isCompact_Icc.of_isClosed_subset
        ((isClosed_eq (Complex.continuous_im.comp L.cont₁) continuous_const).inter isClosed_Icc)
        Set.inter_subset_right
    have hcod : ({u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v}ᶜ)
        ∈ Filter.codiscreteWithin {u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v} := by
      rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
      intro u hu
      simp only [Set.union_self]
      have hΦu : Φ (L.τ u) = v := by rw [← him u hu.1]; exact hu.2
    -- `τ u` lies in the image of the half plane, and `Φ` is analytic there
      have hmemΓ : Γ (L.τ u) ∈ fl.Ψ '' {w : ℂ | w.re < -L.R} := by
        by_contra h
        exact hvW ⟨L.τ u, h, hΦu⟩
      have hmemRay : Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)
          ∈ fl.Ψ '' {w : ℂ | w.re < -L.R} := hmemΓ
      have haz : AnalyticAt ℝ Φ (L.τ u) := by
        show AnalyticAt ℝ (fun s : ℝ => (Function.invFunOn fl.Ψ {w : ℂ | w.re < -L.R}
          (Work.EL.rayPt d.hN Work.EL.alpha1 s)).im) (L.τ u)
        exact levelSetIm_analyticAt_im_invFunOn_rayPt d fl L (L.hτ1 u) hmemRay
      refine Metric.mem_nhdsWithin_iff.mpr ?_
      rcases haz.eventually_eq_or_eventually_ne (analyticAt_const (v := v)) with heq | hne
      · -- `Φ ≡ v` near `τ u` would put `v` in the countable set
        exfalso
        obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp heq
        exact hvC ⟨L.τ u - δ, L.τ u + δ, by linarith,
          fun t ht => hδsub (by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)⟩
      · -- otherwise the punctured neighbourhood of `τ u` avoids the level, and continuity of `τ`
        -- pulls it back
        obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hne
        obtain ⟨δ, hδpos, hδcont⟩ : ∃ δ > 0, ∀ x : ℝ, dist x u < δ →
            dist (L.τ x) (L.τ u) < ε :=
          Metric.continuousAt_iff.mp (Continuous.continuousAt (Cyl.continuous_tau d fl L).1)
            ε hεpos
        refine ⟨δ, hδpos, ?_⟩
        rintro u' ⟨hu'ball, hu'ne⟩ hu'mem
        have hΦu' : Φ (L.τ u') = v := by rw [← him u' hu'mem.1]; exact hu'mem.2
        have hdist : dist (L.τ u') (L.τ u) < ε := hδcont u' (Metric.mem_ball.mp hu'ball)
        have hneτ : L.τ u' ≠ L.τ u := fun h => hu'ne (L.hτmono.injective h)
        have hmem_ball : L.τ u' ∈ Metric.ball (L.τ u) ε := by
          rw [Metric.mem_ball]
          exact hdist
        exact hεsub ⟨hmem_ball, hneτ⟩ hΦu'
    have hfin := hcomp.finite_sdiff_of_mem_codiscreteWithin hcod
    convert hfin using 1
    ext x
    simp
  -- the set of bad values is countable
  have hbad : {v : ℝ | ¬ ({u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v}).Finite}.Countable := by
    refine Set.Countable.mono ?_ (hCcount.union hWcount)
    intro v hv
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    exact hv (hkey v hcon.1 hcon.2)
  -- choose the generic shift
  obtain ⟨η, hη0, hη1, hgood, hgood'⟩ :=
    levelSetIm_exists_eta_shifted_notMem_countable
      {v : ℝ | ¬ ({u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = v}).Finite} hbad y
  have hfinA : ({u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = y + η}).Finite := by
    by_contra h
    exact hgood h
  have hfinB : ({u : ℝ | u ∈ Set.Icc N (N + 1) ∧ (L.γ₁ u).im = -(y + η)}).Finite := by
    by_contra h
    exact hgood' h
  refine ⟨η, hη0, hη1, ?_, ?_⟩
  · refine hfinA.subset ?_
    rintro s ⟨hs, hsim⟩
    exact ⟨⟨hs.1, le_of_lt hs.2⟩, hsim⟩
  · have him2 : ∀ s : ℝ, (L.γ₂ s).im = -(L.γ₁ s).im := by
      intro s
      rw [L.anti s]
      simp
    refine hfinB.subset ?_
    rintro s ⟨hs, hsim⟩
    refine ⟨⟨hs.1, le_of_lt hs.2⟩, ?_⟩
    rw [him2 s] at hsim
    linarith

end Work.ELRig

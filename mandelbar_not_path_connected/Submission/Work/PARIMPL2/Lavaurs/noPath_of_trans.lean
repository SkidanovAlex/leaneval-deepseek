/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.noPath_of_trans` — the path form of `hLB`, for an **abstract**
transit coordinate

`Submission/Work/PARIMPL2/PathFix.lean` proves the path endgame (`Work.PARIMPL2.transit_crossing`,
`Work.PARIMPL2.noPath`) for the *concrete* transit coordinate `transU P M.nIn` of a `MatchData`,
carrying the three bundles `MatchData`/`TransitData`/`LeakData` through the whole argument.  The
present file removes the bundles: every use of `transU P M.nIn` in that argument is through one of
four properties only —

* continuity on `Nm` (`hcont`);
* blow-up at the parabolic locus (`hblow`);
* the height bound `|Im trans| ≤ r/4` (`hH`);
* the leak escape `distZ trans x < r/2 ⟹ c ∉ Mandelbar` (`hesc`);

so the same proof goes through verbatim for an arbitrary `trans : ℂ → ℂ` satisfying them.  This is
what the assembled `noPath` of a *corrected* bundle chain needs: the chain-D export
`Work.PARIMPL2.Lavaurs.LavaursPhase` delivers its own transit coordinate `transPh P x₀ θ`, and it
must not be forced through the `transU` of `MatchData`.

* `Work.PARIMPL2.Lavaurs.crossing_of_trans` — the crossing lemma (`transit_crossing` with the
  bundles removed);
* `Work.PARIMPL2.Lavaurs.noPath_of_trans` — the requested path statement.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.PathFix

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open LeanEval.ComplexAnalysis (Mandelbar)

variable {c₀ : ℂ}

/-! ## The crossing lemma, for an abstract transit coordinate -/

/-- **The transit crossing.**  Let `Γ` be a continuous path, `a < b`, `Γ a ∈ Nm` on the implosion
side, `Γ b ∉ Nm`, and `Γ` maps `[a,b]` into `ball c₀ ρ`.  If a transit coordinate `trans` is
continuous on `Nm`, blows up at the parabolic locus, has height `≤ r/4` and satisfies the leak
escape at the real level `x` with modulus `r`, then `Γ` cannot be a path in the mandelbar.

This is `Work.PARIMPL2.transit_crossing` with `transU P M.nIn` replaced by `trans` and the bundles
`MatchData`/`TransitData`/`LeakData` replaced by exactly the four properties that proof consumes. -/
theorem crossing_of_trans {d : Work.EL.RootParabolic c₀} {P : Work.PARIMPL.ParNormal d}
    {trans : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn trans P.Nm)
    (hblow : ∀ a : ℂ, P.a2 a = 0 → a ∈ Metric.ball c₀ P.ρ₀ →
      Filter.Tendsto (fun c => (trans c).re) (nhdsWithin a P.Nm) Filter.atBot)
    {Γ : ℝ → ℂ} {a b ρ ρH ρL : ℝ} (hab : a < b) (hΓ : Continuous Γ)
    (hΓmem : ∀ u ∈ Set.Icc a b, Γ u ∈ Mandelbar)
    (haNm : Γ a ∈ P.Nm) (hbNm : Γ b ∉ P.Nm)
    (hballI : ∀ u ∈ Set.Icc a b, dist (Γ u) c₀ < ρ)
    (hρH : ρ ≤ ρH) (hρL : ρ ≤ ρL) (hρP : ρ ≤ P.ρ₀)
    (hH : ∀ c ∈ P.Nm ∩ ball c₀ ρH, |(trans c).im| ≤ r / 4)
    (hLesc : ∀ c ∈ P.Nm ∩ ball c₀ ρL,
      Work.PARIMPL.distZ (trans c) ((x : ℝ) : ℂ) < r / 2 → c ∉ Mandelbar) : False := by
  -- `Γ` stays in the normal-form ball
  have hballab : ∀ u ∈ Set.Icc a b, Γ u ∈ ball c₀ P.ρ₀ :=
    fun u hu => Work.PARIMPL.mem_ball_mono (by rw [mem_ball]; exact hballI u hu) hρP
  have hbale : 0 ≤ P.a2 (Γ b) := by
    by_contra hcon
    exact hbNm ⟨hballab b ⟨hab.le, le_refl b⟩, lt_of_not_ge hcon⟩
  -- the exit time: the first zero of `a₂ ∘ Γ` after `a`
  have hcont2 : ContinuousOn (fun u : ℝ => P.a2 (Γ u)) (Set.Icc a b) :=
    P.cont_a2.comp hΓ.continuousOn (fun u hu => hballab u hu)
  have hzero : ∃ u ∈ Set.Icc a b, P.a2 (Γ u) = 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (P.a2 (Γ a)) (P.a2 (Γ b)) :=
      ⟨le_of_lt haNm.2, hbale⟩
    exact intermediate_value_Icc hab.le hcont2 hmem
  set A : Set ℝ := {u : ℝ | u ∈ Set.Icc a b ∧ P.a2 (Γ u) = 0} with hA
  have hAclosed : IsClosed A := by
    rw [hA]
    have h := hcont2.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := (0 : ℝ)))
    convert h using 2
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  have hAne : A.Nonempty := hzero
  have hAbdd : BddBelow A := ⟨a, fun u hu => hu.1.1⟩
  set s : ℝ := sInf A with hs
  have hsA : s ∈ A := hAclosed.csInf_mem hAne hAbdd
  have has : a ≤ s := hsA.1.1
  have hsb : s ≤ b := hsA.1.2
  have hs0 : P.a2 (Γ s) = 0 := hsA.2
  have haslt : a < s := by
    rcases lt_or_eq_of_le has with h | h
    · exact h
    · exfalso
      rw [← h] at hs0
      linarith [haNm.2]
  -- the open segment is inside `Nm`
  have hsegNm : ∀ u ∈ Set.Ioo a s, Γ u ∈ P.Nm ∩ ball c₀ ρ := by
    intro u hu
    have huI : u ∈ Set.Icc a b := ⟨hu.1.le, le_trans hu.2.le hsb⟩
    refine ⟨⟨hballab u huI, ?_⟩, by rw [mem_ball]; exact hballI u huI⟩
    have hle : P.a2 (Γ u) ≤ 0 := by
      by_contra hcon
      have hpos : 0 < P.a2 (Γ u) := lt_of_not_ge hcon
      have hcont' : ContinuousOn (fun w : ℝ => P.a2 (Γ w)) (Set.Icc a u) :=
        hcont2.mono (by intro w hw; exact ⟨hw.1, le_trans hw.2 (le_trans hu.2.le hsb)⟩)
      have hmem : (0 : ℝ) ∈ Set.Icc (P.a2 (Γ a)) (P.a2 (Γ u)) := ⟨le_of_lt haNm.2, hpos.le⟩
      obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc hu.1.le hcont' hmem
      have hvA : v ∈ A := ⟨⟨hv.1, le_trans hv.2 (le_trans hu.2.le hsb)⟩, hv0⟩
      have hsv : s ≤ v := csInf_le hAbdd hvA
      exact absurd hu.2 (not_lt.mpr (le_trans hsv hv.2))
    have hne : P.a2 (Γ u) ≠ 0 := by
      intro h0
      have huA : u ∈ A := ⟨huI, h0⟩
      have hsu : s ≤ u := csInf_le hAbdd huA
      exact absurd hsu (not_le.mpr hu.2)
    exact lt_of_le_of_ne hle hne
  -- the crossing
  obtain ⟨K, hK⟩ := exists_int_gt (x - (trans (Γ a)).re)
  set tgt : ℝ := x - (K : ℝ) with htgt
  have htgt_lt : tgt < (trans (Γ a)).re := by rw [htgt]; linarith
  have hB : ∀ᶠ c in 𝓝[P.Nm] (Γ s), (trans c).re ≤ tgt - 1 :=
    tendsto_atBot.mp (hblow (Γ s) hs0 (hballab s ⟨has, hsb⟩)) (tgt - 1)
  rw [eventually_nhdsWithin_iff] at hB
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℂ,
      dist y (Γ s) < ε → (y ∈ P.Nm → (trans y).re ≤ tgt - 1) :=
    Metric.eventually_nhds_iff.mp hB
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ,
      dist z s < δ → dist (Γ z) (Γ s) < ε :=
    Metric.continuousAt_iff.mp hΓ.continuousAt ε hεpos
  set δ₁ : ℝ := min (δ / 2) ((s - a) / 2) with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min (by linarith) (by linarith)
  set u₁ : ℝ := s - δ₁ with hu₁
  have hu₁lt : u₁ < s := by rw [hu₁]; linarith
  have hau₁ : a < u₁ := by
    rw [hu₁]
    have := min_le_right (δ / 2) ((s - a) / 2)
    linarith
  have hu₁dist : dist u₁ s < δ := by
    rw [Real.dist_eq, hu₁, abs_of_neg (by linarith)]
    have := min_le_left (δ / 2) ((s - a) / 2)
    linarith
  have hu₁seg : Γ u₁ ∈ P.Nm ∩ ball c₀ ρ := hsegNm u₁ ⟨hau₁, hu₁lt⟩
  have hu₁le : (trans (Γ u₁)).re ≤ tgt - 1 := by
    have h1 : dist (Γ u₁) (Γ s) < ε := hδ u₁ hu₁dist
    have h2 : Γ u₁ ∈ P.Nm := hu₁seg.1
    exact hε (Γ u₁) h1 h2
  have hu₁lt' : (trans (Γ u₁)).re < tgt := by linarith
  -- continuity of the transit coordinate on `[a, u₁]`
  have hmap : MapsTo Γ (Set.uIcc a u₁) P.Nm := by
    intro u hu
    rw [Set.uIcc_of_le hau₁.le] at hu
    rcases lt_or_eq_of_le hu.1 with hltu | heq
    · exact (hsegNm u ⟨hltu, lt_of_le_of_lt hu.2 hu₁lt⟩).1
    · subst heq; exact haNm
  have hcont1 : ContinuousOn (fun u : ℝ => trans (Γ u)) (Set.uIcc a u₁) := by
    have h := hcont.comp hΓ.continuousOn hmap
    simpa only [Function.comp_def] using h
  have hcont' : ContinuousOn (fun u : ℝ => (trans (Γ u)).re) (Set.uIcc a u₁) := by
    simpa only [Function.comp_def] using Complex.continuous_re.comp_continuousOn hcont1
  -- the intermediate value theorem
  have hmem : tgt ∈ Set.uIcc ((fun u : ℝ => (trans (Γ u)).re) a)
      ((fun u : ℝ => (trans (Γ u)).re) u₁) :=
    Set.mem_uIcc.mpr (Or.inr ⟨hu₁lt'.le, htgt_lt.le⟩)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_uIcc hcont' hmem
  rw [Set.uIcc_of_le hau₁.le] at hu
  -- the crossing parameter escapes
  have huNm : Γ u ∈ P.Nm ∩ ball c₀ ρ := by
    rcases lt_or_eq_of_le hu.1 with hltu | heq
    · exact hsegNm u ⟨hltu, lt_of_le_of_lt hu.2 hu₁lt⟩
    · subst heq; exact ⟨haNm, by rw [mem_ball]; exact hballI a ⟨le_refl a, hab.le⟩⟩
  have huH : |(trans (Γ u)).im| ≤ r / 4 :=
    hH (Γ u) ⟨huNm.1, Work.PARIMPL.mem_ball_mono huNm.2 hρH⟩
  have hdist : ‖trans (Γ u) - (((x - (K : ℝ)) : ℝ) : ℂ)‖ < r / 2 := by
    have hsub : trans (Γ u) - (((x - (K : ℝ)) : ℝ) : ℂ)
        = (((trans (Γ u)).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.sub_re, hfu, htgt]
      · simp [Complex.sub_im]
    rw [hsub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith [hr]
  have hZ : Work.PARIMPL.distZ (trans (Γ u)) ((x : ℝ) : ℂ) < r / 2 := by
    refine lt_of_le_of_lt (Work.PARIMPL.distZ_le _ _ K) ?_
    have hsum : (trans (Γ u) + (K : ℂ)) - ((x : ℝ) : ℂ)
        = trans (Γ u) - (((x - (K : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [dist_eq_norm, hsum]
    exact hdist
  exact (hLesc (Γ u) ⟨huNm.1, Work.PARIMPL.mem_ball_mono huNm.2 hρL⟩ hZ)
    (hΓmem u ⟨hu.1, le_trans hu.2 (le_trans hu₁lt.le hsb)⟩)

/-! ## The requested lemma -/

theorem noPath_of_trans {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
    {trans : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn trans P.Nm)
    (hblow : ∀ a : ℂ, P.a2 a = 0 → a ∈ Metric.ball c₀ P.ρ₀ →
      Filter.Tendsto (fun c => (trans c).re) (nhdsWithin a P.Nm) Filter.atBot)
    (hH : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, |(trans c).im| ≤ r / 4)
    (hesc : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (trans c) ((x : ℝ) : ℂ) < r / 2 → c ∉ LeanEval.ComplexAnalysis.Mandelbar) :
    ∀ γ : C(Set.Icc (0:ℝ) 1, ℂ), (∀ t, γ t ∈ LeanEval.ComplexAnalysis.Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ P.Nm) := by
  intro γ hγ hmem
  -- the two radii
  obtain ⟨ρH, hρHpos, hH'⟩ := hH
  obtain ⟨ρL, hρLpos, hLesc⟩ := hesc
  set ρ : ℝ := min (min ρH ρL) P.ρ₀ with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hρHpos hρLpos) P.hρ₀
  have hρH' : ρ ≤ ρH := by
    rw [hρdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hρL' : ρ ≤ ρL := by
    rw [hρdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hρP' : ρ ≤ P.ρ₀ := by
    rw [hρdef]; exact min_le_right _ _
  -- the path, reparametrised on `ℝ`
  set Γ : ℝ → ℂ := fun t => γ (Set.projIcc (0 : ℝ) 1 (by norm_num) t) with hΓdef
  have hΓcont : Continuous Γ := γ.continuous.comp continuous_projIcc
  have hΓmem01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Γ t ∈ Mandelbar := by
    intro t ht
    change γ (Set.projIcc (0 : ℝ) 1 (by norm_num) t) ∈ Mandelbar
    rw [Set.projIcc_of_mem (by norm_num) ht]
    exact hγ ⟨t, ht⟩
  -- a sequence of parameters in `Nm` whose images converge to `c₀`
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ Γ t ∈ P.Nm ∧
      dist (Γ t) c₀ < 1 / (n + 1) := by
    intro n
    have hε : 0 < (1 : ℝ) / (n + 1) := by positivity
    obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hmem ((1 : ℝ) / (n + 1)) hε
    obtain ⟨t, ht⟩ := Set.mem_range.mp hy.1
    refine ⟨(t : ℝ), t.2, ?_, ?_⟩
    · change γ (Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ)) ∈ P.Nm
      rw [Set.projIcc_of_mem (by norm_num) t.2, ht]
      exact hy.2
    · change dist (γ (Set.projIcc (0 : ℝ) 1 (by norm_num) (t : ℝ))) c₀ < 1 / (n + 1)
      rw [Set.projIcc_of_mem (by norm_num) t.2, ht, dist_comm]
      exact hd
  choose t htI htNm htD using hseq
  obtain ⟨tstar, htstarI, φ, hφmono, hφtend⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).tendsto_subseq htI
  -- the limit time
  have hΓt : Tendsto (fun n => Γ (t n)) atTop (𝓝 c₀) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
    have h2 : (1 : ℝ) / (N + 1) < ε := by
      have h3 : (1 : ℝ) / ε < (N : ℝ) + 1 := by
        have hN' : (1 : ℝ) / ε < (N : ℝ) := hN
        linarith
      have h4 : ε * (1 / ε) < ε * ((N : ℝ) + 1) := mul_lt_mul_of_pos_left h3 hε
      have h5 : ε * (1 / ε) = 1 := by field_simp
      rw [h5] at h4
      rw [div_lt_iff₀ (by positivity)]
      linarith
    exact lt_of_lt_of_le (htD n) (le_of_lt (lt_of_le_of_lt h1 h2))
  have hΓstar : Γ tstar = c₀ := by
    have h1 : Tendsto (fun n => Γ (t (φ n))) atTop (𝓝 (Γ tstar)) :=
      (hΓcont.tendsto tstar).comp hφtend
    have h2 : Tendsto (fun n => Γ (t (φ n))) atTop (𝓝 c₀) :=
      hΓt.comp hφmono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  -- the segment from a nearby parameter to the limit time stays in the `ρ`-ball
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ,
      dist z tstar < δ → dist (Γ z) (Γ tstar) < ρ / 2 :=
    Metric.continuousAt_iff.mp hΓcont.continuousAt (ρ / 2) (by linarith)
  have hev : ∀ᶠ n in atTop, dist (t (φ n)) tstar < δ / 2 :=
    (Metric.tendsto_nhds.mp hφtend) (δ / 2) (by linarith)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hev
  set τ : ℝ := t (φ n₀) with hτdef
  have hτI : τ ∈ Set.Icc (0 : ℝ) 1 := htI (φ n₀)
  have hτclose : dist τ tstar < δ / 2 := hn₀ n₀ le_rfl
  have hsegball : ∀ u ∈ Set.uIcc τ tstar, dist (Γ u) c₀ < ρ := by
    intro u hu
    have h1 : dist u tstar ≤ dist τ tstar := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
          abs_of_nonpos (by linarith)]
        linarith
      · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        linarith
    have h2 : dist (Γ u) (Γ tstar) < ρ / 2 := hδ u (lt_of_le_of_lt h1 (by linarith))
    rw [hΓstar] at h2
    linarith
  -- the two endpoints
  have hτNm : Γ τ ∈ P.Nm := htNm (φ n₀)
  have htsNm : Γ tstar ∉ P.Nm := by
    intro hcon
    rw [hΓstar, Work.PARIMPL.ParNormal.mem_Nm, P.a2₀] at hcon
    exact absurd hcon.2 (lt_irrefl 0)
  have hne : τ ≠ tstar := fun h => htsNm (h ▸ hτNm)
  -- the crossing
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine crossing_of_trans hr hcont hblow hlt hΓcont ?_ hτNm htsNm ?_ hρH' hρL' hρP' hH' hLesc
    · intro u hu
      exact hΓmem01 u ⟨le_trans hτI.1 hu.1, le_trans hu.2 htstarI.2⟩
    · intro u hu
      exact hsegball u (Set.mem_uIcc.mpr (Or.inl hu))
  · -- `tstar < τ`: reverse the parameterisation
    set Γ' : ℝ → ℂ := fun u => Γ (τ + tstar - u) with hΓ'def
    have hΓ'cont : Continuous Γ' :=
      hΓcont.comp ((continuous_const.add continuous_const).sub continuous_id)
    have hΓ'mem : ∀ u ∈ Set.Icc tstar τ, Γ' u ∈ Mandelbar := by
      intro u hu
      have h1 : τ + tstar - u ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [hu.2, htstarI.1], by linarith [hu.1, hτI.2]⟩
      simpa only [hΓ'def] using hΓmem01 _ h1
    have hΓ'ball : ∀ u ∈ Set.Icc tstar τ, dist (Γ' u) c₀ < ρ := by
      intro u hu
      have h1 : τ + tstar - u ∈ Set.uIcc τ tstar :=
        Set.mem_uIcc.mpr (Or.inr ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      simpa only [hΓ'def] using hsegball _ h1
    refine crossing_of_trans hr hcont hblow hgt hΓ'cont hΓ'mem ?_ ?_ hΓ'ball hρH' hρL' hρP' hH' hLesc
    · show Γ (τ + tstar - tstar) ∈ P.Nm
      rw [show τ + tstar - tstar = τ by ring]
      exact hτNm
    · show Γ (τ + tstar - τ) ∉ P.Nm
      rw [show τ + tstar - τ = tstar by ring]
      exact htsNm

end Work.PARIMPL2.Lavaurs

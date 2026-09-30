import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Work.OddBound.longHomotopy

open Set Filter Metric Topology

/-- **The first crossing of a level.**

Let `g` be continuous on `[0,S]` with `g 0 < lam` and with some point of `[0,S]` where `lam ≤ g`.
Then there is a *first* such point `τ`: `g τ = lam` and `lam ≤ g σ` implies `τ ≤ σ` for `σ ∈ [0,S]`. -/
private lemma exists_first_crossing {g : ℝ → ℝ} {S lam : ℝ}
    (hg : ContinuousOn g (Set.Icc 0 S)) (h0 : g 0 < lam)
    (hex : ∃ σ ∈ Set.Icc 0 S, lam ≤ g σ) :
    ∃ τ ∈ Set.Icc 0 S, g τ = lam ∧ ∀ σ ∈ Set.Icc 0 S, lam ≤ g σ → τ ≤ σ := by
  haveI : CompactSpace (↥(Set.Icc (0:ℝ) S)) := isCompact_iff_compactSpace.mp isCompact_Icc
  set g' : ↥(Set.Icc (0:ℝ) S) → ℝ := fun σ => g σ.1 with hg'def
  have hg' : Continuous g' := hg.domRestrict
  obtain ⟨σ₀, hσ₀⟩ := hex
  have hAne : {σ : ↥(Set.Icc (0:ℝ) S) | lam ≤ g' σ}.Nonempty := ⟨⟨σ₀, hσ₀.1⟩, hσ₀.2⟩
  have hAcl : IsClosed {σ : ↥(Set.Icc (0:ℝ) S) | lam ≤ g' σ} := isClosed_Ici.preimage hg'
  obtain ⟨τ, hτA, hτmin⟩ :=
    IsCompact.exists_isMinOn hAcl.isCompact hAne continuous_subtype_val.continuousOn
  have hτA' : lam ≤ g' τ := hτA
  have hτmem : τ.1 ∈ Set.Icc (0:ℝ) S := τ.2
  have hge : lam ≤ g τ.1 := hτA'
  have hτ0 : τ.1 ≠ 0 := by
    intro h
    have h2 : g' τ = g 0 := by rw [hg'def]; exact congrArg g h
    rw [h2] at hτA'
    linarith
  have hτpos : 0 < τ.1 := lt_of_le_of_ne hτmem.1 (Ne.symm hτ0)
  have hbound : ∀ k : ℕ, max 0 (τ.1 - 1/(k+1 : ℝ)) < τ.1 := by
    intro k
    refine max_lt hτpos ?_
    have : (0:ℝ) < (k+1 : ℝ) := by positivity
    have := one_div_pos.mpr this
    linarith
  set seq : ℕ → ↥(Set.Icc (0:ℝ) S) := fun k =>
    ⟨max 0 (τ.1 - 1/(k+1 : ℝ)), by
      refine ⟨le_max_left _ _, ?_⟩
      exact le_trans (le_of_lt (hbound k)) hτmem.2⟩ with hseqdef
  have hseqval : ∀ k, (seq k).1 = max 0 (τ.1 - 1/(k+1 : ℝ)) := fun k => rfl
  have hseqtend : Tendsto (fun k => (seq k).1) atTop (nhds τ.1) := by
    have hc : Tendsto (fun _ : ℕ => τ.1) atTop (nhds τ.1) := tendsto_const_nhds
    have hd : Tendsto (fun k : ℕ => 1/(k+1 : ℝ)) atTop (nhds (0:ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun k : ℕ => τ.1 - 1/(k+1 : ℝ)) atTop (nhds (τ.1 - 0)) := hc.sub hd
    have h1' : Tendsto (fun k : ℕ => τ.1 - 1/(k+1 : ℝ)) atTop (nhds τ.1) := by simpa using h1
    have h2 : Tendsto (fun k : ℕ => max 0 (τ.1 - 1/(k+1 : ℝ))) atTop (nhds (max 0 τ.1)) :=
      (continuous_const.max continuous_id).tendsto _ |>.comp h1'
    have h3 : max 0 τ.1 = τ.1 := max_eq_right hτmem.1
    rw [h3] at h2
    refine h2.congr' ?_
    filter_upwards with k
    rw [hseqval k]
  have hnotA : ∀ k, ¬ (lam ≤ g ((seq k).1)) := by
    intro k hk
    have hmem : seq k ∈ {σ : ↥(Set.Icc (0:ℝ) S) | lam ≤ g' σ} := by
      show lam ≤ g' (seq k)
      rw [hg'def]
      exact hk
    have hh : τ.1 ≤ (seq k).1 := hτmin hmem
    rw [hseqval k] at hh
    exact absurd hh (not_le.mpr (hbound k))
  have hle : g τ.1 ≤ lam := by
    have hseqWithin : Tendsto (fun k => (seq k).1) atTop (nhdsWithin τ.1 (Set.Icc (0:ℝ) S)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hseqtend, Eventually.of_forall fun k => (seq k).2⟩
    refine le_of_tendsto (((hg.continuousWithinAt hτmem).tendsto).comp hseqWithin) ?_
    exact Eventually.of_forall fun k => le_of_lt (not_le.mp (hnotA k))
  refine ⟨τ.1, hτmem, le_antisymm hle hge, ?_⟩
  intro σ hσ hl
  have hmem : (⟨σ, hσ⟩ : ↥(Set.Icc (0:ℝ) S)) ∈ {σ : ↥(Set.Icc (0:ℝ) S) | lam ≤ g' σ} := by
    show lam ≤ g' _
    rw [hg'def]
    exact hl
  exact hτmin hmem

/-- **The abstract core of the parametric lifting argument.**

`f : X → Y` continuous and locally injective on the open ball of radius `R` in a
finite-dimensional normed space `X`; `Φ : ℝ × ℝ → Y` continuous; `W : ℝ → ℝ → X` with
slice-wise continuous `s ↦ W s t` on `[0,S]`, `W 0 t = 0`, `f (W s t) = Φ (s,t)` and
`‖W s t‖ < R` on `[0,S] × [0,1]`.  Then `(s,t) ↦ W s t` is continuous on the rectangle. -/
theorem lift_family_continuity_core
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [CompleteSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {R : ℝ}
    (hloc : ∀ v : X, ‖v‖ < R → ∃ u ∈ nhds v, ∀ w ∈ u, ∀ w' ∈ u, f w = f w' → w = w')
    {Φ : ℝ × ℝ → Y} (hΦ : Continuous Φ)
    {W : ℝ → ℝ → X} {S : ℝ}
    (hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContinuousOn (fun s : ℝ => W s t) (Set.Icc (0 : ℝ) S))
    (hzero : ∀ t ∈ Set.Icc (0 : ℝ) 1, W 0 t = 0)
    (hG : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S, f (W s t) = Φ (s, t))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s t‖ < R) :
    ContinuousOn (fun u : ℝ × ℝ => W u.1 u.2) (Set.Icc (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1) := by
  classical
  intro u₀ hu₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_contra hcon
  push Not at hcon
  choose g hg using fun n : ℕ => hcon (1/(n+1 : ℝ)) (by positivity)
  have hu₀1 : u₀.1 ∈ Set.Icc (0:ℝ) S := (mem_prod.mp hu₀).1
  have hu₀2 : u₀.2 ∈ Set.Icc (0:ℝ) 1 := (mem_prod.mp hu₀).2
  have hg1 : ∀ n, (g n).1 ∈ Set.Icc (0:ℝ) S := fun n => (mem_prod.mp (hg n).1).1
  have hgt : ∀ n, (g n).2 ∈ Set.Icc (0:ℝ) 1 := fun n => (mem_prod.mp (hg n).1).2
  have hgd : ∀ n, dist (g n) u₀ < 1/(n+1 : ℝ) := fun n => (hg n).2.1
  have hgε : ∀ n, ε ≤ dist (W (g n).1 (g n).2) (W u₀.1 u₀.2) := fun n => (hg n).2.2
  have hg_lim : Tendsto g atTop (nhds u₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hgd n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs_lim : Tendsto (fun n => (g n).1) atTop (nhds u₀.1) :=
    (continuous_fst.tendsto u₀).comp hg_lim
  have ht_lim : Tendsto (fun n => (g n).2) atTop (nhds u₀.2) :=
    (continuous_snd.tendsto u₀).comp hg_lim
  have hsT_lim : Tendsto (fun n => W (g n).1 u₀.2) atTop (nhds (W u₀.1 u₀.2)) :=
    ((hslice u₀.2 hu₀2).continuousWithinAt hu₀1).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hs_lim, Eventually.of_forall hg1⟩)
  -- the deviation is bounded below by `ε/2` along the bad sequence
  have hdev : ∀ᶠ n in atTop, ε/2 ≤ ‖W (g n).1 (g n).2 - W (g n).1 u₀.2‖ := by
    have hmem : {x : X | ‖x - W u₀.1 u₀.2‖ < ε/2} ∈ nhds (W u₀.1 u₀.2) := by
      have hb' : ball (W u₀.1 u₀.2) (ε/2) ∈ nhds (W u₀.1 u₀.2) := ball_mem_nhds _ (by linarith)
      refine Filter.mem_of_superset hb' ?_
      intro x hx
      rw [mem_ball, dist_eq_norm] at hx
      exact hx
    have hhalf : ∀ᶠ n in atTop, ‖W (g n).1 u₀.2 - W u₀.1 u₀.2‖ < ε/2 := hsT_lim.eventually hmem
    filter_upwards [hhalf] with n hn
    have h1 : ε ≤ ‖W (g n).1 (g n).2 - W u₀.1 u₀.2‖ := by
      rw [← dist_eq_norm]; exact hgε n
    have h2 : ‖W (g n).1 (g n).2 - W u₀.1 u₀.2‖
        ≤ ‖W (g n).1 (g n).2 - W (g n).1 u₀.2‖ + ‖W (g n).1 u₀.2 - W u₀.1 u₀.2‖ := by
      have h3 := norm_add_le (W (g n).1 (g n).2 - W (g n).1 u₀.2) (W (g n).1 u₀.2 - W u₀.1 u₀.2)
      rwa [sub_add_sub_cancel] at h3
    linarith
  -- ## the collision produced by crossing each level `lam < ε/2`
  have hclaim : ∀ lam : ℝ, 0 < lam → lam < ε/2 → ∃ τ ∈ Set.Icc (0:ℝ) S, ∃ v : X,
      f v = f (W τ u₀.2) ∧ ‖v - W τ u₀.2‖ = lam := by
    intro lam hlam0 hlamε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hdev.mono (fun n hn => le_trans hlamε.le hn))
    -- the first crossing time of the level `lam` along the `n`-th slice pair
    have hcross : ∀ n : ℕ, N ≤ n → ∃ τ ∈ Set.Icc (0:ℝ) S,
        ‖W τ (g n).2 - W τ u₀.2‖ = lam ∧ ∀ σ ∈ Set.Icc (0:ℝ) S,
          lam ≤ ‖W σ (g n).2 - W σ u₀.2‖ → τ ≤ σ := by
      intro n hn
      refine exists_first_crossing ((hslice (g n).2 (hgt n)).sub (hslice u₀.2 hu₀2)).norm ?_ ?_
      · rw [hzero (g n).2 (hgt n), hzero u₀.2 hu₀2, sub_zero, norm_zero]
        exact hlam0
      · exact ⟨(g n).1, hg1 n, hN n hn⟩
    have hspec : ∀ n : ℕ, ∃ τ ∈ Set.Icc (0:ℝ) S,
        ‖W τ (g (n+N)).2 - W τ u₀.2‖ = lam ∧ ∀ σ ∈ Set.Icc (0:ℝ) S,
          lam ≤ ‖W σ (g (n+N)).2 - W σ u₀.2‖ → τ ≤ σ :=
      fun n => hcross (n+N) (Nat.le_add_left N n)
    choose τ hτ using hspec
    -- the crossing points live in a compact set
    have hzmem : ∀ n, ((τ n, W (τ n) (g (n+N)).2) : ℝ × X)
        ∈ Set.Icc (0:ℝ) S ×ˢ Metric.closedBall (0 : X) R := by
      intro n
      refine ⟨(hτ n).1, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact le_of_lt (hb (g (n+N)).2 (hgt (n+N)) (τ n) (hτ n).1)
    obtain ⟨z₀, hz₀, φ, hφ, hzlim⟩ := IsCompact.tendsto_subseq
      (isCompact_Icc.prod (isCompact_closedBall (0:X) R)) hzmem
    have hlimτ : Tendsto (fun k => τ (φ k)) atTop (nhds z₀.1) :=
      (continuous_fst.tendsto z₀).comp hzlim
    have hlimv : Tendsto (fun k => W (τ (φ k)) (g (φ k + N)).2) atTop (nhds z₀.2) :=
      (continuous_snd.tendsto z₀).comp hzlim
    have htlim : Tendsto (fun k => (g (φ k + N)).2) atTop (nhds u₀.2) :=
      ht_lim.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop)
    have hWtlim : Tendsto (fun k => W (τ (φ k)) u₀.2) atTop (nhds (W z₀.1 u₀.2)) :=
      ((hslice u₀.2 hu₀2).continuousWithinAt hz₀.1).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hlimτ, Eventually.of_forall fun k => (hτ (φ k)).1⟩)
    -- the limit points are at distance exactly `lam`
    have hnorm_eq : ‖z₀.2 - W z₀.1 u₀.2‖ = lam := by
      refine tendsto_nhds_unique ((hlimv.sub hWtlim).norm) ?_
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
      exact ((hτ (φ k)).2.1).symm
    -- and they have the same `f`-image
    have hf_eq : f z₀.2 = Φ (z₀.1, u₀.2) := by
      refine tendsto_nhds_unique ((hf.tendsto z₀.2).comp hlimv) ?_
      have hpair : Tendsto (fun k => (τ (φ k), (g (φ k + N)).2)) atTop (nhds (z₀.1, u₀.2)) := by
        rw [nhds_prod_eq]
        exact tendsto_prod_iff'.mpr ⟨hlimτ, htlim⟩
      refine ((hΦ.tendsto (z₀.1, u₀.2)).comp hpair).congr' (Eventually.of_forall fun k => ?_)
      exact ((hG (g (φ k + N)).2 (hgt (φ k + N)) (τ (φ k)) (hτ (φ k)).1)).symm
    exact ⟨z₀.1, hz₀.1, z₀.2, hf_eq.trans (hG u₀.2 hu₀2 z₀.1 hz₀.1).symm, hnorm_eq⟩
  -- ## collisions at arbitrarily small distances
  have hget : ∀ j : ℕ, ∃ p : ℝ × X,
      p.1 ∈ Set.Icc (0:ℝ) S ∧ f p.2 = f (W p.1 u₀.2) ∧
        ‖p.2 - W p.1 u₀.2‖ = ε/(2*((j:ℝ)+2)) := by
    intro j
    have hpos : 0 < ε/(2*((j:ℝ)+2)) := by positivity
    have hlt : ε/(2*((j:ℝ)+2)) < ε/2 := by
      have h4 : (4:ℝ) ≤ 2*((j:ℝ)+2) := by
        have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith
      have hle : ε/(2*((j:ℝ)+2)) ≤ ε/4 := div_le_div_of_nonneg_left hε.le (by norm_num) h4
      linarith
    obtain ⟨τ, hτ, v, hv1, hv2⟩ := hclaim _ hpos hlt
    exact ⟨(τ, v), hτ, hv1, hv2⟩
  choose w hw using hget
  obtain ⟨τinf, hτinf, φ, hφ, hτlim⟩ := IsCompact.tendsto_subseq isCompact_Icc (fun j => (hw j).1)
  have hWlim : Tendsto (fun k => W ((w (φ k)).1) u₀.2) atTop (nhds (W τinf u₀.2)) :=
    ((hslice u₀.2 hu₀2).continuousWithinAt hτinf).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hτlim, Eventually.of_forall fun k => (hw (φ k)).1⟩)
  have hdiffnorm : Tendsto (fun k => ‖(w (φ k)).2 - W ((w (φ k)).1) u₀.2‖) atTop (nhds 0) := by
    have hden : Tendsto (fun k : ℕ => 2*((φ k : ℝ)+2)) atTop atTop := by
      have h1 : Tendsto (fun k : ℕ => ((φ k : ℝ) + 2)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).atTop_add tendsto_const_nhds
      exact h1.const_mul_atTop (by norm_num)
    have h0 : Tendsto (fun k : ℕ => ε/(2*((φ k : ℝ)+2))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden
    refine h0.congr' (Eventually.of_forall fun k => ?_)
    exact ((hw (φ k)).2.2).symm
  have hvlim : Tendsto (fun k => (w (φ k)).2) atTop (nhds (W τinf u₀.2)) := by
    have hdiff : Tendsto (fun k => (w (φ k)).2 - W ((w (φ k)).1) u₀.2) atTop (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa using hdiffnorm
    have h2 : Tendsto (fun k => W ((w (φ k)).1) u₀.2 + ((w (φ k)).2 - W ((w (φ k)).1) u₀.2))
        atTop (nhds (W τinf u₀.2 + 0)) := hWlim.add hdiff
    rw [add_zero] at h2
    refine h2.congr' (Eventually.of_forall fun k => ?_)
    abel
  -- ## contradiction with local injectivity at the common limit
  have hnorm : ‖W τinf u₀.2‖ < R := hb u₀.2 hu₀2 τinf hτinf
  obtain ⟨S₀, hS₀, hS₀inj⟩ := hloc (W τinf u₀.2) hnorm
  have hev1 : ∀ᶠ k in atTop, (w (φ k)).2 ∈ S₀ := hvlim.eventually hS₀
  have hev2 : ∀ᶠ k in atTop, W ((w (φ k)).1) u₀.2 ∈ S₀ := hWlim.eventually hS₀
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  have hfeqk : f ((w (φ k)).2) = f (W ((w (φ k)).1) u₀.2) := (hw (φ k)).2.1
  have hcontr := hS₀inj ((w (φ k)).2) hk1 (W ((w (φ k)).1) u₀.2) hk2 hfeqk
  have hzero' : ε/(2*((φ k : ℝ)+2)) = 0 := by
    rw [← (hw (φ k)).2.2, hcontr, sub_self, norm_zero]
  have hpos' : 0 < ε/(2*((φ k : ℝ)+2)) := by positivity
  linarith

end Work.OddBound.longHomotopy

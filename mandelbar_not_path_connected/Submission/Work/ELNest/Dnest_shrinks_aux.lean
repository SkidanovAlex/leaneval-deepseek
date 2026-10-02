/-
# EL nest at `b₂`: the inverse branch `g₆` and its iterates

This file collects the elementary facts about the level-`n` regions `Δ̂ₙ = S.D n` of the nest at
the branch point `b₂` and about the inverse branch `g₆ = S.g6` of `f_c^6 = F6 c` that the proof of
`Work.ELNest.Dnest_shrinks` (the nest shrinks to `b₂`) needs.

The two structural inputs are the fields
* `NestData.pbD n : BijOn (F6 c) (S.D (n+1)) (S.D n)` (the level-`n+1` region is the pull-back of
  the level-`n` region), and
* `NestData.g6_left`, `NestData.g6_mem` (`g₆` is the inverse branch on `Δ̂₀`, mapping into `Δ̂₁`).
Together with the injectivity of `F6 c` on `Δ̂₁` (which follows from `pbD 0`) they show that `g₆`
is a *bijection* `Δ̂ₙ → Δ̂ₙ₊₁` for every `n`, i.e.

  `S.g6 '' S.D n = S.D (n+1)`  and  `(S.g6^[n]) '' S.D 0 = S.D n`,

so the nest is exactly the orbit of `Δ̂₀` under `g₆`.  Consequently the sequence of iterates
`g₆^[n]` is a normal family on `Δ̂₀` (Montel: it is holomorphic and its images all lie in the
bounded set `Δ̂₀`), and the main theorem of this file says that every locally uniform limit of a
subsequence of `g₆^[n]` agrees with the constant `b₂` on `Δ̂₀`.

The argument for the latter is the one of `NOTES_LEAD_mandelbar_EL_F_contracts.md` (N4): if `ψ` is a
locally uniform limit of `g₆^[n k]` and `ψ` were non-constant, then, taking a sparse subsequence
`m` of the gaps and a further subsequence along which `g₆^[m]` converges to `φ`, one has
`(φ - id) ∘ ψ = 0` on `Δ̂₀`; since `ψ` is non-constant, the zeros of the analytic function `φ - id`
accumulate and the identity theorem gives `φ = id`, whence `Δ̂₀ = φ '' Δ̂₀ ⊆ closure Δ̂₁ ⊆ Δ̂₀` by
`Dnest_cl`.  So `Δ̂₀ = closure Δ̂₁` would be a non-empty clopen subset of `ℂ`, hence all of `ℂ`,
contradicting the boundedness of `Δ̂₀`.  The constant is identified as `b₂` because `g₆` fixes
`b₂`.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.Normal.isNormalFamily_of_tendsto_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology
open scoped Topology

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-! ## Elementary facts about the nest at `b₂` -/

theorem NestData.D_def (S : NestData c) (n : ℕ) :
    S.D n = polyRegion [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n) := rfl

/-- The levels of the nest at `b₂` are decreasing: `Δ̂ₘ ⊇ Δ̂ₙ` for `m ≤ n`. -/
theorem NestData.D_anti (S : NestData c) : ∀ {m n : ℕ}, m ≤ n → S.D n ⊆ S.D m := by
  intro m n hmn
  induction hmn with
  | refl => exact fun _ hz => hz
  | step hmn ih => exact fun z hz => ih (S.Dnest_sub _ hz)

/-- `b₂` is fixed by `f_c^6`. -/
theorem NestData.F6_b2 (S : NestData c) : F6 c S.b2 = S.b2 := by
  have h : Function.IsFixedPt (Work.Landing.Tsq c) S.b2 := S.b2_fix
  show (Work.Landing.Tsq c)^[3] S.b2 = S.b2
  exact h.iterate 3

/-- The inverse branch `g₆` fixes `b₂`. -/
theorem NestData.g6_b2 (S : NestData c) : S.g6 S.b2 = S.b2 := by
  have h1 : S.g6 S.b2 ∈ S.D 1 := S.g6_mem _ (S.b2_mem_D 0)
  have h2 : F6 c (S.g6 S.b2) = S.b2 := S.g6_left _ (S.b2_mem_D 0)
  exact (S.pbD 0).injOn h1 (S.b2_mem_D 1) (by rw [h2, S.F6_b2])

/-- `b₂` is fixed by every iterate of `g₆`. -/
theorem NestData.g6_iterate_fix (S : NestData c) (p : ℕ) : (S.g6^[p]) S.b2 = S.b2 := by
  induction p with
  | zero => rfl
  | succ q ih => rw [Function.iterate_succ_apply', ih, S.g6_b2]

/-- **`g₆` is a bijection `Δ̂ₙ → Δ̂ₙ₊₁`.**  The point `g₆ z` and the (unique) point `u ∈ Δ̂ₙ₊₁`
with `F6 u = z` both lie in `Δ̂₁` and have the same image under `F6`, which is injective there. -/
theorem NestData.g6_image (S : NestData c) (n : ℕ) : S.g6 '' S.D n = S.D (n + 1) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro w ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hFu⟩ := (S.pbD n).surjOn hz
    have hzD0 : z ∈ S.D 0 := S.D_anti (Nat.zero_le n) hz
    have hun : S.g6 z ∈ S.D 1 := S.g6_mem z hzD0
    have hu1 : u ∈ S.D 1 := S.D_anti (Nat.succ_le_succ (Nat.zero_le n)) hu
    have huu : u = S.g6 z := (S.pbD 0).injOn hu1 hun (by rw [hFu, S.g6_left z hzD0])
    rwa [huu] at hu
  · intro v hv
    refine ⟨F6 c v, (S.pbD n).mapsTo hv, ?_⟩
    have hvD0 : F6 c v ∈ S.D 0 := S.D_anti (Nat.zero_le n) ((S.pbD n).mapsTo hv)
    have h1 : S.g6 (F6 c v) ∈ S.D 1 := S.g6_mem _ hvD0
    have h3 : v ∈ S.D 1 := S.D_anti (Nat.succ_le_succ (Nat.zero_le n)) hv
    exact (S.pbD 0).injOn h1 h3 (by rw [S.g6_left _ hvD0])

/-- **`Δ̂ₙ` is the `n`-th iterate of `Δ̂₀` under `g₆`.** -/
theorem NestData.g6_iterate_image (S : NestData c) (n : ℕ) :
    (S.g6^[n]) '' S.D 0 = S.D n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Set.image_comp, ih, S.g6_image]

/-- `g₆` maps `Δ̂₀` into itself. -/
theorem NestData.MapsTo_g6 (S : NestData c) : MapsTo S.g6 (S.D 0) (S.D 0) := by
  intro z hz
  have h1 : S.g6 z ∈ S.D (0 + 1) := by
    rw [← S.g6_image 0]
    exact ⟨z, hz, rfl⟩
  exact (S.Dnest_sub 0) h1

/-! ## The potential and boundedness -/

/-- Every level of the nest lies below its potential level `log (Dlev L n)`. -/
theorem NestData.D_subset_pot (S : NestData c) (n : ℕ) :
    S.D n ⊆ {z | pot S.d.hN z < Real.log (Dlev S.L n)} := by
  intro z hz
  rw [S.D_def] at hz
  rw [S.Dmem n] at hz
  exact hz.2

namespace NestData

/-- `Dlev L 0 = L`. -/
theorem Dlev_zero (L : ℝ) : Dlev L 0 = L := by
  simp [Dlev]

/-- The levels `Dlev L n = L ^ (1/64^n)` decrease with `n`. -/
theorem Dlev_anti {L : ℝ} (hL : 1 < L) {m n : ℕ} (hmn : m ≤ n) : Dlev L n ≤ Dlev L m := by
  rw [Dlev, Dlev, Real.rpow_le_rpow_left_iff hL]
  refine one_div_le_one_div_of_le (pow_pos (by norm_num) m) ?_
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 64) hmn

end NestData

/-- `Δ̂₀` is bounded (it lies below the equipotential of level `L > 1`). -/
theorem NestData.D_bounded (S : NestData c) : Bornology.IsBounded (S.D 0) := by
  refine ((isCompact_le_pot S.d.hN (Real.log S.L)).isBounded).subset ?_
  intro z hz
  have h : pot S.d.hN z < Real.log S.L := by
    have h0 := S.D_subset_pot 0 hz
    rwa [NestData.Dlev_zero] at h0
  exact le_of_lt h

/-- Every level of the nest lies in the fixed compact set `{pot ≤ log L}`. -/
theorem NestData.D_subset_potL (S : NestData c) (n : ℕ) :
    S.D n ⊆ {z | pot S.d.hN z ≤ Real.log S.L} := by
  intro z hz
  have h := S.D_subset_pot n hz
  have h2 : Real.log (Dlev S.L n) ≤ Real.log S.L := by
    have h3 : Dlev S.L n ≤ Dlev S.L 0 := NestData.Dlev_anti S.hL (Nat.zero_le n)
    rw [NestData.Dlev_zero] at h3
    exact Real.log_le_log (lt_trans zero_lt_one (Real.one_lt_rpow S.hL (by positivity))) h3
  exact le_of_lt (lt_of_lt_of_le h h2)

/-- Each level of the nest is open. -/
theorem NestData.isOpen_D (S : NestData c) (n : ℕ) : IsOpen (S.D n) := by
  rw [S.D_def]
  exact Work.ELTop.isOpen_polyRegion S.d.hN [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n)
    (Work.ELTop.isClosed_polyCurve S.d.hN [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n))

/-- `Δ̂₀` is preconnected (it is the region of a ray polygon). -/
theorem NestData.isPreconnected_D0 (S : NestData c) : IsPreconnected (S.D 0) :=
  isPreconnected_polyRegion _ _

/-! ## The iterates of `g₆` form a normal family on `Δ̂₀` -/

theorem NestData.g6_diff_iterate (S : NestData c) (n : ℕ) :
    DifferentiableOn ℂ (S.g6^[n]) (S.D 0) :=
  S.g6_diff.iterate S.MapsTo_g6 n

/-- Montel: the family of iterates of `g₆` is normal on `Δ̂₀`. -/
theorem NestData.isNormalFamily_g6 (S : NestData c) :
    Work.Normal.IsNormalFamily (Set.range (fun n : ℕ => S.g6^[n])) (S.D 0) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ {z | pot S.d.hN z ≤ Real.log S.L}, ‖z‖ ≤ M := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (isCompact_le_pot S.d.hN (Real.log S.L)).isBounded
    exact ⟨r, fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hr hz⟩
  refine Work.Normal.montel_locallyBounded (S.isOpen_D 0) (fun f hf => ?_) ?_
  · obtain ⟨n, rfl⟩ := hf
    exact S.g6_diff_iterate n
  · intro K hKU hKc
    exact ⟨M, fun f hf z hz => by
      obtain ⟨n, rfl⟩ := hf
      refine hM _ ?_
      have hmem : (S.g6^[n]) z ∈ S.D n := by
        rw [← S.g6_iterate_image n]
        exact ⟨z, hKU hz, rfl⟩
      exact S.D_subset_potL n hmem⟩

/-- Every locally uniform limit of a subsequence of the iterates of `g₆` takes its values in
`closure Δ̂₁` on `Δ̂₀`. -/
theorem NestData.g6_lim_sub_closure (S : NestData c) (M : ℕ → ℕ) (χ : ℂ → ℂ)
    (hM : Tendsto M atTop atTop)
    (hχ : TendstoLocallyUniformlyOn (fun k => S.g6^[M k]) χ atTop (S.D 0)) :
    ∀ z ∈ S.D 0, χ z ∈ closure (S.D 1) := by
  intro z hz
  refine mem_closure_of_tendsto (hχ.tendsto_at hz) ?_
  filter_upwards [tendsto_atTop.mp hM 1] with k hk
  exact S.D_anti hk (by rw [← S.g6_iterate_image (M k)]; exact ⟨z, hz, rfl⟩)


/-- The iterates of `g₆` do not tend to infinity locally uniformly on `Δ̂₀`: they all fix `b₂`. -/
theorem NestData.not_tendsto_atTop_g6 (S : NestData c) (M : ℕ → ℕ) :
    ¬ Work.Normal.TendstoLocallyUniformlyAtTop (fun k => S.g6^[M k]) (S.D 0) := by
  intro h
  have hsub : ({S.b2} : Set ℂ) ⊆ S.D 0 := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact S.b2_mem_D 0
  obtain ⟨B, hB⟩ := h {S.b2} hsub isCompact_singleton (‖S.b2‖ + 1)
  have h1 : (S.g6^[M B]) S.b2 = S.b2 := S.g6_iterate_fix (M B)
  have h1' : (fun k => S.g6^[M k]) B S.b2 = S.b2 := by simpa using h1
  have h2 := hB B le_rfl S.b2 rfl
  rw [h1'] at h2
  linarith [norm_nonneg S.b2]

/-- **All locally uniform limits of the iterates of `g₆` are the constant `b₂`.** -/
theorem NestData.g6_lim_eq_const (S : NestData c) (N : ℕ → ℕ) (ψ : ℂ → ℂ)
    (hN : Tendsto N atTop atTop)
    (hψ : TendstoLocallyUniformlyOn (fun k => S.g6^[N k]) ψ atTop (S.D 0)) :
    Set.EqOn ψ (fun _ => S.b2) (S.D 0) := by
  have hb2D0 : S.b2 ∈ S.D 0 := S.b2_mem_D 0
  have hdiff : DifferentiableOn ℂ ψ (S.D 0) :=
    hψ.differentiableOn (Eventually.of_forall fun k => S.g6_diff_iterate (N k)) (S.isOpen_D 0)
  have han : AnalyticOnNhd ℂ ψ (S.D 0) := hdiff.analyticOnNhd (S.isOpen_D 0)
  have hb2val : ψ S.b2 = S.b2 := by
    have h1 : Tendsto (fun k => (S.g6^[N k]) S.b2) atTop (𝓝 (ψ S.b2)) := hψ.tendsto_at hb2D0
    have h2 : (fun k => (S.g6^[N k]) S.b2) = fun _ => S.b2 := by
      funext k; exact S.g6_iterate_fix (N k)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  by_cases hconst : ∀ᶠ W in 𝓝 S.b2, ψ W = S.b2
  · exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq han analyticOnNhd_const
      S.isPreconnected_D0 hb2D0 hconst
  · exfalso
    -- sparse reindexing: the gaps of the index sequence tend to infinity
    have hex : ∀ j (a : ℕ), ∃ i, a < i ∧ N a + (j + 1) ≤ N i := by
      intro j a
      obtain ⟨b, hb⟩ := eventually_atTop.mp (tendsto_atTop.mp hN (N a + (j + 1)))
      exact ⟨max (a + 1) b, lt_of_lt_of_le (Nat.lt_succ_self a) (le_max_left _ _),
        hb _ (le_max_right _ _)⟩
    let K : ℕ → ℕ := fun j => Nat.rec 0 (fun j prev => Classical.choose (hex j prev)) j
    have hK_succ : ∀ j, K (j + 1) = Classical.choose (hex j (K j)) := fun j => rfl
    have hK_lt : ∀ j, K j < K (j + 1) := fun j => by
      rw [hK_succ j]; exact (Classical.choose_spec (hex j (K j))).1
    have hK_gap : ∀ j, N (K j) + (j + 1) ≤ N (K (j + 1)) := fun j => by
      rw [hK_succ j]; exact (Classical.choose_spec (hex j (K j))).2
    have hKmono : StrictMono K := strictMono_nat_of_lt_succ hK_lt
    set m : ℕ → ℕ := fun j => N (K (j + 1)) - N (K j) with hm
    have hm_spec : ∀ j, N (K j) + m j = N (K (j + 1)) := by
      intro j
      exact Nat.add_sub_cancel' (le_trans (Nat.le_add_right _ _) (hK_gap j))
    have hm_ge : ∀ j, j + 1 ≤ m j := by
      intro j
      have h := hK_gap j
      rw [Nat.add_comm] at h
      exact Nat.le_sub_of_add_le h
    have hm_top : Tendsto m atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, fun j hj => le_trans (le_trans hj (Nat.le_succ j)) (hm_ge j)⟩
    -- the reindexed sequence still converges to `ψ`
    have hψK : TendstoLocallyUniformlyOn (fun j => S.g6^[N (K j)]) ψ atTop (S.D 0) :=
      Work.Normal.TendstoLocallyUniformlyOn.comp_strictMono_atTop (φ := K) hψ
        hKmono.tendsto_atTop
    -- extract a convergent subsequence of the gap sequence
    obtain ⟨φ, hφ, hcase⟩ := S.isNormalFamily_g6 (fun j => S.g6^[m j])
      (fun j => ⟨m j, rfl⟩)
    have hnot_top := S.not_tendsto_atTop_g6 (fun j => m (φ j))
    obtain ⟨χ, hχ⟩ : ∃ χ : ℂ → ℂ,
        TendstoLocallyUniformlyOn (fun j => S.g6^[m (φ j)]) χ atTop (S.D 0) := by
      rcases hcase with h | h
      · exact h
      · exact absurd h hnot_top
    have hmφ_top : Tendsto (fun j => m (φ j)) atTop atTop :=
      hm_top.comp hφ.tendsto_atTop
    have hχan : AnalyticOnNhd ℂ χ (S.D 0) :=
      (hχ.differentiableOn (Eventually.of_forall fun j => S.g6_diff_iterate (m (φ j)))
        (S.isOpen_D 0)).analyticOnNhd (S.isOpen_D 0)
    have hχcont : ContinuousOn χ (S.D 0) := hχan.continuousOn
    have hψD0 : ∀ z ∈ S.D 0, ψ z ∈ S.D 0 := fun z hz =>
      S.Dnest_cl (S.g6_lim_sub_closure N ψ hN hψ z hz)
    -- `χ ∘ ψ = ψ` pointwise
    have hrel : ∀ z ∈ S.D 0, χ (ψ z) = ψ z := by
      intro z hz
      have harg : Tendsto (fun j => (S.g6^[N (K (φ j))]) z) atTop (𝓝[S.D 0] (ψ z)) := by
        rw [(nhdsWithin_eq_nhds).mpr ((S.isOpen_D 0).mem_nhds (hψD0 z hz))]
        exact (hψK.tendsto_at hz).comp hφ.tendsto_atTop
      have hpt := hχ.tendsto_comp (hχcont.continuousWithinAt (hψD0 z hz)) (hψD0 z hz) harg
      have hidx : Tendsto (fun j => φ j + 1) atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro b
        obtain ⟨a, ha⟩ := tendsto_atTop_atTop.mp hφ.tendsto_atTop b
        exact ⟨a, fun j hj => by have := ha j hj; omega⟩
      have h2 : Tendsto (fun j => (S.g6^[N (K (φ j + 1))]) z) atTop (𝓝 (ψ z)) := by
        simpa [Function.comp_def] using (hψK.tendsto_at hz).comp hidx
      have hkey : (fun j => (S.g6^[m (φ j)]) ((S.g6^[N (K (φ j))]) z)) =
          (fun j => (S.g6^[N (K (φ j + 1))]) z) := by
        funext j
        rw [← Function.iterate_add_apply, Nat.add_comm, hm_spec (φ j)]
      rw [hkey] at hpt
      exact tendsto_nhds_unique hpt h2
    have hzero : ∀ z ∈ S.D 0, χ (ψ z) - ψ z = 0 := by
      intro z hz; rw [hrel z hz, sub_self]
    -- zeros of `χ - id` accumulate at `b₂`
    have hfreq : ∃ᶠ W in 𝓝[{S.b2}ᶜ] S.b2, χ W - W = 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
      obtain ⟨t, ht, htU⟩ := hU
      have hψcont : ContinuousAt ψ S.b2 :=
        hdiff.continuousOn.continuousAt ((S.isOpen_D 0).mem_nhds hb2D0)
      have hUt : ψ ⁻¹' t ∩ S.D 0 ∈ 𝓝 S.b2 :=
        inter_mem (hψcont.preimage_mem_nhds (hb2val.symm ▸ ht)) ((S.isOpen_D 0).mem_nhds hb2D0)
      have hnotsub : ¬ (ψ ⁻¹' t ∩ S.D 0 ⊆ {W : ℂ | ψ W = S.b2}) := by
        intro hsub
        exact hconst (Filter.mem_of_superset hUt hsub)
      simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
        not_forall] at hnotsub
      obtain ⟨z, hz1, hz2⟩ := hnotsub
      obtain ⟨hz1a, hz1b⟩ := hz1
      refine ⟨ψ z, htU ⟨hz1a, ?_⟩, hzero z hz1b⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hz2
    have hχid : ∀ z ∈ S.D 0, χ z = z := by
      have h0 : Set.EqOn (fun W => χ W - W) 0 (S.D 0) :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
          (hχan.sub analyticOnNhd_id) S.isPreconnected_D0 hb2D0 hfreq
      intro z hz
      have h1 := h0 hz
      simp only [Pi.zero_apply] at h1
      exact sub_eq_zero.mp h1
    -- `Δ̂₀ = χ '' Δ̂₀ ⊆ closure Δ̂₁ ⊆ Δ̂₀` is a non-empty clopen subset of `ℂ`
    have himg : χ '' S.D 0 = S.D 0 := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro w ⟨z, hz, rfl⟩
        rw [hχid z hz]
        exact hz
      · intro z hz
        exact ⟨z, hz, hχid z hz⟩
    have hsubχ : χ '' S.D 0 ⊆ closure (S.D 1) :=
      fun w ⟨z, hz, hzw⟩ =>
        hzw ▸ S.g6_lim_sub_closure (fun j => m (φ j)) χ hmφ_top hχ z hz
    have hD0eq : S.D 0 = closure (S.D 1) := by
      rw [← himg]
      exact Set.Subset.antisymm hsubχ (by rw [himg]; exact S.Dnest_cl)
    have hclopen : IsClopen (S.D 0) :=
      ⟨hD0eq.symm ▸ isClosed_closure, S.isOpen_D 0⟩
    have huniv : S.D 0 = Set.univ := hclopen.eq_univ ⟨S.b2, hb2D0⟩
    have hbdd : Bornology.IsBounded (Set.univ : Set ℂ) :=
      S.D_bounded.subset (le_of_eq huniv.symm)
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hbdd
    have hr1 : (1 : ℝ) ≤ r := by
      have h := hr (Set.mem_univ (1 : ℂ))
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_one] at h
      exact h
    have hmem := hr (Set.mem_univ (((r + 1 : ℝ)) : ℂ))
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
    have hnorm : ‖(((r + 1 : ℝ)) : ℂ)‖ = r + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r + 1)]
    rw [hnorm] at hmem
    linarith

/-- `Δ̂ₘ₊₁` is the image of `Δ̂₁` under `g₆^[m]`. -/
theorem NestData.g6_iterate_image_one (S : NestData c) (m : ℕ) :
    (S.g6^[m]) '' S.D 1 = S.D (m + 1) := by
  have hone : S.g6 '' S.D 0 = S.D 1 := by
    have h := S.g6_image 0
    rwa [show (0 : ℕ) + 1 = 1 from rfl] at h
  have h : (S.g6^[m + 1]) '' S.D 0 = S.D (m + 1) := S.g6_iterate_image (m + 1)
  rw [Function.iterate_succ, Set.image_comp, hone] at h
  exact h

/-- **The iterates of `g₆` converge to `b₂` locally uniformly on `Δ̂₀`.** -/
theorem NestData.g6_tendsto (S : NestData c) :
    TendstoLocallyUniformlyOn (fun n : ℕ => S.g6^[n]) (fun _ => S.b2) atTop (S.D 0) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (S.isOpen_D 0)]
  intro K hKU hKc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hex : ∀ N : ℕ, ∃ m, N ≤ m ∧ ∃ x ∈ K, ε ≤ dist S.b2 ((S.g6^[m]) x) := by
    intro N
    obtain ⟨m, hm, hfail⟩ := frequently_atTop.1 hcon N
    simp only [not_forall, not_lt] at hfail
    obtain ⟨x, hxK, hx⟩ := hfail
    exact ⟨m, hm, x, hxK, hx⟩
  choose m hm using hex
  choose y hy using fun N => (hm N).2
  have hm_top : Tendsto m atTop atTop := by
    rw [tendsto_atTop_atTop]
    exact fun b => ⟨b, fun a ha => le_trans ha (hm a).1⟩
  obtain ⟨φ, hφ, hcase⟩ := S.isNormalFamily_g6 (fun k => S.g6^[m k])
    (fun k => ⟨m k, rfl⟩)
  have hnot_top := S.not_tendsto_atTop_g6 (fun k => m (φ k))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun k => S.g6^[m (φ k)]) ψ atTop (S.D 0) := by
    rcases hcase with h | h
    · exact h
    · exact absurd h hnot_top
  have heq : Set.EqOn ψ (fun _ => S.b2) (S.D 0) :=
    S.g6_lim_eq_const (fun k => m (φ k)) ψ (hm_top.comp hφ.tendsto_atTop) hψ
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact (S.isOpen_D 0)).mp hψ
    K hKU hKc
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  have h1 := hN N le_rfl (y (φ N)) (hy (φ N)).1
  rw [heq (hKU (hy (φ N)).1)] at h1
  linarith [h1, (hy (φ N)).2]

end Work.ELNest

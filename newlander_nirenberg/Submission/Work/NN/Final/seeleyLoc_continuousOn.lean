import Mathlib
import Submission.Work.NN.Final.SeeleyLoc

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

namespace Work.NN.Final

/-! ## A local uniform bound on a tube near the boundary -/

/-- **Local uniform bound on a tube.**  If `g` is continuous on the `W`-restricted closed upper
half space `seHp W = W × [0,∞)` and `x ∈ W`, then for the normal coordinate in a fixed compact
interval `[0,ρ]` the values `g (y,s)` are bounded for `y ∈ W` close to `x`.

The point is that `{x} × [0,ρ]` is a compact subset of `seHp W` *in the `ℝ`-direction*, so the
finitely many local bounds given by continuity at the points `(x,s)` can be combined into one. -/
lemma seeley_tube_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} (hW : IsOpen W) {g : E × ℝ → ℂ}
    (hg : ContinuousOn g (seHp W)) {x : E} (hx : x ∈ W) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ W, ‖y - x‖ < r → ∀ s ∈ Set.Icc (0:ℝ) ρ, ‖g (y, s)‖ ≤ C := by
  classical
  have hstep : ∀ s ∈ Set.Icc (0:ℝ) ρ, ∃ A : Set E, ∃ B : Set ℝ,
      A ∈ 𝓝 x ∧ B ∈ 𝓝 s ∧
      ∀ y ∈ A, ∀ s' ∈ B, y ∈ W → 0 ≤ s' → ‖g (y, s')‖ ≤ ‖g (x, s)‖ + 1 := by
    intro s hs
    have hz : (x, s) ∈ seHp W := by rw [mem_seHp]; exact ⟨hx, hs.1⟩
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hg.continuousWithinAt hz)) 1 (by norm_num)
    refine ⟨Metric.ball x δ, Metric.ball s δ, Metric.ball_mem_nhds x hδpos,
      Metric.ball_mem_nhds s hδpos, ?_⟩
    intro y hy s' hs' hyW hs'0
    have hmem : (y, s') ∈ seHp W := by rw [mem_seHp]; exact ⟨hyW, hs'0⟩
    have hdist : dist (y, s') (x, s) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp hy) (Metric.mem_ball.mp hs')
    have h1 := hδ hmem hdist
    rw [dist_eq_norm] at h1
    calc ‖g (y, s')‖ = ‖g (x, s) + (g (y, s') - g (x, s))‖ := by
          congr 1; abel
      _ ≤ ‖g (x, s)‖ + ‖g (y, s') - g (x, s)‖ := norm_add_le _ _
      _ ≤ ‖g (x, s)‖ + 1 := by linarith
  choose A B hAB using hstep
  obtain ⟨t, ht⟩ := (isCompact_Icc (a := (0:ℝ)) (b := ρ)).elim_nhds_subcover'
    (fun s hs => B s hs) (fun s hs => (hAB s hs).2.1)
  let Aall : Set E := ⋂ s ∈ t, A s.1 s.2
  let Call : ℝ := ∑ s ∈ t, (‖g (x, s.1)‖ + 1)
  have hAall : Aall ∈ 𝓝 x := by
    change (⋂ s ∈ t, A s.1 s.2) ∈ 𝓝 x
    rw [Filter.biInter_finset_mem]
    intro s _
    exact (hAB s.1 s.2).1
  have hCall_nonneg : 0 ≤ Call := by
    change 0 ≤ ∑ s ∈ t, (‖g (x, s.1)‖ + 1)
    exact Finset.sum_nonneg (fun i _ => by positivity)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hAall
  refine ⟨r, hrpos, Call, hCall_nonneg, ?_⟩
  intro y hyW hyr s' hs'
  obtain ⟨s₀, hs₀⟩ := Set.mem_iUnion.mp (ht hs')
  obtain ⟨hs₀t, hs₀B⟩ := Set.mem_iUnion.mp hs₀
  have hyA : y ∈ Aall := hrsub (Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hyr))
  have hyA₀ : y ∈ A s₀.1 s₀.2 := Set.mem_iInter.mp (Set.mem_iInter.mp hyA s₀) hs₀t
  have hbound := (hAB s₀.1 s₀.2).2.2 y hyA₀ s' hs₀B hyW hs'.1
  have hle : ‖g (x, s₀.1)‖ + 1 ≤ Call := by
    change ‖g (x, s₀.1)‖ + 1 ≤ ∑ s ∈ t, (‖g (x, s.1)‖ + 1)
    exact Finset.single_le_sum (f := fun s : ↥(Set.Icc (0:ℝ) ρ) => ‖g (x, s.1)‖ + 1)
      (fun i _ => by positivity) hs₀t
  exact le_trans hbound hle

/-! ## Continuity of the Seeley sum on the open lower slab -/

/-- The Seeley sum `seeleySum a b g` is continuous on the open lower slab `seLw W δ`.  At every
point of the slab the sum is locally finite (`eventuallyEq_finset_seeleySum`) and each term is
continuous there, because the shear `p ↦ (p.1, -(b m) * p.2)` maps `seLw W δ` into
`seUp W ⊆ seHp W`. -/
lemma seeleySum_continuousOn_seLw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {W : Set E} (hW : IsOpen W)
    {δ : ℝ} {g : E × ℝ → ℂ} (hg : ContinuousOn g (seHp W)) :
    ContinuousOn (seeleySum a b g) (seLw W δ) := by
  intro p hp
  rw [mem_seLw] at hp
  obtain ⟨hpW, _, hpneg⟩ := hp
  obtain ⟨S, hS⟩ := eventuallyEq_finset_seeleySum hb hbT g hpneg
  have hterm : ∀ m, ContinuousAt (seeleyTerm a b g m) p := by
    intro m
    have hΦc : ContinuousAt (fun q : E × ℝ => (q.1, -(b m) * q.2)) p := by fun_prop
    have hΦp : (p.1, -(b m) * p.2) ∈ seUp W := by
      rw [mem_seUp]
      refine ⟨hpW, ?_⟩
      show 0 < -(b m) * p.2
      rw [show -(b m) * p.2 = b m * (-p.2) from by ring]
      exact mul_pos (by linarith [hb m]) (by linarith)
    have hg_at : ContinuousAt g (p.1, -(b m) * p.2) :=
      (hg.mono seUp_subset_seHp).continuousAt ((isOpen_seUp hW).mem_nhds hΦp)
    have hcomp : ContinuousAt (fun q : E × ℝ => g (q.1, -(b m) * q.2)) p :=
      hg_at.comp (f := fun q : E × ℝ => (q.1, -(b m) * q.2)) hΦc
    have hcut : ContinuousAt (fun q : E × ℝ => seeleyCut (-(b m) * q.2)) p :=
      (seeleyCut_contDiff.continuous.comp
        (by fun_prop : Continuous fun q : E × ℝ => -(b m) * q.2)).continuousAt
    have htmp : ContinuousAt
        (fun q : E × ℝ => (a m) • (seeleyCut (-(b m) * q.2) • g (q.1, -(b m) * q.2))) p :=
      (hcut.smul hcomp).const_smul (a m)
    show ContinuousAt (fun q : E × ℝ => (a m) • (seeleyCut (-(b m) * q.2) • g (q.1, -(b m) * q.2))) p
    exact htmp
  have hfin : ContinuousAt (fun q => ∑ m ∈ S, seeleyTerm a b g m q) p :=
    tendsto_finsetSum S (fun m _ => hterm m)
  exact (hfin.congr_of_eventuallyEq hS).continuousWithinAt

/-! ## Continuity of the Seeley extension on the slab -/

/-- Continuity of the Seeley extension `seeleyExt a b g` on the `W`-restricted slab
`seSl W δ = W × (-δ,∞)`, for `δ > 0`, assuming `g` continuous on the closed upper half space
`seHp W` and the moment hypothesis `∑' m, a m = 1` together with `Summable (fun m => |a m|)`.

Intended proof: on the open upper half space the extension equals `g`, hence is continuous; on the
open lower slab it equals the locally finite sum `∑_m seeleyTerm a b g m` (use
`exists_finset_seeleyTerm_eq_zero`), hence is continuous there since each term is.  At a boundary
point `(x,0)`, `x ∈ W`, one shows `∑' m, a m * χ (-(b m) * t) * g (x, -(b m) * t) → g (x,0)` as
`t → 0⁻` by dominated convergence in `m`: the summands are dominated by `|a m|` times a bound for
`|g|` on a small ball around `(x,0)` intersected with `seHp W` (use `hg`), and converge pointwise to
`a m * g (x,0)` since `seeleyCut 0 = 1`; summing the limits and using `∑' m, a m = 1` gives `g (x,0)`. -/
theorem seeleyLoc_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) (ha : ∑' m, a m = 1)
    (hsum : Summable fun m => |a m|) {W : Set E} (hW : IsOpen W)
    {δ : ℝ} (hδ : 0 < δ) {g : E × ℝ → ℂ} (hg : ContinuousOn g (seHp W)) :
    ContinuousOn (seeleyExt a b g) (seSl W δ) := by
  intro p hp
  rw [mem_seSl] at hp
  obtain ⟨hpW, hpδ⟩ := hp
  rcases lt_trichotomy p.2 0 with hneg | hzero | hpos
  · -- the open lower slab
    have hpLw : p ∈ seLw W δ := by rw [mem_seLw]; exact ⟨hpW, hpδ, hneg⟩
    have hcont : ContinuousAt (seeleySum a b g) p :=
      (seeleySum_continuousOn_seLw hb hbT hW hg).continuousAt
        ((isOpen_seLw hW δ).mem_nhds hpLw)
    have hev : seeleyExt a b g =ᶠ[𝓝 p] seeleySum a b g :=
      Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hneg)
        (fun q hq => seeleyExt_of_neg a b g hq)
    exact (hcont.congr_of_eventuallyEq hev).continuousWithinAt
  · -- the boundary `p.2 = 0`
    have hp_mem : p ∈ seHp W := by rw [mem_seHp]; exact ⟨hpW, le_of_eq hzero.symm⟩
    -- `seSl W δ` is the union of the closed upper half space and the open lower slab
    have hsplit : seSl W δ = seHp W ∪ seLw W δ := by
      ext q
      simp only [mem_seSl, mem_seHp, mem_seLw, Set.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hq : 0 ≤ q.2
        · exact Or.inl ⟨h1, hq⟩
        · exact Or.inr ⟨h1, h2, lt_of_not_ge hq⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, _⟩)
        · exact ⟨h1, by linarith⟩
        · exact ⟨h1, by linarith⟩
    -- the limit from above
    have hUp : Tendsto (seeleyExt a b g) (𝓝[seHp W] p) (𝓝 (g p)) := by
      have hev : seeleyExt a b g =ᶠ[𝓝[seHp W] p] g :=
        Filter.eventuallyEq_of_mem self_mem_nhdsWithin
          (fun q hq => seeleyExt_of_nonneg a b g (by rw [mem_seHp] at hq; exact hq.2))
      exact Filter.Tendsto.congr' hev.symm (hg.continuousWithinAt hp_mem)
    -- the limit from below
    have hS : Tendsto (seeleySum a b g) (𝓝[seLw W δ] p) (𝓝 (g p)) := by
      obtain ⟨r, hrpos, C, hCnonneg, htube⟩ := seeley_tube_bound hW hg hpW (ρ := 2) (by norm_num)
      have hboundsum : Summable (fun m : ℕ => |a m| * C) := hsum.mul_right C
      have hlim : ∀ m, Tendsto (fun q : E × ℝ => seeleyTerm a b g m q)
          (𝓝[seLw W δ] p) (𝓝 (a m • g p)) := by
        intro m
        have hΦ : ContinuousWithinAt (fun q : E × ℝ => (q.1, -(b m) * q.2))
            (seLw W δ) p := by fun_prop
        have hmap : MapsTo (fun q : E × ℝ => (q.1, -(b m) * q.2)) (seLw W δ) (seHp W) := by
          intro q hq
          rw [mem_seLw] at hq
          have hmem : (q.1, -(b m) * q.2) ∈ seHp W := by
            rw [mem_seHp]
            refine ⟨hq.1, ?_⟩
            show 0 ≤ -(b m) * q.2
            rw [show -(b m) * q.2 = b m * (-q.2) from by ring]
            exact le_of_lt (mul_pos (by linarith [hb m]) (by linarith [hq.2.2]))
          exact hmem
        have hΦp : (p.1, -(b m) * p.2) ∈ seHp W := by
          rw [mem_seHp]
          refine ⟨hpW, ?_⟩
          rw [hzero, mul_zero]
        have hcomp : ContinuousWithinAt (fun q : E × ℝ => g (q.1, -(b m) * q.2))
            (seLw W δ) p :=
          (hg.continuousWithinAt hΦp).comp
            (f := fun q : E × ℝ => (q.1, -(b m) * q.2)) hΦ hmap
        have hcut : ContinuousWithinAt (fun q : E × ℝ => seeleyCut (-(b m) * q.2))
            (seLw W δ) p :=
          (seeleyCut_contDiff.continuous.comp
            (by fun_prop : Continuous fun q : E × ℝ => -(b m) * q.2)).continuousAt.continuousWithinAt
        have hsm : ContinuousWithinAt
            (fun q : E × ℝ => (a m) • (seeleyCut (-(b m) * q.2) • g (q.1, -(b m) * q.2)))
            (seLw W δ) p :=
          (hcut.smul hcomp).const_smul (a m)
        have hsm' : Tendsto (fun q : E × ℝ => seeleyTerm a b g m q) (𝓝[seLw W δ] p)
            (𝓝 (seeleyTerm a b g m p)) := hsm
        have hval : seeleyTerm a b g m p = a m • g p := by
          have h1 : -(b m) * p.2 = 0 := by rw [hzero, mul_zero]
          have h0 : seeleyCut (0:ℝ) = 1 := seeleyCut_eq_one (by norm_num)
          have h2 : ((p.1, (0:ℝ)) : E × ℝ) = p := Prod.ext rfl hzero.symm
          simp only [seeleyTerm, h1, h0, h2, one_smul]
        rwa [hval] at hsm'
      have hdom : ∀ᶠ q in 𝓝[seLw W δ] p, ∀ m, ‖seeleyTerm a b g m q‖ ≤ |a m| * C := by
        rw [eventually_nhdsWithin_iff]
        have hnb : ∀ᶠ q : E × ℝ in 𝓝 p, ‖q.1 - p.1‖ < r := by
          have hin : {q : E × ℝ | q.1 ∈ Metric.ball p.1 r} ∈ 𝓝 p :=
            (Metric.isOpen_ball.preimage continuous_fst).mem_nhds (Metric.mem_ball_self hrpos)
          filter_upwards [hin] with q hq
          simpa [dist_eq_norm] using Metric.mem_ball.mp hq
        filter_upwards [hnb] with q hq
        intro hqmem m
        rw [mem_seLw] at hqmem
        obtain ⟨hqW, _, hqneg⟩ := hqmem
        by_cases hs2 : -(b m) * q.2 ≤ 2
        · have hsmem : -(b m) * q.2 ∈ Set.Icc (0:ℝ) 2 :=
            ⟨le_of_lt (by
              show 0 < -(b m) * q.2
              rw [show -(b m) * q.2 = b m * (-q.2) from by ring]
              exact mul_pos (by linarith [hb m]) (by linarith)), hs2⟩
          have hgq : ‖g (q.1, -(b m) * q.2)‖ ≤ C :=
            htube q.1 hqW hq (-(b m) * q.2) hsmem
          have hcutle : |seeleyCut (-(b m) * q.2)| ≤ 1 := by
            rw [abs_of_nonneg (seeleyCut_nonneg _)]; exact seeleyCut_le_one _
          simp only [seeleyTerm, norm_smul, Real.norm_eq_abs]
          calc |a m| * (|seeleyCut (-(b m) * q.2)| * ‖g (q.1, -(b m) * q.2)‖)
              ≤ |a m| * (1 * C) := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                exact mul_le_mul hcutle hgq (norm_nonneg _) (by norm_num)
            _ = |a m| * C := by ring
        · push_neg at hs2
          have hpos : 0 < -(b m) * q.2 := by
            rw [show -(b m) * q.2 = b m * (-q.2) from by ring]
            exact mul_pos (by linarith [hb m]) (by linarith)
          have harg : 2 ≤ |-(b m) * q.2| := by rw [abs_of_pos hpos]; linarith
          simp only [seeleyTerm, seeleyCut_eq_zero harg, zero_smul, smul_zero, norm_zero]
          exact mul_nonneg (abs_nonneg _) hCnonneg
      have htann := tendsto_tsum_of_dominated_convergence
        (f := fun q (m : ℕ) => seeleyTerm a b g m q) (g := fun m => a m • g p)
        (bound := fun m => |a m| * C) (𝓕 := 𝓝[seLw W δ] p) hboundsum hlim hdom
      have hval : (∑' m : ℕ, a m • g p) = g p := by
        simp only [Complex.real_smul]
        rw [tsum_mul_right, ← Complex.ofReal_tsum, ha]
        simp
      rw [hval] at htann
      change Tendsto (fun q : E × ℝ => ∑' m, seeleyTerm a b g m q) (𝓝[seLw W δ] p) (𝓝 (g p))
      exact htann
    have hLw : Tendsto (seeleyExt a b g) (𝓝[seLw W δ] p) (𝓝 (g p)) := by
      have hev : seeleyExt a b g =ᶠ[𝓝[seLw W δ] p] seeleySum a b g :=
        Filter.eventuallyEq_of_mem self_mem_nhdsWithin
          (fun q hq => seeleyExt_of_neg a b g (by rw [mem_seLw] at hq; exact hq.2.2))
      exact Filter.Tendsto.congr' hev.symm hS
    have hgoal : ContinuousWithinAt (seeleyExt a b g) (seSl W δ) p := by
      have ht : Tendsto (seeleyExt a b g) (𝓝[seSl W δ] p) (𝓝 (seeleyExt a b g p)) := by
        rw [show seeleyExt a b g p = g p from seeleyExt_of_nonneg a b g (le_of_eq hzero.symm)]
        rw [hsplit, nhdsWithin_union]
        exact Filter.Tendsto.sup hUp hLw
      exact ht
    exact hgoal
  · -- the open upper half space
    have hseSl_nbhd : seSl W δ ∈ 𝓝 p :=
      (isOpen_seSl hW δ).mem_nhds (by rw [mem_seSl]; exact ⟨hpW, by linarith⟩)
    have hnbhd : seUp W ∈ 𝓝 p :=
      (isOpen_seUp hW).mem_nhds (by rw [mem_seUp]; exact ⟨hpW, hpos⟩)
    have hcontg : ContinuousAt g p := (hg.mono seUp_subset_seHp).continuousAt hnbhd
    have hev : seeleyExt a b g =ᶠ[𝓝[seSl W δ] p] g := by
      rw [nhdsWithin_eq_nhds.mpr hseSl_nbhd]
      exact Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)
        (fun q hq => seeleyExt_of_nonneg a b g (le_of_lt hq))
    exact hcontg.continuousWithinAt.congr_of_eventuallyEq hev
      (seeleyExt_of_nonneg a b g (le_of_lt hpos))

end Work.NN.Final

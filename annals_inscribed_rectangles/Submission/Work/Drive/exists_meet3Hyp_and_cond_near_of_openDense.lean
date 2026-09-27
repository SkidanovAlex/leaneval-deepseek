import Mathlib
import Submission.Work.Drive.hdenseNodeOpens

/-!
# The *based* localized genericity: an arbitrary base point `m` of the unit ball

`Work.Drive.exists_meet3Hyp_rot_local_of_openDenseN` (`Drive/hdenseNodeOpens.lean`) produces a
parameter `t` of *small norm* — i.e. near the centre `0` — at which the design's rotated triple
satisfies `Meet3Hyp` and a finite family of extra open conditions holds.  This file proves the
*centred* form actually consumed by the design: for an arbitrary **base point** `m` of the open unit
ball (which is the point the remaining open conditions `A k` are known to contain, `hmA`) there is a
parameter `t` in **every** ball around `m` that meets all the conditions at once.

The two differences from the `N`-version are exactly the two places where the centre `0` entered:

* the point `s` at which the localized parametric Sard is run (the richness of the family
  `sweepChartFam` is available at *every* centre, `Work.Drive.richness_sweepChartFam`) is now taken
  **near `m`** — the induction `exists_mem_all_near_of_isOpen_dense_fintype` below, which stays inside
  the ball of radius `(1 - ‖m‖)/2` so that the density hypothesis (available on the closed unit ball)
  applies at every intermediate point;
* the extra conditions `A k` (open, all containing `m`) are met by shrinking the working radius to
  `min ε' δA`, where `δA` is a ball around `m` inside `⋂ k, A k`.

Everything in between (the translated family, its smoothness/seam/slice data, the richness transfer
and `Work.Drive.localSard`) is the same argument, verbatim.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_m3hops : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **A finite family of open conditions, dense at every point of the closed unit ball, has a common
point in every ball around any point `x` of the open unit ball.**

This is `Work.Drive.exists_mem_all_of_isOpen_dense_fintypeN` with the centre `0` replaced by `x`.  The
induction keeps every intermediate point inside the ball `B (x, (1 - ‖x‖)/2)`, which is contained in
the closed unit ball (where the density hypothesis is available); the radius of the final ball is
clamped to `(1 - ‖x‖)/2` accordingly. -/
theorem exists_mem_all_near_of_isOpen_dense_fintype
    {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hopen : ∀ i, IsOpen (P i))
    (hdense : ∀ i, ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∃ y, y ∈ P i ∧ ‖y - x‖ < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ y, ‖y - x‖ < ε ∧ ∀ i, y ∈ P i := by
  classical
  set r : ℝ := (1 - ‖x‖) / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hxr : ‖x‖ + r < 1 := by rw [hrdef]; linarith
  set ε₁ : ℝ := min ε r with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min hε hrpos
  have hε₁ε : ε₁ ≤ ε := by rw [hε₁def]; exact min_le_left _ _
  have hε₁r : ε₁ ≤ r := by rw [hε₁def]; exact min_le_right _ _
  have key : ∀ S : Finset ι, ∃ y, ‖y - x‖ < ε₁ ∧ ∀ i ∈ S, y ∈ P i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨x, by simpa using hε₁pos, by simp⟩
    | insert i S hi ih =>
        obtain ⟨y, hyx, hyS⟩ := ih
        have hy1 : ‖y‖ ≤ 1 := by
          have h : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
            have h2 := norm_add_le (y - x) x
            rwa [sub_add_cancel] at h2
          linarith
        have hOpenS : IsOpen (⋂ j ∈ S, P j) := isOpen_biInter_finset (fun j _ => hopen j)
        have hyMem : y ∈ ⋂ j ∈ S, P j := Set.mem_iInter₂.mpr hyS
        obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.isOpen_iff.mp hOpenS y hyMem
        obtain ⟨y', hy'P, hy'y⟩ := hdense i y hy1 (min δ₂ (ε₁ - ‖y - x‖))
          (lt_min hδ₂pos (by linarith))
        refine ⟨y', ?_, ?_⟩
        · have h1 : ‖y' - y‖ < ε₁ - ‖y - x‖ := lt_of_lt_of_le hy'y (min_le_right _ _)
          have h2 : ‖y' - x‖ ≤ ‖y' - y‖ + ‖y - x‖ := by
            have h3 := norm_add_le (y' - y) (y - x)
            rwa [sub_add_sub_cancel] at h3
          linarith
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · exact hy'P
          · have hmem : y' ∈ ⋂ j ∈ S, P j := hδ₂sub (by
              rw [Metric.mem_ball, dist_eq_norm]
              exact lt_of_lt_of_le hy'y (min_le_left _ _))
            exact Set.mem_iInter₂.mp hmem j hjS
  obtain ⟨y, hy, hyall⟩ := key Finset.univ
  exact ⟨y, lt_of_lt_of_le hy hε₁ε, fun i => hyall i (Finset.mem_univ i)⟩

/-- **The *localized* joint genericity of the design's rotated triple at an arbitrary base point `m`
of the open unit ball, for an arbitrary finite family of open-dense conditions.**

This is `Work.Drive.exists_meet3Hyp_rot_local_of_openDenseN` with the centre `0` replaced by `m` and
with a finite family `A k` of *open* conditions (all containing `m`) imposed at the same parameter.
The point `m` is where the localized Sard is anchored: the parameter produced lies in any prescribed
ball around `m`.

The chart is taken per base point (the localized form of `Work.Drive.refTripleLocal`), and the
family's richness (`Work.Drive.richness_sweepChartFam`, proved) replaces a global residency of the
triple locus in one chart — `hloc` is *not* provable for the capping space
(`Submission/Work/Drive/CHART_SOURCE_OPACITY.md`). -/
theorem exists_meet3Hyp_and_cond_near_of_openDense
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u : Fin 3 → UnitAddCircle)
    {ι : Type} [Finite ι]
    (Pcond : ι → Set (EuclideanSpace ℝ (Fin 12)))
    (hPopen : ∀ i : ι, IsOpen (Pcond i))
    (hPdense : ∀ i : ι, ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ Pcond i ∧ ‖y - x‖ < δ)
    {κ : Type} [Finite κ] (A : κ → Set (EuclideanSpace ℝ (Fin 12)))
    (hAopen : ∀ k : κ, IsOpen (A k))
    (m : EuclideanSpace ℝ (Fin 12)) (hmA : ∀ k : κ, m ∈ A k) (hm1 : ‖m‖ < 1)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - m‖ < ε' ∧
      @Work.Drive.Meet3Hyp Work.Drive.CappingSpace _ Work.Drive.cappingCharted
        Work.Drive.isManifold_cappingCharted
        (Work.Drive.sweepChartFam (fun j => Work.Drive.rotPresentation Q (u j)) Ξ c t) ∧
      (∀ i : ι, t ∈ Pcond i) ∧ (∀ k : κ, t ∈ A k) := by
  classical
  -- ## 0. the conditions `A k` hold in a ball around `m`
  have hAinter : IsOpen (⋂ k : κ, A k) := isOpen_iInter_of_finite (fun k => hAopen k)
  obtain ⟨δA, hδApos, hδAsub⟩ := Metric.isOpen_iff.mp hAinter m (Set.mem_iInter.mpr hmA)
  set ρ : ℝ := min ε' δA with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hε' hδApos
  have hρ_ε' : ρ ≤ ε' := by rw [hρdef]; exact min_le_left _ _
  have hρ_δA : ρ ≤ δA := by rw [hρdef]; exact min_le_right _ _
  -- ## 1. a point `s` near `m` satisfying all the conditions
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨s, hsm, hsP⟩ :=
    exists_mem_all_near_of_isOpen_dense_fintype Pcond hPopen hPdense hm1 (ρ / 4)
      (by linarith)
  -- ## 2. a ball around `s` on which all the conditions hold
  have hOpenInter : IsOpen (⋂ i : ι, Pcond i) := isOpen_iInter_of_finite (fun i => hPopen i)
  obtain ⟨δP, hδPpos, hδPsub⟩ := Metric.isOpen_iff.mp hOpenInter s (Set.mem_iInter.mpr hsP)

  let P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace := fun j => rotPresentation Q (u j)
  have hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k) :=
    fun k => contMDiff_rotPresentation Q (u k) (contMDiff_diskPlane (Q := Q) hQ.1)
  have hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y) :=
    fun k y hy => rotPresentation_seamInv Q hQ.2 (u k) y hy
  let G : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t k x => sweepChartFam P Ξ c t k x
  have hGfun : ∀ t : EuclideanSpace ℝ (Fin 12),
      G t = sweepChartFam (fun j => rotPresentation Q (u j)) Ξ c t := by
    intro t; rfl
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hGsm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2) :=
    fun k => contMDiff_sweepChartFam P Ξ c hslice k
  -- ## 3. the translated family
  let Gs : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun τ k x => G (s + τ) k x
  set ετ : ℝ := min δP ((ρ - ‖s - m‖) / 2) with hετdef
  have hετpos : 0 < ετ := by
    rw [hετdef]
    exact lt_min hδPpos (by linarith)
  have hετ_δP : ετ ≤ δP := by rw [hετdef]; exact min_le_left _ _
  have hετ_ρ : ετ ≤ (ρ - ‖s - m‖) / 2 := by rw [hετdef]; exact min_le_right _ _
  have hGs_sm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => Gs q.1 k q.2) := by
    intro k
    have htrans : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => (s + q.1, q.2)) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have hcomp := (hGsm k).comp htrans
    simpa only [Function.comp_def, Gs] using hcomp
  have hGs_slice : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Gs τ k) := by
    intro τ k
    have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((s + τ, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hGsm k).comp (contMDiff_iff_contDiff.mpr hφ')
    simpa only [Function.comp_def, Gs, G, sweepChartFam_apply] using hcomp
  have hGs_seam : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → Gs τ k x = Gs τ k (seamInv x) := by
    intro τ k x hx
    have hinst : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
        (fun z => Ξ (blk k (s + τ)) (P k z)) y
          = (fun z => Ξ (blk k (s + τ)) (P k z)) (seamInv2 y) :=
      fun y hy => congrArg (Ξ (blk k (s + τ))) (hPseam k y hy)
    have h := clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k (s + τ)) (P k z)) hinst x hx
    simpa only [Gs, G, sweepChartFam_apply, Function.comp_def] using h
  -- ## 4. the richness of the translated family, from the richness at the centre `s`
  have hrich := richness_sweepChartFam P Ξ c hΞ hc hcdist hP
  have hGs_surj : ∀ (p : CappingSpace) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ),
      IsCompact K → 0 < δ →
      (∀ (τ : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        ∀ k : Fin 3, Gs τ k (TParity.bPartC k y) ∈ (chr p).source) →
      ∀ (τ : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
        TParity.chartDiff3 p (Gs τ) y = 0 →
        Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (Gs τ') y) τ) := by
    intro p K δ hK hδ hcont τ y hτ hy hz
    have hcontain : ∀ (t : EuclideanSpace ℝ (Fin 12)) (y' : EuclideanSpace ℝ (Fin 9)),
        ‖t - s‖ < δ → y' ∈ K → ∀ k : Fin 3,
          sweepChartFam P Ξ c t k (TParity.bPartC k y') ∈ (chr p).source := by
      intro t y' ht hy' k
      have hswap : Gs (t - s) = G t := by
        funext k x
        simp only [Gs, G]
        rw [show s + (t - s) = t by abel]
      have h := hcont (t - s) y' ht hy' k
      rw [hswap] at h
      exact h
    have hsrc : ∀ k : Fin 3, G (s + τ) k (TParity.bPartC k y) ∈ (chr p).source := by
      intro k
      have h := hcont τ y hτ hy k
      simpa only [Gs] using h
    have hz' : TParity.chartDiff3 p (G (s + τ)) y = 0 := by
      simpa only [Gs] using hz
    have hsurj := hrich p K s δ hK hδ hcontain (s + τ) y
      (by rw [add_sub_cancel_left]; exact hτ) hy hz'
    have hsm := contDiffAt_chartDiff3_family_fin 12 G hGsm p (s + τ) hsrc
    have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          ((t', y) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9))) (s + τ) :=
      contDiffAt_id.prodMk contDiffAt_const
    have hsm'' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G q.1) q.2) ∘
          (fun t' : EuclideanSpace ℝ (Fin 12) => (t', y))) (s + τ) :=
      hsm.comp (s + τ) hinner
    have hsm' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G t') y) (s + τ) := hsm''
    have hF : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin 12) =>
        TParity.chartDiff3 p (G t') y)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G t') y) (s + τ)) (s + τ) :=
      (hsm'.differentiableAt top_ne_zero_m3hops).hasFDerivAt
    have hshift : HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin 12) => s + τ')
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 12))) τ := by
      simpa using (hasFDerivAt_id τ).const_add s
    have hcomp := hF.comp τ hshift
    rw [ContinuousLinearMap.comp_id] at hcomp
    have heq : fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (Gs τ') y) τ
        = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          TParity.chartDiff3 p (G t') y) (s + τ) := by
      have h1 : (fun τ' : EuclideanSpace ℝ (Fin 12) =>
            TParity.chartDiff3 p (Gs τ') y)
          = (fun τ' : EuclideanSpace ℝ (Fin 12) =>
            TParity.chartDiff3 p (G (s + τ')) y) := rfl
      rw [h1]
      exact hcomp.fderiv
    rw [heq]
    exact hsurj
  -- ## 5. the localized Sard at the translated base
  obtain ⟨τ, hτ, hM⟩ := localSard (M := CappingSpace) (m := 12) Gs hGs_sm hGs_slice
    hGs_seam hGs_surj ετ hετpos
  -- ## 6. the conclusion
  have hdist_lt : ‖s + τ - m‖ < ρ := by
    have h1 : ‖s + τ - m‖ ≤ ‖s - m‖ + ‖τ‖ := by
      have heq : s + τ - m = (s - m) + τ := by abel
      rw [heq]
      exact norm_add_le _ _
    have h2 : ‖τ‖ < (ρ - ‖s - m‖) / 2 := lt_of_lt_of_le hτ hετ_ρ
    linarith
  refine ⟨s + τ, ?_, ?_, ?_, ?_⟩
  · linarith
  · have hM' : Meet3Hyp CappingSpace (G (s + τ)) := by simpa only [Gs] using hM
    rwa [hGfun (s + τ)] at hM'
  · intro i
    have hmem : s + τ ∈ ⋂ i : ι, Pcond i := hδPsub (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP)
    exact Set.mem_iInter.mp hmem i
  · intro k
    have hmem : s + τ ∈ ⋂ k : κ, A k := hδAsub (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hdist_lt hρ_δA)
    exact Set.mem_iInter.mp hmem k

end

end Work.Drive

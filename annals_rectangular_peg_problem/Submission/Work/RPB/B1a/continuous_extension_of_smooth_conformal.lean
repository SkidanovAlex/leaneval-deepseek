import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB1a.Caratheodory.exists_small_crosscut
import Submission.Work.RPB1a.Caratheodory.exists_diam_le_of_cap
import Submission.Work.RPB1a.Caratheodory.exists_continuousOn_closedBall_of_diam_lens
import Submission.Work.RPB1a.Caratheodory.mem_closure_of_continuousOn_closedBall
import Submission.Work.RPB1a.Caratheodory.notMem_of_continuousOn_closedBall
import Submission.Work.RPB1a.jordan_domain_of_loop
import Submission.Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn
import Submission.Work.RPB.B1a.isPreconnected_ball_sdiff_closedBall
import Submission.Work.RPB.B1a.exists_diam_le_of_connected_cover_frontier
import Submission.Work.RPB.B1a.exists_forall_ball_preconnected_inter_of_smooth_loop

/-!
# `Work.RPB.B1a.continuous_extension_of_smooth_conformal`

Carathéodory's boundary correspondence in the shape the B1a route consumes: a conformal map
`f` of the unit disc onto a bounded Jordan domain `D` whose boundary is a smooth loop `v`
extends continuously to the closed disc, and carries the unit circle into `range v`.

## Strategy

The analytic input is the length–area estimate
`Work.RPB1a.Caratheodory.exists_small_crosscut`: for every boundary point `ζ` of the disc there are
circular crosscuts `sphere ζ r ∩ ball 0 1` of arbitrarily small image diameter.  The topological
input is that this forces the *caps* `ball ζ r ∩ ball 0 1` to have arbitrarily small image, which is
proved here directly by a "cut-off" argument:

* the chord `sphere ζ r ∩ ball 0 1` splits the disc into the cap `L` and the far side
  `M = ball 0 1 \ closedBall ζ r`, both connected;
* hence `f '' L` and `f '' M` are the two pieces of `D \ f '' (chord)`, and their closures
  `T₁ = closure (f '' L)`, `T₂ = closure (f '' M)` are compact connected with `T₁ ∪ T₂ = closure D`;
* the two closures meet only in the closed image crosscut (any other common boundary point would
  have to be a common cluster point of the images of the cap and of the far side, which is
  impossible by the local connectivity of `D` at boundary points,
  `exists_forall_ball_preconnected_inter_of_smooth_loop`);
* so `diam (T₁ ∩ T₂) → 0`, while `T₂` stays wide because it contains the fixed image of `0` and
  of `ζ / 2`, which lie in every far side;
* a disc cannot be split into two compact connected pieces with small intersection and one wide
  piece (`exists_diam_le_of_connected_cover_frontier`), so `diam T₁ → 0`, and then
  `diam (f '' cap) ≤ diam T₁ → 0`.

The continuous extension then comes from
`Work.RPB1a.Caratheodory.exists_continuousOn_closedBall_of_diam_lens`, and the two remaining
inclusions of the circle into `range v = frontier D` from
`Work.RPB1a.Caratheodory.mem_closure_of_continuousOn_closedBall` and
`Work.RPB1a.Caratheodory.notMem_of_continuousOn_closedBall`.
-/

namespace Work.RPB.B1a

open Complex Set Metric Filter
open scoped Topology

set_option autoImplicit false

noncomputable section

/-! ## Elementary consequences of the open mapping theorem -/

private lemma isOpenMap_ball {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hfinj : Set.InjOn f (Metric.ball 0 1)) :
    ∀ V : Set ℂ, V ⊆ Metric.ball 0 1 → IsOpen V → IsOpen (f '' V) :=
  fun _V hV hVo =>
    Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn hVo (hf.mono hV) (hfinj.mono hV)

/-- The inverse of an injective holomorphic map of the disc is continuous on the image. -/
private lemma continuousOn_invFunOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hfinj : Set.InjOn f (Metric.ball 0 1)) :
    ContinuousOn (Function.invFunOn f (Metric.ball 0 1)) (f '' Metric.ball 0 1) := by
  have hopen : ∀ V : Set ℂ, V ⊆ Metric.ball 0 1 → IsOpen V → IsOpen (f '' V) :=
    isOpenMap_ball hf hfinj
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  obtain ⟨u, hu, rfl⟩ := hx
  have hWo : IsOpen (Metric.ball u ε ∩ Metric.ball 0 1) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have himg : IsOpen (f '' (Metric.ball u ε ∩ Metric.ball 0 1)) :=
    hopen _ inter_subset_right hWo
  have hmem : f u ∈ f '' (Metric.ball u ε ∩ Metric.ball 0 1) :=
    ⟨u, ⟨Metric.mem_ball_self hε, hu⟩, rfl⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp himg _ hmem
  refine ⟨δ, hδ, ?_⟩
  intro y hy hdy
  obtain ⟨w, hw, rfl⟩ := hδsub hdy
  have hgw : Function.invFunOn f (Metric.ball 0 1) (f w) = w :=
    hfinj (Function.invFunOn_mem ⟨w, hw.2, rfl⟩) hw.2 (Function.invFunOn_eq ⟨w, hw.2, rfl⟩)
  have hgu : Function.invFunOn f (Metric.ball 0 1) (f u) = u :=
    hfinj (Function.invFunOn_mem ⟨u, hu, rfl⟩) hu (Function.invFunOn_eq ⟨u, hu, rfl⟩)
  rw [hgw, hgu]
  exact Metric.mem_ball.mp hw.1

/-- The closure of the image of `L ⊆ ball` meets the image disc exactly in the image of
`closure L ∩ ball`. -/
private lemma closure_image_inter_eq {f : ℂ → ℂ} (hfinj : Set.InjOn f (Metric.ball 0 1))
    (hcont : ContinuousOn f (Metric.ball 0 1))
    (hopen : ∀ V : Set ℂ, V ⊆ Metric.ball 0 1 → IsOpen V → IsOpen (f '' V))
    {L : Set ℂ} (hL : L ⊆ Metric.ball 0 1) :
    closure (f '' L) ∩ (f '' Metric.ball 0 1) = f '' (closure L ∩ Metric.ball 0 1) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro p ⟨hp, u, hu, rfl⟩
    have hucl : u ∈ closure L := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      rw [Metric.mem_closure_iff] at hp
      have hWo : IsOpen (Metric.ball u ε ∩ Metric.ball 0 1) :=
        Metric.isOpen_ball.inter Metric.isOpen_ball
      have himg : IsOpen (f '' (Metric.ball u ε ∩ Metric.ball 0 1)) :=
        hopen _ inter_subset_right hWo
      have hmem : f u ∈ f '' (Metric.ball u ε ∩ Metric.ball 0 1) :=
        ⟨u, ⟨Metric.mem_ball_self hε, hu⟩, rfl⟩
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp himg _ hmem
      obtain ⟨q, hq, hdist⟩ := hp δ hδ
      obtain ⟨v, hvL, rfl⟩ := hq
      have : f v ∈ f '' (Metric.ball u ε ∩ Metric.ball 0 1) :=
        hδsub (Metric.mem_ball.mpr (by simpa [dist_comm] using hdist))
      obtain ⟨w, hw, hwv⟩ := this
      have hwv' : w = v := hfinj hw.2 (hL hvL) hwv
      exact ⟨v, hvL, by rw [← hwv', dist_comm]; exact Metric.mem_ball.mp hw.1⟩
    exact ⟨u, ⟨hucl, hu⟩, rfl⟩
  · rintro p ⟨u, ⟨hucl, hu⟩, rfl⟩
    refine ⟨?_, ⟨u, hu, rfl⟩⟩
    rw [Metric.mem_closure_iff] at hucl ⊢
    intro ε hε
    have hcatu : ContinuousAt f u :=
      hcont.continuousAt (Metric.isOpen_ball.mem_nhds hu)
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcatu ε hε
    obtain ⟨v, hvL, hvu⟩ := hucl δ hδ
    exact ⟨f v, ⟨v, hvL, rfl⟩, by simpa [dist_comm] using hδc (by simpa [dist_comm] using hvu)⟩

/-! ## The cap estimate: shrinking crosscuts shrink the caps -/

private theorem lens_tendsto_zero {v : ℝ → ℂ} (hv : IsSmoothLoop v) {D : Set ℂ}
    (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDfr : closure D \ interior D = Set.range v)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hfinj : Set.InjOn f (Metric.ball 0 1)) (hfim : f '' Metric.ball 0 1 = D)
    {ζ : ℂ} (hζ : ζ ∈ Metric.sphere 0 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n < 1) (hr0 : Filter.Tendsto r Filter.atTop (𝓝 0))
    (hcross : Filter.Tendsto
      (fun n => Metric.diam (closure (f '' (Metric.sphere ζ (r n) ∩ Metric.ball 0 1))))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => Metric.diam (f '' (Metric.ball ζ (r n) ∩ Metric.ball 0 1)))
      Filter.atTop (𝓝 0) := by
  have hζnorm : ‖ζ‖ = 1 := by
    have h := Metric.mem_sphere.mp hζ
    rwa [dist_eq_norm, sub_zero] at h
  have hfcont : ContinuousOn f (Metric.ball (0 : ℂ) 1) := hf.continuousOn
  have hopen : ∀ V : Set ℂ, V ⊆ Metric.ball (0 : ℂ) 1 → IsOpen V → IsOpen (f '' V) :=
    isOpenMap_ball hf hfinj
  have hinv : ContinuousOn (Function.invFunOn f (Metric.ball 0 1)) (f '' Metric.ball 0 1) :=
    continuousOn_invFunOn hf hfinj
  have hcl : ∀ L : Set ℂ, L ⊆ Metric.ball (0 : ℂ) 1 →
      closure (f '' L) ∩ (f '' Metric.ball (0 : ℂ) 1) =
        f '' (closure L ∩ Metric.ball (0 : ℂ) 1) :=
    fun L hL => closure_image_inter_eq hfinj hfcont hopen hL
  have hfr : frontier D = Set.range v := by
    rw [← closure_sdiff_interior D]; exact hDfr
  have hclD : closure D = D ∪ frontier D := by
    rw [IsOpen.frontier_eq hDo]
    exact (union_sdiff_cancel subset_closure).symm
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hhalf_mem : ζ / 2 ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_div, hζnorm]; norm_num
  have hhalf_ne : (0 : ℂ) ≠ ζ / 2 := by
    intro h
    have h2 : ‖(0 : ℂ)‖ = ‖ζ / 2‖ := by rw [h]
    rw [norm_zero, norm_div, hζnorm] at h2
    norm_num at h2
  have hd0 : 0 < dist (f 0) (f (ζ / 2)) := by
    rw [dist_pos]; exact fun h => hhalf_ne (hfinj hzero_mem hhalf_mem h)
  have hmain : ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      Metric.diam (f '' (Metric.ball ζ (r n) ∩ Metric.ball (0 : ℂ) 1)) ≤ η := by
    intro η hη
    obtain ⟨ε, hε, hεT⟩ := exists_diam_le_of_connected_cover_frontier v hv D hDo hDc hDb hDfr
      (η := min η (dist (f 0) (f (ζ / 2)) / 2)) (lt_min hη (half_pos hd0))
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hr0 (1 / 2) (by norm_num)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hcross ε hε
    refine Filter.eventually_atTop.mpr ⟨max N₁ N₂, fun n hn => ?_⟩
    have hrn : r n < 1 / 2 := by
      have h := hN₁ n (le_trans (le_max_left _ _) hn)
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact h.2
    have hdiam_n : Metric.diam (closure (f '' (Metric.sphere ζ (r n) ∩ Metric.ball 0 1))) ≤ ε := by
      have h := hN₂ n (le_trans (le_max_right _ _) hn)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg] at h
      exact h.le
    have hrpos : 0 < r n := (hr n).1
    have hr1 : r n < 1 := (hr n).2
    set L : Set ℂ := Metric.ball ζ (r n) ∩ Metric.ball (0 : ℂ) 1 with hL
    set M : Set ℂ := Metric.ball (0 : ℂ) 1 \ Metric.closedBall ζ (r n) with hM
    set C : Set ℂ := Metric.sphere ζ (r n) ∩ Metric.ball (0 : ℂ) 1 with hC
    have hLsub : L ⊆ Metric.ball (0 : ℂ) 1 := by rw [hL]; exact inter_subset_right
    have hMsub : M ⊆ Metric.ball (0 : ℂ) 1 := by rw [hM]; exact diff_subset
    have hCsub : C ⊆ Metric.ball (0 : ℂ) 1 := by rw [hC]; exact inter_subset_right
    have hLopen : IsOpen L := by
      rw [hL]; exact Metric.isOpen_ball.inter Metric.isOpen_ball
    have hMopen : IsOpen M := by
      rw [hM]; exact Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
    have hLpre : IsPreconnected L := by
      rw [hL]
      exact ((convex_ball ζ (r n)).inter (convex_ball (0 : ℂ) 1)).isPreconnected
    have hMpre : IsPreconnected M := by
      rw [hM]
      exact isPreconnected_ball_sdiff_closedBall hζnorm hrpos (lt_trans hrn (by norm_num))
    have hsplit : Metric.ball (0 : ℂ) 1 \ C = L ∪ M := by
      rw [hC, hL, hM]
      ext z
      simp only [mem_diff, mem_union, mem_inter_iff, mem_sphere, mem_ball, mem_closedBall]
      constructor
      · rintro ⟨hz1, hz2⟩
        have hne : dist z ζ ≠ r n := fun h => hz2 ⟨h, hz1⟩
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨h, hz1⟩
        · exact Or.inr ⟨hz1, not_le.mpr h⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h2, fun hc => absurd hc.1 (ne_of_lt h1)⟩
        · exact ⟨h1, fun hc => absurd hc.1 (ne_of_gt (not_le.mp h2))⟩
    have hLMdisj : Disjoint L M := by
      rw [hL, hM, Set.disjoint_left]
      rintro z ⟨hz1, -⟩ ⟨-, hz2⟩
      rw [Metric.mem_ball] at hz1
      rw [Metric.mem_closedBall] at hz2
      exact hz2 (le_of_lt hz1)
    have hCL : C ⊆ closure L := by
      rw [hC, hL]
      rintro z ⟨hz1, hz2⟩
      rw [Metric.mem_closure_iff]
      intro δ hδ
      have hzr : dist z ζ = r n := Metric.mem_sphere.mp hz1
      have hz0 : dist z 0 < 1 := Metric.mem_ball.mp hz2
      set t : ℝ := max (1 / 2) (1 - δ / (2 * r n)) with ht
      have ht0 : (0 : ℝ) < t := by
        have : (0 : ℝ) < 1 / 2 := by norm_num
        rw [ht]
        exact lt_of_lt_of_le this (le_max_left _ _)
      have ht1 : t < 1 := by
        rw [ht]
        refine max_lt (by norm_num) ?_
        have hpos : 0 < δ / (2 * r n) := div_pos hδ (by positivity)
        linarith
      have ht2 : 1 - t ≤ δ / (2 * r n) := by
        have h := le_max_right (1 / 2 : ℝ) (1 - δ / (2 * r n))
        rw [← ht] at h
        linarith
      refine ⟨(1 - t) • ζ + t • z, ?_, ?_⟩
      · rw [mem_inter_iff, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm]
        constructor
        · have h1 : (1 - t) • ζ + t • z - ζ = t • (z - ζ) := by module
          rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm, hzr]
          nlinarith [ht1, hrpos]
        · have h1 : (1 - t) • ζ + t • z - 0 = (1 - t) • ζ + t • z := sub_zero _
          rw [h1]
          calc ‖(1 - t) • ζ + t • z‖
              ≤ ‖(1 - t) • ζ‖ + ‖t • z‖ := norm_add_le _ _
            _ = (1 - t) * 1 + t * ‖z‖ := by
                simp only [norm_smul, Real.norm_eq_abs, hζnorm,
                  abs_of_pos (by linarith : (0 : ℝ) < 1 - t), abs_of_pos ht0]
            _ < 1 := by
                have hz : ‖z‖ < 1 := by simpa [dist_eq_norm, sub_zero] using hz0
                nlinarith [ht0, ht1, hz]
      · rw [dist_eq_norm, norm_sub_rev]
        have h1 : (1 - t) • ζ + t • z - z = (1 - t) • (ζ - z) := by module
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 - t),
          norm_sub_rev, ← dist_eq_norm, hzr]
        have h3 : (1 - t) * r n ≤ δ / 2 := by
          have h2rn : (0 : ℝ) < 2 * r n := by linarith
          have h4 := (le_div_iff₀ h2rn).mp ht2
          nlinarith
        linarith [h3, hδ]
    have hLcl : closure L ⊆ Metric.closedBall ζ (r n) := by
      rw [hL]
      refine closure_minimal ?_ Metric.isClosed_closedBall
      intro z hz
      rw [mem_inter_iff] at hz
      exact le_of_lt (Metric.mem_ball.mp hz.1)
    have hMcl : closure M ⊆ {z : ℂ | r n ≤ dist z ζ} := by
      rw [hM]
      refine closure_minimal ?_ (isClosed_le continuous_const (continuous_id.dist continuous_const))
      intro z hz
      rw [Set.mem_sdiff, mem_closedBall] at hz
      exact le_of_lt (not_le.mp hz.2)
    have hDsplit : D \ f '' C = f '' L ∪ f '' M := by
      have hbC : Metric.ball (0 : ℂ) 1 ∩ C = C := Set.inter_eq_right.mpr hCsub
      calc D \ f '' C
          = f '' Metric.ball (0 : ℂ) 1 \ f '' (Metric.ball (0 : ℂ) 1 ∩ C) := by rw [hfim, hbC]
        _ = f '' (Metric.ball (0 : ℂ) 1 \ C) := (Set.InjOn.image_sdiff (t := C) hfinj).symm
        _ = f '' (L ∪ M) := by rw [hsplit]
        _ = f '' L ∪ f '' M := by rw [Set.image_union]
    have hdisjLM : Disjoint (f '' L) (f '' M) := by
      rw [Set.disjoint_left]
      rintro z ⟨w, hw, rfl⟩ ⟨w', hw', hw''⟩
      have hww : w = w' := hfinj (hLsub hw) (hMsub hw') hw''.symm
      subst hww
      exact (Set.disjoint_left.mp hLMdisj hw) hw'
    have hunion : closure (f '' L) ∪ closure (f '' M) = closure D := by
      refine Set.Subset.antisymm (union_subset ?_ ?_) ?_
      · exact closure_mono (by rw [← hfim]; exact Set.image_mono hLsub)
      · exact closure_mono (by rw [← hfim]; exact Set.image_mono hMsub)
      · rw [← hfim]
        have hball : Metric.ball (0 : ℂ) 1 = C ∪ (L ∪ M) := by
          rw [← hsplit]
          exact (union_sdiff_cancel hCsub).symm
        rw [hball]
        have hsubC : f '' C ⊆ closure (f '' L) := by
          refine (Set.image_mono ?_).trans (by rw [← hcl L hLsub]; exact inter_subset_left)
          exact fun z hz => ⟨hCL hz, hCsub hz⟩
        refine closure_minimal ?_ (isClosed_closure.union isClosed_closure)
        rw [Set.image_union, Set.image_union]
        exact union_subset (hsubC.trans subset_union_left)
          (union_subset (subset_closure.trans subset_union_left)
            (subset_closure.trans subset_union_right))
    have hinter : closure (f '' L) ∩ closure (f '' M) ⊆ closure (f '' C) := by
      rintro p ⟨hpL, hpM⟩
      by_cases hpfr : p ∈ frontier D
      · have hpv : p ∈ Set.range v := by rw [← hfr]; exact hpfr
        obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
          exists_forall_ball_preconnected_inter_of_smooth_loop v hv hDo hDc hDfr hpv
        by_contra hcon
        rw [Metric.mem_closure_iff] at hcon
        push_neg at hcon
        obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hcon
        have hρpos : 0 < min ρ₀ (ρ₁ / 2) := lt_min hρ₀pos (half_pos hρ₁pos)
        have hρsub : closure (f '' C) ⊆ {y : ℂ | min ρ₀ (ρ₁ / 2) ≤ dist p y} := by
          refine closure_minimal ?_
            (isClosed_le continuous_const (continuous_const.dist continuous_id))
          intro y hy
          show min ρ₀ (ρ₁ / 2) ≤ dist p y
          exact le_trans (min_le_right _ _) (le_trans (by linarith : ρ₁ / 2 ≤ ρ₁) (hρ₁ y hy))
        have hpre : IsPreconnected (D ∩ Metric.ball p (min ρ₀ (ρ₁ / 2))) :=
          hρ₀ _ hρpos (min_le_left _ _)
        have hfLopen : IsOpen (f '' L) := hopen L hLsub hLopen
        have hfMopen : IsOpen (f '' M) := hopen M hMsub hMopen
        have hsub : D ∩ Metric.ball p (min ρ₀ (ρ₁ / 2)) ⊆ f '' L ∪ f '' M := by
          rintro z ⟨hzD, hzball⟩
          have hzC : z ∉ f '' C := by
            intro hzc
            have h1 : min ρ₀ (ρ₁ / 2) ≤ dist p z := hρsub (subset_closure hzc)
            rw [Metric.mem_ball, dist_comm] at hzball
            linarith
          have hz' : z ∈ D \ f '' C := ⟨hzD, hzC⟩
          rwa [hDsplit] at hz'
        rcases hpre.subset_or_subset hfLopen hfMopen hdisjLM hsub with hsubL | hsubM
        · have hempty : f '' M ∩ Metric.ball p (min ρ₀ (ρ₁ / 2)) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨hzM, hzball'⟩
            have hzD : z ∈ D := by
              obtain ⟨w, hw, rfl⟩ := hzM
              rw [← hfim]
              exact ⟨w, hMsub hw, rfl⟩
            exact Set.disjoint_left.mp hdisjLM (hsubL ⟨hzD, hzball'⟩) hzM
          obtain ⟨q, hq, hqd⟩ := Metric.mem_closure_iff.mp hpM (min ρ₀ (ρ₁ / 2)) hρpos
          have hmem : q ∈ f '' M ∩ Metric.ball p (min ρ₀ (ρ₁ / 2)) :=
            ⟨hq, Metric.mem_ball.mpr (by rw [dist_comm]; exact hqd)⟩
          rw [hempty] at hmem
          exact hmem
        · have hempty : f '' L ∩ Metric.ball p (min ρ₀ (ρ₁ / 2)) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨hzL, hzball'⟩
            have hzD : z ∈ D := by
              obtain ⟨w, hw, rfl⟩ := hzL
              rw [← hfim]
              exact ⟨w, hLsub hw, rfl⟩
            exact Set.disjoint_right.mp hdisjLM (hsubM ⟨hzD, hzball'⟩) hzL
          obtain ⟨q, hq, hqd⟩ := Metric.mem_closure_iff.mp hpL (min ρ₀ (ρ₁ / 2)) hρpos
          have hmem : q ∈ f '' L ∩ Metric.ball p (min ρ₀ (ρ₁ / 2)) :=
            ⟨hq, Metric.mem_ball.mpr (by rw [dist_comm]; exact hqd)⟩
          rw [hempty] at hmem
          exact hmem
      · have hpD : p ∈ D := by
          have h1 : p ∈ closure D := by
            have h2 : p ∈ closure (f '' L) ∪ closure (f '' M) := subset_union_left hpL
            rwa [hunion] at h2
          rw [hclD] at h1
          rcases h1 with h | h
          · exact h
          · exact absurd h hpfr
        have hp' : p ∈ f '' Metric.ball (0 : ℂ) 1 := by rw [hfim]; exact hpD
        have hpbothL : p ∈ closure (f '' L) ∩ f '' Metric.ball (0 : ℂ) 1 := ⟨hpL, hp'⟩
        rw [hcl L hLsub] at hpbothL
        obtain ⟨w, hwLmem, hwp⟩ := hpbothL
        have hpbothM : p ∈ closure (f '' M) ∩ f '' Metric.ball (0 : ℂ) 1 := ⟨hpM, hp'⟩
        rw [hcl M hMsub] at hpbothM
        obtain ⟨w', hw'Mmem, hw'p⟩ := hpbothM
        have hww : w = w' := hfinj hwLmem.2 hw'Mmem.2 (by rw [hwp, hw'p])
        subst hww
        refine subset_closure ⟨w, ?_, hwp⟩
        rw [hC, mem_inter_iff, mem_sphere]
        exact ⟨le_antisymm (Metric.mem_closedBall.mp (hLcl hwLmem.1)) (hMcl hw'Mmem.1),
          hwLmem.2⟩
    have hz0M : (0 : ℂ) ∈ M := by
      rw [hM, mem_diff]
      refine ⟨Metric.mem_ball_self one_pos, ?_⟩
      rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hζnorm]
      exact not_le.mpr hr1
    have hhalfM : ζ / 2 ∈ M := by
      rw [hM, mem_diff]
      refine ⟨hhalf_mem, ?_⟩
      rw [mem_closedBall, dist_eq_norm]
      have h1 : ‖ζ / 2 - ζ‖ = 1 / 2 := by
        rw [show ζ / 2 - ζ = -(ζ / 2) by ring, norm_neg, norm_div, hζnorm]
        norm_num
      rw [h1]
      exact not_le.mpr hrn
    have hzLmem : (1 - r n / 2) • ζ ∈ L := by
      rw [hL, mem_inter_iff, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm]
      constructor
      · rw [show (1 - r n / 2) • ζ - ζ = (-(r n / 2)) • ζ by module,
          norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hrpos), hζnorm, mul_one]
        exact half_lt_self hrpos
      · rw [show (1 - r n / 2) • ζ - 0 = (1 - r n / 2) • ζ by rw [sub_zero], norm_smul,
          Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 - r n / 2), hζnorm, mul_one]
        linarith
    have hfar : dist (f 0) (f (ζ / 2)) ≤ Metric.diam (closure (f '' M)) := by
      refine Metric.dist_le_diam_of_mem ?_ (subset_closure ⟨0, hz0M, rfl⟩)
        (subset_closure ⟨ζ / 2, hhalfM, rfl⟩)
      exact hDb.closure.subset ((closure_mono (Set.image_mono hMsub)).trans (by rw [hfim]))
    have hconnT₁ : IsConnected (closure (f '' L)) :=
      ⟨⟨f ((1 - r n / 2) • ζ), subset_closure ⟨_, hzLmem, rfl⟩⟩,
        (hLpre.image f (hfcont.mono hLsub)).closure⟩
    have hconnT₂ : IsConnected (closure (f '' M)) :=
      ⟨⟨f 0, subset_closure ⟨0, hz0M, rfl⟩⟩, (hMpre.image f (hfcont.mono hMsub)).closure⟩
    have hsmall : Metric.diam (closure (f '' L) ∩ closure (f '' M)) ≤ ε := by
      refine (Metric.diam_mono hinter
        (hDb.subset (by rw [← hfim]; exact Set.image_mono hCsub)).closure).trans ?_
      rw [hC]
      exact hdiam_n
    rcases hεT (closure (f '' L)) (closure (f '' M)) isClosed_closure hconnT₁ isClosed_closure
      hconnT₂ hunion hsmall with h1 | h2
    · rw [← Metric.diam_closure (f '' L)]
      exact le_trans h1 (min_le_left _ _)
    · exfalso
      have h2' : Metric.diam (closure (f '' M)) ≤ dist (f 0) (f (ζ / 2)) / 2 :=
        le_trans h2 (min_le_right _ _)
      exact absurd (hfar.trans h2') (not_le.mpr (half_lt_self hd0))
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hmain (η / 2) (half_pos hη))
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
    exact lt_of_le_of_lt (hN n hn) (half_lt_self hη)⟩

/-! ## The lens estimate and the extension -/

private theorem lens_estimate (v : ℝ → ℂ) (hv : IsSmoothLoop v) (D : Set ℂ)
    (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDfr : closure D \ interior D = Set.range v)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hfinj : Set.InjOn f (Metric.ball 0 1)) (hfim : f '' Metric.ball 0 1 = D) :
    ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, ∀ ε > 0,
      ∃ r : ℝ, 0 < r ∧ Metric.diam (f '' (Metric.ball ζ r ∩ Metric.ball (0 : ℂ) 1)) ≤ ε := by
  intro ζ hζ ε hε
  have hchoice : ∀ n : ℕ, ∃ s : ℝ, 0 < s ∧ s < 1 / ((n : ℝ) + 1) ∧
      Metric.diam (closure (f '' (Metric.sphere ζ s ∩ Metric.ball (0 : ℂ) 1))) <
        1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨s, hs0, hs1, hs2⟩ :=
      Work.RPB1a.Caratheodory.exists_small_crosscut hDb hf hfinj hfim ζ hζ
        (1 / ((n : ℝ) + 1)) (by positivity) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨s, hs0, hs1, hs2⟩
  choose r hr using hchoice
  have hrpos : ∀ n : ℕ, 0 < r n := fun n => (hr n).1
  have hrlt : ∀ n : ℕ, r n < 1 / ((n : ℝ) + 1) := fun n => (hr n).2.1
  have hrdiam : ∀ n : ℕ,
      Metric.diam (closure (f '' (Metric.sphere ζ (r n) ∩ Metric.ball (0 : ℂ) 1))) <
        1 / ((n : ℝ) + 1) := fun n => (hr n).2.2
  have hrone : ∀ n : ℕ, r n < 1 := by
    intro n
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; simp
    linarith [hrlt n]
  have hr0 : Filter.Tendsto r Filter.atTop (𝓝 0) :=
    squeeze_zero (fun n => (hrpos n).le) (fun n => (hrlt n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hcross : Filter.Tendsto
      (fun n => Metric.diam (closure (f '' (Metric.sphere ζ (r n) ∩ Metric.ball (0 : ℂ) 1))))
      Filter.atTop (𝓝 0) :=
    squeeze_zero (fun n => Metric.diam_nonneg) (fun n => (hrdiam n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := lens_tendsto_zero hv hDo hDc hDb hDfr hf hfinj hfim hζ
    (fun n => ⟨hrpos n, hrone n⟩) hr0 hcross
  exact Work.RPB1a.Caratheodory.exists_diam_le_of_cap
    ⟨r, fun n => ⟨hrpos n, hrone n⟩, hr0, hlim⟩ hε

theorem continuous_extension_of_smooth_conformal (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v)
    (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDfr : closure D \ interior D = Set.range v)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hfinj : Set.InjOn f (Metric.ball 0 1)) (hfim : f '' Metric.ball 0 1 = D) :
    ∃ F : ℂ → ℂ, ContinuousOn F (Metric.closedBall 0 1) ∧ Set.EqOn F f (Metric.ball 0 1) ∧
      Set.MapsTo F (Metric.sphere 0 1) (Set.range v) := by
  have hdiam := lens_estimate v hv D hDo hDc hDb hDfr f hf hfinj hfim
  obtain ⟨F, hFc, hFeq⟩ :=
    Work.RPB1a.Caratheodory.exists_continuousOn_closedBall_of_diam_lens hf.continuousOn
      (by rw [hfim]; exact hDb) hdiam
  have hFim : F '' Metric.ball (0 : ℂ) 1 = D := by
    rw [← hfim]
    exact Set.image_congr fun x hx => hFeq hx
  refine ⟨F, hFc, hFeq, ?_⟩
  intro z hz
  have hcl : F z ∈ closure D :=
    Work.RPB1a.Caratheodory.mem_closure_of_continuousOn_closedBall hFc hFim hz
  have hnot : F z ∉ D :=
    Work.RPB1a.Caratheodory.notMem_of_continuousOn_closedBall hf hfinj hfim hFc hFeq hz
  have hmem : F z ∈ closure D \ interior D := by
    refine ⟨hcl, ?_⟩
    rwa [hDo.interior_eq]
  rwa [hDfr] at hmem

end

end Work.RPB.B1a

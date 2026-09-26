import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.MetricSpace.Closeds
import Submission.Commons.Topology.Continuum.exists_subseq_hausdorffDist_tendsto_zero
import Submission.Commons.Topology.Plane.disk_model_pullback_compact

open scoped Topology
open Filter Set

namespace Commons.Topology.Jordan

private lemma abs_infDist_sub_le (u v : Set ℂ) (x y : ℂ) :
    |(Metric.infDist x u - Metric.infDist x v) - (Metric.infDist y u - Metric.infDist y v)| ≤
      2 * dist x y := by
  have h1 : |Metric.infDist x u - Metric.infDist y u| ≤ dist x y := by
    have := (Metric.lipschitz_infDist_pt u).dist_le_mul x y
    simpa [Real.dist_eq] using this
  have h2 : |Metric.infDist x v - Metric.infDist y v| ≤ dist x y := by
    have := (Metric.lipschitz_infDist_pt v).dist_le_mul x y
    simpa [Real.dist_eq] using this
  have h3 : (Metric.infDist x u - Metric.infDist x v) - (Metric.infDist y u - Metric.infDist y v)
      = (Metric.infDist x u - Metric.infDist y u) - (Metric.infDist x v - Metric.infDist y v) := by
    ring
  rw [h3]
  calc |(Metric.infDist x u - Metric.infDist y u) - (Metric.infDist x v - Metric.infDist y v)|
      ≤ |Metric.infDist x u - Metric.infDist y u| + |Metric.infDist x v - Metric.infDist y v|
        := abs_sub _ _
    _ ≤ dist x y + dist x y := add_le_add h1 h2
    _ = 2 * dist x y := by ring

/-- If `E n` are preconnected and converge to `L` in Hausdorff distance with `L` compact, then
`L` is preconnected. -/
theorem isPreconnected_of_hausdorffDist_tendsto_zero {E : ℕ → Set ℂ} {L : Set ℂ} {R : ℝ}
    (hE : ∀ n, IsPreconnected (E n)) (hEne : ∀ n, (E n).Nonempty)
    (hsub : ∀ n, E n ⊆ Metric.closedBall (0 : ℂ) R) (hL : IsCompact L)
    (h : Filter.Tendsto (fun n => Metric.hausdorffDist (E n) L) Filter.atTop (nhds 0)) :
    IsPreconnected L := by
  rcases L.eq_empty_or_nonempty with rfl | hLne
  · exact isPreconnected_empty
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hL.isClosed]
  intro u v hu hv hLuv huv
  by_contra hcon
  have hLu : ¬ L ⊆ u := fun hsub' => hcon (Or.inl hsub')
  have hLv : ¬ L ⊆ v := fun hsub' => hcon (Or.inr hsub')
  obtain ⟨q, hqL, hqu⟩ := Set.not_subset.mp hLu
  obtain ⟨p, hpL, hpv⟩ := Set.not_subset.mp hLv
  have hpu : p ∈ u := by rcases hLuv hpL with h | h; exacts [h, absurd h hpv]
  have hqv : q ∈ v := by rcases hLuv hqL with h | h; exacts [absurd h hqu, h]
  have hvne : v.Nonempty := ⟨q, hqv⟩
  have hune : u.Nonempty := ⟨p, hpu⟩
  set f : ℂ → ℝ := fun x => Metric.infDist x u - Metric.infDist x v with hf
  have hfc : Continuous f :=
    (Metric.continuous_infDist_pt u).sub (Metric.continuous_infDist_pt v)
  have hfne : ∀ x ∈ L, f x ≠ 0 := by
    intro x hxL
    have hxuv : x ∈ u ∪ v := hLuv hxL
    rcases hxuv with hxu | hxv
    · have hxv' : x ∉ v := fun hc => Set.disjoint_left.mp huv hxu hc
      have hpos : 0 < Metric.infDist x v :=
        (Metric.infDist_pos_iff_notMem_closure hvne).mp (by rw [hv.closure_eq]; exact hxv')
      simp only [hf]
      rw [Metric.infDist_zero_of_mem hxu]
      linarith
    · have hxu' : x ∉ u := fun hc => Set.disjoint_left.mp huv hc hxv
      have hpos : 0 < Metric.infDist x u :=
        (Metric.infDist_pos_iff_notMem_closure hune).mp (by rw [hu.closure_eq]; exact hxu')
      simp only [hf]
      rw [Metric.infDist_zero_of_mem hxv]
      linarith
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ x ∈ L, δ ≤ |f x| := by
    obtain ⟨x₀, hx₀L, hmin⟩ := hL.exists_isMinOn hLne hfc.abs.continuousOn
    exact ⟨|f x₀|, abs_pos.mpr (hfne x₀ hx₀L), fun x hx => hmin hx⟩
  have hfp : f p < 0 := by
    have hpos : 0 < Metric.infDist p v :=
      (Metric.infDist_pos_iff_notMem_closure hvne).mp (by rw [hv.closure_eq]; exact hpv)
    simp only [hf]; rw [Metric.infDist_zero_of_mem hpu]; linarith
  have hfq : 0 < f q := by
    have hpos : 0 < Metric.infDist q u :=
      (Metric.infDist_pos_iff_notMem_closure hune).mp (by rw [hu.closure_eq]; exact hqu)
    simp only [hf]; rw [Metric.infDist_zero_of_mem hqv]; linarith
  have h_open_lt : IsOpen {x : ℂ | f x < 0} := isOpen_lt hfc continuous_const
  have h_open_gt : IsOpen {x : ℂ | 0 < f x} := isOpen_lt continuous_const hfc
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.isOpen_iff.mp h_open_lt p hfp
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.isOpen_iff.mp h_open_gt q hfq
  set ε : ℝ := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  set η : ℝ := min ε (δ / 4) with hηdef
  have hη : 0 < η := lt_min hε (by linarith)
  have hev : ∀ᶠ n in atTop, Metric.hausdorffDist (E n) L < η :=
    (tendsto_order.1 h).2 η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hfin : ∀ n, Metric.hausdorffEDist (E n) L ≠ ⊤ := fun n =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hEne n) hLne
      (Metric.isBounded_closedBall.subset (hsub n)) hL.isBounded
  have hkey : ∀ n ≥ N, False := by
    intro n hn
    have hdn : Metric.hausdorffDist (E n) L < η := hN n hn
    have hdε : Metric.hausdorffDist (E n) L < ε := lt_of_lt_of_le hdn (min_le_left _ _)
    have hdδ : Metric.hausdorffDist (E n) L < δ / 4 := lt_of_lt_of_le hdn (min_le_right _ _)
    obtain ⟨e, heE, hed⟩ :=
      Metric.exists_dist_lt_of_hausdorffDist_lt' hpL hdε (hfin n)
    have hed' : dist p e < ε := by rw [dist_comm]; exact hed
    have hef : f e < 0 :=
      hε₁sub (by rw [Metric.mem_ball, dist_comm]
                 exact lt_of_lt_of_le hed' (min_le_left _ _))
    obtain ⟨e', he'E, he'd⟩ :=
      Metric.exists_dist_lt_of_hausdorffDist_lt' hqL hdε (hfin n)
    have he'd' : dist q e' < ε := by rw [dist_comm]; exact he'd
    have he'f : 0 < f e' :=
      hε₂sub (by rw [Metric.mem_ball, dist_comm]
                 exact lt_of_lt_of_le he'd' (min_le_right _ _))
    have hpre : IsPreconnected (f '' E n) := (hE n).image f hfc.continuousOn
    have hfe : f e ∈ f '' E n := ⟨e, heE, rfl⟩
    have hfe' : f e' ∈ f '' E n := ⟨e', he'E, rfl⟩
    have hmem0 : (0:ℝ) ∈ f '' E n :=
      hpre.Icc_subset hfe hfe' ⟨le_of_lt hef, le_of_lt he'f⟩
    obtain ⟨x, hxE, hfx⟩ := hmem0
    obtain ⟨l, hlL, hlx⟩ : ∃ l ∈ L, dist x l < δ / 4 :=
      Metric.exists_dist_lt_of_hausdorffDist_lt hxE hdδ (hfin n)
    have hbig : δ ≤ |f l| := hδle l hlL
    have hclose : |f x - f l| ≤ 2 * dist x l := abs_infDist_sub_le u v x l
    rw [hfx] at hclose
    simp only [zero_sub, abs_neg] at hclose
    have : |f l| < δ := by linarith
    linarith [hbig, this]
  exact hkey N le_rfl


/-! ### The disk model of the one-point compactification

`demb z = z / (1 + ‖z‖)` maps `ℂ` homeomorphically onto the open unit disk; together with the unit
circle (playing the role of the point at infinity) it is a metric realisation, inside `ℂ`, of the
one-point compactification of `ℂ`.  This lets us apply the Blaschke selection principle to sequences
of *unbounded* connected sets. -/

/-- The disk-model map `z ↦ z / (1 + ‖z‖)`. -/
private noncomputable def demb (z : ℂ) : ℂ := z / (((1 : ℝ) + ‖z‖ : ℝ) : ℂ)

/-- The inverse of `demb` on the open unit disk: `w ↦ w / (1 - ‖w‖)`. -/
private noncomputable def dembInv (w : ℂ) : ℂ := w / (((1 : ℝ) - ‖w‖ : ℝ) : ℂ)

private lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

private lemma demb_apply (z : ℂ) : demb z = z / (((1 : ℝ) + ‖z‖ : ℝ) : ℂ) := rfl

private lemma dembInv_apply (w : ℂ) : dembInv w = w / (((1 : ℝ) - ‖w‖ : ℝ) : ℂ) := rfl

private lemma demb_norm (z : ℂ) : ‖demb z‖ = ‖z‖ / (1 + ‖z‖) := by
  rw [demb_apply, norm_div, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]

private lemma demb_norm_lt_one (z : ℂ) : ‖demb z‖ < 1 := by
  rw [demb_norm, div_lt_one (by positivity)]
  linarith [norm_nonneg z]

private lemma demb_norm_le (z : ℂ) : ‖demb z‖ ≤ ‖z‖ := by
  rw [demb_norm]
  exact div_le_self (norm_nonneg z) (by linarith [norm_nonneg z])

private lemma demb_zero : demb (0 : ℂ) = 0 := by
  simp [demb_apply]

private lemma dembInv_demb (z : ℂ) : dembInv (demb z) = z := by
  have hne : (1 + ‖z‖ : ℝ) ≠ 0 := by positivity
  rw [dembInv_apply, demb_norm]
  have h1 : (1 - ‖z‖ / (1 + ‖z‖) : ℝ) = 1 / (1 + ‖z‖) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
    ring
  rw [h1, demb_apply]
  have h2 : (((1 : ℝ) + ‖z‖ : ℝ) : ℂ) * (((1 / (1 + ‖z‖) : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hne]
    simp
  rw [div_div, h2, div_one]

private lemma demb_injective : Function.Injective demb := by
  intro z w hzw
  have := congrArg dembInv hzw
  rwa [dembInv_demb, dembInv_demb] at this

private lemma demb_dembInv {w : ℂ} (hw : ‖w‖ < 1) : demb (dembInv w) = w := by
  have hne : (1 - ‖w‖ : ℝ) ≠ 0 := by linarith
  rw [dembInv_apply]
  have hnorm : ‖w / (((1 : ℝ) - ‖w‖ : ℝ) : ℂ)‖ = ‖w‖ / (1 - ‖w‖) := by
    rw [norm_div, norm_ofReal_eq_abs, abs_of_nonneg (by linarith)]
  rw [demb_apply, hnorm]
  have h1 : (1 + ‖w‖ / (1 - ‖w‖) : ℝ) = 1 / (1 - ‖w‖) := by
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
    ring
  rw [h1]
  have h2 : (((1 : ℝ) - ‖w‖ : ℝ) : ℂ) * (((1 / (1 - ‖w‖) : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hne]
    simp
  rw [div_div, h2, div_one]

private lemma demb_mem_image_iff {K : Set ℂ} {w : ℂ} :
    w ∈ demb '' K ↔ ‖w‖ < 1 ∧ dembInv w ∈ K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨demb_norm_lt_one z, by rw [dembInv_demb]; exact hz⟩
  · rintro ⟨hw, hwK⟩
    exact ⟨dembInv w, hwK, demb_dembInv hw⟩

private lemma continuous_demb : Continuous demb := by
  unfold demb
  refine Continuous.div₀ continuous_id ?_ ?_
  · exact Complex.continuous_ofReal.comp (continuous_const.add continuous_norm)
  · intro z
    exact_mod_cast (by positivity : (1 + ‖z‖ : ℝ) ≠ 0)

private lemma continuousOn_dembInv : ContinuousOn dembInv (Metric.ball (0:ℂ) 1) := by
  unfold dembInv
  refine ContinuousOn.div₀ continuousOn_id ?_ ?_
  · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_norm)).continuousOn
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
    exact_mod_cast (by linarith : (1 - ‖w‖ : ℝ) ≠ 0)

/-- Accumulation points of `demb '' K` are in `demb '' K` or on the unit circle. -/
private lemma demb_image_closure_subset {K : Set ℂ} (hK : IsClosed K) :
    closure (demb '' K) ⊆ demb '' K ∪ Metric.sphere (0 : ℂ) 1 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  intro w hw
  have hsub1 : demb '' K ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rintro u ⟨z, -, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (demb_norm_lt_one z)
  have hwle : ‖w‖ ≤ 1 := by
    have h := closure_minimal hsub1 Metric.isClosed_closedBall hw
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  by_cases hw1 : ‖w‖ = 1
  · exact Or.inr (by rw [Metric.mem_sphere, dist_zero_right]; exact hw1)
  · refine Or.inl ?_
    have hwlt : ‖w‖ < 1 := lt_of_le_of_ne hwle hw1
    rw [demb_mem_image_iff]
    refine ⟨hwlt, ?_⟩
    have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hwlt
    have hc : ContinuousAt dembInv w :=
      continuousOn_dembInv.continuousAt (Metric.isOpen_ball.mem_nhds hwball)
    rw [hK.mem_iff_infDist_zero hKne, ← Metric.mem_closure_iff_infDist_zero hKne]
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδh⟩ := Metric.continuousAt_iff.mp hc ε hε
    obtain ⟨u, hu, hwu⟩ := Metric.mem_closure_iff.mp hw δ hδ
    obtain ⟨z, hzK, rfl⟩ := hu
    have h1 : dist (demb z) w < δ := by rw [dist_comm]; exact hwu
    have h2 := hδh h1
    rw [dembInv_demb] at h2
    exact ⟨z, hzK, by rw [dist_comm]; exact h2⟩

/-- Blaschke selection, with the qualitative properties of the limit. -/
private theorem exists_hausdorff_limit_compact {E : ℕ → Set ℂ} {R : ℝ}
    (hne : ∀ n, (E n).Nonempty) (hsub : ∀ n, E n ⊆ Metric.closedBall (0 : ℂ) R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : Set ℂ, L.Nonempty ∧ IsCompact L ∧
      L ⊆ Metric.closedBall (0 : ℂ) R ∧
      Filter.Tendsto (fun n => Metric.hausdorffDist (E (φ n)) L) Filter.atTop (nhds 0) := by
  have hball : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hclos_sub : ∀ n, closure (E n) ⊆ Metric.closedBall (0 : ℂ) R := by
    intro n
    calc closure (E n) ⊆ closure (Metric.closedBall (0 : ℂ) R) := closure_mono (hsub n)
      _ = Metric.closedBall (0 : ℂ) R := Metric.isClosed_closedBall.closure_eq
  have hcomp : ∀ n, IsCompact (closure (E n)) := fun n =>
    hball.of_isClosed_subset isClosed_closure (hclos_sub n)
  let G : ℕ → TopologicalSpace.NonemptyCompacts ℂ := fun n =>
    ⟨⟨closure (E n), hcomp n⟩, (hne n).closure⟩
  have hGmem : ∀ n,
      G n ∈ {K : TopologicalSpace.NonemptyCompacts ℂ | (K : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) R} :=
    fun n => hclos_sub n
  have hS : IsCompact
      {K : TopologicalSpace.NonemptyCompacts ℂ | (K : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) R} :=
    TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hball
  obtain ⟨K, hKmem, φ, hφmono, hφlim⟩ := hS.tendsto_subseq hGmem
  refine ⟨φ, hφmono, (K : Set ℂ), K.2, K.1.2, hKmem, ?_⟩
  have hdist : Filter.Tendsto (fun n => dist (G (φ n)) K) Filter.atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hφlim
  have heq : (fun n => dist (G (φ n)) K)
      = (fun n => Metric.hausdorffDist (E (φ n)) (K : Set ℂ)) := by
    funext n
    simp only [Metric.NonemptyCompacts.dist_eq]
    have hG : (G (φ n) : Set ℂ) = closure (E (φ n)) := rfl
    rw [hG, Metric.hausdorffDist_closure₁]
  rw [heq] at hdist
  exact hdist

/-- **Welding lemma.**  If `E n` are nonempty preconnected subsets of a fixed closed ball in `ℂ`,
all meeting a fixed compact set `A`, and some point `x` has `infDist x (E n) → 0`, then there is a
compact preconnected set `L` contained in `closure (⋃ n, E n)` with `x ∈ L` and `L ∩ A ≠ ∅`. -/
private theorem exists_preconnected_limit_meeting {E : ℕ → Set ℂ} {R : ℝ} {x : ℂ} {A : Set ℂ}
    (hE : ∀ n, IsPreconnected (E n)) (hEne : ∀ n, (E n).Nonempty)
    (hsub : ∀ n, E n ⊆ Metric.closedBall (0 : ℂ) R)
    (hx : Filter.Tendsto (fun n => Metric.infDist x (E n)) Filter.atTop (nhds 0))
    (hA : IsCompact A) (hAm : ∀ n, (E n ∩ A).Nonempty) :
    ∃ L : Set ℂ, IsCompact L ∧ IsPreconnected L ∧ x ∈ L ∧ (L ∩ A).Nonempty ∧
      L ⊆ closure (⋃ n, E n) := by
  classical
  choose a haE haA using hAm
  obtain ⟨a₀, ha₀A, φ₁, hφ₁mono, hφ₁lim⟩ := hA.tendsto_subseq haA
  obtain ⟨φ₂, hφ₂mono, L, hLne, hLc, hLsub, hlim⟩ :=
    exists_hausdorff_limit_compact (E := fun n => E (φ₁ n)) (R := R)
      (fun n => hEne _) (fun n => hsub _)
  have hfin : ∀ n, Metric.hausdorffEDist (E (φ₁ (φ₂ n))) L ≠ ⊤ := fun n =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hEne _) hLne
      (Metric.isBounded_closedBall.subset (hsub _)) hLc.isBounded
  have hx₂ : Filter.Tendsto (fun n => Metric.infDist x (E (φ₁ (φ₂ n)))) Filter.atTop (nhds 0) :=
    hx.comp (hφ₁mono.comp hφ₂mono).tendsto_atTop
  have ha₂ : Filter.Tendsto (fun n => a (φ₁ (φ₂ n))) Filter.atTop (nhds a₀) :=
    hφ₁lim.comp hφ₂mono.tendsto_atTop
  refine ⟨L, hLc, ?_, ?_, ?_, ?_⟩
  · exact isPreconnected_of_hausdorffDist_tendsto_zero (fun n => hE _) (fun n => hEne _)
      (fun n => hsub _) hLc hlim
  · rw [hLc.isClosed.mem_iff_infDist_zero hLne]
    refine le_antisymm ?_ Metric.infDist_nonneg
    by_contra hcon
    have hpos : 0 < Metric.infDist x L := lt_of_not_ge hcon
    have h1 : ∀ᶠ n in Filter.atTop, Metric.infDist x (E (φ₁ (φ₂ n))) < Metric.infDist x L / 2 :=
      (tendsto_order.1 hx₂).2 _ (by linarith)
    have h2 : ∀ᶠ n in Filter.atTop,
        Metric.hausdorffDist (E (φ₁ (φ₂ n))) L < Metric.infDist x L / 2 :=
      (tendsto_order.1 hlim).2 _ (by linarith)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    have := Metric.infDist_le_infDist_add_hausdorffDist (x := x)
      (s := E (φ₁ (φ₂ n))) (t := L) (hfin n)
    linarith
  · have hd : Filter.Tendsto (fun n => Metric.infDist (a (φ₁ (φ₂ n))) L) Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun n => Metric.infDist_nonneg) (fun n => ?_) hlim
      exact Metric.infDist_le_hausdorffDist_of_mem (haE _) (hfin n)
    have hcl : a₀ ∈ closure L := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hε2 : (0 : ℝ) < ε / 2 := by linarith
      have h1 : ∀ᶠ n in Filter.atTop, Metric.infDist (a (φ₁ (φ₂ n))) L < ε / 2 :=
        (tendsto_order.1 hd).2 _ hε2
      have h2 : ∀ᶠ n in Filter.atTop, dist a₀ (a (φ₁ (φ₂ n))) < ε / 2 := by
        filter_upwards [ha₂ (Metric.ball_mem_nhds a₀ hε2)] with n hn
        rw [Set.mem_preimage, Metric.mem_ball, dist_comm] at hn
        exact hn
      obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
      obtain ⟨y, hyL, hy⟩ := (Metric.infDist_lt_iff hLne).mp hn1
      exact ⟨y, hyL, by linarith [dist_triangle a₀ (a (φ₁ (φ₂ n))) y, hy, hn2]⟩
    exact ⟨a₀, hLc.isClosed.closure_eq ▸ hcl, ha₀A⟩
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 ε hε)
    obtain ⟨w, hw, hdw⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt' hz (hN N le_rfl) (hfin N)
    exact ⟨w, Set.mem_iUnion.mpr ⟨φ₁ (φ₂ N), hw⟩, by rw [dist_comm]; exact hdw⟩

/-- The transport step of the disk model: boundary bumping for ball traces, i.e. the commons lemma
`Commons.Topology.Plane.disk_model_pullback_compact`. -/
private theorem pullback_step {K : Set ℂ} (hK : IsClosed K) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {L : Set ℂ} (hLc : IsPreconnected L) (hLcomp : IsCompact L) (h0L : (0 : ℂ) ∈ L)
    (hsub : L ⊆ demb '' K ∪ Metric.sphere (0 : ℂ) 1)
    (hmeet : (L ∩ Metric.sphere (0 : ℂ) ρ).Nonempty) :
    ∃ z : ℂ, ‖z‖ = ρ / (1 - ρ) ∧ z ∈ connectedComponentIn K (0 : ℂ) := by
  refine Commons.Topology.Plane.disk_model_pullback_compact hK hρ hρ1 hLc hLcomp h0L ?_ hmeet
  have hone : demb = fun z : ℂ => z / (((1 : ℝ) + ‖z‖ : ℝ) : ℂ) := rfl
  rwa [hone] at hsub

/-- **Crux helper.**  Let `K ⊆ ℂ` be closed, `0 ∈ K`, `r > 0`.  If `(Q n)` are connected
components of `K`, each meeting the circle `{z | ‖z‖ = r}` and each coming arbitrarily close to
`0` (`dist 0 (Q n) → 0`), then some point of that circle lies in the connected component of `0`
in `K`. -/
theorem component_meets_circle_of_components_approaching {K : Set ℂ} (hK : IsClosed K)
    (h0 : (0 : ℂ) ∈ K) {r : ℝ} (hr : 0 < r) (Q : ℕ → Set ℂ)
    (hQ : ∀ n, ∃ x ∈ K, Q n = connectedComponentIn K x)
    (hQr : ∀ n, (Q n ∩ {z : ℂ | ‖z‖ = r}).Nonempty)
    (hQ0 : Filter.Tendsto (fun n => Metric.infDist (0 : ℂ) (Q n)) Filter.atTop (nhds 0)) :
    ∃ z : ℂ, ‖z‖ = r ∧ z ∈ connectedComponentIn K (0 : ℂ) := by
  set ρ : ℝ := r / (1 + r) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hρlt : ρ < 1 := by
    rw [hρdef, div_lt_one (by positivity)]
    linarith
  have hρr : ρ / (1 - ρ) = r := by
    rw [hρdef]
    field_simp
    ring
  -- the compactification of `K` realised inside the closed unit ball
  set Kc : Set ℂ := closure (demb '' K) ∪ Metric.sphere (0 : ℂ) 1 with hKcdef
  have hKcclosed : IsClosed Kc := isClosed_closure.union Metric.isClosed_sphere
  have hQsub : ∀ n, Q n ⊆ K := by
    intro n
    obtain ⟨x, _, hxQ⟩ := hQ n
    rw [hxQ]
    exact connectedComponentIn_subset K x
  -- the preconnected images
  set E : ℕ → Set ℂ := fun n => closure (demb '' Q n) with hEdef
  have hEne : ∀ n, (E n).Nonempty := by
    intro n
    obtain ⟨x, hxK, hxQ⟩ := hQ n
    refine ⟨demb x, subset_closure ⟨x, ?_, rfl⟩⟩
    rw [hxQ]
    exact mem_connectedComponentIn hxK
  have hEpc : ∀ n, IsPreconnected (E n) := by
    intro n
    obtain ⟨x, _, hxQ⟩ := hQ n
    have h1 : IsPreconnected (Q n) := by
      rw [hxQ]
      exact isPreconnected_connectedComponentIn
    exact (h1.image demb continuous_demb.continuousOn).closure
  have hEsub : ∀ n, E n ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro n
    refine closure_minimal ?_ Metric.isClosed_closedBall
    rintro w ⟨z, -, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (demb_norm_lt_one z)
  have hEmeet : ∀ n, (E n ∩ (Kc ∩ Metric.sphere (0 : ℂ) ρ)).Nonempty := by
    intro n
    obtain ⟨z, hzQ, hzr⟩ := hQr n
    refine ⟨demb z, subset_closure ⟨z, hzQ, rfl⟩, Or.inl (subset_closure ⟨z, hQsub n hzQ, rfl⟩), ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, demb_norm, hzr, hρdef]
  have hE0 : Filter.Tendsto (fun n => Metric.infDist (0 : ℂ) (E n)) Filter.atTop (nhds 0) := by
    have hb : Filter.Tendsto
        (fun n => Metric.infDist (0 : ℂ) (Q n) + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      simpa using hQ0.add tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => Metric.infDist_nonneg) (fun n => ?_) hb
    have hne : (Q n).Nonempty := by
      obtain ⟨x, hxK, hxQ⟩ := hQ n
      exact ⟨x, by rw [hxQ]; exact mem_connectedComponentIn hxK⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨x, hxQ, hx⟩ := (Metric.infDist_lt_iff hne).mp
      (by linarith : Metric.infDist (0 : ℂ) (Q n) < Metric.infDist (0 : ℂ) (Q n) + 1 / ((n:ℝ)+1))
    rw [dist_zero_left] at hx
    calc Metric.infDist (0 : ℂ) (E n) ≤ ‖demb x‖ := by
          rw [← dist_zero_left (demb x)]
          exact Metric.infDist_le_dist_of_mem (subset_closure ⟨x, hxQ, rfl⟩)
      _ ≤ ‖x‖ := demb_norm_le x
      _ ≤ Metric.infDist (0 : ℂ) (Q n) + 1 / ((n : ℝ) + 1) := le_of_lt hx
  have hAc : IsCompact (Kc ∩ Metric.sphere (0 : ℂ) ρ) := by
    refine (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      (hKcclosed.inter Metric.isClosed_sphere) ?_
    intro z hz
    have h1 : ‖z‖ = ρ := by
      have := hz.2
      rwa [Metric.mem_sphere, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_zero_right, h1]
    exact hρlt.le
  obtain ⟨L, hLc, hLpc, h0L, hLmeet, hLsub⟩ :=
    exists_preconnected_limit_meeting hEpc hEne hEsub hE0 hAc hEmeet
  -- `L` lies in the disk model of `K`
  have hLsubK : L ⊆ demb '' K ∪ Metric.sphere (0 : ℂ) 1 := by
    have hunion : (⋃ n, E n) ⊆ Kc := by
      intro w hw
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
      rw [hEdef] at hn
      rw [hKcdef]
      exact (closure_mono (Set.image_mono (hQsub n))).trans Set.subset_union_left hn
    have h2 : closure (⋃ n, E n) ⊆ Kc := by
      rw [hKcdef]
      exact closure_minimal hunion hKcclosed
    have h3 : Kc ⊆ demb '' K ∪ Metric.sphere (0 : ℂ) 1 := by
      rw [hKcdef]
      exact union_subset (demb_image_closure_subset hK) Set.subset_union_right
    exact fun z hz => h3 (h2 (hLsub hz))
  have hmeet' : (L ∩ Metric.sphere (0 : ℂ) ρ).Nonempty := by
    obtain ⟨w, hwL, -, hwS⟩ := hLmeet
    exact ⟨w, hwL, hwS⟩
  obtain ⟨z, hzr, hzP⟩ := pullback_step hK hρpos hρlt hLpc hLc h0L hLsubK hmeet'
  exact ⟨z, by rw [hzr, hρr], hzP⟩

/-- A bounded connected component of a closed set leaves a "spanning-free" annulus around `0`. -/
theorem annulus_no_spanning {K : Set ℂ} (hK : IsClosed K) (h0 : (0 : ℂ) ∈ K)
    (hbdd : Bornology.IsBounded (connectedComponentIn K 0)) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ C : Set ℂ, C ⊆ K → IsPreconnected C →
        (C ∩ {z : ℂ | ‖z‖ = a}).Nonempty →
        (C ∩ {z : ℂ | ‖z‖ = b}).Nonempty → False := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbdd
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (0:ℂ)) (hM 0 (mem_connectedComponentIn h0))
  by_contra hcon
  push_neg at hcon
  -- for every `n`, a preconnected subset of `K` meeting the circles of radii `1/(n+2)` and `M+1`
  have hlt : ∀ n : ℕ, (1:ℝ) / ((n:ℝ) + 2) < M + 1 := by
    intro n
    have h1 : (1:ℝ) / ((n:ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  choose C hC hCpre hCab using fun n : ℕ => hcon (1 / ((n:ℝ) + 2)) (M + 1) (by positivity) (hlt n)
  have hCa : ∀ n, (C n ∩ {z : ℂ | ‖z‖ = 1 / ((n:ℝ) + 2)}).Nonempty := fun n => (hCab n).1
  have hCb : ∀ n, (C n ∩ {z : ℂ | ‖z‖ = M + 1}).Nonempty := fun n => (hCab n).2.1
  choose x hxC hxr using hCa
  have hxK : ∀ n, x n ∈ K := fun n => hC n (hxC n)
  -- the components containing the `C n`
  set Q : ℕ → Set ℂ := fun n => connectedComponentIn K (x n) with hQdef
  have hQ : ∀ n, ∃ y ∈ K, Q n = connectedComponentIn K y := fun n => ⟨x n, hxK n, rfl⟩
  have hCl : ∀ n, C n ⊆ Q n := fun n =>
    IsPreconnected.subset_connectedComponentIn (hCpre n) (hxC n) (hC n)
  have hQr : ∀ n, (Q n ∩ {z : ℂ | ‖z‖ = M + 1}).Nonempty := by
    intro n
    obtain ⟨z, hz, hzr⟩ := hCb n
    exact ⟨z, hCl n hz, hzr⟩
  have hQ0 : Filter.Tendsto (fun n => Metric.infDist (0 : ℂ) (Q n)) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => Metric.infDist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmem : x n ∈ Q n := mem_connectedComponentIn (hxK n)
    calc Metric.infDist (0:ℂ) (Q n) ≤ dist (0:ℂ) (x n) := Metric.infDist_le_dist_of_mem hmem
      _ = 1 / ((n:ℝ) + 2) := by rw [dist_zero_left, hxr n]
      _ ≤ 1 / ((n:ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨z, hzr, hzP⟩ := component_meets_circle_of_components_approaching hK h0
    (by linarith) Q hQ hQr hQ0
  have : ‖z‖ ≤ M := hM z hzP
  rw [hzr] at this
  linarith

end Commons.Topology.Jordan

/-!
## Summary

**`annulus_no_spanning`** (the target): if `K ⊆ ℂ` is closed, `0 ∈ K` and the connected component
of `0` in `K` is bounded, then there are `0 < a < b` such that no preconnected subset of `K` meets
both circles `‖z‖ = a` and `‖z‖ = b`.

Proof route:

1. **Contradiction reduction.**  If every pair `a < b` is spanned, apply this to `a = 1/(n+2)` and
   `b = M+1` (where `comp_0 K ⊆ closedBall 0 M`), obtaining preconnected `C n ⊆ K` meeting both
   circles.  Passing to the components `Q n` gives connected components of `K` meeting the circle
   of radius `M+1` with `infDist 0 (Q n) → 0`.
2. **The crux** (`component_meets_circle_of_components_approaching`): such a family of components
   forces the component of `0` to meet the circle, contradicting `comp_0 K ⊆ closedBall 0 M`.
3. The crux is proved via the **disk model** of the one-point compactification:
   `demb z = z / (1 + ‖z‖)` maps `ℂ` homeomorphically onto the open unit disk, and
   `closure (demb '' K) ∪ {‖w‖ = 1}` is the image of `K` in the compactification.  The images
   `E n := closure (demb '' Q n)` are nonempty preconnected subsets of the closed unit ball meeting
   the circle of radius `ρ := r/(1+r)`, with `infDist 0 (E n) → 0`; Blaschke selection plus
   `exists_preconnected_limit_meeting` produce a compact preconnected `L ⊆ closure (⋃ n, E n)` with
   `0 ∈ L` and `L` meeting that circle.
4. **Boundary bumping** (`Commons.Topology.Plane.disk_model_pullback_compact`, the transport step,
   proved in the shared commons): a compact preconnected `L` through `0` in the disk model meeting
   the circle of radius `ρ` forces `comp_0 K` either to meet the circle of radius `ρ/(1-ρ)` (when `L`
   stays inside the open disk) or to be unbounded (when `L` meets the "circle at infinity"), and
   either way `comp_0 K` meets the circle of radius `ρ/(1-ρ) = r`.
-/

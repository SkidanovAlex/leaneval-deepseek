import Mathlib
import Submission.Work.Routing.junctionHelpers
import Submission.Work.Crux.reparam_gen

/-!
# Tools for the stage piece of the drawn arc

Three self-contained lemmas used by `Work.Drive.TwoRays.stagePieceOfDrawnArc`:

* `exists_chartBall_subset_given`: chart balls around a point of a chart source form a
  neighbourhood basis, *in the given chart*.
* `arc_gap_of_negative_segment`: an arc through `σ` which contains a piece of the *negative* `u`-segment
  near `σ` contains no point of the *positive* `u`-segment near `σ`.
* `exists_chartSeed`: the straight germ ray (reparametrised) is a seed arc for the reachability, and
  its non-germ part can be kept inside a prescribed gap of the spike.
-/

namespace Work.Drive.TwoRays

open Set Topology
open scoped Manifold ContDiff
open Work.Noncompact.CompressionTube

/-- Chart balls around a point of the source of a chart `c` form a neighbourhood basis *in that
chart*: every open neighbourhood `U ∋ σ` contains the image of a ball around `c σ`. -/
lemma exists_chartBall_subset_given {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M} (hσsrc : σ ∈ c.source)
    {U : Set M} (hUo : IsOpen U) (hσU : σ ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ c.symm '' Metric.ball (c σ) ρ ⊆ U := by
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target hUo
  have hmem : c σ ∈ c.target ∩ c.symm ⁻¹' U := by
    refine ⟨c.map_source hσsrc, ?_⟩
    change c.symm (c σ) ∈ U
    rw [c.left_inv hσsrc]
    exact hσU
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen (c σ) hmem
  exact ⟨ρ, hρ, by rintro x ⟨y, hy, rfl⟩; exact (hball hy).2⟩

/-- **The gap of the spike.**

Let `A` be a continuous arc, injective on `[0,1]`, with `A 1 = σ`, which contains the whole
*negative* `u`-chart segment `s ↦ c.symm (c σ - s • u)`, `s ∈ [0,ε₀]`, around its endpoint `σ`
(in the image of its parameter interval).  Then the *positive* `u`-chart segment has a gap at `σ`:
there is `δ > 0` such that `c.symm (c σ + s • u) ∉ A '' [0,1]` for every `s ∈ (0,δ]`.

The proof: the times of the negative segment fill a genuine interval ending at `1` (the map
`A : [0,1] → A '' [0,1]` is a homeomorphism, so the preimage of the negative segment is an interval
which contains `1` and another point), hence the tail of `A` lies on the negative segment; a point of
the positive segment close to `σ` has a time close to `1` (the early part `A '' [0, t₀]` is a compact
set avoiding `σ`, so a chart ball around `σ` misses it), hence also on the negative segment, which is
impossible since the two segments meet only at `σ`. -/
theorem arc_gap_of_negative_segment {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {σ : M} (hσsrc : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0)
    {A : ℝ → M} (hAc : Continuous A) (hAinj : Set.InjOn A (Set.Icc (0:ℝ) 1))
    (hA1 : A 1 = σ)
    {ε₀ ε₁ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁)
    (hseg : ∀ s : ℝ, 0 ≤ s → s ≤ ε₀ → c.symm (c σ - s • u) ∈ A '' Set.Icc (0:ℝ) 1)
    (htgtm : ∀ s : ℝ, 0 ≤ s → s ≤ ε₀ → c σ - s • u ∈ c.target)
    (htgtp : ∀ s : ℝ, 0 < s → s ≤ ε₁ → c σ + s • u ∈ c.target) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε₁ ∧
      ∀ s : ℝ, 0 < s → s ≤ δ → c.symm (c σ + s • u) ∉ A '' Set.Icc (0:ℝ) 1 := by
  classical
  set I : Set ℝ := Set.Icc (0:ℝ) 1 with hI
  have hIcomp : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  have hIpc : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  set G : Set ℝ := Set.Icc (0:ℝ) ε₀ with hG
  have hGcomp : CompactSpace G := isCompact_iff_compactSpace.mp isCompact_Icc
  have hGpc : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  set K : Set M := A '' I with hK
  have hgcont : Continuous fun y : G => c.symm (c σ - y.1 • u) :=
    c.continuousOn_symm.comp_continuous (by fun_prop) (fun y => htgtm y.1 y.2.1 y.2.2)
  set Φ : I → K := fun t => ⟨A t.1, ⟨t.1, t.2, rfl⟩⟩ with hΦdef
  have hΦc : Continuous Φ :=
    Continuous.subtype_mk (hAc.comp continuous_subtype_val) (fun t => ⟨t.1, t.2, rfl⟩)
  have hΦb : Function.Bijective Φ := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have h1 : A x = A y := by
        have h2 := congrArg Subtype.val hxy
        simpa [hΦdef] using h2
      exact Subtype.ext (hAinj hx hy h1)
    · rintro ⟨z, hz⟩
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨⟨t, ht⟩, ?_⟩
      exact Subtype.ext htz
  have hΦhom : IsHomeomorph Φ := (isHomeomorph_iff_continuous_bijective).mpr ⟨hΦc, hΦb⟩
  set e : I ≃ₜ K := hΦhom.homeomorph Φ with hedef
  set gK : G → K := fun y => ⟨c.symm (c σ - y.1 • u), hseg y.1 y.2.1 y.2.2⟩ with hgKdef
  have hgKc : Continuous gK :=
    Continuous.subtype_mk (f := fun y : G => c.symm (c σ - y.1 • u)) hgcont
      (fun y => hseg y.1 y.2.1 y.2.2)
  set τ : G → I := fun y => e.symm (gK y) with hτdef
  have hτc : Continuous τ := e.symm.continuous.comp hgKc
  set T : Set ℝ := {t : ℝ | ∃ y : G, (τ y : ℝ) = t} with hTdef
  have hTeq : T = Subtype.val '' (Set.range τ) := by
    ext t; constructor
    · rintro ⟨y, rfl⟩; exact ⟨τ y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩
  have hTpc : IsPreconnected T := by
    rw [hTeq]
    have h1 : IsPreconnected (τ '' Set.univ) := isPreconnected_univ.image τ hτc.continuousOn
    rw [Set.image_univ] at h1
    exact h1.image _ continuous_subtype_val.continuousOn
  have hord : Set.OrdConnected T := isPreconnected_iff_ordConnected.mp hTpc
  have hy0G : (0:ℝ) ∈ G := by simp [hG, hε₀.le]
  have hy1G : ε₀ ∈ G := by simp [hG, hε₀.le]
  have h1I : (1:ℝ) ∈ I := by simp [hI]
  have hτ0 : ((τ ⟨0, hy0G⟩ : I) : ℝ) = 1 := by
    have h1 : gK ⟨0, hy0G⟩ = e ⟨1, h1I⟩ := by
      refine Subtype.ext ?_
      show c.symm (c σ - (0:ℝ) • u) = A 1
      rw [hA1, zero_smul, sub_zero, c.left_inv hσsrc]
    rw [hτdef]
    show ((e.symm (gK ⟨0, hy0G⟩) : I) : ℝ) = 1
    rw [h1, Homeomorph.symm_apply_apply]
  have hAval : ∀ y : G, A (τ y).1 = c.symm (c σ - y.1 • u) := by
    intro y
    have h1 : e (τ y) = gK y := by rw [hτdef]; exact e.apply_symm_apply (gK y)
    have h2 := congrArg Subtype.val h1
    simpa [hedef, hΦdef, hgKdef] using h2
  have hτ1lt : ((τ ⟨ε₀, hy1G⟩ : I) : ℝ) < 1 := by
    refine lt_of_le_of_ne (τ ⟨ε₀, hy1G⟩).2.2 ?_
    intro hcon
    have h3 : c.symm (c σ - ε₀ • u) = σ := by
      have h4 := hAval ⟨ε₀, hy1G⟩
      rw [hcon, hA1] at h4
      exact h4.symm
    have h5 : c σ - ε₀ • u = c σ := by
      have hinj : Set.InjOn c.symm c.target := by
        have h := c.symm.injOn
        rwa [OpenPartialHomeomorph.symm_source] at h
      have h6 : c.symm (c σ - ε₀ • u) = c.symm (c σ) := by
        rw [h3, c.left_inv hσsrc]
      exact hinj (htgtm ε₀ hε₀.le le_rfl) (c.map_source hσsrc) h6
    have h7 : ε₀ • u = 0 := by
      have h8 : c σ - ε₀ • u - c σ = 0 := by rw [h5, sub_self]
      have h9 : c σ - ε₀ • u - c σ = -(ε₀ • u) := by abel
      rw [h9] at h8
      simpa using h8
    rcases smul_eq_zero.mp h7 with h | h
    · exact absurd h (ne_of_gt hε₀)
    · exact hu h
  have htail : ∀ t : ℝ, ((τ ⟨ε₀, hy1G⟩ : I) : ℝ) ≤ t → t ≤ 1 →
      A t ∈ (fun y : ℝ => c.symm (c σ - y • u)) '' G := by
    intro t ht1 ht2
    have hmem1 : ((τ ⟨ε₀, hy1G⟩ : I) : ℝ) ∈ T := ⟨⟨ε₀, hy1G⟩, rfl⟩
    have hmem2 : (1:ℝ) ∈ T := ⟨⟨0, hy0G⟩, hτ0⟩
    have ht : t ∈ T := (hord.out hmem1 hmem2) ⟨ht1, ht2⟩
    obtain ⟨y, hy⟩ := ht
    refine ⟨y.1, y.2, ?_⟩
    have h5 : c.symm (c σ - y.1 • u) = A t := by
      rw [← hAval y]
      rw [hy]
    exact h5
  have hK₀c : IsCompact (A '' (I ∩ Set.Iic ((τ ⟨ε₀, hy1G⟩ : I) : ℝ))) :=
    (isCompact_Icc.inter_right isClosed_Iic).image hAc
  have hσK₀ : σ ∉ A '' (I ∩ Set.Iic ((τ ⟨ε₀, hy1G⟩ : I) : ℝ)) := by
    rintro ⟨t, ht, hat⟩
    have ht1 : t = 1 := hAinj ht.1 ⟨by norm_num, le_rfl⟩ (by rw [hat, hA1])
    have h2 : t ≤ ((τ ⟨ε₀, hy1G⟩ : I) : ℝ) := ht.2
    rw [ht1] at h2
    linarith [hτ1lt]
  have hK₀o : IsOpen (A '' (I ∩ Set.Iic ((τ ⟨ε₀, hy1G⟩ : I) : ℝ)))ᶜ :=
    hK₀c.isClosed.isOpen_compl
  obtain ⟨ρ, hρpos, hρsub⟩ :=
    exists_chartBall_subset_given (n := n) hσsrc hK₀o hσK₀
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine ⟨min ε₁ (ρ / (2 * ‖u‖)), ?_, ?_, ?_⟩
  · exact lt_min hε₁ (by positivity)
  · exact (min_le_left _ _).trans le_rfl
  · intro s hs hδ hmem
    obtain ⟨t, ht, hAt⟩ := hmem
    have hballmem : c.symm (c σ + s • u) ∈ c.symm '' Metric.ball (c σ) ρ := by
      refine ⟨c σ + s • u, ?_, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs]
      have h2 : s ≤ ρ / (2 * ‖u‖) := hδ.trans (min_le_right _ _)
      have h3 : s * ‖u‖ ≤ (ρ / (2 * ‖u‖)) * ‖u‖ := mul_le_mul_of_nonneg_right h2 hun.le
      have h4 : (ρ / (2 * ‖u‖)) * ‖u‖ = ρ / 2 := by field_simp
      linarith
    have hnotK₀ : c.symm (c σ + s • u) ∉ A '' (I ∩ Set.Iic ((τ ⟨ε₀, hy1G⟩ : I) : ℝ)) :=
      fun hx => hρsub hballmem hx
    have ht_gt : ((τ ⟨ε₀, hy1G⟩ : I) : ℝ) < t := by
      by_contra hcon
      exact hnotK₀ ⟨t, ⟨ht, le_of_not_gt hcon⟩, hAt⟩
    obtain ⟨y, hyG, hyeq⟩ := htail t (by linarith) ht.2
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h1 : c σ + s • u = c σ - y • u := by
      refine hinj ?_ ?_ ?_
      · exact htgtp s hs (hδ.trans (min_le_left _ _ |>.trans le_rfl))
      · exact htgtm y hyG.1 hyG.2
      · rw [← hAt, ← hyeq]
    have h2 : (s + y) • u = 0 := by
      have h3 : s • u + y • u = 0 := by
        have h4 : s • u = -(y • u) := by
          rw [sub_eq_add_neg] at h1
          exact add_left_cancel h1
        rw [h4]; abel
      rw [add_smul]; exact h3
    have h4 : s + y = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hu
    linarith [h4, hs, hyG.1]

/-- **The seed arc of the stage**: the straight germ ray, reparametrised so that its parameter stays
below the prescribed bound `b`.  The resulting arc has the prescribed germ `t ↦ c.symm (c σ + t • v)`
on `[0,e]`, stays inside `C`, and its part beyond `e` avoids the closed set `B` — this needs only that
the *spike line* is in `C` (resp. off `B`) below `eps`, with `(L+1) * b < eps` and `(L+1) * b ≤ L`. -/
theorem exists_chartSeed {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {σ : M} (hσsrc : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0)
    {L eps e b : ℝ} (hL : 0 < L) (heps : 0 < eps)
    (he : 0 < e) (he1 : e < 1) (heb : e < b) (hbeps : (L + 1) * b < eps)
    (hbL : (L + 1) * b ≤ L)
    (htgt : ∀ s : ℝ, |s| ≤ L + 3 → c σ + s • u ∈ c.target)
    {C B : Set M}
    (hC : ∀ s : ℝ, 0 ≤ s → s ≤ L → c.symm (c σ + s • u) ∈ C)
    (hB : ∀ s : ℝ, 0 < s → s < eps → c.symm (c σ + s • u) ∉ B) :
    ∃ (φ : ℝ → ℝ) (A : ℝ → M), StrictMono φ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder A ∧ A 0 = σ ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) A t)) ∧
      Set.InjOn A (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, A t = c.symm (c σ + φ t • ((L + 1) • u))) ∧
      (∀ t : ℝ, c σ + φ t • ((L + 1) • u) ∈ c.target) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → A t ∈ C) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → A t = c.symm (c σ + t • ((L + 1) • u))) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → A t ∉ B) ∧ A 1 ∈ C ∧ A 1 ∉ B := by
  classical
  have hLp : (0:ℝ) < L + 1 := by linarith
  set v : EuclideanSpace ℝ (Fin n) := (L + 1) • u with hvdef
  have hv : v ≠ 0 := by
    rw [hvdef]
    intro h0
    rcases smul_eq_zero.mp h0 with h | h
    · linarith
    · exact hu h
  set a₀ : ℝ := -(L + 3) / (L + 1) with hadef
  have ha₀ : a₀ < 0 := by
    rw [hadef, neg_div, neg_lt_zero]; positivity
  obtain ⟨φ, hφcd, hφpos, hφid, hφrange, hφ1, -⟩ :=
    Work.Noncompact.CompressionTube.exists_smooth_reparam_gen a₀ b e 1 ha₀ he he1 le_rfl heb
  have hφmono : StrictMono φ := strictMono_of_deriv_pos hφpos
  have hφ0 : φ 0 = 0 := hφid 0 ⟨le_refl 0, he.le⟩
  have hφe : φ e = e := hφid e ⟨he.le, le_refl e⟩
  have hline : ∀ x ∈ Set.Ioo a₀ b, c σ + x • v ∈ c.target := by
    intro x hx
    have h1 : c σ + x • v = c σ + (x * (L + 1)) • u := by rw [hvdef, smul_smul]
    rw [h1]
    refine htgt (x * (L + 1)) ?_
    rw [abs_le]
    have hxb : x < b := hx.2
    have hxa : a₀ < x := hx.1
    rw [hadef] at hxa
    have h2 : x * (L + 1) < b * (L + 1) := by nlinarith [hxb, hLp]
    have h4 : (-(L + 3) / (L + 1)) * (L + 1) = -(L + 3) := by field_simp
    have h3 : -(L + 3) < x * (L + 1) := by nlinarith [hxa, hLp, h4]
    have h5 : b * (L + 1) < eps := by nlinarith [hbeps]
    constructor <;> linarith
  obtain ⟨hAsm, hAimm⟩ :=
    Work.Routing.reparamChartLine_contMDiff_immersion (n := n) (M := M) hc hσsrc hv hφcd hφpos
      hφrange hline
  have hrew : ∀ t : ℝ, c σ + φ t • v = c σ + ((φ t) * (L + 1)) • u :=
    fun t => by rw [hvdef, smul_smul]
  have hmain : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → c.symm (c σ + φ t • v) ∈ C := by
    intro t ht
    have hφt0 : 0 ≤ φ t := by
      have h := hφmono.monotone ht.1; rwa [hφ0] at h
    have hφtb : φ t < b := lt_of_le_of_lt (hφmono.monotone ht.2) hφ1.2
    rw [hrew t]
    exact hC _ (by nlinarith [hφt0, hLp]) (by nlinarith [hφtb, hbL])
  have hout : ∀ t : ℝ, e < t → t ≤ 1 → c.symm (c σ + φ t • v) ∉ B := by
    intro t het ht1
    rw [hrew t]
    refine hB _ ?_ ?_
    · have h2 : φ e < φ t := hφmono het
      rw [hφe] at h2
      nlinarith [h2, hLp]
    · have h2 : φ t < b := lt_of_le_of_lt (hφmono.monotone ht1) hφ1.2
      nlinarith [h2, hbeps]
  have hshape : ∀ t : ℝ, c.symm (c σ + φ t • v) = c.symm (c σ + φ t • ((L + 1) • u)) :=
    fun t => by rw [hvdef]
  have htgt' : ∀ t : ℝ, c σ + φ t • ((L + 1) • u) ∈ c.target :=
    fun t => hline (φ t) (hφrange ⟨t, rfl⟩)
  have hinjOn : Set.InjOn (fun t : ℝ => c.symm (c σ + φ t • v)) (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h1 : c σ + φ s • v = c σ + φ t • v :=
      hinj (hline _ (hφrange ⟨s, rfl⟩)) (hline _ (hφrange ⟨t, rfl⟩)) hst
    have h3 : (φ s - φ t) • v = 0 := by rw [sub_smul, add_left_cancel h1, sub_self]
    have h2 : φ s = φ t := by
      rcases smul_eq_zero.mp h3 with h | h
      · linarith
      · exact absurd h hv
    exact hφmono.injective h2
  have hgerm' : ∀ t : ℝ, 0 ≤ t → t ≤ e →
      c.symm (c σ + φ t • v) = c.symm (c σ + t • ((L + 1) • u)) := by
    intro t ht0 hte
    rw [hφid t ⟨ht0, hte⟩]
  refine ⟨φ, fun t : ℝ => c.symm (c σ + φ t • v), hφmono, hφcd, hAsm, ?_, hAimm, hinjOn,
    hshape, htgt', hmain, hgerm', hout, ?_, ?_⟩
  · show c.symm (c σ + φ 0 • v) = σ
    rw [hφ0, zero_smul, add_zero, c.left_inv hσsrc]
  · exact hmain 1 ⟨by norm_num, le_rfl⟩
  · exact hout 1 he1 le_rfl

end Work.Drive.TwoRays

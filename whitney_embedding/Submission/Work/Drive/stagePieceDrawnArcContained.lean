import Mathlib
import Submission.Work.Drive.TwoRays.stageTools
import Submission.Work.Routing.rootedArcAvoidHalfOpen
import Submission.Work.Noncompact.CompressionTube.immersedLine
import Submission.Work.Noncompact.Routing.arcs_removal

/-!
# The stage piece drawn on a contained arc

`Work.Drive.stagePieceDrawnArcContained` is the stage engine of the recursion: given the arriving
piece `P` (ending at `σ` with a prescribed straight germ in a chart `c`), an open preconnected
region `C`, a drawn arc `A ⊆ C` that already contains the trace `P '' Icc 0 1 ∩ C`, and a target
point `q ∈ C` off `A` and off the spike, it produces a new smooth immersed piece `Q` from `σ` to
`q`, inside `C`, whose initial germ is the straight segment `t ↦ c.symm (c σ + t • ((L+1) • u))`,
which meets `P` and `A` only at `σ`.

Compared with `Work.Drive.TwoRays.stagePieceOfDrawnArc`, this statement **drops** its two unused
hypotheses (`hProot`, the rootedness of `P` at `σ` for the radius `ρ`, and the stray `hAspike`) and
**adds** the conclusion row `∀ t ∈ Icc 0 1, Q t ∈ C` (the engine already returns it).  Neither
dropped hypothesis is needed by the argument -- the germ extent `eg` is cut out of the *open* region
`C` and the arc `A`, not out of a ball of radius `ρ` -- so the proof below is that theorem's proof
verbatim, transplanted into this statement (same hypothesis names, same conclusion, plus the
containment row, which is `hQimg` there).
-/

namespace Work.Drive

set_option maxHeartbeats 4000000

theorem stagePieceDrawnArcContained {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {P : ℝ → M} {σ : M}
    (hPsm : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder P)
    (hPinj : Set.InjOn P (Set.Icc (0:ℝ) 1)) (hP1 : P 1 = σ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M) (hσsrc : σ ∈ c.source)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hPgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm (c σ + (t - 1) • u))
    (hPtgt : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → c σ + (t - 1) • u ∈ c.target)
    {ρ : ℝ} (hρ : 0 < ρ)
    {C : Set M} (hCo : IsOpen C) (hCpc : IsPreconnected C)
    {A : ℝ → M} (hAc : Continuous A) (hAinj : Set.InjOn A (Set.Icc (0:ℝ) 1))
    (hAC : A '' Set.Icc (0:ℝ) 1 ⊆ C) (hA1 : A 1 = σ)
    (hPA : P '' Set.Icc (0:ℝ) 1 ∩ C ⊆ A '' Set.Icc (0:ℝ) 1)
    {L : ℝ} (hL : 0 < L) (hLρ : L * ‖u‖ < ρ)
    (hspikeC : ∀ s : ℝ, 0 ≤ s → s ≤ L → c.symm (c σ + s • u) ∈ C)
    (hspike_tgt : ∀ s : ℝ, |s| ≤ L + 3 → c σ + s • u ∈ c.target)
    {q : M} (hqC : q ∈ C) (hqA : q ∉ A '' Set.Icc (0:ℝ) 1)
    (hqspike : q ∉ (fun s : ℝ => c.symm (c σ + s • u)) '' Set.Icc (0:ℝ) L)
    (hpq : q ≠ c.symm (c σ + L • u)) :
    ∃ (Q : ℝ → M) (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (eout ρout : ℝ),
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder Q ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Function.Injective
        (mfderiv Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n) Q t)) ∧
      Set.InjOn Q (Set.Icc (0:ℝ) 1) ∧
      Q 0 = σ ∧ Q 1 = q ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q t ∈ C) ∧
      (∃ eg : ℝ, 0 < eg ∧ ∀ t : ℝ, 0 ≤ t → t ≤ eg →
        Q t = c.symm (c σ + t • ((L + 1) • u))) ∧
      0 < eout ∧ eout ≤ 1 ∧ w ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder M ∧ q ∈ c'.source ∧
      (∀ t : ℝ, 1 - eout ≤ t → t ≤ 1 → Q t = c'.symm (c' q + (t - 1) • w)) ∧
      0 < ρout ∧ (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        Q t ∈ c'.symm '' Metric.ball (c' q) ρout → t ∈ Set.Icc (1 - eout) 1) ∧
      P '' Set.Icc (0:ℝ) 1 ∩ Q '' Set.Icc (0:ℝ) 1 ⊆ {σ} ∧
      Q '' Set.Icc (0:ℝ) 1 ∩ A '' Set.Icc (0:ℝ) 1 ⊆ {σ} := by
  classical
  have hLp : (0:ℝ) < L + 1 := by linarith
  set v : EuclideanSpace ℝ (Fin n) := (L + 1) • u with hvdef
  have hv : v ≠ 0 := by
    rw [hvdef]
    intro h0
    rcases smul_eq_zero.mp h0 with h | h
    · linarith
    · exact hu h
  have hσC : σ ∈ C := by
    have h : c.symm (c σ + (0:ℝ) • u) ∈ C := hspikeC 0 le_rfl hL.le
    rwa [zero_smul, add_zero, c.left_inv hσsrc] at h
  obtain ⟨ρC, hρC, hρCsub⟩ :=
    Work.Drive.TwoRays.exists_chartBall_subset_given (n := n) hσsrc hCo hσC
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  -- ## the negative germ segment lies on the drawn arc
  set ε₀ : ℝ := min e (ρC / (2 * ‖u‖)) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min he (by positivity)
  have hε₀e : ε₀ ≤ e := min_le_left _ _
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ ε₀ → c.symm (c σ - s • u) ∈ A '' Set.Icc (0:ℝ) 1 := by
    intro s hs0 hsε
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h
      simp only [zero_smul, sub_zero]
      exact ⟨1, ⟨by norm_num, le_rfl⟩, hA1.trans (c.left_inv hσsrc).symm⟩
    · have hmem : c.symm (c σ - s • u) ∈ C := by
        refine hρCsub ⟨c σ - s • u, ?_, rfl⟩
        rw [Metric.mem_ball, dist_eq_norm, show c σ - s • u - c σ = -(s • u) from by abel,
          norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos h]
        have h2 : s ≤ ρC / (2 * ‖u‖) := hsε.trans (min_le_right _ _)
        have h3 : s * ‖u‖ ≤ (ρC / (2 * ‖u‖)) * ‖u‖ := mul_le_mul_of_nonneg_right h2 hun.le
        have h4 : (ρC / (2 * ‖u‖)) * ‖u‖ = ρC / 2 := by field_simp
        linarith
      have htime : (1:ℝ) - s ∈ Set.Icc (0:ℝ) 1 := by
        constructor <;> linarith [hε₀e, he, he1, hs0]
      have hPg : P (1 - s) = c.symm (c σ - s • u) := by
        have h := hPgerm (1 - s) (by linarith [hsε, hε₀e]) (by linarith [hs0])
        rw [h]
        rw [show (1:ℝ) - s - 1 = -s from by ring, neg_smul, sub_eq_add_neg]
      exact hPA ⟨⟨1 - s, htime, hPg⟩, hmem⟩
  have htgtm : ∀ s : ℝ, 0 ≤ s → s ≤ ε₀ → c σ - s • u ∈ c.target := by
    intro s hs0 hsε
    have h := hPtgt (1 - s) (by linarith [hsε, hε₀e]) (by linarith [hs0])
    rw [show (1:ℝ) - s - 1 = -s from by ring, neg_smul] at h
    exact h
  have htgtp : ∀ s : ℝ, 0 < s → s ≤ L + 3 → c σ + s • u ∈ c.target :=
    fun s hs hs' => hspike_tgt s (by rw [abs_of_pos hs]; linarith)
  obtain ⟨δ, hδpos, hδle, hδgap⟩ :=
    Work.Drive.TwoRays.arc_gap_of_negative_segment (n := n) (M := M) hσsrc hu hAc hAinj hA1
      hε₀ (by linarith) hseg htgtm htgtp
  -- ## the germ extent of the new piece and the seed parameter bound
  set gm : ℝ := min δ L with hgmdef
  have hgmpos : 0 < gm := lt_min hδpos hL
  have hgmδ : gm ≤ δ := min_le_left δ L
  have hgmL : gm ≤ L := min_le_right δ L
  set eg : ℝ := min (1/2) (gm / (4 * (L + 1))) with hegdef
  have heg : 0 < eg := lt_min (by norm_num) (by positivity)
  have heg1 : eg < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have heggm : (L + 1) * eg < gm := by
    have h2 : eg ≤ gm / (4 * (L + 1)) := min_le_right _ _
    have h3 : (L + 1) * eg ≤ (L + 1) * (gm / (4 * (L + 1))) :=
      mul_le_mul_of_nonneg_left h2 hLp.le
    have h4 : (L + 1) * (gm / (4 * (L + 1))) = gm / 4 := by field_simp
    nlinarith [h3, h4, hgmpos]
  have hegδ : (L + 1) * eg < δ := lt_of_lt_of_le heggm hgmδ
  have hegL : (L + 1) * eg ≤ L := le_of_lt (lt_of_lt_of_le heggm hgmL)
  set bb : ℝ := gm / (2 * (L + 1)) with hbbdef
  have hbbpos : 0 < bb := by rw [hbbdef]; positivity
  have hegb : eg < bb := by
    have h2 : eg ≤ gm / (4 * (L + 1)) := min_le_right _ _
    have h3 : gm / (4 * (L + 1)) < gm / (2 * (L + 1)) := by
      rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 4 * (L + 1))
        (by linarith : (0:ℝ) < 2 * (L + 1))]
      nlinarith [hgmpos, hLp]
    exact lt_of_le_of_lt h2 h3
  have hbbδ : (L + 1) * bb < δ := by
    have h2 : (L + 1) * bb = gm / 2 := by rw [hbbdef]; field_simp
    nlinarith [h2, hgmδ, hgmpos]
  have hbbL : (L + 1) * bb ≤ L := by
    have h2 : (L + 1) * bb = gm / 2 := by rw [hbbdef]; field_simp
    nlinarith [h2, hgmL, hgmpos]
  -- ## the seed arc
  obtain ⟨φ, Aseed, hφmono, hφcd, hSsm, hS0, hSimm, hSinj, hSshape, hStgt, hSimg, hSgerm, hSav,
    hS1C, hS1B⟩ :=
    Work.Drive.TwoRays.exists_chartSeed (n := n) (M := M) (eps := δ) hc hσsrc hu hL hδpos heg
      heg1 hegb hbbδ hbbL hspike_tgt hspikeC (fun s hs hslt => hδgap s hs hslt.le)
  -- ## the germ segment of the new piece
  set Gset : Set M := c.symm '' ((fun t : ℝ => c σ + t • v) '' Set.Icc (0:ℝ) eg) with hGdef
  have hgermtgt : ∀ t : ℝ, 0 ≤ t → t ≤ eg → c σ + t • v ∈ c.target := by
    intro t ht0 hte
    have h1 : c σ + t • v = c σ + (t * (L + 1)) • u := by rw [hvdef, smul_smul]
    rw [h1]
    refine hspike_tgt (t * (L + 1)) ?_
    rw [abs_le]
    constructor <;> nlinarith [ht0, hte, hegL, hLp]
  have hgermC : ∀ t : ℝ, 0 ≤ t → t ≤ eg → c.symm (c σ + t • v) ∈ C := by
    intro t ht0 hte
    have h1 : c σ + t • v = c σ + (t * (L + 1)) • u := by rw [hvdef, smul_smul]
    rw [h1]
    exact hspikeC _ (by positivity) (by nlinarith [hte, hegL])
  have hφeg : φ eg = eg := by
    have h1 : c.symm (c σ + φ eg • v) = c.symm (c σ + eg • v) := by
      rw [← hSshape eg, hSgerm eg heg.le le_rfl]
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have hStgt' : c σ + φ eg • v ∈ c.target := by
      simpa only [hvdef] using hStgt eg
    have h2 : φ eg • v = eg • v :=
      add_left_cancel (hinj hStgt' (hgermtgt eg heg.le le_rfl) h1)
    have h3 : (φ eg - eg) • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · linarith
    · exact absurd h hv
  have hseed_G : ∀ t : ℝ, eg < t → t ≤ 1 → Aseed t ∉ Gset := by
    intro t het ht1 hmem
    obtain ⟨y, ⟨s, hs, hys⟩, hyx⟩ := hmem
    have hkey : c.symm (c σ + φ t • v) = c.symm (c σ + s • v) := by
      have h1 : Aseed t = c.symm (c σ + s • v) := by
        rw [← hyx, ← hys]
      have h2 : c.symm (c σ + φ t • v) = Aseed t := by
        simpa only [hvdef] using (hSshape t).symm
      rw [h2, h1]
    exfalso
    have hStgt' : c σ + φ t • v ∈ c.target := by
      simpa only [hvdef] using hStgt t
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h1 : φ t • v = s • v :=
      add_left_cancel (hinj hStgt' (hgermtgt s hs.1 hs.2) hkey)
    have h2 : φ t = s := by
      have h3 : (φ t - s) • v = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · linarith
      · exact absurd h hv
    have h4 : φ eg < φ t := hφmono het
    rw [hφeg] at h4
    linarith [h2, h4, hs.2]
  -- ## the region
  set Sset : Set M := A '' Set.Icc (0:ℝ) 1 ∪ Gset with hSdef
  set Uset : Set M := C \ Sset with hUdef
  have hAcl : IsClosed (A '' Set.Icc (0:ℝ) 1) := (isCompact_Icc.image hAc).isClosed
  have hGcl : IsClosed Gset := by
    have hY : IsCompact ((fun t : ℝ => c σ + t • v) '' Set.Icc (0:ℝ) eg) :=
      isCompact_Icc.image (by fun_prop)
    have hYt : ((fun t : ℝ => c σ + t • v) '' Set.Icc (0:ℝ) eg) ⊆ c.target := by
      rintro y ⟨t, ht, rfl⟩
      exact hgermtgt t ht.1 ht.2
    have h2 := hY.image_of_continuousOn (f := fun y : EuclideanSpace ℝ (Fin n) => c.symm y)
      (c.continuousOn_symm.mono hYt)
    simpa only [hGdef, Set.image_image] using h2.isClosed
  have hScl : IsClosed Sset := by rw [hSdef]; exact hAcl.union hGcl
  have hUopen : IsOpen Uset := by rw [hUdef]; exact hCo.sdiff hScl
  -- the concatenation of the arc and the germ segment
  have hψmem : ∀ t : ℝ, eg * min 1 (max 0 (2 * t - 1)) ∈ Set.Icc (0:ℝ) eg := by
    intro t
    constructor
    · have h2 : 0 ≤ min 1 (max 0 (2 * t - 1)) := le_min zero_le_one (le_max_left _ _)
      positivity
    · have h2 : min 1 (max 0 (2 * t - 1)) ≤ 1 := min_le_left _ _
      nlinarith
  have hψeq : ∀ t : ℝ, (2:ℝ)⁻¹ ≤ t → t ≤ 1 →
      eg * min 1 (max 0 (2 * t - 1)) = eg * (2 * t - 1) := by
    intro t ht1 ht2
    have h3 : 0 ≤ 2 * t - 1 := by linarith
    have h4 : 2 * t - 1 ≤ 1 := by linarith
    rw [max_eq_right h3, min_eq_right h4]
  set γ : ℝ → M := fun t => if t ≤ (2:ℝ)⁻¹ then A (2 * t)
    else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v) with hγdef
  have hγev : ∀ t : ℝ, γ t = (if t ≤ (2:ℝ)⁻¹ then A (2 * t)
      else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v)) := fun t => rfl
  have hγcont2 : Continuous fun t : ℝ =>
      c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v) :=
    c.continuousOn_symm.comp_continuous (by fun_prop)
      (fun t => hgermtgt _ (hψmem t).1 (hψmem t).2)
  have hγc : Continuous γ := by
    rw [hγdef]
    refine Continuous.if_le (f := fun t : ℝ => t) (g := fun _ : ℝ => (2:ℝ)⁻¹)
      (hAc.comp (by fun_prop)) hγcont2 continuous_id continuous_const ?_
    intro x hx
    rw [hx]
    have h3 : min 1 (max 0 (2 * (2:ℝ)⁻¹ - 1)) = 0 := by norm_num
    have h4 : (2:ℝ) * (2:ℝ)⁻¹ = 1 := by norm_num
    rw [h3, h4]
    simp only [mul_zero, zero_smul, add_zero]
    exact hA1.trans (c.left_inv hσsrc).symm
  have hGset_mem : ∀ s : ℝ, 0 ≤ s → s ≤ eg → c.symm (c σ + s • v) ∈ Gset :=
    fun s h1 h2 => ⟨c σ + s • v, ⟨s, ⟨h1, h2⟩, rfl⟩, rfl⟩
  have hγimg : γ '' Set.Icc (0:ℝ) 1 = Sset := by
    rw [hSdef, hGdef]
    ext x; constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hγev t]
      by_cases hcase : t ≤ (2:ℝ)⁻¹
      · rw [if_pos hcase]
        exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith [hcase]⟩, rfl⟩
      · rw [if_neg hcase]
        exact Or.inr ⟨c σ + (eg * min 1 (max 0 (2 * t - 1))) • v,
          ⟨eg * min 1 (max 0 (2 * t - 1)), hψmem t, rfl⟩, rfl⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨y, ⟨s, hs, rfl⟩, rfl⟩)
      · refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
        rw [hγev (u / 2)]
        have hcase : u / 2 ≤ (2:ℝ)⁻¹ := by linarith [hu.2]
        rw [if_pos hcase]
        congr 1
        ring
      · rcases eq_or_lt_of_le hs.1 with h0 | h0
        · have h0' : c.symm (c σ + s • v) = σ := by
            subst h0
            simp only [zero_smul, add_zero]
            exact c.left_inv hσsrc
          refine ⟨(2:ℝ)⁻¹, ⟨by norm_num, by norm_num⟩, ?_⟩
          rw [h0', hγev ((2:ℝ)⁻¹), if_pos (le_refl _)]
          have h4 : (2:ℝ) * (2:ℝ)⁻¹ = 1 := by norm_num
          rw [h4]
          exact hA1
        · have hspos : 0 < s := h0
          refine ⟨(s / eg + 1) / 2, ⟨by positivity, ?_⟩, ?_⟩
          · have h2 : s / eg ≤ 1 := by rw [div_le_one heg]; exact hs.2
            linarith
          · have hhalf : (2:ℝ)⁻¹ < (s / eg + 1) / 2 := by
              have h2 : (0:ℝ) < s / eg := by positivity
              rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
              have h3 : (2:ℝ)⁻¹ * 2 = 1 := by norm_num
              rw [h3]
              linarith
            rw [hγev ((s / eg + 1) / 2), if_neg (not_le.mpr hhalf)]
            have harg : eg * min 1 (max 0 (2 * ((s / eg + 1) / 2) - 1)) = s := by
              have h1 : 2 * ((s / eg + 1) / 2) - 1 = s / eg := by ring
              have h2 : 0 ≤ s / eg := by positivity
              have h3 : s / eg ≤ 1 := by rw [div_le_one heg]; exact hs.2
              rw [h1, max_eq_right h2, min_eq_right h3]
              field_simp
            rw [harg]
  have hGA : Gset ∩ A '' Set.Icc (0:ℝ) 1 ⊆ {σ} := by
    rintro x ⟨hxG, hxA⟩
    obtain ⟨y, ⟨s, hs, hys⟩, hyx⟩ := hxG
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · have h1 : c.symm (c σ + s • v) = σ := by
        subst h0
        simp only [zero_smul, add_zero]
        exact c.left_inv hσsrc
      rw [← hyx, ← hys, h1]
      exact rfl
    · exfalso
      have h1 : s * (L + 1) ≤ δ := by
        have h2 : s * (L + 1) ≤ eg * (L + 1) := mul_le_mul_of_nonneg_right hs.2 hLp.le
        have h3 : eg * (L + 1) = (L + 1) * eg := by ring
        linarith [h2, h3, hegδ]
      have h4 := hδgap (s * (L + 1)) (by positivity) h1
      apply h4
      have harg : c σ + (s * (L + 1)) • u = c σ + s • v := by rw [hvdef, smul_smul]
      have hys' : c σ + s • v = y := by
        show (fun t : ℝ => c σ + t • v) s = y
        exact hys
      rw [harg, hys', hyx]
      exact hxA
  have hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hst' : (if s ≤ (2:ℝ)⁻¹ then A (2 * s)
        else c.symm (c σ + (eg * min 1 (max 0 (2 * s - 1))) • v))
        = (if t ≤ (2:ℝ)⁻¹ then A (2 * t)
        else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v)) := by
      rw [← hγev s, ← hγev t]
      exact hst
    by_cases hsc : s ≤ (2:ℝ)⁻¹
    · by_cases htc : t ≤ (2:ℝ)⁻¹
      · rw [if_pos hsc, if_pos htc] at hst'
        have h1 : 2 * s = 2 * t :=
          hAinj ⟨by linarith [hs.1], by linarith [hsc]⟩
            ⟨by linarith [ht.1], by linarith [htc]⟩ hst'
        linarith
      · have hxA : γ s ∈ A '' Set.Icc (0:ℝ) 1 := by
          refine ⟨2 * s, ⟨by linarith [hs.1], by linarith [hsc]⟩, ?_⟩
          change A (2 * s) = (if s ≤ (2:ℝ)⁻¹ then A (2 * s)
            else c.symm (c σ + (eg * min 1 (max 0 (2 * s - 1))) • v))
          rw [if_pos hsc]
        have hxG : γ t ∈ Gset := by
          change (if t ≤ (2:ℝ)⁻¹ then A (2 * t)
            else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v)) ∈ Gset
          rw [if_neg htc]
          exact hGset_mem _ (hψmem t).1 (hψmem t).2
        have h4 : A (2 * s) = γ s := by
          change A (2 * s) = (if s ≤ (2:ℝ)⁻¹ then A (2 * s)
            else c.symm (c σ + (eg * min 1 (max 0 (2 * s - 1))) • v))
          rw [if_pos hsc]
        have hσ : γ s = σ := by
          have hmem : γ s ∈ Gset := by rw [hst]; exact hxG
          exact hGA ⟨hmem, hxA⟩
        have h2 : 2 * s = 1 := by
          have h3 : A (2 * s) = A 1 := h4.trans (hσ.trans hA1.symm)
          exact hAinj ⟨by linarith [hs.1], by linarith [hsc]⟩ ⟨by norm_num, le_rfl⟩ h3
        rw [if_pos hsc, if_neg htc] at hst'
        have h5 : eg * min 1 (max 0 (2 * t - 1)) = 0 := by
          have hinj : Set.InjOn c.symm c.target := by
            have h := c.symm.injOn
            rwa [OpenPartialHomeomorph.symm_source] at h
          have h6 : c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v)
              = c.symm (c σ + (0:ℝ) • v) := by
            have h6a : c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v) = σ :=
              hst'.symm.trans (h4.trans hσ)
            rw [h6a]
            simp only [zero_smul, add_zero]
            exact (c.left_inv hσsrc).symm
          have h7 : (eg * min 1 (max 0 (2 * t - 1))) • v = (0:ℝ) • v :=
            add_left_cancel (hinj (hgermtgt _ (hψmem t).1 (hψmem t).2)
              (by simpa using c.map_source hσsrc) h6)
          have h8 : ((eg * min 1 (max 0 (2 * t - 1))) - 0) • v = 0 := by
            rw [sub_smul, h7, sub_self]
          rcases smul_eq_zero.mp h8 with h | h
          · linarith
          · exact absurd h hv
        rw [hψeq t (not_le.mp htc).le ht.2] at h5
        have h8 : 2 * t - 1 = 0 := by
          rcases mul_eq_zero.mp h5 with h | h
          · exact absurd h (ne_of_gt heg)
          · exact h
        linarith [h2, h8]
    · by_cases htc : t ≤ (2:ℝ)⁻¹
      · have hxA : γ t ∈ A '' Set.Icc (0:ℝ) 1 := by
          refine ⟨2 * t, ⟨by linarith [ht.1], by linarith [htc]⟩, ?_⟩
          change A (2 * t) = (if t ≤ (2:ℝ)⁻¹ then A (2 * t)
            else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v))
          rw [if_pos htc]
        have hxG : γ s ∈ Gset := by
          change (if s ≤ (2:ℝ)⁻¹ then A (2 * s)
            else c.symm (c σ + (eg * min 1 (max 0 (2 * s - 1))) • v)) ∈ Gset
          rw [if_neg hsc]
          exact hGset_mem _ (hψmem s).1 (hψmem s).2
        have hσ : γ t = σ := by
          have hmem : γ t ∈ Gset := by rw [← hst]; exact hxG
          exact hGA ⟨hmem, hxA⟩
        have h2 : 2 * t = 1 := by
          have h4 : A (2 * t) = γ t := by
            change A (2 * t) = (if t ≤ (2:ℝ)⁻¹ then A (2 * t)
              else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v))
            rw [if_pos htc]
          have h3 : A (2 * t) = A 1 := h4.trans (hσ.trans hA1.symm)
          exact hAinj ⟨by linarith [ht.1], by linarith [htc]⟩ ⟨by norm_num, le_rfl⟩ h3
        rw [if_neg hsc, if_pos htc] at hst'
        have h5 : eg * min 1 (max 0 (2 * s - 1)) = 0 := by
          have hinj : Set.InjOn c.symm c.target := by
            have h := c.symm.injOn
            rwa [OpenPartialHomeomorph.symm_source] at h
          have h4 : A (2 * t) = γ t := by
            change A (2 * t) = (if t ≤ (2:ℝ)⁻¹ then A (2 * t)
              else c.symm (c σ + (eg * min 1 (max 0 (2 * t - 1))) • v))
            rw [if_pos htc]
          have h6 : c.symm (c σ + (eg * min 1 (max 0 (2 * s - 1))) • v)
              = c.symm (c σ + (0:ℝ) • v) := by
            have h6a : c.symm (c σ + (eg * min 1 (max 0 (2 * s - 1))) • v) = σ :=
              hst'.trans (h4.trans hσ)
            rw [h6a]
            simp only [zero_smul, add_zero]
            exact (c.left_inv hσsrc).symm
          have h7 : (eg * min 1 (max 0 (2 * s - 1))) • v = (0:ℝ) • v :=
            add_left_cancel (hinj (hgermtgt _ (hψmem s).1 (hψmem s).2)
              (by simpa using c.map_source hσsrc) h6)
          have h8 : ((eg * min 1 (max 0 (2 * s - 1))) - 0) • v = 0 := by
            rw [sub_smul, h7, sub_self]
          rcases smul_eq_zero.mp h8 with h | h
          · linarith
          · exact absurd h hv
        rw [hψeq s (not_le.mp hsc).le hs.2] at h5
        have h8 : 2 * s - 1 = 0 := by
          rcases mul_eq_zero.mp h5 with h | h
          · exact absurd h (ne_of_gt heg)
          · exact h
        linarith [h2, h8]
      · rw [if_neg hsc, if_neg htc] at hst'
        have hinj : Set.InjOn c.symm c.target := by
          have h := c.symm.injOn
          rwa [OpenPartialHomeomorph.symm_source] at h
        have h1 : (eg * min 1 (max 0 (2 * s - 1))) • v = (eg * min 1 (max 0 (2 * t - 1))) • v :=
          add_left_cancel (hinj (hgermtgt _ (hψmem s).1 (hψmem s).2)
            (hgermtgt _ (hψmem t).1 (hψmem t).2) hst')
        have h2 : eg * min 1 (max 0 (2 * s - 1)) = eg * min 1 (max 0 (2 * t - 1)) := by
          have h3 : (eg * min 1 (max 0 (2 * s - 1)) - eg * min 1 (max 0 (2 * t - 1))) • v = 0 := by
            rw [sub_smul, h1, sub_self]
          rcases smul_eq_zero.mp h3 with h | h
          · linarith
          · exact absurd h hv
        rw [hψeq s (not_le.mp hsc).le hs.2, hψeq t (not_le.mp htc).le ht.2] at h2
        have h4 : 2 * s - 1 = 2 * t - 1 := by
          rcases mul_eq_zero.mp (by linarith [h2] : eg * ((2 * s - 1) - (2 * t - 1)) = 0) with h | h
          · exact absurd h (ne_of_gt heg)
          · linarith
        linarith
  have hγC : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ C := by
    intro t ht
    rw [hγev t]
    by_cases hcase : t ≤ (2:ℝ)⁻¹
    · rw [if_pos hcase]
      exact hAC ⟨2 * t, ⟨by linarith [ht.1], by linarith [hcase]⟩, rfl⟩
    · rw [if_neg hcase]
      exact hgermC _ (hψmem t).1 (hψmem t).2
  have hUpc : IsPreconnected Uset := by
    rw [hUdef, ← hγimg]
    exact Work.Noncompact.Routing.isPreconnected_sdiff_image_arc hn hCo hCpc hγc hγinj hγC
  -- ## the reachability
  have hUW : C \ Sset ⊆ Uset := by rw [hUdef]
  have hUsub : Uset ⊆ C := by rw [hUdef]; exact Set.sdiff_subset
  have hSUdisj : Disjoint Sset Uset := by
    rw [Set.disjoint_left]
    intro x hxS hxU
    rw [hUdef] at hxU
    exact hxU.2 hxS
  have hUdisj : Disjoint Uset (c.symm '' ((fun t : ℝ => c σ + t • v) '' Set.Icc (0:ℝ) eg)) := by
    rw [Set.disjoint_left]
    intro x hxU hxG
    rw [hUdef] at hxU
    exact hxU.2 (Or.inr hxG)
  have hAavoid : ∀ t : ℝ, eg < t → t ≤ 1 → Aseed t ∉ Sset := by
    intro t het ht1
    rw [hSdef]
    intro hx
    rcases hx with h | h
    · exact hSav t het ht1 h
    · exact hseed_G t het ht1 h
  have hqS : q ∉ Sset := by
    rw [hSdef]
    intro hx
    rcases hx with h | h
    · exact hqA h
    · obtain ⟨y, ⟨s, hs, hys⟩, hyx⟩ := h
      apply hqspike
      refine ⟨s * (L + 1), ⟨by nlinarith [hs.1, hLp], by nlinarith [hs.2, hegL]⟩, ?_⟩
      rw [← hyx, ← hys]
      show c.symm (c σ + (s * (L + 1)) • u) = c.symm (c σ + s • ((L + 1) • u))
      rw [smul_smul]
  obtain ⟨Q, hQ0, hQ1, hQsm, hQimm, hQinj, hQimg, hQgerm, hQav, c', w, e', he'pos, hwne, hc'max,
    hqsrc, hQterm⟩ :=
    Work.Routing.rootedArcAvoidHalfOpen (n := n) (M := M) (W := C) (U := Uset) (S := Sset)
      (c := c) (p := σ) (q := q) (v := v) (e := eg) (A := Aseed)
      hn hCo hUopen hUpc hScl hUW hUsub hSUdisj hc hσsrc hv heg hgermC hUdisj heg1
      hSsm hS0 hSgerm hSimg hSimm hSinj hAavoid hqC hqS
  -- ## the conclusion
  have heout : 0 < min e' 1 := lt_min he'pos (by norm_num)
  have heout1 : min e' 1 ≤ 1 := min_le_right _ _
  have hQterm' : ∀ t : ℝ, 1 - min e' 1 ≤ t → t ≤ 1 →
      Q t = c'.symm (c' q + (t - 1) • w) := by
    intro t ht1 ht2
    exact hQterm t (by linarith [min_le_left e' 1]) ht2
  obtain ⟨ρout, hρout, -, hρoutrow⟩ :=
    Work.Noncompact.CompressionTube.exists_trace_ball (n := n) (M := M) (c := c') (P := Q)
      hQsm.continuous hQinj hQ1 hqsrc heout heout1 hQterm' (C := Set.univ) isOpen_univ trivial
  have hMeet2 : Q '' Set.Icc (0:ℝ) 1 ∩ A '' Set.Icc (0:ℝ) 1 ⊆ {σ} := by
    rintro x ⟨⟨t, ht, rfl⟩, hxA⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hQ0]
      exact rfl
    · by_cases hte : t ≤ eg
      · exfalso
        have h1 : c.symm (c σ + (t * (L + 1)) • u) ∉ A '' Set.Icc (0:ℝ) 1 := by
          refine hδgap _ (by positivity) ?_
          have h2 : t * (L + 1) ≤ eg * (L + 1) := mul_le_mul_of_nonneg_right hte hLp.le
          have h3 : eg * (L + 1) = (L + 1) * eg := by ring
          linarith [h2, h3, hegδ]
        apply h1
        have h4 : c.symm (c σ + t • v) = c.symm (c σ + (t * (L + 1)) • u) := by
          rw [hvdef, smul_smul]
        rw [← h4, ← hQgerm t ht.1 hte]
        exact hxA
      · refine absurd ?_ (hQav t (lt_of_not_ge hte) ht.2)
        rw [hSdef]
        exact Or.inl hxA
  have hMeet1 : P '' Set.Icc (0:ℝ) 1 ∩ Q '' Set.Icc (0:ℝ) 1 ⊆ {σ} := by
    rintro x ⟨hxP, hxQ⟩
    obtain ⟨t, ht, rfl⟩ := hxQ
    exact hMeet2 ⟨⟨t, ht, rfl⟩, hPA ⟨hxP, hQimg t ht⟩⟩
  refine ⟨Q, c', w, min e' 1, ρout, hQsm, ?_, hQinj, hQ0, hQ1, hQimg, ⟨eg, heg, ?_⟩, heout, heout1,
    hwne, hc'max, hqsrc, hQterm', hρout, hρoutrow, hMeet1, hMeet2⟩
  · exact fun t _ => hQimm t
  · exact fun t ht0 hte => by simpa only [hvdef] using hQgerm t ht0 hte

end Work.Drive

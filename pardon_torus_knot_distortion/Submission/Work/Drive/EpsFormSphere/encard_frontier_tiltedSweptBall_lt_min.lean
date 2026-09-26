import Mathlib
import Submission.Work.Drive.EpsFormSphere.encard_frontier_inter_lt_min
import Submission.Work.Drive.EpsForm.sweepThrough

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- **The frontier of the closed tilted slab** lies on its two faces `|⟪v,·⟫ - a| = h`. -/
theorem frontier_tiltedSlabClosed_subset (a : ℝ) (v : R3) (h : ℝ) :
    frontier (Work.Drive.EpsForm.tiltedSlabClosed a v h) ⊆
      {y : R3 | |inner ℝ v y - a| = h} := by
  intro x hx
  rw [frontier, Set.mem_sdiff] at hx
  obtain ⟨hxcl, hxint⟩ := hx
  have hcl : x ∈ Work.Drive.EpsForm.tiltedSlabClosed a v h := by
    have := hxcl
    rwa [(Work.Drive.EpsForm.isClosed_tiltedSlabClosed a v h).closure_eq] at this
  have hle : |inner ℝ v x - a| ≤ h := by
    simpa [Work.Drive.EpsForm.tiltedSlabClosed] using hcl
  have hnot : ¬ |inner ℝ v x - a| < h := by
    intro hlt
    have hopen : IsOpen {y : R3 | |inner ℝ v y - a| < h} :=
      isOpen_lt (by fun_prop) continuous_const
    have hsub : {y : R3 | |inner ℝ v y - a| < h} ⊆
        Work.Drive.EpsForm.tiltedSlabClosed a v h := fun y hy => by
      show |inner ℝ v y - a| ≤ h
      exact le_of_lt hy
    exact hxint (interior_maximal hsub hopen hlt)
  exact le_antisymm hle (not_lt.mp hnot)

/-- **The frontier of the removed region of the tilted sweep** lies on the two faces of the tilted
slab or on the wall `{ℓ = lam}` inside the slab. -/
theorem frontier_tiltedSlab_wall_subset (a lam : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) :
    frontier (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam}) ⊆
      {y : R3 | |inner ℝ v y - a| = h} ∪ {y : R3 | |inner ℝ v y - a| < h ∧ ℓ y = lam} := by
  intro x hx
  have hfr := frontier_inter_subset (Work.Drive.EpsForm.tiltedSlabClosed a v h)
    {y : R3 | ℓ y < lam} hx
  rw [frontier, Set.mem_sdiff] at hx
  obtain ⟨hxcl, hxint⟩ := hx
  rcases hfr with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Or.inl (frontier_tiltedSlabClosed_subset a v h h1)
  · have hle_face : |inner ℝ v x - a| ≤ h := by
      have hclA : x ∈ closure (Work.Drive.EpsForm.tiltedSlabClosed a v h) :=
        closure_mono Set.inter_subset_left hxcl
      have := hclA
      rwa [(Work.Drive.EpsForm.isClosed_tiltedSlabClosed a v h).closure_eq] at this
    by_cases habs : |inner ℝ v x - a| = h
    · exact Or.inl habs
    · have hlt : |inner ℝ v x - a| < h := lt_of_le_of_ne hle_face habs
      have hle : ℓ x ≤ lam := by
        refine closure_minimal ?_ (isClosed_le ℓ.continuous continuous_const)
          (closure_mono Set.inter_subset_right hxcl)
        intro y hy; exact le_of_lt (show ℓ y < lam from hy)
      have hge : lam ≤ ℓ x := by
        by_contra hcon
        have hlt2 : ℓ x < lam := not_le.mp hcon
        have hopen' : IsOpen ({y : R3 | |inner ℝ v y - a| < h} ∩ {y : R3 | ℓ y < lam}) :=
          (isOpen_lt (by fun_prop) continuous_const).inter
            (isOpen_lt ℓ.continuous continuous_const)
        have hsub : ({y : R3 | |inner ℝ v y - a| < h} ∩ {y : R3 | ℓ y < lam}) ⊆
            Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam} :=
          fun y hy => ⟨show |inner ℝ v y - a| ≤ h from
            le_of_lt (show |inner ℝ v y - a| < h from hy.1), hy.2⟩
        exact hxint (interior_maximal hsub hopen' ⟨hlt, hlt2⟩)
      exact Or.inr ⟨hlt, le_antisymm hle hge⟩

/-- **The frontier of the tilted swept ball** lies on the box sphere, on the tilted slab faces, or on
the wall `{ℓ = lam}`. -/
theorem frontier_tiltedSwept_subset (s a h lam : ℝ) (c v : R3) (σ : Equiv.Perm (Fin 3))
    (ℓ : R3 →L[ℝ] ℝ) :
    frontier (Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam})) ⊆
      frontier (Submission.PBox s c σ) ∪
        ({y : R3 | |inner ℝ v y - a| = h} ∪ {y : R3 | |inner ℝ v y - a| < h ∧ ℓ y = lam}) := by
  refine subset_trans (frontier_sdiff_subset (Submission.PBox s c σ) _) ?_
  intro y hy
  rcases hy with hy | hy
  · exact Or.inl hy
  · exact Or.inr (frontier_tiltedSlab_wall_subset a lam v h ℓ hy)

/-- A frontier point of a difference `A \ B` lies on the frontier of `A` or inside `A`. -/
theorem frontier_sdiff_subset_frontier_union {X : Type*} [TopologicalSpace X] (A B : Set X) :
    frontier (A \ B) ⊆ frontier A ∪ A := by
  intro x hx
  rw [frontier, Set.mem_sdiff] at hx
  obtain ⟨hxcl, hxint⟩ := hx
  rcases em (x ∈ A) with hxA | hxA
  · exact Or.inr hxA
  · exact Or.inl ⟨closure_mono sdiff_subset hxcl, fun h => hxA (interior_subset h)⟩

/-- A `C¹` function with nonzero derivative at `t` takes values strictly below, and strictly above,
its value at `t`, arbitrarily close to `t`. -/
theorem exists_near_lt_self_and_gt {f : ℝ → ℝ} {t : ℝ} (hcont : Continuous f)
    (hdcont : Continuous (deriv f)) (ha : deriv f t ≠ 0) :
    (∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ f r < f t) ∧
      (∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ f t < f r) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hev : ∀ᶠ r in nhds t, deriv f r < 0 := (isOpen_lt hdcont continuous_const).mem_nhds hneg
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
    have hanti : StrictAntiOn f (Set.Ioo (t - δ) (t + δ)) := by
      refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont.continuousOn ?_
      intro x hx
      rw [interior_Ioo] at hx
      have hxb : x ∈ Metric.ball t δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact hδ hxb
    constructor
    · intro ε hε
      set d : ℝ := min ε δ / 2 with hd
      have hdpos : 0 < d := by
        have h : 0 < min ε δ := lt_min hε hδpos
        rw [hd]; linarith
      have hdε : d < ε := by
        have h : min ε δ ≤ ε := min_le_left _ _
        rw [hd]; linarith
      have hdδ : d < δ := by
        have h : min ε δ ≤ δ := min_le_right _ _
        rw [hd]; linarith
      refine ⟨t + d, ?_, ?_⟩
      · have hdd : t + d - t = d := by ring
        rw [hdd, abs_of_pos hdpos]; exact hdε
      · exact hanti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    · intro ε hε
      set d : ℝ := min ε δ / 2 with hd
      have hdpos : 0 < d := by
        have h : 0 < min ε δ := lt_min hε hδpos
        rw [hd]; linarith
      have hdε : d < ε := by
        have h : min ε δ ≤ ε := min_le_left _ _
        rw [hd]; linarith
      have hdδ : d < δ := by
        have h : min ε δ ≤ δ := min_le_right _ _
        rw [hd]; linarith
      refine ⟨t - d, ?_, ?_⟩
      · have hdd : t - d - t = -d := by ring
        rw [hdd, abs_neg, abs_of_pos hdpos]; exact hdε
      · exact hanti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  · have hev : ∀ᶠ r in nhds t, 0 < deriv f r := (isOpen_lt continuous_const hdcont).mem_nhds hpos
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hev
    have hmono : StrictMonoOn f (Set.Ioo (t - δ) (t + δ)) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont.continuousOn ?_
      intro x hx
      rw [interior_Ioo] at hx
      have hxb : x ∈ Metric.ball t δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact hδ hxb
    constructor
    · intro ε hε
      set d : ℝ := min ε δ / 2 with hd
      have hdpos : 0 < d := by
        have h : 0 < min ε δ := lt_min hε hδpos
        rw [hd]; linarith
      have hdε : d < ε := by
        have h : min ε δ ≤ ε := min_le_left _ _
        rw [hd]; linarith
      have hdδ : d < δ := by
        have h : min ε δ ≤ δ := min_le_right _ _
        rw [hd]; linarith
      refine ⟨t - d, ?_, ?_⟩
      · have hdd : t - d - t = -d := by ring
        rw [hdd, abs_neg, abs_of_pos hdpos]; exact hdε
      · exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    · intro ε hε
      set d : ℝ := min ε δ / 2 with hd
      have hdpos : 0 < d := by
        have h : 0 < min ε δ := lt_min hε hδpos
        rw [hd]; linarith
      have hdε : d < ε := by
        have h : min ε δ ≤ ε := min_le_left _ _
        rw [hd]; linarith
      have hdδ : d < δ := by
        have h : min ε δ ≤ δ := min_le_right _ _
        rw [hd]; linarith
      refine ⟨t + d, ?_, ?_⟩
      · have hdd : t + d - t = d := by ring
        rw [hdd, abs_of_pos hdpos]; exact hdε
      · exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

/-- **At a transversal crossing of a face of the tilted slab, the knot admits in-box slab points
arbitrarily close.** -/
theorem exists_inBoxTiltedSlab_near_of_face {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s a h : ℝ} {v : R3} {t : ℝ} (hpos : 0 < h)
    (hface : deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0)
    (hbox : K.curve t ∈ Submission.PBox s c σ)
    (hlevel : |inner ℝ v (K.curve t) - a| = h) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, |r - t| < ε ∧ |inner ℝ v (K.curve r) - a| < h ∧
      K.curve r ∈ Submission.PBox s c σ := by
  intro ε hε
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K.curve := K.smooth
  have hdiff : ∀ r : ℝ, HasDerivAt K.curve (deriv K.curve r) r := fun r =>
    ((K.smooth.differentiable (by simp)) r).hasDerivAt
  let f : ℝ → ℝ := fun r => inner ℝ v (K.curve r) - a
  have hf_cont : Continuous f := by
    show Continuous fun r : ℝ => inner ℝ v (K.curve r) - a
    exact (continuous_const.inner hsm.continuous).sub continuous_const
  have hf_deriv : deriv f = fun r : ℝ => inner ℝ v (deriv K.curve r) := by
    funext r
    have h1 : HasDerivAt K.curve (deriv K.curve r) r := hdiff r
    have h2 : HasDerivAt (fun s : ℝ => inner ℝ v (K.curve s)) (inner ℝ v (deriv K.curve r)) r :=
      (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt r h1
    exact (h2.sub_const a).deriv
  have hface' : deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = inner ℝ v (deriv K.curve t) := by
    have h1 : HasDerivAt K.curve (deriv K.curve t) t := hdiff t
    exact ((innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t h1).deriv
  have hf_dcont : Continuous (deriv f) := by
    rw [hf_deriv]
    exact (innerSL ℝ v).continuous.comp (hsm.continuous_deriv (by simp))
  have hane : deriv f t ≠ 0 := by
    have h1 : deriv f t = inner ℝ v (deriv K.curve t) := by simp [hf_deriv]
    rw [h1, ← hface']; exact hface
  have habs : |f t| = h := hlevel
  have hbox_nhds : ∀ᶠ r in nhds t, K.curve r ∈ Submission.PBox s c σ :=
    hsm.continuous.continuousAt.eventually ((isOpen_PBox' s c σ).mem_nhds hbox)
  obtain ⟨δ3, hδ3pos, hδ3⟩ := Metric.mem_nhds_iff.mp hbox_nhds
  have h3 : ∀ r : ℝ, |r - t| < δ3 → K.curve r ∈ Submission.PBox s c σ := fun r hr =>
    hδ3 (by rw [Metric.mem_ball, Real.dist_eq]; exact hr)
  obtain ⟨δ2, hδ2pos, hδ2⟩ := (Metric.continuousAt_iff.mp hf_cont.continuousAt) (2 * h)
    (by linarith)
  have h2 : ∀ r : ℝ, |r - t| < δ2 → |f r - f t| < 2 * h := by
    intro r hr
    have hh := hδ2 (x := r) (by rw [Real.dist_eq]; exact hr)
    rwa [Real.dist_eq] at hh
  have hmin : 0 < min (min ε δ2) δ3 := lt_min (lt_min hε hδ2pos) hδ3pos
  have hle1 : min (min ε δ2) δ3 ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hle2 : min (min ε δ2) δ3 ≤ δ2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hle3 : min (min ε δ2) δ3 ≤ δ3 := min_le_right _ _
  rcases (abs_eq (le_of_lt hpos)).mp habs with hft | hft
  · obtain ⟨r, hrt, hrlt⟩ := (exists_near_lt_self_and_gt hf_cont hf_dcont hane).1
      (min (min ε δ2) δ3) hmin
    have hr2 : |r - t| < δ2 := lt_of_lt_of_le hrt hle2
    refine ⟨r, lt_of_lt_of_le hrt hle1, ?_, ?_⟩
    · have h1 : f r < h := by rw [← hft]; exact hrlt
      have h2' : -h < f r := by
        have hh := (abs_lt.mp (h2 r hr2)).1
        linarith
      have h3' : |f r| < h := abs_lt.mpr ⟨h2', h1⟩
      simpa [f] using h3'
    · exact h3 r (lt_of_lt_of_le hrt hle3)
  · obtain ⟨r, hrt, hrgt⟩ := (exists_near_lt_self_and_gt hf_cont hf_dcont hane).2
      (min (min ε δ2) δ3) hmin
    have hr2 : |r - t| < δ2 := lt_of_lt_of_le hrt hle2
    refine ⟨r, lt_of_lt_of_le hrt hle1, ?_, ?_⟩
    · have h1 : f r < h := by
        have hh := (abs_lt.mp (h2 r hr2)).2
        rw [hft] at hh; linarith
      have h2' : -h < f r := by rw [← hft]; exact hrgt
      have h3' : |f r| < h := abs_lt.mpr ⟨h2', h1⟩
      simpa [f] using h3'
    · exact h3 r (lt_of_lt_of_le hrt hle3)

/-- **The count at a regular level of the tilted sweep** (the tilted analogue of the proved
`Work.Drive.EpsFormSphere.encard_frontier_inter_lt_min`, in the geometry of the corrected design
`Work.Drive.EpsForm.tiltedSlabClosed`): the knot meets the frontier of the swept ball in fewer than
`min p q` points.  The hypotheses `hatt`, `hcover`, `hface` are the knot's general position in the
tilted slab (its maximal in-box slab arcs around the crossings of the tilted cutting plane
`{⟪v,·⟫ = a}`, with `ℓ` monotone along them; every in-box slab point connected to a crossing; and
transversal crossings of the two face planes `{⟪v,·⟫ = a ± h}`).

Proof route (reviewers' notes): `frontier (PBox \ (tiltedSlabClosed ∩ {ℓ<lam})) ⊆ frontier PBox ∪
frontier tiltedSlabClosed ∪ frontier {ℓ<lam}`, and the hypotheses cap the in-box frontier parameter
count at ≤ 4, so `hSbound` plus `hsmall` finish.  The tilted analogue of
`Work.Drive.EpsFormSphere.exists_inBoxSlab_near_of_face` is needed for the face parameters. -/
theorem encard_frontier_tiltedSweptBall_lt_min
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s a h lam : ℝ} (c v : R3) (σ : Equiv.Perm (Fin 3)) (ℓ : R3 →L[ℝ] ℝ)
    (hSbound : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hUbound : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ inner ℝ v (K.curve t) = a}
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))
    (hatt : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ → inner ℝ v (K.curve t) = a →
      ∃ h₀ t₁ t₂ : ℝ, 0 < h₀ ∧ h < h₀ ∧ t₁ < t ∧ t < t₂ ∧
        (∀ r ∈ Set.Ioo t₁ t₂,
          |inner ℝ v (K.curve r) - a| < h ∧ K.curve r ∈ Submission.PBox s c σ) ∧
        (∀ r ∈ Set.Ico 0 (2 * Real.pi), (r < t₁ ∨ t₂ < r) →
          |inner ℝ v (K.curve r) - a| < h → K.curve r ∈ Submission.PBox s c σ → False) ∧
        ∀ r ∈ Set.Ioo t₁ t₂, ∀ r' ∈ Set.Ioo t₁ t₂, r < r' → ℓ (K.curve r) < ℓ (K.curve r'))
    (hcover : ∀ t : ℝ, t ∈ Set.Ico 0 (2 * Real.pi) →
      |inner ℝ v (K.curve t) - a| < h → K.curve t ∈ Submission.PBox s c σ →
      ∃ t' : ℝ, t' ∈ Set.Ico 0 (2 * Real.pi) ∧ inner ℝ v (K.curve t') = a ∧
        ∀ r : ℝ, r ∈ Set.Icc (min t t') (max t t') →
          |inner ℝ v (K.curve r) - a| < h ∧ K.curve r ∈ Submission.PBox s c σ)
    (hface : ∀ r : ℝ, |inner ℝ v (K.curve r) - a| = h → K.curve r ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) r ≠ 0) :
    Set.encard (Set.range K.curve ∩ frontier
        (Submission.PBox s c σ \
          (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam}))) <
      (Nat.min p q : ENNReal) := by
  classical
  set R : Set R3 := Submission.PBox s c σ \
      (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam}) with hR
  set BadPath : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
    K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ frontier R} with hBadPath
  -- ### the arithmetic
  have hd1 : 1 ≤ d := Work.Drive.EpsForm.distortionBound_one_le K d hbound
  have hminR : 150 * d < (Nat.min p q : ℝ) := by
    have h := hsmall
    rw [show Submission.countConst = (150 : ℝ) from rfl] at h
    exact h
  have hminpos : 0 < (Nat.min p q : ℝ) := by linarith
  have hkey : 75 * d + 4 < (Nat.min p q : ℝ) := by
    have h150 : (150 : ℝ) < (Nat.min p q : ℝ) := by linarith
    linarith
  -- ### the two counts
  have hencS :
      (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal) ≤ ENNReal.ofReal (75 * d) := by
    have h := hSbound
    rw [ten_mul_one_add_eps_div_eps] at h
    exact h
  have hencP : (↑(Set.encard BadPath) : ENNReal) ≤ 4 := by
    by_cases hpos : 0 < h
    · -- ### the geometric case `0 < h`
      set T : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        |inner ℝ v (K.curve t) - a| < h ∧ K.curve t ∈ Submission.PBox s c σ} with hT
      set Fset : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ |inner ℝ v (K.curve t) - a| = h} with hFset
      set Wset : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ |inner ℝ v (K.curve t) - a| < h ∧
          ℓ (K.curve t) = lam} with hWset
      have hBW : BadPath ⊆ Fset ∪ Wset := by
        intro t ht
        rw [hBadPath] at ht
        obtain ⟨htIco, htbox, htR⟩ := ht
        rw [hR] at htR
        have hfr := frontier_tiltedSwept_subset s a h lam c v σ ℓ htR
        rcases hfr with hf | hf
        · have hmem : K.curve t ∈ interior (Submission.PBox s c σ) := by
            rw [(isOpen_PBox' s c σ).interior_eq]
            exact htbox
          exact absurd hmem hf.2
        · rcases hf with h | h
          · exact Or.inl (by rw [hFset]; exact ⟨htIco, htbox, h⟩)
          · exact Or.inr (by rw [hWset]; exact ⟨htIco, htbox, h.1, h.2⟩)
      by_cases hTne : T.Nonempty
      · -- ### there is an in-box slab arc
        obtain ⟨t₀, ht₀⟩ := hTne
        rw [hT] at ht₀
        obtain ⟨ht₀Ico, ht₀slab, ht₀box⟩ := ht₀
        obtain ⟨t', ht'Ico, ht'plane, hseg⟩ := hcover t₀ ht₀Ico ht₀slab ht₀box
        have ht'box : K.curve t' ∈ Submission.PBox s c σ :=
          (hseg t' ⟨min_le_right _ _, le_max_right _ _⟩).2
        obtain ⟨h₀, α, β, hh₀, hhα, ht'α, ht'β, hArc, hMax, hMono⟩ :=
          hatt t' ht'box ht'plane
        have hαβ : α < β := lt_trans ht'α ht'β
        have hTsub : T ⊆ Set.Icc α β := by
          intro r hr
          rw [hT] at hr
          obtain ⟨hrIco, hrslab, hrbox⟩ := hr
          by_contra hcon
          rw [Set.mem_Icc, not_and_or] at hcon
          rcases hcon with hc | hc
          · exact hMax r hrIco (Or.inl (not_le.mp hc)) hrslab hrbox
          · exact hMax r hrIco (Or.inr (not_le.mp hc)) hrslab hrbox
        have hwall : ∀ r ∈ Set.Ioo α β, ∀ r' ∈ Set.Ioo α β,
            ℓ (K.curve r) = lam → ℓ (K.curve r') = lam → r = r' := by
          intro r hr r' hr' h1 h2
          rcases lt_trichotomy r r' with h | h | h
          · have hc := hMono r hr r' hr' h
            rw [h1, h2] at hc
            exact absurd hc (lt_irrefl lam)
          · exact h
          · have hc := hMono r' hr' r hr h
            rw [h1, h2] at hc
            exact absurd hc (lt_irrefl lam)
        obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
            Set.Ioo α β ∩ {r : ℝ | ℓ (K.curve r) = lam} ⊆ {c₀} := by
          by_cases hne : (Set.Ioo α β ∩ {r : ℝ | ℓ (K.curve r) = lam}).Nonempty
          · obtain ⟨r₀, hr₀⟩ := hne
            exact ⟨r₀, fun r hr => by
              rw [Set.mem_singleton_iff]
              exact hwall r hr.1 r₀ hr₀.1 hr.2 hr₀.2⟩
          · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ hne⟩
        have hFsub : Fset ⊆ insert α (insert β (insert 0 ({c₀} : Set ℝ))) := by
          intro t ht
          rw [hFset] at ht
          obtain ⟨htIco, htbox, htlev⟩ := ht
          rcases eq_or_ne t 0 with h0 | h0
          · rw [h0]; simp
          · have ht_pos : 0 < t := lt_of_le_of_ne htIco.1 (Ne.symm h0)
            have hnear : ∀ ε : ℝ, 0 < ε → ∃ r ∈ T, |r - t| < ε := by
              intro ε hε
              set δ : ℝ := min (min ε t) (2 * Real.pi - t) / 2 with hδ
              have hδpos : 0 < δ := by
                rw [hδ]
                have h1 : 0 < min (min ε t) (2 * Real.pi - t) :=
                  lt_min (lt_min hε ht_pos) (by linarith [htIco.2])
                positivity
              have hδε : δ ≤ ε := by
                rw [hδ]
                have h1 := min_le_left (min ε t) (2 * Real.pi - t)
                have h2 := min_le_left ε t
                linarith
              have hδt : δ ≤ t := by
                rw [hδ]
                have h1 := min_le_left (min ε t) (2 * Real.pi - t)
                have h2 := min_le_right ε t
                linarith
              have hδ2 : δ ≤ 2 * Real.pi - t := by
                rw [hδ]
                have h1 := min_le_right (min ε t) (2 * Real.pi - t)
                linarith
              obtain ⟨r, hdd, hrslab, hrbox⟩ :=
                exists_inBoxTiltedSlab_near_of_face (K := K) (v := v) (a := a) (h := h)
                  (s := s) (c := c) (σ := σ) (t := t) hpos (hface t htlev htbox) htbox htlev
                  δ hδpos
              refine ⟨r, ?_, ?_⟩
              · rw [hT]
                rw [abs_lt] at hdd
                exact ⟨⟨by linarith, by linarith⟩, hrslab, hrbox⟩
              · rw [abs_lt] at hdd ⊢
                exact ⟨by linarith, by linarith⟩
            have htcl : t ∈ closure T := by
              rw [Metric.mem_closure_iff]
              intro ε hε
              obtain ⟨r, hrT, hd⟩ := hnear ε hε
              exact ⟨r, hrT, by rw [Real.dist_eq, abs_sub_comm]; exact hd⟩
            have htin : t ∈ Set.Icc α β := by
              have h2 := closure_mono hTsub htcl
              rwa [closure_Icc] at h2
            have hnotin : t ∉ Set.Ioo α β := by
              intro hioo
              have hlt : |inner ℝ v (K.curve t) - a| < h := (hArc t hioo).1
              rw [htlev] at hlt
              exact absurd hlt (lt_irrefl h)
            rcases Set.mem_Icc.mp htin with ⟨h1, h2⟩
            rcases eq_or_lt_of_le h1 with h | h
            · rw [← h]; simp
            · rcases eq_or_lt_of_le h2 with h' | h'
              · rw [h']; simp
              · exact absurd ⟨h, h'⟩ hnotin
        have hWsub : Wset ⊆ insert α (insert β (insert 0 ({c₀} : Set ℝ))) := by
          intro t ht
          rw [hWset] at ht
          obtain ⟨htIco, htbox, htlt, htlam⟩ := ht
          have htT : t ∈ T := by rw [hT]; exact ⟨htIco, htlt, htbox⟩
          have htab : t ∈ Set.Icc α β := hTsub htT
          rcases Set.mem_Icc.mp htab with ⟨h1, h2⟩
          rcases eq_or_lt_of_le h1 with h | h
          · rw [← h]; simp
          · rcases eq_or_lt_of_le h2 with h' | h'
            · rw [h']; simp
            · have hmem : t ∈ Set.Ioo α β ∩ {r : ℝ | ℓ (K.curve r) = lam} := ⟨⟨h, h'⟩, htlam⟩
              have hc := hc₀ hmem
              rw [Set.mem_singleton_iff] at hc
              rw [hc]; simp
        have hsub : BadPath ⊆ insert α (insert β (insert 0 ({c₀} : Set ℝ))) :=
          Set.Subset.trans hBW (Set.union_subset hFsub hWsub)
        have henc4 :
            (↑(Set.encard (insert α (insert β (insert 0 ({c₀} : Set ℝ))))) : ENNReal) ≤ 4 := by
          have h1 : Set.encard (insert α (insert β (insert 0 ({c₀} : Set ℝ)))) ≤ 4 := by
            calc Set.encard (insert α (insert β (insert 0 ({c₀} : Set ℝ))))
                ≤ Set.encard (insert β (insert 0 ({c₀} : Set ℝ))) + 1 :=
                  Set.encard_insert_le _ _
              _ ≤ (Set.encard (insert 0 ({c₀} : Set ℝ)) + 1) + 1 :=
                  add_le_add (Set.encard_insert_le (insert 0 ({c₀} : Set ℝ)) β) le_rfl
              _ ≤ ((Set.encard ({c₀} : Set ℝ) + 1) + 1) + 1 :=
                  add_le_add
                    (add_le_add (Set.encard_insert_le ({c₀} : Set ℝ) 0) le_rfl) le_rfl
              _ = 4 := by rw [Set.encard_singleton]; norm_num
          simpa using ENat.toENNReal_mono h1
        exact le_trans (ENat.toENNReal_mono (Set.encard_le_encard hsub)) henc4
      · -- ### there is no in-box slab point at all
        have hTe : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hTne
        have hT₀e : {t : ℝ | |inner ℝ v (K.curve t) - a| < h ∧
            K.curve t ∈ Submission.PBox s c σ} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          obtain ⟨htslab, htbox⟩ := ht
          have hmem : K.curve t ∈ Set.range K.curve := ⟨t, rfl⟩
          rw [Work.Drive.EpsForm.range_knot_eq_image_Ico K] at hmem
          obtain ⟨r, hrIco, hr⟩ := hmem
          have hrT : r ∈ T := by
            rw [hT]
            exact ⟨hrIco, by rw [hr]; exact htslab, by rw [hr]; exact htbox⟩
          rw [hTe] at hrT
          exact hrT
        have hF_empty : Fset = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rw [hFset] at ht
          obtain ⟨htIco, htbox, htlev⟩ := ht
          obtain ⟨r, -, hrslab, hrbox⟩ :=
            exists_inBoxTiltedSlab_near_of_face (K := K) (v := v) (a := a) (h := h)
              (s := s) (c := c) (σ := σ) (t := t) hpos (hface t htlev htbox) htbox htlev 1 one_pos
          have hrT₀ : r ∈ {t : ℝ | |inner ℝ v (K.curve t) - a| < h ∧
              K.curve t ∈ Submission.PBox s c σ} := ⟨hrslab, hrbox⟩
          rw [hT₀e] at hrT₀
          exact hrT₀
        have hW_empty : Wset = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rw [hWset] at ht
          obtain ⟨htIco, htbox, htlt, -⟩ := ht
          have hmem : t ∈ T := by rw [hT]; exact ⟨htIco, htlt, htbox⟩
          rw [hTe] at hmem
          exact hmem
        have hBe : BadPath = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro t ht
          rcases hBW ht with h | h
          · rw [hF_empty] at h; exact h
          · rw [hW_empty] at h; exact h
        rw [hBe, Set.encard_empty]
        simp
    · -- ### `h ≤ 0`: the frontier count is empty
      have hBe : BadPath = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro t ht
        rw [hBadPath] at ht
        obtain ⟨htIco, htbox, htR⟩ := ht
        rw [hR] at htR
        have hfr := frontier_tiltedSwept_subset s a h lam c v σ ℓ htR
        rcases hfr with hf | hf
        · have hmem : K.curve t ∈ interior (Submission.PBox s c σ) := by
            rw [(isOpen_PBox' s c σ).interior_eq]
            exact htbox
          exact absurd hmem hf.2
        · rcases hf with hf | hf
          · have hzero : |inner ℝ v (K.curve t) - a| = 0 :=
              le_antisymm (by rw [hf]; exact not_lt.mp hpos) (abs_nonneg _)
            have hfa : inner ℝ v (K.curve t) = a := by
              have h0 := abs_eq_zero.mp hzero
              linarith
            obtain ⟨h₀, t₁, t₂, hh₀, hhα, ht₁, ht₂, hArc, -, -⟩ := hatt t htbox hfa
            have hcontra : (0 : ℝ) < h := by
              have hlt := (hArc t ⟨ht₁, ht₂⟩).1
              rw [hzero] at hlt
              exact hlt
            exact absurd hcontra hpos
          · have h1 : (0 : ℝ) ≤ |inner ℝ v (K.curve t) - a| := abs_nonneg _
            have h2 : h ≤ 0 := not_lt.mp hpos
            linarith [hf.1]
      rw [hBe, Set.encard_empty]
      simp
  -- ### the box-sphere part of the frontier
  have hBad_sub :
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ frontier R} ⊆
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ Submission.boxNorm c σ (K.curve t) = s} ∪
      BadPath := by
    intro t ht
    obtain ⟨htIco, htR⟩ := ht
    rw [hR] at htR
    by_cases hbox : K.curve t ∈ Submission.PBox s c σ
    · exact Or.inr (by rw [hBadPath]; exact ⟨htIco, hbox, htR⟩)
    · refine Or.inl ⟨htIco, ?_⟩
      rcases frontier_sdiff_subset_frontier_union (Submission.PBox s c σ)
        (Work.Drive.EpsForm.tiltedSlabClosed a v h ∩ {y : R3 | ℓ y < lam}) htR with hf | hf
      · exact frontier_PBox_subset_boxNorm s c σ hf
      · exact absurd hf hbox
  have harith : ENNReal.ofReal (75 * d) + (4 : ENNReal) < (Nat.min p q : ENNReal) := by
    have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ENNReal) := by simp
    rw [← h4, ← ENNReal.ofReal_add (by positivity) (by norm_num),
      ← ENNReal.ofReal_natCast (Nat.min p q)]
    exact (ENNReal.ofReal_lt_ofReal_iff hminpos).mpr hkey
  -- ### assembly
  have hstep1 :
      (↑(Set.encard (Set.range K.curve ∩ frontier R)) : ENNReal) ≤
      (↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ frontier R}) : ENNReal) :=
    ENat.toENNReal_mono (Work.Drive.EpsForm.encard_range_inter_le_param K _)
  have hstep2 := encard_le_add_of_subset_union hBad_sub
  exact lt_of_le_of_lt (le_trans hstep1 (le_trans hstep2 (add_le_add hencS hencP))) harith


end

end Work.Drive.EpsFormSphere

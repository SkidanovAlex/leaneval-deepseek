import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.crossing_time
import Submission.Work.Diff.Dim2.crossing_time_smooth
import Submission.Work.Diff.Dim2.flow_shift
import Submission.Work.Diff.Dim2.flow_lowers_f
import Submission.Work.Diff.C.rdist_continuous
import Submission.Commons.Topology.Order.Ioo_mem_nhdsWithin_lt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter


/-! ## Auxiliary lemmas

These are the abstract (manifold-free) ingredients of the proof of `tau`: the local
monotonicity of a function with a positive derivative, the "constant derivative one implies
affine" mean-value statement, the uniqueness of a level crossing with transverse crossings, the
crossing of an annulus of unit speed, and a compactness engine producing a level crossing.
-/

/-- **A positive derivative gives two-sided local strict increase.** -/
theorem local_mono_of_hasDerivAt {h : ℝ → ℝ} {s₀ c : ℝ} (hd : HasDerivAt h c s₀) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) δ, h (s₀ - t) < h s₀ ∧ h s₀ < h (s₀ + t) := by
  have hslope : ∀ᶠ x in 𝓝[≠] s₀, 0 < slope h s₀ x :=
    hd.tendsto_slope.eventually (isOpen_Ioi.mem_nhds hc)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hslope
  obtain ⟨ε, hε, hε'⟩ := hslope
  refine ⟨ε, hε, fun t ht => ?_⟩
  have ht0 : 0 < t := ht.1
  have hne1 : s₀ - t ≠ s₀ := by intro h; linarith [sub_eq_self.mp h]
  have hne2 : s₀ + t ≠ s₀ := by intro h; linarith [add_eq_left.mp h]
  have hd1 : dist (s₀ - t) s₀ < ε := by
    rw [Real.dist_eq]
    have : (s₀ - t) - s₀ = -t := by ring
    rw [this, abs_neg, abs_of_pos ht0]
    exact ht.2
  have hd2 : dist (s₀ + t) s₀ < ε := by
    rw [Real.dist_eq]
    have : (s₀ + t) - s₀ = t := by ring
    rw [this, abs_of_pos ht0]
    exact ht.2
  have hs1 : 0 < slope h s₀ (s₀ - t) := hε' hd1 hne1
  have hs2 : 0 < slope h s₀ (s₀ + t) := hε' hd2 hne2
  rw [slope_def_field] at hs1 hs2
  constructor
  · have hneg : h (s₀ - t) - h s₀ < 0 := by
      rcases div_pos_iff.mp hs1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : (s₀ - t) - s₀ < 0 := by linarith
        exact absurd h2 (not_lt.mpr this.le)
      · exact h1
    linarith
  · have hpos : 0 < h (s₀ + t) - h s₀ := by
      rcases div_pos_iff.mp hs2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · have : 0 < (s₀ + t) - s₀ := by linarith
        exact absurd h2 (not_lt.mpr this.le)
    linarith

/-- **A function with derivative one on an interval is affine there.** -/
theorem eq_add_of_hasDerivAt_one {h : ℝ → ℝ} {s₀ s₁ : ℝ} (hle : s₀ ≤ s₁)
    (hcont : ContinuousOn h (Set.Icc s₀ s₁))
    (hd : ∀ s ∈ Set.Icc s₀ s₁, HasDerivAt h 1 s) :
    ∀ s ∈ Set.Icc s₀ s₁, h s = h s₀ + (s - s₀) := by
  intro s hs
  rcases lt_or_eq_of_le hs.1 with hlt | heq
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope h (fun _ => (1:ℝ)) hlt
      (hcont.mono (Set.Icc_subset_Icc le_rfl hs.2))
      (fun x hx => hd x ⟨hx.1.le, hx.2.le.trans hs.2⟩)
    have hden : s - s₀ ≠ 0 := by linarith
    have h1 : (h s - h s₀) / (s - s₀) = 1 := hcs.symm
    have h2 : h s - h s₀ = 1 * (s - s₀) := (div_eq_iff hden).mp h1
    linarith
  · subst heq; ring

/-- **Uniqueness of a level crossing of a flow, from the transversality of the crossing.**
If at every point `y` with `f y = ℓ` the function `s ↦ f (φ y s)` has derivative `1` at `0`, then
the level `ℓ` is crossed at most once by each trajectory. -/
theorem crossing_unique_of_deriv
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {φ : X → ℝ → X}
    (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
    (hφ0 : ∀ x : X, φ x 0 = x)
    (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
    {ℓ : ℝ} (hderiv : ∀ y : X, f y = ℓ → HasDerivAt (fun s : ℝ => f (φ y s)) 1 0) :
    ∀ x : X, ∀ t t' : ℝ, f (φ x t) = ℓ → f (φ x t') = ℓ → t = t' := by
  intro x t t' ht ht'
  have key : ∀ a b : ℝ, f (φ x a) = ℓ → f (φ x b) = ℓ → a < b → False := by
    intro a b ha hb hab
    set y : X := φ x a with hy
    have hyf : f y = ℓ := ha
    have hcross : f (φ y (b - a)) = ℓ := by
      rw [hy, hφadd x a (b - a)]
      have : a + (b - a) = b := by ring
      rw [this]; exact hb
    have hcont : Continuous fun s : ℝ => f (φ y s) :=
      hf.comp (hφcont.comp (continuous_const.prodMk continuous_id))
    have hy0 : φ y 0 = y := hφ0 y
    obtain ⟨δ, hδ, hδ'⟩ := local_mono_of_hasDerivAt (hderiv y hyf) one_pos
    have hδ'' : ∀ t ∈ Set.Ioo (0:ℝ) δ, f (φ y (-t)) < ℓ ∧ ℓ < f (φ y t) := by
      intro t ht
      have h1 := hδ' t ht
      simp only [zero_sub, zero_add] at h1
      rw [hy0, hyf] at h1
      exact h1
    have hdel_le : δ ≤ b - a := by
      by_contra hcon
      push_neg at hcon
      have h1 := hδ'' (b - a) ⟨by linarith, hcon⟩
      rw [hcross] at h1
      exact lt_irrefl ℓ h1.2
    set Z : Set ℝ := {s : ℝ | δ ≤ s ∧ f (φ y s) = ℓ} with hZdef
    have hZne : Z.Nonempty := ⟨b - a, hdel_le, hcross⟩
    have hbdd : BddBelow Z := ⟨δ, fun s hs => hs.1⟩
    have hZcl : IsClosed Z := by
      rw [hZdef]
      exact IsClosed.inter isClosed_Ici (isClosed_eq hcont continuous_const)
    set s₂ : ℝ := sInf Z with hs₂def
    have hs₂Z : s₂ ∈ Z := hZcl.csInf_mem hZne hbdd
    have hs₂pos : 0 < s₂ := lt_of_lt_of_le hδ hs₂Z.1
    have hs₂val : f (φ y s₂) = ℓ := hs₂Z.2
    have hmin : ∀ σ ∈ Set.Ioo (0:ℝ) s₂, f (φ y σ) ≠ ℓ := by
      intro σ hσ hcon
      rcases lt_or_ge σ δ with hlt | hge
      · exact absurd (hδ'' σ ⟨hσ.1, hlt⟩).2 (not_lt.mpr hcon.le)
      · have hmem : σ ∈ Z := ⟨hge, hcon⟩
        have := csInf_le hbdd hmem
        rw [← hs₂def] at this
        exact absurd this (not_le.mpr hσ.2)
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := local_mono_of_hasDerivAt (hderiv (φ y s₂) hs₂val) one_pos
    have hs₂0 : φ (φ y s₂) 0 = φ y s₂ := hφ0 (φ y s₂)
    have hδ₂'' : ∀ t ∈ Set.Ioo (0:ℝ) δ₂, f (φ y (s₂ - t)) < ℓ ∧ ℓ < f (φ y (s₂ + t)) := by
      intro t ht
      have h1 := hδ₂' t ht
      simp only [zero_sub, zero_add] at h1
      rw [hs₂0, hs₂val] at h1
      have heq1 : φ (φ y s₂) (-t) = φ y (s₂ - t) := by rw [hφadd, sub_eq_add_neg]
      have heq2 : φ (φ y s₂) t = φ y (s₂ + t) := by rw [hφadd]
      rw [heq1, heq2] at h1
      exact h1
    have hδs₂ : δ ≤ s₂ := hs₂Z.1
    set τ : ℝ := min δ₂ s₂ / 2 with hτdef
    have hτpos : 0 < τ := by rw [hτdef]; exact half_pos (lt_min hδ₂ hs₂pos)
    have hτlt : τ < δ₂ := by rw [hτdef]; linarith [min_le_left δ₂ s₂]
    have hτs : τ < s₂ := by rw [hτdef]; linarith [min_le_right δ₂ s₂]
    have hlow : f (φ y (s₂ - τ)) < ℓ := (hδ₂'' τ ⟨hτpos, hτlt⟩).1
    have hbig : ℓ < f (φ y (δ / 2)) := (hδ'' (δ / 2) ⟨by linarith, by linarith⟩).2
    have hzero : ∃ c ∈ Set.Ioo (0:ℝ) s₂, f (φ y c) = ℓ := by
      rcases le_total (δ / 2) (s₂ - τ) with hle | hle
      · have hct' : ContinuousOn (fun σ : ℝ => f (φ y σ) - ℓ) (Set.Icc (δ / 2) (s₂ - τ)) :=
          (hcont.sub continuous_const).continuousOn
        have hmem : (0:ℝ) ∈ Set.Icc (f (φ y (s₂ - τ)) - ℓ) (f (φ y (δ / 2)) - ℓ) :=
          ⟨by linarith, by linarith⟩
        obtain ⟨c, hc, hcv⟩ := (mem_image ..).mp ((intermediate_value_Icc' hle hct') hmem)
        exact ⟨c, ⟨by linarith [hc.1], by linarith [hc.2, hτpos]⟩, by linarith [hcv]⟩
      · have hct' : ContinuousOn (fun σ : ℝ => f (φ y σ) - ℓ) (Set.Icc (s₂ - τ) (δ / 2)) :=
          (hcont.sub continuous_const).continuousOn
        have hmem : (0:ℝ) ∈ Set.Icc (f (φ y (s₂ - τ)) - ℓ) (f (φ y (δ / 2)) - ℓ) :=
          ⟨by linarith, by linarith⟩
        obtain ⟨c, hc, hcv⟩ := (mem_image ..).mp ((intermediate_value_Icc hle hct') hmem)
        exact ⟨c, ⟨by linarith [hc.1, hτpos], by linarith [hc.2, hδs₂, hs₂pos]⟩, by linarith [hcv]⟩
    obtain ⟨c, hcIoo, hcv⟩ := hzero
    exact hmin c hcIoo hcv
  rcases lt_trichotomy t t' with h | h | h
  · exact (key t t' ht ht' h).elim
  · exact h
  · exact (key t' t ht' ht h).elim


/-- **Crossing of an annulus at unit speed** (forward case).  If a continuous function `f` grows
at speed exactly one along the flow of `φ` at every point where its value lies in the annulus
`[c₁,c₂]`, then starting from `x` with `f x ∈ [c₁,c₂]` the value `ℓ ∈ [c₁,c₂]` is reached after
time `ℓ - f x`. -/
theorem flow_cross_annulus_fwd
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) {φ : X → ℝ → X}
    (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
    (hφ0 : ∀ x : X, φ x 0 = x)
    (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
    {c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hu : ∀ y : X, c₁ ≤ f y → f y ≤ c₂ → HasDerivAt (fun s : ℝ => f (φ y s)) 1 0)
    {x : X} {ℓ : ℝ} (hx : c₁ ≤ f x) (hx₂ : f x ≤ c₂) (hℓ : c₁ ≤ ℓ) (hℓ₂ : ℓ ≤ c₂)
    (hT : 0 ≤ ℓ - f x) :
    f (φ x (ℓ - f x)) = ℓ := by
  by_contra hdev
  have hcont : Continuous fun σ : ℝ => f (φ x σ) :=
    hf.comp (hφcont.comp (continuous_const.prodMk continuous_id))
  have hshift : ∀ s : ℝ, c₁ ≤ f (φ x s) → f (φ x s) ≤ c₂ →
      HasDerivAt (fun σ : ℝ => f (φ x σ)) 1 s := by
    intro s h1 h2
    have hbase : HasDerivAt (fun τ : ℝ => f (φ (φ x s) τ)) 1 (-s + s) := by
      simpa using hu (φ x s) h1 h2
    have h3 : HasDerivAt (fun σ : ℝ => f (φ (φ x s) (σ - s))) 1 s := by
      simpa [sub_eq_add_neg, add_comm] using HasDerivAt.comp_const_add (-s) s hbase
    have h4 : (fun σ : ℝ => f (φ x σ)) = (fun σ : ℝ => f (φ (φ x s) (σ - s))) := by
      funext σ
      rw [hφadd]
      congr 1
      ring
    rw [← h4] at h3
    exact h3
  set T : ℝ := ℓ - f x with hTdef
  set K : ℝ → ℝ := fun σ => f (φ x σ) - σ with hKdef
  have hKcont : Continuous K := hcont.sub continuous_id
  have hK0 : K 0 = f x := by simp [hKdef, hφ0 x]
  set D : Set ℝ := {σ : ℝ | 0 ≤ σ ∧ σ ≤ T ∧ K σ ≠ f x} with hDdef
  have hTmem : T ∈ D := by
    refine ⟨hT, le_rfl, ?_⟩
    intro hcon
    apply hdev
    have hh := hcon; rw [hKdef] at hh; simp only [] at hh; linarith
  have hDne : D.Nonempty := ⟨T, hTmem⟩
  have hbdd : BddBelow D := ⟨0, fun σ hσ => hσ.1⟩
  set s₀ : ℝ := sInf D with hs₀def
  have hs₀ge : 0 ≤ s₀ := le_csInf hDne (fun σ hσ => hσ.1)
  have hs₀le : s₀ ≤ T := by
    have h1 := csInf_le hbdd hTmem
    rw [← hs₀def] at h1
    exact h1
  have hs₀val : K s₀ = f x := by
    by_contra hne
    have hopen : {σ : ℝ | K σ ≠ f x} ∈ 𝓝 s₀ :=
      hKcont.continuousAt (isOpen_ne.mem_nhds hne)
    rw [Metric.mem_nhds_iff] at hopen
    obtain ⟨ε, hε, hε'⟩ := hopen
    have hs₀pos : 0 < s₀ := by
      rcases lt_or_eq_of_le hs₀ge with h | h
      · exact h
      · exfalso
        rw [← h] at hne
        exact hne hK0
    set ε' : ℝ := min ε s₀ / 2 with hε'def
    have hε'pos : 0 < ε' := by rw [hε'def]; exact half_pos (lt_min hε hs₀pos)
    have hε'ε : ε' < ε := by rw [hε'def]; linarith [min_le_left ε s₀]
    have hε's : ε' < s₀ := by rw [hε'def]; linarith [min_le_right ε s₀]
    have hmem : s₀ - ε' ∈ D := by
      refine ⟨by linarith, by linarith, ?_⟩
      apply hε'
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have h1 := csInf_le hbdd hmem
    rw [← hs₀def] at h1
    linarith
  have hs₀f : f (φ x s₀) = f x + s₀ := by
    have := hs₀val; rw [hKdef] at this; simp only [] at this; linarith
  have hs₀ltT : s₀ < T := by
    rcases lt_or_eq_of_le hs₀le with h | h
    · exact h
    · exfalso; rw [h] at hs₀val; exact hTmem.2.2 hs₀val
  have hext : ∃ ε : ℝ, 0 < ε ∧ ε ≤ T - s₀ ∧
      ∀ σ ∈ Set.Icc s₀ (s₀ + ε), K σ = f x := by
    have hTs : 0 < T - s₀ := by linarith [hs₀ltT]
    have hle0 : c₁ ≤ f (φ x s₀) := by rw [hs₀f]; linarith
    rcases lt_or_eq_of_le hle0 with hgt | heq
    · -- generic case
      have hlt2 : f (φ x s₀) < c₂ := by rw [hs₀f]; linarith
      obtain ⟨ε₀, hε₀, hε₀'⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ σ : ℝ, dist σ s₀ < ε₀ → c₁ ≤ f (φ x σ) ∧ f (φ x σ) ≤ c₂ := by
        have h1 : ∀ᶠ σ in 𝓝 s₀, f (φ x σ) ∈ Set.Icc c₁ c₂ :=
          hcont.continuousAt.eventually (Icc_mem_nhds hgt hlt2)
        rw [Metric.eventually_nhds_iff] at h1
        obtain ⟨ε₀, hε₀, hε₀'⟩ := h1
        exact ⟨ε₀, hε₀, fun σ hd => hε₀' hd⟩
      set m : ℝ := min (ε₀ / 2) (T - s₀) with hmdef
      have hmpos : 0 < m := by rw [hmdef]; exact lt_min (half_pos hε₀) hTs
      have hmT : m ≤ T - s₀ := by rw [hmdef]; exact min_le_right _ _
      have hmε : m ≤ ε₀ / 2 := by rw [hmdef]; exact min_le_left _ _
      refine ⟨m, hmpos, hmT, fun σ hσ => ?_⟩
      have hann : ∀ τ ∈ Set.Icc s₀ (s₀ + m), c₁ ≤ f (φ x τ) ∧ f (φ x τ) ≤ c₂ := by
        intro τ hτ
        apply hε₀' τ
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hτ.1], by linarith [hτ.2, hmε]⟩
      have hlin := eq_add_of_hasDerivAt_one (show s₀ ≤ s₀ + m by linarith)
        hcont.continuousOn (fun τ hτ => hshift τ (hann τ hτ).1 (hann τ hτ).2)
      have hσ' := hlin σ hσ
      rw [hKdef]
      simp only []
      rw [hσ', hs₀f]
      ring
    · -- degenerate case: the value at s₀ is exactly c₁, so s₀ = 0
      have hs₀0 : s₀ = 0 := by linarith [hs₀f, heq, hx]
      have hfx' : f x = c₁ := by linarith [hs₀f, heq, hs₀0]
      have hd0 : HasDerivAt (fun σ : ℝ => f (φ x σ)) 1 0 := hu x hx hx₂
      obtain ⟨δ, hδ, hδ'⟩ := local_mono_of_hasDerivAt hd0 one_pos
      have hincr : ∀ t ∈ Set.Ioo (0:ℝ) δ, f x < f (φ x t) := by
        intro t ht
        have h1 := hδ' t ht
        simp only [zero_sub, zero_add] at h1
        rw [hφ0 x] at h1
        exact h1.2
      obtain ⟨ε₀, hε₀, hε₀'⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ σ : ℝ, dist σ 0 < ε₀ → f (φ x σ) < c₂ := by
        have h1 : ∀ᶠ σ in 𝓝 (0:ℝ), f (φ x σ) < c₂ :=
          hcont.continuousAt.eventually (isOpen_Iio.mem_nhds (by
            show f (φ x 0) < c₂
            rw [hφ0 x, hfx']
            exact hc))
        rw [Metric.eventually_nhds_iff] at h1
        obtain ⟨ε₀, hε₀, hε₀'⟩ := h1
        exact ⟨ε₀, hε₀, fun σ hd => hε₀' hd⟩
      set m : ℝ := min δ (min ε₀ (T - s₀)) / 2 with hmdef
      have hmpos : 0 < m := by
        rw [hmdef]
        exact half_pos (lt_min hδ (lt_min hε₀ hTs))
      have hmδ : m < δ := by
        rw [hmdef]
        have h1 := min_le_left δ (min ε₀ (T - s₀)); linarith
      have hmε : m < ε₀ := by
        rw [hmdef]
        have h1 := min_le_right δ (min ε₀ (T - s₀))
        have h2 := min_le_left ε₀ (T - s₀)
        linarith
      have hmT : m ≤ T - s₀ := by
        rw [hmdef]
        have h1 := min_le_right δ (min ε₀ (T - s₀))
        have h2 := min_le_right ε₀ (T - s₀)
        linarith
      refine ⟨m, hmpos, hmT, fun σ hσ => ?_⟩
      have hann : ∀ τ ∈ Set.Icc s₀ (s₀ + m), c₁ ≤ f (φ x τ) ∧ f (φ x τ) ≤ c₂ := by
        intro τ hτ
        rw [hs₀0, zero_add] at hτ
        constructor
        · rcases hτ.1.lt_or_eq with h | h
          · have h1 := hincr τ ⟨h, lt_of_le_of_lt hτ.2 hmδ⟩
            rw [hfx'] at h1
            exact h1.le
          · rw [← h, hφ0 x, hfx']
        · have h1 : dist τ 0 < ε₀ := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
            exact lt_of_le_of_lt hτ.2 hmε
          exact (hε₀' τ h1).le
      have hlin := eq_add_of_hasDerivAt_one (show s₀ ≤ s₀ + m by linarith)
        hcont.continuousOn (fun τ hτ => hshift τ (hann τ hτ).1 (hann τ hτ).2)
      have hσ' := hlin σ hσ
      rw [hKdef]
      simp only []
      rw [hσ', hs₀f]
      ring
  obtain ⟨ε, hε, hεT, hε'⟩ := hext
  have hlow : ∀ d ∈ D, s₀ + ε ≤ d := by
    intro d hd
    have hd1 : s₀ ≤ d := by
      have h1 := csInf_le hbdd hd
      rw [← hs₀def] at h1
      exact h1
    by_contra hcon
    push_neg at hcon
    have hmem : d ∈ Set.Icc s₀ (s₀ + ε) := ⟨hd1, hcon.le⟩
    exact hd.2.2 (hε' d hmem)
  have h1 : s₀ + ε ≤ s₀ := by
    have h2 := le_csInf hDne hlow
    rw [← hs₀def] at h2
    exact h2
  linarith

/-- **Crossing of an annulus at unit speed** (general case). -/
theorem flow_cross_annulus
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) {φ : X → ℝ → X}
    (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
    (hφ0 : ∀ x : X, φ x 0 = x)
    (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
    {c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hu : ∀ y : X, c₁ ≤ f y → f y ≤ c₂ → HasDerivAt (fun s : ℝ => f (φ y s)) 1 0)
    {x : X} {ℓ : ℝ} (hx : c₁ ≤ f x) (hx₂ : f x ≤ c₂) (hℓ : c₁ ≤ ℓ) (hℓ₂ : ℓ ≤ c₂) :
    f (φ x (ℓ - f x)) = ℓ := by
  rcases le_total (0:ℝ) (ℓ - f x) with hT | hT
  · exact flow_cross_annulus_fwd hf hφcont hφ0 hφadd hc hu hx hx₂ hℓ hℓ₂ hT
  · -- reverse time: apply the forward version to `-f` and the reversed flow
    have hf' : Continuous fun y : X => - f y := hf.neg
    have hc' : -c₂ < -c₁ := by linarith
    have hφ0' : ∀ y : X, φ y (-(0:ℝ)) = y := by intro y; rw [neg_zero]; exact hφ0 y
    have hφadd' : ∀ (y : X) (s t : ℝ), φ (φ y (-s)) (-t) = φ y (-(s + t)) := by
      intro y s t
      rw [hφadd]
      congr 1
      ring
    have hu' : ∀ y : X, -c₂ ≤ - f y → - f y ≤ -c₁ →
        HasDerivAt (fun τ : ℝ => - f (φ y (-τ))) 1 0 := by
      intro y h1 h2
      have hy1 : c₁ ≤ f y := by linarith
      have hy2 : f y ≤ c₂ := by linarith
      have hbase : HasDerivAt (fun σ : ℝ => f (φ y σ)) 1 0 := hu y hy1 hy2
      have hbase' : HasDerivAt (fun σ : ℝ => f (φ y σ)) 1 ((fun σ : ℝ => -σ) 0) := by
        simpa using hbase
      have hneg : HasDerivAt (fun σ : ℝ => -σ) (-1) 0 := hasDerivAt_neg 0
      have hcomp := hbase'.comp 0 hneg
      have hfun : (fun σ : ℝ => f (φ y σ)) ∘ (fun σ : ℝ => -σ)
          = (fun τ : ℝ => f (φ y (-τ))) := rfl
      rw [hfun] at hcomp
      have hmid : HasDerivAt (fun τ : ℝ => f (φ y (-τ))) (-1) 0 := by
        simpa using hcomp
      have hout : HasDerivAt (fun v : ℝ => -v) (-1) ((fun τ : ℝ => f (φ y (-τ))) 0) := by
        have h0 : HasDerivAt (fun v : ℝ => -v) (-1) (f (φ y 0)) := by
          simpa using hasDerivAt_neg (f (φ y 0))
        simpa using h0
      have hfin := hout.comp 0 hmid
      have hfin' : HasDerivAt (fun τ : ℝ => - f (φ y (-τ))) ((-1) * (-1)) 0 := hfin
      simpa using hfin'
    have hx' : -c₂ ≤ - f x := by linarith
    have hx₂' : - f x ≤ -c₁ := by linarith
    have hℓ' : -c₂ ≤ -ℓ := by linarith
    have hℓ₂' : -ℓ ≤ -c₁ := by linarith
    have hT' : 0 ≤ (-ℓ) - (-f x) := by linarith
    have hφcont' : Continuous fun p : X × ℝ => φ p.1 (-p.2) :=
      hφcont.comp (continuous_fst.prodMk continuous_snd.neg)
    have key := flow_cross_annulus_fwd (f := fun y : X => - f y)
      (φ := fun y : X => fun τ : ℝ => φ y (-τ)) hf' hφcont' hφ0' hφadd' hc' hu' hx' hx₂' hℓ' hℓ₂' hT'
    have hval : (-ℓ) - (-f x) = -(ℓ - f x) := by ring
    rw [hval] at key
    have hneg : φ x (-(-(ℓ - f x))) = φ x (ℓ - f x) := by
      congr 1; ring
    rw [hneg] at key
    linarith [key]


/-- **A compactness engine for level crossings.**  If a continuous function `f` decreases strictly
backwards in time along the flow at every point of the region `{a ≤ f} ∩ {c ≤ g}`, and the backward
trajectory of `x` stays in `{c ≤ g}`, then it must reach the level `a`. -/
theorem flow_level_engine
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) {φ : X → ℝ → X}
    (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
    (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
    {a c : ℝ} {x : X}
    (hdec : ∀ y : X, a ≤ f y → c ≤ g y →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)
    (hstay : ∀ t : ℝ, 0 ≤ t → c ≤ g (φ x (-t)))
    (hxf : a < f x) :
    ∃ t : ℝ, 0 ≤ t ∧ f (φ x (-t)) ≤ a := by
  by_contra hcon
  push_neg at hcon
  set W : ℝ → X := fun t : ℝ => φ x (-t) with hWdef
  set O : Set X := W '' Set.Ici (0:ℝ) with hOdef
  set L : ℝ := sInf (f '' O) with hLdef
  have hOne : O.Nonempty := ⟨W 0, (0:ℝ), Set.mem_Ici.mpr le_rfl, rfl⟩
  have hSne : (f '' O).Nonempty := hOne.image f
  have hbdd : BddBelow (f '' O) := by
    refine ⟨a, ?_⟩
    rintro v ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact (hcon t ht).le
  have hLle : ∀ t : ℝ, 0 ≤ t → L ≤ f (W t) := by
    intro t ht
    rw [hLdef]
    exact csInf_le hbdd ⟨W t, ⟨t, ht, rfl⟩, rfl⟩
  have hLge : a ≤ L := by
    rw [hLdef]
    refine le_csInf hSne ?_
    rintro v ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact (hcon t ht).le
  have happrox : ∀ ε > 0, ∃ t : ℝ, 0 ≤ t ∧ f (W t) < L + ε := by
    intro ε hε
    have h1 : L < L + ε := by linarith
    rw [hLdef] at h1
    obtain ⟨v, hv, hlt⟩ := exists_lt_of_csInf_lt hSne h1
    obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨t, ht, hlt⟩
  have hKc : IsCompact (closure O) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hne : (closure O ∩ ⋂ n : ℕ, {y : X | f y ≤ L + 1 / ((n:ℝ) + 1)}).Nonempty := by
    refine hKc.inter_iInter_nonempty _ (fun n => isClosed_le hf continuous_const) ?_
    intro u
    obtain ⟨t, ht, hlt⟩ := happrox (1 / (((u.sup id : ℕ) : ℝ) + 1)) (by positivity)
    refine ⟨W t, subset_closure ⟨t, ht, rfl⟩, ?_⟩
    rw [Set.mem_iInter]
    intro n
    rw [Set.mem_iInter]
    intro hn
    show f (W t) ≤ L + 1 / ((n:ℝ) + 1)
    have hnc : n ∈ u := hn
    have hnle : (n : ℝ) + 1 ≤ ((u.sup id : ℕ) : ℝ) + 1 := by
      have h1 := Finset.le_sup (f := fun n : ℕ => n) hnc
      have h2 : (n : ℝ) ≤ ((u.sup id : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have h3 : 1 / (((u.sup id : ℕ) : ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hnle
    linarith
  obtain ⟨z, hzcl, hzint⟩ := hne
  have hfz_le : f z ≤ L := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    have hn' : 1 / ((n:ℝ) + 1) ≤ ε := by
      have h2 : (1:ℝ) / ε < (n:ℝ) := hn
      have h3 : 1 < ε * (n:ℝ) := by
        rw [div_lt_iff₀ hε] at h2
        linarith
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
      nlinarith
    have h4 : f z ≤ L + 1 / ((n:ℝ) + 1) := mem_iInter.mp hzint n
    linarith
  have hfz_ge : L ≤ f z := by
    have hsub : O ⊆ {y : X | L ≤ f y} := by
      rintro y ⟨t, ht, rfl⟩
      exact hLle t ht
    exact closure_minimal hsub (isClosed_le continuous_const hf) hzcl
  have hfz : f z = L := le_antisymm hfz_le hfz_ge
  have hgz : c ≤ g z := by
    have hsub : O ⊆ {y : X | c ≤ g y} := by
      rintro y ⟨t, ht, rfl⟩
      exact hstay t ht
    exact closure_minimal hsub (isClosed_le continuous_const hg) hzcl
  obtain ⟨δ, hδ, hδ'⟩ := hdec z (by rw [hfz]; exact hLge) hgz
  have hcont' : Continuous fun y : X => f (φ y (-(δ/2))) :=
    hf.comp (hφcont.comp (continuous_id.prodMk continuous_const))
  have hneigh : {y : X | f (φ y (-(δ/2))) < L} ∈ 𝓝 z :=
    hcont'.continuousAt (isOpen_Iio.mem_nhds (by
      have h1 := hδ' (δ/2) ⟨by linarith, by linarith⟩
      rw [hfz] at h1
      exact h1))
  obtain ⟨y, hyN, hyO⟩ := mem_closure_iff_nhds.mp hzcl _ hneigh
  obtain ⟨t, ht, rfl⟩ := hyO
  have hval : f (W (t + δ/2)) < L := by
    have heq : φ (φ x (-t)) (-(δ/2)) = φ x (-(t + δ/2)) := by
      rw [hφadd]
      congr 1
      ring
    have h1 : f (φ (φ x (-t)) (-(δ/2))) < L := hyN
    rw [heq] at h1
    simpa [hWdef] using h1
  have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
  have h2 := hLle (t + δ/2) (by linarith)
  linarith

theorem tau
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D a γ v : ℝ} (ha : 0 < a) (hg : 0 < γ)
    (haD : a < D) (h2a : 2 * a < v) (h2g : 2 * γ < v) (h5g : 5 * γ / 2 ≤ v)
    (hsep1 : a + γ / 8 < D) (hsep2 : 3 * a / 2 + γ / 4 < D)
    (hsep3 : 3 * a / 2 + 5 * γ / 2 < D)
    (hDGt : Real.pi / 2 < D) (hDLt : D < Real.pi)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (htri : ∀ y : M, D ≤ Work.Diff.C.rdist (I := I) (M := M) p y +
      Work.Diff.C.rdist (I := I) (M := M) q y)
    (hsmP : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v →
      CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hasc : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Submission.GSField.IsAscentAt hmet p y (V y))
    (hnz : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 8 ≤ Work.Diff.C.rdist (I := I) (M := M) q y → V y ≠ 0)
    (hval : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ 3 * a / 2 →
      V y = Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y)
    (hvalq : ∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
      V y = - Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y) :
    ∃ τ : M → ℝ,
      ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ
        {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
          γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x} ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-(τ x)) x) = a) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ∀ t : ℝ,
        Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 t x) = a → t = -(τ x)) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2 →
        τ x = Work.Diff.C.rdist (I := I) (M := M) p x - a) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        3 * a / 2 ≤ Work.Diff.C.rdist (I := I) (M := M) p x → a / 2 ≤ τ x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ∀ s : ℝ, 0 ≤ s →
        a / 4 < Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) →
        τ (Φ 0 s x) = τ x + s) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        mfderiv I 𝓘(ℝ,ℝ) τ x (V x) = 1) := by
  classical
  -- ## Setup
  set F : M → ℝ := fun y : M => Work.Diff.C.rdist (I := I) (M := M) p y with hFdef
  set G : M → ℝ := fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y with hGdef
  set A : Set M := {x : M | a / 4 < F x ∧ γ / 4 < G x} with hAdef
  have hFcont : Continuous F := Work.Diff.C.rdist_continuous (I := I) (M := M) p
  have hGcont : Continuous G := Work.Diff.C.rdist_continuous (I := I) (M := M) q
  have hAopen : IsOpen A := by
    rw [hAdef]
    exact (isOpen_lt continuous_const hFcont).inter (isOpen_lt continuous_const hGcont)
  have ha4 : (0:ℝ) < a / 4 := by linarith
  have hg4 : (0:ℝ) < γ / 4 := by linarith
  have hg8g4 : γ / 8 < γ / 4 := by linarith
  have hc12 : a / 4 < 3 * a / 2 := by linarith
  have ha_le : a / 4 ≤ a := by linarith
  have ha32 : a ≤ 3 * a / 2 := by linarith
  have h3av : 3 * a / 2 < v := by linarith
  -- ## flow data
  have hφ0 : ∀ x : M, Φ 0 0 x = x := fun x => hΦself 0 x
  have hφadd : ∀ (x : M) (s t : ℝ), Φ 0 t (Φ 0 s x) = Φ 0 (s + t) x :=
    fun x s t => Work.Diff.Dim2.flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv s t x
  have hφcontC : Continuous fun q : M × ℝ => Φ 0 q.2 q.1 := by
    have h1 : Continuous fun q : M × ℝ => ((((0:ℝ), q.2) : ℝ × ℝ), q.1) :=
      (continuous_const.prodMk continuous_snd).prodMk continuous_fst
    exact hΦsm.continuous.comp h1
  -- ## basic facts about F and G
  have hFle : ∀ y : M, F y ≤ D := by
    intro y
    have h1 : Manifold.riemannianEDist I p y ≤ ENNReal.ofReal D := hdiam p y
    have h2 : (Manifold.riemannianEDist I p y).toReal ≤ (ENNReal.ofReal D).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    have h3 : (ENNReal.ofReal D).toReal = D := ENNReal.toReal_ofReal (by
      linarith [hDGt, Real.pi_pos])
    show (Manifold.riemannianEDist I p y).toReal ≤ D
    rw [← h3]
    exact h2
  have hFnn : ∀ y : M, 0 ≤ F y := fun y => ENNReal.toReal_nonneg
  have hFsm : ∀ y : M, 0 < F y → F y < v → ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F y :=
    fun y h1 h2 => hsmP y h1 h2
  have hGsm : ∀ y : M, 0 < G y → G y < v → ContMDiffAt I 𝓘(ℝ,ℝ) ∞ G y :=
    fun y h1 h2 => hsmQ y h1 h2
  -- ## the derivative of F (resp. G) along V on the annuli
  have hdV : ∀ y : M, a / 4 ≤ F y → F y ≤ 3 * a / 2 → (mvfderiv I F y) (V y) = 1 := by
    intro y h1 h2
    have hpos : 0 < F y := by linarith
    have hlt : F y < v := by linarith
    have hsm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F y := hFsm y hpos hlt
    have heik : Inner.inner ℝ (Work.Diff.C.rgrad F y) (Work.Diff.C.rgrad F y) = 1 :=
      Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) hmet htor hpos.ne' hsm
    have hval' : V y = Work.Diff.C.rgrad F y := hval y (by simpa using h1) (by simpa using h2)
    have hinner : Inner.inner ℝ (Work.Diff.C.rgrad F y) (V y) = 1 := by
      rw [hval', heik]
    have hir := Work.Diff.C.inner_rgrad (I := I) (M := M) F y (V y)
    exact hir.symm.trans hinner
  have hdVq : ∀ y : M, γ / 4 ≤ G y → G y ≤ 5 * γ / 2 → G y < v →
      (mvfderiv I G y) (V y) = -1 := by
    intro y h1 h2 h3
    have hpos : 0 < G y := by linarith
    have hsm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ G y := hGsm y hpos h3
    have heik : Inner.inner ℝ (Work.Diff.C.rgrad G y) (Work.Diff.C.rgrad G y) = 1 :=
      Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) hmet htor hpos.ne' hsm
    have hval' : V y = - Work.Diff.C.rgrad G y := hvalq y (by simpa using h1) (by simpa using h2)
    have hinner : Inner.inner ℝ (Work.Diff.C.rgrad G y) (V y) = -1 := by
      rw [hval', inner_neg_right, heik]
    have hir := Work.Diff.C.inner_rgrad (I := I) (M := M) G y (V y)
    exact hir.symm.trans hinner
  -- ## the derivative of the flow curve composed with F / G
  have hderiv_flowF : ∀ y : M, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F y →
      HasDerivAt (fun s : ℝ => F (Φ 0 s y)) ((mvfderiv I F y) (V y)) 0 := by
    intro y hFy
    have hfl : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ y) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V y)) := by
      have h := hΦderiv 0 0 y
      rw [hΦself 0 y] at h
      exact h
    have hFmd : MDifferentiableAt I 𝓘(ℝ,ℝ) F y := hFy.mdifferentiableAt (by simp)
    have hFmd' : HasMFDerivAt I 𝓘(ℝ,ℝ) F (Φ 0 0 y) (mfderiv I 𝓘(ℝ,ℝ) F y) := by
      rw [hΦself 0 y]; exact hFmd.hasMFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (F ∘ fun τ : ℝ => Φ 0 τ y) 0
        ((mfderiv I 𝓘(ℝ,ℝ) F y) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V y))) :=
      hFmd'.comp (0 : ℝ) hfl
    have hCLeq : (mfderiv I 𝓘(ℝ,ℝ) F y) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V y))
        = (1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I F y) (V y)) := by
      apply ContinuousLinearMap.ext
      intro c
      show (mfderiv I 𝓘(ℝ,ℝ) F y) (((1 : ℝ →L[ℝ] ℝ).smulRight (V y)) c)
          = ((1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I F y) (V y))) c
      have hA : ((1 : ℝ →L[ℝ] ℝ).smulRight (V y)) c = c • V y := by
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
      have hB : ((1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I F y) (V y))) c
          = c • ((mvfderiv I F y) (V y)) := by
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
      rw [hA, hB, map_smul]
      rfl
    have hfd : HasFDerivAt (F ∘ fun τ : ℝ => Φ 0 τ y)
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I F y) (V y))) 0 := by
      rw [← hCLeq]
      exact hcomp.hasFDerivAt
    have h1 : HasDerivAt (F ∘ fun τ : ℝ => Φ 0 τ y) ((mvfderiv I F y) (V y)) 0 := by
      simpa [ContinuousLinearMap.smulRight_apply] using hfd.hasDerivAt
    have hfun : (F ∘ fun τ : ℝ => Φ 0 τ y) = (fun s : ℝ => F (Φ 0 s y)) := rfl
    rw [hfun] at h1
    exact h1
  have hderiv_flowG : ∀ y : M, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ G y →
      HasDerivAt (fun s : ℝ => G (Φ 0 s y)) ((mvfderiv I G y) (V y)) 0 := by
    intro y hGy
    have hfl : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ y) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V y)) := by
      have h := hΦderiv 0 0 y
      rw [hΦself 0 y] at h
      exact h
    have hGmd : MDifferentiableAt I 𝓘(ℝ,ℝ) G y := hGy.mdifferentiableAt (by simp)
    have hGmd' : HasMFDerivAt I 𝓘(ℝ,ℝ) G (Φ 0 0 y) (mfderiv I 𝓘(ℝ,ℝ) G y) := by
      rw [hΦself 0 y]; exact hGmd.hasMFDerivAt
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (G ∘ fun τ : ℝ => Φ 0 τ y) 0
        ((mfderiv I 𝓘(ℝ,ℝ) G y) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V y))) :=
      hGmd'.comp (0 : ℝ) hfl
    have hCLeq : (mfderiv I 𝓘(ℝ,ℝ) G y) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V y))
        = (1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I G y) (V y)) := by
      apply ContinuousLinearMap.ext
      intro c
      show (mfderiv I 𝓘(ℝ,ℝ) G y) (((1 : ℝ →L[ℝ] ℝ).smulRight (V y)) c)
          = ((1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I G y) (V y))) c
      have hA : ((1 : ℝ →L[ℝ] ℝ).smulRight (V y)) c = c • V y := by
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
      have hB : ((1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I G y) (V y))) c
          = c • ((mvfderiv I G y) (V y)) := by
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
      rw [hA, hB, map_smul]
      rfl
    have hfd : HasFDerivAt (G ∘ fun τ : ℝ => Φ 0 τ y)
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((mvfderiv I G y) (V y))) 0 := by
      rw [← hCLeq]
      exact hcomp.hasFDerivAt
    have h1 : HasDerivAt (G ∘ fun τ : ℝ => Φ 0 τ y) ((mvfderiv I G y) (V y)) 0 := by
      simpa [ContinuousLinearMap.smulRight_apply] using hfd.hasDerivAt
    have hfun : (G ∘ fun τ : ℝ => Φ 0 τ y) = (fun s : ℝ => G (Φ 0 s y)) := rfl
    rw [hfun] at h1
    exact h1
  -- ## unit speed in the F-annulus
  have hu_ann : ∀ y : M, a / 4 ≤ F y → F y ≤ 3 * a / 2 →
      HasDerivAt (fun s : ℝ => F (Φ 0 s y)) 1 0 := by
    intro y h1 h2
    have hpos : 0 < F y := by linarith
    have hlt : F y < v := by linarith
    have hd := hderiv_flowF y (hFsm y hpos hlt)
    rwa [hdV y h1 h2] at hd
  -- ## the local decrease hypothesis at any level above `a / 4`
  have hdec_gen : ∀ (Lv : ℝ), a / 4 ≤ Lv → ∀ y : M, Lv ≤ F y → γ / 4 ≤ G y →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Ioo (0:ℝ) δ, F (Φ 0 (-s) y) < F y := by
    intro Lv hLv y h1 h2
    have hasc' : Submission.GSField.IsAscentAt hmet p y (V y) :=
      hasc y (by show a / 4 ≤ F y; linarith) (by show γ / 8 < G y; linarith)
    have hσ0 : (fun s : ℝ => Φ 0 (-s) y) 0 = y := by
      simp only [neg_zero]
      exact hΦself 0 y
    have hσsm : ContMDiffAt 𝓘(ℝ,ℝ) I ∞ (fun s : ℝ => Φ 0 (-s) y) (0 : ℝ) := by
      have hneg : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => -s) (0 : ℝ) :=
        contMDiff_neg 𝓘(ℝ,ℝ) ∞ (0 : ℝ)
      have h1' : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
          (fun s : ℝ => (((0 : ℝ), -s) : ℝ × ℝ)) (0 : ℝ) :=
        ContMDiffAt.prodMk (contMDiffAt_const (c := (0 : ℝ)) (x := (0 : ℝ))) hneg
      have h2' : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
          (fun s : ℝ => ((((0 : ℝ), -s) : ℝ × ℝ), y)) (0 : ℝ) :=
        ContMDiffAt.prodMk h1' (contMDiffAt_const (c := y) (x := (0 : ℝ)))
      have h3' : ContMDiffAt 𝓘(ℝ,ℝ) I ∞
          ((fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)
            ∘ fun s : ℝ => ((((0 : ℝ), -s) : ℝ × ℝ), y)) (0 : ℝ) :=
        ContMDiffAt.comp (0 : ℝ) (hΦsm ((((0 : ℝ), -(0 : ℝ)) : ℝ × ℝ), y)) h2'
      exact h3'
    have hσv : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => Φ 0 (-s) y) 0 = - V y := by
      have hg : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ y) (-(0 : ℝ))
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y))) :=
        hΦderiv 0 (-(0 : ℝ)) y
      have hn : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) (0 : ℝ)
          (-(1 : ℝ →L[ℝ] ℝ)) :=
        (hasMFDerivAt_id (I := 𝓘(ℝ,ℝ)) (0 : ℝ)).neg
      have hcomp := hg.comp (0 : ℝ) hn
      have hNval : (-(1 : ℝ →L[ℝ] ℝ)) (1 : ℝ) = -(1 : ℝ) := by
        rw [neg_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
      have hGval : ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y))) (-(1 : ℝ))
          = - V (Φ 0 (-(0 : ℝ)) y) := by
        rw [ContinuousLinearMap.smulRight_apply]
        rw [show (1 : ℝ →L[ℝ] ℝ) (-(1 : ℝ)) = -(1 : ℝ) by
          rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]]
        rw [neg_one_smul]
      have hself' : Φ 0 (-(0 : ℝ)) y = y := by
        rw [neg_zero]; exact hΦself 0 y
      have hfun : (fun s : ℝ => Φ 0 (-s) y)
          = ((fun τ : ℝ => Φ 0 τ y) ∘ (fun s : ℝ => -s)) := rfl
      rw [Submission.Geodesic.curveVelocity_apply, hfun, hcomp.mfderiv]
      change ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y)))
          ((-(1 : ℝ →L[ℝ] ℝ)) (1 : ℝ)) = - V y
      rw [hNval, hGval, hself']
    obtain ⟨δ, hδ, hδ'⟩ := Submission.GSFlow.flow_left_lt (cov := cov) hmet htor hpinch
      hasc' hσ0 hσsm hσv
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have hfin1 : Manifold.riemannianEDist I p (Φ 0 (-s) y) ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
    have hfin2 : Manifold.riemannianEDist I p y ≠ ⊤ :=
      (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
    exact (ENNReal.toReal_lt_toReal hfin1 hfin2).mpr (hδ' s hs)
  -- ## the backward trajectory of a point of `{γ/4 < G}` stays in `{γ/4 < G}`
  have hstayG : ∀ x : M, γ / 4 < G x → ∀ t : ℝ, 0 ≤ t → γ / 4 < G (Φ 0 (-t) x) := by
    intro x hx t ht
    by_contra hcon
    push_neg at hcon
    set Z : Set ℝ := {s : ℝ | 0 ≤ s ∧ G (Φ 0 (-s) x) ≤ γ / 4} with hZdef
    have hZne : Z.Nonempty := ⟨t, ht, hcon⟩
    have hZbdd : BddBelow Z := ⟨0, fun s hs => hs.1⟩
    have hcontZ : Continuous fun s : ℝ => G (Φ 0 (-s) x) :=
      hGcont.comp (hφcontC.comp (continuous_const.prodMk continuous_neg))
    have hZcl : IsClosed Z := by
      rw [hZdef]
      exact IsClosed.inter isClosed_Ici (isClosed_le hcontZ continuous_const)
    set s₁ : ℝ := sInf Z with hs₁def
    have hs₁Z : s₁ ∈ Z := hZcl.csInf_mem hZne hZbdd
    have hs₁pos : 0 < s₁ := by
      rcases lt_or_eq_of_le hs₁Z.1 with h | h
      · exact h
      · exfalso
        rw [← h, hZdef] at hs₁Z
        have h1 : G (Φ 0 (-(0:ℝ)) x) ≤ γ / 4 := hs₁Z.2
        rw [neg_zero, hΦself 0 x] at h1
        linarith [h1, hx]
    have hGval : G (Φ 0 (-s₁) x) = γ / 4 := by
      refine le_antisymm hs₁Z.2 ?_
      have hlt : ∀ s ∈ Set.Ioo (0:ℝ) s₁, γ / 4 < G (Φ 0 (-s) x) := by
        intro s hs
        by_contra hc
        push_neg at hc
        have hmem : s ∈ Z := ⟨hs.1.le, hc⟩
        have h1 := csInf_le hZbdd hmem
        rw [← hs₁def] at h1
        linarith [h1, hs.2]
      have htend : Tendsto (fun s : ℝ => G (Φ 0 (-s) x)) (𝓝[<] s₁)
          (𝓝 (G (Φ 0 (-s₁) x))) := hcontZ.continuousAt.tendsto.mono_left inf_le_left
      have hge : ∀ᶠ s in 𝓝[<] s₁, γ / 4 ≤ G (Φ 0 (-s) x) := by
        filter_upwards [Commons.Topology.Order.Ioo_mem_nhdsWithin_lt (show max 0 (s₁ - 1) < s₁ by
          exact max_lt hs₁pos (by linarith))] with s hs
        exact (hlt s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩).le
      exact ge_of_tendsto htend hge
    set w : M := Φ 0 (-s₁) x with hwdef
    have hGw : G w = γ / 4 := hGval
    have hVw : V w = - Work.Diff.C.rgrad G w := hvalq w
      (by show γ / 4 ≤ G w; rw [hGw]) (by show G w ≤ 5 * γ / 2; rw [hGw]; linarith)
    have hwsm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ G w := hGsm w (by rw [hGw]; linarith) (by rw [hGw]; linarith)
    have hderiv_w : HasDerivAt (fun σ : ℝ => G (Φ 0 (-σ) w)) 1 0 := by
      have hfwd := hderiv_flowG w hwsm
      have hbase : HasDerivAt (fun s : ℝ => G (Φ 0 s w)) ((mvfderiv I G w) (V w)) 0 := hfwd
      have hbase' : HasDerivAt (fun s : ℝ => G (Φ 0 s w)) ((mvfderiv I G w) (V w))
          ((fun σ : ℝ => -σ) 0) := by simpa using hbase
      have hneg : HasDerivAt (fun σ : ℝ => -σ) (-1) 0 := hasDerivAt_neg (0:ℝ)
      have hcomp := hbase'.comp 0 hneg
      have hV : (mvfderiv I G w) (V w) = -1 := hdVq w
        (by show γ / 4 ≤ G w; rw [hGw]) (by show G w ≤ 5 * γ / 2; rw [hGw]; linarith)
        (by show G w < v; rw [hGw]; linarith [h2g])
      rw [hV] at hcomp
      have hfin : HasDerivAt (fun σ : ℝ => G (Φ 0 (-σ) w)) ((-1) * (-1)) 0 := hcomp
      simpa using hfin
    obtain ⟨δ, hδ, hδ'⟩ := local_mono_of_hasDerivAt hderiv_w one_pos
    set τ' : ℝ := min δ s₁ / 2 with hτ'def
    have hτ'pos : 0 < τ' := by rw [hτ'def]; exact half_pos (lt_min hδ hs₁pos)
    have hτ'δ : τ' < δ := by rw [hτ'def]; linarith [min_le_left δ s₁]
    have hτ's : τ' < s₁ := by rw [hτ'def]; linarith [min_le_right δ s₁]
    have hmem : s₁ - τ' ∈ Z := by
      refine ⟨by linarith, ?_⟩
      have h1 := (hδ' τ' ⟨hτ'pos, hτ'δ⟩).1
      have h2 : G (Φ 0 τ' w) < G (Φ 0 0 w) := by simpa using h1
      rw [hΦself 0 w] at h2
      have heq : Φ 0 τ' w = Φ 0 (-(s₁ - τ')) x := by
        rw [hwdef, hφadd]
        congr 1
        ring
      rw [heq, hGw] at h2
      exact h2.le
    have h1 := csInf_le hZbdd hmem
    rw [← hs₁def] at h1
    linarith
  -- ## existence of a crossing time
  have hcross_ann : ∀ x : M, x ∈ A → F x ≤ a → ∃ t : ℝ, F (Φ 0 t x) = a := by
    intro x hx hle
    have hann := flow_cross_annulus (f := F) (φ := fun y : M => fun t : ℝ => Φ 0 t y)
      hFcont hφcontC hφ0 hφadd hc12 hu_ann (x := x) (ℓ := a) hx.1.le (by linarith) ha_le ha32
    exact ⟨a - F x, hann⟩
  have hex_far : ∀ x : M, x ∈ A → a < F x → ∃ t : ℝ, F (Φ 0 t x) = a := by
    intro x hx hlt
    obtain ⟨t, ht, hle⟩ := flow_level_engine (f := F) (g := G)
      (φ := fun y : M => fun t : ℝ => Φ 0 t y) (a := a) (c := γ / 4) (x := x)
      hFcont hGcont hφcontC hφadd (hdec_gen a ha_le)
      (fun t ht => (hstayG x hx.2 t ht).le) hlt
    have hcont' : Continuous fun σ : ℝ => F (Φ 0 σ x) :=
      hFcont.comp (hφcontC.comp (continuous_const.prodMk continuous_id))
    have hmem : a ∈ Set.Icc (F (Φ 0 (-t) x)) (F (Φ 0 0 x)) := by
      rw [hφ0 x]
      exact ⟨hle, hlt.le⟩
    obtain ⟨σ, hσ, hσv⟩ := (mem_image ..).mp
      ((intermediate_value_Icc (by linarith : -t ≤ 0) hcont'.continuousOn) hmem)
    exact ⟨σ, hσv⟩
  have hex : ∀ x : M, x ∈ A → ∃ t : ℝ, F (Φ 0 t x) = a := by
    intro x hx
    rcases lt_or_ge a (F x) with h | h
    · exact hex_far x hx h
    · exact hcross_ann x hx h
  have huniq : ∀ x : M, ∀ t t' : ℝ, F (Φ 0 t x) = a → F (Φ 0 t' x) = a → t = t' :=
    crossing_unique_of_deriv hFcont hφcontC hφ0 hφadd (ℓ := a)
      (fun y hy => hu_ann y (by rw [hy]; linarith) (by rw [hy]; linarith))
  -- ## smoothness at the level points
  have hFsmooth : ∀ y : M, F y = a → ContMDiffAt I 𝓘(ℝ,ℝ) ∞ F y := by
    intro y hy
    have hy4 : 0 < F y := by rw [hy]; linarith
    have hyv : F y < v := by rw [hy]; linarith
    exact hsmP y (by simpa using hy4) (by simpa using hyv)
  have htrans : ∀ y : M, F y = a → (mvfderiv I F y) (V y) ≠ 0 := by
    intro y hy
    have h1 : a / 4 ≤ F y := by rw [hy]; linarith
    have h2 : F y ≤ 3 * a / 2 := by rw [hy]; linarith
    rw [hdV y h1 h2]
    norm_num
  obtain ⟨T, hTsm, hTval, hTuniq⟩ := Work.Diff.Dim2.crossing_time (V := V) (Φ := Φ)
    (F := F) (ℓ := a) (A := A) hVsm hΦsm hΦself hΦderiv hFsmooth htrans hex
    (fun x _ t t' ht ht' => huniq x t t' ht ht')
  -- ## the conjuncts about `τ = -T`
  have hτval : ∀ x : M, x ∈ A → F (Φ 0 (T x) x) = a := fun x hx => hTval x hx
  have hτuniq : ∀ x : M, x ∈ A → ∀ t : ℝ, F (Φ 0 t x) = a → t = T x :=
    fun x hx t ht => hTuniq x hx t ht
  have hτshift : ∀ x : M, x ∈ A → ∀ s : ℝ, 0 ≤ s → Φ 0 s x ∈ A →
      -(T (Φ 0 s x)) = -(T x) + s := by
    intro x hx s hs hsA
    have hcomp : Φ 0 (T x - s) (Φ 0 s x) = Φ 0 (T x) x := by
      rw [hφadd]
      have h1 : s + (T x - s) = T x := by ring
      rw [h1]
    have hvaly : F (Φ 0 (T x - s) (Φ 0 s x)) = a := by
      rw [hcomp]
      exact hτval x hx
    have hT' : T x - s = T (Φ 0 s x) := hτuniq (Φ 0 s x) hsA (T x - s) hvaly
    rw [← hT']
    ring
  have hτann : ∀ x : M, x ∈ A → F x ≤ 3 * a / 2 → -(T x) = F x - a := by
    intro x hx hle
    have hann := flow_cross_annulus (f := F) (φ := fun y : M => fun t : ℝ => Φ 0 t y)
      hFcont hφcontC hφ0 hφadd hc12 hu_ann (x := x) (ℓ := a) hx.1.le hle ha_le ha32
    have hT := hτuniq x hx (a - F x) hann
    linarith
  have hτhalf : ∀ x : M, x ∈ A → 3 * a / 2 ≤ F x → a / 2 ≤ -(T x) := by
    intro x hx h3
    have hcont' : Continuous fun σ : ℝ => F (Φ 0 σ x) :=
      hFcont.comp (hφcontC.comp (continuous_const.prodMk continuous_id))
    have hle3 : ∃ t : ℝ, 0 ≤ t ∧ F (Φ 0 (-t) x) ≤ 3 * a / 2 := by
      rcases lt_or_eq_of_le h3 with hlt | heq
      · exact flow_level_engine (f := F) (g := G)
          (φ := fun y : M => fun t : ℝ => Φ 0 t y) (a := 3 * a / 2) (c := γ / 4) (x := x)
          hFcont hGcont hφcontC hφadd (hdec_gen (3 * a / 2) (by linarith))
          (fun t ht => (hstayG x hx.2 t ht).le) hlt
      · exact ⟨0, le_rfl, by rw [neg_zero, hφ0 x, heq]⟩
    set Z : Set ℝ := {s : ℝ | 0 ≤ s ∧ F (Φ 0 (-s) x) ≤ 3 * a / 2} with hZdef
    have hZne : Z.Nonempty := hle3
    have hZbdd : BddBelow Z := ⟨0, fun s hs => hs.1⟩
    have hcontZ : Continuous fun s : ℝ => F (Φ 0 (-s) x) :=
      hcont'.comp continuous_neg
    have hZcl : IsClosed Z := by
      rw [hZdef]
      exact IsClosed.inter isClosed_Ici (isClosed_le hcontZ continuous_const)
    set s₁ : ℝ := sInf Z with hs₁def
    have hs₁Z : s₁ ∈ Z := hZcl.csInf_mem hZne hZbdd
    have hs₁val : F (Φ 0 (-s₁) x) = 3 * a / 2 := by
      refine le_antisymm hs₁Z.2 ?_
      rcases eq_or_lt_of_le hs₁Z.1 with h0 | hpos
      · rw [← h0, neg_zero, hφ0 x]
        exact h3
      · have hlt : ∀ s ∈ Set.Ioo (0:ℝ) s₁, 3 * a / 2 < F (Φ 0 (-s) x) := by
          intro s hs
          by_contra hc
          push_neg at hc
          have hmem : s ∈ Z := ⟨hs.1.le, hc⟩
          have h1 := csInf_le hZbdd hmem
          rw [← hs₁def] at h1
          linarith [h1, hs.2]
        have htend : Tendsto (fun s : ℝ => F (Φ 0 (-s) x)) (𝓝[<] s₁)
            (𝓝 (F (Φ 0 (-s₁) x))) := hcontZ.continuousAt.tendsto.mono_left inf_le_left
        have hge : ∀ᶠ s in 𝓝[<] s₁, 3 * a / 2 ≤ F (Φ 0 (-s) x) := by
          filter_upwards [Commons.Topology.Order.Ioo_mem_nhdsWithin_lt (show max 0 (s₁ - 1) < s₁ by
            exact max_lt hpos (by linarith))] with s hs
          exact (hlt s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩).le
        exact ge_of_tendsto htend hge
    set y : M := Φ 0 (-s₁) x with hydef
    have hyval : F y = 3 * a / 2 := by rw [hydef]; exact hs₁val
    have hs₁0 : 0 ≤ s₁ := hs₁Z.1
    have hann := flow_cross_annulus (f := F) (φ := fun z : M => fun t : ℝ => Φ 0 t z)
      hFcont hφcontC hφ0 hφadd hc12 hu_ann (x := y) (ℓ := a)
      (by rw [hyval]; linarith) (by rw [hyval]) ha_le ha32
    have hcross : F (Φ 0 (-(s₁ + a / 2)) x) = a := by
      have heq : Φ 0 (a - F y) y = Φ 0 (-(s₁ + a / 2)) x := by
        rw [hydef, hφadd]
        have h1 : -s₁ + (a - F y) = -(s₁ + a / 2) := by rw [hyval]; ring
        rw [h1]
      rw [← heq]
      exact hann
    have hT := hτuniq x hx (-(s₁ + a / 2)) hcross
    linarith [hT, hs₁0]
  refine ⟨fun x : M => -T x, hTsm.neg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    simpa using hτval x ⟨h1, h2⟩
  · intro x h1 h2 t ht
    simpa using hτuniq x ⟨h1, h2⟩ t ht
  · intro x h1 h2
    have hG : γ / 4 < G x := by
      have h := htri x
      linarith [hsep2]
    exact hτann x ⟨h1, hG⟩ h2
  · intro x h1 h2 h3
    exact hτhalf x ⟨h1, h2⟩ h3
  · intro x h1 h2 s hs h1' h2'
    exact hτshift x ⟨h1, h2⟩ s hs ⟨h1', h2'⟩
  · -- the derivative of `τ` along `V`
    intro x h1 h2
    have hxA : x ∈ A := ⟨h1, h2⟩
    have hτmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun x : M => -T x) x :=
      ((hTsm.contMDiffAt (hAopen.mem_nhds hxA)).neg).mdifferentiableAt (by simp)
    -- step 1: the derivative of the flow line
    have hchain : HasDerivWithinAt (fun s : ℝ => -(T (Φ 0 s x)))
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x))) 1) (Set.Ici (0:ℝ)) 0 := by
      have hcurve : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) := by
        have h := hΦderiv 0 0 x
        rw [hΦself 0 x] at h
        exact h
      have hτmd' : HasMFDerivAt I 𝓘(ℝ,ℝ) (fun y : M => -T y) (Φ 0 0 x)
          (mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) := by
        rw [hφ0 x]; exact hτmd.hasMFDerivAt
      have hcomp := hτmd'.comp 0 hcurve
      have hCLeq : (mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) ∘L ((1 : ℝ →L[ℝ] ℝ).smulRight (V x))
          = (1 : ℝ →L[ℝ] ℝ).smulRight ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x)) := by
        apply ContinuousLinearMap.ext
        intro c
        show (mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) c)
            = ((1 : ℝ →L[ℝ] ℝ).smulRight ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x))) c
        have hA : ((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) c = c • V x := by
          rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
        have hB : ((1 : ℝ →L[ℝ] ℝ).smulRight ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x))) c
            = c • ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x)) := by
          rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
        rw [hA, hB, map_smul]
      have hfd : HasFDerivAt (fun s : ℝ => -(T (Φ 0 s x)))
          ((1 : ℝ →L[ℝ] ℝ).smulRight ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x))) 0 :=
        hCLeq ▸ hcomp.hasFDerivAt
      exact hfd.hasDerivAt.hasDerivWithinAt
    -- step 2: the derivative is also `1` because the flow shifts `τ` by `s`
    have hev1 : ∀ᶠ s in 𝓝 (0:ℝ), a / 4 < F (Φ 0 s x) := by
      have hcont1 : Continuous fun s : ℝ => F (Φ 0 s x) :=
        hFcont.comp (hφcontC.comp (continuous_const.prodMk continuous_id))
      have h0 : a / 4 < F (Φ 0 0 x) := by rw [hφ0 x]; exact h1
      exact hcont1.continuousAt.eventually (isOpen_Ioi.mem_nhds h0)
    have hev2 : ∀ᶠ s in 𝓝 (0:ℝ), γ / 4 < G (Φ 0 s x) := by
      have hcont2 : Continuous fun s : ℝ => G (Φ 0 s x) :=
        hGcont.comp (hφcontC.comp (continuous_const.prodMk continuous_id))
      have h0 : γ / 4 < G (Φ 0 0 x) := by rw [hφ0 x]; exact h2
      exact hcont2.continuousAt.eventually (isOpen_Ioi.mem_nhds h0)
    have heq_ev : (fun s : ℝ => -(T (Φ 0 s x))) =ᶠ[𝓝[≥] (0:ℝ)]
        (fun s : ℝ => -(T x) + s) := by
      have hmem : ∀ᶠ s in 𝓝 (0:ℝ), a / 4 < F (Φ 0 s x) ∧ γ / 4 < G (Φ 0 s x) :=
        hev1.and hev2
      filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with s hs hs0
      exact hτshift x hxA s hs0 ⟨hs.1, hs.2⟩
    have hright : HasDerivWithinAt (fun s : ℝ => -(T (Φ 0 s x))) 1 (Set.Ici (0:ℝ)) 0 := by
      have hlin : HasDerivWithinAt (fun s : ℝ => -(T x) + s) 1 (Set.Ici (0:ℝ)) 0 := by
        have h1' : HasDerivAt (fun s : ℝ => -(T x) + s) 1 0 := by
          simpa using (hasDerivAt_id (0:ℝ)).const_add (-(T x))
        exact h1'.hasDerivWithinAt
      refine hlin.congr_of_eventuallyEq ?_ ?_
      · exact heq_ev
      · simp [hφ0 x]
    have h1 := hchain.derivWithin (uniqueDiffWithinAt_Ici 0)
    have h2 := hright.derivWithin (uniqueDiffWithinAt_Ici 0)
    have h3 : ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x))) 1) = 1 := by
      rw [← h1, h2]
      try rfl
    have h4 : ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x))) 1)
        = (mfderiv I 𝓘(ℝ,ℝ) (fun y : M => -T y) x) (V x) := by
      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
    exact h4 ▸ h3


end Work.Diff.Dim2

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.glue_line_C1` (leaf B7a)

`GlueLineC1 h c r` states that a function `h : ℝ → ℝ → ℝ` which is `C¹` on the two open
half-strips `θ < c` and `θ > c`, continuous on the full strip `(0,∞) × (c-r,c+r)`, and whose
two partial derivatives have limits at every point `(z₀, c)` of the seam (approached along
the punctured strip), is `C¹` on the full strip and has continuous partial derivatives there.

The proof is the standard gluing-across-a-hypersurface argument.

* At a point of the seam one applies Mathlib's
  `hasFDerivWithinAt_closure_of_tendsto_fderiv` on the two convex open boxes lying below and
  above the seam; the two one-sided conclusions are merged with `HasFDerivWithinAt.union`.
  The union contains an open neighbourhood of the seam point, so the conclusion upgrades to
  an honest `HasFDerivAt`.
* Continuity of the derivative field is then: on the punctured strip it is Mathlib's
  continuity of `fderiv`, and at a seam point a closed-neighbourhood argument shows that the
  derivative-field's limit along the punctured strip at the seam point matches the
  (already established) value there, giving continuity along the whole strip.
-/

noncomputable section

open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §1 The two strips -/

/-- The punctured strip `(0,∞) × ((c-r,c) ∪ (c,c+r))` on which `h` is assumed `C¹`. -/
def glueS (c r : ℝ) : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))

/-- The full strip `(0,∞) × (c-r,c+r)`. -/
def glueU (c r : ℝ) : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ Ioo (c - r) (c + r)

theorem mem_glueU {c r z θ : ℝ} :
    (z, θ) ∈ glueU c r ↔ 0 < z ∧ c - r < θ ∧ θ < c + r := by
  simp [glueU, Set.mem_prod]

theorem mem_glueS {c r z θ : ℝ} :
    (z, θ) ∈ glueS c r ↔ 0 < z ∧ (c - r < θ ∧ θ < c ∨ c < θ ∧ θ < c + r) := by
  unfold glueS
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_union, Set.mem_Ioo]

theorem glueS_subset_glueU {c r : ℝ} (hr : 0 < r) : glueS c r ⊆ glueU c r := by
  rintro ⟨z, θ⟩ hp
  rw [mem_glueS] at hp
  rw [mem_glueU]
  refine ⟨hp.1, ?_, ?_⟩
  · rcases hp.2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · linarith
  · rcases hp.2 with ⟨_, h⟩ | ⟨_, h⟩
    · linarith
    · exact h

theorem isOpen_glueS (c r : ℝ) : IsOpen (glueS c r) :=
  isOpen_Ioi.prod (isOpen_Ioo.union isOpen_Ioo)

theorem isOpen_glueU (c r : ℝ) : IsOpen (glueU c r) :=
  isOpen_Ioi.prod isOpen_Ioo

theorem mem_glueS_of_mem_glueU_of_ne {c r : ℝ} {p : ℝ × ℝ} (hp : p ∈ glueU c r)
    (h : p.2 ≠ c) : p ∈ glueS c r := by
  rw [mem_glueU] at hp
  rw [mem_glueS]
  refine ⟨hp.1, ?_⟩
  rcases lt_trichotomy p.2 c with hlt | heq | hlt
  · exact Or.inl ⟨hp.2.1, hlt⟩
  · exact absurd heq h
  · exact Or.inr ⟨hlt, hp.2.2⟩

/-- The seam point `(z,c)`, `z > 0`, lies in the closure of the punctured strip. -/
theorem seam_mem_closure_glueS {c r : ℝ} (hr : 0 < r) {z : ℝ} (hz : 0 < z) :
    (z, c) ∈ closure (glueS c r) := by
  have hsub : Ioi (0 : ℝ) ×ˢ Ioo c (c + r) ⊆ glueS c r := by
    rintro ⟨z', θ'⟩ hp
    rw [Set.mem_prod] at hp
    rw [mem_glueS]
    exact ⟨hp.1, Or.inr hp.2⟩
  have hmem : (z, c) ∈ closure (Ioi (0 : ℝ) ×ˢ Ioo c (c + r)) := by
    rw [closure_prod_eq, closure_Ioi, closure_Ioo (by linarith : c ≠ c + r)]
    exact ⟨le_of_lt hz, ⟨le_rfl, by linarith⟩⟩
  exact closure_mono hsub hmem

/-! ## §2 The Fréchet derivative versus the two partial derivatives -/

theorem clm_prod_eq_smul_fst_add_smul_snd (L : ℝ × ℝ →L[ℝ] ℝ) :
    L = (L (1, 0)) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (L (0, 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = v.1 • (1, 0) + v.2 • ((0 : ℝ), 1) := by ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  simp
  ring

theorem fderiv_eq_combo {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : DifferentiableAt ℝ (Function.uncurry F) p) :
    fderiv ℝ (Function.uncurry F) p
      = (Work.Spaces.pz F p.1 p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (Work.Spaces.pth F p.1 p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  rw [clm_prod_eq_smul_fst_add_smul_snd (fderiv ℝ (Function.uncurry F) p),
    ← Work.Spaces.pz_eq_fderiv hp, ← Work.Spaces.pth_eq_fderiv hp]

theorem tendsto_fderiv_of_tendsto_partials {F : ℝ → ℝ → ℝ} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    {a b : ℝ} (hdiff : ∀ p ∈ s, DifferentiableAt ℝ (Function.uncurry F) p)
    (h1 : Tendsto (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) (𝓝[s] x) (𝓝 a))
    (h2 : Tendsto (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) (𝓝[s] x) (𝓝 b)) :
    Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p) (𝓝[s] x)
      (𝓝 (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  refine Tendsto.congr' ?_ ((h1.smul tendsto_const_nhds).add (h2.smul tendsto_const_nhds))
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (fderiv_eq_combo (hdiff p hp)).symm

/-! ## §3 Gluing along a convex piece of the strip -/

theorem hasFDerivWithinAt_closure_of_glue {F : ℝ → ℝ → ℝ} {c r : ℝ} {T : Set (ℝ × ℝ)}
    {x : ℝ × ℝ} {L' : ℝ × ℝ →L[ℝ] ℝ} (hTopen : IsOpen T) (hTconv : Convex ℝ T)
    (hTsub : T ⊆ glueS c r) (hTsubU : T ⊆ glueU c r) (hTclU : closure T ⊆ glueU c r)
    (hcont : ContinuousOn (Function.uncurry F) (glueU c r))
    (hdiff : DifferentiableOn ℝ (Function.uncurry F) (glueS c r))
    (htend : Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p) (𝓝[T] x) (𝓝 L')) :
    HasFDerivWithinAt (Function.uncurry F) L' (closure T) x :=
  hasFDerivWithinAt_closure_of_tendsto_fderiv (hdiff.mono hTsub) hTconv hTopen
    (fun y hy => (hcont.continuousWithinAt (hTclU hy)).mono hTsubU) htend

/-! ## §4 The leaf -/

theorem glue_line_C1 (h : ℝ → ℝ → ℝ) (c r : ℝ) :
    Work.FTS_StreamBdry.SB25.GlueLineC1 h c r := by
  classical
  intro hr hScd hUcont hzlim htlim
  have hSopen : IsOpen (glueS c r) := isOpen_glueS c r
  have hUopen : IsOpen (glueU c r) := isOpen_glueU c r
  have hSU : glueS c r ⊆ glueU c r := glueS_subset_glueU hr
  have hDiffOnS : DifferentiableOn ℝ (Function.uncurry h) (glueS c r) :=
    hScd.differentiableOn (by norm_num)
  have hdiffS : ∀ p ∈ glueS c r, DifferentiableAt ℝ (Function.uncurry h) p := fun p hp =>
    hDiffOnS.differentiableAt (hSopen.mem_nhds hp)
  have hfdcontS : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueS c r) :=
    hScd.continuousOn_fderiv_of_isOpen hSopen le_rfl
  -- ### the two boundary limits
  let Lz : ℝ → ℝ := fun z => if hz : 0 < z then Classical.choose (hzlim z hz) else 0
  let Lt : ℝ → ℝ := fun z => if hz : 0 < z then Classical.choose (htlim z hz) else 0
  have hLz : ∀ z (hz : 0 < z), Tendsto (fun p : ℝ × ℝ => Work.Spaces.pz h p.1 p.2)
      (𝓝[glueS c r] (z, c)) (𝓝 (Lz z)) := by
    intro z hz
    have hval : Lz z = Classical.choose (hzlim z hz) := by
      dsimp only [Lz]
      rw [dite_eq_left hz]
    rw [hval]
    exact Classical.choose_spec (hzlim z hz)
  have hLt : ∀ z (hz : 0 < z), Tendsto (fun p : ℝ × ℝ => Work.Spaces.pth h p.1 p.2)
      (𝓝[glueS c r] (z, c)) (𝓝 (Lt z)) := by
    intro z hz
    have hval : Lt z = Classical.choose (htlim z hz) := by
      dsimp only [Lt]
      rw [dite_eq_left hz]
    rw [hval]
    exact Classical.choose_spec (htlim z hz)
  let L : ℝ → ℝ × ℝ →L[ℝ] ℝ := fun z =>
    Lz z • ContinuousLinearMap.fst ℝ ℝ ℝ + Lt z • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hlimfd : ∀ z (hz : 0 < z),
      Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p)
        (𝓝[glueS c r] (z, c)) (𝓝 (L z)) := by
    intro z hz
    exact tendsto_fderiv_of_tendsto_partials hdiffS (hLz z hz) (hLt z hz)
  -- ### differentiability at a seam point
  have hseam : ∀ z (hz : 0 < z), HasFDerivAt (Function.uncurry h) (L z) (z, c) := by
    intro z hz
    have hz3 : z / 2 < 2 * z := by linarith
    have hrl : c - r < c - r / 2 := by linarith
    have hr2 : c - r / 2 < c + r / 2 := by linarith
    have hrr : c + r / 2 < c + r := by linarith
    have hTcleq : ∀ A B : ℝ, A < B →
        closure (Ioo (z / 2) (2 * z) ×ˢ Ioo A B)
          = Icc (z / 2) (2 * z) ×ˢ Icc A B := by
      intro A B hAB
      rw [closure_prod_eq, closure_Ioo (ne_of_lt hz3), closure_Ioo (ne_of_lt hAB)]
    -- one-sided gluing on an arbitrary convex box
    have hside : ∀ A B : ℝ, c - r < A → A < B → B < c + r → A ≤ c → c ≤ B →
        Ioo A B ⊆ Ioo (c - r) c ∪ Ioo c (c + r) →
        HasFDerivWithinAt (Function.uncurry h) (L z)
          (closure (Ioo (z / 2) (2 * z) ×ˢ Ioo A B)) (z, c) := by
      intro A B hA hAB hB hAc hcB hsub
      have hTsub : Ioo (z / 2) (2 * z) ×ˢ Ioo A B ⊆ glueS c r := by
        rintro ⟨z', θ'⟩ hp
        rw [Set.mem_prod] at hp
        rw [mem_glueS]
        exact ⟨by linarith [hp.1.1], hsub hp.2⟩
      have hTclU : closure (Ioo (z / 2) (2 * z) ×ˢ Ioo A B) ⊆ glueU c r := by
        rw [hTcleq A B hAB]
        rintro ⟨z', θ'⟩ hp
        rw [Set.mem_prod] at hp
        rw [mem_glueU]
        exact ⟨by linarith [hp.1.1], by linarith [hp.2.1, hA], by linarith [hp.2.2, hB]⟩
      have hTsubU : Ioo (z / 2) (2 * z) ×ˢ Ioo A B ⊆ glueU c r := Subset.trans hTsub hSU
      exact hasFDerivWithinAt_closure_of_glue (isOpen_Ioo.prod isOpen_Ioo)
        ((convex_Ioo _ _).prod (convex_Ioo _ _)) hTsub hTsubU hTclU hUcont hDiffOnS
        ((hlimfd z hz).mono_left (nhdsWithin_mono _ hTsub))
    have hm := hside (c - r / 2) c hrl (by linarith) (by linarith) (by linarith) le_rfl
      (fun θ hθ => Or.inl ⟨by linarith [hθ.1], hθ.2⟩)
    have hp := hside c (c + r / 2) (by linarith) (by linarith) hrr le_rfl (by linarith)
      (fun θ hθ => Or.inr ⟨hθ.1, by linarith [hθ.2]⟩)
    have hunion := hm.union hp
    have hVsub : Ioo (z / 2) (2 * z) ×ˢ Ioo (c - r / 2) (c + r / 2)
        ⊆ closure (Ioo (z / 2) (2 * z) ×ˢ Ioo (c - r / 2) c)
          ∪ closure (Ioo (z / 2) (2 * z) ×ˢ Ioo c (c + r / 2)) := by
      rintro ⟨z', θ'⟩ hpV
      rw [Set.mem_prod] at hpV
      rcases le_or_gt θ' c with hle | hlt
      · exact Or.inl (by
          rw [hTcleq (c - r / 2) c (by linarith), Set.mem_prod]
          exact ⟨⟨le_of_lt hpV.1.1, le_of_lt hpV.1.2⟩, ⟨le_of_lt hpV.2.1, hle⟩⟩)
      · exact Or.inr (by
          rw [hTcleq c (c + r / 2) (by linarith), Set.mem_prod]
          exact ⟨⟨le_of_lt hpV.1.1, le_of_lt hpV.1.2⟩, ⟨le_of_lt hlt, le_of_lt hpV.2.2⟩⟩)
    have hVnhds : Ioo (z / 2) (2 * z) ×ˢ Ioo (c - r / 2) (c + r / 2) ∈ 𝓝 (z, c) :=
      (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    exact (hunion.mono hVsub).hasFDerivAt hVnhds
  -- ### differentiability on the whole strip
  have hDiffOnU : DifferentiableOn ℝ (Function.uncurry h) (glueU c r) := by
    intro p hp
    by_cases hpc : p.2 = c
    · have hp1 : 0 < p.1 := (mem_glueU.mp hp).1
      have hpeq : p = (p.1, c) := by ext <;> simp [hpc]
      rw [hpeq]
      exact (hseam p.1 hp1).differentiableAt.differentiableWithinAt
    · exact (hdiffS p (mem_glueS_of_mem_glueU_of_ne hp hpc)).differentiableWithinAt
  -- ### the limit field along the seam is continuous
  have hseamcont : ContinuousOn L (Ioi (0 : ℝ)) := by
    intro z0 hz0
    refine (Metric.tendsto_nhds).2 ?_
    intro ε hε
    change {z : ℝ | dist (L z) (L z0) < ε} ∈ 𝓝[Ioi (0 : ℝ)] z0
    rw [Metric.mem_nhdsWithin_iff]
    set W : Set (ℝ × ℝ →L[ℝ] ℝ) := {M | dist M (L z0) ≤ ε / 2} with hWdef
    have hWclosed : IsClosed W := by
      rw [hWdef]
      exact isClosed_le (continuous_id.dist continuous_const) continuous_const
    have hWnhds : W ∈ 𝓝 (L z0) := by
      refine Filter.mem_of_superset
        (Metric.ball_mem_nhds (L z0) (by linarith : (0 : ℝ) < ε / 2)) ?_
      intro M hM
      rw [hWdef, Set.mem_setOf_eq]
      exact le_of_lt (Metric.mem_ball.mp hM)
    obtain ⟨δ', hδ'pos, hδ'sub⟩ := Metric.mem_nhdsWithin_iff.mp ((hlimfd z0 hz0) hWnhds)
    refine ⟨δ' / 2, by linarith, ?_⟩
    rintro z ⟨hzball, hzpos⟩
    change dist (L z) (L z0) < ε
    have hzdist : dist z z0 < δ' / 2 := Metric.mem_ball.mp hzball
    have hne : NeBot (𝓝[glueS c r] (z, c)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (seam_mem_closure_glueS hr hzpos)
    haveI := hne
    have hLzW : L z ∈ W := by
      refine hWclosed.mem_of_tendsto (hlimfd z hzpos) ?_
      change {x : ℝ × ℝ | fderiv ℝ (Function.uncurry h) x ∈ W} ∈ 𝓝[glueS c r] (z, c)
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨δ' / 2, by linarith, ?_⟩
      rintro y ⟨hyball, hyS⟩
      have hy1 : dist y (z0, c) < δ' := by
        have hy2 : dist y (z, c) < δ' / 2 := Metric.mem_ball.mp hyball
        calc dist y (z0, c) ≤ dist y (z, c) + dist (z, c) (z0, c) := dist_triangle _ _ _
          _ = dist y (z, c) + dist z z0 := by simp [Prod.dist_eq, dist_comm]
          _ < δ' / 2 + δ' / 2 := by linarith
          _ = δ' := by ring
      exact hδ'sub ⟨Metric.mem_ball.mpr hy1, hyS⟩
    rw [hWdef, Set.mem_setOf_eq] at hLzW
    linarith
  -- ### continuity of the derivative field on the whole strip
  have hfdcontU : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) := by
    intro p hp
    by_cases hpc : p.2 = c
    · have hp1 : 0 < p.1 := (mem_glueU.mp hp).1
      have hpeq : p = (p.1, c) := by ext <;> simp [hpc]
      have hval : fderiv ℝ (Function.uncurry h) (p.1, c) = L p.1 := (hseam p.1 hp1).fderiv
      rw [hpeq]
      change Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (𝓝[glueU c r] (p.1, c))
        (𝓝 (fderiv ℝ (Function.uncurry h) (p.1, c)))
      rw [hval]
      refine (Metric.tendsto_nhds).2 ?_
      intro ε hε
      change {y : ℝ × ℝ | dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε} ∈
        𝓝[glueU c r] (p.1, c)
      rw [Metric.mem_nhdsWithin_iff]
      have h1 : ∀ᶠ y in 𝓝[glueS c r] (p.1, c),
          dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε / 2 :=
        (hlimfd p.1 hp1) (Metric.ball_mem_nhds (L p.1) (by linarith : (0 : ℝ) < ε / 2))
      have h2 : ∀ᶠ z in 𝓝[Ioi (0 : ℝ)] p.1, dist (L z) (L p.1) < ε / 2 :=
        (hseamcont.continuousWithinAt hp1) (Metric.ball_mem_nhds (L p.1) (by linarith : (0 : ℝ) < ε / 2))
      obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhdsWithin_iff.mp h1
      obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.mem_nhdsWithin_iff.mp h2
      refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
      rintro y ⟨hyball, hyU⟩
      change dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε
      have hydist : dist y (p.1, c) < min δ₁ δ₂ := Metric.mem_ball.mp hyball
      have hyU' := mem_glueU.mp hyU
      by_cases hyc : y.2 = c
      · have hyeq : y = (y.1, c) := by ext <;> simp [hyc]
        have hy1 : 0 < y.1 := hyU'.1
        have hyd : dist y.1 p.1 < δ₂ := by
          have h : dist y (p.1, c) < δ₂ := lt_of_lt_of_le hydist (min_le_right _ _)
          rw [hyeq] at h
          simpa [Prod.dist_eq, dist_comm] using h
        have hval2 : fderiv ℝ (Function.uncurry h) y = L y.1 := by
          rw [hyeq]
          exact (hseam y.1 hy1).fderiv
        rw [hval2]
        exact lt_of_lt_of_le (hδ₂sub ⟨Metric.mem_ball.mpr hyd, hy1⟩) (le_of_lt (by linarith))
      · have hyS : y ∈ glueS c r := mem_glueS_of_mem_glueU_of_ne hyU hyc
        have hb : dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε / 2 :=
          hδ₁sub ⟨Metric.mem_ball.mpr (lt_of_lt_of_le hydist (min_le_left _ _)), hyS⟩
        linarith
    · have hpS : p ∈ glueS c r := mem_glueS_of_mem_glueU_of_ne hp hpc
      exact ((hfdcontS.continuousWithinAt hpS).continuousAt
        (hSopen.mem_nhds hpS)).continuousWithinAt
  -- ### assemble
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry h) (glueU c r) := by
    have hfd0 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) :=
      contDiffOn_zero.2 hfdcontU
    have hiff := contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ)
      (f := Function.uncurry h) (s := glueU c r) (n := 0) hUopen
    rw [show (0 : WithTop ℕ∞) + 1 = 1 from by simp] at hiff
    exact hiff.2 ⟨hDiffOnU, fun h0 => absurd h0 (by simp), hfd0⟩
  refine ⟨hC1, ?_, ?_⟩
  · have hfdc : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) :=
      hC1.continuousOn_fderiv_of_isOpen hUopen le_rfl
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry h) p) ((1 : ℝ), (0 : ℝ))) (glueU c r) :=
      hfdc.clm_apply continuousOn_const
    refine hcomp.congr ?_
    intro p hp
    show Work.Spaces.pz h p.1 p.2 = fderiv ℝ (Function.uncurry h) p (1, 0)
    exact Work.Spaces.pz_eq_fderiv ((hDiffOnU p hp).differentiableAt (hUopen.mem_nhds hp))
  · have hfdc : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) :=
      hC1.continuousOn_fderiv_of_isOpen hUopen le_rfl
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry h) p) ((0 : ℝ), (1 : ℝ))) (glueU c r) :=
      hfdc.clm_apply continuousOn_const
    refine hcomp.congr ?_
    intro p hp
    show Work.Spaces.pth h p.1 p.2 = fderiv ℝ (Function.uncurry h) p (0, 1)
    exact Work.Spaces.pth_eq_fderiv ((hDiffOnU p hp).differentiableAt (hUopen.mem_nhds hp))

end Work.FTS_StreamBdry.SB25

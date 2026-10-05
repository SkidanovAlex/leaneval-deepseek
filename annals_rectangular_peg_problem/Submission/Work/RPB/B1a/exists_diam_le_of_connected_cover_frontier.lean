import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB.B1a.eq_singleton_of_closed_connected_of_cover_ball
import Submission.Work.RPB.B1a.eq_singleton_of_isClosed_connected_cover_of_local
import Submission.Work.RPB.Port.Drive.curve_localSep
import Submission.Work.RPB.Port.Drive.smooth_jordan_separation
import Submission.Work.RPB.B1p.localSep_arc_eps
import Submission.Work.RPB.B1p.localSep_transfer
import Submission.Work.RPB1a.exists_smooth_embedding_descend

/-!
# A small cut of the closed region bounded by a smooth loop cuts off a small piece

This file proves `Work.RPB.B1a.exists_diam_le_of_connected_cover_frontier`: for a smooth loop `v`
bounding a Jordan domain `D` (with `closure D \ interior D = range v`) and any `η > 0` there is
`ε > 0` such that whenever two closed connected sets `T₁`, `T₂` cover `closure D` and their
intersection has diameter at most `ε`, one of them has diameter at most `η`.

The proof is the classical compactness argument.  Suppose no `ε` works: then there are closed
connected sets `T₁ⁿ`, `T₂ⁿ` covering `closure D`, with `diam (T₁ⁿ ∩ T₂ⁿ) ≤ 1/n` and
`diam T₁ⁿ, diam T₂ⁿ ≥ η`.  Passing to a subsequence converging in the Hausdorff distance gives two
closed connected sets `A`, `B` with `A ∪ B = closure D`, both of diameter `≥ η`, and
`A ∩ B` a single point.  A point cannot be a cut point of `closure D`: in the interior of `D` a
small ball around `p` covered by `A` and `B` forces `A ∩ B` to be larger than a point, and on the
frontier the local separation of the curve does the same (a local piece of `closure D` near `p` is
connected and contained in `A ∪ B`, again forcing a larger intersection).

The pieces of local structure used are
* `Work.RPB.B1p.localSep_arc_eps` (a smooth arc locally separates a small ball),
* `Work.RPB.Port.Drive.smooth_jordan_separation` (the plane minus a smooth embedded circle has two
  components, the frontier of each being the curve),
* `Work.RPB.Port.Drive.LocalSep` (local separation), transported to `ℂ` as `LocalSepC`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Complex Set Metric Filter
open scoped ContDiff Topology Manifold ENNReal
open Manifold

noncomputable section

namespace Work.RPB.B1a

/-! ## Local separation in `ℂ` -/

/-- If `closure D \ interior D = range v` then `frontier D = range v`. -/
lemma frontier_eq_range_of_closure_sdiff {v : ℝ → ℂ} {D : Set ℂ}
    (hDfr : closure D \ interior D = Set.range v) : frontier D = Set.range v := by
  rw [frontier_eq_closure_inter_closure, closure_compl]
  rw [Set.sdiff_eq] at hDfr
  exact hDfr

/-- **Local separation data** at a point of a set `K ⊆ ℂ`: an open neighbourhood `U` of the point,
split by `K` into two nonempty open path connected pieces, each of which accumulates at every point
of `K ∩ U`.  The `ℂ`-side mirror of `Work.RPB.Port.Drive.LocalSep`. -/
structure LocalSepC (K U U₁ U₂ : Set ℂ) : Prop where
  isOpen_U : IsOpen U
  isOpen₁ : IsOpen U₁
  isOpen₂ : IsOpen U₂
  pc₁ : IsPathConnected U₁
  pc₂ : IsPathConnected U₂
  disjoint : Disjoint U₁ U₂
  union : U₁ ∪ U₂ = U \ K
  acc₁ : ∀ q ∈ U ∩ K, q ∈ closure U₁
  acc₂ : ∀ q ∈ U ∩ K, q ∈ closure U₂

/-- `e.symm '' s = e ⁻¹' s` for the linear homeomorphism `e : ℂ ≃ ℝ × ℝ`. -/
private lemma image_symm_eq_preimage (s : Set (ℝ × ℝ)) :
    Complex.equivRealProdCLM.symm '' s = (fun x : ℂ => Complex.equivRealProdCLM x) ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨Complex.equivRealProdCLM x, by simpa using hx,
      ContinuousLinearEquiv.symm_apply_apply _ x⟩

/-- `e.symm '' range γ = range v` when `range γ = e '' range v`. -/
private lemma image_symm_range {v : ℝ → ℂ} {γ : Circle → ℝ × ℝ}
    (hrange : Set.range γ = Complex.equivRealProdCLM '' Set.range v) :
    Complex.equivRealProdCLM.symm '' Set.range γ = Set.range v := by
  rw [hrange, Set.image_image]
  have hcomp : (fun x : ℂ => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x))
      = id := by
    funext x
    exact ContinuousLinearEquiv.symm_apply_apply _ x
  rw [hcomp, Set.image_id]

/-- **Transport of local separation from `ℝ × ℝ` to `ℂ`** along the linear homeomorphism
`Complex.equivRealProdCLM`, when the two curves correspond. -/
lemma localSepC_of_localSep {v : ℝ → ℂ} {γ : Circle → ℝ × ℝ}
    (hrange : Set.range γ = Complex.equivRealProdCLM '' Set.range v)
    {U U₁ U₂ : Set (ℝ × ℝ)} (h : Work.RPB.Port.Drive.LocalSep (Set.range γ) U U₁ U₂) :
    LocalSepC (Set.range v) (Complex.equivRealProdCLM.symm '' U)
      (Complex.equivRealProdCLM.symm '' U₁) (Complex.equivRealProdCLM.symm '' U₂) := by
  have hcont : Continuous ⇑Complex.equivRealProdCLM.symm := Complex.equivRealProdCLM.symm.continuous
  have hinj : Function.Injective ⇑Complex.equivRealProdCLM.symm :=
    Complex.equivRealProdCLM.symm.injective
  have hrange' := image_symm_range hrange
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_symm_eq_preimage]
    exact h.isOpen_U.preimage Complex.equivRealProdCLM.continuous
  · rw [image_symm_eq_preimage]
    exact h.isOpen₁.preimage Complex.equivRealProdCLM.continuous
  · rw [image_symm_eq_preimage]
    exact h.isOpen₂.preimage Complex.equivRealProdCLM.continuous
  · exact h.pc₁.image' hcont.continuousOn
  · exact h.pc₂.image' hcont.continuousOn
  · exact Set.disjoint_image_of_injective hinj h.disjoint
  · rw [← Set.image_union, h.union, Set.image_sdiff hinj, hrange']
  · intro q hq
    obtain ⟨⟨y, hyU, hyq⟩, hqK⟩ := hq
    rw [← hyq]
    have hyK : y ∈ Set.range γ := by
      obtain ⟨z, hz⟩ := hqK
      rw [hrange]
      refine ⟨v z, ⟨z, rfl⟩, ?_⟩
      have h1 : Complex.equivRealProdCLM.symm y = v z := by rw [hyq, ← hz]
      have h2 := congrArg Complex.equivRealProdCLM h1
      rw [ContinuousLinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    exact image_closure_subset_closure_image hcont (Set.mem_image_of_mem _ (h.acc₁ y ⟨hyU, hyK⟩))
  · intro q hq
    obtain ⟨⟨y, hyU, hyq⟩, hqK⟩ := hq
    rw [← hyq]
    have hyK : y ∈ Set.range γ := by
      obtain ⟨z, hz⟩ := hqK
      rw [hrange]
      refine ⟨v z, ⟨z, rfl⟩, ?_⟩
      have h1 : Complex.equivRealProdCLM.symm y = v z := by rw [hyq, ← hz]
      have h2 := congrArg Complex.equivRealProdCLM h1
      rw [ContinuousLinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    exact image_closure_subset_closure_image hcont (Set.mem_image_of_mem _ (h.acc₂ y ⟨hyU, hyK⟩))

/-! ## Local separation at the points of a smooth loop -/

/-- The plane curve `t ↦ γ (Circle.exp t)` of a smooth embedded circle is `C^∞`. -/
private lemma contDiff_curve_top (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.RPB.Port.Drive.curve γ) := by
  have h1 : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ := hγ.contMDiff
  have h2 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.RPB.Port.Drive.curve γ) :=
    h1.comp (contMDiff_circleExp (m := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  exact contMDiff_iff_contDiff.mp h2

/-- **Local separation of the range of a smooth embedded circle, localized.**  For every point of
the curve and every `ε > 0` there is a local separation whose neighbourhood is contained in the
ball of radius `ε`.

This is `Work.RPB.Port.Drive.curve_localSep` with the extra smallness, obtained from the arc
statement `Work.RPB.B1p.localSep_arc_eps` and the transfer `Work.RPB.B1p.localSep_transfer` (a
point of the curve close to `p` has a parameter close to that of `p`, by
`Work.RPB.Port.Drive.curve_arc_cover`). -/
lemma exists_localSep_range_curve (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (p : ℝ × ℝ) (hp : p ∈ Set.range γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U U₁ U₂ : Set (ℝ × ℝ), Work.RPB.Port.Drive.LocalSep (Set.range γ) U U₁ U₂ ∧
      p ∈ U ∧ U ⊆ Metric.ball p ε := by
  obtain ⟨c₀, rfl⟩ := hp
  obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective c₀
  have hpθ : Work.RPB.Port.Drive.curve γ θ₀ = γ c₀ := by
    show γ (Circle.exp θ₀) = γ c₀
    rw [hθ₀]
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hpi2' : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  obtain ⟨η, hηpos, hη⟩ := Work.RPB.Port.Drive.curve_arc_cover γ hγ θ₀ hpi2 hpi2'
  -- the parametrization is injective on the arc of length `π` centred at `θ₀`
  have hinj : Set.InjOn (Work.RPB.Port.Drive.curve γ)
      (Set.Icc (θ₀ - Real.pi / 2) (θ₀ + Real.pi / 2)) := by
    intro s hs t ht hst
    obtain ⟨k, hk⟩ := (Work.RPB.Port.Drive.curve_eq_iff γ hγ s t).mp hst
    have habs : |s - t| ≤ Real.pi := by
      rw [abs_le]
      exact ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
    have hkt : s - t = 2 * Real.pi * (k : ℝ) := by linarith [hk]
    have hkabs : |(k : ℝ)| ≤ 1 / 2 := by
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      have heq : |s - t| = 2 * Real.pi * |(k : ℝ)| := by
        rw [hkt, abs_mul, abs_of_pos h2pi]
      rw [heq] at habs
      nlinarith [Real.pi_pos, abs_nonneg (k : ℝ)]
    have hk0 : k = 0 := by
      have h1 : ((|k| : ℤ) : ℝ) ≤ 1 / 2 := by rw [Int.cast_abs]; exact hkabs
      have h2 : (|k| : ℤ) ≤ 0 := by
        by_contra h
        push Not at h
        have h3 : (1 : ℤ) ≤ |k| := h
        have h4 : (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h3
        linarith
      have h5 : (0 : ℝ) < 1 / 2 := by norm_num
      have h6 : 0 ≤ |k| := abs_nonneg k
      exact abs_eq_zero.mp (by omega : |k| = 0)
    rw [hk, hk0]
    ring
  obtain ⟨U, U₁, U₂, hLS, hpmem, hUsub⟩ :=
    Work.RPB.B1p.localSep_arc_eps (G := Work.RPB.Port.Drive.curve γ)
      (contDiff_curve_top γ hγ) (a := θ₀ - Real.pi / 2) (b := θ₀ + Real.pi / 2) (s₀ := θ₀)
      (by linarith) (by linarith) hinj (Work.RPB.Port.Drive.curve_deriv_ne_zero γ hγ θ₀)
      (ε := min ε η) (lt_min hε hηpos)
  refine ⟨U, U₁, U₂, Work.RPB.B1p.localSep_transfer hLS ?_ ?_, ?_, ?_⟩
  · rw [← Work.RPB.Port.Drive.range_curve]
    exact Set.image_subset_range _ _
  · -- a point of the curve in `U` has a parameter within `π/2` of `θ₀`
    rintro y ⟨hyU, c, rfl⟩
    have hyball : γ c ∈ Metric.ball (Work.RPB.Port.Drive.curve γ θ₀) η :=
      Metric.ball_subset_ball (min_le_right _ _) (hUsub hyU)
    obtain ⟨t, ht, htc⟩ := hη c hyball
    refine ⟨t, ?_, htc.symm⟩
    rw [abs_lt] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [← hpθ]; exact hpmem
  · intro z hz
    rw [← hpθ]
    exact Metric.ball_subset_ball (min_le_left _ _) (hUsub hz)

/-- **Local separation on the plane side, at a point of the range of a smooth loop, localized.**
For a smooth loop `v`, every point `p` of its range and every `ε > 0` there are `U, U₁, U₂` with
`LocalSepC (range v) U U₁ U₂`, `p ∈ U` and `U ⊆ ball p ε`. -/
lemma exists_localSepC_range_v (v : ℝ → ℂ) (hv : IsSmoothLoop v) (p : ℂ)
    (hp : p ∈ Set.range v) {ε : ℝ} (hε : 0 < ε) :
    ∃ U U₁ U₂ : Set ℂ, LocalSepC (Set.range v) U U₁ U₂ ∧ p ∈ U ∧ U ⊆ Metric.ball p ε := by
  obtain ⟨γ, hemb, -, -, -, hrange⟩ := Work.RPB1a.exists_smooth_embedding_descend v hv
  have hep : Complex.equivRealProdCLM p ∈ Set.range γ := by
    rw [hrange]
    exact ⟨p, hp, rfl⟩
  -- a radius for which the inverse image of the `ε`-ball around `p` is a ball around `e p`
  obtain ⟨ε', hε'pos, hε'sub⟩ : ∃ ε' > 0, Complex.equivRealProdCLM.symm ''
      Metric.ball (Complex.equivRealProdCLM p) ε' ⊆ Metric.ball p ε := by
    have hcont : ContinuousAt (⇑Complex.equivRealProdCLM.symm) (Complex.equivRealProdCLM p) :=
      Complex.equivRealProdCLM.symm.continuous.continuousAt
    have hmem : Metric.ball p ε ∈ 𝓝 (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM p)) := by
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Metric.ball_mem_nhds p hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds hmem)
    refine ⟨δ, hδpos, fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    exact hδ hy
  obtain ⟨U, U₁, U₂, hLS, hpmem, hUsub⟩ :=
    exists_localSep_range_curve γ hemb (Complex.equivRealProdCLM p) hep hε'pos
  refine ⟨_, _, _, localSepC_of_localSep hrange hLS, ⟨Complex.equivRealProdCLM p, hpmem, ?_⟩, ?_⟩
  · exact ContinuousLinearEquiv.symm_apply_apply _ p
  · intro x hx
    obtain ⟨y, hyU, rfl⟩ := hx
    exact hε'sub ⟨y, hUsub hyU, rfl⟩

/-! ## The two-sided decomposition of the complement of a smooth loop -/

/-- **The complement of the range of a smooth loop in `ℂ` is the disjoint union of a bounded and an
unbounded path connected open set, each having the range as frontier.**

Obtained from the `ℝ × ℝ` statement `Work.RPB.Port.Drive.smooth_jordan_separation` by descending the
loop to a smooth embedding of the circle and transporting along `Complex.equivRealProdCLM`. -/
lemma exists_twoSidedDecomposition (v : ℝ → ℂ) (hv : IsSmoothLoop v) :
    ∃ ins out : Set ℂ, IsOpen ins ∧ IsOpen out ∧ IsPathConnected ins ∧ IsPathConnected out ∧
      Bornology.IsBounded ins ∧ ¬ Bornology.IsBounded out ∧ ins.Nonempty ∧ out.Nonempty ∧
      (Set.range v)ᶜ = ins ∪ out ∧ Disjoint ins out ∧ frontier ins = Set.range v ∧
      frontier out = Set.range v := by
  obtain ⟨γ, hemb, -, -, -, hrange⟩ := Work.RPB1a.exists_smooth_embedding_descend v hv
  obtain ⟨ins₀, out₀, ho₁, ho₂, hpc₁, hpc₂, hb₁, hb₂, hne₁, hne₂, hcov, hdisj, hcl₁, hcl₂⟩ :=
    Work.RPB.Port.Drive.smooth_jordan_separation γ hemb
  have hcont : Continuous ⇑Complex.equivRealProdCLM.symm := Complex.equivRealProdCLM.symm.continuous
  have hrange' := image_symm_range hrange
  have hins_disj : Disjoint ins₀ (Set.range γ) := by
    rw [Set.disjoint_left]
    intro x hx hxK
    have : x ∈ (Set.range γ)ᶜ := by rw [hcov]; exact Or.inl hx
    exact this hxK
  have hout_disj : Disjoint out₀ (Set.range γ) := by
    rw [Set.disjoint_left]
    intro x hx hxK
    have : x ∈ (Set.range γ)ᶜ := by rw [hcov]; exact Or.inr hx
    exact this hxK
  have hfront₁ : frontier ins₀ = Set.range γ := by
    rw [show frontier ins₀ = closure ins₀ \ interior ins₀ from rfl, ho₁.interior_eq, hcl₁]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact absurd h hx
      · exact h
    · intro hx
      exact ⟨Or.inr hx, fun hins => (Set.disjoint_left.mp hins_disj hins hx)⟩
  have hfront₂ : frontier out₀ = Set.range γ := by
    rw [show frontier out₀ = closure out₀ \ interior out₀ from rfl, ho₂.interior_eq, hcl₂]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact absurd h hx
      · exact h
    · intro hx
      exact ⟨Or.inr hx, fun hout => (Set.disjoint_left.mp hout_disj hout hx)⟩
  -- the transported pieces
  have hcov' : (Set.range v)ᶜ = Complex.equivRealProdCLM.symm '' ins₀ ∪
      Complex.equivRealProdCLM.symm '' out₀ := by
    rw [← hrange', ← Set.image_compl_eq Complex.equivRealProdCLM.symm.bijective, hcov,
      Set.image_union]
  have hfront₁' : frontier (Complex.equivRealProdCLM.symm '' ins₀) = Set.range v := by
    have h := Homeomorph.image_frontier (Complex.equivRealProdCLM.symm.toHomeomorph) ins₀
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
    rw [← h, hfront₁, hrange']
  have hfront₂' : frontier (Complex.equivRealProdCLM.symm '' out₀) = Set.range v := by
    have h := Homeomorph.image_frontier (Complex.equivRealProdCLM.symm.toHomeomorph) out₀
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
    rw [← h, hfront₂, hrange']
  have hbdd' : ¬ Bornology.IsBounded (Complex.equivRealProdCLM.symm '' out₀) := by
    intro hb'
    have himg : Complex.equivRealProdCLM '' (Complex.equivRealProdCLM.symm '' out₀) = out₀ := by
      rw [Set.image_image]
      have hcomp : (fun x : ℝ × ℝ => Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm x))
          = id := by
        funext x
        exact ContinuousLinearEquiv.apply_symm_apply _ x
      rw [hcomp, Set.image_id]
    exact hb₂ (himg ▸ Complex.equivRealProdCLM.lipschitzWith.isBounded_image hb')
  refine ⟨Complex.equivRealProdCLM.symm '' ins₀, Complex.equivRealProdCLM.symm '' out₀,
    ?_, ?_, ?_, ?_, ?_, hbdd', ?_, ?_, hcov', ?_, hfront₁', hfront₂'⟩
  · rw [image_symm_eq_preimage]; exact ho₁.preimage Complex.equivRealProdCLM.continuous
  · rw [image_symm_eq_preimage]; exact ho₂.preimage Complex.equivRealProdCLM.continuous
  · exact hpc₁.image' hcont.continuousOn
  · exact hpc₂.image' hcont.continuousOn
  · exact Complex.equivRealProdCLM.symm.lipschitzWith.isBounded_image hb₁
  · exact hne₁.image _
  · exact hne₂.image _
  · exact Set.disjoint_image_of_injective Complex.equivRealProdCLM.symm.injective hdisj

/-! ## Hausdorff limits of compact sets -/

/-- **Blaschke selection**: a sequence of nonempty compact subsets of a compact set has a
subsequence converging in the Hausdorff distance. -/
lemma exists_hausdorff_limit_subseq (K : Set ℂ) (T : ℕ → Set ℂ)
    (hK : IsCompact K) (hT : ∀ n, IsCompact (T n)) (hTne : ∀ n, (T n).Nonempty)
    (hTsub : ∀ n, T n ⊆ K) :
    ∃ A : Set ℂ, IsCompact A ∧ A.Nonempty ∧ A ⊆ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => Metric.hausdorffDist (T (φ n)) A) atTop (𝓝 0) := by
  let L : ℕ → TopologicalSpace.NonemptyCompacts ℂ := fun n => ⟨⟨T n, hT n⟩, hTne n⟩
  have hLcoe : ∀ n, (L n : Set ℂ) = T n := fun n => rfl
  obtain ⟨A', hA'mem, φ, hφ, hconv⟩ :=
    IsCompact.tendsto_subseq (x := L)
      (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hK) (fun n => hTsub n)
  refine ⟨(A' : Set ℂ), A'.isCompact, A'.nonempty, hA'mem, φ, hφ, ?_⟩
  have h1 : Tendsto (fun n => dist (L (φ n)) A') atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hconv
  have h2 : (fun n => dist (L (φ n)) A') = fun n => Metric.hausdorffDist (T (φ n)) (A' : Set ℂ) := by
    funext n
    rw [TopologicalSpace.NonemptyCompacts.dist_eq, hLcoe]
  rw [h2] at h1
  exact h1

/-- **The Hausdorff limit of a sequence of connected compact sets is connected.** -/
lemma isConnected_of_hausdorffDist_tendsto_zero (T : ℕ → Set ℂ) (A : Set ℂ)
    (hT : ∀ n, IsConnected (T n)) (hTA : ∀ n, IsCompact (T n))
    (hA : IsCompact A) (hAne : A.Nonempty)
    (h : Tendsto (fun n => Metric.hausdorffDist (T n) A) atTop (𝓝 0)) : IsConnected A := by
  have hfin : ∀ n, Metric.hausdorffEDist (T n) A ≠ ⊤ := fun n =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hT n).nonempty hAne
      (hTA n).isBounded hA.isBounded
  have hTne : ∀ n, (T n).Nonempty := fun n => (hT n).nonempty
  refine ⟨hAne, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hAuv hAuv_disj
  by_contra hcon
  obtain ⟨x₀, hx₀A, hx₀u⟩ := not_subset.mp (fun h => hcon (Or.inl h))
  obtain ⟨y₀, hy₀A, hy₀v⟩ := not_subset.mp (fun h => hcon (Or.inr h))
  have hx₀v : x₀ ∈ v := by
    rcases hAuv hx₀A with h | h
    · exact absurd h hx₀u
    · exact h
  have hy₀u : y₀ ∈ u := by
    rcases hAuv hy₀A with h | h
    · exact h
    · exact absurd h hy₀v
  -- a positive distance between the two disjoint compact pieces of `A`
  obtain ⟨r₀, hr₀pos, hr₀⟩ : ∃ r₀ > 0, ∀ a ∈ A ∩ u, ∀ b ∈ A ∩ v, r₀ < dist a b := by
    obtain ⟨r, hr, hrlt⟩ := Metric.exists_pos_forall_lt_edist (hA.inter_right hu)
      (hA.isClosed.inter hv) (by
        rw [Set.disjoint_left]
        intro z hz hzv
        simp only [Set.mem_inter_iff] at hz hzv
        exact (Set.eq_empty_iff_forall_notMem.mp hAuv_disj) z (by
          simp only [Set.mem_inter_iff]
          exact ⟨hz.1, hz.2, hzv.2⟩))
    refine ⟨(r : ℝ), by exact_mod_cast hr, fun a ha b hb => ?_⟩
    have h := hrlt a ha b hb
    rw [edist_dist] at h
    by_contra hle
    push Not at hle
    have h4 : ENNReal.ofReal (dist a b) ≤ ENNReal.ofReal ((r : ℝ)) := ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_coe_nnreal] at h4
    exact absurd h (not_lt.mpr h4)
  set δ : ℝ := r₀ / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  set U : Set ℂ := Metric.thickening δ (A ∩ u) with hUdef
  set V : Set ℂ := Metric.thickening δ (A ∩ v) with hVdef
  have hUopen : IsOpen U := Metric.isOpen_thickening
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hdisjUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨a, ha, hza⟩ := Metric.mem_thickening_iff.mp hzU
    obtain ⟨b, hb, hzb⟩ := Metric.mem_thickening_iff.mp hzV
    have hrab : r₀ < dist a b := hr₀ a ha b hb
    have hlt : dist a b < r₀ := by
      have htri : dist a b ≤ dist z a + dist z b := by
        calc dist a b ≤ dist a z + dist z b := dist_triangle a z b
          _ = dist z a + dist z b := by rw [dist_comm a z]
      rw [hδdef] at hza hzb
      linarith
    linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h δ hδpos
  have hN' : ∀ n ≥ N, Metric.hausdorffDist (T n) A < δ := by
    intro n hn
    have h3 := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at h3
  have hsub : ∀ n ≥ N, T n ⊆ U ∪ V := by
    intro n hn z hz
    have h1 : Metric.infDist z A < δ :=
      lt_of_le_of_lt (Metric.infDist_le_hausdorffDist_of_mem hz (hfin n)) (hN' n hn)
    obtain ⟨a, ha, hza⟩ := Metric.infDist_lt_iff hAne |>.mp h1
    rcases hAuv ha with h | h
    · exact Or.inl (Metric.mem_thickening_iff.mpr ⟨a, ⟨ha, h⟩, hza⟩)
    · exact Or.inr (Metric.mem_thickening_iff.mpr ⟨a, ⟨ha, h⟩, hza⟩)
  have hmeetU : ∀ n ≥ N, (T n ∩ U).Nonempty := by
    intro n hn
    have h1 : Metric.infDist y₀ (T n) < δ := by
      have h2 : Metric.infDist y₀ (T n) ≤ Metric.hausdorffDist A (T n) :=
        Metric.infDist_le_hausdorffDist_of_mem hy₀A (by rw [Metric.hausdorffEDist_comm]; exact hfin n)
      have h3 : Metric.hausdorffDist A (T n) < δ := by
        rw [Metric.hausdorffDist_comm]; exact hN' n hn
      exact lt_of_le_of_lt h2 h3
    obtain ⟨z, hz, hyz⟩ := Metric.infDist_lt_iff (hTne n) |>.mp h1
    exact ⟨z, hz, Metric.mem_thickening_iff.mpr ⟨y₀, ⟨hy₀A, hy₀u⟩, by rw [dist_comm]; exact hyz⟩⟩
  have hmeetV : ∀ n ≥ N, (T n ∩ V).Nonempty := by
    intro n hn
    have h1 : Metric.infDist x₀ (T n) < δ := by
      have h2 : Metric.infDist x₀ (T n) ≤ Metric.hausdorffDist A (T n) :=
        Metric.infDist_le_hausdorffDist_of_mem hx₀A (by rw [Metric.hausdorffEDist_comm]; exact hfin n)
      have h3 : Metric.hausdorffDist A (T n) < δ := by
        rw [Metric.hausdorffDist_comm]; exact hN' n hn
      exact lt_of_le_of_lt h2 h3
    obtain ⟨z, hz, hxz⟩ := Metric.infDist_lt_iff (hTne n) |>.mp h1
    exact ⟨z, hz, Metric.mem_thickening_iff.mpr ⟨x₀, ⟨hx₀A, hx₀v⟩, by rw [dist_comm]; exact hxz⟩⟩
  -- contradicting connectedness of `T N`
  rcases (hT N).isPreconnected.subset_or_subset hUopen hVopen hdisjUV (hsub N le_rfl) with h | h
  · obtain ⟨z, hz⟩ := hmeetV N le_rfl
    exact Set.disjoint_left.mp hdisjUV (h hz.1) hz.2
  · obtain ⟨z, hz⟩ := hmeetU N le_rfl
    exact Set.disjoint_left.mp hdisjUV hz.2 (h hz.1)

/-- **The union of two Hausdorff limits covers the limit of the unions.** -/
lemma union_eq_of_hausdorff_tendsto (K : Set ℂ) (T T' : ℕ → Set ℂ) (A B : Set ℂ)
    (hAcl : IsClosed A) (hBcl : IsClosed B) (hKcl : IsClosed K) (hAne : A.Nonempty)
    (hBne : B.Nonempty) (hTne : ∀ n, (T n).Nonempty) (hT'ne : ∀ n, (T' n).Nonempty)
    (hTfin : ∀ n, Metric.hausdorffEDist (T n) A ≠ ⊤)
    (hT'fin : ∀ n, Metric.hausdorffEDist (T' n) B ≠ ⊤)
    (hT : Tendsto (fun n => Metric.hausdorffDist (T n) A) atTop (𝓝 0))
    (hT' : Tendsto (fun n => Metric.hausdorffDist (T' n) B) atTop (𝓝 0))
    (hcover : ∀ n, T n ∪ T' n = K) : A ∪ B = K := by
  refine Set.Subset.antisymm ?_ fun x hxK => ?_
  · -- points of `A` and `B` are limits of points of the `T n`, hence lie in `K`
    have hA : A ⊆ K := by
      intro x hx
      rw [← hKcl.closure_eq]
      refine Metric.mem_closure_iff.mpr fun ε hε => ?_
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hT ε hε
      have h1 : Metric.infDist x (T N) ≤ Metric.hausdorffDist A (T N) :=
        Metric.infDist_le_hausdorffDist_of_mem hx (by rw [Metric.hausdorffEDist_comm]; exact hTfin N)
      have h2 := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg,
        Metric.hausdorffDist_comm] at h2
      obtain ⟨y, hy, hxy⟩ := Metric.infDist_lt_iff (hTne N) |>.mp (lt_of_le_of_lt h1 h2)
      exact ⟨y, (hcover N ▸ Set.subset_union_left : T N ⊆ K) hy, hxy⟩
    have hB : B ⊆ K := by
      intro x hx
      rw [← hKcl.closure_eq]
      refine Metric.mem_closure_iff.mpr fun ε hε => ?_
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hT' ε hε
      have h1 : Metric.infDist x (T' N) ≤ Metric.hausdorffDist B (T' N) :=
        Metric.infDist_le_hausdorffDist_of_mem hx (by rw [Metric.hausdorffEDist_comm]; exact hT'fin N)
      have h2 := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg,
        Metric.hausdorffDist_comm] at h2
      obtain ⟨y, hy, hxy⟩ := Metric.infDist_lt_iff (hT'ne N) |>.mp (lt_of_le_of_lt h1 h2)
      exact ⟨y, (hcover N ▸ Set.subset_union_right : T' N ⊆ K) hy, hxy⟩
    exact Set.union_subset hA hB
  · -- a point of `K` outside `A ∪ B` is too far from both to lie in `T n ∪ T' n`
    by_contra hxout
    have hxA : x ∉ A := fun h => hxout (Or.inl h)
    have hxB : x ∉ B := fun h => hxout (Or.inr h)
    have hδA : 0 < Metric.infDist x A :=
      (Metric.infDist_pos_iff_notMem_closure hAne).mp (by rwa [hAcl.closure_eq])
    have hδB : 0 < Metric.infDist x B :=
      (Metric.infDist_pos_iff_notMem_closure hBne).mp (by rwa [hBcl.closure_eq])
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hT (Metric.infDist x A / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hT' (Metric.infDist x B / 2) (by linarith)
    have hxT : x ∉ T (max N₁ N₂) := by
      intro hxT'
      have h1 : Metric.infDist x A ≤ Metric.hausdorffDist (T (max N₁ N₂)) A :=
        Metric.infDist_le_hausdorffDist_of_mem hxT' (hTfin (max N₁ N₂))
      have h2 := hN₁ (max N₁ N₂) (le_max_left N₁ N₂)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at h2
      linarith
    have hxT' : x ∉ T' (max N₁ N₂) := by
      intro hxT''
      have h1 : Metric.infDist x B ≤ Metric.hausdorffDist (T' (max N₁ N₂)) B :=
        Metric.infDist_le_hausdorffDist_of_mem hxT'' (hT'fin (max N₁ N₂))
      have h2 := hN₂ (max N₁ N₂) (le_max_right N₁ N₂)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at h2
      linarith
    have : x ∈ T (max N₁ N₂) ∪ T' (max N₁ N₂) := hcover (max N₁ N₂) ▸ hxK
    rcases this with h | h
    · exact hxT h
    · exact hxT' h

theorem exists_diam_le_of_connected_cover_frontier (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v)
    (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDfr : closure D \ interior D = Set.range v) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T₁ T₂ : Set ℂ, IsClosed T₁ → IsConnected T₁ → IsClosed T₂ → IsConnected T₂ →
      T₁ ∪ T₂ = closure D → Metric.diam (T₁ ∩ T₂) ≤ ε →
      Metric.diam T₁ ≤ η ∨ Metric.diam T₂ ≤ η := by

  have hfront : frontier D = Set.range v := frontier_eq_range_of_closure_sdiff hDfr
  have hKc : IsCompact (closure D) := hDb.isCompact_closure
  have hKcl : IsClosed (closure D) := hKc.isClosed
  have hKconn : IsConnected (closure D) := hDc.closure
  have hDsub : D ⊆ (Set.range v)ᶜ := by
    intro x hx
    rw [← hfront, IsOpen.frontier_eq hDo]
    exact fun h => h.2 hx
  have hclD : closure D = D ∪ Set.range v := by
    rw [← hfront, IsOpen.frontier_eq hDo]
    exact (Set.union_sdiff_cancel subset_closure).symm
  obtain ⟨ins, out, hio1, hio2, hpc1, hpc2, hibd, hiub, hine1, hine2, hicov, hidisj,
    hifr1, hifr2⟩ := exists_twoSidedDecomposition v hv
  have hDins : D = ins := by
    have h1 : D ⊆ ins ∨ D ⊆ out :=
      hDc.isPreconnected.subset_or_subset hio1 hio2 hidisj (by rw [← hicov]; exact hDsub)
    rcases h1 with h1 | h1
    · have hsub : ins ⊆ D ∪ (ins \ D) := fun x hx => by
        by_cases hxD : x ∈ D
        · exact Or.inl hxD
        · exact Or.inr ⟨hx, hxD⟩
      have hopen : IsOpen (ins \ D) := by
        have h2 : ins \ D = ins ∩ (closure D)ᶜ := by
          ext x
          constructor
          · rintro ⟨hxi, hxD⟩
            refine ⟨hxi, ?_⟩
            intro hxc
            rw [hclD] at hxc
            rcases hxc with h | h
            · exact hxD h
            · have hxins : x ∈ (Set.range v)ᶜ := by rw [hicov]; exact Or.inl hxi
              exact hxins h
          · rintro ⟨hxi, hxc⟩
            exact ⟨hxi, fun hxD => hxc (subset_closure hxD)⟩
        rw [h2]
        exact hio1.inter isClosed_closure.isOpen_compl
      rcases hpc1.isConnected.isPreconnected.subset_or_subset hDo hopen
        (by rw [Set.disjoint_left]; exact fun x hx hx' => hx'.2 hx) hsub with h2 | h2
      · exact Set.Subset.antisymm h1 h2
      · exfalso
        have hDempty : D = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => (h2 (h1 hx)).2 hx
        exact hDc.nonempty.ne_empty hDempty
    · have hsub : out ⊆ D ∪ (out \ D) := fun x hx => by
        by_cases hxD : x ∈ D
        · exact Or.inl hxD
        · exact Or.inr ⟨hx, hxD⟩
      have hopen : IsOpen (out \ D) := by
        have h2 : out \ D = out ∩ (closure D)ᶜ := by
          ext x
          constructor
          · rintro ⟨hxi, hxD⟩
            refine ⟨hxi, ?_⟩
            intro hxc
            rw [hclD] at hxc
            rcases hxc with h | h
            · exact hxD h
            · have hxout : x ∈ (Set.range v)ᶜ := by rw [hicov]; exact Or.inr hxi
              exact hxout h
          · rintro ⟨hxi, hxc⟩
            exact ⟨hxi, fun hxD => hxc (subset_closure hxD)⟩
        rw [h2]
        exact hio2.inter isClosed_closure.isOpen_compl
      rcases hpc2.isConnected.isPreconnected.subset_or_subset hDo hopen
        (by rw [Set.disjoint_left]; exact fun x hx hx' => hx'.2 hx) hsub with h2 | h2
      · exfalso
        exact hiub (by rw [Set.Subset.antisymm h2 h1]; exact hDb)
      · exfalso
        have hDempty : D = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => (h2 (h1 hx)).2 hx
        exact hDc.nonempty.ne_empty hDempty
  have hEout : (closure D)ᶜ = out := by
    rw [hclD, hDins]
    ext x
    constructor
    · intro hx
      have hx1 : x ∉ ins := fun h => hx (Or.inl h)
      have hx2 : x ∉ Set.range v := fun h => hx (Or.inr h)
      have h3 : x ∈ (Set.range v)ᶜ := hx2
      rw [hicov] at h3
      rcases h3 with h | h
      · exact absurd h hx1
      · exact h
    · intro hx
      rintro (h | h)
      · exact Set.disjoint_left.mp hidisj h hx
      · have h3 : x ∈ (Set.range v)ᶜ := by rw [hicov]; exact Or.inr hx
        exact h3 h
  have hloc : ∀ p ∈ Set.range v, ∀ ε > 0, ∃ U U₁ U₂ : Set ℂ,
      LocalSepC (Set.range v) U U₁ U₂ ∧ p ∈ U ∧ U ⊆ Metric.ball p ε ∧
      (D ∩ U = U₁ ∨ D ∩ U = U₂) ∧ IsPreconnected (closure D ∩ U) := by
    intro p hp ε hε
    obtain ⟨U, U₁, U₂, hLS, hpU, hUsub⟩ := exists_localSepC_range_v v hv p hp hε
    have hside1 : U₁ ⊆ ins ∨ U₁ ⊆ out := by
      refine hLS.pc₁.isConnected.isPreconnected.subset_or_subset hio1 hio2 hidisj ?_
      intro x hx
      rw [← hicov]
      have hx' : x ∈ U₁ ∪ U₂ := Or.inl hx
      rw [hLS.union] at hx'
      exact hx'.2
    have hside2 : U₂ ⊆ ins ∨ U₂ ⊆ out := by
      refine hLS.pc₂.isConnected.isPreconnected.subset_or_subset hio1 hio2 hidisj ?_
      intro x hx
      rw [← hicov]
      have hx' : x ∈ U₁ ∪ U₂ := Or.inr hx
      rw [hLS.union] at hx'
      exact hx'.2
    have hinD : (U ∩ ins).Nonempty := by
      have hpcl : p ∈ closure ins := frontier_subset_closure (hifr1 ▸ hp)
      exact _root_.mem_closure_iff.mp hpcl U hLS.isOpen_U hpU
    have houtU : (U ∩ out).Nonempty := by
      have hpcl : p ∈ closure out := frontier_subset_closure (hifr2 ▸ hp)
      exact _root_.mem_closure_iff.mp hpcl U hLS.isOpen_U hpU
    have hnotDD : ¬ (U₁ ⊆ ins ∧ U₂ ⊆ ins) := by
      rintro ⟨h1, h2⟩
      have hsub : U ⊆ closure D := by
        intro x hxU
        rw [hclD, hDins]
        by_cases hx : x ∈ Set.range v
        · exact Or.inr hx
        · refine Or.inl ?_
          have hx'' : x ∈ U₁ ∪ U₂ := by
            rw [hLS.union]
            exact ⟨hxU, hx⟩
          rcases hx'' with h | h
          · exact h1 h
          · exact h2 h
      have hdisj : Disjoint U out := by
        rw [Set.disjoint_left]
        intro x hxU hxout
        have hxc : x ∈ (closure D)ᶜ := by rw [hEout]; exact hxout
        exact hxc (hsub hxU)
      obtain ⟨y, hyU, hyout⟩ := houtU
      exact Set.disjoint_left.mp hdisj hyU hyout
    have hnotOO : ¬ (U₁ ⊆ out ∧ U₂ ⊆ out) := by
      rintro ⟨h1, h2⟩
      have hdisj : Disjoint U ins := by
        rw [Set.disjoint_left]
        intro x hxU hxins
        have hx : x ∈ U \ Set.range v :=
          ⟨hxU, fun h => hDsub (by rw [hDins]; exact hxins) h⟩
        have hx'' : x ∈ U₁ ∪ U₂ := by rw [hLS.union]; exact hx
        rcases hx'' with h | h
        · exact Set.disjoint_left.mp hidisj hxins (h1 h)
        · exact Set.disjoint_left.mp hidisj hxins (h2 h)
      obtain ⟨y, hyU, hyins⟩ := hinD
      exact Set.disjoint_left.mp hdisj hyU hyins
    have hcase : (U₁ ⊆ ins ∧ U₂ ⊆ out) ∨ (U₂ ⊆ ins ∧ U₁ ⊆ out) := by
      rcases hside1 with h1 | h1 <;> rcases hside2 with h2 | h2
      · exact absurd ⟨h1, h2⟩ hnotDD
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact absurd ⟨h1, h2⟩ hnotOO
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hDU : D ∩ U = U₁ := by
        refine Set.Subset.antisymm ?_ ?_
        · intro x hx
          have hx' : x ∈ U \ Set.range v := ⟨hx.2, fun h => hDsub hx.1 h⟩
          have hx'' : x ∈ U₁ ∪ U₂ := by rw [hLS.union]; exact hx'
          rcases hx'' with h | h
          · exact h
          · exfalso
            exact Set.disjoint_left.mp hidisj (by rw [← hDins]; exact hx.1) (h2 h)
        · intro x hx
          refine ⟨by rw [hDins]; exact h1 hx, ?_⟩
          have hx'' : x ∈ U₁ ∪ U₂ := Or.inl hx
          rw [hLS.union] at hx''
          exact hx''.1
      refine ⟨U, U₁, U₂, hLS, hpU, hUsub, Or.inl hDU, ?_⟩
      have hcl : closure D ∩ U = U₁ ∪ (Set.range v ∩ U) := by
        have h1' : closure D ∩ U = (D ∩ U) ∪ (Set.range v ∩ U) := by
          rw [hclD]
          ext x
          constructor
          · rintro ⟨h | h, hx⟩
            · exact Or.inl ⟨h, hx⟩
            · exact Or.inr ⟨h, hx⟩
          · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
            · exact ⟨Or.inl h, hx⟩
            · exact ⟨Or.inr h, hx⟩
        rw [h1', hDU]
      rw [hcl]
      exact hLS.pc₁.isConnected.isPreconnected.subset_closure Set.subset_union_left
        (fun x hx => by
          rcases hx with h | h
          · exact subset_closure h
          · exact hLS.acc₁ x ⟨h.2, h.1⟩)
    · have hDU : D ∩ U = U₂ := by
        refine Set.Subset.antisymm ?_ ?_
        · intro x hx
          have hx' : x ∈ U \ Set.range v := ⟨hx.2, fun h => hDsub hx.1 h⟩
          have hx'' : x ∈ U₁ ∪ U₂ := by rw [hLS.union]; exact hx'
          rcases hx'' with h | h
          · exfalso
            exact Set.disjoint_left.mp hidisj (by rw [← hDins]; exact hx.1) (h2 h)
          · exact h
        · intro x hx
          refine ⟨by rw [hDins]; exact h1 hx, ?_⟩
          have hx'' : x ∈ U₁ ∪ U₂ := Or.inr hx
          rw [hLS.union] at hx''
          exact hx''.1
      refine ⟨U, U₁, U₂, hLS, hpU, hUsub, Or.inr hDU, ?_⟩
      have hcl : closure D ∩ U = U₂ ∪ (Set.range v ∩ U) := by
        have h1' : closure D ∩ U = (D ∩ U) ∪ (Set.range v ∩ U) := by
          rw [hclD]
          ext x
          constructor
          · rintro ⟨h | h, hx⟩
            · exact Or.inl ⟨h, hx⟩
            · exact Or.inr ⟨h, hx⟩
          · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
            · exact ⟨Or.inl h, hx⟩
            · exact ⟨Or.inr h, hx⟩
        rw [h1', hDU]
      rw [hcl]
      exact hLS.pc₂.isConnected.isPreconnected.subset_closure Set.subset_union_left
        (fun x hx => by
          rcases hx with h | h
          · exact subset_closure h
          · exact hLS.acc₂ x ⟨h.2, h.1⟩)
  have key : ¬ (∀ n : ℕ, ∃ T₁ T₂ : Set ℂ, IsClosed T₁ ∧ IsConnected T₁ ∧ IsClosed T₂ ∧
      IsConnected T₂ ∧ T₁ ∪ T₂ = closure D ∧ Metric.diam (T₁ ∩ T₂) ≤ 1 / ((n : ℝ) + 1) ∧
      η < Metric.diam T₁ ∧ η < Metric.diam T₂) := by
    intro hbad
    choose T₁ T₂ hb using hbad
    have hT1cl : ∀ n, IsClosed (T₁ n) := fun n => (hb n).1
    have hT1conn : ∀ n, IsConnected (T₁ n) := fun n => (hb n).2.1
    have hT2cl : ∀ n, IsClosed (T₂ n) := fun n => (hb n).2.2.1
    have hT2conn : ∀ n, IsConnected (T₂ n) := fun n => (hb n).2.2.2.1
    have hcover : ∀ n, T₁ n ∪ T₂ n = closure D := fun n => (hb n).2.2.2.2.1
    have hdia : ∀ n, Metric.diam (T₁ n ∩ T₂ n) ≤ 1 / ((n : ℝ) + 1) :=
      fun n => (hb n).2.2.2.2.2.1
    have hd1 : ∀ n, η < Metric.diam (T₁ n) := fun n => (hb n).2.2.2.2.2.2.1
    have hd2 : ∀ n, η < Metric.diam (T₂ n) := fun n => (hb n).2.2.2.2.2.2.2
    have hT1cpt : ∀ n, IsCompact (T₁ n) := fun n =>
      IsCompact.of_isClosed_subset hKc (hT1cl n) (hcover n ▸ Set.subset_union_left)
    have hT2cpt : ∀ n, IsCompact (T₂ n) := fun n =>
      IsCompact.of_isClosed_subset hKc (hT2cl n) (hcover n ▸ Set.subset_union_right)
    obtain ⟨A, hAcpt, hAne, hAsub, φ₁, hφ₁, hAconv⟩ := exists_hausdorff_limit_subseq (closure D) T₁
      hKc hT1cpt (fun n => (hT1conn n).nonempty) (fun n => hcover n ▸ Set.subset_union_left)
    obtain ⟨B, hBcpt, hBne, hBsub, φ₂, hφ₂, hBconv⟩ := exists_hausdorff_limit_subseq (closure D)
      (fun n => T₂ (φ₁ n)) hKc (fun n => hT2cpt (φ₁ n)) (fun n => (hT2conn (φ₁ n)).nonempty)
      (fun n => hcover (φ₁ n) ▸ Set.subset_union_right)
    set ψ : ℕ → ℕ := φ₁ ∘ φ₂ with hψdef
    have hψmono : StrictMono ψ := hφ₁.comp hφ₂
    have hψtop : Tendsto ψ atTop atTop := hψmono.tendsto_atTop
    have hAconv' : Tendsto (fun n => Metric.hausdorffDist (T₁ (ψ n)) A) atTop (𝓝 0) := by
      have h := hAconv.comp hφ₂.tendsto_atTop
      simpa [hψdef, Function.comp_def] using h
    have hBconv' : Tendsto (fun n => Metric.hausdorffDist (T₂ (ψ n)) B) atTop (𝓝 0) := by
      simpa [hψdef, Function.comp_def] using hBconv
    have hψ1 : Tendsto (fun n => 1 / ((ψ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hψtop
    have hfin1 : ∀ n, Metric.hausdorffEDist (T₁ (ψ n)) A ≠ ⊤ := fun n =>
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hT1conn (ψ n)).nonempty hAne
        (hT1cpt (ψ n)).isBounded hAcpt.isBounded
    have hfin2 : ∀ n, Metric.hausdorffEDist (T₂ (ψ n)) B ≠ ⊤ := fun n =>
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hT2conn (ψ n)).nonempty hBne
        (hT2cpt (ψ n)).isBounded hBcpt.isBounded
    have hAconn : IsConnected A := isConnected_of_hausdorffDist_tendsto_zero
      (fun n => T₁ (ψ n)) A (fun n => hT1conn (ψ n)) (fun n => hT1cpt (ψ n)) hAcpt hAne hAconv'
    have hBconn : IsConnected B := isConnected_of_hausdorffDist_tendsto_zero
      (fun n => T₂ (ψ n)) B (fun n => hT2conn (ψ n)) (fun n => hT2cpt (ψ n)) hBcpt hBne hBconv'
    have hAB : A ∪ B = closure D := union_eq_of_hausdorff_tendsto (closure D) _
      (fun n => T₂ (ψ n)) A B hAcpt.isClosed hBcpt.isClosed hKcl hAne hBne
      (fun n => (hT1conn (ψ n)).nonempty) (fun n => (hT2conn (ψ n)).nonempty) hfin1 hfin2
      hAconv' hBconv' (fun n => hcover (ψ n))
    have hAdiam : η ≤ Metric.diam A := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hAconv' ((η - Metric.diam A) / 4)
        (by linarith)
      have hNb := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at hNb
      have hbdd : Metric.diam (T₁ (ψ N)) ≤ Metric.diam A + 2 * ((η - Metric.diam A) / 4) := by
        refine Metric.diam_le_of_forall_dist_le
          (by linarith [Metric.diam_nonneg (s := A)]) fun x hx y hy => ?_
        have hx1 : Metric.infDist x A ≤ Metric.hausdorffDist (T₁ (ψ N)) A :=
          Metric.infDist_le_hausdorffDist_of_mem hx (hfin1 N)
        obtain ⟨a, ha, hxa⟩ := Metric.infDist_lt_iff hAne |>.mp (lt_of_le_of_lt hx1 hNb)
        have hy1 : Metric.infDist y A ≤ Metric.hausdorffDist (T₁ (ψ N)) A :=
          Metric.infDist_le_hausdorffDist_of_mem hy (hfin1 N)
        obtain ⟨b, hb', hyb⟩ := Metric.infDist_lt_iff hAne |>.mp (lt_of_le_of_lt hy1 hNb)
        have h1 : dist x y ≤ dist x a + dist a y := dist_triangle x a y
        have h2 : dist a y ≤ dist a b + dist b y := dist_triangle a b y
        have h3 : dist a b ≤ Metric.diam A := Metric.dist_le_diam_of_mem hAcpt.isBounded ha hb'
        have h4 : dist b y = dist y b := dist_comm b y
        linarith
      have h5 := hd1 (ψ N)
      linarith
    have hBdiam : η ≤ Metric.diam B := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hBconv' ((η - Metric.diam B) / 4)
        (by linarith)
      have hNb := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at hNb
      have hbdd : Metric.diam (T₂ (ψ N)) ≤ Metric.diam B + 2 * ((η - Metric.diam B) / 4) := by
        refine Metric.diam_le_of_forall_dist_le
          (by linarith [Metric.diam_nonneg (s := B)]) fun x hx y hy => ?_
        have hx1 : Metric.infDist x B ≤ Metric.hausdorffDist (T₂ (ψ N)) B :=
          Metric.infDist_le_hausdorffDist_of_mem hx (hfin2 N)
        obtain ⟨a, ha, hxa⟩ := Metric.infDist_lt_iff hBne |>.mp (lt_of_le_of_lt hx1 hNb)
        have hy1 : Metric.infDist y B ≤ Metric.hausdorffDist (T₂ (ψ N)) B :=
          Metric.infDist_le_hausdorffDist_of_mem hy (hfin2 N)
        obtain ⟨b, hb', hyb⟩ := Metric.infDist_lt_iff hBne |>.mp (lt_of_le_of_lt hy1 hNb)
        have h1 : dist x y ≤ dist x a + dist a y := dist_triangle x a y
        have h2 : dist a y ≤ dist a b + dist b y := dist_triangle a b y
        have h3 : dist a b ≤ Metric.diam B := Metric.dist_le_diam_of_mem hBcpt.isBounded ha hb'
        have h4 : dist b y = dist y b := dist_comm b y
        linarith
      have h5 := hd2 (ψ N)
      linarith
    have hkeypoint : ∀ q ∈ A ∩ B, ∀ ε' > 0, ∃ N, ∀ n ≥ N,
        ∃ c ∈ T₁ (ψ n) ∩ T₂ (ψ n), dist q c < ε' := by
      rintro q ⟨hqA, hqB⟩ ε' hε'
      have hqcl : q ∈ closure D := hAsub hqA
      have hex1 : ∀ n, ∃ x ∈ T₁ (ψ n),
          dist q x ≤ Metric.hausdorffDist (T₁ (ψ n)) A + 1 / ((ψ n : ℝ) + 1) := by
        intro n
        have h1 : Metric.infDist q (T₁ (ψ n)) ≤ Metric.hausdorffDist A (T₁ (ψ n)) :=
          Metric.infDist_le_hausdorffDist_of_mem hqA
            (by rw [Metric.hausdorffEDist_comm]; exact hfin1 n)
        have h2 : Metric.hausdorffDist (T₁ (ψ n)) A = Metric.hausdorffDist A (T₁ (ψ n)) :=
          Metric.hausdorffDist_comm
        have h3 : Metric.infDist q (T₁ (ψ n)) <
            Metric.hausdorffDist (T₁ (ψ n)) A + 1 / ((ψ n : ℝ) + 1) := by
          rw [h2]
          linarith [show (0 : ℝ) < 1 / ((ψ n : ℝ) + 1) by positivity]
        obtain ⟨x, hx, hqx⟩ := Metric.infDist_lt_iff (hT1conn (ψ n)).nonempty |>.mp h3
        exact ⟨x, hx, le_of_lt hqx⟩
      choose a haT haD using hex1
      have hex2 : ∀ n, ∃ x ∈ T₂ (ψ n),
          dist q x ≤ Metric.hausdorffDist (T₂ (ψ n)) B + 1 / ((ψ n : ℝ) + 1) := by
        intro n
        have h1 : Metric.infDist q (T₂ (ψ n)) ≤ Metric.hausdorffDist B (T₂ (ψ n)) :=
          Metric.infDist_le_hausdorffDist_of_mem hqB
            (by rw [Metric.hausdorffEDist_comm]; exact hfin2 n)
        have h2 : Metric.hausdorffDist (T₂ (ψ n)) B = Metric.hausdorffDist B (T₂ (ψ n)) :=
          Metric.hausdorffDist_comm
        have h3 : Metric.infDist q (T₂ (ψ n)) <
            Metric.hausdorffDist (T₂ (ψ n)) B + 1 / ((ψ n : ℝ) + 1) := by
          rw [h2]
          linarith [show (0 : ℝ) < 1 / ((ψ n : ℝ) + 1) by positivity]
        obtain ⟨x, hx, hqx⟩ := Metric.infDist_lt_iff (hT2conn (ψ n)).nonempty |>.mp h3
        exact ⟨x, hx, le_of_lt hqx⟩
      choose b hbT hbD using hex2
      have hlima : Tendsto a atTop (𝓝 q) := by
        rw [Metric.tendsto_atTop]
        intro e he
        have h0 : Tendsto (fun n => Metric.hausdorffDist (T₁ (ψ n)) A + 1 / ((ψ n : ℝ) + 1))
            atTop (𝓝 0) := by simpa using hAconv'.add hψ1
        rw [Metric.tendsto_atTop] at h0
        obtain ⟨N, hN⟩ := h0 e he
        refine ⟨N, fun n hn => ?_⟩
        have h1 := haD n
        have h2 := hN n hn
        rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (add_nonneg Metric.hausdorffDist_nonneg (by positivity))] at h2
        rw [dist_comm]
        exact lt_of_le_of_lt h1 h2
      have hlimb : Tendsto b atTop (𝓝 q) := by
        rw [Metric.tendsto_atTop]
        intro e he
        have h0 : Tendsto (fun n => Metric.hausdorffDist (T₂ (ψ n)) B + 1 / ((ψ n : ℝ) + 1))
            atTop (𝓝 0) := by simpa using hBconv'.add hψ1
        rw [Metric.tendsto_atTop] at h0
        obtain ⟨N, hN⟩ := h0 e he
        refine ⟨N, fun n hn => ?_⟩
        have h1 := hbD n
        have h2 := hN n hn
        rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (add_nonneg Metric.hausdorffDist_nonneg (by positivity))] at h2
        rw [dist_comm]
        exact lt_of_le_of_lt h1 h2
      have hq' : q ∈ D ∪ Set.range v := by rw [← hclD]; exact hqcl
      rcases hq' with hqD | hqV
      · obtain ⟨r, hrpos, hrsub⟩ : ∃ r > 0, Metric.closedBall q r ⊆ D := by
          obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hDo.mem_nhds hqD)
          refine ⟨r / 2, by linarith, fun x hx => hsub ?_⟩
          rw [Metric.mem_ball]
          have hx' := Metric.mem_closedBall.mp hx
          linarith
        set r' : ℝ := min (r / 2) (ε' / 2) with hr'def
        have hr'pos : 0 < r' := lt_min (by linarith) (by linarith)
        have hr'ε : r' < ε' := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        have hr'r : r' ≤ r := le_trans (min_le_left _ _) (by linarith)
        obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N,
            (∃ x ∈ T₁ (ψ n), dist q x < r') ∧ (∃ y ∈ T₂ (ψ n), dist q y < r') := by
          obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hlima r' hr'pos
          obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hlimb r' hr'pos
          refine ⟨max N₁ N₂, fun n hn => ?_⟩
          exact ⟨⟨a n, haT n, by rw [dist_comm]; exact hN₁ n (le_trans (le_max_left _ _) hn)⟩,
            ⟨b n, hbT n, by rw [dist_comm]; exact hN₂ n (le_trans (le_max_right _ _) hn)⟩⟩
        refine ⟨N, fun n hn => ?_⟩
        obtain ⟨⟨x, hxT, hxq⟩, ⟨y, hyT, hyq⟩⟩ := hN n hn
        have hxq' : x ∈ Metric.ball q r' := Metric.mem_ball.mpr (by rw [dist_comm]; exact hxq)
        have hyq' : y ∈ Metric.ball q r' := Metric.mem_ball.mpr (by rw [dist_comm]; exact hyq)
        have hball : Metric.ball q r' ⊆ T₁ (ψ n) ∪ T₂ (ψ n) := by
          rw [hcover (ψ n)]
          exact fun z hz => subset_closure (hrsub (Metric.ball_subset_closedBall (Metric.ball_subset_ball hr'r hz)))
        have hinter : (Metric.ball q r' ∩ (T₁ (ψ n) ∩ T₂ (ψ n))).Nonempty := by
          by_contra hemp
          rw [Set.not_nonempty_iff_eq_empty] at hemp
          rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
            (Metric.isConnected_ball hr'pos).isPreconnected) (T₁ (ψ n)) (T₂ (ψ n))
            (hT1cl (ψ n)) (hT2cl (ψ n)) hball hemp with hc | hc
          · exact (Set.eq_empty_iff_forall_notMem.mp hemp) y ⟨hyq', hc hyq', hyT⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hemp) x ⟨hxq', hxT, hc hxq'⟩
        obtain ⟨c, hc⟩ := hinter
        have hcq : dist q c < r' := by
          have h := Metric.mem_ball.mp hc.1
          rwa [dist_comm] at h
        exact ⟨c, hc.2, lt_trans hcq hr'ε⟩
      · obtain ⟨U, U₁, U₂, hLS, hqU, hUsub, hDU, hSpre⟩ := hloc q hqV ε' hε'
        obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ > 0, Metric.ball q δ ⊆ U := by
          obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hLS.isOpen_U.mem_nhds hqU)
          exact ⟨δ, hδ, hsub⟩
        obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hlima δ hδpos
        obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hlimb δ hδpos
        refine ⟨max N₁ N₂, fun n hn => ?_⟩
        have haU : a n ∈ U :=
          hδsub (Metric.mem_ball.mpr (hN₁ n (le_trans (le_max_left _ _) hn)))
        have hbU : b n ∈ U :=
          hδsub (Metric.mem_ball.mpr (hN₂ n (le_trans (le_max_right _ _) hn)))
        have haS : a n ∈ closure D ∩ U := ⟨hcover (ψ n) ▸ Set.subset_union_left (haT n), haU⟩
        have hbS : b n ∈ closure D ∩ U := ⟨hcover (ψ n) ▸ Set.subset_union_right (hbT n), hbU⟩
        have hinter : ((closure D ∩ U) ∩ (T₁ (ψ n) ∩ T₂ (ψ n))).Nonempty := by
          by_contra hemp
          rw [Set.not_nonempty_iff_eq_empty] at hemp
          rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hSpre) (T₁ (ψ n)) (T₂ (ψ n))
            (hT1cl (ψ n)) (hT2cl (ψ n)) (fun z hz => by rw [hcover (ψ n)]; exact hz.1)
            hemp with hc | hc
          · exact (Set.eq_empty_iff_forall_notMem.mp hemp) (b n) ⟨hbS, hc hbS, hbT n⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hemp) (a n) ⟨haS, haT n, hc haS⟩
        obtain ⟨c, hc⟩ := hinter
        have hcq : dist q c < ε' := by
          have h := Metric.mem_ball.mp (hUsub hc.1.2)
          rwa [dist_comm] at h
        exact ⟨c, hc.2, hcq⟩
    have hABne : (A ∩ B).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hdisjAB : Disjoint A B := Set.disjoint_iff_inter_eq_empty.mpr hemp
      obtain ⟨r, hrpos, hr⟩ := Metric.exists_pos_forall_lt_edist hAcpt hBcpt.isClosed hdisjAB
      set δ : ℝ := (r : ℝ) / 4 with hδdef
      have hδpos : 0 < δ := by rw [hδdef]; positivity
      obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hAconv' δ hδpos
      obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hBconv' δ hδpos
      have h1 : T₁ (ψ (max N₁ N₂)) ⊆ Metric.thickening δ A := by
        intro x hx
        have h3 := hN₁ (max N₁ N₂) (le_max_left _ _)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at h3
        have h4 : Metric.infDist x A < δ :=
          lt_of_le_of_lt (Metric.infDist_le_hausdorffDist_of_mem hx (hfin1 _)) h3
        obtain ⟨a, ha, hxa⟩ := Metric.infDist_lt_iff hAne |>.mp h4
        exact Metric.mem_thickening_iff.mpr ⟨a, ha, hxa⟩
      have h2 : T₂ (ψ (max N₁ N₂)) ⊆ Metric.thickening δ B := by
        intro x hx
        have h3 := hN₂ (max N₁ N₂) (le_max_right _ _)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] at h3
        have h4 : Metric.infDist x B < δ :=
          lt_of_le_of_lt (Metric.infDist_le_hausdorffDist_of_mem hx (hfin2 _)) h3
        obtain ⟨a, ha, hxa⟩ := Metric.infDist_lt_iff hBne |>.mp h4
        exact Metric.mem_thickening_iff.mpr ⟨a, ha, hxa⟩
      have hdisjT : Disjoint (Metric.thickening δ A) (Metric.thickening δ B) := by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        obtain ⟨a, ha, hza⟩ := Metric.mem_thickening_iff.mp hz1
        obtain ⟨b, hb, hzb⟩ := Metric.mem_thickening_iff.mp hz2
        have hrab : (r : ℝ) < dist a b := by
          have h := hr a ha b hb
          rw [edist_dist] at h
          by_contra hle
          have h4 : ENNReal.ofReal (dist a b) ≤ ENNReal.ofReal ((r : ℝ)) :=
            ENNReal.ofReal_le_ofReal (not_lt.mp hle)
          rw [ENNReal.ofReal_coe_nnreal] at h4
          exact absurd h (not_lt.mpr h4)
        have hlt : dist a b < (r : ℝ) := by
          have hc1 : dist a z = dist z a := dist_comm a z
          rw [hδdef] at hza hzb
          linarith [dist_triangle a z b]
        linarith
      have hsep : T₁ (ψ (max N₁ N₂)) ∩ T₂ (ψ (max N₁ N₂)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact Set.disjoint_left.mp hdisjT (h1 hx.1) (h2 hx.2)
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hKconn.isPreconnected)
        (T₁ (ψ (max N₁ N₂))) (T₂ (ψ (max N₁ N₂))) (hT1cl _) (hT2cl _)
        (fun z hz => by rw [← hcover (ψ (max N₁ N₂))] at hz; exact hz)
        (by rw [hsep, Set.inter_empty]) with hc | hc
      · refine (hT2conn (ψ (max N₁ N₂))).nonempty.ne_empty ?_
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        have hmem : y ∈ T₁ (ψ (max N₁ N₂)) ∩ T₂ (ψ (max N₁ N₂)) :=
          ⟨hc (hcover (ψ (max N₁ N₂)) ▸ Set.subset_union_right hy), hy⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hsep) y hmem
      · refine (hT1conn (ψ (max N₁ N₂))).nonempty.ne_empty ?_
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        have hmem : y ∈ T₁ (ψ (max N₁ N₂)) ∩ T₂ (ψ (max N₁ N₂)) :=
          ⟨hy, hc (hcover (ψ (max N₁ N₂)) ▸ Set.subset_union_left hy)⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hsep) y hmem
    obtain ⟨p, hpA, hpB⟩ := hABne
    have hsubsing : (A ∩ B).Subsingleton := by
      intro q hq q' hq'
      by_contra hne
      have hpq' : 0 < dist q q' := dist_pos.mpr hne
      obtain ⟨N₁, hN₁⟩ := hkeypoint q hq (dist q q' / 4) (by linarith)
      obtain ⟨N₂, hN₂⟩ := hkeypoint q' hq' (dist q q' / 4) (by linarith)
      obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp hψ1 (dist q q' / 4) (by linarith)
      have h4 := hN₃ (max (max N₁ N₂) N₃) (le_max_right _ _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h4
      obtain ⟨c, hc, hcq⟩ := hN₁ (max (max N₁ N₂) N₃)
        (le_trans (le_max_left _ _) (le_max_left _ _))
      obtain ⟨c', hc', hc'q'⟩ := hN₂ (max (max N₁ N₂) N₃)
        (le_trans (le_max_right _ _) (le_max_left _ _))
      have hc'q'' : dist c' q' < dist q q' / 4 := by rw [dist_comm]; exact hc'q'
      have hd : dist c c' ≤ Metric.diam (T₁ (ψ (max (max N₁ N₂) N₃)) ∩ T₂ (ψ (max (max N₁ N₂) N₃))) :=
        Metric.dist_le_diam_of_mem
          ((hT1cpt _).inter_right (hT2cl _)).isBounded hc hc'
      have h5 := hdia (ψ (max (max N₁ N₂) N₃))
      have t1 : dist q q' ≤ dist q c + dist c q' := dist_triangle q c q'
      have t2 : dist c q' ≤ dist c c' + dist c' q' := dist_triangle c c' q'
      have hc'' : dist c q' < dist q q' / 4 := lt_of_le_of_lt t2 (by linarith)
      linarith
    have hpq : ∀ q ∈ A ∩ B, q = p := fun q hq => hsubsing hq ⟨hpA, hpB⟩
    have hintAB : A ∩ B ⊆ ({p} : Set ℂ) := fun q hq => Set.mem_singleton_iff.mpr (hpq q hq)
    -- `A` and `B` meet in the single point `p`, so neither can have diameter `≥ η > 0`
    have habsurd : ¬ (A = {p} ∨ B = {p}) := by
      rintro (h | h)
      · rw [h, Metric.diam_singleton] at hAdiam
        linarith
      · rw [h, Metric.diam_singleton] at hBdiam
        linarith
    have hfinal : False := by
      have hp' : p ∈ D ∪ Set.range v := by rw [← hclD]; exact hAsub hpA
      rcases hp' with hpD | hpV
      · -- `p` is an interior point: a punctured disc around `p` cannot be covered by `A` and `B`
        obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hDo.mem_nhds hpD)
        have hcover' : Metric.ball p r ⊆ A ∪ B := by
          intro z hz
          rw [hAB]
          exact subset_closure (hrsub hz)
        exact habsurd (eq_singleton_of_closed_connected_of_cover_ball A B p r hrpos
          hAcpt.isClosed hBcpt.isClosed hAconn hBconn hcover' hpA hpB hintAB)
      · -- `p` is on the frontier: a local piece of `closure D` decides the side
        obtain ⟨U, U₁, U₂, hLS, hpU, _hUsub, hDU, _hSpre⟩ := hloc p hpV 1 (by norm_num)
        have hWpc : IsPreconnected (D ∩ U) := by
          rcases hDU with h | h
          · rw [h]; exact hLS.pc₁.isConnected.isPreconnected
          · rw [h]; exact hLS.pc₂.isConnected.isPreconnected
        have hWsub : D ∩ U ⊆ closure D ∩ U := fun z hz => ⟨subset_closure hz.1, hz.2⟩
        have hWnotp : p ∉ D ∩ U := by
          rintro ⟨hpD', hpU'⟩
          have h1 : p ∈ U₁ ∪ U₂ := by
            have hz : p ∈ D ∩ U := ⟨hpD', hpU'⟩
            rcases hDU with h | h
            · exact Or.inl (h ▸ hz)
            · exact Or.inr (h ▸ hz)
          rw [hLS.union] at h1
          obtain ⟨-, hpv⟩ := h1
          exact hpv hpV
        have hclW : closure D ∩ U ⊆ closure (D ∩ U) := by
          intro z hz
          obtain ⟨hzD, hzU⟩ := hz
          rw [_root_.mem_closure_iff]
          intro O hO hzO
          obtain ⟨y, hyOU, hyD⟩ :=
            _root_.mem_closure_iff.mp hzD (O ∩ U) (hO.inter hLS.isOpen_U) ⟨hzO, hzU⟩
          obtain ⟨hyO, hyU⟩ := hyOU
          exact ⟨y, hyO, hyD, hyU⟩
        exact habsurd (eq_singleton_of_isClosed_connected_cover_of_local A B (closure D) U (D ∩ U) p
          hAcpt.isClosed hBcpt.isClosed hAconn hBconn hLS.isOpen_U hpU hpA hpB hAB hintAB
          hWpc hWsub hWnotp hclW)
    exact hfinal
  by_contra hcon
  have hcon' : ∀ ε > 0, ¬ (∀ T₁ T₂ : Set ℂ, IsClosed T₁ → IsConnected T₁ → IsClosed T₂ →
      IsConnected T₂ → T₁ ∪ T₂ = closure D → Metric.diam (T₁ ∩ T₂) ≤ ε →
      Metric.diam T₁ ≤ η ∨ Metric.diam T₂ ≤ η) := fun ε hε h => hcon ⟨ε, hε, h⟩
  exact key (fun n => by
    by_contra hbad
    apply hcon' (1 / ((n : ℝ) + 1)) (by positivity)
    intro T₁ T₂ hi1 hc1 hi2 hc2 hu hdd
    by_contra h7
    exact hbad ⟨T₁, T₂, hi1, hc1, hi2, hc2, hu, hdd,
      not_le.mp fun h => h7 (Or.inl h), not_le.mp fun h => h7 (Or.inr h)⟩)


end Work.RPB.B1a

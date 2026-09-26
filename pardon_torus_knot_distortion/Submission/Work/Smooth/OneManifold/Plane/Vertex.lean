import Mathlib
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_triple
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential

/-!
# The plane model of a tangential vertex

Let `f g h : ℝ × ℝ → ℝ` be `C¹` with a common zero at `p`, and let `r ≠ 0` be a direction in which
all three derivatives at `p` are positive.  Then the zero set of the maximum,
`{q | max (max (f q) (g q)) (h q) = 0}`,
is locally an arc: in coordinates in which `r` is the first coordinate direction
(`Work.Smooth.OneManifold.vertexLinearMap`), the zero set of each of the three functions is a graph
`x = ψ y` over the *second* coordinate (`Work.Smooth.BoxGeneric.LocalArc.exists_root_triple`), and
the zero set of the maximum is the graph of the *minimum* `min (min ψ φ) χ` of the three implicit
functions — a graph of a continuous function, hence locally an arc.

This is the plane model of a *tangential vertex* of a box, i.e. of the fourth and last local model
of the box-norm level set (see `Work.Smooth.OneManifold.isLocallyEuclideanAt_of_vertex_tangent`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **The linear map sending `(1,0)` to `r`** (`r = (a,b)`): the reflection in the line through
`r`, scaled by `‖r‖`, i.e. `(x,y) ↦ (a x + b y, b x - a y)`. -/
def vertexLinearMap (r : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((r.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) + (r.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    ((r.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) - (r.1 • ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem vertexLinearMap_apply (r v : ℝ × ℝ) :
    vertexLinearMap r v = (r.1 * v.1 + r.2 * v.2, r.2 * v.1 - r.1 * v.2) := rfl

theorem vertexLinearMap_one_zero (r : ℝ × ℝ) : vertexLinearMap r (1, 0) = r := by
  ext <;> simp

theorem vertexLinearMap_sq (r : ℝ × ℝ) (v : ℝ × ℝ) :
    vertexLinearMap r (vertexLinearMap r v) = (r.1 ^ 2 + r.2 ^ 2) • v := by
  ext <;> simp <;> ring

/-- `max (max a b) c = 0` in terms of the three numbers. -/
lemma max_three_eq_zero_iff {a b c : ℝ} :
    max (max a b) c = 0 ↔ a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0 ∧ (a = 0 ∨ b = 0 ∨ c = 0) := by
  constructor
  · intro h
    have h1 : max a b ≤ 0 := le_trans (le_max_left _ _) (le_of_eq h)
    have h2 : c ≤ 0 := le_trans (le_max_right _ _) (le_of_eq h)
    have ha : a ≤ 0 := le_trans (le_max_left _ _) h1
    have hb : b ≤ 0 := le_trans (le_max_right _ _) h1
    refine ⟨ha, hb, h2, ?_⟩
    by_contra hc
    rw [not_or, not_or] at hc
    obtain ⟨hc1, hc2, hc3⟩ := hc
    have hlt : max (max a b) c < 0 :=
      max_lt (max_lt (lt_of_le_of_ne ha hc1) (lt_of_le_of_ne hb hc2)) (lt_of_le_of_ne h2 hc3)
    rw [h] at hlt
    exact lt_irrefl 0 hlt
  · rintro ⟨ha, hb, hc, h0⟩
    rcases h0 with h0 | h0 | h0
    · rw [h0, max_eq_left hb, max_eq_left hc]
    · rw [h0, max_eq_right ha, max_eq_left hc]
    · rw [h0, max_eq_right (max_le ha hb)]

/-- **The zero set of the maximum of three functions with a common positive directional derivative
is locally an arc.** -/
theorem isLocallyArc_max_three {f g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hh : ContDiff ℝ 1 h) {p : ℝ × ℝ} (hfp : f p = 0) (hgp : g p = 0) (hhp : h p = 0)
    {r : ℝ × ℝ} (hr : r ≠ 0) (hdf : 0 < fderiv ℝ f p r) (hdg : 0 < fderiv ℝ g p r)
    (hdh : 0 < fderiv ℝ h p r) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
      IsLocallyArcP (V ∩ {q : ℝ × ℝ | max (max (f q) (g q)) (h q) = 0}) := by
  -- the linear change of coordinates with `M (1,0) = r`
  set s : ℝ := r.1 ^ 2 + r.2 ^ 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    rcases eq_or_ne r.1 0 with h | h
    · have hr2 : r.2 ≠ 0 := by
        intro h2
        exact hr (Prod.ext h h2)
      nlinarith [sq_pos_of_ne_zero hr2, sq_nonneg r.1]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg r.2]
  let M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := vertexLinearMap r
  have hM10 : M (1, 0) = r := vertexLinearMap_one_zero r
  have hMM : ∀ v : ℝ × ℝ, M (M v) = s • v := vertexLinearMap_sq r
  let N : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := s⁻¹ • M
  have hNM : ∀ v : ℝ × ℝ, N (M v) = v := by
    intro v
    show s⁻¹ • M (M v) = v
    rw [hMM v, smul_smul, inv_mul_cancel₀ (ne_of_gt hspos), one_smul]
  have hMN : ∀ v : ℝ × ℝ, M (N v) = v := by
    intro v
    show M (s⁻¹ • M v) = v
    rw [map_smul, hMM v, smul_smul, inv_mul_cancel₀ (ne_of_gt hspos), one_smul]
  have hMinj : Function.Injective M := fun u v huv => by
    have h := congrArg N huv
    rwa [hNM u, hNM v] at h
  -- the affine change of coordinates
  let T : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  { toFun := fun z => p + M z
    invFun := fun q => N (q - p)
    left_inv := fun z => by
      show N ((p + M z) - p) = z
      rw [add_sub_cancel_left, hNM]
    right_inv := fun q => by
      show p + M (N (q - p)) = q
      rw [hMN, add_sub_cancel]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hT_apply : ∀ z : ℝ × ℝ, (T z : ℝ × ℝ) = p + M z := fun z => rfl
  -- the pulled-back functions
  set F : ℝ × ℝ → ℝ := fun z => f (p + M z) with hFdef
  set G : ℝ × ℝ → ℝ := fun z => g (p + M z) with hGdef
  set H : ℝ × ℝ → ℝ := fun z => h (p + M z) with hHdef
  have hFcd : ContDiff ℝ 1 F := by rw [hFdef]; fun_prop
  have hGcd : ContDiff ℝ 1 G := by rw [hGdef]; fun_prop
  have hHcd : ContDiff ℝ 1 H := by rw [hHdef]; fun_prop
  have hF0 : F 0 = 0 := by simp [hFdef, hfp]
  have hG0 : G 0 = 0 := by simp [hGdef, hgp]
  have hH0 : H 0 = 0 := by simp [hHdef, hhp]
  have hFd : 0 < (fderiv ℝ F 0) (1, 0) := by
    rw [hFdef, Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear f hf p M]
    simpa [hM10] using hdf
  have hGd : 0 < (fderiv ℝ G 0) (1, 0) := by
    rw [hGdef, Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear g hg p M]
    simpa [hM10] using hdg
  have hHd : 0 < (fderiv ℝ H 0) (1, 0) := by
    rw [hHdef, Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear h hh p M]
    simpa [hM10] using hdh
  -- the three implicit functions
  obtain ⟨Rx, Ry, hRxpos, hRypos, ψ, φ, χ, hψ0, hφ0, hχ0, hψcont, hφcont, hχcont, hroot,
    hsign, hzero⟩ :=
    Work.Smooth.BoxGeneric.LocalArc.exists_root_triple hFcd hGcd hHcd hF0 hG0 hH0 hFd hGd hHd
  -- shrink the second coordinate so that the three graphs stay in the strip `|x| < Rx`
  have hmem_Ry : Set.Ioo (-Ry) Ry ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hψnb : ψ ⁻¹' Set.Ioo (-Rx) Rx ∈ nhds (0 : ℝ) := by
    refine (hψcont.continuousAt hmem_Ry).preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hψ0]
    exact ⟨by linarith, by linarith⟩
  have hφnb : φ ⁻¹' Set.Ioo (-Rx) Rx ∈ nhds (0 : ℝ) := by
    refine (hφcont.continuousAt hmem_Ry).preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hφ0]
    exact ⟨by linarith, by linarith⟩
  have hχnb : χ ⁻¹' Set.Ioo (-Rx) Rx ∈ nhds (0 : ℝ) := by
    refine (hχcont.continuousAt hmem_Ry).preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hχ0]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨δψ, hδψpos, hδψ⟩ := Metric.mem_nhds_iff.mp hψnb
  obtain ⟨δφ, hδφpos, hδφ⟩ := Metric.mem_nhds_iff.mp hφnb
  obtain ⟨δχ, hδχpos, hδχ⟩ := Metric.mem_nhds_iff.mp hχnb
  set Ry' : ℝ := min (min (min δψ δφ) δχ) Ry with hRy'def
  have hRy'pos : 0 < Ry' :=
    lt_min (lt_min (lt_min hδψpos hδφpos) hδχpos) hRypos
  have hRy'leRy : Ry' ≤ Ry := min_le_right _ _
  have hRy'leψ : Ry' ≤ δψ :=
    le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
  have hRy'leφ : Ry' ≤ δφ :=
    le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
  have hRy'leχ : Ry' ≤ δχ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  -- the box of parameters
  set A : Set (ℝ × ℝ) := {z : ℝ × ℝ | |z.1| < Rx ∧ |z.2| < Ry'} with hAdef
  have hAopen : IsOpen A := by
    rw [hAdef]
    have h1 : IsOpen {z : ℝ × ℝ | |z.1| < Rx} := by
      have heq : {z : ℝ × ℝ | |z.1| < Rx} = {z : ℝ × ℝ | -Rx < z.1} ∩ {z | z.1 < Rx} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
      rw [heq]
      exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)
    have h2 : IsOpen {z : ℝ × ℝ | |z.2| < Ry'} := by
      have heq : {z : ℝ × ℝ | |z.2| < Ry'} = {z : ℝ × ℝ | -Ry' < z.2} ∩ {z | z.2 < Ry'} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
      rw [heq]
      exact (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)
    exact h1.inter h2
  have hsignA : ∀ z ∈ A, (F z ≤ 0 ↔ z.1 ≤ ψ z.2) ∧ (G z ≤ 0 ↔ z.1 ≤ φ z.2) ∧
      (H z ≤ 0 ↔ z.1 ≤ χ z.2) := by
    intro z hz
    rw [hAdef] at hz
    exact hsign z.1 z.2 (le_of_lt hz.1) (le_of_lt (lt_of_lt_of_le hz.2 hRy'leRy))
  have hzeroA : ∀ z ∈ A, (F z = 0 ↔ z.1 = ψ z.2) ∧ (G z = 0 ↔ z.1 = φ z.2) ∧
      (H z = 0 ↔ z.1 = χ z.2) := by
    intro z hz
    rw [hAdef] at hz
    exact hzero z.1 z.2 (le_of_lt hz.1) (le_of_lt (lt_of_lt_of_le hz.2 hRy'leRy))
  -- the graph of the minimum of the three implicit functions
  have hmcont : ContinuousOn (fun y : ℝ => min (min (ψ y) (φ y)) (χ y))
      (Set.Ioo (-Ry') Ry') := by
    refine ContinuousOn.inf (ContinuousOn.inf ?_ ?_) ?_
    · exact hψcont.mono fun y hy => ⟨by linarith [hy.1, hRy'leRy], by linarith [hy.2, hRy'leRy]⟩
    · exact hφcont.mono fun y hy => ⟨by linarith [hy.1, hRy'leRy], by linarith [hy.2, hRy'leRy]⟩
    · exact hχcont.mono fun y hy => ⟨by linarith [hy.1, hRy'leRy], by linarith [hy.2, hRy'leRy]⟩
  have hgraph : {z : ℝ × ℝ | z.2 ∈ Set.Ioo (-Ry') Ry' ∧
        z.1 = min (min (ψ z.2) (φ z.2)) (χ z.2)}
      = A ∩ {z : ℝ × ℝ | max (max (F z) (G z)) (H z) = 0} := by
    ext z
    constructor
    · rintro ⟨hz2, hz1⟩
      have hψabs : |ψ z.2| < Rx := by
        have hmem : ψ z.2 ∈ Set.Ioo (-Rx) Rx := hδψ (by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
          exact ⟨by linarith [hz2.1, hRy'leψ], by linarith [hz2.2, hRy'leψ]⟩)
        rwa [abs_lt]
      have hφabs : |φ z.2| < Rx := by
        have hmem : φ z.2 ∈ Set.Ioo (-Rx) Rx := hδφ (by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
          exact ⟨by linarith [hz2.1, hRy'leφ], by linarith [hz2.2, hRy'leφ]⟩)
        rwa [abs_lt]
      have hχabs : |χ z.2| < Rx := by
        have hmem : χ z.2 ∈ Set.Ioo (-Rx) Rx := hδχ (by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
          exact ⟨by linarith [hz2.1, hRy'leχ], by linarith [hz2.2, hRy'leχ]⟩)
        rwa [abs_lt]
      have hmabs : |min (min (ψ z.2) (φ z.2)) (χ z.2)| < Rx := by
        rcases min_choice (min (ψ z.2) (φ z.2)) (χ z.2) with hh | hh
        · rw [hh]
          rcases min_choice (ψ z.2) (φ z.2) with hh' | hh'
          · rw [hh']; exact hψabs
          · rw [hh']; exact hφabs
        · rw [hh]; exact hχabs
      have hzA : z ∈ A := by
        rw [hAdef]
        exact ⟨by rw [hz1]; exact hmabs, by rw [abs_lt]; exact ⟨hz2.1, hz2.2⟩⟩
      refine ⟨hzA, ?_⟩
      change max (max (F z) (G z)) (H z) = 0
      rw [max_three_eq_zero_iff]
      obtain ⟨hFle, hGle, hHle⟩ := hsignA z hzA
      obtain ⟨hFeq, hGeq, hHeq⟩ := hzeroA z hzA
      have h1 : z.1 ≤ ψ z.2 := by
        rw [hz1]; exact le_trans (min_le_left _ _) (min_le_left _ _)
      have h2 : z.1 ≤ φ z.2 := by
        rw [hz1]; exact le_trans (min_le_left _ _) (min_le_right _ _)
      have h3 : z.1 ≤ χ z.2 := by
        rw [hz1]; exact min_le_right _ _
      refine ⟨hFle.mpr h1, hGle.mpr h2, hHle.mpr h3, ?_⟩
      rcases min_choice (min (ψ z.2) (φ z.2)) (χ z.2) with hh | hh
      · rcases min_choice (ψ z.2) (φ z.2) with hh' | hh'
        · exact Or.inl (hFeq.mpr (by rw [hz1, hh, hh']))
        · exact Or.inr (Or.inl (hGeq.mpr (by rw [hz1, hh, hh'])))
      · exact Or.inr (Or.inr (hHeq.mpr (by rw [hz1, hh])))
    · rintro ⟨hzA, hzmax⟩
      obtain ⟨hz1, hz2⟩ : |z.1| < Rx ∧ |z.2| < Ry' := by
        rwa [hAdef] at hzA
      change max (max (F z) (G z)) (H z) = 0 at hzmax
      rw [max_three_eq_zero_iff] at hzmax
      obtain ⟨hFle, hGle, hHle, hone⟩ := hzmax
      obtain ⟨hFiff, hGiff, hHiff⟩ := hsignA z hzA
      obtain ⟨hFeq, hGeq, hHeq⟩ := hzeroA z hzA
      have hz1leψ : z.1 ≤ ψ z.2 := hFiff.mp hFle
      have hz1leφ : z.1 ≤ φ z.2 := hGiff.mp hGle
      have hz1leχ : z.1 ≤ χ z.2 := hHiff.mp hHle
      refine ⟨?_, ?_⟩
      · rw [abs_lt] at hz2
        exact hz2
      · rcases hone with h | h | h
        · have hz1' : z.1 = ψ z.2 := hFeq.mp h
          have hψφ : ψ z.2 ≤ φ z.2 := by rw [← hz1']; exact hz1leφ
          have hψχ : ψ z.2 ≤ χ z.2 := by rw [← hz1']; exact hz1leχ
          rw [hz1', min_eq_left (le_trans (min_le_left _ _) hψχ), min_eq_left hψφ]
        · have hz1' : z.1 = φ z.2 := hGeq.mp h
          have hφψ : φ z.2 ≤ ψ z.2 := by rw [← hz1']; exact hz1leψ
          have hφχ : φ z.2 ≤ χ z.2 := by rw [← hz1']; exact hz1leχ
          rw [hz1', min_eq_left (le_trans (min_le_right _ _) hφχ), min_eq_right hφψ]
        · have hz1' : z.1 = χ z.2 := hHeq.mp h
          have hχψ : χ z.2 ≤ ψ z.2 := by rw [← hz1']; exact hz1leψ
          have hχφ : χ z.2 ≤ φ z.2 := by rw [← hz1']; exact hz1leφ
          rw [hz1', min_eq_right (le_min hχψ hχφ)]
  have hloc : IsLocallyArcP (A ∩ {z : ℝ × ℝ | max (max (F z) (G z)) (H z) = 0}) :=
    isLocallyArc_of_eq hgraph (isLocallyArc_graph_snd hmcont)
  -- transfer back along the affine change of coordinates
  refine ⟨T '' A, T.isOpenMap A hAopen, ⟨0, ?_, ?_⟩, ?_⟩
  · rw [hAdef]
    exact ⟨by simpa using hRxpos, by simpa using hRy'pos⟩
  · show (T 0 : ℝ × ℝ) = p
    rw [hT_apply, map_zero, add_zero]
  · have hFz : ∀ z : ℝ × ℝ, F z = f (p + M z) := fun z => by rw [hFdef]
    have hGz : ∀ z : ℝ × ℝ, G z = g (p + M z) := fun z => by rw [hGdef]
    have hHz : ∀ z : ℝ × ℝ, H z = h (p + M z) := fun z => by rw [hHdef]
    have hT_image : T '' (A ∩ {z : ℝ × ℝ | max (max (F z) (G z)) (H z) = 0})
        = (T '' A) ∩ {q : ℝ × ℝ | max (max (f q) (g q)) (h q) = 0} := by
      ext q
      constructor
      · rintro ⟨z, ⟨hzA, hzmax⟩, hzq⟩
        have hzmax' : q ∈ {q : ℝ × ℝ | max (max (f q) (g q)) (h q) = 0} := by
          rw [← hzq, hT_apply]
          change max (max (f (p + M z)) (g (p + M z))) (h (p + M z)) = 0
          rw [← hFz z, ← hGz z, ← hHz z]
          exact hzmax
        exact ⟨⟨z, hzA, hzq⟩, hzmax'⟩
      · rintro ⟨⟨z, hzA, hzq⟩, hzmax⟩
        have hzmax' : max (max (F z) (G z)) (H z) = 0 := by
          rw [← hzq, hT_apply] at hzmax
          change max (max (f (p + M z)) (g (p + M z))) (h (p + M z)) = 0 at hzmax
          rw [← hFz z, ← hGz z, ← hHz z] at hzmax
          exact hzmax
        exact ⟨z, ⟨hzA, hzmax'⟩, hzq⟩
    rw [← hT_image]
    exact isLocallyArc_image_of_homeomorph T hloc

end

end Work.Smooth.OneManifold

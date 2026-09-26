import Mathlib
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_isometric_linear_of_ne_zero
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_pair
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential

/-!
# The plane model of a tangential corner

Let `f g : ℝ × ℝ → ℝ` be `C¹` with `f p = g p = 0`, with the *same* nonzero derivative at `p`
(`fderiv f p = fderiv g p ≠ 0`).  Then the zero set of the maximum,
`{q | max (f q) (g q) = 0}`,
is locally an arc: in coordinates in which the common derivative is the first coordinate, the two
zero sets `{f = 0}` and `{g = 0}` are graphs `x = ψ y`, `x = φ y` of continuous functions over a
common interval, and `max (f q) (g q) = 0` is equivalent to `x = min (ψ y) (φ y)` — a graph of a
continuous function, hence locally an arc.

This is the tangential companion of `Work.Smooth.OneManifold.isLocallyArc_max_of_isInvertible`.  The
graph description of the two zero sets is `Work.Smooth.BoxGeneric.LocalArc.exists_root_pair`, and
the linear change of coordinates is `exists_isometric_linear_of_ne_zero`.
-/

open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **A tangential corner of a level set of a maximum is locally an arc.** -/
theorem isLocallyArc_max_of_tangential {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfp : f p = 0) (hgp : g p = 0)
    (htang : fderiv ℝ f p = fderiv ℝ g p) (hreg : fderiv ℝ f p ≠ 0) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ p ∈ V ∧
      Work.Smooth.SphereJordan.IsLocallyArc ↥(V ∩ {q : ℝ × ℝ | max (f q) (g q) = 0}) := by
  -- an isometric change of coordinates bringing the common derivative to the first coordinate
  obtain ⟨M, hiso, hsurj, hpos⟩ :=
    Work.Smooth.BoxGeneric.LocalArc.exists_isometric_linear_of_ne_zero (fderiv ℝ f p) hreg
  set F : ℝ × ℝ → ℝ := fun z => f (p + M z) with hFdef
  set G : ℝ × ℝ → ℝ := fun z => g (p + M z) with hGdef
  have hFcd : ContDiff ℝ 1 F := by rw [hFdef]; fun_prop
  have hGcd : ContDiff ℝ 1 G := by rw [hGdef]; fun_prop
  have hF0 : F 0 = 0 := by simp [hFdef, hfp]
  have hG0 : G 0 = 0 := by simp [hGdef, hgp]
  have hFG : fderiv ℝ F 0 = fderiv ℝ G 0 := by
    rw [hFdef, hGdef,
      Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear f hf p M,
      Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear g hg p M, htang]
  have hposF : 0 < (fderiv ℝ F 0) (1, 0) := by
    rw [Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear f hf p M]
    simpa using hpos
  -- the two zero sets are graphs over the second coordinate
  obtain ⟨Rx, Ry, hRxpos, hRypos, ψ, φ, hψ0, hφ0, hψcont, hφcont, hroot, hsign, hzero⟩ :=
    Work.Smooth.BoxGeneric.LocalArc.exists_root_pair hFcd hGcd hF0 hG0 hFG hposF
  -- shrink the second coordinate so that the graphs stay in the strip `|x| < Rx`
  have hmem_ψ : Set.Ioo (-Ry) Ry ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hψca : ContinuousAt ψ 0 := hψcont.continuousAt hmem_ψ
  have hφca : ContinuousAt φ 0 := hφcont.continuousAt hmem_ψ
  have hψnb : ψ ⁻¹' Set.Ioo (-Rx) Rx ∈ 𝓝 (0 : ℝ) := by
    refine hψca.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hψ0]
    exact ⟨by linarith, by linarith⟩
  have hφnb : φ ⁻¹' Set.Ioo (-Rx) Rx ∈ 𝓝 (0 : ℝ) := by
    refine hφca.preimage_mem_nhds (isOpen_Ioo.mem_nhds ?_)
    rw [hφ0]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨δψ, hδψpos, hδψ⟩ := Metric.mem_nhds_iff.mp hψnb
  obtain ⟨δφ, hδφpos, hδφ⟩ := Metric.mem_nhds_iff.mp hφnb
  set Ry' : ℝ := min (min δψ δφ) Ry with hRy'def
  have hRy'pos : 0 < Ry' := lt_min (lt_min hδψpos hδφpos) hRypos
  have hRy'leRy : Ry' ≤ Ry := min_le_right _ _
  have hRy'leψ : Ry' ≤ δψ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRy'leφ : Ry' ≤ δφ := le_trans (min_le_left _ _) (min_le_right _ _)
  -- the graph of the minimum
  set ψ' : ℝ → ℝ := fun y => min (ψ y) (φ y) with hψ'def
  have hψ'cont : ContinuousOn ψ' (Set.Ioo (-Ry') Ry') := by
    rw [hψ'def]
    refine ContinuousOn.inf ?_ ?_
    · exact hψcont.mono (fun y hy => ⟨by linarith [hy.1, hRy'leRy], by linarith [hy.2, hRy'leRy]⟩)
    · exact hφcont.mono (fun y hy => ⟨by linarith [hy.1, hRy'leRy], by linarith [hy.2, hRy'leRy]⟩)
  -- the open box of parameters
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
  -- the sign and zero conditions on the box
  have hsignA : ∀ z ∈ A, (F z ≤ 0 ↔ z.1 ≤ ψ z.2) ∧ (G z ≤ 0 ↔ z.1 ≤ φ z.2) := by
    intro z hz
    rw [hAdef] at hz
    exact hsign z.1 z.2 (le_of_lt hz.1) (le_of_lt (lt_of_lt_of_le hz.2 hRy'leRy))
  have hzeroA : ∀ z ∈ A, (F z = 0 ↔ z.1 = ψ z.2) ∧ (G z = 0 ↔ z.1 = φ z.2) := by
    intro z hz
    rw [hAdef] at hz
    exact hzero z.1 z.2 (le_of_lt hz.1) (le_of_lt (lt_of_lt_of_le hz.2 hRy'leRy))
  -- the graph description of the model
  have hgraph : {z : ℝ × ℝ | z.2 ∈ Set.Ioo (-Ry') Ry' ∧ z.1 = ψ' z.2}
      = A ∩ {z : ℝ × ℝ | max (F z) (G z) = 0} := by
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
      have hminabs : |ψ' z.2| < Rx := by
        rw [hψ'def]
        change |min (ψ z.2) (φ z.2)| < Rx
        rcases min_choice (ψ z.2) (φ z.2) with h | h <;> rw [h]
        · exact hψabs
        · exact hφabs
      have hzA : z ∈ A := by
        rw [hAdef]
        exact ⟨by rw [hz1]; exact hminabs, by rw [abs_lt]; exact ⟨hz2.1, hz2.2⟩⟩
      refine ⟨hzA, ?_⟩
      change max (F z) (G z) = 0
      rw [Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff]
      refine ⟨?_, ?_, ?_⟩
      · rw [(hsignA z hzA).1, hz1]
        change min (ψ z.2) (φ z.2) ≤ ψ z.2
        exact min_le_left _ _
      · rw [(hsignA z hzA).2, hz1]
        change min (ψ z.2) (φ z.2) ≤ φ z.2
        exact min_le_right _ _
      · rcases min_choice (ψ z.2) (φ z.2) with h | h
        · refine Or.inl ?_
          rw [(hzeroA z hzA).1, hz1]
          change min (ψ z.2) (φ z.2) = ψ z.2
          exact h
        · refine Or.inr ?_
          rw [(hzeroA z hzA).2, hz1]
          change min (ψ z.2) (φ z.2) = φ z.2
          exact h
    · rintro ⟨hzA, hzmax⟩
      obtain ⟨hz1, hz2⟩ : |z.1| < Rx ∧ |z.2| < Ry' := by
        rw [hAdef] at hzA
        exact hzA
      change max (F z) (G z) = 0 at hzmax
      rw [Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff] at hzmax
      obtain ⟨hfz, hgz, hzero'⟩ := hzmax
      have hz1leψ : z.1 ≤ ψ z.2 := (hsignA z hzA).1.mp hfz
      have hz1leφ : z.1 ≤ φ z.2 := (hsignA z hzA).2.mp hgz
      have hz1eq : z.1 = ψ z.2 ∨ z.1 = φ z.2 := by
        rcases hzero' with h | h
        · exact Or.inl ((hzeroA z hzA).1.mp h)
        · exact Or.inr ((hzeroA z hzA).2.mp h)
      have hz2mem : z.2 ∈ Set.Ioo (-Ry') Ry' := by
        rw [abs_lt] at hz2
        exact hz2
      refine ⟨hz2mem, ?_⟩
      rcases hz1eq with h | h
      · rw [hψ'def]
        change z.1 = min (ψ z.2) (φ z.2)
        rw [min_eq_left (by rw [← h]; exact hz1leφ)]
        exact h
      · rw [hψ'def]
        change z.1 = min (ψ z.2) (φ z.2)
        rw [min_eq_right (by rw [← h]; exact hz1leψ)]
        exact h
  have hloc : Work.Smooth.SphereJordan.IsLocallyArc
      ↥(A ∩ {z : ℝ × ℝ | max (F z) (G z) = 0}) :=
    isLocallyArc_of_eq hgraph (isLocallyArc_graph_snd hψ'cont)
  -- transport back along `z ↦ p + M z`
  let Minv : ℝ × ℝ → ℝ × ℝ := Function.surjInv hsurj
  have hMinv : ∀ a : ℝ × ℝ, M (Minv a) = a := fun a => Function.surjInv_eq hsurj a
  have hMinj : Function.Injective M := by
    intro a b hab
    have h : M (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : ‖a - b‖ = 0 := by rw [← hiso (a - b), h, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have hMinv_left : ∀ z : ℝ × ℝ, Minv (M z) = z := fun z => hMinj (hMinv (M z))
  have hMinv_cont : Continuous Minv := by
    rw [Metric.continuous_iff]
    intro a ε hε
    refine ⟨ε, hε, fun b hb => ?_⟩
    have hd : dist (M (Minv b)) (M (Minv a)) = dist b a := by rw [hMinv b, hMinv a]
    have hdist : dist (Minv b) (Minv a) = dist (M (Minv b)) (M (Minv a)) := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, hiso]
    rw [hdist, hd]
    exact hb
  let T : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  { toFun := fun z => p + M z
    invFun := fun q => Minv (q - p)
    left_inv := fun z => by
      show Minv ((p + M z) - p) = z
      rw [add_sub_cancel_left, hMinv_left]
    right_inv := fun q => by
      show p + M (Minv (q - p)) = q
      rw [hMinv, add_sub_cancel]
    continuous_toFun := by fun_prop
    continuous_invFun := hMinv_cont.comp (by fun_prop) }
  have hT_apply : ∀ z : ℝ × ℝ, (T z : ℝ × ℝ) = p + M z := fun z => rfl
  have hT_image : T '' (A ∩ {z : ℝ × ℝ | max (F z) (G z) = 0})
      = (T '' A) ∩ {q : ℝ × ℝ | max (f q) (g q) = 0} := by
    have hFz : ∀ z : ℝ × ℝ, F z = f (p + M z) := fun z => by rw [hFdef]
    have hGz : ∀ z : ℝ × ℝ, G z = g (p + M z) := fun z => by rw [hGdef]
    ext q
    constructor
    · rintro ⟨z, ⟨hzA, hzmax⟩, hzq⟩
      have hzmax' : q ∈ {q : ℝ × ℝ | max (f q) (g q) = 0} := by
        rw [← hzq, hT_apply]
        change max (f (p + M z)) (g (p + M z)) = 0
        rw [← hFz z, ← hGz z]
        exact hzmax
      exact ⟨⟨z, hzA, hzq⟩, hzmax'⟩
    · rintro ⟨⟨z, hzA, hzq⟩, hzmax⟩
      have hzmax' : max (F z) (G z) = 0 := by
        rw [← hzq, hT_apply] at hzmax
        change max (f (p + M z)) (g (p + M z)) = 0 at hzmax
        rw [← hFz z, ← hGz z] at hzmax
        exact hzmax
      exact ⟨z, ⟨hzA, hzmax'⟩, hzq⟩
  refine ⟨T '' A, T.isOpenMap A hAopen, ⟨0, ?_, ?_⟩, ?_⟩
  · rw [hAdef]
    exact ⟨by simpa using hRxpos, by simpa using hRy'pos⟩
  · show (T 0 : ℝ × ℝ) = p
    rw [hT_apply, map_zero, add_zero]
  · rw [← hT_image]
    exact isLocallyArc_image_of_homeomorph T hloc

end

end Work.Smooth.OneManifold

import Mathlib
import Submission.Work.Drive.FamBox.Defs
import Submission.Work.Drive.finite_of_isCompact_of_isolated

/-!
# Finiteness of the boundary meet set `boxBMeet F G`

Two smooth maps `F G : ℝ⁵ → M` into a smooth `4`-manifold `M`, meeting transversally on the box
`[0,1]⁵`.  This file proves that the part of the meet set lying on the boundary of the box is
**finite**:

* `boxBMeet_isolated_of_face` — a boundary meet `b` lying on the face `i` (all other coordinates
  strictly inside `(0,1)`) with a common tangent direction `σ` of `Lf F G b` non-zero in the
  coordinate `i` is *isolated* in `boxBMeet F G`; near `b` the meet set is the graph
  `u ↦ u • eᵢ + η u` over the `i`-th coordinate, and a boundary meet near `b` must lie on the face
  `i` and have its `i`-th coordinate within `1` of `b i ∈ {0,1}`, hence equal to it;
* `finite_boxBMeet` — the target, by compactness of `boxBMeet F G ⊆ [0,1]⁵` and
  `Work.Drive.finite_of_isCompact_of_isolated`.

This is the same-box analogue of `Work.Drive.ManifoldParity.finite_bInterSet`, with the two block
projections of the `(2,3)`-split replaced by the identity.
-/

namespace Work.Drive.FamBox

open scoped Manifold ContDiff Topology
open Set Manifold

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## Isolation of a boundary meet point on a face -/

/-- **A boundary meet point on a face is isolated.**  Let `F G : ℝ⁵ → M` be smooth, `b` a meet
inside the box lying on the face with (ambient) coordinate `p` — all the other coordinates of `b`
strictly inside `(0,1)` — and suppose the derivative of the charted difference map at `b` is
surjective on the coordinate hyperplane `{v | v p = 0}`.  Then `b` is isolated in `boxBMeet F G`. -/
theorem boxBMeet_isolated_of_face (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {b : Amb 4} (hbeq : F b = G b)
    (p : Fin 5) (hpe : b p = 0 ∨ b p = 1)
    (hpo : ∀ q : Fin 5, q ≠ p → b q ∈ Set.Ioo (0 : ℝ) 1)
    (hsurj_p : Function.Surjective (fun v : {v : Amb 4 // v p = 0} =>
      fderiv ℝ (chartDif (F b) F G) b v.1)) :
    ∃ U : Set (Amb 4), IsOpen U ∧ b ∈ U ∧ U ∩ boxBMeet F G ⊆ {b} := by
  have hbreg : b ∈ chartReg (F b) F G := mem_chartReg_self F G hbeq
  obtain ⟨δ₀, ρ, η, hδ₀, hρ, hηsmooth, hηi, hηb, hchar⟩ :=
    exists_local_graph_box (F b) F G hF hG hbreg hbeq p hsurj_p
  have hηc : Continuous η := hηsmooth.continuous
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  -- the three open conditions defining the neighbourhood
  have hU1 : IsOpen {y : Amb 4 | |y p - b p| < δ} := by
    have hcont : Continuous fun y : Amb 4 => |y p - b p| :=
      (((PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) p)).sub continuous_const).abs
    exact isOpen_Iio.preimage hcont
  have hU2 : IsOpen {y : Amb 4 |
      ‖y - (y p) • EuclideanSpace.single p (1 : ℝ) - η (y p)‖ < ρ} := by
    have hcont : Continuous fun y : Amb 4 =>
        y - (y p) • EuclideanSpace.single p (1 : ℝ) - η (y p) := by
      fun_prop
    exact isOpen_Iio.preimage hcont.norm
  have hU3 : IsOpen {y : Amb 4 | ∀ q : Fin 5, q ≠ p → y q ∈ Set.Ioo (0 : ℝ) 1} := by
    have hset : {y : Amb 4 | ∀ q : Fin 5, q ≠ p → y q ∈ Set.Ioo (0 : ℝ) 1} =
        ⋂ (q : {q : Fin 5 // q ≠ p}),
          {y : Amb 4 | y (q : Fin 5) ∈ Set.Ioo (0 : ℝ) 1} := by
      ext y
      simp [Set.mem_iInter, Subtype.forall]
    rw [hset]
    exact isOpen_iInter_of_finite fun q =>
      isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) (q : Fin 5))
  refine ⟨{y : Amb 4 | |y p - b p| < δ} ∩
      {y : Amb 4 |
        ‖y - (y p) • EuclideanSpace.single p (1 : ℝ) - η (y p)‖ < ρ} ∩
      {y : Amb 4 | ∀ q : Fin 5, q ≠ p → y q ∈ Set.Ioo (0 : ℝ) 1},
    (hU1.inter hU2).inter hU3, ⟨⟨?_, ?_⟩, hpo⟩, ?_⟩
  · show |b p - b p| < δ
    rw [sub_self, abs_zero]; exact hδ
  · show ‖b - (b p) • EuclideanSpace.single p (1 : ℝ) - η (b p)‖ < ρ
    rw [hηb, sub_self, norm_zero]; exact hρ
  · rintro y ⟨⟨⟨hy1, hy2⟩, hy3⟩, hyS⟩
    obtain ⟨hybox, hyeq, hybdry⟩ := mem_boxBMeet.mp hyS
    have hy1₀ : |y p - b p| < δ₀ := lt_of_lt_of_le hy1 hδδ₀
    obtain ⟨-, r, hr⟩ := hybdry
    have hrp : r = p := by
      by_contra hne
      have hyr : y r ∈ Set.Ioo (0 : ℝ) 1 := hy3 r hne
      rcases hr with h | h
      · rw [h] at hyr
        exact lt_irrefl 0 hyr.1
      · rw [h] at hyr
        exact lt_irrefl 1 hyr.2
    have hyp : y p = 0 ∨ y p = 1 := by
      rcases hr with h | h
      · left; rwa [hrp] at h
      · right; rwa [hrp] at h
    have hsub1 : |y p - b p| < 1 := lt_of_lt_of_le hy1 hδ1
    have hypb : y p = b p := by
      rcases hyp with h | h <;> rcases hpe with h' | h'
      · rw [h, h']
      · rw [h, h'] at hsub1; norm_num at hsub1
      · rw [h, h'] at hsub1; norm_num at hsub1
      · rw [h, h']
    have hgraph := (hchar y hy1₀ hy2).2
    have hyeq' : y = (y p) • EuclideanSpace.single p (1 : ℝ) + η (y p) := hgraph.mp hyeq
    have hbgraph : b = (b p) • EuclideanSpace.single p (1 : ℝ) + η (b p) := by
      rw [hηb]; abel
    have hyb : y = b := by
      calc y = (y p) • EuclideanSpace.single p (1 : ℝ) + η (y p) := hyeq'
        _ = (b p) • EuclideanSpace.single p (1 : ℝ) + η (b p) := by rw [hypb]
        _ = b := hbgraph.symm
    simpa using hyb

end

/-! ## The target -/

/-- **Finiteness of the boundary meet set.**  For smooth maps `F G : ℝ⁵ → M` into a smooth
`4`-manifold, meeting transversally on the box (`htrans`) and satisfying the face hypothesis
`hface` (every boundary meet lies on exactly one face of the box, the other coordinates strictly
inside, with a kernel vector of `Lf F G b` non-zero in that coordinate), the set `boxBMeet F G` of
meets on the boundary of the box is finite.

The local graph structure (`exists_local_graph_box` at the face coordinate, obtained from
`chartDif_face_of_kernel` and `chartDif_surjective_of_Lf`) shows that each point of `boxBMeet F G` is
isolated in it (`boxBMeet_isolated_of_face`); compactness of `boxBMeet F G`
(`isCompact_boxMeet`, a closed subset of the compact box `[0,1]⁵`) then gives finiteness via
`Work.Drive.finite_of_isCompact_of_isolated`. -/
theorem finite_boxBMeet {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F G : EuclideanSpace ℝ (Fin 5) → M)
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hG : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (htrans : ∀ x : EuclideanSpace ℝ (Fin 5), x ∈ Submission.Drive.unitBox 4 → F x = G x →
      Function.Surjective (Work.Drive.FamBox.Lf F G x))
    (hface : ∀ b : EuclideanSpace ℝ (Fin 5), b ∈ Submission.Drive.unitBox 4 → F b = G b →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : EuclideanSpace ℝ (Fin 5), Work.Drive.FamBox.Lf F G b σ = 0 ∧ σ i ≠ 0) :
    (Work.Drive.FamBox.boxBMeet F G).Finite := by
  classical
  have hFc : Continuous F := hF.continuous
  have hGc : Continuous G := hG.continuous
  have hisol : ∀ b ∈ Work.Drive.FamBox.boxBMeet F G, ∃ U : Set (EuclideanSpace ℝ (Fin 5)),
      IsOpen U ∧ b ∈ U ∧ U ∩ Work.Drive.FamBox.boxBMeet F G ⊆ {b} := by
    intro b hb
    obtain ⟨hbb, hbeq, hbbd⟩ := Work.Drive.FamBox.mem_boxBMeet.mp hb
    have hbreg : b ∈ Work.Drive.FamBox.chartReg (F b) F G :=
      Work.Drive.FamBox.mem_chartReg_self F G hbeq
    have hsurj : Function.Surjective
        (fderiv ℝ (Work.Drive.FamBox.chartDif (F b) F G) b) :=
      Work.Drive.FamBox.chartDif_surjective_of_Lf (F b) F G hF hG hbreg hbeq
        (htrans b hbb hbeq)
    obtain ⟨i, hi0, hiin, σ, hσ, hσi⟩ := hface b hbb hbeq hbbd
    refine Work.Drive.FamBox.boxBMeet_isolated_of_face F G hF hG hbeq i hi0 hiin ?_
    exact Work.Drive.FamBox.chartDif_face_of_kernel (F b) F G hF hG hbreg hbeq hsurj hσ hσi
  have hclosed : IsClosed (Work.Drive.FamBox.boxBMeet F G) :=
    Work.Drive.FamBox.isClosed_boxBMeet F G hFc hGc
  have hK : IsCompact (Work.Drive.FamBox.boxBMeet F G) :=
    (Work.Drive.isCompact_unitBox 4).of_isClosed_subset hclosed (fun _ hx => hx.1)
  exact Work.Drive.finite_of_isCompact_of_isolated hK hisol

end Work.Drive.FamBox

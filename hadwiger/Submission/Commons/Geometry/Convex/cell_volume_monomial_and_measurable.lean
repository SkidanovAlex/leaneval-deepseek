import Mathlib
import Submission.Commons.MeasureTheory.Measure.cylinder_measurable_orthogonal
import Submission.Commons.MeasureTheory.Measure.cylinderVolume_orthogonal
import Submission.Commons.Geometry.Convex.intrinsicInterior_measurableSet

open Set MeasureTheory Metric
open scoped Pointwise ENNReal
set_option linter.unusedSectionVars false

noncomputable section

namespace Commons.Geometry.Convex.CellVol



variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- the normal cone -/
def NC (P F : Set V) : Set V :=
  {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}

lemma nc_zero_mem (P F : Set V) : (0 : V) ∈ NC P F := by
  intro x hx y hy
  simp

lemma nc_smul_of_nonneg {P F : Set V} {c : ℝ} (hc : 0 ≤ c) {z : V} (hz : z ∈ NC P F) :
    c • z ∈ NC P F := by
  intro x hx y hy
  have h := hz x hx y hy
  calc
    inner ℝ (c • z) x = c * inner ℝ z x := by simp [real_inner_smul_left]
    _ ≤ c * inner ℝ z y := mul_le_mul_of_nonneg_left h hc
    _ = inner ℝ (c • z) y := by simp [real_inner_smul_left]

lemma nc_isClosed (P F : Set V) : IsClosed (NC P F) := by
  classical
  rw [NC]
  rw [show {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}
      = ⋂ x ∈ P, ⋂ y ∈ F, {z : V | inner ℝ z x ≤ inner ℝ z y} by
      ext z
      simp [Set.mem_iInter]]
  exact isClosed_biInter (fun x hx => isClosed_biInter (fun y hy =>
    isClosed_le (Continuous.inner continuous_id continuous_const)
      (Continuous.inner continuous_id continuous_const)))

lemma nc_subset_direction_orthogonal {P F : Set V} (hFP : F ⊆ P) :
    NC P F ⊆ (affineSpan ℝ F).directionᗮ := by
  intro z hz
  change ∀ u ∈ (affineSpan ℝ F).direction, inner ℝ u z = 0
  rw [direction_affineSpan, vectorSpan_def]
  intro u hu
  let φ : V →ₗ[ℝ] ℝ := (innerₗ V) z
  have huφ : u ∈ φ.ker := by
    apply (Submodule.mem_span.mp hu) φ.ker
    rintro v hv
    rcases hv with ⟨x, hxF, y, hyF, hxy⟩
    change inner ℝ z v = 0
    rw [← hxy]
    have h1 : inner ℝ z x ≤ inner ℝ z y := hz x (hFP hxF) y hyF
    have h2 : inner ℝ z y ≤ inner ℝ z x := hz y (hFP hyF) x hxF
    have heq : inner ℝ z x = inner ℝ z y := le_antisymm h1 h2
    calc
      inner ℝ z (x -ᵥ y) = inner ℝ z (x - y) := by rw [vsub_eq_sub]
      _ = inner ℝ z x - inner ℝ z y := by rw [inner_sub_right]
      _ = 0 := by rw [heq]; ring
  have huz : inner ℝ z u = 0 := huφ
  rw [real_inner_comm]
  exact huz

/-- the intrinsic interior lies inside the affine span -/
lemma intrinsicInterior_subset_affineSpan (s : Set V) :
    intrinsicInterior ℝ s ⊆ (affineSpan ℝ s : Set V) := by
  intro x hx
  rw [mem_intrinsicInterior] at hx
  rcases hx with ⟨y, hy, hyx⟩
  rw [← hyx]
  exact y.2

/-- Orthogonal embedding of the Euclidean model of a submodule into `V`. -/
def embOf (L : Submodule ℝ V) : EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) →ₗᵢ[ℝ] V :=
  (L.subtypeₗᵢ).comp (stdOrthonormalBasis ℝ L).repr.symm.toLinearIsometry

lemma embOf_mem (L : Submodule ℝ V) (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ L))) :
    embOf L x ∈ (L : Set V) :=
  ((stdOrthonormalBasis ℝ L).repr.symm x).2

lemma range_embOf (L : Submodule ℝ V) : Set.range (embOf L) = (L : Set V) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact embOf_mem L x
  · intro hv
    let l : L := ⟨v, hv⟩
    refine ⟨(stdOrthonormalBasis ℝ L).repr l, ?_⟩
    simp [embOf, l]


-- generic cone ∩ ball scaling (EuclideanSpace instances as real normed spaces)
lemma cone_ball_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : Set E} (hN0 : (0 : E) ∈ N) (hNc : ∀ ⦃c : ℝ⦄, 0 ≤ c → c • N ⊆ N)
    (t : ℝ) (ht : 0 ≤ t) :
    N ∩ Metric.closedBall (0 : E) t = t • (N ∩ Metric.closedBall (0 : E) 1) := by
  by_cases ht0 : t = 0
  · subst t
    ext z
    constructor
    · intro hz
      have hz0 : z = 0 := by
        have hn : ‖z‖ ≤ (0 : ℝ) := by simpa [Metric.closedBall, dist_eq_norm] using hz.2
        exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg z))
      subst z
      refine ⟨0, ⟨hN0, by simp⟩, ?_⟩
      simp
    · rintro ⟨z', hz', rfl⟩
      constructor
      · simpa using hN0
      · simpa using (norm_nonneg (0 : E))
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    ext z
    constructor
    · intro hz
      let z' : E := t⁻¹ • z
      refine ⟨z', ?_, ?_⟩
      · constructor
        · apply (hNc (inv_nonneg.mpr ht))
          exact ⟨z, hz.1, rfl⟩
        · simp [z', Metric.closedBall, dist_eq_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ht, abs_of_nonneg (inv_nonneg.mpr ht)]
          -- ‖t⁻¹ • z‖ ≤ 1
          have hnz : ‖z‖ ≤ t := by simpa [Metric.closedBall, dist_eq_norm] using hz.2
          have hinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht
          calc
            t⁻¹ * ‖z‖ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hnz hinv
            _ = 1 := by field_simp [ne_of_gt htpos]
      · simp [z']
        rw [smul_smul]
        norm_num
        -- t • (t⁻¹ • z) = (t * t⁻¹) • z = z
        rw [mul_inv_cancel₀ (ne_of_gt htpos)]
        simp
    · rintro ⟨z', hz', rfl⟩
      constructor
      · apply (hNc ht)
        exact ⟨z', hz'.1, rfl⟩
      · have hn1 : ‖z'‖ ≤ 1 := by simpa [Metric.closedBall, dist_eq_norm] using hz'.2
        simp [Metric.closedBall, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        calc
          t * ‖z'‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hn1 ht
          _ = t := by ring

-- --------------------------------------------------------------------------


end Commons.Geometry.Convex.CellVol

namespace Commons.Geometry.Convex

open Commons.Geometry.Convex.CellVol
open Commons.MeasureTheory.Measure

theorem cell_volume_monomial_and_measurable
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (P F : Set V) (hFP : F ⊆ P) (hFne : F.Nonempty) (hFcl : IsClosed F)
    (hFcvx : Convex ℝ F) (hFbd : Bornology.IsBounded F)
    (t : ℝ) (ht : 0 ≤ t) :
    let NC : Set V := {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}
    let cell : ℝ → Set V := fun s : ℝ =>
      Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ F) (NC ∩ Metric.closedBall (0 : V) s)
    MeasurableSet (cell t) ∧
    MeasureTheory.volume (cell t) =
      ENNReal.ofReal (t ^ Module.finrank ℝ (Submodule.orthogonal (affineSpan ℝ F).direction)) *
        MeasureTheory.volume (cell 1) := by
  classical
  -- unfold the lets and reintroduce as sets
  dsimp only
  let NCc : Set V := {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}
  let F_i : Set V := intrinsicInterior ℝ F
  let cell : ℝ → Set V := fun s : ℝ =>
      Set.image2 (fun (x y : V) => x + y) F_i (NCc ∩ Metric.closedBall (0 : V) s)
  -- geometry data
  let D : Submodule ℝ V := (affineSpan ℝ F).direction
  let W : Submodule ℝ V := Submodule.orthogonal D
  let d : ℕ := Module.finrank ℝ D
  let e : ℕ := Module.finrank ℝ W
  rcases hFne with ⟨a, haF⟩
  let e1 : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] V := embOf D
  let e2 : EuclideanSpace ℝ (Fin e) →ₗᵢ[ℝ] V := embOf W
  -- (A) NC facts
  have hNC0 : (0 : V) ∈ NCc := nc_zero_mem P F
  have hNCsmul : ∀ ⦃c : ℝ⦄, 0 ≤ c → c • NCc ⊆ NCc := by
    intro c hc z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact nc_smul_of_nonneg hc hw
  have hNCcl : IsClosed NCc := nc_isClosed P F
  have hNCorth : NCc ⊆ (W : Set V) := by
    intro z hz
    exact nc_subset_direction_orthogonal (P := P) (F := F) hFP hz
  -- (B) facts about F_i
  have hFi_affine : F_i ⊆ (affineSpan ℝ F : Set V) := intrinsicInterior_subset_affineSpan F
  have hFi_shift : ∀ f ∈ F_i, f - a ∈ (D : Set V) := by
    intro f hf
    have hfs : f ∈ (affineSpan ℝ F : Set V) := hFi_affine hf
    have has : a ∈ (affineSpan ℝ F : Set V) := subset_affineSpan ℝ F haF
    change f - a ∈ (affineSpan ℝ F).direction
    exact AffineSubspace.vsub_mem_direction hfs has
  -- (C) image and measurability facts for A
  let A : Set (EuclideanSpace ℝ (Fin d)) := {x | a + e1 x ∈ F_i}
  have hAmeas : MeasurableSet A := by
    have hmeasF : MeasurableSet (F_i : Set V) := by
      simpa using (Commons.Geometry.Convex.intrinsicInterior_measurableSet F)
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => a + e1 x) := by
      fun_prop
    change MeasurableSet ((fun x : EuclideanSpace ℝ (Fin d) => a + e1 x) ⁻¹' F_i)
    exact hmeasF.preimage hcont.measurable
  have hFim : F_i = (fun x : EuclideanSpace ℝ (Fin d) => a + e1 x) '' A := by
    ext f
    constructor
    · intro hf
      rw [mem_image]
      have hfs : f - a ∈ (D : Set V) := hFi_shift f hf
      have hr : f - a ∈ Set.range e1 := by
        rw [show Set.range e1 = (D : Set V) by simpa [e1] using (range_embOf D)]
        exact hfs
      rcases hr with ⟨x, hx⟩
      refine ⟨x, ?_, ?_⟩
      · change a + e1 x ∈ F_i
        rw [hx]
        have h : a + (f - a) = f := by abel
        simpa [h] using hf
      · change a + e1 x = f
        rw [hx]
        abel
    · intro hv
      rw [mem_image] at hv
      rcases hv with ⟨x, hxA, hxv⟩
      rw [← hxv]
      exact hxA
  -- (D) spanning and orthogonality of the two embeddings
  have hspan : Submodule.span ℝ (Set.range e1 ∪ Set.range e2) = ⊤ := by
    rw [show Set.range e1 = (D : Set V) by simpa [e1] using (range_embOf D)]
    rw [show Set.range e2 = (W : Set V) by simpa [e2] using (range_embOf W)]
    rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq]
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have horth : ∀ x y, inner ℝ (e1 x) (e2 y) = 0 := by
    intro x y
    have hx : e1 x ∈ (D : Set V) := by simpa [e1] using embOf_mem D x
    have hy : e2 y ∈ ((W : Set V)) := by simpa [e2] using embOf_mem W y
    exact (Submodule.mem_orthogonal (K := D) (v := e2 y)).mp hy (e1 x) hx
  -- (E) Z facts
  let N : Set (EuclideanSpace ℝ (Fin e)) := {z | e2 z ∈ NCc}
  let Z : ℝ → Set (EuclideanSpace ℝ (Fin e)) := fun s => N ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin e)) s
  have hN0 : (0 : EuclideanSpace ℝ (Fin e)) ∈ N := by
    change e2 (0 : EuclideanSpace ℝ (Fin e)) ∈ NCc
    simpa using hNC0
  have hNc : ∀ ⦃c : ℝ⦄, 0 ≤ c → c • N ⊆ N := by
    intro c hc z hz
    rcases hz with ⟨w, hw, rfl⟩
    change e2 (c • w) ∈ NCc
    rw [map_smul]
    exact nc_smul_of_nonneg hc (by change e2 w ∈ NCc; exact hw)
  have hZmeas : ∀ s : ℝ, MeasurableSet (Z s) := by
    intro s
    have hclN : IsClosed (N : Set (EuclideanSpace ℝ (Fin e))) := by
      have hpre : N = e2 ⁻¹' NCc := by rfl
      rw [hpre]
      exact hNCcl.preimage e2.continuous
    have hclB : IsClosed (Metric.closedBall (0 : EuclideanSpace ℝ (Fin e)) s) := by
      exact Metric.isClosed_closedBall
    exact (hclN.inter hclB).measurableSet
  have hCim : ∀ s : ℝ, NCc ∩ Metric.closedBall (0 : V) s = e2 '' (Z s) := by
    intro s
    ext v
    constructor
    · intro hv
      rcases hv with ⟨hvNC, hvball⟩
      have hvr : v ∈ Set.range e2 := by
        rw [show Set.range e2 = (W : Set V) by simpa [e2] using (range_embOf W)]
        exact hNCorth hvNC
      rcases hvr with ⟨z, hz⟩
      refine ⟨z, ?_, ?_⟩
      · change z ∈ N ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin e)) s
        constructor
        · change e2 z ∈ NCc
          rw [hz]
          exact hvNC
        · have hv : ‖v‖ ≤ s := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hvball
          have hnorm : ‖e2 z‖ = ‖z‖ := e2.norm_map z
          have hnz : ‖z‖ ≤ s := by
            rw [← hnorm]
            simpa [hz] using hv
          simpa [Metric.mem_closedBall, dist_eq_norm] using hnz
      · exact hz
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨hzN, hzball⟩
      constructor
      · change e2 z ∈ NCc
        exact hzN
      · have hn : ‖z‖ ≤ s := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
        have hnorm : ‖e2 z‖ = ‖z‖ := e2.norm_map z
        have hn2 : ‖e2 z‖ ≤ s := by rwa [hnorm]
        simpa [Metric.mem_closedBall, dist_eq_norm] using hn2
  have hZ_smul : Z t = t • Z 1 := by
    change N ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin e)) t =
      t • (N ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin e)) 1)
    exact cone_ball_smul (E := EuclideanSpace ℝ (Fin e)) hN0 hNc t ht
  -- (F) cylinder picture: cell s = image2 ...
  have hcell_cyl : ∀ s : ℝ, cell s =
      Set.image2 (fun (x y : V) => x + y)
        ((fun x : EuclideanSpace ℝ (Fin d) => a + e1 x) '' A)
        (e2 '' (Z s)) := by
    intro s
    change Set.image2 (fun (x y : V) => x + y) F_i (NCc ∩ Metric.closedBall (0 : V) s)
      = Set.image2 (fun (x y : V) => x + y)
          ((fun x : EuclideanSpace ℝ (Fin d) => a + e1 x) '' A) (e2 '' (Z s))
    rw [hFim, hCim s]
  -- (G) measurable cell t
  have hmeas : MeasurableSet (cell t) := by
    rw [hcell_cyl t]
    exact cylinder_measurable_orthogonal (V := V) e1 e2 hspan horth a A (Z t) hAmeas (hZmeas t)
  -- (H) volumes
  have hvol_cyl : ∀ s : ℝ, volume (cell s) = volume A * volume (Z s) := by
    intro s
    rw [hcell_cyl s]
    exact cylinderVolume_orthogonal (V := V) e1 e2 hspan horth a A (Z s) hAmeas (hZmeas s)
  have hvolZ : volume (Z t) = ENNReal.ofReal (t ^ e) * volume (Z 1) := by
    rw [hZ_smul]
    have hsc :=
      MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := (volume : Measure (EuclideanSpace ℝ (Fin e))))
        ht (Z 1)
    rwa [finrank_euclideanSpace_fin] at hsc
  -- (I) assemble
  constructor
  · exact hmeas
  · have h1 : volume (cell t) = volume A * volume (Z t) := hvol_cyl t
    have h2 : volume (cell 1) = volume A * volume (Z 1) := hvol_cyl 1
    calc
      volume (cell t) = volume A * volume (Z t) := h1
      _ = volume A * (ENNReal.ofReal (t ^ e) * volume (Z 1)) := by rw [hvolZ]
      _ = ENNReal.ofReal (t ^ e) * (volume A * volume (Z 1)) := by
        ac_rfl
      _ = ENNReal.ofReal (t ^ e) * volume (cell 1) := by rw [← h2]

end Commons.Geometry.Convex

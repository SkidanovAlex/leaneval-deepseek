import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs

namespace Work.Drive.ManifoldParity

open scoped Manifold ContDiff

/-- The "square" block index is injective. -/
theorem faceData_sqIdx_injective : Function.Injective Work.Drive.sqIdx := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [Work.Drive.sqIdx_val] at h'
  exact Fin.ext h'

/-- The "cube" block index is injective. -/
theorem faceData_cbIdx_injective : Function.Injective Work.Drive.cbIdx := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [Work.Drive.cbIdx_val] at h'
  omega

/-- **The face condition in the two pictures, square block.**  Being a boundary coordinate at
`sqIdx i` and strictly inside on all *other* ambient coordinates is the same as being a boundary
coordinate at `i` and strictly inside on all other square coordinates and on all cube coordinates. -/
theorem faceData_forall_ne_sqIdx_iff (x : Work.Drive.Amb 4) (i : Fin 2) :
    (∀ j : Fin 5, j ≠ Work.Drive.sqIdx i → x j ∈ Set.Ioo (0 : ℝ) 1) ↔
      (∀ j : Fin 2, j ≠ i → Work.Drive.sqPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ j : Fin 3, Work.Drive.cbPart x j ∈ Set.Ioo (0 : ℝ) 1) := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j => ?_⟩
    · have hh := h (Work.Drive.sqIdx j) (fun he => hj (faceData_sqIdx_injective he))
      simpa using hh
    · have hh := h (Work.Drive.cbIdx j) (fun he => Work.Drive.sqIdx_ne_cbIdx i j he.symm)
      simpa using hh
  · rintro ⟨h1, h2⟩ j hj
    revert hj
    refine Fin.addCases (m := 2) (n := 3)
      (motive := fun j => j ≠ Work.Drive.sqIdx i → x j ∈ Set.Ioo (0 : ℝ) 1) ?_ ?_ j
    · intro i' hi'
      have hne : i' ≠ i := fun he => hi' (by rw [he]; rfl)
      exact h1 i' hne
    · intro j' _
      exact h2 j'

/-- **The face condition in the two pictures, cube block.**  The analogue of
`faceData_forall_ne_sqIdx_iff` for an index of the cube block. -/
theorem faceData_forall_ne_cbIdx_iff (x : Work.Drive.Amb 4) (j : Fin 3) :
    (∀ k : Fin 5, k ≠ Work.Drive.cbIdx j → x k ∈ Set.Ioo (0 : ℝ) 1) ↔
      (∀ i : Fin 2, Work.Drive.sqPart x i ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k : Fin 3, k ≠ j → Work.Drive.cbPart x k ∈ Set.Ioo (0 : ℝ) 1) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · have hh := h (Work.Drive.sqIdx i) (fun he => Work.Drive.sqIdx_ne_cbIdx i j he)
      simpa using hh
    · have hh := h (Work.Drive.cbIdx k) (fun he => hk (faceData_cbIdx_injective he))
      simpa using hh
  · rintro ⟨h1, h2⟩ k hk
    revert hk
    refine Fin.addCases (m := 2) (n := 3)
      (motive := fun k => k ≠ Work.Drive.cbIdx j → x k ∈ Set.Ioo (0 : ℝ) 1) ?_ ?_ k
    · intro i' _
      exact h1 i'
    · intro k' hk'
      have hne : k' ≠ j := fun he => hk' (by rw [he]; rfl)
      exact h2 k' hne

/-- At a point at which the two chains meet, the chart at the common image point contains both
images. -/
theorem faceData_mem_chartRegion_self {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    {x : Work.Drive.Amb 4} (heq : D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x)) :
    x ∈ Work.Drive.chartRegion (D (Work.Drive.sqPart x)) D N := by
  rw [Work.Drive.mem_chartRegion]
  have hmem : ∀ y : M, y ∈ (Work.Drive.chr y).source := fun y => by
    rw [Work.Drive.chr, ← extChartAt_source (I := 𝓡 4) y]
    exact mem_extChartAt_source _
  exact ⟨hmem _, by rw [heq]; exact hmem _⟩

open scoped Manifold ContDiff in
/-- **The face data of the intersection set.**  From the face hypothesis `hface` of
`Work.Drive.ManifoldParity.even_ncard_bInterSet_of_tangential_field` (every boundary intersection is
on exactly one face of the box, transversally) together with the transversality `htrans`, the
tangency `hVtan` of `V` and the non-vanishing `hVne` of `V` on the intersection set, one obtains the
face-free form of the hypothesis used by the flow argument: at every boundary point `b` of the
intersection set there is an *ambient* index `i : Fin 5` with `b i ∈ {0,1}`, all other coordinates of
`b` strictly inside `(0,1)`, and `V b i ≠ 0`.

Proof ingredients: split the two disjuncts of `hface` by the block decomposition
(`Work.Drive.exists_fin_five_iff`, `Work.Drive.sqPart_apply`, `Work.Drive.cbPart_apply`, `sqIdx`,
`cbIdx`); the index is `sqIdx i` (respectively `cbIdx j`); the hyperplane condition on the derivative
of the charted difference map is `Work.Drive.chartDiff_face_of_kernel` (with `mkPart σ τ`, using
`Work.Drive.mkPart_sqIdx`/`mkPart_cbIdx` and `Work.Drive.chartDiff_surjective_of_transverse` for the
surjectivity), and `V b i ≠ 0` follows from
`Work.Drive.kernel_coord_ne_zero`/`Work.Drive.vcoord_ne_zero_of_tangent`. -/
theorem face_data_interSet {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤)
    (hface : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → x ∈ Submission.Drive.unitBoxBdry 4 →
      (∃ i : Fin 2, (Work.Drive.sqPart x i = 0 ∨ Work.Drive.sqPart x i = 1) ∧
          (∀ j : Fin 2, j ≠ i → Work.Drive.sqPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, Work.Drive.cbPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (Work.Drive.cbPart x j = 0 ∨ Work.Drive.cbPart x j = 1) ∧
          (∀ k : Fin 3, k ≠ j → Work.Drive.cbPart x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, Work.Drive.sqPart x i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ τ j ≠ 0))
    (V : Work.Drive.Amb 4 → Work.Drive.Amb 4)
    (hVtan : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → ∀ p : M,
      x ∈ Work.Drive.chartRegion p D N →
      fderiv ℝ (Work.Drive.chartDiff p D N) x (V x) = 0)
    (hVne : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → V x ≠ 0) :
    ∀ b : Work.Drive.Amb 4, b ∈ Work.Drive.interSet D N →
      b ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (b i = 0 ∨ b i = 1) ∧ (∀ j : Fin 5, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
        V b i ≠ 0 := by
  intro b hb hbbdry
  obtain ⟨hbox, heq⟩ := Work.Drive.mem_interSet.mp hb
  have hbx : b ∈ Work.Drive.chartRegion (D (Work.Drive.sqPart b)) D N :=
    faceData_mem_chartRegion_self D N heq
  have hsurj : Function.Surjective
      (fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart b)) D N) b) :=
    Work.Drive.chartDiff_surjective_of_transverse (D (Work.Drive.sqPart b)) D N hD hN hbx heq
      (htrans b hbox heq)
  have htan : fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart b)) D N) b (V b) = 0 :=
    hVtan b hbox heq (D (Work.Drive.sqPart b)) hbx
  have hne : V b ≠ 0 := hVne b hbox heq
  rcases hface b hbox heq hbbdry with
    ⟨i, hiface, hsqi, hcbi, σ, τ, hστ, hσi⟩ | ⟨j, hjface, hcbj, hsqi, σ, τ, hστ, hτj⟩
  · refine ⟨Work.Drive.sqIdx i, ?_, ?_, ?_⟩
    · simpa using hiface
    · exact (faceData_forall_ne_sqIdx_iff b i).mpr ⟨hsqi, hcbi⟩
    · exact Work.Drive.vcoord_ne_zero_of_tangent hbx heq hsurj htan hne
        (Work.Drive.chartDiff_face_of_kernel (D (Work.Drive.sqPart b)) D N hD hN hbx heq hsurj hστ
          (by rw [Work.Drive.mkPart_sqIdx]; exact hσi))
  · refine ⟨Work.Drive.cbIdx j, ?_, ?_, ?_⟩
    · simpa using hjface
    · exact (faceData_forall_ne_cbIdx_iff b j).mpr ⟨hsqi, hcbj⟩
    · exact Work.Drive.vcoord_ne_zero_of_tangent hbx heq hsurj htan hne
        (Work.Drive.chartDiff_face_of_kernel (D (Work.Drive.sqPart b)) D N hD hN hbx heq hsurj hστ
          (by rw [Work.Drive.mkPart_cbIdx]; exact hτj))

end Work.Drive.ManifoldParity

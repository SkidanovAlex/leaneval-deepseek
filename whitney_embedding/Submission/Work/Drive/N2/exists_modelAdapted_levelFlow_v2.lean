import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelOrbitMono
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.gramDetNeZero
import Submission.Work.Drive.N2.ambientFieldAux
import Submission.Work.Drive.N2.ambientFieldProps
import Submission.Work.Drive.N2.ambientFieldSmooth
import Submission.Work.Drive.N2.levelFlowAssembly
import Submission.Work.Drive.N2.exists_contDiff_bump_isCompact
import Submission.Work.Drive.N2.auxField_retraction_ne_zero
import Submission.Work.Drive.N2.exists_smooth_retraction_manifold
import Submission.Work.Projection.compact_embedding

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

set_option maxHeartbeats 1600000

/-- The ambient data: a Whitney embedding of the compact surface into `ℝ ^ 5` together with a
nearest-point retraction of a neighbourhood of its image. -/
theorem exists_ambSetup_of_compact (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M] :
    Nonempty (AmbSetup M) := by
  obtain ⟨e, he, hemp, himm⟩ := Work.Projection.exists_embedding_euclidean_of_compact 2 (M := M)
  obtain ⟨U, π, hU, hUe, hπ, hπe, _hπd, hπo⟩ :=
    exists_smooth_retraction_manifold (n := 2) (N := 2 * 2 + 1) e he hemp.injective himm
  exact ⟨AmbSetup.mk e he hemp.injective himm U π hU hUe hπ hπe hπo⟩

/-- **The bumps of the construction.**  `χd` is `1` on the embedded surface and supported in the
tubular neighbourhood; `χi i` is `1` near the image of `closure (C i)` and supported in the model
region of the chart `i`; `χf` is `1` near the image of the set of points on which the sum of the
chart bumps differs from `1` (there the far field has to carry the unit speed of `f`) and is
supported where the auxiliary field does not vanish. -/
theorem exists_modelAdapted_bumpData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    (A : AmbSetup M) (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {ι : Type*} [Fintype ι]
    (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (hφ : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ i y) (φ i).source)
    (hφ' : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => (φ i).symm u) (φ i).target)
    (hdisj : ∀ i j, i ≠ j → Disjoint (φ i).source (φ j).source)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, IsCompact (closure (C i)) ∧ closure (C i) ⊆ (φ i).source)
    (hCcrit : ∀ y, (∀ i, y ∉ C i) → ¬ Work.Drive.Morse.IsCritical f y) :
    ∃ (χd : EuclideanSpace ℝ (Fin 5) → ℝ) (χi : ι → EuclideanSpace ℝ (Fin 5) → ℝ)
      (χf : EuclideanSpace ℝ (Fin 5) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χd ∧ HasCompactSupport χd ∧
      tsupport χd ⊆ A.U ∧ Set.range A.e ⊆ interior {z | χd z = 1} ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χi i) ∧ HasCompactSupport (χi i) ∧
        tsupport (χi i) ⊆ modelRegion A (φ i) ∩ interior {z | χd z = 1} ∧
        A.e '' closure (C i) ⊆ interior {z | χi i z = 1}) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χf ∧ HasCompactSupport χf ∧
      tsupport χf ⊆ {z | auxField (fun z => χd z • A.e (A.π z))
          (fun z => χd z • f (A.π z)) z ≠ 0} ∩ interior {z | χd z = 1} ∧
      A.e '' {y : M | (∑ i, χi i (A.e y)) ≠ 1} ⊆ interior {z | χf z = 1} := by
  classical
  -- the damping bump
  obtain ⟨χd, hχd_sm, hχd_cs, hχd_supp, hχd_int⟩ :=
    exists_contDiff_bump_isCompact (isCompact_range A.he.continuous) A.hU A.hUe
  set Ed : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5) :=
    fun z => χd z • A.e (A.π z) with hEddef
  set Gd : EuclideanSpace ℝ (Fin 5) → ℝ := fun z => χd z • f (A.π z) with hGddef
  have hEd_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ed :=
    (contDiff_damped_E_G A χd hχd_sm hχd_supp f hf).1
  have hGd_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Gd :=
    (contDiff_damped_E_G A χd hχd_sm hχd_supp f hf).2
  -- the chart bumps
  have hbump_i : ∀ i, ∃ χ : EuclideanSpace ℝ (Fin 5) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ modelRegion A (φ i) ∩ interior {z | χd z = 1} ∧
      A.e '' closure (C i) ⊆ interior {z | χ z = 1} := by
    intro i
    have hKi : IsCompact (A.e '' closure (C i)) := (hCcl i).1.image A.he.continuous
    have hOi : IsOpen (modelRegion A (φ i) ∩ interior {z | χd z = 1}) :=
      (isOpen_modelRegion A (φ i) (hφ i)).inter isOpen_interior
    have hKiOi : A.e '' closure (C i) ⊆ modelRegion A (φ i) ∩ interior {z | χd z = 1} := by
      rintro z ⟨y, hy, rfl⟩
      refine ⟨⟨⟨A.hUe ⟨y, rfl⟩, ?_⟩, ?_⟩, hχd_int ⟨y, rfl⟩⟩
      · show A.π (A.e y) ∈ (φ i).source
        rw [A.hπe]
        exact (hCcl i).2 hy
      · exact gramDet_ne_zero_of_mem_source A (φ i) (hφ i) (hφ' i) ((hCcl i).2 hy)
    exact exists_contDiff_bump_isCompact hKi hOi hKiOi
  choose χi hχi_sm hχi_cs hχi_supp hχi_one using hbump_i
  -- the far bump
  set S : Set M := {y : M | (∑ i, χi i (A.e y)) ≠ 1} with hSdef
  have hKf : IsCompact (A.e '' closure S) := isClosed_closure.isCompact.image A.he.continuous
  have hOf : IsOpen ({z : EuclideanSpace ℝ (Fin 5) | auxField Ed Gd z ≠ 0}
      ∩ interior {z | χd z = 1}) := by
    have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin 5) | auxField Ed Gd z = 0} :=
      isClosed_eq (contDiff_auxField Ed Gd hEd_sm hGd_sm).continuous continuous_const
    exact (isOpen_compl_iff.mpr hclosed).inter isOpen_interior
  have hKfOf : A.e '' closure S ⊆ {z : EuclideanSpace ℝ (Fin 5) | auxField Ed Gd z ≠ 0}
      ∩ interior {z | χd z = 1} := by
    rintro z ⟨y, hy, rfl⟩
    refine ⟨?_, hχd_int ⟨y, rfl⟩⟩
    have hnc : ¬ Work.Drive.Morse.IsCritical f y := by
      refine hCcrit y fun i hyi => ?_
      -- a neighbourhood of `y` lies in the complement of `S`
      have hmem : Sᶜ ∈ 𝓝 y := by
        have hset : Sᶜ = {w : M | (∑ j, χi j (A.e w)) = 1} := by
          rw [hSdef]
          ext w
          simp
        rw [hset]
        have hopen1 : {w : M | w ∈ (φ i).source} ∈ 𝓝 y :=
          (φ i).open_source.mem_nhds (hCsub i hyi)
        have hmem1 : A.e y ∈ interior {z | χi i z = 1} :=
          hχi_one i ⟨y, subset_closure hyi, rfl⟩
        have hopen2 : {w : M | A.e w ∈ interior {z | χi i z = 1}} ∈ 𝓝 y :=
          A.he.continuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hmem1)
        filter_upwards [hopen1, hopen2] with w hw1 hw2
        have h1 : χi i (A.e w) = 1 := interior_subset (s := {z | χi i z = 1}) hw2
        have h2 : ∀ j, j ≠ i → χi j (A.e w) = 0 := by
          intro j hj
          by_contra hne'
          have hmemj : A.e w ∈ tsupport (χi j) :=
            subset_tsupport _ (Function.mem_support.mpr hne')
          have hreg : A.e w ∈ modelRegion A (φ j) :=
            (Set.subset_inter_iff.mp (hχi_supp j)).1 hmemj
          have hsrc : A.π (A.e w) ∈ (φ j).source := by
            simp only [modelRegion, Set.mem_inter_iff, Set.mem_setOf_eq] at hreg
            exact hreg.1.2
          rw [A.hπe] at hsrc
          exact Set.disjoint_left.mp (hdisj j i hj) hsrc hw1
        rw [Finset.sum_eq_single i (fun j _ hj => h2 j hj)
          (fun h => absurd (Finset.mem_univ i) h), h1]
      obtain ⟨w, hw1, hw2⟩ := (mem_closure_iff_nhds.mp hy) Sᶜ hmem
      exact (Set.mem_compl_iff S w).mp hw1 hw2
    simpa [hEddef, hGddef] using auxField_damped_ne_zero A χd hχd_int f hf hnc
  obtain ⟨χf, hχf_sm, hχf_cs, hχf_supp, hχf_one⟩ := exists_contDiff_bump_isCompact hKf hOf hKfOf
  refine ⟨χd, χi, χf, hχd_sm, hχd_cs, hχd_supp, hχd_int,
    fun i => ⟨hχi_sm i, hχi_cs i, hχi_supp i, hχi_one i⟩, hχf_sm, hχf_cs, hχf_supp, ?_⟩
  refine (Set.image_mono (subset_closure)).trans hχf_one


theorem exists_modelAdapted_levelFlow_v2 {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f)
    {ι : Type*} [Fintype ι]
    (x : ι → M) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hsrc : ∀ i, x i ∈ (φ i).source) (hcen : ∀ i, φ i (x i) = 0)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (hval : ∀ i y, y ∈ (φ i).source →
      f y = f (x i) + Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) y)
    (hφ : ∀ i, ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun y => φ i y) (φ i).source)
    (hφ' : ∀ i, ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat)
      (fun y => (φ i).symm y) (φ i).target)
    (hdisj : ∀ i j, i ≠ j → Disjoint (φ i).source (φ j).source)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, IsCompact (closure (C i)) ∧ closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, Work.Drive.N2.modelBall (φ i) (r i) ⊆ C i)
    (hCcrit : ∀ y, (∀ i, y ∉ C i) → ¬ Work.Drive.Morse.IsCritical f y) :
    ∃ Φ : ℝ × M → M,
      ContMDiff ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) Φ ∧
      (∀ y, Φ (0, y) = y) ∧
      (∀ a b y, Φ (a, Φ (b, y)) = Φ (a + b, y)) ∧
      (∀ (y : M) (t : ℝ), (∀ i, y ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
        f (Φ (t, y)) = f y + t) ∧
      (∀ (i : ι) (y : M) (t₁ t₂ : ℝ),
        (∀ u ∈ Set.Icc (min t₁ t₂) (max t₁ t₂), Φ (u, y) ∈ C i ∧ 0 < ‖φ i (Φ (u, y))‖) →
        |Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) (Φ (t₁, y))| <
          |Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) (Φ (t₂, y))| →
        ‖φ i (Φ (t₁, y))‖ < ‖φ i (Φ (t₂, y))‖) := by
  classical
  by_cases hne : Nonempty M
  · haveI := hne
    obtain ⟨A⟩ := exists_ambSetup_of_compact M
    obtain ⟨χd, χi, χf, hχd_sm, hχd_cs, hχd_supp, hχd_int, hχi, hχf_sm, hχf_cs, hχf_supp,
      hχf_one⟩ :=
      exists_modelAdapted_bumpData A f hf φ hφ hφ' hdisj C hCsub hCcl hCcrit
    obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4, hΦ5⟩ :=
      exists_modelAdapted_levelFlow_of_bumps A f hf x φ s₁ s₂ r hr hsrc hcen hsgn hval hφ hφ'
        hdisj C hCsub hCcl hCball hCcrit χd hχd_sm hχd_supp hχd_int χi
        (fun i => (hχi i).1) (fun i => (hχi i).2.1) (fun i => (hχi i).2.2.1)
        (fun i => (hχi i).2.2.2) χf hχf_sm hχf_cs hχf_supp hχf_one
    exact ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4, hΦ5⟩
  · haveI : IsEmpty M := not_nonempty_iff.mp hne
    refine ⟨fun p : ℝ × M => p.2, contMDiff_snd, ?_, ?_, ?_, ?_⟩
    · intro y; exact isEmptyElim y
    · intro a b y; exact isEmptyElim y
    · intro y; exact isEmptyElim y
    · intro i y; exact isEmptyElim y

end Work.Drive.N2

import Mathlib
import Submission.Work.WilE7.CoreStep.hdich_of_persist
import Submission.Work.CoreStep.persist_of_Zavoid_same_hrank
import Submission.Work.CoreStep.persist_of_Zavoid_cross2

namespace Work.CoreStep

theorem hdich_of_pieces {n m r : ℕ} (k : Fin r → ℕ)
    (T : Fin r → WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : ∀ t : Fin r, (T t).Good)
    (hrank : ∀ (t : Fin r) (z : Fin (0 + (n + (m + 1))) → ℝ), z ∈ (T t).X.set →
      Work.WilE7.MainDesign.projRank (T t) z = n + (m + 1) - (T t).j)
    (hfin : ∀ (t : Fin r) (x : Fin n → ℝ),
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet (T t)) x).Finite)
    (C : Set (Fin n → ℝ)) (hpre : IsPreconnected C)
    (s : ∀ t : Fin r, Fin (k t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hinj : ∀ (t : Fin r) (x : Fin n → ℝ), x ∈ C →
      Function.Injective fun j : Fin (k t) => s t j x)
    (hsub : ∀ (t : Fin r) (j : Fin (k t)) (x : Fin n → ℝ), x ∈ C →
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s t j x)) ∈ (T t).X.set)
    (hcov : ∀ (t : Fin r) (z : Fin (n + (m + 1)) → ℝ),
      z ∈ Work.WilE7.MainDesign.absSet (T t) →
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
      ∃ j : Fin (k t), s t j (WilkiesDesign.E.projFirst n (m + 1) z) =
        WilkiesDesign.E.projSnd n (m + 1) z)
    (Wl : Fin r → Fin r → List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hWlgood : ∀ (i j : Fin r) (W : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
      W ∈ Wl i j → W.Good)
    (hWlsub : ∀ (i j : Fin r) (W : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
      W ∈ Wl i j → W.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet (T i) (T j)).set)
    (hWlcov : ∀ i j : Fin r,
      (Work.WilE7.CoreStep.absLevelPairSet (T i) (T j)).set = ⋃ W ∈ Wl i j, W.X.set)
    (havoid : ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s i a x₀) (Fin.last m) = (s j b x₀) (Fin.last m) →
      (∀ W ∈ Wl i j, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - (T i).j →
        Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s i a x₀)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j b x₀)))
            ∉ W.X.set) ∧
      (∀ W ∈ Wl i j, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - (T i).j →
        Work.WilE7.CoreStep.pairPtUp
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s i a x₀)))
          (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j b x₀)))
            ∉ closure W.X.set \ W.X.set)) :
    ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)),
      (∃ x ∈ C, (s i a x) (Fin.last m) = (s j b x) (Fin.last m)) →
      ∀ x ∈ C, (s i a x) (Fin.last m) = (s j b x) (Fin.last m) := by
  -- Step 1: pairwise persistence of the level identity, assembled from the piece data.
  have hpers : ∀ (i j : Fin r) (a : Fin (k i)) (b : Fin (k j)) (x₀ : Fin n → ℝ), x₀ ∈ C →
      (s i a x₀) (Fin.last m) = (s j b x₀) (Fin.last m) →
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U,
        (s i a x) (Fin.last m) = (s j b x) (Fin.last m) := by
    intro i j a b x₀ hx₀ hlev
    exact persist_of_Zavoid_cross2 (T i) (T j) (hT i) (hT j)
      (hrank i) (hrank j) (hfin i) (hfin j) C (s i) (s j)
      (hcont i) (hcont j) (hinj i) (hinj j) (hsub i) (hsub j) (hcov i) (hcov j)
      (Wl i j) (hWlgood i j) (hWlsub i j) (hWlcov i j)
      (fun a' b' x' hx' hlev' => havoid i j a' b' x' hx' hlev') a b x₀ hx₀ hlev
  -- Step 2: the clopen argument on the preconnected base `C`.
  intro i j a b hex x hx
  classical
  let φ : C → ℝ := fun y => (s i a (y : Fin n → ℝ)) (Fin.last m)
  let ψ : C → ℝ := fun y => (s j b (y : Fin n → ℝ)) (Fin.last m)
  let A : Set C := {y | φ y = ψ y}
  have hφcont : Continuous φ :=
    (continuous_apply (Fin.last m)).comp
      ((hcont i a).comp_continuous continuous_subtype_val (fun y => y.2))
  have hψcont : Continuous ψ :=
    (continuous_apply (Fin.last m)).comp
      ((hcont j b).comp_continuous continuous_subtype_val (fun y => y.2))
  -- closed: preimage of the diagonal under a continuous map
  have hAclosed : IsClosed A := isClosed_eq hφcont hψcont
  -- nonempty: the given point of `C` where the two sheets agree
  have hAne : A.Nonempty := by
    obtain ⟨x₀, hx₀C, hx₀eq⟩ := hex
    exact ⟨⟨x₀, hx₀C⟩, by simpa [A, φ, ψ] using hx₀eq⟩
  -- open: persistence of the identity gives a neighbourhood of every point of `A`
  have hloc : ∀ y : C, y ∈ A → ∃ V : Set (Fin n → ℝ), IsOpen V ∧ (y : Fin n → ℝ) ∈ V ∧
      ∀ z : C, (z : Fin n → ℝ) ∈ V → z ∈ A := by
    intro y hy
    obtain ⟨U, hU, hUU⟩ :=
      hpers i j a b (y : Fin n → ℝ) y.2 (by simpa [A, φ, ψ] using hy)
    obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
    refine ⟨V, hVopen, hyV, ?_⟩
    intro z hz
    have hz' : (s i a (z : Fin n → ℝ)) (Fin.last m)
        = (s j b (z : Fin n → ℝ)) (Fin.last m) :=
      hUU (z : Fin n → ℝ) ⟨z.2, hVU hz⟩
    simpa [A, φ, ψ] using hz'
  choose V hVopen hyV hVgood using hloc
  let W : Set (Fin n → ℝ) := ⋃ y, ⋃ (hy : y ∈ A), V y hy
  have hWopen : IsOpen W := isOpen_iUnion fun y => isOpen_iUnion fun hy => hVopen y hy
  have hAeq : A = Subtype.val ⁻¹' W := by
    ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hyV z hz⟩⟩
    · intro hz
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hyA, hzy⟩ := Set.mem_iUnion.mp hy
      exact hVgood y hyA z hzy
  have hAopen : IsOpen A := hAeq ▸ hWopen.preimage continuous_subtype_val
  -- `C` is preconnected, so its only clopen subsets are `∅` and `univ`
  have hunivpre : IsPreconnected (Set.univ : Set C) :=
    (Subtype.preconnectedSpace hpre).isPreconnected_univ
  rcases hunivpre.subset_or_subset hAopen hAclosed.isOpen_compl disjoint_compl_right
      (fun z _ => by_cases (fun hz : z ∈ A => Or.inl hz) (fun hz => Or.inr hz)) with hsub' | hsub'
  · exact hsub' (Set.mem_univ ⟨x, hx⟩)
  · exact absurd hAne.some_mem (hsub' (Set.mem_univ hAne.some))

end Work.CoreStep

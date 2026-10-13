import Mathlib
import Submission.Work.WilE7.CoreStep.sortSheets

namespace Work.WilE7.CoreStep

theorem hdich_of_persist {p m r : ℕ} (C : Set (Fin p → ℝ)) (hCpre : IsPreconnected C)
    (k : Fin r → ℕ)
    (s : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hpers : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')) (x₀ : Fin p → ℝ), x₀ ∈ C →
      (s t j x₀) (Fin.last m) = (s t' j' x₀) (Fin.last m) →
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) :
    ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
      ∀ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m) := by
  intro t t' j j' hex x hx
  classical
  -- Work in the subtype `C`; the set where the two sheets agree is clopen there.
  let φ : C → ℝ := fun y => (s t j (y : Fin p → ℝ)) (Fin.last m)
  let ψ : C → ℝ := fun y => (s t' j' (y : Fin p → ℝ)) (Fin.last m)
  let A : Set C := {y | φ y = ψ y}
  have hφcont : Continuous φ :=
    (continuous_apply (Fin.last m)).comp
      ((hcont t j).comp_continuous continuous_subtype_val (fun y => y.2))
  have hψcont : Continuous ψ :=
    (continuous_apply (Fin.last m)).comp
      ((hcont t' j').comp_continuous continuous_subtype_val (fun y => y.2))
  -- closed: preimage of the diagonal under a continuous map
  have hAclosed : IsClosed A := isClosed_eq hφcont hψcont
  -- nonempty: the given point of `C` where the two sheets agree
  have hAne : A.Nonempty := by
    obtain ⟨x₀, hx₀C, hx₀eq⟩ := hex
    exact ⟨⟨x₀, hx₀C⟩, by simpa [A, φ, ψ] using hx₀eq⟩
  -- open: persistence of the identity gives a neighbourhood of every point of `A`
  have hloc : ∀ y : C, y ∈ A → ∃ V : Set (Fin p → ℝ), IsOpen V ∧ (y : Fin p → ℝ) ∈ V ∧
      ∀ z : C, (z : Fin p → ℝ) ∈ V → z ∈ A := by
    intro y hy
    obtain ⟨U, hU, hUU⟩ :=
      hpers t t' j j' (y : Fin p → ℝ) y.2 (by simpa [A, φ, ψ] using hy)
    obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
    refine ⟨V, hVopen, hyV, ?_⟩
    intro z hz
    have hz' : (s t j (z : Fin p → ℝ)) (Fin.last m)
        = (s t' j' (z : Fin p → ℝ)) (Fin.last m) :=
      hUU (z : Fin p → ℝ) ⟨z.2, hVU hz⟩
    simpa [A, φ, ψ] using hz'
  choose V hVopen hyV hVgood using hloc
  let W : Set (Fin p → ℝ) := ⋃ y, ⋃ (hy : y ∈ A), V y hy
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
    (Subtype.preconnectedSpace hCpre).isPreconnected_univ
  rcases hunivpre.subset_or_subset hAopen hAclosed.isOpen_compl disjoint_compl_right
      (fun z _ => by_cases (fun hz : z ∈ A => Or.inl hz) (fun hz => Or.inr hz)) with hsub | hsub
  · exact hsub (Set.mem_univ ⟨x, hx⟩)
  · exact absurd hAne.some_mem (hsub (Set.mem_univ hAne.some))

end Work.WilE7.CoreStep

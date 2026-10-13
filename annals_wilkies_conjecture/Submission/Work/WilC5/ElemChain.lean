import Submission.Work.Wilkies.CG.Spec
import Mathlib.ModelTheory.ElementarySubstructures

namespace Work.WilC5

open FirstOrder Language

/-- **Tarski–Vaught witnesses for an elementary substructure.**

If `S ≤ M` is an elementary substructure, `φ` is a bounded formula with `n + 1` free variables,
`x : Fin n → S` is a tuple of elements of `S`, and the formula holds in `M` of the tuple `x`
together with some `a : M`, then it already holds of `x` together with some element of `S`.

This is the converse of `FirstOrder.Language.Substructure.isElementary_of_exists`, i.e. it says
that the inclusion `S ↪ M` satisfies the Tarski–Vaught test. -/
theorem exists_witness_of_isElementary {L : FirstOrder.Language} {M : Type} [L.Structure M]
    (S : L.ElementarySubstructure M)
    (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M)
    (h : φ.Realize default (Fin.snoc ((↑) ∘ x) a : Fin (n + 1) → M)) :
    ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) (↑b) : Fin (n + 1) → M) := by
  -- The existential closure `∃' φ` is witnessed in `M` ...
  have h1 : (∃' φ).Realize ((S.subtype : S → M) ∘ (default : Empty → S))
      ((S.subtype : S → M) ∘ x) := by
    rw [BoundedFormula.realize_ex]
    refine ⟨a, ?_⟩
    have hv : ((S.subtype : S → M) ∘ (default : Empty → S)) = (default : Empty → M) :=
      Unique.eq_default _
    rw [hv]
    exact h
  -- ... and the elementary embedding `S.subtype` transports it to `S`.
  have h2 : (∃' φ).Realize (default : Empty → S) x :=
    ((S.subtype).map_boundedFormula (∃' φ) (default : Empty → S) x).mp h1
  rw [BoundedFormula.realize_ex] at h2
  obtain ⟨b, hb⟩ := h2
  refine ⟨b, ?_⟩
  -- Transport the realization back from `S` to `M`.
  have h3 := ((S.subtype).map_boundedFormula φ (default : Empty → S) (Fin.snoc x b)).mpr hb
  have hv : ((S.subtype : S → M) ∘ (default : Empty → S)) = (default : Empty → M) :=
    Unique.eq_default _
  rw [hv] at h3
  convert h3 using 2
  rw [Fin.comp_snoc]
  simp

/-- **An increasing chain of elementary substructures has an elementary union.**

Given `S : ℕ → L.ElementarySubstructure M` with `S n ⊆ S (n + 1)` for all `n`, the union
`⋃ n, S n` is again the underlying set of an elementary substructure of `M`. -/
theorem ElemChain {L : FirstOrder.Language} {M : Type} [L.Structure M]
    (S : ℕ → L.ElementarySubstructure M)
    (hmono : ∀ n : ℕ, ((S n : Set M) ⊆ ((S (n + 1) : L.ElementarySubstructure M) : Set M))) :
    ∃ E : L.ElementarySubstructure M, (E : Set M) = ⋃ n : ℕ, (S n : Set M) := by
  -- Monotonicity in the index, by induction on the gap.
  have mono : ∀ {i j : ℕ}, i ≤ j → (S i : Set M) ⊆ (S j : Set M) := by
    intro i j hij
    induction hij with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  -- The union as a first-order substructure.
  let U : L.Substructure M :=
  { carrier := ⋃ n : ℕ, (S n : Set M)
    fun_mem := by
      intro n f x hx
      -- Every entry of the tuple lies in some `S (k i)`; the whole tuple lies in `S N` for
      -- `N` the maximum of the `k i`.
      choose k hk using fun i => Set.mem_iUnion.mp (hx i)
      refine Set.mem_iUnion.mpr ⟨Finset.univ.sup k, ?_⟩
      have hle : ∀ i, k i ≤ Finset.univ.sup k := fun i => Finset.le_sup (Finset.mem_univ i)
      have hmem : ∀ i, x i ∈ (S (Finset.univ.sup k) : Set M) := fun i => mono (hle i) (hk i)
      exact ((S (Finset.univ.sup k) : L.Substructure M)).fun_mem f x hmem }
  refine ⟨U.toElementarySubstructure ?_, ?_⟩
  · -- The Tarski–Vaught test for `U`, reduced to the corresponding test for a single `S N`.
    intro n φ x a ha
    choose k hk using fun i => Set.mem_iUnion.mp (x i).2
    have hle : ∀ i, k i ≤ Finset.univ.sup k := fun i => Finset.le_sup (Finset.mem_univ i)
    have hNk : ∀ i, ((x i : U) : M) ∈ (S (Finset.univ.sup k) : Set M) := fun i =>
      mono (hle i) (hk i)
    let x' : Fin n → S (Finset.univ.sup k) := fun i => ⟨x i, hNk i⟩
    obtain ⟨b, hb⟩ := exists_witness_of_isElementary (S (Finset.univ.sup k)) n φ x' a ha
    exact ⟨⟨b, Set.mem_iUnion.mpr ⟨Finset.univ.sup k, b.2⟩⟩, hb⟩
  · rfl

end Work.WilC5

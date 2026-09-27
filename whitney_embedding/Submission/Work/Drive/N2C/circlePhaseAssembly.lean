import Mathlib
import Submission.Work.Drive.N2C.circlePhase

/-!
# Extending a smooth periodic family on an embedded circle to the surface

Given a `CirclePhaseCover` of the curve `γ` — a finite family of open sets `U i` covering the curve
and smooth phase functions `φ i` on `U i` reading a parameter of the curve modulo the period — the
function

`G s y = ∑ i, ρ i (s, y) • A s (φ i y)`

(where `ρ` is a smooth partition of unity subordinate to the cover `{y | y.2 ∈ U i} ∪ {y | y.2 ∉ γ}`)
is smooth on `ℝ × M` and restricts to `A s x` on `γ x`: the terms with `ρ i` non-zero at `(s, γ x)`
have `γ x ∈ U i`, hence `φ i (γ x) = x + k` for an integer `k`, and `A` is `1`-periodic in its
second variable.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

noncomputable section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]

/-- **The assembly of the extension from a phase cover.** -/
theorem exists_contMDiff_extend_of_circlePhaseCover {γ : ℝ → M} (hγc : Continuous γ)
    (hper : Function.Periodic γ 1) {ι : Type*} [Fintype ι] (C : CirclePhaseCover γ ι)
    (A : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A p.1 p.2))
    (hperA : ∀ (s x : ℝ), A s (x + 1) = A s x) :
    ∃ G : ℝ → M → EuclideanSpace ℝ (Fin 3),
      ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × M => G p.1 p.2) ∧
      (∀ (s : ℝ) (x : ℝ), G s (γ x) = A s x) := by
  classical
  -- the compact piece of the circle, and every parameter has a representative in `[0,1]`
  have hKc : IsCompact (γ '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hγc
  have hKcl : IsClosed (γ '' Set.Icc (0:ℝ) 1) := hKc.isClosed
  have hmemK : ∀ x : ℝ, γ x ∈ γ '' Set.Icc (0:ℝ) 1 := by
    intro x
    refine ⟨Int.fract x, ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩, ?_⟩
    have h1 := (hper.zsmul ⌊x⌋ (Int.fract x)).symm
    simp only [zsmul_one] at h1
    rw [Int.fract_add_floor] at h1
    exact h1
  -- the open cover of `ℝ × M` on which the local phases are smooth
  let W : Option ι → Set (ℝ × M) := fun o => match o with
    | none => {p | p.2 ∉ γ '' Set.Icc (0:ℝ) 1}
    | some i => {p | p.2 ∈ C.U i}
  have hWopen : ∀ o, IsOpen (W o) := by
    intro o
    cases o with
    | none => exact isOpen_compl_iff.mpr (hKcl.preimage continuous_snd)
    | some i => exact (C.isOpen_U i).preimage continuous_snd
  have hWcover : Set.univ ⊆ ⋃ o, W o := by
    intro p _
    by_cases h : p.2 ∈ γ '' Set.Icc (0:ℝ) 1
    · obtain ⟨t, ht, ht2⟩ := h
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (C.cover ⟨t, ht2⟩)
      exact Set.mem_iUnion.mpr ⟨some i, hi⟩
    · exact Set.mem_iUnion.mpr ⟨none, h⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (s := (Set.univ : Set (ℝ × M))) isClosed_univ W hWopen hWcover
  -- the function to be extended, in coordinates
  let Bj : ℝ × ℝ → EuclideanSpace ℝ (Fin 3) := fun q => A q.1 q.2
  have hBsmooth : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,ℝ))) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      ((⊤ : ℕ∞) : WithTop ℕ∞) Bj := by
    have h := hA.contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  -- the local pieces
  let Φ : Option ι → ℝ × M → ℝ := fun o p => match o with
    | none => 0
    | some i => C.φ i p.2
  let g : Option ι → ℝ × M → EuclideanSpace ℝ (Fin 3) := fun o p => Bj (p.1, Φ o p)
  have hg : ∀ o, ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (g o) (W o) := by
    intro o
    cases o with
    | none =>
      have hpair : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓡 2))
          ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,ℝ))) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => (p.1, (0 : ℝ))) (W none) := by
        refine (contMDiffOn_prod_iff _).mpr ⟨?_, ?_⟩
        · exact contMDiffOn_fst
        · exact contMDiffOn_const
      have hcomp := hBsmooth.contMDiffOn.comp (t := Set.univ) hpair
        (fun p _ => Set.mem_univ _)
      simpa [g, Φ, Bj, Function.comp_def] using hcomp
    | some i =>
      have hpair : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓡 2))
          ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,ℝ))) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => (p.1, C.φ i p.2)) (W (some i)) := by
        refine (contMDiffOn_prod_iff _).mpr ⟨?_, ?_⟩
        · exact contMDiffOn_fst
        · have h1 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2)
              ((⊤ : ℕ∞) : WithTop ℕ∞) Prod.snd (W (some i)) := contMDiffOn_snd
          have h2 := (C.contMDiff_φ i).comp h1 (fun p hp => hp)
          simpa [Function.comp_def] using h2
      have hcomp := hBsmooth.contMDiffOn.comp (t := Set.univ) hpair
        (fun p _ => Set.mem_univ _)
      simpa [g, Φ, Bj, Function.comp_def] using hcomp
  refine ⟨fun s y => ∑ᶠ o, ρ o (s, y) • g o (s, y), ?_, ?_⟩
  · exact hρ.contMDiff_finsum_smul hWopen hg
  · intro s x
    have hAint : ∀ (y : ℝ) (k : ℤ), A s (y + (k : ℝ)) = A s y := by
      intro y k
      have hP : Function.Periodic (fun z => A s z) 1 := fun z => hperA s z
      have h := hP.int_mul k y
      simpa using h
    have hterm : ∀ o : Option ι,
        ρ o (s, γ x) • g o (s, γ x) = ρ o (s, γ x) • A s x := by
      intro o
      by_cases h0 : ρ o (s, γ x) = 0
      · rw [h0, zero_smul, zero_smul]
      · have hmem : (s, γ x) ∈ W o := hρ o (subset_closure (by simpa using h0))
        cases o with
        | none => exact absurd (hmemK x) hmem
        | some i =>
          have hUi : γ x ∈ C.U i := hmem
          obtain ⟨k, hk⟩ := C.phase i (γ x) hUi x rfl
          have hval : g (some i) (s, γ x) = A s x := by
            calc g (some i) (s, γ x) = Bj (s, Φ (some i) (s, γ x)) := rfl
              _ = A s (C.φ i (γ x)) := rfl
              _ = A s (x + (k : ℝ)) := by rw [hk]
              _ = A s x := hAint x k
          rw [hval]
    calc ∑ᶠ o, ρ o (s, γ x) • g o (s, γ x)
        = ∑ᶠ o, ρ o (s, γ x) • A s x := finsum_congr hterm
      _ = (∑ᶠ o, ρ o (s, γ x)) • A s x := (finsum_smul _ _).symm
      _ = (1 : ℝ) • A s x := by
            have hsum : (∑ᶠ o : Option ι, ρ o (s, γ x)) = 1 := by
              simpa using ρ.toPartitionOfUnity.sum_eq_one (Set.mem_univ (s, γ x))
            rw [hsum]
      _ = A s x := one_smul _ _

end

end Work.Drive.N2C

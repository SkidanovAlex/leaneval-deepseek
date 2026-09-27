import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Tools for smooth left inverses of properly embedded lines

Two reusable ingredients of the *smooth* (`C^∞`) statement
`Work.Noncompact.CompressionTube.exists_smooth_left_inverse_infty`, namely the smooth Urysohn bump
on a manifold and the gluing of local left inverses by a smooth partition of unity.

Both are stated at the *smooth* order `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`.  Note that this is **not**
`Notation.lean`'s `smoothOrder = ⊤ : WithTop ℕ∞`, which Mathlib denotes `ω` and which means
*analytic* (see `Mathlib/Analysis/Calculus/ContDiff/Defs.lean` and `ContDiffOn.analyticOn`);
the `ω` reading is the reason the sibling statements of this chapter do not compile against
Mathlib lemmas stated at `∞`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

/-- The *smooth* (`C^∞`) order, `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (not `smoothOrder`, which is `ω`). -/
abbrev infOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **A smooth Urysohn bump on a manifold.**  A compact set `K` inside an open set `W` admits a
smooth `[0,1]`-valued function equal to `1` on a neighbourhood of `K` and with topological support
inside `W`. -/
theorem exists_contMDiff_bump_between {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) infOrder M]
    [T2Space M] [SecondCountableTopology M]
    {K W : Set M} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ β : M → ℝ, ContMDiff (MC n) MCreal infOrder β ∧
      (∀ x, β x ∈ Set.Icc 0 1) ∧ K ⊆ interior {x | β x = 1} ∧ tsupport β ⊆ W := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : NormalSpace M := inferInstance
  have hKcl : IsClosed K := hK.isClosed
  have hdisj : Disjoint (Wᶜ) K := disjoint_compl_left_iff_subset.mpr hKW
  obtain ⟨f, hf0, hf1, hfI⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (MC n) hW.isClosed_compl hKcl hdisj
  refine ⟨f, f.contMDiff, hfI, ?_, ?_⟩
  · intro x hx
    exact mem_interior_iff_mem_nhds.mpr ((mem_nhdsSet_iff_forall.mp hf1) x hx)
  · have hsub : Wᶜ ⊆ interior {z | f z = 0} :=
      fun x hx => mem_interior_iff_mem_nhds.mpr ((mem_nhdsSet_iff_forall.mp hf0) x hx)
    have hset : {z | f z = 0} ⊆ (support f)ᶜ := by
      intro z hz
      rw [mem_compl_iff, mem_support]
      exact fun h => h hz
    have hinner : interior {z | f z = 0} ⊆ (tsupport f)ᶜ := by
      calc interior {z | f z = 0} ⊆ interior (support f)ᶜ := interior_mono hset
        _ = (tsupport f)ᶜ := interior_compl
    have h1 : tsupport f ⊆ (interior {z | f z = 0})ᶜ := by
      simpa using (compl_subset_compl.mpr hinner : (tsupport f)ᶜᶜ ⊆ (interior {z | f z = 0})ᶜ)
    have h2 : (interior {z | f z = 0})ᶜ ⊆ W := by
      intro x hx
      by_contra hxW
      exact hx (hsub hxW)
    exact h1.trans h2

/-- **Gluing local left inverses.**  Let `γ : ℝ → M` have closed image and let `(U s, F s)` be
local data: `U s` an open neighbourhood of `γ s` and `F s` a function smooth on `U s` with
`F s = s` on `U s ∩ range γ`.  Then the data glue to a globally smooth left inverse of `γ`.

Only the closedness of the range of `γ` is used (no smoothness, injectivity or properness of `γ`,
and no dimension hypothesis). -/
theorem smooth_left_inverse_of_local {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) infOrder M] [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hprop : IsProperMap γ)
    (U : ℝ → Set M) (hUo : ∀ s, IsOpen (U s)) (hUm : ∀ s, γ s ∈ U s)
    (F : ℝ → M → ℝ) (hF : ∀ s, ContMDiffOn (MC n) MCreal infOrder (F s) (U s))
    (hUF : ∀ s t : ℝ, γ t ∈ U s → F s (γ t) = t) :
    ∃ g : M → ℝ, ContMDiff (MC n) MCreal infOrder g ∧ ∀ s : ℝ, g (γ s) = s := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  let C : Set M := range γ
  have hCcl : IsClosed C := hprop.isClosed_range
  let V : Option ℝ → Set M := fun i => match i with | none => Cᶜ | some s => U s
  have hVo : ∀ i, IsOpen (V i) := by
    intro i; cases i with
    | none => exact hCcl.isOpen_compl
    | some s => exact hUo s
  have hVcov : C ⊆ ⋃ i, V i := by
    rintro x ⟨t, rfl⟩
    exact mem_iUnion.mpr ⟨some t, hUm t⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (MC n) hCcl V hVo hVcov
  let G : Option ℝ → M → ℝ := fun i => match i with | none => 0 | some s => F s
  have hG : ∀ i, ContMDiffOn (MC n) MCreal infOrder (G i) (V i) := by
    intro i; cases i with
    | none => exact contMDiffOn_const
    | some s => exact hF s
  refine ⟨fun x => ∑ᶠ i, ρ i x • G i x, ?_, ?_⟩
  · exact hρ.contMDiff_finsum_smul hVo hG
  · intro t
    have htC : γ t ∈ C := ⟨t, rfl⟩
    have hterm : ∀ i, ρ i (γ t) • G i (γ t) = ρ i (γ t) • t := by
      intro i
      by_cases h0 : ρ i (γ t) = 0
      · simp [h0]
      · have hmem : γ t ∈ tsupport (ρ i) := subset_closure (mem_support.mpr h0)
        have hsub : γ t ∈ V i := hρ i hmem
        cases i with
        | none => exact absurd htC hsub
        | some s => show ρ (some s) (γ t) • F s (γ t) = ρ (some s) (γ t) • t
                    rw [hUF s t hsub]
    change (∑ᶠ i, ρ i (γ t) • G i (γ t)) = t
    rw [finsum_congr hterm]
    have h₁ : (∑ᶠ i, ρ i (γ t) • t) = ∑ i ∈ ρ.finsupport (γ t), ρ i (γ t) • t :=
      (ρ.sum_finsupport_smul_eq_finsum (γ t) (fun _ _ => t)).symm
    rw [h₁, ← Finset.sum_smul, ρ.sum_finsupport (γ t) htC, one_smul]

end

end Work.Noncompact.CompressionTube

import Mathlib
import Submission.Work.Diff.EXT.covK_onFrameFamily

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gluing finitely many local jointly smooth tangent fields into a global one

Given a finite family of open sets `V i ⊆ ℝ × M` covering the slab `[a,b] × M` and, on each `V i`,
a tangent field `G i` which is jointly smooth there and agrees on the slab with a given field `X`,
we produce a field `Xg`, jointly smooth on all of `ℝ × M`, which agrees with `X` on the slab.
This is the "global extension from a finite cover" step of the ODE area: it turns the local
one-sided extensions of `Work.Diff.ODE.exists_localExt_at` into a global field, to which the global
flow contract `Submission.Diff.SmoothFlow` can be applied.

The proof is the classical partition-of-unity argument.  The three ingredients are
`exists_smooth_partition_subordinate` (a smooth partition of unity subordinate to the cover),
`jointField_smul_of_tsupport` (cutting off a field that is smooth on an open set by a smooth
function supported in it) and `jointField_finset_sum_univ` (finite sums of jointly smooth fields).
-/

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- A finite sum of jointly smooth tangent fields on `ℝ × M` is jointly smooth on `ℝ × M`. -/
theorem jointField_finset_sum_univ
    {ι : Type*} (s : Finset ι) {X : ι → ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (h : ∀ i ∈ s, Work.Diff.EXT.JointField (X i) Set.univ) :
    Work.Diff.EXT.JointField (fun t y => ∑ i ∈ s, X i t y) Set.univ := by
  classical
  intro p _
  rw [contMDiffWithinAt_univ]
  -- work inside the chart at `p.2`
  set W : Set (ℝ × M) := Set.univ ×ˢ (chartAt H p.2).source with hWdef
  have hWopen : IsOpen W := isOpen_univ.prod (chartAt H p.2).open_source
  have hpW : p ∈ W := ⟨mem_univ p.1, mem_chart_source H p.2⟩
  have hWsub : W ⊆ Set.univ ×ˢ (chartAt H p.2).source := fun q hq => hq
  have h1 : Work.Diff.EXT.JointField (fun t y => ∑ i ∈ s, (1 : ℝ) • X i t y) W :=
    Work.Diff.EXT.jointField_sum (x₀ := p.2) hWsub (X := X) (c := fun _ _ => (1 : ℝ)) s
      (fun i hi => (h i hi).mono (Set.subset_univ W)) (fun i _ => contMDiffOn_const)
  have h2 : (fun t y => ∑ i ∈ s, (1 : ℝ) • X i t y) = (fun t y => ∑ i ∈ s, X i t y) := by
    funext t y
    simp
  rw [h2] at h1
  exact h1.contMDiffAt (hWopen.mem_nhds hpW)

/-- Multiplying a field which is jointly smooth on an open set `V` by a smooth function whose
topological support is contained in `V` gives a globally jointly smooth field. -/
theorem jointField_smul_of_tsupport
    {V : Set (ℝ × M)} (hV : IsOpen V)
    {X : ℝ → Work.Diff.EXT.TField (I := I) (M := M)} (hX : Work.Diff.EXT.JointField X V)
    {ρ : ℝ × M → ℝ}
    (hρ : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) ∞ ρ)
    (hsub : tsupport ρ ⊆ V) :
    Work.Diff.EXT.JointField (fun t y => ρ (t, y) • X t y) Set.univ := by
  intro p _
  rw [contMDiffWithinAt_univ]
  by_cases hp : p ∈ tsupport ρ
  · -- at a point of `tsupport ρ ⊆ V` the field is a product of two smooth objects
    have hpV : p ∈ V := hsub hp
    set W : Set (ℝ × M) := (Set.univ ×ˢ (chartAt H p.2).source) ∩ V with hWdef
    have hWopen : IsOpen W := (isOpen_univ.prod (chartAt H p.2).open_source).inter hV
    have hpW : p ∈ W := ⟨⟨mem_univ p.1, mem_chart_source H p.2⟩, hpV⟩
    have hsm : Work.Diff.EXT.JointField (fun t y => ρ (t, y) • X t y) W :=
      Work.Diff.EXT.jointField_smul (x₀ := p.2) (fun q hq => hq.1)
        (hX.mono (fun q hq => hq.2)) hρ.contMDiffOn
    exact hsm.contMDiffAt (hWopen.mem_nhds hpW)
  · -- off the support the field agrees, near `p`, with the (smooth) zero section
    have hcompl : (tsupport ρ)ᶜ ∈ 𝓝 p := (isClosed_tsupport ρ).isOpen_compl.mem_nhds hp
    have hev : (fun q : ℝ × M => (⟨q.2, ρ q • X q.1 q.2⟩ : TangentBundle I M))
        =ᶠ[𝓝 p] (fun q : ℝ × M => (⟨q.2, (0 : TangentSpace I q.2)⟩ : TangentBundle I M)) := by
      filter_upwards [hcompl] with q hq
      have h0 : ρ q = 0 := by
        by_contra hcon
        exact hq (subset_closure (Function.mem_support.mpr hcon))
      rw [h0, zero_smul]
    have hzero : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, (0 : TangentSpace I q.2)⟩ : TangentBundle I M)) :=
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd
    exact hzero.contMDiffAt.congr_of_eventuallyEq hev

/-- **Smooth partition of unity subordinate to a finite open cover of a slab.**  For a finite family
of open sets `V i` (`i ∈ s`) covering `[a,b] × M`, there are smooth functions `ρ i` with
`tsupport (ρ i) ⊆ V i`, vanishing for `i ∉ s`, and summing to `1` on the slab. -/
theorem exists_smooth_partition_subordinate
    {ι : Type*} (s : Finset ι) (V : ι → Set (ℝ × M)) {a b : ℝ}
    [T2Space M] [CompactSpace M]
    (hV : ∀ i ∈ s, IsOpen (V i))
    (hcover : (Set.Icc a b ×ˢ Set.univ) ⊆ ⋃ i ∈ s, V i) :
    ∃ ρ : ι → ℝ × M → ℝ,
      (∀ i ∈ s, ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
        (⊤ : ℕ∞) (ρ i)) ∧
      (∀ i ∈ s, tsupport (ρ i) ⊆ V i) ∧
      (∀ i ∉ s, ρ i = 0) ∧
      (∀ q ∈ Set.Icc a b ×ˢ Set.univ, ∑ i ∈ s, ρ i q = 1) := by
  classical
  -- the cover of all of `ℝ × M`: the `V i` for `i ∈ s` and the complement of the slab
  let U : ι ⊕ Unit → Set (ℝ × M) := fun j =>
    Sum.elim (fun i => if i ∈ s then V i else ∅) (fun _ => (Set.Icc a b ×ˢ Set.univ)ᶜ) j
  have hUinl : ∀ i, U (Sum.inl i) = if i ∈ s then V i else ∅ := fun i => rfl
  have hUinr : ∀ u, U (Sum.inr u) = (Set.Icc a b ×ˢ Set.univ)ᶜ := fun u => rfl
  have hUopen : ∀ j, IsOpen (U j) := by
    intro j
    rcases j with i | u
    · rw [hUinl i]
      by_cases hi : i ∈ s
      · rw [if_pos hi]; exact hV i hi
      · rw [if_neg hi]; exact isOpen_empty
    · rw [hUinr u]; exact (isClosed_Icc.prod isClosed_univ).isOpen_compl
  have hUcover : (Set.univ : Set (ℝ × M)) ⊆ ⋃ j, U j := by
    intro q _
    by_cases hqs : q ∈ Set.Icc a b ×ˢ Set.univ
    · have hq : q ∈ ⋃ i ∈ s, V i := hcover hqs
      rw [Set.mem_iUnion₂] at hq
      obtain ⟨i, hi, hqi⟩ := hq
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, by rw [hUinl i, if_pos hi]; exact hqi⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inr (), by rw [hUinr]; exact hqs⟩
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    ((modelWithCornersSelf ℝ ℝ).prod I) (s := Set.univ) isClosed_univ U hUopen hUcover
  refine ⟨fun i => (χ (Sum.inl i) : ℝ × M → ℝ), ?_, ?_, ?_, ?_⟩
  · intro i _
    exact (χ (Sum.inl i)).contMDiff
  · intro i hi
    have h1 := hχ (Sum.inl i)
    rwa [hUinl i, if_pos hi] at h1
  · intro i hi
    funext q
    have h1 := hχ (Sum.inl i)
    rw [hUinl i, if_neg hi] at h1
    by_contra hcon
    exact h1 (subset_closure (Function.mem_support.mpr hcon))
  · intro q hq
    have h1 : ∑ᶠ j : ι ⊕ Unit, (χ j : ℝ × M → ℝ) q = 1 := χ.sum_eq_one (mem_univ q)
    have hsupp : Function.support (fun j : ι ⊕ Unit => (χ j : ℝ × M → ℝ) q)
        ⊆ ((s.disjSum ({()} : Finset Unit) : Finset (ι ⊕ Unit)) : Set (ι ⊕ Unit)) := by
      intro j hj
      rw [Finset.mem_coe, Finset.mem_disjSum]
      rcases j with i | u
      · left
        refine ⟨i, ?_, rfl⟩
        by_contra hi
        have h2 := hχ (Sum.inl i)
        rw [hUinl i, if_neg hi] at h2
        exact hj (by
          by_contra hc
          exact False.elim (h2 (subset_closure (Function.mem_support.mpr hc))))
      · right
        refine ⟨(), Finset.mem_singleton_self _, ?_⟩
        have hu : u = () := Subsingleton.elim u ()
        rw [hu]
    rw [finsum_eq_sum_of_support_subset (fun j : ι ⊕ Unit => (χ j : ℝ × M → ℝ) q) hsupp] at h1
    rw [Finset.sum_disjSum] at h1
    have hzero : (χ (Sum.inr ()) : ℝ × M → ℝ) q = 0 := by
      have h2 := hχ (Sum.inr ())
      rw [hUinr] at h2
      by_contra hc
      exact (h2 (subset_closure (Function.mem_support.mpr hc))) hq
    have hsing : ∑ x ∈ ({()} : Finset Unit), (χ (Sum.inr x) : ℝ × M → ℝ) q = 0 := by
      rw [Finset.sum_singleton]
      exact hzero
    rw [hsing, add_zero] at h1
    exact h1

end Helpers

/-- **Gluing lemma**: a finite linear combination of jointly smooth fields `G i` (smooth on `V i`)
with coefficients supported in `V i` is jointly smooth on all of `ℝ × M`. -/
theorem jointField_sum_partition_glue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {ι : Type*} (s : Finset ι) {V : ι → Set (ℝ × M)}
    {G : ι → ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (hV : ∀ i ∈ s, IsOpen (V i)) (hG : ∀ i ∈ s, Work.Diff.EXT.JointField (G i) (V i))
    {ρ : ι → ℝ × M → ℝ}
    (hρ : ∀ i ∈ s, ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) (ρ i))
    (hρsub : ∀ i ∈ s, tsupport (ρ i) ⊆ V i) :
    Work.Diff.EXT.JointField (fun t y => ∑ i ∈ s, ρ i (t, y) • G i t y) Set.univ :=
  jointField_finset_sum_univ s
    (fun i hi => jointField_smul_of_tsupport (hV i hi) (hG i hi) (hρ i hi) (hρsub i hi))

theorem exists_global_ext_of_finite_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {X : ℝ → Work.Diff.EXT.TField (I := I) (M := M)} {a b : ℝ} (hab : a < b)
    {ι : Type*} (s : Finset ι) (V : ι → Set (ℝ × M))
    (G : ι → ℝ → Work.Diff.EXT.TField (I := I) (M := M))
    (hV : ∀ i ∈ s, IsOpen (V i)) (hG : ∀ i ∈ s, Work.Diff.EXT.JointField (G i) (V i))
    (hcover : (Set.Icc a b ×ˢ Set.univ) ⊆ ⋃ i ∈ s, V i)
    (hagr : ∀ i ∈ s, ∀ q ∈ V i, q.1 ∈ Set.Icc a b → G i q.1 q.2 = X q.1 q.2) :
    ∃ Xg : ℝ → Work.Diff.EXT.TField (I := I) (M := M),
      Work.Diff.EXT.JointField Xg Set.univ ∧
      ∀ t ∈ Set.Icc a b, ∀ x : M, Xg t x = X t x := by
  classical
  obtain ⟨ρ, hρsmooth, hρsub, hρzero, hρsum⟩ :=
    exists_smooth_partition_subordinate (I := I) (M := M) s V hV hcover
  refine ⟨fun t y => ∑ i ∈ s, ρ i (t, y) • G i t y,
    jointField_sum_partition_glue s hV hG hρsmooth hρsub, ?_⟩
  intro t ht x
  have htx : ((t, x) : ℝ × M) ∈ Set.Icc a b ×ˢ Set.univ :=
    ⟨⟨ht.1, ht.2⟩, mem_univ x⟩
  have h1 : ∑ i ∈ s, ρ i (t, x) • G i t x = ∑ i ∈ s, ρ i (t, x) • X t x := by
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : ρ i (t, x) = 0
    · rw [h, zero_smul, zero_smul]
    · have hmem : (t, x) ∈ tsupport (ρ i) := subset_closure (Function.mem_support.mpr h)
      have hVmem : (t, x) ∈ V i := hρsub i hi hmem
      have hagri : G i t x = X t x := hagr i hi (t, x) hVmem ⟨ht.1, ht.2⟩
      rw [hagri]
  change (∑ i ∈ s, ρ i (t, x) • G i t x) = X t x
  rw [h1, ← Finset.sum_smul, hρsum (t, x) htx, one_smul]

end Work.Diff.ODE

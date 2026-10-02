import Mathlib
import Submission.Work.Thom.subsingleton_PieceCoh_genFibre
import Submission.Work.Cohomology.subsingleton_pdCohSub_union
import Submission.Work.Cohomology.pdCohSub_iUnion_of_wf
import Submission.Work.Thom.Glue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Vanishing of the relative cohomology of a bundle piece below the rank, for an arbitrary piece

For a real vector bundle `Z` of rank `n` over a topological space `B` and an **arbitrary** subset
`W ⊆ B` (not necessarily open, and not necessarily contained in a chart), the relative cohomology
of the piece of the Thom pair over `W`,

  `Work.Thom.PieceCoh Z W m = H^m(X|_W, X|_W ∖ 0)`,   `X = Z.TotalSpace`,

vanishes for `m < n`.

The chart-local case (`W` contained in a single chart of `Z`) is
`Work.Thom.subsingleton_PieceCoh_genFibre`.  The passage to an arbitrary `W` is the usual
transfinite Mayer–Vietoris induction over the cover of the bundle, run **inside the subspace
`↥(π⁻¹ W)` of the total space**: there the pieces `π⁻¹(W ∩ ⋃_{β ≤ i} baseSet β)` are *open*, so
the two-piece step `Work.Cohomology.subsingleton_pdCohSub_union` and the transfinite union step
`Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf` both apply.  The chart-local input in the
subspace is transported from the ambient total space by
`Work.Cohomology.subU_pdCohSub_transfer`, and at the end the vanishing of the relative cohomology
of the pair `(↥(π⁻¹ W), ↥(π⁻¹ W) ∖ 0)` is read off from the vanishing for `Set.univ` inside the
subspace.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- `Subsingleton` of the relative cohomology of a piece transfers along an equality of the
pieces (inside a fixed ambient space). -/
theorem subsingleton_pdCohSub_of_eq {X : Type} [TopologicalSpace X] (A : Set X) {U U' : Set X}
    {k : ℕ} (h : U = U') (hs : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A U k)) :
    Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A U' k) := by
  cases h
  exact hs

/-- Vanishing of the relative cohomology of a pair from the vanishing of the relative cohomology
of the piece `Set.univ` (the identification `↥univ ≅ X` of the pairs). -/
theorem subsingleton_pdCoh_of_subsingleton_pdCohSub_univ' {X : Type} [TopologicalSpace X]
    (A : Set X) (k : ℕ)
    (h : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A Set.univ k)) :
    Subsingleton (Work.Cohomology.pdCoh (TopCat.of X) A k) := by
  let e : ↥(Set.univ : Set X) ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Set.mem_univ x⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  obtain ⟨iso⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    {y : ↥(Set.univ : Set X) | (y : X) ∈ A} A e (fun _ => Iff.rfl) k
  exact Work.Cohomology.subsingleton_of_iso iso h

/-- **Vanishing of the relative cohomology of a bundle piece below the rank**, for an arbitrary
subset `W` of the base and an arbitrary finite-dimensional real fibre. -/
theorem subsingleton_PieceCoh_of_lt_finrank {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (W : Set B) {m : ℕ}
    (hm : m < Module.finrank ℝ F) :
    Subsingleton (Work.Thom.PieceCoh Z W m) := by
  classical
  let W₀ : Set Z.TotalSpace := Z.proj ⁻¹' W
  let A' : Set ↥W₀ := {y : ↥W₀ | (y : Z.TotalSpace) ∈ zeroComplement Z}
  have hmain : Subsingleton (Work.Cohomology.pdCoh (TopCat.of ↥W₀) A' m) := by
    obtain ⟨inst, hwf⟩ := exists_wellFoundedLT ι
    letI : LinearOrder ι := inst
    haveI : WellFoundedLT ι := hwf
    let Q : ι → Set B := fun i => ⋃ β ≤ i, Z.baseSet β
    let P : ι → Set B := fun i => ⋃ β < i, Z.baseSet β
    let V : ι → Set ↥W₀ := fun i => {z : ↥W₀ | (z : Z.TotalSpace) ∈ Z.proj ⁻¹' (Q i)}
    have hQP : ∀ i, Q i = P i ∪ Z.baseSet i := by
      intro i
      ext x
      simp only [Q, P, Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro ⟨β, hβ, hx⟩
        rcases lt_or_eq_of_le hβ with h | h
        · exact Or.inl ⟨β, h, hx⟩
        · exact Or.inr (h ▸ hx)
      · rintro (⟨β, hβ, hx⟩ | hx)
        · exact ⟨β, le_of_lt hβ, hx⟩
        · exact ⟨i, le_rfl, hx⟩
    have hVopen : ∀ i, IsOpen (V i) := by
      intro i
      exact ((isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ i => Z.isOpen_baseSet β).preimage
        Z.continuous_proj).preimage continuous_subtype_val
    have hVmono : Monotone V := by
      intro i j hij z hz
      simp only [V, Q, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iUnion] at hz ⊢
      obtain ⟨β, hβ, hz⟩ := hz
      exact ⟨β, le_trans hβ hij, hz⟩
    -- the well-founded induction over the cover of the base
    have key : ∀ i : ι, ∀ j ≤ m,
        Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥W₀) A' (V i) j) := by
      intro i
      refine WellFoundedLT.induction (motive := fun i : ι => ∀ j ≤ m,
        Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥W₀) A' (V i) j)) i ?_
      intro i ih j hj
      haveI : Inhabited ι := ⟨i⟩
      -- the chart-local vanishing, transported from the total space into the subspace `↥W₀`
      have hchart : ∀ (T : Set B), T ⊆ Z.baseSet i → T ⊆ W → ∀ e : ℕ,
          e < Module.finrank ℝ F →
          Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥W₀) A'
            {z : ↥W₀ | (z : Z.TotalSpace) ∈ Z.proj ⁻¹' T} e) := by
        intro T hT hTW e he
        have hE : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
            (zeroComplement Z) (Z.proj ⁻¹' T) e) :=
          subsingleton_PieceCoh_genFibre Z i hT he
        have hsub : Z.proj ⁻¹' T ⊆ W₀ := fun x hx => hTW (Set.mem_preimage.mp hx)
        have htr := Work.Cohomology.subU_pdCohSub_transfer (zeroComplement Z) hsub e hE
        refine subsingleton_pdCohSub_of_eq A' ?_ htr
        rfl
      -- the union of the pieces of the smaller indices is the piece over `P i`
      have hPQ2 : (⋃ k : ↥(Set.Iio i), Q k.1) = P i := by
        ext x
        simp only [P, Q, Set.mem_iUnion]
        constructor
        · rintro ⟨k, β, hβ, hx⟩
          exact ⟨β, lt_of_le_of_lt hβ k.2, hx⟩
        · rintro ⟨β, hβ, hx⟩
          exact ⟨⟨β, hβ⟩, β, le_rfl, hx⟩
      have hprev_eq : (⋃ k : ↥(Set.Iio i), V k.1)
          = {z : ↥W₀ | (z : Z.TotalSpace) ∈ Z.proj ⁻¹' (P i)} := by
        have h1 : (⋃ k : ↥(Set.Iio i), V k.1)
            = (Subtype.val : ↥W₀ → Z.TotalSpace) ⁻¹'
                (⋃ k : ↥(Set.Iio i), Z.proj ⁻¹' (Q k.1)) := by
          rw [Set.preimage_iUnion]
          rfl
        rw [h1, ← Set.preimage_iUnion, hPQ2]
        rfl
      -- the transfinite union step on the smaller pieces
      have hlim := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf A'
        (fun k : ↥(Set.Iio i) => V k.1) (fun k => hVopen k.1)
        (fun a b hab => hVmono hab) m (fun k j hj => ih k.1 k.2 j hj)
      have hUj : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥W₀) A'
          {z : ↥W₀ | (z : Z.TotalSpace) ∈ Z.proj ⁻¹' (P i)} j) :=
        subsingleton_pdCohSub_of_eq A' hprev_eq (hlim j hj)
      -- the two-piece Mayer–Vietoris step, adding the chart `i`
      refine Work.Cohomology.subsingleton_pdCohSub_union A'
        (W := V i) (U := {z : ↥W₀ | (z : Z.TotalSpace) ∈ Z.proj ⁻¹' (P i)})
        (V := {z : ↥W₀ | (z : Z.TotalSpace) ∈ Z.proj ⁻¹' (Z.baseSet i)})
        (hVopen i) ?_ ?_ ?_ ?_ ?_ j hUj ?_ ?_
      · exact ((isOpen_iUnion fun β => isOpen_iUnion fun _ : β < i =>
          Z.isOpen_baseSet β).preimage Z.continuous_proj).preimage continuous_subtype_val
      · exact (Z.isOpen_baseSet i).preimage Z.continuous_proj |>.preimage continuous_subtype_val
      · -- `U ⊆ V i`
        intro z hz
        simp only [V, P, Q, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iUnion] at hz ⊢
        obtain ⟨β, hβ, hz⟩ := hz
        exact ⟨β, le_of_lt hβ, hz⟩
      · -- `V ⊆ V i`
        intro z hz
        simp only [V, Q, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iUnion]
        exact ⟨i, le_rfl, hz⟩
      · -- `U ∪ V = V i`
        ext z
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, V]
        rw [hQP i]
        simp only [Set.mem_union]
      · -- the chart-local piece over `baseSet i`
        refine subsingleton_pdCohSub_of_eq A' ?_
          (hchart (Z.baseSet i ∩ W) Set.inter_subset_left Set.inter_subset_right j (by omega))
        ext z
        constructor
        · intro hz
          exact hz.1
        · intro hz
          exact ⟨hz, z.2⟩
      · -- the overlap, one degree down
        intro e he
        have hen : e < Module.finrank ℝ F := by omega
        refine subsingleton_pdCohSub_of_eq A' ?_
          (hchart ((P i ∩ Z.baseSet i) ∩ W) (fun x hx => hx.1.2)
            (fun x hx => hx.2) e hen)
        ext z
        constructor
        · intro hz
          exact ⟨hz.1.1, hz.1.2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2⟩, z.2⟩
    -- the whole subspace is the union of the pieces
    have hunion : (⋃ i : ι, V i) = Set.univ := by
      have hQB : (⋃ i : ι, Q i) = Set.univ := by
        refine Set.eq_univ_of_forall fun x => ?_
        refine Set.mem_iUnion.mpr ⟨Z.indexAt x, ?_⟩
        simp only [Q, Set.mem_iUnion]
        exact ⟨Z.indexAt x, le_rfl, Z.mem_baseSet_at x⟩
      have h1 : (⋃ i : ι, V i)
          = (Subtype.val : ↥W₀ → Z.TotalSpace) ⁻¹' (⋃ i : ι, Z.proj ⁻¹' (Q i)) := by
        rw [Set.preimage_iUnion]
        rfl
      rw [h1, ← Set.preimage_iUnion, hQB]
      simp
    -- the transfinite union step over the whole index set
    have hfin := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf A' V hVopen hVmono m
      (fun i j hj => key i j hj)
    have hsub : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of ↥W₀) A' Set.univ m) :=
      subsingleton_pdCohSub_of_eq A' hunion (hfin m le_rfl)
    exact subsingleton_pdCoh_of_subsingleton_pdCohSub_univ' A' m hsub
  exact hmain

end

end Work.Thom

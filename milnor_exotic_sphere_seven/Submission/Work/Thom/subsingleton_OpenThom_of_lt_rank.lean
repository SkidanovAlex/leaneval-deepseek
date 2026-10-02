import Mathlib
import Submission.Work.Thom.subsingleton_PieceCoh_of_lt_rank
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.subsingleton_pdCohSub_union
import Submission.Work.Cohomology.pdCohSub_iUnion_of_wf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# Global low-degree vanishing of the Thom pair of a real bundle of rank `n`

For a real vector bundle `Z` of rank `n` over a topological space `B`, presented by gluing data
(charts) indexed by `ι`, and for `W ⊆ B` a set contained in a single chart of `Z`, the relative
cohomology `Work.Thom.PieceCoh Z W m = H^m(X|_W, X|_W ∖ 0)` of the piece of the Thom pair over
`W` vanishes below the rank (`Work.Thom.subsingleton_PieceCoh_of_lt_rank`).

This file removes the chart restriction.  Theorem `subsingleton_OpenThom_of_lt_rank` proves

  `H^m(E, E∖0; ℤ) = 0` for `m < n`

for *every* real bundle of rank `n`, with **no** hypothesis on the base `B` (in particular no
paracompactness, no finiteness of the cover, no separation) and none on `ι`.

## The argument

We prove the stronger statement

`Q_j(W) : Subsingleton (H^j(X|_{⋃ β ≤ i baseSet β}, X|_{⋃ β ≤ i baseSet β} ∖ 0))`

for the *cumulative* pieces of the cover, and then pass to the union.  Two tools do all the work,
both in terms of the relative cohomology `pdCohSub` of the honest relative cochain complex:

* `Work.Cohomology.subsingleton_pdCohSub_union` — the two-piece Mayer–Vietoris step: if the three
  pieces `U`, `V`, `U ∩ V` of the pair have vanishing cohomology in the relevant degrees then so
  does `U ∪ V`;
* `Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf` — the transfinite union step: for an
  increasing well-ordered family of open sets all of whose members have vanishing cohomology up to
  degree `d`, the union does too.

Fixing the degree `m < n`, we endow `ι` with a well-order (Zermelo).  By well-founded recursion on
`i : ι` we show `Q_j (⋃ β ≤ i, baseSet β)` for every `j ≤ m`:

* the union `⋃ β < i, (⋃ γ ≤ β, baseSet γ)` of the previously handled pieces is `⋃ β < i, baseSet β`,
  so the transfinite union step applies to the family of earlier pieces (well-founded induction
  hypothesis) and gives vanishing on `⋃ β < i, baseSet β`;
* the two-piece step applied to `U = X|_{⋃ β < i baseSet β}`, `V = X|_{baseSet i}` (whose overlap is
  chart-local, hence covered by `subsingleton_PieceCoh_of_lt_rank`) gives `Q_j (⋃ β ≤ i baseSet β)`.

Finally the same transfinite union step, applied to the whole family of cumulative pieces, gives
vanishing on `⋃ i, (⋃ β ≤ i, baseSet β) = B`; transporting along the homeomorphism of pairs
`(↥univ, ↥univ ∩ A) ≅ (X, A)` gives the claim for `H^m(E, E∖0)`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **The relative cohomology of the pair `(X,A)` from the piece over all of `X`.**  The pair
`(↥(univ : Set X), ↥univ ∩ A)` is the pair `(X,A)` under the canonical homeomorphism, so a
subsingleton on the former gives one on the latter. -/
theorem subsingleton_pdCoh_of_subsingleton_pdCohSub_univ {X : Type} [TopologicalSpace X]
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

/-- Global low-degree vanishing of the Thom pair of a real bundle of rank `n`:
`H^m(E, E∖0; ℤ) = 0` for `m < n` (`E = Z.TotalSpace`, `E∖0 = Work.Thom.zeroComplement Z`). -/
theorem subsingleton_OpenThom_of_lt_rank {B : Type} [TopologicalSpace B] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (m : ℕ) (hm : m < n) :
    Subsingleton (Work.Thom.OpenThom Z m) := by
  classical
  obtain ⟨inst, hwf⟩ := exists_wellFoundedLT ι
  letI : LinearOrder ι := inst
  haveI : WellFoundedLT ι := hwf
  -- the cumulative pieces of the cover, at the level of the base and of the total space
  let Q : ι → Set B := fun i => ⋃ β ≤ i, Z.baseSet β
  let P : ι → Set B := fun i => ⋃ β < i, Z.baseSet β
  let Cov : ι → Set Z.TotalSpace := fun i => Z.proj ⁻¹' (Q i)
  -- `Q i = P i ∪ baseSet i`
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
  -- `P i = ⋃ β < i, Q β`
  have hPQ : ∀ i, P i = ⋃ β < i, Q β := by
    intro i
    ext x
    simp only [P, Q, Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hx⟩
      exact ⟨β, hβ, β, le_rfl, hx⟩
    · rintro ⟨β, hβ, γ, hγ, hx⟩
      exact ⟨γ, lt_of_le_of_lt hγ hβ, hx⟩
  have hCovopen : ∀ i, IsOpen (Cov i) := by
    intro i
    exact (isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ i => Z.isOpen_baseSet β).preimage
      Z.continuous_proj
  have hCovmono : Monotone Cov := by
    intro i j hij x hx
    simp only [Cov, Q, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨β, hβ, hx⟩ := hx
    exact ⟨β, le_trans hβ hij, hx⟩
  -- the well-founded induction
  have key : ∀ i : ι, ∀ j ≤ m,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Cov i) j) := by
    intro i
    refine WellFoundedLT.induction (motive := fun i : ι => ∀ j ≤ m,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Cov i) j)) i ?_
    intro i ih j hj
    -- the union of the pieces of the smaller indices is the piece over `P i`
    have hPQ2 : (⋃ k : ↥(Set.Iio i), Q k.1) = P i := by
      ext x
      simp only [P, Q, Set.mem_iUnion]
      constructor
      · rintro ⟨k, β, hβ, hx⟩
        exact ⟨β, lt_of_le_of_lt hβ k.2, hx⟩
      · rintro ⟨β, hβ, hx⟩
        exact ⟨⟨β, hβ⟩, β, le_rfl, hx⟩
    have hprev_eq : (⋃ k : ↥(Set.Iio i), Cov k.1) = Z.proj ⁻¹' (P i) := by
      have h1 : (⋃ k : ↥(Set.Iio i), Cov k.1)
          = ⋃ k : ↥(Set.Iio i), Z.proj ⁻¹' (Q k.1) := rfl
      rw [h1, ← Set.preimage_iUnion, hPQ2]
    -- the transfinite union step on the smaller pieces
    have hlim := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf (zeroComplement Z)
      (fun k : ↥(Set.Iio i) => Cov k.1) (fun k => hCovopen k.1)
      (fun a b hab => hCovmono hab) m (fun k j hj => ih k.1 k.2 j hj)
    have hUj : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
        (zeroComplement Z) (Z.proj ⁻¹' (P i)) j) := hprev_eq ▸ hlim j hj
    -- the two-piece Mayer–Vietoris step, adding the chart `i`
    refine Work.Cohomology.subsingleton_pdCohSub_union (zeroComplement Z)
      (W := Cov i) (U := Z.proj ⁻¹' (P i)) (V := Z.proj ⁻¹' (Z.baseSet i))
      (hCovopen i) ?_ ?_ ?_ ?_ ?_ j hUj ?_ ?_
    · exact (isOpen_iUnion fun β => isOpen_iUnion fun _ : β < i => Z.isOpen_baseSet β).preimage
        Z.continuous_proj
    · exact (Z.isOpen_baseSet i).preimage Z.continuous_proj
    · refine Set.preimage_mono fun x hx => ?_
      simp only [P, Q, Set.mem_iUnion] at hx ⊢
      obtain ⟨β, hβ, hx⟩ := hx
      exact ⟨β, le_of_lt hβ, hx⟩
    · refine Set.preimage_mono fun x hx => ?_
      simp only [Q, Set.mem_iUnion]
      exact ⟨i, le_rfl, hx⟩
    · rw [← Set.preimage_union, ← hQP i]
    · haveI : Inhabited ι := ⟨i⟩
      exact subsingleton_PieceCoh_of_lt_rank n ι Z i (fun _ hx => hx) (by omega)
    · intro e he
      haveI : Inhabited ι := ⟨i⟩
      have hen : e < n := by omega
      have h1 : Subsingleton (PieceCoh Z (P i ∩ Z.baseSet i) e) :=
        subsingleton_PieceCoh_of_lt_rank n ι Z i (fun x hx => hx.2) hen
      simpa only [Set.preimage_inter, PieceCoh] using h1
  -- the whole base is the union of the cumulative pieces
  have huniv : (⋃ i : ι, Cov i) = Set.univ := by
    have hQB : (⋃ i : ι, Q i) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      refine Set.mem_iUnion.mpr ⟨Z.indexAt x, ?_⟩
      simp only [Q, Set.mem_iUnion] at *
      exact ⟨Z.indexAt x, le_rfl, Z.mem_baseSet_at x⟩
    have h1 : (⋃ i : ι, Cov i) = Z.proj ⁻¹' (⋃ i : ι, Q i) := (Set.preimage_iUnion).symm
    rw [h1, hQB, Set.preimage_univ]
  -- the transfinite union step over the whole index set
  have hfin := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf (zeroComplement Z) Cov
    hCovopen hCovmono m (fun i j hj => key i j hj)
  have hsub : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
      (zeroComplement Z) Set.univ m) := huniv ▸ hfin m le_rfl
  exact subsingleton_pdCoh_of_subsingleton_pdCohSub_univ (zeroComplement Z) m hsub

end

end Work.Thom

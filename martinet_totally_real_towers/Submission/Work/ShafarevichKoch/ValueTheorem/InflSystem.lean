import Mathlib
import Submission.Work.ShafarevichKoch.ValueTheorem.Basic
import Submission.Work.ShafarevichKoch.exists_H2Infl_with_kernel
import Submission.Work.ShafarevichKoch.exists_openNormal_H2_lift
import Submission.Work.ConCohomology.Functoriality

/-!
# `Work.ShafarevichKoch.ValueTheorem.InflSystem` -- the colimit system of `H²(Γ,𝔽₂)`

**Namespace** `Work.ShafarevichKoch`; module `Submission.Work.ShafarevichKoch.ValueTheorem.InflSystem`.

For a compact totally disconnected group `Γ` the continuous cohomology `H²(Γ,𝔽₂)` is the filtered
colimit of the finite levels `H²(Γ ⧸ U, 𝔽₂)` along the **inflation** maps.  This module packages the
system:

* `H2InflTwo U : H²(Γ ⧸ U, 𝔽₂) →+ H²(Γ,𝔽₂)`, the inflation with the canonical trivial-action
  compatibility, and the covering property `exists_openNormal_H2InflTwo_mem_range` (from
  `Work.ShafarevichKoch.exists_openNormal_H2_lift`);
* **monotonicity** `H2InflTwo_range_mono`: for open normal subgroups `U' ≤ U` the range at the
  *finer* level is *larger* -- the composition law of the colimit system, and the reason its ranges
  are *directed*;
* `H2InflTwo_range_directed` and `exists_openNormal_H2InflTwo_mem_range_finset`: every *finite* set
  of classes of `H²(Γ,𝔽₂)` is visible at one level;
* **`natCard_contH2_le_of_range_bound` / `contH2DimLe_of_range_finrank`**: a uniform bound on the
  cardinalities of the *level ranges* bounds `H²(Γ,𝔽₂)`.  The bound is needed on the ranges and not
  on the levels: the inflation `H²(Γ ⧸ Φ(Γ)) → H²(Γ)` is not injective (for `Γ = ℤ₂` the Frattini
  level is `𝔽₂` with `H²(𝔽₂,𝔽₂) = 𝔽₂` while `H²(ℤ₂,𝔽₂) = 0`), so the levels alone do not bound
  `H²_cont` -- and they are not bounded in the applications.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.ShafarevichKoch

open Work.ConCohomology

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## The canonical inflation -/

/-- The compatibility of the trivial `Γ`-action and the trivial `Γ ⧸ U`-action on `𝔽₂`: both are
the unique action (`Work.ShafarevichKoch.smul_zmodTwo_eq`). -/
theorem zmodTwo_hcomp (U : OpenNormalSubgroup Γ) :
    ∀ (σ : Γ) (m : ZMod 2), σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m :=
  fun σ m => (smul_zmodTwo_eq σ m).trans
    (smul_zmodTwo_eq (QuotientGroup.mk' U.toSubgroup σ) m).symm

/-- **The inflation** `H²(Γ ⧸ U, 𝔽₂) →+ H²(Γ, 𝔽₂)` with the canonical trivial actions. -/
noncomputable def H2InflTwo (U : OpenNormalSubgroup Γ) :
    H2 (Γ ⧸ U.toSubgroup) (ZMod 2) →+ H2 Γ (ZMod 2) :=
  H2Infl U (zmodTwo_hcomp U)

@[simp] theorem H2InflTwo_mk (U : OpenNormalSubgroup Γ) (z : Z2 (Γ ⧸ U.toSubgroup) (ZMod 2)) :
    H2InflTwo U (H2.mk z) = H2.mk (Z2Infl U (zmodTwo_hcomp U) z) := rfl

/-- The covering half of the colimit description: every class of `H²(Γ,𝔽₂)` is the inflation of a
class of a finite level. -/
theorem exists_openNormal_H2InflTwo_mem_range [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ] (x : H2 Γ (ZMod 2)) :
    ∃ U : OpenNormalSubgroup Γ, x ∈ (H2InflTwo U).range := by
  obtain ⟨U, y, hy⟩ := exists_openNormal_H2_lift x
  exact ⟨U, y, hy⟩

/-! ## Monotonicity: the composition law of the inflation system -/

/-- **The inflation from a coarser level factors through the inflation from a finer one.**  For open
normal `U' ≤ U` (so that `Γ ⧸ U' ↠ Γ ⧸ U`) the range of `H2InflTwo U` is contained in the range of
`H2InflTwo U'`. -/
theorem H2InflTwo_range_mono {U U' : OpenNormalSubgroup Γ} (h : U'.toSubgroup ≤ U.toSubgroup) :
    (H2InflTwo U).range ≤ (H2InflTwo U').range := by
  classical
  haveI : DiscreteTopology (Γ ⧸ U'.toSubgroup) := QuotientGroup.discreteTopology U'.isOpen'
  let π : Γ ⧸ U'.toSubgroup →* Γ ⧸ U.toSubgroup :=
    QuotientGroup.map U'.toSubgroup U.toSubgroup (MonoidHom.id Γ) (by simpa using h)
  have hπ : ∀ σ : Γ, π (QuotientGroup.mk' U'.toSubgroup σ) = QuotientGroup.mk' U.toSubgroup σ :=
    fun σ => QuotientGroup.map_mk' U'.toSubgroup U.toSubgroup (MonoidHom.id Γ) _ σ
  have hcont : Continuous π := continuous_of_discreteTopology
  have hcomp : ∀ (a : Γ ⧸ U'.toSubgroup) (m : ZMod 2), a • m = π a • m :=
    fun a m => (smul_zmodTwo_eq a m).trans (smul_zmodTwo_eq (π a) m).symm
  rintro x ⟨y, rfl⟩
  obtain ⟨z, rfl⟩ :=
    QuotientAddGroup.mk'_surjective (B2' (Γ ⧸ U.toSubgroup) (ZMod 2)) y
  refine ⟨H2Res π hcont hcomp (H2.mk z), ?_⟩
  change H2InflTwo U' (H2Res π hcont hcomp (H2.mk z)) = H2InflTwo U (H2.mk z)
  simp only [H2InflTwo_mk, H2Res_mk]
  have key : (Z2Infl U' (zmodTwo_hcomp U') (Z2Res π hcont hcomp z) : Z2 Γ (ZMod 2))
      = Z2Infl U (zmodTwo_hcomp U) z := by
    refine Subtype.ext ?_
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    simp only [Z2Infl_coe, cochain2Infl_apply, Z2Res_coe, cochain2Res_apply, hπ σ, hπ τ]
  rw [key]

/-- **The family of level ranges is directed**: any two are contained in the range of a common
finer level. -/
theorem H2InflTwo_range_directed (U U' : OpenNormalSubgroup Γ) :
    ∃ U'' : OpenNormalSubgroup Γ,
      (H2InflTwo U).range ≤ (H2InflTwo U'').range ∧
        (H2InflTwo U').range ≤ (H2InflTwo U'').range := by
  have hopen : IsOpen ((U.toSubgroup ⊓ U'.toSubgroup : Subgroup Γ) : Set Γ) := by
    have hset : ((U.toSubgroup ⊓ U'.toSubgroup : Subgroup Γ) : Set Γ) =
        (U.toSubgroup : Set Γ) ∩ (U'.toSubgroup : Set Γ) := rfl
    rw [hset]
    exact U.isOpen'.inter U'.isOpen'
  exact ⟨⟨⟨U.toSubgroup ⊓ U'.toSubgroup, hopen⟩, inferInstance⟩,
    H2InflTwo_range_mono inf_le_left, H2InflTwo_range_mono inf_le_right⟩

/-- **Every finite set of classes of `H²(Γ,𝔽₂)` is visible at a single finite level.** -/
theorem exists_openNormal_H2InflTwo_mem_range_finset [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ] (s : Finset (H2 Γ (ZMod 2))) :
    ∃ U : OpenNormalSubgroup Γ, ∀ x ∈ s, x ∈ (H2InflTwo U).range := by
  classical
  induction s using Finset.induction with
  | empty =>
      obtain ⟨U₀, -⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (U := (Set.univ : Set Γ)) isOpen_univ trivial
      exact ⟨U₀, by simp⟩
  | insert a s _ ih =>
      obtain ⟨U, hU⟩ := ih
      obtain ⟨U', hU'⟩ := exists_openNormal_H2InflTwo_mem_range a
      obtain ⟨U'', h1, h2⟩ := H2InflTwo_range_directed U U'
      refine ⟨U'', fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h2 hU'
      · exact h1 (hU x hx)

/-! ## The collapse of the colimit for finite `H²`

If `H²(Γ,𝔽₂)` is finite, the directed covering family of level ranges has a *maximal* member: the
whole of `H²(Γ,𝔽₂)` is realised at a single finite level.  This is the form in which the
*finite-level* transgression computations (`Work.HopfGaschutz.tgClass_surjective`,
`card_conjInvariantZ1`) can be consumed for a pro-`2` group. -/

/-- **If `H²(Γ,𝔽₂)` is finite, it is realised at a single finite level.** -/
theorem exists_openNormal_H2InflTwo_range_eq_top [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ] (hfin : Finite (H2 Γ (ZMod 2))) :
    ∃ U : OpenNormalSubgroup Γ, (H2InflTwo U).range = ⊤ := by
  classical
  haveI : Fintype (H2 Γ (ZMod 2)) := Fintype.ofFinite _
  obtain ⟨U, hU⟩ := exists_openNormal_H2InflTwo_mem_range_finset
    (Finset.univ : Finset (H2 Γ (ZMod 2)))
  exact ⟨U, (AddSubgroup.eq_top_iff' _).mpr fun x => hU x (Finset.mem_univ x)⟩

/-! ## Finiteness of the level ranges -/

/-- Each level range is finite: it is the image of the finite group `H²(Γ ⧸ U, 𝔽₂)`. -/
theorem finite_range_H2InflTwo [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (U : OpenNormalSubgroup Γ) : Finite ↥((H2InflTwo U).range) := by
  haveI : Finite (H2 (Γ ⧸ U.toSubgroup) (ZMod 2)) :=
    finite_contH2_of_finite (Γ ⧸ U.toSubgroup)
  exact Finite.of_surjective
    (fun y : H2 (Γ ⧸ U.toSubgroup) (ZMod 2) =>
      (⟨H2InflTwo U y, ⟨y, rfl⟩⟩ : ↥((H2InflTwo U).range)))
    (fun x => by obtain ⟨y, hy⟩ := x.2; exact ⟨y, Subtype.ext hy⟩)

/-- A Finset is contained in the range of one level. -/
theorem finset_subset_range_of_finite [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ] (s : Finset (H2 Γ (ZMod 2))) :
    ∃ U : OpenNormalSubgroup Γ, (s : Set (H2 Γ (ZMod 2))) ⊆ (H2InflTwo U).range := by
  obtain ⟨U, hU⟩ := exists_openNormal_H2InflTwo_mem_range_finset s
  exact ⟨U, fun x hx => hU x (Finset.mem_coe.mp hx)⟩

/-- **`H²(Γ,𝔽₂)` is finite and bounded by the level ranges.**  A uniform bound `N` on the
cardinalities of the images of the finite levels bounds the whole of `H²(Γ,𝔽₂)` by `N`. -/
theorem finite_and_natCard_contH2_le_of_range_bound [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ] {N : ℕ}
    (h : ∀ U : OpenNormalSubgroup Γ, Nat.card ((H2InflTwo U).range) ≤ N) :
    Finite (H2 Γ (ZMod 2)) ∧ Nat.card (H2 Γ (ZMod 2)) ≤ N := by
  classical
  have hfin : Finite (H2 Γ (ZMod 2)) := by
    by_contra hnf
    haveI : Infinite (H2 Γ (ZMod 2)) := not_finite_iff_infinite.mp hnf
    let e : ℕ ↪ H2 Γ (ZMod 2) := Infinite.natEmbedding _
    let s : Finset (H2 Γ (ZMod 2)) := (Finset.range (N + 1)).map e
    have hscard : s.card = N + 1 := by
      simp [s, Finset.card_map]
    obtain ⟨U, hU⟩ := finset_subset_range_of_finite s
    haveI := finite_range_H2InflTwo U
    have hinj : Function.Injective
        (fun x : ↥s => (⟨(x : H2 Γ (ZMod 2)), hU x.2⟩ : ↥((H2InflTwo U).range))) :=
      fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
    have hle : Nat.card ↥s ≤ Nat.card ↥((H2InflTwo U).range) :=
      Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_finsetCard s] at hle
    have := h U
    omega
  refine ⟨hfin, ?_⟩
  haveI := hfin
  haveI : Fintype (H2 Γ (ZMod 2)) := Fintype.ofFinite _
  obtain ⟨U, hU⟩ := finset_subset_range_of_finite (Finset.univ : Finset (H2 Γ (ZMod 2)))
  haveI hfr := finite_range_H2InflTwo U
  have hinj : Function.Injective
      (fun x : H2 Γ (ZMod 2) => (⟨x, hU (Finset.mem_univ x)⟩ : ↥((H2InflTwo U).range))) :=
    fun a b hab => by simpa using congrArg Subtype.val hab
  exact le_trans (Nat.card_le_card_of_injective _ hinj) (h U)

/-- **The dimension bound for `H²(Γ,𝔽₂)` from a uniform bound on the level ranges.** -/
theorem contH2DimLe_of_range_finrank [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ] {r : ℕ}
    (h : ∀ U : OpenNormalSubgroup Γ, ∃ k ≤ r, Nat.card ((H2InflTwo U).range) = 2 ^ k) :
    Work.RelatorRank.ContH2DimLe Γ r := by
  classical
  obtain ⟨hfin, hb⟩ := finite_and_natCard_contH2_le_of_range_bound (N := 2 ^ r) (fun U => by
    obtain ⟨k, hk, hk'⟩ := h U
    rw [hk']
    exact Nat.pow_le_pow_right (by norm_num) hk)
  haveI := hfin
  haveI : Fintype (H2 Γ (ZMod 2)) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod 2) (H2 Γ (ZMod 2)) := Module.Finite.of_finite
  have hcard : Nat.card (H2 Γ (ZMod 2))
      = 2 ^ Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) := natCard_eq_two_pow_finrank _
  refine ⟨Module.finrank (ZMod 2) (H2 Γ (ZMod 2)), ?_, hcard⟩
  rw [hcard] at hb
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hb

end Work.ShafarevichKoch

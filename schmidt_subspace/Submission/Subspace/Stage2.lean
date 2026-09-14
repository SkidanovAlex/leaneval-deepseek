import Mathlib
import Submission.Subspace.StageF
import Submission.Commons.Analysis.Normed.finite_bounded_int_vectors

/-!
# Stage 2: from the failure of the subspace theorem to a general-position family

This file assembles the "falsity ⇒ approximation domain" half of the proof of Schmidt's
subspace theorem.  Assuming that for a fixed `ε > 0` the affine subspace theorem fails
(i.e. the set of *small* nonzero integer points is not contained in any finite union of
proper `ℚ`-subspaces), we construct

* an infinite set `Z ⊆ ℤ^σ` of small points, all of whose linear-form values are nonzero,
* which is in *general position* (every subset of at most `|σ|` points is `ℚ`-independent),
* together with an exponent vector `c : σ → ℝ` with `∑ c_i < 0` such that
  `‖Lᵢ(x)‖ ≤ ‖x‖^{cᵢ}` for all `x ∈ Z`, `i : σ`.

The construction combines
* `formZero_cover` (Stage F): solutions where some form vanishes are already covered,
* the general-position extraction (commons): an infinite set that is not finitely covered
  by proper subspaces contains an infinite general-position subset,
* the uniform exponent-vector extraction (commons): the pigeonhole step.

The single remaining deep input of the whole development ("rank descent") is the statement
that no such general-position family exists; see `Submission/Work/BLUEPRINT.md`.
-/

open scoped BigOperators

namespace Submission.Subspace

/-- The canonical map `ℤ^σ → ℚ^σ`. -/
abbrev intCastVec {σ : Type*} : (σ → ℤ) → (σ → ℚ) := fun x i => (x i : ℚ)

lemma intCastVec_injective {σ : Type*} : Function.Injective (intCastVec (σ := σ)) := by
  intro x y hxy
  funext i
  have h := congrFun hxy i
  simp only [intCastVec] at h
  exact_mod_cast h

section Stage2

variable {σ : Type*} [Fintype σ]

/-- Nonzero integer points satisfying the strict smallness hypothesis whose linear-form
values are all nonzero. -/
def SmallNonzero (L : σ → σ → ℂ) (ε : ℝ) : Set (σ → ℤ) :=
  {x | x ≠ 0 ∧ Small L ε x ∧ ∀ i : σ, (∑ j : σ, L i j * (x j : ℂ) : ℂ) ≠ 0}

/-- The image of `SmallNonzero L ε` in `ℚ^σ` under the canonical embedding `ℤ^σ → ℚ^σ`. -/
def SmallNonzeroRat (L : σ → σ → ℂ) (ε : ℝ) : Set (σ → ℚ) :=
  {v | ∃ x : σ → ℤ, x ∈ SmallNonzero L ε ∧ intCastVec x = v}

lemma mem_SmallNonzeroRat_iff (L : σ → σ → ℂ) (ε : ℝ) (v : σ → ℚ) :
    v ∈ SmallNonzeroRat L ε ↔ ∃ x : σ → ℤ, x ∈ SmallNonzero L ε ∧ intCastVec x = v :=
  Iff.rfl

/-- **Place identity.**  For coefficients lying in a number field `K ⊆ ℂ`, the infinite place
of `K` induced by the identity embedding evaluates the `K`-linear form `∑ⱼ aᵢⱼ xⱼ` as the
complex modulus of the corresponding `ℂ`-linear form. -/
lemma place_val_eq (K : IntermediateField ℚ ℂ) [NumberField K] (L : σ → σ → ℂ)
    (hLK : ∀ i j, L i j ∈ K) (x : σ → ℤ) (i : σ) :
    (NumberField.InfinitePlace.mk (IntermediateField.val K)).val
        (∑ j : σ, (⟨L i j, hLK i j⟩ : K) * (x j : K))
      = ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ := by
  rw [show (NumberField.InfinitePlace.mk (IntermediateField.val K)).val
        (∑ j : σ, (⟨L i j, hLK i j⟩ : K) * (x j : K))
      = (NumberField.InfinitePlace.mk (IntermediateField.val K))
        (∑ j : σ, (⟨L i j, hLK i j⟩ : K) * (x j : K)) from rfl]
  rw [NumberField.InfinitePlace.apply]
  congr 1
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp [map_intCast]

/-- The negation of the affine subspace theorem for a fixed `ε`, made explicit. -/
def NotCovered (L : σ → σ → ℂ) (ε : ℝ) : Prop :=
  ¬ ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
    ∀ x : σ → ℤ, x ≠ 0 → Small L ε x → ∃ W ∈ T, intCastVec x ∈ W

/-- **Extraction of a small point avoiding a prescribed finite family.**  If the subspace
theorem fails for `ε`, then for every finite family `T` of proper `ℚ`-subspaces there is a
small nonzero integer point with all form values nonzero lying outside `⋃ T`.

The proof adjoins the `|σ|` fixed hyperplanes `{Lᵢ = 0}` (which cover all solutions with a
vanishing form value, `formZero_cover`) and applies the failure hypothesis. -/
theorem exists_smallNonzero_notMem (L : σ → σ → ℂ) (ε : ℝ) (ind : LinearIndependent ℂ L)
    (hnc : NotCovered (σ := σ) L ε)
    (T : Set (Submodule ℚ (σ → ℚ))) (hTfin : T.Finite) (hTprop : ∀ W ∈ T, W ≠ ⊤) :
    ∃ x : σ → ℤ, x ∈ SmallNonzero L ε ∧ ∀ W ∈ T, intCastVec x ∉ W := by
  classical
  obtain ⟨T₀, hT₀fin, hT₀prop, hT₀cov⟩ := formZero_cover L ind
  have hfin : (T ∪ T₀).Finite := hTfin.union hT₀fin
  have hprop : ∀ W ∈ T ∪ T₀, W ≠ ⊤ := by
    intro W hW
    rcases hW with hW | hW
    · exact hTprop W hW
    · exact hT₀prop W hW
  by_contra hcon
  push Not at hcon
  apply hnc
  refine ⟨T ∪ T₀, hfin, hprop, ?_⟩
  intro x hx0 hx
  by_cases hz : ∀ i : σ, (∑ j : σ, L i j * (x j : ℂ) : ℂ) ≠ 0
  · rcases hcon x ⟨hx0, hx, hz⟩ with ⟨W, hW, hxW⟩
    exact ⟨W, Set.mem_union_left _ hW, hxW⟩
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    obtain ⟨W, hW, hxW⟩ := hT₀cov x ⟨i, hi⟩
    exact ⟨W, Set.mem_union_right _ hW, hxW⟩

/-- The set `SmallNonzeroRat L ε` cannot be covered by finitely many proper
`ℚ`-subspaces, provided the subspace theorem fails for `ε`. -/
theorem not_coverable_smallNonzeroRat (L : σ → σ → ℂ) (ε : ℝ) (ind : LinearIndependent ℂ L)
    (hnc : NotCovered (σ := σ) L ε) :
    ¬ ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ v ∈ SmallNonzeroRat L ε, ∃ W ∈ T, v ∈ W := by
  rintro ⟨T, hTfin, hTprop, hcov⟩
  obtain ⟨x, hxmem, hxout⟩ := exists_smallNonzero_notMem L ε ind hnc T hTfin hTprop
  obtain ⟨W, hW, hxW⟩ := hcov (intCastVec x) ⟨x, hxmem, rfl⟩
  exact hxout W hW hxW

/-- `SmallNonzeroRat L ε` is infinite when the subspace theorem fails for `ε` and
`|σ| ≥ 2`. -/
theorem smallNonzeroRat_infinite (hσ : 2 ≤ Fintype.card σ) (L : σ → σ → ℂ) (ε : ℝ)
    (ind : LinearIndependent ℂ L) (hnc : NotCovered (σ := σ) L ε) :
    (SmallNonzeroRat L ε).Infinite := by
  classical
  by_contra hinf
  rw [Set.not_infinite] at hinf
  apply not_coverable_smallNonzeroRat L ε ind hnc
  refine ⟨(fun v => Submodule.span ℚ ({v} : Set (σ → ℚ))) '' SmallNonzeroRat L ε,
    hinf.image _, ?_, ?_⟩
  · rintro W ⟨v, hv, rfl⟩
    exact span_singleton_ne_top_of_two_le_card hσ v
  · intro v hv
    exact ⟨Submodule.span ℚ ({v} : Set (σ → ℚ)), ⟨v, hv, rfl⟩, Submodule.subset_span (by simp)⟩

/-- `SmallNonzero` is infinite when the subspace theorem fails and `|σ| ≥ 2` (the canonical
embedding `ℤ^σ → ℚ^σ` is injective). -/
theorem smallNonzero_infinite (hσ : 2 ≤ Fintype.card σ) (L : σ → σ → ℂ) (ε : ℝ)
    (ind : LinearIndependent ℂ L) (hnc : NotCovered (σ := σ) L ε) :
    (SmallNonzero L ε).Infinite := by
  classical
  by_contra hinf
  rw [Set.not_infinite] at hinf
  apply smallNonzeroRat_infinite hσ L ε ind hnc
  have himg : (SmallNonzeroRat L ε : Set (σ → ℚ)) = intCastVec '' SmallNonzero L ε := by
    ext v
    constructor
    · rintro ⟨x, hx, hxv⟩
      exact ⟨x, hx, hxv⟩
    · rintro ⟨x, hx, hxv⟩
      exact ⟨x, hx, hxv⟩
  rw [himg]
  exact hinf.image _

/-- General position for a set of integer points: every finite subset of size at most
`|σ|` is `ℚ`-linearly independent. -/
def GenPos (Y : Set (σ → ℤ)) : Prop :=
  ∀ T : Finset (σ → ℤ), (↑T : Set (σ → ℤ)) ⊆ Y → T.card ≤ Fintype.card σ →
    LinearIndependent ℚ (fun x : T => fun j : σ => (((x : σ → ℤ) j : ℤ) : ℚ))

/-- **Transfer of general position from `ℚ^σ` to `ℤ^σ`.**  An infinite general-position
subset of `SmallNonzeroRat L ε` pulls back to an infinite general-position subset of
`SmallNonzero L ε`. -/
theorem genPosInt_transfer (L : σ → σ → ℂ) (ε : ℝ) (Y : Set (σ → ℚ))
    (hYsub : Y ⊆ SmallNonzeroRat L ε) (hYinf : Y.Infinite)
    (hgp : ∀ T : Finset (σ → ℚ), (↑T : Set (σ → ℚ)) ⊆ Y → T.card ≤ Fintype.card σ →
      LinearIndepOn ℚ id (↑T : Set (σ → ℚ))) :
    ∃ Z : Set (σ → ℤ), Z ⊆ SmallNonzero L ε ∧ Z.Infinite ∧ GenPos Z := by
  classical
  have hcast_inj : Function.Injective (intCastVec (σ := σ)) := intCastVec_injective
  let Z : Set (σ → ℤ) := {x | intCastVec x ∈ Y}
  have hZmem : ∀ x : σ → ℤ, x ∈ Z ↔ intCastVec x ∈ Y := fun x => Iff.rfl
  have hZne : Z ⊆ SmallNonzero L ε := by
    intro x hx
    rw [hZmem] at hx
    rcases (mem_SmallNonzeroRat_iff L ε (intCastVec x)).mp (hYsub hx) with ⟨x', hx'mem, hx'eq⟩
    rw [← hcast_inj hx'eq]
    exact hx'mem
  have himg : (intCastVec '' Z : Set (σ → ℚ)) = Y := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hZmem x).mp hx
    · intro hv
      rcases (mem_SmallNonzeroRat_iff L ε v).mp (hYsub hv) with ⟨x, hxmem, hxeq⟩
      refine ⟨x, ?_, hxeq⟩
      rw [hZmem, hxeq]
      exact hv
  have hZinf : Z.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    rw [← himg] at hYinf
    exact hYinf (hfin.image _)
  refine ⟨Z, hZne, hZinf, ?_⟩
  intro T hTsub hTcard
  set T' : Finset (σ → ℚ) := T.image intCastVec with hT'def
  have hT'card : T'.card = T.card := Finset.card_image_of_injective _ hcast_inj
  have hT'sub : (↑T' : Set (σ → ℚ)) ⊆ Y := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_image] at hv
    rcases hv with ⟨x, hx, rfl⟩
    exact hTsub (Finset.mem_coe.mpr hx)
  have hli : LinearIndependent ℚ (fun v : (↑T' : Set (σ → ℚ)) => (v : σ → ℚ)) :=
    (hgp T' hT'sub (by rw [hT'card]; exact hTcard)).linearIndependent
  let F : T → (↑T' : Set (σ → ℚ)) := fun x => ⟨intCastVec (x : σ → ℤ), by
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨(x : σ → ℤ), Finset.mem_coe.mp x.2, rfl⟩⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    exact hcast_inj (Subtype.ext_iff.mp hxy)
  have hcomp := hli.comp F hF
  simpa [Function.comp_def, F, intCastVec] using hcomp

end Stage2

end Submission.Subspace

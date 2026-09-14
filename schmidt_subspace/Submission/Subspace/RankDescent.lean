import Mathlib
import Submission.Subspace.Stage2
import Submission.Commons.LinearAlgebra.GeneralPosition.not_finite_cover_of_genPos

/-!
# The deep input: rank descent

The whole remaining mathematical content of Schmidt's subspace theorem is isolated here as a
single statement, `RankDescent`.  It is the "rank descent" / "Roth machinery" heart of the
proof: an infinite family of small solutions *in general position* cannot exist.

Since `ℚ`-linear dependence of `|σ|` points of `ℚ^σ` is exactly "lying in a hyperplane"
through the origin, the general-position hypothesis says that no `|σ|` of the points lie in a
common hyperplane; the rank-descent theorem (Schmidt 1972; see
`Submission/Work/BLUEPRINT.md` and arXiv:2502.00731 §4) asserts that the approximation domain
`{x : |Lᵢ(x)| ≤ ‖x‖^{cᵢ}}` has rank `< |σ|` for all but finitely many solutions, whence all
solutions lie in a finite union of proper subspaces.

This statement is *equivalent* to the affine subspace theorem
(`RankDescent → SubspaceTheoremSubspaces`, below, and conversely).
-/

open scoped BigOperators

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ]

/-- **Rank descent (the deep input).**  For every exponent vector `c` with negative
coordinate sum there is no infinite set of nonzero integer points in general position, with all
linear-form values nonzero, on which all the linear forms are bounded by `‖x‖^{cᵢ}`.

The extra hypothesis "all form values are nonzero" is harmless (it is provided for free by
Stage 2, which removes the solutions where some `Lᵢ` vanishes using `formZero_cover`) and is
the form in which the classical rank-descent argument (survey arXiv:2502.00731 §4) is run. -/
def RankDescent (L : σ → σ → ℂ) : Prop :=
  ∀ c : σ → ℝ, (∑ i : σ, c i < 0) →
    ¬ ∃ Y : Set (σ → ℤ), Y.Infinite ∧ GenPos Y ∧
      (∀ x ∈ Y, ∀ i : σ, (∑ j : σ, L i j * (x j : ℂ) : ℂ) ≠ 0) ∧
      ∀ x ∈ Y, ∀ i : σ, ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ ≤ ‖x‖ ^ (c i)

/-- **Stage 2, stated as a single implication.**  If the affine subspace theorem fails for
`ε`, then there is an exponent vector `c` with `∑ cᵢ < 0` and an infinite general-position
family of small points on which all forms are bounded by `‖x‖^{cᵢ}`.

This is proved by `Stage2.smallNonzeroRat_infinite` + the general-position extraction +
the uniform exponent-vector extraction; the final assembly lives in
`Submission/Subspace/Stage2Assembly.lean`. -/
def Stage2Output (L : σ → σ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → NotCovered (σ := σ) L ε →
    ∃ c : σ → ℝ, (∑ i : σ, c i < 0) ∧ ∃ Z : Set (σ → ℤ),
      Z ⊆ SmallNonzero L ε ∧ Z.Infinite ∧ GenPos Z ∧
      ∀ x ∈ Z, ∀ i : σ, ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ ≤ ‖x‖ ^ (c i)

/-- **The deep input implies the affine subspace theorem.**  This is the "cheap" direction of
the reduction: the rank-descent statement contradicts the existence of the general-position
family produced by Stage 2. -/
theorem subspaces_of_rankDescent (L : σ → σ → ℂ) (hRD : RankDescent (σ := σ) L)
    (hStage2 : Stage2Output (σ := σ) L) :
    SubspaceTheoremSubspaces σ L := by
  intro ε hε
  by_contra hnc
  obtain ⟨c, hc, Z, hZsub, hZinf, hZgp, hZb⟩ := hStage2 ε hε hnc
  exact hRD c hc ⟨Z, hZinf, hZgp, fun x hx => (hZsub hx).2.2, hZb⟩

/-- `GenPos` for integer points transfers to general position (for the identity family) of the
image in `ℚ^σ`. -/
lemma genPos_image (Y : Set (σ → ℤ)) (h : GenPos Y) :
    ∀ T' : Finset (σ → ℚ), (↑T' : Set (σ → ℚ)) ⊆ intCastVec '' Y →
      T'.card ≤ Module.finrank ℚ (σ → ℚ) →
        LinearIndependent ℚ (fun v : T' => (v : σ → ℚ)) := by
  classical
  intro T' hT' hcard
  rw [Module.finrank_fintype_fun_eq_card (R := ℚ) (η := σ)] at hcard
  have hpre : ∀ v ∈ T', ∃ x : σ → ℤ, x ∈ Y ∧ intCastVec x = v := by
    intro v hv
    rcases hT' (Finset.mem_coe.mpr hv) with ⟨x, hx, hxv⟩
    exact ⟨x, hx, hxv⟩
  let F : ↥T' → (σ → ℤ) := fun v => Classical.choose (hpre v v.2)
  have hFmem : ∀ v : ↥T', F v ∈ Y := fun v => (Classical.choose_spec (hpre v v.2)).1
  have hFeq : ∀ v : ↥T', intCastVec (F v) = (v : σ → ℚ) :=
    fun v => (Classical.choose_spec (hpre v v.2)).2
  have hFinj : Function.Injective F := by
    intro v w hvw
    apply Subtype.ext
    rw [← hFeq v, ← hFeq w, hvw]
  set T : Finset (σ → ℤ) := (Finset.univ : Finset ↥T').image F with hTdef
  have hTsub : (↑T : Set (σ → ℤ)) ⊆ Y := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Finset.mem_image] at hx
    rcases hx with ⟨v, -, rfl⟩
    exact hFmem v
  have hTcard : T.card ≤ Fintype.card σ := by
    rw [hTdef, Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_coe]
    exact hcard
  have hli := h T hTsub hTcard
  let g : ↥T' → ↥T := fun v => ⟨F v, by
    rw [hTdef, Finset.mem_image]
    exact ⟨v, Finset.mem_univ v, rfl⟩⟩
  have hg : Function.Injective g := by
    intro v w hvw
    exact hFinj (congrArg (fun x : ↥T => (x : σ → ℤ)) hvw)
  have hcomp := hli.comp g hg
  have hfun : ((fun x : ↥T => fun j : σ => (((x : σ → ℤ)) j : ℚ)) ∘ g) =
      (fun v : ↥T' => (v : σ → ℚ)) := by
    funext v j
    exact congrFun (hFeq v) j
  rwa [hfun] at hcomp

/-- **Tightness of the reduction.**  The affine subspace theorem (proper-subspace form)
implies rank descent: an infinite general-position family in an approximation domain is
covered by finitely many proper subspaces, and one of them then contains `|σ|` of its points,
which would be dependent. -/
theorem rankDescent_of_subspaces (hσ : 1 ≤ Fintype.card σ) (L : σ → σ → ℂ)
    (h : SubspaceTheoremSubspaces σ L) : RankDescent (σ := σ) L := by
  classical
  intro c hc hbad
  obtain ⟨Y, hYinf, hYgp, _, hYb⟩ := hbad
  -- the points of norm `> 1` are all but finitely many
  set Y' : Set (σ → ℤ) := Y ∩ {x : σ → ℤ | 1 < ‖x‖} with hY'def
  have hY'sub : Y' ⊆ Y := Set.inter_subset_left
  have hY'inf : Y'.Infinite := by
    have hfin : ({x : σ → ℤ | ‖x‖ ≤ 1} : Set (σ → ℤ)).Finite :=
      Commons.Analysis.Normed.finite_bounded_int_vectors 1
    have hsub : Y ⊆ Y' ∪ {x : σ → ℤ | ‖x‖ ≤ 1} := by
      intro x hx
      by_cases h1 : 1 < ‖x‖
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (le_of_not_gt h1)
    by_contra hc
    rw [Set.not_infinite] at hc
    exact hYinf ((hc.union hfin).subset hsub)
  have hY'gp : GenPos Y' := fun T hT hcard => hYgp T (fun x hx => hY'sub (hT hx)) hcard
  have hY'ne : ∀ x ∈ Y', x ≠ 0 := by
    intro x hx hx0
    rw [hY'def, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    rw [hx0] at hx
    have h2 : (1 : ℝ) < ‖(0 : σ → ℤ)‖ := hx.2
    simp at h2
    linarith
  have hY'small : ∀ x ∈ Y', Small L (-(∑ i, c i) / 2) x := by
    intro x hx
    rw [hY'def, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    obtain ⟨hxY, hx1⟩ := hx
    rw [small_iff_prod,
      show -(-(∑ i, c i) / 2) = (∑ i, c i) / 2 from by ring]
    have hx0 : 0 < ‖x‖ := lt_trans zero_lt_one hx1
    have h1 : (∏ i, ‖(∑ j, L i j * (x j : ℂ) : ℂ)‖) ≤ ‖x‖ ^ (∑ i, c i) := by
      calc (∏ i, ‖(∑ j, L i j * (x j : ℂ) : ℂ)‖) ≤ ∏ i, ‖x‖ ^ (c i) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hYb x hxY i)
        _ = ‖x‖ ^ (∑ i, c i) := (Real.rpow_sum_of_pos hx0 c Finset.univ).symm
    have h2 : ‖x‖ ^ (∑ i, c i) < ‖x‖ ^ ((∑ i, c i) / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt hx1 (by linarith)
    linarith
  have hε : 0 < -(∑ i, c i) / 2 := by linarith
  obtain ⟨T, hTfin, hTprop, hTcov⟩ := h (-(∑ i, c i) / 2) hε
  refine Commons.LinearAlgebra.GeneralPosition.not_finite_cover_of_genPos
    (K := ℚ) (V := σ → ℚ) (genPos_image Y' hY'gp) ?_ ⟨hTfin.toFinset, ?_, ?_⟩
  · exact hY'inf.image intCastVec_injective.injOn
  · intro W hW
    exact hTprop W ((hTfin.mem_toFinset).mp hW)
  · intro v hv
    rcases hv with ⟨x, hx, rfl⟩
    obtain ⟨W, hW, hxW⟩ := hTcov x (hY'ne x hx) (hY'small x hx)
    exact ⟨W, (hTfin.mem_toFinset).mpr hW, hxW⟩

end Submission.Subspace

import Submission.Work.CharPrelim.weightSpace_finDim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The weight spaces span

For an arbitrary (possibly infinite-dimensional) representation `ρ : Z →* Module.End k V` of a
finite abelian group `Z` over an algebraically closed field `k` with `|Z|` invertible, the
weight spaces span `V`.  The proof restricts `ρ` to the finite-dimensional `Z`-invariant
subspace spanned by the orbit of a vector and applies the finite-dimensional case.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.CharPrelim

variable {k V Z : Type*}

/-- **The weight spaces span the whole space**: `⨆ χ, weightSpace ρ χ = ⊤` for an arbitrary
representation of a finite abelian group `Z` over an algebraically closed field `k` in which
`|Z|` is invertible. -/
theorem weightSpace_span [Field k] [IsAlgClosed k] [CommGroup Z] [Finite Z] [AddCommGroup V]
    [Module k V] (ρ : Z →* Module.End k V) (hcard : IsUnit ((Nat.card Z : ℕ) : k)) :
    (⨆ (χ : Z →* kˣ), weightSpace ρ χ) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr (fun v => ?_)
  set U : Submodule k V := Submodule.span k (Set.range fun z : Z => ρ z v) with hU
  have hUfg : U.FG := Submodule.fg_span (Set.finite_range _)
  haveI : Module.Finite k U := Module.Finite.of_fg hUfg
  have hmaps : ∀ z' : Z, ∀ x ∈ U, ρ z' x ∈ U := by
    intro z' x hx
    have hle : U ≤ Submodule.comap (ρ z') U := by
      rw [hU, Submodule.span_le]
      rintro y ⟨z, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [← Module.End.mul_apply, ← map_mul, mul_comm z' z]
      exact Submodule.subset_span ⟨z * z', rfl⟩
    exact hle hx
  have htop : (⨆ χ : Z →* kˣ, weightSpace (restrictRep ρ U hmaps) χ) = ⊤ :=
    weightSpace_finDim (restrictRep ρ U hmaps) hcard
  have hspan : U ≤ ⨆ χ : Z →* kˣ, weightSpace ρ χ := by
    calc U = Submodule.map U.subtype ⊤ := (Submodule.map_subtype_top U).symm
      _ = Submodule.map U.subtype (⨆ χ : Z →* kˣ, weightSpace (restrictRep ρ U hmaps) χ) := by
            rw [htop]
      _ = ⨆ χ : Z →* kˣ, Submodule.map U.subtype
              (weightSpace (restrictRep ρ U hmaps) χ) :=
            Submodule.map_iSup U.subtype (fun χ : Z →* kˣ =>
              weightSpace (restrictRep ρ U hmaps) χ)
      _ ≤ ⨆ χ : Z →* kˣ, weightSpace ρ χ :=
            iSup_le (fun χ =>
              le_trans (weightSpace_restrictRep_le ρ U hmaps χ) (le_iSup _ χ))
  have hvU : v ∈ U := by
    rw [hU]
    have h : (fun z : Z => ρ z v) 1 ∈ Submodule.span k (Set.range fun z : Z => ρ z v) :=
      Submodule.subset_span (Set.mem_range_self (1 : Z))
    simpa using h
  exact hspan hvU

end Work.CharPrelim

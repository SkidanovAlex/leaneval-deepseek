import Mathlib
import Submission.Work.HP.BCSDefs

/-!
# `Work.HP.BCS.sRank_map_projU_add_one_le`

For a lattice `Λ ⊆ ℝ^ι` over `ℤ` and a nonzero `u ∈ Λ`, the orthogonal projection
`projUZ u : Λ → u^⊥` drops the rank by at least one:

`sRank (Λ.map (projUZ u)) + 1 ≤ sRank Λ`.

## Proof

Consider `f := (projUZ u).comp Λ.subtype : Λ →ₗ[ℤ] ℝ^ι`, whose range is
`Λ.map (projUZ u)`.  Rank–nullity over `ℤ` (`Submodule.finrank_quotient_add_finrank`
together with `LinearMap.quotKerEquivRange`) gives

`finrank ℤ f.range + finrank ℤ f.ker = finrank ℤ Λ`,

and `u ≠ 0` lies in `f.ker`, so the line `ℤ ∙ u` — a rank-one submodule of `Λ` because
`Λ` is torsion free — is contained in `f.ker`.  Monotonicity of `finrank` then gives
`1 ≤ finrank ℤ f.ker`, which yields the claim.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.BCS

theorem sRank_map_projU_add_one_le (ι : Type) [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) [Module.Finite ℤ Λ]
    [Module.IsTorsionFree ℤ Λ] {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ) (hu0 : u ≠ 0) :
    sRank (Λ.map (projUZ u)) + 1 ≤ sRank Λ := by
  classical
  -- The projection `Λ → u^⊥`, viewed as a `ℤ`-linear map out of `Λ`.
  set f : Λ →ₗ[ℤ] EuclideanSpace ℝ ι := (projUZ u).comp Λ.subtype with hfdef
  have hrange : f.range = Λ.map (projUZ u) := by
    rw [hfdef, LinearMap.range_comp, Submodule.range_subtype]
  -- Rank–nullity for `f`.
  have hq : Module.finrank ℤ (Λ ⧸ f.ker) + Module.finrank ℤ ↥f.ker = Module.finrank ℤ Λ :=
    Submodule.finrank_quotient_add_finrank (R := ℤ) f.ker
  have hqr : Module.finrank ℤ (Λ ⧸ f.ker) = Module.finrank ℤ ↥f.range :=
    LinearEquiv.finrank_eq f.quotKerEquivRange
  have hq' : Module.finrank ℤ ↥f.range + Module.finrank ℤ ↥f.ker = Module.finrank ℤ Λ := by
    rw [← hqr]; exact hq
  -- `u` is mapped to `0` by the projection, so `ℤ ∙ u` lies in the kernel.
  have hspan : Submodule.span ℤ ({⟨u, hu⟩} : Set Λ) ≤ f.ker := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp [hfdef, projUZ_apply, projU_self_eq_zero u hu0]
  have hx0 : (⟨u, hu⟩ : Λ) ≠ 0 := by
    intro h; exact hu0 (Subtype.ext_iff.mp h)
  -- The line spanned by a nonzero element of a torsion-free module has rank one.
  have hfin1 : Module.finrank ℤ ↥(Submodule.span ℤ ({⟨u, hu⟩} : Set Λ)) = 1 := by
    have hinj : Function.Injective (LinearMap.toSpanSingleton ℤ Λ (⟨u, hu⟩ : Λ)) := by
      rw [← LinearMap.ker_eq_bot]
      exact LinearMap.ker_toSpanSingleton ℤ hx0
    have h1 := LinearMap.finrank_range_of_inj (R := ℤ) hinj
    rw [LinearMap.range_toSpanSingleton] at h1
    rw [h1]
    exact Module.finrank_self ℤ
  have h1ker : 1 ≤ Module.finrank ℤ ↥f.ker := by
    rw [← hfin1]
    exact Submodule.finrank_mono hspan
  have hkey : Module.finrank ℤ ↥f.range + 1 ≤ Module.finrank ℤ Λ := by
    calc Module.finrank ℤ ↥f.range + 1
        ≤ Module.finrank ℤ ↥f.range + Module.finrank ℤ ↥f.ker := Nat.add_le_add_left h1ker _
      _ = Module.finrank ℤ Λ := hq'
  rw [sRank, sRank, ← hrange]
  exact hkey

end Work.HP.BCS

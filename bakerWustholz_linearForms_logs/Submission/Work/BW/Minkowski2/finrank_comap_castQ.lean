import Mathlib
import Submission.Work.BW.Minkowski2.adapted_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ℤ`-rank of the integer points of a `ℚ`-subspace of `ℚⁿ`

For a `ℚ`-subspace `V ⊆ ℚⁿ`, the set `ℤⁿ ∩ V` of integer points of `V` is a `ℤ`-submodule of
`ℤⁿ` (namely `Submodule.comap (castQ n) (V.restrictScalars ℤ)`), and the main result here is
that its `ℤ`-rank equals `dim_ℚ V`.

The proof rests on two facts:
* every rational vector is a positive rational multiple of an integer vector
  (`exists_nat_smul_castQ`), so the integer points of `V` span `V` over `ℚ`;
* for a finite free `ℤ`-submodule `p` of a `ℚ`-module, `finrank ℚ (span ℚ p) = finrank ℤ p`
  (`Submodule.finrank_span_eq_finrank`), together with the fact that `castQ n` restricts to an
  isomorphism `ℤⁿ ∩ V ≃ V ∩ ℤⁿ` onto its image.
-/

namespace Work.BW.Minkowski2

set_option linter.style.haveILetI false

open Module

variable {n : ℕ}

/-- **Clearing denominators.** Every vector of `ℚⁿ` is a positive rational multiple of an integer
vector: there is `m > 0` and `x : Fin n → ℤ` with `castQ n x = m • v`. -/
theorem exists_nat_smul_castQ (v : Fin n → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ x : Fin n → ℤ, castQ n x = (m : ℚ) • v := by
  classical
  refine ⟨∏ i, (v i).den, Finset.prod_pos (fun i _ => (v i).den_pos),
    fun i => (v i).num * ∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ), ?_⟩
  ext i
  simp only [castQ_apply, Pi.smul_apply, smul_eq_mul]
  rw [Int.cast_mul, Int.cast_prod, Nat.cast_prod]
  simp only [Int.cast_natCast]
  have hden : ((v i).den : ℚ) ≠ 0 := by positivity
  have hnum : ((v i).num : ℚ) = v i * ((v i).den : ℚ) := by
    have h := Rat.num_div_den (v i)
    rw [div_eq_iff hden] at h
    exact h
  rw [hnum]
  rw [← Finset.prod_erase_mul Finset.univ (fun j => ((v j).den : ℚ)) (Finset.mem_univ i)]
  ring

/-- The `ℤ`-rank of the lattice of integer points of a `ℚ`-subspace `V ⊆ ℚⁿ` equals `dim_ℚ V`. -/
theorem finrank_comap_castQ {n : ℕ} (V : Submodule ℚ (Fin n → ℚ)) :
    Module.finrank ℤ (Submodule.comap (Work.BW.Minkowski2.castQ n) (V.restrictScalars ℤ)) =
      Module.finrank ℚ V := by
  classical
  have hinj : Function.Injective (castQ n) := by
    intro x y h
    ext i
    have hh := congrFun h i
    simp only [castQ_apply] at hh
    exact_mod_cast hh
  -- the integer points of `V`, viewed inside `ℤⁿ` and inside `ℚⁿ`
  let W : Submodule ℤ (Fin n → ℤ) := Submodule.comap (castQ n) (V.restrictScalars ℤ)
  let p : Submodule ℤ (Fin n → ℚ) := W.map (castQ n)
  -- `castQ n` identifies `W` with its image `p`
  have he : W ≃ₗ[ℤ] p := Submodule.equivMapOfInjective (castQ n) hinj W
  haveI : Module.Finite ℤ p := Module.Finite.equiv he
  haveI : Module.Free ℤ p := Free.of_equiv he
  -- the integer points of `V` span `V` over `ℚ`
  have hspan : Submodule.span ℚ (p : Set (Fin n → ℚ)) = V := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hy
    · intro v hv
      obtain ⟨m, _hmpos, x, hx⟩ := exists_nat_smul_castQ v
      have hxW : x ∈ W := by
        rw [Submodule.mem_comap]
        rw [hx]
        exact V.smul_mem (m : ℚ) hv
      have hxp : castQ n x ∈ p := ⟨x, hxW, rfl⟩
      have hm0 : (m : ℚ) ≠ 0 := by positivity
      have hv' : v = ((m : ℚ))⁻¹ • (castQ n x) := by
        rw [hx, smul_smul, inv_mul_cancel₀ hm0, one_smul]
      rw [hv']
      exact Submodule.smul_mem _ ((m : ℚ))⁻¹ (Submodule.subset_span hxp)
  calc Module.finrank ℤ W = Module.finrank ℤ p := LinearEquiv.finrank_eq he
    _ = Module.finrank ℚ (Submodule.span ℚ (p : Set (Fin n → ℚ))) :=
        (Submodule.finrank_span_eq_finrank ℚ p).symm
    _ = Module.finrank ℚ V := by rw [hspan]

end Work.BW.Minkowski2

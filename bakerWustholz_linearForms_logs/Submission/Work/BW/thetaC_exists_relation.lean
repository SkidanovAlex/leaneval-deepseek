import Mathlib
import Submission.Work.BW.relation_lattice_defs
import Submission.Work.BW.minimal_dependent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace Work.BW

open Complex

/-- Elementary denominateur-clearing step: a `ℚ`-linear dependence among the `ℓᵢ` yields a
nonzero **integer** relation `∑ᵢ yᵢ ℓᵢ = 0`.  Concretely, for `g : Fin m → ℚ` with
`∑ᵢ gᵢ • ℓᵢ = 0`, taking `D = ∏ᵢ (gᵢ).den` and `yᵢ = (gᵢ).num · (D / (gᵢ).den)` gives an integer
vector with `∑ᵢ yᵢ ℓᵢ = D · ∑ᵢ gᵢ ℓᵢ = 0`. -/
theorem thetaC_exists_relation {m : ℕ} (ℓ : Fin m → ℂ) (hdep : ¬ LinearIndependent ℚ ℓ) :
    ∃ y : Fin m → ℤ, y ≠ 0 ∧ thetaC ℓ y = 0 := by
  classical
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let D : ℕ := ∏ i, (g i).den
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (g i).den_pos
  let y : Fin m → ℤ := fun i => (g i).num * ((D / (g i).den : ℕ) : ℤ)
  -- `y` is (up to the common factor `D`) the rational vector `g`.
  have hkey : ∀ i, (y i : ℚ) = (D : ℚ) * g i := by
    intro i
    show (((g i).num * ((D / (g i).den : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * g i
    rw [Int.cast_mul, Int.cast_natCast]
    have hden : (g i).den ∣ D := by
      dsimp only [D]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hdiv : ((D / (g i).den : ℕ) : ℚ) = (D : ℚ) / ((g i).den : ℚ) :=
      Nat.cast_div hden (by exact_mod_cast (g i).den_nz)
    have hden0 : ((g i).den : ℚ) ≠ 0 := by exact_mod_cast (g i).den_nz
    rw [hdiv, mul_div_assoc', div_eq_iff hden0]
    rw [mul_assoc, Rat.mul_den_eq_num (g i)]
    ring
  refine ⟨y, ?_, ?_⟩
  · -- `y` is nonzero because `g` is nonzero.
    intro hy0
    have hyi : y i₀ = 0 := congrFun hy0 i₀
    have h := hkey i₀
    rw [hyi, Int.cast_zero] at h
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    exact hi₀ ((mul_eq_zero.mp h.symm).resolve_left hD0)
  · rw [thetaC]
    have hyic : ∀ i, (y i : ℂ) = (D : ℂ) * (g i : ℂ) := fun i => by
      exact_mod_cast hkey i
    calc ∑ i, (y i : ℂ) * ℓ i
        = ∑ i, ((D : ℂ) * (g i : ℂ)) * ℓ i := Finset.sum_congr rfl fun i _ => by rw [hyic i]
      _ = (D : ℂ) * ∑ i, (g i : ℂ) * ℓ i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by
            have hg' : ∑ i, (g i : ℂ) * ℓ i = 0 := by
              rw [← hg]
              exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]; simp
            rw [hg', mul_zero]

end Work.BW

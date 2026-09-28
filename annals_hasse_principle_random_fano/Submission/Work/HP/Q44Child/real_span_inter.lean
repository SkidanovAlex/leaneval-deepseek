import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Q44Child.free_dual_ne_zero

/-!
# The integral points of the real span of a primitive lattice

Let `Λ ⊆ ℤ^5` be a primitive (= saturated / pure) integral lattice.  Then the integral
vectors lying in its real span `Lℝ Λ ⊆ E5 = ℝ^5` are exactly the vectors of `Λ`.

The proof is a duality argument.  Saturation says precisely that the quotient `ℤ^5 ⧸ Λ` is
torsion free; being finitely generated it is therefore free over the PID `ℤ`
(`Module.free_of_finite_type_torsion_free'`).  If `v ∉ Λ` then the class of `v` in the
quotient is non-zero, so by `free_dual_ne_zero` there is a `ℤ`-linear functional `φ` on the
quotient with `φ v ≠ 0`; pulling it back gives a `ℤ`-linear `ψ : ℤ^5 → ℤ` with `ψ|_Λ = 0`
and `ψ v ≠ 0`.  Extending `ψ` to an `ℝ`-linear functional `Ψ` on `ℝ^5` — possible because
the standard integer basis of `ℤ^5` is also an `ℝ`-basis of `ℝ^5` — it vanishes on the whole
real span of `Λ`, contradicting `toE v ∈ Lℝ Λ`.
-/

namespace Work.HP.Q44Child

set_option linter.style.haveILetI false

noncomputable section

open Module

/-- For a primitive (= saturated) integral lattice the quotient `ℤ^5 ⧸ Λ` is torsion free:
if `r • v ∈ Λ` with `r ≠ 0`, then `v ∈ Λ`. -/
lemma isTorsionFree_quot_of_isPrimLat (Λ : Submodule ℤ (Fin 5 → ℤ))
    (h : Work.HP.IsPrimLat Λ) : Module.IsTorsionFree ℤ ((Fin 5 → ℤ) ⧸ Λ) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r m hm
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    revert hm
    refine Submodule.Quotient.induction_on Λ m ?_
    intro x hx
    rw [← Submodule.Quotient.mk_smul Λ r x, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact h x r hr hx

/-- Every `ℤ`-linear functional on `ℤ^5` extends to an `ℝ`-linear functional on `ℝ^5`,
agreeing with it on the standard lattice. -/
lemma exists_toE_linear_extension (ψ : (Fin 5 → ℤ) →ₗ[ℤ] ℤ) :
    ∃ Ψ : E5 →ₗ[ℝ] ℝ, ∀ w : Fin 5 → ℤ, Ψ (toE w) = (ψ w : ℝ) := by
  let Ψ : E5 →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i : Fin 5, x.ofLp i * (ψ (Pi.single i 1) : ℝ)
      map_add' := by
        intro a b
        simp only [WithLp.ofLp_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          RingHom.id_apply]
        exact Finset.sum_congr rfl fun i _ => by ring }
  refine ⟨Ψ, ?_⟩
  intro w
  have hΨ : Ψ (toE w) = ∑ i : Fin 5, (toE w).ofLp i * (ψ (Pi.single i 1) : ℝ) := rfl
  have h1 : ψ w = ∑ i : Fin 5, w i * ψ (Pi.single i (1 : ℤ)) := by
    conv_lhs => rw [show w = ∑ i : Fin 5, w i • (Pi.single i (1 : ℤ)) from by
      funext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp
  rw [hΨ]
  simp only [toE_ofLp]
  rw [h1]
  push_cast
  ring

theorem real_span_inter (Λ : Submodule ℤ (Fin 5 → ℤ)) (hΛs : Work.HP.IsPrimLat Λ)
    (v : Fin 5 → ℤ) (hv : Work.HP.Q44Child.toE v ∈ Work.HP.Q44Child.Lℝ Λ) : v ∈ Λ := by
  classical
  by_contra hvΛ
  haveI hTF : Module.IsTorsionFree ℤ ((Fin 5 → ℤ) ⧸ Λ) :=
    isTorsionFree_quot_of_isPrimLat Λ hΛs
  haveI hFin : Module.Finite ℤ ((Fin 5 → ℤ) ⧸ Λ) := Module.Finite.quotient ℤ Λ
  haveI hFree : Module.Free ℤ ((Fin 5 → ℤ) ⧸ Λ) := Module.free_of_finite_type_torsion_free'
  have hq : (Submodule.Quotient.mk v : (Fin 5 → ℤ) ⧸ Λ) ≠ 0 := by
    simp only [ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hvΛ
  obtain ⟨φ, hφ⟩ := free_dual_ne_zero hq
  let ψ : (Fin 5 → ℤ) →ₗ[ℤ] ℤ := φ.comp Λ.mkQ
  have hψv : ψ v ≠ 0 := by
    show φ (Λ.mkQ v) ≠ 0
    rwa [Submodule.mkQ_apply]
  obtain ⟨Ψ, hΨ⟩ := exists_toE_linear_extension ψ
  have hψzero : ∀ w ∈ Λ, ψ w = 0 := by
    intro w hw
    show φ (Λ.mkQ w) = 0
    rw [Submodule.mkQ_apply, show Submodule.Quotient.mk w = 0 from by
      rw [Submodule.Quotient.mk_eq_zero]; exact hw, map_zero]
  have hker : Lℝ Λ ≤ LinearMap.ker Ψ := by
    rw [Lℝ]
    refine Submodule.span_le.mpr ?_
    rintro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    exact LinearMap.mem_ker.mpr (by rw [hΨ w, hψzero w hw]; simp)
  have hzero : Ψ (toE v) = 0 := hker hv
  rw [hΨ v, Int.cast_eq_zero] at hzero
  exact hψv hzero

end

end Work.HP.Q44Child

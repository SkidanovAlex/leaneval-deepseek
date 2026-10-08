import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The "modulo the inner automorphism" step of the Hua argument (L4 of the lead's note)

If a subgroup `Z'` of `MulAut A(K,θ)` is the conjugate `ψ Λ ψ⁻¹` of the standard torus, then
re-coordinatising by `ψ⁻¹` turns every element of `Z'` into a standard torus element `h_λ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem mem_torus_of_conj {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {Z' : Subgroup (MulAut (SzA (GaloisField 2 m) θ))} {ψ : MulAut (SzA (GaloisField 2 m) θ)}
    (hψ : Z' = ((SzA.hLamHom θ).range).map (MulAut.conj ψ).toMonoidHom) :
    ∀ z ∈ Z', ∃ lam : (GaloisField 2 m)ˣ, ∀ x : SzA (GaloisField 2 m) θ,
      ψ⁻¹ (z (ψ x)) = SzA.hLam θ (lam : GaloisField 2 m) x := by
  intro z hz
  rw [hψ] at hz
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
  obtain ⟨lam, rfl⟩ := hw
  refine ⟨lam, fun x => ?_⟩
  rw [← hwz]
  show ψ⁻¹ (((MulAut.conj ψ) (SzA.hLamHom θ lam)) (ψ x)) = SzA.hLam θ (lam : GaloisField 2 m) x
  have h1 : ∀ y : SzA (GaloisField 2 m) θ, ψ⁻¹ (ψ y) = y := by
    intro y
    rw [← MulAut.mul_apply, inv_mul_cancel]
    rfl
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply]
  rw [h1, h1]
  rfl

end Work.ZassenhausSuzuki

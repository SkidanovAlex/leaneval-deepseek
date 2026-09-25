import Mathlib
import Submission.Commons.FieldTheory.Galois.hilbert90_cyclic

namespace Commons.FieldTheory.Galois

theorem ker_norm_le_range_of_cyclic_of_div_mem_range_norm
    {B B₁ E : Type*} [Field B] [Field B₁] [Field E]
    [Algebra B B₁] [Algebra B₁ E]
    [FiniteDimensional B B₁] [IsGalois B B₁] [FiniteDimensional B₁ E]
    (hcyc : IsCyclic (B₁ ≃ₐ[B] B₁))
    (hL : ∀ (σ : B₁ ≃ₐ[B] B₁) (x : B₁ˣ),
      Units.map σ.toRingEquiv.toMonoidHom x / x ∈
        MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁))) :
    MonoidHom.ker (Units.map (Algebra.norm B : B₁ →* B)) ≤
      MonoidHom.range (Units.map (Algebra.norm B₁ : E →* B₁)) := by
  obtain ⟨σ, hσ⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  have hu1 : Algebra.norm B (u : B₁) = 1 := by
    have h := congrArg (fun t : Bˣ => (t : B)) hu
    simpa using h
  obtain ⟨z, hz⟩ :=
    (hilbert90_cyclic (K := B) (L := B₁) σ hσ (u : B₁)).mp hu1
  have heq : u = Units.map σ.toRingEquiv.toMonoidHom z / z := by
    rw [Units.ext_iff, Units.val_div_eq_div_val, Units.coe_map]
    exact hz
  rw [heq]
  exact hL σ z

end Commons.FieldTheory.Galois

import Submission.Work.ORCoherence.Imports
import Submission.Work.ORCoherence.Retract
import Submission.Work.ORCoherence.Basic2
import Submission.Work.ORCoherence.Tensor.balanced_subsingleton_range_of_span
import Submission.Work.ORCoherence.Tensor.balanced_eq_bot_of_subsingleton
import Submission.Work.ORCoherence.Tensor.exists_complement_projection
import Submission.Work.ORCoherence.Tensor.exists_finset_span_finsupp
import Mathlib.Algebra.Module.Projective

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

universe u

/-- **Lemma 3.1 of Jaikin-Zapirain–Linton** (the form used in the proof, with the
retraction data made explicit): if `P` is a retract of a free `R`-module and `S ⊗[R] P`
is a finitely generated `S`-module, then `P` is a finitely generated `R`-module. -/
theorem finite_of_balanced_finite {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) {X : Type u} {P : Type u} [AddCommGroup P] [Module R P]
    (s : P →ₗ[R] (X →₀ R)) (π : (X →₀ R) →ₗ[R] P) (hπ : ∀ p, π (s p) = p)
    (h : Module.Finite S (Balanced f P)) : Module.Finite R P := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_span_tmul_one f P h
  set N : Submodule R P := Submodule.span R (T : Set P) with hN
  have hNfg : N.FG := by
    rw [hN]
    exact Submodule.fg_span T.finite_toSet
  have hsN : (Submodule.map s N).FG := hNfg.map s
  obtain ⟨X₀, hX₀⟩ := Tensor.exists_finset_span_finsupp X (Submodule.map s N) hsN
  obtain ⟨ρ, hρ⟩ := Tensor.exists_complement_projection (R := R) X X₀
  set ψ : P →ₗ[R] (X →₀ R) := ρ.comp s with hψ
  have hψ0 : ∀ m ∈ T, ψ m = 0 := by
    intro m hm
    have hmN : m ∈ N := Submodule.subset_span hm
    have hs : s m ∈ Submodule.map s N := Submodule.mem_map_of_mem hmN
    have hker : s m ∈ LinearMap.ker ρ := by rw [hρ]; exact hX₀ hs
    simpa [hψ, LinearMap.mem_ker] using hker
  haveI : Subsingleton (Balanced f (LinearMap.range ψ)) :=
    Tensor.balanced_subsingleton_range_of_span f ψ T hT hψ0
  have hrange : LinearMap.range ψ = ⊥ :=
    Tensor.balanced_eq_bot_of_subsingleton f hf X (LinearMap.range ψ) inferInstance
  have hψzero : ψ = 0 := LinearMap.range_eq_bot.mp hrange
  have hsmem : ∀ p : P, s p ∈ LinearMap.ker ρ := by
    intro p
    have : ψ p = 0 := by rw [hψzero]; rfl
    simpa [hψ, LinearMap.mem_ker] using this
  have hmap : Submodule.map π (LinearMap.ker ρ) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro p
    exact ⟨s p, hsmem p, hπ p⟩
  have hkerfg : (LinearMap.ker ρ).FG := by
    rw [hρ]
    refine Submodule.fg_span ?_
    rw [show {x : X →₀ R | ∃ i ∈ X₀, x = Finsupp.single i (1 : R)} =
      (fun i => Finsupp.single i (1 : R)) '' (X₀ : Set X) from by
        ext x; simp [eq_comm]]
    exact (X₀.finite_toSet).image _
  have htop : (⊤ : Submodule R P).FG := by
    rw [← hmap]
    exact hkerfg.map π
  exact Module.Finite.of_fg_top htop

end Work.ORCoherence

namespace Work.ORCoherence

universe u

/-- **Lemma 3.1 of Jaikin-Zapirain–Linton**: if `P` is a projective left `R`-module and
`S ⊗[R] P` is a finitely generated `S`-module, then `P` is a finitely generated `R`-module. -/
theorem finite_of_balanced_finite_of_projective {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) (P : ModuleCat.{u} R) [Projective P]
    (h : Module.Finite S (Balanced f P)) : Module.Finite R P := by
  obtain ⟨X, s, π, hs⟩ := projective_retract_free P
  have hπ : ∀ p : P, π.hom (s.hom p) = p := by
    intro p
    have h := congrArg (fun (u : P ⟶ P) => u.hom p) hs
    simpa using h
  exact finite_of_balanced_finite f hf s.hom π.hom hπ h

end Work.ORCoherence

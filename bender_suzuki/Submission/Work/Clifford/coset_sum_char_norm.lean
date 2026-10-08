import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

set_option linter.style.haveILetI false

open Classical
open CategoryTheory

namespace Work.Clifford

theorem coset_sum_char_norm {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] [Fintype N]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G)
    (hext : Work.Clifford.Extends N χ θ) (g : G) :
    ∑ n : N, χ (g * n) * starRingEnd ℂ (χ (g * n)) = (Nat.card N : ℂ) := by
  classical
  have hθ' := hθ
  obtain ⟨V, hVsimple, hVχ⟩ := hχ
  obtain ⟨W, hWsimple, hWθ⟩ := hθ
  have hVχ2 : Representation.character V.ρ = χ := hVχ
  haveI := hVsimple
  -- restriction of `V.character` to `N` is `θ`
  have hres : ∀ n : N, V.character (n : G) = θ n := by
    intro n
    rw [hVχ]
    exact congrFun hext n
  have hstarth : ∀ n : N, starRingEnd ℂ (θ n) = θ n⁻¹ := by
    intro n
    rw [← hWθ]
    exact star_char_eq_char_inv W n
  -- `V` is nontrivial
  haveI hVnt : Nontrivial ↥V := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    refine CategoryTheory.id_nonzero V ?_
    apply Action.hom_ext
    rw [Action.id_hom, Action.zero_hom]
    ext x
    exact hsub.elim x 0
  -- the conjugation representation of `G` on `End V`, and its restriction to `N`
  let Ad : Representation ℂ G (↥V →ₗ[ℂ] ↥V) := Representation.linHom V.ρ V.ρ
  let τ : Representation ℂ N (↥V →ₗ[ℂ] ↥V) := Ad.comp N.subtype
  let E : Submodule ℂ (↥V →ₗ[ℂ] ↥V) := τ.invariants
  let A : (↥V →ₗ[ℂ] ↥V) →ₗ[ℂ] (↥V →ₗ[ℂ] ↥V) := ∑ n : N, τ n
  have hτchar : ∀ n : N, τ.character n = θ n⁻¹ * θ n := by
    intro n
    have h1 : τ.character n = Ad.character (n : G) := rfl
    rw [h1]
    have h2 : Ad.character (n : G) = V.character ((n : G))⁻¹ * V.character (n : G) := by
      have hAdeq : Ad = Representation.linHom V.ρ V.ρ := rfl
      rw [hAdeq]
      exact Representation.char_linHom V.ρ V.ρ (n : G)
    have hcoevinv : ((n : G))⁻¹ = ((n⁻¹ : N) : G) := by simp
    rw [h2, hcoevinv, hres n, hres n⁻¹]
  have hsum1 : (∑ n : N, θ n⁻¹ * θ n) = ∑ n : N, θ n * starRingEnd ℂ (θ n) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hstarth n, mul_comm]
  have hsum2 : (∑ n : N, θ n * starRingEnd ℂ (θ n)) = (Nat.card N : ℂ) := by
    have hcf : cfInner θ θ = 1 := by
      rw [cfInner_eq_ite_of_mem_Irr hθ' hθ']; simp
    have hcard : (∑ n : N, θ n * starRingEnd ℂ (θ n))
        = (Fintype.card N : ℂ) * cfInner θ θ := by
      rw [cfInner_apply]
      field_simp
    rw [hcard, hcf, mul_one, Fintype.card_eq_nat_card]
  have hstep4 : ∑ n : N, τ.character n = (Nat.card N : ℂ) := by
    have h1 : (∑ n : N, τ.character n) = ∑ n : N, θ n⁻¹ * θ n :=
      Finset.sum_congr rfl (fun n _ => hτchar n)
    rw [h1, hsum1, hsum2]
  have hAdchar : ∀ x : G, Ad.character x = χ x * starRingEnd ℂ (χ x) := by
    intro x
    have hAdeq : Ad = Representation.linHom V.ρ V.ρ := rfl
    rw [hAdeq, Representation.char_linHom, hVχ2]
    rw [show χ x⁻¹ = starRingEnd ℂ (χ x) from by
      rw [← hVχ2]; exact (star_char_eq_char_inv V x).symm]
    rw [mul_comm]
  have hstep1 : (∑ n : N, χ (g * ↑n) * starRingEnd ℂ (χ (g * ↑n)))
      = ∑ n : N, Ad.character (g * ↑n) :=
    Finset.sum_congr rfl (fun n _ => (hAdchar (g * ↑n)).symm)
  have hstep2 : (∑ n : N, Ad.character (g * ↑n))
      = LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) (Ad g * A) := by
    have h1 : ∀ n : N,
        Ad.character (g * ↑n) = LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) (Ad g * τ n) := by
      intro n
      have h2 : Ad.character (g * ↑n)
          = LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) (Ad (g * ↑n)) := rfl
      rw [h2, map_mul, show Ad (↑n) = τ n from rfl]
    rw [Finset.sum_congr rfl (fun n _ => h1 n)]
    rw [← map_sum]
    congr 1
    show (∑ n : N, Ad g * τ n) = Ad g * (∑ n : N, τ n)
    exact (Finset.mul_sum Finset.univ (fun n : N => τ n) (Ad g)).symm
  have hstep3 : LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) A = ∑ n : N, τ.character n := by
    show LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) (∑ n : N, τ n) = ∑ n : N, τ.character n
    rw [map_sum]
    rfl
  have hfinE : Module.finrank ℂ ↥E = 1 := by
    have hcard := Representation.card_inv_mul_sum_char_eq_finrank τ
    rw [hstep4] at hcard
    have hNne : (Nat.card N : ℂ) ≠ 0 := by
      have hpos : 0 < Nat.card N := Nat.card_pos
      exact_mod_cast hpos.ne'
    rw [inv_mul_cancel₀ hNne] at hcard
    exact_mod_cast hcard.symm
  have hAdone : ∀ x : G, Ad x (1 : ↥V →ₗ[ℂ] ↥V) = 1 := by
    intro x
    have hAdeq : Ad = Representation.linHom V.ρ V.ρ := rfl
    rw [hAdeq, Representation.linHom_apply]
    ext v
    simp only [LinearMap.comp_apply, Module.End.one_eq_id, LinearMap.id_apply]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id,
      LinearMap.id_apply]
  have hone : (1 : ↥V →ₗ[ℂ] ↥V) ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : ↥V)
    exact hx (by have h2 := congrArg (fun f : ↥V →ₗ[ℂ] ↥V => f x) h; simpa using h2)
  have honeE : (1 : ↥V →ₗ[ℂ] ↥V) ∈ E := by
    show (1 : ↥V →ₗ[ℂ] ↥V) ∈ τ.invariants
    rw [Representation.mem_invariants]
    intro m
    exact hAdone (m : G)
  have hEspan : E = ℂ ∙ (1 : ↥V →ₗ[ℂ] ↥V) := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact honeE
    · rw [finrank_span_singleton hone, hfinE]
  have hmemA : ∀ Y : (↥V →ₗ[ℂ] ↥V), A Y ∈ E := by
    intro Y
    show A Y ∈ τ.invariants
    rw [Representation.mem_invariants]
    intro m
    have hmul : τ m * A = A := by
      show τ m * (∑ n : N, τ n) = ∑ n : N, τ n
      rw [Finset.mul_sum]
      exact Fintype.sum_bijective (fun n : N => m * n) (Group.mulLeft_bijective m)
        (fun n : N => τ m * τ n) (fun n : N => τ n) (fun n => (map_mul τ m n).symm)
    show τ m (A Y) = A Y
    rw [← Module.End.mul_apply, hmul]
  have hscal : ∀ Y : (↥V →ₗ[ℂ] ↥V), ∃ c : ℂ, c • (1 : ↥V →ₗ[ℂ] ↥V) = A Y := by
    intro Y
    have hmem : A Y ∈ (ℂ ∙ (1 : ↥V →ₗ[ℂ] ↥V)) := hEspan ▸ hmemA Y
    exact Submodule.mem_span_singleton.mp hmem
  have hkeyB : Ad g * A = A := by
    ext Y
    rw [Module.End.mul_apply]
    obtain ⟨c, hc⟩ := hscal Y
    rw [← hc, map_smul, hAdone g]
  calc ∑ n : N, χ (g * ↑n) * starRingEnd ℂ (χ (g * ↑n))
      = ∑ n : N, Ad.character (g * ↑n) := hstep1
    _ = LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) (Ad g * A) := hstep2
    _ = LinearMap.trace ℂ (↥V →ₗ[ℂ] ↥V) A := by rw [hkeyB]
    _ = ∑ n : N, τ.character n := hstep3
    _ = (Nat.card N : ℂ) := hstep4

end Work.Clifford

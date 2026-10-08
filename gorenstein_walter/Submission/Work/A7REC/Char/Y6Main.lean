/-
Area `A7REC`: **the assembly of the corrected C1e leaf** (`A7Y6Values2Prop`).

Given the six pieces

* `A7Y6SigmaLinProp`  (the trace computation at `σ`),
* `A7ZetaSevenRelationProp`, `A7Y6SevenValueProp`, `A7Y6TraceFinrankProp`
  (the values at elements of order `7`),
* `A7Y6PowerThreeProp` (the cyclotomic power map `g ↦ g³`, using the uniqueness of the
  degree-`6` character),
* `A7RepNeOneProp` (faithfulness),

and the *proved* local fact `Basic.exists_involution_inverting` (an involution inverting each
`σ ≠ 1` of `U`, from the `A₇` configuration), we prove `A7Y6Values2Prop`.

Everything else here is transport: the trace of `ρ` is a class function, `OneInvClass` makes all
involutions conjugate to `z` (so all have trace `2`), and `w σ` is an involution when `w` inverts
`σ`.
-/
import Mathlib
import Submission.Work.A7REC.Char.Y6Defs
import Submission.Work.A7REC.Assembly
import Submission.Work.A7REC.Basic.exists_involution_inverting
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrr

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup OddOrder.RepresentationTheory

/-- An element whose square is `1` and which is not `1` has order `2`. -/
private lemma y6_orderOf_eq_two_of_sq_eq_one {G : Type*} [Group G] {x : G} (h1 : x ≠ 1)
    (h2 : x * x = 1) :
    orderOf x = 2 := by
  have h3 : x ^ 2 = 1 := by rwa [pow_two]
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

/-- **The assembly.**  `A7Y6Values2Prop` from its six pieces. -/
theorem a7Y6Values2_of_pieces
    (hLin : Work.A7REC.A7Y6SigmaLinProp) (hZeta : Work.A7REC.A7ZetaSevenRelationProp)
    (hPow : Work.A7REC.A7Y6PowerThreeProp) (hSev : Work.A7REC.A7Y6SevenValueProp)
    (hTF : Work.A7REC.A7Y6TraceFinrankProp) (hRep : Work.A7REC.A7RepNeOneProp) :
    Work.A7REC.A7Y6Values2Prop := by
  intro G instG instF S z U V hyps hone σ W instW₁ instW₂ instW₃ ρ hσU hσ1 hσ3 hcomm
    hirr h6 hztr hzσtr huniq
  letI : Group G := instG
  letI : Finite G := instF
  letI : AddCommGroup W := instW₁
  letI : Module ℂ W := instW₂
  letI : FiniteDimensional ℂ W := instW₃
  haveI : IsSimpleGroup G := hyps.1
  -- ### the local configuration
  let ctx : Work.A7REC.A7RecCtx G := Work.A7REC.A7RecCtx.ofHyps hyps
  obtain ⟨w, hw2, hwinv⟩ := Work.A7REC.Basic.exists_involution_inverting ctx hσU hσ1
  -- powers of the elements in play
  have hσpow : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
  have hσinv : σ⁻¹ = σ * σ := by
    rw [inv_eq_iff_mul_eq_one]
    show σ * (σ * σ) = 1
    rw [show σ * (σ * σ) = σ ^ 3 by rw [← pow_two, ← pow_succ'], hσpow]
  have hz2' : orderOf z = 2 := hyps.2.2.2.2.1
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2'] at h
    simpa [pow_two] using h
  have hwpow : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hw2] at h
    simpa [pow_two] using h
  have hwpow2 : w ^ 2 = 1 := by rw [pow_two]; exact hwpow
  have hzpow2 : z ^ 2 = 1 := by rw [pow_two]; exact hzsq
  -- `w` inverts `σ`, so `w * σ` is an involution
  have hws : w * σ * w = σ⁻¹ := by
    calc w * σ * w = (w * σ * w⁻¹) * (w * w) := by group
      _ = σ⁻¹ := by rw [hwinv, hwpow, mul_one]
  have hwsq : (w * σ) * (w * σ) = 1 := by
    rw [show w * σ * (w * σ) = (w * σ * w) * σ by group, hws, inv_mul_cancel]
  have hws1 : w * σ ≠ 1 := by
    intro h
    have hσeq : σ = w := by
      have h1 : σ = w * (w * σ) := by rw [← mul_assoc, hwpow, one_mul]
      rw [h, mul_one] at h1
      exact h1
    have h2 : orderOf σ = 2 := by rw [hσeq, hw2]
    omega
  have hws2 : orderOf (w * σ) = 2 := y6_orderOf_eq_two_of_sq_eq_one hws1 hwsq
  -- traces of the `ρ`-images of all involutions, via `OneInvClass`
  have htr_conj : ∀ x : G, orderOf x = 2 → LinearMap.trace ℂ W (ρ x) = 2 := by
    intro x hx
    have h := ClassFunction.of_isConj (repCharacterClassFunction ρ) (hone x z hx hz2')
    have h2 : (repCharacterClassFunction ρ) z = 2 := by
      rw [repCharacterClassFunction_apply]
      exact hztr
    change (repCharacterClassFunction ρ) x = 2
    rw [h, h2]
  -- ### the value at `σ`
  have hvalσ : LinearMap.trace ℂ W (ρ σ) = 3 := by
    refine hLin W h6 (ρ σ) (ρ w) (ρ z) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_pow, hσpow, map_one]
    · rw [← map_pow, hwpow2, map_one]
    · have h1 : (ρ w) * (ρ σ) * (ρ w) = ρ (w * σ * w) := by rw [← map_mul, ← map_mul]
      have h2 : (ρ σ) * (ρ σ) = ρ (σ * σ) := by rw [← map_mul]
      rw [h1, h2, hws, hσinv]
    · rw [← map_pow, hzpow2, map_one]
    · have h1 : (ρ σ) * (ρ z) = ρ (σ * z) := by rw [← map_mul]
      have h2 : (ρ z) * (ρ σ) = ρ (z * σ) := by rw [← map_mul]
      rw [h1, h2, hcomm]
    · have h1 : (ρ w) * (ρ σ) = ρ (w * σ) := by rw [← map_mul]
      rw [h1]
      exact htr_conj (w * σ) hws2
    · exact hztr
    · have h1 : (ρ z) * (ρ σ) = ρ (z * σ) := by rw [← map_mul]
      rw [h1]
      exact hzσtr
  refine ⟨hvalσ, fun x hx7 => ?_⟩
  have hxne : x ≠ 1 := by
    rintro rfl
    simp only [orderOf_one] at hx7
    omega
  -- ### the values at elements of order `7`
  have hpow : LinearMap.trace ℂ W (ρ (x ^ 3)) = LinearMap.trace ℂ W (ρ x) :=
    hPow G W ρ hirr h6 huniq x hx7
  rcases hSev G W h6 ρ x hx7 hpow with h | h
  · exact h
  · exfalso
    have hfin : LinearMap.trace ℂ W (ρ x) = (Module.finrank ℂ W : ℂ) := by
      rw [h, h6]; norm_num
    have hx1 : ρ x = 1 := hTF G W ρ x hx7 hfin
    have hntriv : LinearMap.trace ℂ W (ρ z) ≠ (Module.finrank ℂ W : ℂ) := by
      rw [hztr, h6]; norm_num
    exact hRep G W ρ z hyps.1 hntriv x hxne hx1

end Work.A7REC.Char

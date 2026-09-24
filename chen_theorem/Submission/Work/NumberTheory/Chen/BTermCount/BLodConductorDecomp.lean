import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrCharSum

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-- Conductor decomposition of the sum of the twisted character sums `bProdCharSum`
over the non-principal characters modulo `d`: every non-principal character modulo `d`
is the lift of a unique primitive character modulo its conductor `c ∣ d`, and the
conductor of a non-principal character is `≥ 2`. -/
theorem BLodConductorDecomp (x M Y d : ℕ) [NeZero d] :
    (∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ ≠ 1)),
        ‖bProdCharSum x M Y d χ‖)
      = ∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
          ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            ‖bProdCharSum x M Y d
              (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖ := by
  -- (1) the filtered sum is the sum of the principal-killed summand
  have hL : (∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ ≠ 1)),
        ‖bProdCharSum x M Y d χ‖)
      = ∑ χ : DirichletCharacter ℂ d,
          (if χ = 1 then (0:ℝ) else ‖bProdCharSum x M Y d χ‖) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun χ _ => by by_cases h : χ = 1 <;> simp [h])
  -- (2) the primitive-lift decomposition of the full sum (over `ℂ`)
  have hdec := Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts d
    (fun χ : DirichletCharacter ℂ d =>
      ((if χ = 1 then (0:ℝ) else ‖bProdCharSum x M Y d χ‖ : ℝ) : ℂ))
  -- (3) the term attached to the level `c = 1` vanishes
  have hzero : ∀ c ∈ d.divisors.attach, ¬ (2 ≤ c.1) →
      (∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
        ((if (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) = 1
            then (0:ℝ) else ‖bProdCharSum x M Y d
              (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖ : ℝ) : ℂ))
        = 0 := by
    intro c _ hlt
    have hc1 : c.1 = 1 := by
      have hpos := Nat.pos_of_mem_divisors c.2
      omega
    haveI : Subsingleton (DirichletCharacter ℂ c.1) := by rw [hc1]; infer_instance
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    have hψ : ψ.1 = 1 := Subsingleton.elim _ _
    rw [hψ, DirichletCharacter.changeLevel_one]
    simp
  -- (4) a primitive character of level `≥ 2` stays non-trivial after lifting
  have hlift_ne : ∀ c ∈ d.divisors.attach, 2 ≤ c.1 →
      ∀ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
        DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1 ≠ 1 := by
    intro c _ hc2 ψ h1
    have hcond : (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1).conductor
        = c.1 := by
      rw [DirichletCharacter.conductor_changeLevel ψ.1 (Nat.mem_divisors.mp c.2).1,
        (DirichletCharacter.isPrimitive_def ψ.1).mp ψ.2]
    rw [h1, DirichletCharacter.conductor_one] at hcond
    omega
  -- (5) the same vanishing, phrased for the sum over the attached divisors
  have hfilt :
      (∑ c ∈ d.divisors.attach,
        ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
          ((if (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) = 1
              then (0:ℝ) else ‖bProdCharSum x M Y d
                (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖ : ℝ) : ℂ))
      = ∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
          ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            ((if (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) = 1
                then (0:ℝ) else ‖bProdCharSum x M Y d
                  (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖ : ℝ) : ℂ) :=
    (Finset.sum_filter_of_ne (s := d.divisors.attach) (p := fun c => 2 ≤ c.1)
      (f := fun c => ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
        ((if (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) = 1
            then (0:ℝ) else ‖bProdCharSum x M Y d
              (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖ : ℝ) : ℂ))
      (fun c hc hne => by
        by_contra hlt
        exact hne (hzero c hc hlt))).symm
  -- (6) assemble the complexified identity
  apply Complex.ofReal_injective
  conv_lhs => simp only [hL]
  conv_lhs => simp only [Complex.ofReal_sum]
  conv_lhs => simp only [hdec]
  conv_rhs => simp only [Complex.ofReal_sum]
  conv_lhs => simp only [hfilt]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro ψ _
  simp only [if_neg (hlift_ne c (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hc).2 ψ)]

end Work.NumberTheory.Chen.BTermCount

import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup

namespace Work.LinnikAreas.Density4

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- The finite "lcm" weight `F` of HB §11 is an entire function of `s`: it is a finite
double sum of constants times `[d,e] ^ (-s)`, and `[d,e] ≥ 1` is nonzero. -/
lemma differentiable_lcmF (q : ℕ) [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (lcmF q U V W χ) := by
  have key : Differentiable ℂ (fun s : ℂ => ∑ d ∈ Finset.Icc 1 (Nat.ceil V),
      ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
      ((psiM U V d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
        * (χ ((Nat.lcm d e : ℕ) : ZMod q)) * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))) := by
    refine Differentiable.fun_sum (fun d hd => ?_)
    refine Differentiable.fun_sum (fun e he => ?_)
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hlcm : Nat.lcm d e ≠ 0 := by
      have := Nat.lcm_pos (by omega : 0 < d) (by omega : 0 < e)
      omega
    have hlcmc : ((Nat.lcm d e : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hlcm
    have hbase : Differentiable ℂ (fun s : ℂ => (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))) :=
      (differentiable_id.neg).const_cpow (Or.inl hlcmc)
    exact hbase.const_mul _
  exact key

/-- For a nontrivial character `χ`, the shifted `L`-function `u ↦ L(ρ + u, χ)` is entire,
hence so is the difference-quotient `s ↦ dslope (u ↦ L(ρ + u, χ)) 0 s`. -/
lemma differentiable_dslope_LFunction_shift (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (ρ : ℂ) :
    Differentiable ℂ (dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0) := by
  have hL : Differentiable ℂ (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) :=
    (differentiable_LFunction hχ).comp (differentiable_id.const_add ρ)
  have h := (differentiableOn_dslope (f := fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u))
    (c := 0) (s := Set.univ) (by simp)).mpr hL.differentiableOn
  rwa [differentiableOn_univ] at h

theorem diffOn_Gamma_dslope_mul_lcmF (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hX : 0 < X) (ρ : ℂ) (c₁ c₂ : ℝ) (hc₁ : -1 < c₁) (hc₁₂ : c₁ ≤ c₂) (T : ℝ) :
    DifferentiableOn ℂ (fun s : ℂ => Complex.Gamma (s + 1)
        * dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s
        * (X : ℂ) ^ s * lcmF q U V W χ (ρ + s))
      (Set.uIcc c₁ c₂ ×ℂ Set.uIcc (-T) T) := by
  have hshift : Differentiable ℂ (fun u : ℂ => ρ + u) := differentiable_id.const_add ρ
  have hd : Differentiable ℂ
      (dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0) :=
    differentiable_dslope_LFunction_shift q χ hχ ρ
  have hlcm : Differentiable ℂ (fun s : ℂ => lcmF q U V W χ (ρ + s)) :=
    (differentiable_lcmF q U V W χ).comp hshift
  have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hX
  intro s hs
  have hsre : -1 < s.re := by
    have hm : s.re ∈ Set.uIcc c₁ c₂ := hs.1
    rcases Set.mem_uIcc.mp hm with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hGam : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) s := by
    refine (Complex.differentiableAt_Gamma (s + 1) ?_).comp s ?_
    · intro m hm
      have h3 : (s + 1).re = (-(m : ℂ)).re := congrArg Complex.re hm
      have h1 : (-(m : ℂ)).re = -(m : ℝ) := by simp
      have h2 : (s + 1).re = s.re + 1 := by simp
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · exact differentiableAt_id.add_const 1
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl hXne)
  have hlcm' : DifferentiableAt ℂ (fun z : ℂ => lcmF q U V W χ (ρ + z)) s :=
    hlcm.differentiableAt
  exact (((hGam.mul hd.differentiableAt).mul hpow).mul hlcm').differentiableWithinAt

end Work.LinnikAreas.Density4

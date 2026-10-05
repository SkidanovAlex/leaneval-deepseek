import Mathlib
import Submission.Work.RPV.V

namespace Work.RPB.B5

open Work.RPV

/-- The phase lift `Ac` of a `2π`-periodic curve is equivariant under integer shifts of the
parameter: shifting the parameter by `2π l` shifts `Ac` by `2π l`. -/
private theorem Ac_add_two_pi_mul' (Ac : ℝ → ℝ → ℝ → ℝ)
    (hperA : ∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi)
    (τ σ t : ℝ) (l : ℤ) :
    Ac τ σ (t + 2 * Real.pi * l) = Ac τ σ t + 2 * Real.pi * l :=
  Int.induction_on l (by simp)
    (fun n ih => by
      have ih' : Ac τ σ (t + 2 * Real.pi * (n : ℝ)) = Ac τ σ t + 2 * Real.pi * (n : ℝ) := by
        simpa using ih
      rw [show (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
        show t + 2 * Real.pi * ((n : ℝ) + 1) = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi
          by ring,
        hperA τ σ (t + 2 * Real.pi * (n : ℝ)), ih']
      ring)
    (fun n ih => by
      have ih' : Ac τ σ (t + 2 * Real.pi * (-(n : ℝ))) = Ac τ σ t + 2 * Real.pi * (-(n : ℝ)) := by
        simpa using ih
      have key := hperA τ σ ((t + 2 * Real.pi * (-(n : ℝ))) - 2 * Real.pi)
      have h2 : (t + 2 * Real.pi * (-(n : ℝ)) - 2 * Real.pi) + 2 * Real.pi
          = t + 2 * Real.pi * (-(n : ℝ)) := by ring
      rw [h2] at key
      have key' : Ac τ σ ((t + 2 * Real.pi * (-(n : ℝ))) - 2 * Real.pi)
          = Ac τ σ (t + 2 * Real.pi * (-(n : ℝ))) - 2 * Real.pi := by linarith [key]
      rw [show ((-(n : ℤ) - 1 : ℤ) : ℝ) = -(n : ℝ) - 1 by push_cast; ring,
        show t + 2 * Real.pi * (-(n : ℝ) - 1)
            = (t + 2 * Real.pi * (-(n : ℝ))) - 2 * Real.pi by ring,
        key', ih']
      ring)

theorem collar_noSpurious_restricted (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ)
    (hperΓ : ∀ τ σ t, Γc τ σ (t + 2 * Real.pi) = Γc τ σ t)
    (hperA : ∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi)
    (hemb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ →
      (∀ t, deriv (fun s => Γc τ σ s) t ≠ 0) ∧
      (∀ t t', Γc τ σ t = Γc τ σ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ σ' t t' (k : ℤ) (μ : ℝ), 0 ≤ σ → 0 ≤ σ' →
      (∀ m : ℤ, μ ≠ 2 * Real.pi * m) →
      Work.RPV.levelPt (Γc τ σ t) σ (Ac τ σ t) ≠
        Work.RPV.Tk k (Work.RPV.tau μ (Work.RPV.levelPt (Γc τ σ' t') σ' (Ac τ σ' t'))) := by
  intro τ hτ σ σ' t t' k μ hσ hσ' hμ h
  -- Both sides lie on the collar levels `K₀ = -1 - σ`, `-1 - σ'`, and `K₀` is preserved by
  -- `Tk` and `tau`: hence `σ = σ'`.
  have hK : K0 (levelPt (Γc τ σ t) σ (Ac τ σ t)) =
      K0 (Tk k (tau μ (levelPt (Γc τ σ' t') σ' (Ac τ σ' t')))) := by rw [h]
  rw [K0_levelPt, K0_Tk, K0_tau, K0_levelPt] at hK
  have hσσ : σ = σ' := by linarith
  -- rewrite `σ'` as `σ` everywhere
  rw [← hσσ] at h
  -- `uproj` is preserved by `Tk` and `tau`: the reduced coordinates of the two points agree.
  have hu : Γc τ σ t = Γc τ σ t' := by
    have h1 := congrArg uproj h
    rwa [uproj_levelPt, uproj_Tk, uproj_tau, uproj_levelPt] at h1
  -- comparing the phase coordinate `q₂` gives `Ac τ σ t = Ac τ σ t' + μ + 2π k`.
  have hp : Ac τ σ t = Ac τ σ t' + μ + 2 * Real.pi * (k : ℝ) := by
    have h2 := congrArg (fun x : PS => x.1.2) h
    simp only [Tk, tau, levelPt] at h2
    linarith [h2]
  -- the embedded level curve is injective mod `2π`
  obtain ⟨-, hinj⟩ := hemb τ hτ σ hσ
  obtain ⟨m, hm⟩ := hinj t t' hu
  rw [hm, Ac_add_two_pi_mul' Ac hperA τ σ t m] at hp
  -- hence `μ ∈ 2πℤ`, contradicting `hμ`
  refine hμ (-(m + k)) ?_
  have h3 : μ = -(2 * Real.pi * (m : ℝ)) - 2 * Real.pi * (k : ℝ) := by linarith [hp]
  rw [h3]; push_cast; ring

end Work.RPB.B5

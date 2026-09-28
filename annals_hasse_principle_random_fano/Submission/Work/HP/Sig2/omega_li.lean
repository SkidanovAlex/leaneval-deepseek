import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.eq_pm_of_prim_prop
import Submission.Work.HP.Lat.detLAux

/-!
# Pairs in `Omega d n B` are `ℤ`-linearly independent

If `p.1, p.2` are primitive integer vectors with `p.1 ≠ p.2` and `p.1 ≠ -p.2` (as in the
definition of `Work.HP.Omega`), then they are linearly independent over `ℤ`.  Indeed a nontrivial
integer relation makes them proportional over `ℚ`, and two proportional primitive vectors are
equal up to sign (`eq_pm_of_prim_prop`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Sig2

open Work.HP

/-- Two primitive integer vectors which are not equal up to sign are `ℤ`-linearly independent. -/
theorem li_of_prim_ne_pm {n : ℕ} (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : x ≠ y) (hxy' : x ≠ -y) : LinearIndependent ℤ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_contra hcon
  push Not at hcon
  -- not both coefficients vanish
  have hnotboth : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    exact hcon h.1 h.2
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [zero_smul, zero_add] at hab
    have hb : b = 0 := by
      by_contra hb
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (isPrim_ne_zero hy)
      have := congrFun hab i
      simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      exact hi (by simpa using (mul_eq_zero.mp this).resolve_left hb)
    exact hnotboth.elim (fun h => h rfl) (fun h => h hb)
  -- proportionality over `ℚ`
  refine absurd ?_ (not_or.mpr ⟨hxy, hxy'⟩)
  refine eq_pm_of_prim_prop x y hx hy (-(b : ℚ) / (a : ℚ)) ?_
  funext i
  have hi : a * x i + b * y i = 0 := by
    have := congrFun hab i
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using this
  have hcast : ((a : ℚ)) * (x i : ℚ) + ((b : ℚ)) * (y i : ℚ) = 0 := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hi
    push_cast at this
    simpa using this
  show (x i : ℚ) = -(b : ℚ) / (a : ℚ) * (y i : ℚ)
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast ha
  have h1 : (a : ℚ) * (x i : ℚ) = -(b : ℚ) * (y i : ℚ) := by linarith [hcast]
  have h2 : (x i : ℚ) * (a : ℚ) = -(b : ℚ) * (y i : ℚ) := by rw [mul_comm]; exact h1
  rw [div_mul_eq_mul_div, eq_div_iff haq, h2]

/-- Pairs in `Omega d n B` are `ℤ`-linearly independent. -/
theorem li_of_mem_Omega (d n : ℕ) (B : ℝ)
    (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) (hp : p ∈ Omega d n B) :
    LinearIndependent ℤ ![p.1, p.2] := by
  obtain ⟨h1, h2, hne, hne'⟩ := hp
  exact li_of_prim_ne_pm p.1 p.2 h1.1 h2.1 hne hne'

end Work.HP.Sig2

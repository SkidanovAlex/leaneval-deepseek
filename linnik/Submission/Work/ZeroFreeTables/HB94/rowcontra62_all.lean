import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.table10_62_cert
import Submission.Work.ZeroFreeTables.HB94.hbLemma6_2_engine_restricted
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.ZeroFreeTables

/-- The rows of HB Table 10 are all `≤ 1` in both coordinates (local copy). -/
theorem tableR_hbTable10_le_one_aux {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) :
    p.1 ≤ 1 ∧ p.2 ≤ 1 := by
  simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num

/-- `Work.ZeroFreeTables.row_of_cert62` (local copy, with the lower bound `A` dropped: the
certificate `table10_62_cert` has no lower bound on `u`). -/
theorem row_of_cert62_free (T : TestFn) (c ε a b : ℝ) (hε : 0 < ε)
    (hcert : ∀ u v : ℝ, u ≤ a → u ≤ v → v ≤ b →
      T.F (-u) - T.F 0 - T.F (v - u) + T.f 0 * (3 * (c + ε)) < 0)
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
    (hcore : 0 ≤ T.F (-(lamOf q ρ₁)) - T.F 0 - T.F (lamOf q ρ₂ - lamOf q ρ₁) +
      T.f 0 * (3 * (c + ε)))
    (hl1a : lamOf q ρ₁ ≤ a) (hle : lamOf q ρ₁ ≤ lamOf q ρ₂)
    (hl2 : lamOf q ρ₂ ≤ b) : False := by
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) hl1a hle hl2
  linarith only [hcore, hneg]

/-- **The five-term route of HB Lemma 9.4 with the `χ ^ 60 = 1` supply.**

`Work.ZeroFreeTables.HB94.rowcontra62q` with the supply `L52Hyp · (1/8) ε δ` restricted by
`χ ^ 60 = 1` instead of `orderOf χ ≤ 20`. -/
theorem rowcontra62_all (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 60 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ)
    {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) :
    ∃ q₁ : ℕ, q₀ ≤ q₁ ∧ ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ) [NeZero χ₁.conductor]
      [NeZero χ₂.conductor] [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₁ * χ₂⁻¹).conductor],
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
      χ₁ ^ 60 = 1 → χ₂ ^ 60 = 1 → (χ₁ * χ₂) ^ 60 = 1 → (χ₁ * χ₂⁻¹) ^ 60 = 1 →
      0 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  obtain ⟨lam, hl, hcert⟩ := table10_62_cert p hp
  obtain ⟨qE, hqE⟩ := hbLemma6_2_engine_restricted (tf72T lam hl) ((1:ℝ)/8) (1/1000000) δ
    (by norm_num) hδ0 hδ1
  refine ⟨max q₀ qE, le_max_left _ _, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ _i1 _i2 _i3 _i4 hmin hZ1 hZ2 hc1 hc2 hc21 hc21'
    h160 h260 hA60 hB60 h0le hl1a hl2
  have hq' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hqE' : qE ≤ q := le_trans (le_max_right _ _) hq
  have hneA : χ₁ * χ₂ ≠ 1 := fun h => hc21' (eq_inv_of_mul_eq_one_right h)
  have hneB : χ₁ * χ₂⁻¹ ≠ 1 := fun h => hc21 ((mul_inv_eq_one.mp h).symm)
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ := isMin1_lam_le hmin.1 hZ2
  have hp1 := (tableR_hbTable10_le_one_aux hp).1
  have hp2 := (tableR_hbTable10_le_one_aux hp).2
  have h1 : lamOf q ρ₁ ≤ 1 := le_trans hl1a hp1
  have h2 : lamOf q ρ₂ ≤ 1 := le_trans hl2 hp2
  have hcore := hqE q hqE' χ₁ χ₂ ρ₁ ρ₂
    (hL52 q hq' χ₁ hc1 h160) (hL52 q hq' χ₂ hc2 h260)
    (hL52 q hq' (χ₁ * χ₂) hneA hA60) (hL52 q hq' (χ₁ * χ₂⁻¹) hneB hB60)
    hmin hZ1 hZ2 hc1 hc2 hc21 hc21' h1 h2
  refine row_of_cert62_free (tf72T lam hl) ((1:ℝ)/8) (1/1000000) p.1 p.2
    (by norm_num) ?_ χ₁ χ₂ ρ₁ ρ₂ hcore hl1a hlam12 hl2
  intro u v hua huv hvb
  exact hcert u v hua huv hvb

end Work.ZeroFreeTables.HB94

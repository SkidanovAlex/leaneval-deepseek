import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.table10_93_cert
import Submission.Work.ZeroFreeTables.hbLemma9_3_engine
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.ZeroFreeTables

/-- **Thresholded form of `Work.ZeroFreeTables.row_of_cert93`** (`HBLemma9_4_proof.lean`): the
log-derivative supply is available only from a threshold `q₀`, and `hbLemma9_3_engine` returns a
threshold; the output threshold is `max q₀ qE`. -/
theorem row_of_cert93_q (q₀ : ℕ) (T : TestFn) (k ε c δ A a b : ℝ) (hk : 0 ≤ k) (hε : 0 < ε)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hA : 348/1000 ≤ A) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hcert : ∀ u v : ℝ, A ≤ u → u ≤ a → u ≤ v → v ≤ b →
      (k ^ 2 + 1 / 2) * (T.F (-u) - T.F 0) - 2 * k * T.F (v - u) +
        T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * (c + ε)) < 0)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) :
    ∃ q₁ : ℕ, q₀ ≤ q₁ ∧ ∀ q : ℕ, q₁ ≤ q →
      ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      A ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ a → lamOf q ρ₂ ≤ b → False := by
  obtain ⟨qE, hqE⟩ := hbLemma9_3_engine T k c ε δ hk hε hδ0 hδ1
  refine ⟨max q₀ qE, le_max_left _ _, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1'
    hl1 hl1a hl2
  have hq' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hqE' : qE ≤ q := le_trans (le_max_right _ _) hq
  have hlam2 : lamOf q ρ₂ ≤ 1 := le_trans hl2 hb1
  have hlam1 : lamOf q ρ₁ ≤ 1 := le_trans hl1a ha1
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ := isMin1_lam_le hmin.1 hZ2
  have h92 := hqE q hqE' χ₁ χ₂ ρ₁ ρ₂ (fun χ _ hχ => hL52 q hq' χ hχ)
    hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1' hlam1 hlam2
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) hl1 hl1a hlam12 hl2
  linarith only [h92, hneg]

/-- **Thresholded form of the Lemma 9.3 route** `Work.ZeroFreeTables.rowcontra93`. -/
theorem rowcontra93q (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) (ha : (36/100 : ℝ) ≤ p.1) :
    ∃ q₁ : ℕ, q₀ ≤ q₁ ∧ ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  obtain ⟨lam, k, hl, hk, hcert⟩ := table10_93_cert p hp ha
  have hp1 : p.1 ≤ 702/1000 := by
    have hmem := hp
    simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num
  have hp2 : p.2 ≤ 929/1000 := by
    have hmem := hp
    simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num
  obtain ⟨q₁, hq₁ge, hq₁⟩ := row_of_cert93_q q₀ (tf72T lam hl) k (1/1000000) (1/6) δ
    (348/1000 : ℝ) p.1 p.2 hk (by norm_num) hδ0 hδ1 (le_refl _) (by linarith) (by linarith)
    hcert hL52
  refine ⟨q₁, hq₁ge, ?_⟩
  intro q hq inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1' hl hla hlb
  exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1' hl hla hlb

end Work.ZeroFreeTables.HB94

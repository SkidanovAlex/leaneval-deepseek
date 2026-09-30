import Mathlib
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.step6_defs
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Finset

/-- A prime lying in `[a, b]` and not dividing `q` belongs to `(primesIn a b).filter (· ∤ q)`. -/
lemma step6v2_mem_primesIn_filter {a b : ℝ} {q p : ℕ}
    (hp : Work.BMF.IsPrimeIn a b p) (hq : ¬ p ∣ q) :
    p ∈ (Work.BMF.primesIn a b).filter (fun p ↦ ¬ p ∣ q) := by
  obtain ⟨hpp, h1, h2⟩ := hp
  rw [Finset.mem_filter]
  refine ⟨?_, hq⟩
  simp only [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, hpp⟩

theorem step6v2_tuple_prime {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pr : V → V → ℕ × ℕ) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ)
    (P : ℝ) (k : ℕ) (hk : 1 ≤ k) (hP : (k.factorial : ℝ) < P)
    (q₀ qb : ℕ)
    (hcop : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' → ¬ (pr v v').1 ∣ q₀ ∧ ¬ (pr v v').2 ∣ q₀)
    (hqb : ∀ p : ℕ, p.Prime → ¬ p ∣ k.factorial → ¬ p ∣ q₀ → ¬ p ∣ qb)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2)
    (w : Fin ℓ → V) (hw : w ∈ Work.N8.step6Walks Adj T ℓ) :
    (∀ j, Work.N8.step6Tuple1 ℓ pr w j ∈
        (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ qb)) ∧
      (∀ j, Work.N8.step6Tuple2 ℓ pr w j ∈
        (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ qb)) := by
  classical
  obtain ⟨hwT, hwAdj⟩ := mem_step6Walks.mp hw
  -- primality of each edge label
  have hpr : ∀ j : Fin ℓ,
      Work.BMF.IsPrimeIn P (2 * P) (pr (w j) (w (step6next ℓ j))).1 ∧
      Work.BMF.IsPrimeIn P (2 * P) (pr (w j) (w (step6next ℓ j))).2 :=
    fun j => hedge (w j) (hwT j) (w (step6next ℓ j)) (hwT _) (hwAdj j)
  -- the first component is coprime to `q₀`
  have hndvd_q0 : ∀ j : Fin ℓ, ¬ (pr (w j) (w (step6next ℓ j))).1 ∣ q₀ :=
    fun j => (hcop (w j) (hwT j) (w (step6next ℓ j)) (hwT _) (hwAdj j)).1
  -- the second component is coprime to `q₀`
  have hndvd_q0' : ∀ j : Fin ℓ, ¬ (pr (w j) (w (step6next ℓ j))).2 ∣ q₀ :=
    fun j => (hcop (w j) (hwT j) (w (step6next ℓ j)) (hwT _) (hwAdj j)).2
  -- the first component does not divide `k!` (it exceeds it)
  have hndvd_fac : ∀ j : Fin ℓ, ¬ (pr (w j) (w (step6next ℓ j))).1 ∣ k.factorial := by
    intro j hd
    have h1 : P ≤ ((pr (w j) (w (step6next ℓ j))).1 : ℝ) := (hpr j).1.2.1
    have hlt : k.factorial < (pr (w j) (w (step6next ℓ j))).1 := by
      have : (k.factorial : ℝ) < ((pr (w j) (w (step6next ℓ j))).1 : ℝ) := lt_of_lt_of_le hP h1
      exact_mod_cast this
    exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_dvd (Nat.factorial_pos k) hd))
  -- the second component does not divide `k!` either
  have hndvd_fac' : ∀ j : Fin ℓ, ¬ (pr (w j) (w (step6next ℓ j))).2 ∣ k.factorial := by
    intro j hd
    have h1 : P ≤ ((pr (w j) (w (step6next ℓ j))).2 : ℝ) := (hpr j).2.2.1
    have hlt : k.factorial < (pr (w j) (w (step6next ℓ j))).2 := by
      have : (k.factorial : ℝ) < ((pr (w j) (w (step6next ℓ j))).2 : ℝ) := lt_of_lt_of_le hP h1
      exact_mod_cast this
    exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_dvd (Nat.factorial_pos k) hd))
  constructor
  · intro j
    exact step6v2_mem_primesIn_filter (hpr j).1
      (hqb _ (hpr j).1.1 (hndvd_fac j) (hndvd_q0 j))
  · intro j
    exact step6v2_mem_primesIn_filter (hpr j).2
      (hqb _ (hpr j).2.1 (hndvd_fac' j) (hndvd_q0' j))

end Work.N8

import Submission.Work.Fx.FxCommon

/-!
# Linear cost bookkeeping for chained `Spec`s

Every step of the fixed-point programs has a cost bounded by `K * (szl window + 1)`.  This module
provides the normalised cost `linCost K` and chaining lemmas for exact-window steps.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- The normalised cost bound `t ↦ K * (szl t + 1)`. -/
def linCost (K : ℕ) : List Val → ℕ := fun t => K * (szl t + 1)

/-- Register a bound on the cost of a `Spec`. -/
theorem Spec.lin (hk : KernelLib) {main p : Cmd} {n : ℕ} {P Q : _} {C : List Val → ℕ} {K : ℕ}
    (h : Spec main p n P Q C) (hC : ∀ t, t.length = n → P t → C t ≤ linCost K t) :
    Spec main p n P Q (linCost K) :=
  Spec.mono hk h (fun t _ h => h) (fun t o _ _ h => h) (fun t ht hP => hC t ht hP)

/-- Chain two exact-window steps with linear costs. -/
theorem Spec.seq_det_lin (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val}
    {K1 K2 C : ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) (linCost K1))
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (linCost K2))
    (hB : B.length = m) (hsz : szl B ≤ C * (szl A + 1)) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D) (linCost (K1 + K2 * (C + 1))) := by
  have hcost : ∀ (t o : List Val), t.length = n → t = A → o = B →
      linCost K2 o ≤ K2 * (C + 1) * (szl t + 1) := by
    intro t o _ hAt hBo
    rw [hAt, hBo]
    simp only [linCost]
    have hsz' : szl B + 1 ≤ (C + 1) * (szl A + 1) := by
      have h1' := hsz
      have h2' : 1 ≤ szl A + 1 := Nat.succ_pos _
      nlinarith
    calc K2 * (szl B + 1) ≤ K2 * ((C + 1) * (szl A + 1)) := Nat.mul_le_mul_left _ hsz'
      _ = K2 * (C + 1) * (szl A + 1) := by ring
  have h := Spec.seq hk (main := main) (p := p) (q := q) (n := n) (m := m)
    (P := fun t => t = A) (Q := fun _ o => o = B) (C := linCost K1)
    (P' := fun t => t = B) (Q' := fun _ o => o = D) (C' := linCost K2)
    (B := fun t => K2 * (C + 1) * (szl t + 1)) h1 h2
    (by intro t o _ hAt hBo; rw [hBo]; exact hB)
    (by intro t o _ hAt hBo; rw [hBo])
    hcost
  refine Spec.mono hk h (fun t _ h => h) ?_ ?_
  · intro t o _ _ hQ
    rcases hQ with ⟨m, hm, hD⟩
    exact hD
  · intro t _ _
    simp only [linCost]
    nlinarith

/-- A step with an exact window but an arbitrary cost, followed by a linear-cost step. -/
theorem Spec.seq_det_lin' (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val} {K2 C : ℕ}
    {C1 : List Val → ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) C1)
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (linCost K2))
    (hB : B.length = m) (hsz : szl B ≤ C * (szl A + 1)) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D)
      (fun t => C1 t + K2 * (C + 1) * (szl t + 1)) := by
  have hcost : ∀ (t o : List Val), t.length = n → t = A → o = B →
      linCost K2 o ≤ K2 * (C + 1) * (szl t + 1) := by
    intro t o _ hAt hBo
    rw [hAt, hBo]
    simp only [linCost]
    have hsz' : szl B + 1 ≤ (C + 1) * (szl A + 1) := by
      have h1' := hsz
      have h2' : 1 ≤ szl A + 1 := Nat.succ_pos _
      nlinarith
    calc K2 * (szl B + 1) ≤ K2 * ((C + 1) * (szl A + 1)) := Nat.mul_le_mul_left _ hsz'
      _ = K2 * (C + 1) * (szl A + 1) := by ring
  have h := Spec.seq hk (main := main) (p := p) (q := q) (n := n) (m := m)
    (P := fun t => t = A) (Q := fun _ o => o = B) (C := C1)
    (P' := fun t => t = B) (Q' := fun _ o => o = D) (C' := linCost K2)
    (B := fun t => K2 * (C + 1) * (szl t + 1)) h1 h2
    (by intro t o _ hAt hBo; rw [hBo]; exact hB)
    (by intro t o _ hAt hBo; rw [hBo])
    hcost
  exact Spec.mono hk h (fun t _ h => h) (fun t o _ _ hQ => by
    rcases hQ with ⟨m, hm, hD⟩; exact hD) (fun t _ _ => le_rfl)

/-- Extend an exact-window `Spec` with a carried block `E` that is not touched. -/
theorem Spec.extend_exact (hk : KernelLib) {main p : Cmd} {n k : ℕ} {A B : List Val}
    {C : List Val → ℕ} (h : Spec main p n (fun t => t = A) (fun _ o => o = B) C) {E : List Val}
    (hE : E.length = k) :
    Spec main p (n + k) (fun t => t = A ++ E) (fun _ o => o = B ++ E) (fun _ => C A) := by
  intro top rest ht hP
  have hA : A.length = n := by
    have h1 := ht
    rw [hP, List.length_append, hE] at h1
    omega
  rw [hP]
  refine hk.conseq (main := main) (p := p)
    (P := fun vs => vs = A ++ (E ++ rest)) (P' := fun vs => vs = (A ++ E) ++ rest)
    (Q := fun _ out => ∃ o, out = o ++ (E ++ rest) ∧ o = B)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ o = B ++ E)
    (C := fun _ => C A) (C' := fun _ => C A)
    (h A (E ++ rest) hA rfl) ?_ ?_ (fun vs _ => le_rfl)
  · intro vs hv
    rw [hv, List.append_assoc]
  · intro vs out hv hQ
    rcases hQ with ⟨o, hout, ho⟩
    rw [ho] at hout
    exact ⟨B ++ E, by rw [hout, List.append_assoc], rfl⟩

/-- Extend an exact-window `Spec` with a carried block, then register a linear cost. -/
theorem Spec.extend_lin (hk : KernelLib) {main p : Cmd} {n k : ℕ} {A B : List Val} {C : List Val → ℕ}
    {K : ℕ} (h : Spec main p n (fun t => t = A) (fun _ o => o = B) C) {E : List Val}
    (hE : E.length = k) (hC : C A ≤ linCost K (A ++ E)) :
    Spec main p (n + k) (fun t => t = A ++ E) (fun _ o => o = B ++ E) (linCost K) :=
  Spec.mono hk (Spec.extend_exact hk h hE) (fun t _ h => h) (fun t o _ _ h => h)
    (fun t _ hAt => by rw [hAt]; exact hC)

end Work.Fx

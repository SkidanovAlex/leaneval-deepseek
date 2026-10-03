import Mathlib
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.decor_tlU_tlW_at

namespace Work.OROneRel

/-- The `j`-th `a`-letter of the decorated walk of `tlU p q`, i.e. the edge `((0), m + j q)`, lies in
the window `Wedge p q a b` as soon as `a ≤ m` and `m + p q ≤ b`. -/
theorem mem_Wedge_of_a_decor (p q : ℕ) {a b m : ℤ} (ham : a ≤ m)
    (hmb : m + (p : ℤ) * (q : ℤ) ≤ b) (j : Fin p) :
    (((0 : Fin 2), m + (j : ℤ) * (q : ℤ)) : Fin 2 × ℤ) ∈ Wedge p q a b := by
  rw [mem_Wedge_zero]
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg _
  have hjlt : (j : ℤ) < (p : ℤ) := by exact_mod_cast j.isLt
  constructor
  · nlinarith [ham, hj0, hq0]
  · nlinarith [hmb, hjlt, hq0]

/-- The `k`-th `b`-letter of the decorated walk of `tlU p q`, i.e. the edge `((1), m + p q - k p)`,
lies in the window `Wedge p q a b` as soon as `a ≤ m` and `m + p q ≤ b`. -/
theorem mem_Wedge_of_b_decor (p q : ℕ) {a b m : ℤ} (ham : a ≤ m)
    (hmb : m + (p : ℤ) * (q : ℤ) ≤ b) (k : Fin q) :
    (((1 : Fin 2), m + (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)) : Fin 2 × ℤ) ∈ Wedge p q a b := by
  rw [mem_Wedge_one]
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg _
  have hklt : (k : ℤ) < (q : ℤ) := by exact_mod_cast k.isLt
  constructor
  · nlinarith [ham, hklt, hp0]
  · nlinarith [hmb, hk0, hp0]

theorem WrelGen_decor_tlU_letters_mem (p q : ℕ) (hp : 1 ≤ p) {a b m : ℤ} (ham : a ≤ m)
    (hmb : m + (p : ℤ) * (q : ℤ) ≤ b) :
    ∀ (e : Fin 2 × ℤ) (bool : Bool), (e, bool) ∈
      decor (tlW p q) m (wordOf (tlU p q)) → e ∈ Wedge p q a b := by
  intro e bool he
  rw [decor_tlU_tlW_at] at he
  rw [List.mem_append] at he
  rcases he with he | he
  · rw [List.mem_ofFn] at he
    obtain ⟨j, hj⟩ := he
    simp only [Prod.mk.injEq] at hj
    rw [← hj.1]
    exact mem_Wedge_of_a_decor p q ham hmb j
  · rw [List.mem_ofFn] at he
    obtain ⟨k, hk⟩ := he
    simp only [Prod.mk.injEq] at hk
    rw [← hk.1]
    exact mem_Wedge_of_b_decor p q ham hmb k

end Work.OROneRel

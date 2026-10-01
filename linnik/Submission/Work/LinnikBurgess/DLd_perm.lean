import Mathlib
import Submission.Work.LinnikBurgess.frame_step_defs

namespace Work.LinnikBurgess

open Polynomial

/-- The product `∏_l (X + a_l)` only sees the multiset of the `a_l`, hence is invariant under
permuting the triple. -/
lemma cubicZ_comp_perm (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    cubicZ (fun l => a (σ l)) = cubicZ a := by
  simp only [cubicZ]
  exact Equiv.prod_comp σ (fun l => X + C ((a l : ℕ) : ℤ))

/-- `critN a b = f_a' f_b - f_a f_b'` is invariant under permuting the first triple. -/
lemma critN_comp_perm (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    critN (fun l => a (σ l)) b = critN a b := by
  simp only [critN, cubicZ_comp_perm]

/-- `critN` is invariant under permuting the second triple. -/
lemma critN_comp_perm_right (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    critN a (fun l => b (σ l)) = critN a b := by
  simp only [critN, cubicZ_comp_perm]

/-- `derivative ∘ critN` inherits the permutation invariance. -/
lemma derivative_critN_comp_perm (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    derivative (critN (fun l => a (σ l)) b) = derivative (critN a b) := by
  rw [critN_comp_perm]

/-- `UnitAt` only depends on the set (indeed the multiset) of the `a_l`; permuting the first
triple does not change it. -/
lemma UnitAt_comp_perm (p y : ℕ) (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    UnitAt p y (fun l => a (σ l)) b ↔ UnitAt p y a b := by
  constructor
  · intro h
    have h1 : ∀ l : Fin 3, ¬ p ∣ y + a l := by
      intro l
      obtain ⟨m, hm⟩ := σ.surjective l
      have := (h m).1
      simpa [hm] using this
    exact fun l => ⟨h1 l, (h l).2⟩
  · intro h l
    exact ⟨(h (σ l)).1, (h l).2⟩

/-- `UnitAt` is invariant under permuting the second triple. -/
lemma UnitAt_comp_perm_right (p y : ℕ) (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    UnitAt p y a (fun l => b (σ l)) ↔ UnitAt p y a b := by
  constructor
  · intro h
    have h2 : ∀ l : Fin 3, ¬ p ∣ y + b l := by
      intro l
      obtain ⟨m, hm⟩ := σ.surjective l
      have := (h m).2
      simpa [hm] using this
    exact fun l => ⟨(h l).1, h2 l⟩
  · intro h l
    exact ⟨(h l).1, (h (σ l)).2⟩

/-- `DL_p` (double-critical level `≥ s` at the prime `p`) is invariant under permuting either
triple. -/
lemma DLp_perm (p s : ℕ) (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    DLp p s (fun l : Fin 3 => a (σ l)) b ↔ DLp p s a b := by
  have hN : critN (fun l => a (σ l)) b = critN a b := critN_comp_perm a b σ
  have hd : derivative (critN (fun l => a (σ l)) b) = derivative (critN a b) :=
    derivative_critN_comp_perm a b σ
  have hU : ∀ q y, UnitAt q y (fun l => a (σ l)) b ↔ UnitAt q y a b :=
    fun q y => UnitAt_comp_perm q y a b σ
  simp only [DLp]
  constructor
  · rintro ⟨y, hu, h1, h2⟩
    exact ⟨y, (hU p y).mp hu, by rw [← hN]; exact h1, by rw [← hd]; exact h2⟩
  · rintro ⟨y, hu, h1, h2⟩
    exact ⟨y, (hU p y).mpr hu, by rw [hN]; exact h1, by rw [hd]; exact h2⟩

/-- `DL_d` is invariant under permuting the first triple: `∏_l (X + a_l)` is symmetric in the `a_l`, so `cubicZ` and `critN` — and hence `DL_d`, `DLp`, `UnitAt` — are unchanged by `a ↦ a ∘ σ`. -/
theorem DLd_perm {d : ℕ} (a b : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) :
    DLd d (fun l : Fin 3 => a (σ l)) b ↔ DLd d a b := by
  have hN : critN (fun l => a (σ l)) b = critN a b := critN_comp_perm a b σ
  have hd : derivative (critN (fun l => a (σ l)) b) = derivative (critN a b) :=
    derivative_critN_comp_perm a b σ
  have hU : ∀ p y, UnitAt p y (fun l => a (σ l)) b ↔ UnitAt p y a b :=
    fun p y => UnitAt_comp_perm p y a b σ
  simp only [DLd]
  constructor
  · rintro ⟨y, hu, h1, h2⟩
    exact ⟨y, fun p hp => (hU p y).mp (hu p hp), by rw [← hN]; exact h1, by rw [← hd]; exact h2⟩
  · rintro ⟨y, hu, h1, h2⟩
    exact ⟨y, fun p hp => (hU p y).mpr (hu p hp), by rw [hN]; exact h1, by rw [hd]; exact h2⟩

end Work.LinnikBurgess

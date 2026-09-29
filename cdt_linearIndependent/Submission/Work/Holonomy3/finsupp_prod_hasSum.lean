import Mathlib

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Work.Holonomy3

/-- The bijection `ℕ × (Fin n →₀ ℕ) ≃ (Fin (n+1) →₀ ℕ)` given by `Finsupp.cons`. -/
private noncomputable def consEquiv (n : ℕ) : ℕ × (Fin n →₀ ℕ) ≃ (Fin (n + 1) →₀ ℕ) where
  toFun p := Finsupp.cons p.1 p.2
  invFun m := (m 0, Finsupp.tail m)
  left_inv p := by simp
  right_inv m := Finsupp.cons_tail m

private lemma consEquiv_apply (n : ℕ) (p : ℕ × (Fin n →₀ ℕ)) :
    consEquiv n p = Finsupp.cons p.1 p.2 := rfl

/-- Multivariate version: the total sum of the product family over the multi-index monoid
equals the product of the individual sums, together with absolute summability. -/
private lemma aux (d : ℕ) (g : Fin d → ℕ → ℂ) (z : Fin d → ℂ)
    (h : ∀ s : Fin d, Summable (fun j : ℕ => ‖g s j * z s ^ j‖)) :
    HasSum (fun n : Fin d →₀ ℕ => ∏ s : Fin d, (g s (n s) * z s ^ (n s)))
        (∏ s : Fin d, ∑' j : ℕ, g s j * z s ^ j) ∧
      Summable (fun n : Fin d →₀ ℕ => ‖∏ s : Fin d, (g s (n s) * z s ^ (n s))‖) := by
  induction d with
  | zero =>
    constructor
    · haveI : Fintype (Fin 0 →₀ ℕ) := Fintype.ofSubsingleton 0
      simpa using hasSum_fintype (fun _ : Fin 0 →₀ ℕ => (1 : ℂ))
    · haveI : Fintype (Fin 0 →₀ ℕ) := Fintype.ofSubsingleton 0
      have h1 : HasSum (fun _ : Fin 0 →₀ ℕ => (1 : ℝ)) 1 := by
        simpa using hasSum_fintype (fun _ : Fin 0 →₀ ℕ => (1 : ℝ))
      simpa using h1.summable
  | succ n ih =>
    obtain ⟨hGsum, hGnorm⟩ :=
      ih (fun s : Fin n => g s.succ) (fun s : Fin n => z s.succ) (fun s => h s.succ)
    have hfsum : HasSum (fun j : ℕ => g 0 j * z 0 ^ j) (∑' j : ℕ, g 0 j * z 0 ^ j) :=
      (h 0).of_norm.hasSum
    have hmul_norm : Summable (fun p : ℕ × (Fin n →₀ ℕ) =>
        ‖(g 0 p.1 * z 0 ^ p.1) * (∏ s : Fin n, (g s.succ (p.2 s) * z s.succ ^ (p.2 s)))‖) :=
      Summable.mul_norm (f := fun j : ℕ => g 0 j * z 0 ^ j)
        (g := fun m : Fin n →₀ ℕ => ∏ s : Fin n, (g s.succ (m s) * z s.succ ^ (m s)))
        (h 0) hGnorm
    have hmul_summ : Summable (fun p : ℕ × (Fin n →₀ ℕ) =>
        (g 0 p.1 * z 0 ^ p.1) * (∏ s : Fin n, (g s.succ (p.2 s) * z s.succ ^ (p.2 s)))) :=
      hmul_norm.of_norm
    have hprod : HasSum (fun p : ℕ × (Fin n →₀ ℕ) =>
        (g 0 p.1 * z 0 ^ p.1) * (∏ s : Fin n, (g s.succ (p.2 s) * z s.succ ^ (p.2 s))))
        ((∑' j : ℕ, g 0 j * z 0 ^ j) *
          (∏ s : Fin n, ∑' j : ℕ, g s.succ j * z s.succ ^ j)) :=
      HasSum.mul (f := fun j : ℕ => g 0 j * z 0 ^ j)
        (g := fun m : Fin n →₀ ℕ => ∏ s : Fin n, (g s.succ (m s) * z s.succ ^ (m s)))
        hfsum hGsum hmul_summ
    have hfun : ((fun m : Fin (n + 1) →₀ ℕ => ∏ s : Fin (n + 1), (g s (m s) * z s ^ (m s))) ∘
        ⇑(consEquiv n)) =
        fun p : ℕ × (Fin n →₀ ℕ) =>
          (g 0 p.1 * z 0 ^ p.1) * (∏ s : Fin n, (g s.succ (p.2 s) * z s.succ ^ (p.2 s))) := by
      funext p
      simp only [Function.comp_apply, consEquiv_apply, Fin.prod_univ_succ, Finsupp.cons_zero,
        Finsupp.cons_succ]
    constructor
    · have hcomp : HasSum ((fun m : Fin (n + 1) →₀ ℕ =>
          ∏ s : Fin (n + 1), (g s (m s) * z s ^ (m s))) ∘ ⇑(consEquiv n))
          ((∑' j : ℕ, g 0 j * z 0 ^ j) *
            (∏ s : Fin n, ∑' j : ℕ, g s.succ j * z s.succ ^ j)) := by
        rw [hfun]
        exact hprod
      have h2 := (Equiv.hasSum_iff (f := fun m : Fin (n + 1) →₀ ℕ =>
          ∏ s : Fin (n + 1), (g s (m s) * z s ^ (m s))) (consEquiv n)).mp hcomp
      rw [Fin.prod_univ_succ]
      exact h2
    · have hfun2 : ((fun m : Fin (n + 1) →₀ ℕ =>
          ‖∏ s : Fin (n + 1), (g s (m s) * z s ^ (m s))‖) ∘ ⇑(consEquiv n)) =
          fun p : ℕ × (Fin n →₀ ℕ) =>
            ‖(g 0 p.1 * z 0 ^ p.1) * (∏ s : Fin n, (g s.succ (p.2 s) * z s.succ ^ (p.2 s)))‖ := by
        funext p
        simp only [Function.comp_apply, consEquiv_apply, Fin.prod_univ_succ, Finsupp.cons_zero,
          Finsupp.cons_succ]
      have hS : Summable ((fun m : Fin (n + 1) →₀ ℕ =>
          ‖∏ s : Fin (n + 1), (g s (m s) * z s ^ (m s))‖) ∘ ⇑(consEquiv n)) := by
        rw [hfun2]
        exact hmul_norm
      exact (Equiv.summable_iff (f := fun m : Fin (n + 1) →₀ ℕ =>
          ‖∏ s : Fin (n + 1), (g s (m s) * z s ^ (m s))‖) (consEquiv n)).mp hS

theorem finsupp_prod_hasSum {d : ℕ} (g : Fin d → ℕ → ℂ) (z : Fin d → ℂ)
    (h : ∀ s : Fin d, Summable (fun j : ℕ => ‖g s j * z s ^ j‖)) :
    HasSum (fun n : Fin d →₀ ℕ => (∏ s : Fin d, g s (n s)) * ∏ s : Fin d, z s ^ (n s))
      (∏ s : Fin d, ∑' j : ℕ, g s j * z s ^ j) := by
  simpa [Finset.prod_mul_distrib] using (aux d g z h).1

end Work.Holonomy3

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.SimpleRing.Principal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- The partial sum `∑_{n < M} χ(n)` of a nontrivial Dirichlet character. -/
private noncomputable def charSum {N : ℕ} (χ : DirichletCharacter ℂ N) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M, (χ (n : ZMod N) : ℂ)

/-- Summing over all residues mod `N` equals summing over the representatives `0, …, N-1`. -/
private lemma sum_univ_zmod_eq_sum_range {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    (∑ a : ZMod N, g a) = ∑ n ∈ Finset.range N, g (n : ZMod N) := by
  classical
  have hval (a : ZMod N) : (a.val : ZMod N) = a := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  refine Finset.sum_bij (s := (Finset.univ : Finset (ZMod N))) (t := Finset.range N)
    (fun a _ => a.val) ?hi ?inj ?surj ?h
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a₁ _ a₂ _ h
    apply ZMod.val_injective
    exact h
  · intro b hb
    refine ⟨(b : ZMod N), by simp, ?_⟩
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
  · intro a _
    rw [hval a]

/-- A nontrivial Dirichlet character sums to zero over any `N` consecutive integers. -/
private lemma char_block_sum_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℕ) :
    (∑ t ∈ Finset.range N, (χ ((s + t : ℕ) : ZMod N) : ℂ)) = 0 := by
  calc
    (∑ t ∈ Finset.range N, (χ ((s + t : ℕ) : ZMod N) : ℂ))
        = ∑ t ∈ Finset.range N, (χ ((s : ZMod N) + (t : ZMod N)) : ℂ) := by
            apply Finset.sum_congr rfl
            intro t _
            congr 1
            simp
    _ = ∑ a : ZMod N, (χ ((s : ZMod N) + a) : ℂ) := by
            rw [← sum_univ_zmod_eq_sum_range (N := N)
              (g := fun a : ZMod N => (χ ((s : ZMod N) + a) : ℂ))]
    _ = (∑ a : ZMod N, (χ a : ℂ)) := by
            exact Fintype.sum_equiv (Equiv.addLeft (s : ZMod N))
              (fun a : ZMod N => (χ ((s : ZMod N) + a) : ℂ)) (fun a : ZMod N => (χ a : ℂ)) (by simp)
    _ = 0 := by
            simpa using (MulChar.sum_eq_zero_of_ne_one (R := ZMod N) (R' := ℂ) hχ)

/-- The partial sums of a nontrivial Dirichlet character are periodic with period `N`. -/
private lemma charSum_add_N {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (M : ℕ) :
    charSum χ (M + N) = charSum χ M := by
  unfold charSum
  rw [← Finset.sum_range_add_sum_Ico (f := fun n => (χ (n : ZMod N) : ℂ)) (m := M) (n := M + N)
        (Nat.le_add_right M N)]
  have hblock : (∑ n ∈ Finset.Ico M (M + N), (χ (n : ZMod N) : ℂ)) = 0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Nat.add_sub_cancel_left]
    exact char_block_sum_zero χ hχ M
  rw [hblock, add_zero]

/-- A partial sum depends only on the length modulo `N`. -/
private lemma charSum_mod {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (M : ℕ) :
    charSum χ M = charSum χ (M % N) := by
  have hM : M = (M / N) * N + M % N := by
    simpa [mul_comm] using (Nat.div_add_mod M N).symm
  have hind : ∀ q : ℕ, charSum χ (q * N + M % N) = charSum χ (M % N) := by
    intro q
    induction q with
    | zero => simp [charSum]
    | succ q ih =>
        have harg : (q + 1) * N + M % N = q * N + M % N + N := by ring
        rw [harg]
        rw [charSum_add_N χ hχ (q * N + M % N)]
        exact ih
  conv_lhs => rw [hM]
  exact hind (M / N)

/-- Partial sums of a nontrivial Dirichlet character over `0 ≤ n < M` are uniformly
bounded by the conductor: `‖∑_{n < M} χ(n)‖ ≤ N` for every `M`. -/
private lemma partial_sum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (M : ℕ) : ‖charSum χ M‖ ≤ (N : ℝ) := by
  have hred : charSum χ M = charSum χ (M % N) := charSum_mod χ hχ M
  rw [hred]
  unfold charSum
  have hr : M % N < N := Nat.mod_lt M (Nat.pos_of_ne_zero (NeZero.ne N))
  calc
    ‖∑ t ∈ Finset.range (M % N), (χ (t : ZMod N) : ℂ)‖ ≤
        ∑ t ∈ Finset.range (M % N), ‖(χ (t : ZMod N) : ℂ)‖ := by
      exact norm_sum_le (Finset.range (M % N)) (fun t => (χ (t : ZMod N) : ℂ))
    _ ≤ ∑ t ∈ Finset.range (M % N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      simpa using (DirichletCharacter.norm_le_one χ (t : ZMod N))
    _ = (M % N : ℕ) := by simp
    _ ≤ (N : ℝ) := by exact_mod_cast (Nat.le_of_lt hr)

/-- An interval sum is the difference of two partial sums. -/
private lemma interval_eq_sub {N : ℕ} (χ : DirichletCharacter ℂ N) {x y : ℕ} (hxy : x ≤ y) :
    (∑ n ∈ Finset.Icc x y, (χ (n : ZMod N) : ℂ)) = charSum χ (y + 1) - charSum χ x := by
  rw [show (Finset.Icc x y : Finset ℕ) = Finset.Ico x (y + 1) from
    (Finset.Ico_add_one_right_eq_Icc x y).symm]
  unfold charSum
  exact Finset.sum_Ico_eq_sub (f := fun n => (χ (n : ZMod N) : ℂ)) (m := x) (n := y + 1) (by omega)

/-- Partial sums of a nontrivial Dirichlet character over the interval `[x, y]` are
uniformly bounded by twice the conductor: `‖∑_{x ≤ n ≤ y} χ(n)‖ ≤ 2N` for `x ≤ y`. -/
theorem interval_sum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x y : ℕ} (hxy : x ≤ y) :
    ‖∑ n ∈ Finset.Icc x y, (χ (n : ZMod N) : ℂ)‖ ≤ (2 * N : ℝ) := by
  rw [interval_eq_sub χ hxy]
  calc
    ‖charSum χ (y + 1) - charSum χ x‖ ≤ ‖charSum χ (y + 1)‖ + ‖charSum χ x‖ := norm_sub_le _ _
    _ ≤ (N : ℝ) + (N : ℝ) := by
      exact add_le_add (partial_sum_bound χ hχ (y + 1)) (partial_sum_bound χ hχ x)
    _ = (2 * N : ℝ) := by ring

end Commons.NumberTheory.DirichletCharacter
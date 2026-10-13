import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Cell.Junk

open WilkiesDesign Work.WilG1.Cell

/-- Monotonicity of `S.Ω` in the `F`-index: raising the `F`-bound keeps membership. -/
theorem Ω_mono_F_le (S : WilkiesDesign.SOMin) {F F' D n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hle : F ≤ F') : X ∈ S.Ω F' D n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => rw [Nat.add_zero]; exact h
  | succ d ih => rw [Nat.add_succ]; exact S.mono_F ih

/-- Monotonicity of `S.Ω` in the `D`-index: raising the `D`-bound keeps membership. -/
theorem Ω_mono_D_le (S : WilkiesDesign.SOMin) {F D D' n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hle : D ≤ D') : X ∈ S.Ω F D' n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => rw [Nat.add_zero]; exact h
  | succ d ih => rw [Nat.add_succ]; exact S.mono_D ih

/-- The iterated statement: for every function `h` whose graph lies in `S.Ω F' D' (n+1)`,
all iterated junk partials of `h` along words of length `≤ k` admit a *uniform* `S.Ω`-bound
`(A, B)` with the `D`-parameter read as `B.eval D'`.

The induction is on the word length.  The key point is that the recursion
`junkIt h (i :: w) = junkIt (junkP h i) w` attaches the *first* direction to the outer
function, so at every step the induction hypothesis may be applied to the `n` new functions
`junkP h i` (`i : Fin n`).  Only these finitely many alternatives have to be merged — by a
pointwise `Finset.sup` for the `F`-index and by summing the corresponding polynomials for
the `D`-index — so no enumeration of words is needed. -/
theorem junkIt_mem_aux (S : WilkiesDesign.SOMin) {n : ℕ}
    (hstep : ∀ (m F' : ℕ) (g : (Fin m → ℝ) → ℝ) (i : Fin m) (D' : ℕ),
      WilkiesDesign.graphOf g ∈ S.Ω F' D' (m + 1) →
        ∃ (a : ℕ) (b : Polynomial ℕ),
          WilkiesDesign.graphOf (junkP g i) ∈ S.Ω a (b.eval D') (m + 1)) :
    ∀ (k : ℕ) (h : (Fin n → ℝ) → ℝ) (F' D' : ℕ),
      WilkiesDesign.graphOf h ∈ S.Ω F' D' (n + 1) →
      ∃ (A : ℕ) (B : Polynomial ℕ), ∀ (w : List (Fin n)), w.length ≤ k →
        WilkiesDesign.graphOf (junkIt h w) ∈ S.Ω A (B.eval D') (n + 1) := by
  intro k
  induction k with
  | zero =>
      intro h F' D' hh
      refine ⟨F', Polynomial.X, fun w hw => ?_⟩
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hw0, junkIt_nil]
      simpa [Polynomial.eval_X] using hh
  | succ k ih =>
      intro h F' D' hh
      have key : ∀ i : Fin n, ∃ (A : ℕ) (B : Polynomial ℕ),
          ∀ w : List (Fin n), w.length ≤ k →
            WilkiesDesign.graphOf (junkIt (junkP h i) w) ∈ S.Ω A (B.eval D') (n + 1) := by
        intro i
        obtain ⟨a, b, hab⟩ := hstep n F' h i D' hh
        obtain ⟨A, B, hAB⟩ := ih (junkP h i) a (b.eval D') hab
        refine ⟨A, B.comp b, fun w hw => ?_⟩
        rw [Polynomial.eval_comp]
        exact hAB w hw
      choose A_i B_i hB_i using key
      refine ⟨max F' (Finset.univ.sup A_i), Polynomial.X + ∑ i : Fin n, B_i i, fun w hw => ?_⟩
      match w with
      | [] =>
          rw [junkIt_nil]
          refine Ω_mono_D_le S (Ω_mono_F_le S hh (le_max_left _ _)) ?_
          have hev : (Polynomial.X + ∑ i : Fin n, B_i i).eval D'
              = D' + ∑ i : Fin n, (B_i i).eval D' := by
            rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_finsetSum]
          rw [hev]; omega
      | i :: w' =>
          have hwk : w'.length ≤ k := by
            simp only [List.length_cons] at hw; omega
          have hm := hB_i i w' hwk
          rw [junkIt_cons]
          refine Ω_mono_D_le S (Ω_mono_F_le S hm ?_) ?_
          · exact le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)
          · have hsum : (B_i i).eval D' ≤ ∑ j : Fin n, (B_i j).eval D' :=
              Finset.single_le_sum (f := fun j => (B_i j).eval D')
                (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
            have hev : (Polynomial.X + ∑ i : Fin n, B_i i).eval D'
                = D' + ∑ i : Fin n, (B_i i).eval D' := by
              rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_finsetSum]
            rw [hev]; omega

theorem junkIt_mem (S : WilkiesDesign.SOMin) {n F : ℕ} (f : (Fin n → ℝ) → ℝ) (k D : ℕ)
    (hstep : ∀ (m F' : ℕ) (g : (Fin m → ℝ) → ℝ) (i : Fin m) (D' : ℕ),
      WilkiesDesign.graphOf g ∈ S.Ω F' D' (m + 1) →
        ∃ (a : ℕ) (b : Polynomial ℕ),
          WilkiesDesign.graphOf (junkP g i) ∈ S.Ω a (b.eval D') (m + 1))
    (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (n + 1)) :
    ∃ (A : ℕ) (B : Polynomial ℕ), ∀ (w : List (Fin n)), w.length ≤ k →
      WilkiesDesign.graphOf (junkIt f w) ∈ S.Ω A (B.eval D) (n + 1) :=
  junkIt_mem_aux (n := n) S hstep k f F D hf

end Work.WilG1.Cell.Junk

import ChallengeDeps
import Submission.Vinogradov.Core
import Submission.Vinogradov.Asymptotic
import Submission.Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- In the regime `s ≤ k`, every matching `y` is a permutation of `x`, so a
fixed `x` has at most `s!` matching partners. -/
lemma fiber_le_factorial {s k X : ℕ} (hsk : s ≤ k)
    (x : Fin s → Finset.Icc 1 X) :
    ((Finset.univ.filter (fun y : Fin s → Finset.Icc 1 X => Matches s k X (x, y))).card)
      ≤ Nat.factorial s := by
  let xv : Fin s → ℕ := fun i => (x i).1
  let S := (Finset.univ.filter (fun y : Fin s → Finset.Icc 1 X => Matches s k X (x, y)))
  let g : (Fin s → Finset.Icc 1 X) → Equiv.Perm (Fin s) := fun y =>
    if h : ∀ j ≤ s, (∑ i, (xv i) ^ j) = (∑ i, ((y i).1) ^ j) then
      Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y i).1) h)
    else 1
  have hinj : Set.InjOn g (↑S) := by
    intro y hy y' hy' hgy
    apply funext
    intro i
    apply Subtype.ext
    have hycond : Matches s k X (x, y) := by
      simpa [S, Finset.mem_filter] using hy
    have hy'cond : Matches s k X (x, y') := by
      simpa [S, Finset.mem_filter] using hy'
    have hpow : ∀ j ≤ s, (∑ i, (xv i) ^ j) = (∑ i, ((y i).1) ^ j) := by
      intro j hj
      simpa [xv] using hycond j (le_trans hj hsk)
    have hpow' : ∀ j ≤ s, (∑ i, (xv i) ^ j) = (∑ i, ((y' i).1) ^ j) := by
      intro j hj
      simpa [xv] using hy'cond j (le_trans hj hsk)
    have hgyu : g y = Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y i).1) hpow) := by
      dsimp [g]
      rw [dif_pos hpow]
    have hgy'u : g y' = Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y' i).1) hpow') := by
      dsimp [g]
      rw [dif_pos hpow']
    have hch := Classical.choose_spec (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y i).1) hpow)
    have hch' := Classical.choose_spec (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y' i).1) hpow')
    have hval : ((y i).1) = ((y' i).1) := by
      have hyv : (y i).1 = xv ((Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y i).1) hpow)) i) := hch i
      have hy'v : (y' i).1 = xv ((Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s xv (fun i => (y' i).1) hpow')) i) := hch' i
      rw [hyv, hy'v, ← hgyu, ← hgy'u]
      rw [hgy]
    exact hval
  have hSimg : (S.image g).card = S.card := Finset.card_image_of_injOn hinj
  have hsub : S.image g ⊆ (Finset.univ : Finset (Equiv.Perm (Fin s))) := by
    intro z hz
    simp
  have hle : S.card ≤ (Finset.univ : Finset (Equiv.Perm (Fin s))).card := by
    rw [← hSimg]
    exact Finset.card_le_card hsub
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin s))).card = Nat.factorial s := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rwa [hperm] at hle



/-- In the regime `s ≤ k`, `J s k X ≤ s! · X^s`: at most `s!` partners for each
of the `X^s` possible `x`-tuples. -/
lemma J_le_factorial_mul_pow {s k X : ℕ} (hsk : s ≤ k) :
    J s k X ≤ ((Nat.factorial s) * (X ^ s) : ℕ) := by
  rw [J_eq_filter_card]
  let P := (Finset.univ.filter (fun xy : PairSpace s X => Matches s k X xy))
  let xv : PairSpace s X → Fin s → ℕ := fun xy i => (xy.1 i).1
  let g : PairSpace s X → (Fin s → Finset.Icc 1 X) × Equiv.Perm (Fin s) := fun xy =>
    if h : ∀ j ≤ s, (∑ i, (xv xy i) ^ j) = (∑ i, ((xy.2 i).1) ^ j) then
      (xy.1, Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) h))
    else (xy.1, 1)
  have hinj : Set.InjOn g (↑P) := by
    intro xy hxy xy' hxy' hg
    apply Prod.ext
    · -- first coordinates equal
      have hc : Matches s k X xy := by simpa [P, Finset.mem_filter] using hxy
      have hc' : Matches s k X xy' := by simpa [P, Finset.mem_filter] using hxy'
      have hpow : ∀ j ≤ s, (∑ i, (xv xy i) ^ j) = (∑ i, ((xy.2 i).1) ^ j) := by
        intro j hj
        simpa [xv] using hc j (le_trans hj hsk)
      have hpow' : ∀ j ≤ s, (∑ i, (xv xy' i) ^ j) = (∑ i, ((xy'.2 i).1) ^ j) := by
        intro j hj
        simpa [xv] using hc' j (le_trans hj hsk)
      have hgxy : g xy = (xy.1, Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) hpow)) := by
        dsimp [g]
        rw [dif_pos hpow]
      have hgxy' : g xy' = (xy'.1, Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy') (fun i => (xy'.2 i).1) hpow')) := by
        dsimp [g]
        rw [dif_pos hpow']
      calc
        xy.1 = (g xy).1 := by rw [hgxy]
        _ = (g xy').1 := congrArg Prod.fst hg
        _ = xy'.1 := by rw [hgxy']
    · -- second coordinates equal
      have hc : Matches s k X xy := by simpa [P, Finset.mem_filter] using hxy
      have hc' : Matches s k X xy' := by simpa [P, Finset.mem_filter] using hxy'
      have hpow : ∀ j ≤ s, (∑ i, (xv xy i) ^ j) = (∑ i, ((xy.2 i).1) ^ j) := by
        intro j hj
        simpa [xv] using hc j (le_trans hj hsk)
      have hpow' : ∀ j ≤ s, (∑ i, (xv xy' i) ^ j) = (∑ i, ((xy'.2 i).1) ^ j) := by
        intro j hj
        simpa [xv] using hc' j (le_trans hj hsk)
      have hσ : (g xy).2 = Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) hpow) := by
        dsimp [g]
        rw [dif_pos hpow]
      have hσ' : (g xy').2 = Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy') (fun i => (xy'.2 i).1) hpow') := by
        dsimp [g]
        rw [dif_pos hpow']
      have hg2 : (g xy).2 = (g xy').2 := congrArg Prod.snd hg
      have hperm : Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) hpow)
          = Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy') (fun i => (xy'.2 i).1) hpow') := by
        rw [← hσ, ← hσ']
        exact hg2
      apply funext
      intro i
      apply Subtype.ext
      have hch := Classical.choose_spec (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) hpow)
      have hch' := Classical.choose_spec (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy') (fun i => (xy'.2 i).1) hpow')
      have hfst : xy.1 = xy'.1 := by
        have hgxy : g xy = (xy.1, Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) hpow)) := by
          dsimp [g]
          rw [dif_pos hpow]
        have hgxy' : g xy' = (xy'.1, Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy') (fun i => (xy'.2 i).1) hpow')) := by
          dsimp [g]
          rw [dif_pos hpow']
        calc
          xy.1 = (g xy).1 := by rw [hgxy]
          _ = (g xy').1 := congrArg Prod.fst hg
          _ = xy'.1 := by rw [hgxy']
      have hxv_eq : xv xy = xv xy' := by
        apply funext
        intro t
        dsimp [xv]
        exact congrArg (fun f : Fin s → Finset.Icc 1 X => (f t).1) hfst
      let ch1 : Equiv.Perm (Fin s) := Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy) (fun i => (xy.2 i).1) hpow)
      let ch1' : Equiv.Perm (Fin s) := Classical.choose (Commons.Combinatorics.Fin.exists_perm_of_powerSums_eq s (xv xy') (fun i => (xy'.2 i).1) hpow')
      have hchv : (xy.2 i).1 = xv xy (ch1 i) := by simpa [ch1] using (hch i)
      have hchv' : (xy'.2 i).1 = xv xy' (ch1' i) := by simpa [ch1'] using (hch' i)
      have hperm12 : ch1 = ch1' := by
        dsimp [ch1, ch1']
        rw [← hσ, ← hσ']
        exact hg2
      calc
        (xy.2 i).1 = xv xy (ch1 i) := hchv
        _ = xv xy' (ch1 i) := congrFun hxv_eq (ch1 i)
        _ = xv xy' (ch1' i) := by rw [hperm12]
        _ = (xy'.2 i).1 := hchv'.symm
  have himg : (P.image g).card = P.card := Finset.card_image_of_injOn hinj
  have hsub : P.image g ⊆ (Finset.univ : Finset ((Fin s → Finset.Icc 1 X) × Equiv.Perm (Fin s))) := by
    intro z hz
    simp
  have hle : P.card ≤ (Finset.univ : Finset ((Fin s → Finset.Icc 1 X) × Equiv.Perm (Fin s))).card := by
    rw [← himg]
    exact Finset.card_le_card hsub
  have hcard : (Finset.univ : Finset ((Fin s → Finset.Icc 1 X) × Equiv.Perm (Fin s))).card
      = Nat.factorial s * X ^ s := by
    rw [Finset.card_univ, Fintype.card_prod]
    rw [Fintype.card_perm, Fintype.card_fin]
    rw [Fintype.card_fun, Fintype.card_fin]
    simp [Nat.card_Icc]
    ring
  rw [hcard] at hle
  exact_mod_cast hle

/-- The theorem in the regime `s ≤ k` (at least as many moments as variables). -/
theorem vmvt_short (s k : ℕ) (hsk : s ≤ k) (ε : ℝ) (hε : 0 < ε) :
    VMVT s k ε hε := by
  apply vmvt_of_eventually_le_first s k ε hε
  refine ⟨(Nat.factorial s : ℝ), by exact_mod_cast (Nat.factorial_pos s), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with X hX
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hJ : J s k X ≤ (↑(Nat.factorial s * X ^ s) : ℝ) := by
    exact_mod_cast (J_le_factorial_mul_pow (s := s) (k := k) (X := X) hsk)
  calc
    J s k X ≤ (↑(Nat.factorial s * X ^ s) : ℝ) := hJ
    _ = (Nat.factorial s : ℝ) * (↑(X ^ s) : ℝ) := by norm_num
    _ ≤ (Nat.factorial s : ℝ) * (X : ℝ) ^ (s + ε) := by
      refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast Nat.zero_le (Nat.factorial s))
      calc
        (↑(X ^ s) : ℝ) = (X : ℝ) ^ ((s : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; norm_num
        _ ≤ (X : ℝ) ^ (s + ε) := by
          apply Real.rpow_le_rpow_of_exponent_le hx1
          norm_num
          linarith
    _ = (Nat.factorial s : ℝ) * (X : ℝ) ^ (s + ε) := by rfl

end
end Submission.Vinogradov

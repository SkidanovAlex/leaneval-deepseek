import Mathlib
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.double_sum_diag
import Submission.Work.Higman.polyRep_add
import Submission.Work.Higman.bivariate_monomial_indep
import Submission.Work.Higman.frob_diag_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem bilinear_frob {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (B : F → F → F)
    (hx : ∀ y x x', B (x + x') y = B x y + B x' y)
    (hy : ∀ x y y', B x (y + y') = B x y + B x y')
    (hsym : ∀ x y, B x y = B y x) (hdiag : ∀ x, B x x = 0) :
    ∃ d : ℕ → ℕ → F, (∀ k l, d k l = d l k) ∧ (∀ k, d k k = 0) ∧
      ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        d k l * x ^ (2 ^ k) * y ^ (2 ^ l) := by
  classical
  -- coefficient of `x ^ (2 ^ k)` in the Frobenius expansion of `B · y`
  let a : ℕ → F → F := fun k y => (polyRep (fun x => B x y)).coeff (2 ^ k)
  have hA : ∀ y x, B x y = ∑ k ∈ Finset.range n, a k y * x ^ (2 ^ k) := by
    intro y x
    exact additive_frob hcard (fun x => B x y) (fun x x' => hx y x x') x
  -- additivity of each `a k`, from linearity of `polyRep`
  have ha_add : ∀ k, ∀ y y', a k (y + y') = a k y + a k y' := by
    intro k y y'
    have hp : polyRep (fun x => B x (y + y')) =
        polyRep (fun x => B x y) + polyRep (fun x => B x y') := by
      rw [show (fun x => B x (y + y')) = (fun x => B x y + B x y') from
        funext (fun x => hy x y y')]
      exact polyRep_add (fun x => B x y) (fun x => B x y')
    show (polyRep (fun x => B x (y + y'))).coeff (2 ^ k) =
      (polyRep (fun x => B x y)).coeff (2 ^ k) + (polyRep (fun x => B x y')).coeff (2 ^ k)
    rw [hp, Polynomial.coeff_add]
  -- the two-variable coefficients
  let d0 : ℕ → ℕ → F := fun k l => (polyRep (a k)).coeff (2 ^ l)
  have hd0frob : ∀ k y, a k y = ∑ l ∈ Finset.range n, d0 k l * y ^ (2 ^ l) := by
    intro k y
    show a k y = ∑ l ∈ Finset.range n, (polyRep (a k)).coeff (2 ^ l) * y ^ (2 ^ l)
    exact additive_frob hcard (a k) (ha_add k) y
  have hA2 : ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        d0 k l * x ^ (2 ^ k) * y ^ (2 ^ l) := by
    intro x y
    rw [hA y x]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hd0frob k y, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  -- symmetry of the coefficients, from `hsym`
  have hsym_d0 : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, d0 k l = d0 l k := by
    have hc := bivariate_monomial_indep hcard (fun k l => d0 k l - d0 l k)
      (by
        intro x y
        have h1 := hA2 x y
        have h2 := hA2 y x
        have hs := hsym x y
        rw [h1, h2] at hs
        have hN : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              d0 k l * y ^ (2 ^ k) * x ^ (2 ^ l))
            = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              d0 l k * x ^ (2 ^ k) * y ^ (2 ^ l) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
          ring
        have hgoal : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              d0 k l * x ^ (2 ^ k) * y ^ (2 ^ l))
            = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              d0 l k * x ^ (2 ^ k) * y ^ (2 ^ l) := hs.trans hN
        have hsplit : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              (d0 k l - d0 l k) * x ^ (2 ^ k) * y ^ (2 ^ l))
            = (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
                d0 k l * x ^ (2 ^ k) * y ^ (2 ^ l))
              - (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
                d0 l k * x ^ (2 ^ k) * y ^ (2 ^ l)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
        rw [hsplit, hgoal, sub_self])
    intro k hk l hl
    exact sub_eq_zero.mp (hc k hk l hl)
  -- vanishing of the diagonal coefficients, from `hdiag`
  have hdiag_d0 : ∀ k ∈ Finset.range n, d0 k k = 0 := by
    have hsum : ∀ x : F, ∑ k ∈ Finset.range n, d0 k k * x ^ (2 ^ (k + 1)) = 0 := by
      intro x
      have hbz : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            d0 k l * x ^ (2 ^ k) * x ^ (2 ^ l)) = 0 := by
        have h := hA2 x x
        rw [hdiag x] at h
        exact h.symm
      have hg_sym : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n,
          d0 k l * x ^ (2 ^ k) * x ^ (2 ^ l) = d0 l k * x ^ (2 ^ l) * x ^ (2 ^ k) := by
        intro k hk l hl
        rw [hsym_d0 k hk l hl]
        ring
      have hds := double_sum_diag (Finset.range n)
        (fun k l => d0 k l * x ^ (2 ^ k) * x ^ (2 ^ l)) hg_sym
      rw [hds] at hbz
      have hconv : (∑ k ∈ Finset.range n, d0 k k * x ^ (2 ^ k) * x ^ (2 ^ k))
          = ∑ k ∈ Finset.range n, d0 k k * x ^ (2 ^ (k + 1)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [mul_assoc, ← pow_add,
          show 2 ^ k + 2 ^ k = 2 ^ (k + 1) from by rw [pow_succ]; ring]
      rw [hconv] at hbz
      exact hbz
    exact frob_diag_zero hcard (fun k => d0 k k) hsum
  -- extend the coefficients to all of `ℕ × ℕ` by zero, to satisfy the global clauses
  let d : ℕ → ℕ → F := fun k l => if k < n ∧ l < n then d0 k l else 0
  refine ⟨d, ?_, ?_, ?_⟩
  · intro k l
    show (if k < n ∧ l < n then d0 k l else 0)
        = (if l < n ∧ k < n then d0 l k else 0)
    by_cases hkl : k < n ∧ l < n
    · rw [if_pos hkl, if_pos ⟨hkl.2, hkl.1⟩]
      exact hsym_d0 k (Finset.mem_range.mpr hkl.1) l (Finset.mem_range.mpr hkl.2)
    · rw [if_neg hkl, if_neg (fun h => hkl ⟨h.2, h.1⟩)]
  · intro k
    show (if k < n ∧ k < n then d0 k k else 0) = 0
    by_cases hk : k < n
    · rw [if_pos ⟨hk, hk⟩]
      exact hdiag_d0 k (Finset.mem_range.mpr hk)
    · rw [if_neg (fun h => hk h.1)]
  · intro x y
    rw [hA2 x y]
    refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => ?_))
    have hk' : k < n := Finset.mem_range.mp hk
    have hl' : l < n := Finset.mem_range.mp hl
    show d0 k l * x ^ (2 ^ k) * y ^ (2 ^ l)
        = (if k < n ∧ l < n then d0 k l else 0) * x ^ (2 ^ k) * y ^ (2 ^ l)
    rw [if_pos ⟨hk', hl'⟩]

end Work.Higman

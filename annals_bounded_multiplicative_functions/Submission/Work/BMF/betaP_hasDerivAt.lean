import Mathlib
import Submission.Work.BMF.exp_sum_taylor_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- **Chain rule for the Heath–Brown remainder function.**  For `f` of class `C^k` (`k ≥ 2`) on
the open interval `(0,N)`, with `n ≥ 1`, `n + L < N` and `t ∈ [1,L]`, the function
`betaP k f n t = f (n+t) - tayP k f n t` is differentiable at `t` with derivative
`f'(n+t) - Σ_{i ∈ range (k-1)} f^{(i+1)}(n) t^i / i!`. -/
theorem betaP_hasDerivAt (k : ℕ) (hk : 2 ≤ k) {N : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ k f (Set.Ioo (0:ℝ) (N:ℝ)))
    {n L : ℕ} (hn : 1 ≤ n) (hnL : n + L < N) {t : ℝ} (ht : t ∈ Set.Icc (1:ℝ) L) :
    HasDerivAt (betaP k f (n:ℝ))
      (deriv f ((n:ℝ) + t) -
        ∑ i ∈ Finset.range (k - 1),
          iteratedDeriv (i + 1) f (n:ℝ) * t ^ i / (Nat.factorial i : ℝ)) t := by
  -- `n + t` lies in the open interval `(0, N)` on which `f` is `C^k`.
  have hx : (n:ℝ) + t ∈ Set.Ioo (0:ℝ) (N:ℝ) := by
    refine ⟨?_, ?_⟩
    · have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith [ht.1]
    · have h2 : (n:ℝ) + (L:ℝ) < (N:ℝ) := by exact_mod_cast hnL
      linarith [ht.2]
  -- `f` is differentiable at `n + t`, since `k ≥ 1`.
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hd : HasDerivAt f (deriv f ((n:ℝ)+t)) ((n:ℝ)+t) :=
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt hk0).hasDerivAt
  -- Derivative of `s ↦ f (n + s)`.
  have h1 : HasDerivAt (fun s : ℝ => f ((n:ℝ)+s)) (deriv f ((n:ℝ)+t)) t :=
    hd.comp_const_add (n:ℝ) t
  -- Derivative of the Taylor polynomial, term by term.
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ i ∈ Finset.range (k-1),
        iteratedDeriv (i+1) f (n:ℝ) * s^(i+1) / (Nat.factorial (i+1):ℝ))
      (∑ i ∈ Finset.range (k-1),
        iteratedDeriv (i+1) f (n:ℝ) * ((i:ℝ)+1) * t^i / (Nat.factorial (i+1):ℝ)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hp : HasDerivAt (fun s : ℝ => iteratedDeriv (i+1) f (n:ℝ) * s^(i+1))
        (iteratedDeriv (i+1) f (n:ℝ) * (((i+1:ℕ):ℝ) * t^((i+1)-1))) t :=
      (hasDerivAt_pow (i+1) t).const_mul _
    refine (hp.div_const ((Nat.factorial (i+1):ℝ))).congr_deriv ?_
    rw [Nat.add_sub_cancel]; push_cast; ring
  -- Rewrite the derivative of the `i`-th term using `(i+1)! = (i+1) * i!`.
  have key : (∑ i ∈ Finset.range (k-1),
      iteratedDeriv (i+1) f (n:ℝ) * ((i:ℝ)+1) * t^i / (Nat.factorial (i+1):ℝ))
      = ∑ i ∈ Finset.range (k-1),
      iteratedDeriv (i+1) f (n:ℝ) * t^i / (Nat.factorial i :ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hfac : (Nat.factorial (i+1) : ℝ) = ((i:ℝ)+1) * (Nat.factorial i : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    have h2 : ((i:ℝ)+1) ≠ 0 := by positivity
    have h3 : (Nat.factorial i : ℝ) ≠ 0 := by positivity
    field_simp
  have hsum' : HasDerivAt (tayP k f (n:ℝ))
      (∑ i ∈ Finset.range (k-1),
        iteratedDeriv (i+1) f (n:ℝ) * t^i / (Nat.factorial i :ℝ)) t := by
    rw [show tayP k f (n:ℝ) = (fun s : ℝ => ∑ i ∈ Finset.range (k-1),
        iteratedDeriv (i+1) f (n:ℝ) * s^(i+1) / (Nat.factorial (i+1):ℝ)) from by
      ext s; simp [tayP]]
    exact hsum.congr_deriv key
  have hfin : HasDerivAt (fun s : ℝ => f ((n:ℝ)+s) - tayP k f (n:ℝ) s)
      (deriv f ((n:ℝ)+t) - ∑ i ∈ Finset.range (k-1),
        iteratedDeriv (i+1) f (n:ℝ) * t^i / (Nat.factorial i :ℝ)) t :=
    h1.sub hsum'
  rw [show betaP k f (n:ℝ) = (fun s : ℝ => f ((n:ℝ)+s) - tayP k f (n:ℝ) s) from by
    ext s; simp [betaP]]
  exact hfin

end Work.BMF

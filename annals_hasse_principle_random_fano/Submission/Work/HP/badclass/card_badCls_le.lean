import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.density_aux
import Submission.Work.HP.badclass.BadDefs
import Submission.Work.HP.badclass.eval_ker
import Submission.Work.HP.badclass.grad_ker
import Submission.Work.HP.badclass.pair_ker
import Submission.Work.HP.badclass.chebyshev
import Submission.Work.HP.badclass.sum_Mval
import Submission.Work.HP.badclass.sum_Mval_sq
import Submission.Work.HP.badclass.resonant_card
import Submission.Work.HP.badclass.torus_card
import Submission.Work.HP.badclass.arith

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.badclass


/-- The number of coefficient classes having `x` as a nonsingular zero is at most `p^{N-1}`. -/
private lemma Dset_ncard_le {d n p N : ℕ} [NeZero p] (hp : p.Prime) (hN : N = Work.HP.NN d n)
    (x : Fin (n + 1) → ZMod p) (hx : ∀ i, x i ≠ 0) :
    (Work.HP.Dset d n p x).ncard ≤ p ^ (N - 1) := by
  have h1 := eval_ker d n p hp x hx
  have h2 : (Work.HP.Dset d n p x).ncard ≤
      ({a : Work.HP.Mon d n → ZMod p | Work.HP.formEvalZMod d n p a x = 0}).ncard := by
    apply Set.ncard_mono
    intro a ha
    simp only [Work.HP.Dset, Set.mem_ofPred_eq] at ha
    exact ha.1
  rw [h1, ← hN] at h2
  exact h2

/-- The number of coefficient classes having `x` as a nonsingular zero is at least
`p^{N-1} - p^{N-(n+1)}` when `p ∤ d`. -/
private lemma Dset_ncard_ge {d n p N : ℕ} [NeZero p] (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 1 ≤ d)
    (hN : N = Work.HP.NN d n) (x : Fin (n + 1) → ZMod p) (hx : ∀ i, x i ≠ 0) :
    p ^ (N - 1) - p ^ (N - (n + 1)) ≤ (Work.HP.Dset d n p x).ncard := by
  have hA := eval_ker d n p hp x hx
  have hB := grad_ker d n p hp hd hpd x hx
  rw [← hN] at hA hB
  set A : Set (Work.HP.Mon d n → ZMod p) :=
    {a | Work.HP.formEvalZMod d n p a x = 0} with hAdef
  set B : Set (Work.HP.Mon d n → ZMod p) :=
    {a | ∀ i, Work.HP.gradZ d n p a i x = 0} with hBdef
  have hAnc : A.ncard = p ^ (N - 1) := by rw [hAdef]; exact hA
  have hBnc : B.ncard = p ^ (N - (n + 1)) := by rw [hBdef]; exact hB
  have hsub : A \ B ⊆ Work.HP.Dset d n p x := by
    intro a ha
    simp only [Set.mem_sdiff, hAdef, Set.mem_ofPred_eq] at ha
    refine ⟨ha.1, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact ha.2 hcon
  have h1 : (A \ B).ncard ≤ (Work.HP.Dset d n p x).ncard := Set.ncard_mono hsub
  have h2 : (A \ B).ncard = A.ncard - (A ∩ B).ncard := by
    rw [show A \ B = A \ (A ∩ B) by
      ext a; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto]
    exact Set.ncard_sdiff Set.inter_subset_left (Set.finite_univ.subset (Set.subset_univ _))
  have h3 : (A ∩ B).ncard ≤ p ^ (N - (n + 1)) := by
    have h4 := Set.ncard_mono (Set.inter_subset_right :
      A ∩ B ⊆ B)
    rwa [hBnc] at h4
  rw [h2, hAnc] at h1
  omega

/-- The number of torus points collinear with `x` is at most `p`. -/
private lemma resonant_card_le (n p : ℕ) [NeZero p] (x : Fin (n + 1) → ZMod p) :
    (((Work.HP.torFinset n p).filter (fun y => ∃ z : ZMod p, y = z • x)).card : ℝ) ≤ p := by
  exact_mod_cast resonant_card n p x

/-- The second-moment bound on the number of classes with no nonsingular `F_p`-zero. -/
private lemma moment_bound (d n p N : ℕ) [NeZero p] (hp : p.Prime) (hpd : ¬ p ∣ d) (hd : 1 ≤ d)
    (hN : N = Work.HP.NN d n) (hNge : n + 1 ≤ N) (hn : 3 ≤ n) (hp2 : 2 ≤ p) :
    (({a : Work.HP.Mon d n → ZMod p | Work.HP.Mval d n p a = 0}).ncard : ℝ) ≤
      (2 ^ (n + 2) + 4) * (p : ℝ) ^ (N - n + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  set m : ℝ := ((Work.HP.torFinset n p).card : ℝ) with hmdef
  have hmval : ((Work.HP.torFinset n p).card : ℕ) = (p - 1) ^ (n + 1) := torus_card n p
  have hmpos : 0 < m := by
    rw [hmdef, hmval, Nat.cast_pow]
    have : (0:ℝ) < ((p - 1 : ℕ) : ℝ) := by
      have h : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
      rw [h]; linarith
    exact pow_pos this _
  have hm_lb : ((p : ℝ) / 2) ^ (n + 1) ≤ m := by
    rw [hmdef, hmval, Nat.cast_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ (n + 1)
    have h : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
    rw [h]; linarith
  set S : ℝ := ∑ a : Work.HP.Mon d n → ZMod p, (Work.HP.Mval d n p a : ℝ) with hSdef
  set T : ℝ := ∑ a : Work.HP.Mon d n → ZMod p, ((Work.HP.Mval d n p a : ℝ)) ^ 2 with hTdef
  set q : ℝ := (p : ℝ) ^ N with hqdef
  have hcardq : ((Fintype.card (Work.HP.Mon d n → ZMod p) : ℕ) : ℝ) = q := by
    rw [hqdef, hN, Fintype.card_fun, ZMod.card, Nat.cast_pow]
  -- first moment
  have hS_eq : S = ∑ x ∈ Work.HP.torFinset n p, ((Work.HP.Dset d n p x).ncard : ℝ) := by
    rw [hSdef, ← Nat.cast_sum, sum_Mval]
    push_cast
    rfl
  have hS_lb : m * ((p : ℝ) ^ (N - 1) - (p : ℝ) ^ (N - (n + 1))) ≤ S := by
    rw [hS_eq, hmdef]
    have h1 : ((Work.HP.torFinset n p).card : ℝ)
          * ((p : ℝ) ^ (N - 1) - (p : ℝ) ^ (N - (n + 1)))
        = ∑ _x ∈ Work.HP.torFinset n p,
            ((p : ℝ) ^ (N - 1) - (p : ℝ) ^ (N - (n + 1))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    apply Finset.sum_le_sum
    intro x hx
    have hxt : ∀ i, x i ≠ 0 := by
      simpa only [Work.HP.torFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hcast : ((p ^ (N - 1) - p ^ (N - (n + 1)) : ℕ) : ℝ)
        = (p : ℝ) ^ (N - 1) - (p : ℝ) ^ (N - (n + 1)) := by
      rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) (by omega)), Nat.cast_pow, Nat.cast_pow]
    rw [← hcast]
    exact_mod_cast Dset_ncard_ge hp hpd hd hN x hxt
  -- second moment
  have hT_eq : T = ∑ x ∈ Work.HP.torFinset n p, ∑ y ∈ Work.HP.torFinset n p,
      (((Work.HP.Dset d n p x) ∩ (Work.HP.Dset d n p y)).ncard : ℝ) := by
    rw [hTdef]
    rw [show (∑ a : Work.HP.Mon d n → ZMod p, ((Work.HP.Mval d n p a : ℝ)) ^ 2)
        = ((∑ a : Work.HP.Mon d n → ZMod p, Work.HP.Mval d n p a ^ 2 : ℕ) : ℝ) by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [Nat.cast_pow])]
    rw [sum_Mval_sq]
    push_cast
    rfl
  have hinner : ∀ x ∈ Work.HP.torFinset n p,
      ∑ y ∈ Work.HP.torFinset n p,
        (((Work.HP.Dset d n p x) ∩ (Work.HP.Dset d n p y)).ncard : ℝ)
      ≤ m * (p : ℝ) ^ (N - 2) + (p : ℝ) * (p : ℝ) ^ (N - 1) := by
    intro x hx
    have hxt : ∀ i, x i ≠ 0 := by
      simpa only [Work.HP.torFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    have hpair : ∀ y ∈ Work.HP.torFinset n p,
        (((Work.HP.Dset d n p x) ∩ (Work.HP.Dset d n p y)).ncard : ℝ)
          ≤ (p : ℝ) ^ (N - 2)
            + (if ∃ z : ZMod p, y = z • x then (p : ℝ) ^ (N - 1) else 0) := by
      intro y hy
      have hyt : ∀ i, y i ≠ 0 := by
        simpa only [Work.HP.torFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hy
      by_cases hres : ∃ z : ZMod p, y = z • x
      · rw [if_pos hres]
        have h1 : ((Work.HP.Dset d n p x ∩ Work.HP.Dset d n p y).ncard : ℝ)
            ≤ (p : ℝ) ^ (N - 1) := by
          have h2 := Set.ncard_mono (Set.inter_subset_left :
            Work.HP.Dset d n p x ∩ Work.HP.Dset d n p y ⊆ Work.HP.Dset d n p x)
          exact_mod_cast le_trans h2 (Dset_ncard_le hp hN x hxt)
        linarith [(by positivity : (0:ℝ) ≤ (p : ℝ) ^ (N - 2))]
      · rw [if_neg hres]
        have hpk := pair_ker d n p hp hd (by omega) x y hxt hyt hres
        rw [← hN] at hpk
        have h2 : (Work.HP.Dset d n p x ∩ Work.HP.Dset d n p y).ncard
            ≤ ({a : Work.HP.Mon d n → ZMod p |
                Work.HP.formEvalZMod d n p a x = 0 ∧
                Work.HP.formEvalZMod d n p a y = 0}).ncard := by
          apply Set.ncard_mono
          intro a ha
          simp only [Set.mem_inter_iff, Work.HP.Dset, Set.mem_ofPred_eq] at ha
          exact ⟨ha.1.1, ha.2.1⟩
        rw [hpk] at h2
        exact_mod_cast h2
    have h2 : ∑ y ∈ Work.HP.torFinset n p,
        (((Work.HP.Dset d n p x) ∩ (Work.HP.Dset d n p y)).ncard : ℝ)
        ≤ ∑ y ∈ Work.HP.torFinset n p,
          ((p : ℝ) ^ (N - 2)
            + (if ∃ z : ZMod p, y = z • x then (p : ℝ) ^ (N - 1) else 0)) :=
      Finset.sum_le_sum (fun y hy => hpair y hy)
    refine le_trans h2 ?_
    rw [Finset.sum_add_distrib]
    have h3 : (∑ _y ∈ Work.HP.torFinset n p, (p : ℝ) ^ (N - 2))
        = m * (p : ℝ) ^ (N - 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← hmdef]
    have h4 : (∑ y ∈ Work.HP.torFinset n p,
        (if ∃ z : ZMod p, y = z • x then (p : ℝ) ^ (N - 1) else 0))
        ≤ (p : ℝ) * (p : ℝ) ^ (N - 1) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (resonant_card_le n p x) (by positivity)
    rw [h3]
    linarith [h4]
  have hT_ub : T ≤ m * (m * (p : ℝ) ^ (N - 2) + q) := by
    rw [hT_eq]
    calc ∑ x ∈ Work.HP.torFinset n p, ∑ y ∈ Work.HP.torFinset n p,
          (((Work.HP.Dset d n p x) ∩ (Work.HP.Dset d n p y)).ncard : ℝ)
        ≤ ∑ _x ∈ Work.HP.torFinset n p,
            (m * (p : ℝ) ^ (N - 2) + (p : ℝ) * (p : ℝ) ^ (N - 1)) :=
          Finset.sum_le_sum (fun x hx => hinner x hx)
      _ = ((Work.HP.torFinset n p).card : ℝ)
            * (m * (p : ℝ) ^ (N - 2) + (p : ℝ) * (p : ℝ) ^ (N - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = m * (m * (p : ℝ) ^ (N - 2) + q) := by
          have hpN : (p : ℝ) * (p : ℝ) ^ (N - 1) = (p : ℝ) ^ N := by
            rw [← pow_succ', show N - 1 + 1 = N by omega]
          rw [hqdef, hpN, ← hmdef]
  -- Chebyshev
  have hchev := chebyshev (fun a : Work.HP.Mon d n → ZMod p => Work.HP.Mval d n p a)
  rw [hcardq] at hchev
  have hM0 : (({a : Work.HP.Mon d n → ZMod p | Work.HP.Mval d n p a = 0}).ncard : ℝ)
      ≤ ((Finset.univ.filter (fun a => Work.HP.Mval d n p a = 0)).card : ℝ) := by
    have h : (Finset.univ.filter (fun a : Work.HP.Mon d n → ZMod p =>
        a ∈ ({a : Work.HP.Mon d n → ZMod p | Work.HP.Mval d n p a = 0} : Set _)))
        = Finset.univ.filter (fun a => Work.HP.Mval d n p a = 0) := by
      ext a; simp
    rw [Work.HP.ncard_eq_filter_card, h]
  have hchev' : (({a : Work.HP.Mon d n → ZMod p | Work.HP.Mval d n p a = 0}).ncard : ℝ)
      * S ^ 2 ≤ q * (q * T - S ^ 2) := by
    have h1 : ((Finset.univ.filter (fun a => Work.HP.Mval d n p a = 0)).card : ℝ) * S ^ 2
        ≤ q * (q * T - S ^ 2) := hchev
    nlinarith [hM0, sq_nonneg S, h1]
  exact arith_step hn hNge (by exact_mod_cast hp2) hm_lb hmpos hS_lb hT_ub hqdef hchev'

/-- Paucity of the `p`-adic "bad" classes (the design's `|B_p| ≪ p^{N−(n−1)}`, matching the
paper's "second moment sigma" lemma): there is a constant `C > 0`, depending only on `d, n`, such
that for every prime `p` the number of coefficient classes mod `p` whose reduction has no
nonsingular `F_p`-zero is at most `C · p^(N − (n−1))` — i.e. its density is `O(p ^ (−(n−1)))`,
uniformly in `p`.  Here `N = NN d n` is the number of monomials and `BadCls d n p a` says that
every nonzero `F_p`-zero of the reduction of `f_a` is singular.

Route (note: the exponent `−(n−1)` is sharp-ish — at `(d,n) = (2,3)` the count is `≍ p^{N−2}` —
and the additional power of `p` relative to `p^{N−n}` comes from the over-dispersion of the
number of nonsingular zeros): let `N'(a) = #{x ≠ 0 in F_p^(n+1) : f_a(x) = 0 and ∇f_a(x) ≠ 0}`,
so that `BadCls` is the complement of `{a : N'(a) ≥ 1}`.  For a fixed `x ≠ 0` the map
`a ↦ (f_a(x), ∂_0 f_a(x), …, ∂_n f_a(x))` is linear of rank `≥ n+1`, and `a ↦ f_a(x)` is a nonzero
functional (the monomial `x_i^d` is nonzero when `x_i ≠ 0`), so
`P(f_a(x) = 0 ∧ ∇f_a(x) ≠ 0) = 1/p − O(p^{−(n+1)})` and `𝔼[N'] = p^n(1 + O(1/p))`.  The second
moment is `𝔼[N'²] = (𝔼[N'])²(1 + Θ(p^{−(n−1)}))`: the pairs `(x,y)` with `ν(x) ∝ ν(y)`
(equivalently `y = zx` with `z ∈ F_p^×`, or more generally `y_i = ζ_i x_i` with `ζ_i^d` independent
of `i`) contribute `O(p^{n+1})`, all other pairs contributing `P(x)·P(y)(1 + O(p^{−(n+1)}))`.
Hence `Var(N') = O(p^{n+1})` and Chebyshev gives `P(N'(a) = 0) ≤ Var(N')/𝔼[N']² = O(p^{−(n−1)})`,
which is the claim.  Only `n ≥ 3` is used, to make `p^{−(n−1)}` summable over the primes. -/
theorem card_badCls_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime →
      (({a : Mon d n → ZMod p | BadCls d n p a}.ncard : ℝ))
      ≤ C * (p : ℝ) ^ NN d n / (p : ℝ) ^ (n - 1) := by
  classical
  refine ⟨max ((2:ℝ) ^ (n + 3) + 4) (((max d 2 : ℕ) : ℝ) ^ (n - 1)), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  · intro p hp
    by_cases hsmall : p ≤ max d 2
    · -- small primes: the trivial bound suffices
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hpN : ({a : Work.HP.Mon d n → ZMod p | BadCls d n p a}.ncard : ℝ)
          ≤ (p : ℝ) ^ (Work.HP.NN d n) := by
        have h1 : {a : Work.HP.Mon d n → ZMod p | BadCls d n p a}.ncard
            ≤ (Finset.univ : Finset (Work.HP.Mon d n → ZMod p)).card := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_mono (by rw [Finset.coe_univ]; exact Set.subset_univ _)
        have h2 : (Finset.univ : Finset (Work.HP.Mon d n → ZMod p)).card
            = p ^ Work.HP.NN d n := by
          rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
        exact_mod_cast h1.trans_eq h2
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      have hmono : (p : ℝ) ^ (n - 1) ≤ ((max d 2 : ℕ) : ℝ) ^ (n - 1) :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsmall) (n - 1)
      have hCge : (p : ℝ) ^ (n - 1)
          ≤ max ((2:ℝ) ^ (n + 3) + 4) (((max d 2 : ℕ) : ℝ) ^ (n - 1)) :=
        hmono.trans (le_max_right _ _)
      have hpos : 0 < (p : ℝ) ^ (n - 1) := by positivity
      calc ({a : Work.HP.Mon d n → ZMod p | BadCls d n p a}.ncard : ℝ)
          ≤ (p : ℝ) ^ (Work.HP.NN d n) := hpN
        _ = (p : ℝ) ^ (Work.HP.NN d n) * ((p : ℝ) ^ (n - 1) / (p : ℝ) ^ (n - 1)) := by
              rw [div_self (ne_of_gt hpos), mul_one]
        _ ≤ (p : ℝ) ^ (Work.HP.NN d n) * (max ((2:ℝ) ^ (n + 3) + 4)
              (((max d 2 : ℕ) : ℝ) ^ (n - 1)) / (p : ℝ) ^ (n - 1)) := by
              apply mul_le_mul_of_nonneg_left
              · exact div_le_div_of_nonneg_right hCge (le_of_lt hpos)
              · positivity
        _ = max ((2:ℝ) ^ (n + 3) + 4) (((max d 2 : ℕ) : ℝ) ^ (n - 1))
              * (p : ℝ) ^ (Work.HP.NN d n) / (p : ℝ) ^ (n - 1) := by ring
    · -- large primes: the second-moment bound
      have hp2 : 2 ≤ p := hp.two_le
      have hpgt : max d 2 < p := lt_of_not_ge hsmall
      have hpd : ¬ p ∣ d := by
        intro hdiv
        have hle : p ≤ d := Nat.le_of_dvd (by omega) hdiv
        omega
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hsub : {a : Work.HP.Mon d n → ZMod p | BadCls d n p a} ⊆
          {a : Work.HP.Mon d n → ZMod p | Work.HP.Mval d n p a = 0} := by
        intro a ha
        exact Work.HP.Mval_eq_zero_of_badCls d n p a ha
      have hNge : n + 1 ≤ Work.HP.NN d n := Work.HP.le_NN d n (by omega)
      have hmain := moment_bound d n p (Work.HP.NN d n) hp hpd (by omega) rfl hNge hn hp2
      have hexp : Work.HP.NN d n - n + 1 = Work.HP.NN d n - (n - 1) := by omega
      have hle : ({a : Work.HP.Mon d n → ZMod p | BadCls d n p a}.ncard : ℝ)
          ≤ (2 ^ (n + 2) + 4) * (p : ℝ) ^ (Work.HP.NN d n - (n - 1)) := by
        have h1 : ({a : Work.HP.Mon d n → ZMod p | BadCls d n p a}.ncard : ℝ)
            ≤ ({a : Work.HP.Mon d n → ZMod p | Work.HP.Mval d n p a = 0}.ncard : ℝ) :=
          by exact_mod_cast Set.ncard_mono hsub
        refine le_trans h1 ?_
        rw [← hexp]
        exact hmain
      refine le_trans hle ?_
      have hC : (2 ^ (n + 2) + 4 : ℝ)
          ≤ max ((2:ℝ) ^ (n + 3) + 4) (((max d 2 : ℕ) : ℝ) ^ (n - 1)) := by
        refine le_trans ?_ (le_max_left _ _)
        have h : (2:ℝ) ^ (n + 2) ≤ 2 ^ (n + 3) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      calc (2 ^ (n + 2) + 4) * (p : ℝ) ^ (Work.HP.NN d n - (n - 1))
          ≤ max ((2:ℝ) ^ (n + 3) + 4) (((max d 2 : ℕ) : ℝ) ^ (n - 1))
              * (p : ℝ) ^ (Work.HP.NN d n - (n - 1)) :=
            mul_le_mul_of_nonneg_right hC (by positivity)
        _ = max ((2:ℝ) ^ (n + 3) + 4) (((max d 2 : ℕ) : ℝ) ^ (n - 1))
              * (p : ℝ) ^ (Work.HP.NN d n) / (p : ℝ) ^ (n - 1) := by
            have hps : (p : ℝ) ^ (Work.HP.NN d n - (n - 1))
                = (p : ℝ) ^ (Work.HP.NN d n) / (p : ℝ) ^ (n - 1) := by
              rw [eq_div_iff (by positivity : (p:ℝ) ^ (n-1) ≠ 0), ← pow_add]
              congr 1
              omega
            rw [hps, mul_div_assoc]

end Work.HP.badclass

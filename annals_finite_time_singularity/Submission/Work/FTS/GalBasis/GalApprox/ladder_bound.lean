import Mathlib
import Submission.Work.FTS.GalBasis.PolyApprox.exists_contDiffOn_Ioo_of_contDiffAt_Icc
import Submission.Work.FTS.GalBasis.PolyApprox.continuousOn_iteratedDeriv_of_contDiffOn_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.GalBasis.GalApprox.ladder_bound`

The sharp Taylor ladder with Lagrange remainder:  if `H` is `C^4` at every point of `[a,b]`
and `|H⁗| ≤ M` there, then for every `i ≤ 4` and `x ∈ [a,b]` the `i`-th derivative of `H` at `x`
differs from the `i`-th derivative (at `x`) of the order-`3` Taylor polynomial of `H` at `a`
by at most `M * (b - a)^(4-i) / (4-i)!`.

The proof has three parts.

* The Taylor polynomial `T y = ∑_{k<4} H^{(k)}(a)/k! * (y-a)^k` has `i`-th derivative
  `T^{(i)} x = ∑_{s ∈ Icc i 3} H^{(s)}(a) * (x-a)^(s-i)/(s-i)!`
  (`iteratedDeriv_sum_pow_sub_gal` computes the iterated derivatives of a finite combination of
  powers and the range-`4` sum is truncated at `i` because `k.descFactorial i = 0` for `k < i`),
  and `T⁗ = 0` while `T^{(i)}(a) = H^{(i)}(a)` for `i ≤ 3`.
* `h := H - T` therefore has `h^{(i)}(a) = 0` for `i ≤ 3` and `|h⁗| ≤ M` on `[a,b]`; and the
  difference appearing in the statement is exactly `h^{(i)}(x)`.
* The sharp ladder `|h^{(i)} x| ≤ M (x-a)^(4-i)/(4-i)!` is proved one step at a time
  (`ladder_step_gen`): downward induction from `i = 4` to `i = 0`, each step being Rolle's
  theorem applied to `t ↦ h^{(i)} t - c (t-a)^n` with `c = h^{(i)} x/(x-a)^n`.
  (This is the classical "cleverly weighted Rolle" proof of the Lagrange remainder, and it is
  what gives the sharp `1/(4-i)!` factor that a naive repeated mean value bound loses.)
-/

noncomputable section

open Set Finset Filter
open scoped Topology

namespace Work.FTS.GalBasis.GalApprox

set_option linter.unnecessarySeqFocus false

/-! ## Iterated derivatives of a finite combination of powers of `(y - a)` -/

/-- The iterated derivatives of `y ↦ ∑ k ∈ s, c k * (y - a) ^ k`:  the sum is differentiated
termwise and `iteratedDeriv i (y ↦ (y - a) ^ k) x = k.descFactorial i * (x - a) ^ (k - i)`. -/
theorem iteratedDeriv_sum_pow_sub_gal (s : Finset ℕ) (c : ℕ → ℝ) (a : ℝ) (i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun y => ∑ k ∈ s, c k * (y - a) ^ k) x
      = ∑ k ∈ s, c k * ((k.descFactorial i : ℝ) * (x - a) ^ (k - i)) := by
  rw [iteratedDeriv_fun_sum (I := s) (f := fun k y => c k * (y - a) ^ k) (x := x) (n := i)]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [iteratedDeriv_const_mul_field]
    congr 1
    have h := congr_fun (iteratedDeriv_comp_sub_const (𝕜 := ℝ) i (fun y : ℝ => y ^ k) a) x
    rw [h, iteratedDeriv_pow]
  · intro k _hk
    fun_prop

/-! ## An elementary fact about iterated derivatives on an open interval -/

private lemma diffOn_iteratedDeriv_of_contDiffOn_Ioo {c d : ℝ} {h : ℝ → ℝ}
    (hC : ContDiffOn ℝ 4 h (Set.Ioo c d)) {i : ℕ} (hi : i < 4) :
    DifferentiableOn ℝ (iteratedDeriv i h) (Set.Ioo c d) := by
  have hilt : ((i : ℕ) : WithTop ℕ∞) < (4 : WithTop ℕ∞) := by exact_mod_cast hi
  have hd := hC.differentiableOn_iteratedDerivWithin hilt isOpen_Ioo.uniqueDiffOn
  exact hd.congr (fun y hy => (iteratedDerivWithin_of_isOpen isOpen_Ioo hy).symm)

/-! ## One step of the ladder: Rolle's theorem with the power weight -/

/-- **One rung of the sharp Taylor ladder.**  Let `h` be `C^4` on an open interval containing
`[a,b]`, let `h^{(j)}(a) = 0` and suppose the bound
`|h^{(j+1)} y| ≤ M (y-a)^(n-1)/(n-1)!` holds on `[a,b]`, where `j + n = 4` and `1 ≤ n`.
Then `|h^{(j)} x| ≤ M (x-a)^n/n!` on `[a,b]`.

This is the classical proof of the Lagrange form of the Taylor remainder: if
`c := h^{(j)} x/(x-a)^n` then `t ↦ h^{(j)} t - c (t-a)^n` vanishes at `a` and at `x`, so some
`ξ ∈ (a,x)` is a stationary point; there the two derivatives
`h^{(j+1)} ξ` and `c n (ξ-a)^{n-1}` agree, and the induction hypothesis at `ξ` gives the sharp
bound for `c`. -/
private lemma ladder_step_gen {c d a b M : ℝ} {h : ℝ → ℝ} {j n : ℕ}
    (hjn : j + n = 4) (hn : 1 ≤ n)
    (hC : ContDiffOn ℝ 4 h (Set.Ioo c d)) (hsub : Set.Icc a b ⊆ Set.Ioo c d)
    (h0 : iteratedDeriv j h a = 0)
    (hprev : ∀ y ∈ Set.Icc a b,
      |iteratedDeriv (j + 1) h y| ≤ M * (y - a) ^ (n - 1) / ((n - 1).factorial : ℝ)) :
    ∀ x ∈ Set.Icc a b,
      |iteratedDeriv j h x| ≤ M * (x - a) ^ n / (n.factorial : ℝ) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hax
  · subst hxa
    rw [h0, sub_self, zero_pow (by omega : n ≠ 0)]
    simp
  · have hj4 : j ≤ 4 := by omega
    have hj3 : j < 4 := by omega
    set cc : ℝ := iteratedDeriv j h x / (x - a) ^ n with hcc
    have hccx : cc * (x - a) ^ n = iteratedDeriv j h x := by
      rw [hcc, div_mul_cancel₀ _ (pow_ne_zero _ (by linarith))]
    have hFa : (fun t : ℝ => iteratedDeriv j h t - cc * (t - a) ^ n) a = 0 := by
      simp only [h0, sub_self, zero_pow (by omega : n ≠ 0), mul_zero]
    have hFx : (fun t : ℝ => iteratedDeriv j h t - cc * (t - a) ^ n) x = 0 := by
      simp only [hccx, sub_self]
    have hcont : ContinuousOn (fun t : ℝ => iteratedDeriv j h t - cc * (t - a) ^ n)
        (Set.Icc a x) := by
      refine ContinuousOn.sub ?_ ?_
      · exact Work.FTS.GalBasis.PolyApprox.continuousOn_iteratedDeriv_of_contDiffOn_Ioo hC
          (fun y hy => hsub ⟨hy.1, hy.2.trans hx.2⟩) hj4
      · fun_prop
    obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero hax hcont (hFa.trans hFx.symm)
    have hξab : ξ ∈ Set.Icc a b := ⟨le_of_lt hξ.1, hξ.2.le.trans hx.2⟩
    have hξIoo : ξ ∈ Set.Ioo c d := hsub hξab
    have hderivi : HasDerivAt (iteratedDeriv j h) (iteratedDeriv (j + 1) h ξ) ξ := by
      have hd := (diffOn_iteratedDeriv_of_contDiffOn_Ioo hC hj3).differentiableAt
        (isOpen_Ioo.mem_nhds hξIoo)
      convert hd.hasDerivAt using 1
      exact congr_fun (iteratedDeriv_succ (n := j) (f := h)) ξ
    have hderivp : HasDerivAt (fun t : ℝ => cc * (t - a) ^ n)
        (cc * ((n : ℝ) * (ξ - a) ^ (n - 1))) ξ := by
      have h2 : HasDerivAt (fun t : ℝ => t - a) 1 ξ := by
        simpa using (hasDerivAt_id ξ).sub_const a
      have h3 := h2.pow n
      convert h3.const_mul cc using 1 <;> ring
    have hFderiv : HasDerivAt (fun t : ℝ => iteratedDeriv j h t - cc * (t - a) ^ n)
        (iteratedDeriv (j + 1) h ξ - cc * ((n : ℝ) * (ξ - a) ^ (n - 1))) ξ :=
      hderivi.sub hderivp
    have heq : iteratedDeriv (j + 1) h ξ = cc * ((n : ℝ) * (ξ - a) ^ (n - 1)) := by
      have h1 : deriv (fun t : ℝ => iteratedDeriv j h t - cc * (t - a) ^ n) ξ
          = iteratedDeriv (j + 1) h ξ - cc * ((n : ℝ) * (ξ - a) ^ (n - 1)) := hFderiv.deriv
      rw [h1] at hξ0
      linarith
    have hξapos : 0 < ξ - a := by linarith [hξ.1]
    have hEpos : 0 < (n : ℝ) * (ξ - a) ^ (n - 1) := by
      refine mul_pos ?_ (pow_pos hξapos _)
      exact Nat.cast_pos.mpr (by omega : 0 < n)
    have h1 : |cc| * ((n : ℝ) * (ξ - a) ^ (n - 1)) = |iteratedDeriv (j + 1) h ξ| := by
      rw [heq, abs_mul, abs_of_nonneg hEpos.le]
    have h2 : |iteratedDeriv (j + 1) h ξ| ≤ M * (ξ - a) ^ (n - 1) / ((n - 1).factorial : ℝ) :=
      hprev ξ hξab
    have hstep1 : |cc| * ((n : ℝ) * (ξ - a) ^ (n - 1))
        ≤ M * (ξ - a) ^ (n - 1) / ((n - 1).factorial : ℝ) := by
      rw [h1]; exact h2
    have hpowpos : 0 < (ξ - a) ^ (n - 1) := pow_pos hξapos _
    have hstep1' : (|cc| * (n : ℝ)) * (ξ - a) ^ (n - 1)
        ≤ (M / ((n - 1).factorial : ℝ)) * (ξ - a) ^ (n - 1) := by
      have e1 : |cc| * ((n : ℝ) * (ξ - a) ^ (n - 1))
          = (|cc| * (n : ℝ)) * (ξ - a) ^ (n - 1) := by ring
      have e2 : M * (ξ - a) ^ (n - 1) / ((n - 1).factorial : ℝ)
          = (M / ((n - 1).factorial : ℝ)) * (ξ - a) ^ (n - 1) := by ring
      rw [e1, e2] at hstep1; exact hstep1
    have hstep2 : |cc| * (n : ℝ) ≤ M / ((n - 1).factorial : ℝ) :=
      le_of_mul_le_mul_right hstep1' hpowpos
    have hfacpos : (0 : ℝ) < ((n - 1).factorial : ℝ) := by positivity
    have hstep3 : (|cc| * (n : ℝ)) * ((n - 1).factorial : ℝ) ≤ M := by
      have h := mul_le_mul_of_nonneg_right hstep2 hfacpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hfacpos)] at h
    have hccbound : |cc| ≤ M / ((n : ℝ) * ((n - 1).factorial : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ((n - 1).factorial : ℝ))]
      linarith [hstep3]
    have hfacn : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
    have hccx' : |iteratedDeriv j h x| = |cc| * (x - a) ^ n := by
      rw [← hccx, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x - a) ^ n)]
    rw [hccx', hfacn]
    refine (mul_le_mul_of_nonneg_right hccbound (by positivity : (0 : ℝ) ≤ (x - a) ^ n)).trans_eq ?_
    ring_nf

/-! ## The ladder bound -/

theorem ladder_bound {H : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hH : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 4 H x)
    (hM : ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 H y| ≤ M) :
    ∀ i : ℕ, i ≤ 4 → ∀ x ∈ Set.Icc a b,
      |iteratedDeriv i H x -
        ∑ s ∈ Finset.Icc i 3,
          iteratedDeriv s H a * (x - a) ^ (s - i) / ((s - i).factorial : ℝ)|
        ≤ M * (b - a) ^ (4 - i) / ((4 - i).factorial : ℝ) := by
  -- `M ≥ 0`, and an open interval on which `H` is `C^4`.
  obtain ⟨c, d, _hca, _hbd, hsub, hC⟩ :=
    Work.FTS.GalBasis.PolyApprox.exists_contDiffOn_Ioo_of_contDiffAt_Icc hab hH
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_rfl, hab⟩)
  -- The order-three Taylor polynomial of `H` at `a`.
  set T : ℝ → ℝ :=
    fun y => ∑ k ∈ Finset.range 4, (iteratedDeriv k H a / (k.factorial : ℝ)) * (y - a) ^ k
    with hT
  have hpoly : ContDiff ℝ 4 T := by
    rw [hT]
    exact ContDiff.sum fun k _hk =>
      ContDiff.mul contDiff_const (ContDiff.pow (contDiff_id.sub contDiff_const) k)
  have hTderiv : ∀ i x, iteratedDeriv i T x
      = ∑ k ∈ Finset.range 4,
          (iteratedDeriv k H a / (k.factorial : ℝ)) * ((k.descFactorial i : ℝ) * (x - a) ^ (k - i)) := by
    intro i x
    rw [hT]
    exact iteratedDeriv_sum_pow_sub_gal _ _ _ _ _
  -- The `i`-th derivative of `T` is the sum appearing in the statement.
  have hTsum : ∀ i ≤ 3, ∀ x, iteratedDeriv i T x
      = ∑ s ∈ Finset.Icc i 3, iteratedDeriv s H a * (x - a) ^ (s - i) / ((s - i).factorial : ℝ) := by
    intro i hi x
    rw [hTderiv]
    have hsplit : Finset.range 4 = Finset.Icc i 3 ∪ Finset.range i := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc i 3) (Finset.range i) := by
      rw [Finset.disjoint_left]; intro k hk hk2
      simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range] at hk2; omega
    rw [hsplit, Finset.sum_union hdisj]
    -- the terms with `k < i` vanish, since `k.descFactorial i = 0`
    have hz : ∑ k ∈ Finset.range i,
        (iteratedDeriv k H a / (k.factorial : ℝ)) * ((k.descFactorial i : ℝ) * (x - a) ^ (k - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk]; ring
    rw [hz, add_zero]
    -- the remaining terms are rearranged into the statement's normal form
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have hfac : ((s.descFactorial i : ℕ) : ℝ) * (((s - i).factorial : ℕ) : ℝ)
        = ((s.factorial : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial hs.1]
    have hd : ((s.descFactorial i : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero, ne_eq, Nat.descFactorial_eq_zero_iff_lt]; omega
    have hf2 : (((s - i).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [← hfac]
    field_simp
  -- `T` reproduces the derivatives of `H` at `a` up to order three, and its fourth is zero
  have hTathree : ∀ i ≤ 3, iteratedDeriv i T a = iteratedDeriv i H a := by
    intro i hi
    rw [hTsum i hi a,
      Finset.sum_eq_single i
        (fun s hs _hne => by
          simp only [Finset.mem_Icc] at hs
          rw [sub_self, zero_pow (by omega : s - i ≠ 0), mul_zero, zero_div])
        (fun hmem => absurd (Finset.mem_Icc.mpr ⟨le_rfl, hi⟩) hmem)]
    simp
  have hT4 : ∀ x, iteratedDeriv 4 T x = 0 := by
    intro x
    rw [hTderiv]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : k < 4)]
    ring
  -- `h = H - T` has vanishing derivatives at `a` up to order three and `|h⁗| ≤ M`
  have hCh : ContDiffOn ℝ 4 (H - T) (Set.Ioo c d) := hC.sub hpoly.contDiffOn
  have h0 : ∀ m < 4, iteratedDeriv m (H - T) a = 0 := by
    intro m hm
    rw [iteratedDeriv_sub ((hH a ⟨le_rfl, hab⟩).of_le (by exact_mod_cast (le_of_lt hm)))
      (hpoly.contDiffAt.of_le (by exact_mod_cast (le_of_lt hm))),
      hTathree m (by omega), sub_self]
  have hMh : ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 (H - T) y| ≤ M := by
    intro y hy
    rw [iteratedDeriv_sub (hH y hy) hpoly.contDiffAt, hT4 y, sub_zero]
    exact hM y hy
  -- the four rungs of the ladder
  have H4 : ∀ x ∈ Set.Icc a b,
      |iteratedDeriv 4 (H - T) x| ≤ M * (x - a) ^ (0 : ℕ) / ((0 : ℕ).factorial : ℝ) := by
    intro x hx; simpa using hMh x hx
  have H3 : ∀ x ∈ Set.Icc a b,
      |iteratedDeriv 3 (H - T) x| ≤ M * (x - a) ^ (1 : ℕ) / ((1 : ℕ).factorial : ℝ) :=
    ladder_step_gen (j := 3) (n := 1) (by norm_num) (by norm_num) hCh hsub (h0 3 (by norm_num))
      (by intro y hy; simpa using H4 y hy)
  have H2 : ∀ x ∈ Set.Icc a b,
      |iteratedDeriv 2 (H - T) x| ≤ M * (x - a) ^ (2 : ℕ) / ((2 : ℕ).factorial : ℝ) :=
    ladder_step_gen (j := 2) (n := 2) (by norm_num) (by norm_num) hCh hsub (h0 2 (by norm_num))
      (by intro y hy; simpa using H3 y hy)
  have H1 : ∀ x ∈ Set.Icc a b,
      |iteratedDeriv 1 (H - T) x| ≤ M * (x - a) ^ (3 : ℕ) / ((3 : ℕ).factorial : ℝ) :=
    ladder_step_gen (j := 1) (n := 3) (by norm_num) (by norm_num) hCh hsub (h0 1 (by norm_num))
      (by intro y hy; simpa using H2 y hy)
  have H0 : ∀ x ∈ Set.Icc a b,
      |iteratedDeriv 0 (H - T) x| ≤ M * (x - a) ^ (4 : ℕ) / ((4 : ℕ).factorial : ℝ) :=
    ladder_step_gen (j := 0) (n := 4) (by norm_num) (by norm_num) hCh hsub (h0 0 (by norm_num))
      (by intro y hy; simpa using H1 y hy)
  have hbound : ∀ (i : ℕ) (_hi3 : i ≤ 3), ∀ y ∈ Set.Icc a b,
      |iteratedDeriv i (H - T) y| ≤ M * (y - a) ^ (4 - i) / ((4 - i).factorial : ℝ) := by
    intro i _hi3
    interval_cases i
    · simpa using H0
    · simpa using H1
    · simpa using H2
    · simpa using H3
  -- the difference in the statement is `iteratedDeriv i (H - T) x`
  have hkey : ∀ (i : ℕ) (_hi3 : i ≤ 3), ∀ x ∈ Set.Icc a b,
      iteratedDeriv i H x - ∑ s ∈ Finset.Icc i 3,
          iteratedDeriv s H a * (x - a) ^ (s - i) / ((s - i).factorial : ℝ)
        = iteratedDeriv i (H - T) x := by
    intro i hi3 x hx
    rw [iteratedDeriv_sub ((hH x hx).of_le (by exact_mod_cast (by omega : i ≤ 4)))
      (hpoly.contDiffAt.of_le (by exact_mod_cast (by omega : i ≤ 4))), hTsum i hi3 x]
  intro i hi x hx
  rcases eq_or_lt_of_le hi with h4 | hlt
  · -- `i = 4`: the Taylor sum is empty
    subst h4
    have hempty : Finset.Icc 4 3 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_of_lt (by norm_num)
    rw [hempty, Finset.sum_empty, sub_zero]
    simpa using hM x hx
  · rw [hkey i (by omega) x hx]
    refine (hbound i (by omega) x hx).trans ?_
    have h1 : (x - a) ^ (4 - i) ≤ (b - a) ^ (4 - i) :=
      pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) _
    have h2 : M * (x - a) ^ (4 - i) / ((4 - i).factorial : ℝ)
        ≤ M * (b - a) ^ (4 - i) / ((4 - i).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hM0)
      positivity
    exact h2

end Work.FTS.GalBasis.GalApprox

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `H`-complexity of the coefficients of the inverse series

This is the analytic core of the third case (`b = c⋄ = c⁻¹`) of [JZLA20, Proposition 5.1].

Let `c = ∑ cₙ` be a non-zero element of the skew Laurent series ring `D_{N,P}((t;τ))` occurring in
[JZLA20, Proposition 5.1] and let `b = ∑ bₙ = c⁻¹` be its inverse in `D_{N,P}((t;τ))` (a division
ring, `D_{N,P}` being one).  The `H`-complexities of the coefficients of the inverse are bounded
by the `H`-complexities of the coefficients of `c`, and on the `log²` scale by the `H`-complexity
of the *leading* coefficient of `c`:

if `c` vanishes below `m`, if `c_m ≠ 0`, and if `T` is a tree with
`Tree_H (c_m) < T`, `log² Tree_H (-1) < T` and `log² Tree_H (cᵢ) < T` for all `i`, then
`log² Tree_H (bₙ) < T` for **all** `n`.

The `d2log` (`log²`) form is exactly the form in which this estimate is used: `log²` of a product
is bounded by the maximum of the `log²`s of the factors, and `log² Tree_H (c⁻¹) ≤ Tree_H c`
([JZLA20, Lemma 4.3(xii)]: `Tree_H (c⁻¹) ≤ exp (exp (Tree_H c))`).

The proof is an induction on `n ≥ -m`.  The `(n+m)`-th coefficient of `c · b = 1` is `0` (and `1`
for `n = -m`); solving that convolution equation for `b.1 n` — this is
`SkewLaurentSeries.inv_coeff` — expresses `b.1 n`, up to the twist `τᵐ` (which does not change the
`H`-complexity, `treeH_conj_coeffToP`), as `c_m⁻¹` times

  `1 - ∑ i ∈ [m+1, n+2m], cᵢ · (τⁱ (b_{n+m-i}))`   (respectively  `- ∑ …`  when `n ≠ -m`).

Every index `n + m - i` occurring in the sum is `< n` (because `i > m`) and `≥ -m` (because
`i ≤ n + 2m`), so the induction hypothesis applies to `b.1 (n+m-i)`; the complexity of `c_m⁻¹` is
`≤ exp (exp (Tree_H c_m))`, so its `log²` is `≤ Tree_H c_m < T` (`treeH_inv_le`); the complexity of
each summand is at most the product of the complexities of its two factors
(`treeH_coeffToP_mul_ofAdd_le`), whose `log²`s are `< T` by hypothesis and by induction
(`⋄` and `+` of [JZLA20, Lemma 4.3(ix),(x)]); and the complexity of a finite sum is at most the
sum of the complexities (`treeH_le_sum`).
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51.ratOp_aux
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.SkewLaurentSeries.isDivisionRing_skewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.SkewLaurentSeries.inv_coeff
import Submission.Work.ORHughesFree.Prop51.conj
import Submission.Work.ORHughesFree.Prop51.treeH_coeffToP_mul_ofAdd_le

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-! ### `coeffToP` is a ring homomorphism -/

private theorem coeff_inv_coeffToP_mul (d : Prop51Data Γ P DN) (x y : ↥DN) :
    d.coeffToP (x * y) = d.coeffToP x * d.coeffToP y := rfl

private theorem coeff_inv_coeffToP_sub (d : Prop51Data Γ P DN) (x y : ↥DN) :
    d.coeffToP (x - y) = d.coeffToP x - d.coeffToP y := rfl

private theorem coeff_inv_coeffToP_neg (d : Prop51Data Γ P DN) (x : ↥DN) :
    d.coeffToP (-x) = -d.coeffToP x := rfl

private theorem coeff_inv_coeffToP_one (d : Prop51Data Γ P DN) :
    d.coeffToP (1 : ↥DN) = 1 := rfl

private theorem coeff_inv_coeffToP_zero (d : Prop51Data Γ P DN) :
    d.coeffToP (0 : ↥DN) = 0 := rfl

private theorem coeff_inv_coeffToP_sum (d : Prop51Data Γ P DN) (s : Finset ℤ)
    (g : ℤ → ↥DN) : d.coeffToP (∑ i ∈ s, g i) = ∑ i ∈ s, d.coeffToP (g i) :=
  map_sum (Subring.subtype DN) _ _

/-! ### Complexity estimates for sums, products and the constant `1` -/

/-- The `d2log`-bound is preserved by finite sums of trees: if every summand `t i` satisfies
`d2log (t i) < some A`, then so does the sum.  (The empty sum is `0`, whose `d2log` is `none`,
which is `< some A`.) -/
private theorem coeff_inv_olt_d2log_sum {ι : Type} (s : Finset ι) (t : ι → Tree) (A : Tree)
    (h : ∀ i ∈ s, Tree.Olt (Tree.d2log (t i)) (some A)) :
    Tree.Olt (Tree.d2log (∑ i ∈ s, t i)) (some A) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Tree.d2log_zero]
      exact ⟨Tree.ole_none_left _, Tree.not_ole_some_none A⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine Tree.ole_olt_trans (Tree.ole_d2log_add (t a) (∑ i ∈ s, t i)) ?_
      exact Tree.olt_omax_of (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The `d2log`-bound is preserved by finite sums of elements of `D_{H,P}`. -/
private theorem coeff_inv_olt_d2log_treeH_sum (d : Prop51Data Γ P DN) {ι : Type} (s : Finset ι)
    (x : ι → P) (hmem : ∀ i ∈ s, x i ∈ d.DH) {T : Tree}
    (h : ∀ i ∈ s, Tree.Olt (Tree.d2log (d.treeH (x i))) (some T)) :
    Tree.Olt (Tree.d2log (d.treeH (∑ i ∈ s, x i))) (some T) :=
  Tree.ole_olt_trans (Tree.ole_d2log_of_le (treeH_le_sum (d := d) s x hmem))
    (coeff_inv_olt_d2log_sum s (fun i => d.treeH (x i)) T h)

/-- The `d2log`-bound is preserved by products of elements of `D_{H,P}`. -/
private theorem coeff_inv_olt_d2log_treeH_mul (d : Prop51Data Γ P DN) {x y : P}
    (hx : x ∈ d.DH) (hy : y ∈ d.DH) {T : Tree}
    (h1 : Tree.Olt (Tree.d2log (d.treeH x)) (some T))
    (h2 : Tree.Olt (Tree.d2log (d.treeH y)) (some T)) :
    Tree.Olt (Tree.d2log (d.treeH (x * y))) (some T) :=
  Tree.ole_olt_trans (Tree.ole_d2log_of_le (treeH_le_mul (d := d) hx hy))
    (Tree.ole_olt_trans (Tree.ole_d2log_mul (d.treeH x) (d.treeH y))
      (Tree.olt_omax_of h1 h2))

/-- The `d2log`-bound is preserved by sums of elements of `D_{H,P}`. -/
private theorem coeff_inv_olt_d2log_treeH_add (d : Prop51Data Γ P DN) {x y : P}
    (hx : x ∈ d.DH) (hy : y ∈ d.DH) {T : Tree}
    (h1 : Tree.Olt (Tree.d2log (d.treeH x)) (some T))
    (h2 : Tree.Olt (Tree.d2log (d.treeH y)) (some T)) :
    Tree.Olt (Tree.d2log (d.treeH (x + y))) (some T) :=
  Tree.ole_olt_trans (Tree.ole_d2log_of_le (treeH_le_add (d := d) hx hy))
    (Tree.ole_olt_trans (Tree.ole_d2log_add (d.treeH x) (d.treeH y))
      (Tree.olt_omax_of h1 h2))

/-- The `d2log` of the complexity of the unit `1` is `none`, hence below every `some T`. -/
private theorem coeff_inv_olt_d2log_treeH_one (d : Prop51Data Γ P DN) (T : Tree) :
    Tree.Olt (Tree.d2log (d.treeH (1 : P))) (some T) := by
  have h1 : (1 : P) = d.Φ (RatU.ofGroup (1 : Γ)) := by rw [RatU.ofGroup_one, map_one]
  have hlog : Tree.log (1 : Tree) = some 0 := Tree.log_exp 0
  rw [h1, treeH_ofGroup d 1, Tree.d2log_eq_some hlog, (Tree.log_spec 0).1 rfl]
  exact ⟨Tree.ole_none_left _, Tree.not_ole_some_none T⟩

/-- One summand of the convolution: the `d2log`-complexity of
`f.1 i * (τⁱ (u.1 (N - i)))` is bounded by `some T` as soon as the two factors are. -/
private theorem coeff_inv_olt_d2log_term (d : Prop51Data Γ P DN)
    (f u : SkewLaurentSeries ↥DN) (N i : ℤ) {T : Tree}
    (h1 : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (f.1 i)))) (some T))
    (h2 : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (u.1 (N - i))))) (some T)) :
    Tree.Olt
      (Tree.d2log (d.treeH (d.coeffToP (f.1 i * ((Multiplicative.ofAdd i) • u.1 (N - i))))))
      (some T) :=
  Tree.ole_olt_trans (Tree.ole_d2log_of_le (treeH_coeffToP_mul_ofAdd_le d f u N i))
    (Tree.ole_olt_trans
      (Tree.ole_d2log_mul (d.treeH (d.coeffToP (f.1 i)))
        (d.treeH (d.coeffToP (u.1 (N - i)))))
      (Tree.olt_omax_of h1 h2))

/-! ### The induction -/

/-- **The coefficients of the inverse series are strictly below the bound.**  If `f` vanishes
below `m` with `f.1 m ≠ 0`, if `u` is its two-sided inverse in `D_{N,P}((t;τ))` (so that `u`
vanishes below `-m`), and if the complexities of the coefficients of `f` together with that of
`-1` have `d2log` strictly below `some T`, with the *leading* coefficient satisfying the stronger
`Tree_H (f.1 m) < T`, then every coefficient of the inverse series `u` has `d2log` strictly below
`some T`.

This is the strong-induction form (no induction hypothesis is assumed): the induction is on
`n ≥ -m`, so it is run on the natural number `n + m`. -/
theorem coeff_inv_step_strong {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Prop51Data Γ P DN)
    {T : Tree} {f u : SkewLaurentSeries ↥DN} {m : ℤ}
    (hfu : f * u = 1) (huf : u * f = 1)
    (hm : ∀ j : ℤ, j < m → f.1 j = 0) (hm' : f.1 m ≠ 0) (hmunit : IsUnit (f.1 m))
    (hu : SkewLaurentSeries.VanishesBelow u (-m))
    (hT : Tree.lt (d.treeH (d.coeffToP (f.1 m))) T)
    (hneg : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (-1)))) (some T))
    (hf : ∀ i : ℤ, Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (f.1 i)))) (some T)) :
    ∀ n : ℤ, -m ≤ n → Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (u.1 n)))) (some T) := by
  classical
  -- The leading coefficient `f.1 m` of `f` is a unit of `D_{N,P}` (hypothesis `hmunit`; in the
  -- intended instantiation this comes from `Prop51Inv` and `Prop51Data.DN_inv_closed`).
  obtain ⟨ainv, hainv1, hainv2⟩ : ∃ a : ↥DN, f.1 m * a = 1 ∧ a * f.1 m = 1 := by
    have hunit : IsUnit (f.1 m) := hmunit
    refine ⟨↑((hunit.unit)⁻¹), ?_, ?_⟩
    · have h : (↑hunit.unit * ↑((hunit.unit)⁻¹) : ↥DN) = 1 := Units.mul_inv hunit.unit
      rwa [hunit.unit_spec] at h
    · have h : (↑((hunit.unit)⁻¹) * ↑hunit.unit : ↥DN) = 1 := Units.inv_mul hunit.unit
      rwa [hunit.unit_spec] at h
  -- The complexity of `c_m⁻¹` is `≤ exp (exp (Tree_H c_m))`, so its `log²` is `≤ Tree_H c_m < T`.
  have hA : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP ainv))) (some T) := by
    have hab : d.coeffToP (f.1 m) * d.coeffToP ainv = 1 := by
      rw [← coeff_inv_coeffToP_mul d, hainv1, coeff_inv_coeffToP_one d]
    have hba : d.coeffToP ainv * d.coeffToP (f.1 m) = 1 := by
      rw [← coeff_inv_coeffToP_mul d, hainv2, coeff_inv_coeffToP_one d]
    exact Tree.ole_olt_trans
      (olt_d2log_treeH_inv_le d (d.coeffToP_mem (f.1 m)) (d.coeffToP_mem ainv) hab hba)
      (Tree.ole_some_of_lt hT)
  -- The induction, run on the natural number `n + m`.
  have key : ∀ k : ℕ, ∀ n : ℤ, n + m = (k : ℤ) →
      Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (u.1 n)))) (some T) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hk
      -- The `(n+m)`-th coefficient of `f * u = 1`, solved for `u.1 n`.
      have hrec := SkewLaurentSeries.inv_coeff (f := f) (g := u) (m := m) (ainv := ainv)
        hainv1 hainv2 hm hu hfu (n + m)
      rw [show n + m - m = n by ring] at hrec
      -- The induction hypothesis, at every index `≥ -m` strictly below `n`.
      have ihj : ∀ j : ℤ, -m ≤ j → j < n →
          Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (u.1 j)))) (some T) := by
        intro j hj1 hj2
        have hj0 : (0 : ℤ) ≤ j + m := by omega
        have hjk : (j + m).toNat < k := by
          refine (Int.toNat_lt hj0).2 ?_
          omega
        exact ih (j + m).toNat hjk j (by rw [Int.toNat_of_nonneg hj0])
      split_ifs at hrec with h0
      · -- `n = -m`: the coefficient of `1` is `1` and the convolution sum is empty.
        have hsum0 : (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
            f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i))) = 0 := by
          rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        have hW : Tree.Olt
            (Tree.d2log (d.treeH (1 - d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
              f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i)))))) (some T) := by
          rw [hsum0, coeff_inv_coeffToP_zero d, sub_zero]
          exact coeff_inv_olt_d2log_treeH_one d T
        have hWmem : (1 - d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
            f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i)))) ∈ d.DH :=
          d.DH.sub_mem d.DH.one_mem (d.coeffToP_mem _)
        have hprod := coeff_inv_olt_d2log_treeH_mul (d := d) (d.coeffToP_mem ainv) hWmem hA hW
        have hrecP : d.coeffToP ((Multiplicative.ofAdd m) • u.1 n)
            = d.coeffToP ainv * (1 - d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
                f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i)))) := by
          rw [hrec, coeff_inv_coeffToP_mul, coeff_inv_coeffToP_sub, coeff_inv_coeffToP_one,
            coeff_inv_coeffToP_sum]
        rw [← treeH_conj_coeffToP d m (u.1 n), hrecP]
        exact hprod
      · -- `n ≠ -m`: the coefficient of `1` is `0`, and the convolution sum is bounded termwise.
        have hS : Tree.Olt
            (Tree.d2log (d.treeH (d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
              f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i)))))) (some T) := by
          rw [coeff_inv_coeffToP_sum]
          refine coeff_inv_olt_d2log_treeH_sum (d := d) _ _
            (fun i _ => d.coeffToP_mem _) (fun i hi => ?_)
          rw [Finset.mem_Icc] at hi
          exact coeff_inv_olt_d2log_term (d := d) f u (n + m) i (hf i)
            (ihj ((n + m) - i) (by omega) (by omega))
        have hW : Tree.Olt
            (Tree.d2log (d.treeH (-(d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
              f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i))))))) (some T) :=
          olt_d2log_neg d (d.coeffToP_mem _) hS hneg
        have hWmem : (-(d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
            f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i))))) ∈ d.DH :=
          d.DH.neg_mem (d.coeffToP_mem _)
        have hprod := coeff_inv_olt_d2log_treeH_mul (d := d) (d.coeffToP_mem ainv) hWmem hA hW
        have hrecP : d.coeffToP ((Multiplicative.ofAdd m) • u.1 n)
            = d.coeffToP ainv * (-(d.coeffToP (∑ i ∈ Finset.Icc (m + 1) ((n + m) + m),
                f.1 i * ((Multiplicative.ofAdd i) • u.1 (n + m - i))))) := by
          rw [hrec, zero_sub, coeff_inv_coeffToP_mul, coeff_inv_coeffToP_neg,
            coeff_inv_coeffToP_sum]
        rw [← treeH_conj_coeffToP d m (u.1 n), hrecP]
        exact hprod
  intro n hn
  have h0 : (0 : ℤ) ≤ n + m := by omega
  exact key (n + m).toNat n (by rw [Int.toNat_of_nonneg h0])

/-- **The coefficients of the inverse series.**  Let `f, u ∈ D_{N,P}((t;τ))` be mutually inverse,
let `f` vanish below `m` with `f.1 m ≠ 0` and let `T` be a tree such that

* `Tree_H (f.1 m) < T` (the leading coefficient),
* `log² Tree_H (-1) < T`,
* `log² Tree_H (f.1 i) < T` for every `i`.

Then `log² Tree_H (u.1 n) < T` for every `n ≥ -m`, given the conclusion for all smaller indices
`j < n` (which is what the induction of [JZLA20, Proposition 5.1, case 3] provides).

In the notation of the proof of [JZLA20, Proposition 5.1]: `f = ∑ cₙ`, `u = ∑ bₙ = (∑ cₙ)⁻¹`,
`m = k = min {n : cₙ ≠ 0}` and `T = Tree_H (b)`, where `b = Φ (γ⋄)` is the element of `D_{H,P}`
whose complexity is realised by `γ⋄`. -/
theorem coeff_inv_step {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {T : Work.ORHughesFree.Tree} {f u : Work.ORHughesFree.SkewLaurentSeries ↥DN} {m : ℤ}
    (hfu : f * u = 1) (huf : u * f = 1)
    (hm : ∀ j : ℤ, j < m → f.1 j = 0) (hm' : f.1 m ≠ 0) (hmunit : IsUnit (f.1 m))
    (hu : Work.ORHughesFree.SkewLaurentSeries.VanishesBelow u (-m))
    (hT : Work.ORHughesFree.Tree.lt (d.treeH (d.coeffToP (f.1 m))) T)
    (hneg : Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.d2log (d.treeH (d.coeffToP (-1)))) (some T))
    (hf : ∀ i : ℤ, Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.d2log (d.treeH (d.coeffToP (f.1 i)))) (some T))
    {n : ℤ} (hn : -m ≤ n)
    (hIH : ∀ j : ℤ, j < n → Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.d2log (d.treeH (d.coeffToP (u.1 j)))) (some T)) :
    Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.d2log (d.treeH (d.coeffToP (u.1 n)))) (some T) :=
  coeff_inv_step_strong d hfu huf hm hm' hmunit hu hT hneg hf n hn

end Work.ORHughesFree.Prop51

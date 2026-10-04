import Mathlib
import Submission.Work.Diff.STE.B3.ENormSq_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open BigOperators

namespace Work.Diff.STE.B3

/-- `pdList` of positive order annihilates a constant function. -/
lemma pdList_const_of_ne_nil {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List ι) (c : ℂ)
    (hl : l ≠ []) :
    Work.Diff.STE.pdList l (fun _ : ι → ℝ => c) = fun _ => 0 := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact pdList_cons_const a l' c

/-- The iterated Leibniz rule, solved for `∂^l (F·g)`:
`∂^l (F·g) = F·∂^l g + Σ_{p ∈ splitsNE l} ∂^{p.1}F · ∂^{p.2}g`. -/
lemma pdList_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List ι) (F g : (ι → ℝ) → ℂ)
    (hF : ∀ q : List ι, List.Sublist q l → q.length < l.length → Differentiable ℝ (pdList q F))
    (hg : ∀ q : List ι, List.Sublist q l → q.length < l.length → Differentiable ℝ (pdList q g)) :
    pdList l (fun z => F z * g z)
      = fun y => F y * pdList l g y
        + (((Work.Diff.STE.splitsNE l).map (fun p => pdList p.1 F y * pdList p.2 g y))).sum := by
  have h := Work.Diff.STE.pdList_mul_sub l F g hF hg
  funext y
  have hy := congrFun h y
  rw [← Work.Diff.STE.splitsNE_eq_filter l] at hy
  exact (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)

/-- Swapping a list-sum and a `Finset` sum. -/
lemma list_sum_finset_sum_swap {α β : Type*} (L : List α) (s : Finset β) (f : α → β → ℝ) :
    (L.map (fun a => ∑ b ∈ s, f a b)).sum = ∑ b ∈ s, (L.map (fun a => f a b)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Finset.sum_add_distrib]

/-- **The recursion for the entries of the inverse.**  Differentiating `G · H = 1` with the
iterated Leibniz rule and multiplying by `H` on the left gives, for `l ≠ []`,
`∂^l H_{ij} = -Σ_{k'} H_{i k'} Σ_{m'} Σ_{p ∈ splitsNE l} (∂^{p.1}G_{k'm'})(∂^{p.2}H_{m'j})`. -/
private lemma pdList_inv_entry_aux {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : (ι → ℝ) → Fin n → Fin n → ℂ) (l : List ι) (hl : l ≠ [])
    (hG : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => G x i j))
    (hH : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => H x i j))
    (hGH : ∀ x : ι → ℝ, Matrix.of (G x) * Matrix.of (H x) = 1)
    (hHG : ∀ x : ι → ℝ, Matrix.of (H x) * Matrix.of (G x) = 1)
    (i j : Fin n) (x : ι → ℝ) :
    Work.Diff.STE.pdList l (fun y => H y i j) x
      = - ∑ k' : Fin n, H x i k' * (∑ m' : Fin n,
          (((Work.Diff.STE.splitsNE l).map (fun p =>
            Work.Diff.STE.pdList p.1 (fun y => G y k' m') x
              * Work.Diff.STE.pdList p.2 (fun y => H y m' j) x))).sum) := by
  classical
  -- smoothness gives differentiability of all the jets involved
  have hdiff : ∀ (f : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ q : List ι,
      List.Sublist q l → q.length < l.length → Differentiable ℝ (pdList q f) := by
    intro f hf q _ _
    refine (Work.Diff.STE.cm_contDiff_pdList q 1 f ?_).differentiable (by norm_num)
    exact hf.of_le (by exact_mod_cast le_top)
  -- the diagonal entries of `G * H` are constant, so their jets vanish
  have hzero : ∀ r : Fin n,
      pdList l (fun z => (Matrix.of (G z) * Matrix.of (H z)) r j) x = 0 := by
    intro r
    have hc : (fun z => (Matrix.of (G z) * Matrix.of (H z)) r j)
        = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) r j := by
      funext z
      rw [hGH z]
    rw [hc]
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
    exact congrFun (pdList_cons_const a l' _) x
  -- linearity over the summation index
  have hlin : ∀ r : Fin n,
      pdList l (fun z => ∑ k' : Fin n, G z r k' * H z k' j)
        = fun z => ∑ k' : Fin n, pdList l (fun z => G z r k' * H z k' j) z := by
    intro r
    exact pdList_finset_sum l Finset.univ (fun k' z => G z r k' * H z k' j)
      (fun k' _ => (hG r k').mul (hH k' j))
  -- the Leibniz expansion, solved for the `H`-factor
  have hleib : ∀ r : Fin n,
      (∑ k' : Fin n, G x r k' * pdList l (fun z => H z k' j) x)
        = - ∑ k' : Fin n, (((Work.Diff.STE.splitsNE l).map (fun p =>
            pdList p.1 (fun z => G z r k') x
              * pdList p.2 (fun z => H z k' j) x))).sum := by
    intro r
    have hmul : (fun z => (Matrix.of (G z) * Matrix.of (H z)) r j)
        = fun z => ∑ k' : Fin n, G z r k' * H z k' j := by
      funext z
      simp only [Matrix.mul_apply, Matrix.of_apply]
    have hsum0 : ∑ k' : Fin n,
        pdList l (fun z => G z r k' * H z k' j) x = 0 := by
      have hz := hzero r
      rw [hmul, hlin r] at hz
      exact hz
    have hsum1 : ∑ k' : Fin n, (G x r k' * pdList l (fun z => H z k' j) x
        + (((Work.Diff.STE.splitsNE l).map (fun p =>
            pdList p.1 (fun z => G z r k') x
              * pdList p.2 (fun z => H z k' j) x))).sum) = 0 := by
      rw [← hsum0]
      refine Finset.sum_congr rfl fun k' _ => ?_
      exact (congrFun (pdList_mul_eq l (fun z => G z r k') (fun z => H z k' j)
        (hdiff _ (hG r k')) (hdiff _ (hH k' j))) x).symm
    rw [Finset.sum_add_distrib] at hsum1
    exact eq_neg_of_add_eq_zero_left hsum1
  -- multiply by `H` on the left and use `H * G = 1`
  have hkeyG : ∀ k' : Fin n, (∑ i' : Fin n, H x i i' * G x i' k')
      = (if i = k' then 1 else 0) := by
    intro k'
    have h := hHG x
    have hmat := congrFun (congrFun h i) k'
    rw [Matrix.mul_apply, Matrix.one_apply] at hmat
    exact hmat
  have hmulH : (∑ i' : Fin n, H x i i' * (∑ k' : Fin n,
        G x i' k' * pdList l (fun z => H z k' j) x))
      = pdList l (fun z => H z i j) x := by
    have h1 : ∀ i' : Fin n, H x i i' * (∑ k' : Fin n,
          G x i' k' * pdList l (fun z => H z k' j) x)
        = ∑ k' : Fin n, H x i i' * (G x i' k'
            * pdList l (fun z => H z k' j) x) :=
      fun i' => Finset.mul_sum ..
    rw [Finset.sum_congr rfl (fun i' _ => h1 i'), Finset.sum_comm]
    have h2 : ∀ k' : Fin n, (∑ i' : Fin n, H x i i' * (G x i' k'
          * pdList l (fun z => H z k' j) x))
        = (∑ i' : Fin n, H x i i' * G x i' k')
          * pdList l (fun z => H z k' j) x := by
      intro k'
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i' _ => by ring
    rw [Finset.sum_congr rfl (fun k' _ => h2 k')]
    simp only [hkeyG]
    rw [Finset.sum_eq_single i (fun k' _ hk' => by rw [if_neg (Ne.symm hk'), zero_mul])
      (fun hmem => absurd (Finset.mem_univ i) hmem)]
    simp
  -- assemble
  calc pdList l (fun z => H z i j) x
      = ∑ i' : Fin n, H x i i' * (∑ k' : Fin n,
          G x i' k' * pdList l (fun z => H z k' j) x) := hmulH.symm
    _ = ∑ i' : Fin n, H x i i' * (- ∑ k' : Fin n,
          (((Work.Diff.STE.splitsNE l).map (fun p =>
            pdList p.1 (fun z => G z i' k') x
              * pdList p.2 (fun z => H z k' j) x))).sum) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [hleib i']
    _ = - ∑ k' : Fin n, H x i k' * (∑ m' : Fin n,
          (((Work.Diff.STE.splitsNE l).map (fun p =>
            pdList p.1 (fun z => G z k' m') x
              * pdList p.2 (fun z => H z m' j) x))).sum) := by
        rw [Finset.sum_congr rfl (fun i' _ => by rw [mul_neg, Finset.mul_sum]),
          Finset.sum_neg_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i' _ => (Finset.mul_sum ..).symm

/-- Pointwise bound for the iterated partial derivatives of the entries of the inverse of a
smooth matrix field `H = G⁻¹` (so that `G H = H G = 1` pointwise), obtained by differentiating
`G·H = 1` with the iterated Leibniz rule (`Work.Diff.STE.pdList_mul_sub`) and multiplying by `H`.
`(k : ℕ)` with `1 ≤ k`, `q : Fin k → ι` indexes the derivative word. -/
theorem pdVec_inv_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (G H : (ι → ℝ) → Fin n → Fin n → ℂ) (W : ℝ)
    (hG : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => G x i j))
    (hH : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => H x i j))
    (hGH : ∀ x : ι → ℝ, Matrix.of (G x) * Matrix.of (H x) = 1)
    (hHG : ∀ x : ι → ℝ, Matrix.of (H x) * Matrix.of (G x) = 1)
    (hW : ∀ (x : ι → ℝ) (i j : Fin n), ‖H x i j‖ ≤ W)
    (k : ℕ) (hk : 1 ≤ k) (q : Fin k → ι) (i j : Fin n) (x : ι → ℝ) :
    ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖
      ≤ W * (Finset.univ : Finset (Fin n)).sum (fun k' =>
          ((Work.Diff.STE.splitsNE (List.ofFn q)).map (fun p =>
            (Finset.univ : Finset (Fin n)).sum (fun m' =>
              ‖Work.Diff.STE.pdList p.1 (fun y => G y k' m') x‖
                * ‖Work.Diff.STE.pdList p.2 (fun y => H y m' j) x‖))).sum) := by
  classical
  set l : List ι := List.ofFn q with hl
  have hl_len : l.length = k := by rw [hl]; exact List.length_ofFn
  have hl_ne : l ≠ [] := by
    intro h
    rw [h] at hl_len
    simp only [List.length_nil] at hl_len
    omega
  have hpv : Work.Diff.STE.pdVec k q (fun y => H y i j) = pdList l (fun y => H y i j) := by
    simp only [Work.Diff.STE.pdVec, hl]
  have hW0 : 0 ≤ W := le_trans (norm_nonneg _) (hW x i j)
  set Ta : Fin n → Fin n → ℂ := fun k' m' => ((Work.Diff.STE.splitsNE l).map (fun p =>
        pdList p.1 (fun y => G y k' m') x
          * pdList p.2 (fun y => H y m' j) x)).sum with hTa
  set T : Fin n → Fin n → ℝ := fun k' m' => ((Work.Diff.STE.splitsNE l).map (fun p =>
        ‖pdList p.1 (fun y => G y k' m') x‖
          * ‖pdList p.2 (fun y => H y m' j) x‖)).sum with hT
  have hid := pdList_inv_entry_aux G H l hl_ne hG hH hGH hHG i j x
  rw [hpv]
  calc ‖pdList l (fun y => H y i j) x‖
      = ‖∑ k' : Fin n, H x i k' * (∑ m' : Fin n, Ta k' m')‖ := by rw [hid, norm_neg, hTa]
    _ ≤ ∑ k' : Fin n, ‖H x i k' * (∑ m' : Fin n, Ta k' m')‖ := norm_sum_le _ _
    _ = ∑ k' : Fin n, ‖H x i k'‖ * ‖∑ m' : Fin n, Ta k' m'‖ := by
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [norm_mul]
    _ ≤ ∑ k' : Fin n, W * ‖∑ m' : Fin n, Ta k' m'‖ := by
        refine Finset.sum_le_sum (fun k' _ => ?_)
        exact mul_le_mul_of_nonneg_right (hW x i k') (norm_nonneg _)
    _ = W * ∑ k' : Fin n, ‖∑ m' : Fin n, Ta k' m'‖ := by rw [← Finset.mul_sum]
    _ ≤ W * ∑ k' : Fin n, ∑ m' : Fin n, ‖Ta k' m'‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k' _ => norm_sum_le _ _)) hW0
    _ ≤ W * ∑ k' : Fin n, ∑ m' : Fin n, T k' m' := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun k' _ => Finset.sum_le_sum (fun m' _ => ?_))) hW0
        rw [hTa, hT]
        refine le_trans (Work.Diff.STE.cm_list_sum_norm_le (Work.Diff.STE.splitsNE l) (fun p =>
            pdList p.1 (fun y => G y k' m') x
              * pdList p.2 (fun y => H y m' j) x)) ?_
        exact le_of_eq (congrArg (fun L : List ℝ => L.sum) (List.map_congr_left
          (fun p (_ : p ∈ Work.Diff.STE.splitsNE l) => norm_mul _ _)))
    _ = W * ∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map (fun p =>
            ∑ m' : Fin n, ‖pdList p.1 (fun y => G y k' m') x‖
              * ‖pdList p.2 (fun y => H y m' j) x‖)).sum := by
        congr 1
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [hT]
        exact (list_sum_finset_sum_swap (Work.Diff.STE.splitsNE l) Finset.univ (fun p m' =>
          ‖pdList p.1 (fun y => G y k' m') x‖
            * ‖pdList p.2 (fun y => H y m' j) x‖)).symm

end Work.Diff.STE.B3

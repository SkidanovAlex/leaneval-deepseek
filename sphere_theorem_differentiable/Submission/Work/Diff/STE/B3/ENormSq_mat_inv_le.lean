import Mathlib
import Submission.Work.Diff.STE.B3.ENormSq_basic
import Submission.Work.Diff.STE.B3.list_sum_rpow_le
import Submission.Work.Diff.STE.B3.rpow_mul_le_amgm
import Submission.Work.Diff.STE.GN.lp_mono_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

/-! ## Elementary helpers for the Moser-type inverse estimate -/

/-- A list-sum of a constant multiple of a real function. -/
lemma list_sum_map_mul_left' {α : Type*} (L : List α) (c : ℝ) (f : α → ℝ) :
    (L.map (fun a => c * f a)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]; ring

/-- Integrability of a pointwise list-sum, in the `(L.map (fun b => f b x)).sum` presentation. -/
lemma integrable_list_sum_apply {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (L : List β) (f : β → (ι → ℝ) → ℝ)
    (h : ∀ b ∈ L, Integrable (f b) (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    Integrable (fun x : ι → ℝ => (L.map (fun b => f b x)).sum)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have := integrable_list_sum (ι := ι) (L.map f) (by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact h b hb)
  simpa [List.map_map, Function.comp_def] using this

/-- The integral of a pointwise list-sum, in the `(L.map (fun b => f b x)).sum` presentation. -/
lemma integral_list_sum_apply {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (L : List β) (f : β → (ι → ℝ) → ℝ)
    (h : ∀ b ∈ L, Integrable (f b) (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    (∫ x in Work.Diff.STE.unitCube, (L.map (fun b => f b x)).sum)
      = (L.map (fun b => ∫ x in Work.Diff.STE.unitCube, f b x)).sum := by
  have := integral_list_sum (ι := ι) (L.map f) (by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact h b hb)
  simpa [List.map_map, Function.comp_def] using this

/-- The bookkeeping sequence of exponents of the Moser-type induction. -/
def Lam (k : ℕ) : ℕ := (k + 2).factorial * 3 ^ (k + 2)

lemma Lam_pos (k : ℕ) : 1 ≤ Lam k := by
  rw [Lam]
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (by norm_num)))

lemma Lam_succ_mul (k : ℕ) : Lam (k + 1) = 3 * (k + 3) * Lam k := by
  rw [Lam, Lam, Nat.factorial_succ, pow_succ]
  ring

lemma Lam_succ (k : ℕ) : Lam k + 8 ≤ Lam (k + 1) := by
  have h1 := Lam_succ_mul k
  have h2 := Lam_pos k
  have h5 : 8 ≤ 8 * Lam k := by
    have : (1 : ℕ) ≤ Lam k := h2
    nlinarith
  rw [h1]
  calc Lam k + 8 ≤ Lam k + 8 * Lam k := by omega
    _ = 9 * Lam k := by ring
    _ ≤ 3 * (k + 3) * Lam k := by
        refine Nat.mul_le_mul_right _ ?_
        omega

lemma Lam_mono : Monotone Lam :=
  monotone_nat_of_le_succ fun k => le_trans (Nat.le_add_right _ _) (Lam_succ k)

/-- `G * H = 1` implies `H * G = 1` for square matrices over a field. -/
lemma mul_eq_one_comm' {n : ℕ} {G H : Matrix (Fin n) (Fin n) ℂ} (h : G * H = 1) : H * G = 1 := by
  have hdet : G.det * H.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr fun hz => by
    rw [hz, zero_mul] at hdet
    exact zero_ne_one hdet
  have hinv : G⁻¹ = H := Matrix.inv_eq_right_inv h
  have h1 := Matrix.nonsing_inv_mul G hunit
  rwa [hinv] at h1

/-- The restricted measure of the unit cube is a probability measure. -/
lemma real_restrict_unitCube {ι : Type*} [Fintype ι] :
    (volume.restrict (Work.Diff.STE.unitCube (ι := ι)) : Measure (ι → ℝ)).real Set.univ = 1 := by
  show ((volume.restrict (Work.Diff.STE.unitCube (ι := ι)) : Measure (ι → ℝ)) Set.univ).toReal = 1
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
  simp

/-! ## The pointwise recursion for the entries of the inverse of a matrix field -/

/-- The iterated Leibniz rule, solved for `∂^l (F·g)`. -/
lemma pdList_mul_eq' {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List ι)
    (F g : (ι → ℝ) → ℂ)
    (hF : ∀ q : List ι, List.Sublist q l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F))
    (hg : ∀ q : List ι, List.Sublist q l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q g)) :
    Work.Diff.STE.pdList l (fun z => F z * g z)
      = fun y => F y * Work.Diff.STE.pdList l g y
        + (((Work.Diff.STE.splitsNE l).map (fun p => Work.Diff.STE.pdList p.1 F y
            * Work.Diff.STE.pdList p.2 g y))).sum := by
  have h := Work.Diff.STE.pdList_mul_sub l F g hF hg
  funext y
  have hy := congrFun h y
  rw [← Work.Diff.STE.splitsNE_eq_filter l] at hy
  exact (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)

/-- Swapping a list-sum and a `Finset` sum. -/
lemma list_sum_finset_sum_swap' {α β R : Type*} [AddCommMonoid R] (L : List α) (s : Finset β)
    (f : α → β → R) :
    (L.map (fun a => ∑ b ∈ s, f a b)).sum = ∑ b ∈ s, (L.map (fun a => f a b)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Finset.sum_add_distrib]

/-- **The recursion for the entries of the inverse.**  Differentiating `G·H = 1` (with the
iterated Leibniz rule) and multiplying by `H` on the left gives, for `l ≠ []`,
`∂^l H_{ij} = -Σ_{k'} H_{i k'} Σ_{m'} Σ_{p ∈ splitsNE l} (∂^{p.1}G_{k'm'})(∂^{p.2}H_{m'j})`. -/
theorem pdList_inv_entry' {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
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
      List.Sublist q l → q.length < l.length → Differentiable ℝ (Work.Diff.STE.pdList q f) := by
    intro f hf q _ _
    refine (cm_contDiff_pdList q 1 f ?_).differentiable (by norm_num)
    exact hf.of_le (by exact_mod_cast le_top)
  -- the diagonal entries of `G * H` are constant, so their jets vanish
  have hzero : ∀ r : Fin n,
      Work.Diff.STE.pdList l (fun z => (Matrix.of (G z) * Matrix.of (H z)) r j) x = 0 := by
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
      Work.Diff.STE.pdList l (fun z => ∑ k' : Fin n, G z r k' * H z k' j)
        = fun z => ∑ k' : Fin n, Work.Diff.STE.pdList l (fun z => G z r k' * H z k' j) z := by
    intro r
    exact pdList_finset_sum l Finset.univ (fun k' z => G z r k' * H z k' j)
      (fun k' _ => (hG r k').mul (hH k' j))
  -- the Leibniz expansion, solved for the `H`-factor
  have hleib : ∀ r : Fin n,
      (∑ k' : Fin n, G x r k' * Work.Diff.STE.pdList l (fun z => H z k' j) x)
        = - ∑ k' : Fin n, (((Work.Diff.STE.splitsNE l).map (fun p =>
            Work.Diff.STE.pdList p.1 (fun z => G z r k') x
              * Work.Diff.STE.pdList p.2 (fun z => H z k' j) x))).sum := by
    intro r
    have hmul : (fun z => (Matrix.of (G z) * Matrix.of (H z)) r j)
        = fun z => ∑ k' : Fin n, G z r k' * H z k' j := by
      funext z
      simp only [Matrix.mul_apply, Matrix.of_apply]
    have hsum0 : ∑ k' : Fin n,
        Work.Diff.STE.pdList l (fun z => G z r k' * H z k' j) x = 0 := by
      have hz := hzero r
      rw [hmul, hlin r] at hz
      exact hz
    have hsum1 : ∑ k' : Fin n, (G x r k' * Work.Diff.STE.pdList l (fun z => H z k' j) x
        + (((Work.Diff.STE.splitsNE l).map (fun p =>
            Work.Diff.STE.pdList p.1 (fun z => G z r k') x
              * Work.Diff.STE.pdList p.2 (fun z => H z k' j) x))).sum) = 0 := by
      rw [← hsum0]
      refine Finset.sum_congr rfl fun k' _ => ?_
      exact (congrFun (pdList_mul_eq' l (fun z => G z r k') (fun z => H z k' j)
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
        G x i' k' * Work.Diff.STE.pdList l (fun z => H z k' j) x))
      = Work.Diff.STE.pdList l (fun z => H z i j) x := by
    have h1 : ∀ i' : Fin n, H x i i' * (∑ k' : Fin n,
          G x i' k' * Work.Diff.STE.pdList l (fun z => H z k' j) x)
        = ∑ k' : Fin n, H x i i' * (G x i' k'
            * Work.Diff.STE.pdList l (fun z => H z k' j) x) :=
      fun i' => Finset.mul_sum ..
    rw [Finset.sum_congr rfl (fun i' _ => h1 i'), Finset.sum_comm]
    have h2 : ∀ k' : Fin n, (∑ i' : Fin n, H x i i' * (G x i' k'
          * Work.Diff.STE.pdList l (fun z => H z k' j) x))
        = (∑ i' : Fin n, H x i i' * G x i' k')
          * Work.Diff.STE.pdList l (fun z => H z k' j) x := by
      intro k'
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i' _ => by ring
    rw [Finset.sum_congr rfl (fun k' _ => h2 k')]
    simp only [hkeyG]
    rw [Finset.sum_eq_single i (fun k' _ hk' => by rw [if_neg (Ne.symm hk'), zero_mul])
      (fun hmem => absurd (Finset.mem_univ i) hmem)]
    simp
  -- assemble
  calc Work.Diff.STE.pdList l (fun z => H z i j) x
      = ∑ i' : Fin n, H x i i' * (∑ k' : Fin n,
          G x i' k' * Work.Diff.STE.pdList l (fun z => H z k' j) x) := hmulH.symm
    _ = ∑ i' : Fin n, H x i i' * (- ∑ k' : Fin n,
          (((Work.Diff.STE.splitsNE l).map (fun p =>
            Work.Diff.STE.pdList p.1 (fun z => G z i' k') x
              * Work.Diff.STE.pdList p.2 (fun z => H z k' j) x))).sum) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [hleib i']
    _ = - ∑ k' : Fin n, H x i k' * (∑ m' : Fin n,
          (((Work.Diff.STE.splitsNE l).map (fun p =>
            Work.Diff.STE.pdList p.1 (fun z => G z k' m') x
              * Work.Diff.STE.pdList p.2 (fun z => H z m' j) x))).sum) := by
        rw [Finset.sum_congr rfl (fun i' _ => by rw [mul_neg, Finset.mul_sum]),
          Finset.sum_neg_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i' _ => (Finset.mul_sum ..).symm

/-- Pointwise bound for the iterated partial derivatives of the entries of the inverse of a
smooth matrix field `H = G⁻¹`, obtained from `pdList_inv_entry'`. -/
theorem pdVec_inv_le' {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
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
  have hid := pdList_inv_entry' G H l hl_ne hG hH hGH hHG i j x
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
        simp only [hT]
        exact (list_sum_finset_sum_swap' (Work.Diff.STE.splitsNE l) Finset.univ (fun p m' =>
          ‖pdList p.1 (fun y => G y k' m') x‖
            * ‖pdList p.2 (fun y => H y m' j) x‖)).symm

/-- **Moser-type tame estimate for the inverse of a bounded matrix field on the torus.**

PROOF ROUTE.  `G x * H x = 1` gives `H = G⁻¹` pointwise, hence (Cramer) `H = adj(G) / det G` with
`det G` bounded below (`det G · det H = 1` and `‖H‖ ≤ W` give `|det G| ≥ (n! W^n)^{-1}`).
1. `adj(G)` and `det G` are polynomials in the entries of `G`, so their `H^m` energies are bounded by
   `C(1 + ENormSqMat m G)`; the needed step is the "`H^m` is an algebra" estimate for two periodic
   functions `a, b` with sup bounds `A, B`: expand `pdVec` of `a*b` by the Leibniz rule (induction
   on the list, using `fderiv_mul`/`pd` of a product) into the `2^m` terms indexed by the chosen
   positions, bound a term with `j` derivatives on `a` by
   `‖pdVec j .. a‖_{L^{2m/j}} · ‖pdVec (m-j) .. b‖_{L^{2m/(m-j)}}` (Hölder; the exponents are
   conjugate: `j/(2m) + (m-j)/(2m) = 1/2`), use `HasGNBound` for both factors and Young's inequality
   (`x^{j/m} y^{(m-j)/m} ≤ (j/m)x + ((m-j)/m)y`) to get `ENormSq m (a*b) ≤ C(1 + ENormSq m a + ENormSq m b)`.
2. *Scalar inverse.*  For a smooth periodic `t` with `|t| ≥ 1/W` one proves
   `ENormSq m (1/t) ≤ C(1 + ENormSq m t)` by strong induction on the order, using the recursion
   `∂^β (1/t) = -(1/t) · Σ_{0<α≤β} C(β,α) (∂^α t)(∂^{β-α}(1/t))`, the `HasGNBound` of `t` and of
   `1/t`, Hölder, and an ε-version of Young's inequality (`x^{i/m}y^{(m-i)/m} ≤ ε y + C_ε x`) to
   absorb the top-order term; `HasGNBound` is available for *every* smooth periodic function by the
   hypothesis `hGN` (instantiated with the sup bound of that function).
3. Combine: `H = adj(G) · (1/det G)`, apply step 1 to the product and step 2 to `t = det G`. -/
theorem ENormSq_mat_inv_le {ι : Type*} [Fintype ι] [DecidableEq ι] (n m : ℕ) (U W : ℝ)
    (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hGN : ∃ K : ℝ, 0 ≤ K ∧ ∀ (U' : ℝ) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f → (∀ x : ι → ℝ, ‖f x‖ ≤ U') →
      Work.Diff.STE.B3.HasGNBound m U' K f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G H : (ι → ℝ) → Fin n → Fin n → ℂ),
      (∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => G x i j)) →
      (∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => H x i j)) →
      (∀ i j : Fin n, Work.Diff.STE.Periodic1 (fun x : ι → ℝ => G x i j)) →
      (∀ i j : Fin n, Work.Diff.STE.Periodic1 (fun x : ι → ℝ => H x i j)) →
      (∀ (x : ι → ℝ) (i j : Fin n), ‖G x i j‖ ≤ U) →
      (∀ (x : ι → ℝ) (i j : Fin n), ‖H x i j‖ ≤ W) →
      (∀ x : ι → ℝ, Matrix.of (G x) * Matrix.of (H x) = 1) →
      Work.Diff.STE.B3.ENormSqMat m H ≤ C * (1 + Work.Diff.STE.B3.ENormSqMat m G) := by
  classical
  haveI : IsProbabilityMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.GN.isProbabilityMeasure_restrict_unitCube
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: both sides vanish
    subst hn0
    refine ⟨1, zero_le_one, ?_⟩
    intro G H hG hH hGp hHp hGb hHb hGH
    have h0 : ENormSqMat m H = 0 := by
      rw [ENormSqMat]
      refine Finset.sum_eq_zero fun i _ => ?_
      exact Fin.elim0 i
    rw [h0]
    refine mul_nonneg zero_le_one ?_
    linarith [ENormSqMat_nonneg m G]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `m = 0`: only the sup bounds are used
    subst hm0
    refine ⟨(n : ℝ) ^ 2 * W ^ 2 + 1, by positivity, ?_⟩
    intro G H hG hH hGp hHp hGb hHb hGH
    have hvol : (volume.restrict (Work.Diff.STE.unitCube (ι := ι)) :
        Measure (ι → ℝ)).real Set.univ = 1 := by
      show ((volume.restrict (Work.Diff.STE.unitCube (ι := ι)) : Measure (ι → ℝ)) Set.univ).toReal = 1
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
      simp
    have hint : ∀ (i j : Fin n), (∫ x in Work.Diff.STE.unitCube, ‖H x i j‖ ^ 2) ≤ W ^ 2 := by
      intro i j
      have h1 : (∫ x in Work.Diff.STE.unitCube, ‖H x i j‖ ^ 2)
          ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), W ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (integrable_const _) (Filter.Eventually.of_forall fun x => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hHb x i j) 2
      have h2 : (∫ x in Work.Diff.STE.unitCube (ι := ι), W ^ 2) = W ^ 2 := by
        simp only [MeasureTheory.integral_const, hvol, one_smul]
      linarith [h1, h2.le]
    have hmain : ENormSqMat 0 H ≤ (n : ℝ) ^ 2 * W ^ 2 := by
      rw [ENormSqMat]
      calc ∑ i : Fin n, ∑ j : Fin n, Work.Diff.STE.ENormSq 0 (fun x => H x i j)
          = ∑ i : Fin n, ∑ j : Fin n,
              ∫ x in Work.Diff.STE.unitCube, ‖H x i j‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            exact ENormSq_zero_eq _
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, W ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hint i j
        _ = (n : ℝ) ^ 2 * W ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hE1 : (1 : ℝ) ≤ 1 + ENormSqMat 0 G := by linarith [ENormSqMat_nonneg 0 G]
    calc ENormSqMat 0 H ≤ (n : ℝ) ^ 2 * W ^ 2 := hmain
      _ ≤ ((n : ℝ) ^ 2 * W ^ 2 + 1) * (1 + ENormSqMat 0 G) := by
          have h1 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * W ^ 2 := by positivity
          nlinarith [hE1, h1]
  -- main case: `1 ≤ n` and `1 ≤ m`
  obtain ⟨K, hK0, hGN⟩ := hGN
  set USup : ℝ := max 1 U with hUSup
  have hUSup1 : 1 ≤ USup := by rw [hUSup]; exact le_max_left _ _
  have hUUSup : U ≤ USup := by rw [hUSup]; exact le_max_right _ _
  have hUSup0 : 0 ≤ USup := le_trans zero_le_one hUSup1
  set K0 : ℝ := K * USup ^ ((2 : ℝ) * (m : ℝ)) + 1 with hK0def
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]
    have := mul_nonneg hK0 (Real.rpow_nonneg hUSup0 ((2 : ℝ) * (m : ℝ)))
    linarith
  have hK01 : 1 ≤ K0 := by
    rw [hK0def]
    have := mul_nonneg hK0 (Real.rpow_nonneg hUSup0 ((2 : ℝ) * (m : ℝ)))
    linarith
  set Lall : ℝ := (n : ℝ) ^ 2 * (2 : ℝ) ^ m with hLall
  set Bign : ℝ := 1 + K0 + max 1 W + ((n : ℝ) + 1) ^ 2 + (2 : ℝ) ^ m + (Lall + 1)
    with hBign
  have hBign1 : 1 ≤ Bign := by
    rw [hBign]
    have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
    have hmax : (1 : ℝ) ≤ max 1 W := le_max_left 1 W
    have hn2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
    have hL0 : (0 : ℝ) ≤ Lall := by rw [hLall]; positivity
    linarith
  have hBign0 : 0 ≤ Bign := le_trans zero_le_one hBign1
  have hBignK0 : K0 ≤ Bign := by
    rw [hBign]
    have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
    have hmax : (1 : ℝ) ≤ max 1 W := le_max_left 1 W
    have hn2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
    have hL0 : (0 : ℝ) ≤ Lall := by rw [hLall]; positivity
    linarith
  have hBignW1 : max 1 W ≤ Bign := by
    rw [hBign]
    have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
    have hn2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
    have hL0 : (0 : ℝ) ≤ Lall := by rw [hLall]; positivity
    linarith
  have hBignW : W ≤ Bign := le_trans (le_max_right _ _) hBignW1
  have hBignn : (n : ℝ) ≤ Bign := by
    rw [hBign]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hsq : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
    have hmax : (1 : ℝ) ≤ max 1 W := le_max_left 1 W
    have hL0 : (0 : ℝ) ≤ Lall := by rw [hLall]; positivity
    linarith
  have hBignn2 : (n : ℝ) ^ 2 ≤ Bign := by
    rw [hBign]
    have hsq : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
    have hmax : (1 : ℝ) ≤ max 1 W := le_max_left 1 W
    have hL0 : (0 : ℝ) ≤ Lall := by rw [hLall]; positivity
    linarith
  have hBign2m : (2 : ℝ) ^ m ≤ Bign := by
    rw [hBign]
    have hn2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
    have hmax : (1 : ℝ) ≤ max 1 W := le_max_left 1 W
    have hL0 : (0 : ℝ) ≤ Lall := by rw [hLall]; positivity
    linarith
  have hBignLall : Lall ≤ Bign := by
    rw [hBign]
    have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ m := pow_nonneg (by norm_num) m
    have hn2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
    have hmax : (1 : ℝ) ≤ max 1 W := le_max_left 1 W
    linarith
  refine ⟨(n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m * Bign ^ (2 * m * Lam m) + 1,
    by positivity, ?_⟩
  intro G H hG hH hGp hHp hGb hHb hGH
  have hHG : ∀ x : ι → ℝ, Matrix.of (H x) * Matrix.of (G x) = 1 :=
    fun x => mul_eq_one_comm' (hGH x)
  set E : ℝ := ENormSqMat m G with hE
  have hE0 : 0 ≤ E := by rw [hE]; exact ENormSqMat_nonneg m G
  have hE1 : 1 ≤ 1 + E := by linarith
  -- the energy of a single entry of `G` is dominated by `E`
  have hEntry : ∀ (k' m' : Fin n), Work.Diff.STE.ENormSq m (fun y => G y k' m') ≤ E := by
    intro k' m'
    rw [hE, ENormSqMat]
    calc Work.Diff.STE.ENormSq m (fun y => G y k' m')
        ≤ ∑ j : Fin n, Work.Diff.STE.ENormSq m (fun y => G y k' j) :=
          Finset.single_le_sum (f := fun j => Work.Diff.STE.ENormSq m (fun y => G y k' j))
            (fun j _ => ENormSq_nonneg m _) (Finset.mem_univ m')
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, Work.Diff.STE.ENormSq m (fun y => G y i j) :=
          Finset.single_le_sum (f := fun i => ∑ j : Fin n,
            Work.Diff.STE.ENormSq m (fun y => G y i j))
            (fun i _ => Finset.sum_nonneg fun j _ => ENormSq_nonneg m _) (Finset.mem_univ k')
  -- the main induction
  have claim : ∀ k : ℕ, 1 ≤ k → k ≤ m → ∀ (q : Fin k → ι) (i j : Fin n),
      (∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖
        ^ ((2 * (m : ℝ)) / (k : ℝ))) ≤ Bign ^ (2 * m * Lam k) * (1 + E) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih hk1 hkm q i j
    set p : ℝ := (2 * (m : ℝ)) / (k : ℝ) with hp
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hp2 : 2 ≤ p := by
      rw [hp, le_div_iff₀ hkR]
      linarith
    have hp0 : 0 < p := by linarith
    have hpnn : 0 ≤ p := le_of_lt hp0
    have hp1 : 1 ≤ p := by linarith
    have hp_le : p ≤ (2 : ℝ) * (m : ℝ) := by
      rw [hp, div_le_iff₀ hkR]
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      nlinarith [hk1R, show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
    set l : List ι := List.ofFn q with hl
    have hllen : l.length = k := by rw [hl]; exact List.length_ofFn
    set Zt : Fin n → List ι × List ι → Fin n → (ι → ℝ) → ℝ := fun k' pp m' x =>
      ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
        * ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖ with hZt
    set YY : Fin n → (ι → ℝ) → ℝ := fun k' x =>
      ((Work.Diff.STE.splitsNE l).map (fun pp => ∑ m' : Fin n, Zt k' pp m' x)).sum with hYY
    set SS : (ι → ℝ) → ℝ := fun x => ∑ k' : Fin n, YY k' x with hSS
    have hZt0 : ∀ (k' : Fin n) (pp : List ι × List ι) (m' : Fin n) (x : ι → ℝ),
        0 ≤ Zt k' pp m' x :=
      fun k' pp m' x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hYY0 : ∀ (k' : Fin n) (x : ι → ℝ), 0 ≤ YY k' x := by
      intro k' x
      rw [hYY]
      refine List.sum_nonneg fun z hz => ?_
      obtain ⟨pp, _, rfl⟩ := List.mem_map.mp hz
      exact Finset.sum_nonneg fun m' _ => hZt0 k' pp m' x
    have hSS0 : ∀ x : ι → ℝ, 0 ≤ SS x := by
      intro x
      rw [hSS]
      exact Finset.sum_nonneg fun k' _ => hYY0 k' x
    -- the pointwise recursion bound
    have hpoint : ∀ x : ι → ℝ,
        ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ≤ Bign * SS x := by
      intro x
      have hchild := pdVec_inv_le' G H W hG hH hGH hHG hHb k hk1 q i j x
      have hEq : (∑ k' : Fin n, ((Work.Diff.STE.splitsNE (List.ofFn q)).map
            (fun p' => ∑ m' : Fin n, ‖Work.Diff.STE.pdList p'.1 (fun y => G y k' m') x‖
              * ‖Work.Diff.STE.pdList p'.2 (fun y => H y m' j) x‖)).sum) = SS x := by
        simp only [hSS, hYY, hZt, hl]
      rw [hEq] at hchild
      calc ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ≤ W * SS x := hchild
        _ ≤ Bign * SS x := mul_le_mul_of_nonneg_right hBignW (hSS0 x)
    -- continuity of the individual factors
    have contZ : ∀ (a : List ι) (f : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f →
        Continuous (fun x => ‖Work.Diff.STE.pdList a f x‖) := by
      intro a f hf
      have h1 : Work.Diff.STE.pdList a f = Work.Diff.STE.pdVec a.length a.get f := by
        rw [Work.Diff.STE.pdVec, List.ofFn_get]
      rw [h1]
      exact (continuous_pdVec _ _ _ ((hf.of_le (by exact_mod_cast le_top)))).norm
    -- integrability of the terms
    have hZt_int : ∀ (k' : Fin n) (pp : List ι × List ι) (m' : Fin n),
        Integrable (fun x => (Zt k' pp m' x) ^ p)
          (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
      intro k' pp m'
      simp only [hZt]
      refine cm_integrableOn_unitCube_of_continuous ?_
      exact ((contZ pp.1 (fun y => G y k' m') (hG k' m')).mul
        (contZ pp.2 (fun y => H y m' j) (hH m' j))).rpow_const (fun x => Or.inr hpnn)
    -- the pointwise power-mean bound
    have hp_le' : p ≤ ((2 * m : ℕ) : ℝ) := by
      have := hp_le; push_cast at this ⊢; linarith
    have hBp : Bign ^ p ≤ Bign ^ (2 * m) := by
      rw [← Real.rpow_natCast Bign (2 * m)]
      exact Real.rpow_le_rpow_of_exponent_le hBign1 hp_le'
    have hlen_bd : ((Work.Diff.STE.splitsNE l).length : ℝ) ≤ Bign := by
      have h1 : (Work.Diff.STE.splitsNE l).length ≤ 2 ^ k := by
        rw [Work.Diff.STE.splitsNE_eq_filter]
        refine le_trans (List.length_filter_le _ _) ?_
        rw [Work.Diff.STE.cm_splits_length_count, hllen]
      have h1R : ((Work.Diff.STE.splitsNE l).length : ℝ) ≤ ((2 : ℕ) ^ k : ℝ) := by
        exact_mod_cast h1
      have h2 : ((2 : ℕ) ^ k : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
      rw [h2] at h1R
      have h3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hkm
      exact le_trans h1R (le_trans h3 hBign2m)
    have hpm_pt : ∀ x : ι → ℝ, (SS x) ^ p ≤ Bign ^ (6 * m) * (∑ k' : Fin n,
        ((Work.Diff.STE.splitsNE l).map
          (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) := by
      intro x
      have h1 : (SS x) ^ p ≤ ((n : ℝ)) ^ (p - 1) * (∑ k' : Fin n, (YY k' x) ^ p) := by
        rw [hSS]
        have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
          (s := (Finset.univ : Finset (Fin n))) (f := fun k' => YY k' x) hp1
          (fun k' _ => hYY0 k' x)
        have hcard : (((Finset.univ : Finset (Fin n)).card : ℕ) : ℝ) = (n : ℝ) := by
          rw [Finset.card_univ, Fintype.card_fin]
        rw [hcard] at h
        exact h
      have h1b : ((n : ℝ)) ^ (p - 1) ≤ Bign ^ (2 * m) := by
        calc ((n : ℝ)) ^ (p - 1) ≤ Bign ^ (p - 1) :=
              Real.rpow_le_rpow (Nat.cast_nonneg n) hBignn (by linarith)
          _ ≤ Bign ^ ((2 : ℝ) * (m : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hBign1 (by linarith)
          _ = Bign ^ (2 * m) := by
              rw [show ((2 : ℝ) * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
                Real.rpow_natCast]
      have h2 : ∀ k' : Fin n, (YY k' x) ^ p ≤ Bign ^ (2 * m) *
          ((Work.Diff.STE.splitsNE l).map
            (fun pp => (∑ m' : Fin n, Zt k' pp m' x) ^ p)).sum := by
        intro k'
        have h := list_sum_rpow_le hp1
          ((Work.Diff.STE.splitsNE l).map (fun pp => ∑ m' : Fin n, Zt k' pp m' x))
          (fun z hz => by
            obtain ⟨pp, _, rfl⟩ := List.mem_map.mp hz
            exact Finset.sum_nonneg fun m' _ => hZt0 k' pp m' x)
        rw [List.length_map, List.map_map] at h
        have hb2 : ((Work.Diff.STE.splitsNE l).length : ℝ) ^ p ≤ Bign ^ (2 * m) := by
          calc ((Work.Diff.STE.splitsNE l).length : ℝ) ^ p ≤ Bign ^ p :=
                Real.rpow_le_rpow (Nat.cast_nonneg _) hlen_bd hpnn
            _ ≤ Bign ^ ((2 : ℝ) * (m : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le hBign1 (by linarith)
            _ = Bign ^ (2 * m) := by
                rw [show ((2 : ℝ) * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
                  Real.rpow_natCast]
        rw [hYY]
        calc ((Work.Diff.STE.splitsNE l).map (fun pp => ∑ m' : Fin n, Zt k' pp m' x)).sum ^ p
            ≤ ((Work.Diff.STE.splitsNE l).length : ℝ) ^ p *
                ((Work.Diff.STE.splitsNE l).map
                  (fun pp => (∑ m' : Fin n, Zt k' pp m' x) ^ p)).sum := h
          _ ≤ Bign ^ (2 * m) *
                ((Work.Diff.STE.splitsNE l).map
                  (fun pp => (∑ m' : Fin n, Zt k' pp m' x) ^ p)).sum :=
              mul_le_mul_of_nonneg_right hb2 (List.sum_nonneg fun z hz => by
                obtain ⟨pp, _, rfl⟩ := List.mem_map.mp hz
                exact Real.rpow_nonneg (Finset.sum_nonneg fun m' _ => hZt0 k' pp m' x) p)
      have h3 : ∀ (k' : Fin n) (pp : List ι × List ι),
          (∑ m' : Fin n, Zt k' pp m' x) ^ p ≤ Bign ^ (2 * m) *
            (∑ m' : Fin n, (Zt k' pp m' x) ^ p) := by
        intro k' pp
        have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
          (s := (Finset.univ : Finset (Fin n))) (f := fun m' => Zt k' pp m' x) hp1
          (fun m' _ => hZt0 k' pp m' x)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        exact h.trans (mul_le_mul_of_nonneg_right h1b
          (Finset.sum_nonneg fun m' _ => Real.rpow_nonneg (hZt0 k' pp m' x) p))
      have h2' : (∑ k' : Fin n, (YY k' x) ^ p) ≤ Bign ^ (2 * m) * (∑ k' : Fin n,
          ((Work.Diff.STE.splitsNE l).map
            (fun pp => (∑ m' : Fin n, Zt k' pp m' x) ^ p)).sum) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k' _ => h2 k'
      have h3' : (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
            (fun pp => (∑ m' : Fin n, Zt k' pp m' x) ^ p)).sum) ≤
          Bign ^ (2 * m) * (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k' _ => ?_
        rw [← list_sum_map_mul_left' ((Work.Diff.STE.splitsNE l)) (Bign ^ (2 * m))
          (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)]
        exact List.sum_le_sum fun pp _ => h3 k' pp
      have h4m : Bign ^ (2 * m) * Bign ^ (2 * m) = Bign ^ (4 * m) := by
        rw [← pow_add]; congr 1; ring
      have h6m : Bign ^ (4 * m) * Bign ^ (2 * m) = Bign ^ (6 * m) := by
        rw [← pow_add]; congr 1; ring
      have hC : (Bign ^ (2 * m)) * (Bign ^ (2 * m) * (Bign ^ (2 * m) *
          (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum))) =
          Bign ^ (6 * m) * (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) := by
        rw [← mul_assoc, h4m, ← mul_assoc, h6m]
      calc (SS x) ^ p ≤ ((n : ℝ)) ^ (p - 1) * (∑ k' : Fin n, (YY k' x) ^ p) := h1
        _ ≤ Bign ^ (2 * m) * (∑ k' : Fin n, (YY k' x) ^ p) :=
            mul_le_mul_of_nonneg_right h1b (Finset.sum_nonneg fun k' _ =>
              Real.rpow_nonneg (hYY0 k' x) p)
        _ ≤ Bign ^ (2 * m) * (Bign ^ (2 * m) * (∑ k' : Fin n,
              ((Work.Diff.STE.splitsNE l).map
                (fun pp => (∑ m' : Fin n, Zt k' pp m' x) ^ p)).sum)) :=
            mul_le_mul_of_nonneg_left h2' (pow_nonneg hBign0 _)
        _ ≤ Bign ^ (2 * m) * (Bign ^ (2 * m) * (Bign ^ (2 * m) * (∑ k' : Fin n,
              ((Work.Diff.STE.splitsNE l).map
                (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h3' (pow_nonneg hBign0 _)) (pow_nonneg hBign0 _)
        _ = Bign ^ (6 * m) * (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
              (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) := hC
    -- integrate the pointwise bound
    have hGsum_int : Integrable (fun x : ι → ℝ => ∑ k' : Fin n,
        ((Work.Diff.STE.splitsNE l).map
          (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum)
        (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
      refine integrable_finsetSum _ fun k' _ => integrable_list_sum_apply
        ((Work.Diff.STE.splitsNE l)) (fun pp x => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)
        (fun pp _ => integrable_finsetSum _ fun m' _ => hZt_int k' pp m')
    have hintG : ∀ x : ι → ℝ, ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ^ p
        ≤ Bign ^ (2 * m + 6 * m) * (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
          (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) := by
      intro x
      calc ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ^ p
          ≤ (Bign * SS x) ^ p := Real.rpow_le_rpow (norm_nonneg _) (hpoint x) hpnn
        _ = Bign ^ p * (SS x) ^ p := Real.mul_rpow hBign0 (hSS0 x)
        _ ≤ Bign ^ (2 * m) * (SS x) ^ p :=
            mul_le_mul_of_nonneg_right hBp (Real.rpow_nonneg (hSS0 x) p)
        _ ≤ Bign ^ (2 * m) * (Bign ^ (6 * m) * (∑ k' : Fin n,
              ((Work.Diff.STE.splitsNE l).map
                (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum)) :=
            mul_le_mul_of_nonneg_left (hpm_pt x) (pow_nonneg hBign0 _)
        _ = Bign ^ (2 * m + 6 * m) * (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
              (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) := by
            rw [← mul_assoc, ← pow_add]
    have hint1 : (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ^ p) ≤ Bign ^ (2 * m + 6 * m) *
        (∫ x in Work.Diff.STE.unitCube, (∑ k' : Fin n,
          ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum)) := by
      have hmono : (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ^ p)
          ≤ ∫ x in Work.Diff.STE.unitCube, Bign ^ (2 * m + 6 * m) *
              (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
                (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (hGsum_int.const_mul _) (Filter.Eventually.of_forall fun x => hintG x)
      have h2 : (∫ x in Work.Diff.STE.unitCube, Bign ^ (2 * m + 6 * m) *
            (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
              (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum))
          = Bign ^ (2 * m + 6 * m) * (∫ x in Work.Diff.STE.unitCube, (∑ k' : Fin n,
              ((Work.Diff.STE.splitsNE l).map
                (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum)) :=
        integral_const_mul _ _
      linarith [hmono, h2.le]
    have hint2 : (∫ x in Work.Diff.STE.unitCube, (∑ k' : Fin n,
          ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)).sum))
        = (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube,
              (Zt k' pp m' x) ^ p)).sum) := by
      rw [integral_finsetSum _ (fun k' _ => integrable_list_sum_apply
        ((Work.Diff.STE.splitsNE l)) (fun pp x => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)
        (fun pp _ => integrable_finsetSum _ fun m' _ => hZt_int k' pp m'))]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [integral_list_sum_apply ((Work.Diff.STE.splitsNE l))
        (fun pp x => ∑ m' : Fin n, (Zt k' pp m' x) ^ p)
        (fun pp _ => integrable_finsetSum _ fun m' _ => hZt_int k' pp m')]
      exact congrArg List.sum (List.map_congr_left fun pp _ =>
        integral_finsetSum _ fun m' _ => hZt_int k' pp m')
    have hint3 : (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ^ p) ≤ Bign ^ (2 * m + 6 * m) *
        (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
          (fun pp => ∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube,
            (Zt k' pp m' x) ^ p)).sum) := by
      rw [hint2] at hint1
      exact hint1

    -- the per-term bound
    have hterm : ∀ (k' : Fin n) (pp : List ι × List ι), pp ∈ Work.Diff.STE.splitsNE l →
        ∀ (m' : Fin n),
        (∫ x in Work.Diff.STE.unitCube, (Zt k' pp m' x) ^ p)
          ≤ Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) := by
      intro k' pp hpp m'
      have hppS : pp ∈ Work.Diff.STE.splits l := by
        rw [Work.Diff.STE.splitsNE_eq_filter] at hpp
        exact (List.mem_filter.mp hpp).1
      have hne : pp.1 ≠ [] := by
        rw [Work.Diff.STE.splitsNE_eq_filter] at hpp
        exact of_decide_eq_true (List.mem_filter.mp hpp).2
      have hlen0 : pp.1.length + pp.2.length = k := by
        have h := Work.Diff.STE.cm_splits_mem_length l pp hppS
        rw [hllen] at h
        exact h
      have ha1 : 1 ≤ pp.1.length := List.length_pos_of_ne_nil hne
      have hb_lt : pp.2.length < k := by omega
      have hb_le_m : pp.2.length ≤ m := le_trans (le_of_lt hb_lt) hkm
      have hpd1 : Work.Diff.STE.pdList pp.1 (fun y => G y k' m')
          = Work.Diff.STE.pdVec pp.1.length pp.1.get (fun y => G y k' m') := by
        rw [Work.Diff.STE.pdVec, List.ofFn_get]
      have hGNp : ∀ (a : ℕ) (ha : 1 ≤ a) (ham : a ≤ m) (β : Fin a → ι),
          (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec a β (fun y => G y k' m') x‖ ^ ((2 * (m : ℝ)) / (a : ℝ)))
            ≤ K0 * (1 + E) := by
        intro a ha ham β
        have hgn := hGN USup (fun y => G y k' m') (hG k' m') (hGp k' m')
          (fun y => le_trans (hGb y k' m') hUUSup)
        have h := hgn a ha ham β
        have hKb : K * USup ^ ((2 * (m : ℝ)) / (a : ℝ) - 2) ≤ K0 := by
          have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
          have h1 : USup ^ ((2 * (m : ℝ)) / (a : ℝ) - 2) ≤ USup ^ ((2 : ℝ) * (m : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_le hUSup1 ?_
            have hdiv : (2 * (m : ℝ)) / (a : ℝ) ≤ 2 * (m : ℝ) := by
              rw [div_le_iff₀ (by linarith : (0 : ℝ) < (a : ℝ))]
              nlinarith [haR, show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
            linarith
          calc K * USup ^ ((2 * (m : ℝ)) / (a : ℝ) - 2) ≤ K * USup ^ ((2 : ℝ) * (m : ℝ)) :=
                mul_le_mul_of_nonneg_left h1 hK0
            _ ≤ K0 := by rw [hK0def]; linarith
        calc (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec a β (fun y => G y k' m') x‖ ^ ((2 * (m : ℝ)) / (a : ℝ)))
            ≤ K * USup ^ ((2 * (m : ℝ)) / (a : ℝ) - 2) *
                Work.Diff.STE.ENormSq m (fun y => G y k' m') := h
          _ ≤ K0 * Work.Diff.STE.ENormSq m (fun y => G y k' m') :=
              mul_le_mul_of_nonneg_right hKb (ENormSq_nonneg m _)
          _ ≤ K0 * E := mul_le_mul_of_nonneg_left (hEntry k' m') hK00
          _ ≤ K0 * (1 + E) := mul_le_mul_of_nonneg_left (by linarith : E ≤ 1 + E) hK00
      by_cases hpp2 : pp.2 = []
      · -- the `H`-factor is undifferentiated
        have ha : pp.1.length = k := by rw [hpp2] at hlen0; omega
        have hZeq : ∀ x, Zt k' pp m' x = ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
            * ‖H x m' j‖ := by
          intro x
          simp only [hZt, hpp2, Work.Diff.STE.pdList, List.foldr_nil]
        have hstep : ∀ x, (Zt k' pp m' x) ^ p ≤ W ^ p *
            ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p := by
          intro x
          rw [hZeq x, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hHb x m' j) hpnn)
            (Real.rpow_nonneg (norm_nonneg _) p)
        have hIntR : Integrable (fun x => W ^ p *
            ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p)
            (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
          (integrableOn_norm_pdList_rpow hpnn pp.1 _ (hG k' m')).const_mul _
        have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          hIntR (Filter.Eventually.of_forall fun x => hstep x)
        have hEq2 : (∫ x in Work.Diff.STE.unitCube, W ^ p *
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p)
            = W ^ p * (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p) :=
          integral_const_mul _ _
        have hexp : p = ((2 * (m : ℝ)) / (pp.1.length : ℝ)) := by
          rw [hp, ha]
        have hGN1 : (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p) ≤ K0 * (1 + E) := by
          have ha_le : pp.1.length ≤ m := by rw [ha]; exact hkm
          have h := hGNp pp.1.length ha1 ha_le pp.1.get
          rw [← hpd1, ← hexp] at h
          exact h
        have hWp : W ^ p ≤ Bign ^ (2 * m) := by
          calc W ^ p ≤ Bign ^ p := Real.rpow_le_rpow hW hBignW hpnn
            _ ≤ Bign ^ (2 * m) := hBp
        calc (∫ x in Work.Diff.STE.unitCube, (Zt k' pp m' x) ^ p)
            ≤ W ^ p * (∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p) := by
              rw [← hEq2]; exact hmono
          _ ≤ Bign ^ (2 * m) * (K0 * (1 + E)) := by
              have h2 : (0 : ℝ) ≤ 1 + E := by linarith [hE0]
              have h3 : (0 : ℝ) ≤ ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖ ^ p :=
                integral_nonneg fun x => by positivity
              exact mul_le_mul hWp hGN1 h3 (pow_nonneg hBign0 _)
          _ ≤ Bign ^ (2 * m) * (Bign * (1 + E)) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBignK0 ?_)
                (pow_nonneg hBign0 _)
              linarith
          _ = Bign ^ (2 * m + 1) * (1 + E) := by rw [← mul_assoc, ← pow_succ]
          _ ≤ Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) := by
              refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBign1 ?_) (by linarith)
              have : 1 ≤ Lam (k - 1) := Lam_pos _
              omega
      · -- both factors are differentiated
        have hb1 : 1 ≤ pp.2.length := List.length_pos_of_ne_nil hpp2
        have hratio : ((pp.1.length : ℝ) / (k : ℝ)) + ((pp.2.length : ℝ) / (k : ℝ)) = 1 := by
          rw [← add_div, ← Nat.cast_add, hlen0, div_self (by positivity : (k : ℝ) ≠ 0)]
        have hpd2 : Work.Diff.STE.pdList pp.2 (fun y => H y m' j)
            = Work.Diff.STE.pdVec pp.2.length pp.2.get (fun y => H y m' j) := by
          rw [Work.Diff.STE.pdVec, List.ofFn_get]
        have hagm : ∀ x, (Zt k' pp m' x) ^ p ≤ ((pp.1.length : ℝ) / (k : ℝ)) *
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ))
            + ((pp.2.length : ℝ) / (k : ℝ)) *
              ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ)) := by
          intro x
          have h := rpow_mul_le_amgm (u := ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖)
            (v := ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖)
            (m := m) (k := k) (a := pp.1.length) (b := pp.2.length)
            (norm_nonneg _) (norm_nonneg _) hk1 ha1 hb1 hlen0
          simpa only [hZt, hp] using h
        have hIntR : Integrable (fun x => ((pp.1.length : ℝ) / (k : ℝ)) *
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ))
            + ((pp.2.length : ℝ) / (k : ℝ)) *
              ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ)))
            (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
          ((integrableOn_norm_pdList_rpow (by positivity) pp.1 _ (hG k' m')).const_mul _).add
            ((integrableOn_norm_pdList_rpow (by positivity) pp.2 _ (hH m' j)).const_mul _)
        have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          hIntR (Filter.Eventually.of_forall fun x => hagm x)
        have hIntR1 : Integrable (fun x => ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ)))
            (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
          integrableOn_norm_pdList_rpow (by positivity) pp.1 _ (hG k' m')
        have hIntR2 : Integrable (fun x => ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ)))
            (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
          integrableOn_norm_pdList_rpow (by positivity) pp.2 _ (hH m' j)
        have hEq2 : (∫ x in Work.Diff.STE.unitCube, ((pp.1.length : ℝ) / (k : ℝ)) *
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ))
            + ((pp.2.length : ℝ) / (k : ℝ)) *
              ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ)))
            = ((pp.1.length : ℝ) / (k : ℝ)) * (∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                  ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ)))
              + ((pp.2.length : ℝ) / (k : ℝ)) * (∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                  ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ))) := by
          rw [integral_add (hIntR1.const_mul _) (hIntR2.const_mul _),
            integral_const_mul, integral_const_mul]
        have hA : (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ))) ≤ K0 * (1 + E) := by
          have ha_le : pp.1.length ≤ m := by omega
          have h := hGNp pp.1.length ha1 ha_le pp.1.get
          rw [← hpd1] at h
          exact h
        have hB : (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ)))
            ≤ Bign ^ (2 * m * Lam (pp.2.length)) * (1 + E) := by
          have h := ih pp.2.length hb_lt hb1 hb_le_m pp.2.get m' j
          rw [← hpd2] at h
          exact h
        have hBle : (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ)))
            ≤ Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) := by
          refine le_trans hB (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBign1 ?_) (by linarith))
          have hmono : pp.2.length ≤ k - 1 := by omega
          have hL : Lam (pp.2.length) ≤ Lam (k - 1) := Lam_mono hmono
          nlinarith [hL, Nat.zero_le (2 * m)]
        have h1 : ((pp.1.length : ℝ) / (k : ℝ)) * (K0 * (1 + E))
            ≤ ((pp.1.length : ℝ) / (k : ℝ)) *
              (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc K0 * (1 + E) ≤ Bign * (1 + E) :=
                mul_le_mul_of_nonneg_right hBignK0 (by linarith)
            _ ≤ Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) := by
                refine mul_le_mul_of_nonneg_right ?_ (by linarith)
                have hexp1 : 1 ≤ Lam (k - 1) * (2 * m) + 2 * m + 1 := by
                  have := Lam_pos (k - 1); omega
                simpa using pow_le_pow_right₀ hBign1 hexp1
        calc (∫ x in Work.Diff.STE.unitCube, (Zt k' pp m' x) ^ p)
            ≤ (∫ x in Work.Diff.STE.unitCube, ((pp.1.length : ℝ) / (k : ℝ)) *
                  ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                    ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ))
                + ((pp.2.length : ℝ) / (k : ℝ)) *
                  ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                    ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ))) := hmono
          _ = ((pp.1.length : ℝ) / (k : ℝ)) * (∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdList pp.1 (fun y => G y k' m') x‖
                    ^ ((2 * (m : ℝ)) / (pp.1.length : ℝ)))
              + ((pp.2.length : ℝ) / (k : ℝ)) * (∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdList pp.2 (fun y => H y m' j) x‖
                    ^ ((2 * (m : ℝ)) / (pp.2.length : ℝ))) := hEq2
          _ ≤ ((pp.1.length : ℝ) / (k : ℝ)) * (K0 * (1 + E))
              + ((pp.2.length : ℝ) / (k : ℝ)) *
                (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) :=
              add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
                (mul_le_mul_of_nonneg_left hBle (by positivity))
          _ ≤ ((pp.1.length : ℝ) / (k : ℝ)) *
                (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E))
              + ((pp.2.length : ℝ) / (k : ℝ)) *
                (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) :=
              add_le_add h1 le_rfl
          _ = (((pp.1.length : ℝ) / (k : ℝ)) + ((pp.2.length : ℝ) / (k : ℝ))) *
                (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) := by ring
          _ = Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) := by rw [hratio, one_mul]
    -- the sum of the per-term bounds
    have hsum : (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
          (fun pp => ∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube,
            (Zt k' pp m' x) ^ p)).sum)
        ≤ ((n : ℝ) * ((Work.Diff.STE.splitsNE l).length : ℝ) * (n : ℝ))
            * (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) := by
      have hc : (0 : ℝ) ≤ Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) :=
        mul_nonneg (pow_nonneg hBign0 _) (by linarith)
      have hinner : ∀ (k' : Fin n) (pp : List ι × List ι), pp ∈ Work.Diff.STE.splitsNE l →
          (∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube, (Zt k' pp m' x) ^ p)
            ≤ (n : ℝ) * (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) := by
        intro k' pp hpp
        calc (∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube, (Zt k' pp m' x) ^ p)
            ≤ ∑ _m' : Fin n, Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E) :=
              Finset.sum_le_sum fun m' _ => hterm k' pp hpp m'
          _ = (n : ℝ) * (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
            (fun pp => ∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube, (Zt k' pp m' x) ^ p)).sum)
          ≤ ∑ _k' : Fin n, (((Work.Diff.STE.splitsNE l).map
              (fun _pp => (n : ℝ) *
                (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)))).sum) := by
            refine Finset.sum_le_sum fun k' _ => ?_
            exact List.sum_le_sum fun pp hpp => hinner k' pp hpp
        _ = (n : ℝ) * ((Work.Diff.STE.splitsNE l).length : ℝ) *
              ((n : ℝ) * (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, list_sum_const]
            ring
        _ = ((n : ℝ) * ((Work.Diff.STE.splitsNE l).length : ℝ) * (n : ℝ))
              * (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)) := by ring
    -- the counting bound
    have hcnt : (n : ℝ) * ((Work.Diff.STE.splitsNE l).length : ℝ) * (n : ℝ) ≤ Bign ^ 3 := by
      have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      calc (n : ℝ) * ((Work.Diff.STE.splitsNE l).length : ℝ) * (n : ℝ)
          ≤ Bign * Bign * Bign :=
            mul_le_mul (mul_le_mul hBignn hlen_bd (Nat.cast_nonneg _) hBign0) hBignn
              (Nat.cast_nonneg _) (mul_nonneg hBign0 hBign0)
        _ = Bign ^ 3 := by ring
    -- the exponent comparison
    have hexp2 : 2 * m + 6 * m + 3 + (Lam (k - 1) * (2 * m) + 2 * m + 1) ≤ 2 * m * Lam k := by
      have hLam : Lam (k - 1) + 8 ≤ Lam k := by
        have h := Lam_succ (k - 1)
        rwa [Nat.sub_add_cancel hk1] at h
      have hm1 : 1 ≤ m := hmpos
      nlinarith [hLam, hm1, Nat.zero_le (Lam (k - 1)), Nat.zero_le m, Nat.zero_le k]
    -- assembly of the induction step
    calc (∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k q (fun y => H y i j) x‖ ^ p)
        ≤ Bign ^ (2 * m + 6 * m) * (∑ k' : Fin n, ((Work.Diff.STE.splitsNE l).map
              (fun pp => ∑ m' : Fin n, ∫ x in Work.Diff.STE.unitCube,
                (Zt k' pp m' x) ^ p)).sum) := hint3
      _ ≤ Bign ^ (2 * m + 6 * m) * (((n : ℝ) * ((Work.Diff.STE.splitsNE l).length : ℝ)
            * (n : ℝ)) * (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E))) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg hBign0 _)
      _ ≤ Bign ^ (2 * m + 6 * m) * (Bign ^ 3 *
            (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcnt ?_)
            (pow_nonneg hBign0 _)
          exact mul_nonneg (pow_nonneg hBign0 _) (by linarith)
      _ = Bign ^ (2 * m + 6 * m + 3 + (Lam (k - 1) * (2 * m) + 2 * m + 1)) * (1 + E) := by
          have hassoc : Bign ^ (2 * m + 6 * m) * (Bign ^ 3 *
                (Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1) * (1 + E)))
              = (Bign ^ (2 * m + 6 * m) * Bign ^ 3 *
                Bign ^ (Lam (k - 1) * (2 * m) + 2 * m + 1)) * (1 + E) := by ring
          rw [hassoc, ← pow_add, ← pow_add]
      _ ≤ Bign ^ (2 * m * Lam k) * (1 + E) := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBign1 hexp2) (by linarith)
    -- the final term of the claim
  -- assembly over the matrix entries
  have hfinal : ENormSqMat m H ≤ (n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m *
      Bign ^ (2 * m * Lam m) * (1 + E) := by
    rw [ENormSqMat]
    simp only [Work.Diff.STE.ENormSq]
    calc ∑ i : Fin n, ∑ j : Fin n, ∑ _q : Fin m → ι,
          ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m _q (fun y => H y i j) x‖ ^ 2
        ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _q : Fin m → ι,
            Bign ^ (2 * m * Lam m) * (1 + E) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            Finset.sum_le_sum fun qq _ => ?_
          have h := claim m hmpos (le_refl m) qq i j
          have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hmpos)
          have hExp : ((2 * (m : ℝ)) / (m : ℝ)) = 2 := by
            rw [mul_div_assoc, div_self hmR, mul_one]
          have hfe : (fun x : ι → ℝ =>
                ‖Work.Diff.STE.pdVec m qq (fun y => H y i j) x‖ ^ ((2 * (m : ℝ)) / (m : ℝ)))
              = fun x : ι → ℝ => ‖Work.Diff.STE.pdVec m qq (fun y => H y i j) x‖ ^ 2 := by
            funext x
            rw [hExp, Real.rpow_ofNat]
          rw [hfe] at h
          exact h
      _ = (n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m *
            (Bign ^ (2 * m * Lam m) * (1 + E)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun,
            nsmul_eq_mul, Nat.cast_pow]
          ring
      _ = (n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m * Bign ^ (2 * m * Lam m) * (1 + E) := by
          ring
  calc ENormSqMat m H ≤ ((n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m * Bign ^ (2 * m * Lam m))
        * (1 + E) := hfinal
    _ ≤ ((n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m * Bign ^ (2 * m * Lam m) + 1) * (1 + E) := by
        have h1 : (0 : ℝ) ≤ 1 + E := by linarith
        have h2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m * Bign ^ (2 * m * Lam m) :=
          by positivity
        nlinarith [h1, h2]
    _ = ((n : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ m * Bign ^ (2 * m * Lam m) + 1)
        * (1 + ENormSqMat m G) := by rw [hE]

end Work.Diff.STE.B3

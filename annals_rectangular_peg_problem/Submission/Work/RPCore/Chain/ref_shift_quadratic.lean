import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.ref_action_quadratic

/-!
# C4: removing the linear part of the reference chain action by a translation

The reference chain action `chainAction n (refGF N δ)` is the quadratic-plus-linear function
`z ↦ BvForm n N δ z z / 2 + Lav n N δ z` (see `ref_action_quadratic`).  Since the polar form
`BvForm n N δ` has the diagonal line `ℝ ∙ diagVec n` as kernel (`refForm_kernel`) and `Lav`
vanishes on it, the linear part can be removed by translating the variables: there is a shift
`w` with `BvForm n N δ w z + Lav n N δ z = 0` for all `z`, and then

`chainAction n (refGF N δ) z = BvForm n N δ (z - w) (z - w) / 2 + chainAction n (refGF N δ) w`.

This file constructs `w` explicitly.  The only linear functional that has to be matched is
`Lav z = -δ ∑_{j ∈ middle} (z.2 j).2`, so it suffices to take a shift with vanishing momenta,
vanishing first angular coordinate, and second angular coordinate `φ` whose successive
differences are `δ` on the middle block and `0` outside it:

`φ k = δ · #{i < k : N ≤ i < 2N}`.

Indeed `BvForm n N δ w z = ∑_j (z.2 j).2 · (φ (j+1) - φ j) = δ ∑_{j ∈ middle} (z.2 j).2
= - Lav n N δ z`.

## Main additions

* `phi`, `wvec` — the angular profile and the shift vector;
* `BvForm_eq` together with the bilinearity (`Q*_sub_left/right`, `BvForm_polar`) of `BvForm`,
  packaged through the three summands `Q1`, `Q2`, `Q3`;
* `BvForm_wvec_left`, `BvForm_wvec_right` — the annihilation identities for the shift;
* `ref_shift_quadratic` — the requested statement.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

/-- Angular profile of the shift: `δ` times the number of indices `i < k` that lie in the middle
block `N ≤ i < 2N`.  Its successive differences are `δ` on the middle block and `0` elsewhere. -/
private def phi (N : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  δ * ∑ i ∈ Finset.range k, (if midBlock N i then (1 : ℝ) else 0)

/-- The shift vector: vanishing momenta, vanishing `q₁`-coordinate, and angular coordinate `phi`.
It is the vector representing the linear functional `- Lav n N δ` under `BvForm n N δ`. -/
private def wvec (n N : ℕ) (δ : ℝ) : ChainSp n :=
  (fun k => ((0 : ℝ), phi N δ (k : ℕ)), fun _ => 0)

private theorem phi_succ_sub (N : ℕ) (δ : ℝ) (n : ℕ) (j : Fin n) :
    phi N δ ((j.succ : Fin (n + 1)) : ℕ) - phi N δ ((j.castSucc : Fin (n + 1)) : ℕ)
      = δ * (if midBlock N (j : ℕ) then (1 : ℝ) else 0) := by
  unfold phi
  rw [Fin.val_succ, Fin.val_castSucc]
  rw [Finset.sum_range_succ]
  ring

/-! ### The three summands of `BvForm` and their bilinearity -/

/-- The first (trivial) summand of `BvForm n N δ`: the linearised chain action of the identity
steps. -/
private def Q1 (n : ℕ) (z z' : ChainSp n) : ℝ :=
  ∑ j : Fin n,
    ((z.2 j).1 * ((z'.1 j.succ).1 - (z'.1 j.castSucc).1) +
     (z'.2 j).1 * ((z.1 j.succ).1 - (z.1 j.castSucc).1) +
     (z.2 j).2 * ((z'.1 j.succ).2 - (z'.1 j.castSucc).2) +
     (z'.2 j).2 * ((z.1 j.succ).2 - (z.1 j.castSucc).2))

/-- The second summand of `BvForm n N δ` (the middle-block cross term in `q₁` and `p₁`). -/
private def Q2 (n N : ℕ) (z z' : ChainSp n) : ℝ :=
  ∑ j : Fin n,
    (if midBlock N (j : ℕ) then
       ((z.1 j.castSucc).1 * (z'.2 j).1 + (z'.1 j.castSucc).1 * (z.2 j).1) else 0)

/-- The third summand of `BvForm n N δ` (the middle-block quadratic term in `q₁` and `p₁`). -/
private def Q3 (n N : ℕ) (z z' : ChainSp n) : ℝ :=
  ∑ j : Fin n,
    (if midBlock N (j : ℕ) then
       ((z.1 j.castSucc).1 * (z'.1 j.castSucc).1 + (z.2 j).1 * (z'.2 j).1) else 0)

private theorem BvForm_eq (n N : ℕ) (δ : ℝ) (z z' : ChainSp n) :
    BvForm n N δ z z' = Q1 n z z' - (1 / Real.cos δ - 1) * Q2 n N z z'
      + Real.tan δ * Q3 n N z z' := rfl

private theorem Q1_sub_left (n) (a b c : ChainSp n) :
    Q1 n (a - b) c = Q1 n a c - Q1 n b c := by
  unfold Q1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]; ring

private theorem Q1_sub_right (n) (a c d : ChainSp n) :
    Q1 n a (c - d) = Q1 n a c - Q1 n a d := by
  unfold Q1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]; ring

private theorem Q2_sub_left (n N) (a b c : ChainSp n) :
    Q2 n N (a - b) c = Q2 n N a c - Q2 n N b c := by
  unfold Q2
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]
  split_ifs <;> ring

private theorem Q2_sub_right (n N) (a c d : ChainSp n) :
    Q2 n N a (c - d) = Q2 n N a c - Q2 n N a d := by
  unfold Q2
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]
  split_ifs <;> ring

private theorem Q3_sub_left (n N) (a b c : ChainSp n) :
    Q3 n N (a - b) c = Q3 n N a c - Q3 n N b c := by
  unfold Q3
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]
  split_ifs <;> ring

private theorem Q3_sub_right (n N) (a c d : ChainSp n) :
    Q3 n N a (c - d) = Q3 n N a c - Q3 n N a d := by
  unfold Q3
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]
  split_ifs <;> ring

private theorem Q1_polar (n : ℕ) (z w : ChainSp n) :
    Q1 n (z - w) (z - w) = Q1 n z z - Q1 n z w - Q1 n w z + Q1 n w w := by
  rw [Q1_sub_left, Q1_sub_right, Q1_sub_right]; ring

private theorem Q2_polar (n N : ℕ) (z w : ChainSp n) :
    Q2 n N (z - w) (z - w) = Q2 n N z z - Q2 n N z w - Q2 n N w z + Q2 n N w w := by
  rw [Q2_sub_left, Q2_sub_right, Q2_sub_right]; ring

private theorem Q3_polar (n N : ℕ) (z w : ChainSp n) :
    Q3 n N (z - w) (z - w) = Q3 n N z z - Q3 n N z w - Q3 n N w z + Q3 n N w w := by
  rw [Q3_sub_left, Q3_sub_right, Q3_sub_right]; ring

/-- `BvForm n N δ` is a symmetric bilinear form: its polarisation at `z - w` is the expected
expansion.  (Only bilinearity in the form of the two subtraction rules is needed.) -/
private theorem BvForm_polar (n N : ℕ) (δ : ℝ) (z w : ChainSp n) :
    BvForm n N δ (z - w) (z - w)
      = BvForm n N δ z z - BvForm n N δ z w - BvForm n N δ w z + BvForm n N δ w w := by
  rw [BvForm_eq, BvForm_eq, BvForm_eq, BvForm_eq, BvForm_eq]
  rw [Q1_polar, Q2_polar, Q3_polar]
  ring

/-! ### The shift annihilates `Lav` -/

private theorem BvForm_wvec_left (n N : ℕ) (δ : ℝ) (z : ChainSp n) :
    BvForm n N δ (wvec n N δ) z + Lav n N δ z = 0 := by
  unfold BvForm Lav wvec
  simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  simp only [ite_self, Finset.sum_const_zero, mul_zero, add_zero]
  have h1 : ∀ x : Fin n, (z.2 x).2 * (phi N δ ↑x.succ - phi N δ ↑x.castSucc)
      = δ * (if midBlock N (x : ℕ) then (z.2 x).2 else 0) := by
    intro x
    rw [phi_succ_sub]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [← Finset.mul_sum]
  ring

private theorem BvForm_wvec_right (n N : ℕ) (δ : ℝ) (z : ChainSp n) :
    BvForm n N δ z (wvec n N δ) + Lav n N δ z = 0 := by
  unfold BvForm Lav wvec
  simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  simp only [ite_self, Finset.sum_const_zero, mul_zero, add_zero]
  have h1 : ∀ x : Fin n, (z.2 x).2 * (phi N δ ↑x.succ - phi N δ ↑x.castSucc)
      = δ * (if midBlock N (x : ℕ) then (z.2 x).2 else 0) := by
    intro x
    rw [phi_succ_sub]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [← Finset.mul_sum]
  ring

/-- **C4.**  The reference chain action `chainAction n (refGF N δ) = BvForm n N δ · · / 2 + Lav`
can be put in purely quadratic form by translating along the shift `wvec n N δ`, which kills the
linear part `Lav`. -/
theorem ref_shift_quadratic (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (hcos : Real.cos δ ≠ 0) (hsin : Real.sin ((N : ℝ) * δ) ≠ 0) :
    ∃ w : Work.RPCore.Chain.ChainSp n,
      (∀ z, Work.RPCore.Chain.BvForm n N δ w z + Work.RPCore.Chain.Lav n N δ z = 0) ∧
      (∀ z, Work.RPV.chainAction n (fun j => Work.RPCore.Chain.refGF N δ (j : ℕ)) z.1 z.2
        = Work.RPCore.Chain.BvForm n N δ (z - w) (z - w) / 2
          + Work.RPV.chainAction n (fun j => Work.RPCore.Chain.refGF N δ (j : ℕ)) w.1 w.2) := by
  refine ⟨wvec n N δ, fun z => BvForm_wvec_left n N δ z, ?_⟩
  intro z
  have hwl : BvForm n N δ (wvec n N δ) z + Lav n N δ z = 0 := BvForm_wvec_left n N δ z
  have hwr : BvForm n N δ z (wvec n N δ) + Lav n N δ z = 0 := BvForm_wvec_right n N δ z
  have hww : BvForm n N δ (wvec n N δ) (wvec n N δ) + Lav n N δ (wvec n N δ) = 0 :=
    BvForm_wvec_left n N δ (wvec n N δ)
  have hpol := BvForm_polar n N δ z (wvec n N δ)
  rw [ref_action_quadratic n N hN hn δ z, ref_action_quadratic n N hN hn δ (wvec n N δ)]
  rw [hpol]
  rw [show BvForm n N δ (wvec n N δ) z = - Lav n N δ z by linarith,
      show BvForm n N δ z (wvec n N δ) = - Lav n N δ z by linarith,
      show BvForm n N δ (wvec n N δ) (wvec n N δ) = - Lav n N δ (wvec n N δ) by linarith]
  ring

end

end Work.RPCore.Chain

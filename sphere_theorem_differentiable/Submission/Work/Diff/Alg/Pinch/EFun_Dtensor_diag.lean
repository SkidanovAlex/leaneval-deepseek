import Mathlib
import Submission.Work.Diff.Alg.Pinch.DiagDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The isotropic-curvature form of the Böhm–Wilking tensor for diagonal Ricci

For a curvature array `S` whose Ricci tensor is diagonal (`ric S i j = 0` for `i ≠ j`), every
tensor appearing in the Böhm–Wilking difference tensor `Work.Diff.Alg.Pinch.Dtensor` is a
Kulkarni–Nomizu product of *diagonal* tensors.  Composing the master evaluation
`Work.Diff.Alg.Pinch.EFun_knProd_diag` with additivity/homogeneity of `EFun`
(`EFun_add_lin`, `EFun_smul_lin`) and the symmetry of `Zf` (`Zf_symm`) therefore identifies

`EFun (Dtensor n b S) x y z w` with the double sum `∑ᵢⱼ Wt n b S i j · Zf x y z w i j`

of the Böhm–Wilking pair weights `Wt` (`d_ij` of Böhm–Wilking Corollary 2.3).  The proof is
purely algebraic: with `mᵢ = ric0 S i i`, `λⱼ = ric S j j` and `F = ∑ₖ mₖ²`,

* `ric0 S = diag m` and `ric S = diag λ` are diagonal (`ric0` differs from `ric` by a multiple of
  the identity, `id2`);
* `ric0sq S = diag (mᵢ²)` and `ric0Frob2 S = ∑ₖ mₖ²`;
* `EFun_knProd_diag` turns the four terms into `∑ᵢⱼ mᵢmⱼZfᵢⱼ`, `∑ᵢⱼ λᵢλⱼZfᵢⱼ`,
  `2b²∑ᵢⱼ mᵢ²Zfᵢⱼ` and `c₃ F ∑ᵢⱼ Zfᵢⱼ`, with `c₃ = bwC n b` (`dtensorCoeff_eq_bwC`);
* `∑ᵢⱼ mᵢ²Zfᵢⱼ = ∑ᵢⱼ mⱼ²Zfᵢⱼ` (`Finset.sum_comm` plus `Zf_symm`) symmetrizes the `b²` term into
  `b² ∑ᵢⱼ (mᵢ²+mⱼ²)Zfᵢⱼ`, which is the third coefficient of `Wt`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open Work.Diff.Alg.Q2P (EFun)

variable {n : ℕ}

/-- Summation of a diagonal product against the two Kronecker deltas. -/
private lemma sum_diag_mul_diag {n : ℕ} (u v : Fin n → ℝ) (i j : Fin n) :
    (∑ k, (if i = k then u i else 0) * (if k = j then v k else 0))
      = if i = j then u i * v i else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      have hki : ¬ (i = k) := fun hh => hk hh.symm
      simp [hki]
    · intro hm; exact absurd (Finset.mem_univ i) hm
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i = k
    · rw [if_pos hk]
      have hkj : ¬ (k = j) := fun hh => h (hk.trans hh)
      simp [hkj]
    · simp [hk]

/-- The four terms of `Dtensor` on a diagonal Ricci tensor, expanded into a single double sum
(with the `b²` term still in asymmetric form). -/
private lemma combine4 {n : ℕ} (c1 c2 c3 c4 : ℝ) (A B C D : Fin n → Fin n → ℝ) :
    c1 * (∑ i, ∑ j, A i j) + c2 * (∑ i, ∑ j, B i j) + c3 * (∑ i, ∑ j, C i j)
        + c4 * (∑ i, ∑ j, D i j)
      = ∑ i, ∑ j, (c1 * A i j + c2 * B i j + c3 * C i j + c4 * D i j) := by
  have hinner : ∀ i, c1 * (∑ j, A i j) + c2 * (∑ j, B i j) + c3 * (∑ j, C i j)
      + c4 * (∑ j, D i j)
      = ∑ j, (c1 * A i j + c2 * B i j + c3 * C i j + c4 * D i j) := by
    intro i
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc c1 * (∑ i, ∑ j, A i j) + c2 * (∑ i, ∑ j, B i j) + c3 * (∑ i, ∑ j, C i j)
        + c4 * (∑ i, ∑ j, D i j)
      = ∑ i, (c1 * (∑ j, A i j) + c2 * (∑ j, B i j) + c3 * (∑ j, C i j)
          + c4 * (∑ j, D i j)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (c1 * A i j + c2 * B i j + c3 * C i j + c4 * D i j) :=
        Finset.sum_congr rfl (fun i _ => hinner i)

theorem EFun_Dtensor_diag (n : ℕ) (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Curv4 n} (hdiag : ∀ i j : Fin n, i ≠ j → ric S i j = 0) (x y z w : Fin n → ℝ) :
    EFun (Dtensor n b S) x y z w = ∑ i, ∑ j, Wt n b S i j * Zf x y z w i j := by
  classical
  -- diagonal forms of the relevant tensors
  have hl : ric S = fun i j => if i = j then ric S i i else 0 := by
    funext i j
    by_cases h : i = j
    · subst h; simp
    · simp [hdiag i j h, h]
  have hm : ric0 S = fun i j => if i = j then ric0 S i i else 0 := by
    funext i j
    by_cases h : i = j
    · subst h; simp [ric0, id2]
    · have h1 : ric S i j = 0 := hdiag i j h
      simp [ric0, id2, h, h1]
  have hq : ric0sq S = fun i j => if i = j then (ric0 S i i) ^ 2 else 0 := by
    funext i j
    rw [ric0sq, hm]
    simpa [pow_two] using sum_diag_mul_diag (fun k => ric0 S k k) (fun k => ric0 S k k) i j
  have hf : ric0Frob2 S = ∑ k, (ric0 S k k) ^ 2 := by
    rw [ric0Frob2, hm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j _ hj
      have hji : ¬ (i = j) := fun hh => hj hh.symm
      simp [hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- the value of `EFun` on each of the four `knProd` summands
  have e1 : EFun (knProd (ric0 S) (ric0 S)) x y z w
      = ∑ i, ∑ j, (ric0 S i i * ric0 S j j) * Zf x y z w i j := by
    conv_lhs => rw [hm]
    rw [EFun_knProd_diag n (fun k => ric0 S k k) (fun k => ric0 S k k) x y z w]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [Zf]
  have e2 : EFun (knProd (ric S) (ric S)) x y z w
      = ∑ i, ∑ j, (ric S i i * ric S j j) * Zf x y z w i j := by
    conv_lhs => rw [hl]
    rw [EFun_knProd_diag n (fun k => ric S k k) (fun k => ric S k k) x y z w]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [Zf]
  have e3 : EFun (knProd (ric0sq S) (id2 n)) x y z w
      = ∑ i, ∑ j, (ric0 S i i) ^ 2 * Zf x y z w i j := by
    conv_lhs => rw [hq]
    rw [show id2 n = (fun i j : Fin n => if i = j then (1 : ℝ) else 0) from rfl]
    rw [EFun_knProd_diag n (fun k => (ric0 S k k) ^ 2) (fun _ => (1 : ℝ)) x y z w]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [Zf]
    ring
  have e4 : EFun (knProd (id2 n) (id2 n)) x y z w = ∑ i, ∑ j, Zf x y z w i j := by
    rw [show id2 n = (fun i j : Fin n => if i = j then (1 : ℝ) else 0) from rfl]
    rw [EFun_knProd_diag n (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) x y z w]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [Zf]
    ring
  -- unfold `Dtensor` and distribute `EFun`
  rw [Dtensor]
  rw [EFun_add_lin, EFun_add_lin, EFun_add_lin,
    EFun_smul_lin, EFun_smul_lin, EFun_smul_lin, EFun_smul_lin]
  rw [e1, e2, e3, e4]
  rw [hf, dtensorCoeff_eq_bwC hn2 hb hb']
  -- symmetrize the `b²` term
  have hsplit : (∑ i, ∑ j, ((ric0 S i i) ^ 2 + (ric0 S j j) ^ 2) * Zf x y z w i j)
      = (∑ i, ∑ j, (ric0 S i i) ^ 2 * Zf x y z w i j)
        + (∑ i, ∑ j, (ric0 S j j) ^ 2 * Zf x y z w i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hswap : (∑ i, ∑ j, (ric0 S j j) ^ 2 * Zf x y z w i j)
      = (∑ i, ∑ j, (ric0 S i i) ^ 2 * Zf x y z w i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Zf_symm x y z w]
  have hsym22 : 2 * (∑ i, ∑ j, (ric0 S i i) ^ 2 * Zf x y z w i j)
      = (∑ i, ∑ j, ((ric0 S i i) ^ 2 + (ric0 S j j) ^ 2) * Zf x y z w i j) := by
    rw [hsplit, hswap]; ring
  have hsym : (2 * b ^ 2) * (∑ i, ∑ j, (ric0 S i i) ^ 2 * Zf x y z w i j)
      = b ^ 2 * (∑ i, ∑ j, ((ric0 S i i) ^ 2 + (ric0 S j j) ^ 2) * Zf x y z w i j) := by
    rw [← hsym22]; ring
  rw [hsym, combine4]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [Wt, ric0, id2, if_true]
  ring

end Work.Diff.Alg.Pinch

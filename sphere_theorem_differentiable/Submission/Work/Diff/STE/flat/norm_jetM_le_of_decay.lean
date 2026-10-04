import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.flat.CSq_le_of_decay
import Submission.Work.Diff.STE.flat.pd_seriesFun_of_summable
import Submission.Work.Diff.STE.fill.tsum_norm_dmulV_le_of_decay

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A quantitative sup bound for the spatial `2`-jet of a decaying Fourier family

`Work.Diff.STE.flat.norm_jetM_le_of_decay`: if a **single** coefficient family
`c : (Fin n → ℤ) → MatC n` satisfies the pointwise decay bound

  `‖c k a b‖ * ⟨k⟩^{2M} ≤ C`   for all `k, a, b`,

where `⟨k⟩² = wt k = 1 + Σ kᵢ²` and the order `M` dominates the dimension
(`n + 4 < 2 * M`), then the spatial `2`-jet of the associated Fourier series is bounded by a
constant *linear in `C`*,

  `‖jetM (seriesFunM c) x‖ ≤ C' * C`,

with a constant `C'` depending only on `n` and `M`.

## The proof

`M ≫ n` makes the coefficient family `ℓ¹` with all the polynomial weights of degree `≤ 2`; this is
a purely elementary `ℓ¹` (rather than `ℓ²`/Sobolev) argument, so no Gårding/Sobolev machinery is
needed.  Concretely, the decay bound gives the pointwise majorant

  `⟨k⟩^{2j} ‖c k a b‖ ≤ C · ⟨k⟩^{-2(M-j)}`   for `j ≤ 2`,

and `∑_k ⟨k⟩^{-2(M-2)} < ∞` precisely because `n < 2 (M - 2)`, i.e. `n + 4 < 2M`
(`Work.Diff.STE.summable_wt_inv'`).  Term by term differentiation of the Fourier series
(`Work.Diff.STE.flat.pd_seriesFun_of_summable`, the `N = 1` form of `Work.Diff.STE.pd_seriesFun`)
identifies the iterated derivative of length `≤ 2` with the Fourier series of the multiplicatively
weighted family (`Work.Diff.STE.dmulV`, whose norm is controlled by
`Work.Diff.STE.norm_dmulV_le`), and the weights are absorbed by
`Work.Diff.STE.flat.tsum_norm_dmulV_le_of_decay`.  The three components of `jetM` are then
recombined entrywise by `norm_jetM_le_of_entrywise`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators

variable {n : ℕ}

/-! ## The two analytic inputs

Both are provided by the neighbourhood: `Work.Diff.STE.flat.pd_seriesFun_of_summable` (term by term
differentiation under the single summability hypothesis `Summable (fun k => wt k * ‖γ k‖)`) and
`Work.Diff.STE.flat.tsum_norm_dmulV_le_of_decay` (the weighted `ℓ¹` estimate for the differentiated
coefficient family).  They are recorded here under local names so that the assembly below is
self-contained. -/

/-- Term by term differentiation of a Fourier series, under the single hypothesis
`Summable (fun k => ⟨k⟩² ‖γ k‖)`: the `i`-th partial derivative of `seriesFun γ` is the Fourier
series of the coefficient family `dmul i γ` (`k ↦ 2πi kᵢ γ k`).  This is
`Work.Diff.STE.pd_seriesFun` with the hypothesis `∀ N, Summable (fun k => ⟨k⟩^N ‖γ k‖)` weakened to
`N = 1` (the existence proof only ever uses `N = 1`). -/
private lemma pd_seriesFun_of_summ_aux (i : Fin n) (γ : (Fin n → ℤ) → ℂ)
    (hγ : Summable (fun k : Fin n → ℤ => (wt k) * ‖γ k‖)) :
    ∀ x : Fin n → ℝ, pd i (seriesFun γ) x = seriesFun (dmul i γ) x :=
  pd_seriesFun_of_summable i γ hγ

/-- The weighted `ℓ¹` estimate for the differentiated coefficient family: under the decay
hypothesis `‖γ k‖ ⟨k⟩^{2M} ≤ C` (with `C ≥ 0`) and for every list `l` of at most two directions,
`k ↦ ‖dmulV l γ k‖` is summable with `∑_k ‖dmulV l γ k‖ ≤ K C`, where `K = (2π)² ∑_k ⟨k⟩^{-2(M-2)}`
does not depend on `C`, `γ` or `l`. -/
private lemma tsum_norm_dmulV_le_aux {M : ℕ} (hM : n + 4 < 2 * M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (hC : 0 ≤ C) (γ : (Fin n → ℤ) → ℂ),
      (∀ k : Fin n → ℤ, ‖γ k‖ * (wt k) ^ M ≤ C) →
      ∀ (l : List (Fin n)), l.length ≤ 2 →
        Summable (fun k : Fin n → ℤ => ‖dmulV l γ k‖) ∧
        (∑' k : Fin n → ℤ, ‖dmulV l γ k‖) ≤ K * C :=
  Work.Diff.STE.fill.tsum_norm_dmulV_le_of_decay hM

/-! ## Term by term differentiation along a list of directions -/

/-- Iterated term by term differentiation: if `k ↦ ⟨k⟩^{2|l|} ‖γ k‖` is summable, then the
iterated derivative `pdList l` of `seriesFun γ` is the Fourier series of the family
`dmulV l γ` (whose `k`-th coefficient is `∏_{i ∈ l} 2πi kᵢ · γ k`). -/
private lemma pdList_seriesFun_of_summable (l : List (Fin n)) (γ : (Fin n → ℤ) → ℂ)
    (hγ : Summable (fun k : Fin n → ℤ => (wt k) ^ l.length * ‖γ k‖)) :
    ∀ x : Fin n → ℝ, pdList l (seriesFun γ) x = seriesFun (dmulV l γ) x := by
  induction l with
  | nil => intro x; rw [dmulV_nil]; rfl
  | cons i l ih =>
      intro x
      -- the hypothesis of the induction, obtained by lowering the exponent by one
      have h1 : Summable (fun k : Fin n → ℤ => (wt k) ^ l.length * ‖γ k‖) := by
        refine Summable.of_nonneg_of_le
          (fun k => mul_nonneg (pow_nonneg (wt_pos k).le _) (norm_nonneg _)) (fun k => ?_) hγ
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (wt_one_le k) (Nat.le_succ _)) (norm_nonneg _)
      have hfun : pdList l (seriesFun γ) = seriesFun (dmulV l γ) := funext (ih h1)
      -- the summability hypothesis of `pd_seriesFun` for the differentiated family
      have h2 : Summable (fun k : Fin n → ℤ => (wt k) * ‖dmulV l γ k‖) := by
        refine Summable.of_nonneg_of_le
          (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _)) (fun k => ?_)
          (hγ.mul_left ((2 * Real.pi) ^ l.length))
        calc (wt k) * ‖dmulV l γ k‖
            ≤ (wt k) * ((2 * Real.pi * wt k) ^ l.length * ‖γ k‖) :=
              mul_le_mul_of_nonneg_left (norm_dmulV_le l γ k) (wt_pos k).le
          _ = (2 * Real.pi) ^ l.length * ((wt k) ^ (l.length + 1) * ‖γ k‖) := by
              rw [mul_pow]; ring
      rw [show pdList (i :: l) (seriesFun γ) = pd i (pdList l (seriesFun γ)) from rfl, hfun,
        pd_seriesFun_of_summ_aux i (dmulV l γ) h2 x, dmulV_cons]

/-! ## The `ℓ¹` bound for a Fourier series -/

/-- A Fourier series is bounded by the `ℓ¹` mass of its coefficients. -/
private lemma norm_seriesFun_le_tsum_norm (δ : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ)
    (hδ : Summable (fun k : Fin n → ℤ => ‖δ k‖)) :
    ‖seriesFun δ x‖ ≤ ∑' k : Fin n → ℤ, ‖δ k‖ := by
  have h : Summable (fun k : Fin n → ℤ => ‖δ k * fourierExp k x‖) :=
    hδ.congr (fun k => by rw [norm_mul, norm_fourierExp, mul_one])
  calc ‖seriesFun δ x‖ = ‖∑' k : Fin n → ℤ, δ k * fourierExp k x‖ := rfl
    _ ≤ ∑' k : Fin n → ℤ, ‖δ k * fourierExp k x‖ := norm_tsum_le_tsum_norm h
    _ = ∑' k : Fin n → ℤ, ‖δ k‖ :=
        tsum_congr (fun k => by rw [norm_mul, norm_fourierExp, mul_one])

/-! ## The scalar core: iterated derivatives of a decaying Fourier series -/

/-- **The quantitative `C²` bound for a decaying scalar Fourier series.**  With `n + 4 < 2M`,
there is `K ≥ 0` such that for every `C ≥ 0`, every coefficient family `γ` with
`‖γ k‖ ⟨k⟩^{2M} ≤ C`, every list `l` of at most two directions and every `x`,

  `‖∂_l (seriesFun γ) x‖ ≤ K C`.

The proof is the `ℓ¹` argument described in the module docstring: the decay bound gives the
pointwise majorant `⟨k⟩^{2j} ‖γ k‖ ≤ C ⟨k⟩^{-2(M-2)}` for `j ≤ 2`, the weight is preserved by the
Fourier multiplier `dmulV l` of order `|l| ≤ 2`, and `∑_k ⟨k⟩^{-2(M-2)}` converges because
`n < 2 (M - 2)`. -/
private lemma norm_pdList_seriesFun_le_of_decay (M : ℕ) (hM : n + 4 < 2 * M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (hC : 0 ≤ C) (γ : (Fin n → ℤ) → ℂ),
      (∀ k : Fin n → ℤ, ‖γ k‖ * (wt k) ^ M ≤ C) →
      ∀ (l : List (Fin n)), l.length ≤ 2 → ∀ x : Fin n → ℝ,
        ‖pdList l (seriesFun γ) x‖ ≤ K * C := by
  obtain ⟨K, hK, hKb⟩ := tsum_norm_dmulV_le_aux (n := n) (M := M) hM
  refine ⟨K, hK, fun C hC γ hdec l hl x => ?_⟩
  have h2M : 2 ≤ M := by omega
  -- the dual weight `⟨k⟩^{-2(M-2)}` is summable on `ℤⁿ`
  have hsum : Summable (fun k : Fin n → ℤ => ((wt k) ^ (M - 2))⁻¹) :=
    summable_wt_inv' (n := n) (s := M - 2) (by omega)
  -- the decay hypothesis, in the form `⟨k⟩^{2j} ‖γ k‖ ≤ C ⟨k⟩^{-2(M-2)}` for `j = |l| ≤ 2`
  have hpoint : ∀ k : Fin n → ℤ, (wt k) ^ l.length * ‖γ k‖ ≤ C * ((wt k) ^ (M - 2))⁻¹ := by
    intro k
    have hpos : (0 : ℝ) < (wt k) ^ (M - 2) := pow_pos (wt_pos k) _
    have hJle : (wt k) ^ l.length ≤ (wt k) ^ 2 :=
      pow_le_pow_right₀ (wt_one_le k) (by omega)
    have hpow : (wt k) ^ 2 * (wt k) ^ (M - 2) = (wt k) ^ M := by
      rw [← pow_add]; congr 1; omega
    have key : (wt k) ^ 2 * ‖γ k‖ * (wt k) ^ (M - 2) = ‖γ k‖ * (wt k) ^ M := by
      rw [mul_right_comm, hpow, mul_comm]
    calc (wt k) ^ l.length * ‖γ k‖ ≤ (wt k) ^ 2 * ‖γ k‖ :=
          mul_le_mul_of_nonneg_right hJle (norm_nonneg _)
      _ ≤ C * ((wt k) ^ (M - 2))⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hpos, key]
          exact hdec k
  have hsumL : Summable (fun k : Fin n → ℤ => (wt k) ^ l.length * ‖γ k‖) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (wt_pos k).le _) (norm_nonneg _)) hpoint
      (hsum.mul_left C)
  rw [pdList_seriesFun_of_summable l γ hsumL x]
  exact (norm_seriesFun_le_tsum_norm (dmulV l γ) x (hKb C hC γ hdec l hl).1).trans
    (hKb C hC γ hdec l hl).2

/-! ## Entrywise bounds for the three components of a jet -/

/-- The sup-norm of the spatial `2`-jet `jetM u x` is bounded by `r ≥ 0` as soon as all the
entries of its three components (value, first and second spatial derivatives) are.  This is
pure norm bookkeeping with the sup norm on `Fin n → _` and the max norm on products. -/
private lemma norm_jetM_le_of_entrywise (u : Torus n) (x : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h0 : ∀ i j : Fin n, ‖u x i j‖ ≤ r)
    (h1 : ∀ c i j : Fin n, ‖pdM c u x i j‖ ≤ r)
    (h2 : ∀ c d i j : Fin n, ‖pdM c (pdM d u) x i j‖ ≤ r) :
    ‖jetM u x‖ ≤ r := by
  show max ‖u x‖ (max ‖(fun c => pdM c u x)‖ ‖(fun c d => pdM c (pdM d u) x)‖) ≤ r
  refine max_le ((pi_norm_le_iff_of_nonneg hr).mpr
    (fun i => (pi_norm_le_iff_of_nonneg hr).mpr (h0 i))) ?_
  refine max_le ((pi_norm_le_iff_of_nonneg hr).mpr (fun c =>
    (pi_norm_le_iff_of_nonneg hr).mpr
      (fun i => (pi_norm_le_iff_of_nonneg hr).mpr (h1 c i)))) ?_
  exact (pi_norm_le_iff_of_nonneg hr).mpr (fun c => (pi_norm_le_iff_of_nonneg hr).mpr
    (fun d => (pi_norm_le_iff_of_nonneg hr).mpr
      (fun i => (pi_norm_le_iff_of_nonneg hr).mpr (h2 c d i))))

/-! ## The target -/

theorem norm_jetM_le_of_decay {n : ℕ} (M : ℕ) (hM : n + 4 < 2 * M) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (C : ℝ) (hC : 0 ≤ C) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ (k : Fin n → ℤ) (a b : Fin n), ‖c k a b‖ * (Work.Diff.STE.wt k) ^ M ≤ C) →
      ∀ x : Fin n → ℝ, ‖Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x‖ ≤ C' * C := by
  obtain ⟨K, hK, hKb⟩ := norm_pdList_seriesFun_le_of_decay (n := n) M hM
  refine ⟨K, hK, fun C hC c hdec x => ?_⟩
  -- the entrywise bound for every iterated derivative of order `≤ 2`
  have hentry : ∀ (l : List (Fin n)) (a b : Fin n), l.length ≤ 2 →
      ‖pdList l (seriesFun (fun k : Fin n → ℤ => c k a b)) x‖ ≤ K * C :=
    fun l a b hl => hKb C hC (fun k => c k a b) (fun k => hdec k a b) l hl x
  refine norm_jetM_le_of_entrywise (seriesFunM c) x (mul_nonneg hK hC) ?_ ?_ ?_
  · intro a b
    show ‖seriesFun (fun k : Fin n → ℤ => c k a b) x‖ ≤ K * C
    exact hentry [] a b (by simp)
  · intro cc a b
    show ‖pd cc (seriesFun (fun k : Fin n → ℤ => c k a b)) x‖ ≤ K * C
    exact hentry [cc] a b (by simp)
  · intro cc dd a b
    show ‖pd cc (pd dd (seriesFun (fun k : Fin n → ℤ => c k a b))) x‖ ≤ K * C
    exact hentry [cc, dd] a b (by simp)

end Work.Diff.STE.flat

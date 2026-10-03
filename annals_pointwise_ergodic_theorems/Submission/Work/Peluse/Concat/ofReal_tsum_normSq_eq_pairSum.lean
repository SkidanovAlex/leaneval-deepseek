import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Concat

open scoped BigOperators

noncomputable section

/-! ## Elementary helpers -/

/-- Membership in the symmetric interval `symIcc L` is the condition `natAbs ≤ L`. -/
private lemma mem_symIcc_iff {L : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    have h' : ((x.natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast h'
  · intro h
    have h' : |x| ≤ (L : ℤ) := by
      have h'' : ((x.natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
      simpa only [Int.natCast_natAbs] using h''
    exact abs_le.mp h'

/-- A shift of a function supported in `[-K,K]` is supported in `[-(K+|b|), K+|b|]`. -/
private lemma supportIn_shift {g : ℤ → ℂ} {K : ℕ} (h : Work.Peluse.SupportIn g K) (b : ℤ) :
    Work.Peluse.SupportIn (fun y : ℤ => g (y + b)) (K + b.natAbs) := by
  intro y hy
  have h1 : y.natAbs ≤ (y + b).natAbs + b.natAbs := by
    have h2 := Int.natAbs_sub_le (y + b) b
    rwa [add_sub_cancel_right] at h2
  exact h (y + b) (by omega)

/-- If `x` lies outside the box `symIcc (N + ∑_{a∈Q} |a|)`, then `f (x + a) = 0` for every
`a ∈ Q`, provided `f` is supported in `[-N,N]`. -/
private lemma eq_zero_of_outside_box {N : ℕ} {Q : Finset ℤ} {f : ℤ → ℂ}
    (hsup : Work.Peluse.SupportIn f N) {x : ℤ}
    (hx : N + ∑ a ∈ Q, a.natAbs < x.natAbs) (a : ℤ) (ha : a ∈ Q) : f (x + a) = 0 := by
  have ha' : a.natAbs ≤ ∑ b ∈ Q, b.natAbs :=
    Finset.single_le_sum (fun b _ => Nat.zero_le b.natAbs) ha
  have hxN : N + a.natAbs < x.natAbs := lt_of_le_of_lt (Nat.add_le_add_left ha' N) hx
  have h1 : x.natAbs ≤ (x + a).natAbs + a.natAbs := by
    have h2 := Int.natAbs_sub_le (x + a) a
    rwa [add_sub_cancel_right] at h2
  exact hsup (x + a) (by omega)

/-- **The per-pair reindexing.**  For a direction `a ∈ Q`, the substitution `y = x + a'` turns the
pairing `x ↦ f (x+a) · conj (f (x+a'))` (summed over a box containing the `x`-support of `f`) into
the autocorrelation of `f` at the shift `a - a'`. -/
private lemma sum_pair_reindex {N : ℕ} {Q : Finset ℤ} {f : ℤ → ℂ}
    (hsup : Work.Peluse.SupportIn f N) {a : ℤ} (ha : a ∈ Q) (a' : ℤ) :
    (∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs),
        f (x + a) * star (f (x + a')))
      = ∑' y : ℤ, star (f y) * f (y + (a - a')) := by
  have hzero : ∀ x : ℤ, x ∉ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs) →
      f (x + a) * star (f (x + a')) = 0 := by
    intro x hx
    have hx' : N + ∑ b ∈ Q, b.natAbs < x.natAbs := by
      by_contra hcon
      exact hx (mem_symIcc_iff.mpr (not_lt.mp hcon))
    rw [eq_zero_of_outside_box hsup hx' a ha, zero_mul]
  have hfin : (∑' y : ℤ, star (f y) * f (y + (a - a')))
      = ∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs), f (x + a) * star (f (x + a')) := by
    rw [← (Equiv.addRight a').tsum_eq]
    simp only [Equiv.coe_addRight]
    have hpt : ∀ z : ℤ, star (f (z + a')) * f (z + a' + (a - a'))
        = f (z + a) * star (f (z + a')) := by
      intro z
      rw [show z + a' + (a - a') = z + a by ring, mul_comm]
    rw [tsum_congr hpt]
    exact tsum_eq_sum (s := Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs)) hzero
  exact hfin.symm

/-- **The `ℓ²` mass of a window sum, expanded as a pair sum.**

For `f : ℤ → ℂ` supported in `[-N,N]`, an arbitrary finite set of directions `Q : Finset ℤ` and the
window sum `W x = ∑_{a ∈ Q} f (x + a)`,

`∑'_x ‖W x‖² = ∑_{a ∈ Q} ∑_{a' ∈ Q} ∑'_y conj (f y) · f (y + (a - a'))`.

This is the level-one expansion behind `Work.Peluse.Concat.uNormPow_one_eq_autocorr`: the pointwise
identity `‖W x‖² = W x · conj (W x)` (i.e. `Complex.mul_conj`) expands the square over the pairs
`(a,a')`, and substituting `y = x + a'` in the (finitely supported, hence absolutely convergent)
`x`-sum turns each inner sum into `∑'_y conj (f y) · f (y + (a - a'))`.

Proof ingredients available in Mathlib: `Complex.ofReal_tsum` (no summability side condition),
`Complex.mul_conj`/`Complex.normSq_eq_norm_sq` for `(‖z‖^2 : ℂ) = z * star z`, `Finset.sum_mul_sum`
and `star_sum` for the expansion, `Equiv.tsum_eq (Equiv.addRight _)` for the shift, and either
`tsum_eq_sum` restricted to a finite box `symIcc (N + ∑_{a∈Q} |a|)` or
`Summable.tsum_finsetSum` for the interchange of the `x`-sum with the finite `(a,a')`-sums.
The analogous bookkeeping is carried out in `Submission/Work/Peluse/Concat/sum_uNormPow_one_eq_kernel.lean`
(private lemma `sumUKernel_pairing`) and in `Submission/Work/Peluse/Ulower/ss_progAvg_normSq_eq_autocorrSum.lean`. -/
theorem ofReal_tsum_normSq_eq_pairSum {N : ℕ} {Q : Finset ℤ} {f : ℤ → ℂ}
    (hsup : Work.Peluse.SupportIn f N) :
    ((∑' x : ℤ, ‖∑ a ∈ Q, f (x + a)‖ ^ 2 : ℝ) : ℂ)
      = ∑ a ∈ Q, ∑ a' ∈ Q, ∑' y : ℤ, star (f y) * f (y + (a - a')) := by
  -- (1) `‖W x‖² = W x · conj (W x)`, expanded over the pairs `(a,a')`
  have h1 : ((∑' x : ℤ, ‖∑ a ∈ Q, f (x + a)‖ ^ 2 : ℝ) : ℂ)
      = ∑' x : ℤ, ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun x => ?_)
    have hW : (∑ a ∈ Q, f (x + a)) * star (∑ a ∈ Q, f (x + a))
        = ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')) := by
      rw [star_sum, Finset.sum_mul_sum]
    rw [← hW, ← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj]
  -- (2) restrict the `x`-tsum to the box `symIcc (N + ∑ |a|)`, outside of which `W x = 0`
  have h2 : (∑' x : ℤ, ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')))
      = ∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs),
          ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')) := by
    refine tsum_eq_sum (fun x hx => ?_)
    have hx' : N + ∑ b ∈ Q, b.natAbs < x.natAbs := by
      by_contra hcon
      exact hx (mem_symIcc_iff.mpr (not_lt.mp hcon))
    refine Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun a' _ => ?_))
    rw [eq_zero_of_outside_box hsup hx' a ha, zero_mul]
  -- (3) swap the finite `x`-sum with the finite `(a,a')`-sums
  have h3 : (∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs),
          ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')))
      = ∑ a ∈ Q, ∑ a' ∈ Q, ∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs),
          f (x + a) * star (f (x + a')) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  -- (4) substitute `y = x + a'` in each inner sum
  have h4 : ∀ a ∈ Q, ∀ a' ∈ Q,
      (∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs), f (x + a) * star (f (x + a')))
        = ∑' y : ℤ, star (f y) * f (y + (a - a')) :=
    fun a ha a' _ => sum_pair_reindex hsup ha a'
  calc ((∑' x : ℤ, ‖∑ a ∈ Q, f (x + a)‖ ^ 2 : ℝ) : ℂ)
      = ∑' x : ℤ, ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')) := h1
    _ = ∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs),
          ∑ a ∈ Q, ∑ a' ∈ Q, f (x + a) * star (f (x + a')) := h2
    _ = ∑ a ∈ Q, ∑ a' ∈ Q, ∑ x ∈ Work.Peluse.symIcc (N + ∑ b ∈ Q, b.natAbs),
          f (x + a) * star (f (x + a')) := h3
    _ = ∑ a ∈ Q, ∑ a' ∈ Q, ∑' y : ℤ, star (f y) * f (y + (a - a')) :=
        Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun a' ha' => h4 a ha a' ha'))

end

end Work.Peluse.Concat

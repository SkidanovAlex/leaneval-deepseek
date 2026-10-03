import Mathlib
import Submission.Work.Peluse.Concat.TransferDefs
import Submission.Work.Peluse.BoxNorm.boxNormPow_le_one

/-!
# `Work.Peluse.Concat.NormCrux`: the remaining gap of `concatCoreHigh`

This module is **sorry-free** and isolates the single `Prop` to which
`Submission/Work/Peluse/Concat/concatCoreHigh.lean` reduces the target `ConcatCoreHigh`.

`NormCrux` is the transposed Peluse Lemma 5.1/5.6 chain in *norm* form: for every `s ≥ 2` there is
`c_s > 0` such that for every non-degenerate difference tuple `d` the level-`(2^s-1)` box-norm power
of `f` at the dilated directions `c (d·ω_i)[D]` is at most `c_s` times the level-`2^s` uniformity
**norm** of `f` at the undilated direction `c[D]`.

Three features of the statement are essential; each was pinned down by a counterexample found in
this workspace (all recorded in `NOTES_concatCoreHigh_SESSION10.md` and
`NOTES_boxNormPowDilationTransfer_FALSE.md`):

1. the **norm** form (`Zbox = ‖f‖_{□^{2^s-1}}^{2^{2^s-1}}` against `uNorm s' = ‖f‖_{U^{s'}}`):
   the *power* form `c_s·Zbox² ≤ uNormPow s' (c[D])` is FALSE — `s = 2`, `M₁ = M₂ = 3`, `γ' = 1`,
   `D = 9`, `f = 1_{2ℤ}`, `d = (2,2)`: `Zbox → 1/2` while `uNormPow 2 → 1/8` (ratio `→ 2`);
2. the **level** `s' = 2^s`, strictly above the level `2^s - 1` of the box norm on the left: with
   `s' = 2^s - 1` the cubic phase `f = e(2πix³/(6q³))` on `[-N,N]` with `c = 1`, `D = q³`,
   `M₁ = D`, `M₂ = 1`, `γ' = 1`, `d = (q,q)` gives `Zbox ≈ 1` (level-`3` cube coherent) while
   `uNormPow 3 (1[D]) → T_3(q³,q^{-3}) → 0`: `Zbox/uNorm 3 = 1.15` at `q = 2` (`N = 2000`) and
   `≍ q^{1/4} → ∞`; at level `2^s = 4` the same family gives `Zbox/uNorm 4 = 0.995 < 1`
   (a degree-`3` phase is invisible to the level-`4` cube);
3. the **constant** `C_s` depending only on `s` (numerically `≈ 1`).

Two decompositions of `NormCrux` were tried and are **refuted**; they are recorded only so that
they are not attempted again (see the two notes):

* `BoxNormPowEqualize` ("replace the direction family by one of its members", `∃ j`) — FALSE: the
  level-`2` box norm sees the *mixed* frequencies `c(Σ ω_i q_i)`, which a single member cannot
  reproduce (`f = 1_{pℤ}` with `q = (1,p)`: ratio `≍ p`; quadratic phase with `q = (D+1,D+2)`:
  ratio `≍ D`);
* `BoxNormPowDilationTransfer` ("dilate the single direction") — FALSE for a degree-`k` phase with
  `D = q^k` (the level-`k` cube at the dilated direction is coherent while the one at the base
  direction cancels).

-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

lemma boxNormPow_eq_zero_of_empty {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ}
    (i : Fin t) (h : Q i = ∅) : Work.Peluse.boxNormPow t Q S f = 0 := by
  have h0 : (∏ j : Fin t, (((Q j).card : ℂ))⁻¹) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [h]; simp
  simp only [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum]
  rw [h0]; simp

lemma Zbox_eq_zero_of_D_zero {s : ℕ} {c : ℤ} {N : ℕ}
    {ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)} {f : ℤ → ℂ} (hs : 1 ≤ s)
    (d : Fin s → ℤ) : Zbox c 0 N ωOf f d = 0 := by
  have h2 : 2 ≤ 2 ^ s := by
    calc (2:ℕ) = 2^1 := rfl
      _ ≤ 2^s := Nat.pow_le_pow_right (by norm_num) hs
  have hpos : 0 < 2 ^ s - 1 := by omega
  haveI : Nonempty (Fin (2 ^ s - 1)) := ⟨⟨0, hpos⟩⟩
  refine boxNormPow_eq_zero_of_empty (Q := dirFam c 0 ωOf d) (S := Work.Peluse.symIcc N)
    (f := f) (Classical.arbitrary _) ?_
  simp [dirFam, Work.Peluse.arithIcc]

/-- The remaining gap of `concatCoreHigh`, in norm form (see the module docstring). -/
def NormCrux : Prop :=
  ∀ s : ℕ, 2 ≤ s → ∃ c : ℝ, 0 < c ∧
    ∀ (c' : ℤ), 0 < c' → ∀ (M₁ M₂ : ℕ) (γ' : ℝ) (N : ℕ) (f : ℤ → ℂ),
      1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c' : ℝ) →
      0 < γ' → γ' ≤ 1 → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      ∀ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool), Function.Injective ωOf →
        (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) →
      ∀ d : Fin s → ℤ, ¬ IsBad d →
      c * Zbox c' (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N ωOf f d ≤
        Work.Peluse.uNorm (2 ^ s) (Work.Peluse.arithIcc c' (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f

/-- `(uNormPow k Q S f) ^ (1/2^k) = uNorm k Q S f`. -/
lemma uNormPow_rpow_eq (k : ℕ) (Q S : Finset ℤ) (f : ℤ → ℂ) :
    (Work.Peluse.uNormPow k Q S f) ^ (1 / ((2 : ℝ) ^ k)) = Work.Peluse.uNorm k Q S f := rfl

/-- From `x ^ (2^k) ≤ uNormPow k` conclude `x ≤ uNorm k` (`x ≥ 0`). -/
lemma le_uNorm_of_pow_le {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) {Q S : Finset ℤ}
    {f : ℤ → ℂ} (h : x ^ (2 ^ k) ≤ Work.Peluse.uNormPow k Q S f) :
    x ≤ Work.Peluse.uNorm k Q S f := by
  have hself : (x ^ (2 ^ k)) ^ (1 / ((2 : ℝ) ^ k)) = x := by
    rw [← Real.rpow_natCast x (2 ^ k), ← Real.rpow_mul hx]
    have hexp : (((2 ^ k : ℕ)) : ℝ) * (1 / ((2 : ℝ) ^ k)) = 1 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, mul_one_div, div_self (by positivity : ((2 : ℝ) ^ k) ≠ 0)]
    rw [hexp, Real.rpow_one]
  rw [Work.Peluse.uNorm]
  calc x = (x ^ (2 ^ k)) ^ (1 / ((2 : ℝ) ^ k)) := hself.symm
    _ ≤ (Work.Peluse.uNormPow k Q S f) ^ (1 / ((2 : ℝ) ^ k)) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)

/-- `0 ≤ uNorm t Q S f`. -/
lemma uNorm_nonneg (t : ℕ) (Q S : Finset ℤ) (f : ℤ → ℂ) : 0 ≤ Work.Peluse.uNorm t Q S f := by
  rw [Work.Peluse.uNorm]
  refine Real.rpow_nonneg ?_ _
  simp only [Work.Peluse.uNormPow, Work.Peluse.boxNormPow, Work.Peluse.boxSumPow]
  exact norm_nonneg _

end

end Work.Peluse.Concat

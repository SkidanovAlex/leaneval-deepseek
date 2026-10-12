import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.NWindow_shift` — the number grading of `NWindow`

`T.NWindow M Φ` (FS `eq:LocalizedAftercNumber`) says that `Φ` is a finite sum
`Σ_{m ≤ ⌊M⌋} φ_m` of eigenvectors of FS's true number `n₊` (`T.N`) with integer
eigenvalues `m`.  FS's whole §10 proof runs on the fact that the mode operators
*shift* such a window according to their `n₊`-grading:

* `a_k`, `ã_s` lower (`[n₊,a_k] = -a_k`), so they preserve the window;
* `a_k†`, `ã_s†`, `b_k`, `b_k†` raise by one (the Bogoliubov `b_k` is a
  combination of a lowering `a_k` and a raising `a_{−k}†`, so it only raises to
  `M+1`), and the window is additive and monotone.

This file proves exactly that, plus the two structural facts used implicitly:
the window is monotone in `M` and is closed under sums (`max`) and scalars.

The key point in the lowering case is that `φ_0` (the `n₊ = 0` component) is
**killed** by a lowering operator: `n₊(Lφ_0) = -Lφ_0` would be an eigenvector
with the negative eigenvalue `-1`, which positivity of `n₊` forbids.  The two
`Finset.range` reindexings that turn that eigenvalue bookkeeping into the
`NWindow` witness of `LΨ` are `sum_range_ite_succ`/`sum_range_ite_pred`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

/-! ## Two general `Finset.range` identities

These reindex the two shifted windows that arise when a lowering
(`Lφ_{m+1}`, eigenvalue `m`) or a raising (`Lφ_{m-1}`, eigenvalue `m`)
operator is applied to the witness of `NWindow`. -/

theorem sum_range_ite_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (if j + 1 ≤ n then f (j + 1) else 0) =
      ∑ m ∈ Finset.range n, f (m + 1) := by
  rw [Finset.sum_range_succ]
  have hz : (if n + 1 ≤ n then f (n + 1) else 0) = 0 := by
    rw [if_neg (by omega)]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_pos (Nat.succ_le_of_lt (Finset.mem_range.mp hj))]

theorem sum_range_ite_pred {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (if 1 ≤ j then f (j - 1) else 0) =
      ∑ m ∈ Finset.range n, f m := by
  rw [Finset.sum_range_succ']
  have hz : (if 1 ≤ 0 then f (0 - 1) else 0) = (0 : M) := by
    rw [if_neg (by omega)]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos (Nat.succ_le_succ (Nat.zero_le j)), Nat.add_sub_cancel]

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

namespace TildeData

variable {F : Work.BoseB7.FockData Mode} (T : TildeData F)

/-- **Monotonicity of the window.** A finite combination of `N`-eigenvectors with
eigenvalues `0 ≤ m ≤ ⌊M'⌋` also has eigenvalues `≤ ⌊M''⌋` when `M' ≤ M''`. -/
theorem NWindow_mono {M' M'' : ℝ} {Ψ : F.H} (h : T.NWindow M' Ψ) (hle : M' ≤ M'') :
    T.NWindow M'' Ψ := by
  obtain ⟨φ, hφ, hsum⟩ := h
  refine ⟨fun m => if m ≤ ⌊M'⌋₊ then φ m else 0, ?_, ?_⟩
  · intro m
    dsimp only
    by_cases hm : m ≤ ⌊M'⌋₊
    · rw [if_pos hm, hφ m]
    · rw [if_neg hm, map_zero, smul_zero]
  · rw [hsum]
    calc ∑ m ∈ Finset.range (⌊M'⌋₊ + 1), φ m
        = ∑ m ∈ Finset.range (⌊M'⌋₊ + 1), (if m ≤ ⌊M'⌋₊ then φ m else 0) :=
          Finset.sum_congr rfl fun m hm =>
            (if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).symm
      _ = ∑ m ∈ Finset.range (⌊M''⌋₊ + 1), (if m ≤ ⌊M'⌋₊ then φ m else 0) :=
          Finset.sum_subset (fun x hx => by
              rw [Finset.mem_range] at hx ⊢
              have := Nat.floor_mono hle
              omega)
            (fun x hx hxs => by
              rw [Finset.mem_range] at hx hxs
              rw [if_neg (by omega)])

/-- **Additivity of the window**: the sum of a vector of window `M₁` and one of
window `M₂` lies in window `max M₁ M₂`. -/
theorem NWindow_add {M₁ M₂ : ℝ} {Ψ Χ : F.H} (h₁ : T.NWindow M₁ Ψ)
    (h₂ : T.NWindow M₂ Χ) : T.NWindow (max M₁ M₂) (Ψ + Χ) := by
  obtain ⟨φ, hφ, hsum⟩ := h₁
  obtain ⟨χ, hχ, hsum₂⟩ := h₂
  refine ⟨fun m => (if m ≤ ⌊M₁⌋₊ then φ m else 0) + (if m ≤ ⌊M₂⌋₊ then χ m else 0),
    ?_, ?_⟩
  · intro m
    dsimp only
    have h1 : T.N (if m ≤ ⌊M₁⌋₊ then φ m else 0)
        = (m : ℝ) • (if m ≤ ⌊M₁⌋₊ then φ m else 0) := by
      by_cases hm : m ≤ ⌊M₁⌋₊
      · rw [if_pos hm, hφ m]
      · rw [if_neg hm, map_zero, smul_zero]
    have h2 : T.N (if m ≤ ⌊M₂⌋₊ then χ m else 0)
        = (m : ℝ) • (if m ≤ ⌊M₂⌋₊ then χ m else 0) := by
      by_cases hm : m ≤ ⌊M₂⌋₊
      · rw [if_pos hm, hχ m]
      · rw [if_neg hm, map_zero, smul_zero]
    rw [map_add, h1, h2, smul_add]
  · rw [hsum, hsum₂, Finset.sum_add_distrib]
    congr 1
    · calc ∑ m ∈ Finset.range (⌊M₁⌋₊ + 1), φ m
          = ∑ m ∈ Finset.range (⌊M₁⌋₊ + 1), (if m ≤ ⌊M₁⌋₊ then φ m else 0) :=
            Finset.sum_congr rfl fun m hm =>
              (if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).symm
        _ = ∑ m ∈ Finset.range (⌊max M₁ M₂⌋₊ + 1), (if m ≤ ⌊M₁⌋₊ then φ m else 0) :=
            Finset.sum_subset (fun x hx => by
                rw [Finset.mem_range] at hx ⊢
                have := Nat.floor_mono (le_max_left M₁ M₂)
                omega)
              (fun x hx hxs => by
                rw [Finset.mem_range] at hx hxs
                rw [if_neg (by omega)])
    · calc ∑ m ∈ Finset.range (⌊M₂⌋₊ + 1), χ m
          = ∑ m ∈ Finset.range (⌊M₂⌋₊ + 1), (if m ≤ ⌊M₂⌋₊ then χ m else 0) :=
            Finset.sum_congr rfl fun m hm =>
              (if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).symm
        _ = ∑ m ∈ Finset.range (⌊max M₁ M₂⌋₊ + 1), (if m ≤ ⌊M₂⌋₊ then χ m else 0) :=
            Finset.sum_subset (fun x hx => by
                rw [Finset.mem_range] at hx ⊢
                have := Nat.floor_mono (le_max_right M₁ M₂)
                omega)
              (fun x hx hxs => by
                rw [Finset.mem_range] at hx hxs
                rw [if_neg (by omega)])

/-- **Homogeneity of the window.** -/
theorem NWindow_smul (c : ℝ) {M : ℝ} {Ψ : F.H} (h : T.NWindow M Ψ) :
    T.NWindow M (c • Ψ) := by
  obtain ⟨φ, hφ, hsum⟩ := h
  refine ⟨fun m => c • φ m, ?_, ?_⟩
  · intro m
    dsimp only
    rw [map_smul, hφ m, smul_comm]
  · rw [hsum, Finset.smul_sum]

/-- A linear map whose number grading is a **lowering** (`[N,L] = -L`) kills the
`N = 0` part: `N f = 0 → L f = 0`.  Indeed `L f` would be an `N`-eigenvector with
eigenvalue `-1`, which positivity forbids. -/
theorem apply_eq_zero_of_N_eq_zero {L : F.H →ₗ[ℝ] F.H}
    (hgrade : T.N ∘ₗ L = L ∘ₗ T.N - L) {f : F.H} (hf : T.N f = 0) : L f = 0 := by
  have hN : T.N (L f) = -(L f) := by
    have h := LinearMap.congr_fun hgrade f
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, hf, map_zero] at h
    simpa using h
  have hpos : 0 ≤ F.bp (T.N (L f)) (L f) := T.N_nonneg (L f)
  have hneg : F.bp (-(L f)) (L f) = -(F.bp (L f) (L f)) := by simp
  rw [hN, hneg] at hpos
  have hnn : 0 ≤ F.bp (L f) (L f) := F.bp_nonneg (L f)
  exact F.bp_def (L f) (le_antisymm (by linarith) hnn)

/-- **A lowering operator preserves the window.** If `[N,L] = -L` and `Ψ` is a
combination of eigenvectors with eigenvalues `0,…,⌊M⌋`, then `L Ψ` is a
combination of eigenvectors with eigenvalues `0,…,⌊M⌋` (the `m = 0` part is
annihilated by `apply_eq_zero_of_N_eq_zero`). -/
theorem NWindow_lower {L : F.H →ₗ[ℝ] F.H} (hgrade : T.N ∘ₗ L = L ∘ₗ T.N - L)
    {M : ℝ} {Ψ : F.H} (h : T.NWindow M Ψ) : T.NWindow M (L Ψ) := by
  obtain ⟨φ, hφ, hsum⟩ := h
  have hkill : L (φ 0) = 0 :=
    T.apply_eq_zero_of_N_eq_zero hgrade (by rw [hφ 0]; simp)
  refine ⟨fun j => if j + 1 ≤ ⌊M⌋₊ then L (φ (j + 1)) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases hj : j + 1 ≤ ⌊M⌋₊
    · rw [if_pos hj]
      have hkey : ∀ v : F.H, (((j + 1 : ℕ) : ℝ)) • v - v = (j : ℝ) • v := by
        intro v
        have hc : (((j + 1 : ℕ) : ℝ)) - 1 = (j : ℝ) := by push_cast; ring
        calc (((j + 1 : ℕ) : ℝ)) • v - v
            = (((j + 1 : ℕ) : ℝ)) • v - 1 • v := by rw [one_smul]
          _ = ((((j + 1 : ℕ) : ℝ)) - 1) • v := (sub_smul _ 1 v).symm
          _ = (j : ℝ) • v := by rw [hc]
      have h := LinearMap.congr_fun hgrade (φ (j + 1))
      simp only [LinearMap.comp_apply, LinearMap.sub_apply] at h
      rw [h, hφ (j + 1), map_smul]
      exact hkey _
    · rw [if_neg hj, map_zero, smul_zero]
  · rw [hsum, map_sum]
    rw [sum_range_ite_succ (fun m => L (φ m)) ⌊M⌋₊]
    have h2 := Finset.sum_range_succ' (fun m => L (φ m)) ⌊M⌋₊
    rw [hkill, add_zero] at h2
    rw [← h2]

/-- **A raising operator increases the window by one.** If `[N,L] = +L` and
`Ψ ∈ NWindow M`, then `L Ψ ∈ NWindow (M+1)` (only the `M ≥ 0` case is used, so
that `⌊M+1⌋₊ = ⌊M⌋₊ + 1`). -/
theorem NWindow_raise {L : F.H →ₗ[ℝ] F.H} (hgrade : T.N ∘ₗ L = L ∘ₗ T.N + L)
    {M : ℝ} (hM : 0 ≤ M) {Ψ : F.H} (h : T.NWindow M Ψ) : T.NWindow (M + 1) (L Ψ) := by
  obtain ⟨φ, hφ, hsum⟩ := h
  have hfloor : ⌊M + 1⌋₊ = ⌊M⌋₊ + 1 := Nat.floor_add_one hM
  refine ⟨fun j => if 1 ≤ j then L (φ (j - 1)) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases hj : 1 ≤ j
    · rw [if_pos hj]
      have hkey : ∀ v : F.H, (((j - 1 : ℕ) : ℝ)) • v + v = (j : ℝ) • v := by
        intro v
        have hc : (((j - 1 : ℕ) : ℝ)) + 1 = (j : ℝ) := by
          have hj1 : ((((j - 1 : ℕ) + 1 : ℕ)) : ℝ) = (j : ℝ) := by
            rw [Nat.sub_add_cancel hj]
          rw [Nat.cast_add, Nat.cast_one] at hj1
          exact hj1
        calc (((j - 1 : ℕ) : ℝ)) • v + v
            = (((j - 1 : ℕ) : ℝ)) • v + 1 • v := by rw [one_smul]
          _ = ((((j - 1 : ℕ) : ℝ)) + 1) • v := (add_smul _ 1 v).symm
          _ = (j : ℝ) • v := by rw [hc]
      have h := LinearMap.congr_fun hgrade (φ (j - 1))
      simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
      rw [h, hφ (j - 1), map_smul]
      exact hkey _
    · rw [if_neg hj, map_zero, smul_zero]
  · rw [hsum, map_sum, hfloor]
    rw [sum_range_ite_pred (fun m => L (φ m)) (⌊M⌋₊ + 1)]

/-- `ã_s` lowers the window (FS's grading `[n₊,ã_s] = -ã_s`). -/
theorem NWindow_ta (s : Mode) {M : ℝ} {Ψ : F.H} (h : T.NWindow M Ψ) :
    T.NWindow M (T.ta s Ψ) :=
  NWindow_lower T (T.N_ta s) h

/-- `ã_s†` raises the window. -/
theorem NWindow_taDag (s : Mode) {M : ℝ} (hM : 0 ≤ M) {Ψ : F.H} (h : T.NWindow M Ψ) :
    T.NWindow (M + 1) (T.taDag s Ψ) :=
  NWindow_raise T (T.N_taDag s) hM h

theorem NWindow_a (k : Mode) {M : ℝ} {Ψ : F.H} (h : T.NWindow M Ψ) :
    T.NWindow M (F.a k Ψ) :=
  NWindow_lower T (T.N_a k) h

theorem NWindow_aDag (k : Mode) {M : ℝ} (hM : 0 ≤ M) {Ψ : F.H} (h : T.NWindow M Ψ) :
    T.NWindow (M + 1) (F.aDag k Ψ) :=
  NWindow_raise T (T.N_aDag k) hM h

end TildeData

theorem NWindow_shift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    {M : ℝ} (hM : 0 ≤ M) {Φ : F.H} (hΦ : T.NWindow M Φ) (s k : Mode) :
    (∀ {M' M'' : ℝ} {Ψ : F.H}, T.NWindow M' Ψ → M' ≤ M'' → T.NWindow M'' Ψ) ∧
    (∀ {M₁ M₂ : ℝ} {Ψ Χ : F.H}, T.NWindow M₁ Ψ → T.NWindow M₂ Χ →
      T.NWindow (max M₁ M₂) (Ψ + Χ)) ∧
    T.NWindow M (T.ta s Φ) ∧ T.NWindow (M + 1) (T.taDag s Φ) ∧
    T.NWindow M (F.a k Φ) ∧ T.NWindow (M + 1) (F.aDag k Φ) ∧
    T.NWindow (M + 1) (F.bOp E.alpha k Φ) ∧ T.NWindow (M + 1) (F.bOpDag E.alpha k Φ) := by
  have hb : T.NWindow (M + 1) (F.bOp E.alpha k Φ) := by
    show T.NWindow (M + 1) ((F.a k + (E.alpha k) • F.aDag (-k)) Φ)
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    refine T.NWindow_mono (T.NWindow_add (T.NWindow_a k hΦ)
      (T.NWindow_smul (E.alpha k) (T.NWindow_aDag (-k) hM hΦ))) ?_
    exact max_le (by linarith) (by linarith)
  have hbd : T.NWindow (M + 1) (F.bOpDag E.alpha k Φ) := by
    show T.NWindow (M + 1) ((F.aDag k + (E.alpha k) • F.a (-k)) Φ)
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    refine T.NWindow_mono (T.NWindow_add (T.NWindow_aDag k hM hΦ)
      (T.NWindow_smul (E.alpha k) (T.NWindow_a (-k) hΦ))) ?_
    exact max_le (by linarith) (by linarith)
  exact ⟨fun h hle' => T.NWindow_mono h hle', fun h₁ h₂ => T.NWindow_add h₁ h₂,
    T.NWindow_ta s hΦ, T.NWindow_taDag s hM hΦ, T.NWindow_a k hΦ, T.NWindow_aDag k hM hΦ,
    hb, hbd⟩

end Work.BoseB7A

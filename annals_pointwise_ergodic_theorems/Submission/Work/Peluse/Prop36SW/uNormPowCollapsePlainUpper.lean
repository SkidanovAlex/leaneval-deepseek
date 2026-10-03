import Mathlib
import Submission.Work.Peluse.TransferUp.RawPowDefs
import Submission.Work.Peluse.UControl.piecePetSetup
import Submission.Work.Peluse.Prop36SW.npowLagWeights

/-!
# Collapsing the step set of the uniformity-norm power from `[L]` down to `[2M+1]`

The target `Work.Peluse.Prop36SW.uNormPowCollapsePlainUpper` is the *upper* counterpart of the
proved `uNormPowCollapsePlain`: for a `1`-bounded function `f` supported in `[-M,M]` and any
`L ≥ 2M+1`, the `2^t`-th power of Peluse's uniformity norm of `f` over the long step set
`[L] = {1,…,L}` is bounded by a constant times the dilution factor `((2M+1)/L)^t` times the norm
over the shortest admissible step set `[2M+1]`.

## Strategy

Everything is phrased through the normalised box-norm power
`TransferUp.Npow t d S F H := |S| H^t ‖F‖^{2^t}_{□^t_{d_i[H]}(S)}`, for which

* `uNormPow t (arithIcc 1 H) S f = Npow t (fun _ => 1) S f H / (|S| H^t)` (definitional), so the
  target is equivalent to the *same-scale* collapse `Npow t 1 S f L ≤ C Npow t 1 S f (2M+1)`;
* `Npow_succ` (peel recursion): `Npow (k+1) 1 S F H = ∑_m ψ_H(m) · Npow k 1 S (F · conj(F(·+m))) H`.

The collapse is proved by induction on the level `t ≥ 1` for the statement

`UC t : ∃ C, 0 < C ∧ ∀ M f, SupportIn f M → (‖f‖ ≤ 1) → ∀ H ≥ 2M+1,
   Npow t 1 (symIcc M) f H ≤ C · Npow t 1 (symIcc M) f (2M+1)`.

* **`UC 1`** is `npowOneCollapseLe` (the level-one collapse: the `ℓ²`-mass of the window sums of `f`
  is `K‖Σ‖² - PF` with `PF ≤ M‖Σ‖²`, sharp).
* **`UC k ⟹ UC (k+1)`**: the peel recursion writes the level-`(k+1)` quantity at scale `H` as the
  `ψ_H`-weighted average of level-`k` quantities of the difference functions
  `lagFun f m = f · conj(f(·+m))`.  Those are again supported in `[-M,M]` and `1`-bounded, so `UC k`
  bounds each of them at the *fixed* scale `2M+1`; the `ψ_H`-weights can then be replaced by the
  `ψ_{2M+1}`-weights by `npowLagWeights` (the lag-weight comparison, proved for all levels), and
  the result is `Npow (k+1) 1 S f (2M+1)` again by the peel recursion.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse
open Work.Peluse.TransferUp

noncomputable section

/-- The lag index set `{-(N-1), …, N-1}`. -/
private def lagSet (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)

/-- The difference function `y ↦ f y · conj (f (y+m))` attached to the lag `m`. -/
private def lagFun (f : ℤ → ℂ) (m : ℤ) : ℤ → ℂ := fun y => f y * star (f (y + m))

private lemma lagFun_apply (f : ℤ → ℂ) (m y : ℤ) :
    lagFun f m y = f y * star (f (y + m)) := rfl

/-- Difference functions of a function supported in `[-M,M]` are supported in `[-M,M]`. -/
private lemma supportIn_lagFun {M : ℕ} {f : ℤ → ℂ} (hsup : SupportIn f M) (m : ℤ) :
    SupportIn (lagFun f m) M := by
  intro x hx
  show f x * star (f (x + m)) = 0
  rw [hsup x hx, zero_mul]

/-- Difference functions of a `1`-bounded function are `1`-bounded. -/
private lemma norm_lagFun {f : ℤ → ℂ} (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) (m : ℤ) :
    ∀ x : ℤ, ‖lagFun f m x‖ ≤ 1 := by
  intro x
  show ‖f x * star (f (x + m))‖ ≤ 1
  rw [norm_mul, norm_star]
  exact mul_le_one₀ (hb x) (norm_nonneg _) (hb _)

/-- If `|m| ≥ 2M+1` then the difference function of a function supported in `[-M,M]` vanishes. -/
private lemma lagFun_eq_zero {M : ℕ} {f : ℤ → ℂ} (hsup : SupportIn f M) {m : ℤ}
    (hm : 2 * M + 1 ≤ m.natAbs) : lagFun f m = 0 := by
  funext y
  show f y * star (f (y + m)) = 0
  by_cases hy : y.natAbs ≤ M
  · have h1 : (((2 * M + 1 : ℕ)) : ℤ) ≤ |m| := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hm
    have hy' : |y| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hy
    have h2 : (M : ℤ) < |y + m| := by
      have h := abs_add_le (y + m) (-y)
      rw [abs_neg] at h
      have h3 : y + m + -y = m := by ring
      rw [h3] at h
      omega
    have h4 : (M : ℕ) < (y + m).natAbs := by
      rw [← Int.natCast_natAbs] at h2
      exact_mod_cast h2
    rw [hsup (y + m) h4, star_zero, mul_zero]
  · have h5 : (M : ℕ) < y.natAbs := by omega
    rw [hsup y h5, zero_mul]

/-- `Npow` of the zero function vanishes. -/
private lemma npow_zero (t : ℕ) (d : Fin t → ℤ) (S : Finset ℤ) (H : ℕ) :
    Npow t d S (0 : ℤ → ℂ) H = 0 := by
  have hbox : Work.Peluse.boxNormPow t (fun i : Fin t => Work.Peluse.arithIcc (d i) H) S
      (0 : ℤ → ℂ) = 0 := by
    rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum_eq]
    simp
  rw [Npow, hbox, mul_zero]

/-- The **same-scale collapse** at level `t`: the level-`t` box-norm power of a `1`-bounded function
supported in `[-M,M]` at *any* scale `H ≥ 2M+1` is bounded by a constant times its value at the
shortest admissible scale `2M+1`. -/
private def UC (t : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (f : ℤ → ℂ), 1 ≤ M → Work.Peluse.SupportIn f M →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → ∀ (H : ℕ), 2 * M + 1 ≤ H →
      Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f H
        ≤ C * Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1)

/-- The level-one collapse in the `Npow` vocabulary with the scale bound re-associated. -/
private lemma uc_one : UC 1 := by
  obtain ⟨C, hC, hcol⟩ := npowOneCollapseLe
  exact ⟨C, hC, fun M f hM hsup hb H hH => hcol H M f hM hH hsup hb⟩

/-- The induction step of the collapse: the lag-weight comparison at level `k` upgrades `UC k` to
`UC (k+1)`. -/
private lemma uc_succ (k : ℕ) (hk : 1 ≤ k) (ih : UC k) : UC (k + 1) := by
  obtain ⟨C, hC, hineq⟩ := ih
  obtain ⟨Cw, hCw, hw⟩ := npowLagWeights (t := k) hk
  refine ⟨C * Cw, mul_pos hC hCw, ?_⟩
  intro M f hM hsup hb H hH
  have hH1 : 1 ≤ H := by omega
  have hW1 : 1 ≤ 2 * M + 1 := by omega
  have hfin : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsup
  -- the peel recursion at the two scales
  have hpeelH := Npow_succ (t := k) hk (fun _ : Fin (k + 1) => (1 : ℤ)) (by norm_num)
    (Work.Peluse.symIcc M) f hfin (H := H) hH1
  have hpeelW := Npow_succ (t := k) hk (fun _ : Fin (k + 1) => (1 : ℤ)) (by norm_num)
    (Work.Peluse.symIcc M) f hfin (H := 2 * M + 1) hW1
  have hdiff : ∀ m : ℤ, (fun y : ℤ => f y * star (f (y + (fun _ : Fin (k + 1) => (1 : ℤ)) 0 * m)))
      = lagFun f m := by
    intro m; funext y; simp [lagFun_apply]
  have hpeelH' : Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (Work.Peluse.symIcc M) f H
      = ∑ m ∈ lagSet H, psi H m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) H := by
    rw [hpeelH]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hdiff m]
  have hpeelW' : Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1)
      = ∑ m ∈ lagSet (2 * M + 1), psi (2 * M + 1) m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1) := by
    rw [hpeelW]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hdiff m]
  -- the vanishing of the summands outside `lagSet (2M+1)`
  have hsubset : lagSet (2 * M + 1) ⊆ lagSet H := by
    intro m hm
    simp only [lagSet, Finset.mem_Icc] at hm ⊢
    have hcast : (((2 * M + 1 : ℕ)) : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH
    omega
  have hvanish : ∀ m ∈ lagSet H, m ∉ lagSet (2 * M + 1) →
      psi H m * Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1)
        = 0 := by
    intro m _ hm
    have hnat : 2 * M + 1 ≤ m.natAbs := by
      have hm' : ¬ ((-(((2 * M + 1 : ℕ)) : ℤ)) + 1 ≤ m
          ∧ m ≤ (((2 * M + 1 : ℕ)) : ℤ) - 1) := by
        simpa only [lagSet, Finset.mem_Icc] using hm
      rw [not_and_or] at hm'
      rcases hm' with h | h
      · have h2 : (((2 * M + 1 : ℕ)) : ℤ) ≤ -m := by omega
        have h3 := Int.le_natAbs (a := -m)
        rw [Int.natAbs_neg] at h3
        omega
      · have h2 : (((2 * M + 1 : ℕ)) : ℤ) ≤ m := by omega
        have h3 := Int.le_natAbs (a := m)
        omega
    rw [lagFun_eq_zero hsup hnat, npow_zero]
    ring
  have hterm : ∀ m : ℤ, Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) H
      ≤ C * Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1) :=
    fun m => hineq M (lagFun f m) hM (supportIn_lagFun hsup m) (norm_lagFun hb m) H hH
  have hlag := hw H M f hM hH hsup hb
  calc Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (Work.Peluse.symIcc M) f H
      = ∑ m ∈ lagSet H, psi H m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) H := hpeelH'
    _ ≤ ∑ m ∈ lagSet H, psi H m *
          (C * Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1)) :=
        Finset.sum_le_sum (fun m _ =>
          mul_le_mul_of_nonneg_left (hterm m) (psi_nonneg H m))
    _ = C * ∑ m ∈ lagSet H, psi H m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)
    _ = C * ∑ m ∈ lagSet (2 * M + 1), psi H m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1) := by
        rw [Finset.sum_subset hsubset hvanish]
    _ ≤ C * (Cw * ∑ m ∈ lagSet (2 * M + 1), psi (2 * M + 1) m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (Work.Peluse.symIcc M) (lagFun f m) (2 * M + 1)) :=
        mul_le_mul_of_nonneg_left hlag hC.le
    _ = C * Cw * Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1) := by
        rw [hpeelW']
        ring

/-- The same-scale collapse holds at every level `t ≥ 1`. -/
private lemma uc_all (t : ℕ) (ht : 1 ≤ t) : UC t :=
  Nat.le_induction uc_one (fun k hk ih => uc_succ k hk ih) t ht

/-- The target, in the `Npow` vocabulary. -/
private lemma npow_collapse {t : ℕ} (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
      Work.Peluse.SupportIn f M → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f L
          ≤ C * Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1) := by
  obtain ⟨C, hC, h⟩ := uc_all t ht
  exact ⟨C, hC, fun L M f hM hLM hsup hb => h M f hM hsup hb L hLM⟩

/-- `uNormPow` in terms of `Npow`. -/
private lemma uNormPow_eq_npow (t : ℕ) (M H : ℕ) (hH : 1 ≤ H) (f : ℤ → ℂ) :
    Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) H) (Work.Peluse.symIcc M) f
      = Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f H
          / (((Work.Peluse.symIcc M).card : ℝ) * (H : ℝ) ^ t) := by
  have hHne : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega))
  have hcardne : ((Work.Peluse.symIcc M).card : ℝ) ≠ 0 := by
    have : 0 < (Work.Peluse.symIcc M).card :=
      Finset.card_pos.mpr ⟨0, by simp [Work.Peluse.symIcc]⟩
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  rw [Npow, Work.Peluse.uNormPow]
  field_simp

theorem uNormPowCollapsePlainUpper {t : ℕ} (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
      Work.Peluse.SupportIn f M → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) f
          ≤ C * (((2 * M + 1 : ℕ) : ℝ) / (L : ℝ)) ^ t
              * Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) f := by
  obtain ⟨C, hC, h⟩ := npow_collapse (t := t) (le_trans (by norm_num : 1 ≤ 2) ht)
  refine ⟨C, hC, ?_⟩
  intro L M f hM hLM hsup hb
  have hL1 : 1 ≤ L := by omega
  have hW1 : 1 ≤ 2 * M + 1 := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hWpos : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ) := by positivity
  have hcardpos : (0 : ℝ) < ((Work.Peluse.symIcc M).card : ℝ) := by
    have : 0 < (Work.Peluse.symIcc M).card :=
      Finset.card_pos.mpr ⟨0, by simp [Work.Peluse.symIcc]⟩
    exact_mod_cast this
  have hkey : Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f L
      ≤ C * Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1) :=
    h L M f hM hLM hsup hb
  rw [uNormPow_eq_npow t M L hL1 f, uNormPow_eq_npow t M (2 * M + 1) hW1 f]
  have hfac : C * (((2 * M + 1 : ℕ) : ℝ) / (L : ℝ)) ^ t
      * (Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1)
          / (((Work.Peluse.symIcc M).card : ℝ) * (((2 * M + 1 : ℕ)) : ℝ) ^ t))
      = C * Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M) f (2 * M + 1)
          / (((Work.Peluse.symIcc M).card : ℝ) * (L : ℝ) ^ t) := by
    rw [div_pow]
    field_simp
  rw [hfac]
  exact div_le_div_of_nonneg_right hkey (by positivity)

end

end Work.Peluse.Prop36SW

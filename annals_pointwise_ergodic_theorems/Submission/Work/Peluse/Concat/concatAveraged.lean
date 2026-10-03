import Mathlib
import Submission.Work.Peluse.Concat.cruxDefs
import Submission.Work.Peluse.Concat.arithIcc_shrink_dvd_ge
import Submission.Work.Peluse.Peel.boxNormPow_diag_ge
import Submission.Work.Peluse.Peel.boxNormPow_diag_peel

/-!
# The *averaged* reduction of `Work.Peluse.Concat.ConcatCoreHigh`

`Submission/Work/Peluse/Concat/concatCoreHigh.lean` reduces the target to the *single pair* statement
`Work.Peluse.Concat.NormCrux` (one non-degenerate difference `d` at a time).  The single-pair shape
is strictly stronger than the target — the paper (Peluse, *Bounds for sets with no polynomial
progressions*, arXiv:1909.00309, Theorem 3.5 / Lemma 5.6) proves the **averaged** statement — and
the present session found that the single-pair form is what forces the `NormCrux`-specific level
`2^s (see `NOTES_concatCoreHigh_SESSION11.md`).

This module replaces that reduction by the **sound** one, which keeps the average over the shift
pairs and is therefore strictly weaker (and it is what the paper actually proves):

* `Work.Peluse.Concat.boxAvgGen` — the average of the level-`(2^s-1)` box-norm powers over the
  shift pairs with a **non-degenerate** difference `h - h'`;
* `Work.Peluse.Concat.AveragedCrux` — the rounded Peluse Theorem 3.5/§5 concatenation in the
  workspace's transposed parameterisation:

      ∀ s ≥ 2, ∃ C > 0, ∃ s' ≥ 3, ∀ (data), ∀ ωOf, boxAvgGen s M₁ c ωOf D N f
        ≤ C · uNorm s' (c[D]) (symIcc N) f ,      D = ⌊γ' M₁ M₂⌋ ;

* `Work.Peluse.Concat.averagedCrux_of_normCrux` — `NormCrux ⟹ AveragedCrux` (so the new gap
  subsumes the old one; nothing is lost by working with the averaged form);
* `Work.Peluse.Concat.concatCoreHigh_of_averagedCrux` — `AveragedCrux ⟹ ConcatCoreHigh`, proved
  here by splitting the average into its degenerate and non-degenerate parts and using the two
  elementary bounds `Work.Peluse.Concat.badPairsBound` / `cardBadPairs` (the degenerate pairs carry
  weight `O(2^{3s}/M₁)`) and the mass lower bound `Work.Peluse.Concat.uNormPow_ge_mass`
  (`Lmass ≤ M₁ · uNorm s'` for `s' ≥ 3`, because `D ≤ M₁²`).

Neither `NormCrux` nor `AveragedCrux` is proved; both are single named gaps.  The point of this
module is that the *weaker* of the two suffices, and that its shape is the one the literature
proves.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-- The `2^t`-th power of the uniformity norm is nonnegative. -/
lemma uNormPow_nonneg (t : ℕ) (Q S : Finset ℤ) (f : ℤ → ℂ) : 0 ≤ Work.Peluse.uNormPow t Q S f := by
  simp only [Work.Peluse.uNormPow, Work.Peluse.boxNormPow]
  exact norm_nonneg _

/-- Every box-norm power is nonnegative. -/
lemma Zbox_nonneg {s : ℕ} (c : ℤ) (D N : ℕ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool))
    (f : ℤ → ℂ) (d : Fin s → ℤ) : 0 ≤ Zbox c D N ωOf f d := by
  simp only [Zbox, Work.Peluse.boxNormPow]
  exact norm_nonneg _

/-- `2 (n+1) ≤ 2^n` for `n ≥ 3`. -/
lemma two_mul_succ_le_two_pow : ∀ n : ℕ, 3 ≤ n → 2 * (n + 1) ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h2 : (2 : ℕ) ≤ 2 ^ k := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * (k + 1 + 1) = 2 * (k + 1) + 2 := by ring
        _ ≤ 2 ^ k + 2 := by omega
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by ring

/-- The **generic part** of the box-norm average: the average of the level-`(2^s-1)` box-norm
powers `Zbox` over the shift pairs `(h,h')` whose difference `h - h'` is *non-degenerate*
(`¬ IsBad`). -/
def boxAvgGen (s M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)) (D N : ℕ)
    (f : ℤ → ℂ) : ℝ := by
  classical
  exact ((M₁ : ℝ))⁻¹ ^ (2 * s) *
    ∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁,
      (if IsBad (tupSub h h') then 0 else Zbox c D N ωOf f (tupSub h h'))

/-- The **degenerate part** of the box-norm average. -/
def boxAvgBad (s M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)) (D N : ℕ)
    (f : ℤ → ℂ) : ℝ := by
  classical
  exact ((M₁ : ℝ))⁻¹ ^ (2 * s) *
    ∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁,
      (if IsBad (tupSub h h') then Zbox c D N ωOf f (tupSub h h') else 0)

lemma boxAvg_eq_gen_add_bad (s M₁ : ℕ) (c : ℤ)
    (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool)) (D N : ℕ) (f : ℤ → ℂ) :
    boxAvg s M₁ c ωOf D N f = boxAvgGen s M₁ c ωOf D N f + boxAvgBad s M₁ c ωOf D N f := by
  classical
  simp only [boxAvg, boxAvgGen, boxAvgBad, Zsum, ← Finset.sum_add_distrib, ← mul_add]
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  by_cases hb : IsBad (tupSub h h')
  · simp only [hb, if_true, add_zero, zero_add]; rfl
  · simp only [hb, if_false, zero_add, add_zero]; rfl

lemma boxAvgGen_nonneg {s M₁ : ℕ} (c : ℤ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool))
    (D N : ℕ) (f : ℤ → ℂ) : 0 ≤ boxAvgGen s M₁ c ωOf D N f := by
  classical
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun h' _ => ?_
  by_cases hb : IsBad (tupSub h h') <;> simp [hb, Zbox_nonneg]

lemma boxAvgBad_nonneg {s M₁ : ℕ} (c : ℤ) (ωOf : Fin (2 ^ s - 1) → (Fin s → Bool))
    (D N : ℕ) (f : ℤ → ℂ) : 0 ≤ boxAvgBad s M₁ c ωOf D N f := by
  classical
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun h' _ => ?_
  by_cases hb : IsBad (tupSub h h') <;> simp [hb, Zbox_nonneg]

/-- **The averaged (rounded Peluse §5) crux**: the average of the level-`(2^s-1)` box-norm powers
with the *long-scale dilated* direction families `c((h-h')·ωOf i)[D]`, taken over the shift pairs
with non-degenerate difference, is dominated by the level-`s'` uniformity norm of `f` at the
undilated scale `c[D]`, with `s' ≥ 3` and a constant depending only on `s`.

This is Peluse's Theorem 3.5 in the workspace's transposed, long-direction-scale parameterisation,
with the average over the shift pairs kept (no passage to a single difference). -/
def AveragedCrux : Prop :=
  ∀ s : ℕ, 2 ≤ s → ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 3 ≤ s' ∧
    ∀ (c : ℤ), 0 < c → ∀ (M₁ M₂ : ℕ) (γ' : ℝ) (N : ℕ) (f : ℤ → ℂ),
      1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ' → γ' ≤ 1 → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      ∀ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool), Function.Injective ωOf →
        (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) →
      boxAvgGen s M₁ c ωOf (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N f ≤
        C * Work.Peluse.uNorm s' (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f

/-- `NormCrux` implies `AveragedCrux`: the average of quantities each bounded by `uNorm s'` is
bounded by the same quantity.  (So the averaged gap is strictly weaker.) -/
theorem averagedCrux_of_normCrux (h : NormCrux) : AveragedCrux := by
  classical
  intro s hs
  obtain ⟨cs, hcs, hcrux⟩ := h s hs
  refine ⟨cs⁻¹, inv_pos.mpr hcs, 2 ^ s, ?_, ?_⟩
  · have : 4 ≤ 2 ^ s := by
      calc (4 : ℕ) = 2 ^ 2 := rfl
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega
  intro c hc M₁ M₂ γ' N f hM₂ hM₂M₁ hN hNc hγ' hγ'1 hsup hbd ωOf hωinj hωnz
  have hM₁ : 1 ≤ M₁ := le_trans hM₂ hM₂M₁
  have hcard1 : (((Finset.univ : Finset (Fin s → Fin M₁)).card : ℕ) : ℝ) = (M₁ : ℝ) ^ s := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  have hU : (0 : ℝ) ≤ Work.Peluse.uNorm (2 ^ s)
      (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (Work.Peluse.symIcc N) f :=
    uNorm_nonneg _ _ _ _
  have hterm : ∀ h h' : Fin s → Fin M₁,
      (if IsBad (tupSub h h') then (0 : ℝ) else Zbox c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N ωOf f
          (tupSub h h'))
        ≤ cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
            (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
            (Work.Peluse.symIcc N) f := by
    intro h h'
    by_cases hb : IsBad (tupSub h h')
    · simp only [hb, if_true]
      positivity
    · simp only [hb, if_false]
      have := hcrux c hc M₁ M₂ γ' N f hM₂ hM₂M₁ hN hNc hγ' hγ'1 hsup hbd ωOf hωinj hωnz
        (tupSub h h') hb
      calc Zbox c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N ωOf f (tupSub h h')
          = cs⁻¹ * (cs * Zbox c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N ωOf f (tupSub h h')) := by
            field_simp
        _ ≤ cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
              (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
              (Work.Peluse.symIcc N) f := mul_le_mul_of_nonneg_left this (by positivity)
  rw [boxAvgGen]
  have hsum : (∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁,
        (if IsBad (tupSub h h') then (0 : ℝ) else Zbox c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N ωOf f
          (tupSub h h')))
      ≤ (M₁ : ℝ) ^ (2 * s) * (cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
          (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f) := by
    calc (∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁, _)
        ≤ ∑ _h : Fin s → Fin M₁, (((Finset.univ : Finset (Fin s → Fin M₁)).card : ℕ) : ℝ) *
            (cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
              (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
              (Work.Peluse.symIcc N) f) := by
          refine Finset.sum_le_sum fun h _ => ?_
          calc (∑ h' : Fin s → Fin M₁, _)
              ≤ ∑ _h' : Fin s → Fin M₁, (cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
                  (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
                  (Work.Peluse.symIcc N) f) :=
                Finset.sum_le_sum fun h' _ => hterm h h'
            _ = (((Finset.univ : Finset (Fin s → Fin M₁)).card : ℕ) : ℝ) *
                  (cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
                    (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
                    (Work.Peluse.symIcc N) f) := by
                simp [Finset.sum_const, nsmul_eq_mul]
      _ = (M₁ : ℝ) ^ (2 * s) * (cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
            (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
            (Work.Peluse.symIcc N) f) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard1, ← mul_assoc, ← pow_add,
            show s + s = 2 * s from by ring]
  calc ((M₁ : ℝ))⁻¹ ^ (2 * s) * (∑ h : Fin s → Fin M₁, ∑ h' : Fin s → Fin M₁, _)
      ≤ ((M₁ : ℝ))⁻¹ ^ (2 * s) * ((M₁ : ℝ) ^ (2 * s) * (cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
          (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = cs⁻¹ * Work.Peluse.uNorm (2 ^ s)
          (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f := by
        have hMne : (M₁ : ℝ) ≠ 0 := by positivity
        rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hMne), one_mul]

/-- **The `s = 2` case** of `AveragedCrux` (the base case of the ladder, cf. Peluse's Lemma 5.5:
the `s = 2` case of her Lemma 5.1 is proved separately and is the hardest of the base cases).  It is
the instance of `AveragedCrux` at level `2`; in the workspace's transposed parameterisation this is
the statement that the average over the shift pairs of the level-`3` box-norm powers with the
*dilated long* direction families `c((h-h')·ω_i)[D]` is dominated by the level-`s'` uniformity norm
of `f` at the undilated scale `c[D]`, `D = ⌊γ'M₁M₂⌋`. -/
def AveragedCruxTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ s' : ℕ, 3 ≤ s' ∧
    ∀ (c : ℤ), 0 < c → ∀ (M₁ M₂ : ℕ) (γ' : ℝ) (N : ℕ) (f : ℤ → ℂ),
      1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
      0 < γ' → γ' ≤ 1 → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      ∀ ωOf : Fin (2 ^ 2 - 1) → (Fin 2 → Bool), Function.Injective ωOf →
        (∀ i : Fin (2 ^ 2 - 1), ωOf i ≠ 0) →
      boxAvgGen 2 M₁ c ωOf (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat N f ≤
        C * Work.Peluse.uNorm s' (Work.Peluse.arithIcc c (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (Work.Peluse.symIcc N) f

/-- `AveragedCrux` implies its `s = 2` case `AveragedCruxTwo` (so the latter is the base case of
the former). -/
theorem averagedCruxTwo_of_averagedCrux (h : AveragedCrux) : AveragedCruxTwo := by
  classical
  obtain ⟨C, hC, s', hs', hcrux⟩ := h 2 (by norm_num)
  exact ⟨C, hC, s', hs', fun c hc M₁ M₂ γ' N f hM₂ hM₂M₁ hN hNc hγ' hγ'1 hsup hbd ωOf hωinj hωnz =>
    hcrux c hc M₁ M₂ γ' N f hM₂ hM₂M₁ hN hNc hγ' hγ'1 hsup hbd ωOf hωinj hωnz⟩

end

end Work.Peluse.Concat

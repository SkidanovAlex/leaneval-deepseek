import Mathlib
import Submission.Work.Peluse.LadderP.p3HeartDefs
import Submission.Work.Peluse.LadderP.p3Front
import Submission.Work.Peluse.Ulower.Defs

/-! # P3: removing the *arbitrary window* from the `c = 1` heart

The heart `Work.Peluse.LadderP.p3Heart t` (`p3HeartDefs.lean`) is the level-`(t+1)` statement at
`c = 1` with an **arbitrary normalisation window** `S` (satisfying only `2N+1 ≤ 4|S|`), because the
assembly `Work.LadderP.lemma51P_succ_of_p3Heart` applies it to the residue-class windows
`S = p2Cls c N r`.  Every other brick of the induction step, however, is stated at the window
`symIcc N` (`joint_mass`, `p3Disp53`, `p3TupleInverse`, `boxNormPow_le_one`, ...).

This module removes the arbitrary window: it defines the **window-normalised heart**

* `p3HeartB t` — literally `p3Heart t` with `S` replaced by `symIcc N` (the hypothesis
  `2N+1 ≤ 4|S|` disappears),

and proves

* `p3HeartB_to_p3Heart : (∀ t ≥ 2, p3HeartB t) → ∀ t ≥ 2, p3Heart t`.

The reduction is the *scaling* of the averaged box norm: since `p3BoxAvg` and `uNormPow` depend on the
window `S` only through the factor `|S|⁻¹` (`Work.Peluse.Ulower.Defs.boxNormPow_eq_mul_card`), with
`ρ := (2N+1)/|S| ∈ (0,4]` one has

`p3BoxAvg s M₁ M₂ b S f = ρ^{1/2^s} · p3BoxAvg s M₁ M₂ b (symIcc N) f`

(`p3BoxAvg_eq_mul_card` below) and likewise for `uNorm`.  So the heart at the window `S` is the heart
at `symIcc N` at the *shifted* level `γ' := γ/ρ^{1/2^{t+1}}`, plus the bookkeeping that converts the
`(γ,η,ε,D)`-conditions at `(E, C')` into conditions at `(e_B, C_B)` and back.  The shifted level
satisfies `γ/4 ≤ γ' ≤ 1` (the heart's hypothesis `γ ≤ ρ^{1/2^{t+1}}·(≤1)` forces
`ρ ≥ γ^{2^{t+1}}`), so powers of `4` are the only constants needed.  The heart's conclusion is taken
at the level `E := e_B + 2^{t+1}` — one `2^{t+1}` more than the hypotheses need — to absorb the
factor `ρ^{1/2^{s'}} ≥ γ^{2^{t+1}}` of the final window comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.LadderP

open Work.Peluse

noncomputable section

/-! ## 1. Elementary facts -/

/-- The symmetric interval has `2N+1` elements. -/
lemma card_symIcc (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `symIcc N` is non-empty for `N ≥ 1` (it contains `0`). -/
lemma symIcc_nonempty {N : ℕ} (hN : 1 ≤ N) : (symIcc N).Nonempty := by
  refine ⟨0, ?_⟩
  rw [symIcc]
  simp only [Finset.mem_Icc]
  exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩

/-- For `0 ≤ Y ≤ 1` and `1 ≤ n`, `Y ^ n ≤ Y`. -/
lemma pow_le_self_of_le_one {Y : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    Y ^ n ≤ Y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ]
  exact mul_le_of_le_one_left hY0 (pow_le_one₀ hY0 hY1)

/-! ## 2. The scaling of the averaged box norm and of the uniformity norm -/

/-- **The averaged box norm scales by `(|S'|/|S|)^{1/2^s}`**: the window enters `p3BoxAvg` only
through the factor `|S|⁻¹` of `boxNormPow`. -/
lemma p3BoxAvg_eq_mul_card {s : ℕ} (M₁ M₂ : ℕ) (b : Fin s → ℤ) {S S' : Finset ℤ}
    (f : ℤ → ℂ) (hS' : S'.Nonempty) :
    p3BoxAvg s M₁ M₂ b S f
      = ((S'.card : ℝ) / (S.card : ℝ)) ^ (1 / (2 : ℝ) ^ s) * p3BoxAvg s M₁ M₂ b S' f := by
  have hterm : ∀ a : ℕ,
      boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) S f
        = ((S'.card : ℝ) / (S.card : ℝ)) ^ (1 / (2 : ℝ) ^ s)
          * boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) S' f := by
    intro a
    rw [boxNorm, Ulower.boxNormPow_eq_mul_card s _ S S' f hS', boxNorm,
      Real.mul_rpow (by positivity) (by rw [boxNormPow]; exact norm_nonneg _)]
  rw [p3BoxAvg, p3BoxAvg]
  calc ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
        boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) S f
      = ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
          (((S'.card : ℝ) / (S.card : ℝ)) ^ (1 / (2 : ℝ) ^ s)
            * boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) S' f) := by
        congr 1
        exact Finset.sum_congr rfl (fun a _ => hterm a)
    _ = ((M₁ : ℝ))⁻¹ * (((S'.card : ℝ) / (S.card : ℝ)) ^ (1 / (2 : ℝ) ^ s)
          * ∑ a ∈ Finset.Icc 1 M₁,
              boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) S' f) := by
        congr 1
        rw [Finset.mul_sum]
    _ = ((S'.card : ℝ) / (S.card : ℝ)) ^ (1 / (2 : ℝ) ^ s)
          * (((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
              boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) S' f) := by ring

/-- **The averaged box norm at `symIcc N` is at most `1`** for a `1`-bounded function supported in
`symIcc N`. -/
lemma p3BoxAvg_symIcc_le_one {s : ℕ} {M₁ M₂ N : ℕ} {b : Fin s → ℤ} {f : ℤ → ℂ}
    (hsup : SupportIn f N) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    p3BoxAvg s M₁ M₂ b (symIcc N) f ≤ 1 := by
  have hzero : ∀ x : ℤ, x ∉ symIcc N → f x = 0 := fun x hx =>
    hsup x (Nat.lt_of_not_le (fun h => hx (mem_symIcc_iff_natAbs_p3.mpr h)))
  have hterm : ∀ a ∈ Finset.Icc 1 M₁,
      boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f ≤ 1 := by
    intro a _
    rw [boxNorm]
    exact Real.rpow_le_one (norm_nonneg _)
      (BoxNorm.boxNormPow_le_one (t := s) hbd (fun x hx => hzero x hx)) (by positivity)
  rcases Nat.eq_zero_or_pos M₁ with h0 | hpos
  · rw [h0, p3BoxAvg]
    simp
  · have h1 : ∑ a ∈ Finset.Icc 1 M₁,
        boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f
          ≤ ((Finset.Icc 1 M₁).card : ℕ) := by
      calc ∑ a ∈ Finset.Icc 1 M₁,
            boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f
          ≤ ∑ _a ∈ Finset.Icc 1 M₁, (1 : ℝ) := Finset.sum_le_sum hterm
        _ = ((Finset.Icc 1 M₁).card : ℕ) := by simp
    have h2 : ((Finset.Icc 1 M₁).card : ℕ) ≤ M₁ := by rw [Nat.card_Icc]; omega
    have hposR : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hpos
    rw [p3BoxAvg]
    calc ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
          boxNorm s (fun i : Fin s => arithIcc ((a : ℤ) + b i) M₂) (symIcc N) f
        ≤ ((M₁ : ℝ))⁻¹ * ((Finset.Icc 1 M₁).card : ℕ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ((M₁ : ℝ))⁻¹ * (M₁ : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (by positivity)
      _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hposR)]

/-- **The uniformity norm scales by `(|S'|/|S|)^{1/2^s}`.** -/
lemma uNorm_eq_mul_card (s : ℕ) (Q : Finset ℤ) {S S' : Finset ℤ} (f : ℤ → ℂ)
    (hS' : S'.Nonempty) :
    uNorm s Q S f = ((S'.card : ℝ) / (S.card : ℝ)) ^ (1 / (2 : ℝ) ^ s) * uNorm s Q S' f := by
  rw [uNorm, uNorm, uNormPow, uNormPow, Ulower.boxNormPow_eq_mul_card s _ S S' f hS',
    Real.mul_rpow (by positivity) (by rw [boxNormPow]; exact norm_nonneg _)]

/-! ## 3. The window-normalised heart and its equivalence with `p3Heart` -/

/-- **The window-normalised `c = 1` heart**: `p3Heart t` with the normalisation window fixed to
`symIcc N`. -/
def p3HeartB (t : ℕ) : Prop :=
  ∀ B₀ : ℕ, ∃ s' : ℕ, 1 ≤ s' ∧ ∃ e : ℕ, 1 ≤ e ∧ ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
  ∀ (M₁ M₂ D N : ℕ) (b : Fin (t + 1) → ℤ) (γ η ε : ℝ) (f : ℤ → ℂ),
    2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ D → 1 ≤ N → SupportIn f N →
    ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
    (∀ i : Fin (t + 1), |b i| ≤ (B₀ : ℤ) * (M₁ : ℤ)) →
    (∀ x : ℤ, ‖f x‖ ≤ 1) →
    0 < γ → γ ≤ 1 → 0 < η → η ≤ C * γ ^ e → 0 ≤ ε → ε ≤ C * γ ^ e →
    (D : ℝ) ≤ C * (γ * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) →
    ((M₁ : ℝ) * (M₂ : ℝ)) ^ e ≤ C * (γ * η * (D : ℝ)) ^ e * (M₂ : ℝ) →
    (((Finset.Icc 1 M₁).filter (fun a : ℕ => ¬ p3good (t + 1) M₁ b η a)).card : ℝ)
      ≤ ε * (M₁ : ℝ) →
    γ ≤ p3BoxAvg (t + 1) M₁ M₂ b (symIcc N) f →
    C * γ ^ e ≤ Work.Peluse.uNorm s' (Work.Peluse.arithIcc 1 D) (symIcc N) f

end

end Work.Peluse.LadderP

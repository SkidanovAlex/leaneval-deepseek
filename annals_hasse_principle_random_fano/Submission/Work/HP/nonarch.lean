import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.sum_Floc_sigQ_rpow_le
import Submission.Work.HP.NA.bigW_bounds
import Submission.Work.HP.NA.primCount_le_fiber
import Submission.Work.HP.NA.badcard_le_rpow
import Submission.Work.HP.NA.sum_primFinset_bigW_le
import Submission.Work.HP.NA.sigQ_bigW_pos
import Submission.Work.HP.NA.isPrimGen_intCast_of_isPrim
import Submission.Work.HP.NA.sum_FlocInset_eq_primFinset
import Submission.Work.HP.NA.final_arith

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false



/-!
Node N11 (`nonarch`): the non-Archimedean factor is rarely small, normalised by `A^N`.

The proof follows Browning--Le Boudec--Sawin, Section 5.2.  All the analytic/number-theoretic
content is in the helper modules under `Submission/Work/HP/NA/`; this file assembles it.
-/

open Filter
set_option autoImplicit false

noncomputable section

namespace Work.HP

/-- `sigmaLoc` for an integer coefficient vector agrees with `sigQ` for its reduction. -/
private lemma sigmaLoc_eq_sigQ (d n W : ℕ) (a : Mon d n → ℤ) :
    sigmaLoc d n a W = NA.sigQ d n W (fun m => (a m : ZMod W)) := rfl

/-- N11. Proposition "non-Archimedean factor rarely small", normalised by `A^N`. -/
theorem nonarch (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => LocSet d n (wOf (A * φ)) a ∧
          sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6))
        ≤ K * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨C₁, hC₁pos, hper₀⟩ := NA.sum_Floc_sigQ_rpow_le d n hd hn
  refine ⟨3 ^ NN d n * C ^ (1 / (4 * (n : ℝ))) * Real.exp (5 * C₁),
    by positivity, ?_⟩
  intro φ hφ
  -- the per-prime bound on the *primitive* sums
  have hper : ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ NA.primFinset d n (p ^ r),
          (NA.sigQ d n (p ^ r) a) ^ (-(1 / (4 * (n : ℝ)))))
        ≤ (p : ℝ) ^ (r * NN d n) * (1 + C₁ / (p : ℝ) ^ ((5 : ℝ) / 4)) := by
    intro p r _ hp hr
    rw [← NA.sum_FlocInset_eq_primFinset d n p r hn1]
    exact hper₀ p r hp hr
  filter_upwards [NA.bigW_bounds φ hφ, eventually_gt_atTop (0 : ℝ)] with A hA hApos
  obtain ⟨hW1, hWA⟩ := hA
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hApos
  have hWpos : 0 < bigW (wOf (A * φ)) :=
    Nat.cast_pos.mp (lt_of_lt_of_le zero_lt_one hW1)
  have hWposR : (0 : ℝ) < (bigW (wOf (A * φ)) : ℝ) := by exact_mod_cast hWpos
  haveI : NeZero (bigW (wOf (A * φ))) := ⟨ne_of_gt hWpos⟩
  have hκpos : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
  have hC₀pos : (0 : ℝ) < C / φ ^ ((1 : ℝ) / 6) := by
    have : (0 : ℝ) < φ ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (lt_trans zero_lt_one hφ) _
    positivity
  set P : (Mon d n → ℤ) → Prop := fun a =>
    IsPrim a ∧ (LocSet d n (wOf (A * φ)) a ∧
      sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6)) with hPdef
  set Bad : (Mon d n → ZMod (bigW (wOf (A * φ)))) → Prop := fun c =>
    NA.IsPrimGen (bigW (wOf (A * φ))) c ∧ 0 < NA.sigQ d n (bigW (wOf (A * φ))) c ∧
      NA.sigQ d n (bigW (wOf (A * φ))) c < C / φ ^ ((1 : ℝ) / 6) with hBaddef
  have hP : ∀ a, P a → Bad (fun m => (a m : ZMod (bigW (wOf (A * φ))))) := by
    rintro a ⟨hpr, hLoc, hlt⟩
    refine ⟨NA.isPrimGen_intCast_of_isPrim a hpr, ?_, ?_⟩
    · exact NA.sigQ_bigW_pos d n (wOf (A * φ)) a (fun p hp hpw => hLoc.2 p hp hpw)
    · rw [← sigmaLoc_eq_sigQ d n (bigW (wOf (A * φ))) a]; exact hlt
  have hfib := NA.primCount_le_fiber d n (bigW (wOf (A * φ))) hWpos A hA0 P Bad hP
  have hbad := NA.badcard_le_rpow d n (bigW (wOf (A * φ)))
    (C / φ ^ ((1 : ℝ) / 6)) (1 / (4 * (n : ℝ))) hC₀pos hκpos
  have hsum := NA.sum_primFinset_bigW_le d n C₁ hC₁pos (wOf (A * φ))
    (1 / (4 * (n : ℝ))) hκpos hper
  have hcard : (Nat.card {c : Mon d n → ZMod (bigW (wOf (A * φ))) //
        NA.IsPrimGen (bigW (wOf (A * φ))) c ∧
          0 < NA.sigQ d n (bigW (wOf (A * φ))) c ∧
          NA.sigQ d n (bigW (wOf (A * φ))) c < C / φ ^ ((1 : ℝ) / 6)} : ℝ)
      ≤ (C / φ ^ ((1 : ℝ) / 6)) ^ (1 / (4 * (n : ℝ))) *
          ((bigW (wOf (A * φ)) : ℝ) ^ (NN d n) * Real.exp (5 * C₁)) := by
    calc (Nat.card _ : ℝ)
        ≤ (C / φ ^ ((1 : ℝ) / 6)) ^ (1 / (4 * (n : ℝ))) *
            (∑ c ∈ NA.primFinset d n (bigW (wOf (A * φ))),
              (NA.sigQ d n (bigW (wOf (A * φ))) c) ^ (-(1 / (4 * (n : ℝ))))) := hbad
      _ ≤ (C / φ ^ ((1 : ℝ) / 6)) ^ (1 / (4 * (n : ℝ))) *
            ((bigW (wOf (A * φ)) : ℝ) ^ (NN d n) * Real.exp (5 * C₁)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  have hset : primSet d n A (fun a => LocSet d n (wOf (A * φ)) a ∧
        sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6))
      = primSet d n A (fun a => IsPrim a ∧ (LocSet d n (wOf (A * φ)) a ∧
        sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6))) := by
    ext a
    simp only [primSet, Set.mem_setOf_eq]
    tauto
  have hprim : primCount d n A (fun a => LocSet d n (wOf (A * φ)) a ∧
        sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6)) = primCount d n A P := by
    unfold primCount
    rw [hset, hPdef]
  calc primCount d n A (fun a => LocSet d n (wOf (A * φ)) a ∧
          sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6))
      = primCount d n A P := hprim
    _ ≤ (2 * A / (bigW (wOf (A * φ)) : ℝ) + 1) ^ (NN d n) *
          (Nat.card {c : Mon d n → ZMod (bigW (wOf (A * φ))) //
            NA.IsPrimGen (bigW (wOf (A * φ))) c ∧
              0 < NA.sigQ d n (bigW (wOf (A * φ))) c ∧
              NA.sigQ d n (bigW (wOf (A * φ))) c < C / φ ^ ((1 : ℝ) / 6)} : ℝ) := hfib
    _ ≤ (2 * A / (bigW (wOf (A * φ)) : ℝ) + 1) ^ (NN d n) *
          ((C / φ ^ ((1 : ℝ) / 6)) ^ (1 / (4 * (n : ℝ))) *
            ((bigW (wOf (A * φ)) : ℝ) ^ (NN d n) * Real.exp (5 * C₁))) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (3 ^ NN d n * C ^ (1 / (4 * (n : ℝ))) * Real.exp (5 * C₁)) * A ^ NN d n
          / φ ^ (1 / (24 * (n : ℝ))) :=
          NA.final_arith d n C C₁ (bigW (wOf (A * φ)) : ℝ) A φ hd hn hC hC₁pos hWposR hWA hA0 hφ

end Work.HP

import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Repelling.defect_bound
import Submission.Work.FatouCoord.Repelling.defect_lipschitz
import Submission.Work.FatouCoord.Flower.norm_defect_le
import Submission.Work.FatouCoord.Flower.norm_Lambda_sub_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The correction `Z w = V w - w - (1 - a) Λ w` is bounded

Let `f z = z + z ^ 2 h z` be a parabolic germ with `h 0 = 1` and `a = h'(0)`, and let `V` be an
*injective* solution of the conjugacy equation `V (w + 1) = wMap f (V w)` on a left half-plane
`{Re w < -R}`, with `V w ≈ w` and with a quantitative right inverse (`hVinv`).  Then the
correction `Z w = V w - w - (1 - a) Λ w` is bounded on a far left half-plane.

The proof is the "shift left" argument.  The defining property of the defect is

`Z (w + 1) - Z w = defect f a w (Z w)`,

and on `{Re w < -1}` the defect is `O((1 + log ‖w‖ + ‖ζ‖)/‖w‖²)` for `‖ζ‖ ≤ C √‖w‖`
(`Flower.norm_defect_le`).  Two facts close the argument:

* For `x` far to the left there is a shift `k` such that `y = x - k` satisfies `‖V y‖ ≥ R₁` and
  `(V y - (1-a) Λ (V y)).re < -R₁`; the inverse hypothesis `hVinv` applied at `V y` then identifies
  the preimage with `y` (by injectivity) and gives `‖Z y‖ ≤ 4 + C`.
* Telescoping the defect equation along `x, x - 1, …, x - k` bounds `‖Z x - Z y‖` by the
  convergent series `∑_j 1/((j + 1 + R₂) √(j + 1 + R₂))`.
-/

namespace Work.FatouCoord.Flower

open Work.FatouCoord Work.FatouCoord.Petal

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-! ## Elementary real estimates -/

/-- `1 + log t ≤ 3 √t` for `t ≥ 1`. -/
private lemma one_add_log_le_three_sqrt {t : ℝ} (h1 : 1 ≤ t) :
    1 + Real.log t ≤ 3 * Real.sqrt t := by
  have h2 : Real.log t ≤ 2 * Real.sqrt t := by
    have := Repelling.abs_log_le_two_sqrt h1
    linarith [le_abs_self (Real.log t)]
  have h3 : 1 ≤ Real.sqrt t := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt h1
  linarith

/-- `u ↦ 1/(u √u)` is antitone on the positive reals. -/
private lemma inv_mul_sqrt_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    1 / (v * Real.sqrt v) ≤ 1 / (u * Real.sqrt u) := by
  refine one_div_le_one_div_of_le (by positivity) ?_
  exact mul_le_mul huv (Real.sqrt_le_sqrt huv) (Real.sqrt_nonneg u) (le_trans hu.le huv)

/-- `√t / t² = 1/(t √t)`. -/
private lemma sqrt_div_sq_eq_inv_mul_sqrt {t : ℝ} (ht : 0 < t) :
    Real.sqrt t / t ^ 2 = 1 / (t * Real.sqrt t) := by
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [hs]

/-- Linear beats square root: for `A, B, N ≥ 0` and `s > 0` there is `k` with
`A √(N + k) + B < k + s`. -/
private lemma exists_nat_sqrt_lt' {A B N s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hs : 0 < s) : ∃ k : ℕ, A * Real.sqrt (N + (k : ℝ)) + B < (k : ℝ) + s := by
  set M : ℝ := max N (max (8 * A ^ 2) (max (2 * B) 1)) with hMdef
  have hNM : N ≤ M := by rw [hMdef]; exact le_max_left _ _
  have h8AM : 8 * A ^ 2 ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h2BM : 2 * B ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨k, hk⟩ := exists_nat_gt M
  have hkM : M ≤ (k : ℝ) := le_of_lt hk
  have hNk : N ≤ (k : ℝ) := le_trans hNM hkM
  have h8A : 8 * A ^ 2 ≤ (k : ℝ) := le_trans h8AM hkM
  have h2B : 2 * B ≤ (k : ℝ) := le_trans h2BM hkM
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hstep1 : Real.sqrt (N + (k : ℝ)) ≤ Real.sqrt (2 * (k : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hstep2 : A * Real.sqrt (2 * (k : ℝ)) ≤ (k : ℝ) / 2 := by
    have hA2 : A ^ 2 * (2 * (k : ℝ)) ≤ ((k : ℝ) / 2) ^ 2 := by
      have h1 : A ^ 2 ≤ (k : ℝ) / 8 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
        linarith
      calc A ^ 2 * (2 * (k : ℝ)) ≤ ((k : ℝ) / 8) * (2 * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = ((k : ℝ) / 2) ^ 2 := by ring
    have hmul : Real.sqrt (A ^ 2 * (2 * (k : ℝ))) = A * Real.sqrt (2 * (k : ℝ)) := by
      rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
    rw [← hmul]
    calc Real.sqrt (A ^ 2 * (2 * (k : ℝ))) ≤ Real.sqrt (((k : ℝ) / 2) ^ 2) :=
          Real.sqrt_le_sqrt hA2
      _ = (k : ℝ) / 2 := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  have hBk : B ≤ (k : ℝ) / 2 := by linarith
  refine ⟨k, ?_⟩
  have hmain : A * Real.sqrt (N + (k : ℝ)) ≤ (k : ℝ) / 2 :=
    le_trans (mul_le_mul_of_nonneg_left hstep1 hA) hstep2
  linarith

/-- `∑_{j<k} 1/((j + 1 + R) √(j + 1 + R)) ≤ 2/√R` for `R > 0`. -/
private lemma sum_range_inv_mul_sqrt_le' {R : ℝ} (hR : 0 < R) (k : ℕ) :
    ∑ j ∈ Finset.range k, 1 / (((j : ℝ) + 1 + R) * Real.sqrt ((j : ℝ) + 1 + R))
      ≤ 2 / Real.sqrt R := by
  have hterm : ∀ j : ℕ,
      1 / (((j : ℝ) + 1 + R) * Real.sqrt ((j : ℝ) + 1 + R))
        ≤ 2 * (1 / Real.sqrt ((j : ℝ) + R) - 1 / Real.sqrt ((j : ℝ) + 1 + R)) := by
    intro j
    set s : ℝ := (j : ℝ) + R with hsdef
    set t : ℝ := (j : ℝ) + 1 + R with htdef
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hs0 : 0 < s := by rw [hsdef]; linarith
    have ht0 : 0 < t := by rw [htdef]; linarith
    have hts : t = s + 1 := by rw [htdef, hsdef]; ring
    have hsqs : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
    have hsqst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hsqrt : (Real.sqrt t - Real.sqrt s) * (Real.sqrt t + Real.sqrt s) = 1 := by
      nlinarith [hsqs, hsqst, hts]
    have hrev : Real.sqrt t - Real.sqrt s = 1 / (Real.sqrt t + Real.sqrt s) := by
      rw [eq_div_iff (by positivity : Real.sqrt t + Real.sqrt s ≠ 0)]
      exact hsqrt
    have hfac : 2 * (1 / Real.sqrt s - 1 / Real.sqrt t)
        = 2 * ((Real.sqrt t - Real.sqrt s) / (Real.sqrt s * Real.sqrt t)) := by
      rw [div_sub_div (1 : ℝ) (1 : ℝ) (by positivity : Real.sqrt s ≠ 0)
        (by positivity : Real.sqrt t ≠ 0)]
      try ring
    have hmid : 2 * ((Real.sqrt t - Real.sqrt s) / (Real.sqrt s * Real.sqrt t))
        = 2 / ((Real.sqrt t + Real.sqrt s) * Real.sqrt s * Real.sqrt t) := by
      rw [hrev]
      field_simp
      try ring
    have hbound : 1 / (t * Real.sqrt t)
        ≤ 2 / ((Real.sqrt t + Real.sqrt s) * Real.sqrt s * Real.sqrt t) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < t * Real.sqrt t)
        (by positivity : (0 : ℝ) < (Real.sqrt t + Real.sqrt s) * Real.sqrt s * Real.sqrt t)]
      have hst : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt (by rw [hts]; linarith)
      have h1 : (Real.sqrt t + Real.sqrt s) * Real.sqrt s ≤ 2 * t := by
        have h2 : Real.sqrt t * Real.sqrt s ≤ t := by
          calc Real.sqrt t * Real.sqrt s ≤ Real.sqrt t * Real.sqrt t :=
                mul_le_mul_of_nonneg_left hst (Real.sqrt_nonneg t)
            _ = t := hsqst
        have h3 : (Real.sqrt t + Real.sqrt s) * Real.sqrt s
            = Real.sqrt t * Real.sqrt s + s := by rw [add_mul, hsqs]
        rw [h3]
        linarith [h2, hts]
      have h4 : (Real.sqrt t + Real.sqrt s) * Real.sqrt s * Real.sqrt t
          ≤ 2 * t * Real.sqrt t := by
        have h5 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg t)
        linarith [h5]
      nlinarith [h4]
    linarith [hfac, hmid, hbound]
  have hstep : ∀ j : ℕ,
      (1 / Real.sqrt ((j : ℝ) + R) - 1 / Real.sqrt ((j : ℝ) + 1 + R))
        = ((fun i : ℕ => 1 / Real.sqrt ((i : ℝ) + R)) j
            - (fun i : ℕ => 1 / Real.sqrt ((i : ℝ) + R)) (j + 1)) := by
    intro j
    simp only [Nat.cast_add, Nat.cast_one]
  calc ∑ j ∈ Finset.range k, 1 / (((j : ℝ) + 1 + R) * Real.sqrt ((j : ℝ) + 1 + R))
      ≤ ∑ j ∈ Finset.range k,
          2 * (1 / Real.sqrt ((j : ℝ) + R) - 1 / Real.sqrt ((j : ℝ) + 1 + R)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = 2 * (1 / Real.sqrt R - 1 / Real.sqrt ((k : ℝ) + R)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_congr rfl (fun j _ => hstep j),
          Finset.sum_range_sub' (fun j : ℕ => 1 / Real.sqrt ((j : ℝ) + R))]
        norm_num
    _ ≤ 2 / Real.sqrt R := by
        have h1 : 0 ≤ 2 / Real.sqrt ((k : ℝ) + R) := by positivity
        rw [show 2 * (1 / Real.sqrt R - 1 / Real.sqrt ((k : ℝ) + R))
            = 2 / Real.sqrt R - 2 / Real.sqrt ((k : ℝ) + R) by ring]
        linarith

/-! ## The main theorem -/

theorem Z_bounded {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') {R : ℝ} (hRr : 1 / r < R) (V : ℂ → ℂ) (hVdiff : DifferentiableOn ℂ V {w : ℂ | w.re < -R}) (hVshift : ∀ w : ℂ, w.re < -R → V (w + 1) = Work.FatouCoord.wMap f (V w)) (hVbd : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖) (hVref : ∀ w : ℂ, w.re < -R → ‖V w - w‖ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2) (hVinj : Set.InjOn V {w : ℂ | w.re < -R}) (hVinv : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ Y : ℂ, R₁ ≤ ‖Y‖ → (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y).re < -R₁ → ∃ x : ℂ, x.re < -R ∧ V x = Y ∧ ‖x - (Y - (1 - a) * Work.FatouCoord.Petal.Lambda Y)‖ ≤ 4) : ∃ C R₂ : ℝ, 0 < R₂ ∧ ∀ x : ℂ, x.re < -R₂ → ‖V x - x - (1 - a) * Work.FatouCoord.Petal.Lambda x‖ ≤ C := by
  obtain ⟨R₁, hR₁pos, hVinv'⟩ := hVinv
  set Z : ℂ → ℂ := fun w => V w - w - (1 - a) * Petal.Lambda w with hZ
  have hZval : ∀ w : ℂ, Z w = V w - w - (1 - a) * Petal.Lambda w := by intro w; simp [hZ]
  have hn0 : (0 : ℝ) ≤ ‖1 - a‖ := norm_nonneg _
  set C₀ : ℝ := 4 * ‖1 - a‖ + 4 * Real.pi * ‖1 - a‖ + 1 / 2 with hC₀
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀]; nlinarith [hn0, Real.pi_pos]
  -- (0) a priori bound coming from `hVref`
  have hapriori : ∀ w : ℂ, w.re < -R → 1 ≤ ‖w‖ →
      ‖Z w‖ ≤ 4 * ‖1 - a‖ * Real.sqrt ‖w‖ + (4 * Real.pi * ‖1 - a‖ + 1 / 2) := by
    intro w hw hw1
    have hL : ‖Petal.Lambda w‖ ≤ 2 * Real.sqrt ‖w‖ + 2 * Real.pi :=
      Repelling.norm_Lambda_le w hw1
    have hV := hVref w hw
    rw [hZval w]
    calc ‖V w - w - (1 - a) * Petal.Lambda w‖
        ≤ ‖V w - w‖ + ‖(1 - a) * Petal.Lambda w‖ := norm_sub_le _ _
      _ = ‖V w - w‖ + ‖1 - a‖ * ‖Petal.Lambda w‖ := by rw [norm_mul]
      _ ≤ (‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2)
            + ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) :=
          add_le_add hV (mul_le_mul_of_nonneg_left hL hn0)
      _ = 4 * ‖1 - a‖ * Real.sqrt ‖w‖ + (4 * Real.pi * ‖1 - a‖ + 1 / 2) := by ring
  -- (1) the defect bound with the constant `C₀`
  obtain ⟨Kd, Nd, hKdpos, hNdpos, hdefect⟩ := norm_defect_le (f := f) (h := h) (a := a) (r := r) hb C₀
  have hKdnn : 0 ≤ Kd := le_of_lt hKdpos
  have haprioriC : ∀ y : ℂ, y.re < -R → 1 ≤ ‖y‖ → ‖Z y‖ ≤ C₀ * Real.sqrt ‖y‖ := by
    intro y hy hy1
    have hsq1 : 1 ≤ Real.sqrt ‖y‖ := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt hy1
    have h := hapriori y hy hy1
    have h2 : (4 * Real.pi * ‖1 - a‖ + 1 / 2)
        ≤ (4 * Real.pi * ‖1 - a‖ + 1 / 2) * Real.sqrt ‖y‖ :=
      le_mul_of_one_le_right (by positivity) hsq1
    have h3 : 4 * ‖1 - a‖ * Real.sqrt ‖y‖ + (4 * Real.pi * ‖1 - a‖ + 1 / 2)
        ≤ (4 * ‖1 - a‖ + (4 * Real.pi * ‖1 - a‖ + 1 / 2)) * Real.sqrt ‖y‖ := by
      nlinarith [h2, Real.sqrt_nonneg ‖y‖]
    rw [hC₀]
    linarith [h, h3]
  -- (2) the shift identity for `Z`
  have hshiftZ : ∀ w : ℂ, w.re < -R → Z (w + 1) - Z w = Petal.defect f a w (Z w) := by
    intro w hw
    have h := hVshift w hw
    rw [hZval (w + 1), hZval w, h]
    rw [Petal.defect_apply, Petal.corr_apply]
    have e : w + (1 - a) * Petal.Lambda w + (V w - w - (1 - a) * Petal.Lambda w) = V w := by
      ring
    rw [e]
    ring
  -- (3) telescoping
  have htelescope : ∀ x : ℂ, x.re < -R → ∀ k : ℕ,
      Z x - Z (x - (k : ℂ))
        = ∑ j ∈ Finset.range k,
            Petal.defect f a (x - (((j + 1 : ℕ)) : ℂ)) (Z (x - (((j + 1 : ℕ)) : ℂ))) := by
    intro x hx k
    have hstep : ∀ i : ℕ, Z (x - (i : ℂ)) - Z (x - (((i + 1 : ℕ)) : ℂ))
        = Petal.defect f a (x - (((i + 1 : ℕ)) : ℂ)) (Z (x - (((i + 1 : ℕ)) : ℂ))) := by
      intro i
      have hre : (x - (((i + 1 : ℕ)) : ℂ)).re < -R := by
        simp only [Complex.sub_re, Complex.natCast_re]
        have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
      have h := hshiftZ (x - (((i + 1 : ℕ)) : ℂ)) hre
      rwa [show x - (((i + 1 : ℕ)) : ℂ) + 1 = x - (i : ℂ) by push_cast; ring] at h
    have h1 := Finset.sum_range_sub' (fun i : ℕ => Z (x - (i : ℂ))) k
    have h2 : ∑ i ∈ Finset.range k, (Z (x - (i : ℂ)) - Z (x - (((i + 1 : ℕ)) : ℂ)))
        = ∑ i ∈ Finset.range k,
            Petal.defect f a (x - (((i + 1 : ℕ)) : ℂ)) (Z (x - (((i + 1 : ℕ)) : ℂ))) :=
      Finset.sum_congr rfl (fun i _ => hstep i)
    rw [h2] at h1
    simp only [Nat.cast_zero, sub_zero] at h1
    exact h1.symm
  -- (4) constants
  set K₁ : ℝ := ‖1 - a‖ * (2 + 2 * Real.pi) + 1 / 2 with hK₁
  set K₂ : ℝ := 2 * K₁ + 2 * Real.pi with hK₂
  set B₁ : ℝ := (4 * Real.pi * ‖1 - a‖ + 1 / 2) + ‖1 - a‖ * K₂ + R₁ with hB₁
  set R₂ : ℝ := max (max (max R Nd) (2 * R₁)) 1 with hR₂
  have hR₂pos : 0 < R₂ := by
    rw [hR₂]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRR₂ : R ≤ R₂ := by
    rw [hR₂]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hNdR₂ : Nd ≤ R₂ := by
    rw [hR₂]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hR₁R₂ : 2 * R₁ ≤ R₂ := by
    rw [hR₂]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h1R₂ : (1 : ℝ) ≤ R₂ := by rw [hR₂]; exact le_max_right _ _
  have hK₁nn : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hB₁nn : 0 ≤ B₁ := by rw [hB₁, hK₂, hK₁]; nlinarith [hn0, Real.pi_pos, hR₁pos]
  refine ⟨4 + ‖1 - a‖ * K₂ + 2 * Kd * (3 + C₀) / Real.sqrt R₂ + 1,
    R₂, hR₂pos, fun x hx => ?_⟩
  rw [← hZval x]
  -- the good shift
  obtain ⟨k, hk⟩ := exists_nat_sqrt_lt' (A := 4 * ‖1 - a‖) (B := B₁) (N := ‖x‖) (s := -x.re)
    (by positivity) hB₁nn (norm_nonneg x) (by linarith)
  set y : ℂ := x - (k : ℂ) with hy
  have hyre' : y.re = x.re - (k : ℝ) := by rw [hy, Complex.sub_re, Complex.natCast_re]
  have hyneg : y.re < 0 := by
    rw [hyre']
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith [hx]
  have hyre : y.re < -R := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hyre']; linarith [hx, hRR₂, hk0]
  have hynorm : R₂ ≤ ‖y‖ := by
    have h1 : |y.re| ≤ ‖y‖ := Complex.abs_re_le_norm y
    rw [abs_of_neg hyneg, hyre'] at h1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith [hx]
  have hy1 : 1 ≤ ‖y‖ := le_trans h1R₂ hynorm
  have hVy_norm : R₁ ≤ ‖V y‖ := by
    have hb' := hVbd y hyre
    have h1 : ‖y‖ ≤ ‖V y - y‖ + ‖V y‖ := by
      calc ‖y‖ = ‖(y - V y) + V y‖ := by ring_nf
        _ ≤ ‖y - V y‖ + ‖V y‖ := norm_add_le _ _
        _ = ‖V y - y‖ + ‖V y‖ := by rw [norm_sub_rev]
    have h2 : ‖y‖ / 2 ≤ ‖V y‖ := by linarith [hb', norm_nonneg (V y)]
    linarith [hR₁R₂, hynorm]
  have hVy_y : ‖V y - y‖ ≤ ‖y‖ / 2 := by
    have h := hVbd y hyre
    linarith
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy1
  have hs1 : 1 ≤ Real.sqrt ‖y‖ := by simpa [Real.sqrt_one] using Real.sqrt_le_sqrt hy1
  have hyVsq : ‖V y - y‖ ≤ K₁ * Real.sqrt ‖y‖ := by
    have h := hVref y hyre
    have h1 : 2 * Real.sqrt ‖y‖ + 2 * Real.pi ≤ (2 + 2 * Real.pi) * Real.sqrt ‖y‖ := by
      nlinarith [hs1, Real.pi_pos]
    have h2 : ‖1 - a‖ * (2 * Real.sqrt ‖y‖ + 2 * Real.pi)
        ≤ ‖1 - a‖ * ((2 + 2 * Real.pi) * Real.sqrt ‖y‖) :=
      mul_le_mul_of_nonneg_left h1 hn0
    have h3 : ‖1 - a‖ * ((2 + 2 * Real.pi) * Real.sqrt ‖y‖) + 1 / 2
        ≤ (‖1 - a‖ * (2 + 2 * Real.pi) + 1 / 2) * Real.sqrt ‖y‖ := by
      nlinarith [hs1, hn0, Real.pi_pos]
    rw [hK₁]
    linarith [h, h2, h3]
  have hLam : ‖Petal.Lambda y - Petal.Lambda (V y)‖ ≤ K₂ := by
    have hyne : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hypos)
    have h1 : ‖Petal.Lambda (V y) - Petal.Lambda y‖ ≤ 2 * ‖V y - y‖ / ‖y‖ + 2 * Real.pi :=
      norm_Lambda_sub_close hyne hVy_y
    have hs : 0 < Real.sqrt ‖y‖ := Real.sqrt_pos.mpr hypos
    have h4 : 2 * ‖V y - y‖ / ‖y‖ ≤ 2 * K₁ := by
      have h5 : 2 * ‖V y - y‖ / ‖y‖ ≤ 2 * K₁ / Real.sqrt ‖y‖ := by
        rw [div_le_div_iff₀ hypos hs]
        have h6 := mul_le_mul_of_nonneg_right hyVsq (Real.sqrt_nonneg ‖y‖)
        nlinarith [Real.mul_self_sqrt hypos.le, h6]
      have h7 : 2 * K₁ / Real.sqrt ‖y‖ ≤ 2 * K₁ := by
        rw [div_le_iff₀ hs]
        nlinarith [hK₁nn, hs1]
      linarith [h5, h7]
    rw [norm_sub_rev, hK₂]
    linarith [h1, h4]
  have hZy : ‖Z y‖ ≤ 4 * ‖1 - a‖ * Real.sqrt (‖x‖ + (k : ℝ)) + (4 * Real.pi * ‖1 - a‖ + 1 / 2) := by
    have h := hapriori y hyre hy1
    have hyn : ‖y‖ ≤ ‖x‖ + (k : ℝ) := by
      calc ‖y‖ = ‖x - (k : ℂ)‖ := by rw [hy]
        _ ≤ ‖x‖ + ‖(k : ℂ)‖ := norm_sub_le _ _
        _ = ‖x‖ + (k : ℝ) := by rw [Complex.norm_natCast]
    have hsq : Real.sqrt ‖y‖ ≤ Real.sqrt (‖x‖ + (k : ℝ)) := Real.sqrt_le_sqrt hyn
    have h5 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * ‖1 - a‖)
    linarith [h, h5]
  have hVy_re : (V y - (1 - a) * Petal.Lambda (V y)).re < -R₁ := by
    have hkey : V y - (1 - a) * Petal.Lambda (V y)
        = y + Z y + (1 - a) * (Petal.Lambda y - Petal.Lambda (V y)) := by
      rw [hZval y]; ring
    have hbound : (V y - (1 - a) * Petal.Lambda (V y)).re
        ≤ y.re + ‖Z y‖ + ‖1 - a‖ * K₂ := by
      rw [hkey]
      have h3 : ((1 - a) * (Petal.Lambda y - Petal.Lambda (V y))).re ≤ ‖1 - a‖ * K₂ := by
        calc ((1 - a) * (Petal.Lambda y - Petal.Lambda (V y))).re
            ≤ ‖(1 - a) * (Petal.Lambda y - Petal.Lambda (V y))‖ := Complex.re_le_norm _
          _ = ‖1 - a‖ * ‖Petal.Lambda y - Petal.Lambda (V y)‖ := by rw [norm_mul]
          _ ≤ ‖1 - a‖ * K₂ := mul_le_mul_of_nonneg_left hLam hn0
      have h4 : (Z y).re ≤ ‖Z y‖ := Complex.re_le_norm _
      have h5 : (y + Z y + (1 - a) * (Petal.Lambda y - Petal.Lambda (V y))).re
          = y.re + (Z y).re + ((1 - a) * (Petal.Lambda y - Petal.Lambda (V y))).re := by
        simp only [Complex.add_re]
      rw [h5]
      linarith [h3, h4]
    have hfinal : y.re + ‖Z y‖ + ‖1 - a‖ * K₂ < -R₁ := by
      rw [hyre']
      rw [hB₁] at hk
      linarith [hZy, hk]
    linarith [hbound, hfinal]
  -- apply the inverse hypothesis
  obtain ⟨x', hx're, hVx', hdist⟩ := hVinv' (V y) hVy_norm hVy_re
  have hx'y : x' = y := hVinj hx're hyre hVx'
  have hdist' : ‖y - (V y - (1 - a) * Petal.Lambda (V y))‖ ≤ 4 := by
    have h := hdist
    rw [hx'y] at h
    exact h
  have hZy_small : ‖Z y‖ ≤ 4 + ‖1 - a‖ * K₂ := by
    have h1 : Z y = (V y - y - (1 - a) * Petal.Lambda (V y))
        + (1 - a) * (Petal.Lambda (V y) - Petal.Lambda y) := by
      rw [hZval y]; ring
    rw [h1]
    have h2 : ‖V y - y - (1 - a) * Petal.Lambda (V y)‖
        = ‖y - (V y - (1 - a) * Petal.Lambda (V y))‖ := by
      rw [show V y - y - (1 - a) * Petal.Lambda (V y)
          = -(y - (V y - (1 - a) * Petal.Lambda (V y))) by ring, norm_neg]
    calc ‖(V y - y - (1 - a) * Petal.Lambda (V y))
          + (1 - a) * (Petal.Lambda (V y) - Petal.Lambda y)‖
        ≤ ‖V y - y - (1 - a) * Petal.Lambda (V y)‖
          + ‖(1 - a) * (Petal.Lambda (V y) - Petal.Lambda y)‖ := norm_add_le _ _
      _ = ‖V y - y - (1 - a) * Petal.Lambda (V y)‖
          + ‖1 - a‖ * ‖Petal.Lambda (V y) - Petal.Lambda y‖ := by rw [norm_mul]
      _ ≤ 4 + ‖1 - a‖ * K₂ := by
          rw [h2]
          have h3 : ‖Petal.Lambda (V y) - Petal.Lambda y‖ ≤ K₂ := by
            rw [norm_sub_rev]; exact hLam
          linarith [hdist', mul_le_mul_of_nonneg_left h3 hn0]
  -- telescoping and summation
  have htel := htelescope x (by linarith [hx, hRR₂]) k
  have hsub : Z (x - (k : ℂ)) = Z y := by rw [hy]
  rw [hsub] at htel
  have hterm : ∀ j ∈ Finset.range k,
      ‖Petal.defect f a (x - (((j + 1 : ℕ)) : ℂ)) (Z (x - (((j + 1 : ℕ)) : ℂ)))‖
        ≤ Kd * (3 + C₀) / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂)) := by
    intro j hj
    set w : ℂ := x - (((j + 1 : ℕ)) : ℂ) with hw
    have hwre : w.re = x.re - ((j : ℝ) + 1) := by
      rw [hw, Complex.sub_re, Complex.natCast_re]; push_cast; ring
    have hwre1 : w.re < -1 := by
      rw [hwre]
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith [hx, h1R₂]
    have hwnorm : ((j : ℝ) + 1 + R₂) ≤ ‖w‖ := by
      have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      have h2 : w.re < 0 := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        rw [hwre]; linarith [hx, hRR₂, hj0]
      rw [abs_of_neg h2, hwre] at h1
      linarith [hx]
    have hw1 : 1 ≤ ‖w‖ := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith [hwnorm, h1R₂]
    have hwNd : Nd ≤ ‖w‖ := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith [hNdR₂, hwnorm]
    have hζ : ‖Z w‖ ≤ C₀ * Real.sqrt ‖w‖ := by
      apply haprioriC w _ hw1
      rw [hwre]; linarith [hRR₂, hx]
    have hdef := hdefect w (Z w) hwre1 hwNd hζ
    have hlog : 1 + Real.log ‖w‖ + ‖Z w‖ ≤ (3 + C₀) * Real.sqrt ‖w‖ := by
      have h1 := one_add_log_le_three_sqrt hw1
      nlinarith [h1, hζ, hC₀nn, Real.sqrt_nonneg ‖w‖]
    have hnum : Kd * (1 + Real.log ‖w‖ + ‖Z w‖) ≤ Kd * ((3 + C₀) * Real.sqrt ‖w‖) :=
      mul_le_mul_of_nonneg_left hlog hKdnn
    have hp2 : 0 < ‖w‖ ^ 2 := by positivity
    have hstep1 : Kd * (1 + Real.log ‖w‖ + ‖Z w‖) / ‖w‖ ^ 2
        ≤ Kd * (3 + C₀) * Real.sqrt ‖w‖ / ‖w‖ ^ 2 := by
      have hnum2 := mul_le_mul_of_nonneg_right hnum (le_of_lt hp2)
      rw [div_le_div_iff₀ hp2 hp2]
      linarith [hnum2]
    have hstep2 : Kd * (3 + C₀) * Real.sqrt ‖w‖ / ‖w‖ ^ 2
        = Kd * (3 + C₀) * (1 / (‖w‖ * Real.sqrt ‖w‖)) := by
      have h := sqrt_div_sq_eq_inv_mul_sqrt (t := ‖w‖) (lt_of_lt_of_le zero_lt_one hw1)
      calc Kd * (3 + C₀) * Real.sqrt ‖w‖ / ‖w‖ ^ 2
          = Kd * (3 + C₀) * (Real.sqrt ‖w‖ / ‖w‖ ^ 2) := by ring
        _ = Kd * (3 + C₀) * (1 / (‖w‖ * Real.sqrt ‖w‖)) := by rw [h]
    have hstep3 : Kd * (3 + C₀) * (1 / (‖w‖ * Real.sqrt ‖w‖))
        ≤ Kd * (3 + C₀) * (1 / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact inv_mul_sqrt_antitone (by linarith) hwnorm
    calc ‖Petal.defect f a w (Z w)‖
        ≤ Kd * (1 + Real.log ‖w‖ + ‖Z w‖) / ‖w‖ ^ 2 := hdef
      _ ≤ Kd * (3 + C₀) * Real.sqrt ‖w‖ / ‖w‖ ^ 2 := hstep1
      _ = Kd * (3 + C₀) * (1 / (‖w‖ * Real.sqrt ‖w‖)) := hstep2
      _ ≤ Kd * (3 + C₀) * (1 / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂))) := hstep3
      _ = Kd * (3 + C₀) / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂)) := by ring
  have hsum := sum_range_inv_mul_sqrt_le' hR₂pos k
  have hCnn : 0 ≤ Kd * (3 + C₀) := by
    refine mul_nonneg hKdnn ?_
    linarith [hC₀nn]
  have hsumStep : (∑ j ∈ Finset.range k,
        Kd * (3 + C₀) / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂)))
      = Kd * (3 + C₀) * (∑ j ∈ Finset.range k,
          1 / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  calc ‖Z x‖ ≤ ‖Z x - Z y‖ + ‖Z y‖ := by
        have h : Z x = (Z x - Z y) + Z y := by ring
        conv_lhs => rw [h]
        exact norm_add_le _ _
    _ = ‖∑ j ∈ Finset.range k,
            Petal.defect f a (x - (((j + 1 : ℕ)) : ℂ)) (Z (x - (((j + 1 : ℕ)) : ℂ)))‖
          + ‖Z y‖ := by rw [← htel]
    _ ≤ (∑ j ∈ Finset.range k,
            ‖Petal.defect f a (x - (((j + 1 : ℕ)) : ℂ)) (Z (x - (((j + 1 : ℕ)) : ℂ)))‖)
          + ‖Z y‖ := by
        have h := norm_sum_le (Finset.range k)
          (fun j => Petal.defect f a (x - (((j + 1 : ℕ)) : ℂ)) (Z (x - (((j + 1 : ℕ)) : ℂ))))
        linarith
    _ ≤ (∑ j ∈ Finset.range k,
            Kd * (3 + C₀) / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂)))
          + (4 + ‖1 - a‖ * K₂) := by
        have h1 := Finset.sum_le_sum hterm
        linarith [hZy_small]
    _ = Kd * (3 + C₀) * (∑ j ∈ Finset.range k,
            1 / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂)))
          + (4 + ‖1 - a‖ * K₂) := by rw [hsumStep]
    _ ≤ Kd * (3 + C₀) * (2 / Real.sqrt R₂) + (4 + ‖1 - a‖ * K₂) := by
        have h3 : Kd * (3 + C₀) * (∑ j ∈ Finset.range k,
              1 / (((j : ℝ) + 1 + R₂) * Real.sqrt ((j : ℝ) + 1 + R₂)))
            ≤ Kd * (3 + C₀) * (2 / Real.sqrt R₂) := mul_le_mul_of_nonneg_left hsum hCnn
        linarith [h3]
    _ ≤ 4 + ‖1 - a‖ * K₂ + 2 * Kd * (3 + C₀) / Real.sqrt R₂ + 1 := by
        have h4 : Kd * (3 + C₀) * (2 / Real.sqrt R₂)
            = 2 * Kd * (3 + C₀) / Real.sqrt R₂ := by ring
        linarith [h4]

end

end Work.FatouCoord.Flower

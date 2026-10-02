/-
# EL nest: the angles `bAng`, `bAng'` nest

Area `Submission/Work/ELNest/`, lemma `bAng_nest_arc`.  The level-`n` pair of the `z₁`-nest is
`Qp n = (βₙ', βₙ + 1)` with
`βₙ = α₁ - (α₁ - β₀)/1024ⁿ`, `βₙ' = α₂ + (β₀' - α₂)/1024ⁿ`,
`α₁ = 371/1023`, `α₂ = 404/1023`, `β₀ = 379859/1047552`, `β₀' = 414113/1047552`.

The two angles of the level-`(n+1)` pair (namely `β'_{n+1}` and `β_{n+1} + 1`) both lie strictly
inside the counterclockwise arc `(βₙ + 1, β'ₙ + 1)`: the arcs of the nest are nested.

Everything is elementary real arithmetic on the explicit rational data:

* `βₙ` increases with `n` and stays in `(β₀, α₁)`;
* `β'ₙ` decreases with `n` and stays in `(α₂, β₀']`;
* `α₁ < α₂` and `β₀' < 1`.

Since `βₙ > 0`, `α₁ < α₂` and `β'ₙ ≤ β₀' < 1`, the relevant fractional parts are the numbers
themselves, which turns `InArc` into two linear inequalities.
-/
import Mathlib
import Submission.Work.ELNest.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

open Work.EL

/-! ## Elementary facts about the angle data -/

/-- `1024ⁿ > 0`. -/
lemma pow1024_pos (n : ℕ) : (0 : ℝ) < (1024 : ℝ) ^ n := pow_pos (by norm_num) n

/-- `1024ⁿ ≥ 1`. -/
lemma one_le_pow1024 (n : ℕ) : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)

/-- `α₁ < α₂`. -/
lemma alpha1_lt_alpha2 : alpha1 < alpha2 := by
  rw [alpha1, alpha2]; norm_num

/-- `α₁ < 1`. -/
lemma alpha1_lt_one : alpha1 < 1 := by
  rw [alpha1]; norm_num

/-- `β₀ > 0`. -/
lemma beta0_pos : 0 < beta0 := by rw [beta0]; norm_num

/-- `β₀' < 1`. -/
lemma beta0'_lt_one : beta0' < 1 := by rw [beta0']; norm_num

/-- `α₁ - β₀ > 0`. -/
lemma d1_pos : 0 < alpha1 - beta0 := by rw [alpha1, beta0]; norm_num

/-- `β₀' - α₂ > 0`. -/
lemma d2_pos : 0 < beta0' - alpha2 := by rw [beta0', alpha2]; norm_num

/-- Dividing a nonnegative number by `1024ⁿ ≥ 1` does not increase it. -/
lemma div_pow_le (D : ℝ) (hD : 0 ≤ D) (n : ℕ) : D / (1024 : ℝ) ^ n ≤ D := by
  have h := div_le_div_of_nonneg_left hD (by norm_num : (0 : ℝ) < 1) (one_le_pow1024 n)
  simpa using h

/-- Dividing a positive number by the larger `1024ⁿ⁺¹` strictly decreases it. -/
lemma div_pow_succ_lt (D : ℝ) (hD : 0 < D) (n : ℕ) :
    D / (1024 : ℝ) ^ (n + 1) < D / (1024 : ℝ) ^ n := by
  have h : (1024 : ℝ) ^ n < (1024 : ℝ) ^ (n + 1) := by
    rw [pow_succ]; nlinarith [pow1024_pos n]
  exact div_lt_div_of_pos_left hD (pow1024_pos n) h

/-- `β₀ ≤ βₙ`: the nest angles `βₙ` approach `α₁` from above `β₀`. -/
lemma bAng_ge_beta0 (n : ℕ) : beta0 ≤ bAng n := by
  rw [bAng]
  linarith [div_pow_le (alpha1 - beta0) (le_of_lt d1_pos) n]

/-- `βₙ > 0`. -/
lemma bAng_pos (n : ℕ) : 0 < bAng n := lt_of_lt_of_le beta0_pos (bAng_ge_beta0 n)

/-- `βₙ < α₁`. -/
lemma bAng_lt_alpha1 (n : ℕ) : bAng n < alpha1 := by
  rw [bAng]
  linarith [div_pos d1_pos (pow1024_pos n)]

/-- `βₙ` is strictly increasing. -/
lemma bAng_mono (n : ℕ) : bAng n < bAng (n + 1) := by
  rw [bAng, bAng]
  linarith [div_pow_succ_lt (alpha1 - beta0) d1_pos n]

/-- `α₂ < β'ₙ`: the nest angles `β'ₙ` approach `α₂` from above. -/
lemma bAng'_gt_alpha2 (n : ℕ) : alpha2 < bAng' n := by
  rw [bAng']
  linarith [div_pos d2_pos (pow1024_pos n)]

/-- `β'ₙ ≤ β₀'`. -/
lemma bAng'_le_beta0' (n : ℕ) : bAng' n ≤ beta0' := by
  rw [bAng']
  linarith [div_pow_le (beta0' - alpha2) (le_of_lt d2_pos) n]

/-- `β'ₙ` is strictly decreasing. -/
lemma bAng'_anti (n : ℕ) : bAng' (n + 1) < bAng' n := by
  rw [bAng', bAng']
  linarith [div_pow_succ_lt (beta0' - alpha2) d2_pos n]

/-! ## The nesting of the arcs -/

/-- **The arcs of the `z₁`-nest are nested.**  Both angles of the level-`(n+1)` pair lie strictly
inside the open counterclockwise arc from the second angle `βₙ + 1` of the level-`n` pair to the
first angle `β'ₙ + 1` of the level-`n` pair. -/
theorem bAng_nest_arc (n : ℕ) :
    Work.EL.InArc (Work.ELNest.bAng' (n + 1)) (Work.ELNest.bAng n + 1)
        (Work.ELNest.bAng' n + 1) ∧
    Work.EL.InArc (Work.ELNest.bAng (n + 1) + 1) (Work.ELNest.bAng n + 1)
        (Work.ELNest.bAng' n + 1) := by
  have hAA : alpha1 < alpha2 := alpha1_lt_alpha2
  have h1c : bAng' (n + 1) < 1 := lt_of_le_of_lt (bAng'_le_beta0' (n + 1)) beta0'_lt_one
  have h1d : bAng' n < 1 := lt_of_le_of_lt (bAng'_le_beta0' n) beta0'_lt_one
  -- the first angle of the level-`n+1` pair
  have hpos1 : 0 < bAng' (n + 1) - bAng n := by
    linarith [bAng'_gt_alpha2 (n + 1), bAng_lt_alpha1 n]
  have hlt1 : bAng' (n + 1) - bAng n < bAng' n - bAng n := by linarith [bAng'_anti n]
  have hsmall1 : bAng' (n + 1) - bAng n < 1 := by linarith [bAng_pos n]
  have hfract1 : Int.fract (bAng' (n + 1) - (bAng n + 1)) = bAng' (n + 1) - bAng n := by
    rw [show bAng' (n + 1) - (bAng n + 1) = (bAng' (n + 1) - bAng n) - ((1 : ℤ) : ℝ) by
      push_cast; ring]
    rw [Int.fract_sub_intCast]
    exact Int.fract_eq_self.mpr ⟨le_of_lt hpos1, hsmall1⟩
  -- the length of the arc, i.e. `β'ₙ - βₙ`
  have hpos0 : 0 < bAng' n - bAng n := by linarith [bAng'_gt_alpha2 n, bAng_lt_alpha1 n]
  have hsmall0 : bAng' n - bAng n < 1 := by linarith [bAng_pos n]
  have hfract2 : Int.fract ((bAng' n + 1) - (bAng n + 1)) = bAng' n - bAng n := by
    rw [show (bAng' n + 1) - (bAng n + 1) = bAng' n - bAng n by ring]
    exact Int.fract_eq_self.mpr ⟨le_of_lt hpos0, hsmall0⟩
  -- the second angle of the level-`n+1` pair
  have hpos2 : 0 < bAng (n + 1) - bAng n := by linarith [bAng_mono n]
  have hsmall2 : bAng (n + 1) - bAng n < 1 := by
    have h : bAng (n + 1) < 1 := lt_trans (bAng_lt_alpha1 (n + 1)) alpha1_lt_one
    linarith [bAng_pos n]
  have hlt2 : bAng (n + 1) - bAng n < bAng' n - bAng n := by
    linarith [bAng_lt_alpha1 (n + 1), bAng'_gt_alpha2 n]
  have hfract3 : Int.fract (bAng (n + 1) + 1 - (bAng n + 1)) = bAng (n + 1) - bAng n := by
    rw [show bAng (n + 1) + 1 - (bAng n + 1) = bAng (n + 1) - bAng n by ring]
    exact Int.fract_eq_self.mpr ⟨le_of_lt hpos2, hsmall2⟩
  constructor
  · rw [Work.EL.InArc, Work.EL.arcLen, hfract1, hfract2]
    exact ⟨hpos1, hlt1⟩
  · rw [Work.EL.InArc, Work.EL.arcLen, hfract3, hfract2]
    exact ⟨hpos2, hlt2⟩

/-- **The near arcs of the `z₁`-nest are nested as sets** — the *orientation-complete* form of
NEST (T6) for consecutive levels: every angle of the near arc `(β_{n+1} + 1, β'_{n+1} + 1)` of
the level-`(n+1)` pair lies in the near arc `(βₙ + 1, β'ₙ + 1)` of the level-`n` pair.  (The two
`InArc` *membership* statements of `bAng_nest_arc` are strictly weaker: they say that the two
boundary angles of the level-`(n+1)` pair lie in the arc of the level-`n` pair, not that the
whole arc is contained.)  This is the hypothesis form consumed by the field
`Work.ELNest.NestData.nest_side`; see `Submission/Work/ELAssembly/NOTES_FALSE_nest_side.md` for
why the older two-`InArc` form of that field is not inhabitable. -/
theorem InArc_bAng_nest {n : ℕ} {θ : ℝ}
    (h : Work.EL.InArc θ (bAng (n + 1) + 1) (bAng' (n + 1) + 1)) :
    Work.EL.InArc θ (bAng n + 1) (bAng' n + 1) := by
  have hBA : 0 < bAng' (n + 1) - bAng (n + 1) :=
    sub_pos.mpr (lt_trans (lt_trans (bAng_lt_alpha1 (n + 1)) alpha1_lt_alpha2)
      (bAng'_gt_alpha2 (n + 1)))
  have hBA1 : bAng' (n + 1) - bAng (n + 1) < 1 := by
    have h1 : bAng' (n + 1) < 1 := lt_of_le_of_lt (bAng'_le_beta0' (n + 1)) beta0'_lt_one
    linarith [bAng_pos (n + 1)]
  have hA : 0 < bAng (n + 1) - bAng n := sub_pos.mpr (bAng_mono n)
  have hb : 0 < bAng' n - bAng n :=
    sub_pos.mpr (lt_trans (lt_trans (bAng_lt_alpha1 n) alpha1_lt_alpha2) (bAng'_gt_alpha2 n))
  have hb1 : bAng' n - bAng n < 1 := by
    have h1 : bAng' n < 1 := lt_of_le_of_lt (bAng'_le_beta0' n) beta0'_lt_one
    linarith [bAng_pos n]
  -- the source arc, decomposed along its witnesses
  obtain ⟨δ, k, hδ0, hδ1, hθ⟩ : ∃ δ : ℝ, ∃ k : ℤ, 0 < δ ∧
      δ < bAng' (n + 1) - bAng (n + 1) ∧ θ = (bAng (n + 1) + 1) + δ + k := by
    refine ⟨Int.fract (θ - (bAng (n + 1) + 1)), ⌊θ - (bAng (n + 1) + 1)⌋, h.1, ?_, ?_⟩
    · have hh : Int.fract (θ - (bAng (n + 1) + 1))
          < Work.EL.arcLen (bAng (n + 1) + 1) (bAng' (n + 1) + 1) := h.2
      rw [Work.EL.arcLen,
        show (bAng' (n + 1) + 1) - (bAng (n + 1) + 1)
          = bAng' (n + 1) - bAng (n + 1) by ring,
        Int.fract_eq_self.mpr ⟨le_of_lt hBA, hBA1⟩] at hh
      exact hh
    · have h' := Int.self_sub_floor (θ - (bAng (n + 1) + 1))
      linarith
  -- the source arc is contained in the target arc
  have hfr : Int.fract (θ - (bAng n + 1)) = (bAng (n + 1) - bAng n) + δ := by
    rw [hθ]
    have hrew : (bAng (n + 1) + 1) + δ + ((k : ℤ) : ℝ) - (bAng n + 1)
        = ((bAng (n + 1) - bAng n) + δ) + ((k : ℤ) : ℝ) := by ring
    rw [hrew, Int.fract_add_intCast]
    refine Int.fract_eq_self.mpr ⟨by linarith, ?_⟩
    have h3 : bAng' (n + 1) ≤ bAng' n := le_of_lt (bAng'_anti n)
    linarith [bAng_pos n]
  have hfr2 : Int.fract (bAng' n + 1 - (bAng n + 1)) = bAng' n - bAng n := by
    rw [show bAng' n + 1 - (bAng n + 1) = bAng' n - bAng n by ring,
      Int.fract_eq_self.mpr ⟨le_of_lt hb, hb1⟩]
  rw [Work.EL.InArc, Work.EL.arcLen, hfr, hfr2]
  constructor
  · linarith
  · have h3 : bAng' (n + 1) ≤ bAng' n := le_of_lt (bAng'_anti n)
    linarith

end Work.ELNest

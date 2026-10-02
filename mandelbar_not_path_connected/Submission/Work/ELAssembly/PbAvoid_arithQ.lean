import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.bAng_range
import Submission.Work.ELNest.bAng_nest_arc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## (A1): an arc lies in another arc once a lift lies inside

If `(lo, hi)` and `(p, q)` are both counterclockwise arcs of length in `(0, 1)` and the pair
`(lo, hi)` lies inside `(p, q)` *up to* an integer lift `m` (`p ≤ lo + m` and `hi + m ≤ q`), then
every angle in `(lo, hi)` lies in `(p, q)`.  The proof reduces both memberships to statements
about `Int.fract` at a common integer translate. -/
lemma arc_inArc_of_lift :
    ∀ {lo hi p q : ℝ} (m : ℤ), lo < hi → hi - lo < 1 → p < q → q - p < 1 →
      p ≤ lo + (m : ℝ) → hi + (m : ℝ) ≤ q → ∀ θ : ℝ,
        Work.EL.InArc θ lo hi → Work.EL.InArc θ p q := by
  intro lo hi p q m hlo hhi hpq hqp hp hq θ hθ
  have hAarc : Work.EL.arcLen lo hi = hi - lo := by
    rw [Work.EL.arcLen]
    exact Int.fract_eq_self.mpr ⟨le_of_lt (sub_pos.mpr hlo), hhi⟩
  have hParc : Work.EL.arcLen p q = q - p := by
    rw [Work.EL.arcLen]
    exact Int.fract_eq_self.mpr ⟨le_of_lt (sub_pos.mpr hpq), hqp⟩
  have hs1 : Int.fract (θ - lo) < hi - lo := by rw [← hAarc]; exact hθ.2
  set s : ℝ := Int.fract (θ - lo) + (lo - p + (m : ℝ)) with hs_def
  have hs0 : 0 < s := by
    rw [hs_def]
    have h : (0 : ℝ) ≤ lo - p + (m : ℝ) := by linarith
    linarith [hθ.1]
  have hslt : s < q - p := by
    rw [hs_def]
    linarith [hs1, hq]
  have hfr : Int.fract s = s := Int.fract_eq_self.mpr ⟨le_of_lt hs0, lt_trans hslt hqp⟩
  have key : θ - p - ((⌊θ - lo⌋ - m : ℤ) : ℝ) = s := by
    rw [hs_def]
    have h := Int.self_sub_floor (θ - lo)
    push_cast
    linarith
  have heq : Int.fract (θ - p) = s := by
    rw [← Int.fract_sub_intCast (θ - p) (⌊θ - lo⌋ - m), key, hfr]
  rw [Work.EL.InArc, hParc, heq]
  exact ⟨hs0, hslt⟩

/-- **(wake_lt)** All five wake arcs `Wⱼ = (wakeLo j, wakeHi j)` of the root portrait are
non-degenerate, of length `< 1`. -/
lemma wake_arc_lt (j : ℕ) :
    Work.EL.wakeLo j < Work.EL.wakeHi j ∧ Work.EL.wakeHi j - Work.EL.wakeLo j < 1 := by
  have h5 : j % 5 < 5 := Nat.mod_lt j (by norm_num)
  interval_cases h : j % 5 <;> simp [Work.EL.wakeLo, Work.EL.wakeHi, h] <;> norm_num

/-! ## The iterates `T^[j] αᵢ` of the root-portrait angles, `1 ≤ j ≤ 4` -/

lemma T1a : Work.EL.T^[1] Work.EL.alpha1 = (281 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha1, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T1b : Work.EL.T^[1] Work.EL.alpha2 = (215 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha2, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T2a : Work.EL.T^[2] Work.EL.alpha1 = (461 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha1, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T2b : Work.EL.T^[2] Work.EL.alpha2 = (593 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha2, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T3a : Work.EL.T^[3] Work.EL.alpha1 = (101 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha1, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T3b : Work.EL.T^[3] Work.EL.alpha2 = (860 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha2, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T4a : Work.EL.T^[4] Work.EL.alpha1 = (821 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha1, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]
lemma T4b : Work.EL.T^[4] Work.EL.alpha2 = (326 / 1023 : ℝ) := by
  norm_num [Work.EL.T, Work.EL.alpha2, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply]

/-! ## The fractional parts of the nest angles

`βₙ' ∈ (α₂, β₀'] ⊂ (0, 1)` and `βₙ + 1 ∈ (1, 2)`, so their `Int.fract` is the angle itself. -/

lemma bAng'_fract (n : ℕ) : Int.fract (Work.ELNest.bAng' n) = Work.ELNest.bAng' n := by
  refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
  · exact le_of_lt (lt_trans (by norm_num [Work.ELNest.alpha2]) (Work.ELNest.bAng'_gt_alpha2 n))
  · exact lt_of_le_of_lt (Work.ELNest.bAng'_le_beta0' n) Work.ELNest.beta0'_lt_one

lemma bAng_shift_fract (n : ℕ) : Int.fract (Work.ELNest.bAng n + 1) = Work.ELNest.bAng n := by
  have hpos : 0 < Work.ELNest.bAng n := Work.ELNest.bAng_pos n
  have hlt : Work.ELNest.bAng n < 1 :=
    lt_trans (Work.ELNest.bAng_lt_alpha1 n) (by norm_num [Work.ELNest.alpha1])
  have h1 : Int.fract (Work.ELNest.bAng n + 1)
      = Int.fract (Work.ELNest.bAng n + ((1 : ℤ) : ℝ)) := by norm_num
  rw [h1, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt⟩

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The rational arithmetic of `hcvQ`** (`NOTES_LEAD_mandelbar_pbavoid.md` §3.4, "(A1), wake_lt,
beta0_le_bAng, Q-W, Q-ND"), bundled as one conjunction because the pieces are used together:
(A1) an arc lies in another arc once a lift lies inside (both of length in `(0,1)`);
(wake_lt) the five wake arcs are non-degenerate; (β₀ ≤ βₙ) the lower level-`n` nest angle stays
above `β₀`; (Q-W) each wake arc `W_j`, `j = 1..4`, lies in the far arc `(β'ₙ, βₙ + 1)` of the
level-`n` pair `Qp n` (lifts `m = 1,0,0,0`); (Q-ND) neither angle of `Qp n` has a fractional part
equal to `T^j α₁` or `T^j α₂`, `j = 1..4`.  All are `linarith`/`norm_num` on the closed forms
`bAng n = α₁ - (α₁-β₀)/1024ⁿ`, `bAng' n = α₂ + (β₀'-α₂)/1024ⁿ` and `bAng_range`
(`βₙ ∈ (0, α₁)`, `β'ₙ ∈ (α₂, β₀']`); `T^[j] αᵢ` is evaluated by `norm_num` for the concrete
`j ≤ 4` (`T θ = Int.fract (-2θ)`), giving `T^[1] α₁ = 281/1023`, `T^[1] α₂ = 215/1023`,
`T^[2] α₁ = 461/1023`, `T^[2] α₂ = 593/1023`, `T^[3] α₁ = 101/1023`, `T^[3] α₂ = 860/1023`,
`T^[4] α₁ = 821/1023`, `T^[4] α₂ = 326/1023`. -/
theorem PbAvoid_arithQ :
    (∀ {lo hi p q : ℝ} (m : ℤ), lo < hi → hi - lo < 1 → p < q → q - p < 1 →
      p ≤ lo + (m : ℝ) → hi + (m : ℝ) ≤ q → ∀ θ : ℝ,
        Work.EL.InArc θ lo hi → Work.EL.InArc θ p q) ∧
    (∀ j : ℕ, Work.EL.wakeLo j < Work.EL.wakeHi j ∧ Work.EL.wakeHi j - Work.EL.wakeLo j < 1) ∧
    (∀ n : ℕ, Work.ELNest.beta0 ≤ Work.ELNest.bAng n) ∧
    (∀ n j : ℕ, 1 ≤ j → j < 5 → ∀ θ : ℝ,
      Work.EL.InArc θ (Work.EL.wakeLo j) (Work.EL.wakeHi j) →
        Work.EL.InArc θ (Work.ELNest.bAng' n) (Work.ELNest.bAng n + 1)) ∧
    (∀ n j : ℕ, 1 ≤ j → j < 5 →
      (Int.fract (Work.ELNest.bAng' n) ≠ (Work.EL.T^[j] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.bAng' n) ≠ (Work.EL.T^[j] Work.EL.alpha2)) ∧
      (Int.fract (Work.ELNest.bAng n + 1) ≠ (Work.EL.T^[j] Work.EL.alpha1) ∧
        Int.fract (Work.ELNest.bAng n + 1) ≠ (Work.EL.T^[j] Work.EL.alpha2))) := by
  refine ⟨arc_inArc_of_lift, wake_arc_lt, ?_, ?_, ?_⟩
  · intro n
    exact Work.ELNest.bAng_ge_beta0 n
  · -- (Q-W)
    intro n j hj1 hj5 θ hθ
    have hb2 := Work.ELNest.bAng_ge_beta0 n
    have hb3 := Work.ELNest.bAng'_gt_alpha2 n
    have hb4 := Work.ELNest.bAng'_le_beta0' n
    have hbpos := Work.ELNest.bAng_pos n
    have ha2b : Work.ELNest.alpha1 < Work.ELNest.alpha2 := Work.ELNest.alpha1_lt_alpha2
    have hb0'1 : Work.ELNest.beta0' < 1 := Work.ELNest.beta0'_lt_one
    have hbp1 : Work.ELNest.bAng' n < 1 := lt_of_le_of_lt hb4 hb0'1
    have hpq : Work.ELNest.bAng' n < Work.ELNest.bAng n + 1 := by linarith
    have hb1 := Work.ELNest.bAng_lt_alpha1 n
    have hqp : Work.ELNest.bAng n + 1 - Work.ELNest.bAng' n < 1 := by linarith
    have e1 : (281 / 1023 : ℝ) ≤ Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    have e2 : (326 / 1023 : ℝ) ≤ Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    have e3 : (101 / 1023 : ℝ) ≤ Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    have e4 : Work.ELNest.beta0' ≤ (461 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    have e5 : Work.ELNest.beta0' ≤ (860 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    have e6 : Work.ELNest.beta0' ≤ (821 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    interval_cases j
    · simp only [Work.EL.wakeLo, Work.EL.wakeHi] at hθ
      exact arc_inArc_of_lift (1 : ℤ) (by norm_num) (by norm_num) hpq hqp
        (by linarith) (by linarith) θ hθ
    · simp only [Work.EL.wakeLo, Work.EL.wakeHi] at hθ
      exact arc_inArc_of_lift (0 : ℤ) (by norm_num) (by norm_num) hpq hqp
        (by linarith) (by linarith) θ hθ
    · simp only [Work.EL.wakeLo, Work.EL.wakeHi] at hθ
      exact arc_inArc_of_lift (0 : ℤ) (by norm_num) (by norm_num) hpq hqp
        (by linarith) (by linarith) θ hθ
    · simp only [Work.EL.wakeLo, Work.EL.wakeHi] at hθ
      exact arc_inArc_of_lift (0 : ℤ) (by norm_num) (by norm_num) hpq hqp
        (by linarith) (by linarith) θ hθ
  · -- (Q-ND)
    intro n j hj1 hj5
    rw [bAng'_fract, bAng_shift_fract]
    have hb1 := Work.ELNest.bAng_lt_alpha1 n
    have hb2 := Work.ELNest.bAng_ge_beta0 n
    have hb3 := Work.ELNest.bAng'_gt_alpha2 n
    have hb4 := Work.ELNest.bAng'_le_beta0' n
    have n1 : (281 / 1023 : ℝ) ≤ Work.ELNest.alpha2 := by norm_num [Work.ELNest.alpha2]
    have n2 : (215 / 1023 : ℝ) ≤ Work.ELNest.alpha2 := by norm_num [Work.ELNest.alpha2]
    have n3 : Work.ELNest.beta0' < (461 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    have n4 : Work.ELNest.beta0' < (593 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    have n5 : (101 / 1023 : ℝ) ≤ Work.ELNest.alpha2 := by norm_num [Work.ELNest.alpha2]
    have n6 : Work.ELNest.beta0' < (860 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    have n7 : Work.ELNest.beta0' < (821 / 1023 : ℝ) := by norm_num [Work.ELNest.beta0']
    have n8 : (326 / 1023 : ℝ) ≤ Work.ELNest.alpha2 := by norm_num [Work.ELNest.alpha2]
    have m1 : (281 / 1023 : ℝ) < Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    have m2 : (215 / 1023 : ℝ) < Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    have m3 : Work.ELNest.alpha1 < (461 / 1023 : ℝ) := by norm_num [Work.ELNest.alpha1]
    have m4 : Work.ELNest.alpha1 < (593 / 1023 : ℝ) := by norm_num [Work.ELNest.alpha1]
    have m5 : (101 / 1023 : ℝ) < Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    have m6 : Work.ELNest.alpha1 < (860 / 1023 : ℝ) := by norm_num [Work.ELNest.alpha1]
    have m7 : Work.ELNest.alpha1 < (821 / 1023 : ℝ) := by norm_num [Work.ELNest.alpha1]
    have m8 : (326 / 1023 : ℝ) < Work.ELNest.beta0 := by norm_num [Work.ELNest.beta0]
    interval_cases j <;>
      simp only [T1a, T1b, T2a, T2b, T3a, T3b, T4a, T4b] <;>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h <;>
      linarith [hb1, hb2, hb3, hb4, n1, n2, n3, n4, n5, n6, n7, n8,
        m1, m2, m3, m4, m5, m6, m7, m8]

end Work.ELAssembly

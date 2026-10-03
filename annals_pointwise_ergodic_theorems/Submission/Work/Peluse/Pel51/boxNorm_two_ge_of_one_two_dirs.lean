import Mathlib
import Submission.Work.Peluse.LadderA.levelRaiseAppendBd
import Submission.Work.Peluse.BoxNorm.boxNorm_pow
import Submission.Work.Peluse.Ulower.Defs
import Submission.Work.Peluse.Pel51.boxNormPow_card_mul_eq
import Submission.Work.Peluse.LadderA.rpowLevelRaise

/-!
# The level raise `□¹_Q → □²_(Q,R)` with a bounded second direction

`Work.Peluse.LadderA.levelRaiseAppendBd` raises the box norm from level `1` to level `2` by
appending one direction, but it requires the appended direction set to lie in `[-N,N]` — the same
window over which the norm is taken — because the Gowers–Cauchy–Schwarz step it iterates shifts
the argument of `f` by elements of that direction set.

The target of this file removes that restriction in the only way available: the appended direction
`R` is allowed to be as large as `Cw·N`, at the cost of taking the level-`2` norm over the enlarged
window `symIcc (Cw·N)` — which is the *same* enlargement for the level-`1` factor, and the two
cancel because the support window enters `boxNormPow` only through the normalising factor `|S|⁻¹`
(`Work.Peluse.Pel51.boxNormPow_card_mul_eq`).  Concretely, with `r = |symIcc N| / |symIcc (Cw·N)|`,

* the level raise over `symIcc (Cw·N)` reads `(1/2)·(r·a)² ≤ r·b`, where `a`, `b` are the level-`1`
  and level-`2` box-norm powers over `symIcc N`;
* dividing by `r` gives `(r/2)·a² ≤ b`, and since `r ≥ 1/(2·Cw)` (i.e. `|symIcc N| ≥ |symIcc (Cw·N)|/(2·Cw)`,
  the elementary cardinality estimate) this yields `(1/(4·Cw))·a² ≤ b`;
* taking `2²`-nd roots (`Work.Peluse.LadderA.rpowLevelRaise`) and identifying the roots with the
  box *norms* gives the claim.

## Main results

* `Work.Peluse.Pel51.boxNorm_two_ge_of_one_two_dirs`: the statement above.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

/-- `symIcc` is nonempty (it contains `0`). -/
lemma symIcc_nonempty' (N : ℕ) : (symIcc N).Nonempty := ⟨0, by simp [symIcc]⟩

/-- The cardinality of the symmetric interval: `|symIcc N| = 2N + 1`. -/
lemma card_symIcc' (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]; omega

/-- **The exact window ratio for the box-norm power.**  Changing the support window from `symIcc M`
to `symIcc N` multiplies `boxNormPow` by exactly `|symIcc N| / |symIcc M|`: the window enters
`prodCubeSum` only as the normalising factor `|S|⁻¹`. -/
lemma boxNormPow_symIcc_ratio {t : ℕ} (Q : Fin t → Finset ℤ) (N M : ℕ) (f : ℤ → ℂ) :
    boxNormPow t Q (symIcc M) f
      = ((symIcc N).card : ℝ) / ((symIcc M).card : ℝ) * boxNormPow t Q (symIcc N) f := by
  have h := boxNormPow_card_mul_eq Q (symIcc_nonempty' M) (symIcc_nonempty' N) f
  have hM : ((symIcc M).card : ℝ) ≠ 0 := by
    have := Finset.card_ne_zero.mpr (symIcc_nonempty' M); exact_mod_cast this
  rw [div_mul_eq_mul_div, eq_div_iff hM]
  rw [mul_comm (boxNormPow t Q (symIcc M) f)]
  exact h

/-- **The elementary cardinality estimate.**  For `1 ≤ Cw` the ratio `|symIcc N| / |symIcc (Cw·N)|`
dominates `1/(2·Cw)`; equivalently `1/(4·Cw) ≤ (|symIcc N| / |symIcc (Cw·N)|)/2`.  Both
cardinalities are `2L+1`, so this is `4·Cw·(2N+1) ≥ 2·(2·Cw·N+1)`. -/
lemma inv_four_mul_le_ratio (Cw N : ℕ) (hCw : 1 ≤ Cw) :
    (1 : ℝ) / (4 * (Cw : ℝ))
      ≤ (((symIcc N).card : ℝ) / ((symIcc (Cw * N)).card : ℝ)) / 2 := by
  rw [card_symIcc', card_symIcc']
  push_cast
  have hCw1 : (1:ℝ) ≤ (Cw:ℝ) := by exact_mod_cast hCw
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hCw0 : (0:ℝ) < (Cw:ℝ) := by linarith
  have hprod : (0:ℝ) ≤ (Cw:ℝ) * (N:ℝ) := mul_nonneg hCw0.le hN0
  have hd1 : (4 * (Cw:ℝ)) ≠ 0 := by positivity
  have hd2 : (2 * ((Cw:ℝ) * (N:ℝ)) + 1) ≠ 0 := by positivity
  have hd3 : (2:ℝ) ≠ 0 := by norm_num
  field_simp
  nlinarith [hCw1, hN0, hprod]

theorem boxNorm_two_ge_of_one_two_dirs (Cw : ℕ) (hCw : 1 ≤ Cw) {Q R : Finset ℤ}
    (hQ : Q.Nonempty) (hR : R.Nonempty) {N : ℕ} (hN : 1 ≤ N)
    (hbd : ∀ z : ℤ, z ∈ R → |z| ≤ ((Cw * N : ℕ) : ℤ)) {f : ℤ → ℂ}
    (hsup : Work.Peluse.SupportIn f N) :
    ((1 : ℝ) / (4 * (Cw : ℝ))) ^ (1 / 4 : ℝ)
        * Work.Peluse.boxNorm 1 (fun _ : Fin 1 => Q) (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNorm 2 (fun i : Fin 2 => if i = 0 then Q else R) (Work.Peluse.symIcc N) f
    := by
  classical
  have hNpos : 0 < Cw * N := Nat.mul_pos (by omega) (by omega)
  -- `f` vanishes off the enlarged window `symIcc (Cw * N)`
  have hsupM : ∀ x : ℤ, x ∉ symIcc (Cw * N) → f x = 0 := by
    intro x hx
    apply hsup
    by_contra hcon
    rw [not_lt] at hcon
    refine hx ?_
    rw [symIcc, Finset.mem_Icc]
    have h1 : x.natAbs ≤ Cw * N := le_trans hcon (Nat.le_mul_of_pos_left N (by omega))
    have h2 : (x.natAbs : ℤ) ≤ ((Cw * N : ℕ) : ℤ) := by exact_mod_cast h1
    exact abs_le.mp (by rwa [Int.abs_eq_natAbs])
  -- the level raise over the enlarged window
  have hlev := Work.Peluse.LadderA.levelRaiseAppendBd (a := 1) (b := 1) (N := Cw * N)
      hNpos (fun _ : Fin 1 => Q) (fun _ : Fin 1 => R) f (fun _ => hQ) (fun _ => hR)
      (fun _ z hz => hbd z hz) hsupM
  have happ : (Fin.append (fun _ : Fin 1 => Q) (fun _ : Fin 1 => R))
      = fun i : Fin 2 => if i = 0 then Q else R := by
    funext i; fin_cases i <;> simp [Fin.append] <;> rfl
  rw [happ] at hlev
  have hlev' : (1/2:ℝ) * (boxNormPow 1 (fun _ : Fin 1 => Q) (symIcc (Cw*N)) f)^2
      ≤ boxNormPow 2 (fun i : Fin 2 => if i = 0 then Q else R) (symIcc (Cw*N)) f := by
    simpa using hlev
  -- the level-`1` and level-`2` quantities over the original window `symIcc N`
  set a : ℝ := boxNormPow 1 (fun _ : Fin 1 => Q) (symIcc N) f with ha
  set b : ℝ := boxNormPow 2 (fun i : Fin 2 => if i = 0 then Q else R) (symIcc N) f with hb
  set r : ℝ := ((symIcc N).card : ℝ) / ((symIcc (Cw*N)).card : ℝ) with hrdef
  have ha0 : 0 ≤ a := by rw [ha, boxNormPow]; exact norm_nonneg _
  have hrpos : 0 < r := by
    rw [hrdef]
    exact div_pos (by exact_mod_cast Finset.card_pos.mpr (symIcc_nonempty' N))
      (by exact_mod_cast Finset.card_pos.mpr (symIcc_nonempty' (Cw*N)))
  have hratio1 : boxNormPow 1 (fun _ : Fin 1 => Q) (symIcc (Cw*N)) f = r * a := by
    rw [boxNormPow_symIcc_ratio (fun _ : Fin 1 => Q) N (Cw*N) f, hrdef, ha]
  have hratio2 :
      boxNormPow 2 (fun i : Fin 2 => if i = 0 then Q else R) (symIcc (Cw*N)) f = r * b := by
    rw [boxNormPow_symIcc_ratio (fun i : Fin 2 => if i = 0 then Q else R) N (Cw*N) f,
      hrdef, hb]
  rw [hratio1, hratio2] at hlev'
  -- divide off the common window factor `r`
  have hra : (r/2) * a^2 ≤ b := by
    have heq : (1/2:ℝ) * (r*a)^2 = r * ((r/2)*a^2) := by ring
    rw [heq] at hlev'
    exact le_of_mul_le_mul_left hlev' hrpos
  have hconst : (1:ℝ)/(4*(Cw:ℝ)) ≤ r/2 := by
    rw [hrdef]; exact inv_four_mul_le_ratio Cw N hCw
  have hmain : (1/(4*(Cw:ℝ))) * a^2 ≤ b := by
    have h := mul_le_mul_of_nonneg_right hconst (sq_nonneg a)
    linarith [h, hra]
  have hc0 : (0:ℝ) ≤ 1/(4*(Cw:ℝ)) := by
    have : (0:ℝ) < (Cw:ℝ) := by exact_mod_cast (by omega : 0 < Cw)
    positivity
  -- take the `4`-th roots
  have hgoal := Work.Peluse.LadderA.rpowLevelRaise (X := a) (Y := b) (c := 1/(4*(Cw:ℝ)))
      (mm := 1) (tt := 1) (β := 2) ha0 hc0 (by norm_num) hmain
  have hgoal' : ((1:ℝ)/(4*(Cw:ℝ)))^(1/4:ℝ) * a^(1/2:ℝ) ≤ b^(1/4:ℝ) := by
    convert hgoal using 2 <;> norm_num
  have hbox1 : boxNorm 1 (fun _ : Fin 1 => Q) (symIcc N) f = a^(1/2:ℝ) := by
    rw [Work.Peluse.boxNorm, ha]; norm_num
  have hbox2 : boxNorm 2 (fun i : Fin 2 => if i = 0 then Q else R) (symIcc N) f = b^(1/4:ℝ) := by
    rw [Work.Peluse.boxNorm, hb]; norm_num
  rw [hbox1, hbox2]
  exact hgoal'

end Work.Peluse.Pel51

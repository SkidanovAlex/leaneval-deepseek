import Mathlib
import Submission.Work.Landing.Core
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A bounded window of the second-iterate orbit bounds the whole orbit

`Tsq c = T_c ∘ T_c` is the holomorphic second iterate of the antiholomorphic
quadratic `T_c(z) = z̄² + c`, and `orbit c w n = T_c^[n] w`.

The lemma `boundedOrbit_of_ball` says that if the orbit of `w` under
`(Tsq c)^[k]` (that is, the subsequence of `T_c`-iterates with indices
multiples of `2k`) stays inside one ball, then the whole `T_c`-orbit of `w` is
bounded.  The gap between two consecutive known indices is `2k`, and each of
the skipped points is obtained from a known one by applying `T_c` at most
`2k - 1` times; since `‖T_c x‖ ≤ ‖x‖² + ‖c‖`, the orbit cannot escape.

Nothing here needs `r` to be positive or `w` to be special.
-/

namespace Work.LandLeaves

open Function
open Work.ParamRays (orbit BoundedOrbit)
open LeanEval.ComplexAnalysis (Tantibar)

/-- `Tsq c` is the second iterate of `T_c`: `Tsq c = T_c ∘ T_c`. -/
theorem Tsq_eq_comp (c : ℂ) : Work.Landing.Tsq c = Tantibar c ∘ Tantibar c := by
  funext z
  simp [Work.Landing.Tsq_apply, Tantibar]

/-- `Tsq c` is the second iterate of `T_c`, as an iterate. -/
theorem Tsq_eq_iterate_two (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq_apply, Tantibar, Function.iterate_succ_apply']

/-- Iterating `Tsq c` `k` then `m` times is iterating `T_c` `2 * k * m` times. -/
theorem iterate_tsq (c : ℂ) (k m : ℕ) :
    ((Work.Landing.Tsq c)^[k])^[m] = (Tantibar c)^[2 * k * m] := by
  rw [Tsq_eq_iterate_two, ← Function.iterate_mul, ← Function.iterate_mul]
  congr 1
  ring

/-- The `2 * k * m`-th `T_c`-iterate of `w` is the `m`-th `(Tsq c)^[k]`-iterate of `w`. -/
theorem orbit_eq_iterate_tsq (c w : ℂ) (k m : ℕ) :
    orbit c w (2 * k * m) = ((Work.Landing.Tsq c)^[k])^[m] w := by
  show (Tantibar c)^[2 * k * m] w = ((Work.Landing.Tsq c)^[k])^[m] w
  rw [iterate_tsq]

/-! ## The a-priori bound sequence

`boundConst c b` is the sequence `b, max b (b² + ‖c‖), …`: the `n`-th term
bounds `‖T_c^[n] x‖` once `‖x‖ ≤ b`. -/

/-- The bound sequence: `boundConst c b 0 = b` and
`boundConst c b (n+1) = max (boundConst c b n) ((boundConst c b n)² + ‖c‖)`,
so that `‖x‖ ≤ b` implies `‖T_c^[n] x‖ ≤ boundConst c b n`. -/
noncomputable def boundConst (c : ℂ) (b : ℝ) : ℕ → ℝ
  | 0 => b
  | n + 1 => max (boundConst c b n) ((boundConst c b n) ^ 2 + ‖c‖)

@[simp] theorem boundConst_zero (c : ℂ) (b : ℝ) : boundConst c b 0 = b := rfl

@[simp] theorem boundConst_succ (c : ℂ) (b : ℝ) (n : ℕ) :
    boundConst c b (n + 1) = max (boundConst c b n) ((boundConst c b n) ^ 2 + ‖c‖) := rfl

theorem boundConst_mono (c : ℂ) (b : ℝ) : Monotone (boundConst c b) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

/-- Applying `T_c` `n` times maps the ball of radius `b` into `boundConst c b n`. -/
theorem norm_orbit_le_boundConst_of_le {c x : ℂ} {b : ℝ} (hx : ‖x‖ ≤ b) (n : ℕ) :
    ‖(Tantibar c)^[n] x‖ ≤ boundConst c b n := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc ‖Tantibar c ((Tantibar c)^[n] x)‖
        ≤ ‖(Tantibar c)^[n] x‖ ^ 2 + ‖c‖ := Work.ParamRays.norm_Tantibar_le c _
      _ ≤ (boundConst c b n) ^ 2 + ‖c‖ := by
          have h1 : 0 ≤ ‖(Tantibar c)^[n] x‖ := norm_nonneg _
          have h2 := pow_le_pow_left₀ h1 ih 2
          linarith
      _ ≤ boundConst c b (n + 1) := le_max_right _ _

/-- The main estimate: every `T_c`-iterate of `w` at an index of the form
`2 * k * m + j` is bounded by `boundConst c (‖z‖ + r) j`, provided the
`(Tsq c)^[k]`-orbit of `w` stays within distance `r` of `z`. -/
theorem norm_orbit_le_boundConst {c z : ℂ} {k : ℕ} {r : ℝ} {w : ℂ}
    (hball : ∀ m : ℕ, ‖((Work.Landing.Tsq c)^[k])^[m] w - z‖ < r) (m j : ℕ) :
    ‖orbit c w (2 * k * m + j)‖ ≤ boundConst c (‖z‖ + r) j := by
  induction j with
  | zero =>
    have h1 : ‖((Work.Landing.Tsq c)^[k])^[m] w - z‖ < r := hball m
    have h2 : ‖((Work.Landing.Tsq c)^[k])^[m] w - z + z‖ ≤
        ‖((Work.Landing.Tsq c)^[k])^[m] w - z‖ + ‖z‖ := norm_add_le _ _
    rw [sub_add_cancel] at h2
    have h3 : ‖((Work.Landing.Tsq c)^[k])^[m] w‖ ≤ ‖z‖ + r := by linarith
    rw [Nat.add_zero, show boundConst c (‖z‖ + r) 0 = ‖z‖ + r from rfl]
    simpa only [orbit, iterate_tsq] using h3
  | succ j ih =>
    have hidx : 2 * k * m + (j + 1) = (2 * k * m + j) + 1 := (Nat.add_assoc _ _ _).symm
    rw [hidx, Work.ParamRays.orbit_succ]
    calc ‖Tantibar c (orbit c w (2 * k * m + j))‖
        ≤ ‖orbit c w (2 * k * m + j)‖ ^ 2 + ‖c‖ := Work.ParamRays.norm_Tantibar_le c _
      _ ≤ (boundConst c (‖z‖ + r) j) ^ 2 + ‖c‖ := by
          have h1 : 0 ≤ ‖orbit c w (2 * k * m + j)‖ := norm_nonneg _
          have h2 := pow_le_pow_left₀ h1 ih 2
          linarith
      _ ≤ boundConst c (‖z‖ + r) (j + 1) := le_max_right _ _

/-- If the orbit of `w` under `(Tsq c)^[k]` is contained in a ball, then the
whole `T_c`-orbit of `w` is bounded. -/
theorem boundedOrbit_of_ball {c z : ℂ} {k : ℕ} (hk : 0 < k) {r : ℝ} {w : ℂ}
    (hball : ∀ m : ℕ, ‖((Work.Landing.Tsq c)^[k])^[m] w - z‖ < r) :
    Work.ParamRays.BoundedOrbit c w := by
  refine ⟨boundConst c (‖z‖ + r) (2 * k), fun n => ?_⟩
  have h2k : 0 < 2 * k := by omega
  have hmod : n % (2 * k) < 2 * k := Nat.mod_lt n h2k
  have hidx : 2 * k * (n / (2 * k)) + n % (2 * k) = n := Nat.div_add_mod n (2 * k)
  have hb := norm_orbit_le_boundConst hball (n / (2 * k)) (n % (2 * k))
  rw [hidx] at hb
  exact le_trans hb (boundConst_mono c (‖z‖ + r) (by omega))

end Work.LandLeaves

import Mathlib
import Submission.Work.Escape.Shadow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The shadow iterates are asymptotically monic: `shadowTd (k+1) z ≈ (shadowTd k z)^d`

The holomorphic shadows `shadowTd d c k` of the iterates of the antipolynomial
`Td d c : z ↦ z̄^d + c` satisfy two structural identities, valid for **every** `k`:

* `‖shadowTd d c k z‖ = ‖(Td d c)^[k] z‖` (`shadowTd_norm_iterate`): a shadow has the same
  modulus as the corresponding iterate of the antipolynomial;
* `‖shadowTd d c (k+1) z - (shadowTd d c k z)^d‖ = ‖c‖` (`shadowTd_step_norm`): one shadow
  iterate is the `d`-th power of the previous one up to an error of constant size `‖c‖`.

Together these give the main estimate `shadowTd_ratio_tendsto`: on orbits that are large enough,
the ratio `shadowTd (k+1) z / (shadowTd k z)^d` is arbitrarily close to `1`, uniformly in `k`.
This is the "asymptotically monic / Böttcher" estimate for the shadow family; it is the input that
makes the pull-backs of `log ‖shadowTd k ·‖` converge.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-- A holomorphic shadow has the same modulus as the corresponding iterate of the antipolynomial:
`‖shadowTd d c k z‖ = ‖(Td d c)^[k] z‖`.

(`shadowTd d c 0 = id`, `shadowTd d c 1 = fTd d c = conj ∘ Td d c`, and
`shadowTd d c (n+2) = shadowTd d c n ∘ pTd d c` with `pTd d c = Td d c ∘ Td d c`; each of the two
types of steps preserves the modulus, and `pTd` realizes two steps of `Td`.) -/
theorem shadowTd_norm_iterate (d : ℕ) (c : ℂ) :
    ∀ k : ℕ, ∀ z : ℂ, ‖shadowTd d c k z‖ = ‖(Td d c)^[k] z‖ := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro z; simp
  | one => intro z; rw [shadowTd_one, Function.iterate_one, fTd_apply, Complex.norm_conj]
  | more n _ih1 _ih2 =>
      intro z
      rw [shadowTd_add_two, Function.comp_apply, _ih1]
      have hp : pTd d c z = (Td d c)^[2] z := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
        exact pTd_apply d c z
      rw [hp, ← Function.iterate_add_apply]

/-- Consecutive shadows differ from a `d`-th power by the parameter: for every `k` and `z`,
`‖shadowTd d c (k+1) z - (shadowTd d c k z)^d‖ = ‖c‖`.

Indeed, for even `k = 2j` the difference equals `conj c`, and for odd `k = 2j+1` it equals `c`;
the statement is parity-free because both alternatives have modulus `‖c‖`. -/
theorem shadowTd_step_norm (d : ℕ) (c : ℂ) :
    ∀ k : ℕ, ∀ z : ℂ, ‖shadowTd d c (k + 1) z - (shadowTd d c k z) ^ d‖ = ‖c‖ := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro z
      have : shadowTd d c (0 + 1) z - (shadowTd d c 0 z) ^ d = (starRingEnd ℂ) c := by
        simp [fTd]
      rw [this, Complex.norm_conj]
  | one =>
      intro z
      have h1 : shadowTd d c (1 + 1) z = pTd d c z := by
        rw [show 1 + 1 = 0 + 2 from by norm_num, shadowTd_add_two (n := 0)]
        rfl
      rw [h1]
      have : pTd d c z - (shadowTd d c 1 z) ^ d = c := by
        simp [pTd, fTd]
      rw [this]
  | more n ih1 _ih2 =>
      intro z
      have h1 : shadowTd d c (n + 2 + 1) z = shadowTd d c (n + 1) (pTd d c z) := by
        rw [show n + 2 + 1 = (n + 1) + 2 from by ring, shadowTd_add_two, Function.comp_apply]
      have h2 : shadowTd d c (n + 2) z = shadowTd d c n (pTd d c z) := by
        rw [shadowTd_add_two, Function.comp_apply]
      rw [h1, h2]
      exact ih1 (pTd d c z)

/-- **The shadow ratios tend to `1` uniformly on large orbits.**

For every `ε > 0` there is a radius `ρ` such that whenever the `k`-th iterate of the antipolynomial
`Td d c` (with `1 ≤ d`) at `z` has modulus at least `ρ`, the ratio of consecutive shadows satisfies
`‖shadowTd d c (k+1) z / (shadowTd d c k z)^d - 1‖ ≤ ε`. -/
theorem shadowTd_ratio_tendsto (d : ℕ) (c : ℂ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, ∀ k : ℕ, ∀ z : ℂ, ρ ≤ ‖(Td d c)^[k] z‖ →
      ‖shadowTd d c (k + 1) z / (shadowTd d c k z) ^ d - 1‖ ≤ ε := by
  refine ⟨max 1 (‖c‖ / ε + 1), fun k z hz => ?_⟩
  -- The radius is at least `1`, so `‖shadowTd d c k z‖ ≥ 1 > 0`.
  have hρ1 : (1 : ℝ) ≤ max 1 (‖c‖ / ε + 1) := le_max_left _ _
  have hSk : max 1 (‖c‖ / ε + 1) ≤ ‖shadowTd d c k z‖ := by
    rw [shadowTd_norm_iterate]; exact hz
  have hSpos : 0 < ‖shadowTd d c k z‖ := lt_of_lt_of_le one_pos (le_trans hρ1 hSk)
  have hSne : shadowTd d c k z ≠ 0 := norm_pos_iff.mp hSpos
  have hpow_ne : (shadowTd d c k z) ^ d ≠ 0 := pow_ne_zero d hSne
  -- Rewrite the ratio using the constant-size error of a single shadow step.
  have hkey : shadowTd d c (k + 1) z / (shadowTd d c k z) ^ d - 1
      = (shadowTd d c (k + 1) z - (shadowTd d c k z) ^ d) / (shadowTd d c k z) ^ d := by
    rw [sub_div, div_self hpow_ne]
  rw [hkey, norm_div, shadowTd_step_norm, norm_pow]
  -- Reduce to `‖c‖ ≤ ε * ‖shadowTd d c k z‖^d`.
  rw [div_le_iff₀ (pow_pos hSpos d)]
  calc ‖c‖ = ε * (‖c‖ / ε) := by field_simp
    _ ≤ ε * ‖shadowTd d c k z‖ ^ d := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        calc ‖c‖ / ε ≤ max 1 (‖c‖ / ε + 1) := le_trans (by linarith) (le_max_right _ _)
          _ ≤ (max 1 (‖c‖ / ε + 1)) ^ d := le_self_pow₀ (le_max_left _ _) (by omega)
          _ ≤ ‖shadowTd d c k z‖ ^ d :=
              pow_le_pow_left₀ (le_trans (by norm_num) hρ1) hSk d

end Work.Escape

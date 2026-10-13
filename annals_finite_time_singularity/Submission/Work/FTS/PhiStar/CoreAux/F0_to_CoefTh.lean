/-
# `FTS/PhiStar/CoreAux/F0_to_CoefTh.lean` — the flat class `F0` bounds the angular
coefficient norm `CoefTh`

`Work.FTS.VocabO.CoefTh n f` is the sum of the open-quadrant suprema of the mixed
derivatives `D_z^b D_θ^i (∂_θ f)` with `b + i ≤ n` (the "angular coefficient norm" of the
transport clauses), and `CoefThMem n f` is the corresponding *membership* statement (each
slot is bounded).  This file shows that both are implied by the flat class

`F0 n K (∂_θ f)`  —  `|(z+1)^k ∂_z^k D_θ^i(∂_θ f)| ≤ K` on the open quadrant for `k + i ≤ n`.

**The mathematics.**  The only thing that has to be converted is the radial operator:
`F0` controls the plain iterates `∂_z^k` with the weight `(z+1)^k`, while `CoefTh` uses the
curvilinear `D_z = z ∂_z`.  The bridge is the first-order product rule

`∂_z^k (z · ∂_z g) = z · ∂_z^{k+1} g + k · ∂_z^k g`   (`pzIter_zpz_expand`),

which is proved once and for all in `CoreAux/F0_zpz.lean` (it needs only the interior
smoothness `SmoothOpen g`, through `SmoothOpen.hasDerivAt_slice_pzIter`).  Iterating it `b`
times shows that `D_z^b g` is again controlled by the same flat data, with a constant
`((m+1)^b)` (the loss is the sum `K + m K ≤ (m+1)K` at every step).

Concretely:

* `RadB m K g` is the *radial* half of the flat class: `|(z+1)^k ∂_z^k g| ≤ K` for `k ≤ m`;
* `RadB_DzIter` : `RadB m K g  →  RadB (m-b) (((m+1)^b)K) (D_z^b g)` for `b ≤ m`;
* `F0 n K (∂_θ f)` gives `RadB (n-i) K (D_θ^i (∂_θ f))` immediately (apply the hypothesis at
  `k + i ≤ n`), so `|D_z^b D_θ^i (∂_θ f)| ≤ (n+1)^n K` for `b + i ≤ n`, which is `CoefThMem`
  and bounds each of the `(n+1)^2` terms of `CoefTh`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The radial half of the flat class -/

/-- **The radial flat class on the open quadrant**: `|(z+1)^k ∂_z^k g| ≤ K` for `k ≤ m`
and all `(z,θ) ∈ (0,∞) × (0,π/2)`.  This is `Work.FTS.PhiStar.F0` with the angular slot
forgotten. -/
def RadB (m : ℕ) (K : ℝ) (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ k ≤ m, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |(z + 1) ^ k * Work.Spaces.pzIter k g z θ| ≤ K

/-- Monotonicity of `RadB` in the constant. -/
theorem RadB.mono {m : ℕ} {K K' : ℝ} {g : ℝ → ℝ → ℝ} (hK : K ≤ K') (h : RadB m K g) :
    RadB m K' g :=
  fun k hk z θ hz hθ hθ' => le_trans (h k hk z θ hz hθ hθ') hK

/-! ## One step of the product rule for `z ∂_z` -/

/-- **One step**: if `RadB m K g` holds with `m ≥ 1` and `g` is `C^∞` on the open quadrant,
then the radial derivatives of `z ∂_z g` obey the same flat bounds up to order `m - 1`, with
the constant `((m:ℝ)+1)K`.

This is the radial half of `F0_zpz`, with the proof of `F0_zpz` verbatim. -/
theorem RadB_zpz {m : ℕ} (hm : 1 ≤ m) {K : ℝ} {g : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (h : RadB m K g) :
    RadB (m - 1) (((m : ℝ) + 1) * K) (fun z θ => z * Work.Spaces.pz g z θ) := by
  intro k hk z θ hz hθ hθ'
  have hkm : k ≤ m := le_trans hk (Nat.sub_le m 1)
  have hk1 : k + 1 ≤ m := by omega
  have hzk : (0 : ℝ) < z + 1 := by linarith
  -- the `k`-fold product rule for the new function
  have hexp := pzIter_zpz_expand (A := fun z θ => z * Work.Spaces.pz g z θ) (B := g)
    (fun z' θ' _ _ _ => rfl) hg k z θ hz hθ hθ'
  have hb1 : (z + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) g z θ| ≤ K := by
    have h' := h (k + 1) hk1 z θ hz hθ hθ'
    rwa [abs_mul, abs_of_pos (pow_pos hzk (k + 1))] at h'
  have hb0 : (z + 1) ^ k * |Work.Spaces.pzIter k g z θ| ≤ K := by
    have h' := h k hkm z θ hz hθ hθ'
    rwa [abs_mul, abs_of_pos (pow_pos hzk k)] at h'
  have htri : |z * Work.Spaces.pzIter (k + 1) g z θ
        + (k : ℝ) * Work.Spaces.pzIter k g z θ|
      ≤ (z + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
        + (k : ℝ) * |Work.Spaces.pzIter k g z θ| := by
    have h1 : |z * Work.Spaces.pzIter (k + 1) g z θ|
        ≤ (z + 1) * |Work.Spaces.pzIter (k + 1) g z θ| := by
      rw [abs_mul, abs_of_pos hz]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : |(k : ℝ) * Work.Spaces.pzIter k g z θ|
        = (k : ℝ) * |Work.Spaces.pzIter k g z θ| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    calc |z * Work.Spaces.pzIter (k + 1) g z θ
          + (k : ℝ) * Work.Spaces.pzIter k g z θ|
        ≤ |z * Work.Spaces.pzIter (k + 1) g z θ|
          + |(k : ℝ) * Work.Spaces.pzIter k g z θ| := abs_add_le _ _
      _ ≤ (z + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
          + (k : ℝ) * |Work.Spaces.pzIter k g z θ| := by
          rw [h2]; exact add_le_add h1 le_rfl
  rw [hexp, abs_mul, abs_of_pos (pow_pos hzk k)]
  calc (z + 1) ^ k * |z * Work.Spaces.pzIter (k + 1) g z θ
        + (k : ℝ) * Work.Spaces.pzIter k g z θ|
      ≤ (z + 1) ^ k * ((z + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
        + (k : ℝ) * |Work.Spaces.pzIter k g z θ|) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg hzk.le k)
    _ = (z + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) g z θ|
        + (k : ℝ) * ((z + 1) ^ k * |Work.Spaces.pzIter k g z θ|) := by
        rw [pow_succ]; ring
    _ ≤ K + (k : ℝ) * K :=
        add_le_add hb1 (mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg k))
    _ ≤ ((m : ℝ) + 1) * K := by
        have hkm' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
        nlinarith [hK]

/-! ## Iterating the step: `D_z^b` is controlled by the flat data -/

/-- **`D_z^b` is controlled by the radial flat data.**  If `RadB m K g` holds and `g` is
`C^∞` on the open quadrant, then for every `b ≤ m` the iterate `D_z^b g` obeys the radial flat
bounds up to order `m - b` with the constant `((m:ℝ)+1)^b K`. -/
theorem RadB_DzIter {m : ℕ} {K : ℝ} {g : ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ b ≤ m, RadB m K g → RadB (m - b) (((m : ℝ) + 1) ^ b * K) (Work.Spaces.DzIter b g) := by
  intro b
  induction b with
  | zero =>
      intro _ h
      simpa using h
  | succ b ih =>
      intro hb h
      have hbm : b ≤ m := by omega
      have hrec : RadB (m - b) (((m : ℝ) + 1) ^ b * K) (Work.Spaces.DzIter b g) := ih hbm h
      have hm1 : 1 ≤ m - b := by omega
      have hKb : 0 ≤ ((m : ℝ) + 1) ^ b * K := mul_nonneg (pow_nonneg (by positivity) b) hK
      have hstep := RadB_zpz hm1 hKb (hg.DzIter b) hrec
      have hsub : m - (b + 1) = m - b - 1 := by omega
      rw [hsub]
      refine RadB.mono ?_ hstep
      have hle : (((m - b : ℕ) : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
        have : ((m - b : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m b
        linarith
      calc (((m - b : ℕ) : ℝ) + 1) * (((m : ℝ) + 1) ^ b * K)
          ≤ ((m : ℝ) + 1) * (((m : ℝ) + 1) ^ b * K) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg (pow_nonneg (by positivity) b) hK)
        _ = ((m : ℝ) + 1) ^ (b + 1) * K := by rw [pow_succ]; ring

/-! ## The bridge to `CoefTh` -/

/-- Auxiliary exponent identity. -/
private theorem pow_two_mul_pow (a : ℝ) (n : ℕ) : a ^ 2 * a ^ n = a ^ (n + 2) := by
  rw [← pow_add]
  congr 1
  omega

theorem F0_to_CoefTh (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (f : ℝ → ℝ → ℝ), 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.PhiStar.F0 n K (Work.Spaces.pth f) → Work.FTS.VocabO.CoefThMem n f ∧ Work.FTS.VocabO.CoefTh n f ≤ C * K := by
  refine ⟨((n : ℝ) + 1) ^ (n + 2) + 1, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 2) := pow_nonneg (by positivity) _
    linarith
  intro K f hK hsf hf
  -- the pointwise bound on every slot of the coefficient norm
  have key : ∀ b i : ℕ, b + i ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ ((n : ℝ) + 1) ^ n * K := by
    intro b i hbi z θ hz hθ hθ'
    have hbm : b ≤ n - i := by omega
    have hrad : RadB (n - i) K (Work.Spaces.DthIter i (Work.Spaces.pth f)) := by
      intro k hk z' θ' hz' hθ' hθ''
      exact hf k i (by omega) z' θ' hz' hθ' hθ''
    have hDz := RadB_DzIter (m := n - i) (K := K)
      (g := Work.Spaces.DthIter i (Work.Spaces.pth f)) hK ((hsf.pth).DthIter i) b hbm hrad
    have h0 := hDz 0 (Nat.zero_le _) z θ hz hθ hθ'
    simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul] at h0
    refine h0.trans ?_
    have hbase : (((n - i : ℕ) : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : ((n - i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n i
      linarith
    have h2 : (((n - i : ℕ) : ℝ) + 1) ^ b ≤ ((n : ℝ) + 1) ^ b :=
      pow_le_pow_left₀ (by positivity) hbase b
    have h3 : ((n : ℝ) + 1) ^ b ≤ ((n : ℝ) + 1) ^ n :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) (by omega)
    exact mul_le_mul_of_nonneg_right (h2.trans h3) hK
  refine ⟨fun b i hbi => ⟨((n : ℝ) + 1) ^ n * K, fun z θ hz hθ hθ' =>
    key b i hbi z θ hz hθ hθ'⟩, ?_⟩
  have hterm : ∀ b ∈ Finset.range (n + 1), ∀ i ∈ Finset.range (n + 1),
      (if b + i ≤ n then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
        else 0) ≤ ((n : ℝ) + 1) ^ n * K := by
    intro b _ i _
    split_ifs with hbi
    · exact Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' => key b i hbi z θ hz hθ hθ')
    · exact mul_nonneg (pow_nonneg (by positivity) n) hK
  calc Work.FTS.VocabO.CoefTh n f
      = ∑ b ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
          (if b + i ≤ n then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f))
            else 0) := rfl
    _ ≤ ∑ b ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
          ((n : ℝ) + 1) ^ n * K :=
        Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi => hterm b hb i hi
    _ = ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) ^ n * K) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((n : ℝ) + 1) ^ (n + 2) * K := by
        rw [← mul_assoc, pow_two_mul_pow]
    _ ≤ (((n : ℝ) + 1) ^ (n + 2) + 1) * K :=
        mul_le_mul_of_nonneg_right (by linarith) hK

end Work.FTS.PhiStar.CoreAux

import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.NeumannBasics
import Submission.Slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The per-cell slice energy is bounded below by the Neumann ground state

The per-cell bracket ingredient: for the slice `u : X n → ℝ` of a localised
piece in cell `j` (`n := cellCount a j`), frozen at background `x`, the
whole-space energy

    sliceWsE n v u := ∫ |∇u|²  +  ∫ u²·Σ_{t<t′} v(y_t − y_t′)

satisfies `eNeu n (2ℓ) v · ∫u² ≤ sliceWsE n v u` whenever `u` is smooth and
supported inside a shifted standard box `constShift c + box n (2ℓ)` (the
slices of an assignment piece have exactly this support: the strict cell cube
`cellSupp3 ℓ j` lies strictly inside the extended cell of side `2ℓ`).

Proof route (all ingredients are fully proved upstream):
  * shift `u` by `constShift c` to `ũ`, supported in `box n (2ℓ)` —
    `support_shiftAll`, and the whole-space energies are preserved
    (`gradSq_shift`, `intWs_constShift`, plus the measure-preserving
    `L²`-norm identity);
  * `ũ` is an admissible `CNeu` state (`CNeu.ofFun`) when `∫u² > 0`;
  * `eNeu_le_quot_ofFun` gives `eNeu n (2ℓ) v ≤ (kinNeu + intNeu)(ũ)/∫ũ²`;
  * `kinWs_eq_box` / `intWs_eq_intNeu_box` identify the box energies of `ũ`
    with its whole-space energies.

The zero-norm case (`∫u² = 0`) is handled separately (both sides vanish).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The whole-space energy of an `n`-particle function `u`: kinetic
`∫ Σ_{t,k}(∂_{tk}u)²` plus interaction `∫ u²·Σ_{t<t′} v(y_t − y_t′)`. -/
noncomputable def sliceWsE (n : ℕ) (v : ℝ³ → ℝ) (u : X n → ℝ) : ℝ :=
  (∫ y : X n, ∑ t : Fin n, ∑ k : Fin 3, (fderiv ℝ u y (kcDir n t k)) ^ 2) +
    ∫ y : X n, (u y) ^ 2 * intPairSum n v y

/-- A function whose support lies in the box has equal whole-space and box
`L²`-norms. -/
lemma normSq_box_eq_ws {N : ℕ} {L : ℝ} {f : X N → ℝ}
    (hsup : Function.support f ⊆ box N L) :
    (∫ x : X N, (f x) ^ 2) = ∫ x in box N L, (f x) ^ 2 := by
  have hzero : ∀ x : X N, x ∉ box N L → (f x) ^ 2 = 0 := by
    intro x hx
    have hfx : f x = 0 := by
      by_contra h
      exact hx (hsup (Function.mem_support.mpr h))
    simp [hfx]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L) (μ := volume)
    (f := fun x : X N => (f x) ^ 2) hzero).symm

/-- The whole-space `L²`-norm is invariant under the common shift. -/
lemma normSq_shift {n : ℕ} (c : ℝ³) {u : X n → ℝ} (hu : ContDiff ℝ ∞ u) :
    (∫ y : X n, (u (y + constShift n c)) ^ 2) = ∫ y : X n, (u y) ^ 2 := by
  let T : X n → X n := fun y => y + constShift n c
  have hmp : MeasurePreserving T volume volume := by
    dsimp [T]
    simpa [add_comm] using (measurePreserving_add_left volume (constShift n c))
  have hme : MeasurableEmbedding T := by
    dsimp [T]
    simpa using ((Homeomorph.addRight (constShift n c)).measurableEmbedding)
  have h := MeasurePreserving.integral_comp hmp hme (fun z : X n => (u z) ^ 2)
  simpa [T] using h

/-- The whole-space interaction energy is invariant under the common shift
(the pair density needs no shifting: it is pointwise translation invariant). -/
lemma intWs_shift_sq {n : ℕ} (c : ℝ³) (v : ℝ³ → ℝ) {u : X n → ℝ}
    (hu : ContDiff ℝ 1 u) :
    (∫ x : X n, (u (x + constShift n c)) ^ 2 * intPairSum n v x) =
      (∫ x : X n, (u x) ^ 2 * intPairSum n v x) := by
  calc
    (∫ x : X n, (u (x + constShift n c)) ^ 2 * intPairSum n v x)
        = ∫ x : X n, (u (x + constShift n c)) ^ 2 *
            intPairSum n v (x + constShift n c) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← intPairSum_shift n c v x]
    _ = ∫ x : X n, (u x) ^ 2 * intPairSum n v x := by
          exact intWs_constShift (c := c) (v := v) (f := u) hu

/-- **The per-cell slice energy is bounded below by the Neumann ground
state**: for a smooth `n`-particle function supported in a shifted standard
box, `eNeu n (2ℓ) v · ∫u² ≤ sliceWsE n v u`. -/
lemma sliceWsE_ge_eNeu {n : ℕ} {ℓ : ℝ} {c : ℝ³} {v : ℝ³ → ℝ} (hn : 1 ≤ n)
    (hℓ : 0 < ℓ) (hv : 0 ≤ v) {u : X n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hsup : Function.support u ⊆ {y : X n | y - constShift n c ∈ box n (2 * ℓ)}) :
    eNeu n (2 * ℓ) v * (∫ y : X n, (u y) ^ 2) ≤ sliceWsE n v u := by
  -- shift `u` back to the standard box
  let ũ : X n → ℝ := fun z => u (z + constShift n c)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have htr : ContDiff ℝ ∞ (fun z : X n => z + constShift n c) := by
    exact contDiff_id.add contDiff_const
  have hũ : ContDiff ℝ ∞ ũ := by
    dsimp [ũ]
    exact hu.comp htr
  have hũ1 : ContDiff ℝ 1 ũ := hũ.of_le (by norm_num)
  have hsupũ : Function.support ũ ⊆ box n (2 * ℓ) := by
    dsimp [ũ]
    exact support_shiftAll (w := constShift n c) hsup
  -- whole-space norm of `u` = box norm of `ũ`
  have hnorm : (∫ y : X n, (u y) ^ 2) = ∫ x in box n (2 * ℓ), (ũ x) ^ 2 := by
    calc
      (∫ y : X n, (u y) ^ 2) = ∫ y : X n, (u (y + constShift n c)) ^ 2 :=
        (normSq_shift c hu).symm
      _ = ∫ y : X n, (ũ y) ^ 2 := by
        simp [ũ]
      _ = ∫ y in box n (2 * ℓ), (ũ y) ^ 2 := normSq_box_eq_ws hsupũ
  by_cases hz : (∫ y : X n, (u y) ^ 2) = 0
  · -- zero norm: both sides vanish
    rw [hz, mul_zero]
    -- `0 ≤ sliceWsE n v u`: both energy terms are integrals of nonnegative
    -- functions (`v ≥ 0`)
    unfold sliceWsE
    have hk : 0 ≤ ∫ y : X n, ∑ t : Fin n, ∑ k : Fin 3,
        (fderiv ℝ u y (kcDir n t k)) ^ 2 := by
      exact integral_nonneg (fun y =>
        Finset.sum_nonneg (fun t ht =>
          Finset.sum_nonneg (fun k hk => sq_nonneg (fderiv ℝ u y (kcDir n t k)))))
    have hi : 0 ≤ ∫ y : X n, (u y) ^ 2 * intPairSum n v y := by
      exact integral_nonneg (fun y =>
        mul_nonneg (sq_nonneg (u y)) (by
          unfold intPairSum
          exact Finset.sum_nonneg (fun p hp => hv (y p.1 - y p.2))))
    exact add_nonneg hk hi
  · -- nonzero norm: promote `ũ` to a Neumann trial state
    have hpos : 0 < ∫ y : X n, (u y) ^ 2 := by
      have hnn : 0 ≤ ∫ y : X n, (u y) ^ 2 :=
        integral_nonneg (fun y => sq_nonneg (u y))
      exact lt_of_le_of_ne hnn (by intro h0; exact hz h0.symm)
    have hposũ : 0 < ∫ x in box n (2 * ℓ), (ũ x) ^ 2 := by
      rw [← hnorm]
      exact hpos
    have hneũ : ũ ≠ 0 := by
      intro h0
      have hb0 : (∫ x in box n (2 * ℓ), (ũ x) ^ 2) = 0 := by simp [h0]
      rw [← hnorm] at hb0
      exact (ne_of_gt hpos) hb0
    have hquot := eNeu_le_quot_ofFun (N := n) (L := 2 * ℓ) (v := v) hv
      (f := ũ) hũ hneũ hposũ
    have hmul := (le_div_iff₀ hposũ).mp hquot
    -- identify the Neumann energies of `ũ` with the whole-space energies of `u`
    have hkinNeu_eq :
        kinNeu n (2 * ℓ) (CNeu.ofFun hũ hneũ hposũ) =
          ∫ y : X n, ∑ t : Fin n, ∑ k : Fin 3, (fderiv ℝ u y (kcDir n t k)) ^ 2 := by
      calc
        kinNeu n (2 * ℓ) (CNeu.ofFun hũ hneũ hposũ)
            = ∫ y in box n (2 * ℓ), (∑ t : Fin n, ∑ k : Fin 3,
                (fderiv ℝ ũ y (kcDir n t k)) ^ 2) := by
              simp [kinNeu, CNeu.ofFun]
        _ = ∫ y : X n, ∑ t : Fin n, ∑ k : Fin 3, (fderiv ℝ u y (kcDir n t k)) ^ 2 := by
              exact kinBox_shift (w := constShift n c) (L := 2 * ℓ) (f := u) hu1 hsup
    have hintNeu_eq :
        intNeu n (2 * ℓ) v (CNeu.ofFun hũ hneũ hposũ) =
          ∫ y : X n, (u y) ^ 2 * intPairSum n v y := by
      calc
        intNeu n (2 * ℓ) v (CNeu.ofFun hũ hneũ hposũ)
            = ∫ y in box n (2 * ℓ), (ũ y) ^ 2 * intPairSum n v y := by
              simp [intNeu, CNeu.ofFun, intPairSum]
        _ = ∫ y : X n, (ũ y) ^ 2 * intPairSum n v y := by
              exact (intWs_eq_intNeu_box (v := v) (L := 2 * ℓ) (f := ũ) hũ1 hsupũ).symm
        _ = ∫ y : X n, (u y) ^ 2 * intPairSum n v y := by
              simpa [ũ] using (intWs_shift_sq (c := c) (v := v) hu1)
    calc
      eNeu n (2 * ℓ) v * (∫ y : X n, (u y) ^ 2)
          ≤ kinNeu n (2 * ℓ) (CNeu.ofFun hũ hneũ hposũ) +
              intNeu n (2 * ℓ) v (CNeu.ofFun hũ hneũ hposũ) := by
            simpa [hnorm] using hmul
      _ = sliceWsE n v u := by
            unfold sliceWsE
            rw [hkinNeu_eq, hintNeu_eq]


/-
# The pointwise product rule for the `ℋ⁴`-integrand, against the slot right-hand side

This module proves `Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots`: for `χ, f` of class
`SmoothOpen` (`C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`) there is a universal
constant `C > 0` with

  `HkIntegrand α 4 (χ · f) z θ ≤ C * mulSlotRHS α χ f z θ`   (`z > 0`, `0 < θ < π/2`),

where `mulSlotRHS` (of `SlotDefs.lean`) is the Leibniz expansion of the `ℋ⁴`-integrand of
`χ · f`: the multiplier derivatives `mixed b a χ` are kept raw and every `f`-factor is
replaced by the corresponding slot density (`zslot`, `mslot`, `zslotW`).

Route.  Unfold `HkIntegrand α 4 (χ·f)` into its pure `D_z`-slots and its mixed slots
(`1 ≤ i`, `i + j ≤ 4`).

* Pure slots: `leibniz_open_Dz` expands `D_z^i (χ·f)` into the binomial sum
  `∑_{b≤i} C(i,b) (D_z^b χ)(D_z^{i-b} f)`; Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) and
  `C(i,b) ≤ 2^i ≤ 16` bound the square by `256 · ∑_b (D_z^b χ)²(zslot (i-b) f)²`, and each of
  those summands is a term of the `D_z`-block of `mulSlotRHS` (`single_le_sum`, all summands
  are ≥ 0).  The constant is `(i+1)² · 256 ≤ 6400`.
* Mixed slots: `leibniz_open_mixed` expands `D_z^jD_θ^i (χ·f)`; after two Cauchy–Schwarz
  steps and `C(i,a)C(j,b) ≤ 256` the square is bounded by
  `65536 · ∑_{a,b} (mixed b a χ)²ρ²`, where `ρ` is `mixed (j-b)(i-a) f · Wt α` — i.e. exactly
  the `mslot` slot, or, when `i - a = 0` (all `θ`-derivatives on the multiplier), exactly the
  `zslotW` slot.  Each summand is again a term of the mixed block of `mulSlotRHS`; the constant
  is `((i+1)(j+1))² · 65536 ≤ 40 960 000`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `n.choose k ≤ 2^n ≤ 16` for `n ≤ 4`, hence `(n.choose k : ℝ)² ≤ 256`. -/
private lemma binom_sq_le_256 (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 4) :
    (n.choose k : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
  have h2 : n.choose k ≤ 16 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
      _ = 16 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 16 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]

/-- An `if`-block whose value is nonnegative is nonnegative. -/
private lemma blk_nonneg {p : Prop} [Decidable p] {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ (if p then A else 0) := by
  split_ifs with h
  · exact hA
  · exact le_refl 0

/-! ## The two blocks of `mulSlotRHS`, as explicit sums -/

/-- The `(j,s)`-summand of the `D_z`-block of `mulSlotRHS`. -/
def slotZTerm (χ f : Fn) (z θ : ℝ) (j s : ℕ) : ℝ :=
  if s ≤ j then (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2 else 0

/-- The `(i,j,a,b)`-summand of the mixed block of `mulSlotRHS`. -/
def slotMTerm (α : ℝ) (χ f : Fn) (z θ : ℝ) (i j a b : ℕ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ 4 ∧ a ≤ i ∧ b ≤ j then
    (Work.Spaces.mixed b a χ z θ) ^ 2 *
      (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
        else (zslotW α (j - b) f z θ) ^ 2)
    else 0

/-- The `D_z`-block of `mulSlotRHS`. -/
def slotZSum (χ f : Fn) (z θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, ∑ s ∈ Finset.range 5, slotZTerm χ f z θ j s

/-- The mixed block of `mulSlotRHS`. -/
def slotMSum (α : ℝ) (χ f : Fn) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
    ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, slotMTerm α χ f z θ i j a b

lemma mulSlotRHS_eq_slotSums (α : ℝ) (χ f : Fn) (z θ : ℝ) :
    mulSlotRHS α χ f z θ = slotZSum χ f z θ + slotMSum α χ f z θ := rfl

lemma slotZTerm_nonneg (χ f : Fn) (z θ : ℝ) (j s : ℕ) :
    0 ≤ slotZTerm χ f z θ j s :=
  blk_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma slotMTerm_nonneg (α : ℝ) (χ f : Fn) (z θ : ℝ) (i j a b : ℕ) :
    0 ≤ slotMTerm α χ f z θ i j a b :=
  blk_nonneg (by positivity)

lemma slotZSum_nonneg (χ f : Fn) (z θ : ℝ) : 0 ≤ slotZSum χ f z θ :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => slotZTerm_nonneg χ f z θ j s

lemma slotMSum_nonneg (α : ℝ) (χ f : Fn) (z θ : ℝ) : 0 ≤ slotMSum α χ f z θ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => slotMTerm_nonneg α χ f z θ i j a b

lemma mulSlotRHS_nonneg (α : ℝ) (χ f : Fn) (z θ : ℝ) : 0 ≤ mulSlotRHS α χ f z θ := by
  rw [mulSlotRHS_eq_slotSums]
  exact add_nonneg (slotZSum_nonneg χ f z θ) (slotMSum_nonneg α χ f z θ)

/-! ## Every Leibniz summand of `mulSlotRHS` is small enough -/

/-- A term of the `D_z`-block of `mulSlotRHS` is dominated by `mulSlotRHS`. -/
lemma slotZSum_ge_term (α : ℝ) (χ f : Fn) (z θ : ℝ) {j s : ℕ} (hj : j ≤ 4) (hs : s ≤ j) :
    (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2
      ≤ mulSlotRHS α χ f z θ := by
  have hmemj : j ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hmems : s ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hsplit : (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2
      = slotZTerm χ f z θ j s := by
    unfold slotZTerm
    rw [if_pos hs]
  have hinner : slotZTerm χ f z θ j s
      ≤ ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j s' :=
    Finset.single_le_sum (f := fun s' => slotZTerm χ f z θ j s')
      (fun s' _ => slotZTerm_nonneg χ f z θ j s') hmems
  have houter : (∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j s')
      ≤ ∑ j' ∈ Finset.range 5, ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j' s' :=
    Finset.single_le_sum
      (f := fun j' => ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j' s')
      (fun j' _ => Finset.sum_nonneg fun s' _ => slotZTerm_nonneg χ f z θ j' s') hmemj
  have hz : slotZSum χ f z θ
      = ∑ j' ∈ Finset.range 5, ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j' s' := rfl
  rw [mulSlotRHS_eq_slotSums, hz]
  calc (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2
      = slotZTerm χ f z θ j s := hsplit
    _ ≤ ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j s' := hinner
    _ ≤ ∑ j' ∈ Finset.range 5, ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j' s' := houter
    _ ≤ (∑ j' ∈ Finset.range 5, ∑ s' ∈ Finset.range 5, slotZTerm χ f z θ j' s')
          + slotMSum α χ f z θ := le_add_of_nonneg_right (slotMSum_nonneg α χ f z θ)

/-- A term of the mixed block of `mulSlotRHS` is dominated by `mulSlotRHS`. -/
lemma slotMSum_ge_term (α : ℝ) (χ f : Fn) (z θ : ℝ) {i j a b : ℕ}
    (hi : i ≤ 4) (hj : j ≤ 4) (ha : a ≤ i) (hb : b ≤ j) (hi1 : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed b a χ z θ) ^ 2 *
        (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
          else (zslotW α (j - b) f z θ) ^ 2)
      ≤ mulSlotRHS α χ f z θ := by
  have hmem : ∀ x : ℕ, x ≤ 4 → x ∈ Finset.range 5 :=
    fun x hx => Finset.mem_range.mpr (by omega)
  have hi5 : i ∈ Finset.range 5 := hmem i hi
  have hj5 : j ∈ Finset.range 5 := hmem j hj
  have ha5 : a ∈ Finset.range 5 := hmem a (by omega)
  have hb5 : b ∈ Finset.range 5 := hmem b (by omega)
  have hterm : slotMTerm α χ f z θ i j a b
      = (Work.Spaces.mixed b a χ z θ) ^ 2 *
          (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
            else (zslotW α (j - b) f z θ) ^ 2) := by
    unfold slotMTerm
    rw [if_pos ⟨hi1, hij, ha, hb⟩]
  have h1 : slotMTerm α χ f z θ i j a b
      ≤ ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i j a b' :=
    Finset.single_le_sum (f := fun b' => slotMTerm α χ f z θ i j a b')
      (fun b' _ => slotMTerm_nonneg α χ f z θ i j a b') hb5
  have h2 : (∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i j a b')
      ≤ ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i j a' b' :=
    Finset.single_le_sum
      (f := fun a' => ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i j a' b')
      (fun a' _ => Finset.sum_nonneg fun b' _ => slotMTerm_nonneg α χ f z θ i j a' b') ha5
  have h3 : (∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i j a' b')
      ≤ ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5,
          slotMTerm α χ f z θ i j' a' b' :=
    Finset.single_le_sum
      (f := fun j' => ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5,
        slotMTerm α χ f z θ i j' a' b')
      (fun j' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
        slotMTerm_nonneg α χ f z θ i j' a' b') hj5
  have h4 : (∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5,
        slotMTerm α χ f z θ i j' a' b')
      ≤ ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5,
          ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i' j' a' b' :=
    Finset.single_le_sum
      (f := fun i' => ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5,
        slotMTerm α χ f z θ i' j' a' b')
      (fun i' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun a' _ =>
        Finset.sum_nonneg fun b' _ => slotMTerm_nonneg α χ f z θ i' j' a' b') hi5
  have hm : slotMSum α χ f z θ
      = ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5,
          ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i' j' a' b' := rfl
  rw [mulSlotRHS_eq_slotSums, hm]
  calc (Work.Spaces.mixed b a χ z θ) ^ 2 *
        (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
          else (zslotW α (j - b) f z θ) ^ 2)
      = slotMTerm α χ f z θ i j a b := hterm.symm
    _ ≤ ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i j a b' := h1
    _ ≤ ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5,
          slotMTerm α χ f z θ i j a' b' := h2
    _ ≤ ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5, ∑ b' ∈ Finset.range 5,
          slotMTerm α χ f z θ i j' a' b' := h3
    _ ≤ ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5,
          ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i' j' a' b' := h4
    _ ≤ slotZSum χ f z θ
          + ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5, ∑ a' ∈ Finset.range 5,
              ∑ b' ∈ Finset.range 5, slotMTerm α χ f z θ i' j' a' b' :=
        le_add_of_nonneg_left (slotZSum_nonneg χ f z θ)

/-! ## The pure `D_z`-slots of `HkIntegrand α 4 (χ · f)` -/

private lemma zSlot_le {α : ℝ} {χ f : Fn} (hχ : Work.FTS.EllipticEst.SmoothOpen χ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {i : ℕ} (hi : i ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
      ≤ 6400 * mulSlotRHS α χ f z θ := by
  have hnn : 0 ≤ mulSlotRHS α χ f z θ := mulSlotRHS_nonneg α χ f z θ
  have hsum : Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ
      = ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
            * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) := by
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i χ f hχ hf z θ hz hθ0 hθ1,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hcs : (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
            * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2 := by
    rw [hsum]
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => (i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
        * Work.Spaces.DzIter (i - b) f z θ * pw z θ))
  have hterm : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
        * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2
        ≤ 256 * mulSlotRHS α χ f z θ := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (i.choose b : ℝ) ^ 2 ≤ 256 := binom_sq_le_256 i b hbi hi
    have hcore : (Work.Spaces.mixed b 0 χ z θ) ^ 2 * (zslot (i - b) f z θ) ^ 2
        ≤ mulSlotRHS α χ f z θ := slotZSum_ge_term α χ f z θ hi (by omega)
    have hcorenn : 0 ≤ (Work.Spaces.mixed b 0 χ z θ) ^ 2 * (zslot (i - b) f z θ) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h1 : ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
          * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2
        = (i.choose b : ℝ) ^ 2 * ((Work.Spaces.mixed b 0 χ z θ) ^ 2
            * (zslot (i - b) f z θ) ^ 2) := by
      simp only [Work.Spaces.mixed_zero_right, zslot]
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcb hcorenn)
      (mul_le_mul_of_nonneg_left hcore (by norm_num))
  have hsum_bd : ∑ b ∈ Finset.range (i + 1),
        ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
          * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    simp [nsmul_eq_mul]
  have h256 : (0 : ℝ) ≤ 256 * mulSlotRHS α χ f z θ := mul_nonneg (by norm_num) hnn
  have hfin : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ))
      ≤ 6400 * mulSlotRHS α χ f z θ := by
    have hm : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
      have hi4 : (i : ℝ) ≤ 4 := by exact_mod_cast hi
      push_cast
      linarith
    have h1 : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ))
        ≤ 5 * (5 * (256 * mulSlotRHS α χ f z θ)) :=
      mul_le_mul hm (mul_le_mul hm (le_refl ((256 : ℝ) * mulSlotRHS α χ f z θ)) h256
        (by norm_num))
        (mul_nonneg (by positivity) h256) (by norm_num)
    have h2 : 5 * (5 * (256 * mulSlotRHS α χ f z θ)) = 6400 * mulSlotRHS α χ f z θ := by
      ring
    linarith [h1, h2]
  calc (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
            * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2 := hcs
    _ ≤ ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ)) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ ≤ 6400 * mulSlotRHS α χ f z θ := hfin

/-! ## The mixed slots of `HkIntegrand α 4 (χ · f)` -/

private lemma mSlot_le {α : ℝ} {χ f : Fn} (hχ : Work.FTS.EllipticEst.SmoothOpen χ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {i j : ℕ} (hi1 : 1 ≤ i) (hij : i + j ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 40960000 * mulSlotRHS α χ f z θ := by
  have hnn : 0 ≤ mulSlotRHS α χ f z θ := mulSlotRHS_nonneg α χ f z θ
  have hi4 : i ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hlei := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i χ f hχ hf z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (i.choose a : ℝ) * (j.choose b : ℝ)
    * (Work.Spaces.mixed b a χ z θ * Work.Spaces.mixed (j - b) (i - a) f z θ
        * Work.Spaces.Wt α z θ) with hYdef
  have hYsplit : (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b) ^ 2 := by
    have hkey : Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b := by
      rw [hlei, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  have hper : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (Y a b) ^ 2 ≤ 65536 * mulSlotRHS α χ f z θ := by
    intro a ha b hb
    have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hcha : (i.choose a : ℝ) ^ 2 ≤ 256 := binom_sq_le_256 i a hai hi4
    have hchb : (j.choose b : ℝ) ^ 2 ≤ 256 := binom_sq_le_256 j b hbj hj4
    have hch : (i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hYW : (Work.Spaces.mixed (j - b) (i - a) f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
            else (zslotW α (j - b) f z θ) ^ 2) := by
      by_cases hcase : 1 ≤ i - a
      · rw [if_pos hcase]
        rfl
      · rw [if_neg hcase]
        have hzero : i - a = 0 := by omega
        rw [hzero]
        simp only [Work.Spaces.mixed_zero_right, zslotW]
    have hY0 : (Y a b) ^ 2 = (i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2
        * (Work.Spaces.mixed b a χ z θ) ^ 2
        * (Work.Spaces.mixed (j - b) (i - a) f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hYdef]
      ring
    have hslot : (Work.Spaces.mixed b a χ z θ) ^ 2 *
        (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
          else (zslotW α (j - b) f z θ) ^ 2) ≤ mulSlotRHS α χ f z θ :=
      slotMSum_ge_term α χ f z θ hi4 hj4 hai hbj hi1 hij
    have hBnn : 0 ≤ (Work.Spaces.mixed b a χ z θ) ^ 2 *
        (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
          else (zslotW α (j - b) f z θ) ^ 2) := by
      by_cases hc : 1 ≤ i - a
      · rw [if_pos hc]; positivity
      · rw [if_neg hc]; positivity
    rw [hY0, hYW]
    rw [mul_assoc ((i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2)
      ((Work.Spaces.mixed b a χ z θ) ^ 2)
      (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
        else (zslotW α (j - b) f z θ) ^ 2)]
    exact le_trans (mul_le_mul_of_nonneg_right hch hBnn)
      (mul_le_mul_of_nonneg_left hslot (by norm_num))
  have hcardI : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hij25 : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 25 := by
    have h1 : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
    have h2 : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (65536 * mulSlotRHS α χ f z θ) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (65536 * mulSlotRHS α χ f z θ)
      = ((i : ℝ) + 1) * ((j : ℝ) + 1) * (65536 * mulSlotRHS α χ f z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun a => ∑ b ∈ Finset.range (j + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (65536 * mulSlotRHS α χ f z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 * (65536 * mulSlotRHS α χ f z θ) := by
        rw [hsumconst]; ring
    _ ≤ 625 * (65536 * mulSlotRHS α χ f z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
        nlinarith [hij25, h0]
    _ = 40960000 * mulSlotRHS α χ f z θ := by ring

/-! ## The product rule -/

theorem HkIntegrand_mul_le_slots {α : ℝ} {χ f : Work.FTS.Galerkin.Fn}
    (hχ : Work.FTS.EllipticEst.SmoothOpen χ) (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 4 (fun z θ => χ z θ * f z θ) z θ
        ≤ C * Work.FTS.GalBasis.cc.mulSlotRHS α χ f z θ := by
  refine ⟨1024032001, by norm_num, ?_⟩
  intro z θ hz hθ0 hθ1
  have hnn : 0 ≤ mulSlotRHS α χ f z θ := mulSlotRHS_nonneg α χ f z θ
  have hZ : (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
      ≤ 5 * (6400 * mulSlotRHS α χ f z θ) := by
    have hper : ∀ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
          ≤ 6400 * mulSlotRHS α χ f z θ := by
      intro i hi
      exact zSlot_le hχ hf (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hz hθ0 hθ1
    calc (∑ i ∈ Finset.range 5,
          (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (6400 * mulSlotRHS α χ f z θ) := Finset.sum_le_sum hper
      _ = 5 * (6400 * mulSlotRHS α χ f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hM : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 25 * (40960000 * mulSlotRHS α χ f z θ) := by
    have hper : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 40960000 * mulSlotRHS α χ f z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        exact mSlot_le hχ hf hc.1 hc.2 hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg (by norm_num) hnn
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
            (40960000 * mulSlotRHS α χ f z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hper i hi j hj
      _ = 25 * (40960000 * mulSlotRHS α χ f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hsplit : Work.Spaces.HkIntegrand α 4 (fun z θ => χ z θ * f z θ) z θ
      = (∑ i ∈ Finset.range 5,
            (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  rw [hsplit]
  calc (∑ i ∈ Finset.range 5,
          (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ 5 * (6400 * mulSlotRHS α χ f z θ)
        + 25 * (40960000 * mulSlotRHS α χ f z θ) := add_le_add hZ hM
    _ = 1024032000 * mulSlotRHS α χ f z θ := by ring
    _ ≤ 1024032001 * mulSlotRHS α χ f z θ :=
        mul_le_mul_of_nonneg_right (by norm_num) hnn

end Work.FTS.GalBasis.cc

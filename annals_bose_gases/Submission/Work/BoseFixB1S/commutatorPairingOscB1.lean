import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.OscFibBound
import Submission.Work.BoseFixB1S.OscFibDefs
import Submission.Work.BoseFixB1S.commutatorPairingB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.commutatorPairingOscB1`

The **oscillation form** of the commutator pairing: the estimate

  `|Σᵢ⟨[Θ₊(n₀),M_fib]Q_{B,i}Φ, Θ₋(n₀)P_{B,i}Φ⟩| ≤ 4·Cosc·√(n₊·Pmass)`

with the fibre weight `fib` controlled only by its `L²(A)`-*oscillation*
`Cosc² = (1/volA)∫_A(fib − ⦵_A fib)²` instead of a sup-norm bound (which is what
`Work.BoseFixB1S.commutatorPairingB1` uses).

## The route

* the `n₀`-calculus identity `[Θ₊(n₀),M_fib]Q_{B,i}Φ =ᵐ exclFunOp δ (P_{B,i}(M_fib Q_{B,i}Φ))`
  (`δ r = √(r+2) − √(r+1)`) is proved by regrouping both sums over the subset idempotents into the
  pairs `{T, T ∪ {i}}` (`OscFibDefs.sum_erase_pair` + `n0IterFibPair_osc` below); this needs only
  the *slice-dominated* class `OscFibDefs.OscDom` for the unbounded multiplier `fib (· i)`;
* `‖exclFunOp δ W‖₂ ≤ ‖W‖₂` is Bessel (`sqIntegralProjSumLe`) for the *bounded* `W`;
* the fibre oscillation enters through the covariance Cauchy–Schwarz
  `‖P_{B,i}(w(· i)Ψ)‖₂ ≤ Cosc·‖1_A(· i)Ψ‖₂` for the mean-free part `w = fib − ⦵_A fib`
  (`boxPInd_mul_sq_le_osc`).
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases
open Work.UBBInputs8

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `Θ₊(r) = √(r+1) + √c`. -/
noncomputable def oscTheta (c : ℝ) : ℝ → ℝ := fun r => Real.sqrt (r + 1) + Real.sqrt c

/-- `Θ₋(r) = √(r+1) − √c`. -/
noncomputable def oscThetaM (c : ℝ) : ℝ → ℝ := fun r => Real.sqrt (r + 1) - Real.sqrt c

/-- `δ(r) = √(r+2) − √(r+1) = Θ₊(r+1) − Θ₊(r)`. -/
noncomputable def oscDelta : ℝ → ℝ := fun r => Real.sqrt (r + 2) - Real.sqrt (r + 1)

/-! ## 0. The `Q`-projection is annihilated by the box indicator of its own slot -/

theorem Aind_mul_boxQInd {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N)
    (Φ : X N → ℝ) (x : X N) :
    Aind A (x i) * UBBInputs8.boxQInd volA A i Φ x = UBBInputs8.boxQInd volA A i Φ x := by
  rw [show UBBInputs8.boxQInd volA A i Φ x
      = Aind A (x i) * Φ x - UBBInputs8.boxPInd volA A i Φ x from rfl,
    boxPInd_eq volA A i Φ x]
  calc Aind A (x i) * (Aind A (x i) * Φ x - Aind A (x i) * oneMean volA A i Φ x)
      = (Aind A (x i) * Aind A (x i)) * Φ x
        - (Aind A (x i) * Aind A (x i)) * oneMean volA A i Φ x := by ring
    _ = Aind A (x i) * Φ x - Aind A (x i) * oneMean volA A i Φ x := by
        rw [Aind_mul_self]

/-! ## 1. Additivity of the slot iteration on the slice-dominated class -/

theorem n0Slot_add_slice {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} (b : Fin N → Bool) (j : Fin N)
    {Φ Ψ : X N → ℝ} (hΦ : OscDom ℓ A w i Φ) (hΨ : OscDom ℓ A w i Ψ) :
    ∀ x ∈ abox N ℓ,
      n0Slot volA A b j (Φ + Ψ) x = n0Slot volA A b j Φ x + n0Slot volA A b j Ψ x := by
  intro x hx
  by_cases hb : b j = true
  · rw [n0Slot_apply_true volA A b j _ hb x, n0Slot_apply_true volA A b j Φ hb x,
      n0Slot_apply_true volA A b j Ψ hb x]
    exact boxPInd_add volA A j x
      (oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hΦ j x hx)
      (oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hΨ j x hx)
  · have hbf : b j = false := bool_eq_false_of_not_eq_true hb
    rw [n0Slot_apply_false volA A b j _ hbf x, n0Slot_apply_false volA A b j Φ hbf x,
      n0Slot_apply_false volA A b j Ψ hbf x]
    show (Φ + Ψ) x - UBBInputs8.boxPInd volA A j (Φ + Ψ) x
      = (Φ x - UBBInputs8.boxPInd volA A j Φ x) + (Ψ x - UBBInputs8.boxPInd volA A j Ψ x)
    simp only [Pi.add_apply]
    rw [boxPInd_add volA A j x
      (oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hΦ j x hx)
      (oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hΨ j x hx)]
    ring

theorem n0Iter_add_slice {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} (b : Fin N → Bool) :
    ∀ (l : List (Fin N)) (Φ Ψ : X N → ℝ), OscDom ℓ A w i Φ → OscDom ℓ A w i Ψ →
      ∀ x ∈ abox N ℓ, n0Iter volA A b l (Φ + Ψ) x = n0Iter volA A b l Φ x + n0Iter volA A b l Ψ x := by
  intro l
  induction l with
  | nil => intro Φ Ψ _ _ x _; rfl
  | cons k l ih =>
    intro Φ Ψ hΦ hΨ x hx
    rw [n0Iter_cons, n0Iter_cons, n0Iter_cons]
    have hΦ' : OscDom ℓ A w i (n0Slot volA A b k Φ) :=
      oscDom_n0Slot hℓ hvol hA hvolA hAc hw b k hΦ
    have hΨ' : OscDom ℓ A w i (n0Slot volA A b k Ψ) :=
      oscDom_n0Slot hℓ hvol hA hvolA hAc hw b k hΨ
    have hagree : ∀ y ∈ abox N ℓ,
        n0Slot volA A b k (Φ + Ψ) y = (n0Slot volA A b k Φ + n0Slot volA A b k Ψ) y :=
      fun y hy => n0Slot_add_slice hℓ hvol hA hvolA hAc hw b k hΦ hΨ y hy
    rw [n0Iter_eq_of_eqOn_box hA hAc b hagree l x hx]
    exact ih (n0Slot volA A b k Φ) (n0Slot volA A b k Ψ) hΦ' hΨ' x hx

/-! ## 2. The paired fibre commutation on the slice-dominated class -/

theorem n0IterFibPair_osc {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hwm : Measurable w) (hw : IntegrableOn w A) {i : Fin N} {b b' : Fin N → Bool}
    (hb0 : b i = false) (hb1 : b' i = true) :
    ∀ (L : List (Fin N)), L.Nodup → (∀ j ∈ L, j ≠ i → b j = b' j) →
      ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
        n0Iter volA A b L (fun y => w (y i) * Ψ y) x
            + n0Iter volA A b' L (fun y => w (y i) * Ψ y) x
          = w (x i) * (n0Iter volA A b L Ψ x + n0Iter volA A b' L Ψ x) := by
  intro L
  induction L with
  | nil => intro _ _ Ψ _ x _; simp only [n0Iter]; ring
  | cons k l ih =>
    intro hnd hagr Ψ hΨ x hx
    obtain ⟨hkl, hl⟩ := List.nodup_cons.mp hnd
    have hagrl : ∀ j ∈ l, j ≠ i → b j = b' j :=
      fun j hj hne => hagr j (List.mem_cons_of_mem k hj) hne
    have hstate : OscDom ℓ A w i (fun y => w (y i) * Ψ y) :=
      oscDom_w_mul_bdd hwm hΨ.1 hΨ.2.choose_spec
    by_cases hki : k = i
    · -- the head is the marked slot: its projection cancels between the two patterns
      rw [hki] at hkl ⊢
      have hbcongr : ∀ X : X N → ℝ, n0Iter volA A b' l X = n0Iter volA A b l X :=
        fun X => (n0Iter_congr volA A l X
          (fun j hj => hagrl j hj (fun h => hkl (by rw [← h]; exact hj)))).symm
      have hRHS : w (x i) * (n0Iter volA A b (i :: l) Ψ x + n0Iter volA A b' (i :: l) Ψ x)
          = w (x i) * (n0Iter volA A b l (n0Slot volA A b i Ψ) x
              + n0Iter volA A b' l (n0Slot volA A b' i Ψ) x) := by
        rw [n0Iter_cons, n0Iter_cons]
      rw [hRHS]
      have hS1 : OscDom ℓ A w i ((fun y => w (y i) * Ψ y)
          - UBBInputs8.boxPInd volA A i (fun y => w (y i) * Ψ y)) :=
        oscDom_sub hstate (oscDom_boxPInd hℓ hvol hA hvolA hAc hw hstate i)
      have hS2 : OscDom ℓ A w i (UBBInputs8.boxPInd volA A i (fun y => w (y i) * Ψ y)) :=
        oscDom_boxPInd hℓ hvol hA hvolA hAc hw hstate i
      have hT1 : OscDom ℓ A w i (Ψ - UBBInputs8.boxPInd volA A i Ψ) :=
        oscDom_sub (oscDom_of_goodState hΨ) (oscDom_boxPInd hℓ hvol hA hvolA hAc hw
          (oscDom_of_goodState hΨ) i)
      have hT2 : OscDom ℓ A w i (UBBInputs8.boxPInd volA A i Ψ) :=
        oscDom_boxPInd hℓ hvol hA hvolA hAc hw (oscDom_of_goodState hΨ) i
      have hL : n0Iter volA A b l (n0Slot volA A b i (fun y => w (y i) * Ψ y)) x
            + n0Iter volA A b' l (n0Slot volA A b' i (fun y => w (y i) * Ψ y)) x
            = w (x i) * n0Iter volA A b l Ψ x := by
        rw [n0Slot_eq_false volA A b i _ hb0, n0Slot_eq_true volA A b' i _ hb1, hbcongr]
        rw [← n0Iter_add_slice hℓ hvol hA hvolA hAc hw b l
          ((fun y => w (y i) * Ψ y) - UBBInputs8.boxPInd volA A i (fun y => w (y i) * Ψ y))
          (UBBInputs8.boxPInd volA A i (fun y => w (y i) * Ψ y)) hS1 hS2 x hx]
        rw [sub_add_cancel]
        exact n0IterFibComm_free hA hAc w i b l hkl Ψ x hx
      have hR : w (x i) * (n0Iter volA A b l (n0Slot volA A b i Ψ) x
            + n0Iter volA A b' l (n0Slot volA A b' i Ψ) x)
            = w (x i) * n0Iter volA A b l Ψ x := by
        rw [n0Slot_eq_false volA A b i Ψ hb0, n0Slot_eq_true volA A b' i Ψ hb1, hbcongr]
        rw [← n0Iter_add_slice hℓ hvol hA hvolA hAc hw b l
          (Ψ - UBBInputs8.boxPInd volA A i Ψ) (UBBInputs8.boxPInd volA A i Ψ) hT1 hT2 x hx]
        rw [sub_add_cancel]
      conv_lhs => rw [n0Iter_cons, n0Iter_cons]
      rw [hL, hR]
    · -- the head is an ordinary slot: it commutes with the fibre weight
      have hneq : k ≠ i := hki
      have hRHS : w (x i) * (n0Iter volA A b (k :: l) Ψ x + n0Iter volA A b' (k :: l) Ψ x)
          = w (x i) * (n0Iter volA A b l (n0Slot volA A b k Ψ) x
              + n0Iter volA A b' l (n0Slot volA A b k Ψ) x) := by
        rw [n0Iter_cons, n0Iter_cons,
          show n0Slot volA A b' k Ψ = n0Slot volA A b k Ψ from
            (n0Slot_congr volA A (hagr k List.mem_cons_self hneq)).symm]
      have hbk : b k = b' k := hagr k List.mem_cons_self hneq
      have hX : GoodState ℓ (n0Slot volA A b k Ψ) :=
        goodState_n0Slot hℓ hvol hA hvolA hAc b k hΨ
      have hswap1 : ∀ y ∈ abox N ℓ,
          n0Slot volA A b k (fun y => w (y i) * Ψ y) y
            = (fun y => w (y i) * n0Slot volA A b k Ψ y) y :=
        fun y hy => n0Slot_slot_fib volA A b hneq w Ψ y
      have hswap2 : ∀ y ∈ abox N ℓ,
          n0Slot volA A b' k (fun y => w (y i) * Ψ y) y
            = (fun y => w (y i) * n0Slot volA A b k Ψ y) y := by
        intro y hy
        rw [show n0Slot volA A b' k (fun y => w (y i) * Ψ y) y
              = w (y i) * n0Slot volA A b' k Ψ y from
            n0Slot_slot_fib volA A b' hneq w Ψ y,
          show n0Slot volA A b' k Ψ = n0Slot volA A b k Ψ from
            (n0Slot_congr volA A hbk).symm]
      rw [hRHS]
      conv_lhs => rw [n0Iter_cons, n0Iter_cons]
      rw [n0Iter_eq_of_eqOn_box hA hAc b
          (f := n0Slot volA A b k (fun y => w (y i) * Ψ y))
          (g := fun y => w (y i) * n0Slot volA A b k Ψ y) hswap1 l x hx,
        n0Iter_eq_of_eqOn_box hA hAc b'
          (f := n0Slot volA A b' k (fun y => w (y i) * Ψ y))
          (g := fun y => w (y i) * n0Slot volA A b k Ψ y) hswap2 l x hx]
      exact ih hl hagrl (n0Slot volA A b k Ψ) hX x hx

/-! ## 3. The commutator identity at the oscillation level -/

theorem commutator_eq_exclFunOp_osc {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {fib : E3 → ℝ} (hfm : Measurable fib) (hfi : IntegrableOn fib A) (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ)
    (hPΨ : ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A i Ψ x = 0) :
    (fun x : X N => n0FunOp volA A (oscTheta c) (fun y : X N => fib (y i) * Ψ y) x
        - fib (x i) * n0FunOp volA A (oscTheta c) Ψ x)
      =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => exclFunOp volA A i oscDelta
        (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x) := by
  have hXg : OscDom ℓ A fib i (fun y : X N => fib (y i) * Ψ y) :=
    oscDom_w_mul_bdd hfm hΨ.1 hΨ.2.choose_spec
  have hWg : GoodState ℓ (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) :=
    goodState_boxPInd_osc hℓ hvol hA hvolA hAc hfi hXg
  -- the pair identity for the sector `{T, T ∪ {i}}`
  have hpair : ∀ T : Finset (Fin N), i ∉ T → ∀ x ∈ abox N ℓ,
      n0ProjOp volA A T (fun y : X N => fib (y i) * Ψ y) x
        + n0ProjOp volA A (insert i T) (fun y : X N => fib (y i) * Ψ y) x
      = fib (x i) * (n0ProjOp volA A T Ψ x + n0ProjOp volA A (insert i T) Ψ x) := by
    intro T hiT x hx
    have hnd : (List.ofFn (fun j : Fin N => j)).Nodup :=
      List.nodup_ofFn.mpr (fun a b h => h)
    have hagr : ∀ j ∈ List.ofFn (fun j : Fin N => j), j ≠ i →
        (fun j : Fin N => decide (j ∈ T)) j = (fun j : Fin N => decide (j ∈ insert i T)) j := by
      intro j _ hji
      refine decide_eq_decide.mpr ⟨fun h => Finset.mem_insert.mpr (Or.inr h), fun h => ?_⟩
      rcases Finset.mem_insert.mp h with h' | h'
      · exact absurd h' hji
      · exact h'
    have hb0 : (fun j : Fin N => decide (j ∈ T)) i = false := by simpa using hiT
    have hb1 : (fun j : Fin N => decide (j ∈ insert i T)) i = true := by simp
    have hp := n0IterFibPair_osc hℓ hvol hA hvolA hAc hfm hfi hb0 hb1
      (List.ofFn (fun j : Fin N => j)) hnd hagr Ψ hΨ x hx
    simpa only [n0ProjOp] using hp
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  -- (F1): the `Ψ`-sectors containing `i` vanish
  have hF1 : ∀ S : Finset (Fin N), i ∈ S → n0ProjOp volA A S Ψ x = 0 := by
    intro S hiS
    have h2 : n0ProjOp volA A S (UBBInputs8.boxPInd volA A i Ψ) x = 0 := by
      rw [n0ProjOp]
      rw [n0Iter_eq_of_eqOn_box hA hAc (fun j : Fin N => decide (j ∈ S))
        (f := UBBInputs8.boxPInd volA A i Ψ) (g := (0 : X N → ℝ))
        (fun y hy => hPΨ y hy) (List.ofFn (fun j : Fin N => j)) x hx]
      exact congrFun (n0Iter_zero volA A (fun j : Fin N => decide (j ∈ S))
        (List.ofFn (fun j : Fin N => j))) x
    have h1 := n0ProjOp_boxPInd_apply hℓ hvol hA hvolA hAc S i hΨ x hx
    rw [if_pos hiS] at h1
    rw [← h1, h2]
  -- the `P_iX`-sectors avoiding `i` vanish, and the sectors containing `i` see `X`
  have hWzero : ∀ S : Finset (Fin N), i ∉ S →
      n0ProjOp volA A S (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x = 0 := by
    intro S hiS
    have hfix : UBBInputs8.boxPInd volA A i
        (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y))
        = UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y) :=
      boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i _
    have h1 := n0ProjOp_boxPInd_apply hℓ hvol hA hvolA hAc S i hWg x hx
    rw [hfix, if_neg hiS] at h1
    exact h1
  have hF2 : ∀ S : Finset (Fin N), i ∈ S →
      n0ProjOp volA A S (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x
        = n0ProjOp volA A S (fun y : X N => fib (y i) * Ψ y) x :=
    fun S hiS => n0ProjOp_boxPInd_osc hℓ hvol hA hvolA hAc hfi S hiS hXg x hx
  have hmain : n0FunOp volA A (oscTheta c) (fun y : X N => fib (y i) * Ψ y) x
        - fib (x i) * n0FunOp volA A (oscTheta c) Ψ x
      = ∑ T ∈ (Finset.univ.erase i).powerset, oscDelta (T.card : ℝ)
          * n0ProjOp volA A (insert i T) (fun y : X N => fib (y i) * Ψ y) x := by
    rw [n0FunOp_eq_sum_card volA A (oscTheta c) (fun y : X N => fib (y i) * Ψ y),
      n0FunOp_eq_sum_card volA A (oscTheta c) Ψ]
    have h1 : (∑ S : Finset (Fin N), oscTheta c (S.card : ℝ)
          * n0ProjOp volA A S (fun y : X N => fib (y i) * Ψ y) x)
        - fib (x i) * (∑ S : Finset (Fin N), oscTheta c (S.card : ℝ) * n0ProjOp volA A S Ψ x)
        = ∑ S : Finset (Fin N), oscTheta c (S.card : ℝ)
            * (n0ProjOp volA A S (fun y : X N => fib (y i) * Ψ y) x
              - fib (x i) * n0ProjOp volA A S Ψ x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun S _ => by ring)
    rw [h1, sum_erase_pair i (oscTheta c)
      (fun S => n0ProjOp volA A S (fun y : X N => fib (y i) * Ψ y) x
        - fib (x i) * n0ProjOp volA A S Ψ x)]
    apply Finset.sum_congr rfl
    intro T hT
    have hiT : i ∉ T := fun h => Finset.notMem_erase i _ ((Finset.mem_powerset.mp hT) h)
    have hp := hpair T hiT x hx
    have hz := hF1 (insert i T) (Finset.mem_insert_self i T)
    have hF : n0ProjOp volA A T (fun y : X N => fib (y i) * Ψ y) x
          - fib (x i) * n0ProjOp volA A T Ψ x
        = - (n0ProjOp volA A (insert i T) (fun y : X N => fib (y i) * Ψ y) x
              - fib (x i) * n0ProjOp volA A (insert i T) Ψ x) := by
      have hp' := hp
      rw [hz, add_zero] at hp'
      rw [hz, mul_zero, sub_zero]
      linarith [hp']
    rw [hF, hz]
    have hΘδ : oscDelta (T.card : ℝ)
        = oscTheta c ((T.card : ℝ) + 1) - oscTheta c (T.card : ℝ) := by
      simp only [oscDelta, oscTheta]
      have h4 : ((T.card : ℝ) + 1) + 1 = (T.card : ℝ) + 2 := by ring
      rw [h4]
      ring
    rw [hΘδ]
    ring
  have hexcl : exclFunOp volA A i oscDelta
        (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x
      = ∑ T ∈ (Finset.univ.erase i).powerset, oscDelta (T.card : ℝ)
          * n0ProjOp volA A (insert i T) (fun y : X N => fib (y i) * Ψ y) x := by
    rw [show exclFunOp volA A i oscDelta
          (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x
        = ∑ S : Finset (Fin N), oscDelta ((S.card : ℝ) - (if i ∈ S then 1 else 0))
            * n0ProjOp volA A S
                (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x from rfl]
    rw [powersetErasePairSum i oscDelta (fun S => n0ProjOp volA A S
      (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * Ψ y)) x)]
    apply Finset.sum_congr rfl
    intro T hT
    have hiT : i ∉ T := fun h => Finset.notMem_erase i _ ((Finset.mem_powerset.mp hT) h)
    rw [hWzero T hiT, hF2 (insert i T) (Finset.mem_insert_self i T)]
    ring
  rw [hmain, hexcl]

/-! ## 4. The `exclFunOp`-Parseval identity -/

theorem exclFunOp_eq_sum_filter_osc {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {W : X N → ℝ} (hW : GoodState ℓ W) (i : Fin N)
    (hfix : ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A i W x = W x)
    (δ : ℝ → ℝ) :
    ∀ x ∈ abox N ℓ,
      exclFunOp volA A i δ W x
        = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
            (fun S : Finset (Fin N) => δ ((S.card : ℝ) - (if i ∈ S then 1 else 0))) S
              * n0ProjOp volA A S W x := by
  intro x hx
  have hzero : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => ¬ (i ∈ S)),
      (fun S : Finset (Fin N) => δ ((S.card : ℝ) - (if i ∈ S then 1 else 0))) S
        * n0ProjOp volA A S W x = 0 := by
    intro S hS
    have hiS : i ∉ S := by simpa using (Finset.mem_filter.mp hS).2
    have hzeroW : n0ProjOp volA A S W x = 0 := by
      have h1 := n0ProjOp_boxPInd_apply hℓ hvol hA hvolA hAc S i hW x hx
      rw [if_neg hiS] at h1
      have h2 : n0ProjOp volA A S (UBBInputs8.boxPInd volA A i W) x
          = n0ProjOp volA A S W x :=
        n0Iter_eq_of_eqOn_box hA hAc (fun j : Fin N => decide (j ∈ S))
          (f := UBBInputs8.boxPInd volA A i W) (g := W)
          (fun y hy => hfix y hy) (List.ofFn (fun j : Fin N => j)) x hx
      rw [h2] at h1
      exact h1
    rw [hzeroW, mul_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Finset (Fin N))))
    (p := fun S : Finset (Fin N) => i ∈ S)
    (f := fun S : Finset (Fin N) =>
      (fun S : Finset (Fin N) => δ ((S.card : ℝ) - (if i ∈ S then 1 else 0))) S
        * n0ProjOp volA A S W x)
  simp only [exclFunOp]
  rw [← hsplit, Finset.sum_eq_zero hzero, add_zero]

/-! ## 5. The single-slot oscillation estimate -/

theorem pairingBound_single_osc {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {fib : E3 → ℝ} (hfm : Measurable fib)
    (hfibint : IntegrableOn (fun z => (fib z - (∫ z in A, fib z) / volA) ^ 2) A)
    {Cosc : ℝ} (hCosc0 : 0 ≤ Cosc)
    (hosc : Cosc ^ 2 * volA ≥ ∫ z in A, (fib z - (∫ z in A, fib z) / volA) ^ 2)
    (i : Fin N) :
    |∫ x in abox N ℓ,
        ((n0FunOp volA A (oscTheta c)
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (oscTheta c) (UBBInputs8.boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ Cosc * Real.sqrt (∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          * Real.sqrt (∫ x in abox N ℓ,
              (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x ^ 2) := by
  classical
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := exists_abox_bound hℓ hΦc
  have hΦ : GoodState ℓ Φ := ⟨hΦc.measurable, CΦ, hCΦ⟩
  have hQ : GoodState ℓ (UBBInputs8.boxQInd volA A i Φ) :=
    goodState_boxQInd hℓ hvol hA hvolA hAc i hΦ
  have hQP : ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A i Φ) x = 0 :=
    fun x hx => boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i hΦ x hx
  have hPΦ : GoodState ℓ (UBBInputs8.boxPInd volA A i Φ) :=
    goodState_boxPInd hℓ hvol hA hvolA hAc i hΦ
  have hv : GoodState ℓ (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) := by
    refine goodState_n0FunOp hℓ hvol hA hvolA hAc (oscThetaM c)
      (C := Real.sqrt ((N : ℝ) + 1) + |Real.sqrt c|) ?_ hPΦ
    intro S
    have h1 : (S.card : ℝ) ≤ (N : ℝ) := by
      have h2 : S.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ S
      rw [Finset.card_univ, Fintype.card_fin] at h2
      exact_mod_cast h2
    calc |oscThetaM c (S.card : ℝ)|
        = |Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c| := rfl
      _ ≤ |Real.sqrt ((S.card : ℝ) + 1)| + |Real.sqrt c| := abs_sub _ _
      _ = Real.sqrt ((S.card : ℝ) + 1) + |Real.sqrt c| := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt ((N : ℝ) + 1) + |Real.sqrt c| := by
          have h3 : (S.card : ℝ) + 1 ≤ (N : ℝ) + 1 := by linarith
          linarith [Real.sqrt_le_sqrt h3]
  haveI hAfinI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt (volume_A_lt_top hℓ hAc))
  -- the mean-free fibre
  set κ : ℝ := (∫ z in A, fib z) / volA with hκ
  set w : E3 → ℝ := fun z : E3 => fib z - κ with hw
  have hwm : Measurable w := by
    rw [hw]; exact hfm.sub measurable_const
  have hw2 : IntegrableOn (fun z => w z ^ 2) A volume := by
    simpa only [hw, hκ] using hfibint
  have hw1 : IntegrableOn w A volume := by
    have hmeas : AEStronglyMeasurable w ((volume : Measure E3).restrict A) :=
      hwm.aestronglyMeasurable
    refine Integrable.mono' (g := fun z : E3 => 1 + w z ^ 2) ?_ hmeas ?_
    · exact (MeasureTheory.integrable_const (1 : ℝ)).add hw2
    · filter_upwards with z
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs (w z), abs_nonneg (w z)]
  have hfi : IntegrableOn fib A volume := by
    have hsum : IntegrableOn (fun z : E3 => (w z) + κ) A volume :=
      hw1.add (MeasureTheory.integrable_const κ)
    refine IntegrableOn.congr_fun hsum (fun z _ => ?_) hA
    rw [hw]; ring
  have hosc' : ∫ z in A, w z ^ 2 ≤ Cosc ^ 2 * volA := by
    simpa only [hw, hκ] using hosc
  -- the `W`-state
  have hWg : GoodState ℓ
      (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) :=
    goodState_boxPInd_osc hℓ hvol hA hvolA hAc hfi
      (oscDom_w_mul_bdd hfm hQ.1 hQ.2.choose_spec)
  have hWfix : ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A i
      (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
      = UBBInputs8.boxPInd volA A i
          (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y) x :=
    fun x hx => congrFun (boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i _) x
  -- the coefficient bound for `δ`
  have hδb : ∀ S : Finset (Fin N),
      |oscDelta ((S.card : ℝ) - (if i ∈ S then 1 else 0))| ≤ 1 := by
    intro S
    by_cases hiS : i ∈ S
    · rw [if_pos hiS]
      have ha : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
      have hval : oscDelta ((S.card : ℝ) - 1)
          = Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt (S.card : ℝ) := by
        simp only [oscDelta]
        congr 2 <;> ring
      rw [hval]
      exact sqrt_add_one_sub_sqrt_abs_le_one _ ha
    · rw [if_neg hiS, sub_zero]
      have h := sqrt_add_one_sub_sqrt_abs_le_one ((S.card : ℝ) + 1) (by positivity)
      have h4 : (S.card : ℝ) + 1 + 1 = (S.card : ℝ) + 2 := by ring
      rw [h4] at h
      simpa only [oscDelta] using h
  have hEg : GoodState ℓ (exclFunOp volA A i oscDelta
      (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y))) :=
    goodState_exclFunOp hℓ hvol hA hvolA hAc i oscDelta hδb hWg
  -- the identity
  have hD := commutator_eq_exclFunOp_osc (c := c) hℓ hvol hA hvolA hAc hfm hfi i hQ hQP
  -- the Bessel step
  have hparse := exclFunOp_eq_sum_filter_osc hℓ hvol hA hvolA hAc hWg i hWfix oscDelta
  have hcb : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
      |(fun S : Finset (Fin N) => oscDelta ((S.card : ℝ) - (if i ∈ S then 1 else 0))) S| ≤ 1 := by
    intro S hS
    exact hδb S
  have hsq : ∫ x in abox N ℓ, (exclFunOp volA A i oscDelta
        (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y))) x ^ 2
      = ∫ x in abox N ℓ, (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
          (fun S : Finset (Fin N) => oscDelta ((S.card : ℝ) - (if i ∈ S then 1 else 0))) S
            * n0ProjOp volA A S (UBBInputs8.boxPInd volA A i
                (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x) ^ 2 := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    simp only [hparse x hx]
  have hBessel : ∫ x in abox N ℓ, (exclFunOp volA A i oscDelta
        (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y))) x ^ 2
      ≤ ∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A i
          (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x ^ 2 := by
    rw [hsq]
    exact sqIntegralProjSumLe hℓ hvol hA hvolA hAc i hWg hWfix _ hcb
  -- the fibre-oscillation bound
  have hWeq : ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y) x
        = UBBInputs8.boxPInd volA A i
            (fun y : X N => w (y i) * UBBInputs8.boxQInd volA A i Φ y) x := by
    intro x hx
    have hint1 : IntegrableOn
        (fun z => (fun y : X N => w (y i) * UBBInputs8.boxQInd volA A i Φ y)
          (Function.update x i z)) A volume :=
      oscDom_integrableOn_slot (volA := volA) (i := i)
        (Ψ := fun y : X N => w (y i) * UBBInputs8.boxQInd volA A i Φ y) hℓ hA hAc hw1
        (oscDom_w_mul_bdd hwm hQ.1 hQ.2.choose_spec) i x hx
    have hint2 : IntegrableOn
        (fun z => κ * UBBInputs8.boxQInd volA A i Φ (Function.update x i z)) A volume :=
      (oscDom_integrableOn_slot (volA := volA) (i := i)
        (Ψ := UBBInputs8.boxQInd volA A i Φ) hℓ hA hAc hw1
        (oscDom_of_goodState hQ) i x hx).const_mul κ
    have hadd := boxPInd_add (Φ := fun y : X N => w (y i) * UBBInputs8.boxQInd volA A i Φ y)
      (Ψ := fun y : X N => κ * UBBInputs8.boxQInd volA A i Φ y) volA A i x hint1 hint2
    rw [boxPInd_const_mul volA A i κ (UBBInputs8.boxQInd volA A i Φ) x, hQP x hx, mul_zero,
      add_zero] at hadd
    have hcongr : ((fun y : X N => w (y i) * UBBInputs8.boxQInd volA A i Φ y)
          + fun y : X N => κ * UBBInputs8.boxQInd volA A i Φ y)
        = fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y := by
      funext y
      have hy : w (y i) + κ = fib (y i) := by rw [hw]; ring
      rw [Pi.add_apply, ← hy]; ring
    rw [hcongr] at hadd
    exact hadd
  have hWbound : ∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A i
        (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x ^ 2
      ≤ Cosc ^ 2 * ∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2 := by
    have h1 : ∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A i
          (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x ^ 2
        = ∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A i
            (fun y : X N => w (y i) * UBBInputs8.boxQInd volA A i Φ y) x) ^ 2 := by
      apply setIntegral_congr_fun (abox_measurable N ℓ)
      intro x hx
      simp only [hWeq x hx]
    rw [h1]
    have hchild := boxPInd_mul_sq_le_osc_local (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc
      hwm hw2 hosc' (hΨ := hQ) i
    refine le_trans hchild (le_of_eq ?_)
    congr 1
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    simp only [Aind_mul_boxQInd volA A i Φ x]
  -- Cauchy–Schwarz and the conclusion
  have hEint : ∫ x in abox N ℓ,
        ((n0FunOp volA A (oscTheta c)
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (oscTheta c) (UBBInputs8.boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x
      = ∫ x in abox N ℓ, (exclFunOp volA A i oscDelta
          (UBBInputs8.boxPInd volA A i
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y))) x
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x := by
    apply integral_congr_ae
    filter_upwards [hD] with x hx
    rw [hx]
  rw [hEint]
  have hE2 : Real.sqrt (∫ x in abox N ℓ, (exclFunOp volA A i oscDelta
        (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y))) x ^ 2)
      ≤ Cosc * Real.sqrt (∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
    refine le_trans (Real.sqrt_le_sqrt (le_trans hBessel hWbound)) ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hCosc0]
  have hstep : Real.sqrt (∫ x in abox N ℓ, (exclFunOp volA A i oscDelta
          (UBBInputs8.boxPInd volA A i (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y))) x ^ 2)
        * Real.sqrt (∫ x in abox N ℓ,
            (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x ^ 2)
      ≤ (Cosc * Real.sqrt (∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2))
        * Real.sqrt (∫ x in abox N ℓ,
            (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x ^ 2) :=
    mul_le_mul hE2 le_rfl (Real.sqrt_nonneg _) (by positivity)
  refine le_trans (pairing_le_sqrt hℓ hEg hv) ?_
  refine le_trans hstep ?_
  rw [mul_assoc]

/-! ## 6. The summed oscillation pairing -/

theorem commutatorPairingOscB1 {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib)
    (hfibint : MeasureTheory.IntegrableOn
      (fun z => (fib z - (∫ z in A, fib z) / volA) ^ 2) A)
    {Cosc : ℝ} (hCosc0 : 0 ≤ Cosc)
    (hosc : Cosc ^ 2 * volA ≥ ∫ z in A,
      (fib z - (∫ z in A, fib z) / volA) ^ 2) :
    |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        ((Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
            (fun y : Submission.BoseGases.X N =>
              fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (Work.UBBInputs8.boxQInd volA A i Φ)) x)
        * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
            (Work.UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ 4 * Cosc * Real.sqrt
          ((∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.n0FunOp volA A
                  (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd volA A i Φ)) x ^ 2)) := by
  classical
  let Ai : Fin N → ℝ := fun i : Fin N => ∫ x in abox N ℓ, (UBBInputs8.boxQInd volA A i Φ x) ^ 2
  let Bi : Fin N → ℝ := fun i : Fin N => ∫ x in abox N ℓ,
    (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x ^ 2
  have hsingle : ∀ i : Fin N,
      |∫ x in abox N ℓ,
        ((n0FunOp volA A (oscTheta c)
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (oscTheta c) (UBBInputs8.boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ Cosc * Real.sqrt (Ai i) * Real.sqrt (Bi i) :=
    fun i => pairingBound_single_osc hℓ hvol hA hvolA hAc hΦc hfm hfibint hCosc0 hosc i
  have hA0 : ∀ i : Fin N, 0 ≤ Ai i := fun i => integral_nonneg (fun x => sq_nonneg _)
  have hB0 : ∀ i : Fin N, 0 ≤ Bi i := fun i => integral_nonneg (fun x => sq_nonneg _)
  change |∑ i : Fin N, ∫ x in abox N ℓ,
        ((n0FunOp volA A (oscTheta c)
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (oscTheta c) (UBBInputs8.boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ 4 * Cosc * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i))
  calc |∑ i : Fin N, ∫ x in abox N ℓ,
        ((n0FunOp volA A (oscTheta c)
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (oscTheta c) (UBBInputs8.boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ ∑ i : Fin N, |∫ x in abox N ℓ,
        ((n0FunOp volA A (oscTheta c)
            (fun y : X N => fib (y i) * UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (oscTheta c) (UBBInputs8.boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (oscThetaM c) (UBBInputs8.boxPInd volA A i Φ)) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, Cosc * Real.sqrt (Ai i) * Real.sqrt (Bi i) :=
        Finset.sum_le_sum (fun i _ => hsingle i)
    _ = Cosc * ∑ i : Fin N, (Real.sqrt (Ai i) * Real.sqrt (Bi i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ Cosc * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i)) := by
        apply mul_le_mul_of_nonneg_left _ hCosc0
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
          (fun i : Fin N => Real.sqrt (Ai i)) (fun i : Fin N => Real.sqrt (Bi i))
        have h1 : (∑ i : Fin N, (Real.sqrt (Ai i)) ^ 2) = ∑ i : Fin N, Ai i :=
          Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hA0 i))
        have h2 : (∑ i : Fin N, (Real.sqrt (Bi i)) ^ 2) = ∑ i : Fin N, Bi i :=
          Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hB0 i))
        rw [h1, h2] at hcs
        exact Real.le_sqrt_of_sq_le hcs
    _ ≤ 4 * Cosc * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i)) := by
        have h0 : 0 ≤ Cosc * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i)) :=
          mul_nonneg hCosc0 (Real.sqrt_nonneg _)
        linarith

end Work.BoseFixB1S

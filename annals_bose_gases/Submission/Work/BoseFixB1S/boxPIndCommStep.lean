import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SKELETON — the base case of the `n0Iter` induction (`FINDING_perBoxFWeightB1.md` §7.7d route)

The route for `boxPIndCommN0FunOp` (`P_{B,i}` commutes with `n0FunOp g`) is an induction on the slot
list of `n0Iter`: at each slot `j` the operation is `P_{B,j}` or `1 − P_{B,j}`, and `P_{B,i}` must be
pushed past it.  This file supplies the **base case and the two per-slot facts**, in the form the
induction consumes (`Continuous Ψ` → `GoodState` → the corpus's pointwise commutations).

* `continuous_goodState` — `Continuous Ψ` implies the corpus's `GoodState ℓ Ψ` (measurable +
  bounded on the box, by compactness).  This is the entry point: `boxPInd_boxPInd_comm_good` and its
  siblings are stated for `GoodState ℓ Ψ`, not for `Continuous Ψ`.
* `boxPInd_comp_comm_continuous` — the **first slot-recursion step** (`§7.7d`'s "moving `Pᵢ` past
  `P_j`"), `i ≠ j`, a.e. on `abox N ℓ`, straight from the corpus's pointwise
  `boxPInd_boxPInd_comm_good`.

## §7.7b / regularity

The pairwise commutation is **Fubini** over `A × A`, so the `Continuous Ψ` hypothesis is
load-bearing and is *not* decoration: without it the iterated integrals can differ (witness in
§7.7d: `Ψ = (φ(x₀)² − φ(x₁)²)/(φ(x₀)²+φ(x₁)²)²` gives `±π/4`).

## Still to be supplied for the full induction

**All per-slot facts are now present** (this file + `boxPInd_boxComp.lean`):
`boxPInd_comp_comm_continuous` (`i ≠ j`, `P_j`), `boxPInd_comp_qInd_comm_continuous` (`i ≠ j`,
`Q_j`), `boxPInd_comp_self` (`j = i`, `P_i` — the corpus's `boxPInd_idem`, no `GoodState` needed),
`boxPInd_comp_qInd_self` (`j = i`, `P_iQ_i = 0`).  **One fact still to check before the induction
closes**: the *swapped* self-zero `Q_{B,i}P_{B,i} = 0` (i.e. `boxQInd_boxPInd_self_zero`, the mirror
of `boxPInd_boxQInd_self_zero`) — grep `boxPInd_boxComp.lean` first; if absent it is a one-line
mirror of the existing proof.  With it the induction over `n0Iter`'s slot list, and the sum over `k`
for `n0LagrangeOp`/`n0FunOp`, are assembly only.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`Continuous Ψ` gives the corpus's `GoodState`.**  Entry point of the §7.7d route: the pairwise
commutations in `boxPInd_boxComp.lean` are stated for `GoodState ℓ Ψ`. -/
theorem continuous_goodState {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ}
    (hΨc : Continuous Ψ) : GoodState ℓ Ψ := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Ψ) hΨc.continuousOn
  exact ⟨hΨc.measurable, C, fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx⟩

/-- **The first slot-recursion step** (`§7.7d`): `P_{B,i}` commutes with `P_{B,j}` for `i ≠ j`,
a.e. on the box, for `Continuous Ψ`. -/
theorem boxPInd_comp_comm_continuous {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨc : Continuous Ψ) :
    (fun x => Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
        fun x => Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x := by
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  exact boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij (continuous_goodState hℓ hΨc) x hx

/-- **The `j = i` case of the slot recursion**: `P_{B,i}` fixes its own slot's projection
(the corpus's `boxPInd_idem`, which needs no `GoodState` and holds globally). -/
theorem boxPInd_comp_self {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvol : volA ≠ 0) (i : Fin N)
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Ψ)
      = Work.UBBInputs8.boxPInd volA A i Ψ :=
  boxPInd_idem volA A hA hvolA hvol i Ψ

/-- **The `j = i` case for the complement**: `P_{B,i}(1 − P_{B,i}) = 0` on the box, for
`Continuous Ψ` (the corpus's `boxPInd_boxQInd_self_zero` through `continuous_goodState`). -/
theorem boxPInd_comp_qInd_self {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Ψ : X N → ℝ} (hΨc : Continuous Ψ) (i : Fin N) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A i Ψ) x = 0 := by
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  exact boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i (continuous_goodState hℓ hΨc) x hx

/-- **The `1 − P_{B,j}` step for `i ≠ j`**: `P_{B,i}` commutes with the complement `Q_{B,j}`, a.e.
on the box, for `Continuous Ψ` (the corpus's `boxPInd_boxQInd_comm_good` with the slots swapped, so
that the projection moved is `P_{B,i}` and the complement is `Q_{B,j}`). -/
theorem boxPInd_comp_qInd_comm_continuous {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : j ≠ i) {Ψ : X N → ℝ} (hΨc : Continuous Ψ) :
    (fun x => Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
        fun x => Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x := by
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  exact boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij (continuous_goodState hℓ hΨc) x hx

/-- **The per-slot commutation** `P_{B,i}(n0Slot b j Ψ) = n0Slot b j (P_{B,i}Ψ)` on the box:
either `b j = true` (then it is `boxPInd_boxPInd_comm_good`, or `rfl` when `i = j`) or `b j = false`
(then linearity of `boxPInd` over the difference — `boxPInd_add` with `integral_neg` — followed by
the same commutation). -/
theorem n0Slot_comm_boxPInd_local {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i j : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      Work.BoseFixB1S.n0Slot volA A b j (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) x
        = Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1S.n0Slot volA A b j Ψ) x := by
  intro x hx
  by_cases hb : b j = true
  · rw [n0Slot_eq_true volA A b j (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) hb,
      n0Slot_eq_true volA A b j Ψ hb]
    by_cases hij : i = j
    · subst hij; rfl
    · exact boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hΨ x hx
  · have hbf : b j = false := bool_eq_false_of_not_eq_true hb
    rw [n0Slot_eq_false volA A b j (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) hbf,
      n0Slot_eq_false volA A b j Ψ hbf]
    -- linearity of `P_{B,i}` over the difference `Ψ - P_{B,j}Ψ`
    have hPsi : IntegrableOn (fun z => Ψ (Function.update x i z)) A volume := by
      obtain ⟨CΨ, hCΨ⟩ := hΨ.2
      exact slotInt_of_bound (N := N) hℓ hA hAc i x hx hΨ.1 hCΨ
    obtain ⟨hmP, CP, hbP⟩ := goodState_boxPInd hℓ hvol hA hvolA hAc j hΨ
    have hPj : IntegrableOn
        (fun z => (fun y : X N => - (Work.UBBInputs8.boxPInd volA A j Ψ y))
          (Function.update x i z)) A volume :=
      slotInt_of_bound (N := N) hℓ hA hAc i x hx hmP.neg (fun y hy => by
        simpa using hbP y hy)
    have hlin : Work.UBBInputs8.boxPInd volA A i
          (Ψ - Work.UBBInputs8.boxPInd volA A j Ψ) x
        = Work.UBBInputs8.boxPInd volA A i Ψ x
          - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x := by
      have h1 : Work.UBBInputs8.boxPInd volA A i
            (Ψ - Work.UBBInputs8.boxPInd volA A j Ψ) x
          = Work.UBBInputs8.boxPInd volA A i
              (Ψ + fun y : X N => - (Work.UBBInputs8.boxPInd volA A j Ψ y)) x :=
        congrArg (fun Φ => Work.UBBInputs8.boxPInd volA A i Φ x) rfl
      rw [h1, boxPInd_add volA A i x hPsi hPj]
      have h2 : Work.UBBInputs8.boxPInd volA A i
            (fun y : X N => - (Work.UBBInputs8.boxPInd volA A j Ψ y)) x
          = - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x := by
        simp only [Work.UBBInputs8.boxPInd]
        rw [MeasureTheory.integral_neg]
        ring
      rw [h2]
      ring
    rw [hlin]
    simp only [Pi.sub_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hΨ x hx]

/-- **`P_{B,i}` commutes with the whole slot iteration** — the induction over `n0Iter`'s slot list,
one `n0Slot_comm_boxPInd_local` per slot and one use of the induction hypothesis (at the
`GoodState`-preserved state `n0Slot b j Ψ`), the two sides being compared on the box via the corpus's
`n0Iter_eq_of_eqOn_box` congruence. -/
theorem n0Iter_comm_boxPInd_local {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i : Fin N) :
    ∀ (l : List (Fin N)) {Ψ : X N → ℝ}, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
      Work.BoseFixB1S.n0Iter volA A b l (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) x
        = Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1S.n0Iter volA A b l Ψ) x := by
  intro l
  induction l with
  | nil => intro Ψ _ x _; rw [Work.BoseFixB1S.n0Iter, Work.BoseFixB1S.n0Iter]
  | cons j l ih =>
    intro Ψ hΨ x hx
    rw [n0Iter_cons, n0Iter_cons]
    rw [n0Iter_eq_of_eqOn_box (volA := volA) hA hAc b
      (f := Work.BoseFixB1S.n0Slot volA A b j
        (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y))
      (g := fun y => Work.UBBInputs8.boxPInd volA A i
        (Work.BoseFixB1S.n0Slot volA A b j Ψ) y)
      (fun y hy => n0Slot_comm_boxPInd_local hℓ hvol hA hvolA hAc b i j hΨ y hy) l x hx]
    exact ih (goodState_n0Slot hℓ hvol hA hvolA hAc b j hΨ) x hx

end Work.BoseFixB1S

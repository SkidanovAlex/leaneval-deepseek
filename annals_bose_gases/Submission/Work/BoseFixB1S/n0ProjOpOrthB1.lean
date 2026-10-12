import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0OpEqSpectral
import Submission.Work.n0ProjOpOrthAux.n0Iter_fix
import Submission.Work.n0ProjOpOrthAux.n0Iter_sub
import Submission.Work.n0ProjOpOrthAux.n0Slot_selfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The single-slot operator commutes with the box projections `P_j` -/

/-- **`T_i` commutes with `P_j` on the box.**  With `T_i = n0Slot volA A b i` the slot operator
(`P_{B,i}` or its pointwise complement), `T_i(P_jΨ) = P_j(T_iΨ)` holds pointwise on `abox N ℓ` for
every state measurable and bounded on the box. -/
theorem n0Slot_comm_boxPInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i j : Fin N) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0Slot volA A b i (UBBInputs8.boxPInd volA A j Ψ) x
        = UBBInputs8.boxPInd volA A j (n0Slot volA A b i Ψ) x := by
  obtain ⟨hm, C, hb⟩ := hΨ
  have hgood : GoodState ℓ Ψ := ⟨hm, C, hb⟩
  intro x hx
  by_cases h : b i = true
  · rw [n0Slot_apply_true volA A b i (UBBInputs8.boxPInd volA A j Ψ) h x,
      n0Slot_eq_true volA A b i Ψ h]
    by_cases hij : i = j
    · subst hij; rfl
    · exact (boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hgood x hx).symm
  · have hf : b i = false := bool_eq_false_of_not_eq_true h
    rw [n0Slot_apply_false volA A b i (UBBInputs8.boxPInd volA A j Ψ) hf x,
      n0Slot_eq_false volA A b i Ψ hf]
    have hInt1 : IntegrableOn (fun z : E3 => Ψ (Function.update x j z)) A volume :=
      slotInt_of_bound hℓ hA hAc j x hx hm hb
    have hInt2 : IntegrableOn
        (fun z : E3 => UBBInputs8.boxPInd volA A i Ψ (Function.update x j z)) A volume :=
      slotInt_of_bound hℓ hA hAc j x hx (measurable_boxPInd volA A hA i hm)
        (abs_boxPInd_le hℓ hvol hA hvolA hAc i hb)
    rw [boxPInd_sub (Φ := Ψ) (Ψ := UBBInputs8.boxPInd volA A i Ψ) volA A j x hInt1 hInt2]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hgood x hx]

/-! ## 2. The `P_j` commute with the whole slot iteration -/

/-- **`P_j` commutes with the iteration**: `P_j(n0Iter b l Ψ) = n0Iter b l (P_jΨ)` on the box. -/
theorem n0Iter_comm_boxPInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (j : Fin N) :
    ∀ (l : List (Fin N)) {Ψ : X N → ℝ}, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
      n0Iter volA A b l (UBBInputs8.boxPInd volA A j Ψ) x
        = UBBInputs8.boxPInd volA A j (n0Iter volA A b l Ψ) x := by
  intro l
  induction l with
  | nil => intro Ψ _ x _; rw [n0Iter, n0Iter]
  | cons i l ih =>
    intro Ψ hΨ x hx
    rw [n0Iter_cons, n0Iter_cons]
    have hΨi : GoodState ℓ (n0Slot volA A b i Ψ) := goodState_n0Slot hℓ hvol hA hvolA hAc b i hΨ
    rw [← ih hΨi x hx]
    have hpoint : ∀ y ∈ abox N ℓ, n0Slot volA A b i (UBBInputs8.boxPInd volA A j Ψ) y
        = UBBInputs8.boxPInd volA A j (n0Slot volA A b i Ψ) y :=
      fun y hy => n0Slot_comm_boxPInd hℓ hvol hA hvolA hAc b i j hΨ y hy
    exact n0Iter_eq_of_eqOn_box hA hAc b hpoint l x hx

/-! ## 3. The single-slot operator commutes with the whole slot iteration -/

/-- **`T_i` commutes with the iteration**: `n0Iter b l (T_iΨ) = T_i(n0Iter b l Ψ)` on the box. -/
theorem n0Iter_comm_slot {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i : Fin N) (l : List (Fin N)) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0Iter volA A b l (n0Slot volA A b i Ψ) x
        = n0Slot volA A b i (n0Iter volA A b l Ψ) x := by
  intro x hx
  by_cases hbi : b i = true
  · have hL : n0Iter volA A b l (n0Slot volA A b i Ψ) x
        = UBBInputs8.boxPInd volA A i (n0Iter volA A b l Ψ) x := by
      rw [n0Slot_eq_true volA A b i Ψ hbi]
      exact n0Iter_comm_boxPInd hℓ hvol hA hvolA hAc b i l hΨ x hx
    have hR : n0Slot volA A b i (n0Iter volA A b l Ψ) x
        = UBBInputs8.boxPInd volA A i (n0Iter volA A b l Ψ) x :=
      n0Slot_apply_true volA A b i (n0Iter volA A b l Ψ) hbi x
    rw [hL, hR]
  · have hbf : b i = false := bool_eq_false_of_not_eq_true hbi
    have hPi : GoodState ℓ (UBBInputs8.boxPInd volA A i Ψ) :=
      goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
    have hL : n0Iter volA A b l (n0Slot volA A b i Ψ) x
        = n0Iter volA A b l Ψ x - n0Iter volA A b l (UBBInputs8.boxPInd volA A i Ψ) x := by
      rw [n0Slot_eq_false volA A b i Ψ hbf]
      exact Work.n0ProjOpOrthAux.n0Iter_sub hℓ hvol hA hvolA hAc b l hΨ hPi x hx
    have hP : n0Iter volA A b l (UBBInputs8.boxPInd volA A i Ψ) x
        = UBBInputs8.boxPInd volA A i (n0Iter volA A b l Ψ) x :=
      n0Iter_comm_boxPInd hℓ hvol hA hvolA hAc b i l hΨ x hx
    have hR : n0Slot volA A b i (n0Iter volA A b l Ψ) x
        = n0Iter volA A b l Ψ x - UBBInputs8.boxPInd volA A i (n0Iter volA A b l Ψ) x :=
      n0Slot_apply_false volA A b i (n0Iter volA A b l Ψ) hbf x
    rw [hL, hP, hR]

/-! ## 4. Splitting the iteration at an occurrence of a slot -/

/-- **Splitting the list at a slot**: the iteration over `l₁ ++ j :: l₂` is the iteration over
`l₂` applied to the state obtained from the iteration over `l₁` by the slot operator `T_j`. -/
theorem n0Iter_append_slot {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (j : Fin N) :
    ∀ (l₁ l₂ : List (Fin N)) (Ψ : X N → ℝ),
      n0Iter volA A b (l₁ ++ j :: l₂) Ψ
        = n0Iter volA A b l₂ (n0Slot volA A b j (n0Iter volA A b l₁ Ψ)) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ Ψ; rw [List.nil_append, n0Iter_cons, n0Iter]
  | cons i l₁' ih =>
    intro l₂ Ψ
    rw [List.cons_append, n0Iter_cons, ih l₂ (n0Slot volA A b i Ψ),
      ← n0Iter_cons volA A b i l₁' Ψ]

/-! ## 5. Annihilation of a state killed in one slot of the list -/

/-- **A slot that kills the state kills the whole iteration.**  If `j` occurs in the list `l` and
the slot operator at `j` annihilates `Ψ` on the box, then `n0Iter volA A b l Ψ = 0` on the box. -/
theorem n0Iter_kill {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) {j : Fin N} {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ)
    (l : List (Fin N)) (hj : j ∈ l)
    (hkill : ∀ x ∈ abox N ℓ, n0Slot volA A b j Ψ x = 0) :
    ∀ x ∈ abox N ℓ, n0Iter volA A b l Ψ x = 0 := by
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hj
  have hT0 : ∀ x ∈ abox N ℓ, n0Slot volA A b j (n0Iter volA A b l₁ Ψ) x = (0 : X N → ℝ) x := by
    intro x hx
    by_cases hbj : b j = true
    · have hPj : ∀ y ∈ abox N ℓ, UBBInputs8.boxPInd volA A j Ψ y = (0 : X N → ℝ) y := by
        intro y hy
        have h := hkill y hy
        rw [n0Slot_apply_true volA A b j Ψ hbj y] at h
        simpa using h
      have hcm : UBBInputs8.boxPInd volA A j (n0Iter volA A b l₁ Ψ) x
          = n0Iter volA A b l₁ (UBBInputs8.boxPInd volA A j Ψ) x :=
        (n0Iter_comm_boxPInd hℓ hvol hA hvolA hAc b j l₁ hΨ x hx).symm
      have hzero : n0Iter volA A b l₁ (UBBInputs8.boxPInd volA A j Ψ) x = 0 := by
        rw [n0Iter_eq_of_eqOn_box (g := (0 : X N → ℝ)) hA hAc b hPj l₁ x hx]
        simpa using congrFun (n0Iter_zero volA A b l₁) x
      rw [n0Slot_apply_true volA A b j (n0Iter volA A b l₁ Ψ) hbj x, hcm]
      simpa using hzero
    · have hbf : b j = false := bool_eq_false_of_not_eq_true hbj
      have hPj : ∀ y ∈ abox N ℓ, UBBInputs8.boxPInd volA A j Ψ y = Ψ y := by
        intro y hy
        have h := hkill y hy
        rw [n0Slot_apply_false volA A b j Ψ hbf y] at h
        exact (sub_eq_zero.mp h).symm
      rw [n0Slot_apply_false volA A b j (n0Iter volA A b l₁ Ψ) hbf x,
        ← n0Iter_comm_boxPInd hℓ hvol hA hvolA hAc b j l₁ hΨ x hx,
        n0Iter_eq_of_eqOn_box hA hAc b hPj l₁ x hx]
      simp
  intro x hx
  rw [n0Iter_append_slot]
  rw [n0Iter_eq_of_eqOn_box (g := (0 : X N → ℝ)) hA hAc b hT0 l₂ x hx]
  simpa using congrFun (n0Iter_zero volA A b l₂) x

/-! ## 6. Self-adjointness of the iteration -/

/-- **Self-adjointness of the whole iteration**: the product (in list order) of the slot operators
is self-adjoint on `L²(abox N ℓ)`.  The induction peels the head slot operator `T_i`, moves it to
the second argument by the single-slot self-adjointness, and pushes it back through the tail by
`n0Iter_comm_slot`. -/
theorem n0Iter_selfAdjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) :
    ∀ (l : List (Fin N)) {Φ Ψ : X N → ℝ}, GoodState ℓ Φ → GoodState ℓ Ψ →
      (∫ x in abox N ℓ, n0Iter volA A b l Φ x * Ψ x)
        = ∫ x in abox N ℓ, Φ x * n0Iter volA A b l Ψ x := by
  intro l
  induction l with
  | nil => intro Φ Ψ _ _; rw [n0Iter, n0Iter]
  | cons i l ih =>
    intro Φ Ψ hΦ hΨ
    rw [n0Iter_cons, n0Iter_cons]
    have hΦi : GoodState ℓ (n0Slot volA A b i Φ) := goodState_n0Slot hℓ hvol hA hvolA hAc b i hΦ
    have hΨl : GoodState ℓ (n0Iter volA A b l Ψ) := goodState_n0Iter hℓ hvol hA hvolA hAc b l hΨ
    rw [ih (Φ := n0Slot volA A b i Φ) (Ψ := Ψ) hΦi hΨ]
    rw [Work.n0ProjOpOrthAux.n0Slot_selfAdjoint (Φ := Φ) (Ψ := n0Iter volA A b l Ψ)
      hℓ hvol hA hvolA hAc b i hΦ hΨl]
    rw [show (∫ x in abox N ℓ, Φ x * n0Slot volA A b i (n0Iter volA A b l Ψ) x)
        = ∫ x in abox N ℓ, Φ x * n0Iter volA A b l (n0Slot volA A b i Ψ) x from by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      rw [n0Iter_comm_slot hℓ hvol hA hvolA hAc b i l hΨ x hx]]

/-! ## 7. Idempotence on the box -/

/-- **Idempotence of the subset idempotents** on the box: `n0ProjOp S ∘ n0ProjOp S = n0ProjOp S`.
By the eigen-property `n0IterEigen` every slot operator `T_i` fixes `n0ProjOp S Ψ` on the box, so
the iteration over the full slot list does nothing (`Work.n0ProjOpOrthAux.n0Iter_fix`). -/
theorem n0ProjOp_idem {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0ProjOp volA A S (n0ProjOp volA A S Ψ) x = n0ProjOp volA A S Ψ x := by
  have hEig : ∀ i : Fin N, ∀ y ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A i
          (n0Iter volA A (fun i => decide (i ∈ S)) (List.ofFn (fun i : Fin N => i)) Ψ) y
        = (if i ∈ S then
            n0Iter volA A (fun i => decide (i ∈ S)) (List.ofFn (fun i : Fin N => i)) Ψ y
          else 0) :=
    fun i y hy => n0IterEigen hℓ hvol hA hvolA hAc S hΨ i y hy
  have hfix : ∀ i ∈ List.ofFn (fun i : Fin N => i), ∀ y ∈ abox N ℓ,
      n0Slot volA A (fun i => decide (i ∈ S)) i
          (n0Iter volA A (fun i => decide (i ∈ S)) (List.ofFn (fun i : Fin N => i)) Ψ) y
        = n0Iter volA A (fun i => decide (i ∈ S)) (List.ofFn (fun i : Fin N => i)) Ψ y := by
    intro i _ y hy
    by_cases hi : i ∈ S
    · rw [n0Slot_apply_true volA A (fun i => decide (i ∈ S)) i _ (by simpa using hi) y,
        hEig i y hy, if_pos hi]
    · rw [n0Slot_apply_false volA A (fun i => decide (i ∈ S)) i _ (by simpa using hi) y,
        hEig i y hy, if_neg hi, sub_zero]
  intro x hx
  exact Work.n0ProjOpOrthAux.n0Iter_fix hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S))
    (List.ofFn (fun i : Fin N => i)) hfix x hx

/-! ## 8. Orthogonality on the box -/

/-- **Orthogonality of the subset idempotents**: for `S ≠ T`,
`n0ProjOp S (n0ProjOp T Ψ) = 0` on the box.  Pick a slot `j ∈ S △ T`: the slot operator of `S`
at `j` is `P_j` (if `j ∈ S \ T`) or `1 − P_j` (if `j ∈ T \ S`), and the eigen-property of the
`T`-component makes it vanish on `n0ProjOp T Ψ`; then `n0Iter_kill`. -/
theorem n0ProjOp_orth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) (hST : S ≠ T) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ, n0ProjOp volA A S (n0ProjOp volA A T Ψ) x = 0 := by
  have hB : GoodState ℓ (n0Iter volA A (fun i => decide (i ∈ T))
      (List.ofFn (fun i : Fin N => i)) Ψ) :=
    goodState_n0Iter hℓ hvol hA hvolA hAc _ _ hΨ
  have hEigT : ∀ i : Fin N, ∀ y ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A i
          (n0Iter volA A (fun i => decide (i ∈ T)) (List.ofFn (fun i : Fin N => i)) Ψ) y
        = (if i ∈ T then
            n0Iter volA A (fun i => decide (i ∈ T)) (List.ofFn (fun i : Fin N => i)) Ψ y
          else 0) :=
    fun i y hy => n0IterEigen hℓ hvol hA hvolA hAc T hΨ i y hy
  have hsplit : (∃ j ∈ S, j ∉ T) ∨ (∃ j ∈ T, j ∉ S) := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    exact hST (Finset.ext fun j => ⟨fun hj => h1 j hj, fun hj => h2 j hj⟩)
  have hjL : ∀ j : Fin N, j ∈ List.ofFn (fun i : Fin N => i) :=
    fun j => List.mem_ofFn.mpr ⟨j, rfl⟩
  rcases hsplit with ⟨j, hjS, hjT⟩ | ⟨j, hjT, hjS⟩
  · have hkill : ∀ x ∈ abox N ℓ, n0Slot volA A (fun i => decide (i ∈ S)) j
        (n0Iter volA A (fun i => decide (i ∈ T)) (List.ofFn (fun i : Fin N => i)) Ψ) x = 0 := by
      intro x hx
      have hbj : (fun i : Fin N => decide (i ∈ S)) j = true := by simpa using hjS
      rw [n0Slot_apply_true volA A (fun i => decide (i ∈ S)) j _ hbj x, hEigT j x hx,
        if_neg hjT]
    intro x hx
    exact n0Iter_kill hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) hB
      (List.ofFn (fun i : Fin N => i)) (hjL j) hkill x hx
  · have hkill : ∀ x ∈ abox N ℓ, n0Slot volA A (fun i => decide (i ∈ S)) j
        (n0Iter volA A (fun i => decide (i ∈ T)) (List.ofFn (fun i : Fin N => i)) Ψ) x = 0 := by
      intro x hx
      have hbj : (fun i : Fin N => decide (i ∈ S)) j = false := by simpa using hjS
      rw [n0Slot_apply_false volA A (fun i => decide (i ∈ S)) j _ hbj x, hEigT j x hx,
        if_pos hjT, sub_self]
    intro x hx
    exact n0Iter_kill hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) hB
      (List.ofFn (fun i : Fin N => i)) (hjL j) hkill x hx

/-! ## 9. The target -/

theorem n0ProjOpOrthB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∀ S : Finset (Fin N), ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x
          = Work.BoseFixB1S.n0ProjOp volA A S Ψ x)
    ∧ (∀ S T : Finset (Fin N), S ≠ T → ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S (Work.BoseFixB1S.n0ProjOp volA A T Ψ) x = 0)
    ∧ (∀ S : Finset (Fin N), ∀ {Φ Ψ' : Submission.BoseGases.X N → ℝ},
        Work.BoseFixB1S.GoodState ℓ Φ → Work.BoseFixB1S.GoodState ℓ Ψ' →
        ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.n0ProjOp volA A S Φ x * Ψ' x
          = ∫ x in Submission.BoseGases.abox N ℓ,
              Φ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ' x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S x hx
    exact n0ProjOp_idem hℓ hvol hA hvolA hAc S hΨ x hx
  · intro S T hST x hx
    exact n0ProjOp_orth hℓ hvol hA hvolA hAc S T hST hΨ x hx
  · intro S Φ Ψ' hΦ hΨ'
    exact n0Iter_selfAdjoint hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S))
      (List.ofFn (fun i : Fin N => i)) hΦ hΨ'

end Work.BoseFixB1S

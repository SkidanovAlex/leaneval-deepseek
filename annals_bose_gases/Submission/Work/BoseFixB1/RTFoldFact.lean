import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQInd_selfAdjoint_bdd
import Submission.Work.BoseFixB1.flatPiece_eigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The multiplication operator `Rᵢ = rInd A i` -/

/-- `Rᵢ` is measurable when `A` is. -/
theorem rInd_measurable {N : ℕ} {A : Set 𝔼3} (hA : MeasurableSet A) (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : Measurable Ψ) : Measurable (rInd A i Ψ) := by
  show Measurable (fun y : X N => Aᶜ.indicator (fun _ => (1 : ℝ)) (y i) * Ψ y)
  exact ((measurable_const.indicator hA.compl).comp (measurable_pi_apply i)).mul hΨ

/-- `|RᵢΨ x| ≤ |Ψ x|` pointwise. -/
theorem abs_rInd_le {N : ℕ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) (x : X N) :
    |rInd A i Ψ x| ≤ |Ψ x| := by
  have h1 : |Aᶜ.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hx : x i ∈ Aᶜ
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [rInd, abs_mul]
  calc |Aᶜ.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * |Ψ x| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |Ψ x| := one_mul _

/-- `Rᵢ` is idempotent. -/
theorem rInd_mul_self {N : ℕ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) :
    rInd A i (rInd A i Ψ) = rInd A i Ψ := by
  funext x
  have h1 : Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Aᶜ.indicator (fun _ => (1 : ℝ)) (x i)
      = Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) := by
    by_cases hx : x i ∈ Aᶜ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  simp only [rInd]
  rw [← mul_assoc, h1]

/-- `Rᵢ` of the zero state. -/
theorem rInd_zero {N : ℕ} (A : Set 𝔼3) (i : Fin N) :
    rInd A i (fun _ : X N => (0 : ℝ)) = fun _ => 0 := by
  funext x
  simp [rInd]

/-- `Rᵢ` of a state switched off by an `if`. -/
theorem rInd_ite_zero {N : ℕ} (A : Set 𝔼3) (i : Fin N) (c : Prop) [Decidable c]
    (Φ : X N → ℝ) :
    rInd A i (fun y => if c then Φ y else 0)
      = fun y => if c then rInd A i Φ y else 0 := by
  funext x
  simp only [rInd]
  by_cases hc : c <;> simp [hc]

/-- `Rᵢ` of a state switched *on* by an `if`. -/
theorem rInd_zero_ite {N : ℕ} (A : Set 𝔼3) (i : Fin N) (c : Prop) [Decidable c]
    (Φ : X N → ℝ) :
    rInd A i (fun y => if c then 0 else Φ y)
      = fun y => if c then 0 else rInd A i Φ y := by
  funext x
  simp only [rInd]
  by_cases hc : c <;> simp [hc]

/-- `Rᵢ` is a congruence for pointwise equality on the analysis box. -/
theorem rInd_congr_abox {N : ℕ} {ℓ : ℝ} (A : Set 𝔼3) (i : Fin N) {f g : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, f y = g y) :
    ∀ x ∈ abox N ℓ, rInd A i f x = rInd A i g x := by
  intro x hx
  simp only [rInd]
  rw [h x hx]

/-- **`Pᵢ ∘ Rᵢ = 0`** (the defining slot integral of `Pᵢ` runs over `A`). -/
theorem boxPInd_rInd_zero {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A) (i : Fin N)
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i (rInd A i Ψ) = fun _ => (0 : ℝ) := by
  funext x
  have h : (∫ z in A, rInd A i Ψ (Function.update x i z)) = 0 := by
    rw [show (∫ z in A, rInd A i Ψ (Function.update x i z)) = ∫ _z in A, (0 : ℝ) from
      setIntegral_congr_fun hA (fun z hz => by
        rw [rInd, Function.update_self,
          Set.indicator_of_notMem (fun hmem => (Set.mem_compl_iff A z).mp hmem hz), zero_mul])]
    simp
  simp only [Work.UBBInputs8.boxPInd]
  rw [h]
  ring

/-- **`Qᵢ ∘ Rᵢ = 0`**: `QᵢRᵢ = 1_A(·ᵢ)Rᵢ − PᵢRᵢ = 0`. -/
theorem boxQInd_rInd_zero {N : ℕ} {V : ℝ} {A : Set 𝔼3} (hA : MeasurableSet A) (i : Fin N)
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxQInd V A i (rInd A i Ψ) = fun _ => (0 : ℝ) := by
  funext x
  rw [show Work.UBBInputs8.boxQInd V A i (rInd A i Ψ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * rInd A i Ψ x
        - Work.UBBInputs8.boxPInd V A i (rInd A i Ψ) x from rfl]
  rw [show Work.UBBInputs8.boxPInd V A i (rInd A i Ψ) x
      = (1 / V) * (∫ z in A, rInd A i Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  have h : (∫ z in A, rInd A i Ψ (Function.update x i z)) = 0 := by
    rw [show (∫ z in A, rInd A i Ψ (Function.update x i z)) = ∫ _z in A, (0 : ℝ) from
      setIntegral_congr_fun hA (fun z hz => by
        rw [rInd, Function.update_self,
          Set.indicator_of_notMem (fun hmem => (Set.mem_compl_iff A z).mp hmem hz), zero_mul])]
    simp
  rw [h]
  simp only [rInd]
  by_cases hx : x i ∈ A
  · rw [Set.indicator_of_notMem (fun hmem => (Set.mem_compl_iff A (x i)).mp hmem hx)]
    ring
  · rw [Set.indicator_of_notMem hx]
    ring

/-- **`Rᵢ ∘ Pᵢ = 0`** (`Pᵢ` already carries the box indicator `1_A(xᵢ)`). -/
theorem rInd_boxPInd_zero {N : ℕ} {V : ℝ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) :
    rInd A i (Work.UBBInputs8.boxPInd V A i Ψ) = fun _ => (0 : ℝ) := by
  funext x
  rw [show rInd A i (Work.UBBInputs8.boxPInd V A i Ψ) x
      = Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Work.UBBInputs8.boxPInd V A i Ψ x from rfl]
  rw [show Work.UBBInputs8.boxPInd V A i Ψ x
      = (1 / V) * (∫ z in A, Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  by_cases hx : x i ∈ A
  · rw [Set.indicator_of_notMem (fun hmem => (Set.mem_compl_iff A (x i)).mp hmem hx)]
    ring
  · rw [Set.indicator_of_mem ((Set.mem_compl_iff A (x i)).mpr hx),
      Set.indicator_of_notMem hx]
    ring

/-- **`Rᵢ ∘ Qᵢ = 0`** (`Qᵢ` also carries the box indicator `1_A(xᵢ)`). -/
theorem rInd_boxQInd_zero {N : ℕ} {V : ℝ} (A : Set 𝔼3) (i : Fin N) (Ψ : X N → ℝ) :
    rInd A i (Work.UBBInputs8.boxQInd V A i Ψ) = fun _ => (0 : ℝ) := by
  funext x
  rw [show rInd A i (Work.UBBInputs8.boxQInd V A i Ψ) x
      = Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Work.UBBInputs8.boxQInd V A i Ψ x from rfl]
  rw [show Work.UBBInputs8.boxQInd V A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd V A i Ψ x from rfl]
  rw [show Work.UBBInputs8.boxPInd V A i Ψ x
      = (1 / V) * (∫ z in A, Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  by_cases hx : x i ∈ A
  · rw [Set.indicator_of_notMem (fun hmem => (Set.mem_compl_iff A (x i)).mp hmem hx)]
    ring
  · rw [Set.indicator_of_mem ((Set.mem_compl_iff A (x i)).mpr hx),
      Set.indicator_of_notMem hx]
    ring

/-! ## 2. Commutation with a multiplication in another slot -/

/-- **`Pᵢ` commutes with multiplication by a function of the slot `j ≠ i`.** -/
theorem boxPInd_mul_other {N : ℕ} {V : ℝ} (A : Set 𝔼3) {i j : Fin N} (hij : i ≠ j)
    (g : 𝔼3 → ℝ) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i (fun y => g (y j) * Ψ y)
      = fun x => g (x j) * Work.UBBInputs8.boxPInd V A i Ψ x := by
  funext x
  simp only [Work.UBBInputs8.boxPInd]
  have h1 : ∀ z : 𝔼3, (Function.update x i z) j = x j := by
    intro z
    rw [Function.update_apply, if_neg]
    exact fun h => hij h.symm
  have h2 : (∫ z in A, (fun y => g (y j) * Ψ y) (Function.update x i z))
      = g (x j) * ∫ z in A, Ψ (Function.update x i z) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [h1 z]
  rw [h2]
  ring

/-- **`Qᵢ` commutes with multiplication by a function of the slot `j ≠ i`.** -/
theorem boxQInd_mul_other {N : ℕ} {V : ℝ} (A : Set 𝔼3) {i j : Fin N} (hij : i ≠ j)
    (g : 𝔼3 → ℝ) (Ψ : X N → ℝ) :
    Work.UBBInputs8.boxQInd V A i (fun y => g (y j) * Ψ y)
      = fun x => g (x j) * Work.UBBInputs8.boxQInd V A i Ψ x := by
  funext x
  rw [show Work.UBBInputs8.boxQInd V A i (fun y => g (y j) * Ψ y) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * (g (x j) * Ψ x)
        - Work.UBBInputs8.boxPInd V A i (fun y => g (y j) * Ψ y) x from rfl]
  rw [congr_fun (boxPInd_mul_other (V := V) A hij g Ψ) x]
  rw [show Work.UBBInputs8.boxQInd V A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd V A i Ψ x from rfl]
  ring

/-- **`Rᵢ` commutes with the box projection `Pⱼ`, `j ≠ i`.** -/
theorem rInd_boxPInd_comm {N : ℕ} {V : ℝ} (A : Set 𝔼3) {i j : Fin N} (hij : i ≠ j)
    (Ψ : X N → ℝ) :
    rInd A i (Work.UBBInputs8.boxPInd V A j Ψ)
      = Work.UBBInputs8.boxPInd V A j (rInd A i Ψ) := by
  have h := congr_fun (boxPInd_mul_other (V := V) (A := A) (i := j) (j := i) hij.symm
    (fun y => Aᶜ.indicator (fun _ => (1 : ℝ)) y) Ψ)
  funext x
  exact (h x).symm

/-- **`Rᵢ` commutes with the mean-free projection `Qⱼ`, `j ≠ i`.** -/
theorem rInd_boxQInd_comm {N : ℕ} {V : ℝ} (A : Set 𝔼3) {i j : Fin N} (hij : i ≠ j)
    (Ψ : X N → ℝ) :
    rInd A i (Work.UBBInputs8.boxQInd V A j Ψ)
      = Work.UBBInputs8.boxQInd V A j (rInd A i Ψ) := by
  have h := congr_fun (boxQInd_mul_other (V := V) (A := A) (i := j) (j := i) hij.symm
    (fun y => Aᶜ.indicator (fun _ => (1 : ℝ)) y) Ψ)
  funext x
  exact (h x).symm

/-- **`Rᵢ` and `Rⱼ` commute** for `i ≠ j` (both are multiplication operators). -/
theorem rInd_rInd_comm {N : ℕ} (A : Set 𝔼3) {i j : Fin N} (hij : i ≠ j) (Ψ : X N → ℝ) :
    rInd A i (rInd A j Ψ) = rInd A j (rInd A i Ψ) := by
  funext x
  simp only [rInd]
  ring

/-! ## 3. Measurability and box-boundedness of the fold -/

/-- **The `(P,Q,R)`-fold preserves measurability and box-boundedness.** -/
theorem flatPieceRTList_meas_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ) :
    ∀ (l : List (Fin N)) (S T : Finset (Fin N)) {f : X N → ℝ}, Measurable f →
      (∃ C, ∀ x ∈ abox N ℓ, |f x| ≤ C) →
      Measurable (flatPieceRTList V A l S T f)
        ∧ ∃ C', ∀ x ∈ abox N ℓ, |flatPieceRTList V A l S T f x| ≤ C' := by
  intro l
  induction l with
  | nil => intro S T f hfm hb; exact ⟨by simpa using hfm, by simpa using hb⟩
  | cons i l ih =>
    intro S T f hfm hb
    obtain ⟨hGm, hGb⟩ := ih S T hfm hb
    rw [flatPieceRTList_cons]
    by_cases hiS : i ∈ S
    · rw [if_pos hiS]
      refine ⟨Work.BoseFixB1S.measurable_boxPInd V A hA i hGm, ?_⟩
      obtain ⟨C', hC'⟩ := hGb
      exact ⟨C', Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hC'⟩
    · rw [if_neg hiS]
      by_cases hiT : i ∈ T
      · rw [if_pos hiT]
        refine ⟨Work.SlotWord.measurable_boxQInd V A hA i hGm, ?_⟩
        obtain ⟨C', hC'⟩ := hGb
        exact ⟨2 * C', abs_boxQInd_le_abox hℓ hV hA hVeq hAc i hC'⟩
      · rw [if_neg hiT]
        refine ⟨rInd_measurable hA i hGm, ?_⟩
        obtain ⟨C', hC'⟩ := hGb
        exact ⟨C', fun x hx => le_trans (abs_rInd_le A i _ x) (hC' x hx)⟩

/-! ## 4. The eigen-relation of the pieces -/

/-- **The eigen-relation of the `(P,Q,R)`-fold.**  For a repetition-free slot list `l`, a state
`f` measurable and bounded on the box, a *disjoint* pair `(S,T)` of slot sets and a slot `i ∈ l`,
the three slot operators act on the piece `Θ = flatPieceRTList V A l S T f` as the numbers
`[i∈S]`, `[i∈T]`, `[i∉S∪T]` on the analysis box. -/
theorem flatPieceRTList_eigen {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ) :
    ∀ (l : List (Fin N)), l.Nodup → ∀ (S T : Finset (Fin N)), Disjoint S T → ∀ {f : X N → ℝ},
      Measurable f → (∃ C, ∀ x ∈ abox N ℓ, |f x| ≤ C) →
      (∀ i ∈ l, ∀ x ∈ abox N ℓ,
          Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l S T f) x
            = if i ∈ S then flatPieceRTList V A l S T f x else 0)
      ∧ (∀ i ∈ l, ∀ x ∈ abox N ℓ,
          Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l S T f) x
            = if i ∈ T then flatPieceRTList V A l S T f x else 0)
      ∧ (∀ i ∈ l, ∀ x ∈ abox N ℓ,
          rInd A i (flatPieceRTList V A l S T f) x
            = if i ∈ S ∨ i ∈ T then 0 else flatPieceRTList V A l S T f x) := by
  intro l
  induction l with
  | nil =>
    intro _ S T _ f _ _
    exact ⟨fun i hi => absurd hi List.not_mem_nil, fun i hi => absurd hi List.not_mem_nil,
      fun i hi => absurd hi List.not_mem_nil⟩
  | cons j l' ih =>
    intro hl S T hST f hfm hb
    obtain ⟨hjl', hl'⟩ := List.nodup_cons.mp hl
    obtain ⟨ihP, ihQ, ihR⟩ := ih hl' S T hST hfm hb
    obtain ⟨hGm, Cb, hCb⟩ := flatPieceRTList_meas_bdd hℓ hV hA hVeq hAc l' S T hfm hb
    have hjS_notT : j ∈ S → j ∉ T := fun h1 h2 => Finset.disjoint_left.mp hST h1 h2
    refine ⟨?_, ?_, ?_⟩
    · -- the `P`-relation
      intro i hi x hx
      rcases List.mem_cons.mp hi with hji | hi'
      · rw [hji]
        by_cases hjS : j ∈ S
        · rw [flatPieceRTList_cons, if_pos hjS, if_pos hjS]
          exact congr_fun (boxPInd_self_idem hV hA hVeq j
            (flatPieceRTList V A l' S T f)) x
        · rw [flatPieceRTList_cons, if_neg hjS, if_neg hjS]
          by_cases hjT : j ∈ T
          · rw [if_pos hjT]
            simp [boxPInd_boxQInd_self_zero hV hA hVeq j (flatPieceRTList V A l' S T f)]
          · rw [if_neg hjT]
            simp [boxPInd_rInd_zero (V := V) hA j (flatPieceRTList V A l' S T f)]
      · have hij : i ≠ j := fun h => hjl' (h ▸ hi')
        by_cases hjS : j ∈ S
        · rw [flatPieceRTList_cons, if_pos hjS]
          rw [boxPInd_comm_bdd hℓ hV hA hVeq hAc hij hGm hCb x hx]
          rw [(boxInd_congr_on (V := V) hA hAc j hx (fun y hy => ihP i hi' y hy)).1,
            boxPInd_ite_zero V j (i ∈ S) (flatPieceRTList V A l' S T f) x]
        · rw [flatPieceRTList_cons, if_neg hjS]
          by_cases hjT : j ∈ T
          · rw [if_pos hjT]
            rw [boxPInd_boxQInd_comm_bdd hℓ hV hA hVeq hAc hij hGm hCb x hx]
            rw [(boxInd_congr_on (V := V) hA hAc j hx (fun y hy => ihP i hi' y hy)).2,
              boxQInd_ite_zero V j (i ∈ S) (flatPieceRTList V A l' S T f) x]
          · rw [if_neg hjT]
            rw [show Work.UBBInputs8.boxPInd V A i (rInd A j (flatPieceRTList V A l' S T f)) x
                = Aᶜ.indicator (fun _ => (1 : ℝ)) (x j)
                  * Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l' S T f) x from
              congr_fun (boxPInd_mul_other (V := V) (A := A) (i := i) (j := j) hij
                (fun y => Aᶜ.indicator (fun _ => (1 : ℝ)) y)
                (flatPieceRTList V A l' S T f)) x]
            rw [ihP i hi' x hx]
            by_cases hiS : i ∈ S <;> simp [hiS, rInd]
    · -- the `Q`-relation
      intro i hi x hx
      rcases List.mem_cons.mp hi with hji | hi'
      · rw [hji]
        by_cases hjS : j ∈ S
        · rw [flatPieceRTList_cons, if_pos hjS, if_neg (hjS_notT hjS)]
          simp [boxQInd_self_boxPInd hV hA hVeq j (flatPieceRTList V A l' S T f)]
        · rw [flatPieceRTList_cons, if_neg hjS]
          by_cases hjT : j ∈ T
          · rw [if_pos hjT, if_pos hjT]
            exact congr_fun (boxQInd_self_idem hV hA hVeq j
              (flatPieceRTList V A l' S T f)) x
          · rw [if_neg hjT, if_neg hjT]
            simp [boxQInd_rInd_zero (V := V) hA j (flatPieceRTList V A l' S T f)]
      · have hij : i ≠ j := fun h => hjl' (h ▸ hi')
        by_cases hjS : j ∈ S
        · rw [flatPieceRTList_cons, if_pos hjS]
          rw [boxQInd_boxPInd_comm_bdd hℓ hV hA hVeq hAc hij hGm hCb x hx]
          rw [(boxInd_congr_on (V := V) hA hAc j hx (fun y hy => ihQ i hi' y hy)).1,
            boxPInd_ite_zero V j (i ∈ T) (flatPieceRTList V A l' S T f) x]
        · rw [flatPieceRTList_cons, if_neg hjS]
          by_cases hjT : j ∈ T
          · rw [if_pos hjT]
            rw [boxQInd_boxQInd_comm_bdd hℓ hV hA hVeq hAc hij hGm hCb x hx]
            rw [(boxInd_congr_on (V := V) hA hAc j hx (fun y hy => ihQ i hi' y hy)).2,
              boxQInd_ite_zero V j (i ∈ T) (flatPieceRTList V A l' S T f) x]
          · rw [if_neg hjT]
            rw [show Work.UBBInputs8.boxQInd V A i (rInd A j (flatPieceRTList V A l' S T f)) x
                = Aᶜ.indicator (fun _ => (1 : ℝ)) (x j)
                  * Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l' S T f) x from
              congr_fun (boxQInd_mul_other (V := V) (A := A) (i := i) (j := j) hij
                (fun y => Aᶜ.indicator (fun _ => (1 : ℝ)) y)
                (flatPieceRTList V A l' S T f)) x]
            rw [ihQ i hi' x hx]
            by_cases hiT : i ∈ T <;> simp [hiT, rInd]
    · -- the `R`-relation
      intro i hi x hx
      rcases List.mem_cons.mp hi with hji | hi'
      · rw [hji]
        by_cases hjS : j ∈ S
        · rw [flatPieceRTList_cons, if_pos hjS, if_pos (Or.inl hjS)]
          simp [rInd_boxPInd_zero (V := V) A j (flatPieceRTList V A l' S T f)]
        · rw [flatPieceRTList_cons, if_neg hjS]
          by_cases hjT : j ∈ T
          · rw [if_pos hjT, if_pos (Or.inr hjT)]
            simp [rInd_boxQInd_zero (V := V) A j (flatPieceRTList V A l' S T f)]
          · rw [if_neg hjT, if_neg (fun h => h.elim hjS hjT)]
            exact congr_fun (rInd_mul_self A j (flatPieceRTList V A l' S T f)) x
      · have hij : i ≠ j := fun h => hjl' (h ▸ hi')
        by_cases hjS : j ∈ S
        · rw [flatPieceRTList_cons, if_pos hjS]
          rw [rInd_boxPInd_comm (V := V) A hij (flatPieceRTList V A l' S T f)]
          rw [(boxInd_congr_on (V := V) hA hAc j hx (fun y hy => ihR i hi' y hy)).1,
            boxPInd_zero_ite V j (i ∈ S ∨ i ∈ T) (flatPieceRTList V A l' S T f) x]
        · rw [flatPieceRTList_cons, if_neg hjS]
          by_cases hjT : j ∈ T
          · rw [if_pos hjT]
            rw [rInd_boxQInd_comm (V := V) A hij (flatPieceRTList V A l' S T f)]
            rw [(boxInd_congr_on (V := V) hA hAc j hx (fun y hy => ihR i hi' y hy)).2,
              boxQInd_zero_ite V j (i ∈ S ∨ i ∈ T) (flatPieceRTList V A l' S T f) x]
          · rw [if_neg hjT]
            rw [rInd_rInd_comm A hij (flatPieceRTList V A l' S T f)]
            rw [rInd_congr_abox A j (fun y hy => ihR i hi' y hy) x hx]
            rw [congr_fun (rInd_zero_ite A j (i ∈ S ∨ i ∈ T)
              (flatPieceRTList V A l' S T f)) x]

/-! ## 5. The pieces of the full slot enumeration -/

/-- Measurability and box-boundedness of a full flat piece of a continuous state. -/
theorem flatPieceRT_meas_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (S T : Finset (Fin N)) :
    Measurable (flatPieceRT V A S T Φ)
      ∧ ∃ C, ∀ x ∈ abox N ℓ, |flatPieceRT V A S T Φ x| ≤ C := by
  obtain ⟨C, _hC0, hC⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have h := flatPieceRTList_meas_bdd hℓ hV hA hVeq hAc (List.finRange N) S T
    hΦc.measurable ⟨C, hC⟩
  simpa [flatPieceRT] using h

/-- The eigen-relation for the full flat pieces, in pointwise-on-the-box form. -/
theorem flatPieceRT_eigen_box {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (S T : Finset (Fin N)) (hST : Disjoint S T)
    (i : Fin N) :
    (∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S T Φ) x
        = if i ∈ S then flatPieceRT V A S T Φ x else 0)
      ∧ (∀ x ∈ abox N ℓ, Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S T Φ) x
        = if i ∈ T then flatPieceRT V A S T Φ x else 0)
      ∧ (∀ x ∈ abox N ℓ, rInd A i (flatPieceRT V A S T Φ) x
        = if i ∈ S ∨ i ∈ T then 0 else flatPieceRT V A S T Φ x) := by
  obtain ⟨C, _hC0, hC⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  obtain ⟨h1, h2, h3⟩ := flatPieceRTList_eigen hℓ hV hA hVeq hAc (List.finRange N)
    (List.nodup_finRange N) S T hST hΦc.measurable ⟨C, hC⟩
  exact ⟨fun x hx => h1 i (List.mem_finRange i) x hx,
    fun x hx => h2 i (List.mem_finRange i) x hx,
    fun x hx => h3 i (List.mem_finRange i) x hx⟩

/-! ## 6. Orthogonality of the pieces -/

/-- Two distinct finite sets differ at some element. -/
theorem exists_mem_xor {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ≠ t) :
    ∃ a, (a ∈ s ∧ a ∉ t) ∨ (a ∈ t ∧ a ∉ s) := by
  by_contra hc
  have h1 : ∀ a, a ∈ s → a ∈ t := by
    intro a ha
    by_contra hat
    exact hc ⟨a, Or.inl ⟨ha, hat⟩⟩
  have h2 : ∀ a, a ∈ t → a ∈ s := by
    intro a ha
    by_contra has
    exact hc ⟨a, Or.inr ⟨ha, has⟩⟩
  exact h (Finset.ext fun a => ⟨h1 a, h2 a⟩)

/-- **Orthogonality, `P`-case**: a slot `i` which is in `S` but not in `S'`. -/
theorem flatPieceRT_orth_of_memP {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {S T S' T' : Finset (Fin N)} (hd : Disjoint S T) (hd' : Disjoint S' T') {i : Fin N}
    (hiS : i ∈ S) (hiS' : i ∉ S') :
    (∫ x in abox N ℓ,
        flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x) = 0 := by
  obtain ⟨hm1, C1, hC1⟩ := flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S T
  obtain ⟨hm2, C2, hC2⟩ := flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S' T'
  have hP2 := (flatPieceRT_eigen_box hℓ hV hA hVeq hAc hΦc S' T' hd' i).1
  have hP1 := (flatPieceRT_eigen_box hℓ hV hA hVeq hAc hΦc S T hd i).1
  have e1 : (∫ x in abox N ℓ,
        flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x)
      = ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S T Φ) x
          * flatPieceRT V A S' T' Φ x := by
    refine setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => ?_)
    show flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x
      = Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S T Φ) x * flatPieceRT V A S' T' Φ x
    rw [hP1 x hx, if_pos hiS]
  have e2 : (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S T Φ) x
        * flatPieceRT V A S' T' Φ x)
      = ∫ x in abox N ℓ, flatPieceRT V A S T Φ x
          * Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S' T' Φ) x :=
    Work.BoseFixB1S.boxPIndSelfAdjoint hℓ hV hA hVeq hAc i hm1 (CΦ := C1) hC1
      hm2 (CΨ := C2) hC2
  have e3 : (∫ x in abox N ℓ, flatPieceRT V A S T Φ x
        * Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S' T' Φ) x) = 0 := by
    rw [show (∫ x in abox N ℓ, flatPieceRT V A S T Φ x
          * Work.UBBInputs8.boxPInd V A i (flatPieceRT V A S' T' Φ) x)
        = ∫ _x in abox N ℓ, (0 : ℝ) from
      setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by
        rw [hP2 x hx, if_neg hiS', mul_zero])]
    simp
  rw [e1, e2, e3]

/-- **Orthogonality, `Q`-case**: a slot `i` which is in `T` but not in `T'`. -/
theorem flatPieceRT_orth_of_memQ {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {S T S' T' : Finset (Fin N)} (hd : Disjoint S T) (hd' : Disjoint S' T') {i : Fin N}
    (hiT : i ∈ T) (hiT' : i ∉ T') :
    (∫ x in abox N ℓ,
        flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x) = 0 := by
  obtain ⟨hm1, C1, hC1⟩ := flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S T
  obtain ⟨hm2, C2, hC2⟩ := flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc S' T'
  have hQ2 := (flatPieceRT_eigen_box hℓ hV hA hVeq hAc hΦc S' T' hd' i).2.1
  have hQ1 := (flatPieceRT_eigen_box hℓ hV hA hVeq hAc hΦc S T hd i).2.1
  have e1 : (∫ x in abox N ℓ,
        flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x)
      = ∫ x in abox N ℓ, Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S T Φ) x
          * flatPieceRT V A S' T' Φ x := by
    refine setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => ?_)
    show flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x
      = Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S T Φ) x * flatPieceRT V A S' T' Φ x
    rw [hQ1 x hx, if_pos hiT]
  have e2 : (∫ x in abox N ℓ, Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S T Φ) x
        * flatPieceRT V A S' T' Φ x)
      = ∫ x in abox N ℓ, flatPieceRT V A S T Φ x
          * Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S' T' Φ) x :=
    boxQInd_selfAdjoint_bdd hℓ hV hA hVeq hAc i hm1 (Cf := C1) hC1
      hm2 (Cg := C2) hC2
  have e3 : (∫ x in abox N ℓ, flatPieceRT V A S T Φ x
        * Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S' T' Φ) x) = 0 := by
    rw [show (∫ x in abox N ℓ, flatPieceRT V A S T Φ x
          * Work.UBBInputs8.boxQInd V A i (flatPieceRT V A S' T' Φ) x)
        = ∫ _x in abox N ℓ, (0 : ℝ) from
      setIntegral_congr_fun (abox_measurable N ℓ) (fun x hx => by
        rw [hQ2 x hx, if_neg hiT', mul_zero])]
    simp
  rw [e1, e2, e3]

/-- **Pairwise orthogonality of the `(P,Q,R)`-flat pieces.**  For two pairs `(S,T) ≠ (S',T')` of
disjoint slot sets (i.e. `T ⊆ Sᶜ`, `T' ⊆ S'ᶜ`) the pieces are orthogonal on the analysis box. -/
theorem flatPieceRT_orthogonal {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hVeq : V = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (S T S' T' : Finset (Fin N)) (hT : T ⊆ Sᶜ) (hT' : T' ⊆ S'ᶜ)
    (hne : (S, T) ≠ (S', T')) :
    (∫ x in abox N ℓ,
        flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x) = 0 := by
  have hd : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    exact (Finset.mem_compl.mp (hT hiT)) hiS
  have hd' : Disjoint S' T' := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    exact (Finset.mem_compl.mp (hT' hiT)) hiS
  have hcomm : (∫ x in abox N ℓ,
        flatPieceRT V A S T Φ x * flatPieceRT V A S' T' Φ x)
      = ∫ x in abox N ℓ,
          flatPieceRT V A S' T' Φ x * flatPieceRT V A S T Φ x :=
    setIntegral_congr_fun (abox_measurable N ℓ) (fun x _ => mul_comm _ _)
  by_cases hSS : S = S'
  · have hTT : T ≠ T' := fun h => hne (Prod.ext hSS h)
    obtain ⟨i, hi | hi⟩ := exists_mem_xor hTT
    · exact flatPieceRT_orth_of_memQ hℓ hV hA hVeq hAc hΦc hd hd' hi.1 hi.2
    · rw [hcomm]
      exact flatPieceRT_orth_of_memQ hℓ hV hA hVeq hAc hΦc hd' hd hi.1 hi.2
  · obtain ⟨i, hi | hi⟩ := exists_mem_xor hSS
    · exact flatPieceRT_orth_of_memP hℓ hV hA hVeq hAc hΦc hd hd' hi.1 hi.2
    · rw [hcomm]
      exact flatPieceRT_orth_of_memP hℓ hV hA hVeq hAc hΦc hd' hd hi.1 hi.2

end Work.BoseFixB1

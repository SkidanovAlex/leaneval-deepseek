import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.jointProj_orthogonal`

The joint sector projections `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j` of two **different**
sectors are orthogonal in `L²(abox n ℓ)`:

    ∫_{abox n ℓ} (E_S Φ)(x) · (E_T Ψ)(x) dx = 0      if `S ∩ {0..n−1} ≠ T ∩ {0..n−1}`.

This is the projection algebra of FS §6 (`lem:LocMatrices`, `final_v2.tex`
ll. 1365–1445): the sectors `1_{n₊=k}` are mutually orthogonal because they are
built from the orthogonal slot projections `Pᵢ, Qᵢ = 1 − Pᵢ`.

## The argument

Let `k < n` be a slot in which the two sectors differ, say `k ∈ S`, `k ∉ T`.
The recursion `blockOp` applies, for each slot `j = 0,1,…,n−1`, the operator
`Q_j` (if `j ∈ S`) or `P_j` (if `j ∉ S`); operators of *different* slots commute
(`aP_comm`, `aP_aQ_comm`, `aQ_comm`) and each operator is linear.  Hence

* on the `S` side the factor `Q_k` survives every move of `P_k` past the
  remaining slot operators and `P_k Q_k = 0`, so `P_k (E_S Φ) = 0`;
* on the `T` side we move `P_k` inwards onto its own slot, where it is a mean,
  so `E_T Ψ` does not depend on the `k`-th configuration variable and
  `P_k (E_T Ψ) = E_T Ψ`.

Self-adjointness of `P_k` over the box (`aP_sym_box`) then gives

    ∫ (E_S Φ)(E_T Ψ) = ∫ (P_k E_S Φ)(E_T Ψ) = ∫ (E_S Φ)(P_k E_T Ψ) = 0.

The two inductions are carried out on the number of slots processed; the
predicates `ConstIn` (does not depend on the `k`-th variable) and
`aP ℓ k F = 0` are preserved by every operator of another slot.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseFixB2.Sector

open Submission.BoseGases Work.BoseFixB2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The two invariant predicates

`ConstIn k F` says that `F : X n → ℝ` does not depend on the `k`-th slot.  The
other invariant used below is simply `aP ℓ k F = 0`. -/

/-- `F` does not depend on the `k`-th slot. -/
def ConstIn {n : ℕ} (k : Fin n) (F : X n → ℝ) : Prop :=
  ∀ (x : X n) (z : EuclideanSpace ℝ (Fin 3)), F (Function.update x k z) = F x

/-! ## 2. Elementary slot algebra -/

/-- The mean operator applied to the zero function. -/
lemma aP_apply_zero {ℓ : ℝ} {n : ℕ} (i : Fin n) : aP ℓ i (0 : X n → ℝ) = 0 := by
  funext x
  unfold aP
  simp

/-- The complement operator applied to the zero function. -/
lemma aQ_apply_zero {ℓ : ℝ} {n : ℕ} (i : Fin n) : aQ ℓ i (0 : X n → ℝ) = 0 := by
  funext x
  unfold aQ
  simp [aP_apply_zero i]

/-- `Pₖ` fixes every function that does not depend on the `k`-th slot. -/
lemma aP_of_constIn {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (k : Fin n)
    {F : X n → ℝ} (hF : ConstIn k F) : aP ℓ k F = F := by
  funext x
  calc aP ℓ k F x = (1 / ℓ ^ 3) * (∫ y in acube ℓ, F x) := by
        unfold aP
        congr 1
        apply integral_congr_ae
        filter_upwards with y
        exact hF x y
    _ = F x := by
        rw [integral_const_acube ℓ hℓ]
        field_simp [ne_of_gt hℓ]

/-- Constancy in the slot `i` is preserved by the mean operator in another slot. -/
lemma constIn_aP {ℓ : ℝ} {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {F : X n → ℝ} (hF : ConstIn i F) : ConstIn i (aP ℓ j F) := by
  intro x z
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Function.update_comm hij z y x]
  exact hF (Function.update x j y) z

/-- Constancy in the slot `i` is preserved by the complement operator in another
slot. -/
lemma constIn_aQ {ℓ : ℝ} {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {F : X n → ℝ} (hF : ConstIn i F) : ConstIn i (aQ ℓ j F) := by
  intro x z
  unfold aQ
  rw [hF x z, constIn_aP hij hF x z]

/-! ## 3. `Pₖ` commutes past the operators of another slot

These are the "pull-out" facts used in the induction below: if `PₖF = 0` then
`Pₖ` kills the output of any operator sitting in a slot `≠ k`. -/

/-- `Pᵢ` kills `Pⱼ`-outputs of functions it kills (the operators commute). -/
lemma aP_aP_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {i j : Fin n} {F : X n → ℝ}
    (hF : Continuous F) (h0 : aP ℓ i F = 0) : aP ℓ i (aP ℓ j F) = 0 := by
  funext x
  rw [aP_comm hℓ i j hF x, h0]
  exact congrFun (aP_apply_zero j) x

/-- `Pᵢ` kills `Qⱼ`-outputs of functions it kills (`i ≠ j`). -/
lemma aP_aQ_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {F : X n → ℝ} (hF : Continuous F) (h0 : aP ℓ i F = 0) : aP ℓ i (aQ ℓ j F) = 0 := by
  funext x
  rw [aP_aQ_comm hℓ hij hF x, h0]
  exact congrFun (aQ_apply_zero j) x

/-- The mean operator annihilates its own complement: `PₖQₖ = 0`. -/
lemma aP_aQ_self_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (k : Fin n) {F : X n → ℝ}
    (hF : Continuous F) : aP ℓ k (aQ ℓ k F) = 0 := by
  funext x
  have hc : Continuous (aP ℓ k F) := aP_continuous hℓ k hF
  have hfun : aQ ℓ k F = F - aP ℓ k F := rfl
  rw [hfun, aP_sub hℓ k hF hc x, aP_idem hℓ k hF x]
  simp

/-! ## 4. Continuity of the partial products -/

/-- Every partial product `blockOp ℓ S m Φ` (`m ≤ n`) of continuous slot
operators applied to a continuous state is continuous. -/
lemma blockOp_continuous_local {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (S : Finset ℕ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) : ∀ m, m ≤ n → Continuous (blockOp ℓ S m Φ) := by
  intro m
  induction m with
  | zero => intro _; simpa using hΦ
  | succ m ih =>
    intro hmn
    have hmn' : m < n := hmn
    rw [blockOp_succ S hmn' Φ]
    by_cases hmS : m ∈ S
    · rw [if_pos hmS]; exact aQ_continuous hℓ ⟨m, hmn'⟩ (ih (Nat.le_of_lt hmn'))
    · rw [if_neg hmS]; exact aP_continuous hℓ ⟨m, hmn'⟩ (ih (Nat.le_of_lt hmn'))

/-- `jointProj ℓ S Φ` is continuous for continuous `Φ`. -/
lemma jointProj_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (S : Finset ℕ) {Φ : X n → ℝ}
    (hΦ : Continuous Φ) : Continuous (jointProj ℓ S Φ) :=
  blockOp_continuous_local hℓ S hΦ n le_rfl

/-! ## 5. Slot `k` of a product: `Pₖ E_S Φ = 0` for `k ∈ S`

Induction on the number `m` of slots processed.  As soon as the slot `k` itself
has been processed (at step `k+1`, contributing the factor `Q_k` because
`k ∈ S`), the mean `Pₖ` vanishes and stays zero: every later operator sits in a
slot `≠ k` and therefore commutes with `Pₖ`. -/

lemma aP_blockOp_eq_zero_gen {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {k : ℕ}
    (hk : k < n) (hkS : k ∈ S) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    ∀ m, k < m → m ≤ n → aP ℓ ⟨k, hk⟩ (blockOp ℓ S m Φ) = 0 := by
  intro m
  induction m with
  | zero => intro h1 h2; omega
  | succ m ih =>
    intro hkm hmn
    have hmn' : m < n := hmn
    have hkm' : k ≤ m := Nat.lt_succ_iff.mp hkm
    rw [blockOp_succ S hmn' Φ]
    rcases lt_or_eq_of_le hkm' with hlt | heq
    · -- slot `m ≠ k`: pull `Pₖ` inwards and use the induction hypothesis
      have hne : (⟨k, hk⟩ : Fin n) ≠ ⟨m, hmn'⟩ := by
        intro hcon; have := congrArg Fin.val hcon; simp at this; omega
      have hcont := blockOp_continuous_local hℓ S hΦ m (Nat.le_of_lt hmn')
      have ih' := ih hlt (Nat.le_of_lt hmn')
      by_cases hmS : m ∈ S
      · rw [if_pos hmS]
        exact aP_aQ_eq_zero hℓ (i := ⟨k, hk⟩) (j := ⟨m, hmn'⟩) hne hcont ih'
      · rw [if_neg hmS]
        exact aP_aP_eq_zero hℓ hcont ih'
    · -- slot `m = k`: this step contributes `Q_k`, which `Pₖ` annihilates
      rw [show (⟨m, hmn'⟩ : Fin n) = ⟨k, hk⟩ from Fin.ext heq.symm]
      rw [if_pos (heq ▸ hkS)]
      exact aP_aQ_self_eq_zero hℓ ⟨k, hk⟩
        (blockOp_continuous_local hℓ S hΦ m (Nat.le_of_lt hmn'))

/-- **The slot-`k` mean of the sector `S` vanishes** for `k ∈ S`, `k < n`. -/
lemma aP_blockOp_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {k : ℕ}
    (hk : k < n) (hkS : k ∈ S) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    aP ℓ ⟨k, hk⟩ (jointProj ℓ S Φ) = 0 :=
  aP_blockOp_eq_zero_gen hℓ hk hkS hΦ n hk le_rfl

/-! ## 6. Slot `k` of a product: `Pₖ E_T Ψ = E_T Ψ` for `k ∉ T`

Here the slot `k` carries the *mean* `P_k`; from step `k+1` on, the state no
longer depends on the `k`-th configuration variable, and every later operator
sits in another slot and preserves that independence. -/

lemma constIn_blockOp_gen {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {T : Finset ℕ} {k : ℕ}
    (hk : k < n) (hkT : k ∉ T) {Ψ : X n → ℝ} (hΨ : Continuous Ψ) :
    ∀ m, k < m → m ≤ n → ConstIn ⟨k, hk⟩ (blockOp ℓ T m Ψ) := by
  intro m
  induction m with
  | zero => intro h1 h2; omega
  | succ m ih =>
    intro hkm hmn
    have hmn' : m < n := hmn
    have hkm' : k ≤ m := Nat.lt_succ_iff.mp hkm
    rw [blockOp_succ T hmn' Ψ]
    rcases lt_or_eq_of_le hkm' with hlt | heq
    · -- slot `m ≠ k`: the operators of another slot preserve independence
      have hne : (⟨k, hk⟩ : Fin n) ≠ ⟨m, hmn'⟩ := by
        intro hcon; have := congrArg Fin.val hcon; simp at this; omega
      have ih' := ih hlt (Nat.le_of_lt hmn')
      by_cases hmT : m ∈ T
      · rw [if_pos hmT]
        exact constIn_aQ (i := ⟨k, hk⟩) (j := ⟨m, hmn'⟩) hne ih'
      · rw [if_neg hmT]
        exact constIn_aP (i := ⟨k, hk⟩) (j := ⟨m, hmn'⟩) hne ih'
    · -- slot `m = k`: this step contributes the mean `P_k`
      rw [show (⟨m, hmn'⟩ : Fin n) = ⟨k, hk⟩ from Fin.ext heq.symm]
      rw [if_neg (heq ▸ hkT)]
      exact aP_const_in_coord hℓ ⟨k, hk⟩
        (blockOp_continuous_local hℓ T hΨ m (Nat.le_of_lt hmn'))

/-- Independence of the sector `T` from the slot `k`, for `k ∉ T`. -/
lemma constIn_jointProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {T : Finset ℕ} {k : ℕ}
    (hk : k < n) (hkT : k ∉ T) {Ψ : X n → ℝ} (hΨ : Continuous Ψ) :
    ConstIn ⟨k, hk⟩ (jointProj ℓ T Ψ) :=
  constIn_blockOp_gen hℓ hk hkT hΨ n hk le_rfl

/-- **`Pₖ` fixes the sector `T` pointwise** when `k ∉ T`. -/
lemma aP_jointProj_eq_self {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {T : Finset ℕ} {k : ℕ}
    (hk : k < n) (hkT : k ∉ T) {Ψ : X n → ℝ} (hΨ : Continuous Ψ) :
    aP ℓ ⟨k, hk⟩ (jointProj ℓ T Ψ) = jointProj ℓ T Ψ :=
  aP_of_constIn hℓ ⟨k, hk⟩ (constIn_jointProj hℓ hk hkT hΨ)

/-! ## 7. Orthogonality -/

theorem jointProj_orthogonal {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S T : Finset ℕ} (hST : S ∩ Finset.range n ≠ T ∩ Finset.range n) (Φ Ψ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ) (hΨ : Continuous Ψ) : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseFixB2.jointProj ℓ S Φ x * Work.BoseFixB2.jointProj ℓ T Ψ x) = 0 := by
  -- a slot `< n` in which the two sectors differ
  obtain ⟨k, hk⟩ : ∃ k, (k ∈ S ∩ Finset.range n ∧ k ∉ T ∩ Finset.range n) ∨
      (k ∈ T ∩ Finset.range n ∧ k ∉ S ∩ Finset.range n) := by
    by_contra h
    push Not at h
    exact hST (Finset.ext fun k => ⟨fun hk => (h k).1 hk, fun hk => (h k).2 hk⟩)
  have hkn : k < n := by
    rcases hk with h | h
    · exact Finset.mem_range.mp (Finset.mem_inter.mp h.1).2
    · exact Finset.mem_range.mp (Finset.mem_inter.mp h.1).2
  have hmem : (k ∈ S ∧ k ∉ T) ∨ (k ∈ T ∧ k ∉ S) := by
    rcases hk with h | h
    · exact Or.inl ⟨(Finset.mem_inter.mp h.1).1,
        fun hc => h.2 (Finset.mem_inter.mpr ⟨hc, Finset.mem_range.mpr hkn⟩)⟩
    · exact Or.inr ⟨(Finset.mem_inter.mp h.1).1,
        fun hc => h.2 (Finset.mem_inter.mpr ⟨hc, Finset.mem_range.mpr hkn⟩)⟩
  have hsym := aP_sym_box (N := n) hℓ (⟨k, hkn⟩ : Fin n)
    (jointProj_continuous hℓ S hΦ) (jointProj_continuous hℓ T hΨ)
  rcases hmem with ⟨hkS, hkT⟩ | ⟨hkT, hkS⟩
  · -- `k ∈ S`, `k ∉ T`: `Pₖ` kills the `S`-sector and fixes the `T`-sector
    rw [aP_blockOp_eq_zero hℓ hkn hkS hΦ,
      aP_jointProj_eq_self hℓ hkn hkT hΨ] at hsym
    simpa using hsym.symm
  · -- `k ∈ T`, `k ∉ S`: `Pₖ` fixes the `S`-sector and kills the `T`-sector
    rw [aP_jointProj_eq_self hℓ hkn hkS hΦ,
      aP_blockOp_eq_zero hℓ hkn hkT hΨ] at hsym
    simpa using hsym

end Work.BoseFixB2.Sector

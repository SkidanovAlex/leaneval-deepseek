import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.NormAux
import Submission.Work.NN.Newton.Defect.vecHolder_A_evec
import Submission.Work.NN.Newton.Defect.holderNorm_LD_field_fixed
import Submission.Work.NN.Newton.Defect.holderNorm_A_LD_fixed
import Submission.Work.NN.Newton.Defect.holderNorm_LD_field_field

/-!
# A `C^{0,α}` bound for the quadratic `∂̄`-defect `TA` of the coordinate datum

`TA A z l j k` is the ten-term "quadratic" remainder of the integrability identity for the
coordinate datum (see `Work.NN.Newton.DefectDefs`).  Every term is a product of at most two
factors, each of which is either an entry of `A z` or of `fderiv ℝ A z`; under the
`C^{1,α}`-smallness hypothesis `CVBound A α a P` on the polydisc `P = polydiscR n r` each of the
ten terms therefore has `C^{0,α}`-norm at most `4 a²`, and the ten-term sum is at most
`40 a² ≤ 100 a²`.

Each of the ten terms has one of three shapes, and the corresponding bound is the content of a
sibling module:

* `λ_l((DA_z X_z) Y)` with `X_z = A z e_m` a `C^{0,α}`-small field and `‖Y‖ ≤ 1`
  (`holderNorm_LD_field_fixed`) — this covers the terms involving `LD A z l (A z e_j) Y`;
* `λ_l(A z ((DA_z X) Y))` with `X, Y` unit vectors (`holderNorm_A_LD_fixed`) — the terms
  involving `lamC l (A z (LDv A z X Y))`;
* `λ_l((DA_z X_z) Y_z)` with `X, Y` both columns of `A` (`holderNorm_LD_field_field`) — the two
  quadratic terms `LD A z l (A z e_j) (A z e_k)`.

The ten functions are collected, in order, in the list `ta_TAterms`; subadditivity of
`holderNorm 0 α` over a list (`Work.NN.Newton.holderNorm_zero_list_sum_le`) produces the sum of
the ten individual bounds, and `10 * (4 a²) = 40 a² ≤ 100 a²` closes the estimate.
-/

namespace Work.NN.Newton.Defect

open scoped ENNReal
open Set

noncomputable section

/-! ### Elementary tools -/

/-- Multiplication by a unit complex number does not increase the `C^{0,α}`-norm at order `0`. -/
private lemma ta_holderNorm_zero_unit_mul_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} {c : ℂ} (hc : ‖c‖ = 1) {f : X → ℂ} {Ω : Set X} :
    Work.CR.Flat.holderNorm 0 α (fun z => c * f z) Ω ≤ Work.CR.Flat.holderNorm 0 α f Ω := by
  have h := Work.NN.Newton.holderNorm_zero_const_mul_le (α := α) (c := c) (f := f) (Ω := Ω)
  rwa [hc, ENNReal.ofReal_one, one_mul] at h

/-- Subadditivity of the `C^{0,α}`-norm at order `0` over a list of functions, with the
explicit constant `length · c`. -/
private lemma ta_list_sum_holderNorm_zero_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} {Ω : Set X} {c : ℝ≥0∞} (L : List (X → ℂ))
    (h : ∀ g ∈ L, Work.CR.Flat.holderNorm 0 α g Ω ≤ c) :
    (L.map (fun g => Work.CR.Flat.holderNorm 0 α g Ω)).sum ≤ (L.length : ℝ≥0∞) * c := by
  induction L with
  | nil => simp
  | cons g t ih =>
      have hg : Work.CR.Flat.holderNorm 0 α g Ω ≤ c := h g (by simp)
      have ht : (t.map (fun f => Work.CR.Flat.holderNorm 0 α f Ω)).sum
          ≤ (t.length : ℝ≥0∞) * c := ih (fun f hf => h f (by simp [hf]))
      show Work.CR.Flat.holderNorm 0 α g Ω
            + (t.map (fun f => Work.CR.Flat.holderNorm 0 α f Ω)).sum
          ≤ ((g :: t).length : ℝ≥0∞) * c
      rw [List.length_cons]
      calc Work.CR.Flat.holderNorm 0 α g Ω
            + (t.map (fun f => Work.CR.Flat.holderNorm 0 α f Ω)).sum
          ≤ c + (t.length : ℝ≥0∞) * c := add_le_add hg ht
        _ = ((t.length : ℝ≥0∞) + 1) * c := by rw [add_mul, one_mul, add_comm]
        _ = ((t.length + 1 : ℕ) : ℝ≥0∞) * c := by rw [Nat.cast_add, Nat.cast_one]

private lemma ta_norm_evec_le {n : ℕ} (i : Fin n) : ‖evec i‖ ≤ 1 := by
  rw [evec, Pi.norm_single]
  norm_num

private lemma ta_norm_ievec_le {n : ℕ} (i : Fin n) : ‖ievec i‖ ≤ 1 := by
  rw [ievec, Pi.norm_single, Complex.norm_I]

/-! ### The three term-level bounds -/

/-- Bound for the terms `λ_l((DA_z X_z) Y)` with `X` a `C^{0,α}`-small field, `c` a unit scalar. -/
private lemma ta_bound_LD_field {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ContDiffOn ℝ 1 A (polydiscR n r)) (hA : CVBound A α a (polydiscR n r))
    {c : ℂ} (hc : ‖c‖ = 1) {X : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hX : Work.NN.Final.VecHolder X α a (polydiscR n r))
    {Y : Work.NN.Core.Cn n} (hY : ‖Y‖ ≤ 1) (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => c * LD A z l (X z) Y) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
  calc Work.CR.Flat.holderNorm 0 α (fun z => c * LD A z l (X z) Y) (polydiscR n r)
      ≤ Work.CR.Flat.holderNorm 0 α (fun z => LD A z l (X z) Y) (polydiscR n r) :=
        ta_holderNorm_zero_unit_mul_le (f := fun z => LD A z l (X z) Y) hc
    _ ≤ ENNReal.ofReal (4 * a ^ 2) :=
        holderNorm_LD_field_fixed A hα0 (le_of_lt hα1) hr ha0 ha1 hAc hA hX hY l

/-- Bound for the terms `λ_l(A z ((DA_z X) Y))` with `X`, `Y` unit vectors, `c` a unit scalar. -/
private lemma ta_bound_A_LD {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ContDiffOn ℝ 1 A (polydiscR n r)) (hA : CVBound A α a (polydiscR n r))
    {c : ℂ} (hc : ‖c‖ = 1) {X Y : Work.NN.Core.Cn n} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1)
    (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => c * lamC l (A z ((fderiv ℝ A z X) Y)))
        (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
  (ta_holderNorm_zero_unit_mul_le
      (f := fun z => lamC l (A z ((fderiv ℝ A z X) Y))) hc).trans
    (holderNorm_A_LD_fixed A hα0 (le_of_lt hα1) hr ha0 ha1 hAc hA hX hY l)

/-- Bound for the terms `λ_l((DA_z X_z) Y_z)` with `X`, `Y` columns of `A`, `c` a unit scalar. -/
private lemma ta_bound_LD_field_field {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ContDiffOn ℝ 1 A (polydiscR n r)) (hA : CVBound A α a (polydiscR n r))
    {c : ℂ} (hc : ‖c‖ = 1)
    {X Y : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hX : Work.NN.Final.VecHolder X α a (polydiscR n r))
    (hY : Work.NN.Final.VecHolder Y α a (polydiscR n r)) (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => c * LD A z l (X z) (Y z)) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
  calc Work.CR.Flat.holderNorm 0 α (fun z => c * LD A z l (X z) (Y z)) (polydiscR n r)
      ≤ Work.CR.Flat.holderNorm 0 α (fun z => LD A z l (X z) (Y z)) (polydiscR n r) :=
        ta_holderNorm_zero_unit_mul_le (f := fun z => LD A z l (X z) (Y z)) hc
    _ ≤ ENNReal.ofReal (4 * a ^ 2) :=
        holderNorm_LD_field_field A hα0 (le_of_lt hα1) hr ha0 ha1 hAc hA hX hY l

/-! ### The ten terms of `TA` -/

/-- The ten terms of `TA`, in order, each written as a unit multiple of one of the three
elementary shapes. -/
private def ta_TAterms {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l j k : Fin n) :
    List (Work.NN.Core.Cn n → ℂ) :=
  [ (fun z => Complex.I * LD A z l (A z (evec j)) (evec k)),
    (fun z => Complex.I * lamC l (A z (LDv A z (evec k) (evec j)))),
    (fun z => (-Complex.I) * lamC l (A z (LDv A z (evec j) (evec k)))),
    (fun z => (-Complex.I) * LD A z l (A z (evec k)) (evec j)),
    (fun z => (1 : ℂ) * lamC l (A z (LDv A z (ievec j) (evec k)))),
    (fun z => (-1 : ℂ) * LD A z l (A z (evec j)) (ievec k)),
    (fun z => (-1 : ℂ) * LD A z l (A z (evec j)) (A z (evec k))),
    (fun z => (-1 : ℂ) * lamC l (A z (LDv A z (ievec k) (evec j)))),
    (fun z => (1 : ℂ) * LD A z l (A z (evec k)) (ievec j)),
    (fun z => (1 : ℂ) * LD A z l (A z (evec k)) (A z (evec j))) ]

private lemma ta_TAterms_length {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l j k : Fin n) :
    (ta_TAterms A l j k).length = 10 := rfl

private lemma ta_TA_eq_terms {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (l j k : Fin n) :
    (fun z => TA A z l j k) = fun z => ((ta_TAterms A l j k).map (fun f => f z)).sum := by
  funext z
  simp only [TA, ta_TAterms, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
  ring

/-! ### The main bound -/

theorem holderNorm_TA {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r)) (l j k : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Newton.TA A z l j k)
      (Work.NN.Newton.polydiscR n r) ≤ ENNReal.ofReal (100 * a ^ 2) := by
  have hAc1 : ContDiffOn ℝ 1 A (polydiscR n r) := hAc 1
  have hcol : ∀ m : Fin n,
      Work.NN.Final.VecHolder (fun z => A z (evec m)) α a (polydiscR n r) :=
    fun m => vecHolder_A_evec A ha0 hA m
  -- the ten individual bounds
  have hb1 : Work.CR.Flat.holderNorm 0 α
      (fun z => Complex.I * LD A z l (A z (evec j)) (evec k)) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_LD_field A hα0 hα1 hr ha0 ha1 hAc1 hA (c := Complex.I) (by simp [Complex.norm_I])
      (hcol j) (ta_norm_evec_le k) l
  have hb2 : Work.CR.Flat.holderNorm 0 α
      (fun z => Complex.I * lamC l (A z (LDv A z (evec k) (evec j)))) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_A_LD A hα0 hα1 hr ha0 ha1 hAc1 hA (c := Complex.I)
      (by simp [Complex.norm_I]) (ta_norm_evec_le k) (ta_norm_evec_le j) l
  have hb3 : Work.CR.Flat.holderNorm 0 α
      (fun z => (-Complex.I) * lamC l (A z (LDv A z (evec j) (evec k)))) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_A_LD A hα0 hα1 hr ha0 ha1 hAc1 hA (c := -Complex.I)
      (by simp [Complex.norm_I]) (ta_norm_evec_le j) (ta_norm_evec_le k) l
  have hb4 : Work.CR.Flat.holderNorm 0 α
      (fun z => (-Complex.I) * LD A z l (A z (evec k)) (evec j)) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_LD_field A hα0 hα1 hr ha0 ha1 hAc1 hA (c := -Complex.I)
      (by simp [Complex.norm_I]) (hcol k) (ta_norm_evec_le j) l
  have hb5 : Work.CR.Flat.holderNorm 0 α
      (fun z => (1 : ℂ) * lamC l (A z (LDv A z (ievec j) (evec k)))) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_A_LD A hα0 hα1 hr ha0 ha1 hAc1 hA (c := 1) (by simp)
      (ta_norm_ievec_le j) (ta_norm_evec_le k) l
  have hb6 : Work.CR.Flat.holderNorm 0 α
      (fun z => (-1 : ℂ) * LD A z l (A z (evec j)) (ievec k)) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_LD_field A hα0 hα1 hr ha0 ha1 hAc1 hA (c := -1) (by simp)
      (hcol j) (ta_norm_ievec_le k) l
  have hb7 : Work.CR.Flat.holderNorm 0 α
      (fun z => (-1 : ℂ) * LD A z l (A z (evec j)) (A z (evec k))) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_LD_field_field A hα0 hα1 hr ha0 ha1 hAc1 hA (c := -1) (by simp)
      (hcol j) (hcol k) l
  have hb8 : Work.CR.Flat.holderNorm 0 α
      (fun z => (-1 : ℂ) * lamC l (A z (LDv A z (ievec k) (evec j)))) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_A_LD A hα0 hα1 hr ha0 ha1 hAc1 hA (c := -1) (by simp)
      (ta_norm_ievec_le k) (ta_norm_evec_le j) l
  have hb9 : Work.CR.Flat.holderNorm 0 α
      (fun z => (1 : ℂ) * LD A z l (A z (evec k)) (ievec j)) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_LD_field A hα0 hα1 hr ha0 ha1 hAc1 hA (c := 1) (by simp)
      (hcol k) (ta_norm_ievec_le j) l
  have hb10 : Work.CR.Flat.holderNorm 0 α
      (fun z => (1 : ℂ) * LD A z l (A z (evec k)) (A z (evec j))) (polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) :=
    ta_bound_LD_field_field A hα0 hα1 hr ha0 ha1 hAc1 hA (c := 1) (by simp)
      (hcol k) (hcol j) l
  rw [ta_TA_eq_terms A l j k]
  refine le_trans (Work.NN.Newton.holderNorm_zero_list_sum_le (ta_TAterms A l j k)
    (polydiscR n r)) ?_
  refine le_trans (ta_list_sum_holderNorm_zero_le
    (c := ENNReal.ofReal (4 * a ^ 2)) (ta_TAterms A l j k) ?_) ?_
  · intro g hg
    simp only [ta_TAterms, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hb1
    · exact hb2
    · exact hb3
    · exact hb4
    · exact hb5
    · exact hb6
    · exact hb7
    · exact hb8
    · exact hb9
    · exact hb10
  · rw [ta_TAterms_length A l j k]
    rw [show (↑(10 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (4 * a ^ 2)
        = ENNReal.ofReal (40 * a ^ 2) from by
      rw [show (↑(10 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (10 : ℝ)
            from (ENNReal.ofReal_natCast 10).symm,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
      congr 1
      ring]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg a])

end

end Work.NN.Newton.Defect

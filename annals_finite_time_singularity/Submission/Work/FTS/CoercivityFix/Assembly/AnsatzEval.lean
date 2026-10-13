/-
# `Assembly/AnsatzEval.lean` — the slot evaluation of the `ℋ^k`-form for a product

For a product `f z θ = ψ z · g θ` every slot of the `ℋ^k`-integrand of `f` factors as a
function of `z` times a function of `θ`:

* the radial slot `i` is `(vzIter i ψ z · w z)² · (g θ)² sin(2θ)^{-η}`,
* the mixed slot `(i,j)` (with `1 ≤ i`, `i + j ≤ k`) is
  `(vzIter j ψ z · w z)² · (vthIter i g θ)² sin(2θ)^{-γ(α)}`.

Packaging the slots as a family over `ℕ ⊕ (ℕ × ℕ)` (`SlotS`, `SlotU`, `SlotV`) lets the
iterated integral be evaluated by `sum_prod_iterated` *without any integral-linearity side
condition*, since each slot is integrable by hypothesis.  The result is the *triangular* form

`HkSq α k (ψ·g) = HkSqForm α k ψ g
  = (∑_{i≤k} Zc ψ i)·Sc g 0 η + ∑_{i≤k} [1 ≤ i] (∑_{j≤k-i} Zc ψ j)·Sc g i γ(α)`,

in which the *level shift* `k ↦ k+1` together with `g ↦ vthIter 1 g` is an elementary index
shift (`triaMP_shift`): the level-`(k+1)` mixed sum is the level-`k` one plus the `i = 1` row.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Powers of the angular weight -/

/-- `(s^{a/2})² = s^a` for `s ≥ 0` (the degenerate case `s = 0` is consistent with Lean's
`rpow` convention). -/
theorem rpow_half_sq (a s : ℝ) (hs : 0 ≤ s) : (s ^ (a / 2)) ^ 2 = s ^ a := by
  have h2 : (s ^ (a / 2)) ^ ((2 : ℕ) : ℝ) = s ^ a := by
    rw [← Real.rpow_mul hs (a / 2) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring
  rwa [Real.rpow_natCast] at h2

/-- The light-weight square: `(w / s^{a/2})² = w² s^{-a}`. -/
theorem div_rpow_half_sq (a w s : ℝ) (hs : 0 ≤ s) :
    (w / s ^ (a / 2)) ^ 2 = w ^ 2 * s ^ (-a) := by
  rw [div_pow, rpow_half_sq a s hs, div_eq_mul_inv, ← Real.rpow_neg hs a]

/-- The heavy-weight square: `(x · (w s^{-c/2}))² = x² w² s^{-c}`. -/
theorem mul_rpow_half_sq (c x w s : ℝ) (hs : 0 ≤ s) :
    (x * (w * s ^ (-(c / 2)))) ^ 2 = x ^ 2 * (w ^ 2 * s ^ (-c)) := by
  have h : (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
    have hh : ((s ^ ((-c) / 2)) ^ 2 : ℝ) = s ^ (-c) := rpow_half_sq (-c) s hs
    rwa [neg_div] at hh
  rw [mul_pow, mul_pow, h]

/-! ## The slot index set and the slot families -/

/-- The slot index set of the `ℋ^k`-integrand of a product: the radial slots `Sum.inl i`
(`i ≤ k`) and the mixed slots `Sum.inr (i,j)` (`i,j ≤ k`). -/
def SlotS (k : ℕ) : Finset (ℕ ⊕ (ℕ × ℕ)) :=
  (Finset.range (k + 1)).disjSum ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)))

/-- The `z`-factor of a slot. -/
noncomputable def SlotU (ψ : ℝ → ℝ) (k : ℕ) (p : ℕ ⊕ (ℕ × ℕ)) : ℝ → ℝ :=
  p.elim (fun i => fun z => (vzIter i ψ z * Work.Spaces.w z) ^ 2)
    (fun q => fun z =>
      if 1 ≤ q.1 ∧ q.1 + q.2 ≤ k then (vzIter q.2 ψ z * Work.Spaces.w z) ^ 2 else 0)

/-- The `θ`-factor of a slot. -/
noncomputable def SlotV (α : ℝ) (g : ℝ → ℝ) (p : ℕ ⊕ (ℕ × ℕ)) : ℝ → ℝ :=
  p.elim (fun _ => fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (fun q => fun θ => (vthIter q.1 g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))

@[simp] theorem SlotU_inl (ψ : ℝ → ℝ) (k i : ℕ) (z : ℝ) :
    SlotU ψ k (Sum.inl i) z = (vzIter i ψ z * Work.Spaces.w z) ^ 2 := rfl

@[simp] theorem SlotU_inr (ψ : ℝ → ℝ) (k : ℕ) (q : ℕ × ℕ) (z : ℝ) :
    SlotU ψ k (Sum.inr q) z
      = if 1 ≤ q.1 ∧ q.1 + q.2 ≤ k then (vzIter q.2 ψ z * Work.Spaces.w z) ^ 2 else 0 := rfl

@[simp] theorem SlotV_inl (α : ℝ) (g : ℝ → ℝ) (i : ℕ) (θ : ℝ) :
    SlotV α g (Sum.inl i) θ = (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

@[simp] theorem SlotV_inr (α : ℝ) (g : ℝ → ℝ) (q : ℕ × ℕ) (θ : ℝ) :
    SlotV α g (Sum.inr q) θ
      = (vthIter q.1 g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl

/-! ## The product-sum iterated integral -/

/-- Iterated integral of a finite sum of products, the two factors being integrable on
`Iz` resp. `Iθ`: the integral factors slot by slot.  (No Fubini is needed: the `θ`-integral
of each summand is a constant times the value of the `z`-factor.) -/
theorem sum_prod_iterated {ι : Type*} (s : Finset ι) (u v : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, IntegrableOn (u i) Work.Spaces.Iz)
    (hv : ∀ i ∈ s, IntegrableOn (v i) Work.Spaces.Iθ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, u i z * v i θ)
      = ∑ i ∈ s, (∫ z in Work.Spaces.Iz, u i z) * (∫ θ in Work.Spaces.Iθ, v i θ) := by
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, u i z * v i θ)
      = ∑ i ∈ s, u i z * (∫ θ in Work.Spaces.Iθ, v i θ) := by
    intro z
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by rw [MeasureTheory.integral_const_mul]
    · intro i hi
      exact (hv i hi).const_mul _
  have key : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, u i z * v i θ)
      = ∫ z in Work.Spaces.Iz, ∑ i ∈ s, u i z * (∫ θ in Work.Spaces.Iθ, v i θ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici ?_
    intro z _
    exact hinner z
  rw [key, MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => by rw [MeasureTheory.integral_mul_const]
  · intro i hi
    exact (hu i hi).mul_const _

/-! ## The pointwise expansion of the `ℋ^k`-integrand -/

/-- **The `ℋ^k`-integrand of a product is a sum of products of one-variable functions.** -/
theorem HkIntegrand_slots (α : ℝ) (k : ℕ) (ψ g : ℝ → ℝ)
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ)
    (hg : ContDiff ℝ Work.Stability.smoothOrder g) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => ψ z * g θ) z θ
      = ∑ p ∈ SlotS k, SlotU ψ k p z * SlotV α g p θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rcases hθ with ⟨h1, h2⟩
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hpure : ∀ i : ℕ,
      Work.Spaces.DzIter i (fun z θ => ψ z * g θ) z θ = vzIter i ψ z * g θ :=
    fun i => congrFun (congrFun (DzIter_prod i ψ g hψ) z) θ
  have hmix : ∀ j i : ℕ,
      Work.Spaces.mixed j i (fun z θ => ψ z * g θ) z θ = vzIter j ψ z * vthIter i g θ :=
    fun j i => congrFun (congrFun (mixed_prod j i ψ g hψ hg) z) θ
  rw [Work.Spaces.HkIntegrand]
  simp only [hpure, hmix]
  rw [SlotS, Finset.sum_disjSum, Finset.sum_product]
  simp only [SlotU_inl, SlotU_inr, SlotV_inl, SlotV_inr]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, div_rpow_half_sq Work.Spaces.eta (Work.Spaces.w z) (Real.sin (2 * θ)) hs]
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc,
        mul_rpow_half_sq (Work.Spaces.gam α) (vzIter j ψ z * vthIter i g θ)
          (Work.Spaces.w z) (Real.sin (2 * θ)) hs]
      ring
    · rw [if_neg hc, if_neg hc, zero_mul]

/-! ## The evaluated (triangular) form -/

/-- The closed form of the squared `ℋ^k`-norm of a product. -/
noncomputable def HkSqForm (α : ℝ) (k : ℕ) (ψ g : ℝ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), Zc ψ i) * Sc g 0 Work.Spaces.eta
    + ∑ i ∈ Finset.range (k + 1),
        (if 1 ≤ i then (∑ j ∈ Finset.range (k + 1 - i), Zc ψ j) * Sc g i (Work.Spaces.gam α)
          else 0)

/-- One row of the mixed sum, in triangular form. -/
theorem mixed_row (M : ℕ → ℕ → ℝ) (k i : ℕ) :
    (if 1 ≤ i then (∑ j ∈ Finset.range (k + 1 - i), M i j) else 0)
      = ∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then M i j else 0) := by
  by_cases hi : 1 ≤ i
  · rw [if_pos hi]
    have hsub : Finset.range (k + 1 - i) ⊆ Finset.range (k + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have h1 : (∑ j ∈ Finset.range (k + 1 - i),
          (if 1 ≤ i ∧ i + j ≤ k then M i j else 0))
        = ∑ j ∈ Finset.range (k + 1 - i), M i j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_pos]
      exact ⟨hi, by have := Finset.mem_range.mp hj; omega⟩
    rw [← h1]
    exact Finset.sum_subset hsub fun j hj hjnot => by
      rw [if_neg]
      intro hcon
      exact hjnot (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))
  · rw [if_neg hi]
    exact (Finset.sum_eq_zero fun j _ => by rw [if_neg (fun h => hi h.1)]).symm

/-- The triangular mixed sum equals the double sum. -/
theorem tria_eq_double (M : ℕ → ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        (if 1 ≤ i then (∑ j ∈ Finset.range (k + 1 - i), M i j) else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then M i j else 0) :=
  Finset.sum_congr rfl fun i _ => mixed_row M k i

/-- The triangular sum in the `Zc`/`Sc` vocabulary equals the double sum. -/
theorem tria_eq_double_Zc (α : ℝ) (k : ℕ) (ψ g : ℝ → ℝ) :
    (∑ i ∈ Finset.range (k + 1),
        (if 1 ≤ i then
          (∑ j ∈ Finset.range (k + 1 - i), Zc ψ j * Sc g i (Work.Spaces.gam α)) else 0))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then Zc ψ j * Sc g i (Work.Spaces.gam α) else 0) := by
  have h := tria_eq_double (fun i j => Zc ψ j * Sc g i (Work.Spaces.gam α)) k
  simpa using h

/-- **The evaluation of the squared `ℋ^k`-norm of a product.** -/
theorem HkSq_eq_form (α : ℝ) (k : ℕ) (ψ g : ℝ → ℝ)
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ)
    (hg : ContDiff ℝ Work.Stability.smoothOrder g)
    (hU : ∀ p ∈ SlotS k, IntegrableOn (SlotU ψ k p) Work.Spaces.Iz)
    (hV : ∀ p ∈ SlotS k, IntegrableOn (SlotV α g p) Work.Spaces.Iθ) :
    Work.Spaces.HkSq α k (fun z θ => ψ z * g θ) = HkSqForm α k ψ g := by
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => ψ z * g θ) z θ)
        = ∫ θ in Work.Spaces.Iθ, ∑ p ∈ SlotS k, SlotU ψ k p z * SlotV α g p θ := by
    intro z
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    exact HkIntegrand_slots α k ψ g hψ hg hθ
  have key : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => ψ z * g θ) z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ∑ p ∈ SlotS k, SlotU ψ k p z * SlotV α g p θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici ?_
    intro z _
    exact hinner z
  rw [Work.Spaces.HkSq, key, sum_prod_iterated (SlotS k) (SlotU ψ k) (SlotV α g) hU hV,
    HkSqForm, SlotS, Finset.sum_disjSum, Finset.sum_product]
  simp only [SlotU_inl, SlotU_inr, SlotV_inl, SlotV_inr]
  congr 1
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => rfl
  · have hstep : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (∫ z in Work.Spaces.Iz,
              (if 1 ≤ i ∧ i + j ≤ k then (vzIter j ψ z * Work.Spaces.w z) ^ 2 else 0))
            * (∫ θ in Work.Spaces.Iθ,
                (vthIter i g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then Zc ψ j * Sc g i (Work.Spaces.gam α) else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h1 : (∫ z in Work.Spaces.Iz,
            (if 1 ≤ i ∧ i + j ≤ k then (vzIter j ψ z * Work.Spaces.w z) ^ 2 else 0))
          = (if 1 ≤ i ∧ i + j ≤ k then (1 : ℝ) else 0) * Zc ψ j := by
        have hfun : (fun z : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
              (vzIter j ψ z * Work.Spaces.w z) ^ 2 else 0))
            = fun z : ℝ => (if 1 ≤ i ∧ i + j ≤ k then (1 : ℝ) else 0)
                * (vzIter j ψ z * Work.Spaces.w z) ^ 2 := by
          funext z
          by_cases hc : 1 ≤ i ∧ i + j ≤ k <;> simp [hc]
        rw [hfun, MeasureTheory.integral_const_mul]
        rfl
      rw [h1, Sc]
      by_cases hc : 1 ≤ i ∧ i + j ≤ k <;> simp [hc]
    rw [hstep, ← tria_eq_double_Zc α k ψ g]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 1 ≤ i
    · rw [if_pos hi, if_pos hi, Finset.sum_mul]
    · rw [if_neg hi, if_neg hi]

/-- Shifting the angular slot by one: `Sc (vthIter 1 g) i q = Sc g (i+1) q`. -/
theorem Sc_vthIter_one (g : ℝ → ℝ) (i : ℕ) (q : ℝ) :
    Sc (vthIter 1 g) i q = Sc g (i + 1) q := by
  unfold Sc
  congr 1
  funext θ
  rw [vthIter_add i 1 g]

/-! ## The level shift -/

/-- **The level shift of the triangular mixed sum.** -/
theorem triaMP_shift (Z S : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1 + 1),
        (if 1 ≤ i then (∑ j ∈ Finset.range (n + 1 + 1 - i), Z j) * S i else 0))
      = (∑ i ∈ Finset.range (n + 1), Z i) * S 1
        + ∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then (∑ j ∈ Finset.range (n + 1 - i), Z j) * S (i + 1) else 0) := by
  have hL0 : (if 1 ≤ (0 : ℕ) then (∑ j ∈ Finset.range (n + 1 + 1 - 0), Z j) * S 0 else 0)
      = 0 := by rw [if_neg (by norm_num)]
  have hL1 : (if 1 ≤ (1 : ℕ) then (∑ j ∈ Finset.range (n + 1 + 1 - 1), Z j) * S 1 else 0)
      = (∑ i ∈ Finset.range (n + 1), Z i) * S 1 := by
    rw [if_pos (le_refl 1), show n + 1 + 1 - 1 = n + 1 from by omega]
  have hL2 : ∀ i : ℕ, (if 1 ≤ i + 2 then
        (∑ j ∈ Finset.range (n + 1 + 1 - (i + 2)), Z j) * S (i + 2) else 0)
      = (∑ j ∈ Finset.range (n - i), Z j) * S (i + 2) := by
    intro i
    rw [if_pos (by omega), show n + 1 + 1 - (i + 2) = n - i from by omega]
  have hR0 : (if 1 ≤ (0 : ℕ) then (∑ j ∈ Finset.range (n + 1 - 0), Z j) * S (0 + 1) else 0)
      = 0 := by rw [if_neg (by norm_num)]
  have hR1 : ∀ i : ℕ, (if 1 ≤ i + 1 then
        (∑ j ∈ Finset.range (n + 1 - (i + 1)), Z j) * S (i + 1 + 1) else 0)
      = (∑ j ∈ Finset.range (n - i), Z j) * S (i + 2) := by
    intro i
    rw [if_pos (by omega), show n + 1 - (i + 1) = n - i from by omega,
      show i + 1 + 1 = i + 2 from by omega]
  have hsplit1 : (∑ i ∈ Finset.range (n + 1 + 1),
        (if 1 ≤ i then (∑ j ∈ Finset.range (n + 1 + 1 - i), Z j) * S i else 0))
      = (∑ i ∈ Finset.range (n + 1), (if 1 ≤ i + 1 then
            (∑ j ∈ Finset.range (n + 1 + 1 - (i + 1)), Z j) * S (i + 1) else 0))
        + (if 1 ≤ (0 : ℕ) then (∑ j ∈ Finset.range (n + 1 + 1 - 0), Z j) * S 0 else 0) :=
    Finset.sum_range_succ'
      (fun i => (if 1 ≤ i then (∑ j ∈ Finset.range (n + 1 + 1 - i), Z j) * S i else 0))
      (n + 1)
  have hsplit2 : (∑ i ∈ Finset.range (n + 1), (if 1 ≤ i + 1 then
        (∑ j ∈ Finset.range (n + 1 + 1 - (i + 1)), Z j) * S (i + 1) else 0))
      = (∑ i ∈ Finset.range n, (if 1 ≤ i + 2 then
            (∑ j ∈ Finset.range (n + 1 + 1 - (i + 2)), Z j) * S (i + 2) else 0))
        + (if 1 ≤ (0 : ℕ) + 1 then
            (∑ j ∈ Finset.range (n + 1 + 1 - ((0 : ℕ) + 1)), Z j) * S ((0 : ℕ) + 1)
            else 0) :=
    Finset.sum_range_succ'
      (fun i => (if 1 ≤ i + 1 then
        (∑ j ∈ Finset.range (n + 1 + 1 - (i + 1)), Z j) * S (i + 1) else 0)) n
  have hsplit3 : (∑ i ∈ Finset.range (n + 1),
        (if 1 ≤ i then (∑ j ∈ Finset.range (n + 1 - i), Z j) * S (i + 1) else 0))
      = (∑ i ∈ Finset.range n, (if 1 ≤ i + 1 then
            (∑ j ∈ Finset.range (n + 1 - (i + 1)), Z j) * S (i + 1 + 1) else 0))
        + (if 1 ≤ (0 : ℕ) then (∑ j ∈ Finset.range (n + 1 - 0), Z j) * S ((0 : ℕ) + 1)
            else 0) :=
    Finset.sum_range_succ'
      (fun i => (if 1 ≤ i then (∑ j ∈ Finset.range (n + 1 - i), Z j) * S (i + 1) else 0)) n
  have h3 : (if 1 ≤ (0 : ℕ) + 1 then
        (∑ j ∈ Finset.range (n + 1 + 1 - ((0 : ℕ) + 1)), Z j) * S ((0 : ℕ) + 1) else 0)
      = (∑ i ∈ Finset.range (n + 1), Z i) * S 1 := by
    rw [if_pos (by norm_num), show n + 1 + 1 - ((0 : ℕ) + 1) = n + 1 from by omega]
  rw [hsplit1, hsplit2, hsplit3, hL0, hR0, h3,
    Finset.sum_congr rfl (fun i _ => hL2 i), Finset.sum_congr rfl (fun i _ => hR1 i)]
  ring

/-- The concrete level shift, in the `Zc`/`Sc` vocabulary. -/
theorem triaMP_shift_sc (α : ℝ) (ψ g : ℝ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1 + 1),
        (if 1 ≤ i then
          (∑ j ∈ Finset.range (n + 1 + 1 - i), Zc ψ j) * Sc g i (Work.Spaces.gam α) else 0))
      = (∑ i ∈ Finset.range (n + 1), Zc ψ i) * Sc g 1 (Work.Spaces.gam α)
        + ∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then
              (∑ j ∈ Finset.range (n + 1 - i), Zc ψ j) * Sc g (i + 1) (Work.Spaces.gam α)
              else 0) := by
  have h := triaMP_shift (Zc ψ) (fun i => Sc g i (Work.Spaces.gam α)) n
  simpa using h

/-- **The level shift of the evaluated form.** -/
theorem HkSqForm_shift (α : ℝ) (n : ℕ) (ψ g : ℝ → ℝ) :
    HkSqForm α (n + 1) ψ g - HkSqForm α n ψ (vthIter 1 g)
      = (∑ i ∈ Finset.range (n + 1 + 1), Zc ψ i) * Sc g 0 Work.Spaces.eta
        - (∑ i ∈ Finset.range (n + 1), Zc ψ i) * Sc g 1 Work.Spaces.eta
        + (∑ i ∈ Finset.range (n + 1), Zc ψ i) * Sc g 1 (Work.Spaces.gam α) := by
  have h0 : Sc (vthIter 1 g) 0 Work.Spaces.eta = Sc g 1 Work.Spaces.eta := by
    have h := Sc_vthIter_one g 0 Work.Spaces.eta
    simpa using h
  have hsub : HkSqForm α n ψ (vthIter 1 g)
      = (∑ i ∈ Finset.range (n + 1), Zc ψ i) * Sc g 1 Work.Spaces.eta
        + ∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then
              (∑ j ∈ Finset.range (n + 1 - i), Zc ψ j) * Sc g (i + 1) (Work.Spaces.gam α)
              else 0) := by
    rw [HkSqForm, h0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Sc_vthIter_one]
  rw [hsub, HkSqForm, triaMP_shift_sc α ψ g n]
  ring

end Work.FTS.CoercivityFix.Assembly

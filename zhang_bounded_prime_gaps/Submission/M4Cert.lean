import Mathlib
import Submission.MaynardFunctionals
import Submission.SimplexMono
import Submission.Commons.MeasureTheory.Integral.simplex_integral_scaled
import Submission.Commons.MeasureTheory.Integral.sq_interval_integral_le_len_mul_integral_sq
import Submission.Commons.MeasureTheory.Integral.integral_piFinSuccAbove_of_integrable

open MeasureTheory Finset
open Classical
open scoped BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-!
# The explicit `M_{4,ε}` certificate (Polymath8a, Theorem 3.13(xii'))

Polymath8a, Theorem 3.13(xii') states `M_{4,0.168} > 2.00558`, and Section 7.3 proves it with the
explicit function

  `F(t₁,t₂,t₃,t₄) = (1 - α (t₁+t₂+t₃+t₄)) · 1_{t₁+t₂+t₃+t₄ ≤ 1+ε}`,  `ε = 0.168`, `α = 0.784`.

This module formalises that computation (using the slightly better slope `α = 157/200`, for which
the margin over `2.00558` is unambiguous).  The two integrals

  `I(F)  = ∫_{(1+ε)R⁴} (1-α P₁)²`,
  `J₁(F) = ∫_{(1-ε)R³} (∫₀^{1+ε-P₁'} (1-α(P₁'+s)) ds)²`

are evaluated in closed form with the master simplex formula
`Commons.MeasureTheory.Integral.simplex_integral_scaled`, giving the rational number
`4 J₁(F)/I(F) > 2.00558`.

The point of the module is methodological: it exercises the whole variational pipeline
(`IFuncOrth`, `JFunc`, `MkEps`, the simplex master formula, and the `sSup` endgame) at a size
where every computation is elementary, as a template for the `k = 50` certificate.
-/

/-- `ε = 0.168 = 21/125`, the enlargement parameter of Polymath8a Theorem 3.13(xii'). -/
def eps4 : ℝ := 21/125

/-- `α = 0.785 = 157/200`, the slope of the linear cutoff. -/
def al4 : ℝ := 157/200

lemma simplexSet_eq_simplexC (k : ℕ) (c : ℝ) : simplexSet k c = simplexC k c := rfl

/-- The explicit linear cutoff supported on the enlarged simplex `(1+ε)R⁴`. -/
def F4 (t : Fin 4 → ℝ) : ℝ :=
  (1 - al4 * ∑ i, t i) * (if t ∈ simplexC 4 (1 + eps4) then 1 else 0)

lemma F4_support (t : Fin 4 → ℝ) (h : t ∉ simplexSet 4 (1 + eps4)) : F4 t = 0 := by
  have h' : t ∉ simplexC 4 (1 + eps4) := h
  simp only [F4, if_neg h', mul_zero]

lemma eps4_pos : (0:ℝ) < 1 + eps4 := by norm_num [eps4]

lemma one_sub_eps4_pos : (0:ℝ) < 1 - eps4 := by norm_num [eps4]

/-- A function times the indicator of a set integrates to its integral over the set. -/
lemma integral_mul_ite_eq_setIntegral {α : Type*} [MeasureSpace α] (s : Set α)
    (hs : MeasurableSet s) (g : α → ℝ) :
    ∫ t, g t * (if t ∈ s then 1 else 0) = ∫ t in s, g t := by
  rw [← MeasureTheory.integral_indicator hs (f := g)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show g t * (if t ∈ s then 1 else 0) = s.indicator g t
  by_cases h : t ∈ s
  · rw [Set.indicator_of_mem h, if_pos h, mul_one]
  · rw [Set.indicator_of_notMem h, if_neg h, mul_zero]

/-! ## The master simplex integrals -/

/-- `∫_{c·R^k} (c - Σ t)^a = c^{k+a} a!/(a+k)!`. -/
lemma simplexC_integral_pow (k : ℕ) (c : ℝ) (hc : 0 < c) (a : ℕ) :
    ∫ t in simplexC k c, (c - ∑ i, t i)^a =
      c^(k+a) * (a.factorial : ℝ) / ((a+k).factorial : ℝ) := by
  have h := Commons.MeasureTheory.Integral.simplex_integral_scaled (k := k) c hc a
    (fun _ : Fin k => 0)
  simpa [simplexC] using h

/-- The volume of the `c`-simplex: `∫_{c·R^k} 1 = c^k/k!`. -/
lemma simplexC_integral_one (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∫ _t in simplexC k c, (1:ℝ) = c^k / ((k.factorial : ℕ) : ℝ) := by
  have h := simplexC_integral_pow k c hc 0
  simpa using h

/-- Integrate a polynomial in the simplex coordinate `c - Σ t` against the master formula. -/
lemma simplexC_integral_poly (k : ℕ) (c : ℝ) (hc : 0 < c) (n : ℕ) (coef : ℕ → ℝ) :
    ∫ t in simplexC k c, ∑ m ∈ Finset.range n, coef m * (c - ∑ i, t i)^m
      = ∑ m ∈ Finset.range n,
          coef m * (c^(k+m) * (m.factorial : ℝ) / ((m+k).factorial : ℝ)) := by
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MeasureTheory.integral_const_mul, simplexC_integral_pow k c hc m]
  · intro m _
    have h := (integrableOn_simplexC_poly k c m (fun _ : Fin k => 0)).const_mul (coef m)
    simpa [mul_assoc] using h

/-- Integral of a squared affine function of the simplex coordinate sum. -/
lemma simplexC_integral_sq_affine (k : ℕ) (c : ℝ) (hc : 0 < c) (u v : ℝ) :
    ∫ t in simplexC k c, (u + v * (c - ∑ i, t i))^2 =
      u^2 * (c^k / ((k.factorial : ℕ) : ℝ))
      + 2*u*v * (c^(k+1) / (((k+1).factorial : ℕ) : ℝ))
      + v^2 * (c^(k+2) * 2 / (((k+2).factorial : ℕ) : ℝ)) := by
  set cf : ℕ → ℝ := fun m => if m = 0 then u^2 else if m = 1 then 2*u*v else v^2 with hcf
  have hpt : ∀ t : Fin k → ℝ,
      (u + v * (c - ∑ i, t i))^2
        = ∑ m ∈ Finset.range 3, cf m * (c - ∑ i, t i)^m := by
    intro t
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hcf]
    norm_num
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [simplexC_integral_poly k c hc 3 cf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hcf]
  norm_num
  ring

/-! ## The `I`-integral of the certificate -/

/-- `IFuncOrth 4 F4` is the integral of `(1-αP₁)²` over the enlarged simplex. -/
lemma IFuncOrth_F4 :
    IFuncOrth 4 F4 = ∫ t in simplexC 4 (1 + eps4), (1 - al4 * ∑ i, t i)^2 := by
  rw [IFuncOrth]
  have hpt : ∀ t : Fin 4 → ℝ,
      (F4 t)^2 = (1 - al4 * ∑ i, t i)^2 *
        (if t ∈ simplexC 4 (1 + eps4) then 1 else 0) := by
    intro t
    simp only [F4]
    by_cases h : t ∈ simplexC 4 (1 + eps4) <;> simp [h]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_mul_ite_eq_setIntegral _ (isClosed_simplexC 4 _).measurableSet _

/-- The value of `IFuncOrth 4 F4`, in closed form. -/
lemma IFuncOrth_F4_value :
    IFuncOrth 4 F4 =
      (1 - al4 * (1 + eps4))^2 * ((1 + eps4)^4 / (24:ℝ))
        + 2*(1 - al4 * (1 + eps4))*al4 * ((1 + eps4)^5 / (120:ℝ))
        + al4^2 * ((1 + eps4)^6 * 2 / (720:ℝ)) := by
  rw [IFuncOrth_F4]
  have h := simplexC_integral_sq_affine 4 (1 + eps4) eps4_pos (1 - al4*(1+eps4)) al4
  rw [show (∫ t in simplexC 4 (1 + eps4), (1 - al4 * ∑ i, t i)^2)
      = ∫ t in simplexC 4 (1 + eps4),
          ((1 - al4*(1+eps4)) + al4 * (1 + eps4 - ∑ i, t i))^2 from by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    ring]
  rw [h]
  norm_num

/-! ## The `J`-integral of the certificate -/

/-- Insert `x` at coordinate `i` of a `Fin k`-tuple, reindexing the remaining coordinates
through `Fin.succAbove`. -/
def insAt {k : ℕ} (i : Fin (k+1)) (x : ℝ) (u : Fin k → ℝ) : Fin (k+1) → ℝ :=
  fun j => if h : j = i then x else u ((finSuccAboveEquiv i).symm ⟨j, h⟩)

/-- Reindexing a `Fin k`-tuple to a function on the complement of `i`. -/
def reindex {k : ℕ} (i : Fin (k+1)) :
    (Fin k → ℝ) ≃ᵐ ({j : Fin (k+1) // j ≠ i} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : {j : Fin (k+1) // j ≠ i} => ℝ) (finSuccAboveEquiv i)

lemma reindex_apply {k : ℕ} (i : Fin (k+1)) (u : Fin k → ℝ)
    (j : {j : Fin (k+1) // j ≠ i}) :
    reindex i u j = u ((finSuccAboveEquiv i).symm j) := by
  have h := Equiv.piCongrLeft_apply_apply (fun _ : {j : Fin (k+1) // j ≠ i} => ℝ)
    (finSuccAboveEquiv i) u ((finSuccAboveEquiv i).symm j)
  simp only [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.apply_symm_apply] at h ⊢
  exact h

lemma measurePreserving_reindex {k : ℕ} (i : Fin (k+1)) :
    MeasurePreserving (reindex i) volume volume := by
  have h := MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : {j : Fin (k+1) // j ≠ i} => ℝ) (finSuccAboveEquiv i)
  simpa [reindex] using h

lemma extendAt_reindex {k : ℕ} (i : Fin (k+1)) (x : ℝ) (u : Fin k → ℝ) :
    extendAt i x (reindex i u) = insAt i x u := by
  funext j
  by_cases h : j = i
  · simp [extendAt, insAt, h]
  · simp [extendAt, insAt, h, reindex_apply]

lemma sum_reindex {k : ℕ} (i : Fin (k+1)) (u : Fin k → ℝ) :
    (∑ j : {j : Fin (k+1) // j ≠ i}, reindex i u j) = ∑ j : Fin k, u j := by
  rw [← Equiv.sum_comp (finSuccAboveEquiv i)
    (fun b : {j : Fin (k+1) // j ≠ i} => reindex i u b)]
  exact Finset.sum_congr rfl (fun a _ => by rw [reindex_apply]; simp)

lemma marginalSet_reindex {k : ℕ} (i : Fin (k+1)) (c : ℝ) (u : Fin k → ℝ) :
    marginalSet (k+1) i c (reindex i u) ↔ u ∈ simplexC k c := by
  simp only [marginalSet, simplexC, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨fun a => by
        have := h.1 (finSuccAboveEquiv i a)
        simpa [reindex_apply] using this,
      by rw [← sum_reindex i u]; exact h.2⟩
  · intro h
    exact ⟨fun j => by
        have := h.1 ((finSuccAboveEquiv i).symm j)
        simpa [reindex_apply] using this,
      by rw [sum_reindex i u]; exact h.2⟩

/-- `JFunc` in `Fin k` coordinates: the marginal integral is taken over the simplex in the
remaining `k` coordinates (the paper's `∫_{c·R^{k-1}}`). -/
def JFuncFin (k : ℕ) (i : Fin (k+1)) (c : ℝ) (F : (Fin (k+1) → ℝ) → ℝ) : ℝ :=
  ∫ u : Fin k → ℝ, (∫ x : ℝ, F (insAt i x u))^2 * (if u ∈ simplexC k c then 1 else 0)

/-- `JFunc` is invariant under reindexing the remaining coordinates. -/
theorem JFunc_eq_JFuncFin (k : ℕ) (i : Fin (k+1)) (c : ℝ)
    (F : (Fin (k+1) → ℝ) → ℝ) : JFunc (k+1) i c F = JFuncFin k i c F := by
  rw [JFunc, JFuncFin]
  rw [← (measurePreserving_reindex i).integral_comp'
    (fun t' : {j : Fin (k+1) // j ≠ i} → ℝ =>
      (∫ x : ℝ, F (extendAt i x t'))^2 * (if t' ∈ marginalSet (k+1) i c then 1 else 0))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show (∫ x : ℝ, F (extendAt i x (reindex i u)))^2 *
      (if (reindex i u) ∈ marginalSet (k+1) i c then 1 else 0)
    = (∫ x : ℝ, F (insAt i x u))^2 * (if u ∈ simplexC k c then 1 else 0)
  simp only [extendAt_reindex]
  have hind : (if (reindex i u) ∈ marginalSet (k+1) i c then (1:ℝ) else 0)
      = (if u ∈ simplexC k c then (1:ℝ) else 0) := by
    by_cases h : (reindex i u) ∈ marginalSet (k+1) i c
    · have hu : u ∈ simplexC k c := (marginalSet_reindex i c u).mp h
      simp only [h, if_true, hu]
    · have hu : u ∉ simplexC k c := fun hh => h ((marginalSet_reindex i c u).mpr hh)
      simp only [h, if_false, hu]
  rw [hind]

/-! ## Evaluating the `J`-integral -/

/-- The sum of the coordinates after inserting `x` at position `i`. -/
lemma sum_insAt {k : ℕ} (i : Fin (k+1)) (x : ℝ) (u : Fin k → ℝ) :
    (∑ j : Fin (k+1), insAt i x u j) = x + ∑ j : Fin k, u j := by
  rw [Fin.sum_univ_succAbove _ i]
  congr 1
  · simp [insAt]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsub : (⟨i.succAbove j, i.succAbove_ne j⟩ : {j : Fin (k+1) // j ≠ i})
        = finSuccAboveEquiv i j := by rw [finSuccAboveEquiv_apply]
    simp only [insAt, dif_neg (i.succAbove_ne j), hsub, Equiv.symm_apply_apply]

/-- Nonnegativity after inserting `x` at position `i`. -/
lemma nonneg_insAt {k : ℕ} (i : Fin (k+1)) (x : ℝ) (u : Fin k → ℝ) :
    (∀ j : Fin (k+1), 0 ≤ insAt i x u j) ↔ 0 ≤ x ∧ ∀ j : Fin k, 0 ≤ u j := by
  constructor
  · intro h
    refine ⟨by simpa [insAt] using h i, fun j => ?_⟩
    have := h (i.succAbove j)
    have hsub : (⟨i.succAbove j, i.succAbove_ne j⟩ : {j : Fin (k+1) // j ≠ i})
        = finSuccAboveEquiv i j := by rw [finSuccAboveEquiv_apply]
    simpa [insAt, dif_neg (i.succAbove_ne j), hsub, Equiv.symm_apply_apply] using this
  · rintro ⟨hx, hu⟩ j
    by_cases hj : j = i
    · subst hj; simpa [insAt] using hx
    · rw [insAt]
      simp only [dif_neg hj]
      exact hu ((finSuccAboveEquiv i).symm ⟨j, hj⟩)

/-- `F4` along the line obtained by inserting the coordinate `x` at position `i`. -/
lemma F4_insAt (i : Fin 4) (x : ℝ) (u : Fin 3 → ℝ) :
    F4 (insAt i x u) = (1 - al4 * (x + ∑ j, u j)) *
      (if (∀ j : Fin 3, 0 ≤ u j) ∧ 0 ≤ x ∧ x + ∑ j, u j ≤ 1 + eps4 then 1 else 0) := by
  have hcond : (insAt i x u ∈ simplexC 4 (1 + eps4))
      ↔ ((∀ j : Fin 3, 0 ≤ u j) ∧ 0 ≤ x ∧ x + ∑ j, u j ≤ 1 + eps4) := by
    simp only [simplexC, Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hx, hu⟩ := (nonneg_insAt i x u).mp h1
      exact ⟨hu, hx, by rw [← sum_insAt i x u]; exact h2⟩
    · rintro ⟨hu, hx, hsum⟩
      exact ⟨(nonneg_insAt i x u).mpr ⟨hx, hu⟩, by rw [sum_insAt i x u]; exact hsum⟩
  rw [F4, sum_insAt i x u]
  by_cases h : (insAt i x u ∈ simplexC 4 (1 + eps4))
  · rw [if_pos h, if_pos (hcond.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hcond.mpr hh))]

/-- `∫_0^L (1 - α(x+σ)) dx`. -/
lemma interval_integral_affine (L σ : ℝ) :
    ∫ x in (0:ℝ)..L, (1 - al4 * (x + σ)) = L - al4 * (L^2/2 + σ*L) := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 - al4 * σ)) volume (0:ℝ) L :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => al4 * x) volume (0:ℝ) L :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [show (fun x : ℝ => 1 - al4 * (x + σ)) = fun x => (1 - al4 * σ) - al4 * x from by
    funext x; ring]
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The inner integral of the certificate: `∫_ℝ F4(insert_i x u) dx`. -/
lemma inner_integral (i : Fin 4) (u : Fin 3 → ℝ) (hu : u ∈ simplexC 3 (1 - eps4)) :
    ∫ x : ℝ, F4 (insAt i x u)
      = (1 + eps4 - ∑ j, u j) *
          (1 - al4 * (1 + eps4 + ∑ j, u j) / 2) := by
  set σ : ℝ := ∑ j, u j with hσ
  have hu1 : ∀ j : Fin 3, 0 ≤ u j := hu.1
  have hu2 : σ ≤ 1 - eps4 := hu.2
  have heps : (0:ℝ) < eps4 := by norm_num [eps4]
  have hL : 0 ≤ 1 + eps4 - σ := by linarith
  have hpt : ∀ x : ℝ, F4 (insAt i x u)
      = (1 - al4 * (x + σ)) * (if x ∈ Set.Icc (0:ℝ) (1 + eps4 - σ) then 1 else 0) := by
    intro x
    rw [F4_insAt i x u]
    have hx : ((∀ j : Fin 3, 0 ≤ u j) ∧ 0 ≤ x ∧ x + σ ≤ 1 + eps4)
        ↔ (x ∈ Set.Icc (0:ℝ) (1 + eps4 - σ)) := by
      simp only [Set.mem_Icc]
      constructor
      · rintro ⟨-, hx0, hx1⟩; exact ⟨hx0, by linarith⟩
      · rintro ⟨hx0, hx1⟩; exact ⟨hu1, hx0, by linarith⟩
    by_cases h : (∀ j : Fin 3, 0 ≤ u j) ∧ 0 ≤ x ∧ x + σ ≤ 1 + eps4
    · rw [if_pos h, if_pos (hx.mp h), mul_one]
    · rw [if_neg h, if_neg (fun hh => h (hx.mpr hh)), mul_zero]
  have hstep1 : (∫ x : ℝ, F4 (insAt i x u))
      = ∫ x in Set.Icc (0:ℝ) (1 + eps4 - σ), (1 - al4 * (x + σ)) := by
    rw [show (∫ x : ℝ, F4 (insAt i x u))
        = ∫ x : ℝ, (1 - al4 * (x + σ)) *
            (if x ∈ Set.Icc (0:ℝ) (1 + eps4 - σ) then 1 else 0) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    show (1 - al4 * (t + σ)) * (if t ∈ Set.Icc (0:ℝ) (1 + eps4 - σ) then 1 else 0)
      = (Set.Icc (0:ℝ) (1 + eps4 - σ)).indicator (fun x => 1 - al4 * (x + σ)) t
    by_cases h : t ∈ Set.Icc (0:ℝ) (1 + eps4 - σ)
    · rw [Set.indicator_of_mem h, if_pos h, mul_one]
    · rw [Set.indicator_of_notMem h, if_neg h, mul_zero]
  rw [hstep1]
  rw [show (∫ x in Set.Icc (0:ℝ) (1 + eps4 - σ), (1 - al4 * (x + σ)))
      = ∫ x in (0:ℝ)..(1 + eps4 - σ), (1 - al4 * (x + σ)) from by
    rw [intervalIntegral.integral_of_le hL]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := 1 + eps4 - σ)).symm]
  rw [interval_integral_affine]
  rw [hσ]
  ring

/-- Coefficients of the polynomial `((2ε+z)((1-α)+αz/2))²` (degree `≤ 4`). -/
def coef4 (m : ℕ) : ℝ :=
  if m = 0 then 4*eps4^2*(1-al4)^2
  else if m = 1 then 4*eps4^2*(1-al4)*al4 + 4*eps4*(1-al4)^2
  else if m = 2 then eps4^2*al4^2 + 4*eps4*(1-al4)*al4 + (1-al4)^2
  else if m = 3 then eps4*al4^2 + (1-al4)*al4
  else al4^2/4

/-- The value of the `J`-integral of the certificate: the outer integral of the square of
the inner integral, evaluated with the master simplex formula. -/
lemma JFunc_F4_value (i : Fin 4) :
    JFunc 4 i (1 - eps4) F4 =
      ∑ m ∈ Finset.range 5, coef4 m *
        ((1 - eps4)^(3+m) * (m.factorial : ℝ) / ((m+3).factorial : ℝ)) := by
  rw [JFunc_eq_JFuncFin, JFuncFin]
  have hcongr : (∫ u : Fin 3 → ℝ, (∫ x : ℝ, F4 (insAt i x u))^2 *
        (if u ∈ simplexC 3 (1 - eps4) then 1 else 0))
      = ∫ u in simplexC 3 (1 - eps4), (∫ x : ℝ, F4 (insAt i x u))^2 := by
    rw [← MeasureTheory.integral_indicator (isClosed_simplexC 3 _).measurableSet]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show (∫ x : ℝ, F4 (insAt i x u))^2 * (if u ∈ simplexC 3 (1 - eps4) then 1 else 0)
      = (simplexC 3 (1 - eps4)).indicator (fun u => (∫ x : ℝ, F4 (insAt i x u))^2) u
    by_cases h : u ∈ simplexC 3 (1 - eps4)
    · rw [Set.indicator_of_mem h, if_pos h, mul_one]
    · rw [Set.indicator_of_notMem h, if_neg h, mul_zero]
  rw [hcongr]
  rw [MeasureTheory.setIntegral_congr_fun (isClosed_simplexC 3 _).measurableSet
    (fun u hu => ?_)]
  · rw [simplexC_integral_poly 3 (1 - eps4) one_sub_eps4_pos 5 coef4]
  · rw [inner_integral i u hu]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coef4]
    norm_num
    ring

/-- The certificate ratio exceeds `2.00558`. -/
theorem M4_ratio_gt :
    (2.00558 : ℝ) < (∑ i : Fin 4, JFunc 4 i (1 - eps4) F4) / IFuncOrth 4 F4 := by
  have hJ : ∀ i : Fin 4, JFunc 4 i (1 - eps4) F4 =
      ∑ m ∈ Finset.range 5, coef4 m *
        ((1 - eps4)^(3+m) * (m.factorial : ℝ) / ((m+3).factorial : ℝ)) :=
    fun i => JFunc_F4_value i
  rw [Finset.sum_congr rfl (fun i _ => hJ i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, IFuncOrth_F4_value]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coef4]
  norm_num [eps4, al4]

/-- The certificate function satisfies the admissibility conditions and has positive `I`. -/
theorem M4_admissible :
    (∀ t : Fin 4 → ℝ, t ∉ simplexSet 4 (1 + eps4) → F4 t = 0) ∧ 0 < IFuncOrth 4 F4 := by
  refine ⟨F4_support, ?_⟩
  rw [IFuncOrth_F4_value]
  norm_num [eps4, al4]

/-- **Polymath8a, Theorem 3.13(xii')**: the explicit cutoff `F4` is admissible and its
variational quotient `Σᵢ Jᵢ(F)/I(F)` exceeds `2.00558`.  Equivalently (with the supremum taken
over admissible functions, `MkEps`) this is `M_{4,0.168} > 2.00558`. -/
theorem M4_certificate :
    ∃ F : (Fin 4 → ℝ) → ℝ,
      (∀ t : Fin 4 → ℝ, t ∉ simplexSet 4 (1 + eps4) → F t = 0) ∧
      0 < IFuncOrth 4 F ∧
      (2.00558 : ℝ) < (∑ i : Fin 4, JFunc 4 i (1 - eps4) F) / IFuncOrth 4 F :=
  ⟨F4, M4_admissible.1, M4_admissible.2, M4_ratio_gt⟩

/-- The `MkEps` form of the certificate, from the boundedness of the defining set. -/
theorem MkEps_4_gt_of_bddAbove
    (hbdd : BddAbove {r : ℝ | ∃ F : (Fin 4 → ℝ) → ℝ,
      (∀ t, t ∉ simplexSet 4 (1 + eps4) → F t = 0) ∧
      0 < IFuncOrth 4 F ∧
      r < (∑ i : Fin 4, JFunc 4 i (1 - eps4) F) / IFuncOrth 4 F}) :
    (2.00558 : ℝ) < MkEps 4 eps4 := by
  set r : ℝ := ((2.00558 : ℝ) + (∑ i : Fin 4, JFunc 4 i (1 - eps4) F4) / IFuncOrth 4 F4) / 2
    with hr
  have hmem : r ∈ {r : ℝ | ∃ F : (Fin 4 → ℝ) → ℝ,
      (∀ t, t ∉ simplexSet 4 (1 + eps4) → F t = 0) ∧
      0 < IFuncOrth 4 F ∧
      r < (∑ i : Fin 4, JFunc 4 i (1 - eps4) F) / IFuncOrth 4 F} :=
    ⟨F4, M4_admissible.1, M4_admissible.2, by rw [hr]; linarith [M4_ratio_gt]⟩
  have hle : r ≤ MkEps 4 eps4 := le_csSup hbdd hmem
  rw [hr] at hle
  linarith [M4_ratio_gt]

/-! ## Support of the line integrands (used for the Cauchy--Schwarz bound on `J`) -/

/-- If `F` vanishes off the enlarged simplex, then along any line `x ↦ insAt i x u` the values
vanish outside `[0, 1+ε]`. -/
lemma insAt_eq_zero_of_notMem {k : ℕ} {ε : ℝ} {F : (Fin (k+1) → ℝ) → ℝ}
    (hsupp : ∀ t : Fin (k+1) → ℝ, t ∉ simplexSet (k+1) (1 + ε) → F t = 0)
    (i : Fin (k+1)) (u : Fin k → ℝ) {x : ℝ} (hx : x ∉ Set.Icc (0:ℝ) (1 + ε)) :
    F (insAt i x u) = 0 := by
  refine hsupp _ ?_
  rw [simplexSet, Set.mem_ofPred_eq, not_and_or]
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with hxlt | hxgt
  · left
    rw [not_forall]
    refine ⟨i, ?_⟩
    rw [insAt, dif_pos rfl]
    linarith
  · by_cases hu : ∀ j : Fin k, 0 ≤ u j
    · right
      rw [not_le]
      have h1 : x ≤ ∑ j : Fin (k+1), insAt i x u j := by
        rw [sum_insAt]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hu j))
      linarith
    · left
      rw [not_forall] at hu
      obtain ⟨j, hj⟩ := hu
      rw [not_le] at hj
      rw [not_forall]
      refine ⟨i.succAbove j, ?_⟩
      have hji : i.succAbove j ≠ i := i.succAbove_ne j
      rw [insAt, dif_neg hji]
      have hsub : (⟨i.succAbove j, hji⟩ : {j : Fin (k+1) // j ≠ i}) = finSuccAboveEquiv i j := by
        rw [finSuccAboveEquiv_apply]
      rw [hsub, Equiv.symm_apply_apply]
      linarith

/-! ## The Cauchy--Schwarz bound `Σᵢ Jᵢ(F) ≤ k(1+ε)·I(F)`

This is what makes the defining set of `MkEps` bounded above (and hence the `sSup` an honest
supremum).  The ingredients are Fubini along one coordinate
(`Commons.MeasureTheory.Integral.integral_piFinSuccAbove_of_integrable`), the support of the line
integrands (`insAt_eq_zero_of_notMem`) and Cauchy--Schwarz on an interval
(`Commons.MeasureTheory.Integral.sq_interval_integral_le_len_mul_integral_sq`). -/

/-- `IFuncOrth` as an iterated integral along the inserted coordinate (in the `u`-outer order). -/
lemma IFuncOrth_eq_iterated {k : ℕ} (i : Fin (k+1)) {F : (Fin (k+1) → ℝ) → ℝ}
    (hint : Integrable fun y => (F y)^2) :
    IFuncOrth (k+1) F = ∫ u : Fin k → ℝ, ∫ x : ℝ, (F (Fin.insertNth i x u))^2 := by
  have hkey : ∀ (x : ℝ) (u : Fin k → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm (x, u)
        = Fin.insertNth i x u := by
    intro x u
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i)
      volume volume := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i
  have hprod : Integrable (fun z : ℝ × (Fin k → ℝ) => (F (Fin.insertNth i z.1 z.2))^2)
      (volume.prod volume) := by
    have h := hmp.symm.integrable_comp_of_integrable hint
    refine h.congr ?_
    filter_upwards with z
    rw [Function.comp_apply, hkey]
  have hFub := Commons.MeasureTheory.Integral.integral_piFinSuccAbove_of_integrable i
    (fun y : Fin (k+1) → ℝ => (F y)^2) hint
  rw [show IFuncOrth (k+1) F = ∫ y : Fin (k+1) → ℝ, (F y)^2 from rfl, hFub]
  exact MeasureTheory.integral_integral_swap hprod

/-- The two parametrisations `insAt` and `Fin.insertNth` of the inserted coordinate agree. -/
lemma insAt_eq_insertNth {k : ℕ} (i : Fin (k+1)) (x : ℝ) (u : Fin k → ℝ) :
    insAt i x u = Fin.insertNth i x u := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [insAt, dif_pos rfl, Fin.insertNth_apply_same]
  · have h1 : i.succAbove ((finSuccAboveEquiv i).symm ⟨j, hj⟩) = j := by
      have h2 := Equiv.apply_symm_apply (finSuccAboveEquiv i)
        (⟨j, hj⟩ : {j : Fin (k+1) // j ≠ i})
      rw [finSuccAboveEquiv_apply] at h2
      exact congrArg Subtype.val h2
    have hL : insAt i x u j = u ((finSuccAboveEquiv i).symm ⟨j, hj⟩) := by
      rw [insAt, dif_neg hj]
    have hR : Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) i x u j
        = u ((finSuccAboveEquiv i).symm ⟨j, hj⟩) := by
      conv_lhs => rw [← h1]
      rw [Fin.insertNth_apply_succAbove]
    rw [hL, hR]

/-- Cauchy--Schwarz for a single slice. -/
lemma slice_cs {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {F : (Fin (k+1) → ℝ) → ℝ}
    (hsupp : ∀ t : Fin (k+1) → ℝ, t ∉ simplexSet (k+1) (1 + ε) → F t = 0)
    (i : Fin (k+1)) {u : Fin k → ℝ}
    (hint : Integrable fun x : ℝ => (F (Fin.insertNth i x u))^2) :
    (∫ x : ℝ, F (Fin.insertNth i x u))^2
      ≤ (1 + ε) * ∫ x : ℝ, (F (Fin.insertNth i x u))^2 := by
  set s : Set ℝ := Set.Icc (0:ℝ) (1 + ε) with hs
  have hzero : ∀ x ∉ s, F (Fin.insertNth i x u) = 0 := by
    intro x hx
    rw [← insAt_eq_insertNth i x u]
    exact insAt_eq_zero_of_notMem hsupp i u hx
  have hzero2 : ∀ x ∉ s, (F (Fin.insertNth i x u))^2 = 0 := by
    intro x hx; rw [hzero x hx]; ring
  have hgs : (∫ x : ℝ, F (Fin.insertNth i x u)) = ∫ x in s, F (Fin.insertNth i x u) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  have hgs2 : (∫ x : ℝ, (F (Fin.insertNth i x u))^2)
      = ∫ x in s, (F (Fin.insertNth i x u))^2 := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero2 x hx]
  have hint' : MeasureTheory.IntegrableOn (fun x : ℝ => (F (Fin.insertNth i x u))^2) s :=
    hint.integrableOn
  have hIcc : MeasureTheory.IntegrableOn (fun x : ℝ => (F (Fin.insertNth i x u))^2)
      (Set.Icc (0:ℝ) (1 + ε)) := hint'
  have hconv1 : (∫ x in s, F (Fin.insertNth i x u))
      = ∫ x in (0:ℝ)..(1 + ε), F (Fin.insertNth i x u) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := 1 + ε)).symm
  have hconv2 : (∫ x in s, (F (Fin.insertNth i x u))^2)
      = ∫ x in (0:ℝ)..(1 + ε), (F (Fin.insertNth i x u))^2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := 1 + ε)).symm
  rw [hgs, hgs2, hconv1, hconv2]
  have hcs := Commons.MeasureTheory.Integral.sq_interval_integral_le_len_mul_integral_sq
    (le_of_lt (by linarith : (0:ℝ) < 1 + ε))
    (f := fun x : ℝ => F (Fin.insertNth i x u)) hIcc
  linarith [hcs]

/-- Cauchy--Schwarz bound for one `J`-functional. -/
lemma JFunc_le_IFuncOrth {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (i : Fin (k+1)) {F : (Fin (k+1) → ℝ) → ℝ}
    (hsupp : ∀ t : Fin (k+1) → ℝ, t ∉ simplexSet (k+1) (1 + ε) → F t = 0)
    (hint : Integrable fun y => (F y)^2) :
    JFunc (k+1) i (1 - ε) F ≤ (1 + ε) * IFuncOrth (k+1) F := by
  have hkey : ∀ (x : ℝ) (u : Fin k → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm (x, u)
        = Fin.insertNth i x u := by
    intro x u
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i)
      volume volume := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i
  have hprod : Integrable (fun z : ℝ × (Fin k → ℝ) => (F (Fin.insertNth i z.1 z.2))^2)
      (volume.prod volume) := by
    have h := hmp.symm.integrable_comp_of_integrable hint
    refine h.congr ?_
    filter_upwards with z
    rw [Function.comp_apply, hkey]
  have hmarg : Integrable (fun u : Fin k → ℝ => ∫ x : ℝ, (F (Fin.insertNth i x u))^2) := by
    have h2 := ((MeasureTheory.integrable_prod_iff' hprod.aestronglyMeasurable).mp hprod).2
    refine h2.congr ?_
    filter_upwards with u
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hslice_ae : ∀ᵐ u : Fin k → ℝ, Integrable fun x : ℝ => (F (Fin.insertNth i x u))^2 :=
    hprod.prod_left_ae
  have hRHSe : (fun u : Fin k → ℝ => (1 + ε) * ∫ x : ℝ, (F (insAt i x u))^2)
      = fun u : Fin k → ℝ => (1 + ε) * ∫ x : ℝ, (F (Fin.insertNth i x u))^2 := by
    funext u
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    rw [insAt_eq_insertNth]
  rw [JFunc_eq_JFuncFin k i (1 - ε) F, JFuncFin]
  by_cases hInt : Integrable (fun u : Fin k → ℝ =>
      (∫ x : ℝ, F (insAt i x u))^2 * (if u ∈ simplexC k (1 - ε) then 1 else 0))
  · have hbound_ae : ∀ᵐ u : Fin k → ℝ,
        (∫ x : ℝ, F (insAt i x u))^2 * (if u ∈ simplexC k (1 - ε) then 1 else 0)
          ≤ (1 + ε) * ∫ x : ℝ, (F (insAt i x u))^2 := by
      filter_upwards [hslice_ae] with u hslice
      by_cases hu : u ∈ simplexC k (1 - ε)
      · rw [if_pos hu, mul_one]
        have hcs := slice_cs hε hsupp i (u := u) (by simpa [insAt_eq_insertNth] using hslice)
        simpa [insAt_eq_insertNth] using hcs
      · rw [if_neg hu, mul_zero]
        exact mul_nonneg (by linarith) (MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
    have hRHS : Integrable (fun u : Fin k → ℝ => (1 + ε) * ∫ x : ℝ, (F (insAt i x u))^2) := by
      rw [hRHSe]
      exact hmarg.const_mul _
    have hmono := MeasureTheory.integral_mono_ae hInt hRHS hbound_ae
    calc ∫ u : Fin k → ℝ, (∫ x : ℝ, F (insAt i x u))^2 *
          (if u ∈ simplexC k (1 - ε) then 1 else 0)
        ≤ ∫ u : Fin k → ℝ, (1 + ε) * ∫ x : ℝ, (F (insAt i x u))^2 := hmono
      _ = (1 + ε) * ∫ u : Fin k → ℝ, ∫ x : ℝ, (F (insAt i x u))^2 :=
          MeasureTheory.integral_const_mul _ _
      _ = (1 + ε) * IFuncOrth (k+1) F := by
          rw [IFuncOrth_eq_iterated i hint]
          congr 1
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          beta_reduce
          rw [insAt_eq_insertNth]
  · rw [MeasureTheory.integral_undef hInt]
    exact mul_nonneg (by linarith) (MeasureTheory.integral_nonneg (fun y => sq_nonneg _))

/-- Cauchy--Schwarz bound for the whole `J`-sum. -/
theorem sum_JFunc_le {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {F : (Fin (k+1) → ℝ) → ℝ}
    (hsupp : ∀ t : Fin (k+1) → ℝ, t ∉ simplexSet (k+1) (1 + ε) → F t = 0)
    (hI : 0 < IFuncOrth (k+1) F) :
    (∑ i : Fin (k+1), JFunc (k+1) i (1 - ε) F)
      ≤ ((k+1 : ℕ) : ℝ) * (1 + ε) * IFuncOrth (k+1) F := by
  have hint : Integrable fun y : Fin (k+1) → ℝ => (F y)^2 := by
    by_contra h
    have h0 : IFuncOrth (k+1) F = 0 := by
      rw [IFuncOrth]
      exact MeasureTheory.integral_undef h
    rw [h0] at hI
    exact lt_irrefl 0 hI
  calc (∑ i : Fin (k+1), JFunc (k+1) i (1 - ε) F)
      ≤ ∑ _i : Fin (k+1), (1 + ε) * IFuncOrth (k+1) F :=
        Finset.sum_le_sum (fun i _ => JFunc_le_IFuncOrth hε i hsupp hint)
    _ = ((k+1 : ℕ) : ℝ) * (1 + ε) * IFuncOrth (k+1) F := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The quotient of an admissible function is at most `k(1+ε)`. -/
theorem ratio_le {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {F : (Fin (k+1) → ℝ) → ℝ}
    (hsupp : ∀ t : Fin (k+1) → ℝ, t ∉ simplexSet (k+1) (1 + ε) → F t = 0)
    (hI : 0 < IFuncOrth (k+1) F) :
    (∑ i : Fin (k+1), JFunc (k+1) i (1 - ε) F) / IFuncOrth (k+1) F
      ≤ ((k+1 : ℕ) : ℝ) * (1 + ε) := by
  rw [div_le_iff₀ hI]
  calc (∑ i : Fin (k+1), JFunc (k+1) i (1 - ε) F)
      ≤ ((k+1 : ℕ) : ℝ) * (1 + ε) * IFuncOrth (k+1) F := sum_JFunc_le hε hsupp hI
    _ = ((k+1 : ℕ) : ℝ) * (1 + ε) * IFuncOrth (k+1) F := rfl

/-- The defining set of `MkEps` is bounded above. -/
theorem bddAbove_ratioSet (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    BddAbove {r : ℝ | ∃ F : (Fin (k+1) → ℝ) → ℝ,
      (∀ t, t ∉ simplexSet (k+1) (1 + ε) → F t = 0) ∧ 0 < IFuncOrth (k+1) F ∧
      r < (∑ i : Fin (k+1), JFunc (k+1) i (1 - ε) F) / IFuncOrth (k+1) F} := by
  refine ⟨((k+1 : ℕ) : ℝ) * (1 + ε), fun r hr => ?_⟩
  obtain ⟨F, hsupp, hI, hr⟩ := hr
  exact le_of_lt (lt_of_lt_of_le hr (ratio_le hε hsupp hI))

/-- **Polymath8a, Theorem 3.13(xii')**, in the `MkEps` (supremum) form:
`M_{4,0.168} > 2.00558`. -/
theorem MkEps_4_gt : (2.00558 : ℝ) < MkEps 4 eps4 :=
  MkEps_4_gt_of_bddAbove (bddAbove_ratioSet 3 (by norm_num [eps4] : (0:ℝ) ≤ eps4))

end

end Commons.NumberTheory.MaynardSieve
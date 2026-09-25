import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.BilinRHS
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le

noncomputable section

set_option maxHeartbeats 2000000

universe u v

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

/-- The operator norm on the space of bilinear continuous maps whose arguments live in spaces
of continuous linear maps.  This is the canonical instance; we register it as a `local
instance` because instance search does not reach it through the deep nesting of
`ContinuousLinearMap` structures. -/
private def normNestedCLM (X Y A : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup A] [NormedSpace ℝ A] :
    Norm ((Y →L[ℝ] A) →L[ℝ] (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] A)) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := Y →L[ℝ] A) (F := (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] A))

attribute [local instance] normNestedCLM

/-! ## Auxiliary lemmas for the composition estimate of Hölder norms -/

/-- Elementary real inequality: if `0 < p ≤ M * q` and `M ≥ 0`, then
`r / q ^ α ≤ M ^ α * (r / p ^ α)` for `r ≥ 0` and `α > 0`. -/
private lemma div_rpow_le_mul_div_rpow {r M p q α : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hα : 0 < α)
    (hp : 0 < p) (hpq : p ≤ M * q) : r / q ^ α ≤ M ^ α * (r / p ^ α) := by
  have hq : 0 < q := by
    by_contra h
    have hq0 : q ≤ 0 := le_of_not_gt h
    have : M * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM hq0
    linarith
  have hpq' : p ^ α ≤ M ^ α * q ^ α := by
    calc p ^ α ≤ (M * q) ^ α := Real.rpow_le_rpow hp.le hpq hα.le
      _ = M ^ α * q ^ α := Real.mul_rpow hM hq.le
  have hpα : 0 < p ^ α := Real.rpow_pos_of_pos hp α
  have hqα : 0 < q ^ α := Real.rpow_pos_of_pos hq α
  rw [← mul_div_assoc, le_div_iff₀ hpα, div_mul_eq_mul_div, div_le_iff₀ hqα]
  calc r * p ^ α ≤ r * (M ^ α * q ^ α) := mul_le_mul_of_nonneg_left hpq' hr
    _ = M ^ α * r * q ^ α := by ring

/-- The chain rule at a point of an open set, for functions with values in an arbitrary
normed space: the within-derivative of a composition is the composition of the
within-derivatives. -/
lemma fderivWithin_comp_eq {X Y A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {Φ : X → Y} {u : Y → A} {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t)
    (hst : Set.MapsTo Φ s t) (hΦ : DifferentiableOn ℝ Φ s) (hu : DifferentiableOn ℝ u t) :
    ∀ x ∈ s, fderivWithin ℝ (u ∘ Φ) s x
      = ContinuousLinearMap.compL ℝ X Y A (fderivWithin ℝ u t (Φ x))
          (fderivWithin ℝ Φ s x) := by
  intro x hx
  have hΦx : Φ x ∈ t := hst hx
  have hΦd : DifferentiableAt ℝ Φ x := hΦ.differentiableAt (hs.mem_nhds hx)
  have hud : DifferentiableAt ℝ u (Φ x) := hu.differentiableAt (ht.mem_nhds hΦx)
  rw [fderivWithin_of_isOpen hs hx, fderiv_comp x hud hΦd, ← fderivWithin_of_isOpen ht hΦx,
    ← fderivWithin_of_isOpen hs hx]
  exact (ContinuousLinearMap.compL_apply ℝ X Y A _ _).symm

/-! ### Bounds for the data of the inner map `Φ` -/

section PhiData

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The sup-norm of the `k`-th derivative of `Φ` on `s` is bounded by the (nonnegative part
of the) constant `D k`. -/
lemma iDN_le_ofReal_max (Φ : X → Y) (D : ℕ → ℝ) (s : Set X) (k : ℕ)
    (hD : ∀ x ∈ s, ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k) :
    iDN k Φ s ≤ ENNReal.ofReal (max (D k) 0) := by
  rw [iDN]
  refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ?_
  exact (hD x hx).trans (le_max_left _ _)

/-- The Hölder seminorm of the `k`-th derivative of `Φ` on `s` is bounded by the
(nonnegative part of the) constant `E k`. -/
lemma hSN_le_ofReal_max (Φ : X → Y) (E : ℕ → ℝ) (s : Set X) (k : ℕ) (α : ℝ)
    (hE : ∀ x ∈ s, ∀ y ∈ s,
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    hSN k α Φ s ≤ ENNReal.ofReal (max (E k) 0) := by
  rw [hSN]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hp : 0 < ‖x - y‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  have h1 : ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖
      ≤ max (E k) 0 * ‖x - y‖ ^ α :=
    (hE x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  rw [div_le_iff₀ hp]
  exact h1

end PhiData

/-! ### The combined norm `TN` -/

/-- Sum of the sup-norms of the iterated derivatives up to order `k` and of their Hölder
seminorms of exponent `α`, for functions with values in an arbitrary normed space. -/
noncomputable def TN {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (k : ℕ) (α : ℝ) (f : X → A) (Ω : Set X) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1), (iDN i f Ω + hSN i α f Ω)

@[simp] lemma TN_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (α : ℝ) (f : X → A) (Ω : Set X) :
    TN 0 α f Ω = iDN 0 f Ω + hSN 0 α f Ω := by
  simp [TN]

lemma TN_succ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ) (α : ℝ) (f : X → A)
    (Ω : Set X) :
    TN (k + 1) α f Ω = TN k α f Ω + (iDN (k + 1) f Ω + hSN (k + 1) α f Ω) := by
  simp [TN, Finset.sum_range_succ]

lemma TN_mono {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ) (α : ℝ) (f : X → A)
    (Ω : Set X) : TN k α f Ω ≤ TN (k + 1) α f Ω := by
  rw [TN_succ]
  exact le_add_right le_rfl

lemma iDN_le_TN {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k i : ℕ) (α : ℝ) {f : X → A}
    {Ω : Set X} (hi : i ≤ k) : iDN i f Ω ≤ TN k α f Ω := by
  have h1 : iDN i f Ω ≤ iDN i f Ω + hSN i α f Ω := le_add_right le_rfl
  refine le_trans h1 ?_
  rw [TN]
  exact Finset.single_le_sum (f := fun i => iDN i f Ω + hSN i α f Ω) (fun _ _ => bot_le)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

lemma hSN_le_TN {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k i : ℕ) (α : ℝ) {f : X → A}
    {Ω : Set X} (hi : i ≤ k) : hSN i α f Ω ≤ TN k α f Ω := by
  have h1 : hSN i α f Ω ≤ iDN i f Ω + hSN i α f Ω := le_add_left le_rfl
  refine le_trans h1 ?_
  rw [TN]
  exact Finset.single_le_sum (f := fun i => iDN i f Ω + hSN i α f Ω) (fun _ _ => bot_le)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- Passing to the derivative does not increase the combined norm: the combined norm of
`k`-th order of `fderivWithin u Ω` on `Ω` is bounded by that of order `k+1` of `u`. -/
lemma TN_fderivWithin_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (k : ℕ) (α : ℝ) (u : X → A)
    (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    TN k α (fun y => fderivWithin ℝ u Ω y) Ω ≤ TN (k + 1) α u Ω := by
  have hL : TN k α (fun y => fderivWithin ℝ u Ω y) Ω
      = ∑ i ∈ Finset.range (k + 1), (iDN (i + 1) u Ω + hSN (i + 1) α u Ω) := by
    rw [TN]
    exact Finset.sum_congr rfl fun i _ => by
      rw [iDN_fderivWithin i u Ω hΩ, hSN_fderivWithin i α u Ω hΩ]
  have hR : TN (k + 1) α u Ω
      = (∑ i ∈ Finset.range (k + 1), (iDN (i + 1) u Ω + hSN (i + 1) α u Ω))
        + (iDN 0 u Ω + hSN 0 α u Ω) := by
    rw [TN, Finset.sum_range_succ']
  rw [hL, hR]
  exact le_add_right le_rfl

/-! ### The order `0` case of the composition estimate -/

/-- Composition estimate at order `0`, for targets in an arbitrary normed space. -/
lemma TN_zero_comp_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {t : Set Y}
    {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hst : Set.MapsTo Φ s t)
    (hLip : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ M * ‖x - y‖)
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (u : Y → A) :
    TN 0 α (u ∘ Φ) s ≤ ENNReal.ofReal (1 + M ^ α) * TN 0 α u t := by
  have hMα : (0 : ℝ) ≤ M ^ α := Real.rpow_nonneg hM α
  have hA : iDN 0 (u ∘ Φ) s ≤ iDN 0 u t := by
    rw [iDN_zero_deriv, iDN_zero_deriv]
    exact iSup₂_le fun x hx => le_iSup₂_of_le (Φ x) (hst hx) le_rfl
  have hB : hSN 0 α (u ∘ Φ) s ≤ ENNReal.ofReal (M ^ α) * hSN 0 α u t := by
    rw [hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    by_cases h : Φ x = Φ y
    · simp only [Function.comp_apply, h, sub_self, norm_zero, zero_div, ENNReal.ofReal_zero]
      exact bot_le
    · have hp : 0 < ‖Φ x - Φ y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
      have hlip : ‖Φ x - Φ y‖ ≤ M * ‖x - y‖ := hLip x hx y hy
      have h1 : ENNReal.ofReal
            (‖u (Φ x) - u (Φ y)‖ / ‖Φ x - Φ y‖ ^ α) ≤ hSN 0 α u t := by
        have h' := le_hSN 0 α (f := u) (Ω := t) (hst hx) (hst hy) h
        rw [norm_iteratedFDerivWithin_zero_sub] at h'
        exact h'
      calc ENNReal.ofReal (‖u (Φ x) - u (Φ y)‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (M ^ α * (‖u (Φ x) - u (Φ y)‖ / ‖Φ x - Φ y‖ ^ α)) :=
            ENNReal.ofReal_le_ofReal
              (div_rpow_le_mul_div_rpow (norm_nonneg _) hM hα hp hlip)
        _ = ENNReal.ofReal (M ^ α)
              * ENNReal.ofReal (‖u (Φ x) - u (Φ y)‖ / ‖Φ x - Φ y‖ ^ α) :=
            ENNReal.ofReal_mul hMα
        _ ≤ ENNReal.ofReal (M ^ α) * hSN 0 α u t := mul_le_mul_right h1 _
  rw [TN_zero, TN_zero]
  refine (add_le_add hA hB).trans ?_
  have h1 : ENNReal.ofReal (1 + M ^ α) = 1 + ENNReal.ofReal (M ^ α) := by
    rw [ENNReal.ofReal_add zero_le_one hMα, ENNReal.ofReal_one]
  rw [h1]
  have h2 : (1 + ENNReal.ofReal (M ^ α)) * (iDN 0 u t + hSN 0 α u t)
      = (iDN 0 u t + ENNReal.ofReal (M ^ α) * hSN 0 α u t)
        + (hSN 0 α u t + ENNReal.ofReal (M ^ α) * iDN 0 u t) := by
    ring
  rw [h2]
  exact le_add_right le_rfl

/-! ### The composition estimate in the combined norms -/

/-- Composition estimate in the combined norms `TN`, for targets in an arbitrary normed
space: for every order `k` there is a constant `c ≥ 0` such that the `TN k`-norm of `u ∘ Φ`
on `s` is bounded by `c` times the `TN k`-norm of `u` on `t`. -/
theorem comp_bound_aux_local {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {t : Set Y}
    (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s)
    (hs : IsOpen s) (ht : IsOpen t) (L : ℝ)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (α : ℝ) (hα : 0 < α)
    (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k)
    (E : ℕ → ℝ)
    (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s →
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (A : Type u) [NormedAddCommGroup A] [NormedSpace ℝ A]
      (u : Y → A), (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) u t) →
      TN k α (u ∘ Φ) s ≤ ENNReal.ofReal c * TN k α u t := by
  intro k
  induction k with
  | zero =>
    refine ⟨1 + (max L 0) ^ α, ?_, ?_⟩
    · have h := Real.rpow_nonneg (le_max_right L 0) α
      linarith
    · intro A _ _ u _
      refine TN_zero_comp_le hα (le_max_right L 0) hst ?_ u
      intro x hx y hy
      have h2 : L * ‖x - y‖ ≤ max L 0 * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (le_max_left L 0) (norm_nonneg _)
      linarith [hL x hx y hy]
  | succ k ih =>
    obtain ⟨c, hc0, ihc⟩ := ih
    set DB : ℝ := (∑ m ∈ Finset.range (k + 2), |D m|) + 1 with hDB
    set EB : ℝ := (∑ m ∈ Finset.range (k + 2), |E m|) + 1 with hEB
    have hDBpos : 0 < DB := by rw [hDB]; positivity
    have hEBpos : 0 < EB := by rw [hEB]; positivity
    have hDBle : ∀ m ≤ k + 1, max (D m) 0 ≤ DB := by
      intro m hm
      have h1 : |D m| ≤ ∑ i ∈ Finset.range (k + 2), |D i| :=
        Finset.single_le_sum (f := fun i => |D i|) (fun i _ => abs_nonneg _) (a := m)
          (Finset.mem_range.mpr (by omega))
      have h2 : D m ≤ |D m| := le_abs_self _
      have h3 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 2), |D i| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [hDB]
      exact max_le (by linarith) (by linarith)
    have hEBle : ∀ m ≤ k + 1, max (E m) 0 ≤ EB := by
      intro m hm
      have h1 : |E m| ≤ ∑ i ∈ Finset.range (k + 2), |E i| :=
        Finset.single_le_sum (f := fun i => |E i|) (fun i _ => abs_nonneg _) (a := m)
          (Finset.mem_range.mpr (by omega))
      have h2 : E m ≤ |E m| := le_abs_self _
      have h3 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 2), |E i| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [hEB]
      exact max_le (by linarith) (by linarith)
    set d1 : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (c * DB) with hd1
    set d2 : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (c * (DB + EB)) with hd2
    have hd1nn : 0 ≤ d1 := by
      rw [hd1]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 hDBpos.le)
    have hd2nn : 0 ≤ d2 := by
      rw [hd2]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 (add_nonneg hDBpos.le hEBpos.le))
    refine ⟨c + d1 + d2, by linarith, ?_⟩
    intro A _ _ u hu
    set v : Y → (Y →L[ℝ] A) := fun y => fderivWithin ℝ u t y with hv
    set Ψ : X → (X →L[ℝ] Y) := fun x => fderivWithin ℝ Φ s x with hΨ
    set B : (Y →L[ℝ] A) →L[ℝ] (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] A) :=
      ContinuousLinearMap.compL ℝ X Y A with hB
    set N : ℝ≥0∞ := TN (k + 1) α u t with hN
    have hUs : UniqueDiffOn ℝ s := hs.uniqueDiffOn
    have hUt : UniqueDiffOn ℝ t := ht.uniqueDiffOn
    have hv' : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) v t := by
      intro m
      exact (hu (m + 1)).fderivWithin hUt (by simp only [Nat.cast_succ, le_refl])
    have hIH : TN k α (v ∘ Φ) s ≤ ENNReal.ofReal c * TN k α v t :=
      ihc (Y →L[ℝ] A) v hv'
    have hvC : TN k α (v ∘ Φ) s ≤ ENNReal.ofReal c * N := by
      have h := hIH.trans
        (mul_le_mul_right (TN_fderivWithin_le k α u t hUt) (ENNReal.ofReal c))
      simpa only [hN] using h
    have hΦDN : ∀ m ≤ k + 1, iDN m Φ s ≤ ENNReal.ofReal DB := by
      intro m hm
      exact (iDN_le_ofReal_max Φ D s m (fun x hx => hD m x hx)).trans
        (ENNReal.ofReal_le_ofReal (hDBle m hm))
    have hΦSN : ∀ m ≤ k + 1, hSN m α Φ s ≤ ENNReal.ofReal EB := by
      intro m hm
      exact (hSN_le_ofReal_max Φ E s m α (fun x hx y hy => hE m x hx y hy)).trans
        (ENNReal.ofReal_le_ofReal (hEBle m hm))
    have hΨDN : ∀ m ≤ k, iDN m Ψ s ≤ ENNReal.ofReal DB := by
      intro m hm
      have h : iDN m Ψ s = iDN (m + 1) Φ s := by
        rw [hΨ, iDN_fderivWithin m Φ s hUs]
      rw [h]
      exact hΦDN (m + 1) (by omega)
    have hΨSN : ∀ m ≤ k, hSN m α Ψ s ≤ ENNReal.ofReal EB := by
      intro m hm
      have h : hSN m α Ψ s = hSN (m + 1) α Φ s := by
        rw [hΨ, hSN_fderivWithin m α Φ s hUs]
      rw [h]
      exact hΦSN (m + 1) (by omega)
    have hvΦDN : ∀ j ≤ k, iDN j (v ∘ Φ) s ≤ ENNReal.ofReal c * N := fun j hj =>
      (iDN_le_TN k j α hj).trans hvC
    have hvΦSN : ∀ j ≤ k, hSN j α (v ∘ Φ) s ≤ ENNReal.ofReal c * N := fun j hj =>
      (hSN_le_TN k j α hj).trans hvC
    have hchain : ∀ x ∈ s, fderivWithin ℝ (u ∘ Φ) s x = B ((v ∘ Φ) x) (Ψ x) := by
      intro x hx
      have h := fderivWithin_comp_eq hs ht hst
        ((hΦ 1).differentiableOn (by positivity)) ((hu 1).differentiableOn (by positivity)) x hx
      rw [hB]
      exact h
    have hvΦc : ContDiffOn ℝ k (v ∘ Φ) s := ContDiffOn.comp (hv' k) (hΦ k) hst
    have hΨc : ContDiffOn ℝ k Ψ s := by
      rw [hΨ]
      exact (hΦ (k + 1)).fderivWithin hUs (by simp only [Nat.cast_succ, le_refl])
    have hBnorm : ENNReal.ofReal ‖B‖ ≤ 1 := by
      rw [hB, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      change sInf {c : ℝ | 0 ≤ c ∧ ∀ x,
        ‖(ContinuousLinearMap.compL ℝ X Y A) x‖ ≤ c * ‖x‖} ≤ 1
      refine csInf_le ⟨0, fun c hc => hc.1⟩ ⟨zero_le_one, fun x => ?_⟩
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
        (E := X →L[ℝ] Y) (F := X →L[ℝ] A) _ (norm_nonneg x) fun g => ?_
      exact ContinuousLinearMap.opNorm_comp_le x g
    have hS1 : (∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s))
        ≤ ENNReal.ofReal d1 * N := by
      rw [hd1, ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hc0 hDBpos.le)), Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s)
          ≤ (k.choose j : ℝ≥0∞) * ((ENNReal.ofReal c * N) * ENNReal.ofReal DB) :=
            mul_le_mul_right (mul_le_mul' (hvΦDN j hjk) (hΨDN (k - j) (by omega))) _
        _ = ENNReal.ofReal ((k.choose j : ℝ) * (c * DB)) * N := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (k.choose j)), ENNReal.ofReal_mul hc0,
              ENNReal.ofReal_natCast]
            ring
    have hS2 : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
          (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s))
        ≤ ENNReal.ofReal d2 * N := by
      rw [hd2, ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg hc0 (add_nonneg hDBpos.le hEBpos.le))), Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
          ≤ (ENNReal.ofReal c * N) * ENNReal.ofReal DB :=
        mul_le_mul' (hvΦSN j hjk) (hΨDN (k - j) (by omega))
      have h2 : iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s
          ≤ (ENNReal.ofReal c * N) * ENNReal.ofReal EB :=
        mul_le_mul' (hvΦDN j hjk) (hΨSN (k - j) (by omega))
      calc (k.choose j : ℝ≥0∞) * (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
              + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s)
          ≤ (k.choose j : ℝ≥0∞) * ((ENNReal.ofReal c * N) * ENNReal.ofReal DB
              + (ENNReal.ofReal c * N) * ENNReal.ofReal EB) :=
            mul_le_mul_right (add_le_add h1 h2) _
        _ = ENNReal.ofReal ((k.choose j : ℝ) * (c * (DB + EB))) * N := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg (k.choose j)), ENNReal.ofReal_mul hc0,
              ENNReal.ofReal_add hDBpos.le hEBpos.le, ENNReal.ofReal_natCast]
            ring
    have hDNtop : iDN (k + 1) (u ∘ Φ) s ≤ ENNReal.ofReal d1 * N := by
      have h1 : iDN (k + 1) (u ∘ Φ) s
          = iDN k (fun x => fderivWithin ℝ (u ∘ Φ) s x) s :=
        (iDN_fderivWithin k (u ∘ Φ) s hUs).symm
      have h2 : iDN k (fun x => fderivWithin ℝ (u ∘ Φ) s x) s
          = iDN k (fun x => B ((v ∘ Φ) x) (Ψ x)) s :=
        iDN_congr fun x hx => hchain x hx
      rw [h1, h2]
      have h3 := iDN_bilinear_le (B := B) k (f := v ∘ Φ) (g := Ψ) (Ω := s) hvΦc hΨc hUs
      calc iDN k (fun x => B ((v ∘ Φ) x) (Ψ x)) s
          ≤ ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s)) := h3
        _ ≤ 1 * (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s)) :=
            mul_le_mul_left hBnorm _
        _ = ∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ≥0∞) * (iDN j (v ∘ Φ) s * iDN (k - j) Ψ s) := one_mul _
        _ ≤ ENNReal.ofReal d1 * N := hS1
    have hSNtop : hSN (k + 1) α (u ∘ Φ) s ≤ ENNReal.ofReal d2 * N := by
      have h1 : hSN (k + 1) α (u ∘ Φ) s
          = hSN k α (fun x => fderivWithin ℝ (u ∘ Φ) s x) s :=
        (hSN_fderivWithin k α (u ∘ Φ) s hUs).symm
      have h2 : hSN k α (fun x => fderivWithin ℝ (u ∘ Φ) s x) s
          = hSN k α (fun x => B ((v ∘ Φ) x) (Ψ x)) s :=
        hSN_congr fun x hx => hchain x hx
      rw [h1, h2]
      have h3 := hSN_bilinear_le k α B (f := v ∘ Φ) (g := Ψ) (Ω := s) hvΦc hΨc hUs
      calc hSN k α (fun x => B ((v ∘ Φ) x) (Ψ x)) s
          ≤ ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
              (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
                + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s)) := h3
        _ ≤ 1 * (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
              (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
                + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s)) :=
            mul_le_mul_left hBnorm _
        _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
              (hSN j α (v ∘ Φ) s * iDN (k - j) Ψ s
                + iDN j (v ∘ Φ) s * hSN (k - j) α Ψ s) := one_mul _
        _ ≤ ENNReal.ofReal d2 * N := hS2
    have hbase : TN k α (u ∘ Φ) s ≤ ENNReal.ofReal c * N := by
      have h := (ihc A u hu).trans (mul_le_mul_right (TN_mono k α u t) (ENNReal.ofReal c))
      simpa only [hN] using h
    have hsum : ENNReal.ofReal (c + d1 + d2) * N
        = ENNReal.ofReal c * N + (ENNReal.ofReal d1 * N + ENNReal.ofReal d2 * N) := by
      have h1 : ENNReal.ofReal (c + d1 + d2)
          = ENNReal.ofReal c + ENNReal.ofReal d1 + ENNReal.ofReal d2 := by
        rw [ENNReal.ofReal_add (add_nonneg hc0 hd1nn) hd2nn,
          ENNReal.ofReal_add hc0 hd1nn]
      rw [h1, add_mul, add_mul, add_assoc]
    rw [TN_succ]
    exact (add_le_add hbase (add_le_add hDNtop hSNtop)).trans (le_of_eq hsum.symm)

/-! ### Transfer of the norms along isometric equivalences

The composition estimate is proved first in a single universe (so that the spaces of
continuous linear maps used in the induction stay in that universe); to deduce the general
statement we transport along the isometric equivalences given by `ULift`. -/

section Transfers

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The canonical isometric equivalence between `ULift E` and `E`. -/
noncomputable def uliftLIE (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ULift.{v, u} E ≃ₗᵢ[ℝ] E where
  toFun := ULift.down
  invFun := ULift.up
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl
  norm_map' x := rfl

/-- On the left, composing an iterated derivative with a linear isometry preserves the
difference of the iterated derivatives at two points. -/
lemma norm_iteratedFDerivWithin_sub_comp_lie_left {A A' : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A'] (e : A ≃ₗᵢ[ℝ] A')
    (f : X → A) (i : ℕ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) {x y : X} (hx : x ∈ Ω)
    (hy : y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i (fun z => e (f z)) Ω x
        - iteratedFDerivWithin ℝ i (fun z => e (f z)) Ω y‖
      = ‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ := by
  have h1 : ∀ z ∈ Ω, iteratedFDerivWithin ℝ i (fun x => e (f x)) Ω z
      = (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω z) := by
    intro z hz
    show iteratedFDerivWithin ℝ i (⇑e ∘ f) Ω z
      = (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω z)
    exact ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (e : A ≃L[ℝ] A') f hΩ hz i
  rw [h1 x hx, h1 y hy]
  rw [show (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω x)
        - (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω y)
      = (e : A →L[ℝ] A').compContinuousMultilinearMap
          (iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y) from by
    ext m
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, ← map_sub]]
  rw [show (e : A →L[ℝ] A') = e.toLinearIsometry.toContinuousLinearMap from rfl]
  exact LinearIsometry.norm_compContinuousMultilinearMap e.toLinearIsometry _

/-- On the right, composing an iterated derivative with a linear isometry preserves the
difference of the iterated derivatives at two points. -/
lemma norm_iteratedFDerivWithin_sub_comp_lie_right {X' : Type*} [NormedAddCommGroup X']
    [NormedSpace ℝ X'] {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (e : X' ≃ₗᵢ[ℝ] X) (f : X → A) (i : ℕ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) {x y : X'}
    (hx : x ∈ e ⁻¹' Ω) (hy : y ∈ e ⁻¹' Ω) :
    ‖iteratedFDerivWithin ℝ i (f ∘ e) (e ⁻¹' Ω) x - iteratedFDerivWithin ℝ i (f ∘ e) (e ⁻¹' Ω) y‖
      = ‖iteratedFDerivWithin ℝ i f Ω (e x) - iteratedFDerivWithin ℝ i f Ω (e y)‖ := by
  have h1 : ∀ z ∈ e ⁻¹' Ω, iteratedFDerivWithin ℝ i (f ∘ e) (e ⁻¹' Ω) z
      = (iteratedFDerivWithin ℝ i f Ω (e z)).compContinuousLinearMap
          (fun _ : Fin i => (e : X' →L[ℝ] X)) := by
    intro z hz
    exact ContinuousLinearEquiv.iteratedFDerivWithin_comp_right e.toContinuousLinearEquiv f hΩ hz i
  rw [h1 x hx, h1 y hy]
  rw [show (iteratedFDerivWithin ℝ i f Ω (e x)).compContinuousLinearMap (fun _ : Fin i => (e : X' →L[ℝ] X))
        - (iteratedFDerivWithin ℝ i f Ω (e y)).compContinuousLinearMap (fun _ : Fin i => (e : X' →L[ℝ] X))
      = (iteratedFDerivWithin ℝ i f Ω (e x)
          - iteratedFDerivWithin ℝ i f Ω (e y)).compContinuousLinearMap
            (fun _ : Fin i => (e : X' →L[ℝ] X)) from by
    ext m
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, sub_apply]]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _ (fun _ => e)

/-- `iDN` is invariant under composing with a linear isometry on the right. -/
lemma iDN_comp_lie_right {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X']
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (e : X' ≃ₗᵢ[ℝ] X) (f : X → A) (i : ℕ)
    (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (f ∘ e) (e ⁻¹' Ω) = iDN i f Ω := by
  refine le_antisymm ?_ ?_
  · rw [iDN]
    refine iSup₂_le fun x hx => ?_
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right e f hΩ hx i]
    exact le_iSup₂_of_le (e x) hx le_rfl
  · rw [iDN]
    refine iSup₂_le fun x hx => ?_
    have hmem : e.symm x ∈ e ⁻¹' Ω := by simpa using hx
    refine le_iSup₂_of_le (e.symm x) hmem ?_
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right e f hΩ
      (show e (e.symm x) ∈ Ω from by simpa using hx) i]
    simp

/-- `hSN` is invariant under composing with a linear isometry on the right. -/
lemma hSN_comp_lie_right {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X']
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (e : X' ≃ₗᵢ[ℝ] X) (f : X → A) (i : ℕ)
    (α : ℝ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN i α (f ∘ e) (e ⁻¹' Ω) = hSN i α f Ω := by
  have key := fun x (hx : x ∈ e ⁻¹' Ω) y (hy : y ∈ e ⁻¹' Ω) =>
    norm_iteratedFDerivWithin_sub_comp_lie_right e f i Ω hΩ hx hy
  unfold hSN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hne : e x ≠ e y := fun h => hxy (e.injective h)
    have hnorm : ‖x - y‖ = ‖e x - e y‖ := by rw [← e.norm_map (x - y), map_sub]
    refine le_iSup₂_of_le (e x) hx (le_iSup₂_of_le (e y) hy (le_iSup_of_le hne ?_))
    rw [key x hx y hy, hnorm]
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hx' : e.symm x ∈ e ⁻¹' Ω := by simpa using hx
    have hy' : e.symm y ∈ e ⁻¹' Ω := by simpa using hy
    have hne : e.symm x ≠ e.symm y := fun h => hxy (e.symm.injective h)
    have hnorm : ‖e.symm x - e.symm y‖ = ‖x - y‖ := by
      rw [← e.symm.norm_map (x - y), map_sub]
    refine le_iSup₂_of_le (e.symm x) hx' (le_iSup₂_of_le (e.symm y) hy' (le_iSup_of_le hne ?_))
    rw [key (e.symm x) hx' (e.symm y) hy', hnorm, e.apply_symm_apply x, e.apply_symm_apply y]

/-- `TN` is invariant under composing with a linear isometry on the right. -/
lemma TN_comp_lie_right {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X']
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (e : X' ≃ₗᵢ[ℝ] X) (f : X → A) (k : ℕ)
    (α : ℝ) (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    TN k α (f ∘ e) (e ⁻¹' Ω) = TN k α f Ω := by
  simp only [TN]
  exact Finset.sum_congr rfl fun i _ => by
    rw [iDN_comp_lie_right e f i Ω hΩ, hSN_comp_lie_right e f i α Ω hΩ]

/-- `TN` is invariant under composing with a linear isometry on the left. -/
lemma TN_comp_lie_left {A A' : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup A'] [NormedSpace ℝ A'] (e : A ≃ₗᵢ[ℝ] A') (f : X → A) (k : ℕ) (α : ℝ)
    (Ω : Set X) (hΩ : UniqueDiffOn ℝ Ω) :
    TN k α (fun x => e (f x)) Ω = TN k α f Ω := by
  simp only [TN]
  exact Finset.sum_congr rfl fun i _ => by
    rw [iDN_comp_lie e f i Ω hΩ, hSN_comp_lie e f i α Ω hΩ]

end Transfers

/-! ### The composition estimate in arbitrary universes -/

/-- The composition estimate for the Hölder norms, with the two universes of `X` and `Y`
kept independent: this is proved by lifting both `X` and `Y` into a common universe and
applying `comp_bound_aux_local`. -/
theorem holderNorm_comp_le_general {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {t : Set Y}
    (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s)
    (hs : IsOpen s) (ht : IsOpen t) (L : ℝ)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (α : ℝ) (hα : 0 < α)
    (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k)
    (E : ℕ → ℝ)
    (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s →
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (u : Y → ℂ),
      (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) u t) →
      holderNorm k α (u ∘ Φ) s ≤ ENNReal.ofReal (C k) * holderNorm k α u t := by
  let eX : ULift.{max u v} X ≃ₗᵢ[ℝ] X := uliftLIE X
  let eY : ULift.{max u v} Y ≃ₗᵢ[ℝ] Y := uliftLIE Y
  let eC : ULift.{max u v} ℂ ≃ₗᵢ[ℝ] ℂ := uliftLIE ℂ
  let Φ' : ULift.{max u v} X → ULift.{max u v} Y := fun x => eY.symm (Φ (eX x))
  have hs' : IsOpen (eX ⁻¹' s) := hs.preimage eX.continuous
  have ht' : IsOpen (eY ⁻¹' t) := ht.preimage eY.continuous
  have hUs : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hUt : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  have hUs' : UniqueDiffOn ℝ (eX ⁻¹' s) := hs'.uniqueDiffOn
  have hUt' : UniqueDiffOn ℝ (eY ⁻¹' t) := ht'.uniqueDiffOn
  have hst' : Set.MapsTo Φ' (eX ⁻¹' s) (eY ⁻¹' t) := by
    intro x hx
    show eY (Φ' x) ∈ t
    rw [show Φ' x = eY.symm (Φ (eX x)) from rfl, eY.apply_symm_apply]
    exact hst hx
  have hΦ' : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ' (eX ⁻¹' s) := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat) (fun x : ULift.{max u v} X => Φ (eX x))
        (eX ⁻¹' s) :=
      ContDiffOn.comp_continuousLinearMap (hΦ m) (eX : ULift.{max u v} X →L[ℝ] X)
    exact ContDiffOn.comp ((LinearIsometryEquiv.contDiff eY.symm).contDiffOn) h1
      (Set.mapsTo_univ _ _)
  have hL' : ∀ x ∈ eX ⁻¹' s, ∀ y ∈ eX ⁻¹' s, ‖Φ' x - Φ' y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have h1 : ‖Φ' x - Φ' y‖ = ‖Φ (eX x) - Φ (eX y)‖ := by
      rw [show Φ' x - Φ' y = eY.symm (Φ (eX x) - Φ (eX y)) by
            simp only [Φ', map_sub],
        LinearIsometryEquiv.norm_map]
    have h2 : ‖x - y‖ = ‖eX x - eX y‖ := by
      rw [← eX.norm_map (x - y), map_sub]
    rw [h1, h2]
    exact hL (eX x) hx (eX y) hy
  have hD' : ∀ (k : ℕ) (x : ULift.{max u v} X), x ∈ eX ⁻¹' s →
      ‖iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) x‖ ≤ D k := by
    intro k x hx
    change ‖iteratedFDerivWithin ℝ k (fun x' => eY.symm (Φ (eX x'))) (eX ⁻¹' s) x‖ ≤ D k
    have hleft : ‖iteratedFDerivWithin ℝ k (fun x' => eY.symm (Φ (eX x'))) (eX ⁻¹' s) x‖
        = ‖iteratedFDerivWithin ℝ k (fun x' => Φ (eX x')) (eX ⁻¹' s) x‖ :=
      LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left eY.symm
        (f := fun x' : ULift.{max u v} X => Φ (eX x')) hUs' hx k
    have hright : ‖iteratedFDerivWithin ℝ k (fun x' => Φ (eX x')) (eX ⁻¹' s) x‖
        = ‖iteratedFDerivWithin ℝ k Φ s (eX x)‖ :=
      LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right eX Φ hUs hx k
    rw [hleft, hright]
    exact hD k (eX x) hx
  have hE' : ∀ (k : ℕ) (x : ULift.{max u v} X), x ∈ eX ⁻¹' s →
      ∀ (y : ULift.{max u v} X), y ∈ eX ⁻¹' s →
      ‖iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) x
        - iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) y‖ ≤ E k * ‖x - y‖ ^ α := by
    intro k x hx y hy
    have h1 : ‖iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) x
        - iteratedFDerivWithin ℝ k Φ' (eX ⁻¹' s) y‖
        = ‖iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x')) (eX ⁻¹' s) x
            - iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x'))
                (eX ⁻¹' s) y‖ :=
      norm_iteratedFDerivWithin_sub_comp_lie_left eY.symm
        (fun x' : ULift.{max u v} X => Φ (eX x')) k (eX ⁻¹' s) hUs' hx hy
    have h2 : ‖iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x')) (eX ⁻¹' s) x
        - iteratedFDerivWithin ℝ k (fun x' : ULift.{max u v} X => Φ (eX x')) (eX ⁻¹' s) y‖
        = ‖iteratedFDerivWithin ℝ k Φ s (eX x) - iteratedFDerivWithin ℝ k Φ s (eX y)‖ :=
      norm_iteratedFDerivWithin_sub_comp_lie_right eX Φ k s hUs hx hy
    have h3 : ‖x - y‖ = ‖eX x - eX y‖ := by
      rw [← eX.norm_map (x - y), map_sub]
    rw [h1, h2, h3]
    exact hE k (eX x) hx (eX y) hy
  choose C hC using comp_bound_aux_local hst' hΦ' hs' ht' L hL' α hα D hD' E hE'
  refine ⟨fun k => C k + 1, fun k => by
      have := (hC k).1
      linarith, fun k u hu => ?_⟩
  have hu' : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat)
      (fun y : ULift.{max u v} Y => eC.symm (u (eY y))) (eY ⁻¹' t) := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat) (fun y : ULift.{max u v} Y => u (eY y))
        (eY ⁻¹' t) :=
      ContDiffOn.comp_continuousLinearMap (hu m) (eY : ULift.{max u v} Y →L[ℝ] Y)
    exact ContDiffOn.comp ((LinearIsometryEquiv.contDiff eC.symm).contDiffOn) h1
      (Set.mapsTo_univ _ _)
  have h := (hC k).2 (ULift.{max u v} ℂ) (fun y => eC.symm (u (eY y))) hu'
  have hcomp : (fun y => eC.symm (u (eY y))) ∘ Φ'
      = fun x => eC.symm ((u ∘ Φ) (eX x)) := by
    funext x
    show eC.symm (u (eY (eY.symm (Φ (eX x))))) = eC.symm (u (Φ (eX x)))
    rw [eY.apply_symm_apply]
  have hTN1 : TN k α ((fun y => eC.symm (u (eY y))) ∘ Φ') (eX ⁻¹' s)
      = TN k α (u ∘ Φ) s := by
    have h1 : TN k α (fun x => eC.symm ((u ∘ Φ) (eX x))) (eX ⁻¹' s)
        = TN k α (fun x => (u ∘ Φ) (eX x)) (eX ⁻¹' s) :=
      TN_comp_lie_left eC.symm (fun x => (u ∘ Φ) (eX x)) k α (eX ⁻¹' s) hUs'
    have h2 : TN k α (fun x => (u ∘ Φ) (eX x)) (eX ⁻¹' s) = TN k α (u ∘ Φ) s :=
      TN_comp_lie_right eX (u ∘ Φ) k α s hUs
    rw [hcomp, h1, h2]
  have hTN2 : TN k α (fun y => eC.symm (u (eY y))) (eY ⁻¹' t) = TN k α u t := by
    have h1 : TN k α (fun y => eC.symm (u (eY y))) (eY ⁻¹' t)
        = TN k α (fun y => u (eY y)) (eY ⁻¹' t) :=
      TN_comp_lie_left eC.symm (fun y => u (eY y)) k α (eY ⁻¹' t) hUt'
    have h2 : TN k α (fun y => u (eY y)) (eY ⁻¹' t) = TN k α u t :=
      TN_comp_lie_right eY u k α t hUt
    rw [h1, h2]
  rw [hTN1, hTN2] at h
  have e1 : holderNorm k α (u ∘ Φ) s = TN k α (u ∘ Φ) s := by
    simp only [holderNorm, TN, iDN_complex_eq, hSN_complex_eq]
  have e2 : holderNorm k α u t = TN k α u t := by
    simp only [holderNorm, TN, iDN_complex_eq, hSN_complex_eq]
  rw [e1, e2]
  exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _)

/-! ### The composition estimate -/

theorem holderNorm_comp_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {t : Set Y} (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s) (hs : IsOpen s) (ht : IsOpen t) (L : ℝ) (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (α : ℝ) (hα : 0 < α) (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k) (E : ℕ → ℝ) (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) : ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (u : Y → ℂ), (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) u t) → Work.CR.Flat.holderNorm k α (u ∘ Φ) s ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α u t :=
  holderNorm_comp_le_general hst hΦ hs ht L hL α hα D hD E hE

end Work.CR.Flat.Holder

import Submission.Work.GYFactor7
import Submission.Commons.Analysis.Complex.integral_vertical_shift_pair
import Submission.Commons.Analysis.Integral.integrable_tendsto_log_inv_sq
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_re
import Submission.Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_one_add
import Submission.Commons.NumberTheory.Zeta.norm_inv_riemannZeta_le_one_add

/-!
# Green–Tao §10: the contour shift `Γ_{1+ε} → Γ₁` and `hmain`

`GYFactor7.lean` evaluated the `Γ₁`-integral (Green–Tao Lemma 10.4).  Here we
* shift the contour from `Γ_{1+m}` (where `∏_p E_p` converges absolutely and hence equals
  `G₁G₂G₃`) down to `Γ_{1/log R}` — the shift is pole-free because on the strip
  `Re z ∈ [1/log R, 1+m]` the arguments of every `ζ` lie in `{Re > 1}`, and
* combine the result with `mainSum_eq_contour` to obtain `hmain`.

The integrand is
`Ψ z z' := (G₁(z,z')·G₂(z,z')·G₃(z,z'))·Ker R z z'`, and the shift is
`Commons.Analysis.Complex.integral_vertical_shift_pair` with the weight
`g t = (log(|t|+2)+1)/(a²+t²)`, `a = 1/log R`
(`Commons.Analysis.Integral.integrable_tendsto_log_inv_sq`).
-/

open Finset Filter
open Commons.Analysis.Complex
open scoped BigOperators Topology

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ} {W Amax : ℕ} {A : Fin m → Fin t → ℤ} {b : Fin m → ℤ}

/-! ## 1. A finite product of holomorphic functions on a general normed space -/

lemma differentiableOn_finsetProd'' {α : Type*} [NormedAddCommGroup α] [NormedSpace ℂ α]
    {ι : Type*} {s : Set α} {f : ι → α → ℂ} (u : Finset ι)
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun a => ∏ i ∈ u, f i a) s := by
  classical
  induction u using Finset.induction with
  | empty =>
      exact (differentiableOn_const (c := (1 : ℂ)) :
        DifferentiableOn ℂ (fun _ : α => (1 : ℂ)) s)
  | insert d v hd ih =>
      have h1 : DifferentiableOn ℂ (f d * fun a => ∏ i ∈ v, f i a) s :=
        (h d (Finset.mem_insert_self d v)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      refine h1.congr fun a _ => ?_
      simp only [Pi.mul_apply, Finset.prod_insert hd]

/-! ## 2. Continuity and holomorphy of the ζ-ratio `G₃` and the kernel, in composition form -/

lemma continuousOn_riemannZeta_one_add_comp {α : Type*} [TopologicalSpace α] {s : Set α}
    {F : α → ℂ} (hF : ContinuousOn F s) (hs : ∀ a ∈ s, F a ≠ 0) :
    ContinuousOn (fun a => riemannZeta (1 + F a)) s := by
  refine (differentiableOn_riemannZeta.continuousOn).comp (continuousOn_const.add hF) ?_
  intro a ha
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact fun hcon => hs a ha (add_eq_left.mp hcon)

lemma differentiableOn_riemannZeta_one_add_comp {α : Type*} [NormedAddCommGroup α]
    [NormedSpace ℂ α] {s : Set α} {F : α → ℂ} (hF : DifferentiableOn ℂ F s)
    (hs : ∀ a ∈ s, F a ≠ 0) :
    DifferentiableOn ℂ (fun a => riemannZeta (1 + F a)) s := by
  refine differentiableOn_riemannZeta.comp
    ((differentiableOn_const (c := (1 : ℂ)) :
      DifferentiableOn ℂ (fun _ : α => (1 : ℂ)) s).add hF) ?_
  intro a ha
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact fun hcon => hs a ha (add_eq_left.mp hcon)

lemma continuousOn_G3R_comp {α : Type*} [TopologicalSpace α] {s : Set α}
    {F₁ F₂ : α → Fin m → ℂ} (h₁ : ∀ i, ContinuousOn (fun a => F₁ a i) s)
    (h₂ : ∀ i, ContinuousOn (fun a => F₂ a i) s)
    (hs : ∀ a ∈ s, ∀ i, 0 < (F₁ a i).re ∧ 0 < (F₂ a i).re) :
    ContinuousOn (fun a => G3R (F₁ a) (F₂ a)) s := by
  simp only [G3R]
  have key : ∀ j : Fin m, ContinuousOn (fun a => riemannZeta (1 + F₁ a j + F₂ a j)
      / (riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j))) s := by
    intro j
    have hnum : ContinuousOn (fun a => riemannZeta (1 + F₁ a j + F₂ a j)) s := by
      have hsum : ContinuousOn (fun a : α => 1 + F₁ a j + F₂ a j) s :=
        (continuousOn_const.add (h₁ j)).add (h₂ j)
      have hkey : ∀ a ∈ s, (F₁ a j + F₂ a j) ≠ 0 := by
        intro a ha hcon
        have h2 : (F₁ a j).re + (F₂ a j).re = 0 := by
          have h := congrArg Complex.re hcon
          simp only [Complex.add_re, Complex.zero_re] at h
          exact h
        have h3 := (hs a ha j).1
        have h4 := (hs a ha j).2
        linarith
      refine (differentiableOn_riemannZeta.continuousOn).comp hsum ?_
      intro a ha
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hc => hkey a ha (add_eq_left.mp (by rw [add_assoc] at hc; exact hc))
    have hden : ContinuousOn (fun a => riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j)) s :=
      (continuousOn_riemannZeta_one_add_comp (h₁ j) (fun a ha h0 => by
          exact absurd (hs a ha j).1 (by simp [h0]))).mul
        (continuousOn_riemannZeta_one_add_comp (h₂ j) (fun a ha h0 => by
          exact absurd (hs a ha j).2 (by simp [h0])))
    have hne : ∀ a ∈ s, riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j) ≠ 0 := by
      intro a ha
      refine mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re ?_) (riemannZeta_ne_zero_of_one_lt_re ?_)
      · have := (hs a ha j).1
        simp only [Complex.add_re, Complex.one_re]
        linarith
      · have := (hs a ha j).2
        simp only [Complex.add_re, Complex.one_re]
        linarith
    exact (hnum.div hden hne).congr fun a _ => by simp only [Pi.div_apply]
  exact continuousOn_finsetProd' _ fun j _ => key j

lemma differentiableOn_G3R_comp {α : Type*} [NormedAddCommGroup α] [NormedSpace ℂ α]
    {s : Set α} {F₁ F₂ : α → Fin m → ℂ}
    (h₁ : ∀ i, DifferentiableOn ℂ (fun a => F₁ a i) s)
    (h₂ : ∀ i, DifferentiableOn ℂ (fun a => F₂ a i) s)
    (hs : ∀ a ∈ s, ∀ i, 0 < (F₁ a i).re ∧ 0 < (F₂ a i).re) :
    DifferentiableOn ℂ (fun a => G3R (F₁ a) (F₂ a)) s := by
  simp only [G3R]
  have key : ∀ j : Fin m, DifferentiableOn ℂ (fun a => riemannZeta (1 + F₁ a j + F₂ a j)
      / (riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j))) s := by
    intro j
    have hnum : DifferentiableOn ℂ (fun a => riemannZeta (1 + F₁ a j + F₂ a j)) s := by
      have hsum : DifferentiableOn ℂ (fun a : α => 1 + F₁ a j + F₂ a j) s :=
        ((differentiableOn_const (c := (1 : ℂ)) :
          DifferentiableOn ℂ (fun _ : α => (1 : ℂ)) s).add (h₁ j)).add (h₂ j)
      have hkey : ∀ a ∈ s, (F₁ a j + F₂ a j) ≠ 0 := by
        intro a ha hcon
        have h2 : (F₁ a j).re + (F₂ a j).re = 0 := by
          have h := congrArg Complex.re hcon
          simp only [Complex.add_re, Complex.zero_re] at h
          exact h
        have h3 := (hs a ha j).1
        have h4 := (hs a ha j).2
        linarith
      refine differentiableOn_riemannZeta.comp hsum ?_
      intro a ha
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hc => hkey a ha (add_eq_left.mp (by rw [add_assoc] at hc; exact hc))
    have hden : DifferentiableOn ℂ
        (fun a => riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j)) s :=
      (differentiableOn_riemannZeta_one_add_comp (h₁ j) (fun a ha h0 => by
          exact absurd (hs a ha j).1 (by simp [h0]))).mul
        (differentiableOn_riemannZeta_one_add_comp (h₂ j) (fun a ha h0 => by
          exact absurd (hs a ha j).2 (by simp [h0])))
    have hne : ∀ a ∈ s, riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j) ≠ 0 := by
      intro a ha
      refine mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re ?_) (riemannZeta_ne_zero_of_one_lt_re ?_)
      · have := (hs a ha j).1
        simp only [Complex.add_re, Complex.one_re]
        linarith
      · have := (hs a ha j).2
        simp only [Complex.add_re, Complex.one_re]
        linarith
    have hinv : DifferentiableOn ℂ
        (fun a => (riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j))⁻¹) s :=
      DifferentiableOn.inv hden hne
    have hdiv : DifferentiableOn ℂ (fun a => riemannZeta (1 + F₁ a j + F₂ a j)
        * (riemannZeta (1 + F₁ a j) * riemannZeta (1 + F₂ a j))⁻¹) s :=
      hnum.mul hinv
    exact hdiv.congr fun a _ => div_eq_mul_inv _ _
  exact differentiableOn_finsetProd'' _ fun j _ => key j

lemma continuousOn_Ker_comp {α : Type*} [TopologicalSpace α] {s : Set α}
    {F₁ F₂ : α → Fin m → ℂ} (h₁ : ∀ i, ContinuousOn (fun a => F₁ a i) s)
    (h₂ : ∀ i, ContinuousOn (fun a => F₂ a i) s) (R : ℕ) (hR : (R : ℂ) ≠ 0)
    (hs : ∀ a ∈ s, ∀ i, F₁ a i ≠ 0 ∧ F₂ a i ≠ 0) :
    ContinuousOn (fun a => Ker R (F₁ a) (F₂ a)) s := by
  simp only [Ker]
  have key : ∀ i : Fin m, ContinuousOn
      (fun a => (R : ℂ) ^ (F₁ a i) * (R : ℂ) ^ (F₂ a i)
        * (((F₁ a i) ^ 2 * (F₂ a i) ^ 2)⁻¹)) s := by
    intro i
    have hpow₁ : ContinuousOn (fun a => (R : ℂ) ^ (F₁ a i)) s :=
      (h₁ i).const_cpow (Or.inl hR)
    have hpow₂ : ContinuousOn (fun a => (R : ℂ) ^ (F₂ a i)) s :=
      (h₂ i).const_cpow (Or.inl hR)
    have hinv : ContinuousOn (fun a => (((F₁ a i) ^ 2 * (F₂ a i) ^ 2)⁻¹)) s :=
      (((h₁ i).pow 2).mul ((h₂ i).pow 2)).inv₀ fun a ha => by
        exact mul_ne_zero (pow_ne_zero 2 (hs a ha i).1) (pow_ne_zero 2 (hs a ha i).2)
    exact (hpow₁.mul hpow₂).mul hinv
  exact continuousOn_finsetProd' _ fun i _ => key i

lemma differentiableOn_Ker_comp {α : Type*} [NormedAddCommGroup α] [NormedSpace ℂ α]
    {s : Set α} {F₁ F₂ : α → Fin m → ℂ}
    (h₁ : ∀ i, DifferentiableOn ℂ (fun a => F₁ a i) s)
    (h₂ : ∀ i, DifferentiableOn ℂ (fun a => F₂ a i) s) (R : ℕ) (hR : (R : ℂ) ≠ 0)
    (hs : ∀ a ∈ s, ∀ i, F₁ a i ≠ 0 ∧ F₂ a i ≠ 0) :
    DifferentiableOn ℂ (fun a => Ker R (F₁ a) (F₂ a)) s := by
  simp only [Ker]
  have key : ∀ i : Fin m, DifferentiableOn ℂ
      (fun a => (R : ℂ) ^ (F₁ a i) * (R : ℂ) ^ (F₂ a i)
        * (((F₁ a i) ^ 2 * (F₂ a i) ^ 2)⁻¹)) s := by
    intro i
    have hpow₁ : DifferentiableOn ℂ (fun a => (R : ℂ) ^ (F₁ a i)) s :=
      (h₁ i).const_cpow (Or.inl hR)
    have hpow₂ : DifferentiableOn ℂ (fun a => (R : ℂ) ^ (F₂ a i)) s :=
      (h₂ i).const_cpow (Or.inl hR)
    have hinv : DifferentiableOn ℂ (fun a => (((F₁ a i) ^ 2 * (F₂ a i) ^ 2)⁻¹)) s :=
      DifferentiableOn.inv (((h₁ i).pow 2).mul ((h₂ i).pow 2)) fun a ha => by
        exact mul_ne_zero (pow_ne_zero 2 (hs a ha i).1) (pow_ne_zero 2 (hs a ha i).2)
    exact (hpow₁.mul hpow₂).mul hinv
  exact differentiableOn_finsetProd'' _ fun i _ => key i

/-! ## 3. The §10 integrand of the contour shift, and its continuity on a strip -/

/-- The §10 integrand for the vertical shift: `(G₁G₂G₃)·Ker`. -/
noncomputable def Psi (R : ℕ) (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (z z' : Fin m → ℂ) : ℂ :=
  (G1u W A b z z' * G2u W z z' * G3R z z') * Ker R z z'

lemma mem_goodRegion_of_strip {a bb : ℝ} (hm : 1 ≤ m) (ha : 0 < a)
    {x : (Fin m → ℂ) × (Fin m → ℂ)} (hx : x ∈ stripPair (m := m) a bb) :
    x ∈ goodRegion m (-(1 / (6 * (m : ℝ)))) := by
  rw [mem_stripPair] at hx
  have h6 : (0 : ℝ) < 6 * (m : ℝ) := by
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hneg : -(1 / (6 * (m : ℝ))) < 0 := by
    rw [neg_lt_zero]; positivity
  exact ⟨fun i => lt_trans hneg (lt_of_lt_of_le ha (hx.1 i).1),
    fun i => lt_trans hneg (lt_of_lt_of_le ha (hx.2 i).1)⟩

lemma continuousOn_G3R_pair {a bb : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => G3R x.1 x.2) (stripPair (m := m) a bb) := by
  refine continuousOn_G3R_comp (s := stripPair (m := m) a bb) (fun i => ?_) (fun i => ?_)
    (fun x hx i => ?_)
  · exact ((continuous_apply i).comp continuous_fst).continuousOn.mono (Set.subset_univ _)
  · exact ((continuous_apply i).comp continuous_snd).continuousOn.mono (Set.subset_univ _)
  · rw [mem_stripPair] at hx
    exact ⟨lt_of_lt_of_le ha (hx.1 i).1, lt_of_lt_of_le ha (hx.2 i).1⟩

lemma continuousOn_Ker_pair {a bb : ℝ} (ha : 0 < a) {R : ℕ} (hR0 : (R : ℂ) ≠ 0) :
    ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) => Ker R x.1 x.2) (stripPair (m := m) a bb) := by
  refine continuousOn_Ker_comp (s := stripPair (m := m) a bb) (fun i => ?_) (fun i => ?_) R hR0
    (fun x hx i => ?_)
  · exact ((continuous_apply i).comp continuous_fst).continuousOn.mono (Set.subset_univ _)
  · exact ((continuous_apply i).comp continuous_snd).continuousOn.mono (Set.subset_univ _)
  · rw [mem_stripPair] at hx
    refine ⟨fun h0 => absurd (lt_of_lt_of_le ha (hx.1 i).1) (by simp [h0]), fun h0 =>
      absurd (lt_of_lt_of_le ha (hx.2 i).1) (by simp [h0])⟩

lemma continuousOn_Psi (H : LocHyp W Amax A b) (R : ℕ) (hR0 : (R : ℂ) ≠ 0) {a bb : ℝ}
    (ha : 0 < a) :
    ContinuousOn (Function.uncurry (Psi (t := t) R W A b)) (stripPair (m := m) a bb) := by
  have hsub : stripPair (m := m) a bb ⊆ goodRegion m (-(1 / (6 * (m : ℝ)))) :=
    fun x hx => mem_goodRegion_of_strip H.hm ha hx
  have h12 : ContinuousOn (fun x : (Fin m → ℂ) × (Fin m → ℂ) =>
      G1u W A b x.1 x.2 * G2u W x.1 x.2) (stripPair (m := m) a bb) :=
    ((continuousOn_G1u H).mono hsub).mul ((continuousOn_G2u H).mono hsub)
  exact (h12.mul (continuousOn_G3R_pair (m := m) ha)).mul
    (continuousOn_Ker_pair (m := m) ha hR0)

/-! ## 4. Holomorphy along the coordinate lines -/

lemma differentiableOn_G3R_curve₁ {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableOn ℂ (fun w : ℂ => G3R (Function.update z j w) z') {w : ℂ | 0 < w.re} :=
  differentiableOn_G3R_comp (s := {w : ℂ | 0 < w.re})
    (fun i => (differentiableOn_update z j i).mono (Set.subset_univ _))
    (fun i => differentiableOn_const (c := z' i))
    (fun _w hw i => ⟨update_re_gt hz hw i, hz' i⟩)

lemma differentiableOn_G3R_curve₂ {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableOn ℂ (fun w : ℂ => G3R z (Function.update z' j w)) {w : ℂ | 0 < w.re} :=
  differentiableOn_G3R_comp (s := {w : ℂ | 0 < w.re})
    (fun i => differentiableOn_const (c := z i))
    (fun i => (differentiableOn_update z' j i).mono (Set.subset_univ _))
    (fun _w hw i => ⟨hz i, update_re_gt hz' hw i⟩)

lemma differentiableOn_Ker_curve₁ {R : ℕ} (hR : (R : ℂ) ≠ 0) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableOn ℂ (fun w : ℂ => Ker R (Function.update z j w) z') {w : ℂ | 0 < w.re} :=
  differentiableOn_Ker_comp (s := {w : ℂ | 0 < w.re})
    (fun i => (differentiableOn_update z j i).mono (Set.subset_univ _))
    (fun i => differentiableOn_const (c := z' i)) R hR
    (fun _w hw i => ⟨Complex.ne_zero_of_re_pos (update_re_gt hz hw i), Complex.ne_zero_of_re_pos (hz' i)⟩)

lemma differentiableOn_Ker_curve₂ {R : ℕ} (hR : (R : ℂ) ≠ 0) {z z' : Fin m → ℂ} {j : Fin m}
    (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableOn ℂ (fun w : ℂ => Ker R z (Function.update z' j w)) {w : ℂ | 0 < w.re} :=
  differentiableOn_Ker_comp (s := {w : ℂ | 0 < w.re})
    (fun i => differentiableOn_const (c := z i))
    (fun i => (differentiableOn_update z' j i).mono (Set.subset_univ _)) R hR
    (fun _w hw i => ⟨Complex.ne_zero_of_re_pos (hz i), Complex.ne_zero_of_re_pos (update_re_gt hz' hw i)⟩)

lemma neg_sixth_lt_zero {m : ℕ} (hm : 1 ≤ m) : -(1 / (6 * (m : ℝ))) < 0 := by
  rw [neg_lt_zero]
  have h : (0 : ℝ) < (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  positivity

lemma differentiableAt_Psi_curve₁ (H : LocHyp W Amax A b) (R : ℕ) (hR0 : (R : ℂ) ≠ 0)
    {z z' : Fin m → ℂ} {j : Fin m} (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableAt ℂ (fun w : ℂ => Psi R W A b (Function.update z j w) z') (z j) := by
  have hneg := neg_sixth_lt_zero H.hm
  have hz6 : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re := fun i => lt_trans hneg (hz i)
  have hz6' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re := fun i => lt_trans hneg (hz' i)
  have hs : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z j ∈ {w : ℂ | 0 < w.re} := hz j
  rw [show Psi R W A b = fun z z' => (G1u W A b z z' * G2u W z z' * G3R z z') * Ker R z z'
    from rfl]
  exact (((differentiableAt_G1u_curve₁ H hz6 hz6').mul
      (differentiableAt_G2u_curve₁ H hz6 hz6')).mul
    ((differentiableOn_G3R_curve₁ hz hz').differentiableAt (hs.mem_nhds hmem))).mul
    ((differentiableOn_Ker_curve₁ hR0 hz hz').differentiableAt (hs.mem_nhds hmem))

lemma differentiableAt_Psi_curve₂ (H : LocHyp W Amax A b) (R : ℕ) (hR0 : (R : ℂ) ≠ 0)
    {z z' : Fin m → ℂ} {j : Fin m} (hz : ∀ i, 0 < (z i).re) (hz' : ∀ i, 0 < (z' i).re) :
    DifferentiableAt ℂ (fun w : ℂ => Psi R W A b z (Function.update z' j w)) (z' j) := by
  have hneg := neg_sixth_lt_zero H.hm
  have hz6 : ∀ i, -(1 / (6 * (m : ℝ))) < (z i).re := fun i => lt_trans hneg (hz i)
  have hz6' : ∀ i, -(1 / (6 * (m : ℝ))) < (z' i).re := fun i => lt_trans hneg (hz' i)
  have hs : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z' j ∈ {w : ℂ | 0 < w.re} := hz' j
  rw [show Psi R W A b = fun z z' => (G1u W A b z z' * G2u W z z' * G3R z z') * Ker R z z'
    from rfl]
  exact (((differentiableAt_G1u_curve₂ H hz6 hz6').mul
      (differentiableAt_G2u_curve₂ H hz6 hz6')).mul
    ((differentiableOn_G3R_curve₂ hz hz').differentiableAt (hs.mem_nhds hmem))).mul
    ((differentiableOn_Ker_curve₂ hR0 hz hz').differentiableAt (hs.mem_nhds hmem))

/-! ## 5. The `g`-bound on the strip -/

lemma norm_G3R_le {a : ℝ} (ha : 0 < a) {z z' : Fin m → ℂ}
    (hz : ∀ i, a ≤ (z i).re) (hz' : ∀ i, a ≤ (z' i).re) :
    ‖G3R z z'‖ ≤ ∏ _j : Fin m, ((riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re) := by
  have hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + a) (by linarith))
  have hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + 2 * a) (by linarith))
  rw [G3R, norm_prod]
  refine Finset.prod_le_prod (s := Finset.univ) (f := fun j : Fin m =>
      ‖riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j))‖)
    (g := fun _ : Fin m => (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re)
    (fun j _ => norm_nonneg _) fun j _ => ?_
  have h1 : ‖riemannZeta (1 + z j + z' j)‖ ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re := by
    refine Commons.NumberTheory.Zeta.norm_riemannZeta_le_one_add (a := 2 * a) (by linarith) ?_
    rw [Complex.add_re, Complex.add_re, Complex.one_re]
    linarith [hz j, hz' j]
  have h2 : ‖(riemannZeta (1 + z j))⁻¹‖ ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re := by
    refine Commons.NumberTheory.Zeta.norm_inv_riemannZeta_le_one_add (a := a) ha ?_
    rw [Complex.add_re, Complex.one_re]
    linarith [hz j]
  have h3 : ‖(riemannZeta (1 + z' j))⁻¹‖ ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re := by
    refine Commons.NumberTheory.Zeta.norm_inv_riemannZeta_le_one_add (a := a) ha ?_
    rw [Complex.add_re, Complex.one_re]
    linarith [hz' j]
  have heq : ‖riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j))‖
      = ‖riemannZeta (1 + z j + z' j)‖ * ‖(riemannZeta (1 + z j))⁻¹‖
        * ‖(riemannZeta (1 + z' j))⁻¹‖ := by
    rw [norm_div, norm_mul, div_eq_mul_inv, mul_inv, norm_inv, norm_inv]
    ring
  rw [heq]
  exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hZ2) h3 (norm_nonneg _)
    (mul_nonneg hZ2 hZ1)


/-! ## 6. The weight and the constant of the vertical shift -/

/-- The decay weight of the vertical shift: `(log(|t|+2)+1)/(a²+t²)`. -/
noncomputable def shiftWeight (a : ℝ) : ℝ → ℝ :=
  fun t => (Real.log (|t| + 2) + 1) / (a ^ 2 + t ^ 2)

/-- The constant `Cg` of the vertical-shift bound. -/
noncomputable def shiftBound (R W m : ℕ) (a bb : ℝ) : ℝ :=
  stripBound W m * ((R : ℝ) ^ (2 * bb)) ^ m
    * ((riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re) ^ m

lemma stripBound_nonneg (W m : ℕ) : 0 ≤ stripBound W m := by
  rw [stripBound]; positivity

lemma shiftWeight_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ shiftWeight a t := by
  rw [shiftWeight]
  refine div_nonneg ?_ (by positivity)
  have h1 : (0:ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  linarith

lemma inv_sq_le_shiftWeight {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (a ^ 2 + t ^ 2)⁻¹ ≤ shiftWeight a t := by
  rw [shiftWeight, inv_le_iff_one_le_mul₀ (by positivity)]
  have h1 : (1:ℝ) ≤ Real.log (|t| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
    linarith
  rw [div_mul_cancel₀ _ (by positivity)]
  exact h1

lemma shiftBound_nonneg {R W m : ℕ} {a bb : ℝ} (hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re)
    (hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re) :
    0 ≤ shiftBound R W m a bb := by
  rw [shiftBound]
  have hc : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    mul_nonneg (mul_nonneg hZ2 hZ1) hZ1
  exact mul_nonneg (mul_nonneg (stripBound_nonneg W m) (by positivity)) (pow_nonneg hc m)

/-! ## 7. The `g`-bound for `Ψ` on the strip -/

lemma norm_Ker_le {a bb : ℝ} (ha : 0 < a) {R : ℕ} (hR : 0 < R) {z z' : Fin m → ℂ}
    (hz : ∀ i, a ≤ (z i).re ∧ (z i).re ≤ bb)
    (hz' : ∀ i, a ≤ (z' i).re ∧ (z' i).re ≤ bb) :
    ‖Ker R z z'‖ ≤ ((R : ℝ) ^ (2 * bb)) ^ m
      * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) := by
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hper : ∀ i : Fin m, ‖(R : ℂ) ^ (z i) * (R : ℂ) ^ (z' i)
      * (((z i) ^ 2 * (z' i) ^ 2)⁻¹)‖ ≤ (R : ℝ) ^ (2 * bb)
      * (((a ^ 2 + (z i).im ^ 2) * (a ^ 2 + (z' i).im ^ 2))⁻¹) := by
    intro i
    have hnorm : ‖(R : ℂ) ^ (z i) * (R : ℂ) ^ (z' i) * (((z i) ^ 2 * (z' i) ^ 2)⁻¹)‖
        = (R : ℝ) ^ ((z i).re) * (R : ℝ) ^ ((z' i).re)
          * ((‖z i‖ ^ 2 * ‖z' i‖ ^ 2)⁻¹) := by
      rw [norm_mul, norm_mul, norm_inv, norm_mul, norm_pow, norm_pow,
        ← Complex.ofReal_natCast R,
        Complex.norm_cpow_eq_rpow_re_of_pos hR0 (z i),
        Complex.norm_cpow_eq_rpow_re_of_pos hR0 (z' i)]
    rw [hnorm]
    have h1 : (R : ℝ) ^ ((z i).re) ≤ (R : ℝ) ^ bb :=
      Real.rpow_le_rpow_of_exponent_le hR1 (hz i).2
    have h2 : (R : ℝ) ^ ((z' i).re) ≤ (R : ℝ) ^ bb :=
      Real.rpow_le_rpow_of_exponent_le hR1 (hz' i).2
    have hA : a ^ 2 + (z i).im ^ 2 ≤ ‖z i‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [ha, (hz i).1]
    have hB : a ^ 2 + (z' i).im ^ 2 ≤ ‖z' i‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [ha, (hz' i).1]
    have hinv : (‖z i‖ ^ 2 * ‖z' i‖ ^ 2)⁻¹
        ≤ ((a ^ 2 + (z i).im ^ 2) * (a ^ 2 + (z' i).im ^ 2))⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      exact mul_le_mul hA hB (by positivity) (sq_nonneg _)
    calc (R : ℝ) ^ ((z i).re) * (R : ℝ) ^ ((z' i).re) * ((‖z i‖ ^ 2 * ‖z' i‖ ^ 2)⁻¹)
        ≤ (R : ℝ) ^ bb * (R : ℝ) ^ bb
            * (((a ^ 2 + (z i).im ^ 2) * (a ^ 2 + (z' i).im ^ 2))⁻¹) := by
          refine mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) hinv
            (by positivity) (by positivity)
      _ = (R : ℝ) ^ (2 * bb)
            * (((a ^ 2 + (z i).im ^ 2) * (a ^ 2 + (z' i).im ^ 2))⁻¹) := by
          rw [← Real.rpow_add hR0]; congr 1; ring
  calc ‖Ker R z z'‖ = ∏ i, ‖(R : ℂ) ^ (z i) * (R : ℂ) ^ (z' i)
        * (((z i) ^ 2 * (z' i) ^ 2)⁻¹)‖ := by rw [Ker, norm_prod]
    _ ≤ ∏ i, ((R : ℝ) ^ (2 * bb)
          * (((a ^ 2 + (z i).im ^ 2) * (a ^ 2 + (z' i).im ^ 2))⁻¹)) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hper i
    _ = ((R : ℝ) ^ (2 * bb)) ^ m
          * (∏ i, (((a ^ 2 + (z i).im ^ 2) * (a ^ 2 + (z' i).im ^ 2))⁻¹)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ((R : ℝ) ^ (2 * bb)) ^ m
          * ((∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹)) := by
        congr 1
        rw [Finset.prod_congr rfl (fun i _ => mul_inv _ _), Finset.prod_mul_distrib]
    _ = ((R : ℝ) ^ (2 * bb)) ^ m * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹)
          * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) := by ring

lemma norm_Psi_le {a bb : ℝ} (ha : 0 < a) (H : LocHyp W Amax A b) {R : ℕ} (hR : 1 ≤ R)
    {z z' : Fin m → ℂ}
    (hz : ∀ i, a ≤ (z i).re ∧ (z i).re ≤ bb)
    (hz' : ∀ i, a ≤ (z' i).re ∧ (z' i).re ≤ bb) :
    ‖Psi R W A b z z'‖ ≤ shiftBound R W m a bb
      * (∏ i, shiftWeight a ((z i).im)) * (∏ i, shiftWeight a ((z' i).im)) := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR0 : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le one_pos hR1
  have hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + a) (by linarith))
  have hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + 2 * a) (by linarith))
  have hc : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
      * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    mul_nonneg (mul_nonneg hZ2 hZ1) hZ1
  have hE : 0 ≤ Real.exp (∑' n : ℕ, e1pMajor m n) := Real.exp_nonneg _
  have hD : 0 ≤ (32 : ℝ) ^ (m * W.divisors.card) := by positivity
  have hK : 0 ≤ ((R : ℝ) ^ (2 * bb)) ^ m
      * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) := by
    refine mul_nonneg (mul_nonneg (by positivity) ?_) ?_ <;>
      exact Finset.prod_nonneg fun i _ => by positivity
  have hprod : (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) ≤ ∏ i, shiftWeight a ((z i).im) :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => inv_sq_le_shiftWeight ha _)
  have hprod' : (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) ≤ ∏ i, shiftWeight a ((z' i).im) :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => inv_sq_le_shiftWeight ha _)
  have hSB := shiftBound_nonneg (R := R) (W := W) (m := m) (bb := bb) hZ1 hZ2
  have hneg : -(1 / (6 * (m : ℝ))) < 0 := neg_sixth_lt_zero H.hm
  have hz6 : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z i).re :=
    fun i => le_of_lt (lt_trans hneg (lt_of_lt_of_le ha (hz i).1))
  have hz6' : ∀ i, -(1 / (6 * (m : ℝ))) ≤ (z' i).re :=
    fun i => le_of_lt (lt_trans hneg (lt_of_lt_of_le ha (hz' i).1))
  have hstep := norm_G1u_le (z := z) (z' := z') H hz6 hz6'
  have hstep2 := norm_G2u_le (z := z) (z' := z') H hz6 hz6'
  have hstep3 := norm_G3R_le (m := m) (z := z) (z' := z') ha (fun i => (hz i).1) (fun i => (hz' i).1)
  have hstep4 := norm_Ker_le (m := m) (z := z) (z' := z') ha (by omega : 0 < R) hz hz'
  calc ‖Psi R W A b z z'‖
      ≤ (Real.exp (∑' n : ℕ, e1pMajor m n) * (32 : ℝ) ^ (m * W.divisors.card)
            * (∏ _j : Fin m, ((riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re
              * (riemannZeta ((1 + a : ℝ) : ℂ)).re * (riemannZeta ((1 + a : ℝ) : ℂ)).re)))
          * (((R : ℝ) ^ (2 * bb)) ^ m
            * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹) * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹)) := by
        rw [Psi, norm_mul, norm_mul, norm_mul]
        refine mul_le_mul (mul_le_mul (mul_le_mul hstep hstep2 (norm_nonneg _) hE) hstep3
          (norm_nonneg _) (mul_nonneg hE hD)) hstep4 (by positivity)
          (mul_nonneg (mul_nonneg hE hD) (Finset.prod_nonneg fun j _ => hc))
    _ = shiftBound R W m a bb * (∏ i, (a ^ 2 + (z i).im ^ 2)⁻¹)
          * (∏ i, (a ^ 2 + (z' i).im ^ 2)⁻¹) := by
        rw [shiftBound, stripBound, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ ≤ shiftBound R W m a bb * (∏ i, shiftWeight a ((z i).im))
          * (∏ i, shiftWeight a ((z' i).im)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hprod hSB) hprod'
          (Finset.prod_nonneg fun i _ => by positivity)
          (mul_nonneg hSB (Finset.prod_nonneg fun i _ => shiftWeight_nonneg ha _))

/-! ## 8. The vertical shift `Γ_{bb} → Γ_a` -/

theorem contourShift_Psi (H : LocHyp W Amax A b) {R : ℕ} (hR : 3 ≤ R) {a bb : ℝ}
    (ha : 0 < a) (hab : a ≤ bb) :
    (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Psi R W A b (fun i => sline bb (t i)) (fun i => sline bb (t' i)))
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Psi R W A b (fun i => sline a (t i)) (fun i => sline a (t' i)) := by
  have hRpos : 0 < R := by omega
  have hR1 : 1 ≤ R := by omega
  have hR1R : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hR0R : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le one_pos hR1R
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hZ1 : 0 ≤ (riemannZeta ((1 + a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + a) (by linarith))
  have hZ2 : 0 ≤ (riemannZeta ((1 + 2 * a : ℝ) : ℂ)).re :=
    le_of_lt (Commons.NumberTheory.Zeta.re_riemannZeta_ofReal_pos (σ := 1 + 2 * a) (by linarith))
  exact (integral_vertical_shift_pair (m := m) hab (Psi R W A b)
    (shiftBound_nonneg (R := R) (W := W) (m := m) (bb := bb) hZ1 hZ2)
    (shiftWeight_nonneg ha)
    (Commons.Analysis.Integral.integrable_tendsto_log_inv_sq ha).1
    (Commons.Analysis.Integral.integrable_tendsto_log_inv_sq ha).2.1
    (Commons.Analysis.Integral.integrable_tendsto_log_inv_sq ha).2.2
    (fun z z' hz hz' => norm_Psi_le ha H hR1 hz hz')
    (continuousOn_Psi H R hRc ha)
    (fun j z z' hz hz' => differentiableAt_Psi_curve₁ H R hRc
      (fun i => lt_of_lt_of_le ha (hz i).1) (fun i => lt_of_lt_of_le ha (hz' i).1))
    (fun j z z' hz hz' => differentiableAt_Psi_curve₂ H R hRc
      (fun i => lt_of_lt_of_le ha (hz i).1) (fun i => lt_of_lt_of_le ha (hz' i).1))).symm


/-- On `Re = c > 1` the §10 integrand `Eker` is the shifted integrand `Psi`. -/
lemma Eker_eq_Psi {c : ℝ} (hc : 1 < c) (H : LocHyp W Amax A b) (R : ℕ)
    (p : Fin m → ℝ × ℝ) :
    Eker (t := t) c R W A b p
      = Psi R W A b (fun i => sline c ((p i).1)) (fun i => sline c ((p i).2)) := by
  have hz : ∀ j, 1 < (sline c ((p j).1)).re := fun j => by simpa [sline] using hc
  have hz' : ∀ j, 1 < (sline c ((p j).2)).re := fun j => by simpa [sline] using hc
  rw [Eker, Psi, tprod_eulerFactor_eq H (z := fun i => sline c ((p i).1))
    (z' := fun i => sline c ((p i).2)) hz hz']

/-- `zetaM1Eta R t` is the point of `Γ_{1/log R}` with parameter `t`. -/
lemma zetaM1Eta_eq_sline {R t : ℝ} :
    Commons.NumberTheory.Zeta.zetaM1Eta R t = sline (1 / Real.log R) t := rfl

/-- The §10 integrand of the shifted contour is the one of Green–Tao Lemma 10.4. -/
lemma Psi_mul_I_eq {R : ℕ} (hRc : (R : ℂ) ≠ 0) {a : ℝ} (t t' : Fin m → ℝ) :
    Psi R W A b (fun i => sline a (t i)) (fun i => sline a (t' i))
        * (Complex.I ^ m * Complex.I ^ m)
      = ((G1u W A b (fun j => sline a (t j)) (fun j => sline a (t' j))
              * G2u W (fun j => sline a (t j)) (fun j => sline a (t' j)))
          * (∏ j, (riemannZeta (1 + sline a (t j) + sline a (t' j))
              / (riemannZeta (1 + sline a (t j)) * riemannZeta (1 + sline a (t' j)))))
          * (((R : ℝ)) : ℂ) ^ (∑ j, (sline a (t j) + sline a (t' j)))
          * (∏ j, ((sline a (t j)) ^ 2 * (sline a (t' j)) ^ 2)⁻¹))
        * Complex.I ^ m * Complex.I ^ m := by
  simp only [Psi, Ker_eq (m := m) hRc, G3R, zetaM1Eta_eq_sline, Complex.ofReal_natCast]
  ring

/-- **Green–Tao (10.2) = (ddr)**: the main term of the box average equals
`G₁(0,0)G₂(0,0)(log R)^m` up to Green–Tao's error. -/
theorem mainSum_eq_logR (H : LocHyp W Amax A b) {R : ℕ} (hR : 3 ≤ R) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ‖(mainSum (m := m) (t := t) R W A b : ℂ)
          - (G1u W A b 0 0 * G2u (m := m) W 0 0) * (Real.log (R : ℝ)) ^ m‖
        ≤ C ^ m * stripBound W m * (1 + (Real.log (R : ℝ)) ^ (m - 1))
          + C ^ m * stripBound W m * Real.exp (-(δ * Real.sqrt (Real.log (R : ℝ)))) := by
  obtain ⟨δ, C, hδ, hC, hmain⟩ := zetaBound_G1G2 H
  refine ⟨δ, C, hδ, hC, ?_⟩
  have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hR1
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3one : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have ha : 0 < 1 / Real.log (R : ℝ) := by positivity
  have hlogle : Real.log 3 ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hab : 1 / Real.log (R : ℝ) ≤ 1 + (m : ℝ) := by
    have h1 : 1 / Real.log (R : ℝ) ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le hlog3 hlogle
    have h2 : 1 / Real.log 3 ≤ 1 := by
      rw [div_le_one hlog3]; exact le_of_lt hlog3one
    have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
    linarith
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < R))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast H.hm
  have hc1m : (1 : ℝ) < 1 + (m : ℝ) := by linarith
  have hmain' := hmain (R : ℝ) (by exact_mod_cast hR)
  rw [mainSum_eq_contour (m := m) (t := t) H.hm (c := 1 + (m : ℝ)) (by linarith) R W A b
      H.ht H.hA H.hne H.hW0, ContourInt_eq]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Eker (t := t) (1 + (m : ℝ)) R W A b (fun i => (t_ i, t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)) by
    simp_rw [Eker_eq_Psi hc1m H R]]
  rw [show (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 + (m : ℝ)) (t_ i))
          (fun i => sline (1 + (m : ℝ)) (t_' i)))
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) from
    contourShift_Psi H hR ha hab]
  -- move `I^m * I^m` inside the two integrals
  simp_rw [← MeasureTheory.integral_mul_const]
  -- identify the integrand with the one of Green–Tao Lemma 10.4
  have hI : (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
        Psi R W A b (fun i => sline (1 / Real.log (R : ℝ)) (t_ i))
          (fun i => sline (1 / Real.log (R : ℝ)) (t_' i)) * (Complex.I ^ m * Complex.I ^ m))
      = (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
          (G1u W A b (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
            * G2u W (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
                + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j))
              / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j))
                  * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))))
          * (((R : ℝ)) : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)
              + Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)))
          * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_ j)) ^ 2
                * (Commons.NumberTheory.Zeta.zetaM1Eta (R : ℝ) (t_' j)) ^ 2)⁻¹)
          * Complex.I ^ m * Complex.I ^ m) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t_' => ?_)
    exact Psi_mul_I_eq hRc t_ t_'
  rw [hI]
  exact hmain'

end BoxAvg
end GYMaj

/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Plate
import Submission.Commons.Measure.Integral.abs_rpow_le_convolution_abs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod


/-!
# The class `𝒞(U)`: Fourier transforms of finite complex measures supported in `U`

This module lays the foundational vocabulary for the formalisation of the
Guo–Li–Yung–Zorin-Kranich "short proof" of ℓ²-decoupling for the moment curve
(arXiv:1912.09798), the route recommended in `ROADMAP.lean`.

GLYZ state all decoupling constants for tuples `(f_J)` with `supp f̂_J ⊆ 𝒰_J`;
the three ways the frequency support is used are

* the **uncertainty principle** `|f|^p ≲ |f|^p * φ_J`,
* **affine rescaling** (`supp (f^*)^ ⊆ A_J^{-1} supp f̂`),
* **restriction to translates** `H + z` of hyperplanes.

Rather than formalising a general theory of the Fourier transform of
distributions we represent "`supp f̂ ⊆ U`" by an *explicit* datum

    `f(x) = ∫ u, e(⟪x, Γ u⟫) φ u ∂ν u`

with `ν` a finite measure on an arbitrary index type, `φ ∈ L¹(ν)` measurable,
`Γ` measurable and `Γ u ∈ U` for every `u` with `φ u ≠ 0`.  This is exactly
"`f` is the Fourier transform of the finite complex measure `Γ_*(φ ν)`", and it
is closed under all the operations the proof needs:

* sums and scalar multiples (disjoint union `ι₁ ⊕ ι₂` of the index types),
* precomposition with the *inverse* of an affine map `A_I` — the "affine
  rescaling" of GLYZ Lemma 2.2, whose geometric input
  `A_I ⁻¹' 𝒰_J = 𝒰_{J_I}` is `Plate.affMap_preimage_plate`;
* restriction to `H + z` (replace `Γ` by `P_H ∘ Γ` and `φ` by `e(⟪z,Γ·⟫)φ`),
  so that the lower-degree decoupling step applies;
* multiplication by a Schwartz bump (replace `Γ` by `(u,η) ↦ Γ u + η` and `φ`
  by the tensor product `φ ⊗ ψ̂`; the index type becomes the product).

The payoff is the uncertainty principle: if `ψ̂ ≡ 1` on a neighbourhood of `U`
then `f = f * ψ` for every `f` in the class (a pure Fubini computation), whence
`|f|^p ≲ (|f|^p) * |ψ|` and, once `|ψ| ≲ φ_J`, GLYZ Lemma 3.2.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The unit character -/

/-- The unit character `x ↦ e(⟪x,ξ⟫)` on `E k`. -/
def chat (k : ℕ) (x ξ : E k) : ℂ :=
  Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((⟪x, ξ⟫ : ℝ) : ℂ))

/-- The unit character has modulus one. -/
lemma chat_norm (k : ℕ) (x ξ : E k) : ‖chat k x ξ‖ = 1 := by
  rw [chat, Complex.norm_exp]
  simp

/-- The character is multiplicative in the frequency variable. -/
lemma chat_add (k : ℕ) (x ξ η : E k) : chat k x (ξ + η) = chat k x ξ * chat k x η := by
  rw [chat, chat, chat, inner_add_right, ofReal_add, mul_add, Complex.exp_add]

/-- The character is multiplicative in the space variable. -/
lemma chat_add_left (k : ℕ) (x y ξ : E k) : chat k (x + y) ξ = chat k x ξ * chat k y ξ := by
  rw [chat, chat, chat, inner_add_left, ofReal_add, mul_add, Complex.exp_add]

/-- `chat` applied to the moment curve is the moment-curve character `momChar`. -/
lemma chat_gammaVec (k : ℕ) (x : E k) (t : ℝ) : chat k x (gammaVec k t) = momChar k x t := by
  simp only [chat, momChar, inner_gamma, momPhase]

/-- The character is unimodular, hence continuous in the second variable too. -/
lemma chat_sub (k : ℕ) (x ξ η : E k) : chat k x (ξ - η) = chat k x ξ * (chat k x η)⁻¹ := by
  rw [chat, chat, chat, inner_sub_right, ofReal_sub, mul_sub, Complex.exp_sub, div_eq_mul_inv]

/-- Continuity of the character in its first variable. -/
lemma continuous_chat_left (k : ℕ) (x : E k) : Continuous (fun ξ : E k => chat k x ξ) := by
  unfold chat
  fun_prop

/-- Continuity of the character. -/
lemma continuous_chat_uncurry (k : ℕ) : Continuous (fun p : E k × E k => chat k p.1 p.2) := by
  unfold chat
  fun_prop

/-! ## 2. The class -/

/-- **The class `𝒞(U)`**: `f` is the Fourier transform of a finite (complex) measure
supported in `U`, presented concretely.  There are an index type `ι`, a finite measure
`ν` on it, a measurable density `φ ∈ L¹(ν)` and a measurable map `Γ : ι → E k` with
`Γ u ∈ U` whenever `φ u ≠ 0`, such that `f x = ∫ u, e(⟪x,Γ u⟫) φ u ∂ν`. -/
def IsFourierRep (k : ℕ) (U : Set (E k)) (f : E k → ℂ) : Prop :=
  ∃ (ι : Type) (_ : MeasurableSpace ι) (Γ : ι → E k) (ν : Measure ι) (φ : ι → ℂ),
    IsFiniteMeasure ν ∧ Integrable φ ν ∧ Measurable Γ ∧ Measurable φ ∧
    (∀ u, φ u ≠ 0 → Γ u ∈ U) ∧
    (∀ x, f x = ∫ u, chat k x (Γ u) * φ u ∂ν)

/-- Membership in the class, unfolded. -/
lemma IsFourierRep.mk' {k : ℕ} {U : Set (E k)} {f : E k → ℂ}
    {ι : Type} [m : MeasurableSpace ι] {Γ : ι → E k} {ν : Measure ι} {φ : ι → ℂ}
    (hν : IsFiniteMeasure ν) (hφ : Integrable φ ν) (hΓ : Measurable Γ) (hmφ : Measurable φ)
    (hU : ∀ u, φ u ≠ 0 → Γ u ∈ U)
    (hf : ∀ x, f x = ∫ u, chat k x (Γ u) * φ u ∂ν) : IsFourierRep k U f :=
  ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩

/-- The zero function belongs to the class over every `U`. -/
lemma IsFourierRep.zero (k : ℕ) (U : Set (E k)) : IsFourierRep k U (fun _ => 0) := by
  refine IsFourierRep.mk' (ι := ℝ) (Γ := fun _ => 0) (ν := 0) (φ := fun _ => 0)
    isFiniteMeasureZero ?_ measurable_const measurable_const ?_ ?_
  · exact integrable_zero _ _ _
  · intro u hu; exact absurd rfl hu
  · intro x; simp

/-- The class is monotone in the set `U`. -/
lemma IsFourierRep.mono {k : ℕ} {U V : Set (E k)} {f : E k → ℂ}
    (hUV : U ⊆ V) (hf : IsFourierRep k U f) : IsFourierRep k V f := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩ := hf
  exact IsFourierRep.mk' hν hφ hΓ hmφ (fun u hu => hUV (hU u hu)) hf

section Add

variable {ι₁ ι₂ : Type*} [MeasurableSpace ι₁] [MeasurableSpace ι₂]

/-- Integrability on the first summand of a disjoint union. -/
lemma integrable_map_inl_iff (ν₁ : Measure ι₁) {F : ι₁ ⊕ ι₂ → ℂ} (hF : Measurable F) :
    Integrable F (ν₁.map Sum.inl) ↔ Integrable (fun u => F (Sum.inl u)) ν₁ :=
  integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable

/-- The integral over the first summand of a disjoint union. -/
lemma integral_map_inl (ν₁ : Measure ι₁) {F : ι₁ ⊕ ι₂ → ℂ} (hF : Measurable F) :
    (∫ s, F s ∂(ν₁.map Sum.inl)) = ∫ u, F (Sum.inl u) ∂ν₁ :=
  integral_map measurable_inl.aemeasurable hF.aestronglyMeasurable

/-- Integrability on the second summand of a disjoint union. -/
lemma integrable_map_inr_iff (ν₂ : Measure ι₂) {F : ι₁ ⊕ ι₂ → ℂ} (hF : Measurable F) :
    Integrable F (ν₂.map Sum.inr) ↔ Integrable (fun u => F (Sum.inr u)) ν₂ :=
  integrable_map_measure hF.aestronglyMeasurable measurable_inr.aemeasurable

/-- The integral over the second summand of a disjoint union. -/
lemma integral_map_inr (ν₂ : Measure ι₂) {F : ι₁ ⊕ ι₂ → ℂ} (hF : Measurable F) :
    (∫ s, F s ∂(ν₂.map Sum.inr)) = ∫ u, F (Sum.inr u) ∂ν₂ :=
  integral_map measurable_inr.aemeasurable hF.aestronglyMeasurable

end Add

/-- The class is closed under sums. -/
lemma IsFourierRep.add {k : ℕ} {U V : Set (E k)} {f g : E k → ℂ}
    (hf : IsFourierRep k U f) (hg : IsFourierRep k V g) : IsFourierRep k (U ∪ V) (f + g) := by
  obtain ⟨ι₁, m₁, Γ₁, ν₁, φ₁, hν₁, hφ₁, hΓ₁, hmφ₁, hU₁, hf⟩ := hf
  obtain ⟨ι₂, m₂, Γ₂, ν₂, φ₂, hν₂, hφ₂, hΓ₂, hmφ₂, hU₂, hg⟩ := hg
  letI := m₁
  letI := m₂
  haveI := hν₁
  haveI := hν₂
  have hm : Measurable (Sum.elim φ₁ φ₂ : ι₁ ⊕ ι₂ → ℂ) := hmφ₁.sumElim hmφ₂
  refine IsFourierRep.mk' (ι := ι₁ ⊕ ι₂) (Γ := Sum.elim Γ₁ Γ₂)
    (ν := ν₁.map Sum.inl + ν₂.map Sum.inr) (φ := Sum.elim φ₁ φ₂)
    inferInstance ?_ (hΓ₁.sumElim hΓ₂) hm ?_ ?_
  · rw [integrable_add_measure]
    exact ⟨(integrable_map_inl_iff ν₁ hm).mpr (by simpa using hφ₁),
      (integrable_map_inr_iff ν₂ hm).mpr (by simpa using hφ₂)⟩
  · intro s hs
    cases s with
    | inl u => exact Or.inl (hU₁ u hs)
    | inr u => exact Or.inr (hU₂ u hs)
  · intro x
    simp only [Pi.add_apply]
    have hc : Measurable (fun s : ι₁ ⊕ ι₂ => chat k x (Sum.elim Γ₁ Γ₂ s)) :=
      (continuous_chat_left k x).measurable.comp (hΓ₁.sumElim hΓ₂)
    have hmx : Measurable (fun s : ι₁ ⊕ ι₂ =>
        chat k x (Sum.elim Γ₁ Γ₂ s) * Sum.elim φ₁ φ₂ s) := hc.mul hm
    have hc1 : AEStronglyMeasurable (fun u : ι₁ => chat k x (Γ₁ u)) ν₁ :=
      ((continuous_chat_left k x).measurable.comp hΓ₁).aestronglyMeasurable
    have hc2 : AEStronglyMeasurable (fun u : ι₂ => chat k x (Γ₂ u)) ν₂ :=
      ((continuous_chat_left k x).measurable.comp hΓ₂).aestronglyMeasurable
    have hφ1' : Integrable (fun u : ι₁ => chat k x (Γ₁ u) * φ₁ u) ν₁ :=
      hφ₁.bdd_mul hc1 (Filter.Eventually.of_forall fun u => by rw [chat_norm])
    have hφ2' : Integrable (fun u : ι₂ => chat k x (Γ₂ u) * φ₂ u) ν₂ :=
      hφ₂.bdd_mul hc2 (Filter.Eventually.of_forall fun u => by rw [chat_norm])
    rw [hf x, hg x,
      integral_add_measure ((integrable_map_inl_iff ν₁ hmx).mpr (by simpa using hφ1'))
        ((integrable_map_inr_iff ν₂ hmx).mpr (by simpa using hφ2')),
      integral_map_inl ν₁ hmx, integral_map_inr ν₂ hmx]
    simp [mul_comm]

/-! ## 3. The representing function and its basic properties -/

/-- The function represented by the Fourier datum `(Γ, ν, φ)`. -/
def repFun (k : ℕ) {ι : Type*} [MeasurableSpace ι] (Γ : ι → E k) (ν : Measure ι)
    (φ : ι → ℂ) : E k → ℂ := fun x => ∫ u, chat k x (Γ u) * φ u ∂ν

/-- The class is exactly the set of representing functions of admissible data. -/
lemma isFourierRep_iff {k : ℕ} {U : Set (E k)} {f : E k → ℂ} :
    IsFourierRep k U f ↔ ∃ (ι : Type) (_ : MeasurableSpace ι) (Γ : ι → E k)
      (ν : Measure ι) (φ : ι → ℂ), IsFiniteMeasure ν ∧ Integrable φ ν ∧ Measurable Γ ∧
        Measurable φ ∧ (∀ u, φ u ≠ 0 → Γ u ∈ U) ∧ f = repFun k Γ ν φ := by
  constructor
  · rintro ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩
    exact ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, funext hf⟩
  · rintro ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩
    refine ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, ?_⟩
    intro x; rw [hf]; rfl

/-- Pointwise bound on a representing function. -/
lemma norm_repFun_le {k : ℕ} {ι : Type*} [MeasurableSpace ι] (Γ : ι → E k) (ν : Measure ι)
    {φ : ι → ℂ} (x : E k) :
    ‖repFun k Γ ν φ x‖ ≤ ∫ u, ‖φ u‖ ∂ν := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => by
    simp [chat_norm])

/-- A representing function is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_repFun {k : ℕ} {ι : Type*} [MeasurableSpace ι]
    {Γ : ι → E k} (hΓ : Measurable Γ) {ν : Measure ι} [SigmaFinite ν]
    {φ : ι → ℂ} (hφ : AEStronglyMeasurable φ ν) :
    AEStronglyMeasurable (repFun k Γ ν φ) volume := by
  have hc : Measurable (fun p : E k × ι => chat k p.1 (Γ p.2)) :=
    (continuous_chat_uncurry k).measurable.comp (measurable_fst.prodMk (hΓ.comp measurable_snd))
  exact (hc.aestronglyMeasurable.mul (hφ.comp_snd)).integral_prod_right'
    (μ := (volume : Measure (E k))) (ν := ν)

/-- The class is closed under additive inverses. -/
lemma IsFourierRep.neg {k : ℕ} {U : Set (E k)} {f : E k → ℂ} (hf : IsFourierRep k U f) :
    IsFourierRep k U (-f) := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩ := hf
  refine ⟨ι, m, Γ, ν, -φ, hν, hφ.neg, hΓ, hmφ.neg, fun u hu => hU u (neg_ne_zero.mp hu), ?_⟩
  intro x
  rw [Pi.neg_apply, hf x, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
    simp only [Pi.neg_apply]; ring_nf)

/-- The class is closed under scalar multiples. -/
lemma IsFourierRep.smul {k : ℕ} {U : Set (E k)} {f : E k → ℂ} (c : ℂ)
    (hf : IsFourierRep k U f) : IsFourierRep k U (c • f) := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩ := hf
  refine ⟨ι, m, Γ, ν, c • φ, hν, hφ.const_mul c, hΓ, hmφ.const_mul c,
    fun u hu => hU u (mul_ne_zero_iff.mp (by simpa [Pi.smul_apply] using hu)).2, ?_⟩
  intro x
  rw [Pi.smul_apply, hf x, ← integral_smul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
    simp only [Pi.smul_apply]; ring)

/-- The class is closed under finite sums. -/
lemma IsFourierRep.sum {k : ℕ} {ι : Type*} {U : ι → Set (E k)} {f : ι → E k → ℂ}
    (s : Finset ι) (hf : ∀ i ∈ s, IsFourierRep k (U i) (f i)) :
    IsFourierRep k (⋃ i ∈ s, U i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact IsFourierRep.zero k _
  | insert a t ha ih =>
      have h1 : IsFourierRep k (U a) (f a) := hf a (Finset.mem_insert_self a t)
      have h2 : IsFourierRep k (⋃ i ∈ t, U i) (∑ i ∈ t, f i) :=
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hEq : (⋃ i ∈ insert a t, U i) = U a ∪ (⋃ i ∈ t, U i) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨i, rfl | hi, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      have hsum : (∑ i ∈ insert a t, f i) = f a + ∑ i ∈ t, f i := Finset.sum_insert ha
      rw [hsum, hEq]
      exact h1.add h2

/-! ## 3b. Closure under multiplication (the frequency sets add) -/

/-- The pointwise (Minkowski) sum of two sets of frequencies: the support of the product
of two measures supported in `U` and `V` respectively.  We write it out explicitly rather
than using the `Pointwise` notation for `Set` to keep the file's notation scope unchanged. -/
def setPlus {k : ℕ} (U V : Set (E k)) : Set (E k) := {z | ∃ u ∈ U, ∃ v ∈ V, u + v = z}

lemma mem_setPlus {k : ℕ} {U V : Set (E k)} {z : E k} :
    z ∈ setPlus U V ↔ ∃ u ∈ U, ∃ v ∈ V, u + v = z := Iff.rfl

lemma setPlus_subset {k : ℕ} {U U' V V' : Set (E k)} (hU : U ⊆ U') (hV : V ⊆ V') :
    setPlus U V ⊆ setPlus U' V' := by
  rintro z ⟨u, hu, v, hv, rfl⟩
  exact ⟨u, hU hu, v, hV hv, rfl⟩

/-- **The class is closed under multiplication**, the frequency sets adding: if `f` is
represented by a finite measure supported in `U` and `v` by one supported in `V`, then
`f * v` is represented by the product measure, which is supported in `setPlus U V`.
This is the Fubini step used to multiply the pieces by a Schwartz bump. -/
lemma IsFourierRep.mul {k : ℕ} {U V : Set (E k)} {f v : E k → ℂ}
    (hf : IsFourierRep k U f) (hv : IsFourierRep k V v) :
    IsFourierRep k (setPlus U V) (f * v) := by
  obtain ⟨ι₁, m₁, Γ₁, ν₁, φ₁, hν₁, hφ₁, hΓ₁, hmφ₁, hU₁, hf⟩ := hf
  obtain ⟨ι₂, m₂, Γ₂, ν₂, φ₂, hν₂, hφ₂, hΓ₂, hmφ₂, hU₂, hv⟩ := hv
  letI := m₁
  letI := m₂
  haveI := hν₁
  haveI := hν₂
  refine IsFourierRep.mk' (ι := ι₁ × ι₂) (Γ := fun p => Γ₁ p.1 + Γ₂ p.2)
    (ν := ν₁.prod ν₂) (φ := fun p => φ₁ p.1 * φ₂ p.2) inferInstance ?_ ?_ ?_ ?_ ?_
  · exact hφ₁.mul_prod hφ₂
  · exact (hΓ₁.comp measurable_fst).add (hΓ₂.comp measurable_snd)
  · exact (hmφ₁.comp measurable_fst).mul (hmφ₂.comp measurable_snd)
  · intro p hp
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
    exact ⟨Γ₁ p.1, hU₁ p.1 h1, Γ₂ p.2, hU₂ p.2 h2, rfl⟩
  · intro x
    rw [Pi.mul_apply, hf x, hv x, ← MeasureTheory.integral_prod_mul
      (fun u : ι₁ => chat k x (Γ₁ u) * φ₁ u) (fun u : ι₂ => chat k x (Γ₂ u) * φ₂ u)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change (chat k x (Γ₁ p.1) * φ₁ p.1) * (chat k x (Γ₂ p.2) * φ₂ p.2)
      = chat k x (Γ₁ p.1 + Γ₂ p.2) * (φ₁ p.1 * φ₂ p.2)
    rw [chat_add]; ring

/-! ## 4. Linear structure of `affVec` and the affine rescaling of the class -/

/-- `affVec` as a linear map. -/
noncomputable def affVecLin (k : ℕ) (ρ t₀ : ℝ) : E k →ₗ[ℝ] E k where
  toFun := affVec k ρ t₀
  map_add' := by
    intro x y
    ext l
    simp only [PiLp.add_apply, affVec_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext l
    simp only [RingHom.id_apply, PiLp.smul_apply, smul_eq_mul, affVec_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Defining equation of `affVecLin`. -/
lemma affVecLin_apply (k : ℕ) (ρ t₀ : ℝ) (x : E k) : affVecLin k ρ t₀ x = affVec k ρ t₀ x :=
  rfl

/-- The transpose relation, in the form used by the rescaling identity. -/
lemma inner_affVecLin (k : ℕ) (ρ t₀ : ℝ) (x y : E k) :
    (⟪affVecLin k ρ t₀ x, y⟫ : ℝ) = ⟪x, affVecDual k ρ t₀ y⟫ := by
  rw [affVecLin_apply, real_inner_comm, ← inner_affVec_affVecDual, real_inner_comm]

/-- **The general linear rescaling identity.**  If `Linv` and `M` are adjoint to one
another (`∀ x y, ⟪M x, y⟫ = ⟪x, Linv y⟫`) then rescaling the frequency datum by the affine
map `y ↦ c + Linv y` multiplies the represented function by a unimodular phase and
precomposes it with `M`. -/
lemma repFun_linear_rescale (k : ℕ) {ι : Type} [MeasurableSpace ι]
    (Γ : ι → E k) (ν : Measure ι) (φ : ι → ℂ)
    (Linv M : E k →ₗ[ℝ] E k) (hM : ∀ x y : E k, ⟪M x, y⟫ = ⟪x, Linv y⟫) (c : E k) :
    repFun k (fun u => c + Linv (Γ u)) ν φ
      = fun x => chat k x c * repFun k Γ ν φ (M x) := by
  funext x
  simp only [repFun]
  have h1 : (∫ u, chat k x (c + Linv (Γ u)) * φ u ∂ν)
      = chat k x c * ∫ u, chat k x (Linv (Γ u)) * φ u ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change chat k x (c + Linv (Γ u)) * φ u = chat k x c * (chat k x (Linv (Γ u)) * φ u)
    rw [chat_add]; ring
  rw [h1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change chat k x (Linv (Γ u)) * φ u = chat k (M x) (Γ u) * φ u
  have h2 : chat k x (Linv (Γ u)) = chat k (M x) (Γ u) := by
    simp only [chat, hM]
  rw [h2]

/-- The rescaled frequency datum: `Γ' u = A^{-1}(Γ u)` for
`A = affMap k ρ t₀`. -/
noncomputable def rescaleRep (k : ℕ) (ρ t₀ : ℝ) {ι : Type} [MeasurableSpace ι]
    (Γ : ι → E k) (ν : Measure ι) (φ : ι → ℂ) : E k → ℂ :=
  repFun k (fun u => affMap k ρ⁻¹ (-t₀ / ρ) (Γ u)) ν φ

/-- The affine rescaling identity: precomposing the frequency datum with `A^{-1}` multiplies
the represented function by the unimodular phase `e(⟪·, γ(-t₀/ρ)⟫)` and precomposes it with
the transpose `affVec k ρ⁻¹ (-t₀/ρ)`. -/
lemma rescaleRep_eq (k : ℕ) (ρ t₀ : ℝ) {ι : Type} [MeasurableSpace ι]
    (Γ : ι → E k) (ν : Measure ι) (φ : ι → ℂ) :
    rescaleRep k ρ t₀ Γ ν φ
      = fun x => chat k x (gammaVec k (-t₀ / ρ)) *
          repFun k Γ ν φ (affVecLin k ρ⁻¹ (-t₀ / ρ) x) := by
  have h : (fun u => affMap k ρ⁻¹ (-t₀ / ρ) (Γ u))
      = fun u => gammaVec k (-t₀ / ρ) + affVecDualLin k ρ⁻¹ (-t₀ / ρ) (Γ u) := by
    funext u; rw [affMap_apply, affVecDualLin_apply]
  rw [rescaleRep, h]
  exact repFun_linear_rescale k Γ ν φ (affVecDualLin k ρ⁻¹ (-t₀ / ρ)) (affVecLin k ρ⁻¹ (-t₀ / ρ))
    (fun x y => inner_affVecLin k ρ⁻¹ (-t₀ / ρ) x y) (gammaVec k (-t₀ / ρ))

/-- **The class is closed under affine rescaling.**  If `f` is represented by the datum
`(Γ, ν, φ)` with values in `U`, then the rescaled function `rescaleRep k ρ t₀ Γ ν φ` is in the
class over the preimage `affMap k ρ t₀ ⁻¹' U`. -/
lemma isFourierRep_rescale (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) {ι : Type}
    [MeasurableSpace ι]
    {Γ : ι → E k} {ν : Measure ι} {φ : ι → ℂ} {U : Set (E k)}
    (hν : IsFiniteMeasure ν) (hφ : Integrable φ ν) (hmφ : Measurable φ) (hΓ : Measurable Γ)
    (hU : ∀ u, φ u ≠ 0 → Γ u ∈ U) :
    IsFourierRep k (affMap k ρ t₀ ⁻¹' U) (rescaleRep k ρ t₀ Γ ν φ) := by
  refine IsFourierRep.mk' (ι := ι) (Γ := fun u => affMap k ρ⁻¹ (-t₀ / ρ) (Γ u))
    (ν := ν) (φ := φ) hν hφ ?_ hmφ ?_ (fun x => rfl)
  · have h : (fun u => affMap k ρ⁻¹ (-t₀ / ρ) (Γ u))
        = fun u => gammaVec k (-t₀ / ρ) + affVecDualLin k ρ⁻¹ (-t₀ / ρ) (Γ u) := by
      funext u; rw [affMap_apply, affVecDualLin_apply]
    rw [h]
    exact measurable_const.add
      ((affVecDualLin k ρ⁻¹ (-t₀ / ρ)).continuous_of_finiteDimensional.measurable.comp hΓ)
  · intro u hu
    have h2 : ρ * (-t₀ / ρ) + t₀ = 0 := by field_simp; ring
    have h0 : gammaVec k (0 : ℝ) = 0 := by ext j; simp [gammaVec_apply]
    rw [Set.mem_preimage, affMap_affMap, mul_inv_cancel₀ hρ, h2, affMap_apply,
      affVecDual_one_zero, h0, zero_add]
    exact hU u hu

/-! ## 5. Restriction to the translates of a subspace -/

/-- **The restriction identity.**  If `Ψ : E l →ₗ[ℝ] E k` is an isometry onto a subspace `H`
with adjoint `M` (`∀ y ξ, ⟪Ψ y, ξ⟫ = ⟪y, M ξ⟫`), then the Fourier datum restricted to the
translate `H + z` represents the function `y ↦ f (Ψ y + z)`, with frequency datum
`M ∘ Γ` and density `e(⟪z, Γ·⟫) φ`. -/
lemma repFun_proj_eq (k l : ℕ) {ι : Type} [MeasurableSpace ι]
    (Γ : ι → E k) (ν : Measure ι) (φ : ι → ℂ) (z : E k)
    (Ψ : E l →ₗ[ℝ] E k) (M : E k →ₗ[ℝ] E l) (hΨM : ∀ y ξ, ⟪Ψ y, ξ⟫ = ⟪y, M ξ⟫) :
    repFun l (fun u => M (Γ u)) ν (fun u => chat k z (Γ u) * φ u)
      = fun y => repFun k Γ ν φ (Ψ y + z) := by
  funext y
  simp only [repFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change chat l y (M (Γ u)) * (chat k z (Γ u) * φ u) = chat k (Ψ y + z) (Γ u) * φ u
  have h1 : chat l y (M (Γ u)) = chat k (Ψ y) (Γ u) := by
    simp only [chat, hΨM]
  rw [h1, ← mul_assoc, ← chat_add_left]

/-- **The class is closed under restriction to the translates of a subspace.** -/
lemma isFourierRep_proj (k l : ℕ) {ι : Type} [MeasurableSpace ι]
    {Γ : ι → E k} {ν : Measure ι} {φ : ι → ℂ} {U : Set (E k)} (z : E k)
    (Ψ : E l →ₗ[ℝ] E k) (M : E k →ₗ[ℝ] E l) (_hΨM : ∀ y ξ, ⟪Ψ y, ξ⟫ = ⟪y, M ξ⟫)
    (hν : IsFiniteMeasure ν) (hφ : Integrable φ ν) (hmφ : Measurable φ) (hΓ : Measurable Γ)
    (hU : ∀ u, φ u ≠ 0 → Γ u ∈ U) :
    IsFourierRep l (M '' U)
      (repFun l (fun u => M (Γ u)) ν (fun u => chat k z (Γ u) * φ u)) := by
  have hM : Measurable M := M.continuous_of_finiteDimensional.measurable
  refine IsFourierRep.mk' (ι := ι) (Γ := fun u => M (Γ u)) (ν := ν)
    (φ := fun u => chat k z (Γ u) * φ u) hν ?_ (hM.comp hΓ) ?_ ?_ (fun y => rfl)
  · refine hφ.bdd_mul (((continuous_chat_left k z).measurable.comp hΓ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by rw [chat_norm])
  · exact ((continuous_chat_left k z).measurable.comp hΓ).mul hmφ
  · intro u hu
    exact ⟨Γ u, hU u (right_ne_zero_of_mul hu), rfl⟩

/-! ## 6. The uncertainty principle -/

/-- **The convolution kernel identity**: `∫ y, e(⟪x−y,ξ⟫) ψ y dy = e(⟪x,ξ⟫) ψ̂(ξ)`. -/
lemma integral_chat_sub_mul (k : ℕ) (x ξ : E k) (ψ : E k → ℂ) :
    (∫ y, chat k (x - y) ξ * ψ y) = chat k x ξ * ∫ y, ψ y * chat k (-y) ξ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change chat k (x - y) ξ * ψ y = chat k x ξ * (ψ y * chat k (-y) ξ)
  rw [sub_eq_add_neg, chat_add_left]
  ring

/-- Measurability of the convolution kernel composed with the frequency datum. -/
lemma measurable_chat_sub_fst (k : ℕ) {ι : Type} [MeasurableSpace ι] {Γ : ι → E k}
    (hΓ : Measurable Γ) (x : E k) :
    Measurable (fun p : E k × ι => chat k (x - p.1) (Γ p.2)) := by
  have h1 : Measurable (fun p : E k × ι => (x - p.1, Γ p.2)) :=
    (measurable_const.sub measurable_fst).prodMk (hΓ.comp measurable_snd)
  exact (continuous_chat_uncurry k).measurable.comp h1

/-- Product integrability of the convolution kernel. -/
lemma integrable_chat_sub_mul (k : ℕ) {ι : Type} [MeasurableSpace ι] {Γ : ι → E k}
    (hΓ : Measurable Γ) {ν : Measure ι} [SigmaFinite ν] {d : ι → ℂ} (hd : Integrable d ν)
    {ψ : E k → ℂ} (hψ : Integrable ψ) (x : E k) :
    Integrable (fun p : E k × ι => chat k (x - p.1) (Γ p.2) * d p.2 * ψ p.1)
      (volume.prod ν) := by
  have hb : Integrable (fun p : E k × ι => ‖ψ p.1‖ * ‖d p.2‖) (volume.prod ν) :=
    hψ.norm.mul_prod hd.norm
  refine hb.mono ?_ ?_
  · exact (((measurable_chat_sub_fst k hΓ x).aestronglyMeasurable.mul
      (hd.aestronglyMeasurable.comp_snd)).mul (hψ.aestronglyMeasurable.comp_fst))
  · filter_upwards with p
    rw [norm_mul, norm_mul, chat_norm, one_mul, Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm]

/-- **Fubini step towards the uncertainty principle.**  If `f` is the Fourier transform of a
finite measure with values in `U`, and `ψ̂ ≡ 1` on `U`, then `f = f * ψ`. -/
lemma repFun_conv_eq (k : ℕ) {ι : Type} [MeasurableSpace ι] {Γ : ι → E k} {ν : Measure ι}
    [SigmaFinite ν] {d : ι → ℂ} (hd : Integrable d ν)
    (hΓ : Measurable Γ) {U : Set (E k)} (hU : ∀ u, d u ≠ 0 → Γ u ∈ U)
    {ψ : E k → ℂ} (hψ : Integrable ψ)
    (hψhat : ∀ ξ ∈ U, (∫ y, ψ y * chat k (-y) ξ) = 1) :
    ∀ x, repFun k Γ ν d x = ∫ y, repFun k Γ ν d (x - y) * ψ y := by
  intro x
  have hFun : Integrable (Function.uncurry
      (fun y : E k => fun u : ι => chat k (x - y) (Γ u) * d u * ψ y)) (volume.prod ν) :=
    integrable_chat_sub_mul k hΓ hd hψ x
  have key : (∫ y, (∫ u, chat k (x - y) (Γ u) * d u ∂ν) * ψ y)
      = ∫ u, ∫ y, chat k (x - y) (Γ u) * d u * ψ y ∂volume ∂ν := by
    rw [show (fun y => (∫ u, chat k (x - y) (Γ u) * d u ∂ν) * ψ y)
        = fun y => ∫ u, chat k (x - y) (Γ u) * d u * ψ y ∂ν from by
      funext y; rw [integral_mul_const]]
    exact integral_integral_swap (μ := (volume : Measure (E k))) (ν := ν) hFun
  simp only [repFun]
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change chat k x (Γ u) * d u = ∫ y, chat k (x - y) (Γ u) * d u * ψ y
  have hinner : (∫ y, chat k (x - y) (Γ u) * d u * ψ y) = chat k x (Γ u) * d u := by
    rw [show (fun y => chat k (x - y) (Γ u) * d u * ψ y)
        = fun y => d u * (chat k (x - y) (Γ u) * ψ y) from by funext y; ring]
    rw [integral_const_mul, integral_chat_sub_mul]
    rcases eq_or_ne (d u) 0 with h0 | h0
    · rw [h0]; ring
    · rw [hψhat (Γ u) (hU u h0)]; ring
  rw [hinner]

/-- **Abstract uncertainty principle.**  Let `f` be in the class `𝒞(U)` and let `ψ` be an
`L¹` function with `ψ̂ ≡ 1` on `U` and `|ψ| ≤ φ` for a nonnegative `φ`.  Then for `p ≥ 1`

    `‖f x‖^p ≤ (∫ φ)^(p-1) · ∫ y, ‖f (x-y)‖^p φ y`.

This is the uncertainty principle of Guo–Li–Yung–Zorin-Kranich (Lemma 3.2). -/
lemma IsFourierRep.uncertainty {k : ℕ} {U : Set (E k)} {f : E k → ℂ}
    (hf : IsFourierRep k U f) {ψ : E k → ℂ} (hψ : Integrable ψ)
    (hψhat : ∀ ξ ∈ U, (∫ y, ψ y * chat k (-y) ξ) = 1)
    {φ : E k → ℝ} (hφnn : ∀ y, 0 ≤ φ y) (hψφ : ∀ y, ‖ψ y‖ ≤ φ y)
    {p : ℝ} (hp : 1 ≤ p) (x : E k) (hφ : Integrable φ volume)
    (hint1 : Integrable (fun y => ‖f (x - y)‖ * φ y) volume)
    (hint : Integrable (fun y => ‖f (x - y)‖ ^ p * φ y) volume) :
    ‖f x‖ ^ p ≤ (∫ y, φ y) ^ (p - 1) * ∫ y, ‖f (x - y)‖ ^ p * φ y := by
  classical
  obtain ⟨ι, m, Γ, ν, d, hν, hd, hΓ, hdm, hU, hfd⟩ := hf
  haveI := hν
  have hf_rep : f = repFun k Γ ν d := funext fun x => (hfd x).trans rfl
  have hconv := repFun_conv_eq k hd hΓ hU hψ hψhat
  -- Step 1: `‖f x‖ ≤ ∫ y, ‖f (x-y)‖ φ y`.
  have h1 : ‖f x‖ ≤ ∫ y, ‖f (x - y)‖ * φ y := by
    have ha : ‖f x‖ ≤ ∫ y, ‖f (x - y)‖ * ‖ψ y‖ := by
      rw [hf_rep, hconv x]
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [norm_mul]
    refine ha.trans ?_
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hint1 (Filter.Eventually.of_forall fun y => mul_le_mul_of_nonneg_left (hψφ y) (norm_nonneg _))
  -- Step 2: raise to the `p`-th power and apply weighted Hölder.
  have hpnn : 0 ≤ p := le_trans zero_le_one hp
  refine (Real.rpow_le_rpow (norm_nonneg _) h1 hpnn).trans ?_
  have hHolder := Commons.Measure.Integral.integral_mul_le_rpow_mul_integral_rpow
    (μ := (volume : Measure (E k))) (p := p) hp
    (a := fun y => ‖f (x - y)‖) (w := φ)
    (fun y => norm_nonneg _) hφnn hint hφ
  have hA0 : 0 ≤ ∫ y, ‖f (x - y)‖ ^ p * φ y :=
    integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p) (hφnn y)
  have hW0 : 0 ≤ ∫ y, φ y := integral_nonneg hφnn
  refine (Real.rpow_le_rpow (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (hφnn y))
    hHolder hpnn).trans (le_of_eq ?_)
  rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hW0 _),
    ← Real.rpow_mul hA0, ← Real.rpow_mul hW0]
  have hp0 : p ≠ 0 := by linarith
  have e1 : (1 / p) * p = 1 := by rw [one_div, inv_mul_cancel₀ hp0]
  have e2 : (1 - 1 / p) * p = p - 1 := by rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ hp0]
  rw [e1, e2, Real.rpow_one]
  ring

end Submission.Vinogradov

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxRealise_regular
import Submission.Work.BoseDict.boxRealise_annOf_annOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.BombPairAux` — the vocabulary of the pair row `bomb_pair_eq_cS2C`

The target `Work.BoseBoxFock.bomb_pair_eq_cS2C` is the row

    `bomb m Ψ ((cre m 0)² (ann m 0)² Ψ) = cS2C ℓ (boxRealise e d Ψ)`

of the box ↔ model dictionary (`BF3b`).  `Work.BoseDict.bomb_pair_row` reduces the model
side to the pairing of two *double box annihilations* `boxAnnOf e (evec 0)`, and the two
halves of the remaining box-side computation are

* `boxAnnOf_pairInt` — the norm of the double annihilation is `(n+1)(n+2)‖c‖⁴` times the
  square integral of the peeled double integral `pairInt ℓ Θ`;
* `cS2C_eq_pairInt` — the pair-condensate count `cS2C ℓ Θ` is `(n+1)(n+2)(ℓ⁶)⁻¹` times the
  same integral (one peeled pair-slot term for each of the `(n+1)(n+2)` ordered pairs).

This module fixes the vocabulary they share (the vector `evec0`, the indicator `thetaA` of
the centred cube, the peeled integral `pairInt`) and proves the elementary facts about the
concatenation with the model operators.

Everything here is `sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The condensate coordinate vector -/

/-- The model's condensate coordinate vector `e_0`, i.e. the coordinate vector of
`Work.BoseB4.cre m 0 = Work.BoseB4.creOf m (evec0 m)`. -/
noncomputable def evec0 (m : ℕ) [NeZero m] : Fin m → ℝ := Work.BoseB4.evec m 0

lemma evec0_apply_zero (m : ℕ) [NeZero m] : evec0 m 0 = 1 := by
  change (Pi.single (0 : Fin m) (1 : ℝ) : Fin m → ℝ) 0 = 1
  simp

lemma evec0_apply_ne {m : ℕ} [NeZero m] {l : Fin m} (hl : l ≠ 0) : evec0 m l = 0 := by
  change (Pi.single (0 : Fin m) (1 : ℝ) : Fin m → ℝ) l = 0
  simp [hl]

/-- The physical one-particle function of the coordinate vector `evec0 m` is `e 0`. -/
lemma etaOf_evec0 {m : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ) :
    Work.BoseDict.etaOf e (evec0 m) = e 0 := by
  funext z
  rw [Work.BoseDict.etaOf, Finset.sum_eq_single (0 : Fin m)]
  · simp [evec0_apply_zero]
  · intro l _ hl
    simp [evec0_apply_ne hl]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- `cre m 0` is the creation of the superposition with coordinate vector `evec0 m`. -/
lemma cre_eq_creOf_evec0 {m : ℕ} [NeZero m] :
    Work.BoseB4.cre m 0 = Work.BoseB4.creOf m (evec0 m) := by
  rw [Work.BoseB4.creOf, Finset.sum_eq_single (0 : Fin m)]
  · rw [evec0_apply_zero, one_smul]
  · intro l _ hl
    rw [evec0_apply_ne hl, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- `ann m 0` is the annihilation of the superposition with coordinate vector `evec0 m`. -/
lemma ann_eq_annOf_evec0 {m : ℕ} [NeZero m] :
    Work.BoseB4.ann m 0 = Work.BoseB4.annOf m (evec0 m) := by
  rw [Work.BoseB4.annOf, Finset.sum_eq_single (0 : Fin m)]
  · rw [evec0_apply_zero, one_smul]
  · intro l _ hl
    rw [evec0_apply_ne hl, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-! ## 2. The peeled double box integral -/

/-- The indicator of the centred cube, as a `ℂ`-valued function.  (For `0 < ℓ` this is
`Work.BoseK15.corpusBox.thetaFun ℓ`, see `Work.BoseBoxFock.qCoeff_eq_ft`.) -/
noncomputable def thetaA (ℓ : ℝ) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℂ))

/-- The **peeled double box integral**: the `(n+2)`-particle function `Θ` integrated over two
centred cubes, the first integration variable in the slot `0` and the second in the slot `1`,
with the remaining coordinates `y`. -/
noncomputable def pairInt {n : ℕ} (ℓ : ℝ) (Θ : Work.BoseDict.Xn (n + 2) → ℂ) :
    Work.BoseDict.Xn n → ℂ :=
  fun y => ∫ u in Submission.BoseGases.acube ℓ, ∫ v in Submission.BoseGases.acube ℓ,
    Θ (Fin.cons u (Fin.cons v y))

/-! ## 3. Elementary pairing facts -/

/-- `cIPn` of a function with itself is the `L²`-norm squared (the imaginary part of the
pairing `conj z * z` vanishes identically, so no integrability is needed: both sides are
`0` for a non-integrable function). -/
lemma cIPn_self_re {n : ℕ} (X : Work.BoseDict.Xn n → ℂ) :
    (Work.BoseDict.cIPn n X X).re = ∫ y : Work.BoseDict.Xn n, ‖X y‖ ^ 2 := by
  rw [Work.BoseDict.cIPn]
  have hpt : ∀ y : Work.BoseDict.Xn n,
      (starRingEnd ℂ) (X y) * X y = ((‖X y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [Complex.conj_mul', ← Complex.ofReal_pow]
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- The fourth power of the modulus of the model's condensate coefficient: if `conj c * c`
is `(ℓ³)⁻¹` then `‖c‖⁴ = ((ℓ³)⁻¹)²`. -/
lemma norm_c_pow_four {ℓ : ℝ} {c : ℂ} (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹) :
    ‖c‖ ^ 4 = ((ℓ ^ 3)⁻¹) ^ 2 := by
  have h1 : ‖c‖ ^ 2 = (ℓ ^ 3)⁻¹ := by
    have h := congrArg Complex.re hcc
    rw [Complex.conj_mul'] at h
    rw [← Complex.ofReal_pow] at h
    simp only [Complex.ofReal_re] at h
    exact h
  rw [← h1]
  ring

/-- The support of a realised model vector: if every mode function `e l` vanishes off the
centred cube, then `boxRealise e d Ψ` vanishes off the `d`-particle box. -/
lemma boxRealise_support {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Submission.BoseGases.acube ℓ)
    (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    Function.support (Work.BoseDict.boxRealise e d Ψ) ⊆ Submission.BoseGases.abox d ℓ := by
  classical
  intro x hx
  rw [Function.mem_support] at hx
  rw [Submission.BoseGases.mem_abox_iff]
  by_contra hcon
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hcon
  have hone : ∀ l : Fin m, e l (x i₀) = 0 := fun l => by
    by_contra hne
    exact hi₀ (hsupp l (Function.mem_support.mpr hne))
  have hzero : ∀ α : Fin m →₀ ℕ, Work.BoseDict.modeProd e d α x = 0 := by
    intro α
    rw [Work.BoseDict.modeProd]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀) (hone (σ i₀)), mul_zero]
  have hz : (Work.BoseDict.boxRealise e d Ψ) x = 0 := by
    rw [Work.BoseDict.boxRealise_eq_sum Ψ hΨ]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [hzero α, mul_zero]
  exact hx hz

/-- **The realised model vector is essentially bounded** (it is a finite sum of products of
the `L^∞` mode functions `e l`): `MemLp` with respect to the volume restricted to the box.
Only the measure-theoretic part of `Work.BoseBoxFock.boxRealise_regular` is used. -/
lemma boxRealise_memLp_top {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : Work.BoseB4.RealFock m) :
    MeasureTheory.MemLp (Work.BoseDict.boxRealise e d Ψ) ⊤
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).restrict
        (Submission.BoseGases.abox d ℓ)) := by
  haveI : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).restrict
        (Submission.BoseGases.abox d ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top d ℓ hℓ.le⟩
  obtain ⟨-, haesm, C, hC⟩ := Work.BoseBoxFock.boxRealise_regular hℓ hbdd hsupp Ψ
  refine MeasureTheory.MemLp.of_bound (haesm.mono_measure Measure.restrict_le_self) C ?_
  exact ae_restrict_of_ae hC

/-! ## 4. The explicit formula for the condensate annihilation -/

/-- `pairSet d` is empty for `d < 2` (there is no pair of distinct elements of `Fin d`). -/
lemma pairSet_eq_empty_of_lt_two {d : ℕ} (hd : d < 2) :
    Submission.BoseGases.pairSet d = ∅ := by
  rw [Submission.BoseGases.pairSet, Finset.filter_eq_empty_iff]
  rintro ⟨i, j⟩ - hij
  exact hij (Fin.ext (by have h1 := i.isLt; have h2 := j.isLt; omega))

/-- The explicit coefficient of `annOf m (evec0 m)`: only the mode `0` survives, and the
occupation of the source multi-index is raised by one. -/
lemma annOf_evec0_apply {m : ℕ} [NeZero m] (Ψ : Work.BoseB4.RealFock m) (β : Fin m →₀ ℕ) :
    (Work.BoseB4.annOf m (evec0 m) Ψ) β
      = ((β 0 : ℝ) + 1) * Ψ (β + Work.BoseB4.e m 0) := by
  rw [Work.BoseDict.annOf_apply', Finset.sum_eq_single (0 : Fin m)]
  · rw [evec0_apply_zero]; ring
  · intro l _ hl
    rw [evec0_apply_ne hl]; ring
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

/-- `annOf m (evec0 m)` lowers the total degree by one, in the *additive* form: a monomial
of the image at `β` differs from a monomial of `Ψ` at `β + e_0`. -/
lemma ann_evec0_support_degree {m n : ℕ} [NeZero m] {Ψ : Work.BoseB4.RealFock m}
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = n) :
    ∀ β ∈ (Work.BoseB4.annOf m (evec0 m) Ψ).support, β.sum (fun _ k => k) + 1 = n := by
  intro β hβ
  rw [Finsupp.mem_support_iff, annOf_evec0_apply] at hβ
  have hne : Ψ (β + Work.BoseB4.e m 0) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hβ
    exact hβ rfl
  have hd := hΨ _ (Finsupp.mem_support_iff.mpr hne)
  have hdeg : (β + Work.BoseB4.e m 0).sum (fun _ k => k)
      = β.sum (fun _ k => k) + 1 := by
    rw [show (β + Work.BoseB4.e m 0).sum (fun _ k => k)
          = (β + Work.BoseB4.e m 0).degree from rfl,
      show β.sum (fun _ k => k) = β.degree from rfl,
      map_add, show (Work.BoseB4.e m 0).degree = 1 from by
        rw [Work.BoseB4.e, Finsupp.degree_single]]
  omega

/-- **In degree `< 2` the double condensate annihilation vanishes.** -/
lemma ann0_ann0_eq_zero {m d : ℕ} [NeZero m] {Ψ : Work.BoseB4.RealFock m}
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) (hd : d < 2) :
    Work.BoseB4.ann m 0 (Work.BoseB4.ann m 0 Ψ) = 0 := by
  rw [ann_eq_annOf_evec0]
  set Ψ₁ : Work.BoseB4.RealFock m := Work.BoseB4.annOf m (evec0 m) Ψ with hΨ₁
  have h1 : ∀ β ∈ Ψ₁.support, β.sum (fun _ k => k) + 1 = d :=
    ann_evec0_support_degree hΨ
  have hsupp1 : ∀ β ∈ Ψ₁.support, β.sum (fun _ k => k) = d - 1 := by
    intro β hβ
    have := h1 β hβ
    omega
  have h2 : ∀ γ ∈ (Work.BoseB4.annOf m (evec0 m) Ψ₁).support,
      γ.sum (fun _ k => k) + 1 = d - 1 :=
    ann_evec0_support_degree hsupp1
  refine Finsupp.ext fun γ => ?_
  by_contra hne
  have hγ : γ ∈ (Work.BoseB4.annOf m (evec0 m) Ψ₁).support :=
    Finsupp.mem_support_iff.mpr hne
  have h3 := h2 γ hγ
  omega

end Work.BoseBoxFock

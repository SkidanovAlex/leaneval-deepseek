import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.blockTwo3_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.blockTwo3_bound` — the fibre `L²` bound of block II.3

The general form of the target `Work.BoseBoxFock.blockTwo3_fibre_L2`: for `i ≠ j` in `Fin n`,
`Θ ∈ L²((Fin n → 𝔼))` and `A, B ∈ L²(𝔼)`,

    ∫_{w₀} ∫_{w₁} ‖∫_{x'} ∫_y ∫_u (star Θ(ins w x')) (star A y) (star B u) Θ(ins (y,u) x')‖²
      ≤ ‖A‖²_{L²} ‖B‖²_{L²} ‖Θ‖⁴_{L²} ,

where `ins w x' = splitEquiv hij (x', w)` is the insertion of the free coordinates.

Proof.  For fixed `w = (w₀,w₁)` Cauchy–Schwarz on `Ω = Fib × (𝔼 × 𝔼)` gives

    ‖I(w)‖² ≤ (∫_Ω ‖fidH w‖²)(∫_Ω ‖fidG‖²) ,

and the two factors are computed exactly by Fubini:
`∫_Ω ‖fidG‖² = ‖Θ‖²` (the measure-preserving insertion `splitEquiv`) and
`∫_Ω ‖fidH w‖² = ‖A‖² ‖B‖² · D(w)` with `D(w) = ∫_{x'} ‖Θ (ins w x')‖²`.  Integrating over `w`
and using the fibre identity `∫_w D(w) = ‖Θ‖²` (again the measure-preserving insertion) gives the
claim.
-/

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory

namespace Work.BoseBoxFock

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-- The measure of the outer pair of variables. -/
abbrev volW : Measure (𝔼 × 𝔼) := (volume : Measure 𝔼).prod volume

/-- The measure of the fibre `Fib n i j`. -/
abbrev volF (n : ℕ) (i j : Fin n) : Measure (Fib n i j) := volume

/-- The measure of the Cauchy–Schwarz space `Fib n i j × (𝔼 × 𝔼)`. -/
abbrev volΩ (n : ℕ) (i j : Fin n) : Measure (Fib n i j × (𝔼 × 𝔼)) :=
  (volF n i j).prod volW

/-- The measure of the outer product space `(𝔼 × 𝔼) × Fib n i j`. -/
abbrev volP (n : ℕ) (i j : Fin n) : Measure ((𝔼 × 𝔼) × Fib n i j) :=
  volW.prod (volF n i j)

/-- The measure of the full space `(𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼))`. -/
abbrev volA (n : ℕ) (i j : Fin n) : Measure ((𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼))) :=
  volW.prod (volΩ n i j)

instance instSFiniteVolF (n : ℕ) (i j : Fin n) : SFinite (volF n i j) :=
  inferInstanceAs (SFinite (volume : Measure (Fib n i j)))

instance instSFiniteVolW : SFinite volW :=
  inferInstanceAs (SFinite (volume : Measure (𝔼 × 𝔼)))

instance instSFiniteVolΩ (n : ℕ) (i j : Fin n) : SFinite (volΩ n i j) :=
  inferInstanceAs (SFinite ((volF n i j).prod volW))

instance instSFiniteVolP (n : ℕ) (i j : Fin n) : SFinite (volP n i j) :=
  inferInstanceAs (SFinite (volW.prod (volF n i j)))

instance instSFiniteVolA (n : ℕ) (i j : Fin n) : SFinite (volA n i j) :=
  inferInstanceAs (SFinite (volW.prod (volΩ n i j)))

/-! ## The two factors of the Cauchy–Schwarz step -/

theorem outIns_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (z : (𝔼 × 𝔼) × Fib n i j) :
    outIns hij z = splitEquiv hij (z.2, z.1) := rfl

/-- The state factor `q ↦ Θ (splitEquiv hij q)` of the Cauchy–Schwarz pair. -/
abbrev fidG {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) :
    Fib n i j × (𝔼 × 𝔼) → ℂ := fun q => Θ (splitEquiv hij q)

/-- The `(w, A, B)` factor of the Cauchy–Schwarz pair. -/
abbrev fidH {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) (A B : 𝔼 → ℂ)
    (w : 𝔼 × 𝔼) : Fib n i j × (𝔼 × 𝔼) → ℂ :=
  fun q => ((starRingEnd ℂ) (Θ (splitEquiv hij (q.1, w))) * (starRingEnd ℂ) (A q.2.1))
    * (starRingEnd ℂ) (B q.2.2)

/-- The majorant `D(w) = ∫_{x'} ‖Θ (ins w x')‖²`. -/
abbrev outD {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) (w : 𝔼 × 𝔼) : ℝ :=
  ∫ x' : Fib n i j, ‖Θ (splitEquiv hij (x', w))‖ ^ 2

/-- The transported nonnegative function `z ↦ ‖Θ (ins z.2 z.1)‖²` on `(𝔼×𝔼) × Fib`. -/
abbrev outT {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) :
    (𝔼 × 𝔼) × Fib n i j → ℝ := fun z => ‖Θ (outIns hij z)‖ ^ 2

/-- The product-space form of the inner functional. -/
abbrev fidI {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) (A B : 𝔼 → ℂ)
    (w : 𝔼 × 𝔼) : ℂ := ∫ q : Fib n i j × (𝔼 × 𝔼), fidH hij Θ A B w q * fidG hij Θ q

/-- The iterated form of the inner functional (as in the statement). -/
abbrev trExpr {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) (A B : 𝔼 → ℂ)
    (w₀ w₁ : 𝔼) : ℂ :=
  ∫ x' : Fib n i j, ∫ y : 𝔼, ∫ u : 𝔼,
    ((starRingEnd ℂ) (Θ (splitEquiv hij (x', (w₀, w₁)))) * (starRingEnd ℂ) (A y))
      * (starRingEnd ℂ) (B u) * Θ (splitEquiv hij (x', (y, u)))

/-! ## The state factor -/

theorem fidG_aesm {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) :
    AEStronglyMeasurable (fidG hij Θ) (volΩ n i j) :=
  hΘm.comp_measurePreserving (measurePreserving_splitEquiv hij)

theorem fidG_integrable_sq {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    Integrable (fun q => ‖fidG hij Θ q‖ ^ 2) (volΩ n i j) :=
  ((measurePreserving_splitEquiv hij).integrable_comp (hΘm.norm.pow 2)).mpr hΘL

theorem fidG_memLp {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    MemLp (fidG hij Θ) 2 (volΩ n i j) :=
  (memLp_two_iff_integrable_sq_norm (fidG_aesm hij hΘm)).mpr
    (fidG_integrable_sq hij hΘm hΘL)

theorem fidG_integral {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    ∫ q, ‖fidG hij Θ q‖ ^ 2 ∂(volΩ n i j) = ∫ x, ‖Θ x‖ ^ 2 := by
  have h := (measurePreserving_splitEquiv hij).integral_comp' (fun x : Fin n → 𝔼 => ‖Θ x‖ ^ 2)
  simpa only [fidG, Function.comp_def] using h

/-! ## The `(w, A, B)` factor -/

theorem fidH_norm_sq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) (A B : 𝔼 → ℂ)
    (w : 𝔼 × 𝔼) (q : Fib n i j × (𝔼 × 𝔼)) :
    ‖fidH hij Θ A B w q‖ ^ 2
      = ‖Θ (splitEquiv hij (q.1, w))‖ ^ 2 * (‖A q.2.1‖ ^ 2 * ‖B q.2.2‖ ^ 2) := by
  change ‖((starRingEnd ℂ) (Θ (splitEquiv hij (q.1, w))) * (starRingEnd ℂ) (A q.2.1))
      * (starRingEnd ℂ) (B q.2.2)‖ ^ 2 = _
  rw [norm_mul, norm_mul, starRingEnd_apply, starRingEnd_apply, starRingEnd_apply, norm_star,
    norm_star, norm_star]
  ring

theorem fidH_aesm {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ} {A B : 𝔼 → ℂ}
    (hAm : AEStronglyMeasurable A) (hBm : AEStronglyMeasurable B) (w : 𝔼 × 𝔼)
    (hw : AEStronglyMeasurable (fun x' : Fib n i j => Θ (splitEquiv hij (x', w)))
      (volF n i j)) :
    AEStronglyMeasurable (fidH hij Θ A B w) (volΩ n i j) :=
  ((hw.comp_fst).star.mul ((hAm.comp_fst).comp_snd).star).mul ((hBm.comp_snd).comp_snd).star

theorem fidH_integrable_sq {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    {A B : 𝔼 → ℂ} (hAL : Integrable (fun x => ‖A x‖ ^ 2))
    (hBL : Integrable (fun x => ‖B x‖ ^ 2)) (w : 𝔼 × 𝔼)
    (hw : Integrable (fun x' : Fib n i j => ‖Θ (splitEquiv hij (x', w))‖ ^ 2) (volF n i j)) :
    Integrable (fun q => ‖fidH hij Θ A B w q‖ ^ 2) (volΩ n i j) := by
  have h1 : Integrable (fun z : 𝔼 × 𝔼 => ‖A z.1‖ ^ 2 * ‖B z.2‖ ^ 2) volW :=
    hAL.mul_prod hBL
  have h2 : Integrable (fun q : Fib n i j × (𝔼 × 𝔼) =>
      ‖Θ (splitEquiv hij (q.1, w))‖ ^ 2 * (‖A q.2.1‖ ^ 2 * ‖B q.2.2‖ ^ 2)) (volΩ n i j) :=
    hw.mul_prod h1
  exact h2.congr (Filter.Eventually.of_forall fun q => (fidH_norm_sq hij Θ A B w q).symm)

theorem fidH_integral {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ} {A B : 𝔼 → ℂ}
    (hAL : Integrable (fun x => ‖A x‖ ^ 2)) (hBL : Integrable (fun x => ‖B x‖ ^ 2))
    (w : 𝔼 × 𝔼) (hw : Integrable (fun x' : Fib n i j => ‖Θ (splitEquiv hij (x', w))‖ ^ 2)
      (volF n i j)) :
    ∫ q, ‖fidH hij Θ A B w q‖ ^ 2 ∂(volΩ n i j)
      = ((∫ y, ‖A y‖ ^ 2) * (∫ u, ‖B u‖ ^ 2)) * outD hij Θ w := by
  have h1 : Integrable (fun z : 𝔼 × 𝔼 => ‖A z.1‖ ^ 2 * ‖B z.2‖ ^ 2) volW :=
    hAL.mul_prod hBL
  have h2 : Integrable (fun q : Fib n i j × (𝔼 × 𝔼) =>
      ‖Θ (splitEquiv hij (q.1, w))‖ ^ 2 * (‖A q.2.1‖ ^ 2 * ‖B q.2.2‖ ^ 2)) (volΩ n i j) :=
    hw.mul_prod h1
  rw [show (∫ q, ‖fidH hij Θ A B w q‖ ^ 2 ∂(volΩ n i j))
      = ∫ q, ‖Θ (splitEquiv hij (q.1, w))‖ ^ 2 * (‖A q.2.1‖ ^ 2 * ‖B q.2.2‖ ^ 2)
          ∂(volΩ n i j) from
    integral_congr_ae (Filter.Eventually.of_forall fun q => fidH_norm_sq hij Θ A B w q)]
  rw [MeasureTheory.integral_prod _ h2]
  have hz : ∀ x' : Fib n i j,
      (∫ z : 𝔼 × 𝔼, ‖Θ (splitEquiv hij (x', w))‖ ^ 2 * (‖A z.1‖ ^ 2 * ‖B z.2‖ ^ 2) ∂volW)
        = ‖Θ (splitEquiv hij (x', w))‖ ^ 2 * ((∫ y, ‖A y‖ ^ 2) * (∫ u, ‖B u‖ ^ 2)) := by
    intro x'
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_prod_mul (fun y : 𝔼 => ‖A y‖ ^ 2) (fun u : 𝔼 => ‖B u‖ ^ 2)
  simp only [hz]
  rw [MeasureTheory.integral_mul_const, outD]
  ring

/-! ## The outer variable: integrability and the fibre identity -/

theorem outT_integrable {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    Integrable (outT hij Θ) (volP n i j) :=
  ((measurePreserving_outIns hij).integrable_comp (hΘm.norm.pow 2)).mpr hΘL

theorem outD_integrable {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    Integrable (outD hij Θ) volW := by
  exact (outT_integrable hij hΘm hΘL).integral_prod_left

theorem outD_ae {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    ∀ᵐ w ∂volW,
      Integrable (fun x' : Fib n i j => ‖Θ (splitEquiv hij (x', w))‖ ^ 2) (volF n i j) := by
  exact (outT_integrable hij hΘm hΘL).prod_right_ae

theorem outD_aesm_slice {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) :
    ∀ᵐ w ∂volW,
      AEStronglyMeasurable (fun x' : Fib n i j => Θ (splitEquiv hij (x', w))) (volF n i j) := by
  have h := (hΘm.comp_measurePreserving (measurePreserving_outIns hij)).prodMk_left
  simpa only [outIns_apply, Function.comp_def] using h

theorem outD_integral {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2)) :
    ∫ w, outD hij Θ w ∂volW = ∫ x, ‖Θ x‖ ^ 2 := by
  have hval := (measurePreserving_outIns hij).integral_comp'
    (fun x : Fin n → 𝔼 => ‖Θ x‖ ^ 2)
  have hprod := MeasureTheory.integral_prod (outT hij Θ) (outT_integrable hij hΘm hΘL)
  rw [show (∫ w, outD hij Θ w ∂volW)
      = ∫ w, ∫ x', outT hij Θ (w, x') ∂(volF n i j) ∂volW from rfl]
  rw [← hprod]
  simpa only [outT, outIns_apply, Function.comp_def] using hval

/-! ## Identification of the iterated and product forms -/

theorem fidH_mul_fidG {n : ℕ} {i j : Fin n} (hij : i ≠ j) (Θ : (Fin n → 𝔼) → ℂ) (A B : 𝔼 → ℂ)
    (w₀ w₁ y u : 𝔼) (x' : Fib n i j) :
    fidH hij Θ A B (w₀, w₁) (x', (y, u)) * fidG hij Θ (x', (y, u))
      = ((starRingEnd ℂ) (Θ (splitEquiv hij (x', (w₀, w₁)))) * (starRingEnd ℂ) (A y))
        * (starRingEnd ℂ) (B u) * Θ (splitEquiv hij (x', (y, u))) := rfl

theorem trExpr_eq_fidI {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ} {A B : 𝔼 → ℂ}
    (w₀ w₁ : 𝔼)
    (hF : Integrable (fun q : Fib n i j × (𝔼 × 𝔼) =>
      fidH hij Θ A B (w₀, w₁) q * fidG hij Θ q) (volΩ n i j)) :
    trExpr hij Θ A B w₀ w₁ = fidI hij Θ A B (w₀, w₁) := by
  rw [fidI]
  have hae : ∀ᵐ x' ∂(volF n i j),
      (∫ y : 𝔼, ∫ u : 𝔼, fidH hij Θ A B (w₀, w₁) (x', (y, u)) * fidG hij Θ (x', (y, u)))
        = ∫ z : 𝔼 × 𝔼, fidH hij Θ A B (w₀, w₁) (x', z) * fidG hij Θ (x', z) ∂volW := by
    filter_upwards [hF.prod_right_ae] with x' hx'
    exact (MeasureTheory.integral_prod _ hx').symm
  rw [trExpr]
  refine (integral_congr_ae hae).trans ?_
  exact (MeasureTheory.integral_prod _ hF).symm

/-! ## The main bound -/

theorem fidI_aesm {n : ℕ} {i j : Fin n} (hij : i ≠ j) {Θ : (Fin n → 𝔼) → ℂ} {A B : 𝔼 → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hAm : AEStronglyMeasurable A) (hBm : AEStronglyMeasurable B) :
    AEStronglyMeasurable (fun w : 𝔼 × 𝔼 => ‖fidI hij Θ A B w‖ ^ 2) volW := by
  have hout : AEStronglyMeasurable (fun z : (𝔼 × 𝔼) × Fib n i j => Θ (outIns hij z))
      (volP n i j) := by
    simpa only [Function.comp_def] using
      hΘm.comp_measurePreserving (measurePreserving_outIns hij)
  have hσ : Measure.QuasiMeasurePreserving
      (fun p : (𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼)) => (p.1, p.2.1)) (volA n i j) (volP n i j) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id volW)
      (MeasureTheory.QuasiMeasurePreserving.fst
        (Measure.QuasiMeasurePreserving.id (volΩ n i j)))
  have h1 : AEStronglyMeasurable
      (fun p : (𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼)) => Θ (splitEquiv hij (p.2.1, p.1)))
      (volA n i j) := by
    simpa only [Function.comp_def, outIns_apply] using hout.comp_quasiMeasurePreserving hσ
  have h2 : AEStronglyMeasurable
      (fun p : (𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼)) => A p.2.2.1) (volA n i j) :=
    ((hAm.comp_fst).comp_snd).comp_snd
  have h3 : AEStronglyMeasurable
      (fun p : (𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼)) => B p.2.2.2) (volA n i j) :=
    ((hBm.comp_snd).comp_snd).comp_snd
  have h4 : AEStronglyMeasurable
      (fun p : (𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼)) => Θ (splitEquiv hij p.2)) (volA n i j) :=
    (fidG_aesm hij hΘm).comp_snd
  have hF : AEStronglyMeasurable
      (fun p : (𝔼 × 𝔼) × (Fib n i j × (𝔼 × 𝔼)) =>
        fidH hij Θ A B p.1 p.2 * fidG hij Θ p.2) (volA n i j) :=
    (((h1.star.mul h2.star).mul h3.star).mul h4)
  have h5 : AEStronglyMeasurable
      (fun w : 𝔼 × 𝔼 => ∫ q, fidH hij Θ A B w q * fidG hij Θ q ∂(volΩ n i j)) volW :=
    hF.integral_prod_right'
  exact h5.norm.pow 2

theorem fibre_L2_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Θ : (Fin n → 𝔼) → ℂ} {A B : 𝔼 → ℂ}
    (hΘm : AEStronglyMeasurable Θ) (hΘL : Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : AEStronglyMeasurable A) (hAL : Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : AEStronglyMeasurable B) (hBL : Integrable (fun x => ‖B x‖ ^ 2)) :
    ∫ w₀ : 𝔼, ∫ w₁ : 𝔼, ‖trExpr hij Θ A B w₀ w₁‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  classical
  -- the a.e. bound
  have hae : ∀ᵐ w ∂volW,
      ‖fidI hij Θ A B w‖ ^ 2
        ≤ ((∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2)) * outD hij Θ w := by
    filter_upwards [outD_ae hij hΘm hΘL, outD_aesm_slice hij hΘm] with w hwint hwaesm
    have hHmem : MemLp (fidH hij Θ A B w) 2 (volΩ n i j) :=
      (memLp_two_iff_integrable_sq_norm (fidH_aesm hij hAm hBm w hwaesm)).mpr
        (fidH_integrable_sq hij hAL hBL w hwint)
    have hcs := norm_integral_mul_le_sq hHmem (fidG_memLp hij hΘm hΘL)
    have hfac := fidH_integral hij hAL hBL w hwint
    have hGint := fidG_integral hij hΘm hΘL
    calc ‖fidI hij Θ A B w‖ ^ 2
        = ‖∫ q, fidH hij Θ A B w q * fidG hij Θ q ∂(volΩ n i j)‖ ^ 2 := rfl
      _ ≤ (∫ q, ‖fidH hij Θ A B w q‖ ^ 2 ∂(volΩ n i j))
            * (∫ q, ‖fidG hij Θ q‖ ^ 2 ∂(volΩ n i j)) := hcs
      _ = (((∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2)) * outD hij Θ w) * (∫ x, ‖Θ x‖ ^ 2) := by
          rw [hfac, hGint]
      _ = ((∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2)) * outD hij Θ w := by
          ring_nf
  -- integrability of the majorant, of `‖fidI‖²` and of `‖trExpr‖²`
  have hmaj : Integrable (fun w : 𝔼 × 𝔼 =>
      ((∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2)) * outD hij Θ w) volW :=
    (outD_integrable hij hΘm hΘL).const_mul _
  have hI_int : Integrable (fun w : 𝔼 × 𝔼 => ‖fidI hij Θ A B w‖ ^ 2) volW := by
    refine Integrable.mono' hmaj (fidI_aesm hij hΘm hAm hBm) ?_
    filter_upwards [hae] with w hw
    rw [Real.norm_of_nonneg (by positivity)]
    exact hw
  have htr_eq : (fun w : 𝔼 × 𝔼 => ‖trExpr hij Θ A B w.1 w.2‖ ^ 2)
      =ᵐ[volW] (fun w : 𝔼 × 𝔼 => ‖fidI hij Θ A B w‖ ^ 2) := by
    filter_upwards [outD_ae hij hΘm hΘL, outD_aesm_slice hij hΘm] with w hwint hwaesm
    have hHmem : MemLp (fidH hij Θ A B (w.1, w.2)) 2 (volΩ n i j) :=
      (memLp_two_iff_integrable_sq_norm (fidH_aesm hij hAm hBm (w.1, w.2) hwaesm)).mpr
        (fidH_integrable_sq hij hAL hBL (w.1, w.2) hwint)
    have hF : Integrable (fun q : Fib n i j × (𝔼 × 𝔼) =>
        fidH hij Θ A B (w.1, w.2) q * fidG hij Θ q) (volΩ n i j) :=
      hHmem.integrable_mul (fidG_memLp hij hΘm hΘL)
    rw [trExpr_eq_fidI hij w.1 w.2 hF]
  have htr_int : Integrable (fun w : 𝔼 × 𝔼 => ‖trExpr hij Θ A B w.1 w.2‖ ^ 2) volW :=
    hI_int.congr htr_eq.symm
  rw [← MeasureTheory.integral_prod (fun w : 𝔼 × 𝔼 => ‖trExpr hij Θ A B w.1 w.2‖ ^ 2) htr_int]
  rw [integral_congr_ae htr_eq]
  refine (integral_mono_ae hI_int hmaj hae).trans ?_
  have hlast : (∫ w, (((∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2))
      * outD hij Θ w) ∂volW)
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
    rw [MeasureTheory.integral_const_mul, outD_integral hij hΘm hΘL]
    exact le_of_eq (by ring)
  exact hlast

end Work.BoseBoxFock

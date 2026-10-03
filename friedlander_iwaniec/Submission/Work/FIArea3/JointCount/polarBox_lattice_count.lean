/-
# `Work.FIArea3.JointCount.polarBox_lattice_count` — lattice points of a coset in the polar box

For Gaussian integers `z₀, g₁, g₂` with `|det (g₁, g₂)| = c ≥ 1`, the number of Gaussian
integers `z` in the polar box (5.14) with `z - z₀ ∈ ℤ g₁ + ℤ g₂` is at most
`π (5θ√N + √|g₁|² + √|g₂|²)² / c`.

The lattice `Λ = ℤ g₁ + ℤ g₂` has covolume `c`.  The polar box is contained in the disc of
radius `5θ√N` about the mid-angle point of the sector (`FIArea4.dist_polarBox_le`).  Fix the
half-open fundamental domain `F = {a u + b v : a, b ∈ [-1/2, 1/2)}` of `Λ` (a parallelogram of
area `c`, contained in the disc of radius `(|u| + |v|)/2`).  The translates of `F` by distinct
lattice points are disjoint, each of volume `c`, and those indexed by the lattice points of the
box are contained in `D + F ⊆ D(p, 5θ√N + (|u|+|v|)/2)`, a disc of volume `π(5θ√N + (|u|+|v|)/2)²`.
Comparison of volumes gives the claim.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le

namespace Work.FIArea3.JointCount

open MeasureTheory Finset
open scoped ENNReal
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. The `ℝ`-linear map `(a + bi) ↦ a u + b v` -/

/-- The `ℝ`-linear map `z ↦ z.re • u + z.im • v`. -/
def Llc (u v : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := z.re • u + z.im • v
  map_add' z w := by simp only [Complex.add_re, Complex.add_im, add_smul]; abel
  map_smul' r z := by simp only [Complex.smul_re, Complex.smul_im, smul_add, smul_smul,
    RingHom.id_apply, smul_eq_mul]

@[simp] lemma Llc_apply (u v z : ℂ) : Llc u v z = z.re • u + z.im • v := rfl

lemma Llc_det (u v : ℂ) : LinearMap.det (Llc u v) = u.re * v.im - v.re * u.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI (Llc u v), Matrix.det_fin_two]
  have h00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (Llc u v)) 0 0 = u.re := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Llc]
  have h01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (Llc u v)) 0 1 = v.re := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Llc]
  have h10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (Llc u v)) 1 0 = u.im := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Llc]
  have h11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (Llc u v)) 1 1 = v.im := by
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Llc]
  rw [h00, h01, h10, h11]

lemma Llc_of_int (u v : ℂ) (m n : ℤ) :
    Llc u v ((m : ℂ) + (n : ℂ) * Complex.I) = (m : ℂ) * u + (n : ℂ) * v := by
  simp [Llc, Complex.real_smul]

lemma Llc_injective {u v : ℂ} (h : u.re * v.im - v.re * u.im ≠ 0) :
    Function.Injective (Llc u v) := by
  have hdet : LinearMap.det (Llc u v) ≠ 0 := by rw [Llc_det]; exact h
  have hker : (Llc u v).ker = ⊥ := by
    by_contra hc
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hc)
  exact LinearMap.ker_eq_bot.mp hker

/-- Images of measurable sets under an injective (`ℝ`-)linear self-map of `ℂ` are measurable:
the map extends to a linear equivalence, i.e. a measurable equivalence. -/
lemma measurableSet_image_Llc (u v : ℂ) (hdet : LinearMap.det (Llc u v) ≠ 0)
    (s : Set ℂ) (hs : MeasurableSet s) : MeasurableSet (Llc u v '' s) := by
  have hcoe : ((((Llc u v).equivOfDetNeZero hdet) : ℂ → ℂ)) = Llc u v := by
    funext x
    simp only [LinearMap.equivOfDetNeZero]
    exact LinearEquiv.ofIsUnitDet_apply _ x
  let em : ℂ ≃ᵐ ℂ :=
    (((Llc u v).equivOfDetNeZero hdet).toContinuousLinearEquiv).toHomeomorph.toMeasurableEquiv
  have hcoe2 : (em : ℂ → ℂ) = Llc u v := by
    rw [show (em : ℂ → ℂ) = ((((Llc u v).equivOfDetNeZero hdet) : ℂ → ℂ)) from rfl]
    exact hcoe
  rw [show Llc u v '' s = em '' s from by rw [← hcoe2]]
  rw [show em '' s = em.symm ⁻¹' s from Equiv.image_eq_preimage_symm (em : ℂ ≃ ℂ) s]
  exact hs.preimage em.symm.measurable

/-! ## 2. The unit cell and the lattice -/

/-- The half-open unit cell `[-1/2,1/2) × [-1/2,1/2)` of the Gaussian-integer lattice. -/
def uCell : Set ℂ := Complex.measurableEquivRealProd ⁻¹'
    ((Set.Ico (-(1/2)) (1/2) : Set ℝ) ×ˢ (Set.Ico (-(1/2)) (1/2) : Set ℝ))

lemma mem_uCell (z : ℂ) : z ∈ uCell ↔
    -(1/2) ≤ z.re ∧ z.re < 1/2 ∧ -(1/2) ≤ z.im ∧ z.im < 1/2 := by
  simp only [uCell, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod,
    Set.mem_Ico]
  tauto

lemma measurableSet_uCell : MeasurableSet uCell :=
  (measurableSet_Ico.prod measurableSet_Ico).preimage Complex.measurableEquivRealProd.measurable

lemma volume_uCell : volume uCell = 1 := by
  have hS : NullMeasurableSet
      ((Set.Ico (-(1/2)) (1/2) : Set ℝ) ×ˢ (Set.Ico (-(1/2)) (1/2) : Set ℝ))
      (volume : MeasureTheory.Measure (ℝ × ℝ)) :=
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (f := Complex.measurableEquivRealProd)
    (s := ((Set.Ico (-(1/2)) (1/2) : Set ℝ) ×ˢ (Set.Ico (-(1/2)) (1/2) : Set ℝ))) hS
  rw [show uCell = Complex.measurableEquivRealProd ⁻¹'
      ((Set.Ico (-(1/2)) (1/2) : Set ℝ) ×ˢ (Set.Ico (-(1/2)) (1/2) : Set ℝ)) from rfl, h]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Ico]
  norm_num

/-- The lattice `ℤ u + ℤ v ⊆ ℂ`. -/
def latte (u v : ℂ) : Set ℂ := {w | ∃ a b : ℤ, w = (a : ℂ) * u + (b : ℂ) * v}

/-- The Gaussian integers inside `ℂ`, as a set of complex numbers. -/
def gGrid : Set ℂ := {z | ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * Complex.I}

lemma latte_eq_image (u v : ℂ) : latte u v = Llc u v '' gGrid := by
  ext w; constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a : ℂ) + (b : ℂ) * Complex.I, ⟨a, b, rfl⟩, by simp [Llc, Complex.real_smul]⟩
  · rintro ⟨z, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by simp [Llc, Complex.real_smul]⟩

/-! ## 3. Translations -/

/-- Translation of a set by a complex number. -/
def tsh (w : ℂ) (A : Set ℂ) : Set ℂ := (fun h => w + h) '' A

lemma mem_tsh {w : ℂ} {A : Set ℂ} {x : ℂ} : x ∈ tsh w A ↔ ∃ a ∈ A, w + a = x :=
  Iff.rfl

lemma volume_tsh (w : ℂ) (A : Set ℂ) : volume (tsh w A) = volume A := by
  have h := MeasureTheory.measure_preimage_add volume w (tsh w A)
  rw [show (fun h => w + h) ⁻¹' (tsh w A) = A from ?_] at h
  exact h.symm
  ext x
  simp only [Set.mem_preimage, mem_tsh]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [add_left_cancel hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma measurableSet_tsh {A : Set ℂ} (hA : MeasurableSet A) (w : ℂ) :
    MeasurableSet (tsh w A) := by
  rw [show tsh w A = (fun x => x - w) ⁻¹' A from ?_]
  · exact hA.preimage (by fun_prop)
  · ext x
    simp only [Set.mem_preimage, mem_tsh]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨x - w, hx, by ring⟩

lemma tsh_image (u v : ℂ) (z : ℂ) (A : Set ℂ) :
    tsh (Llc u v z) (Llc u v '' A) = Llc u v '' (tsh z A) := by
  ext x; constructor
  · rw [mem_tsh]
    rintro ⟨f, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨z + a, ⟨a, ha, rfl⟩, by rw [map_add]; exact hx⟩
  · rw [Set.mem_image]
    rintro ⟨y, ⟨a, ha, rfl⟩, hx⟩
    rw [mem_tsh]
    exact ⟨Llc u v a, ⟨a, ha, rfl⟩, by rw [map_add] at hx; exact hx⟩

/-! ## 4. Disjointness of the translates of the fundamental cell -/

lemma image_disjoint_of_injective {f : ℂ → ℂ} (hinj : Function.Injective f) {A B : Set ℂ}
    (h : Disjoint A B) : Disjoint (f '' A) (f '' B) := by
  rw [Set.disjoint_left] at h ⊢
  intro x hxA hxB
  rw [Set.mem_image] at hxA hxB
  obtain ⟨a, ha, rfl⟩ := hxA
  obtain ⟨b, hb, hx⟩ := hxB
  exact h ha (hinj hx ▸ hb)

/-- Distinct Gaussian integers give disjoint translates of the unit cell. -/
lemma disjoint_grid (z₁ z₂ : ℂ) (h₁ : z₁ ∈ gGrid) (h₂ : z₂ ∈ gGrid) (hne : z₁ ≠ z₂) :
    Disjoint (tsh z₁ uCell) (tsh z₂ uCell) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  rw [mem_tsh] at hx₁ hx₂
  obtain ⟨q₁, hq₁, hx₁⟩ := hx₁
  obtain ⟨q₂, hq₂, hx₂⟩ := hx₂
  obtain ⟨m₁, n₁, hz₁⟩ := h₁
  obtain ⟨m₂, n₂, hz₂⟩ := h₂
  have hd : z₁ - z₂ = q₂ - q₁ := by linear_combination hx₁ - hx₂
  have hq₁' := (mem_uCell q₁).mp hq₁
  have hq₂' := (mem_uCell q₂).mp hq₂
  have hreb : (q₂ - q₁).re ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo]
    constructor <;> simp only [Complex.sub_re] <;> linarith [hq₁'.1, hq₁'.2.1, hq₂'.1, hq₂'.2.1]
  have himb : (q₂ - q₁).im ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo]
    constructor <;> simp only [Complex.sub_im]
    <;> linarith [hq₁'.2.2.1, hq₁'.2.2.2, hq₂'.2.2.1, hq₂'.2.2.2]
  have hre : (z₁ - z₂).re = ((m₁ - m₂ : ℤ) : ℝ) := by
    rw [hz₁, hz₂]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_one, mul_zero, add_zero, sub_zero]
    push_cast; ring
  have him : (z₁ - z₂).im = ((n₁ - n₂ : ℤ) : ℝ) := by
    rw [hz₁, hz₂]
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_one, mul_zero, add_zero, sub_zero]
    push_cast; ring
  have hm : m₁ = m₂ := by
    have hmem : ((m₁ - m₂ : ℤ) : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by rw [← hre, hd]; exact hreb
    rw [Set.mem_Ioo] at hmem
    have h1 : (-1 : ℤ) < m₁ - m₂ := by exact_mod_cast hmem.1
    have h2 : m₁ - m₂ < (1 : ℤ) := by exact_mod_cast hmem.2
    omega
  have hn : n₁ = n₂ := by
    have hmem : ((n₁ - n₂ : ℤ) : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by rw [← him, hd]; exact himb
    rw [Set.mem_Ioo] at hmem
    have h1 : (-1 : ℤ) < n₁ - n₂ := by exact_mod_cast hmem.1
    have h2 : n₁ - n₂ < (1 : ℤ) := by exact_mod_cast hmem.2
    omega
  exact hne (by rw [hz₁, hz₂, hm, hn])

/-- Distinct lattice points give disjoint translates of the fundamental parallelogram
`Llc u v '' uCell`. -/
lemma disjoint_tsh_latte (u v : ℂ) (hinj : Function.Injective (Llc u v)) :
    ∀ w₁ w₂ : ℂ, w₁ ∈ latte u v → w₂ ∈ latte u v → w₁ ≠ w₂ →
      Disjoint (tsh w₁ (Llc u v '' uCell)) (tsh w₂ (Llc u v '' uCell)) := by
  intro w₁ w₂ hw₁ hw₂ hne
  obtain ⟨a₁, b₁, hw₁eq⟩ := hw₁
  obtain ⟨a₂, b₂, hw₂eq⟩ := hw₂
  set z₁ : ℂ := (a₁ : ℂ) + (b₁ : ℂ) * Complex.I with hz₁def
  set z₂ : ℂ := (a₂ : ℂ) + (b₂ : ℂ) * Complex.I with hz₂def
  have hLz₁ : Llc u v z₁ = w₁ := by rw [hw₁eq, hz₁def, Llc_of_int]
  have hLz₂ : Llc u v z₂ = w₂ := by rw [hw₂eq, hz₂def, Llc_of_int]
  have hzne : z₁ ≠ z₂ := fun h => hne (by rw [← hLz₁, ← hLz₂, h])
  have hgrid₁ : z₁ ∈ gGrid := ⟨a₁, b₁, by rw [hz₁def]⟩
  have hgrid₂ : z₂ ∈ gGrid := ⟨a₂, b₂, by rw [hz₂def]⟩
  have hd := disjoint_grid z₁ z₂ hgrid₁ hgrid₂ hzne
  rw [← hLz₁, ← hLz₂, tsh_image, tsh_image]
  exact image_disjoint_of_injective hinj hd

/-! ## 5. The lattice-point count -/

/-- **Lattice points of a coset in a disc.**  If `u, v : ℂ` are `ℝ`-linearly independent with
`|det (u,v)| = c > 0`, and `W` is a finite set of points of `ℤu + ℤv` all lying within distance
`R` of `p`, then `#W ≤ π (R + (|u|+|v|)/2)² / c`. -/
lemma card_le_of_mem_latte_closedBall (u v : ℂ) (c : ℝ)
    (hdet : |u.re * v.im - v.re * u.im| = c) (hcpos : 0 < c)
    (p : ℂ) (R : ℝ) (hR : 0 ≤ R) (W : Finset ℂ)
    (hW : ∀ w ∈ W, w ∈ latte u v)
    (hWball : ∀ w ∈ W, ‖w - p‖ ≤ R) :
    (W.card : ℝ) ≤ Real.pi * (R + (‖u‖ + ‖v‖) / 2) ^ 2 / c := by
  have hδ : u.re * v.im - v.re * u.im ≠ 0 := by
    have h := hcpos
    rw [← hdet] at h
    exact abs_pos.mp h
  have hdetL : LinearMap.det (Llc u v) ≠ 0 := by rw [Llc_det]; exact hδ
  have hinj : Function.Injective (Llc u v) := Llc_injective hδ
  set F : Set ℂ := Llc u v '' uCell with hF
  have hFmeas : MeasurableSet F := by
    rw [hF]
    exact measurableSet_image_Llc u v hdetL uCell measurableSet_uCell
  have hFvol : volume F = ENNReal.ofReal c := by
    rw [hF, MeasureTheory.Measure.addHaar_image_linearMap volume (Llc u v) uCell,
      volume_uCell, mul_one, Llc_det, hdet]
  have hFball : ∀ f ∈ F, ‖f‖ ≤ (‖u‖ + ‖v‖) / 2 := by
    intro f hf
    rw [hF, Set.mem_image] at hf
    obtain ⟨q, hq, rfl⟩ := hf
    have hq' := (mem_uCell q).mp hq
    rw [Llc_apply]
    calc ‖q.re • u + q.im • v‖ ≤ ‖q.re • u‖ + ‖q.im • v‖ := norm_add_le _ _
      _ = |q.re| * ‖u‖ + |q.im| * ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (1 / 2) * ‖u‖ + (1 / 2) * ‖v‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (abs_le.mpr ⟨by linarith [hq'.1], by linarith [hq'.2.1]⟩) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_right
              (abs_le.mpr ⟨by linarith [hq'.2.2.1], by linarith [hq'.2.2.2]⟩) (norm_nonneg _)
      _ = (‖u‖ + ‖v‖) / 2 := by ring
  have hdisj : (↑W : Set ℂ).Pairwise (Function.onFun Disjoint (fun w => tsh w F)) := by
    intro w₁ hw₁ w₂ hw₂ hne
    rw [hF]
    exact disjoint_tsh_latte u v hinj w₁ w₂ (hW w₁ hw₁) (hW w₂ hw₂) hne
  have hmeas : ∀ b ∈ W, MeasurableSet (tsh b F) := fun b _ => measurableSet_tsh hFmeas b
  have hvolunion : volume (⋃ w ∈ W, tsh w F) = ENNReal.ofReal (c * W.card) := by
    rw [measure_biUnion_finset hdisj hmeas]
    simp only [volume_tsh, hFvol]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul hcpos.le]
  have hsub : (⋃ w ∈ W, tsh w F) ⊆ Metric.closedBall p (R + (‖u‖ + ‖v‖) / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hwW, hx⟩ := hx
    rw [mem_tsh] at hx
    obtain ⟨f, hfF, rfl⟩ := hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖w + f - p‖ ≤ ‖w - p‖ + ‖f‖ := by
          rw [show w + f - p = (w - p) + f by ring]; exact norm_add_le _ _
      _ ≤ R + (‖u‖ + ‖v‖) / 2 := add_le_add (hWball w hwW) (hFball f hfF)
  have hR' : 0 ≤ R + (‖u‖ + ‖v‖) / 2 := by positivity
  have hle : volume (⋃ w ∈ W, tsh w F) ≤ volume (Metric.closedBall p (R + (‖u‖ + ‖v‖) / 2)) :=
    measure_mono hsub
  rw [hvolunion, Complex.volume_closedBall] at hle
  have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  rw [hpi, ← ENNReal.ofReal_pow hR', ← ENNReal.ofReal_mul (pow_nonneg hR' 2)] at hle
  have hmain : c * W.card ≤ (R + (‖u‖ + ‖v‖) / 2) ^ 2 * Real.pi :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  rw [le_div_iff₀ hcpos, mul_comm (W.card : ℝ) c, mul_comm Real.pi]
  exact hmain

/-! ## 6. Bridging `ℤ[i]` to `ℂ` -/

lemma toComplex_injective : Function.Injective (fun z : GaussianInt => z.toComplex) := by
  intro z w h
  apply Zsqrtd.ext
  · have hh := congrArg Complex.re h
    rw [← GaussianInt.intCast_re z, ← GaussianInt.intCast_re w] at hh
    exact_mod_cast hh
  · have hh := congrArg Complex.im h
    rw [← GaussianInt.intCast_im z, ← GaussianInt.intCast_im w] at hh
    exact_mod_cast hh

lemma det_toComplex_natAbs (g₁ g₂ : GaussianInt) :
    |(g₁.toComplex).re * (g₂.toComplex).im - (g₂.toComplex).re * (g₁.toComplex).im|
      = ((g₁.re * g₂.im - g₁.im * g₂.re).natAbs : ℝ) := by
  rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_im, ← GaussianInt.intCast_re,
    ← GaussianInt.intCast_im]
  rw [show ((g₁.re : ℤ) : ℝ) * ((g₂.im : ℤ) : ℝ) = ((g₁.re * g₂.im : ℤ) : ℝ) by push_cast; ring,
    show ((g₂.re : ℤ) : ℝ) * ((g₁.im : ℤ) : ℝ) = ((g₂.re * g₁.im : ℤ) : ℝ) by push_cast; ring,
    show ((g₁.re * g₂.im : ℤ) : ℝ) - ((g₂.re * g₁.im : ℤ) : ℝ)
        = (((g₁.re * g₂.im - g₁.im * g₂.re : ℤ)) : ℝ) by push_cast; ring,
    Nat.cast_natAbs, Int.cast_abs]

/-! ## 7. The main theorem -/

theorem polarBox_lattice_count (Pa : Work.FITop.Params) (φ : ℝ) (z₀ g₁ g₂ : GaussianInt) (c : ℕ)
    (hc : (g₁.re * g₂.im - g₁.im * g₂.re).natAbs = c) (hcpos : 1 ≤ c) :
    (({z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - z₀ = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}).ncard : ℝ)
      ≤ Real.pi * (5 * (Pa.θ * Real.sqrt Pa.N)
            + Real.sqrt ((Work.FIPlan.gnorm g₁ : ℝ)) + Real.sqrt ((Work.FIPlan.gnorm g₂ : ℝ))) ^ 2
          / (c : ℝ) := by
  classical
  set Fs : Finset GaussianInt := (Work.FIArea3.polarBoxFinset Pa φ).filter
      (fun z => ∃ a b : ℤ, z - z₀ = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂) with hFsdef
  have hset : {z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - z₀ = (a : GaussianInt) * g₁ + (b : GaussianInt) * g₂}
      = (↑Fs : Set GaussianInt) := by
    ext z; simp [hFsdef, Finset.mem_filter]
  rw [hset, Set.ncard_coe_finset]
  set u : ℂ := g₁.toComplex with hu
  set v : ℂ := g₂.toComplex with hv
  set R : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hRdef
  set p : ℂ := (Real.sqrt Pa.N : ℂ) * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I)
      - z₀.toComplex with hp
  set W : Finset ℂ := Fs.image (fun z => z.toComplex - z₀.toComplex) with hWdef
  have hWcard : W.card = Fs.card := by
    rw [hWdef]
    refine Finset.card_image_of_injective Fs ?_
    intro a b hab
    exact toComplex_injective (sub_left_inj.mp hab)
  have hdet : |u.re * v.im - v.re * u.im| = (c : ℝ) := by
    rw [hu, hv, det_toComplex_natAbs, hc]
  have hcpos' : (0 : ℝ) < (c : ℝ) := by
    have : 0 < c := by omega
    exact_mod_cast this
  have hRpos : 0 ≤ R := by
    rw [hRdef]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _)
  have hWmem : ∀ w ∈ W, w ∈ latte u v := by
    intro w hw
    rw [hWdef, Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hFsdef, Finset.mem_filter] at hz
    obtain ⟨_, a, b, hzab⟩ := hz
    refine ⟨a, b, ?_⟩
    have h := congrArg GaussianInt.toComplex hzab
    simp only [map_sub, map_add, map_mul, map_intCast] at h
    rw [hu, hv]
    exact h
  have hWball : ∀ w ∈ W, ‖w - p‖ ≤ R := by
    intro w hw
    rw [hWdef, Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hFsdef, Finset.mem_filter] at hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := (Work.FIArea3.mem_polarBoxFinset.mp hz.1).2
    have hdist := Work.FIArea4.dist_polarBox_le Pa φ z hbox
    have hkey : z.toComplex - z₀.toComplex - p
        = z.toComplex - (Real.sqrt Pa.N : ℂ)
            * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) := by
      rw [hp]; ring
    rw [hRdef, hkey]
    exact hdist
  have hmain := card_le_of_mem_latte_closedBall u v (c : ℝ) hdet hcpos' p R hRpos W hWmem hWball
  rw [hWcard] at hmain
  refine hmain.trans ?_
  have hnorm₁ : ‖u‖ = Real.sqrt ((Work.FIPlan.gnorm g₁ : ℕ) : ℝ) := by
    rw [hu]; exact Work.FIArea4.norm_toComplex_eq_sqrt_gnorm g₁
  have hnorm₂ : ‖v‖ = Real.sqrt ((Work.FIPlan.gnorm g₂ : ℕ) : ℝ) := by
    rw [hv]; exact Work.FIArea4.norm_toComplex_eq_sqrt_gnorm g₂
  rw [hnorm₁, hnorm₂, hRdef]
  have hA : 0 ≤ Real.sqrt ((Work.FIPlan.gnorm g₁ : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hB : 0 ≤ Real.sqrt ((Work.FIPlan.gnorm g₂ : ℕ) : ℝ) := Real.sqrt_nonneg _
  apply div_le_div_of_nonneg_right _ hcpos'.le
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply pow_le_pow_left₀
  · exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _))
      (div_nonneg (add_nonneg hA hB) (by norm_num))
  · nlinarith [hA, hB]

end

end Work.FIArea3.JointCount

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct

open Topology ContDiff Filter
open scoped BigOperators Matrix
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Commons.PaperMoebius

/-- The set of points `(x, y) ∈ ℝ²` with `0 ≤ x ≤ 1`. -/
abbrev unitStrip : Set ℝ² := {x | x 0 ∈ Set.Icc 0 1}

/-- The map `(x, y) ↦ (1 - x, y + a)`. -/
def period (a : ℝ) : ℝ² → ℝ² := fun x ↦ !₂[1 - x 0, x 1 + a]

/-- The set of points `(x, y) ∈ ℝ²` with `0 ≤ x ≤ 1` and `0 ≤ y < a`. -/
def fundamentalDomain (a : ℝ) : Set ℝ² :=
  {x | x 0 ∈ Set.Icc 0 1 ∧ x 1 ∈ Set.Ico 0 a}

/-- A Moebius embedding: a smooth isometric embedding of the strip, periodic
under `period a` and injective on a fundamental domain. -/
structure IsMoebiusEmbedding (a : ℝ) (f : ℝ² → ℝ³) : Prop where
  periodic : ∀ x ∈ unitStrip, f (period a x) = f x
  smooth : ContDiffOn ℝ ∞ f unitStrip
  isometry : ∀ x ∈ unitStrip, Isometry (fderivWithin ℝ f unitStrip x)
  embedding : Set.InjOn f (fundamentalDomain a)

/-- A straight pre-bend chord of the strip: `A ∈ {x₀ = 0}`, `B ∈ {x₀ = 1}`. -/
structure BendData where
  A : ℝ²
  B : ℝ²
  left_coord : A 0 = 0
  right_coord : B 0 = 1

namespace BendData

/-- The horizontal displacement of the bend: `Δ = B₁ − A₁`. -/
def slope (b : BendData) : ℝ := b.B 1 - b.A 1

/-- The height of the centreline point met by the bend. -/
def centreHeight (b : BendData) : ℝ := (b.A 1 + b.B 1) / 2

end BendData

/-- An `f`-relative continuous band foliation by pre-bends: a continuous family
`y ↦ [A y, B y]` of straight chords of the strip, each meeting the centreline
point `(1/2, y)` exactly once, with the deck symmetry `chord (y+a)` =
period-flip of `chord y`, continuous endpoints, and each chord a genuine
pre-bend of the embedded band `f`. -/
structure BandFoliation (a : ℝ) (f : ℝ² → ℝ³) (hf : IsMoebiusEmbedding a f) where
  chord : ℝ → BendData
  centre : ∀ y : ℝ, (chord y).centreHeight = y
  deck : ∀ y : ℝ,
    (chord (y + a)).A = period a (chord y).B ∧
    (chord (y + a)).B = period a (chord y).A
  cont_left : Continuous (fun y : ℝ => ((chord y).A 1 : ℝ))
  cont_right : Continuous (fun y : ℝ => ((chord y).B 1 : ℝ))
  preBend : ∀ y : ℝ, ‖f ((chord y).B) - f ((chord y).A)‖ = ‖(chord y).B - (chord y).A‖

namespace BandFoliation

variable {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}

/-- Left endpoint of the leaf through centreline height `y`. -/
def A (F : BandFoliation a f hf) (y : ℝ) : ℝ² := (F.chord y).A

/-- Right endpoint of the leaf through centreline height `y`. -/
def B (F : BandFoliation a f hf) (y : ℝ) : ℝ² := (F.chord y).B

/-- The horizontal displacement `Δ = B₁ − A₁` of the leaf. -/
def Δ (F : BandFoliation a f hf) (y : ℝ) : ℝ := (F.chord y).slope

/-- The image displacement of the leaf. -/
def leafVec (F : BandFoliation a f hf) (y : ℝ) : ℝ³ := f (B F y) - f (A F y)

/-- The unit image direction of the leaf (orientation from `A` to `B`). -/
def imageDir (F : BandFoliation a f hf) (y : ℝ) : ℝ³ :=
  (‖leafVec F y‖ ⁻¹) • leafVec F y

/-- The image midpoint of the leaf. -/
def imageMid (F : BandFoliation a f hf) (y : ℝ) : ℝ³ :=
  (1 / 2 : ℝ) • (f (A F y) + f (B F y))

/-- `A y` lies on the left boundary line. -/
lemma A_left_coord (F : BandFoliation a f hf) (y : ℝ) : (A F y) 0 = 0 :=
  (F.chord y).left_coord

/-- `B y` lies on the right boundary line. -/
lemma B_right_coord (F : BandFoliation a f hf) (y : ℝ) : (B F y) 0 = 1 :=
  (F.chord y).right_coord

/-- `A y` is a unit-strip point. -/
lemma A_mem_unitStrip (F : BandFoliation a f hf) (y : ℝ) : A F y ∈ unitStrip := by
  rw [unitStrip]; simp [A_left_coord F y]

/-- `B y` is a unit-strip point. -/
lemma B_mem_unitStrip (F : BandFoliation a f hf) (y : ℝ) : B F y ∈ unitStrip := by
  rw [unitStrip]; simp [B_right_coord F y]

end BandFoliation

end Commons.PaperMoebius

open Commons.PaperMoebius

namespace Commons.Geometry.Moebius

/-! ## Auxiliary geometry facts -/

/-- The squared norm in the plane is the sum of the squared coordinates. -/
lemma norm_sq_coord_sum (x : ℝ²) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Fin.sum_univ_two]

/-- A point with `x₀ = 0` equals the left-edge point at its own height. -/
lemma leftEdge_eq_vec {A : ℝ²} (hA0 : A 0 = 0) : A = !₂[(0 : ℝ), A 1] := by
  ext i <;> fin_cases i <;> simp [hA0]

/-- A point with `x₀ = 1` equals the right-edge point at its own height. -/
lemma rightEdge_eq_vec {B : ℝ²} (hB0 : B 0 = 1) : B = !₂[(1 : ℝ), B 1] := by
  ext i <;> fin_cases i <;> simp [hB0]

/-- The left-edge point `(0,y)` is in the unit strip. -/
lemma leftEdge_mem_unitStrip (y : ℝ) : (!₂[(0 : ℝ), y] : ℝ²) ∈ unitStrip := by
  unfold unitStrip; constructor <;> norm_num

/-- The right-edge point `(1,y)` is in the unit strip. -/
lemma rightEdge_mem_unitStrip (y : ℝ) : (!₂[(1 : ℝ), y] : ℝ²) ∈ unitStrip := by
  unfold unitStrip; constructor <;> norm_num

/-- `period` sends the left-edge point `(0,y)` to `(1, y+a)`. -/
lemma period_leftEdge (a y : ℝ) : period a (!₂[(0 : ℝ), y] : ℝ²) = !₂[(1 : ℝ), y + a] := by
  ext i <;> fin_cases i <;> simp [period]

/-- `period` sends the right-edge point `(1,y)` to `(0, y+a)`. -/
lemma period_rightEdge (a y : ℝ) : period a (!₂[(1 : ℝ), y] : ℝ²) = !₂[(0 : ℝ), y + a] := by
  ext i <;> fin_cases i <;> simp [period]

/-- `f (1, y + a) = f (0, y)`. -/
lemma f_leftEdge_eq_rightEdge_plus {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : f !₂[(1 : ℝ), y + a] = f !₂[(0 : ℝ), y] := by
  have h := hf.periodic (!₂[(0 : ℝ), y] : ℝ²) (leftEdge_mem_unitStrip y)
  rwa [period_leftEdge] at h

/-- `f (1, y − a) = f (0, y)`. -/
lemma f_leftEdge_eq_rightEdge_minus {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : f !₂[(1 : ℝ), y - a] = f !₂[(0 : ℝ), y] := by
  have h := hf.periodic (!₂[(1 : ℝ), y - a] : ℝ²) (rightEdge_mem_unitStrip (y - a))
  rw [period_rightEdge] at h
  have harg : y - a + a = y := by ring
  rw [harg] at h
  exact h.symm

/-- The image of the right edge is `2a`-periodic: `f (1, t + 2a) = f (1, t)`. -/
lemma rightEdge_image_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (t : ℝ) : f !₂[(1 : ℝ), t + 2 * a] = f !₂[(1 : ℝ), t] := by
  have h1 : f !₂[(1 : ℝ), t + 2 * a] = f !₂[(0 : ℝ), t + a] := by
    have h := f_leftEdge_eq_rightEdge_plus hf (t + a)
    have harg : t + a + a = t + 2 * a := by ring
    rwa [harg] at h
  have h2 : f !₂[(1 : ℝ), t] = f !₂[(0 : ℝ), t + a] := by
    have h := f_leftEdge_eq_rightEdge_minus hf (t + a)
    have harg : t + a - a = t := by ring
    rwa [harg] at h
  rw [h1, h2]

/-- `t ↦ f (1, t)` is periodic of period `2a`. -/
lemma rightEdge_image_periodic {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    Function.Periodic (fun t : ℝ => f !₂[(1 : ℝ), t]) (2 * a) :=
  fun t => rightEdge_image_period hf t

/-- **Integer window lemma**: for `a > 0` and any real `t`, there is an integer
`k` with `t - k • (2a) ∈ Icc (A - a) (A + a)` (an interval of length `2a`, one
full period of the edge image). -/
lemma exists_int_window {A a t : ℝ} (ha : 0 < a) :
    ∃ k : ℤ, A - a ≤ t - k • (2 * a) ∧ t - k • (2 * a) ≤ A + a := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  set c : ℝ := (t - A - a) / (2 * a) with hc
  have hle : c ≤ ((⌈c⌉ : ℤ) : ℝ) := Int.le_ceil c
  have hlt : ((⌈c⌉ : ℤ) : ℝ) < c + 1 := Int.ceil_lt_add_one c
  have hcmul : c * (2 * a) = t - A - a := by
    rw [hc, div_mul_cancel₀ _ (ne_of_gt h2a)]
  have hsmul : (⌈c⌉ : ℤ) • (2 * a) = ((⌈c⌉ : ℤ) : ℝ) * (2 * a) := zsmul_eq_mul _ _
  refine ⟨⌈c⌉, ?_, ?_⟩
  · have h1 : ((⌈c⌉ : ℤ) : ℝ) * (2 * a) < (c + 1) * (2 * a) :=
      mul_lt_mul_of_pos_right hlt h2a
    rw [add_mul, one_mul, hcmul] at h1
    rw [hsmul]; linarith
  · have h1 : (2 * a) * c ≤ (2 * a) * ((⌈c⌉ : ℤ) : ℝ) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt h2a)
    have h2 : (2 * a) * c = t - A - a := by rw [mul_comm, hcmul]
    rw [h2] at h1
    rw [hsmul]; linarith

/-- The leaf vector is nonzero (a leaf has nondegenerate image chord). -/
lemma leafVec_ne_zero {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}
    (F : BandFoliation a f hf) (y : ℝ) : BandFoliation.leafVec F y ≠ 0 := by
  intro h0
  have hpre : ‖(F.chord y).B - (F.chord y).A‖ = ‖BandFoliation.leafVec F y‖ := by
    rw [BandFoliation.leafVec]
    simpa [BandFoliation.A, BandFoliation.B] using (F.preBend y).symm
  have hcoord : ((F.chord y).B - (F.chord y).A) 0 = 1 := by
    have hb := (F.chord y).right_coord
    have ha := (F.chord y).left_coord
    simp [ha, hb]
  have hge : (1 : ℝ) ≤ ‖(F.chord y).B - (F.chord y).A‖ := by
    have hsq : ‖(F.chord y).B - (F.chord y).A‖ ^ 2 =
        1 + ((F.chord y).B - (F.chord y).A) 1 ^ 2 := by
      rw [norm_sq_coord_sum, hcoord]; ring
    have h2 : (1 : ℝ) ≤ ‖(F.chord y).B - (F.chord y).A‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (((F.chord y).B - (F.chord y).A) 1)]
    have h3 : (1 : ℝ) ≤ Real.sqrt (‖(F.chord y).B - (F.chord y).A‖ ^ 2) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using h2)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h3
  rw [h0, norm_zero] at hpre
  linarith

/-- The leaf vector is `‖leafVec‖ • imageDir`. -/
lemma leafVec_eq_norm_smul {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}
    (F : BandFoliation a f hf) (y : ℝ) :
    BandFoliation.leafVec F y =
      ‖BandFoliation.leafVec F y‖ • BandFoliation.imageDir F y := by
  unfold BandFoliation.imageDir
  rw [smul_smul]
  have hne : ‖BandFoliation.leafVec F y‖ ≠ 0 := norm_ne_zero_iff.mpr (leafVec_ne_zero F y)
  rw [mul_inv_cancel₀ hne, one_smul]

/-- The dot-product form of perpendicularity converts to `inner`. -/
lemma inner_imageDir_eq_zero {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}
    (F : BandFoliation a f hf) {y δ : ℝ}
    (hperp : WithLp.ofLp (BandFoliation.imageDir F y) ⬝ᵥ
        WithLp.ofLp (BandFoliation.imageDir F (y + δ)) = 0) :
    inner ℝ (BandFoliation.imageDir F (y + δ)) (BandFoliation.imageDir F y) = 0 := by
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  exact hperp

/-! ## Main theorem -/

theorem escape_of_shared_endpoint {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (F : BandFoliation a f hf) {y δ : ℝ} (hδ0 : 0 < δ) (hδa : δ < a)
    (hperp : WithLp.ofLp (BandFoliation.imageDir F y) ⬝ᵥ
        WithLp.ofLp (BandFoliation.imageDir F (y + δ)) = 0)
    (hcop : WithLp.ofLp (BandFoliation.imageMid F y - BandFoliation.imageMid F (y + δ)) ⬝ᵥ
        (WithLp.ofLp (BandFoliation.imageDir F y) ⨯₃
          WithLp.ofLp (BandFoliation.imageDir F (y + δ))) = 0)
    (hshared : f ((F.chord y).A) = f ((F.chord (y + δ)).A))
    (hfar : 1 < ‖f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)‖) :
    ∃ s ∈ Set.Icc ((F.chord y).A 1 - a) ((F.chord y).A 1 + a),
      ∃ c : ℝ, ∃ n : ℝ³,
        inner ℝ n (f (F.chord y).B - f (F.chord y).A) = 0 ∧
          f !₂[(1 : ℝ), s] - (1 / 2 : ℝ) • (f (F.chord y).A + f (F.chord y).B) =
            c • (f (F.chord y).B - f (F.chord y).A) + n ∧
          1 < ‖n‖ := by
  -- The right-edge point of the second leaf is `!₂[1, t]`.
  set t : ℝ := (F.chord (y + δ)).B 1 with ht
  have hBd_vec : (F.chord (y + δ)).B = !₂[(1 : ℝ), t] := by
    have h := rightEdge_eq_vec (F.chord (y + δ)).right_coord
    rw [ht]; exact h
  -- shift so that the point lies in the required window
  obtain ⟨k, hk1, hk2⟩ := exists_int_window (A := (F.chord y).A 1) (t := t) ha
  -- periodicity: `f (1, t - k•(2a)) = f (1, t)`
  have hshift : f !₂[(1 : ℝ), t - k • (2 * a)] = f !₂[(1 : ℝ), t] :=
    (rightEdge_image_periodic hf).sub_zsmul_eq k
  have hpt : f !₂[(1 : ℝ), t - k • (2 * a)] = f ((F.chord (y + δ)).B) := by
    rw [hshift, hBd_vec]
  refine ⟨t - k • (2 * a), ⟨hk1, hk2⟩, -(1 / 2 : ℝ),
    f ((F.chord (y + δ)).B) - f ((F.chord y).A), ?_, ?_, ?_⟩
  · -- perpendicularity of the escape vector to the first leaf's direction
    have hinner : inner ℝ (BandFoliation.leafVec F (y + δ)) (BandFoliation.leafVec F y) = 0 := by
      rw [leafVec_eq_norm_smul F (y + δ), leafVec_eq_norm_smul F y,
        real_inner_smul_left, real_inner_smul_right, inner_imageDir_eq_zero F hperp]
      ring
    have hAB : f ((F.chord (y + δ)).B) - f ((F.chord y).A) =
        BandFoliation.leafVec F (y + δ) := by
      simp only [BandFoliation.leafVec, BandFoliation.A, BandFoliation.B]
      rw [hshared]
    have hABy : f ((F.chord y).B) - f ((F.chord y).A) = BandFoliation.leafVec F y := rfl
    rw [hAB, hABy]
    exact hinner
  · -- the decomposition identity
    rw [hpt]
    module
  · -- distance bound
    rw [hshared]
    exact hfar

end Commons.Geometry.Moebius
/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Projection
import Submission.Vinogradov.Straighten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The geometric core of the scale descent (GLYZ Lemma 3.6)

This module contains the *plate comparison* which drives the scale descent of
Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*
(arXiv:1912.09798), §3.3: a plate of a general curve `D` with torsion, at a fine centre `c_i` which
is close to a sub-block centre `c`, is contained in the plate of the *Taylor polynomial* of `D` at
the coarse centre `c_I`, enlarged by a fixed multiplicative factor.

The proof has three layers.

* **`moment_tube`** (the moment-curve layer).  Since the moment curve is a polynomial, the
  translation identity `plate l δ v ⊆ γ(u) + Ctube l · (plate l σ u - γ(u))` is *exact algebra* for
  the moment curve: it follows from the two straightening identities `affVecDual_gammaVec` and
  `affVecDual_gammaDeriv`, the box-coordinate formula `affVecDual_eq_sum_gammaDeriv`, and the
  explicit coordinate bound of `tubeVec_coord_abs_le`.  The constant `Ctube l = 1 + l·l!` is
  harmless because the *fine* scale `δ` and the displacement are both at most `σ`.

* **`ball_subset_taylorPlateLin`** (the non-degeneracy layer).  The straightened plate of the
  Taylor polynomial contains a ball of radius `tubeRho l A cT σ` around its centre: this is
  `Straighten.exists_ball_subset_curveAff_plate` (the moment-curve ball, transported by the
  straightening map) combined with `Straighten.curveAff_image_plate` and the monotonicity
  `CurveLayer.curvePlate_mono`.

* **`curvePlate_subset_taylorPlate`** (the Taylor layer).  The Taylor error
  `D^{(i)}(c_i) - T^{(i)}(c_i) = O(R κ^{l+1-i})` (from `CurveTaylor`) is turned into a *small
  vector* which is absorbed by the ball of the previous step, using the convexity of the plate
  (`absorb_ball_smul`).  This is the only place where the arithmetic constraint
  `R κ^{l+1} ≲ ε · σ^l` — i.e. GLYZ's `κ^{(l+1)/l}` condition on the model scale — enters.

The constants are all *fixed* (they depend on `l`, `A`, `c_T`, `R` but not on the scale), which is
what makes the tube lemma usable at every step of the descent.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- The fixed geometric constant of the tube lemma: `Ctube l = 1 + l·l!`. -/
noncomputable def Ctube (l : ℕ) : ℝ := 1 + (l : ℝ) * (l.factorial : ℝ)

lemma one_le_Ctube (l : ℕ) : 1 ≤ Ctube l := by
  rw [Ctube]
  nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) l.factorial]

lemma Ctube_pos (l : ℕ) : 0 < Ctube l := lt_of_lt_of_le zero_lt_one (one_le_Ctube l)

/-- A point of the plate of the moment curve, written in "difference coordinates" around the
centre `γ(s)`: `tubeVec l y δ s = γ(s) + Σ_i y_i δ^{i+1} γ^{(i+1)}(s)`. -/
noncomputable def tubeVec (l : ℕ) (y : E l) (δ s : ℝ) : E l :=
  gammaVec l s + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) s)

lemma tubeVec_apply (l : ℕ) (y : E l) (δ s : ℝ) :
    tubeVec l y δ s
      = gammaVec l s + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) s) := rfl

/-- **The tube identity of the moment curve.**  Shifting a plate point from the centre `s` to the
centre `s + u` is an application of the transpose affine map `A_{1,u}`. -/
theorem tubeVec_shift (l : ℕ) (y : E l) (δ u s : ℝ) :
    gammaVec l (s + u) - gammaVec l u
        + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) (s + u))
      = affVecDual l 1 u (tubeVec l y δ s) := by
  have hsum : (∑ i : Fin l,
        affVecDual l 1 u (y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) s)))
      = ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) (s + u)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [affVecDual_smul, affVecDual_smul, affVecDual_gammaDeriv]
    simp only [one_mul, one_pow, one_smul]
  rw [tubeVec, affVecDual_add, affVecDual_sum, hsum, affVecDual_gammaVec]
  simp only [one_mul]

/-- Coordinate bound for the tube vector. -/
private lemma tubeVec_coord_abs_le (l : ℕ) {y : E l} (hy : ∀ i : Fin l, |y i| ≤ 1)
    {δ σ s : ℝ} (hδ0 : 0 ≤ δ) (hδσ : δ ≤ σ) (hs : |s| ≤ σ) (i : Fin l) :
    |tubeVec l y δ s i| ≤ (1 + (l : ℝ) * (l.factorial : ℝ)) * σ ^ (i.val + 1) := by
  have hσ0 : 0 ≤ σ := le_trans hδ0 hδσ
  have h1 : |gammaVec l s i| ≤ σ ^ (i.val + 1) := by
    rw [gammaVec_apply, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg s) hs _
  have hdesc : ∀ r : Fin l,
      |(((i.val + 1).descFactorial (r.val + 1) : ℕ) : ℝ)| ≤ (l.factorial : ℝ) := by
    intro r
    have h := gammaDeriv_coord_abs_le l (t := (1 : ℝ)) (by norm_num) (r.val + 1) i
    rw [gammaDeriv_apply] at h
    simpa using h
  have hdδ : ∀ r : Fin l, |δ ^ (r.val + 1)| ≤ σ ^ (r.val + 1) := by
    intro r
    rw [abs_of_nonneg (pow_nonneg hδ0 _)]
    exact pow_le_pow_left₀ hδ0 hδσ _
  have hexp : ∀ r : Fin l, (y r • (δ ^ (r.val + 1) • gammaDeriv l (r.val + 1) s)) i
      = y r * (δ ^ (r.val + 1) * gammaDeriv l (r.val + 1) s i) := by
    intro r
    rw [PiLp.smul_apply, smul_eq_mul, PiLp.smul_apply, smul_eq_mul]
  have h2 : ∀ r : Fin l,
      |y r * (δ ^ (r.val + 1) * gammaDeriv l (r.val + 1) s i)|
        ≤ (l.factorial : ℝ) * σ ^ (i.val + 1) := by
    intro r
    by_cases hri : r.val + 1 ≤ i.val + 1
    · have hss : |s ^ (i.val + 1 - (r.val + 1))| ≤ σ ^ (i.val + 1 - (r.val + 1)) := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg s) hs _
      have hprod : |δ ^ (r.val + 1)| * |s ^ (i.val + 1 - (r.val + 1))| ≤ σ ^ (i.val + 1) := by
        calc |δ ^ (r.val + 1)| * |s ^ (i.val + 1 - (r.val + 1))|
            ≤ σ ^ (r.val + 1) * σ ^ (i.val + 1 - (r.val + 1)) :=
              mul_le_mul (hdδ r) hss (abs_nonneg _) (pow_nonneg hσ0 _)
          _ = σ ^ (i.val + 1) := by
              rw [← pow_add]
              congr 1
              omega
      rw [abs_mul, abs_mul, gammaDeriv_apply, abs_mul]
      have hinner : |δ ^ (r.val + 1)|
          * (|(((i.val + 1).descFactorial (r.val + 1) : ℕ) : ℝ)|
              * |s ^ (i.val + 1 - (r.val + 1))|) ≤ (l.factorial : ℝ) * σ ^ (i.val + 1) := by
        calc |δ ^ (r.val + 1)|
              * (|(((i.val + 1).descFactorial (r.val + 1) : ℕ) : ℝ)|
                * |s ^ (i.val + 1 - (r.val + 1))|)
            = (|δ ^ (r.val + 1)| * |s ^ (i.val + 1 - (r.val + 1))|)
                * |(((i.val + 1).descFactorial (r.val + 1) : ℕ) : ℝ)| := by ring
          _ ≤ σ ^ (i.val + 1) * (l.factorial : ℝ) :=
              mul_le_mul hprod (hdesc r) (abs_nonneg _) (pow_nonneg hσ0 _)
          _ = (l.factorial : ℝ) * σ ^ (i.val + 1) := by ring
      refine le_trans (mul_le_mul (hy r) hinner (by positivity) zero_le_one) ?_
      simp
    · have hz : ((i.val + 1).descFactorial (r.val + 1)) = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [gammaDeriv_apply, hz]
      simp only [Nat.cast_zero, zero_mul, mul_zero, abs_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hσ0 _)
  have hsum : (∑ r : Fin l, y r • (δ ^ (r.val + 1) • gammaDeriv l (r.val + 1) s)) i
      = ∑ r : Fin l, (y r • (δ ^ (r.val + 1) • gammaDeriv l (r.val + 1) s)) i := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
  have hsum2 : (∑ r : Fin l, (y r • (δ ^ (r.val + 1) • gammaDeriv l (r.val + 1) s)) i)
      = ∑ r : Fin l, (y r * (δ ^ (r.val + 1) * gammaDeriv l (r.val + 1) s i)) :=
    Finset.sum_congr rfl fun r _ => hexp r
  rw [tubeVec_apply, PiLp.add_apply, hsum, hsum2]
  have hcard : (∑ _r : Fin l, (l.factorial : ℝ) * σ ^ (i.val + 1))
      = (l : ℝ) * ((l.factorial : ℝ) * σ ^ (i.val + 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : |∑ r : Fin l, (y r * (δ ^ (r.val + 1) * gammaDeriv l (r.val + 1) s i))|
      ≤ (l : ℝ) * ((l.factorial : ℝ) * σ ^ (i.val + 1)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← hcard]
    exact Finset.sum_le_sum fun r _ => h2 r
  calc |gammaVec l s i + ∑ r : Fin l, (y r * (δ ^ (r.val + 1) * gammaDeriv l (r.val + 1) s i))|
      ≤ |gammaVec l s i|
        + |∑ r : Fin l, (y r * (δ ^ (r.val + 1) * gammaDeriv l (r.val + 1) s i))| :=
        abs_add_le _ _
    _ ≤ σ ^ (i.val + 1) + (l : ℝ) * ((l.factorial : ℝ) * σ ^ (i.val + 1)) := add_le_add h1 h3
    _ = (1 + (l : ℝ) * (l.factorial : ℝ)) * σ ^ (i.val + 1) := by ring

/-- **The moment-curve tube lemma.**  A plate point of the moment curve at scale `δ` and centre
offset `v` at distance at most `σ` from the centre `u` differs from `γ(u)` by a vector of the
plate at `u` of scale `Ctube l · σ`. -/
theorem moment_tube (l : ℕ) (hl : 1 ≤ l) {y : E l} (hy : ∀ i : Fin l, |y i| ≤ 1)
    {δ σ u v : ℝ} (hδ0 : 0 ≤ δ) (hσ : 0 < σ) (hm : max δ |v - u| ≤ σ) :
    ∃ w : E l, (∀ i : Fin l, |w i| ≤ 1) ∧
      gammaVec l v - gammaVec l u
          + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) v)
        = curvePlateLin l (gammaDeriv l) (Ctube l * σ) u w := by
  set s : ℝ := v - u with hs
  have hvu : s + u = v := by rw [hs]; ring
  have hsabs : |s| ≤ σ := le_trans (le_max_right δ |s|) hm
  have hδσ : δ ≤ σ := le_trans (le_max_left δ |s|) hm
  set Z : E l := tubeVec l y δ s with hZ
  have hZcoord : ∀ i : Fin l, |Z i| ≤ (1 + (l : ℝ) * (l.factorial : ℝ)) * σ ^ (i.val + 1) := by
    intro i
    rw [hZ]
    exact tubeVec_coord_abs_le l hy hδ0 hδσ hsabs i
  set sc : ℝ := Ctube l * σ with hscdef
  have hscpos : 0 < sc := mul_pos (Ctube_pos l) hσ
  refine ⟨(WithLp.equiv 2 (Fin l → ℝ)).symm
    (fun i => Z i * (((i.val + 1).factorial : ℝ)⁻¹ * (sc ^ (i.val + 1))⁻¹)), ?_, ?_⟩
  · intro i
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm
        (fun i => Z i * (((i.val + 1).factorial : ℝ)⁻¹ * (sc ^ (i.val + 1))⁻¹))) i
        = Z i * (((i.val + 1).factorial : ℝ)⁻¹ * (sc ^ (i.val + 1))⁻¹) := rfl
    have hfa : |(((i.val + 1).factorial : ℝ))⁻¹| = (((i.val + 1).factorial : ℝ))⁻¹ :=
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hsa : |((sc : ℝ) ^ (i.val + 1))⁻¹| = ((sc : ℝ) ^ (i.val + 1))⁻¹ :=
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hscpos.le _))
    rw [hcoe, abs_mul, abs_mul, hfa, hsa]
    have hfac : (0 : ℝ) < ((i.val + 1).factorial : ℝ) := by positivity
    have hifac : (((i.val + 1).factorial : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hfac]
      exact_mod_cast Nat.factorial_pos (i.val + 1)
    have hscp : 0 < sc ^ (i.val + 1) := pow_pos hscpos _
    have hics : sc ^ (i.val + 1) * (sc ^ (i.val + 1))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hscp)
    have hC1 : (1 : ℝ) ≤ Ctube l := one_le_Ctube l
    have hZ' : |Z i| ≤ ((i.val + 1).factorial : ℝ) * sc ^ (i.val + 1) := by
      have h1 := hZcoord i
      have hscg : sc ^ (i.val + 1) = Ctube l ^ (i.val + 1) * σ ^ (i.val + 1) := by
        rw [hscdef, mul_pow]
      have h3 : (1 : ℝ) ≤ ((i.val + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos (i.val + 1)
      have h5 : Ctube l ≤ Ctube l ^ (i.val + 1) :=
        le_self_pow₀ hC1 (by omega)
      have hkey : Ctube l ≤ ((i.val + 1).factorial : ℝ) * Ctube l ^ (i.val + 1) := by
        calc Ctube l ≤ Ctube l ^ (i.val + 1) := h5
          _ = 1 * Ctube l ^ (i.val + 1) := (one_mul _).symm
          _ ≤ ((i.val + 1).factorial : ℝ) * Ctube l ^ (i.val + 1) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
      calc |Z i| ≤ (1 + (l : ℝ) * (l.factorial : ℝ)) * σ ^ (i.val + 1) := h1
        _ = Ctube l * σ ^ (i.val + 1) := by rw [Ctube]
        _ ≤ (((i.val + 1).factorial : ℝ) * Ctube l ^ (i.val + 1)) * σ ^ (i.val + 1) :=
            mul_le_mul_of_nonneg_right hkey (pow_nonneg hσ.le _)
        _ = ((i.val + 1).factorial : ℝ) * sc ^ (i.val + 1) := by rw [hscg]; ring
    calc |Z i| * ((((i.val + 1).factorial : ℝ))⁻¹ * (sc ^ (i.val + 1))⁻¹)
        = (|Z i| * (((i.val + 1).factorial : ℝ))⁻¹) * (sc ^ (i.val + 1))⁻¹ := by ring
      _ ≤ ((((i.val + 1).factorial : ℝ) * sc ^ (i.val + 1)) * (((i.val + 1).factorial : ℝ))⁻¹)
            * (sc ^ (i.val + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hZ' (by positivity)) (by positivity)
      _ = 1 := by field_simp
  · rw [← hvu, tubeVec_shift, affVecDual_eq_sum_gammaDeriv, curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm
        (fun i => Z i * (((i.val + 1).factorial : ℝ)⁻¹ * (sc ^ (i.val + 1))⁻¹))) i
        = Z i * (((i.val + 1).factorial : ℝ)⁻¹ * (sc ^ (i.val + 1))⁻¹) := rfl
    have hscal : Z i * (((i.val + 1).factorial : ℝ)⁻¹ * (sc ^ (i.val + 1))⁻¹) * sc ^ (i.val + 1)
        = Z i * (((i.val + 1).factorial : ℝ)⁻¹ * 1) := by
      have hσp : (sc : ℝ) ^ (i.val + 1) ≠ 0 := ne_of_gt (pow_pos hscpos _)
      have hfp : (((i.val + 1).factorial : ℝ)) ≠ 0 := by positivity
      field_simp
    rw [hcoe, smul_smul, smul_smul, one_pow, hscal, mul_one, ← hZ, mul_one]


/-! ## 2. The absorption of a small error into a convex plate -/

/-- **Absorption.**  A point of a convex set `K ∋ 0` which contains the ball of radius `ρ` stays in
`K` after adding a vector of norm `< ερ`, up to the dilation `1 + ε`. -/
theorem absorb_ball_smul {l : ℕ} {K : Set (E l)} (hconv : Convex ℝ K) (h0 : 0 ∈ K)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hball : Metric.ball 0 ρ ⊆ K) (hε : 0 < ε)
    {p w : E l} (hp : p ∈ K) (hE : ‖w‖ < ε * ρ) :
    ∃ q ∈ K, p + w = (1 + ε) • q := by
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hε1ne : (1 + ε) ≠ 0 := ne_of_gt hε1
  have hcoef0 : (0 : ℝ) ≤ ε * (1 + ε)⁻¹ := by positivity
  have hE' : ε⁻¹ • w ∈ K := by
    have h1 : ‖ε⁻¹ • w‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), inv_mul_lt_iff₀ hε]
      linarith [hE, mul_comm ε ρ]
    exact hball (by rw [Metric.mem_ball, dist_zero_right]; exact h1)
  have hsum : ε * (1 + ε)⁻¹ + (1 + ε)⁻¹ = 1 := by field_simp; ring
  have hmem : (1 + ε)⁻¹ • p + (ε * (1 + ε)⁻¹) • (ε⁻¹ • w) ∈ K :=
    hconv hp hE' (by positivity) hcoef0 (by rw [add_comm]; exact hsum)
  refine ⟨(1 + ε)⁻¹ • p + (ε * (1 + ε)⁻¹) • (ε⁻¹ • w), hmem, ?_⟩
  have hc1 : (1 + ε) * (1 + ε)⁻¹ = 1 := mul_inv_cancel₀ hε1ne
  rw [smul_add]
  simp only [smul_smul]
  rw [hc1]
  rw [show (1 + ε) * (ε * (1 + ε)⁻¹ * ε⁻¹) = 1 by field_simp]
  rw [one_smul, one_smul]

/-! ## 3. The ball inside the plate of the Taylor polynomial -/

/-- The constant of `exists_ball_subset_curveAff_plate`, fixed by choice. -/
noncomputable def tubeCB (l : ℕ) : ℝ :=
  if h : 1 ≤ l then Classical.choose (exists_ball_subset_curveAff_plate l h) else 1

lemma tubeCB_pos {l : ℕ} (hl : 1 ≤ l) : 0 < tubeCB l := by
  rw [tubeCB, dif_pos hl]
  exact (Classical.choose_spec (exists_ball_subset_curveAff_plate l hl)).1

/-- The ball inside the straightened plate, at the scale `δ` (which has to be at most `1`). -/
lemma tubeCB_ball {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {A c₀ t₀ δ c' : ℝ}
    (hc : 0 < c₀) (hA : 1 ≤ A) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc' : |c'| ≤ 1)
    (hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t₀ j| ≤ A)
    (htor : c₀ ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t₀)).det) :
    Metric.ball (curveAff l D 1 t₀ (gammaVec l c'))
      (tubeCB l * (c₀ / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * 1 ^ l * ((l.factorial : ℝ))⁻¹ * δ ^ l))
      ⊆ curveAff l D 1 t₀ '' plate l δ c' := by
  rw [tubeCB, dif_pos hl]
  exact (Classical.choose_spec (exists_ball_subset_curveAff_plate l hl)).2 D A c₀ 1 t₀ δ c'
    hc hA one_pos le_rfl hδ0 hδ1 hc' hbd htor

/-- The ball radius of the straightened plate at the model scale `σ`. -/
noncomputable def tubeRho (l : ℕ) (A cT σ : ℝ) : ℝ :=
  tubeCB l * (cT / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
    * Real.sqrt l) * 1 ^ l * ((l.factorial : ℝ))⁻¹ * (min (Ctube l * σ) 1) ^ l)


lemma tubeK_pos {l : ℕ} (hl : 1 ≤ l) {A : ℝ} (hA : 1 ≤ A) :
    0 < (l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1) * Real.sqrt l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hf : (0 : ℝ) < ((l - 1).factorial : ℝ) := by positivity
  have hsl : 0 < Real.sqrt l := by
    rw [Real.sqrt_pos]; exact_mod_cast hl
  have hsA : 0 < Real.sqrt l * A := mul_pos hsl (lt_of_lt_of_le zero_lt_one hA)
  exact mul_pos (mul_pos (mul_pos hl0 hf) (pow_pos hsA _)) hsl

/-- The dimensional constant of the quantitative lower bound for `tubeRho`. -/
noncomputable def tubeK (l : ℕ) (A : ℝ) : ℝ :=
  (l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1) * Real.sqrt l

/-- The fixed geometric constant of the quantitative lower bound for `tubeRho`:
`tubeCG l A cT sigma^l <= tubeRho l A cT sigma` whenever `Ctube l * sigma <= 1`. -/
noncomputable def tubeCG (l : ℕ) (A cT : ℝ) : ℝ := tubeCB l * (cT / tubeK l A) * ((l.factorial : ℝ))⁻¹

lemma tubeCG_pos {l : ℕ} (hl : 1 ≤ l) {A cT : ℝ} (hA : 1 ≤ A) (hcT : 0 < cT) :
    0 < tubeCG l A cT := by
  rw [tubeCG]
  exact mul_pos (mul_pos (tubeCB_pos hl) (div_pos hcT (tubeK_pos hl hA)))
    (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos l))

lemma tubeRho_mono {l : ℕ} (hl : 1 ≤ l) {A cT : ℝ} (hA : 0 ≤ A) (hcT : 0 ≤ cT) {σ₁ σ₂ : ℝ}
    (h0 : 0 ≤ σ₁) (h : σ₁ ≤ σ₂) : tubeRho l A cT σ₁ ≤ tubeRho l A cT σ₂ := by
  have hC : (0 : ℝ) < Ctube l := Ctube_pos l
  have hK0 : 0 ≤ tubeK l A := by
    rw [tubeK]
    have h1 : (0 : ℝ) ≤ ((l - 1).factorial : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt l := Real.sqrt_nonneg l
    have h3 : (0 : ℝ) ≤ (Real.sqrt l * A) ^ (2 * l - 1) := by positivity
    have h4 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    positivity
  have hmin : min (Ctube l * σ₁) 1 ≤ min (Ctube l * σ₂) 1 :=
    min_le_min (by nlinarith) le_rfl
  have hnn : 0 ≤ min (Ctube l * σ₁) 1 := le_min (by nlinarith) zero_le_one
  have hpow : (min (Ctube l * σ₁) 1) ^ l ≤ (min (Ctube l * σ₂) 1) ^ l :=
    pow_le_pow_left₀ hnn hmin l
  have hB : 0 ≤ cT / tubeK l A * 1 ^ (l:ℕ) * ((l.factorial : ℝ))⁻¹ := by
    have h1 : 0 ≤ cT / tubeK l A := div_nonneg hcT hK0
    have h2 : (0:ℝ) ≤ (1:ℝ) ^ (l:ℕ) := by positivity
    have h3 : (0:ℝ) ≤ ((l.factorial : ℝ))⁻¹ := by positivity
    positivity
  rw [tubeRho, tubeRho]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hB) (tubeCB_pos hl).le

/-- **The quantitative lower bound for the ball radius of the straightened plate.** -/
lemma tubeRho_ge (l : ℕ) (A cT σ : ℝ) :
    tubeCG l A cT * (min (Ctube l * σ) 1) ^ l ≤ tubeRho l A cT σ := by
  have he : tubeCG l A cT * (min (Ctube l * σ) 1) ^ l = tubeRho l A cT σ := by
    rw [tubeRho, tubeCG, tubeK, one_pow, mul_one]
    ring
  rw [he]

lemma tubeRho_pos {l : ℕ} (hl : 1 ≤ l) {A cT σ : ℝ} (hcT : 0 < cT) (hA : 1 ≤ A) (hσ : 0 < σ) :
    0 < tubeRho l A cT σ := by
  rw [tubeRho]
  have h6 : (0 : ℝ) < min (Ctube l * σ) 1 :=
    lt_min (mul_pos (Ctube_pos l) hσ) one_pos
  exact mul_pos (tubeCB_pos hl) (mul_pos (mul_pos (mul_pos
    (div_pos hcT (tubeK_pos hl hA)) (pow_pos one_pos l))
    (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos l))) (pow_pos h6 l))

/-- **The ball inside the plate of the Taylor polynomial.**  The straightened plate of the Taylor
polynomial at the coarse centre `t₀`, of scale `min (Ctube l * σ) 1`, contains the ball of radius
`tubeRho l A cT σ` around its centre. -/
lemma ball_subset_taylorPlateLin {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {A cT σ : ℝ}
    (hA : 1 ≤ A) (hcT : 0 < cT) (hσ : 0 < σ) {t₀ u : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hu : |u| ≤ 1)
    (hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t₀ j| ≤ A)
    (htor : cT ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t₀)).det) :
    Metric.ball 0 (tubeRho l A cT σ)
      ⊆ curvePlateLin l (taylorDeriv l D t₀) (min (Ctube l * σ) 1) (t₀ + u) '' unitBox l := by
  set σ₁ : ℝ := min (Ctube l * σ) 1 with hσ₁def
  have hσ₁0 : 0 < σ₁ := lt_min (mul_pos (Ctube_pos l) hσ) one_pos
  have hσ₁1 : σ₁ ≤ 1 := min_le_right _ _
  have hball := tubeCB_ball (D := D) hl hcT hA hσ₁0 hσ₁1 hu hbd htor
  have hcen : curveAff l D 1 t₀ (gammaVec l u) = taylorDeriv l D t₀ 0 (t₀ + u) := by
    rw [curveAff, curveAff_gammaVec, one_mul]
  have hrad : tubeCB l * (cT / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * 1 ^ l * ((l.factorial : ℝ))⁻¹ * σ₁ ^ l) = tubeRho l A cT σ := by
    rw [tubeRho, hσ₁def]
  rw [hcen, hrad, curveAff_image_plate, one_mul] at hball
  intro z hz
  have hz' : taylorDeriv l D t₀ 0 (t₀ + u) + z
      ∈ Metric.ball (taylorDeriv l D t₀ 0 (t₀ + u)) (tubeRho l A cT σ) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    rwa [Metric.mem_ball, dist_zero_right] at hz
  obtain ⟨y, hy, hyz⟩ := hball hz'
  refine ⟨y, hy, ?_⟩
  simp only [one_mul] at hyz
  exact add_left_cancel hyz


/-! ## 4. The tube lemma for a general curve -/

/-- **The geometric core of the scale descent.**  A plate of a general curve `D` with torsion, at a
centre `c_i` close to a sub-centre `c`, is contained in the plate of the *Taylor polynomial* of `D`
at the coarse centre `c_I`, enlarged by `(1 + ε)`.  This is the step which allows the model
decoupling theorem (proved for the moment curve) to be applied to the straightened curve. -/
theorem curvePlate_subset_taylorPlate {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {A cT R : ℝ} (hbd : CurveBounded l D A) (hA : 1 ≤ A) (htor : CurveTorsion l D cT)
    (hcT : 0 < cT) (htay : CurveTaylor l D R) (hR : 0 ≤ R)
    {c_I c c_i δ σ ε : ℝ} (hcI : c_I ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hci : c_i ∈ Set.Icc (0 : ℝ) 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ) (hε : 0 < ε)
    (hclose : max δ |c_i - c| ≤ σ) (hκ1 : |c_i - c_I| ≤ 1)
    (hnum : 2 * (R * ((l : ℝ) + 1) * (max δ |c_i - c_I|) ^ (l + 1)) < ε * tubeRho l A cT σ) :
    curvePlate l D δ c_i ⊆ curvePlate l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c := by
  have hdist1 : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → |a - b| ≤ 1 := by
    intro a b ha hb
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩
  have huab : |c - c_I| ≤ 1 := hdist1 hc hcI
  have hvab : |c_i - c_I| ≤ 1 := hκ1
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : ∀ i : Fin l, |y i| ≤ 1 := hy
  set u : ℝ := c - c_I with hu
  set v : ℝ := c_i - c_I with hv
  have hcu : c_I + u = c := by rw [hu]; ring
  have hcv : c_I + v = c_i := by rw [hv]; ring
  obtain ⟨w, hw, hweq⟩ := moment_tube l hl hy1 (δ := δ) (σ := σ) (u := u) (v := v) hδ0.le hσ
    (by rw [show v - u = c_i - c by rw [hv, hu]; ring]; exact hclose)
  set Λ : E l →ₗ[ℝ] E l := curveAffLin l D 1 c_I with hΛ
  have hlam0 : ∀ t : ℝ, Λ (gammaVec l t) = taylorDeriv l D c_I 0 (c_I + t) - D 0 c_I := by
    intro t
    have h := curveAff_gammaVec l D 1 c_I t
    rw [← hΛ, one_mul] at h
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h)
  have hlamd : ∀ (i : ℕ) (t : ℝ), Λ (gammaDeriv l (i + 1) t)
      = taylorDeriv l D c_I (i + 1) (c_I + t) := by
    intro i t
    have h := curveAffLin_gammaDeriv l D 1 c_I t (i + 1) (by omega)
    rw [← hΛ, one_mul, one_pow, one_smul] at h
    exact h
  have hZ : Λ (tubeVec l y δ v) = (taylorDeriv l D c_I 0 (c_I + v) - D 0 c_I)
      + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) (c_I + v)) := by
    rw [tubeVec_apply, map_add, map_sum]
    congr 1
    · exact hlam0 v
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, hlamd]
  have htransfer : Λ (curvePlateLin l (gammaDeriv l) (Ctube l * σ) u w)
      = curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c w := by
    rw [curvePlateLin_apply, map_sum, curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hlamd, hcu]
  set B : E l := ∑ i : Fin l,
    y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) (c_I + v)) with hB
  set C : E l := curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c w with hC
  have hZ' : Λ (tubeVec l y δ v) = (taylorDeriv l D c_I 0 (c_I + v) - D 0 c_I) + B := by
    rw [hZ, hB]
  have h1 : Λ (tubeVec l y δ v) - Λ (gammaVec l u) = C := by
    rw [← map_sub]
    have hprev : tubeVec l y δ v - gammaVec l u
        = gammaVec l v - gammaVec l u
          + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) v) := by
      rw [tubeVec_apply]; abel
    rw [hprev, hweq, htransfer, hC]
  have hkey : taylorDeriv l D c_I 0 c_i + B = taylorDeriv l D c_I 0 c + C := by
    rw [← hcv, ← hcu]
    have h3 : C = (taylorDeriv l D c_I 0 (c_I + v) - D 0 c_I) + B
        - (taylorDeriv l D c_I 0 (c_I + u) - D 0 c_I) := by
      rw [← h1, hZ', hlam0 u]
    rw [h3]
    abel
  set err : E l := (D 0 c_i - taylorDeriv l D c_I 0 c_i)
      + ∑ i : Fin l,
          y i • (δ ^ (i.val + 1) • (D (i.val + 1) c_i - taylorDeriv l D c_I (i.val + 1) c_i))
    with herrdef
  have hxsplit : D 0 c_i + curvePlateLin l D δ c_i y = taylorDeriv l D c_I 0 c + C + err := by
    have hmain : D 0 c_i + curvePlateLin l D δ c_i y
        = (taylorDeriv l D c_I 0 c_i + B) + err := by
      have hA : curvePlateLin l D δ c_i y
          = ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) c_i) :=
        curvePlateLin_apply l D δ c_i y
      have hB' : B = ∑ i : Fin l,
          y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) c_i) := by
        rw [hB]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcv]
      have herr' : err = (D 0 c_i + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) c_i))
          - (taylorDeriv l D c_I 0 c_i + ∑ i : Fin l,
              y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) c_i)) := by
        rw [herrdef]
        simp only [smul_sub, Finset.sum_sub_distrib]
        abel
      rw [hA, hB', herr']
      abel
    rw [hmain]
    exact congrArg (· + err) hkey
  have hM0 : (0 : ℝ) ≤ max δ |c_i - c_I| := le_trans (abs_nonneg _) (le_max_right _ _)
  have hM1 : max δ |c_i - c_I| ≤ 1 := max_le hδ1 hκ1
  have hsum_eq : ∀ i : ℕ, (∑ j ∈ Finset.Icc i l,
        (v ^ (j - i) / ((j - i).factorial : ℝ)) • D j c_I) = taylorDeriv l D c_I i c_i := by
    intro i
    rw [taylorDeriv_apply]
  have h1err : ‖D 0 c_i - taylorDeriv l D c_I 0 c_i‖ ≤ R * (max δ |c_i - c_I|) ^ (l + 1) := by
    have h := htay 0 l c_I v (by omega) le_rfl hcI hvab
    rw [show c_I + v = c_i from hcv, hsum_eq 0] at h
    rw [show |v| = |c_i - c_I| by rw [hv]] at h
    exact le_trans h (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _) hR)
  have h2err : ∀ i : Fin l,
      ‖y i • (δ ^ (i.val + 1) • (D (i.val + 1) c_i - taylorDeriv l D c_I (i.val + 1) c_i))‖
        ≤ R * (max δ |c_i - c_I|) ^ (l + 1) := by
    intro i
    have h := htay (i.val + 1) l c_I v (by omega) le_rfl hcI hvab
    rw [show c_I + v = c_i from hcv, hsum_eq (i.val + 1)] at h
    rw [show |v| = |c_i - c_I| by rw [hv]] at h
    have hexp : l + 1 - (i.val + 1) = l - i.val := by omega
    rw [hexp] at h
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hδ0.le _)]
    have h5 : |y i| ≤ 1 := hy1 i
    have h7 : |c_i - c_I| ^ (l - i.val) ≤ (max δ |c_i - c_I|) ^ (l - i.val) :=
      pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _
    calc |y i| * (δ ^ (i.val + 1) * ‖D (i.val + 1) c_i - taylorDeriv l D c_I (i.val + 1) c_i‖)
        ≤ 1 * (δ ^ (i.val + 1) * (R * |c_i - c_I| ^ (l - i.val))) :=
          mul_le_mul h5 (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity) zero_le_one
      _ = R * (δ ^ (i.val + 1) * |c_i - c_I| ^ (l - i.val)) := by ring
      _ ≤ R * (max δ |c_i - c_I|) ^ (l + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hR
          calc δ ^ (i.val + 1) * |c_i - c_I| ^ (l - i.val)
              ≤ (max δ |c_i - c_I|) ^ (i.val + 1)
                  * (max δ |c_i - c_I|) ^ (l - i.val) :=
                mul_le_mul (pow_le_pow_left₀ hδ0.le (le_max_left _ _) (i.val + 1)) h7
                  (pow_nonneg (abs_nonneg _) _) (pow_nonneg hM0 _)
            _ = (max δ |c_i - c_I|) ^ (i.val + 1 + (l - i.val)) := (pow_add _ _ _).symm
            _ = (max δ |c_i - c_I|) ^ (l + 1) := by
                congr 1; omega
  have herrbound : ‖err‖ < ε * tubeRho l A cT σ := by
    have h3 : ‖err‖ ≤ R * (max δ |c_i - c_I|) ^ (l + 1)
        + ∑ _i : Fin l, R * (max δ |c_i - c_I|) ^ (l + 1) := by
      rw [herrdef]
      refine le_trans (norm_add_le _ _) (add_le_add h1err ?_)
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => h2err i)
    have h4 : (∑ _i : Fin l, R * (max δ |c_i - c_I|) ^ (l + 1))
        = (l : ℝ) * (R * (max δ |c_i - c_I|) ^ (l + 1)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h4] at h3
    have h5 : R * (max δ |c_i - c_I|) ^ (l + 1)
        + (l : ℝ) * (R * (max δ |c_i - c_I|) ^ (l + 1))
        = ((l : ℝ) + 1) * (R * (max δ |c_i - c_I|) ^ (l + 1)) := by ring
    rw [h5] at h3
    have hρ0 : 0 < tubeRho l A cT σ := tubeRho_pos hl hcT hA hσ
    nlinarith [h3, hnum, hε, hρ0]
  have hconv : Convex ℝ (curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l) :=
    (convex_unitBox l).linear_image _
  have h0u : (0 : E l) ∈ unitBox l := by
    show ∀ i : Fin l, |(0 : E l) i| ≤ 1
    intro i
    simp
  have h0P : (0 : E l) ∈ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l :=
    ⟨0, h0u, by rw [curvePlateLin_apply]; simp⟩
  have hballP : Metric.ball 0 (tubeRho l A cT σ)
      ⊆ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l := by
    have hball := ball_subset_taylorPlateLin (D := D) hl hA hcT hσ hcI huab
      (fun i hi j => hbd i hi c_I hcI j) (htor c_I hcI)
    rw [hcu] at hball
    intro z hz
    have hmono : curvePlateLin l (taylorDeriv l D c_I) (min (Ctube l * σ) 1) c '' unitBox l
        ⊆ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l := by
      rintro _ ⟨y', hy', rfl⟩
      have hle : min (Ctube l * σ) 1 ≤ Ctube l * σ := min_le_left _ _
      have hmem : taylorDeriv l D c_I 0 c
            + curvePlateLin l (taylorDeriv l D c_I) (min (Ctube l * σ) 1) c y'
          ∈ curvePlate l (taylorDeriv l D c_I) (Ctube l * σ) c :=
        curvePlate_mono (D := taylorDeriv l D c_I) (δ := min (Ctube l * σ) 1)
          (δ' := Ctube l * σ) (t := c)
          (le_of_lt (lt_min (mul_pos (Ctube_pos l) hσ) one_pos)) hle ⟨y', hy', rfl⟩
      obtain ⟨y'', hy'', hy''eq⟩ := hmem
      refine ⟨y'', hy'', ?_⟩
      exact add_left_cancel hy''eq
    exact hmono (hball hz)
  have hPw : curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c w
      ∈ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l :=
    ⟨w, fun i => hw i, rfl⟩
  obtain ⟨q, hq, hqeq⟩ :=
    absorb_ball_smul hconv h0P (tubeRho_pos hl hcT hA hσ) hballP hε hPw herrbound
  have hscaled : (1 + ε) • q
      ∈ curvePlateLin l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c '' unitBox l := by
    obtain ⟨y', hy', rfl⟩ := hq
    refine smul_curvePlateLin_subset (taylorDeriv l D c_I) (le_add_of_nonneg_right hε.le)
      ⟨curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c y', ⟨y', hy', rfl⟩, rfl⟩
  rw [curvePlate]
  obtain ⟨y'', hy'', hy''eq⟩ := hscaled
  refine ⟨y'', hy'', ?_⟩
  change taylorDeriv l D c_I 0 c
      + curvePlateLin l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c y''
    = D 0 c_i + curvePlateLin l D δ c_i y
  have hy''eq' : curvePlateLin l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c y''
      = (1 + ε) • q := hy''eq
  rw [hy''eq', ← hqeq, ← hC, ← add_assoc, ← hxsplit]

end Submission.Vinogradov

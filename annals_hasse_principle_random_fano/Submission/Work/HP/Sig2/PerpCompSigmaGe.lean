import Mathlib
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.Vero.sum_sigma_sq_le

namespace Work.HP.Sig2

open Work.HP Work.HP.Vero Finset

set_option autoImplicit false

noncomputable section

/-! ## Elementary algebraic toolkit

Throughout, `x, y : Fin (n+1) → ℤ`, `X = ∑ xᵢ²`, `Y = ∑ yᵢ²`, `g = ∑ xᵢyᵢ`,
`a = (Y xᵢ - g yᵢ)ᵢ`, `b = (X yᵢ - g xᵢ)ᵢ` and `Δ² = X Y - g²`.  The lemmas below record the
elementary identities used in the proof of `PerpCompSigmaGe`. -/

private abbrev iX {n : ℕ} (x : Fin (n + 1) → ℤ) : ℤ := ∑ i, x i ^ 2
private abbrev iY {n : ℕ} (y : Fin (n + 1) → ℤ) : ℤ := ∑ i, y i ^ 2
private abbrev ig {n : ℕ} (x y : Fin (n + 1) → ℤ) : ℤ := ∑ i, x i * y i
private abbrev sigA {n : ℕ} (x y : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => iY y * x i - ig x y * y i
private abbrev sigB {n : ℕ} (x y : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => iX x * y i - ig x y * x i
private abbrev Del2 {n : ℕ} (x y : Fin (n + 1) → ℤ) : ℤ := iX x * iY y - ig x y ^ 2

private lemma eNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v :=
  Real.sqrt_nonneg _

private lemma rNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rNorm v :=
  Real.sqrt_nonneg _

private lemma eNorm_sq_int {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    eNorm v ^ 2 = ((∑ i, v i ^ 2 : ℤ) : ℝ) := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  push_cast
  rfl

private lemma dotR_toR_toR {ι : Type*} [Fintype ι] (u v : ι → ℤ) :
    dotR (toR u) (toR v) = ((∑ i, u i * v i : ℤ) : ℝ) := by
  simp only [dotR, toR, Int.cast_sum, Int.cast_mul]

private lemma abs_dotR_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    |dotR u v| ≤ rNorm u * rNorm v := by
  have h1 : (dotR u v) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
    simp only [dotR]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : rNorm u * rNorm v = Real.sqrt ((∑ i, u i ^ 2) * (∑ i, v i ^ 2)) := by
    rw [rNorm, rNorm, ← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [h2, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h1

private lemma dotR_le_rNorm_mul {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    dotR u v ≤ rNorm u * rNorm v :=
  le_trans (le_abs_self _) (abs_dotR_le u v)

/-! ## The identities for `a`, `b`, `Δ²` -/

private lemma sigA_dot_x {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, x i * sigA x y i) = Del2 x y := by
  simp only [sigA, Del2, iX, iY, ig, pow_two]
  have h : (∑ i, x i * ((∑ j, y j * y j) * x i - (∑ j, x j * y j) * y i))
      = ∑ i, ((∑ j, y j * y j) * (x i * x i) - (∑ j, x j * y j) * (x i * y i)) := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

private lemma sigB_dot_x {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, x i * sigB x y i) = 0 := by
  simp only [sigB, iX, ig, pow_two]
  have h : (∑ i, x i * ((∑ j, x j * x j) * y i - (∑ j, x j * y j) * x i))
      = ∑ i, ((∑ j, x j * x j) * (x i * y i) - (∑ j, x j * y j) * (x i * x i)) := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

private lemma sigA_dot_y {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, y i * sigA x y i) = 0 := by
  simp only [sigA, iY, ig, pow_two]
  have h : (∑ i, y i * ((∑ j, y j * y j) * x i - (∑ j, x j * y j) * y i))
      = ∑ i, ((∑ j, y j * y j) * (x i * y i) - (∑ j, x j * y j) * (y i * y i)) := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

private lemma sigB_dot_y {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, y i * sigB x y i) = Del2 x y := by
  simp only [sigB, Del2, iX, iY, ig, pow_two]
  have h : (∑ i, y i * ((∑ j, x j * x j) * y i - (∑ j, x j * y j) * x i))
      = ∑ i, ((∑ j, x j * x j) * (y i * y i) - (∑ j, x j * y j) * (x i * y i)) := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private lemma sigA_dot_add {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, (x i + y i) * sigA x y i) = Del2 x y := by
  rw [show (∑ i, (x i + y i) * sigA x y i)
        = ∑ i, x i * sigA x y i + ∑ i, y i * sigA x y i from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)]
  rw [sigA_dot_x, sigA_dot_y, add_zero]

private lemma sigB_dot_add {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, (x i + y i) * sigB x y i) = Del2 x y := by
  rw [show (∑ i, (x i + y i) * sigB x y i)
        = ∑ i, x i * sigB x y i + ∑ i, y i * sigB x y i from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)]
  rw [sigB_dot_x, sigB_dot_y, zero_add]

private lemma sigA_norm_sq {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, sigA x y i ^ 2) = iY y * Del2 x y := by
  simp only [sigA, Del2, iX, iY, ig, pow_two]
  have h : (∑ i, ((∑ j, y j * y j) * x i - (∑ j, x j * y j) * y i)
        * ((∑ j, y j * y j) * x i - (∑ j, x j * y j) * y i))
      = ∑ i, ((∑ j, y j * y j) * (∑ j, y j * y j) * (x i * x i)
          - ((2 : ℤ) * (∑ j, y j * y j) * (∑ j, x j * y j)) * (x i * y i)
          + ((∑ j, x j * y j) * (∑ j, x j * y j)) * (y i * y i)) := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

private lemma sigB_norm_sq {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∑ i, sigB x y i ^ 2) = iX x * Del2 x y := by
  simp only [sigB, Del2, iX, iY, ig, pow_two]
  have h : (∑ i, ((∑ j, x j * x j) * y i - (∑ j, x j * y j) * x i)
        * ((∑ j, x j * x j) * y i - (∑ j, x j * y j) * x i))
      = ∑ i, ((∑ j, x j * x j) * (∑ j, x j * x j) * (y i * y i)
          - ((2 : ℤ) * (∑ j, x j * x j) * (∑ j, x j * y j)) * (x i * y i)
          + ((∑ j, x j * y j) * (∑ j, x j * y j)) * (x i * x i)) := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

private lemma Del2_real {n : ℕ} (x y : Fin (n + 1) → ℤ) :
    eNorm x ^ 2 * eNorm y ^ 2 - (dotR (toR x) (toR y)) ^ 2 = (Del2 x y : ℝ) := by
  rw [eNorm_sq_int, eNorm_sq_int, dotR_toR_toR]
  simp only [Del2, iX, iY, ig, pow_two]
  push_cast
  ring

/-! ## The `ℓ²` bound on `q = σ(a,b)` -/

private lemma rNorm_sigma_le {n : ℕ} (u v : Fin (n + 1) → ℤ) :
    rNorm (toR (sigma n u v)) ≤ Real.sqrt 2 * eNorm u * eNorm v := by
  have h := sum_sigma_sq_le u v
  have ha : (∑ i, (u i : ℝ) ^ 2) = eNorm u ^ 2 := by rw [eNorm_sq_int u]; push_cast; rfl
  have hb : (∑ i, (v i : ℝ) ^ 2) = eNorm v ^ 2 := by rw [eNorm_sq_int v]; push_cast; rfl
  rw [ha, hb] at h
  have hS : (∑ m : Mon 2 n, (sigma n u v m : ℝ) ^ 2)
      ≤ (Real.sqrt 2 * eNorm u * eNorm v) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [h]
  calc rNorm (toR (sigma n u v))
      = Real.sqrt (∑ m : Mon 2 n, (sigma n u v m : ℝ) ^ 2) := rfl
    _ ≤ Real.sqrt ((Real.sqrt 2 * eNorm u * eNorm v) ^ 2) := Real.sqrt_le_sqrt hS
    _ = Real.sqrt 2 * eNorm u * eNorm v :=
        Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (eNorm_nonneg' u))
          (eNorm_nonneg' v))

/-! ## The perpendicular component -/

private lemma sub_perpComp_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ (ι → ℤ)) (w : ι → ℝ) :
    w - perpComp Λ w ∈ Submodule.span ℝ (intCastPi '' (Λ : Set (ι → ℤ))) := by
  rw [perpComp, perpCompB, sub_sub_cancel]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨Subtype.val ((Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ).2 i),
      ((Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ).2 i).2, rfl⟩))

private lemma dotR_zero_of_mem_V2R {n : ℕ} (x y : Fin (n + 1) → ℤ) (q : Mon 2 n → ℤ)
    (hx : dotR (toR (veronese 2 n x)) (toR q) = 0)
    (hy : dotR (toR (veronese 2 n y)) (toR q) = 0) :
    ∀ z ∈ V2R n x y, dotR z (toR q) = 0 := by
  intro z hz
  rw [V2R] at hz
  refine Submodule.span_induction (s := {toR (veronese 2 n x), toR (veronese 2 n y)})
    ?_ ?_ ?_ ?_ hz
  · rintro u (rfl | rfl)
    · exact hx
    · exact hy
  · simp [dotR]
  · intro a b ha hb ha' hb'
    simp only [dotR] at ha' hb' ⊢
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha', hb', add_zero]
  · intro c a ha ha'
    simp only [dotR] at ha' ⊢
    have key : (∑ i, (c • a) i * (toR q) i) = c * ∑ i, a i * (toR q) i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    rw [key, ha', mul_zero]

private lemma dotR_perpComp_eq {n : ℕ} (x y : Fin (n + 1) → ℤ) (w : Mon 2 n → ℝ)
    (q : Mon 2 n → ℤ)
    (hx : dotR (toR (veronese 2 n x)) (toR q) = 0)
    (hy : dotR (toR (veronese 2 n y)) (toR q) = 0) :
    dotR (perpComp (Q2 n x y) w) (toR q) = dotR w (toR q) := by
  have hmem : w - perpComp (Q2 n x y) w ∈ V2R n x y := by
    rw [← span_intCast_Q2 n x y]
    exact sub_perpComp_mem _ _
  have h0 := dotR_zero_of_mem_V2R x y q hx hy (w - perpComp (Q2 n x y) w) hmem
  have hlin : dotR (w - perpComp (Q2 n x y) w) (toR q)
      = dotR w (toR q) - dotR (perpComp (Q2 n x y) w) (toR q) := by
    simp only [dotR, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  linarith

/-! ## The main statement -/

/-- The perpendicular component, with respect to `V₂ = span_ℝ{ν₂(x), ν₂(y)}`, of the Veronese
vector `ν₂(x+y)` is at least `‖x‖²‖y‖² - ⟨x,y⟩²` divided by `√2 ‖x‖ ‖y‖`; stated without division.
(Only a constant `≤ 3` is used downstream.)

IMPORTANT: this file must remain importable together with `Submission.Work.HP.Vero`; do not import
`numaux.Defs`, `DetLOrth`, `det_gam`, `det_gam_gen`, `EElow`, `MDEstimates` (name clash on
`Work.HP.orthLat`).
-/
theorem PerpCompSigmaGe {n : ℕ} (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    wedgeNorm x y ^ 2
      ≤ 3 * (eNorm x * eNorm y) * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) := by
  have hrad : 0 ≤ eNorm x ^ 2 * eNorm y ^ 2 - (dotR (toR x) (toR y)) ^ 2 := by
    have h1 : (dotR (toR x) (toR y)) ^ 2 ≤ (eNorm x * eNorm y) ^ 2 :=
      sq_le_sq' (abs_le.mp (abs_dotR_le (toR x) (toR y))).1
        (abs_le.mp (abs_dotR_le (toR x) (toR y))).2
    rw [mul_pow] at h1
    linarith
  have hDnn : 0 ≤ (Del2 x y : ℝ) := by rw [← Del2_real]; exact hrad
  have hwedge : wedgeNorm x y ^ 2 = (Del2 x y : ℝ) := by
    rw [wedgeNorm, Real.sq_sqrt hrad, Del2_real]
  -- `q = σ(a,b)` is orthogonal to `ν₂(x)` and `ν₂(y)`
  have hqx : dotR (toR (veronese 2 n x)) (toR (sigma n (sigA x y) (sigB x y))) = 0 := by
    rw [dotR_toR_toR]
    have h := dot_veronese_sigma n x (sigA x y) (sigB x y)
    simp only [sigA_dot_x x y, sigB_dot_x x y, mul_zero] at h
    rw [h]
    norm_num
  have hqy : dotR (toR (veronese 2 n y)) (toR (sigma n (sigA x y) (sigB x y))) = 0 := by
    rw [dotR_toR_toR]
    have h := dot_veronese_sigma n y (sigA x y) (sigB x y)
    simp only [sigA_dot_y x y, sigB_dot_y x y, zero_mul] at h
    rw [h]
    norm_num
  -- the pairing with `ν₂(x+y)`
  have hwq : dotR (toR (veronese 2 n (x + y))) (toR (sigma n (sigA x y) (sigB x y)))
      = (Del2 x y : ℝ) ^ 2 := by
    rw [dotR_toR_toR]
    have h := dot_veronese_sigma n (x + y) (sigA x y) (sigB x y)
    simp only [Pi.add_apply, sigA_dot_add x y, sigB_dot_add x y] at h
    rw [h]
    push_cast
    ring
  have hperp := dotR_perpComp_eq x y (toR (veronese 2 n (x + y)))
    (sigma n (sigA x y) (sigB x y)) hqx hqy
  have hqnorm := rNorm_sigma_le (sigA x y) (sigB x y)
  -- the norms of `a` and `b`
  have hna : eNorm (sigA x y) = eNorm y * Real.sqrt (Del2 x y : ℝ) := by
    have h2 : eNorm (sigA x y) ^ 2 = eNorm y ^ 2 * (Del2 x y : ℝ) := by
      simp only [eNorm_sq_int, sigA_norm_sq, iY]
      push_cast
      ring
    rw [← Real.sqrt_sq (eNorm_nonneg' (sigA x y)), h2, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (eNorm_nonneg' y)]
  have hnb : eNorm (sigB x y) = eNorm x * Real.sqrt (Del2 x y : ℝ) := by
    have h2 : eNorm (sigB x y) ^ 2 = eNorm x ^ 2 * (Del2 x y : ℝ) := by
      simp only [eNorm_sq_int, sigB_norm_sq, iX]
      push_cast
      ring
    rw [← Real.sqrt_sq (eNorm_nonneg' (sigB x y)), h2, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (eNorm_nonneg' x)]
  have hsq : Real.sqrt (Del2 x y : ℝ) * Real.sqrt (Del2 x y : ℝ) = (Del2 x y : ℝ) := by
    rw [← sq]
    exact Real.sq_sqrt hDnn
  have hab : eNorm (sigA x y) * eNorm (sigB x y) = eNorm x * eNorm y * (Del2 x y : ℝ) := by
    rw [hna, hnb]
    calc eNorm y * Real.sqrt (Del2 x y : ℝ) * (eNorm x * Real.sqrt (Del2 x y : ℝ))
        = eNorm x * eNorm y * (Real.sqrt (Del2 x y : ℝ) * Real.sqrt (Del2 x y : ℝ)) := by ring
      _ = eNorm x * eNorm y * (Del2 x y : ℝ) := by rw [hsq]
  -- Cauchy–Schwarz plus the norm bound
  have key : (Del2 x y : ℝ) ^ 2 ≤ Real.sqrt 2 * (eNorm x * eNorm y) * (Del2 x y : ℝ)
      * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) := by
    have hcs2 : (Del2 x y : ℝ) ^ 2
        ≤ rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
          * rNorm (toR (sigma n (sigA x y) (sigB x y))) := by
      rw [← hwq, ← hperp]
      exact dotR_le_rNorm_mul _ _
    calc (Del2 x y : ℝ) ^ 2
        ≤ rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
            * rNorm (toR (sigma n (sigA x y) (sigB x y))) := hcs2
      _ ≤ rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
            * (Real.sqrt 2 * eNorm (sigA x y) * eNorm (sigB x y)) :=
          mul_le_mul_of_nonneg_left hqnorm (rNorm_nonneg' _)
      _ = rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
            * (Real.sqrt 2 * (eNorm (sigA x y) * eNorm (sigB x y))) := by ring
      _ = rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
            * (Real.sqrt 2 * (eNorm x * eNorm y * (Del2 x y : ℝ))) := by rw [hab]
      _ = Real.sqrt 2 * (eNorm x * eNorm y) * (Del2 x y : ℝ)
            * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) := by ring
  rw [hwedge]
  by_cases h0 : (Del2 x y : ℝ) = 0
  · rw [h0]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (eNorm_nonneg' x) (eNorm_nonneg' y)))
      (rNorm_nonneg' _)
  · have hpos : 0 < (Del2 x y : ℝ) := lt_of_le_of_ne hDnn (Ne.symm h0)
    have hC : Real.sqrt 2 * (eNorm x * eNorm y) * (Del2 x y : ℝ)
          * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
        = (Real.sqrt 2 * (eNorm x * eNorm y)
            * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))) * (Del2 x y : ℝ) := by
      ring
    have hR := rNorm_nonneg' (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
    have he := mul_nonneg (eNorm_nonneg' x) (eNorm_nonneg' y)
    rw [hC] at key
    have key2 : (Del2 x y : ℝ) * (Del2 x y : ℝ)
        ≤ (Real.sqrt 2 * (eNorm x * eNorm y)
            * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))) * (Del2 x y : ℝ) := by
      have h := key
      rw [show (Del2 x y : ℝ) ^ 2 = (Del2 x y : ℝ) * (Del2 x y : ℝ) from by ring] at h
      exact h
    have hle := le_of_mul_le_mul_right key2 hpos
    have h23 : Real.sqrt 2 ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h2 : Real.sqrt 2 * (eNorm x * eNorm y)
          * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
        ≤ 3 * (eNorm x * eNorm y)
          * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h23 he) hR
    linarith [hle, h2]

end

end Work.HP.Sig2

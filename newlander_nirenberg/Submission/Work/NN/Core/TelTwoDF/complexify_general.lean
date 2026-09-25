import Mathlib

/-!
# Complexifying a real analytic function (reusable pieces)

This module contains two sorry-free layers used by
`Submission.Work.NN.Core.TelTwoDF.exists_complexification_hol`:

* `Cx.exists_analytic_complexification`: a real analytic `f` on an open `Ω ⊆ ℝ^ι` agrees near a
  point `x` with the restriction of a complex analytic `F` on `ℂ^ι` to the real locus (the
  power series of `f` at `x`, complexified coefficient by coefficient).
* concrete maps `Cx.rcL`, `Cx.rcSL`, `Cx.sgL`, `Cx.sgC` for the case `ι = (Fin n ⊕ Unit) × Bool`
  (the real coordinates of `ℂⁿ × ℂ`): `sgL` is the linear map that substitutes `(r.2, ζ)` for the
  fibre coordinate, and on the antidiagonal `ζ = conj s.2` it reproduces the real coordinates of
  `s` (`Cx.sgL_real`).

They are also exactly the ingredients needed for the *corrected* version of the target statement
(which must additionally assume `IsOpen Ω`, see `notes_counterexample.md`).
-/

noncomputable section

open scoped Topology
open Set Metric

namespace Work.NN.Core.TelTwoDF
namespace Cx

/-- The complexification of a real formal multilinear series on `ι → ℝ`: the `ℂ`-multilinear
series whose values on the standard basis agree with those of `p`. -/
noncomputable def cplxSeries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : FormalMultilinearSeries ℝ (ι → ℝ) ℂ) : FormalMultilinearSeries ℂ (ι → ℂ) ℂ :=
  fun k => ∑ δ : Fin k → ι,
    (p k fun j => Pi.single (δ j) (1 : ℝ)) •
      ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compContinuousLinearMap
        (fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) (δ j)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cplxSeries_apply (p : FormalMultilinearSeries ℝ (ι → ℝ) ℂ) (k : ℕ)
    (ξ : Fin k → (ι → ℂ)) :
    cplxSeries p k ξ
      = ∑ δ : Fin k → ι, (p k fun j => Pi.single (δ j) (1 : ℝ)) * ∏ j, ξ j (δ j) := by
  rw [cplxSeries]
  change (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => (ι → ℂ)) ℂ ξ)
    (∑ δ : Fin k → ι,
      (p k fun j => Pi.single (δ j) (1 : ℝ)) •
        ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compContinuousLinearMap
          (fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) (δ j)))) = _
  rw [map_sum]
  simp only [ContinuousMultilinearMap.apply_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The complexified series is controlled by the original one. -/
lemma norm_cplxSeries_le (p : FormalMultilinearSeries ℝ (ι → ℝ) ℂ) (k : ℕ) :
    ‖cplxSeries p k‖ ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := cplxSeries p k)
    (M := (Fintype.card ι : ℝ) ^ k * ‖p k‖) (by positivity) fun ξ => ?_
  rw [cplxSeries_apply]
  calc ‖∑ δ : Fin k → ι, (p k fun j => Pi.single (δ j) (1 : ℝ)) * ∏ j, ξ j (δ j)‖
      ≤ ∑ δ : Fin k → ι, ‖(p k fun j => Pi.single (δ j) (1 : ℝ)) * ∏ j, ξ j (δ j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _δ : Fin k → ι, ‖p k‖ * ∏ j, ‖ξ j‖ := by
        refine Finset.sum_le_sum fun δ _ => ?_
        rw [norm_mul, norm_prod]
        have h1 : ‖p k fun j => Pi.single (δ j) (1 : ℝ)‖ ≤ ‖p k‖ := by
          refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) (le_of_eq ?_)
          rw [Finset.prod_congr rfl (fun j _ => by rw [Pi.norm_single, norm_one]),
            Finset.prod_const_one, mul_one]
        exact mul_le_mul h1
          (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
            (fun j _ => norm_le_pi_norm (ξ j) (δ j)))
          (Finset.prod_nonneg fun j _ => norm_nonneg _) (norm_nonneg _)
    _ = (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ∏ j, ‖ξ j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        ring

/-- The standard basis expansion of a vector. -/
private lemma sum_smul_single_eq (y : ι → ℝ) :
    (∑ i : ι, y i • (Pi.single i (1 : ℝ) : ι → ℝ)) = y := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- On the real locus the complexified series agrees with the original one. -/
lemma cplxSeries_diag (p : FormalMultilinearSeries ℝ (ι → ℝ) ℂ) (k : ℕ) (y : ι → ℝ) :
    cplxSeries p k (fun _ => fun i => (y i : ℂ)) = p k (fun _ => y) := by
  rw [cplxSeries_apply]
  have h1 : (fun _ : Fin k => y)
      = (fun _ : Fin k => ∑ i : ι, y i • (Pi.single i (1 : ℝ) : ι → ℝ)) := by
    funext j; exact (sum_smul_single_eq y).symm
  conv_rhs => rw [h1]
  change _ = (p k).toMultilinearMap
    (fun _ : Fin k => ∑ i : ι, y i • (Pi.single i (1 : ℝ) : ι → ℝ))
  rw [MultilinearMap.map_sum (f := (p k).toMultilinearMap)]
  rw [show (∑ δ : Fin k → ι, (p k).toMultilinearMap
        (fun j => y (δ j) • (Pi.single (δ j) (1:ℝ) : ι → ℝ)))
      = ∑ δ : Fin k → ι, (∏ j : Fin k, y (δ j)) • (p k fun j => Pi.single (δ j) (1:ℝ))
      from Finset.sum_congr rfl fun δ _ =>
        MultilinearMap.map_smul_univ (f := (p k).toMultilinearMap) (fun j => y (δ j))
          (fun j => Pi.single (δ j) (1:ℝ))]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Complex.real_smul, mul_comm]
  congr 1
  exact (map_prod Complex.ofRealHom (fun j => y (δ j)) Finset.univ).symm

/-- The canonical embedding of the real lattice into its complexification does not increase
the norm. -/
private lemma norm_ofReal_pi_le (z : ι → ℝ) : ‖(fun i => (z i : ℂ))‖ ≤ ‖z‖ := by
  rw [Pi.norm_def (f := fun i => (z i : ℂ)), Pi.norm_def (f := z), NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  have h : ‖(z i : ℂ)‖₊ = ‖z i‖₊ := by simp
  rw [h]
  exact Finset.le_sup (s := Finset.univ) (f := fun i => ‖z i‖₊) (Finset.mem_univ i)

/-! ## Complexification of a real analytic function -/

private lemma exists_nnreal_pos_lt (r : ENNReal) (hr : 0 < r) :
    ∃ ρ : NNReal, 0 < ρ ∧ (ρ : ENNReal) < r := by
  rcases eq_top_or_lt_top r with h | h
  · exact ⟨1, zero_lt_one, by rw [h]; exact ENNReal.coe_lt_top⟩
  · have hpos : 0 < r.toNNReal := ENNReal.toNNReal_pos (ne_of_gt hr) (ne_of_lt h)
    refine ⟨r.toNNReal / 2, by positivity, ?_⟩
    rw [← ENNReal.coe_toNNReal (ne_of_lt h), ENNReal.coe_lt_coe]
    exact half_lt_self hpos

/-- **Complexification of a real analytic function of real variables**: a real analytic function
`f` on an open set `Ω ⊆ ℝ^ι` agrees near a point `x` with the restriction of a complex analytic
function `F` on the complexification `ℂ^ι` to the real locus. -/
theorem exists_analytic_complexification {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) {f : (ι → ℝ) → ℂ}
    (hf : AnalyticOn ℝ f Ω) {x : ι → ℝ} (hx : x ∈ Ω) :
    ∃ (F : (ι → ℂ) → ℂ) (ρ : ℝ), 0 < ρ ∧
      AnalyticOn ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ) ∧
      ∀ y : ι → ℝ, dist y x < ρ → F (fun i => (y i : ℂ)) = f y := by
  obtain ⟨p, hp⟩ := hf.analyticAt (hΩ.mem_nhds hx)
  obtain ⟨r, hr⟩ := hp
  obtain ⟨ρ₁, hρ₁pos, hρ₁lt⟩ := exists_nnreal_pos_lt r hr.r_pos
  obtain ⟨C, hCpos, hC⟩ := p.norm_mul_pow_le_of_lt_radius (lt_of_lt_of_le hρ₁lt hr.r_le)
  set M : ℕ := Fintype.card ι + 1 with hM
  set ρ₂ : NNReal := ρ₁ / M with hρ₂
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.succ_pos (Fintype.card ι)
  have hρ₂pos : 0 < ρ₂ := by rw [hρ₂]; positivity
  have hρ₂val : (ρ₂ : ℝ) = (ρ₁ : ℝ) / M := by rw [hρ₂]; push_cast; ring
  have hρ₂le : (ρ₂ : ℝ) ≤ (ρ₁ : ℝ) := by
    rw [hρ₂val, div_le_iff₀ hMpos]
    have h1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    exact le_mul_of_one_le_right (NNReal.coe_nonneg ρ₁) h1
  have hqbound : ∀ k : ℕ, ‖cplxSeries p k‖ * (ρ₂ : ℝ) ^ k ≤ C := by
    intro k
    have h1 : ‖cplxSeries p k‖ ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ := norm_cplxSeries_le p k
    have hcardle : ((Fintype.card ι : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.le_succ _
    have h2 : ((Fintype.card ι : ℝ) * (ρ₂ : ℝ)) ^ k ≤ (ρ₁ : ℝ) ^ k := by
      refine pow_le_pow_left₀ (by positivity) ?_ k
      rw [hρ₂val, mul_div_assoc', div_le_iff₀ hMpos]
      nlinarith [hcardle, NNReal.coe_nonneg ρ₁]
    calc ‖cplxSeries p k‖ * (ρ₂ : ℝ) ^ k
        ≤ ((Fintype.card ι : ℝ) ^ k * ‖p k‖) * (ρ₂ : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ‖p k‖ * ((Fintype.card ι : ℝ) * (ρ₂ : ℝ)) ^ k := by ring
      _ ≤ ‖p k‖ * (ρ₁ : ℝ) ^ k := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ C := hC k
  have hqle : ((ρ₂ : NNReal) : ENNReal) ≤ (cplxSeries p).radius :=
    (cplxSeries p).le_radius_of_bound C hqbound
  have hρ₂leρ₁ : ρ₂ ≤ ρ₁ := by
    rw [← NNReal.coe_le_coe]; exact hρ₂le
  refine ⟨fun ξ => (cplxSeries p).sum (ξ - fun i => (x i : ℂ)), (ρ₂ : ℝ),
    by exact_mod_cast hρ₂pos, ?_, ?_⟩
  · -- complex analyticity of the shifted sum of the complexified series
    have h1 : AnalyticOn ℂ (cplxSeries p).sum (Metric.eball 0 (cplxSeries p).radius) :=
      (FormalMultilinearSeries.analyticOnNhd (p := cplxSeries p)).analyticOn
    have h2 := h1.comp_sub (fun i => (x i : ℂ))
    refine h2.mono ?_
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Set.mem_add]
    refine ⟨z - fun i => (x i : ℂ), ?_, fun i => (x i : ℂ), by simp, ?_⟩
    · rw [Metric.mem_eball]
      refine lt_of_lt_of_le ?_ hqle
      rw [edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
      exact hz
    · abel
  · -- the diagonal identity
    intro y hy
    have hne : (fun i => (y i : ℂ)) - (fun i => (x i : ℂ)) = fun i => ((y - x) i : ℂ) := by
      funext i; simp [Pi.sub_apply]
    show (cplxSeries p).sum ((fun i => (y i : ℂ)) - (fun i => (x i : ℂ))) = f y
    rw [hne]
    have hnorm : ‖(fun i => ((y - x) i : ℂ))‖ ≤ ‖y - x‖ := norm_ofReal_pi_le _
    have hdist : ‖y - x‖ < (ρ₂ : ℝ) := by rw [← dist_eq_norm]; exact hy
    have hyball : (fun i => ((y - x) i : ℂ)) ∈ Metric.eball 0 (cplxSeries p).radius := by
      rw [Metric.mem_eball]
      refine lt_of_lt_of_le ?_ hqle
      rw [edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
      exact lt_of_le_of_lt hnorm hdist
    have hyball' : (y - x) ∈ Metric.eball (0 : ι → ℝ) r := by
      rw [Metric.mem_eball]
      calc edist (y - x) 0 = ((‖y - x‖₊ : NNReal) : ENNReal) := by
            rw [edist_zero_right, enorm_eq_nnnorm]
        _ < ((ρ₁ : NNReal) : ENNReal) := by
            rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
            exact lt_of_lt_of_le hdist hρ₂le
        _ ≤ r := hρ₁lt.le
    have hsum1 : HasSum (fun k : ℕ => (cplxSeries p) k (fun _ => fun i => ((y - x) i : ℂ)))
        ((cplxSeries p).sum (fun i => ((y - x) i : ℂ))) :=
      (cplxSeries p).summable hyball |>.hasSum
    have hsum2 : HasSum (fun k : ℕ => p k (fun _ => y - x)) (f (x + (y - x))) :=
      hr.hasSum hyball'
    have hcongr : (fun k : ℕ => (cplxSeries p) k (fun _ => fun i => ((y - x) i : ℂ)))
        = fun k : ℕ => p k (fun _ => y - x) := funext fun k => cplxSeries_diag p k (y - x)
    rw [show (cplxSeries p).sum (fun i => ((y - x) i : ℂ))
        = ∑' k : ℕ, (cplxSeries p) k (fun _ => fun i => ((y - x) i : ℂ)) from rfl, hcongr,
      hsum2.tsum_eq]
    congr 1
    funext i
    simp [Pi.add_apply, Pi.sub_apply]

/-! ## The concrete coordinate maps for `ℂⁿ × ℂ` -/

/-- The index type of the real coordinates of `ℂⁿ × ℂ`.  The `inl`-part indexes the coordinates
of `ℂⁿ`, the `inr`-part the fibre variable; the `Bool` distinguishes the real from the imaginary
part. -/
abbrev CIdx (n : ℕ) := (Fin n ⊕ Unit) × Bool

variable {n : ℕ}

/-- The real coordinates of a point of `ℂⁿ × ℂ`. -/
noncomputable def rcL : ((Fin n → ℂ) × ℂ) →L[ℝ] (CIdx n → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    match k with
    | (Sum.inl i, false) =>
        Complex.reCLM.comp ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ))
    | (Sum.inl i, true) =>
        Complex.imCLM.comp ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ))
    | (Sum.inr _, false) => Complex.reCLM.comp (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ)
    | (Sum.inr _, true) => Complex.imCLM.comp (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ)

@[simp] lemma rcL_inl_false (r : (Fin n → ℂ) × ℂ) (i : Fin n) :
    rcL r (Sum.inl i, false) = (r.1 i).re := rfl

@[simp] lemma rcL_inl_true (r : (Fin n → ℂ) × ℂ) (i : Fin n) :
    rcL r (Sum.inl i, true) = (r.1 i).im := rfl

@[simp] lemma rcL_inr_false (r : (Fin n → ℂ) × ℂ) (u : Unit) :
    rcL r (Sum.inr u, false) = r.2.re := rfl

@[simp] lemma rcL_inr_true (r : (Fin n → ℂ) × ℂ) (u : Unit) :
    rcL r (Sum.inr u, true) = r.2.im := rfl

/-- A point of `ℂⁿ × ℂ` reconstructed from its real coordinates. -/
noncomputable def rcSL : (CIdx n → ℝ) →L[ℝ] ((Fin n → ℂ) × ℂ) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.pi fun i : Fin n =>
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : CIdx n => ℝ) (Sum.inl i, false)))
        + Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : CIdx n => ℝ) (Sum.inl i, true))))
    ((Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : CIdx n => ℝ) (Sum.inr (), false)))
      + Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : CIdx n => ℝ) (Sum.inr (), true))))

@[simp] lemma rcSL_fst (y : CIdx n → ℝ) (i : Fin n) :
    (rcSL y).1 i = (y (Sum.inl i, false) : ℂ) + Complex.I * (y (Sum.inl i, true) : ℂ) := by
  simp [rcSL, smul_eq_mul]

@[simp] lemma rcSL_snd (y : CIdx n → ℝ) :
    (rcSL y).2 = (y (Sum.inr (), false) : ℂ) + Complex.I * (y (Sum.inr (), true) : ℂ) := by
  simp [rcSL, smul_eq_mul]

lemma rcSL_rcL (r : (Fin n → ℂ) × ℂ) : rcSL (rcL r) = r := by
  refine Prod.ext ?_ ?_
  · funext i
    rw [rcSL_fst, rcL_inl_false, rcL_inl_true, mul_comm Complex.I, Complex.re_add_im]
  · rw [rcSL_snd, rcL_inr_false, rcL_inr_true, mul_comm Complex.I, Complex.re_add_im]

lemma norm_rcL_le (r : (Fin n → ℂ) × ℂ) : ‖rcL r‖ ≤ ‖r‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg r)]
  intro k
  obtain ⟨a, b⟩ := k
  rcases a with i | u <;> cases b
  · rw [rcL_inl_false]
    exact le_trans (le_trans
        (by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (r.1 i))
        (norm_le_pi_norm r.1 i)) (le_trans (norm_fst_le r) le_rfl)
  · rw [rcL_inl_true]
    exact le_trans (le_trans
        (by simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (r.1 i))
        (norm_le_pi_norm r.1 i)) (le_trans (norm_fst_le r) le_rfl)
  · rw [rcL_inr_false]
    exact le_trans (by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm r.2)
      (norm_snd_le r)
  · rw [rcL_inr_true]
    exact le_trans (by simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm r.2)
      (norm_snd_le r)

/-- The complexification of the coordinates in which the fibre coordinate is replaced by the
independent variable: `(r.2, ζ) ↦ ((r.2 + ζ)/2, (r.2 - ζ)/(2i))`. -/
noncomputable def sgL : (((Fin n → ℂ) × ℂ) × ℂ) →L[ℝ] (CIdx n → ℂ) :=
  let P : (((Fin n → ℂ) × ℂ) × ℂ) →L[ℝ] (Fin n → ℂ) :=
    (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ).comp
      (ContinuousLinearMap.fst ℝ ((Fin n → ℂ) × ℂ) ℂ)
  let Q : (((Fin n → ℂ) × ℂ) × ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ).comp
      (ContinuousLinearMap.fst ℝ ((Fin n → ℂ) × ℂ) ℂ)
  let R : (((Fin n → ℂ) × ℂ) × ℂ) →L[ℝ] ℂ :=
    ContinuousLinearMap.snd ℝ ((Fin n → ℂ) × ℂ) ℂ
  ContinuousLinearMap.pi fun k =>
    match k with
    | (Sum.inl i, false) => Complex.ofRealCLM.comp (Complex.reCLM.comp
        ((ContinuousLinearMap.proj i).comp P))
    | (Sum.inl i, true) => Complex.ofRealCLM.comp (Complex.imCLM.comp
        ((ContinuousLinearMap.proj i).comp P))
    | (Sum.inr _, false) => (1 / 2 : ℂ) • (Q + R)
    | (Sum.inr _, true) => ((2 * Complex.I)⁻¹ : ℂ) • (Q - R)

@[simp] lemma sgL_inl_false (p : ((Fin n → ℂ) × ℂ) × ℂ) (i : Fin n) :
    sgL p (Sum.inl i, false) = ((p.1.1 i).re : ℂ) := rfl

@[simp] lemma sgL_inl_true (p : ((Fin n → ℂ) × ℂ) × ℂ) (i : Fin n) :
    sgL p (Sum.inl i, true) = ((p.1.1 i).im : ℂ) := rfl

@[simp] lemma sgL_inr_false (p : ((Fin n → ℂ) × ℂ) × ℂ) (u : Unit) :
    sgL p (Sum.inr u, false) = (1 / 2 : ℂ) * (p.1.2 + p.2) := by
  change (1 / 2 : ℂ) • (p.1.2 + p.2) = (1 / 2 : ℂ) * (p.1.2 + p.2)
  rw [smul_eq_mul]

@[simp] lemma sgL_inr_true (p : ((Fin n → ℂ) × ℂ) × ℂ) (u : Unit) :
    sgL p (Sum.inr u, true) = ((2 * Complex.I)⁻¹ : ℂ) * (p.1.2 - p.2) := by
  change ((2 * Complex.I)⁻¹ : ℂ) • (p.1.2 - p.2) = ((2 * Complex.I)⁻¹ : ℂ) * (p.1.2 - p.2)
  rw [smul_eq_mul]

/-- On the antidiagonal `ζ = conj s.2`, the map `sgL` reproduces the real coordinates of `s`. -/
lemma sgL_real (s : (Fin n → ℂ) × ℂ) :
    sgL (s, (starRingEnd ℂ) s.2) = fun k => ((rcL s) k : ℂ) := by
  funext k
  obtain ⟨a, b⟩ := k
  rcases a with i | u <;> cases b
  · rw [sgL_inl_false, rcL_inl_false]
  · rw [sgL_inl_true, rcL_inl_true]
  · rw [sgL_inr_false, rcL_inr_false]
    have h : s.2 + (starRingEnd ℂ) s.2 = ((2 * s.2.re : ℝ) : ℂ) := Complex.add_conj s.2
    rw [h]
    push_cast
    ring
  · rw [sgL_inr_true, rcL_inr_true]
    have h : s.2 - (starRingEnd ℂ) s.2 = ((2 * s.2.im : ℝ) : ℂ) * Complex.I :=
      Complex.sub_conj s.2
    rw [h]
    push_cast
    field_simp
    try ring

/-- Norm bound for `sgL`. -/
lemma norm_sgL_le (p : ((Fin n → ℂ) × ℂ) × ℂ) : ‖sgL p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  obtain ⟨a, b⟩ := k
  rcases a with i | u <;> cases b
  · rw [sgL_inl_false]
    refine le_trans (le_trans
      (by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (p.1.1 i))
      (norm_le_pi_norm p.1.1 i)) ?_
    exact le_trans (norm_fst_le p.1) (le_add_of_nonneg_right (norm_nonneg p.2))
  · rw [sgL_inl_true]
    refine le_trans (le_trans
      (by simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (p.1.1 i))
      (norm_le_pi_norm p.1.1 i)) ?_
    exact le_trans (norm_fst_le p.1) (le_add_of_nonneg_right (norm_nonneg p.2))
  · rw [sgL_inr_false]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    have h3 : ‖p.1.2 + p.2‖ ≤ ‖p.1‖ + ‖p.2‖ :=
      le_trans (norm_add_le _ _) (add_le_add (norm_snd_le p.1) le_rfl)
    rw [norm_mul, h2]
    linarith [norm_nonneg p.1, norm_nonneg p.2]
  · rw [sgL_inr_true]
    have h5 : ‖((2 * Complex.I)⁻¹ : ℂ)‖ = 1 / 2 := by
      rw [norm_inv, norm_mul, Complex.norm_I, mul_one]
      norm_num
    have h6 : ‖p.1.2 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ :=
      le_trans (norm_sub_le _ _) (add_le_add (norm_snd_le p.1) le_rfl)
    rw [norm_mul, h5]
    linarith [norm_nonneg p.1, norm_nonneg p.2]

/-- The `ℂ`-linear part of `sgL` in the fibre direction. -/
noncomputable def sgC (n : ℕ) : (ℂ × ℂ) →L[ℂ] (CIdx n → ℂ) :=
  ContinuousLinearMap.pi fun k =>
    match k with
    | (Sum.inl _, _) => 0
    | (Sum.inr _, false) =>
        (1 / 2 : ℂ) • ((ContinuousLinearMap.fst ℂ ℂ ℂ) + (ContinuousLinearMap.snd ℂ ℂ ℂ))
    | (Sum.inr _, true) =>
        ((2 * Complex.I)⁻¹ : ℂ) • ((ContinuousLinearMap.fst ℂ ℂ ℂ) - (ContinuousLinearMap.snd ℂ ℂ ℂ))

@[simp] lemma sgC_inl (p : ℂ × ℂ) (i : Fin n) (b : Bool) : sgC n p (Sum.inl i, b) = 0 := by
  cases b <;> rfl

@[simp] lemma sgC_inr_false (p : ℂ × ℂ) (u : Unit) :
    sgC n p (Sum.inr u, false) = (1 / 2 : ℂ) * (p.1 + p.2) := by
  change (1 / 2 : ℂ) • (p.1 + p.2) = (1 / 2 : ℂ) * (p.1 + p.2)
  rw [smul_eq_mul]

@[simp] lemma sgC_inr_true (p : ℂ × ℂ) (u : Unit) :
    sgC n p (Sum.inr u, true) = ((2 * Complex.I)⁻¹ : ℂ) * (p.1 - p.2) := by
  change ((2 * Complex.I)⁻¹ : ℂ) • (p.1 - p.2) = ((2 * Complex.I)⁻¹ : ℂ) * (p.1 - p.2)
  rw [smul_eq_mul]

lemma sgC_eq_sgL (p : ℂ × ℂ) : sgC n p = sgL (((0 : Fin n → ℂ), p.1), p.2) := by
  funext k
  obtain ⟨a, b⟩ := k
  rcases a with i | u <;> cases b <;> simp

end Cx

end Work.NN.Core.TelTwoDF

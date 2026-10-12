import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.L1Tails.W1fun_coulomb_le
import Submission.Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul
import Submission.Work.BoseBoxFock.PCFU.chAslotImages_arith
import Submission.Work.BoseBoxFock.PCFU.imgPair_sq_le
import Submission.Work.BoseBoxFock.PCFU.integrable_dirichletSlice_unrestricted
import Submission.Work.BoseBoxFock.PCFU.integral_lowSlot_kcInsN_sq_le
import Submission.Work.BoseBoxFock.PCFU.sum_integral_fderivSq_eq
import Submission.Work.BoseBoxFock.PCFU.taper_pairing_aux
import Submission.Work.BoseBoxFock.PotCubicPoissonAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000

/-! ## Auxiliary facts for `chAslotImages_le`

The state- and parameter-free ingredients of the route: the support of the window, the
`i`-slot invariance of the low slot, the support of `W₁` and the lattice-finiteness of the
images. -/

/-- `chiScale ℓ x ≠ 0` forces `‖x‖ < ℓ/2` (for `0 < ℓ`). -/
lemma chiScale_ne_zero_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have h1 : Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) ≠ 0 := by
    simpa only [Submission.BoseGases.chiScale] using hx
  have h2 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2 := by
    by_contra hcon
    exact h1 (Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div] at h2
  have h3 := (div_lt_iff₀ hℓ).mp h2
  linarith

/-- The low slot of `aQ j (aP i ·)` is independent of the `i`-slot. -/
lemma lowSlot_aQ_aP_update_eq {n : ℕ} {ℓ κ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {Θ : Submission.BoseGases.X n → ℝ}
    (x : Submission.BoseGases.X n) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
        (Function.update x i z) =
      Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x := by
  have hcomm : ∀ u : E3,
      Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
        (Function.update (Function.update x i z) j u) =
      Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u) := by
    intro u
    have h2 : Function.update (Function.update x i z) j u
        = Function.update (Function.update x j u) i z := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp [Function.update, hij]
      · by_cases hk' : k = j
        · subst hk'
          simp [Function.update, hk]
        · simp [Function.update, hk, hk']
    rw [h2, aQ_aP_update_invariant hij (Function.update x j u) z]
  have hj : (Function.update x i z) j = x j := by
    simp [Function.update, Ne.symm hij]
  have hfun : (fun u : E3 => (((Submission.BoseGases.acube ℓ).indicator
        (fun w => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
          (Function.update (Function.update x i z) j w)) u : ℝ) : ℂ))
      = (fun u : E3 => (((Submission.BoseGases.acube ℓ).indicator
        (fun w => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
          (Function.update x j w)) u : ℝ) : ℂ)) := by
    funext u
    by_cases hu : u ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hcomm u]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
  unfold Work.BoseBoxFix.lowSlot Work.BoseBoxFix.lowMult
  rw [hj, hfun]

/-- The mass of `W₁` is concentrated in the ball of radius `R`. -/
lemma W1fun_eq_zero_of_lt_norm {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {y : E3} (hy : R ≤ ‖y‖) :
    Work.BoseFixR.W1fun v h ℓ y = 0 :=
  Work.BoseBoxFock.PCFU.W1fun_eq_zero_of_le_norm' hv_supp hy

/-- **The lattice finiteness of the images.**  A non-vanishing image
`W₁ (z + ℓ • latVec m)` forces `m` into the fixed finite set `latFinSet ℓ (R + ℓ)`, as soon as
`‖z‖ ≤ ℓ`. -/
lemma mem_latFinSet_of_W1_ne_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hℓ : 0 < ℓ)
    {z : E3} (hz : ‖z‖ ≤ ℓ) {m : Fin 3 → ℤ}
    (hm : Work.BoseFixR.W1fun v h ℓ (z + ℓ • Work.BoseBoxFock.latVec m) ≠ 0) :
    m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ) := by
  have h1 : ‖z + ℓ • Work.BoseBoxFock.latVec m‖ < R := by
    by_contra hcon
    exact hm (W1fun_eq_zero_of_lt_norm hv_supp (le_of_not_gt hcon))
  have h2 : ℓ * ‖Work.BoseBoxFock.latVec m‖ = ‖ℓ • Work.BoseBoxFock.latVec m‖ :=
    (Work.BoseBoxFock.LatFourier.latVec_norm_smul ℓ hℓ.le m).symm
  have h3 : ‖ℓ • Work.BoseBoxFock.latVec m‖
      ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := by
    have h := norm_sub_le (z + ℓ • Work.BoseBoxFock.latVec m) z
    simpa using h
  have h4 : ℓ * ‖Work.BoseBoxFock.latVec m‖ ≤ (R + ℓ) + Real.sqrt 3 * ℓ := by
    nlinarith [h1, h2, h3, norm_nonneg z, Real.sqrt_nonneg 3, hℓ]
  rw [Work.BoseBoxFock.LatFourier.mem_latFinSet]
  have h5 : ‖Work.BoseBoxFock.latVec m‖ ≤ ((R + ℓ) + Real.sqrt 3 * ℓ) / ℓ :=
    (le_div_iff₀ hℓ).mpr (by rw [mul_comm]; exact h4)
  linarith

/-- The images of `W₁` against the `m = 0` term form a **finite** lattice sum: the whole
`latPer3 ℓ W₁ − ℓ³W₁` bracket is `ℓ³` times the sum over the fixed finite set
`latFinSet ℓ (R + ℓ)`, with the `m = 0` term removed. -/
lemma latPer3_sub_eq_sum {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR0 : 0 ≤ R) (hℓ : 0 < ℓ)
    {z : E3} (hz : ‖z‖ ≤ ℓ) :
    Work.BoseBoxFock.latPer3 ℓ (Work.BoseFixR.W1fun v h ℓ) z
        - ((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseFixR.W1fun v h ℓ z : ℝ) : ℂ)
      = ((ℓ ^ 3 : ℝ) : ℂ)
          * ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ),
              (if m = 0 then (0 : ℂ)
                else ((Work.BoseFixR.W1fun v h ℓ (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) := by
  have hsum : Work.BoseBoxFock.LatFourier.latPer ℓ (Work.BoseFixR.W1fun v h ℓ) z
      = ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ),
          ((Work.BoseFixR.W1fun v h ℓ (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
    rw [Work.BoseBoxFock.LatFourier.latPer]
    refine tsum_eq_sum (s := Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ))
      (fun m hm => ?_)
    by_cases hW : Work.BoseFixR.W1fun v h ℓ (z + ℓ • Work.BoseBoxFock.latVec m) = 0
    · rw [hW, Complex.ofReal_zero]
    · exact absurd (mem_latFinSet_of_W1_ne_zero hv_supp hℓ hz hW) hm
  have h0 : (0 : Fin 3 → ℤ) ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ) := by
    rw [Work.BoseBoxFock.LatFourier.mem_latFinSet]
    have hz0 : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
      ext i
      simp [Work.BoseBoxFock.latVec]
    rw [hz0, norm_zero]
    exact div_nonneg (by nlinarith [Real.sqrt_nonneg 3, hR0, hℓ.le]) hℓ.le
  rw [Work.BoseBoxFock.latPer3, hsum, ← mul_sub]
  congr 1
  have h2 : (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ),
        (if m = 0 then ((Work.BoseFixR.W1fun v h ℓ z : ℝ) : ℂ) else 0))
      = ((Work.BoseFixR.W1fun v h ℓ z : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single (0 : Fin 3 → ℤ)]
    · simp
    · intro m _ hm0
      rw [if_neg hm0]
    · intro h
      exact absurd h0 h
  rw [← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hm0 : m = 0
  · subst hm0
    have hz0 : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
      ext i
      simp [Work.BoseBoxFock.latVec]
    simp [hz0]
  · rw [if_neg hm0, if_neg hm0, sub_zero]

/-- A nonzero lattice vector has norm at least `1`. -/
lemma one_le_norm_latVec {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖Work.BoseBoxFock.latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    exact hm (funext (fun i => by simpa using not_not.mp (not_exists.mp h i)))
  have h1 : ‖(Work.BoseBoxFock.latVec m).ofLp i‖ ≤ ‖Work.BoseBoxFock.latVec m‖ :=
    PiLp.norm_apply_le (Work.BoseBoxFock.latVec m) i
  rw [Work.BoseBoxFock.latVec_apply, Real.norm_eq_abs] at h1
  have h2 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
    have h3 : (0 : ℤ) < |m i| := abs_pos.mpr hi
    have h4 : (1 : ℤ) ≤ |m i| := by omega
    exact_mod_cast h4
  linarith

/-- **The image pairing** `P_m(x) = ∫_y χ_ℓ(y)·W₁(x j − y + ℓ•latVec m)·Θ(update x i y) dy`
(the `y`-integral of one lattice image against the state, with the `i`-th slot as the
integration variable). -/
noncomputable def imgPair (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc : Work.BoseBoxFix.LowCut)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (μ : ℝ) (i j : Fin n) (m : Fin 3 → ℤ) (x : Submission.BoseGases.X n) : ℂ :=
  ∫ y : E3,
    ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
      * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
            (x j - y + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)
      * ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ
            (Function.update x i y) : ℝ) : ℂ)

/-- **The lattice-image substitution** `u = x + z − y`: the image `W (x + z − y)` against an
arbitrary profile `f (y)` pairs with `W (u)` against `f (x + z − u)`.  (One line from
`MeasureTheory.integral_sub_left_eq_self`.) -/
lemma integral_img_subst {f : E3 → ℂ} {W : E3 → ℝ} (x z : E3) :
    (∫ y : E3, ((W (x + z - y) : ℝ) : ℂ) * f y)
      = ∫ u : E3, ((W u : ℝ) : ℂ) * f (x + z - u) := by
  have h := MeasureTheory.integral_sub_left_eq_self
    (fun u : E3 => ((W u : ℝ) : ℂ) * f (x + z - u)) volume (x + z)
  simpa using h

/-- **The face-layer gap at the pairing.**  If the outer window `χ_ℓ(x j)` is *large* (larger
than the aliasing-flatness bound `ε = Cg(R/ℓ)^N`), then the image pairing `imgPair` vanishes
identically: every `y` that could contribute violates the aliasing geometry.  Hence
`χ_ℓ(x j)·‖imgPair‖ ≤ ε·‖imgPair‖`. -/
lemma chi_mul_imgPair_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR0 : 0 ≤ R)
    {ε : ℝ} (hε0 : 0 ≤ ε) {Cg : ℝ} {N : ℕ}
    (hCg : ∀ {ℓ ρ : ℝ}, 0 < ℓ → 0 ≤ ρ → ∀ {vv : E3}, 1 ≤ ‖vv‖ →
      ∀ {y u : E3}, ‖y‖ ≤ ℓ / 2 → ‖u‖ ≤ ℓ / 2 → ‖y - u + ℓ • vv‖ ≤ ρ →
        Submission.BoseGases.chiScale ℓ y ≤ Cg * (ρ / ℓ) ^ N)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {μ : ℝ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ) (hε : ε = Cg * (R / Work.BoseBoxFock.ellH v μ) ^ N)
    (fc : Work.BoseBoxFix.LowCut) {n : ℕ} {i j : Fin n} {Φ : Submission.BoseGases.X n → ℝ}
    {m : Fin 3 → ℤ} (hm : m ≠ 0) (x : Submission.BoseGases.X n) :
    Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j)
        * ‖imgPair v h fc Φ μ i j m x‖
      ≤ ε * ‖imgPair v h fc Φ μ i j m x‖ := by
  by_cases hsmall : Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) ≤ ε
  · exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  · have hgt : ε < Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) :=
      lt_of_not_ge hsmall
    have hpos : 0 < Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) :=
      lt_of_le_of_lt hε0 hgt
    have hχj : Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) ≠ 0 :=
      ne_of_gt hpos
    have hnorm : ‖x j‖ < Work.BoseBoxFock.ellH v μ / 2 :=
      chiScale_ne_zero_norm_lt hℓ hχj
    have hzero : ∀ y : E3,
        ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
          * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
                (x j - y + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ
                (Function.update x i y) : ℝ) : ℂ) = 0 := by
      intro y
      by_cases hy : Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) y = 0
      · rw [hy, Complex.ofReal_zero, zero_mul, zero_mul]
      · by_cases hw : Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
            (x j - y + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m) = 0
        · rw [hw, Complex.ofReal_zero, mul_zero, zero_mul]
        · exfalso
          have hy' : ‖y‖ < Work.BoseBoxFock.ellH v μ / 2 :=
            chiScale_ne_zero_norm_lt hℓ hy
          have hw' : ‖x j - y + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec m‖ ≤ R := by
            by_contra hcon
            exact hw (W1fun_eq_zero_of_lt_norm hv_supp (le_of_lt (lt_of_not_ge hcon)))
          have hgap := hCg (ℓ := Work.BoseBoxFock.ellH v μ) (ρ := R) hℓ hR0
            (vv := Work.BoseBoxFock.latVec m) (one_le_norm_latVec hm) (y := x j) (u := y)
            hnorm.le hy'.le hw'
          rw [hε] at hgt
          linarith
    have hP : imgPair v h fc Φ μ i j m x = 0 := by
      unfold imgPair
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards with y
      exact hzero y
    rw [hP, norm_zero, mul_zero, mul_zero]

/-- **The `i`-slot peel** on the full configuration space: integrating over `X (n+1)` is the
same as integrating over the `i`-th coordinate and the remaining ones.  (The measure-preserving
equivalence is `kcInsN`, and the two sides are Fubini.) -/
lemma integral_peel_i {n : ℕ} (i : Fin (n + 1)) {F : Submission.BoseGases.X (n + 1) → ℂ}
    (hF : MeasureTheory.Integrable F volume) :
    (∫ x : Submission.BoseGases.X (n + 1), F x)
      = ∫ r : Submission.BoseGases.X n, ∫ y : E3, F (Submission.BoseGases.kcInsN n i (y, r)) := by
  have hmp := Submission.BoseGases.kc_mp_insN n i
  have hsym : (∫ p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n,
        F (Submission.BoseGases.kcInsN n i p))
      = ∫ r : Submission.BoseGases.X n,
          ∫ y : Submission.BoseGases.kcE3, F (Submission.BoseGases.kcInsN n i (y, r)) := by
    have h2 := MeasureTheory.integral_prod_symm
      (f := fun p : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
        F (Submission.BoseGases.kcInsN n i p))
      ((hmp.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF)
    exact h2
  rw [← hsym]
  exact (hmp.integral_comp' F).symm

/-- The complex-coerced pointwise integrand of the target. -/
noncomputable def chAimgInt {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (i j : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n → ℂ :=
  fun x =>
    ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x : ℝ) : ℂ)
      * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
      * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
      * (Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i)
          - ((Work.BoseBoxFock.ellH v μ) ^ 3 : ℂ)
              * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (x j - x i) : ℝ) : ℂ))
      * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
            (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ))) x : ℝ) : ℂ)

@[simp] lemma chAimgInt_apply {n : ℕ} {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {i j : Fin n}
    {Φ : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n) :
    chAimgInt v h fc μ i j Φ x
      = ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ x : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
        * (Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i)
            - ((Work.BoseBoxFock.ellH v μ) ^ 3 : ℂ)
                * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (x j - x i) : ℝ) : ℂ))
        * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
              (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                  (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ))) x : ℝ) : ℂ) := rfl

/-- **The windowed finite-lattice expansion.**  Multiplying the `latPer3 − ℓ³W₁` bracket by the
two windows makes it the finite `latFinSet ℓ (R+ℓ)`-sum with the `m = 0` term removed: outside
the support of the windows both sides vanish, and inside it the aliasing constraint
`‖b − a‖ < ℓ` holds, which is the hypothesis of `latPer3_sub_eq_sum`. -/
private lemma chiChi_mul_latPer3_sub {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR0 : 0 ≤ R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (a b : E3) :
    ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (Work.BoseBoxFock.latPer3 ℓ (Work.BoseFixR.W1fun v h ℓ) (b - a)
            - ((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseFixR.W1fun v h ℓ (b - a) : ℝ) : ℂ))
      = ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (((ℓ ^ 3 : ℝ) : ℂ)
          * ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ),
              (if m = 0 then (0 : ℂ)
                else ((Work.BoseFixR.W1fun v h ℓ (b - a + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))) := by
  by_cases h : Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.chiScale ℓ b = 0
  · have hz : ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_mul, h, Complex.ofReal_zero]
    rw [hz, zero_mul, zero_mul]
  · have ha : Submission.BoseGases.chiScale ℓ a ≠ 0 := fun hz => h (by rw [hz, zero_mul])
    have hb : Submission.BoseGases.chiScale ℓ b ≠ 0 := fun hz => h (by rw [hz, mul_zero])
    have hna : ‖a‖ < ℓ / 2 := chiScale_ne_zero_norm_lt hℓ ha
    have hnb : ‖b‖ < ℓ / 2 := chiScale_ne_zero_norm_lt hℓ hb
    have hz : ‖b - a‖ ≤ ℓ := by
      have := norm_sub_le b a
      linarith
    rw [latPer3_sub_eq_sum hv_supp hR0 hℓ hz]

/-- The index set of the images has at most `343 = 7³` elements: in the range `‖z‖ ≤ ℓ` only
lattice vectors of norm `≤ R/ℓ + 1 + √3 ≤ 3.25` contribute, so every coordinate lies in
`{-3,…,3}`. -/
private lemma latFinSet_card_le_343 {R ℓ : ℝ} (hR : 0 < R) (h2R : 2 * R ≤ ℓ) :
    (Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ)).card ≤ 343 := by
  have hℓ : 0 < ℓ := by linarith
  have hsub : Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ)
      ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-3) 3) := by
    intro m hm
    rw [Work.BoseBoxFock.LatFourier.mem_latFinSet] at hm
    rw [Fintype.mem_piFinset]
    intro i
    have h1 : |((m i : ℤ) : ℝ)| ≤ ((R + ℓ) + Real.sqrt 3 * ℓ) / ℓ :=
      le_trans (Work.BoseBoxFock.LatFourier.abs_coord_le_norm_latVec m i) hm
    have h2 : ((R + ℓ) + Real.sqrt 3 * ℓ) / ℓ ≤ 13 / 4 := by
      have hs3 : Real.sqrt 3 < 7 / 4 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      rw [div_le_iff₀ hℓ]
      nlinarith [h2R, hs3]
    have h3 : |((m i : ℤ) : ℝ)| ≤ 13 / 4 := le_trans h1 h2
    have hup : ((m i : ℤ) : ℝ) ≤ 13 / 4 := (abs_le.mp h3).2
    have hlo : -(13 / 4 : ℝ) ≤ ((m i : ℤ) : ℝ) := (abs_le.mp h3).1
    have hle : m i ≤ 3 := by
      by_contra hc
      push_neg at hc
      have h4 : (4 : ℤ) ≤ m i := by omega
      have h4r : (4 : ℝ) ≤ ((m i : ℤ) : ℝ) := by exact_mod_cast h4
      linarith
    have hge : -(3 : ℤ) ≤ m i := by
      by_contra hc
      push_neg at hc
      have h4 : m i ≤ -4 := by omega
      have h4r : ((m i : ℤ) : ℝ) ≤ -4 := by exact_mod_cast h4
      linarith
    exact Finset.mem_Icc.mpr ⟨hge, hle⟩
  calc (Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ)).card
      ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-3) 3)).card :=
        Finset.card_le_card hsub
    _ = 343 := by simp [Fintype.card_piFinset]

theorem chAslotImages_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) {J ε₀ : ℝ} (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 ∧
        2 * R ≤ Work.BoseBoxFock.ellH v μ) →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ (i j : Fin n), i ≠ j → ∀ D : ℝ,
          (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) z *
                  (Φ : Submission.BoseGases.X n → ℝ) (Function.update x i z)) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) ≤ D) →
          ‖∫ x : Submission.BoseGases.X n,
              ((Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                      (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i)
                    - ((Work.BoseBoxFock.ellH v μ) ^ 3 : ℂ)
                        * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (x j - x i) : ℝ) : ℂ))
                * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
                            (Φ : Submission.BoseGases.X n → ℝ)))) x : ℝ) : ℂ)‖
            ≤ C * (R / Work.BoseBoxFock.ellH v μ) ^ (2 * M) * Real.sqrt Submission.BoseGases.chiSup
                * Real.sqrt (BoseGases.a v) * (Work.BoseBoxFock.ellH v μ) ^ 3
                * Real.sqrt (Work.BoseBoxFock.ellH v μ) * Real.sqrt D
                * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) := by
  classical
  -- the face-layer constant at the doubled exponent `2 * M`
  obtain ⟨Cg, hCgnn, hCg⟩ := Work.BoseBoxFock.chi_le_of_alias (2 * M)
  refine ⟨343 * Cg * 16 * Real.sqrt Real.pi
      / (Real.sqrt Submission.BoseGases.chiSup * (4 * R ^ 2)) + 1, ?_, ?_⟩
  · positivity
  · intro μ hAdm hreg hKB n Φ hn hnorm hlow i j hij D hD
    cases n with
    | zero => exact absurd (Subsingleton.elim i j) hij
    | succ m =>
    obtain ⟨j', hj'⟩ := (Fin.exists_succAbove_eq_iff (x := i) (y := j)).mpr hij.symm
    let ℓ : ℝ := Work.BoseBoxFock.ellH v μ
    have hℓ : 0 < ℓ := Work.BoseBoxFock.ellH_pos v μ
    have hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0 := hreg.1
    have h2Rℓ : 2 * R ≤ ℓ := hreg.2
    have hR0 : 0 ≤ R := hR.le
    change ‖∫ x : Submission.BoseGases.X (m + 1),
        chAimgInt v h fc μ i j (Φ : Submission.BoseGases.X (m + 1) → ℝ) x‖ ≤
      (343 * Cg * 16 * Real.sqrt Real.pi
          / (Real.sqrt Submission.BoseGases.chiSup * (4 * R ^ 2)) + 1)
        * (R / ℓ) ^ (2 * M) * Real.sqrt Submission.BoseGases.chiSup
        * Real.sqrt (BoseGases.a v) * ℓ ^ 3 * Real.sqrt ℓ * Real.sqrt D
        * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ)
    -- ### the abbreviations
    let ε : ℝ := Cg * (R / ℓ) ^ (2 * M)
    let W : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ
    let Θ : Submission.BoseGases.X (m + 1) → ℝ :=
      Work.BoseBoxFock.boxRestrictR ℓ (Φ : Submission.BoseGases.X (m + 1) → ℝ)
    let Γ : Submission.BoseGases.X (m + 1) → ℝ :=
      Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ) ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
    let S : Finset (Fin 3 → ℤ) := Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ℓ)
    let F : Submission.BoseGases.X (m + 1) → ℂ :=
      chAimgInt v h fc μ i j (Φ : Submission.BoseGases.X (m + 1) → ℝ)
    let G : Submission.BoseGases.X (m + 1) → ℂ := fun x =>
      ((Θ x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
        * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S,
            (if mm = 0 then (0 : ℂ) else ((W (x j - x i + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
        * ((Γ x : ℝ) : ℂ)
    -- ### nonnegativity of the constant factors
    have hε0 : 0 ≤ ε := by
      rw [show ε = Cg * (R / ℓ) ^ (2 * M) from rfl]
      exact mul_nonneg hCgnn (pow_nonneg (le_of_lt (div_pos hR hℓ)) _)
    have hcc0 : 0 ≤ ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)) :=
      mul_nonneg (mul_nonneg (by positivity) hε0) (by positivity)
    -- ### `F` and `G` agree pointwise (the finite lattice expansion)
    have hFG : ∀ x, F x = G x := by
      intro x
      have key := chiChi_mul_latPer3_sub (v := v) (h := h) (R := R) (ℓ := ℓ) hR0 hℓ hv_supp (x i) (x j)
      have hℓeq : Work.BoseBoxFock.ellH v μ = ℓ := rfl
      calc F x
          = ((Θ x : ℝ) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
                * (Work.BoseBoxFock.latPer3 ℓ W (x j - x i)
                    - ((ℓ ^ 3 : ℝ) : ℂ) * ((W (x j - x i) : ℝ) : ℂ)))
              * ((Γ x : ℝ) : ℂ) := by
            simp only [F, chAimgInt_apply, Θ, Γ, W, hℓeq]
            push_cast
            ring
        _ = ((Θ x : ℝ) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)
                * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S,
                    (if mm = 0 then (0 : ℂ)
                      else ((W (x j - x i + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ))))
              * ((Γ x : ℝ) : ℂ) := by
            rw [key]
        _ = G x := by
            simp only [G]
            ring
    have hFGint : (∫ x : Submission.BoseGases.X (m + 1),
          chAimgInt v h fc μ i j (Φ : Submission.BoseGases.X (m + 1) → ℝ) x)
        = ∫ x : Submission.BoseGases.X (m + 1), G x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact hFG x
    rw [hFGint]
    by_cases hGint : MeasureTheory.Integrable G volume
    · -- ================= main branch =================
      let Γ' : Submission.BoseGases.X m → ℝ :=
        fun r => Γ (Submission.BoseGases.kcInsN m i ((0 : E3), r))
      let Z : (Fin 3 → ℤ) → Submission.BoseGases.X m → ℂ := fun mm r =>
        imgPair v h fc Φ μ i j mm (Submission.BoseGases.kcInsN m i ((0 : E3), r))
      let E : Submission.BoseGases.X m → ℝ := fun r =>
        ∫ y : E3, ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
            Submission.BoseGases.chiScale ℓ z
              * (Φ : Submission.BoseGases.X (m + 1) → ℝ)
                  (Submission.BoseGases.kcInsN m i (z, r))) y
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
      let Jr : Submission.BoseGases.X m → ℂ :=
        fun r => ∫ y : E3, G (Submission.BoseGases.kcInsN m i (y, r))
      have hΦc : Continuous (Φ : Submission.BoseGases.X (m + 1) → ℝ) := Φ.contDiff.continuous
      obtain ⟨hΘm, Cθ, hCθ0, hΘb⟩ :=
        Work.BoseBoxFock.boxRestrictR_measurable_bounded (ℓ := ℓ) hℓ hΦc
      -- ### Γ is invariant under changing the `i`-slot
      have hΓinv : ∀ (y : E3) (r : Submission.BoseGases.X m),
          Γ (Submission.BoseGases.kcInsN m i (y, r)) = Γ' r := by
        intro y r
        rw [Submission.BoseGases.kcInsN_update_zero]
        exact lowSlot_aQ_aP_update_eq (n := m + 1) (ℓ := ℓ)
          (κ := Work.BoseBoxFock.PCFU.chKappa v μ) (i := i) (j := j) hij fc
          (Submission.BoseGases.kcInsN m i ((0 : E3), r)) y
      -- ### the `j`-slot of an insertion
      have hjslot : ∀ (y : E3) (r : Submission.BoseGases.X m),
          (Submission.BoseGases.kcInsN m i (y, r)) j = r j' := by
        intro y r
        rw [← hj']
        exact Submission.BoseGases.kc_insN_apply_succ m i y r j'
      -- ### the pointwise expansion along `kcInsN`
      have hpt : ∀ (y : E3) (r : Submission.BoseGases.X m),
          G (Submission.BoseGases.kcInsN m i (y, r))
            = ((Γ' r : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)
              * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S,
                  (if mm = 0 then (0 : ℂ) else
                    ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                      * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                      * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ))) := by
        intro y r
        have h1 : (Submission.BoseGases.kcInsN m i (y, r)) i = y :=
          Submission.BoseGases.kc_insN_apply_same m i y r
        have h3 : ((Γ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
            = ((Γ' r : ℝ) : ℂ) := by rw [hΓinv y r]
        have hsum : ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
              * ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else
                  ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ))
            = ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else
                ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                  * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                  * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun mm _ => ?_)
          by_cases h0 : mm = 0
          · simp [h0]
          · simp only [if_neg h0]
        simp only [G, h1, hjslot y r, h3]
        rw [show ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)
              * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else
                  ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
              * ((Γ' r : ℝ) : ℂ)
            = ((Γ' r : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)
              * (((ℓ ^ 3 : ℝ) : ℂ) * (((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                  * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                  * ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else
                      ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))) from by ring]
        rw [hsum]
      -- ### the per-`mm` integrability in `y`
      have hWrefl : ∀ u : E3, MeasureTheory.Integrable
          (fun y : E3 => Work.BoseFixR.W1fun v h ℓ (u - y)) MeasureTheory.volume :=
        fun u => (Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ).comp_sub_left u
      have hWrefl' : ∀ u w : E3, MeasureTheory.Integrable
          (fun y : E3 => Work.BoseFixR.W1fun v h ℓ (u - y + w)) MeasureTheory.volume := by
        intro u w
        refine (hWrefl (u + w)).congr ?_
        filter_upwards with y
        exact congrArg (fun z : E3 => Work.BoseFixR.W1fun v h ℓ z)
          (show (u + w) - y = u - y + w from by abel)
      have hchiSup0 : 0 ≤ Submission.BoseGases.chiSup :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hchi_le : ∀ z : E3, Submission.BoseGases.chiScale ℓ z ≤ Submission.BoseGases.chiSup :=
        fun z => Submission.BoseGases.chi_le_sqrt_inv _
      have hInt : ∀ (mm : Fin 3 → ℤ) (r : Submission.BoseGases.X m),
          MeasureTheory.Integrable (fun y : E3 => (if mm = 0 then (0 : ℂ) else
            ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
              * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
          MeasureTheory.volume := by
        intro mm r
        by_cases h0 : mm = 0
        · rw [show (fun y : E3 => (if mm = 0 then (0 : ℂ) else
              ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
              = fun _ : E3 => (0 : ℂ) from by funext y; rw [if_pos h0]]
          exact integrable_zero E3 ℂ MeasureTheory.volume
        · rw [show (fun y : E3 => (if mm = 0 then (0 : ℂ) else
              ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
              = fun y : E3 => ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)
              from by funext y; rw [if_neg h0]]
          have hWr := hWrefl' (r j') (ℓ • Work.BoseBoxFock.latVec mm)
          refine MeasureTheory.Integrable.mono'
            (g := fun y : E3 => (Cθ * Submission.BoseGases.chiSup)
              * |Work.BoseFixR.W1fun v h ℓ (r j' - y + ℓ • Work.BoseBoxFock.latVec mm)|)
            (hWr.norm.const_mul _) ?_ ?_
          · have ha1 : AEMeasurable (fun y : E3 =>
                ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)) MeasureTheory.volume :=
              Complex.continuous_ofReal.measurable.comp_aemeasurable
                (hΘm.comp_aemeasurable
                  (by fun_prop : Measurable fun y : E3 =>
                    Submission.BoseGases.kcInsN m i (y, r)).aemeasurable)
            have ha2 : AEMeasurable (fun y : E3 =>
                ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) MeasureTheory.volume :=
              Complex.continuous_ofReal.measurable.comp_aemeasurable
                (Submission.BoseGases.chiScale_contDiff hℓ.ne').continuous.measurable.aemeasurable
            have ha3 : AEMeasurable (fun y : E3 =>
                ((Work.BoseFixR.W1fun v h ℓ
                  (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)) MeasureTheory.volume :=
              Complex.continuous_ofReal.measurable.comp_aemeasurable hWr.aemeasurable
            exact ((ha1.mul ha2).mul ha3).aestronglyMeasurable
          · filter_upwards with y
            have hχy : (0 : ℝ) ≤ Submission.BoseGases.chiScale ℓ y :=
              Submission.BoseGases.chi_nonneg ((ℓ⁻¹ : ℝ) • y)
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hχy]
            exact mul_le_mul
              (mul_le_mul (hΘb _) (hchi_le y) hχy hCθ0)
              le_rfl (abs_nonneg _) (mul_nonneg hCθ0 hchiSup0)
      -- ### the inner integral, evaluated
      have hJr : ∀ r : Submission.BoseGases.X m,
          Jr r = ((Γ' r : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)
            * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else Z mm r)) := by
        intro r
        rw [show Jr r = ∫ y : E3, G (Submission.BoseGases.kcInsN m i (y, r)) from rfl]
        rw [show (∫ y : E3, G (Submission.BoseGases.kcInsN m i (y, r)))
            = ∫ y : E3, ((Γ' r : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)
                * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else
                    ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                      * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                      * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
            from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => hpt y r))]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        congr 1
        congr 1
        rw [show (∫ y : E3, ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else
              ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)))
            = ∑ mm ∈ S, ∫ y : E3, (if mm = 0 then (0 : ℂ) else
                ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)
                  * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                  * ((W (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ))
            from MeasureTheory.integral_finset_sum S (fun mm _ => hInt mm r)]
        refine Finset.sum_congr rfl (fun mm _ => ?_)
        by_cases h0 : mm = 0
        · simp [h0]
        · simp only [if_neg h0]
          rw [show Z mm r = ∫ y : E3,
              ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((Work.BoseFixR.W1fun v h ℓ
                    (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)
                * ((Θ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ) from ?_]
          · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
          · rw [show Z mm r = imgPair v h fc Φ μ i j mm
                (Submission.BoseGases.kcInsN m i ((0 : E3), r)) from rfl]
            rw [imgPair]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
            beta_reduce
            rw [show (Submission.BoseGases.kcInsN m i ((0 : E3), r)) j = r j' from hjslot _ r]
            rw [← Submission.BoseGases.kcInsN_update_zero]
      -- ### the face-layer gap at the pairing
      have hgap : ∀ r : Submission.BoseGases.X m,
          Submission.BoseGases.chiScale ℓ (r j')
              * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖)
            ≤ ε * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) := by
        intro r
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun mm _ => ?_)
        by_cases h0 : mm = 0
        · simp [h0]
        · simp only [if_neg h0]
          have hle : Submission.BoseGases.chiScale ℓ (Submission.BoseGases.kcInsN m i ((0 : E3), r) j)
                * ‖imgPair v h fc Φ μ i j mm (Submission.BoseGases.kcInsN m i ((0 : E3), r))‖
              ≤ ε * ‖imgPair v h fc Φ μ i j mm (Submission.BoseGases.kcInsN m i ((0 : E3), r))‖ :=
            chi_mul_imgPair_le (v := v) (h := h) (R := R) (μ := μ) (n := m + 1)
              (i := i) (j := j) (Φ := (Φ : Submission.BoseGases.X (m + 1) → ℝ))
              hR0 (by positivity : 0 ≤ ε)
              (fun {ℓ'} {ρ} hℓ' hρ {vv} hv1 {y u} hy hu halias =>
                (hCg hℓ' hρ hv1 hy hu halias).1)
              hv_supp hℓ (hε := rfl) fc (m := mm) h0 _
          rw [show (Submission.BoseGases.kcInsN m i ((0 : E3), r)) j = r j' from hjslot _ r]
              at hle
          rwa [show Z mm r = imgPair v h fc Φ μ i j mm
                (Submission.BoseGases.kcInsN m i ((0 : E3), r)) from rfl]
      have hJrB : ∀ r : Submission.BoseGases.X m,
          ‖Jr r‖ ≤ (ℓ ^ 3) * ε * |Γ' r|
            * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) := by
        intro r
        have hχnn : 0 ≤ Submission.BoseGases.chiScale ℓ (r j') :=
          Submission.BoseGases.chi_nonneg _
        have h4 : ‖∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else Z mm r)‖
            ≤ ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) :=
          le_trans (norm_sum_le S _)
            (Finset.sum_le_sum (fun mm _ => by by_cases h0 : mm = 0 <;> simp [h0]))
        have hA : ‖((Γ' r : ℝ) : ℂ)‖ = |Γ' r| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hB : ‖((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)‖
            = Submission.BoseGases.chiScale ℓ (r j') := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχnn]
        have hC : ‖(((ℓ ^ 3 : ℝ) : ℂ))‖ = ℓ ^ 3 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hJr r]
        calc ‖((Γ' r : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (r j') : ℝ) : ℂ)
              * (((ℓ ^ 3 : ℝ) : ℂ) * ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else Z mm r))‖
            = (|Γ' r| * Submission.BoseGases.chiScale ℓ (r j'))
              * (ℓ ^ 3 * ‖∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else Z mm r)‖) := by
              rw [norm_mul, norm_mul, norm_mul, hA, hB, hC]
          _ ≤ (|Γ' r| * Submission.BoseGases.chiScale ℓ (r j'))
              * (ℓ ^ 3 * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h4 (by positivity))
                (mul_nonneg (abs_nonneg _) hχnn)
          _ ≤ (ℓ ^ 3) * ε * |Γ' r| * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) := by
              rw [show |Γ' r| * Submission.BoseGases.chiScale ℓ (r j')
                    * (ℓ ^ 3 * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖))
                  = ℓ ^ 3 * |Γ' r| * (Submission.BoseGases.chiScale ℓ (r j')
                      * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖)) from by ring]
              rw [show ℓ ^ 3 * ε * |Γ' r|
                    * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖)
                  = ℓ ^ 3 * |Γ' r| * (ε * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖))
                  from by ring]
              exact mul_le_mul_of_nonneg_left (hgap r) (mul_nonneg (by positivity) (abs_nonneg _))
      -- ########## the peel, the `L²` inputs and the final chain ##########
      have hpeel : (∫ x : Submission.BoseGases.X (m + 1), G x)
          = ∫ r : Submission.BoseGases.X m, Jr r :=
        integral_peel_i (n := m) i hGint
      have hEmb : MeasurableEmbedding (Submission.BoseGases.kcInsN m i) :=
        (Submission.BoseGases.kcInsN m i).measurableEmbedding
      have hFpeel : MeasureTheory.Integrable
          (fun p : E3 × Submission.BoseGases.X m => G (Submission.BoseGases.kcInsN m i p))
          ((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume) :=
        ((Submission.BoseGases.kc_mp_insN m i).integrable_comp_emb hEmb).mpr hGint
      have hJrInt : MeasureTheory.Integrable Jr MeasureTheory.volume := hFpeel.integral_prod_right
      -- `Z` vanishes off the box, hence so does `Σ'`
      have hZzero : ∀ (mm : Fin 3 → ℤ) (r : Submission.BoseGases.X m),
          r ∉ Submission.BoseGases.abox m ℓ → Z mm r = 0 := by
        intro mm r hr
        rw [show Z mm r = imgPair v h fc Φ μ i j mm
              (Submission.BoseGases.kcInsN m i ((0 : E3), r)) from rfl]
        rw [imgPair]
        refine MeasureTheory.integral_eq_zero_of_ae ?_
        filter_upwards with y
        rw [Pi.zero_apply]
        beta_reduce
        by_cases hy : Submission.BoseGases.chiScale ℓ y = 0
        · rw [hy, Complex.ofReal_zero, zero_mul, zero_mul]
        · have hnot : Submission.BoseGases.kcInsN m i (y, r)
              ∉ Submission.BoseGases.abox (m + 1) ℓ := by
            intro hmem
            exact hr (fun l => by
              have := hmem (i.succAbove l)
              rwa [Submission.BoseGases.kc_insN_apply_succ] at this)
          have hΘ0 : Work.BoseBoxFock.boxRestrictR ℓ (Φ : Submission.BoseGases.X (m + 1) → ℝ)
              (Submission.BoseGases.kcInsN m i (y, r)) = 0 := by
            simp only [Work.BoseBoxFock.boxRestrictR, Set.indicator_of_notMem hnot, mul_zero]
          rw [← Submission.BoseGases.kcInsN_update_zero, hΘ0, Complex.ofReal_zero, mul_zero]
      have hS0 : ∀ r : Submission.BoseGases.X m, r ∉ Submission.BoseGases.abox m ℓ →
          ∑ mm ∈ S, (if mm = 0 then (0 : ℂ) else Z mm r) = 0 := by
        intro r hr
        refine Finset.sum_eq_zero (fun mm _ => ?_)
        by_cases h0 : mm = 0
        · simp [h0]
        · simp only [if_neg h0]
          exact hZzero mm r hr
      have hS0' : ∀ r : Submission.BoseGases.X m, r ∉ Submission.BoseGases.abox m ℓ →
          ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) = 0 := by
        intro r hr
        refine Finset.sum_eq_zero (fun mm _ => ?_)
        by_cases h0 : mm = 0
        · simp [h0]
        · simp only [if_neg h0, norm_eq_zero]
          exact hZzero mm r hr
      have hJr0 : ∀ r : Submission.BoseGases.X m,
          r ∉ Submission.BoseGases.abox m ℓ → Jr r = 0 := by
        intro r hr
        rw [hJr r, hS0 r hr, mul_zero, mul_zero]
      -- ### the low-slot measurability (needed for the product bound below)
      have hκ : 0 < chKappa v μ := chKappa_pos v hAdm.1 hav
      have hΓm : Measurable Γ := by
        obtain ⟨h1, -⟩ := lowSlot_aQ_aP_measurable_bounded (n := m + 1) (fc := fc) (μ := μ)
          (ℓ := ℓ) (κ := chKappa v μ) (Cθ := Cθ) (i := i) (j := j) (Θ := Θ)
          hℓ hκ hCθ0 hΘm hΘb
        exact h1
      have hΓ'm : Measurable Γ' := by
        have hmap : Measurable (fun r : Submission.BoseGases.X m => ((0 : E3), r)) := by fun_prop
        exact hΓm.comp ((Submission.BoseGases.kcInsN m i).measurable.comp hmap)
      have hE0 : ∀ r : Submission.BoseGases.X m, 0 ≤ E r := fun r =>
        integral_nonneg (fun y => Finset.sum_nonneg (fun k _ => sq_nonneg _))
      -- ### the face-layer sum bound: the per-image duality bound + the cardinality bound
      have hZbound : ∀ r : Submission.BoseGases.X m,
          ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖)
            ≤ 343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v) * Real.sqrt (E r) := by
        intro r
        by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
        · set cw : ℝ := 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v) * Real.sqrt (E r)
            with hcw
          have hcw0 : 0 ≤ cw := by rw [hcw]; positivity
          have hterm : ∀ mm : Fin 3 → ℤ, (if mm = 0 then (0 : ℝ) else ‖Z mm r‖) ≤ cw := by
            intro mm
            by_cases h0 : mm = 0
            · rw [if_pos h0]; exact hcw0
            · rw [if_neg h0]
              have hZint : Z mm r = ∫ y : E3,
                  ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                    * ((Work.BoseFixR.W1fun v h ℓ
                        (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)
                    * ((Work.BoseBoxFock.boxRestrictR ℓ
                        (Φ : Submission.BoseGases.X (m + 1) → ℝ)
                        (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ) := by
                rw [show Z mm r = imgPair v h fc Φ μ i j mm
                      (Submission.BoseGases.kcInsN m i ((0 : E3), r)) from rfl]
                rw [imgPair]
                refine MeasureTheory.integral_congr_ae
                  (Filter.Eventually.of_forall (fun y => ?_))
                beta_reduce
                rw [show (Submission.BoseGases.kcInsN m i ((0 : E3), r)) j = r j'
                    from hjslot _ r]
                rw [← Submission.BoseGases.kcInsN_update_zero]
              have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 => Submission.BoseGases.chiScale ℓ u
                  * (Φ : Submission.BoseGases.X (m + 1) → ℝ)
                    (Submission.BoseGases.kcInsN m i (u, r))) :=
                (Submission.BoseGases.chiScale_contDiff hℓ.ne').mul
                  (Φ.contDiff.comp (contDiff_kcInsN_ins i r))
              have hGs : HasCompactSupport (Submission.BoseGases.chiScale ℓ
                  * fun u : E3 => (Φ : Submission.BoseGases.X (m + 1) → ℝ)
                    (Submission.BoseGases.kcInsN m i (u, r))) :=
                (Submission.BoseGases.chiScale_hasCompactSupport hℓ.ne').mul_right
              have hsq : ‖Z mm r‖ ^ 2 ≤ 64 * Real.pi * BoseGases.a v * E r := by
                have hdual := imgPair_sq_le (v := v) (h := h) (R := R) (ℓ := ℓ)
                  hR hv hvrad hv_supp hℓ hRℓ (m := m) i j'
                  (Φ := (Φ : Submission.BoseGases.X (m + 1) → ℝ)) Φ.contDiff mm hr
                rw [← hZint, sum_integral_fderivSq_eq hGc hGs] at hdual
                simpa only [E] using hdual
              have h1 : ‖Z mm r‖ ≤ Real.sqrt (64 * Real.pi * BoseGases.a v * E r) := by
                rw [← Real.sqrt_sq (norm_nonneg (Z mm r))]
                exact Real.sqrt_le_sqrt hsq
              have h2 : Real.sqrt (64 * Real.pi * BoseGases.a v * E r) = cw := by
                rw [hcw]
                rw [show 64 * Real.pi * BoseGases.a v * E r
                    = (8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)
                        * Real.sqrt (E r)) ^ 2 from by
                      rw [show (8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)
                            * Real.sqrt (E r)) ^ 2
                          = 64 * (Real.sqrt Real.pi) ^ 2 * (Real.sqrt (BoseGases.a v)) ^ 2
                            * (Real.sqrt (E r)) ^ 2 from by ring]
                      rw [Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hav.le,
                        Real.sq_sqrt (hE0 r)]]
                exact Real.sqrt_sq (by positivity)
              linarith [h1, h2]
          calc ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) ≤ ∑ _mm ∈ S, cw :=
                Finset.sum_le_sum (fun mm _ => hterm mm)
            _ = (S.card : ℝ) * cw := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 343 * cw := by
                refine mul_le_mul_of_nonneg_right ?_ hcw0
                exact_mod_cast latFinSet_card_le_343 hR h2Rℓ
            _ = 343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v) * Real.sqrt (E r) := by
                rw [hcw]; ring
        · rw [hS0' r hr]
          positivity
      -- ### the integrability of `E` and its box bound
      have hEint : MeasureTheory.Integrable E
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        integrable_dirichletSlice_unrestricted (n := m) i hℓ
          (Φ := (Φ : Submission.BoseGases.X (m + 1) → ℝ)) Φ.contDiff
      have hEbound : (∫ r in Submission.BoseGases.abox m ℓ, E r) ≤ D := by
        have hpeel2 := dirichletPeel (n := m) i hℓ
          (Φ := (Φ : Submission.BoseGases.X (m + 1) → ℝ)) Φ.contDiff
        have hgoal : (∫ r in Submission.BoseGases.abox m ℓ, E r)
            = ∫ r : Submission.BoseGases.X m, (∫ y : E3, ∑ k : Fin 3,
                ‖fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale ℓ z
                  * (Φ : Submission.BoseGases.X (m + 1) → ℝ)
                    (Submission.BoseGases.kcInsN m i (z, r))) y
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
                (Submission.BoseGases.abox m ℓ)) := rfl
        rw [hgoal, ← hpeel2]
        exact hD
      -- ### the `L²` pair `(Γ', E)`: integrability of `Γ'²` and its box bound
      have hΓ2 := integral_lowSlot_kcInsN_sq_le (v := v) (μ := μ) hAdm.1 hav (m := m)
        (Φ := (Φ : Submission.BoseGases.X (m + 1) → ℝ)) hΦc fc i j hij
      have hΓ2int : MeasureTheory.Integrable (fun r : Submission.BoseGases.X m => (Γ' r) ^ 2)
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) := hΓ2.1
      have hΓ2bound : (∫ r in Submission.BoseGases.abox m ℓ, (Γ' r) ^ 2)
          ≤ 4 * Work.BoseBoxFix.normB v μ (m + 1) Φ / ℓ ^ 3 := hΓ2.2
      -- ### the Hölder step
      have hHolder : (∫ r in Submission.BoseGases.abox m ℓ, |Γ' r| * Real.sqrt (E r))
          ≤ Real.sqrt (∫ r in Submission.BoseGases.abox m ℓ, (Γ' r) ^ 2)
            * Real.sqrt (∫ r in Submission.BoseGases.abox m ℓ, E r) := by
        set ν : MeasureTheory.Measure (Submission.BoseGases.X m) :=
          (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ) with hν
        have hm1 : MeasureTheory.MemLp Γ' (ENNReal.ofReal 2) ν := by
          have h := (MeasureTheory.memLp_two_iff_integrable_sq (f := Γ')
            hΓ'm.aestronglyMeasurable).2 hΓ2int
          simpa using h
        have hm2 : MeasureTheory.MemLp (fun r : Submission.BoseGases.X m =>
            Real.sqrt (E r)) (ENNReal.ofReal 2) ν := by
          have h := (MeasureTheory.memLp_two_iff_integrable_sq
            (f := fun r : Submission.BoseGases.X m => Real.sqrt (E r))
            (Real.continuous_sqrt.measurable.comp_aemeasurable
              hEint.aemeasurable).aestronglyMeasurable).2 ?_
          · simpa using h
          · refine hEint.congr ?_
            filter_upwards with r
            exact (Real.sq_sqrt (hE0 r)).symm
        have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := ν) (p := 2) (q := 2)
          (by rw [Real.holderConjugate_iff]; norm_num) hm1 hm2
        have hL : (∫ a : Submission.BoseGases.X m, ‖Γ' a‖ * ‖Real.sqrt (E a)‖ ∂ν)
            = ∫ r in Submission.BoseGases.abox m ℓ, |Γ' r| * Real.sqrt (E r) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with r
          rw [Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg (E r))]
        have hR1 : (∫ a : Submission.BoseGases.X m, ‖Γ' a‖ ^ (2 : ℝ) ∂ν)
            = ∫ r in Submission.BoseGases.abox m ℓ, (Γ' r) ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with r
          rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
        have hR2 : (∫ a : Submission.BoseGases.X m, ‖Real.sqrt (E a)‖ ^ (2 : ℝ) ∂ν)
            = ∫ r in Submission.BoseGases.abox m ℓ, E r := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with r
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (E r)), Real.rpow_two,
            Real.sq_sqrt (hE0 r)]
        rw [hL, hR1, hR2] at hcs
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
        simpa only [hν] using hcs
      -- ### the product integrability on the box
      have hEsqrtm : AEMeasurable (fun r : Submission.BoseGases.X m => Real.sqrt (E r))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        Real.continuous_sqrt.measurable.comp_aemeasurable hEint.aemeasurable
      have hamgm : ∀ r : Submission.BoseGases.X m,
          |Γ' r| * Real.sqrt (E r) ≤ (1 / 2) * ((Γ' r) ^ 2 + E r) := by
        intro r
        nlinarith [sq_nonneg (|Γ' r| - Real.sqrt (E r)), Real.sq_sqrt (hE0 r), sq_abs (Γ' r)]
      have hRHSint : MeasureTheory.Integrable
          (fun r : Submission.BoseGases.X m => |Γ' r| * Real.sqrt (E r))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
            (Submission.BoseGases.abox m ℓ)) :=
        MeasureTheory.Integrable.mono'
          (f := fun r : Submission.BoseGases.X m => |Γ' r| * Real.sqrt (E r))
          (g := fun r : Submission.BoseGases.X m => (1 / 2) * ((Γ' r) ^ 2 + E r))
          ((hΓ2int.add hEint).const_mul (1 / 2))
          (((hΓ'm.aemeasurable.abs).mul hEsqrtm).aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun r => by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (show (0 : ℝ) ≤ |Γ' r| * Real.sqrt (E r) by positivity)]
            exact hamgm r))
      have hJrnint : MeasureTheory.IntegrableOn (fun r : Submission.BoseGases.X m => ‖Jr r‖)
          (Submission.BoseGases.abox m ℓ) MeasureTheory.volume := hJrInt.norm.integrableOn
      have hstep : (∫ r in Submission.BoseGases.abox m ℓ, ‖Jr r‖)
          ≤ ∫ r in Submission.BoseGases.abox m ℓ,
              (ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)))
                * (|Γ' r| * Real.sqrt (E r)) := by
        refine MeasureTheory.setIntegral_mono hJrnint (hRHSint.const_mul _) (fun r => ?_)
        calc ‖Jr r‖ ≤ (ℓ ^ 3) * ε * |Γ' r|
              * ∑ mm ∈ S, (if mm = 0 then 0 else ‖Z mm r‖) := hJrB r
          _ ≤ (ℓ ^ 3) * ε * |Γ' r|
              * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v) * Real.sqrt (E r)) :=
              mul_le_mul_of_nonneg_left (hZbound r)
                (mul_nonneg (mul_nonneg (by positivity) hε0) (abs_nonneg _))
          _ = (ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)))
              * (|Γ' r| * Real.sqrt (E r)) := by ring
      -- ### the final chain
      rw [hpeel]
      calc ‖∫ r : Submission.BoseGases.X m, Jr r‖
          ≤ ∫ r : Submission.BoseGases.X m, ‖Jr r‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ r in Submission.BoseGases.abox m ℓ, ‖Jr r‖ :=
            (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
              (s := Submission.BoseGases.abox m ℓ)
              (fun r hr => by rw [hJr0 r hr, norm_zero])).symm
        _ ≤ ∫ r in Submission.BoseGases.abox m ℓ,
              (ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)))
                * (|Γ' r| * Real.sqrt (E r)) := hstep
        _ = (ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)))
              * ∫ r in Submission.BoseGases.abox m ℓ, |Γ' r| * Real.sqrt (E r) := by
            rw [MeasureTheory.integral_const_mul]
        _ ≤ (ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)))
              * (Real.sqrt (∫ r in Submission.BoseGases.abox m ℓ, (Γ' r) ^ 2)
                * Real.sqrt (∫ r in Submission.BoseGases.abox m ℓ, E r)) :=
            mul_le_mul_of_nonneg_left hHolder hcc0
        _ ≤ (ℓ ^ 3 * ε * (343 * 8 * Real.sqrt Real.pi * Real.sqrt (BoseGases.a v)))
              * (Real.sqrt (4 * Work.BoseBoxFix.normB v μ (m + 1) Φ / ℓ ^ 3)
                * Real.sqrt D) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hΓ2bound)
              (Real.sqrt_le_sqrt hEbound) (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)) hcc0
        _ ≤ (343 * Cg * 16 * Real.sqrt Real.pi
              / (Real.sqrt Submission.BoseGases.chiSup * (4 * R ^ 2)) + 1)
            * (R / ℓ) ^ (2 * M) * Real.sqrt Submission.BoseGases.chiSup
            * Real.sqrt (BoseGases.a v) * ℓ ^ 3 * Real.sqrt ℓ * Real.sqrt D
            * Real.sqrt (Work.BoseBoxFix.normB v μ (m + 1) Φ) :=
            chAslotImages_arith (Cg := Cg) (ℓ := ℓ) (R := R) (D := D)
              (N := Work.BoseBoxFix.normB v μ (m + 1) Φ) (a := BoseGases.a v)
              (chiSup := Submission.BoseGases.chiSup) M hℓ hR h2Rℓ
              Submission.BoseGases.chiSup_pos hCgnn

    · -- =========== the non-integrable (junk-value) branch ===========
      rw [MeasureTheory.integral_undef hGint, norm_zero]
      have hC0 : (0 : ℝ) < Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos
      have hA0 : (0 : ℝ) < 343 * Cg * 16 * Real.sqrt Real.pi
          / (Real.sqrt Submission.BoseGases.chiSup * (4 * R ^ 2)) + 1 := by positivity
      positivity

end Work.BoseBoxFock.PCFU

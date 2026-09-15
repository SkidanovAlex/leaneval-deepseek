/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.PlateGeometry
import Submission.Vinogradov.SymBilinear

/-!
# The uncertainty principle at the coarse scale (GLYZ §3)

The uncertainty principle `DecouplingClass.IsFourierRep.uncertainty` (GLYZ Lemma 3.3) is applied
to the sum `F_J = ∑_{K ⊆ J} f_K` of the fine pieces of a coarse interval `J`, whose Fourier
support is contained in a *constant enlargement* of the coarse plate `𝒰_J` (this is
`PlateGeometry.piecePlate_subset_plate_scaled`, with the constant `8`).

* `uncConst k hk` — the constant `K = ∫ φ` of the canonical gauge bump, in `ℝ≥0∞`;
* `coe_nnnorm_rpow`, `convPow_const_mul`, `convPow_scale` — the elementary `ℝ≥0∞` bookkeeping;
* `integrable_psiPlate`, `integrable_platePsi` — integrability of the plate bump;
* **`isFourierRep_sum_blkFin`** — the block sum of the fine pieces lies in the class `𝒞` over the
  enlarged coarse plate;
* **`norm_rpow_le_convPow_blocks`** — the uncertainty principle for a block sum: for `r ≥ 1`,
  `‖∑_{i ∈ J} f_i x‖^r ≤ K^{r-1}·8^{k(k+1)/2}·(‖∑_{i∈J} f_i‖^r ∗ Φ_J)(x)`, where `Φ_J` is the
  canonical bump of the *coarse* plate `𝒰_J` (at the canonical scale `plateHalf m`).

This is the analytic input of GLYZ Lemma 3.4.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov


/-! ## 1. The constant of the uncertainty principle -/

/-- The constant `K` of the uncertainty principle for the canonical plate bumps. -/
noncomputable def uncConst (k : ℕ) (hk : 1 ≤ k) : ℝ≥0∞ :=
  ENNReal.ofReal (gaugeAmp k hk)
    * ENNReal.ofReal (∫ z, (max 1 (gauge k hk z)) ^ (-(gaugeExp k)))

lemma uncConst_ne_top (k : ℕ) (hk : 1 ≤ k) : uncConst k hk ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

lemma ofReal_integral_phiPlate (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    ENNReal.ofReal (∫ x, phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) = uncConst k hk := by
  rw [integral_phiPlate hk (gaugeExp_gt hk) δ c (gaugeAmp k hk) hδ,
    ENNReal.ofReal_mul (gaugeAmp_pos k hk).le]
  rfl

/-- The `ℝ≥0∞`-value of the `r`-th power of a norm. -/
lemma coe_nnnorm_rpow (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ((‖a‖₊ : NNReal) : ℝ≥0∞) ^ r = ENNReal.ofReal (‖a‖ ^ r) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg a) hr]
  simp [ENNReal.ofReal]

/-! ## 2. `convPow` under a scalar multiple of the weight -/

lemma convPow_const_mul (k : ℕ) (r : ℝ) (g : E k → ℂ) (Ψ : E k → ℝ≥0∞) (a : ℝ≥0∞)
    (ha : a ≠ ∞) (x : E k) :
    convPow k r g (fun y => a * Ψ y) x = a * convPow k r g Ψ x := by
  rw [convPow, convPow]
  rw [show (fun y => (‖g (x - y)‖₊ : ℝ≥0∞) ^ r * (a * Ψ y))
      = fun y => a * ((‖g (x - y)‖₊ : ℝ≥0∞) ^ r * Ψ y) from by
    funext y; ring]
  exact lintegral_const_mul' a _ ha

lemma convPow_scale (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (g : E k → ℂ) {δ t : ℝ} (c : ℝ) (hc : 1 ≤ c)
    (x : E k) :
    convPow k r g (platePhi k hk (c * δ) t) x
      ≤ ENNReal.ofReal (c ^ (k * (k + 1) / 2)) * convPow k r g (platePhi k hk δ t) x := by
  refine (convPow_mono k r g (fun y => platePhi_scale_le hk hc y) x).trans ?_
  rw [convPow_const_mul k r g (platePhi k hk δ t) _ ENNReal.ofReal_ne_top x]

/-! ## 3. Integrability of the plate bump -/

lemma integrable_psiPlate (k : ℕ) {δ c : ℝ} (hδ : δ ≠ 0) {ψ : E k → ℂ}
    (hψ : Integrable ψ) : Integrable (psiPlate k δ c ψ) := by
  have hBint : Integrable (fun x : E k => ψ (plateGaugeLin k δ c x)) :=
    integrable_comp_plateGaugeLin hδ c hψ
  refine (hBint.norm.const_mul |LinearMap.det (plateGaugeLin k δ c)|).mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun x : E k => ψ (plateGaugeLin k δ c x)) volume :=
      hBint.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : E k => chat k x (gammaVec k c)) volume :=
      (continuous_chat_right k (gammaVec k c)).aestronglyMeasurable
    show AEStronglyMeasurable (fun x : E k =>
      ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
        * (chat k x (gammaVec k c) * ψ (plateGaugeLin k δ c x))) volume
    exact aestronglyMeasurable_const.mul (h2.mul h1)
  · filter_upwards with x
    rw [norm_psiPlate]

lemma integrable_platePsi (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    Integrable (platePsi k hk δ c) :=
  integrable_psiPlate k hδ (gaugePsi_int k hk)

/-! ## 4. The block sum is in the class of the enlarged coarse plate -/

theorem isFourierRep_sum_blkFin {k N m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hmN : m ≤ N)
    (q : Fin (2 ^ m)) (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    IsFourierRep k (plate k (8 * plateHalf m) (pieceCenter (2 ^ m) q))
      (fun x => ∑ i ∈ blkFin N m q, f i x) := by
  have hsum : IsFourierRep k (⋃ i ∈ blkFin N m q, piecePlate k (2 ^ N) i)
      (fun x => ∑ i ∈ blkFin N m q, f i x) := by
    have h := IsFourierRep.sum (blkFin N m q) (fun i _ => hf i)
    rwa [show (∑ i ∈ blkFin N m q, f i) = fun x => ∑ i ∈ blkFin N m q, f i x from by
      funext x; rw [Finset.sum_apply]] at h
  refine hsum.mono ?_
  intro ξ hξ
  simp only [Set.mem_iUnion] at hξ
  obtain ⟨i, hi, hξ⟩ := hξ
  exact piecePlate_subset_plate_scaled hk hm hmN q i (mem_blkFin.mp hi) hξ

/-! ## 5. The uncertainty step for a block sum -/

/-- **GLYZ Lemma 3.3 applied to the sum of the fine pieces of a coarse block.**  For `r ≥ 1`
the `r`-th power of the block sum at a point is bounded by the convolved `r`-th power against
the canonical bump of the *enlarged* coarse plate, which is compared back to the canonical
scale. -/
theorem norm_rpow_le_convPow_blocks {k N m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hmN : m ≤ N)
    (q : Fin (2 ^ m)) (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    {r : ℝ} (hr : 1 ≤ r) (x : E k) :
    ((‖∑ i ∈ blkFin N m q, f i x‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ (uncConst k hk) ^ (r - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
        * convPow k r (fun y => ∑ i ∈ blkFin N m q, f i y)
            (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hrpow0 : 0 ≤ r - 1 := by linarith
  set F : E k → ℂ := fun y => ∑ i ∈ blkFin N m q, f i y with hFdef
  have hrep : IsFourierRep k (plate k (8 * plateHalf m) (pieceCenter (2 ^ m) q)) F :=
    isFourierRep_sum_blkFin hk hm hmN q f hf
  have hFcont : Continuous F := hrep.continuous
  obtain ⟨M, hM0, hbdd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : E k, ‖F y‖ ≤ M := by
    obtain ⟨ι, mI, Γ, ν, d, hν, hd, hΓ, hdm, hU, hfd⟩ := hrep
    letI : MeasurableSpace ι := mI
    haveI : IsFiniteMeasure ν := hν
    have hFeq : F = repFun k Γ ν d := funext fun y => (hfd y).trans rfl
    refine ⟨∫ u, ‖d u‖ ∂ν, ?_, fun y => ?_⟩
    · have h := norm_repFun_le Γ ν (φ := d) (0 : E k)
      rw [← hFeq] at h
      exact (norm_nonneg _).trans h
    · rw [hFeq]; exact norm_repFun_le Γ ν (φ := d) y
  have hδpos : 0 < 8 * plateHalf m := by rw [plateHalf]; positivity
  have hδne : 8 * plateHalf m ≠ 0 := hδpos.ne'
  set φ : E k → ℝ := fun y => phiPlate k hk (8 * plateHalf m) (pieceCenter (2 ^ m) q)
      (gaugeExp k) (gaugeAmp k hk) y with hφdef
  have hφint : Integrable φ := platePhi_integrable k hk hδne _
  have hφnn : ∀ y, 0 ≤ φ y :=
    fun y => phiPlate_nonneg k hk _ _ _ _ (gaugeAmp_pos k hk).le y
  have hψint : Integrable (platePsi k hk (8 * plateHalf m) (pieceCenter (2 ^ m) q)) :=
    integrable_platePsi k hk hδne _
  have hψhat : ∀ ξ ∈ plate k (8 * plateHalf m) (pieceCenter (2 ^ m) q),
      (∫ y, platePsi k hk (8 * plateHalf m) (pieceCenter (2 ^ m) q) y * chat k (-y) ξ) = 1 :=
    fun ξ hξ => platePsi_hat k hk hδpos hξ
  have hψφ : ∀ y, ‖platePsi k hk (8 * plateHalf m) (pieceCenter (2 ^ m) q) y‖ ≤ φ y :=
    fun y => norm_platePsi_le k hk _ _ y
  have hcont1 : Continuous (fun y : E k => ‖F (x - y)‖) :=
    (hFcont.comp (continuous_const.sub continuous_id)).norm
  have hint1 : Integrable (fun y : E k => ‖F (x - y)‖ * φ y) :=
    hφint.bdd_mul hcont1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hbdd (x - y))
  have hint : Integrable (fun y : E k => ‖F (x - y)‖ ^ r * φ y) :=
    hφint.bdd_mul (hcont1.rpow_const (fun _ => Or.inr hr0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) r)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbdd (x - y)) hr0)
  have hunc := hrep.uncertainty hψint hψhat hφnn hψφ hr x hφint hint1 hint
  have hnn : ∀ y : E k, 0 ≤ ‖F (x - y)‖ ^ r * φ y :=
    fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) r) (hφnn y)
  have hW0 : 0 ≤ ∫ y, φ y := integral_nonneg hφnn
  have hscale : convPow k r F (platePhi k hk (8 * plateHalf m) (pieceCenter (2 ^ m) q)) x
      ≤ ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
        * convPow k r F (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x :=
    convPow_scale k hk r F (δ := plateHalf m) (t := pieceCenter (2 ^ m) q) (c := 8)
      (by norm_num) x
  calc ((‖F x‖₊ : NNReal) : ℝ≥0∞) ^ r
      = ENNReal.ofReal (‖F x‖ ^ r) := coe_nnnorm_rpow (F x) hr0
    _ ≤ ENNReal.ofReal ((∫ y, φ y) ^ (r - 1) * ∫ y, ‖F (x - y)‖ ^ r * φ y) :=
        ENNReal.ofReal_le_ofReal hunc
    _ = ENNReal.ofReal (∫ y, φ y) ^ (r - 1)
          * ENNReal.ofReal (∫ y, ‖F (x - y)‖ ^ r * φ y) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hW0 _),
          ENNReal.ofReal_rpow_of_nonneg hW0 hrpow0]
    _ = (uncConst k hk) ^ (r - 1)
          * convPow k r F (platePhi k hk (8 * plateHalf m) (pieceCenter (2 ^ m) q)) x := by
        rw [ofReal_integral_phiPlate k hk hδne (pieceCenter (2 ^ m) q),
          ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
        congr 1
        rw [convPow]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) r),
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (F (x - y))) hr0]
        have h2 : ENNReal.ofReal ‖F (x - y)‖ = ((‖F (x - y)‖₊ : NNReal) : ℝ≥0∞) := by
          simp [ENNReal.ofReal]
        rw [h2, hφdef, platePhi_apply]
    _ ≤ (uncConst k hk) ^ (r - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
          * convPow k r F (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x := by
        rw [mul_assoc]
        exact mul_le_mul_right hscale _


end Submission.Vinogradov

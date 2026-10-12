import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.slotCoulTailTsum
import Submission.Work.BoseBoxFock.PCFU.slotFold
import Submission.Work.BoseBoxFock.PCFU.slotFoldSummable
import Submission.Work.BoseBoxFock.PCFU.slotSamplingRefl
import Submission.Work.BoseBoxFock.PCFU.slotTrunc
import Submission.Work.BoseBoxFock.PCFU.slotTsumCS
import Submission.Work.BoseBoxFock.W1fun_integrable_of_regime
import Submission.Work.BoseBoxFock.heatImage_t_rpow
import Submission.Work.BoseBoxFock.kinFT_neg_even_odd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators Topology

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Real-valued UV taper (the `ℝ`-content of `taperC`). -/
def taperR (fu : Work.BoseBoxFix.LowCut) (ℓ : ℝ) (N : ℕ) (n : Fin 3 → ℤ) : ℝ :=
  Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseBoxFock.kappaL ℓ n)

lemma taperC_eq_taperR (fu : Work.BoseBoxFix.LowCut) (ℓ : ℝ) (N : ℕ) (n : Fin 3 → ℤ) :
    taperC fu ℓ N n = ((taperR fu ℓ N n : ℝ) : ℂ) := rfl

/-- The reflected-argument Fourier norm identity. -/
lemma kinFT_refl_neg_norm (g : E3 → ℝ) (y p : E3) :
    ‖Submission.BoseGases.kinFT (fun z : E3 => ((g (y - z) : ℝ) : ℂ)) (-p)‖
      = ‖Submission.BoseGases.kinFT (fun x : E3 => ((g x : ℝ) : ℂ)) p‖ := by
  set u : E3 → ℂ := fun w => ((g (-w) : ℝ) : ℂ) with hu
  have hΨ : (fun z : E3 => ((g (y - z) : ℝ) : ℂ)) = fun z => u (z - y) := by
    funext z
    simp only [hu]
    congr 2
    abel
  rw [hΨ, Work.BoseBoxFock.kinFT_sub_right u y (-p), norm_mul]
  have h1 : ‖Complex.exp (-(Complex.I * (inner ℝ y (-p) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [h1, one_mul]
  have h2 : Submission.BoseGases.kinFT u (-p)
      = Submission.BoseGases.kinFT (fun w => u (-w)) p :=
    Work.BoseBoxFock.kinFT_neg_eq u p
  rw [h2]
  rw [show (fun w => u (-w)) = fun x : E3 => ((g x : ℝ) : ℂ) from by
    funext w; simp [hu]]

/-- `W₁` is integrable, vanishes off the ball of radius `R`, and is even. -/
theorem slotW1_aux {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ)
      ∧ (∀ x : E3, R ≤ ‖x‖ → Work.BoseFixR.W1fun v h ℓ x = 0)
      ∧ (∀ x : E3, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x) := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hzero : ∀ x : E3, R ≤ ‖x‖ → Work.BoseFixR.W1fun v h ℓ x = 0 :=
    fun x hx => W1fun_eq_zero_of_le_norm' hv_supp hx
  have hpt : ∀ x : E3, |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * |Submission.BoseGases.g0 v h x| := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · have h2 := Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R) hℓ hRℓ hx
      have he : Work.BoseFixR.W1fun v h ℓ x
          = Submission.BoseGases.g0 v h x * (Submission.BoseGases.convScale ℓ x)⁻¹ := by
        rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, div_eq_mul_inv]
      rw [he, abs_mul]
      calc |Submission.BoseGases.g0 v h x| * |(Submission.BoseGases.convScale ℓ x)⁻¹|
          ≤ |Submission.BoseGases.g0 v h x| * 2 :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = 2 * |Submission.BoseGases.g0 v h x| := by ring
    · have hz := hzero x (le_of_lt (not_le.mp hx))
      rw [hz, abs_zero]
      positivity
  have hmeas : AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) volume := by
    have hconv : AEStronglyMeasurable (fun x : E3 => (Submission.BoseGases.convScale ℓ x)⁻¹) :=
      (Submission.BoseGases.conv_contDiff.continuous.measurable.comp
        (measurable_id.const_smul (ℓ⁻¹))).inv.aestronglyMeasurable
    refine AEStronglyMeasurable.congr (hg0.aestronglyMeasurable.mul hconv) ?_
    filter_upwards with x
    simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, Pi.mul_apply, Pi.inv_apply]
    rw [div_eq_mul_inv]
  refine ⟨?_, hzero, Work.BoseFixR.isEven_W1fun h hvrad ℓ⟩
  exact MeasureTheory.Integrable.mono' (hg0.abs.const_mul 2) hmeas
    (Filter.Eventually.of_forall hpt)

/-- `W1h` in terms of the real taper and `chat`. -/
lemma W1h_eq_taperR_chat {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (m : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.W1h v h μ fu N m
      = taperR fu (Work.BoseBoxFock.ellH v μ) N (Work.BoseBoxFock.labVec N m)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m) := by
  have hell : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    ellH_eq_sideAt_of_pos hside
  rw [Work.BoseBoxFock.W1h, taperR, hell, kmomLab_eq_kappaL]

/-- The support of the `ℂ`-cast of a real function. -/
lemma tsupport_ofReal (g : E3 → ℝ) :
    tsupport (fun x : E3 => ((g x : ℝ) : ℂ)) = tsupport g := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support, Complex.ofReal_eq_zero]

/-- The reflected state `z ↦ g(y - z)`. -/
def slotPsi (y : E3) (g : E3 → ℝ) : E3 → ℂ := fun z => ((g (y - z) : ℝ) : ℂ)

/-- The `KfrU`-lattice coefficient. -/
def slotBT (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (N : ℕ) (n : Fin 3 → ℤ) : ℂ :=
  Submission.BoseGases.kinFT
    (fun u : E3 => ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))
    (Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n)

/-- The taper-slot coefficient. -/
def slotAT (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut)
    (N : ℕ) (n : Fin 3 → ℤ) : ℂ :=
  (if n ∈ taperS N then taperC fu (Work.BoseBoxFock.ellH v μ) N n else 0)
    * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
          (Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n) : ℝ) : ℂ)

/-- The reflected-state lattice sample. -/
def slotEP (v : E3 → ℝ) (μ : ℝ) (y : E3) (g : E3 → ℝ) (n : Fin 3 → ℤ) : ℂ :=
  Submission.BoseGases.kinFT (slotPsi y g)
    (-(Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n))

/-- The Dirichlet energy of `g`. -/
def slotDir (g : E3 → ℝ) : ℝ :=
  ∫ x : E3, ∑ j : Fin 3, ‖fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2

set_option maxHeartbeats 1600000 in
theorem taperSlotOne :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
        {R μ : ℝ} {fu : Work.BoseBoxFix.LowCut} {N : ℕ},
        0 < R → 0 < Work.BoseBox.sideAt μ (BoseGases.a v) →
        (∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x) → MeasureTheory.MemLp v 1 →
        _root_.BoseGases.IsRadial v →
        tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
        R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
        1 ≤ N →
        ∀ (y : EuclideanSpace ℝ (Fin 3)) (g : EuclideanSpace ℝ (Fin 3) → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) g →
          tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
          ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
              (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w)
                - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w))‖
            ≤ C * (1 + R) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ 3
                * Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹
                    * ∫ x : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
                        ‖fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  obtain ⟨Cst, hCst0, hcoul⟩ := slotCoulTailTsum
  refine ⟨2 * Real.sqrt Cst, by positivity, ?_⟩
  intro v h R μ fu N hR hside hv hv1 hvrad hv_supp hRℓ hN y g hg hgs
  have hℓpos : (0 : ℝ) < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hΛpos : (0 : ℝ) < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N :=
    uvRad_pos hℓpos hN
  obtain ⟨hWint, hWzero, hWev⟩ :=
    slotW1_aux (v := v) (h := h) (R := R) (ℓ := Work.BoseBoxFock.ellH v μ)
      hR hvrad hv_supp hℓpos hRℓ
  -- the reflected state is smooth with compact support
  have hΨcont : ContDiff ℝ (⊤ : ℕ∞) (slotPsi y g) := by
    exact Complex.ofRealCLM.contDiff.comp (hg.comp (contDiff_const.sub contDiff_id))
  have hboxcpt : IsCompact
      {z : E3 | y - z ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)} := by
    have h1 : IsCompact (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :=
      Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (Work.BoseBoxFock.ellH v μ)
    have h2 : IsCompact
        ((fun w : E3 => y - w) '' Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :=
      h1.image (continuous_const.sub continuous_id)
    have heq : ((fun w : E3 => y - w) '' Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
        = {z : E3 | y - z ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨w, hw, hwz⟩
        rw [← hwz]
        have h : y - (y - w) = w := by abel
        rw [h]
        exact hw
      · intro hz
        exact ⟨y - z, hz, by abel⟩
    rw [heq] at h2
    exact h2
  have hΨsupp : tsupport (slotPsi y g)
      ⊆ {z : E3 | y - z ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)} := by
    refine closure_minimal ?_ hboxcpt.isClosed
    intro z hz
    have hz' : g (y - z) ≠ 0 := by
      intro h0
      exact hz (by simp [slotPsi, h0])
    exact hgs (subset_tsupport g (Function.mem_support.mpr hz'))
  have hΨcs : HasCompactSupport (slotPsi y g) :=
    IsCompact.of_isClosed_subset hboxcpt (isClosed_tsupport _) hΨsupp
  -- the two pairing identities
  have hTr := slotTrunc (v := v) (h := h) (μ := μ) (fu := fu) (N := N) (y := y) (g := g) hg hgs
  have hFd := slotFold (ℓ := Work.BoseBoxFock.ellH v μ) (R := R)
      (W := Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (Ψ := slotPsi y g)
      hℓpos hWint hWev hWzero hΨcont hΨcs
  have hsumBT : Summable (fun n : Fin 3 → ℤ => slotBT v h μ N n * slotEP v μ y g n) :=
    slotFoldSummable (ℓ := Work.BoseBoxFock.ellH v μ)
      (W := Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (Ψ := slotPsi y g)
      hℓpos hWint hΨcont hΨcs
  have htr' : (∫ z : E3, ((g (y - z) : ℝ) : ℂ) * KfrU v h μ fu N z)
      = ∑ m : Work.BoseBoxFock.Lab N, ((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ)
          * Submission.BoseGases.kinFT (fun z : E3 => ((g (y - z) : ℝ) : ℂ))
              (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m)) := hTr.2
  have hfd' : (∫ z : E3, ((g (y - z) : ℝ) : ℂ)
        * Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) z)
      = ∑' n : Fin 3 → ℤ, slotBT v h μ N n * slotEP v μ y g n := hFd.2
  -- the tapered finite sum, rewritten over `taperS N`
  have hTrS : (∑ m : Work.BoseBoxFock.Lab N,
        ((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ)
          * Submission.BoseGases.kinFT (fun z : E3 => ((g (y - z) : ℝ) : ℂ))
              (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m)))
      = ∑ n ∈ taperS N, slotAT v h μ fu N n * slotEP v μ y g n := by
    have hterm : ∀ m : Work.BoseBoxFock.Lab N,
        ((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ)
          * Submission.BoseGases.kinFT (fun z : E3 => ((g (y - z) : ℝ) : ℂ))
              (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m))
        = slotAT v h μ fu N (Work.BoseBoxFock.labVec N m)
            * slotEP v μ y g (Work.BoseBoxFock.labVec N m) := by
      intro m
      have hmS : Work.BoseBoxFock.labVec N m ∈ taperS N := mem_taperS.mpr ⟨m, rfl⟩
      rw [W1h_eq_taperR_chat hside m, kmomLab_eq_kappaL]
      dsimp only [slotAT, slotEP, slotPsi]
      rw [if_pos hmS, taperC_eq_taperR]
      push_cast
      rw [show slotPsi y g = (fun z : E3 => ((g (y - z) : ℝ) : ℂ)) from rfl]
    have h1 : (∑ m : Work.BoseBoxFock.Lab N,
          ((Work.BoseBoxFock.W1h v h μ fu N m : ℝ) : ℂ)
            * Submission.BoseGases.kinFT (fun z : E3 => ((g (y - z) : ℝ) : ℂ))
                (-(Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N m)))
        = ∑ m : Work.BoseBoxFock.Lab N,
            slotAT v h μ fu N (Work.BoseBoxFock.labVec N m)
              * slotEP v μ y g (Work.BoseBoxFock.labVec N m) :=
      Finset.sum_congr rfl (fun m _ => hterm m)
    rw [h1]
    show (∑ m : Work.BoseBoxFock.Lab N,
        slotAT v h μ fu N (Work.BoseBoxFock.labVec N m)
          * slotEP v μ y g (Work.BoseBoxFock.labVec N m))
      = ∑ n ∈ taperS N, slotAT v h μ fu N n * slotEP v μ y g n
    rw [taperS]
    exact (Finset.sum_image (f := fun n => slotAT v h μ fu N n * slotEP v μ y g n)
      (g := Work.BoseBoxFock.labVec N) (s := Finset.univ)
      (fun a _ b _ hab => labVec_injective N hab)).symm
  -- the coefficient facts
  have hBTchat : ∀ n : Fin 3 → ℤ,
      slotBT v h μ N n
        = ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n) : ℝ) : ℂ) := by
    intro n
    exact (Work.BoseBoxFock.chat_eq_kinFT_of_even hWev
      (Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n)).symm
  have hEeq : ∀ n : Fin 3 → ℤ,
      slotAT v h μ fu N n - slotBT v h μ N n
        = (if n ∈ taperS N then taperC fu (Work.BoseBoxFock.ellH v μ) N n else 0)
            * slotBT v h μ N n - slotBT v h μ N n := by
    intro n
    dsimp only [slotAT]
    rw [hBTchat n]
  have hEzero : ∀ n : Fin 3 → ℤ,
      ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
          < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N →
      slotAT v h μ fu N n - slotBT v h μ N n = 0 := by
    intro n hn
    have hnS : n ∈ taperS N := mem_taperS_of_norm_lt hℓpos hN hn
    have ht1 : taperC fu (Work.BoseBoxFock.ellH v μ) N n = 1 := taperC_eq_one_of_lt hΛpos hn
    rw [hEeq n, if_pos hnS, ht1, hBTchat n, one_mul, sub_self]
  have hEle : ∀ n : Fin 3 → ℤ,
      ‖slotAT v h μ fu N n - slotBT v h μ N n‖ ≤ 2 * ‖slotBT v h μ N n‖ := by
    intro n
    rw [hEeq n]
    by_cases hn : n ∈ taperS N
    · rw [if_pos hn]
      have hb := taperC_le_one fu (Work.BoseBoxFock.ellH v μ) N n
      have hstep : (taperC fu (Work.BoseBoxFock.ellH v μ) N n * slotBT v h μ N n
            - slotBT v h μ N n)
          = (taperC fu (Work.BoseBoxFock.ellH v μ) N n - 1) * slotBT v h μ N n := by ring
      rw [hstep, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖taperC fu (Work.BoseBoxFock.ellH v μ) N n - 1‖
          ≤ ‖taperC fu (Work.BoseBoxFock.ellH v μ) N n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one]; linarith
        _ = 2 := by norm_num
    · rw [if_neg hn, zero_mul, zero_sub, norm_neg]
      exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)
  -- the combination identity
  have hsumFin : Summable (fun n : Fin 3 → ℤ =>
      if n ∈ taperS N then slotAT v h μ fu N n * slotEP v μ y g n else 0) :=
    summable_of_ne_finset_zero (s := taperS N) (fun n hn => by simp [hn])
  have hcomb : (∫ z : E3, ((g (y - z) : ℝ) : ℂ)
        * (KfrU v h μ fu N z - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) z))
      = ∑' n : Fin 3 → ℤ, (slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n := by
    have hsplit : (∫ z : E3, ((g (y - z) : ℝ) : ℂ)
          * (KfrU v h μ fu N z - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) z))
        = (∫ z : E3, ((g (y - z) : ℝ) : ℂ) * KfrU v h μ fu N z)
          - (∫ z : E3, ((g (y - z) : ℝ) : ℂ)
              * Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) z) := by
      have hFd1 : MeasureTheory.Integrable (fun z : E3 => ((g (y - z) : ℝ) : ℂ)
          * Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) z) := hFd.1
      rw [← MeasureTheory.integral_sub hTr.1 hFd1]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    rw [hsplit, htr', hfd', hTrS]
    have hfin : (∑' n : Fin 3 → ℤ,
        (if n ∈ taperS N then slotAT v h μ fu N n * slotEP v μ y g n else 0))
        = ∑ n ∈ taperS N, slotAT v h μ fu N n * slotEP v μ y g n := by
      rw [tsum_eq_sum (s := taperS N) (fun n hn => by simp [hn])]
      exact Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [← hfin, ← Summable.tsum_sub hsumFin hsumBT]
    refine tsum_congr (fun n => ?_)
    by_cases hn : n ∈ taperS N
    · simp only [slotAT, if_pos hn]
      ring
    · simp only [slotAT, if_neg hn]
      ring
  -- the change of variables
  have hcv : (∫ w : E3, ((g w : ℝ) : ℂ)
        * (KfrU v h μ fu N (y - w) - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w)))
      = ∫ z : E3, ((g (y - z) : ℝ) : ℂ)
        * (KfrU v h μ fu N z - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) z) := by
    rw [← MeasureTheory.integral_sub_left_eq_self
        (f := fun w : E3 => ((g w : ℝ) : ℂ)
          * (KfrU v h μ fu N (y - w) - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w))) volume y]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [show y - (y - z) = z from by abel]
  -- the coulomb-tail bound at the `BT` coefficients
  obtain ⟨hAsumm, hA⟩ := hcoul (v := v) (h := h) (R := R)
    (ℓ := Work.BoseBoxFock.ellH v μ) (N := N) hR hℓpos hv hvrad hv_supp hRℓ hN
  have hsqeq : ∀ n : Fin 3 → ℤ,
      (if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
          ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        then ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        else 0) ^ 2
      = (if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
          ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ then (1 : ℝ) else 0)
        * (‖slotBT v h μ N n‖ ^ 2
            / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ ^ 2) := by
    intro n
    by_cases h : Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
        ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
    · rw [if_pos h, if_pos h, one_mul, div_pow]
    · rw [if_neg h, if_neg h, zero_pow (by norm_num), zero_mul]
  have ha2 : Summable (fun n : Fin 3 → ℤ =>
      (if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
          ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        then ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        else 0) ^ 2) := hAsumm.congr (fun n => (hsqeq n).symm)
  have hA2 : (∑' n : Fin 3 → ℤ,
      (if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
          ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        then ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        else 0) ^ 2)
      ≤ Cst * (1 + R) ^ 6 * (Work.BoseBoxFock.ellH v μ) ^ 3
          / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N := by
    rw [tsum_congr hsqeq]
    exact hA
  -- the sampling identity
  have hGsupp : tsupport (fun x : E3 => ((g x : ℝ) : ℂ))
      ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) := by
    rw [tsupport_ofReal]
    exact hgs
  have hGdiff : ContDiff ℝ 1 (fun x : E3 => ((g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hg.of_le (by simp))
  have hLatt := Work.BoseBoxFock.L1Tails.latticeDirichlet hℓpos hGdiff hGsupp
  have hBsq : Summable (fun n : Fin 3 → ℤ =>
      (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        * ‖Submission.BoseGases.kinFT (fun z : E3 => ((g (y - z) : ℝ) : ℂ))
            (-(Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n))‖) ^ 2) := by
    refine hLatt.summable.congr (fun n => ?_)
    rw [← kinFT_refl_neg_norm g y (Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n)]
    rw [mul_pow]
  have hB2 : (∑' n : Fin 3 → ℤ,
        (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ * ‖slotEP v μ y g n‖) ^ 2)
      = (Work.BoseBoxFock.ellH v μ) ^ 3 * slotDir g := by
    rw [show (fun n : Fin 3 → ℤ =>
          (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
            * ‖slotEP v μ y g n‖) ^ 2)
        = fun n : Fin 3 → ℤ =>
            ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ ^ 2
              * ‖slotEP v μ y g n‖ ^ 2 from funext (fun n => by rw [mul_pow])]
    exact slotSamplingRefl hℓpos hg hgs y
  -- Cauchy-Schwarz
  obtain ⟨hab, hCS⟩ := slotTsumCS
    (a := fun n : Fin 3 → ℤ =>
      if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
          ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        then ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
        else 0)
    (b := fun n : Fin 3 → ℤ =>
      ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ * ‖slotEP v μ y g n‖)
    (fun n => by split <;> positivity)
    (fun n => by positivity)
    ha2 hBsq
  -- summand comparison
  have hsumE : Summable (fun n : Fin 3 → ℤ =>
      (slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n) := by
    refine (hsumFin.sub hsumBT).congr (fun n => ?_)
    by_cases hn : n ∈ taperS N
    · simp only [slotAT, if_pos hn]; ring
    · simp only [slotAT, if_neg hn]; ring
  have hnorm : Summable (fun n : Fin 3 → ℤ =>
      ‖(slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n‖) := hsumE.norm
  have hpoint : ∀ n : Fin 3 → ℤ,
      ‖(slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n‖
        ≤ 2 * ((if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
              ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
            then ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
            else 0)
          * (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ * ‖slotEP v μ y g n‖)) := by
    intro n
    rw [norm_mul]
    by_cases hn : Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
        ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
    · rw [if_pos hn]
      have hκ : (0 : ℝ) < ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ :=
        lt_of_lt_of_le hΛpos hn
      have hκne : ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ ≠ 0 := ne_of_gt hκ
      have hrw : ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
            * (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ * ‖slotEP v μ y g n‖)
          = ‖slotBT v h μ N n‖ * ‖slotEP v μ y g n‖ := by
        field_simp
      rw [hrw]
      calc ‖slotAT v h μ fu N n - slotBT v h μ N n‖ * ‖slotEP v μ y g n‖
          ≤ (2 * ‖slotBT v h μ N n‖) * ‖slotEP v μ y g n‖ :=
            mul_le_mul_of_nonneg_right (hEle n) (norm_nonneg _)
        _ = 2 * (‖slotBT v h μ N n‖ * ‖slotEP v μ y g n‖) := by ring
    · rw [if_neg hn, zero_mul, mul_zero]
      have hz := hEzero n (not_le.mp hn)
      rw [hz, norm_zero, zero_mul]
  have h2ab : Summable (fun n : Fin 3 → ℤ =>
      2 * ((if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
              ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
            then ‖slotBT v h μ N n‖ / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
            else 0)
          * (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ * ‖slotEP v μ y g n‖))) :=
    Summable.mul_left 2 hab
  have hbnd : ‖∑' n : Fin 3 → ℤ,
        (slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n‖
      ≤ 2 * (Real.sqrt (Cst * (1 + R) ^ 6 * (Work.BoseBoxFock.ellH v μ) ^ 3
              / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3 * slotDir g)) := by
    calc ‖∑' n : Fin 3 → ℤ,
            (slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n‖
        ≤ ∑' n : Fin 3 → ℤ,
            ‖(slotAT v h μ fu N n - slotBT v h μ N n) * slotEP v μ y g n‖ :=
          norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Fin 3 → ℤ,
            2 * ((if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
                  ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
                then ‖slotBT v h μ N n‖
                  / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ else 0)
              * (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
                  * ‖slotEP v μ y g n‖)) :=
          Summable.tsum_le_tsum hpoint hnorm h2ab
      _ = 2 * ∑' n : Fin 3 → ℤ,
            ((if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
                  ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
                then ‖slotBT v h μ N n‖
                  / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ else 0)
              * (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
                  * ‖slotEP v μ y g n‖)) := tsum_mul_left
      _ ≤ 2 * (Real.sqrt (∑' n : Fin 3 → ℤ,
              (if Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
                  ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
                then ‖slotBT v h μ N n‖
                  / ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖ else 0) ^ 2)
          * Real.sqrt (∑' n : Fin 3 → ℤ,
              (‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) n‖
                * ‖slotEP v μ y g n‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS (by norm_num)
      _ ≤ 2 * (Real.sqrt (Cst * (1 + R) ^ 6 * (Work.BoseBoxFock.ellH v μ) ^ 3
              / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3 * slotDir g)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul (Real.sqrt_le_sqrt hA2) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          rw [hB2]
  -- final arithmetic
  have hΛne : Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N ≠ 0 := ne_of_gt hΛpos
  have hA0 : 0 ≤ Cst * (1 + R) ^ 6 * (Work.BoseBoxFock.ellH v μ) ^ 3
      / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N := by positivity
  have harith : 2 * (Real.sqrt (Cst * (1 + R) ^ 6 * (Work.BoseBoxFock.ellH v μ) ^ 3
            / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
        * Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3 * slotDir g))
      = (2 * Real.sqrt Cst) * (1 + R) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ 3
          * Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹ * slotDir g) := by
    have hsq : (Real.sqrt Cst * (1 + R) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ 3) ^ 2
          * ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹ * slotDir g)
        = (Cst * (1 + R) ^ 6 * (Work.BoseBoxFock.ellH v μ) ^ 3
            / Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          * ((Work.BoseBoxFock.ellH v μ) ^ 3 * slotDir g) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hCst0]
      field_simp
    rw [← Real.sqrt_mul hA0, ← hsq, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by positivity)]
    ring
  rw [hcv, hcomb]
  exact le_trans hbnd (le_of_eq harith)

end Work.BoseBoxFock.PCFU

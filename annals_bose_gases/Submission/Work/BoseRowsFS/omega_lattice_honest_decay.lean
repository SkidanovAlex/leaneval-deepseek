import ChallengeDeps
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseK15.card_le_of_vec_norm_le
import Submission.Work.BoseK15.sum_inv_one_add_norm_le
import Submission.Work.BoseRowsFS.Hon
import Submission.Work.BoseRowsFS.LatRiemann.lattice_riemann_core
import Submission.Work.BoseRowsFS.honPhi_bounds
import Submission.Work.BoseRowsFS.integral_Phi_div_norm_sq_le
import Submission.Work.BoseRowsFS.mass_identity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

noncomputable section

open scoped BigOperators
open MeasureTheory

set_option maxHeartbeats 10000000
set_option linter.style.haveILetI false

/-! ## 1. The lattice bookkeeping of the box `Lab N` -/

/-- `|x.valMinAbs| ≤ N` for `x : ZMod (2N+1)`. -/
lemma valMinAbs_abs_le (N : ℕ) (x : ZMod (2 * N + 1)) : |x.valMinAbs| ≤ (N : ℤ) := by
  have h := (ZMod.valMinAbs_spec x x.valMinAbs).mp rfl
  have h2 := h.2
  rw [Set.mem_Ioc] at h2
  obtain ⟨h1, h2⟩ := h2
  rw [abs_le]
  constructor <;> omega

/-- The box `[-N,N]³ ⊂ ℤ³` of lattice indices of the cube. -/
noncomputable def boxN (N : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) (N : ℤ))

lemma card_boxN (N : ℕ) : (boxN N).card = (2 * N + 1) ^ 3 := by
  rw [boxN, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 from by
    rw [Int.card_Icc]
    have h : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]]

lemma zero_mem_boxN (N : ℕ) : (0 : Fin 3 → ℤ) ∈ boxN N := by
  rw [boxN, Fintype.mem_piFinset]
  intro i; simp

lemma mem_boxN_iff {N : ℕ} {m : Fin 3 → ℤ} :
    m ∈ boxN N ↔ ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ) := by
  rw [boxN, Fintype.mem_piFinset]
  constructor
  · intro h i; simpa using h i
  · intro h i; simpa using h i

/-- Coordinate of a lattice point is bounded by its norm. -/
lemma coord_le_norm_zvec (m : Fin 3 → ℤ) (i : Fin 3) : |(m i : ℝ)| ≤ ‖zvec m‖ := by
  have h := PiLp.norm_apply_le (zvec m) i
  simpa [zvec] using h

/-- `‖h • m‖ = |h| ‖m‖`. -/
lemma norm_latPt (h : ℝ) (m : Fin 3 → ℤ) : ‖latPt h m‖ = |h| * ‖zvec m‖ := by
  show ‖h • zvec m‖ = |h| * ‖zvec m‖
  rw [norm_smul, Real.norm_eq_abs]

/-- `vec m = 2π • m`. -/
lemma vec_eq_smul_zvec (m : Fin 3 → ℤ) : Work.BoseB4.vec m = (2 * Real.pi) • zvec m := by
  show WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (m i : ℝ))
      = (2 * Real.pi) • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))
  rw [← WithLp.toLp_smul]
  congr 1

@[simp] lemma labVec_zero' (N : ℕ) :
    Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
  funext i
  simp [Work.BoseBoxFock.labVec]

lemma labVec_injective' (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

lemma labVec_mem_boxN (N : ℕ) (n : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.labVec N n ∈ boxN N := by
  rw [mem_boxN_iff]
  intro i
  have h := valMinAbs_abs_le N (n i)
  rw [abs_le] at h
  exact h

/-- `labVec N` hits every index of the box `[-N,N]³`. -/
lemma labVec_mk (N : ℕ) {m : Fin 3 → ℤ} (hm : ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ)) :
    Work.BoseBoxFock.labVec N (fun i => (m i : ZMod (2 * N + 1))) = m := by
  funext i
  show ((m i : ZMod (2 * N + 1))).valMinAbs = m i
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [Set.mem_Ioc]
  have := hm i
  constructor <;> omega

/-- **The lattice label set of the cube is the box minus the origin.** -/
lemma image_erase_labVec (N : ℕ) :
    (Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)).image (Work.BoseBoxFock.labVec N)
      = (boxN N).erase 0 := by
  have hc : Fintype.card (Work.BoseBoxFock.Lab N) = (2 * N + 1) ^ 3 := by
    simp [Work.BoseBoxFock.Lab, ZMod.card]
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
    refine Finset.mem_erase.mpr ⟨?_, labVec_mem_boxN N n⟩
    intro hcon
    exact hn0 (labVec_injective' N (by rw [hcon, labVec_zero']))
  · have h1 : ((Finset.univ.erase (0 : Work.BoseBoxFock.Lab N)).image
        (Work.BoseBoxFock.labVec N)).card = (2 * N + 1) ^ 3 - 1 := by
      rw [Finset.card_image_of_injective _ (labVec_injective' N),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hc]
    have h2 : ((boxN N).erase 0).card = (2 * N + 1) ^ 3 - 1 := by
      rw [Finset.card_erase_of_mem (zero_mem_boxN N), card_boxN]
    rw [h1, h2]

/-- The box momenta are the rescaled lattice `(2π/ℓ)ℤ³`. -/
lemma kmomLab_eq_latPt (ℓ : ℝ) (N : ℕ) (n : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.kmomLab ℓ N n
      = latPt (2 * Real.pi / ℓ) (Work.BoseBoxFock.labVec N n) := by
  rw [Work.BoseBoxFock.kmomLab, vec_eq_smul_zvec, smul_smul, latPt, zvec, ← WithLp.toLp_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 2. The shell bound on the lattice -/

/-- A shell `M ≤ ‖m‖ < 2M` of the lattice contributes at most `400 M` to `Σ ‖m‖⁻²`. -/
lemma shell_lattice_sum {M : ℝ} (hM : 1 ≤ M) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ m ∈ S, M ≤ ‖zvec m‖ ∧ ‖zvec m‖ < 2 * M) :
    ∑ m ∈ S, (‖zvec m‖ ^ 2)⁻¹ ≤ 400 * M := by
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hcount : (S.card : ℝ) ≤ (4 * M + 1) ^ 3 := by
    have h := Work.BoseK15.card_le_of_vec_norm_le S (4 * Real.pi * M)
      (by positivity) (fun m hm => ?_)
    · have h2 : 4 * Real.pi * M / Real.pi + 1 = 4 * M + 1 := by
        field_simp
      rwa [h2] at h
    · have h1 := (hS m hm).2
      calc ‖Work.BoseB4.vec m‖ = (2 * Real.pi) * ‖zvec m‖ := by
            rw [vec_eq_smul_zvec, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        _ ≤ (2 * Real.pi) * (2 * M) := mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = 4 * Real.pi * M := by ring
  have hterm : ∀ m ∈ S, (‖zvec m‖ ^ 2)⁻¹ ≤ (M ^ 2)⁻¹ := by
    intro m hm
    have h1 : M ≤ ‖zvec m‖ := (hS m hm).1
    have h2 : M ^ 2 ≤ ‖zvec m‖ ^ 2 := by nlinarith
    exact inv_anti₀ (by positivity) h2
  calc ∑ m ∈ S, (‖zvec m‖ ^ 2)⁻¹
      ≤ ∑ _m ∈ S, (M ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (M ^ 2)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * M + 1) ^ 3 * (M ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ 400 * M := by
        have h5 : (4 * M + 1) ^ 3 ≤ (5 * M) ^ 3 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 3
        have h6 : (5 * M) ^ 3 * (M ^ 2)⁻¹ = 125 * M := by
          field_simp
          ring
        nlinarith [hcount, hMpos, h5, h6,
          mul_le_mul_of_nonneg_right h5 (by positivity : (0:ℝ) ≤ (M ^ 2)⁻¹)]

end

/-- **Reindexing the honest lattice sum onto `(2π/ℓ)ℤ³`.**  The box modes are the
image of the cube under `labVec`, and `kmomLab ℓ N k = latPt (2π/ℓ) (labVec N k)`. -/
lemma sum_excited_eq_lattice {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
          / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2)
      = ∑ m ∈ ((Finset.univ.erase (0 : Work.BoseBoxFock.Lab (HM μ).N)).image
            (Work.BoseBoxFock.labVec (HM μ).N)),
          Work.BoseBoxFock.uvCut fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
              (latPt (2 * Real.pi / Work.BoseBoxFock.ellH v μ) m)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (latPt (2 * Real.pi / Work.BoseBoxFock.ellH v μ) m)
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                (latPt (2 * Real.pi / Work.BoseBoxFock.ellH v μ) m)
          / (2 * ‖latPt (2 * Real.pi / Work.BoseBoxFock.ellH v μ) m‖ ^ 2) := by
  have hside : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  rw [Finset.sum_image (fun x _ y _ hxy => labVec_injective' _ hxy)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hW1 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
      = Work.BoseBoxFock.uvCut fu
            (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k) := by
    show Work.BoseBoxFock.uvCut fu
          (Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k)
        * Work.BoseFixR.chat
            (Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k) = _
    rw [← hside]
  have hkmom : (Work.BoseRowsFS.honF v h fc fu HM μ).kmom k
      = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k := rfl
  rw [hW1, hkmom, kmomLab_eq_latPt]

/-- **The mass identity at the honest data**: `Ŵ₁ω(0) = (2π)⁻³∫Ŵ₁ĝ/(2‖p‖²)`. -/
lemma honE_W1omega0_eq_integral {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hℓ1 : 1 ≤ Work.BoseBoxFock.ellH v μ)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / (2 * ‖p‖ ^ 2) := by
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := lt_of_lt_of_le one_pos hℓ1
  have hside : Work.BoseBoxFock.ellH v μ
      = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  rw [show (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) 0 from rfl, ← hside,
    Work.BoseB7AK.W1rows.chat_zero]
  have h1 : (∫ x : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) x)
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x * Classical.choose h x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Work.BoseFixR.W1fun, Work.BoseFixR.W1omegaFun, Submission.BoseGases.wScaled]
    ring
  rw [h1]
  exact (mass_identity (v := v) (R := R) (ℓ := Work.BoseBoxFock.ellH v μ)
    hR hℓpos hv_nonneg hvrad hv_supp h hRℓ).symm

set_option maxHeartbeats 10000000 in
theorem omega_lattice_honest_decay {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hdecayW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (hdecayg : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (Ng : ℝ → ℕ) (εg : ℝ) (hεg : 0 < εg)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (hcut : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng μ)
        ∧ Cw ^ 2 * Work.BoseBoxFock.ellH v μ
            ≤ (2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng μ)) ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, Ng μ ≤ (HM μ).N) → ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      |(Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        - (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
              / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2)|
      ≤ C * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat ^ 2
          / (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
  have hχpos : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  -- ### `Cw ≥ 8π`: the decay row at `p = 0` against `∫ g₀ = 8π a`
  have hCw8 : 8 * Real.pi ≤ Cw := by
    set ℓ₀ : ℝ := max 1 (R / Submission.BoseGases.chiR0) with hℓ₀def
    have h1 : 1 ≤ ℓ₀ := le_max_left _ _
    have h2 : R ≤ ℓ₀ * Submission.BoseGases.chiR0 := by
      have h3 : R / Submission.BoseGases.chiR0 ≤ ℓ₀ := le_max_right _ _
      calc R = (R / Submission.BoseGases.chiR0) * Submission.BoseGases.chiR0 := by
            field_simp
        _ ≤ ℓ₀ * Submission.BoseGases.chiR0 := mul_le_mul_of_nonneg_right h3 hχpos.le
    have hℓ0pos : 0 < ℓ₀ := lt_of_lt_of_le one_pos h1
    have hWint : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ₀) :=
      Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ0pos h2
    have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
      Submission.BoseGases.g0_integrable hR hv_supp h
    have hmono : (∫ x, Submission.BoseGases.g0 v h x)
        ≤ ∫ x, Work.BoseFixR.W1fun v h ℓ₀ x :=
      MeasureTheory.integral_mono_ae hg0int hWint
        (Work.BoseB7AK.C3Q.I2_g0_le_W1fun_ae hR hℓ0pos hv_nonneg hvrad hv_supp h h2)
    have hg0 : (∫ x, Submission.BoseGases.g0 v h x) = 8 * Real.pi * _root_.BoseGases.a v :=
      Submission.BoseGases.g0_integral hR hv_supp h
    have hdec := hdecayW ℓ₀ h1 h2 0
    have hchat0 : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ₀) 0
        = ∫ x, Work.BoseFixR.W1fun v h ℓ₀ x := Work.BoseB7AK.W1rows.chat_zero _
    have hkey : 8 * Real.pi * _root_.BoseGases.a v ≤ Cw * _root_.BoseGases.a v := by
      rw [hg0.symm]
      refine le_trans hmono ?_
      rw [← hchat0]
      refine le_trans (le_abs_self _) ?_
      simpa using hdec
    exact le_of_mul_le_mul_right hkey hav
  -- ### the lattice-`∑ ‖m‖⁻⁴` bound
  obtain ⟨C4, hC4nn, hC4any⟩ := Work.BoseK15.sum_inv_one_add_norm_le 2 (by norm_num)
  have hC4b : ∀ S : Finset (Fin 3 → ℤ), (∀ m ∈ S, m ≠ 0) →
      ∑ m ∈ S, (‖zvec m‖ ^ 4)⁻¹ ≤ 4 * (2 * Real.pi) ^ 4 * C4 := by
    intro S hS
    have h1 : ∀ m ∈ S, (‖zvec m‖ ^ 4)⁻¹
        ≤ 4 * (2 * Real.pi) ^ 4 * (((1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹) := by
      intro m hm
      have hm0 : m ≠ 0 := hS m hm
      have hzn : 1 ≤ ‖zvec m‖ := by
        have hex : ∃ i : Fin 3, m i ≠ 0 := by
          by_contra hcon
          exact hm0 (funext fun i => by
            have := not_exists.mp hcon i
            simpa using not_not.mp this)
        obtain ⟨i, hi⟩ := hex
        have h1 : (1 : ℝ) ≤ |(m i : ℝ)| := by
          have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
          exact_mod_cast h2
        exact le_trans h1 (coord_le_norm_zvec m i)
      have hnorm : ‖Work.BoseB4.vec m‖ = 2 * Real.pi * ‖zvec m‖ := by
        rw [vec_eq_smul_zvec, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      have hge : 1 ≤ ‖Work.BoseB4.vec m‖ := by
        rw [hnorm]
        calc (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          _ = 2 * Real.pi * 1 := by ring
          _ ≤ 2 * Real.pi * ‖zvec m‖ := by
              exact mul_le_mul_of_nonneg_left hzn (by positivity)
      have hx : (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2 ≤ 4 * ‖Work.BoseB4.vec m‖ ^ 4 := by
        have h1 : (1 : ℝ) ≤ ‖Work.BoseB4.vec m‖ ^ 2 := one_le_pow₀ hge
        have h2 : 1 + ‖Work.BoseB4.vec m‖ ^ 2 ≤ 2 * ‖Work.BoseB4.vec m‖ ^ 2 := by linarith
        calc (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2
            ≤ (2 * ‖Work.BoseB4.vec m‖ ^ 2) ^ 2 :=
              pow_le_pow_left₀ (by linarith) h2 2
          _ = 4 * ‖Work.BoseB4.vec m‖ ^ 4 := by ring
      have hA : (0 : ℝ) < ‖zvec m‖ ^ 4 := pow_pos (lt_of_lt_of_le one_pos hzn) 4
      have hB : (0 : ℝ) < (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2 := by positivity
      have hnorm4 : ‖Work.BoseB4.vec m‖ ^ 4 = (2 * Real.pi) ^ 4 * ‖zvec m‖ ^ 4 := by
        rw [hnorm]; ring
      have hEq2 : (‖zvec m‖ ^ 4)⁻¹ = (2 * Real.pi) ^ 4 / ‖Work.BoseB4.vec m‖ ^ 4 := by
        rw [hnorm]
        field_simp
      have hEq : 4 * (2 * Real.pi) ^ 4 * ((1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹
          = 4 * (2 * Real.pi) ^ 4 / (1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2 := by
        rw [div_eq_mul_inv]
      rw [hEq2, hEq]
      field_simp
      nlinarith [hx, hnorm4, hA, hB]
    calc ∑ m ∈ S, (‖zvec m‖ ^ 4)⁻¹
        ≤ ∑ m ∈ S, 4 * (2 * Real.pi) ^ 4 * (((1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹) :=
          Finset.sum_le_sum h1
      _ = 4 * (2 * Real.pi) ^ 4 * ∑ m ∈ S, (((1 + ‖Work.BoseB4.vec m‖ ^ 2) ^ 2)⁻¹) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * (2 * Real.pi) ^ 4 * C4 := by
          refine mul_le_mul_of_nonneg_left (hC4any S) (by positivity)
  set Cval : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
      * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
      + 2 * Cw ^ 2 + 100 * Cw ^ 2 * R
      + 100 * Cw ^ 2 with hCvaldef
  refine ⟨Cval, ?_, ?_⟩
  · rw [hCvaldef]
    have h1 : (0 : ℝ) ≤ 4 * (2 * Real.pi) ^ 4 * C4 := by positivity
    have h2 : (0 : ℝ) ≤ Cw ^ 2 / 2 + 8 * Real.pi * R * Cw := by positivity
    positivity
  intro HM hN μ hμ ht
  obtain ⟨hℓ1, hRℓ⟩ := hrég μ hμ ht
  obtain ⟨hcut1, hcut2⟩ := hcut μ hμ ht
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set hr : ℝ := 2 * Real.pi / ℓ with hrdef
  set Λg : ℝ := Work.BoseBoxFock.uvRad ℓ (Ng μ) with hΛgdef
  set Λ : ℝ := Work.BoseBoxFock.uvRad ℓ (HM μ).N with hΛdef
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hrpos : 0 < hr := by rw [hrdef]; positivity
  have hCwpos : 0 < Cw := lt_of_lt_of_le (by positivity) hCw8
  -- monotonicity of the cut radius in `N`
  have hΛgmono : Λg ≤ Λ := by
    rw [hΛgdef, hΛdef, Work.BoseBoxFock.uvRad, Work.BoseBoxFock.uvRad]
    have h1 : (Ng μ : ℝ) ≤ ((HM μ).N : ℝ) := by
      exact_mod_cast hN μ
    nlinarith [Real.pi_pos, hℓpos]
  have hNgpos : 1 ≤ Ng μ := by
    by_contra hcon
    rw [not_le] at hcon
    have hzero : Ng μ = 0 := Nat.lt_one_iff.mp hcon
    have hΛg0 : Λg = 0 := by
      rw [hΛgdef, Work.BoseBoxFock.uvRad, hzero]
      norm_num
    rw [hΛg0] at hcut1
    have h1R : 0 < 1 / R := one_div_pos.mpr hR
    linarith [hcut1, h1R]
  have hΛgpos : 0 < Λg := by
    rw [hΛgdef, Work.BoseBoxFock.uvRad]
    have h1 : (0 : ℝ) < (Ng μ : ℝ) := by exact_mod_cast hNgpos
    positivity
  have hΛpos : 0 < Λ := lt_of_lt_of_le hΛgpos hΛgmono
  -- the key scale: `8π²ℓ ≤ Λ³`
  have hΛ3 : 8 * Real.pi ^ 2 * ℓ ≤ Λ ^ 3 := by
    have h1 : Cw ^ 2 * ℓ ≤ (2 * Λ) ^ 3 := by
      refine le_trans hcut2 ?_
      have h2 : (2 * Λg) ^ 3 ≤ (2 * Λ) ^ 3 := by
        apply pow_le_pow_left₀ <;> linarith
      exact h2
    have h2 : (64 * Real.pi ^ 2) * ℓ ≤ Cw ^ 2 * ℓ := by
      have h3 : (64 * Real.pi ^ 2) ≤ Cw ^ 2 := by
        have h4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 8 * Real.pi) hCw8 2
        nlinarith [h4]
      exact mul_le_mul_of_nonneg_right h3 hℓpos.le
    have h4 : (2 * Λ) ^ 3 = 8 * Λ ^ 3 := by ring
    nlinarith [h1, h2, h4, hΛpos, hℓpos]
  have hT : 1 / (1 + Λ) ^ 3 ≤ 1 / (8 * Real.pi ^ 2 * ℓ) := by
    rw [one_div, one_div]
    refine inv_anti₀ (by positivity) ?_
    exact le_trans hΛ3 (by nlinarith [hΛpos])
  -- ### the profile `Φ` and its two pointwise bounds
  set Φ : EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
      * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / 2 with hΦdef
  have hA0 : (0 : ℝ) ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 := by positivity
  have hB0 : (0 : ℝ) ≤ 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2 := by positivity
  obtain ⟨hΦbd, hΦlip⟩ := honPhi_bounds (v := v) (h := h) (R := R) (ℓ := ℓ)
    hR hℓpos hRℓ hv_nonneg hvrad hv_supp hav hCw (hdecayW ℓ hℓ1 hRℓ) (hdecayg ℓ hℓ1 hRℓ)
  -- ### the mass identity at the honest data
  have hside : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  have hell : (Work.BoseRowsFS.honE v h fc fu HM μ).ell = ℓ := by
    rw [show (Work.BoseRowsFS.honE v h fc fu HM μ).ell
        = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) from rfl, ← hside, ← hℓdef]
  have haScat : (Work.BoseRowsFS.honE v h fc fu HM μ).aScat = _root_.BoseGases.a v := rfl
  have hom : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = (((2 * Real.pi) ^ 3)⁻¹) * ∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2 := by
    rw [honE_W1omega0_eq_integral R hR hv_nonneg hvrad hv_supp HM μ hμ hav hℓ1 hRℓ]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hΦdef]
    ring
  -- ### the sum, reindexed onto the lattice
  set S : Finset (Fin 3 → ℤ) :=
    (Finset.univ.erase (0 : Work.BoseBoxFock.Lab (HM μ).N)).image
      (Work.BoseBoxFock.labVec (HM μ).N) with hSdef
  have hsum := sum_excited_eq_lattice (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav
  rw [← hSdef] at hsum
  set K : Finset (Fin 3 → ℤ) := S.filter (fun m => ‖latPt hr m‖ < 2 * Λ) with hKdef
  have hS_eq : S = (boxN (HM μ).N).erase 0 := image_erase_labVec (HM μ).N
  have hKmem : ∀ m : Fin 3 → ℤ, m ∈ K ↔ (m ≠ 0 ∧ ‖latPt hr m‖ < 2 * Λ) := by
    intro m
    rw [hKdef, Finset.mem_filter, hS_eq, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hm0, _⟩, hlt⟩; exact ⟨hm0, hlt⟩
    · rintro ⟨hm0, hlt⟩
      refine ⟨⟨hm0, ?_⟩, hlt⟩
      rw [mem_boxN_iff]
      intro i
      have h1 : |(m i : ℝ)| ≤ ‖zvec m‖ := coord_le_norm_zvec m i
      have h2Λ : 2 * Λ = hr * (((HM μ).N : ℝ) / 2) := by
        rw [hrdef, hΛdef, Work.BoseBoxFock.uvRad]; ring
      have h3 : ‖zvec m‖ < ((HM μ).N : ℝ) / 2 := by
        rw [h2Λ, norm_latPt, abs_of_pos hrpos] at hlt
        exact lt_of_mul_lt_mul_left hlt hrpos.le
      have h4 : |((m i : ℤ) : ℝ)| < ((HM μ).N : ℝ) := by
        have h5 : |(m i : ℝ)| < ((HM μ).N : ℝ) / 2 := lt_of_le_of_lt h1 h3
        have h6 : ((HM μ).N : ℝ) / 2 ≤ ((HM μ).N : ℝ) := by
          have h7 : (0 : ℝ) ≤ ((HM μ).N : ℝ) := Nat.cast_nonneg _
          linarith
        linarith
      rw [abs_lt] at h4
      constructor
      · have h7 : -(((HM μ).N : ℤ) : ℝ) ≤ ((m i : ℤ) : ℝ) := by
          push_cast
          linarith [h4.1]
        exact_mod_cast h7
      · have h7 : ((m i : ℤ) : ℝ) ≤ (((HM μ).N : ℤ) : ℝ) := by
          push_cast
          linarith [h4.2]
        exact_mod_cast h7
  -- ### the ζ-weight is `1` on the ball of radius `Λ` and `0` outside radius `2Λ`
  have hzeta_one : ∀ m : Fin 3 → ℤ, ‖latPt hr m‖ ≤ Λ →
      Work.BoseBoxFock.uvCut fu Λ (latPt hr m) = 1 := by
    intro m hm
    rw [Work.BoseBoxFock.uvCut, fu.one _ (by rw [div_le_one hΛpos]; exact hm)]
  have hzeta_zero : ∀ m : Fin 3 → ℤ, 2 * Λ ≤ ‖latPt hr m‖ →
      Work.BoseBoxFock.uvCut fu Λ (latPt hr m) = 0 := by
    intro m hm
    rw [Work.BoseBoxFock.uvCut, fu.zero _ (by rw [le_div_iff₀ hΛpos]; linarith)]
  have hzeta_mem : ∀ m : Fin 3 → ℤ, 0 ≤ Work.BoseBoxFock.uvCut fu Λ (latPt hr m)
      ∧ Work.BoseBoxFock.uvCut fu Λ (latPt hr m) ≤ 1 := by
    intro m
    rw [Work.BoseBoxFock.uvCut]
    exact ⟨fu.nonneg _, fu.le_one _⟩
  -- ### the summand, reduced to the lattice and the profile `Φ`
  have hsumid : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
              ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
          / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2))
      = ∑ m ∈ K, Work.BoseBoxFock.uvCut fu Λ (latPt hr m)
          * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2) := by
    rw [hsum]
    have h1 : ∀ m ∈ S, (Work.BoseBoxFock.uvCut fu Λ (latPt hr m)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (latPt hr m)
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (latPt hr m)
          / (2 * ‖latPt hr m‖ ^ 2))
        = Work.BoseBoxFock.uvCut fu Λ (latPt hr m)
            * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2) := by
      intro m _
      simp only [hΦdef]
      ring
    rw [Finset.sum_congr rfl h1]
    refine (Finset.sum_subset (fun m hm => Finset.mem_of_mem_filter m hm) ?_).symm
    intro m hmS hmK
    have hge : 2 * Λ ≤ ‖latPt hr m‖ := by
      by_contra hcon
      exact hmK (Finset.mem_filter.mpr ⟨hmS, not_le.mp hcon⟩)
    rw [hzeta_zero m hge]
    ring
  -- ### the `ℓ`-powers and the ζ-correction
  have hℓ3 : ℓ ^ (-(3 : ℝ)) = (ℓ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hℓpos.le]
    norm_num
  have hr3 : ((2 * Real.pi) ^ 3)⁻¹ * hr ^ 3 = (ℓ ^ 3)⁻¹ := by
    rw [hrdef]
    field_simp
  -- ### the main estimate
  have hmain : |(((2 * Real.pi) ^ 3)⁻¹) * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
      - ℓ ^ (-(3 : ℝ)) * ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          (Work.BoseRowsFS.honE v h fc fu HM μ).W1 k
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)
            / (2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2)|
      ≤ Cval * _root_.BoseGases.a v ^ 2 / ℓ := by
    rw [hsumid]
    set Sg : ℝ := ∑ m ∈ K, Φ (latPt hr m) / ‖latPt hr m‖ ^ 2 with hSgdef
    set Sc : ℝ := ∑ m ∈ K, (1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
      * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2) with hScdef
    have hsplit : (∑ m ∈ K, Work.BoseBoxFock.uvCut fu Λ (latPt hr m)
          * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2))
        = Sg - Sc := by
      rw [hSgdef, hScdef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    have hℓnn : 0 ≤ ℓ ^ (-(3 : ℝ)) := Real.rpow_nonneg hℓpos.le _
    have htri : |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
          - ℓ ^ (-(3 : ℝ)) * (Sg - Sc)|
        ≤ |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
              - ℓ ^ (-(3 : ℝ)) * Sg| + ℓ ^ (-(3 : ℝ)) * |Sc| := by
      have h1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
            - ℓ ^ (-(3 : ℝ)) * (Sg - Sc)
          = (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
              - ℓ ^ (-(3 : ℝ)) * Sg) + ℓ ^ (-(3 : ℝ)) * Sc := by ring
      rw [h1]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_nonneg hℓnn]
    refine le_trans htri ?_
    by_cases hNcase : (HM μ).N ≤ 6
    · -- ### Case B: `N ≤ 6`
      have hℓle : ℓ ≤ 6 * Real.pi * R := by
        have h1 : 1 / R ≤ 2 * Λg := hcut1
        have h2 : 2 * Λg = Real.pi * ((Ng μ : ℝ)) / ℓ := by
          rw [hΛgdef, Work.BoseBoxFock.uvRad]; ring
        rw [h2] at h1
        have h3 : ((Ng μ : ℝ)) ≤ 6 := by
          exact_mod_cast (le_trans (hN μ) hNcase : Ng μ ≤ 6)
        rw [le_div_iff₀ hℓpos] at h1
        have h4 : ℓ ≤ Real.pi * (Ng μ : ℝ) * R := by
          field_simp at h1
          linarith [h1]
        calc ℓ ≤ Real.pi * (Ng μ : ℝ) * R := h4
          _ ≤ Real.pi * 6 * R := by
              refine mul_le_mul_of_nonneg_right ?_ hR.le
              exact mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
          _ = 6 * Real.pi * R := by ring
      -- (i) the continuum part
      have hX : |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)|
          ≤ 100 * Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 / ℓ := by
        have h1 : |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)|
            = ((2 * Real.pi) ^ 3)⁻¹
              * |(∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)]
        rw [h1]
        have h2 : |(∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)|
            ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100 := by
          refine integral_Phi_div_norm_sq_le (by positivity) (fun p => ?_)
          have h3 := hΦbd p
          rw [div_eq_mul_inv] at h3
          exact h3
        refine le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) ?_
        rw [le_div_iff₀ hℓpos]
        have h9 : ((2 * Real.pi) ^ 3)⁻¹ ≤ 1 / 100 := by
          rw [inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 3)]
          nlinarith [Real.pi_gt_three]
        have h10 : ((2 * Real.pi) ^ 3)⁻¹ * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100)
            ≤ (1 / 100) * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100) :=
          mul_le_mul_of_nonneg_right h9 (by positivity)
        have h11 : (1 / 100) * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100) * ℓ
            ≤ (1 / 100) * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100)
              * (6 * Real.pi * R) :=
          mul_le_mul_of_nonneg_left hℓle (by positivity)
        have he : (1 / 100) * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100)
              * (6 * Real.pi * R)
            = 3 * Real.pi * Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 := by ring
        have h12 : (1 / 100) * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100)
              * (6 * Real.pi * R)
            ≤ 100 * Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 := by
          rw [he]
          have h14 : (0 : ℝ) ≤ Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 := by positivity
          have h15 : 3 * Real.pi ≤ 100 := by linarith [Real.pi_lt_four]
          nlinarith [h14, h15]
        have h13 : ((2 * Real.pi) ^ 3)⁻¹ * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100)
              * ℓ ≤ (1 / 100) * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * 100) * ℓ :=
          mul_le_mul_of_nonneg_right h10 hℓpos.le
        exact le_trans h13 (le_trans h11 h12)
      -- (ii) the lattice part: `K` lives in `‖zvec m‖ < 3`, so at most `125` points
      have hcard : (K.card : ℝ) ≤ 125 := by
        have hsub : K ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2) := by
          intro m hm
          rw [Fintype.mem_piFinset]
          intro i
          have h2Λ : 2 * Λ = hr * (((HM μ).N : ℝ) / 2) := by
            rw [hrdef, hΛdef, Work.BoseBoxFock.uvRad]; ring
          have hlt2 : ‖latPt hr m‖ < 2 * Λ := ((hKmem m).mp hm).2
          have hN6 : ((HM μ).N : ℝ) ≤ 6 := by exact_mod_cast hNcase
          have h3 : ‖zvec m‖ < 3 := by
            rw [h2Λ, norm_latPt, abs_of_pos hrpos] at hlt2
            nlinarith [hlt2, hrpos]
          have h4 : |((m i : ℤ) : ℝ)| < 3 := lt_of_le_of_lt (coord_le_norm_zvec m i) h3
          rw [abs_lt] at h4
          rw [Finset.mem_Icc]
          constructor
          · have h5 : (-3 : ℤ) < m i := by
              by_contra hcon
              rw [not_lt] at hcon
              have h6 : ((m i : ℤ) : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast hcon
              linarith [h4.1]
            omega
          · have h5 : m i < (3 : ℤ) := by
              by_contra hcon
              rw [not_lt] at hcon
              have h6 : (3 : ℝ) ≤ ((m i : ℤ) : ℝ) := by exact_mod_cast hcon
              linarith [h4.2]
            omega
        have h6 : K.card ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2)).card :=
          Finset.card_le_card hsub
        have h7 : (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2)).card = 125 := by
          rw [Fintype.card_piFinset]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [show (Finset.Icc (-2 : ℤ) 2).card = 5 from by decide]
          norm_num
        have h8 : (K.card : ℝ) ≤ 125 := by
          rw [h7] at h6
          exact_mod_cast h6
        exact h8
      -- each `m ∈ K` has `‖latPt hr m‖ ≥ hr`
      have hhr : ∀ m ∈ K, (‖latPt hr m‖ ^ 2)⁻¹ ≤ (hr ^ 2)⁻¹ := by
        intro m hm
        have hzn : 1 ≤ ‖zvec m‖ := by
          have hm0 : m ≠ 0 := ((hKmem m).mp hm).1
          have hex : ∃ i : Fin 3, m i ≠ 0 := by
            by_contra hcon
            exact hm0 (funext fun i => by
              have := not_exists.mp hcon i
              simpa using not_not.mp this)
          obtain ⟨i, hi⟩ := hex
          have h1 : (1 : ℝ) ≤ |(m i : ℝ)| := by
            have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
            exact_mod_cast h2
          exact le_trans h1 (coord_le_norm_zvec m i)
        rw [norm_latPt, abs_of_pos hrpos]
        have h1 : hr ≤ hr * ‖zvec m‖ := by nlinarith [hzn, hrpos]
        exact inv_anti₀ (by positivity) (by nlinarith [h1, hrpos])
      have hKsumpt : ∀ m ∈ K, |Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2
          ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (‖latPt hr m‖ ^ 2)⁻¹ := by
        intro m hm
        have hΦm := hΦbd (latPt hr m)
        have hzn : 1 ≤ ‖zvec m‖ := by
          have hm0 : m ≠ 0 := ((hKmem m).mp hm).1
          have hex : ∃ i : Fin 3, m i ≠ 0 := by
            by_contra hcon
            exact hm0 (funext fun i => by
              have := not_exists.mp hcon i
              simpa using not_not.mp this)
          obtain ⟨i, hi⟩ := hex
          have h1 : (1 : ℝ) ≤ |(m i : ℝ)| := by
            have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
            exact_mod_cast h2
          exact le_trans h1 (coord_le_norm_zvec m i)
        have hpos : 0 < ‖latPt hr m‖ ^ 2 := by
          have h1 : 0 < |hr| * ‖zvec m‖ := by
            have h2 : 0 < ‖zvec m‖ := lt_of_lt_of_le one_pos hzn
            exact mul_pos (abs_pos.mpr hrpos.ne') h2
          have h3 : ‖latPt hr m‖ = |hr| * ‖zvec m‖ := norm_latPt hr m
          rw [h3]
          exact pow_pos h1 2
        have h4 : (1 : ℝ) ≤ (1 + ‖latPt hr m‖) ^ 4 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
            (by linarith [norm_nonneg (latPt hr m)] : (1 : ℝ) ≤ 1 + ‖latPt hr m‖) 4
        have h5 : |Φ (latPt hr m)| ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 := by
          refine le_trans hΦm ?_
          have h6 : (0 : ℝ) < (1 + ‖latPt hr m‖) ^ 4 :=
            pow_pos (by positivity : (0 : ℝ) < 1 + ‖latPt hr m‖) 4
          rw [div_le_iff₀ h6]
          nlinarith [h4, sq_nonneg (_root_.BoseGases.a v), hCw]
        calc |Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2
            ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) / ‖latPt hr m‖ ^ 2 :=
              div_le_div_of_nonneg_right h5 hpos.le
          _ = (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (‖latPt hr m‖ ^ 2)⁻¹ := by
              rw [div_eq_mul_inv]
      have hKsum : ∑ m ∈ K, |Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2
          ≤ 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹ := by
        refine le_trans (Finset.sum_le_sum hKsumpt) ?_
        calc ∑ m ∈ K, (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (‖latPt hr m‖ ^ 2)⁻¹
            ≤ ∑ m ∈ K, (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹ :=
              Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hhr m hm) (by positivity))
          _ = (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((K.card : ℝ) * (hr ^ 2)⁻¹) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
          _ ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (125 * (hr ^ 2)⁻¹) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹ := by ring
      have hSg' : |Sg| ≤ 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹ := by
        rw [hSgdef]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine le_trans (Finset.sum_le_sum (fun m _ => ?_)) hKsum
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖latPt hr m‖ ^ 2)]
      have hSc' : |Sc| ≤ 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹ := by
        rw [hScdef]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine le_trans (Finset.sum_le_sum ?_) hKsum
        intro m hm
        have hz := hzeta_mem m
        have h2 : |1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
        calc |(1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
                * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2)|
            = |1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m)|
              * (|Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2) := by
              rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖latPt hr m‖ ^ 2)]
          _ ≤ 1 * (|Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = |Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2 := by rw [one_mul]
      -- (iii) the `ℓ`-powers
      have hsr : ℓ ^ (-(3 : ℝ)) * (hr ^ 2)⁻¹ = 1 / (4 * Real.pi ^ 2 * ℓ) := by
        rw [hℓ3, hrdef]
        field_simp
        ring
      have hparts : ∀ x : ℝ, |x| ≤ 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹ →
          ℓ ^ (-(3 : ℝ)) * |x|
            ≤ 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ) := by
        intro x hx
        refine le_trans (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hℓpos.le _)) ?_
        rw [show ℓ ^ (-(3 : ℝ)) * (125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (hr ^ 2)⁻¹)
            = 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (ℓ ^ (-(3 : ℝ)) * (hr ^ 2)⁻¹) from by
              ring]
        rw [hsr]
        rw [show 125 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (1 / (4 * Real.pi ^ 2 * ℓ))
            = 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ) from by ring]
      have hSgB := hparts Sg hSg'
      have hScB := hparts Sc hSc'
      have hAB : |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
            - ℓ ^ (-(3 : ℝ)) * Sg|
          ≤ 100 * Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 / ℓ
            + 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ) := by
        have h1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
              - ℓ ^ (-(3 : ℝ)) * Sg
            = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
              + (-(ℓ ^ (-(3 : ℝ)) * Sg)) := by ring
        rw [h1]
        refine le_trans (abs_add_le _ _) ?_
        have h2 : |-(ℓ ^ (-(3 : ℝ)) * Sg)| = ℓ ^ (-(3 : ℝ)) * |Sg| := by
          rw [abs_neg, abs_mul, abs_of_nonneg (Real.rpow_nonneg hℓpos.le _)]
        rw [h2]
        linarith [hX, hSgB]
      have harith : 100 * Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 / ℓ
            + 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ)
            + 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ)
          ≤ Cval * _root_.BoseGases.a v ^ 2 / ℓ := by
        rw [hCvaldef]
        have h5 : (125 : ℝ) / (4 * Real.pi ^ 2) ≤ 100 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_gt_three]
        have h4 : 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ)
            + 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ)
            ≤ 100 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ := by
          rw [show 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ)
              + 125 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / (8 * Real.pi ^ 2 * ℓ)
              = (125 / (4 * Real.pi ^ 2)) * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ) from by ring]
          rw [show 100 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ
              = 100 * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ) from by ring]
          exact mul_le_mul_of_nonneg_right h5 (by positivity)
        have h6 : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ := by positivity
        have h7 : (0 : ℝ) ≤ 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ := by positivity
        rw [show ((((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
              * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
              + 2 * Cw ^ 2 + 100 * Cw ^ 2 * R + 100 * Cw ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ
          = ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
              * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
              * _root_.BoseGases.a v ^ 2 / ℓ + 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ
              + 100 * Cw ^ 2 * R * _root_.BoseGases.a v ^ 2 / ℓ
              + (100 * Cw ^ 2) * _root_.BoseGases.a v ^ 2 / ℓ from by ring]
        linarith [h4, h6, h7]
      linarith [hAB, hScB, harith]
    · -- ### Case A: `7 ≤ N`
      push_neg at hNcase
      have h7 : 7 ≤ (HM μ).N := by omega
      have hΛhr : hr * Real.sqrt 3 ≤ Λ := by
        have h1 : (7 : ℝ) ≤ ((HM μ).N : ℝ) := by exact_mod_cast h7
        have h2 : Real.sqrt 3 ≤ 7 / 4 := by
          have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
          nlinarith [Real.sqrt_nonneg 3, h3]
        rw [hrdef, hΛdef, Work.BoseBoxFock.uvRad]
        have hc : 0 < 2 * Real.pi / ℓ := by positivity
        have hmid : (2 * Real.pi / ℓ) * Real.sqrt 3 ≤ (2 * Real.pi / ℓ) * (7 / 4) :=
          mul_le_mul_of_nonneg_left h2 hc.le
        have hmid2 : (2 * Real.pi / ℓ) * (7 / 4) ≤ (2 * Real.pi / ℓ) * ((HM μ).N) / 4 := by
          have h5 : (7 : ℝ) / 4 ≤ ((HM μ).N : ℝ) / 4 := by linarith
          have h6 : (2 * Real.pi / ℓ) * ((7 : ℝ) / 4)
              ≤ (2 * Real.pi / ℓ) * (((HM μ).N : ℝ) / 4) := mul_le_mul_of_nonneg_left h5 hc.le
          calc (2 * Real.pi / ℓ) * (7 / 4) = (2 * Real.pi / ℓ) * ((7 : ℝ) / 4) := by norm_num
            _ ≤ (2 * Real.pi / ℓ) * (((HM μ).N : ℝ) / 4) := h6
            _ = (2 * Real.pi / ℓ) * ((HM μ).N) / 4 := by ring
        calc (2 * Real.pi / ℓ) * Real.sqrt 3 ≤ (2 * Real.pi / ℓ) * (7 / 4) := hmid
          _ ≤ (2 * Real.pi / ℓ) * ((HM μ).N) / 4 := hmid2
      -- the lattice-vs-continuum core
      have hcore := Work.BoseRowsFS.LatRiemann.lattice_riemann_core (h := hr) (Λ := Λ)
        (A := Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2)
        (B := 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2)
        (C4 := 4 * (2 * Real.pi) ^ 4 * C4) hrpos hΛpos hΛhr hA0 hB0
        (by positivity : (0 : ℝ) ≤ 4 * (2 * Real.pi) ^ 4 * C4) hΦbd hΦlip hC4b K hKmem
      -- the ζ-correction on the shell
      have hcorrA : ℓ ^ (-(3 : ℝ)) * |Sc| ≤ 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ := by
        rw [hScdef, hℓ3]
        set Kf : Finset (Fin 3 → ℤ) := K.filter (fun m => Λ < ‖latPt hr m‖) with hKfdef
        have hsplitK : (∑ m ∈ K, (1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
              * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2))
            = ∑ m ∈ Kf, (1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
              * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2) := by
          rw [hKfdef]
          refine (Finset.sum_subset (fun m hm => Finset.mem_of_mem_filter m hm) ?_).symm
          intro m hmK hmKf
          have hle : ‖latPt hr m‖ ≤ Λ := by
            by_contra hcon
            exact hmKf (Finset.mem_filter.mpr ⟨hmK, not_le.mp hcon⟩)
          rw [hzeta_one m hle]
          ring
        rw [hsplitK]
        have hpt : ∀ m ∈ Kf,
            |(1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
                * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2)|
              ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹
                * (‖latPt hr m‖ ^ 2)⁻¹ := by
          intro m hm
          have hmK : m ∈ K := Finset.mem_of_mem_filter m hm
          have hlt : Λ < ‖latPt hr m‖ := (Finset.mem_filter.mp hm).2
          have hz := hzeta_mem m
          have hΦm := hΦbd (latPt hr m)
          have hpos : 0 < ‖latPt hr m‖ ^ 2 := pow_pos (lt_of_lt_of_le hΛpos hlt.le) 2
          have h2 : |1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m)| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
          have h4 : (1 + Λ) ^ 4 ≤ (1 + ‖latPt hr m‖) ^ 4 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 4
          have h5 : (1 : ℝ) / (1 + ‖latPt hr m‖) ^ 4 ≤ 1 / (1 + Λ) ^ 4 :=
            one_div_le_one_div_of_le (by positivity) h4
          have h3 : |Φ (latPt hr m)|
              ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 * ((1 + Λ) ^ 4)⁻¹ := by
            calc |Φ (latPt hr m)|
                ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (1 / (1 + ‖latPt hr m‖) ^ 4) := by
                  rw [← div_eq_mul_one_div]
                  exact hΦm
              _ ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * (1 / (1 + Λ) ^ 4) :=
                  mul_le_mul_of_nonneg_left h5 (by positivity)
              _ = Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 * ((1 + Λ) ^ 4)⁻¹ := by
                  rw [one_div]
          calc |(1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
                  * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2)|
              = |1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m)|
                * (|Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2) := by
                rw [abs_mul, abs_div,
                  abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖latPt hr m‖ ^ 2)]
            _ ≤ 1 * (|Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2) := by
                refine mul_le_mul_of_nonneg_right h2 (by positivity)
            _ = |Φ (latPt hr m)| / ‖latPt hr m‖ ^ 2 := by rw [one_mul]
            _ ≤ ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹)
                  / ‖latPt hr m‖ ^ 2 := div_le_div_of_nonneg_right h3 (by positivity)
            _ = (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹
                  * (‖latPt hr m‖ ^ 2)⁻¹ := by rw [div_eq_mul_inv]
        have h1 := le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hpt)
        have h2 : ∑ m ∈ Kf, (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹
              * (‖latPt hr m‖ ^ 2)⁻¹
            = ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹)
              * ∑ m ∈ Kf, (‖latPt hr m‖ ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
        rw [h2] at h1
        have hM1 : 1 ≤ Λ / hr := by
          rw [le_div_iff₀ hrpos]
          nlinarith [hΛhr, (Real.one_le_sqrt).mpr (by norm_num : (1 : ℝ) ≤ 3)]
        have hshell : ∑ m ∈ Kf, (‖latPt hr m‖ ^ 2)⁻¹
            ≤ (hr ^ 2)⁻¹ * (400 * (Λ / hr)) := by
          have hp : ∀ m ∈ Kf, (‖latPt hr m‖ ^ 2)⁻¹
              = (hr ^ 2)⁻¹ * (‖zvec m‖ ^ 2)⁻¹ := by
            intro m _
            rw [norm_latPt, abs_of_pos hrpos, mul_pow, mul_inv]
          rw [Finset.sum_congr rfl hp]
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine shell_lattice_sum hM1 Kf ?_
          intro m hm
          have hmK : m ∈ K := Finset.mem_of_mem_filter m hm
          have hlt : Λ < ‖latPt hr m‖ := (Finset.mem_filter.mp hm).2
          have hlt2 : ‖latPt hr m‖ < 2 * Λ := ((hKmem m).mp hmK).2
          have hnorm : ‖zvec m‖ = ‖latPt hr m‖ / hr := by
            rw [norm_latPt, abs_of_pos hrpos]
            field_simp
          have hlt' : Λ / hr ≤ ‖zvec m‖ := by
            rw [hnorm]
            exact div_le_div_of_nonneg_right hlt.le hrpos.le
          have hlt2' : ‖zvec m‖ < 2 * (Λ / hr) := by
            rw [hnorm]
            have h9 : 2 * (Λ / hr) = (2 * Λ) / hr := by ring
            rw [h9]
            exact div_lt_div_of_pos_right hlt2 hrpos
          exact ⟨hlt', hlt2'⟩
        have harith : (ℓ ^ 3)⁻¹ * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹
              * ((hr ^ 2)⁻¹ * (400 * (Λ / hr))))
            ≤ 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ := by
          have hΛ4 : Λ ^ 4 ≤ (1 + Λ) ^ 4 := by nlinarith [hΛpos]
          have hnum : (200 : ℝ) * Cw ^ 2 * _root_.BoseGases.a v ^ 2 * Λ * ℓ
              ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 * (16 * Real.pi ^ 3 * (1 + Λ) ^ 4) := by
            have h1 : (0 : ℝ) ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 * ℓ := by positivity
            have h2 : 200 * Λ * ℓ ≤ 16 * Real.pi ^ 3 * (1 + Λ) ^ 4 := by
              have h5 : 8 * Real.pi ^ 2 * ℓ ≤ Λ ^ 3 := hΛ3
              have h6 : (200 : ℝ) ≤ 128 * Real.pi ^ 5 := by
                have h7 : (243 : ℝ) ≤ Real.pi ^ 5 := by
                  have h7' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
                    (by linarith [Real.pi_gt_three] : (3 : ℝ) ≤ Real.pi) 5
                  norm_num at h7'
                  exact h7'
                have h8 : (128 : ℝ) * 243 ≤ 128 * Real.pi ^ 5 :=
                  mul_le_mul_of_nonneg_left h7 (by norm_num)
                linarith [h8]
              have h8 : 200 * ℓ ≤ 16 * Real.pi ^ 3 * Λ ^ 3 := by
                calc 200 * ℓ ≤ 128 * Real.pi ^ 5 * ℓ :=
                      mul_le_mul_of_nonneg_right h6 hℓpos.le
                  _ = 16 * Real.pi ^ 3 * (8 * Real.pi ^ 2 * ℓ) := by ring
                  _ ≤ 16 * Real.pi ^ 3 * Λ ^ 3 :=
                      mul_le_mul_of_nonneg_left h5 (by positivity)
              calc 200 * Λ * ℓ = (200 * ℓ) * Λ := by ring
                _ ≤ (16 * Real.pi ^ 3 * Λ ^ 3) * Λ := mul_le_mul_of_nonneg_right h8 hΛpos.le
                _ = 16 * Real.pi ^ 3 * Λ ^ 4 := by ring
                _ ≤ 16 * Real.pi ^ 3 * (1 + Λ) ^ 4 :=
                    mul_le_mul_of_nonneg_left hΛ4 (by positivity)
            nlinarith [h1, h2]
          rw [le_div_iff₀ hℓpos]
          rw [hrdef]
          have hkey : (ℓ ^ 3)⁻¹ * ((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹
                * (((2 * Real.pi / ℓ) ^ 2)⁻¹ * (400 * (Λ / (2 * Real.pi / ℓ))))) * ℓ
              = 25 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 * Λ * ℓ
                / (Real.pi ^ 3 * (1 + Λ) ^ 4) := by
            have h1 : ℓ ≠ 0 := hℓpos.ne'
            have h2 : Real.pi ≠ 0 := Real.pi_ne_zero
            have h3 : (1 + Λ) ≠ 0 := by positivity
            field_simp
            ring
          rw [hkey]
          rw [div_le_iff₀ (by positivity)]
          have hh : 25 * Λ * ℓ ≤ 2 * Real.pi ^ 3 * (1 + Λ) ^ 4 := by
            have hπ : (25 : ℝ) ≤ 16 * Real.pi ^ 5 := by
              have h7 : (243 : ℝ) ≤ Real.pi ^ 5 := by
                have h7' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
                  (by linarith [Real.pi_gt_three] : (3 : ℝ) ≤ Real.pi) 5
                norm_num at h7'
                exact h7'
              linarith [h7]
            have h1 : ℓ ≤ Λ ^ 3 / (8 * Real.pi ^ 2) := by
              rw [le_div_iff₀ (by positivity)]
              linarith [hΛ3]
            calc 25 * Λ * ℓ ≤ 25 * Λ * (Λ ^ 3 / (8 * Real.pi ^ 2)) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = 25 * Λ ^ 4 / (8 * Real.pi ^ 2) := by ring
              _ ≤ 25 * (1 + Λ) ^ 4 / (8 * Real.pi ^ 2) := by
                  refine div_le_div_of_nonneg_right ?_ (by positivity)
                  nlinarith [hΛ4]
              _ ≤ 2 * Real.pi ^ 3 * (1 + Λ) ^ 4 := by
                  rw [div_le_iff₀ (by positivity)]
                  calc 25 * (1 + Λ) ^ 4 ≤ 16 * Real.pi ^ 5 * (1 + Λ) ^ 4 :=
                        mul_le_mul_of_nonneg_right hπ (by positivity)
                    _ = 2 * Real.pi ^ 3 * (1 + Λ) ^ 4 * (8 * Real.pi ^ 2) := by ring
          have hca : (0 : ℝ) ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 := by positivity
          calc 25 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 * Λ * ℓ
              = (Cw ^ 2 * _root_.BoseGases.a v ^ 2) * (25 * Λ * ℓ) := by ring
            _ ≤ (Cw ^ 2 * _root_.BoseGases.a v ^ 2) * (2 * Real.pi ^ 3 * (1 + Λ) ^ 4) :=
                mul_le_mul_of_nonneg_left hh hca
            _ = 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 * (Real.pi ^ 3 * (1 + Λ) ^ 4) := by ring
        calc (ℓ ^ 3)⁻¹ * |∑ m ∈ Kf, (1 - Work.BoseBoxFock.uvCut fu Λ (latPt hr m))
                * (Φ (latPt hr m) / ‖latPt hr m‖ ^ 2)|
            ≤ (ℓ ^ 3)⁻¹ * (((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹)
                * ∑ m ∈ Kf, (‖latPt hr m‖ ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (ℓ ^ 3)⁻¹ * (((Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2) * ((1 + Λ) ^ 4)⁻¹)
                * ((hr ^ 2)⁻¹ * (400 * (Λ / hr)))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hshell (by positivity)
          _ ≤ 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ := harith
      -- ### Case A assembly: `hcore` bounds the continuum part
      have e1 : (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
          = ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
                * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / 2 / ‖p‖ ^ 2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        simp only [hΦdef] <;> ring
      have e2 : hr ^ 3 * Sg
          = ∑ m ∈ K, hr ^ 3 *
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (latPt hr m)
                * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (latPt hr m) / 2)
              / ‖latPt hr m‖ ^ 2 := by
        rw [hSgdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        simp only [hΦdef] <;> ring
      have hcp : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := inv_pos.mpr (by positivity)
      have hcore' : |(∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2) - hr ^ 3 * Sg| ≤
          1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4) *
            (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2) *
            (hr + 1 / (1 + Λ) ^ 3) := by
        simpa only [e1, e2] using hcore
      have hkeyA : hr + 1 / (1 + Λ) ^ 3 ≤ (2 * Real.pi + 1 / (8 * Real.pi ^ 2)) / ℓ := by
        have h2' : 1 / (1 + Λ) ^ 3 ≤ (1 / (8 * Real.pi ^ 2)) / ℓ := by
          rw [show (1 / (8 * Real.pi ^ 2)) / ℓ = 1 / (8 * Real.pi ^ 2 * ℓ) from by ring]
          exact hT
        rw [show (2 * Real.pi + 1 / (8 * Real.pi ^ 2)) / ℓ
            = 2 * Real.pi / ℓ + (1 / (8 * Real.pi ^ 2)) / ℓ from by ring, hrdef]
        linarith [h2']
      have hK0 : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
          * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2) := by
        have h1 : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
        have h3 : (0 : ℝ) ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2
            + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2 := by positivity
        positivity
      have hbig : ((2 * Real.pi) ^ 3)⁻¹ * (1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4) *
            (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2) *
            (hr + 1 / (1 + Λ) ^ 3))
          ≤ ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ := by
        have e1 : ((2 * Real.pi) ^ 3)⁻¹ * (1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4) *
            (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2) *
            (hr + 1 / (1 + Λ) ^ 3))
            = (((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2))
            * (hr + 1 / (1 + Λ) ^ 3) := by ring
        have e2 : ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ
            = (((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2))
            * ((2 * Real.pi + 1 / (8 * Real.pi ^ 2)) / ℓ) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left hkeyA hK0
      have hcont : |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
            - ℓ ^ (-(3 : ℝ)) * Sg|
          ≤ ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ := by
        calc |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
              - ℓ ^ (-(3 : ℝ)) * Sg|
            = |((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
              - (((2 * Real.pi) ^ 3)⁻¹ * hr ^ 3) * Sg| := by rw [hr3, hℓ3]
          _ = ((2 * Real.pi) ^ 3)⁻¹
              * |(∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2) - hr ^ 3 * Sg| := by
              have e : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2)
                  - (((2 * Real.pi) ^ 3)⁻¹ * hr ^ 3) * Sg
                  = ((2 * Real.pi) ^ 3)⁻¹
                    * ((∫ p : EuclideanSpace ℝ (Fin 3), Φ p / ‖p‖ ^ 2) - hr ^ 3 * Sg) := by ring
              rw [e, abs_mul, abs_of_pos hcp]
          _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4) *
              (Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 + 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2) *
              (hr + 1 / (1 + Λ) ^ 3)) := mul_le_mul_of_nonneg_left hcore' hcp.le
          _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ := hbig
      have hstep2 : ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 / ℓ + 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ
          ≤ Cval * _root_.BoseGases.a v ^ 2 / ℓ := by
        rw [hCvaldef, le_div_iff₀ hℓpos]
        have e : (((((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
              * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
              * _root_.BoseGases.a v ^ 2 / ℓ
              + 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 / ℓ))) * ℓ
            = ((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
              * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
              * _root_.BoseGases.a v ^ 2 + 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2 := by
          field_simp
        rw [e]
        have hca : (0 : ℝ) ≤ (100 * Cw ^ 2 * R + 100 * Cw ^ 2) * _root_.BoseGases.a v ^ 2 :=
          by positivity
        have e2 : ((((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2)) + 2 * Cw ^ 2
            + 100 * Cw ^ 2 * R + 100 * Cw ^ 2)) * _root_.BoseGases.a v ^ 2
            = ((((2 * Real.pi) ^ 3)⁻¹ * 1000 * (1 + 4 * (2 * Real.pi) ^ 4 * C4)
            * (Cw ^ 2 / 2 + 8 * Real.pi * R * Cw) * (2 * Real.pi + 1 / (8 * Real.pi ^ 2))
            * _root_.BoseGases.a v ^ 2 + 2 * Cw ^ 2 * _root_.BoseGases.a v ^ 2)
            + (100 * Cw ^ 2 * R + 100 * Cw ^ 2) * _root_.BoseGases.a v ^ 2) := by ring
        rw [e2]
        linarith [hca]
      exact le_trans (add_le_add hcont hcorrA) hstep2
  rw [hell, haScat, hom]
  exact hmain

end Work.BoseRowsFS

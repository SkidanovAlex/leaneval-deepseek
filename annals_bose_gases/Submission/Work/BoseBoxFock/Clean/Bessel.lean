import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB7AK.W1low.chat_sub_le
import Submission.Work.BoseBoxFock.Clean.ChiSq
import Submission.Work.BoseBoxFock.KafzSym
import Submission.Work.BoseBoxFock.cfock_frame_bessel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/Clean/Bessel.lean`

**Why this module exists.**  The honest Bessel bundle `honestEnvBesselCorrected`
(`Submission/Work/BoseBoxFock/honestEnvBessel.lean`) is the χ̂-Bessel input of the honest
`model_kafz` floor, but its module imports
`Submission.Work.BoseBoxFock.sum_hatChiSq_sq_le`, whose module imports
`Submission.Work.BoseFixR.FarKernelRowsB` → `GateHonest`/`RB5FSFixAux` — two modules that
(after the interface change `F9`, `CloseCond` → `CloseCondFS`) no longer compile, so the whole
cone is unloadable.

This file is a **verbatim copy** of that module (`§1`–`§8`: everything up to and including
`honestEnvBesselCorrected`; the false requested statement `honestEnvBessel` of `§9` is not
copied), with the `sum_hatChiSq_sq_le` import replaced by the copy
`Work.BoseBoxFock.Clean.ChiSq`, re-scoped to `Work.BoseBoxFock.Clean`.  Nothing new is proved
here.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.Clean

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The corpus `chat` identifications

`Work.BoseFixR.chat (χ_ℓ) p = ℓ³ χ̂(ℓ p)` (`ℓ > 0`): the normalised `chat`-transform of the
scaled bump is the corpus `χ̂` at the scaled momentum.  (This is
`Work.BoseGateFS.chat_chiFun_eq`, re-proved here from the two lighter modules
`chat_sub_le` and `BoxChiScaling`.) -/

lemma integrable_chiFun (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z) :=
  (Submission.BoseGases.chiScale_continuous ℓ).integrable_of_hasCompactSupport
    (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ))

lemma integrable_chiFun_sq (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z ^ 2) := by
  have hcs : HasCompactSupport
      (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chiFun ℓ z ^ 2) := by
    refine (Submission.BoseGases.chiScale_hasCompactSupport (ℓ := ℓ) (ne_of_gt hℓ)).mono ?_
    intro x hx
    exact Function.mem_support.mpr
      (fun h => Function.mem_support.mp hx (by simp [Work.BoseFixR.chiFun, h]))
  exact ((Submission.BoseGases.chiScale_continuous ℓ).pow 2).integrable_of_hasCompactSupport hcs

theorem chat_chiFun_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (Work.BoseFixR.chiFun ℓ) p
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos (integrable_chiFun ℓ hℓ) p]
  exact Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ p

theorem chat_chiFun_sq_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (fun z => Work.BoseFixR.chiFun ℓ z ^ 2) q
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChiSq (ℓ • q) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos (integrable_chiFun_sq ℓ hℓ) q]
  exact Work.BoseB4.BoxData.integral_chiLam_sq_mul_cos Work.BoseK15.corpusBox hℓ q

/-! ## 2. The kernels of the honest environment -/

/-- **The `χ̂`-pin at the honest family.**  For a box side `ℓ = sideAt μ (a v) > 0`, the
honest environment's `χ̂`-kernel at the lattice label `k` is the corpus `χ̂` at the lattice
momentum `vec (labVec N k) = ℓ • kmomLab ℓ N k`. -/
theorem honest_hatChi_eq (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    (μ : ℝ) (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.hatChi k
      = Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k)) := by
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [ellH, if_pos hℓ]
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, hell]
  change Work.BoseFixR.chat (Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) /
      Work.BoseFixR.chat
        (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z ^ 2) 0
      = Work.BoseK15.corpusBox.hatChi (vec (labVec (HM μ).N k))
  rw [chat_chiFun_eq (Work.BoseBox.sideAt μ (BoseGases.a v)) hℓ
        (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k),
    chat_chiFun_sq_eq (Work.BoseBox.sideAt μ (BoseGases.a v)) hℓ 0,
    smul_zero, Work.BoseB4.BoxData.hatChiSq_zero, mul_one,
    smul_kmomLab (ne_of_gt hℓ) (HM μ).N k]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 3 (ne_of_gt hℓ))]

/-- **The `χ̂²`-pin at the honest family.**  Same statement for the `χ²`-kernel (the
commutator kernel diagonal). -/
theorem honest_hatChiSq_eq (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    (μ : ℝ) (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.hatChiSq k
      = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k)) := by
  have hell : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [ellH, if_pos hℓ]
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, hell]
  change Work.BoseFixR.chat
        (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z ^ 2)
        (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) /
      Work.BoseFixR.chat
        (fun z => Work.BoseFixR.chiFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z ^ 2) 0
      = Work.BoseK15.corpusBox.hatChiSq (vec (labVec (HM μ).N k))
  rw [chat_chiFun_sq_eq (Work.BoseBox.sideAt μ (BoseGases.a v)) hℓ
        (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k),
    chat_chiFun_sq_eq (Work.BoseBox.sideAt μ (BoseGases.a v)) hℓ 0,
    smul_zero, Work.BoseB4.BoxData.hatChiSq_zero, mul_one,
    smul_kmomLab (ne_of_gt hℓ) (HM μ).N k]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 3 (ne_of_gt hℓ))]

/-! ## 3. The degenerate box side `ℓ = 0`

`sideAt μ (a v) = K_ℓ (μ a v)^{-1/2}` is nonnegative for *every* `μ` (for `μ a v < 0`
Mathlib's real power gives `(μ a v)^{-1/2} = exp(...)·cos(-π/2) = 0`), so the only
non-positive value is `0`.  At `ℓ = 0` the scaled bump `χ_ℓ = χ(·/ℓ)` degenerates to the
constant `χ(0)`, whose `chat`-transform vanishes (the integrand has constant modulus on
`ℝ³`), so both kernels of the honest environment vanish. -/

lemma rpow_neg_half_nonneg (x : ℝ) : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.rpow_def_of_neg h]
    have h1 : -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) := by ring
    rw [h1, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h
    rw [Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)]
  · exact Real.rpow_nonneg h.le _

lemma fsXp_neg_three_half_nonneg (t : ℝ) : 0 ≤ Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) := by
  rw [Work.BoseBox.fsXp]
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.rpow_def_of_neg h]
    refine mul_nonneg (Real.exp_nonneg _) (Real.cos_nonneg_of_mem_Icc ?_)
    have hb : |((-(3 / 2 : ℝ)) / 323) * Real.pi| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      have h1 : |( (-(3 / 2 : ℝ)) / 323 : ℝ)| ≤ 1 / 2 := by norm_num
      calc |( (-(3 / 2 : ℝ)) / 323 : ℝ)| * Real.pi ≤ (1 / 2) * Real.pi :=
            mul_le_mul_of_nonneg_right h1 Real.pi_pos.le
        _ = Real.pi / 2 := by ring
    exact abs_le.mp hb
  · subst h
    rw [Real.zero_rpow (by norm_num : (-(3 / 2 : ℝ) / 323) ≠ 0)]
  · exact Real.rpow_nonneg h.le _

/-- `sideAt μ a ≥ 0` for all `μ, a`. -/
lemma sideAt_nonneg (μ a : ℝ) : 0 ≤ Work.BoseBox.sideAt μ a := by
  rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
    Work.BoseBox.fsParams]
  exact mul_nonneg (fsXp_neg_three_half_nonneg (μ * a ^ 3)) (rpow_neg_half_nonneg (μ * a))

/-- `ℝ³` carries infinite Lebesgue measure, so a nonzero constant is not integrable. -/
lemma not_integrable_const_real {r : ℝ} (hr : r ≠ 0) :
    ¬ Integrable (fun _ : EuclideanSpace ℝ (Fin 3) => r) := by
  intro h
  have hfin := h.2
  unfold HasFiniteIntegral at hfin
  rw [lintegral_const, MeasureTheory.measure_univ_of_isAddLeftInvariant volume] at hfin
  rw [ENNReal.mul_top] at hfin
  · exact absurd hfin (lt_irrefl _)
  · simp [hr]

/-- `chat` of a constant vanishes: the integrand has constant modulus `|c|` on `ℝ³`. -/
lemma chat_const (c : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (fun _ : EuclideanSpace ℝ (Fin 3) => c) p = 0 := by
  rw [Work.BoseFixR.chat]
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [Submission.BoseGases.kinFT]
    simp
  have hni : ¬ Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((c : ℝ) : ℂ)) := by
    intro h
    have h2 : Integrable (fun _ : EuclideanSpace ℝ (Fin 3) => ‖((c : ℝ) : ℂ)‖) := by
      refine h.norm.congr (Filter.Eventually.of_forall fun y => ?_)
      show ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((c : ℝ) : ℂ)‖ = ‖((c : ℝ) : ℂ)‖
      rw [norm_mul, Complex.norm_exp]
      simp
    refine (not_integrable_const_real (r := ‖((c : ℝ) : ℂ)‖) ?_) h2
    exact norm_ne_zero_iff.mpr (by simpa using hc)
  rw [Submission.BoseGases.kinFT, integral_undef hni]
  simp

/-- At `ℓ = 0` the scaled bump `χ_ℓ` is the constant `χ(0)`. -/
lemma chiFun_zero : Work.BoseFixR.chiFun 0
    = fun _ : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi 0 := by
  funext x
  simp [Work.BoseFixR.chiFun, Submission.BoseGases.chiScale]

/-- The `χ̂`-kernel of the honest environment vanishes when the box side is `0`. -/
theorem honest_hatChi_eq_zero (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    (μ : ℝ) (h0 : Work.BoseBox.sideAt μ (BoseGases.a v) = 0) (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.hatChi k = 0 := by
  have hell : ellH v μ = 1 := by
    rw [ellH, h0, if_neg (lt_irrefl (0 : ℝ))]
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, hell, h0]
  change Work.BoseFixR.chat (Work.BoseFixR.chiFun 0) (kmomLab 1 (HM μ).N k) /
      Work.BoseFixR.chat (fun z => Work.BoseFixR.chiFun 0 z ^ 2) 0 = 0
  rw [chiFun_zero, chat_const, chat_const, div_zero]

/-- The `χ̂²`-kernel of the honest environment vanishes when the box side is `0`. -/
theorem honest_hatChiSq_eq_zero (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    (μ : ℝ) (h0 : Work.BoseBox.sideAt μ (BoseGases.a v) = 0) (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.hatChiSq k = 0 := by
  have hell : ellH v μ = 1 := by
    rw [ellH, h0, if_neg (lt_irrefl (0 : ℝ))]
  simp only [HonestBoxFam, KzEnvHon, Work.BoseFixR.KzEnvFs, hell, h0]
  change Work.BoseFixR.chat (fun z => Work.BoseFixR.chiFun 0 z ^ 2)
        (kmomLab 1 (HM μ).N k) /
      Work.BoseFixR.chat (fun z => Work.BoseFixR.chiFun 0 z ^ 2) 0 = 0
  rw [chiFun_zero, chat_const, chat_const, div_zero]

/-! ## 4. The true first conjunct: `Σ_k χ̂(k)² ≤ 1` at the honest model -/

/-- **The first conjunct of `honestEnvBessel`, proved.**  `Σ_k (χ̂ k)² ≤ 1` at the honest
box model, for every `μ`: for `ℓ > 0` this is the lattice Parseval bound
`sum_hatChi_sq_le` transported by `honest_hatChi_eq`; for `ℓ = 0` every term vanishes. -/
theorem honest_hatChi_sum_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∑ k : Lab (HM μ).N, (HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2 ≤ 1 := by
  change ∑ k : (HonestBoxFam v h fc fu HM μ).Mode,
      (HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2 ≤ 1
  rcases eq_or_lt_of_le (sideAt_nonneg μ (BoseGases.a v)) with h0 | hpos
  · have hcongr : ∀ k : (HonestBoxFam v h fc fu HM μ).Mode,
        (HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2 = 0 :=
      fun k => by
        rw [honest_hatChi_eq_zero v h fc fu HM μ h0.symm k]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
    simp
  · have hcongr : ∀ k : (HonestBoxFam v h fc fu HM μ).Mode,
        (HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2
          = (Work.BoseK15.corpusBox.hatChi
              (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 :=
      fun k => by rw [honest_hatChi_eq v h fc fu HM μ hpos k]
    rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
    exact sum_hatChi_sq_le (HM μ).N

/-! ## 5. The honest frame bound and the true third conjunct

`frame_int_bound` (proved in `bessel_honest`) is the lattice frame bound of the honest
χ-modes; `frame_of_synthesis` turns it into the quadratic-form frame bound `hS` of the
family `(HM μ).f`, which is the hypothesis of the complex Bessel inequality
`cfock_frame_bessel`. -/

/-- **The honest frame bound**: `Σ_k ⟪f_k, w⟫² ≤ (48/π)‖w‖²` for the χ-mode coordinates
of the honest box model. -/
theorem honest_frame_bound (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ w : Fin (HM μ).m → ℝ,
      ∑ k : Lab (HM μ).N, (Work.BoseB4.gram ((HM μ).f k) w) ^ 2
        ≤ (48 / Real.pi) * ∑ l : Fin (HM μ).m, (w l) ^ 2 := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hgram : ∀ k k' : Lab (HM μ).N,
      Work.BoseB4.gram ((HM μ).f k) ((HM μ).f k')
        = Work.BoseK15.corpusBox.hatChiSq
            (Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N k'))
          - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k))
            * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k')) := by
    intro k k'
    rw [(HM μ).hf k k', Work.BoseB7.ccrKernel,
      smul_kmomLab_sub (ne_of_gt hℓ) (HM μ).N k k', smul_kmomLab (ne_of_gt hℓ) (HM μ).N k,
      smul_kmomLab (ne_of_gt hℓ) (HM μ).N k']
  refine frame_of_synthesis (HM μ).f (48 / Real.pi) (by positivity) ?_
  intro c
  rw [(Work.BoseB4.gram_quadForm_eq_sum_sq (HM μ).f c).symm]
  have hcongr : ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        c i * Work.BoseB4.gram ((HM μ).f i) ((HM μ).f j) * c j
      = ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, c i * c j *
          (Work.BoseK15.corpusBox.hatChiSq
              (Work.BoseB4.vec (labVec (HM μ).N i - labVec (HM μ).N j))
            - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N i))
              * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N j))) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hgram i j]
    ring
  rw [hcongr]
  exact frame_int_bound (HM μ).N c

/-! ## 6. The reduction of the (false) second conjunct

Conjunct 2 of the requested statement is *exactly* the lattice sum of `χ̂²²` over the
nonzero labels of the cube, evaluated at the corpus `χ`: the `χ̂²`-kernel of the honest
environment is the corpus one (`honest_hatChiSq_eq`).  This is the identity that makes the
falsity of conjunct 2 a statement about the corpus bump alone. -/

/-- **The second conjunct is the corpus lattice sum.**  For `ℓ > 0`,
`Σ_{k ≠ 0} (χ̂² k)²` at the honest model is `Σ_{k ≠ 0} corpusBox.hatChiSq(2π·labVec k)²`. -/
theorem honest_excited_hatChiSq_eq (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2)
      = ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 := by
  change ∑ k ∈ Work.BoseB7.excited (HonestBoxFam v h fc fu HM μ).Mode,
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2
      = ∑ k ∈ Work.BoseB7.excited (HonestBoxFam v h fc fu HM μ).Mode,
          (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2
  exact Finset.sum_congr rfl fun k _ => by rw [honest_hatChiSq_eq v h fc fu HM μ hpos k]

/-- **The corrected second conjunct**: `Σ_{k ≠ 0} (χ̂² k)² ≤ 48/π` at the honest box model,
for every `μ`.  The constant is the sharp one available from the corpus normalisation
(`∫χ⁴ ≤ χ(0)² ≤ 48/π`); `1` is not, see the header. -/
theorem honest_excited_hatChiSq_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2 ≤ 48 / Real.pi := by
  change ∑ k ∈ Work.BoseB7.excited (HonestBoxFam v h fc fu HM μ).Mode,
      (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2 ≤ 48 / Real.pi
  rcases eq_or_lt_of_le (sideAt_nonneg μ (BoseGases.a v)) with h0 | hpos
  · have hcongr : ∀ k : (HonestBoxFam v h fc fu HM μ).Mode,
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2 = 0 :=
      fun k => by
        rw [honest_hatChiSq_eq_zero v h fc fu HM μ h0.symm k]
        ring
    rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
    simp only [Finset.sum_const_zero]
    positivity
  · have hcongr : ∀ k : (HonestBoxFam v h fc fu HM μ).Mode,
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2
          = (Work.BoseK15.corpusBox.hatChiSq
              (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 :=
      fun k => by rw [honest_hatChiSq_eq v h fc fu HM μ hpos k]
    rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun k _ _ => sq_nonneg _)) ?_
    exact sum_hatChiSq_sq_le (HM μ).N

/-! ## 7. The true third conjunct -/

/-- **The third conjunct of `honestEnvBessel`, proved**: the χ-number operator is
dominated by `48/π` times the excited number operator on the spectator Fock space.  It is
the complex spectator Bessel inequality `cfock_frame_bessel` (a sibling `request_lemma`)
fed with the honest frame bound `honest_frame_bound`. -/
theorem honest_nPlusChi_le (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
      (inner ℂ x (nPlusChi (m := (HM μ).m) (HM μ).f x)).re
        ≤ (48 / Real.pi) * (inner ℂ x (nPlusC (m := (HM μ).m) x)).re := by
  intro x
  have hb := cfock_frame_bessel ((HM μ).f) (48 / Real.pi) (by positivity)
    (honest_frame_bound v h fc fu HM μ) x
  simpa only [nPlusChi] using hb

/-! ## 8. The corrected bundle

The requested statement with the *false* second conjunct replaced by the sharp bound
`48/π` (the second conjunct with `1` fails for every `N ≥ 1`, see the header). -/

/-- **The corrected `honestEnvBessel`**: conjunct 1 unchanged, conjunct 2 with the sharp
constant `48/π` instead of `1`, conjunct 3 unchanged. -/
theorem honestEnvBesselCorrected (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ((∑ k : Lab (HM μ).N, (HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2) ≤ 1)
    ∧ ((∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        (HonestBoxFam v h fc fu HM μ).E.hatChiSq k ^ 2) ≤ 48 / Real.pi)
    ∧ (∀ x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
        (inner ℂ x (nPlusChi (m := (HM μ).m) (HM μ).f x)).re
          ≤ (48 / Real.pi) * (inner ℂ x (nPlusC (m := (HM μ).m) x)).re) :=
  ⟨honest_hatChi_sum_le v h fc fu HM μ,
   honest_excited_hatChiSq_le v h fc fu HM μ,
   honest_nPlusChi_le v h fc fu HM μ⟩


end Work.BoseBoxFock.Clean

import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.ChDpieceAsm` — the arithmetic and assembly of the `(D)`-slot

The `(D)`-slot piece `Work.BoseBoxFock.PCFU.chDslot_le` is closed in two steps:

1. **kernel bound** (the analytic part, `chDkernel_sup_le`): for every admissible `μ` in the
   regime and every `N` above a threshold `T μ`, the `z`-kernel of the slot is bounded by
   `θ(μ) = chDA v K0 μ / ℓ³`;
2. **assembly** (this file): the state-side reduction `chDslot_le_of_kernel` converts the kernel
   bound into `‖chDslot‖ ≤ chDA v K0 μ · normB`, and the budget identity `chDA_budget` shows that
   `chDA v K0` is exactly the largest function the `SlotPiece` budget admits, so the piece
   `SlotPiece v h fc fu R J ε₀ chDslot` follows.

`chDA v K0 μ := if 0 < μ then K0·(a v)/(8μℓ³(1+ℓ⁻³)) else 0`, `ℓ = ellH v μ`: then

   2ℓ⁻³·(4μ²ℓ⁶(1+ℓ⁻³)·chDA v K0 μ) = K0·(μ·a v)       (μ > 0),

i.e. the budget clause of `SlotPiece` holds with **equality**.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The constant of the `(D)`-piece: the largest function allowed by the `SlotPiece` budget,
`A μ = K0·(a v)/(8·μ·ℓ³·(1+ℓ⁻³))` for `μ > 0` (`ℓ = ellH v μ`), and `0` for `μ ≤ 0`. -/
noncomputable def chDA (v : E3 → ℝ) (K0 : ℝ) (μ : ℝ) : ℝ :=
  if 0 < μ then K0 * BoseGases.a v / (8 * μ * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ)))
  else 0

lemma chDA_of_pos {v : E3 → ℝ} {K0 μ : ℝ} (hμ : 0 < μ) :
    chDA v K0 μ
      = K0 * BoseGases.a v / (8 * μ * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ))) := by
  rw [chDA, if_pos hμ]

lemma chDA_nonneg {v : E3 → ℝ} (hav : 0 < BoseGases.a v) {K0 : ℝ} (hK0 : 0 ≤ K0) (μ : ℝ) :
    0 ≤ chDA v K0 μ := by
  rw [chDA]
  split_ifs with hμ
  · have hℓ : 0 < ellH v μ := ellH_pos v μ
    have h3 : (0 : ℝ) < (ellH v μ) ^ 3 := by positivity
    have h3i : (0 : ℝ) < (ellH v μ) ^ (-3 : ℤ) := by positivity
    positivity
  · exact le_refl 0

/-- **The budget identity**: `chDA v K0` saturates the `SlotPiece` budget with the multiplicative
constant `K0`. -/
theorem chDA_budget {v : E3 → ℝ} {K0 μ : ℝ} (hμ : 0 < μ) :
    2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * chDA v K0 μ)
      = K0 * (μ * BoseGases.a v) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  rw [chDA_of_pos hμ]
  have h3 : ((ellH v μ) ^ 3) ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  have h3i : (ellH v μ) ^ (-3 : ℤ) = ((ellH v μ) ^ 3)⁻¹ := by
    rw [zpow_neg]
    simp
  have h31 : (1 + ((ellH v μ) ^ 3)⁻¹) ≠ 0 := by
    have : (0 : ℝ) < ((ellH v μ) ^ 3)⁻¹ := by positivity
    linarith
  have h6 : (ellH v μ) ^ 6 = ((ellH v μ) ^ 3) ^ 2 := by ring
  rw [h3i, h6]
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  field_simp
  ring

/-! ## The assembly -/

/-- **The `(D)`-piece from the kernel bound.**  If for every admissible `μ` in the regime and every
`N ≥ T μ` the `z`-kernel of the slot is bounded by `chDA v K0 μ / ℓ³`, and if the state-side
reduction `hred` (the content of `chDslot_le_of_kernel`) is available, then
`SlotPiece v h fc fu R J ε₀ chDslot` holds with the constant `K0` and the threshold `T`. -/
theorem chDslot_le_of_kernelBound
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) {K0 : ℝ} (hK0 : 0 < K0) {T : ℝ → ℕ}
    (hred : ∀ (μ : ℝ), 0 < μ → ∀ (N n : ℕ), ∀ (i j : Fin n), i ≠ j →
      ∀ (Φ : Submission.BoseGases.X n → ℝ),
        MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2)
            (Submission.BoseGases.abox n (ellH v μ)) →
        ∀ {K : ℝ}, 0 ≤ K →
          (∀ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ)) : ℂ)
              * (KχfrU v h μ fu N z - chDC h (ellH v μ) z)‖ ≤ K) →
          ‖chDslot v h fc fu μ N i j (boxRestrictR (ellH v μ) Φ)‖
            ≤ K * (ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ n Φ)
    (hk : ∀ (μ : ℝ), 0 < μ → Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ ellH v μ * Submission.BoseGases.chiR0 → 4 * R ≤ ellH v μ →
        ∀ (N : ℕ), T μ ≤ N → ∀ z : E3,
          ‖(((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ)) : ℂ)
            * (KχfrU v h μ fu N z - chDC h (ellH v μ) z)‖
            ≤ chDA v K0 μ / (ellH v μ) ^ 3) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => chDslot v h fc fu μ N i j Θ) := by
  refine ⟨K0, hK0, chDA v K0, T, fun μ => chDA_nonneg hav hK0.le μ, ?_, ?_⟩
  · intro μ hμ
    rw [chDA_budget (v := v) (K0 := K0) hμ]
  · intro Nmin _hNmin hT hreg HM hMono μ hAdm _hKBs n Φ _hn hnormB _hlowB _hspec i j hij
    have hμ : 0 < μ := hAdm.1
    have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
    have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
      rw [ellH, if_pos hside]
    have hN : T μ ≤ (HM μ).N := le_trans (hT μ) (hMono μ)
    have hz : ∀ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ)) : ℂ)
        * (KχfrU v h μ fu (HM μ).N z - chDC h (ellH v μ) z)‖
          ≤ chDA v K0 μ / (ellH v μ) ^ 3 :=
      hk μ hμ hAdm (hreg μ hAdm).1 (hreg μ hAdm).2 (HM μ).N hN
    have hcont : Continuous (fun x : Submission.BoseGases.X n => ((Φ.1 x : ℝ)) ^ 2) :=
      (Φ.contDiff.continuous).pow 2
    have hΦ : MeasureTheory.IntegrableOn
        (fun x => ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
        (Submission.BoseGases.abox n (ellH v μ)) :=
      hcont.continuousOn.integrableOn_compact
        (Submission.BoseGases.abox_compact n (ellH_pos v μ))
    have hK0' : 0 ≤ chDA v K0 μ / (ellH v μ) ^ 3 :=
      div_nonneg (chDA_nonneg hav hK0.le μ) (pow_nonneg (ellH_pos v μ).le 3)
    have hmain := hred μ hμ (HM μ).N n i j hij (Φ : Submission.BoseGases.X n → ℝ) hΦ hK0' hz
    calc ‖chDslot v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
        ≤ (chDA v K0 μ / (ellH v μ) ^ 3) * (ellH v μ) ^ 3
            * Work.BoseBoxFix.normB v μ n Φ := hmain
      _ = chDA v K0 μ * Work.BoseBoxFix.normB v μ n Φ := by
          rw [div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt (ellH_pos v μ)))]


/-! ## The arithmetic of the kernel bound -/

/-- **The arithmetic of the `(D)`-kernel bound.**  If `μ ≤ M₁` and `μ·ℓ⁻³ ≤ M₂` on the admissible
range, then `chDA v K0` with `K0 := 512·π·CA·R⁶·(M₁+M₂) + 1` dominates the alias term
`2·CA·(R/ℓ)⁶·16πa`:

    2·CA·(R/ℓ)^6·(16π a v) ≤ chDA v K0 μ / ℓ³ .

(Cross-multiplying by `8·μ·ℓ⁶·(1+ℓ⁻³)`, the two sides become
`256π·CA·R⁶·μ·(1+ℓ⁻³)·a v` and `K0·a v`.) -/
theorem chDA_arith {v : E3 → ℝ} {R CA M1 M2 : ℝ} (hR : 0 < R) (hav : 0 < BoseGases.a v)
    (hCA : 0 ≤ CA) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ {μ : ℝ} (hμ : 0 < μ), μ ≤ M1 →
      μ * (ellH v μ) ^ (-3 : ℤ) ≤ M2 →
        2 * CA * (R / ellH v μ) ^ 6 * (16 * Real.pi * BoseGases.a v)
          ≤ chDA v K0 μ / (ellH v μ) ^ 3 := by
  refine ⟨512 * Real.pi * CA * R ^ 6 * (M1 + M2) + 1, by positivity, ?_⟩
  intro μ hμ h1 h2
  have ha : 0 < BoseGases.a v := hav
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hℓ3 : (0 : ℝ) < (ellH v μ) ^ 3 := by positivity
  have h3i : (ellH v μ) ^ (-3 : ℤ) = ((ellH v μ) ^ 3)⁻¹ := by rw [zpow_neg]; simp
  have hden : 0 < 8 * μ * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ)) * (ellH v μ) ^ 3 := by
    have : (0 : ℝ) < 1 + (ellH v μ) ^ (-3 : ℤ) := by
      have := (zpow_pos hℓ (-3 : ℤ))
      linarith
    positivity
  rw [chDA_of_pos hμ, div_div, le_div_iff₀ hden]
  have hkey : 2 * CA * (R / ellH v μ) ^ 6 * (16 * Real.pi * BoseGases.a v)
      * (8 * μ * (ellH v μ) ^ 3 * (1 + (ellH v μ) ^ (-3 : ℤ)) * (ellH v μ) ^ 3)
      = 256 * Real.pi * CA * R ^ 6 * (μ * (1 + (ellH v μ) ^ (-3 : ℤ))) * BoseGases.a v := by
    rw [h3i, div_pow]
    have h3n : ((ellH v μ) ^ 3) ≠ 0 := ne_of_gt hℓ3
    have h3in : (1 + ((ellH v μ) ^ 3)⁻¹) ≠ 0 := by positivity
    field_simp
    ring
  rw [hkey]
  have hle : μ * (1 + (ellH v μ) ^ (-3 : ℤ)) ≤ M1 + M2 := by
    have : μ * (1 + (ellH v μ) ^ (-3 : ℤ))
        = μ + μ * (ellH v μ) ^ (-3 : ℤ) := by ring
    rw [this]
    linarith
  have hcoef : (0 : ℝ) ≤ 256 * Real.pi * CA * R ^ 6 * BoseGases.a v := by positivity
  have hcoef2 : (0 : ℝ) ≤ 256 * Real.pi * CA * R ^ 6 * BoseGases.a v * (M1 + M2) := by positivity
  nlinarith [hle, hcoef, hav]



/-! ## The glue: the two error pieces of the kernel -/

set_option maxHeartbeats 1600000 in
/-- **The kernel bound from the two error pieces.**  With `χ := corpusBox.chiLam ℓ`, if

* the truncation piece factors through the Fourier series of `chDpoisson_E` (`hP2`) and
  `chat W1fun` is `≤ θ₁` beyond the cut-off radius `uvRad ℓ N` (`hS`), while the total lattice mass
  of the bump is `≤ Tailmax` (`hTail`, plus summability `hSum`),
* the alias piece obeys the face-layer bound `Kalias` (`hAlias`, plus summability of the `d`-family
  `halSum`),
* `KχfrU − chDC` splits as the truncation sum plus the (`d ≠ 0`) alias sum (`hσ`),

then `‖χ(z)·(KχfrU − chDC)(z)‖ ≤ Cχ·(θ₁·Tailmax) + Kalias` for every `z`. -/
theorem chDkernel_glue {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut}
    {ℓ : ℝ} {N : ℕ} {μ : ℝ}
    (hℓ : 0 < ℓ) (hN : 1 ≤ N) {Cχ θ₁ Tailmax Kalias : ℝ} (hCχ : 0 ≤ Cχ) (hθ₁ : 0 ≤ θ₁) (hTmax : 0 ≤ Tailmax)
    (hχ : ∀ z : E3, |(Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)| ≤ Cχ)
    (hS : ∀ p : E3, Work.BoseBoxFock.uvRad ℓ N ≤ ‖p‖ →
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ θ₁)
    (hSum : Summable (fun m : Fin 3 → ℤ =>
      |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)|))
    (hTail : (∑' m : Fin 3 → ℤ, |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)|) ≤ Tailmax)
    (hσ : ∀ z : E3,
      KχfrU v h μ fu N z - chDC h ℓ z
        = (∑' d : Fin 3 → ℤ,
            chDconv ℓ (fun u => ((chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
              (z + ℓ • Work.BoseBoxFock.latVec d))
          + (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
              chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                (z + ℓ • Work.BoseBoxFock.latVec d))))
    (hP2 : ∀ z : E3,
      (∑' d : Fin 3 → ℤ,
        chDconv ℓ (fun u => ((chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
          (z + ℓ • Work.BoseBoxFock.latVec d))
      = ∑' m : Fin 3 → ℤ,
          (((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
            * (((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                  (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ)))
    (halSum : ∀ z : E3, Summable (fun d : Fin 3 → ℤ =>
      ‖chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
        (z + ℓ • Work.BoseBoxFock.latVec d)‖))
    (hAlias : ∀ z : E3, (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
        ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
          * chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
              (z + ℓ • Work.BoseBoxFock.latVec d)‖)) ≤ Kalias) :
    ∀ z : E3, ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
        * (KχfrU v h μ fu N z - chDC h ℓ z)‖ ≤ Cχ * (θ₁ * Tailmax) + Kalias := by
  have hΛpos : 0 < Work.BoseBoxFock.uvRad ℓ N := by
    rw [Work.BoseBoxFock.uvRad]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  intro z
  -- the truncation sum is bounded by `θ₁ · Tailmax`
  have hA : ‖(∑' d : Fin 3 → ℤ,
      chDconv ℓ (fun u => ((chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
        (z + ℓ • Work.BoseBoxFock.latVec d))‖ ≤ θ₁ * Tailmax := by
    rw [hP2 z]
    have hb : ∀ m : Fin 3 → ℤ,
        ‖(((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
            * (((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                  (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ))‖
          ≤ θ₁ * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)| := by
      intro m
      have hphase : ‖Complex.exp
          (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ))‖ = 1 := by
        rw [show Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℝ) : ℂ)
              = (((inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z) : ℝ) : ℂ) * Complex.I from by ring,
          Complex.norm_exp_ofReal_mul_I]
      have hvec : ℓ • Work.BoseBoxFock.kmomInt ℓ m = Work.BoseB4.vec m := by
        rw [Work.BoseBoxFock.kmomInt, smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
      have hv1 : ‖(((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
            (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)‖
          = |(Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
            (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)| := RCLike.norm_ofReal _
      have hv2 : ‖(((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)‖
          = |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomInt ℓ m)| := RCLike.norm_ofReal _
      have hv3 : ‖(((Work.BoseK15.corpusBox.hatChi
            (Work.BoseB4.vec m) : ℝ)) : ℂ)‖
          = |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)| := RCLike.norm_ofReal _
      rw [norm_mul, norm_mul, norm_mul, hphase, mul_one, hvec, hv1, hv2, hv3]
      by_cases hcase : ‖Work.BoseBoxFock.kmomInt ℓ m‖ ≤ Work.BoseBoxFock.uvRad ℓ N
      · have huv : Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
            (Work.BoseBoxFock.kmomInt ℓ m) = 1 := by
          rw [Work.BoseBoxFock.uvCut]
          exact Work.BoseBoxFix.LowCut.one fu _ (by
            rw [div_le_one hΛpos]
            exact hcase)
        rw [huv, sub_self, abs_zero, zero_mul, zero_mul]
        exact mul_nonneg hθ₁ (abs_nonneg _)
      · have hgt : Work.BoseBoxFock.uvRad ℓ N < ‖Work.BoseBoxFock.kmomInt ℓ m‖ :=
          lt_of_not_ge hcase
        have h₁ : |(Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
            (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)| ≤ 1 := by
          have h0 : 0 ≤ Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomInt ℓ m) := by
            rw [Work.BoseBoxFock.uvCut]
            exact Work.BoseBoxFix.LowCut.nonneg fu _
          have h1 : Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomInt ℓ m) ≤ 1 := by
            rw [Work.BoseBoxFock.uvCut]
            exact Work.BoseBoxFix.LowCut.le_one fu _
          rw [abs_le]
          constructor <;> linarith
        have h₂ : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
            (Work.BoseBoxFock.kmomInt ℓ m)| ≤ θ₁ := hS _ hgt.le
        calc |Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
                (Work.BoseBoxFock.kmomInt ℓ m) - 1|
              * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                  (Work.BoseBoxFock.kmomInt ℓ m)|
              * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)|
            ≤ 1 * θ₁ * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)| :=
              mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (abs_nonneg _) (by norm_num))
                (abs_nonneg _)
          _ = θ₁ * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)| := by ring
    have hsumm : Summable (fun m : Fin 3 → ℤ =>
        (((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
            * (((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                  (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ))) :=
      Summable.of_norm_bounded (hSum.mul_left θ₁) fun m => hb m
    calc ‖∑' m, _‖ ≤ ∑' m, _ := norm_tsum_le_tsum_norm hsumm.norm
      _ ≤ ∑' m, θ₁ * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)| :=
          Summable.tsum_le_tsum (fun m => hb m) hsumm.norm (hSum.mul_left θ₁)
      _ = θ₁ * ∑' m, |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)| := tsum_mul_left
      _ ≤ θ₁ * Tailmax := mul_le_mul_of_nonneg_left hTail hθ₁
  -- the (`d ≠ 0`) alias sum is bounded by `Kalias`
  have hB : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
      * (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
          chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d)))‖ ≤ Kalias := by
    have hsumm2 : Summable (fun d : Fin 3 → ℤ =>
        ‖(if d = 0 then 0 else chDconv ℓ
          (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d))‖) := by
      refine Summable.of_norm_bounded (halSum z) fun d => ?_
      by_cases hd : d = 0
      · rw [if_pos hd]
        simp only [norm_zero, norm_norm]
        norm_num
      · rw [if_neg hd]
        simp only [norm_norm]
        exact le_rfl
    calc ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then 0 else
            chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
              (z + ℓ • Work.BoseBoxFock.latVec d))‖
        = |Work.BoseK15.corpusBox.chiLam ℓ z| * ‖∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
            chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
              (z + ℓ • Work.BoseBoxFock.latVec d))‖ := by
          rw [norm_mul, show ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)‖
            = |Work.BoseK15.corpusBox.chiLam ℓ z| from RCLike.norm_ofReal _]
      _ ≤ |Work.BoseK15.corpusBox.chiLam ℓ z| *
            (∑' d : Fin 3 → ℤ, ‖(if d = 0 then 0 else
              chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                (z + ℓ • Work.BoseBoxFock.latVec d))‖) :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumm2) (abs_nonneg _)
      _ = (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
            ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
              * chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
                  (z + ℓ • Work.BoseBoxFock.latVec d)‖)) := by
          rw [← tsum_mul_left]
          refine tsum_congr fun d => ?_
          by_cases hd : d = 0
          · rw [if_pos hd, if_pos hd]
            simp
          · rw [if_neg hd, if_neg hd, norm_mul, show
              ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)‖
                = |Work.BoseK15.corpusBox.chiLam ℓ z| from RCLike.norm_ofReal _]
      _ ≤ Kalias := hAlias z
  -- combine the two pieces
  have hA' : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
      * (∑' d : Fin 3 → ℤ, chDconv ℓ
          (fun u => ((chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
          (z + ℓ • Work.BoseBoxFock.latVec d))‖ ≤ Cχ * (θ₁ * Tailmax) := by
    rw [norm_mul, show ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)‖
      = |Work.BoseK15.corpusBox.chiLam ℓ z| from RCLike.norm_ofReal _]
    exact le_trans (mul_le_mul_of_nonneg_right (hχ z) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hA hCχ)
  have hB' : ‖(((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ)) : ℂ)
      * (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
          chDconv ℓ (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d)))‖ ≤ Kalias := hB
  rw [hσ z, mul_add]
  exact le_trans (norm_add_le _ _) (add_le_add hA' hB')


end Work.BoseBoxFock.PCFU

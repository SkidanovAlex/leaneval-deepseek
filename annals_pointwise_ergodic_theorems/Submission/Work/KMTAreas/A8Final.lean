/-
# Area A8 — the final assembly of `VarBilinInterp`

This module assembles the area A8 proof: the clamped variational norm is linearised by the test
objects of `Work.KMTAreas.A8.exists_testObject`, the clamped bound for finitely supported inputs
is `Work.KMTAreas.A8.clamped_bound` (three-lines interpolation of the trilinear form `lam`), the
clamped norms are then passed to the variational norm by monotone convergence, and the bound is
extended from finitely supported to `MemLp` inputs by `Work.KMTAreas.A8.limit_step` (lower
semicontinuity of the variational norm plus Fatou).
-/
import Mathlib
import Submission.Work.KMTAreas.A8.limit_step
import Submission.Work.KMTAreas.A8.clamped_bound
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory (FinSupp)
open PointwiseErgodicTheorems (variationalNorm)

/-- The clamped variational norms increase to the variational norm. -/
lemma iSup_vNormK (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    (⨆ K : ℕ, ENNReal.ofReal (vNormK r K a)) = variationalNorm r a :=
  (A8.vNormK_basic r hr a).2.2

/-- The clamped variational norms are monotone in `K`. -/
lemma monotone_vNormK (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    Monotone fun K : ℕ => ENNReal.ofReal (vNormK r K a) :=
  fun i j hij => ENNReal.ofReal_le_ofReal ((A8.vNormK_basic r hr a).2.1 i j hij)

/-- The clamped variational norm is nonnegative. -/
lemma vNormK_nonneg (r : NNReal) (K : ℕ) (a : ℕ → ℂ) : 0 ≤ vNormK r K a := by
  unfold vNormK supK varK
  refine add_nonneg ?_ ?_
  · refine le_trans (norm_nonneg (a 0)) (Finset.le_sup' (f := fun n => ‖a n‖)
      (Finset.mem_range.mpr (Nat.succ_pos K)))
  · have hb : 0 ≤ ∑ i : Fin (Classical.choice (chainNonempty K)).1.1,
        ‖a ((Classical.choice (chainNonempty K)).2.1 i.succ)
          - a ((Classical.choice (chainNonempty K)).2.1 i.castSucc)‖ ^ (r : ℝ) :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
    exact le_trans (Real.rpow_nonneg hb _) (Finset.le_sup' (s := (Finset.univ : Finset (Chain K)))
      (f := fun p => (∑ i : Fin p.1.1, ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ))
        ^ (1 / (r : ℝ))) (Finset.mem_univ _))

/-- `1 ≤ q` for an interpolated exponent. -/
lemma one_le_of_interp {q q₀ q₁ : ENNReal} {θ : ℝ} (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hrel : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) : 1 ≤ q := by
  rw [← ENNReal.inv_le_one]
  calc q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹ := hrel
    _ ≤ ENNReal.ofReal (1 - θ) * 1 + ENNReal.ofReal θ * 1 := by
        gcongr
        · exact ENNReal.inv_le_one.mpr hq₀
        · exact ENNReal.inv_le_one.mpr hq₁
    _ = 1 := by
        rw [mul_one, mul_one, ← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 - θ by linarith) hθ₀,
          show (1 - θ) + θ = 1 by ring, ENNReal.ofReal_one]

/-- `q < ⊤` for an interpolated exponent. -/
lemma lt_top_of_interp {q q₀ q₁ : ENNReal} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hq₁ : 1 ≤ q₁) (hq₁f : q₁ < ⊤)
    (hrel : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) : q < ⊤ := by
  have hqinv0 : q⁻¹ ≠ 0 := by
    rw [hrel]
    refine ne_of_gt (lt_of_lt_of_le ?_ le_add_self)
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hθ₀).ne'
      (ENNReal.inv_ne_zero.mpr (ne_of_lt hq₁f))
  refine lt_top_iff_ne_top.mpr fun h => hqinv0 ?_
  rw [h, ENNReal.inv_top]

/-- **The bound for finitely supported inputs.** -/
theorem finsupp_bound {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
    (hlin₁ : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {r : NNReal} (hr : 1 ≤ r)
    {a₀ b₀ q₀ a₁ b₁ q₁ a b q : ENNReal} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (ha₀ : 1 < a₀) (ha₀f : a₀ < ⊤) (hb₀ : 1 < b₀) (hb₀f : b₀ < ⊤)
    (ha₁ : 1 < a₁) (ha₁f : a₁ < ⊤) (hb₁ : 1 < b₁) (hb₁f : b₁ < ⊤)
    (hq₀ : 1 ≤ q₀) (hq₀f : q₀ < ⊤) (hq₁ : 1 ≤ q₁) (hq₁f : q₁ < ⊤)
    (hrela : a⁻¹ = ENNReal.ofReal (1 - θ) * a₀⁻¹ + ENNReal.ofReal θ * a₁⁻¹)
    (hrelb : b⁻¹ = ENNReal.ofReal (1 - θ) * b₀⁻¹ + ENNReal.ofReal θ * b₁⁻¹)
    (hrelq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : NNReal}
    (hT₀ : ∀ u v : ℤ → ℂ, FinSupp u → FinSupp v →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T u v n x)) q₀ Measure.count
        ≤ (M₀ : ENNReal) * eLpNorm u a₀ Measure.count * eLpNorm v b₀ Measure.count)
    (hT₁ : ∀ u v : ℤ → ℂ, FinSupp u → FinSupp v →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T u v n x)) q₁ Measure.count
        ≤ (M₁ : ENNReal) * eLpNorm u a₁ Measure.count * eLpNorm v b₁ Measure.count)
    (u v : ℤ → ℂ) (hu : FinSupp u) (hv : FinSupp v) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T u v n x)) q Measure.count
      ≤ ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
        * eLpNorm u a Measure.count * eLpNorm v b Measure.count := by
  classical
  have hq_ge : 1 ≤ q := one_le_of_interp hq₀ hq₁ hθ₀.le hθ₁.le hrelq
  have hq_lt : q < ⊤ := lt_top_of_interp hθ₀ hθ₁ hq₁ hq₁f hrelq
  have hq0 : q ≠ 0 := (lt_of_lt_of_le one_pos hq_ge).ne'
  have hqtop : q ≠ ⊤ := ne_of_lt hq_lt
  have hkey : ∀ K : ℕ, eLpNorm (fun x : ℤ => ENNReal.ofReal (vNormK r K (fun n : ℕ => T u v n x)))
      q Measure.count
      ≤ ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
        * eLpNorm u a Measure.count * eLpNorm v b Measure.count := by
    intro K
    have h := A8.clamped_bound hlin₁ hlin₂ hr K hθ₀ hθ₁ ha₀ ha₀f hb₀ hb₀f ha₁ ha₁f hb₁ hb₁f
      hq₀ hq₀f hq₁ hq₁f hrela hrelb hrelq hT₀ hT₁ u v hu hv
    rw [show eLpNorm (fun x : ℤ => ((vNormK r K (fun n : ℕ => T u v n x) : ℝ) : ℂ)) q Measure.count
        = eLpNorm (fun x : ℤ => ENNReal.ofReal (vNormK r K (fun n : ℕ => T u v n x)))
            q Measure.count from ?_] at h
    · exact h
    · refine eLpNorm_congr_enorm_ae (hf := by pw_aesm) (hg := by pw_aesm) ?_
      filter_upwards with x
      rw [← ofReal_norm, enorm_eq_self]
      congr 1
      exact RCLike.norm_of_nonneg (vNormK_nonneg r K _)
  have hsup := Submission.PointwiseErgodicTheorems.eLpNorm_iSup_le_of_le (μ := Measure.count)
    (p := q) hq0 hqtop (u := fun K x => ENNReal.ofReal (vNormK r K (fun n : ℕ => T u v n x)))
    (fun K => (measurable_of_countable _).aemeasurable)
    (fun x => monotone_vNormK r hr _) hkey
  rwa [show (fun x : ℤ => ⨆ K : ℕ, ENNReal.ofReal (vNormK r K (fun n : ℕ => T u v n x)))
      = fun x : ℤ => variationalNorm r (fun n : ℕ => T u v n x) from by
    funext x
    exact iSup_vNormK r hr _] at hsup

/-- **The bound for `MemLp` inputs.** -/
theorem memLp_bound {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
    (hlin₁ : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {r : NNReal} (hr : 1 ≤ r)
    {a₀ b₀ q₀ a₁ b₁ q₁ a b q : ENNReal} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (ha₀ : 1 < a₀) (ha₀f : a₀ < ⊤) (hb₀ : 1 < b₀) (hb₀f : b₀ < ⊤)
    (ha₁ : 1 < a₁) (ha₁f : a₁ < ⊤) (hb₁ : 1 < b₁) (hb₁f : b₁ < ⊤)
    (hq₀ : 1 ≤ q₀) (hq₀f : q₀ < ⊤) (hq₁ : 1 ≤ q₁) (hq₁f : q₁ < ⊤)
    (hrela : a⁻¹ = ENNReal.ofReal (1 - θ) * a₀⁻¹ + ENNReal.ofReal θ * a₁⁻¹)
    (hrelb : b⁻¹ = ENNReal.ofReal (1 - θ) * b₀⁻¹ + ENNReal.ofReal θ * b₁⁻¹)
    (hrelq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : NNReal}
    (hT₀ : ∀ u v : ℤ → ℂ, FinSupp u → FinSupp v →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T u v n x)) q₀ Measure.count
        ≤ (M₀ : ENNReal) * eLpNorm u a₀ Measure.count * eLpNorm v b₀ Measure.count)
    (hT₁ : ∀ u v : ℤ → ℂ, FinSupp u → FinSupp v →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T u v n x)) q₁ Measure.count
        ≤ (M₁ : ENNReal) * eLpNorm u a₁ Measure.count * eLpNorm v b₁ Measure.count)
    (hconv : ∀ f g : ℤ → ℂ, MemLp f a Measure.count → MemLp g b Measure.count →
      ∀ (n : ℕ) (x : ℤ), Filter.Tendsto (fun K : ℕ => T (Work.KMTContract.truncZ K f)
        (Work.KMTContract.truncZ K g) n x) Filter.atTop (nhds (T f g n x)))
    (f g : ℤ → ℂ) (hfm : MemLp f a Measure.count) (hgm : MemLp g b Measure.count) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T f g n x)) q Measure.count
      ≤ ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
        * eLpNorm f a Measure.count * eLpNorm g b Measure.count := by
  have hq_ge : 1 ≤ q := one_le_of_interp hq₀ hq₁ hθ₀.le hθ₁.le hrelq
  have hq_lt : q < ⊤ := lt_top_of_interp hθ₀ hθ₁ hq₁ hq₁f hrelq
  refine A8.limit_step hr hq_ge hq_lt
    (u := fun K n x => T (Work.KMTContract.truncZ K f) (Work.KMTContract.truncZ K g) n x)
    (v := fun n x => T f g n x)
    (C := ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
      * eLpNorm f a Measure.count * eLpNorm g b Measure.count) ?_ ?_
  · intro K
    refine (finsupp_bound hlin₁ hlin₂ hr hθ₀ hθ₁ ha₀ ha₀f hb₀ hb₀f ha₁ ha₁f hb₁ hb₁f
      hq₀ hq₀f hq₁ hq₁f hrela hrelb hrelq hT₀ hT₁ (Work.KMTContract.truncZ K f)
      (Work.KMTContract.truncZ K g) (Work.KMTContract.finsupp_truncZ K f)
      (Work.KMTContract.finsupp_truncZ K g)).trans ?_
    gcongr
    · refine eLpNorm_mono_enorm (hf := by pw_aesm) (f := Work.KMTContract.truncZ K f) (g := f) ?_
      intro x
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Work.KMTContract.truncZ_apply]
      split_ifs with h
      · exact le_rfl
      · simp
    · refine eLpNorm_mono_enorm (hf := by pw_aesm) (f := Work.KMTContract.truncZ K g) (g := g) ?_
      intro x
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Work.KMTContract.truncZ_apply]
      split_ifs with h
      · exact le_rfl
      · simp
  · intro n x
    exact hconv f g hfm hgm n x

/-- **Area A8 of the KMT contract** (the statement is re-exported as `Work.KMTAreas.area_A8`
in `Submission/Work/KMTAreas/area_A8.lean`). -/
theorem varBilinInterp : Work.KMTContract.VarBilinInterp := by
  intro r a₀ b₀ q₀ a₁ b₁ q₁ a b q θ hr hθ₀ hθ₁ ha₀ ha₀f hb₀ hb₀f ha₁ ha₁f hb₁ hb₁f hq₀ hq₀f
    hq₁ hq₁f ha hb hq
  refine ⟨1, one_pos, ?_⟩
  intro T M₀ M₁ hlin₁ hlin₂ hT₀ hT₁ hconv f g hfm hgm
  have hmain := memLp_bound hlin₁ hlin₂ hr hθ₀ hθ₁ ha₀ ha₀f hb₀ hb₀f ha₁ ha₁f hb₁ hb₁f
    hq₀ hq₀f hq₁ hq₁f ha hb hq hT₀ hT₁ hconv f g hfm hgm
  have hconst : (((Real.toNNReal ((1 : ℝ) * (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ) : NNReal)) : ENNReal)
      = (M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ := by
    have hX : (0 : ℝ) ≤ (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ := by positivity
    rw [show (1 : ℝ) * (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ
        = (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ by ring]
    rw [show (((Real.toNNReal ((M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ) : NNReal)) : ENNReal)
        = ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ) from by
      rw [ENNReal.ofReal_eq_coe_nnreal hX, Real.toNNReal_of_nonneg hX]]
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ (M₀ : ℝ) by positivity)
        (show (0 : ℝ) ≤ 1 - θ by linarith),
      ← ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ (M₁ : ℝ) by positivity)
        (show (0 : ℝ) ≤ θ by linarith),
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => T f g n x)) q Measure.count
      ≤ ((M₀ : ENNReal) ^ (1 - θ) * (M₁ : ENNReal) ^ θ)
        * eLpNorm f a Measure.count * eLpNorm g b Measure.count := hmain
    _ = (((Real.toNNReal ((1 : ℝ) * (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ) : NNReal)) : ENNReal)
        * eLpNorm f a Measure.count * eLpNorm g b Measure.count := by rw [hconst]

end Work.KMTAreas

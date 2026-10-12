import ChallengeDeps
import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.convScale_lower_closedBall
import Submission.Work.BoseBoxFock.PotCubicPoissonAux
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.chBslotAux` — helper estimates for the `(B)` slot

Helper lemmas for `Work.BoseBoxFock.PCFU.chBslot_le`: elementary facts about the window
`χ_Λ = corpusBox.chiLam ℓ` and the weight `W₁ = W1fun v h ℓ`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The mass of the scaled window**: `∫_w χ_Λ(w) = ℓ³ χ̂(0)`.  Immediate from the corpus's
cosine-transform identity `BoxData.integral_chiLam_mul_cos` at `p = 0`. -/
theorem integral_chiLam_eq (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi 0 := by
  have h := Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ (0 : E3)
  simpa using h

/-- **The `L¹` bound on the weight `W₁ = g₀/(χ⋆χ)(·/ℓ)`.**  In the box regime `R ≤ ℓ·chiR0` the
denominator is `≥ 1/2` on `ball(0,R)`, where `g₀` is supported, so `W₁ ≤ 2|g₀|` pointwise and the
mass of `W₁` is at most twice that of `g₀ = v(1−ω)` (which is `ℓ`-independent). -/
theorem W1fun_L1_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * ∫ x : E3, |Submission.BoseGases.g0 v h x| := by
  have hg0supp : tsupport (Submission.BoseGases.g0 v h) ⊆ Metric.ball (0 : E3) R := by
    have h1 : Function.support (Submission.BoseGases.g0 v h) ⊆ Function.support v := by
      intro x hx
      show v x ≠ 0
      intro hv
      exact hx (by show Submission.BoseGases.g0 v h x = 0; simp [Submission.BoseGases.g0, hv])
    exact (closure_mono h1).trans hv_supp
  have hpt : ∀ x : E3, |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * |Submission.BoseGases.g0 v h x| := by
    intro x
    have hW : Work.BoseFixR.W1fun v h ℓ x
        = Submission.BoseGases.g0 v h x / Submission.BoseGases.convScale ℓ x := rfl
    by_cases hx : ‖x‖ ≤ R
    · have hcs : (1 : ℝ) / 2 ≤ Submission.BoseGases.convScale ℓ x :=
        Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx
      have hpos : 0 < Submission.BoseGases.convScale ℓ x := lt_of_lt_of_le (by norm_num) hcs
      rw [hW, abs_div, abs_of_pos hpos]
      rw [div_le_iff₀ hpos]
      nlinarith [abs_nonneg (Submission.BoseGases.g0 v h x), hcs]
    · have hg : Submission.BoseGases.g0 v h x = 0 := by
        by_contra hne
        have hmem := hg0supp (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [Metric.mem_ball, dist_zero_right] at hmem
        exact absurd hmem (not_lt.mpr (le_of_not_ge hx))
      rw [hW, hg, zero_div, abs_zero]
      positivity
  have hWint : Integrable (fun x : E3 => |Work.BoseFixR.W1fun v h ℓ x|) :=
    (Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R) (ℓ := ℓ) hR hv_supp h hℓ hRℓ).abs
  have hgint : Integrable (fun x : E3 => |Submission.BoseGases.g0 v h x|) :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).abs
  calc ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x|
      ≤ ∫ x : E3, 2 * |Submission.BoseGases.g0 v h x| :=
        integral_mono_ae hWint (hgint.const_mul 2) (Filter.Eventually.of_forall hpt)
    _ = 2 * ∫ x : E3, |Submission.BoseGases.g0 v h x| := integral_const_mul _ _

/-! ## The window on the box ball, and the small lattice set -/

/-- **The window vanishes outside `ball(0, ℓ/2)`.** -/
lemma chiLam_eq_zero_of_half_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3} (hz : ℓ / 2 < ‖z‖) :
    Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
  have h : (1 / 2 : ℝ) < ‖(ℓ⁻¹ : ℝ) • z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div]
    rw [lt_div_iff₀ hℓ]
    linarith
  have hchi : Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • z) = 0 :=
    Submission.BoseGases.chi_eq_zero_of_norm_gt _ h
  simpa only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi] using hchi

/-- The window is nonnegative. -/
lemma chiLam_nonneg' (ℓ : ℝ) (z : E3) : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ z := by
  simpa only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi] using
    Submission.BoseGases.chi_nonneg ((ℓ⁻¹ : ℝ) • z)

/-- The window is bounded by the fixed constant `(√ chiNormSq)⁻¹`. -/
lemma chiLam_le_chiSupAbs (ℓ : ℝ) (z : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ z ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  rw [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]
  exact le_trans (le_abs_self _) (Submission.BoseGases.abs_chi_le _)

/-- The finite set of "small" lattice vectors `{-3,…,3}³`, as the image of `(Fin 7)³`. -/
def smLab : Finset (Fin 3 → ℤ) :=
  Finset.univ.image (fun (c : Fin 3 → Fin 7) (i : Fin 3) => (c i : ℤ) - 3)

lemma smLab_card : smLab.card ≤ 343 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_fun]
  norm_num

lemma mem_smLab {d : Fin 3 → ℤ} (h : ∀ i, |d i| ≤ 3) : d ∈ smLab := by
  refine Finset.mem_image.mpr ⟨fun i => ⟨(d i + 3).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have h1 : 0 ≤ d i + 3 := by
      have := h i; rw [abs_le] at this; linarith [this.1]
    have h2 : d i + 3 < (7 : ℤ) := by
      have := h i; rw [abs_le] at this; linarith [this.2]
    have h3 : ((d i + 3).toNat : ℤ) < 7 := by rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · funext i
    show (((⟨(d i + 3).toNat, _⟩ : Fin 7) : ℤ)) - 3 = d i
    have h1 : 0 ≤ d i + 3 := by
      have := h i; rw [abs_le] at this; linarith [this.1]
    simp only [Fin.val_natCast]
    rw [Int.toNat_of_nonneg h1]
    ring

lemma norm_latVec_ge_of_notMem_smLab {d : Fin 3 → ℤ} (h : d ∉ smLab) : 4 ≤ ‖latVec d‖ := by
  by_contra hlt
  push_neg at hlt
  refine h (mem_smLab fun i => ?_)
  have h1 : |((d i : ℤ) : ℝ)| ≤ ‖latVec d‖ := by
    have h2 : ‖(latVec d).ofLp i‖ = |((d i : ℤ) : ℝ)| := by
      rw [show (latVec d).ofLp i = ((d i : ℤ) : ℝ) by simp [latVec, WithLp.ofLp_toLp],
        Real.norm_eq_abs]
    calc |((d i : ℤ) : ℝ)| = ‖(latVec d).ofLp i‖ := h2.symm
      _ ≤ ‖latVec d‖ := PiLp.norm_apply_le (latVec d) i
  have h3 : |((d i : ℤ) : ℝ)| < 4 := lt_of_le_of_lt h1 hlt
  have h5 : |((d i : ℤ) : ℝ)| < 4 := h3
  rw [abs_lt] at h5
  rw [abs_le]
  constructor
  · have : (-4 : ℤ) < d i := by exact_mod_cast h5.1
    omega
  · have : (d i : ℤ) < 4 := by exact_mod_cast h5.2
    omega

/-! ## The lattice images of the smoothed weight

The `(B)`-slot's kernel is `KχfrU − Ĉ`; after the periodisation identity
(`KchiFrU_eq_periodisation`) it splits as `χ_Λ ⋆ (uvSmear − W₁)` plus the images
`Σ_{d≠0}(χ_Λ ⋆ uvSmear)(· + ℓd)`.  The images are controlled here: the two window factors
force the aliasing flatness (`chi_mul_chi_le_of_alias`) at every mass point of the kernel, and
the kernel's *scaled* Schwartz decay `uvKernel_decay` converts that flatness into the polynomial
smallness, the finitely many "small" images being handled by cardinality and the rest by the
decay. -/

end Work.BoseBoxFock.PCFU

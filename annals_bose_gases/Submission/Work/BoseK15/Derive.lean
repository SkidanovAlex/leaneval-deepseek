import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseK15.hatChi_le_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.Derive` — the structural `Q3Kernel` fields

`Work.BoseK15.K15Input` (`Defs.lean`) collects FS's honest data in primitive form.
This module derives from a `K15Input` the fields of `Work.BoseB7A.Q3Kernel` that
are pure *structure* — no analysis:

* `hasKernel` (FS `eq:Commutator_general` in mode indices), the parities
  `W1_even`, `A_even`, `B_even`, `hatChi_even`, `hatChiSq_even`, the identities
  `B_eq`, `tau_even`, the cutoff facts `fL_nonneg`, `fL_le_one`, `fL_even`,
  `fL_supp`, the label arithmetic `kmom_sub`, the `u`-bounds `hatChi_le`,
  `hatChiSq_le`, `W1omega0_nonneg`, `W1omega0_le`, and `q2exLower`.

The χ-decay consequences (K2) are in `ChiSmall.lean`, `ChiSums.lean`,
`ChiForm.lean`; the potential and kinetic ones (K3, K4) in `Pot.lean`,
`AlphaLip.lean`; the `IntKernel` rows (K5) in `Green.lean`.

## Notational note

`Q3Kernel.AB` in `Work.BoseB7A` asks `|E.B k| ≤ E.A k` for **every** mode.
FS only ever use it on `P_H` (`eq:BoverA`, and the `P_H`-inner-radius qualifier
is explicit there); on the modes where `τ` is between `0` and `(2sℓ)⁻¹` and
`Ŵ₁ < 0`, `𝒜 = τ + ℬ` with `|ℬ| > 𝒜`, so the *global* form is not implied by
FS's data.  The chapter proves the `P_H^q` form (`Pot.AB_PHq`) and `Main.lean`
takes the global `AB` as an explicit hypothesis.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

namespace K15Input

/-- `τ` is radial, hence even. -/
lemma tauFun_neg (eT s d ℓ : ℝ) (p : ℝ³) :
    Work.BoseB4.tauFun eT s d ℓ (-p) = Work.BoseB4.tauFun eT s d ℓ p := by
  simp [Work.BoseB4.tauFun, norm_neg]

/-- FS `eq:W1-g` at the modes: `|Ŵ₁(k)| ≤ K₀a`. -/
theorem W1_le_holds (h : K15Input K₀ F T E) (k : Mode) : |E.W1 k| ≤ K₀ * E.aScat := by
  rw [h.W1_eq k]
  exact le_trans (h.W1_le (h.kmom k)) (mul_le_mul_of_nonneg_right h.K₀_w h.aScat_pos.le)

/-- `Ŵ₁` is even at the modes (the modes are symmetric under `k ↦ -k`). -/
theorem W1_even_holds (h : K15Input K₀ F T E) (k : Mode) : E.W1 (-k) = E.W1 k := by
  rw [h.W1_eq (-k), h.W1_eq k, h.kmom_neg k, h.W1_even]

/-- `ℬ = ρ_zŴ₁` (FS `eq:BogHamPositive-1`). -/
theorem B_eq_holds (h : K15Input K₀ F T E) (k : Mode) : E.B k = E.rho * E.W1 k :=
  h.B_eq k

/-- `ℬ` is even. -/
theorem B_even_holds (h : K15Input K₀ F T E) (k : Mode) : E.B (-k) = E.B k := by
  rw [h.B_eq, h.B_eq, h.W1_even_holds k]

/-- The kinetic symbol is even. -/
theorem tau_even_holds (h : K15Input K₀ F T E) (k : Mode) : E.tau (-k) = E.tau k := by
  rw [h.tau_eq, h.tau_eq, h.kmom_neg k, tauFun_neg]

/-- `𝒜` is even. -/
theorem A_even_holds (h : K15Input K₀ F T E) (k : Mode) : E.A (-k) = E.A k := by
  rw [h.A_eq, h.A_eq, h.tau_even_holds k, h.W1_even_holds k]

/-- FS's cutoff `f_L` is nonnegative. -/
theorem fL_nonneg_holds (h : K15Input K₀ F T E) (s : Mode) : 0 ≤ E.fL s := by
  rw [h.fL_eq s]; exact h.fL_nonneg _

/-- FS's cutoff `f_L` is at most `1`. -/
theorem fL_le_one_holds (h : K15Input K₀ F T E) (s : Mode) : E.fL s ≤ 1 := by
  rw [h.fL_eq s]; exact h.fL_le_one _

/-- FS's cutoff `f_L` is even. -/
theorem fL_even_holds (h : K15Input K₀ F T E) (s : Mode) : E.fL (-s) = E.fL s := by
  rw [h.fL_eq (-s), h.fL_eq s, h.kmom_neg s, h.fL_even]

/-- `f_L` is supported in `P_L` (FS l. 1464). -/
theorem fL_supp_holds (h : K15Input K₀ F T E) (s : Mode) (hs : E.fL s ≠ 0) :
    F.PL E.KL E.mu E.aScat s := by
  show ‖F.kmom s‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat)
  rw [h.kmom_eq s]
  exact h.fL_supp (h.kmom s) (by rwa [h.fL_eq s] at hs)

/-- The label arithmetic `kmom (s - k) = kmom s - kmom k` on the pairs §10 uses. -/
theorem kmom_sub_holds (h : K15Input K₀ F T E) (s k : Mode) (hs : E.fL s ≠ 0)
    (hk : k ∈ F.PHset E) : F.kmom (s - k) = F.kmom s - F.kmom k := by
  rw [h.kmom_eq (s - k), h.kmom_eq s, h.kmom_eq k, h.kmom_add s k hs hk]

/-- `kmom 0 = 0` (the momentum assignment is odd). -/
lemma kmom_zero (h : K15Input K₀ F T E) : h.kmom 0 = 0 := by
  have h1 : h.kmom 0 = -h.kmom 0 := by
    simpa using h.kmom_neg (0 : Mode)
  have h3 : (2 : ℝ) • h.kmom 0 = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h1
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

/-- A nonzero mode has nonzero momentum: the momentum assignment is injective and
the condensate mode is the only one at the origin (`n₊ = Σ_{k≠0} a_k†a_k`). -/
theorem kmom_ne_holds (h : K15Input K₀ F T E) {k : Mode} (hk : k ∈ excited Mode) :
    F.kmom k ≠ 0 := by
  intro hz
  have h0 : h.kmom k = h.kmom 0 := by rw [h.kmom_zero, ← h.kmom_eq k]; exact hz
  have hk0 : k = 0 := h.hlat.injective h0
  rw [hk0] at hk
  simp [excited] at hk

/-- FS `eq:Commutator_general` in mode indices, on the summed pairs. -/
theorem hasKernel_holds (h : K15Input K₀ F T E) (i j : Mode) (hi : E.fL i ≠ 0)
    (hj : j ∈ F.PHset E) :
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j := h.hasKernel i j hi hj

/-- `|χ̂| ≤ 1` at the modes (the corpus χ is normalised: `∫χ² = 1`). -/
theorem hatChi_le_holds (h : K15Input K₀ F T E) (s : Mode) : |E.hatChi s| ≤ 1 := by
  rw [h.hatChi_eq s]; exact hatChi_le_one.1 _

/-- `|χ̂²| ≤ 1` at the modes. -/
theorem hatChiSq_le_holds (h : K15Input K₀ F T E) (s : Mode) : |E.hatChiSq s| ≤ 1 := by
  rw [h.hatChiSq_eq s]; exact hatChi_le_one.2 _

/-- `χ̂` is even at the modes (`χ` is even). -/
theorem hatChi_even_holds (h : K15Input K₀ F T E) (s : Mode) : E.hatChi (-s) = E.hatChi s := by
  rw [h.hatChi_eq (-s), h.hatChi_eq s, h.kmom_neg s, smul_neg, Work.BoseB4.BoxData.hatChi_neg]

/-- `χ̂²` is even at the modes. -/
theorem hatChiSq_even_holds (h : K15Input K₀ F T E) (s : Mode) :
    E.hatChiSq (-s) = E.hatChiSq s := by
  rw [h.hatChiSq_eq (-s), h.hatChiSq_eq s, h.kmom_neg s, smul_neg,
    Work.BoseB4.BoxData.hatChiSq_neg]

/-- `Ŵ₁ω(0) ≥ 0`. -/
theorem W1omega0_nonneg_holds (h : K15Input K₀ F T E) : 0 ≤ E.W1omega0 :=
  h.W1omega0_nonneg

/-- `Ŵ₁ω(0) ≤ K₀a`. -/
theorem W1omega0_le_holds (h : K15Input K₀ F T E) : E.W1omega0 ≤ K₀ * E.aScat :=
  h.W1omega0_le

/-- FS's first-quantised `Q₂^ex` cancellation. -/
theorem q2exLower_holds (h : K15Input K₀ F T E) (Ψ : F.H) :
    2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E) :=
  h.q2exLower Ψ

/-- `η = (K_ℓ^{-2}𝓁)^{M̃} ≥ 0`. -/
theorem eta_nonneg (h : K15Input K₀ F T E) : 0 ≤ eta E := by
  rw [eta]
  refine Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg h.Kl_pos.le _) ?_) _
  show 0 ≤ E.mu * E.aScat ^ 3 * E.KH ^ 2
  exact mul_nonneg (mul_nonneg h.mu_pos.le (pow_nonneg h.aScat_pos.le 3)) (sq_nonneg _)

/-! ## The pointwise χ̂-decay consequence -/

/-- **FS `lem:DecaychiHat` at a point**: `|χ̂(p)| ≤ Cchi·(1+‖p‖²)^{-decayOrder}`. -/
lemma hatChi_abs_le (h : K15Input K₀ F T E) (p : ℝ³) :
    |corpusBox.hatChi p| ≤ h.Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder)⁻¹ := by
  have hpos : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder := pow_pos (by positivity) _
  rw [show h.Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder)⁻¹
        = h.Cchi / ((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder from by ring]
  rw [le_div_iff₀ hpos]
  simpa [mul_comm] using h.chi.1 p

/-- **FS `lem:DecaychiHat` for `χ²` at a point.** -/
lemma hatChiSq_abs_le (h : K15Input K₀ F T E) (p : ℝ³) :
    |corpusBox.hatChiSq p| ≤ h.Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder)⁻¹ := by
  have hpos : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder := pow_pos (by positivity) _
  rw [show h.Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder)⁻¹
        = h.Cchi / ((1 : ℝ) + ‖p‖ ^ 2) ^ decayOrder from by ring]
  rw [le_div_iff₀ hpos]
  simpa [mul_comm] using h.chi.2 p

end K15Input

end Work.BoseK15

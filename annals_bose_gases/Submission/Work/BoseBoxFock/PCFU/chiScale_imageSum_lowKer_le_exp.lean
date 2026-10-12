import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le_exp`

The `κ`-uniform version of the `Ksfr`-image bound: the constant is required to be *independent of
the momentum cut-off* `κ`, at the price of the explicit factor `(1 + κ^{2N}) κ^{3-2N}`:

    ‖ χ_ℓ(b) · ℓ³ · ∑'_{d ≠ 0} Κ_κ(u - b + ℓ • latVec d) ‖ ≤ C (1 + κ^{2N}) κ^{3-2N} / ℓ^M .

## The mathematics

The proof is a **scaling reduction** of the (already proved) fixed-`κ` statement
`Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le`, at `κ = 1`, and needs no new analysis.

* **The kernel scales.**  Substituting `p = κ q` in `Κ_κ(z) = (2π)^{-3}∫_p f(‖p‖/κ) cos⟪p,z⟫`
  (a `κ³`-Jacobian, `Work.BoseBoxFock.PCFU.lowKer_scale`) gives
  `Κ_κ(z) = κ³ · Κ_1(κ • z)`.
* **The scaling of the whole expression.**  With `α = ℓ⁻¹ • u` the sub-level of the cube scales
  (`acube_smul`), and `χ_{κℓ}(κ • b) = χ_ℓ(b)` (`chiScale_mul_smul`).  Hence the target's left-hand
  side at `(κ, ℓ, b, u)` is *exactly* the `κ = 1` left-hand side at `(κℓ, κ • b, κ • u)`, and the
  fixed-`κ` theorem gives `C₁/(κℓ)^M`.
* **The bookkeeping** is then the elementary inequality `κ^{-M} ≤ (1 + κ^{2N}) κ^{3-2N}`
  (`zpow_neg_le_mul`), valid for every `κ > 0` exactly when `M + 3 ≤ 2N`: for `κ ≤ 1` the
  exponent `3 - 2N ≤ -M` makes the *negative* powers ordered, while for `κ ≥ 1` one has
  `κ^{-M} ≤ 1 ≤ κ³ ≤ (1 + κ^{2N}) κ^{3-2N}`.

Note that the hypothesis `M + 3 ≤ 2N` (equivalently `2N ≤ K`) is exactly what makes the two
regimes meet: it is the same condition the arithmetic `scalarImageSumBound` uses.
-/

namespace Work.BoseBoxFock.PCFU

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The scaling identity for the low-momentum kernel.**  Rescaling the momentum cut-off by
`κ` rescales the kernel by `κ³` and dilates its argument: `Κ_κ(z) = κ³ · Κ_1(κ • z)`. -/
theorem lowKer_scale (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (z : E3) :
    lowKer fc κ z = κ ^ 3 * lowKer fc 1 (κ • z) := by
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hpt : (fun s : E3 => fc.f (‖κ • s‖ / κ) * Real.cos (inner ℝ (κ • s) z))
      = fun s : E3 => fc.f (‖s‖ / 1) * Real.cos (inner ℝ s (κ • z)) := by
    funext s
    rw [norm_smul, Real.norm_of_nonneg hκ.le, real_inner_smul_left, real_inner_smul_right,
      div_one, mul_div_cancel_left₀ _ hκne]
  unfold lowKer
  rw [Submission.BoseGases.integral_comp_smul_right
    (g := fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) hκ, hpt]
  ring

/-- The scaled bump is invariant when the centre is scaled along with the box:
`χ_{κℓ}(κ • b) = χ_ℓ(b)` for `κ ≠ 0`. -/
lemma chiScale_mul_smul {κ ℓ : ℝ} (hκ : 0 < κ) (b : E3) :
    Submission.BoseGases.chiScale (κ * ℓ) (κ • b) = Submission.BoseGases.chiScale ℓ b := by
  simp only [Submission.BoseGases.chiScale]
  rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hκ), mul_one]

/-- The cube scales: `κ • u ∈ acube (κℓ)` for `κ > 0` and `u ∈ acube ℓ`. -/
lemma acube_smul {κ ℓ : ℝ} (hκ : 0 < κ) {u : E3} (hu : u ∈ Submission.BoseGases.acube ℓ) :
    κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := by
  rw [Submission.BoseGases.mem_acube_iff] at hu ⊢
  intro m
  have hm := hu m
  rw [Set.mem_Icc] at hm ⊢
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  exact ⟨by
      have h := mul_le_mul_of_nonneg_left hm.1 hκ.le
      linarith,
    by
      have h := mul_le_mul_of_nonneg_left hm.2 hκ.le
      linarith⟩

/-- The elementary `κ`-bookkeeping: `κ^{-M} ≤ (1 + κ^{2N}) κ^{3-2N}` for `κ > 0` and
`M + 3 ≤ 2N`.  This is exactly the price of making the constant of the image bound uniform in the
cut-off `κ`. -/
lemma zpow_neg_le_mul {M N : ℕ} (hNM : M + 3 ≤ 2 * N) {κ : ℝ} (hκ : 0 < κ) :
    κ ^ (-(M : ℤ)) ≤ (1 + κ ^ (2 * N)) * κ ^ (3 - 2 * N : ℤ) := by
  have h2N : 3 ≤ 2 * N := by omega
  have hcast : ((2 * N - 3 : ℕ) : ℤ) = 2 * (N : ℤ) - 3 := by
    rw [Nat.cast_sub h2N]
    push_cast
    ring
  have hexp : (3 - 2 * N : ℤ) = -((2 * N - 3 : ℕ) : ℤ) := by
    rw [hcast]; ring
  have hL : κ ^ (-(M : ℤ)) = (κ ^ M)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hR : κ ^ (3 - 2 * N : ℤ) = (κ ^ (2 * N - 3))⁻¹ := by
    rw [hexp, zpow_neg, zpow_natCast]
  rw [hL, hR]
  rcases le_or_gt κ 1 with hκ1 | hκ1
  · -- `κ ≤ 1`: both sides are negative powers, and `3 - 2N ≤ -M` reverses into `M ≤ 2N - 3`
    have hMle : M ≤ 2 * N - 3 := by omega
    have hle : κ ^ (2 * N - 3) ≤ κ ^ M := pow_le_pow_of_le_one hκ.le hκ1 hMle
    have h1 : (κ ^ M)⁻¹ ≤ (κ ^ (2 * N - 3))⁻¹ :=
      (inv_le_inv₀ (pow_pos hκ M) (pow_pos hκ _)).mpr hle
    refine le_trans h1 ?_
    have h2 : (1 : ℝ) ≤ 1 + κ ^ (2 * N) := by
      have := pow_nonneg hκ.le (2 * N); linarith
    have h3 : (0 : ℝ) ≤ (κ ^ (2 * N - 3))⁻¹ :=
      inv_nonneg.mpr (pow_pos hκ _).le
    calc (κ ^ (2 * N - 3))⁻¹ = 1 * (κ ^ (2 * N - 3))⁻¹ := by ring
      _ ≤ (1 + κ ^ (2 * N)) * (κ ^ (2 * N - 3))⁻¹ := mul_le_mul_of_nonneg_right h2 h3
  · -- `1 < κ`: `κ^{-M} ≤ 1` and `κ³ ≤ κ^{2N} κ^{3-2N} ≤ (1 + κ^{2N}) κ^{3-2N}`
    have h1 : (κ ^ M)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hκ1.le)
    refine le_trans h1 ?_
    have hpow : κ ^ (2 * N) = κ ^ 3 * κ ^ (2 * N - 3) := by
      rw [← pow_add]
      congr 1
      omega
    have hne : κ ^ (2 * N - 3) ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
    have key : κ ^ (2 * N) * (κ ^ (2 * N - 3))⁻¹ = κ ^ 3 := by
      rw [hpow, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    have h3 : (1 : ℝ) ≤ κ ^ 3 := one_le_pow₀ hκ1.le
    have h4 : κ ^ (2 * N) * (κ ^ (2 * N - 3))⁻¹
        ≤ (1 + κ ^ (2 * N)) * (κ ^ (2 * N - 3))⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (pow_pos hκ _).le)
      have := pow_nonneg hκ.le (2 * N); linarith
    calc (1 : ℝ) ≤ κ ^ 3 := h3
      _ = κ ^ (2 * N) * (κ ^ (2 * N - 3))⁻¹ := key.symm
      _ ≤ (1 + κ ^ (2 * N)) * (κ ^ (2 * N - 3))⁻¹ := h4

/-- **The `κ`-uniform `Ksfr`-image bound.**  For FS's low-momentum cut-off `fc` and all `M N K`
with `M + 3 ≤ 2N ≤ K` there is `C ≥ 0`, *independent of* `κ`, with

    ‖ χ_ℓ(b) · ℓ³ · ∑'_{d ≠ 0} Κ_κ(u - b + ℓ • latVec d) ‖ ≤ C (1 + κ^{2N}) κ^{3-2N} / ℓ^M

for all `κ, ℓ > 0`, `b`, and `u ∈ acube ℓ`. -/
theorem chiScale_imageSum_lowKer_le_exp (fc : Work.BoseBoxFix.LowCut)
    (M N K : ℕ) (hNM : M + 3 ≤ 2 * N) (hK : 2 * N ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ : ℝ}, 0 < κ → ∀ {ℓ : ℝ}, 0 < ℓ →
      ∀ b u : EuclideanSpace ℝ (Fin 3), u ∈ Submission.BoseGases.acube ℓ →
      ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ
              (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
        ≤ C * (1 + κ ^ (2 * N)) * κ ^ (3 - 2 * N : ℤ) / ℓ ^ M := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := chiScale_imageSum_lowKer_le fc (κ := 1) one_pos M
  refine ⟨C₁, hC₁0, ?_⟩
  intro κ hκ ℓ hℓ b u hu
  have hmem : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := acube_smul hκ hu
  have hbound := hC₁ (mul_pos hκ hℓ) (κ • b) (κ • u) hmem
  -- the argument identity: the rescaled image argument is the image of the rescaled argument
  have harg : ∀ d : Fin 3 → ℤ,
      κ • (u - b + ℓ • Work.BoseBoxFock.latVec d)
        = (κ • u) - (κ • b) + (κ * ℓ) • Work.BoseBoxFock.latVec d := by
    intro d
    simp only [smul_add, smul_sub, smul_smul]
  -- the pointwise scaling of the kernel images
  have hterm : ∀ d : Fin 3 → ℤ,
      (if d = 0 then (0 : ℂ)
        else ((lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = ((κ ^ 3 : ℝ) : ℂ) * (if d = 0 then (0 : ℂ)
          else ((lowKer fc 1 ((κ • u) - (κ • b) + (κ * ℓ) • Work.BoseBoxFock.latVec d)
            : ℝ) : ℂ)) := by
    intro d
    by_cases hd : d = 0
    · rw [if_pos hd, if_pos hd, mul_zero]
    · rw [if_neg hd, if_neg hd]
      have hreal : lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d)
          = κ ^ 3 * lowKer fc 1 ((κ • u) - (κ • b)
              + (κ * ℓ) • Work.BoseBoxFock.latVec d) := by
        conv_lhs => rw [lowKer_scale fc hκ (u - b + ℓ • Work.BoseBoxFock.latVec d)]
        rw [← harg d]
      rw [hreal, Complex.ofReal_mul]
  -- the sum scales
  have hsum : (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
        else ((lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = ((κ ^ 3 : ℝ) : ℂ) * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((lowKer fc 1 ((κ • u) - (κ • b) + (κ * ℓ) • Work.BoseBoxFock.latVec d)
            : ℝ) : ℂ)) := by
    rw [tsum_congr hterm, tsum_mul_left]
  -- the prefactor absorbs `κ³` and rescales to the `κ = 1` shape
  have hprod : ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)
        * (((κ ^ 3 : ℝ) : ℂ) * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((lowKer fc 1 ((κ • u) - (κ • b) + (κ * ℓ) • Work.BoseBoxFock.latVec d)
            : ℝ) : ℂ)))
      = ((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ) * ((((κ * ℓ) ^ 3 : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((lowKer fc 1 ((κ • u) - (κ • b) + (κ * ℓ) • Work.BoseBoxFock.latVec d)
            : ℝ) : ℂ)) := by
    rw [chiScale_mul_smul hκ b]
    push_cast
    ring
  have hEq : ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
      = ‖((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ) * ((((κ * ℓ) ^ 3 : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc 1 ((κ • u) - (κ • b) + (κ * ℓ) • Work.BoseBoxFock.latVec d)
              : ℝ) : ℂ))‖ := by
    rw [hsum, hprod]
  -- the arithmetic `κ^{-M} ≤ (1 + κ^{2N}) κ^{3-2N}`
  have hkey : C₁ / (κ * ℓ) ^ M ≤ C₁ * (1 + κ ^ (2 * N)) * κ ^ (3 - 2 * N : ℤ) / ℓ ^ M := by
    have hinv : ((κ * ℓ) ^ M)⁻¹ = (κ ^ M)⁻¹ * (ℓ ^ M)⁻¹ := by
      rw [mul_pow, mul_inv_rev, mul_comm]
    have hkM : (κ ^ M)⁻¹ = κ ^ (-(M : ℤ)) := by
      rw [zpow_neg, zpow_natCast]
    have hlM : (0 : ℝ) ≤ (ℓ ^ M)⁻¹ := inv_nonneg.mpr (pow_pos hℓ M).le
    have h1 : κ ^ (-(M : ℤ)) ≤ (1 + κ ^ (2 * N)) * κ ^ (3 - 2 * N : ℤ) :=
      zpow_neg_le_mul hNM hκ
    rw [div_eq_mul_inv, hinv, hkM]
    calc C₁ * (κ ^ (-(M : ℤ)) * (ℓ ^ M)⁻¹)
        = (C₁ * κ ^ (-(M : ℤ))) * (ℓ ^ M)⁻¹ := by ring
      _ ≤ (C₁ * ((1 + κ ^ (2 * N)) * κ ^ (3 - 2 * N : ℤ))) * (ℓ ^ M)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC₁0) hlM
      _ = C₁ * (1 + κ ^ (2 * N)) * κ ^ (3 - 2 * N : ℤ) * (ℓ ^ M)⁻¹ := by ring
  exact le_trans (le_of_eq hEq) (le_trans hbound hkey)

end
end Work.BoseBoxFock.PCFU

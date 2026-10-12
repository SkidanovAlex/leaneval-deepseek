import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.EBPerState
import Submission.Work.SmallBoxConvexity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed-`n` smallbox block bound — the Γ-large regime (Work.SmallBoxA0, step 1)

Area: the POTENTIAL-SIDE assembly of the fixed-`n` smallbox operator bound
(`SmallBoxBlockBound.smallbox_state_block_bound` / `smallbox_block_bound`).

This first module disposes of the regime in which the smallbox error shape
`Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}` is NOT small.  There the crude one-body
bound `sboxE Φ ≥ −sboxC·∫Φ²` (`SboxEB.sboxE_chosen_lower`,
`sboxC = μN̂·chiSup²·2·8π(av)`) already dominates the stated error terms:

    eB ≥ (¼(x−μ)² − ½μ²)·8π(av)s³ − Cμ²(av)s³Γ − Cμ(av),   x := N̂/s³,

holds with the UNIVERSAL constant `C := 128π + 144π·chiSup²` whenever
`1 ≤ Γ` (the argument uses only `a ≥ 0`, `0 ≤ x ≤ 9μ` — the window — and
`sboxE ≥ −16π·chiSup²·μ·N̂·(av)`; the hypotheses `0 < s`, `0 < μ`,
`R0 ≤ s·chiR0`, `K_B > 0` are those of the bundle).

Hence the remaining content of the two skeletons is the complementary
regime `Γ < 1`, which is where the exact `q1/q2/q3` word assembly, the
`∬w₂`-A₀ completion and the FibreLocalG2/D1 Bogolubov inputs are needed
(the later modules of this area).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The per-state bound in the Γ-large regime -/

/-- **Per-state block bound, Γ-large regime.**  For a smooth normalised
`N`-particle state over the centred box of side `s`, in the block window
`N̂/s³ ≤ 9μ`, if the FS error shape `Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}`
satisfies `1 ≤ Γ`, then the FS block shape holds with the universal
constant `C := 128π + 144π·chiSup²`:

    sboxE(Φ) ≥ (¼(x−μ)² − ½μ²)·8π(av)s³ − C·μ²(av)s³·Γ − C·μ(av). -/
theorem state_block_bound_large_Gamma {N : ℕ} {s μ R0 : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0) {K_B : ℝ} (hKB : 0 < K_B)
    (hwin : (N : ℝ) / s ^ 3 ≤ (9 : ℝ) * μ)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hΓ : 1 ≤ (R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :
    ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (128 * π + 144 * π * chiSup ^ 2) * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      - (128 * π + 144 * π * chiSup ^ 2) * μ * (a v)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  classical
  set Γ : ℝ := (R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hΓdef
  set C : ℝ := 128 * π + 144 * π * chiSup ^ 2 with hCdef
  set x : ℝ := (N : ℝ) / s ^ 3 with hxdef
  have hs3pos : 0 < s ^ 3 := by positivity
  have hxN : (N : ℝ) = x * s ^ 3 := by
    rw [hxdef, div_mul_cancel₀ _ (ne_of_gt hs3pos)]
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hCge : C ≥ 8 * π * (16 + 18 * chiSup ^ 2) := by
    rw [hCdef]; ring_nf; norm_num
  have hΓ1 : 1 ≤ Γ := hΓ
  have hann : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  -- the crude one-body bound
  have hlower := sboxE_chosen_lower (N := N) (s := s) (R := R0) (μ := μ) (v := v)
    hR0 hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ.le hΦc
  have hsboxC : sboxC N μ v = 16 * π * chiSup ^ 2 * μ * (N : ℝ) * (a v) := by
    rw [sboxC]; ring
  have hlower' : - (16 * π * chiSup ^ 2 * μ * (x * s ^ 3) * (a v))
      ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    have h0 : - sboxC N μ v * (∫ y in abox N s, (Φ y) ^ 2)
        ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := hlower
    rw [hnorm, mul_one, hsboxC, hxN] at h0
    exact h0
  -- the deficit quadratic
  have hf : (1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2 + 2 * chiSup ^ 2 * μ * x
      ≤ (16 + 18 * chiSup ^ 2) * μ ^ 2 := by
    have hx9 : x ≤ 9 * μ := by rw [hxdef]; exact hwin
    have hμnn : 0 ≤ μ := le_of_lt hμ
    have h1 : (x - μ) ^ 2 ≤ 64 * μ ^ 2 := by
      have habs : |x - μ| ≤ 8 * μ := by
        rw [abs_le]
        constructor <;> nlinarith
      nlinarith [sq_abs (x - μ), habs, hμnn]
    have h2 : 2 * chiSup ^ 2 * μ * x ≤ 18 * chiSup ^ 2 * μ ^ 2 := by
      have hc : 0 ≤ 2 * chiSup ^ 2 * μ := by positivity
      have h := mul_le_mul_of_nonneg_left hx9 hc
      nlinarith [h]
    nlinarith [h1, h2, sq_nonneg chiSup, sq_nonneg μ]
  -- the Γ ≥ 1 error term dominates the crude one
  have hCA : 8 * π * (16 + 18 * chiSup ^ 2) ≤ C * Γ := by
    have h1 : 8 * π * (16 + 18 * chiSup ^ 2) ≤ C * 1 := by linarith [hCge]
    have h2 : C * 1 ≤ C * Γ := by nlinarith [hΓ1, hCnn]
    linarith [h1, h2]
  -- key arithmetic:  main − Cμ²(av)s³Γ − Cμ(av) ≤ −16πχ²μ(xs³)(av)
  have hkey : ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
        * (8 * π * (a v) * s ^ 3)
      - C * μ ^ 2 * (a v) * s ^ 3 * Γ - C * μ * (a v)
      ≤ - (16 * π * chiSup ^ 2 * μ * (x * s ^ 3) * (a v)) := by
    set P : ℝ := μ ^ 2 * (a v) * s ^ 3 with hPdef
    set Q : ℝ := μ * (a v) with hQdef
    have hPnn : 0 ≤ P := by rw [hPdef]; positivity
    have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
    -- (a) main + 16πχ²μx(s³)(av) ≤ 8π(16+18χ²)P
    have h8 : 0 ≤ 8 * π * (a v) * s ^ 3 := by positivity
    have hm := mul_le_mul_of_nonneg_left hf h8
    have hident : ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
          + 16 * π * chiSup ^ 2 * μ * (x * s ^ 3) * (a v)
        = 8 * π * (a v) * s ^ 3
          * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2 + 2 * chiSup ^ 2 * μ * x) := by
      ring
    have hA : ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
          + 16 * π * chiSup ^ 2 * μ * (x * s ^ 3) * (a v)
        ≤ 8 * π * (16 + 18 * chiSup ^ 2) * P := by
      calc ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
            + 16 * π * chiSup ^ 2 * μ * (x * s ^ 3) * (a v)
          = 8 * π * (a v) * s ^ 3
            * ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2 + 2 * chiSup ^ 2 * μ * x) := hident
        _ ≤ 8 * π * (a v) * s ^ 3 * ((16 + 18 * chiSup ^ 2) * μ ^ 2) := hm
        _ = 8 * π * (16 + 18 * chiSup ^ 2) * P := by rw [hPdef]; ring
    -- (b) 8π(16+18χ²)P ≤ CΓP + CQ
    have hb : 8 * π * (16 + 18 * chiSup ^ 2) * P ≤ C * Γ * P + C * Q := by
      have h1 : 8 * π * (16 + 18 * chiSup ^ 2) * P ≤ C * Γ * P :=
        mul_le_mul_of_nonneg_right hCA hPnn
      have h2 : 0 ≤ C * Q := by
        have : 0 ≤ C := hCnn
        rw [hQdef]; positivity
      linarith [h1, h2]
    -- combine
    nlinarith [hA, hb, hPdef, hQdef]
  -- conclude
  calc ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - (128 * π + 144 * π * chiSup ^ 2) * μ ^ 2 * (a v) * s ^ 3
            * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        - (128 * π + 144 * π * chiSup ^ 2) * μ * (a v)
      = ((1 / 4 : ℝ) * (x - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
          - C * μ ^ 2 * (a v) * s ^ 3 * Γ - C * μ * (a v) := by
          rw [hCdef, hΓdef, ← hxdef]
    _ ≤ - (16 * π * chiSup ^ 2 * μ * (x * s ^ 3) * (a v)) := hkey
    _ ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := hlower'

/-! ## The `eB`-level bound in the Γ-large regime -/

/-- **`eB`-level block bound, Γ-large regime.**  The infimum form of
`state_block_bound_large_Gamma`: normalise a `CSBox` trial state
(`Ψ := (√∫Φ²)⁻¹ • Φ`, quadratic homogeneity `SboxHomogeneity.sboxE_smul`)
and apply the per-state bound.  This is the `eB`-normalisation pattern that
the exact assembly of the two skeletons also uses at the end. -/
theorem eB_block_bound_large_Gamma {N : ℕ} {s μ R0 : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0) {K_B : ℝ} (hKB : 0 < K_B)
    (hwin : (N : ℝ) / s ^ 3 ≤ (9 : ℝ) * μ)
    (hΓ : 1 ≤ (R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :
    ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (128 * π + 144 * π * chiSup ^ 2) * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      - (128 * π + 144 * π * chiSup ^ 2) * μ * (a v)
    ≤ eB N s μ v h := by
  classical
  let B₀ : ℝ := ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (128 * π + 144 * π * chiSup ^ 2) * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      - (128 * π + 144 * π * chiSup ^ 2) * μ * (a v)
  have hper : ∀ Φ : CSBox N s,
      B₀ ≤ (sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2) := by
    intro Φ
    let Ph : X N → ℝ := Φ
    let I : ℝ := ∫ x in abox N s, (Ph x) ^ 2
    have hIpos : 0 < I := by simpa [I, Ph] using Φ.sq_pos
    have hIne : I ≠ 0 := ne_of_gt hIpos
    let c : ℝ := (Real.sqrt I)⁻¹
    have hsqrt0 : 0 < Real.sqrt I := Real.sqrt_pos.mpr hIpos
    have hc2 : c ^ 2 = I⁻¹ := by
      dsimp [c]
      have hsq : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt (le_of_lt hIpos)
      calc ((Real.sqrt I)⁻¹) ^ 2 = ((Real.sqrt I) ^ 2)⁻¹ := by rw [← inv_pow]
        _ = I⁻¹ := by rw [hsq]
    have hΨc : ContDiff ℝ ∞ (c • Ph) := Φ.contDiff.const_smul c
    have hnorm1 : (∫ x in abox N s, ((c • Ph) x) ^ 2) = 1 := by
      rw [abox_integral_sq_smul]
      rw [hc2]
      field_simp [hIne]
      simp [I]
    have hb := state_block_bound_large_Gamma (N := N) (s := s) (μ := μ) (R0 := R0) (v := v)
      hs hμ hv_nonneg hvrad hv_memL1 hR0 hv_supp h hRs hKB hwin (Φ := c • Ph) hΨc hnorm1 hΓ
    have hE : sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (c • Ph)
        = sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Ph / I := by
      have hsmul := sboxE_smul (N := N) (s := s) (μ := μ) (w := wPairC s v)
        (w1 := wPairC s (g0 v h)) (Φ := Ph) Φ.contDiff c
      rw [hsmul, hc2]
      field_simp [hIne]
    calc B₀ ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (c • Ph) := hb
      _ = sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Ph / I := hE
      _ = sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X N → ℝ) /
            (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2) := by rfl
  have hne : Nonempty (CSBox N s) := nonempty_CSBox N hs
  rw [eB]
  apply le_ciInf (ι := CSBox N s)
  exact hper

end Work.SmallBoxA0

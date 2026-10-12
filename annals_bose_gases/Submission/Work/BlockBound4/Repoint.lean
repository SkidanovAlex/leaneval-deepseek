import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BlockBound4.Defs
import Submission.Work.SmallBoxBridge.Bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# R4 — the per-box comparison, and the downstream re-point

## 1  What this module proves (R4a)

FS's per-box kinetic `T_B = Q_Bχ_B[√−Δ−c]₊²χ_BQ_B` (`eq:appTB`, the faithful
word) is a WINDOWED one-particle operator, and the honest localised kinetic of
the same window is the χ-weighted Dirichlet form.  The comparison is the two
symbol/Parseval facts

* `(|p|−c₀)₊² ≤ ‖p‖²` (the `c₀`-threshold is free), and
* the IMS/commutator step `χ(−Δ)χ ≼ χ²(−Δ) + ‖∇χ‖²_∞` (the `1/s²`-loss),

both of which are ALREADY PROVED in the corpus for the box window `chiScale s`:

* `Submission.BoseGases.pDiagForm_eq_T0Form` — `pDiagForm s F = T0Form s F`
  (the corpus's `𝒯₀`-form of `Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i`);
* `Submission.BoseGases.T0Form_le_kinWord` —
  `T0Form s (fsKinCoeff c) Ψ ≤ 2chiSup²·kinWord + 2·winErrorQ`
  (for `tsupport Ψ ⊆ abox (n+1) s`);
* `Submission.BoseGases.winErrorQ_le_cnPlus` —
  `winErrorQ s Ψ ≤ B·cnPlus s Ψ` whenever `B ≥ Σ_k(∂_kχ_s)²` pointwise.

This module assembles them into the statement the Door-4 consumers need: **the
faithful word is dominated by the honest χ-weighted kinetic plus the `ε_T`-gap
term**.  With the gradient bound `Σ_k(∂_kχ_s)² ≤ K/s²` (the window is
`χ(·/s)`, so `‖∇χ_s‖_∞ ≲ 1/s`) the gap `cgap·cnPlus ≥ n₊/(36s²)` pays the
window error:

    diagWWord s c₀ cgap (n+1) Φ ≤ 2·chiSup²·kinWord (n+1) s Φ + 2·cgap·cnPlus s Φ .

This is the inequality that lets the SLIDING layer (`Work.SmallBoxSliding`,
FS `eq:BSsliding2`) accept the faithful per-box word: it turns the per-box
localisation `hslide` into a statement about the honest kinetic, exactly as in
`Sliding.sliding_sum_identity` (see §3 for the re-point list).

## 2  What R4 is NOT

The comparison is an UPPER bound on the faithful word; it therefore does NOT
transfer a lower bound from the honest word to the faithful one.  Its role is the
opposite: Door 4 supplies a LOWER bound on the per-box faithful ground energy
(`diagW_block_bound_of_D1`), the comparison supplies the localisation
`∫_u (per-box faithful word) ≤ E_ℓ` (the `hslide` hypothesis), and the sliding
identity then gives the Λ-level lower bound on the honest energy `E_ℓ`.  That is
the sense in which Door 4 feeds the DL/UBB chain.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **R4a — the per-box comparison in its general form.**  For a smooth state
supported in the box, the faithful word is dominated by the honest χ-weighted
kinetic word plus `(2B + cgap)·cnPlus`, where `B` dominates the squared gradient
sum of the window.  This is `pDiagForm_eq_T0Form` + `T0Form_le_kinWord` +
`winErrorQ_le_cnPlus`, assembled. -/
theorem diagWWord_le_kinWord_add_cnPlus {n : ℕ} {s c cgap B : ℝ} (hs : 0 < s)
    (hc : 0 ≤ c) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ³, (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2) ≤ B)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    diagWWord s c cgap (n + 1) Φ
      ≤ 2 * chiSup ^ 2 * kinWord (n + 1) s Φ + (2 * B + cgap) * cnPlus s Φ := by
  have h1 : pDiagForm s (fsKinCoeff c) Φ = T0Form s (fsKinCoeff c) Φ :=
    pDiagForm_eq_T0Form hs (fsKinCoeff c) hΦ.continuous
  have h2 : T0Form s (fsKinCoeff c) Φ
      ≤ 2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * winErrorQ s Φ :=
    T0Form_le_kinWord (n := n) hs hc hΦ hsupp
  have h3 : winErrorQ s Φ ≤ B * cnPlus s Φ :=
    Work.SmallBoxBridge.Position.winErrorQ_le_cnPlus (N := n + 1) hs hB0 hB hΦ.continuous
  have h4 : 2 * winErrorQ s Φ ≤ 2 * (B * cnPlus s Φ) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 2)
  have h5 : (2 * B + cgap) * cnPlus s Φ = 2 * (B * cnPlus s Φ) + cgap * cnPlus s Φ := by ring
  rw [diagWWord_apply, h1]
  linarith [h2, h4, h5]

/-- **R4a, gap-paid form (the shape the consumers use).**  If the window-gradient
bound is at the scale `K/s²` and the `ε_T`-gap constant `cgap` pays it
(`2K/s² ≤ cgap`), then

    diagWWord s c₀ cgap (n+1) Φ ≤ 2·chiSup²·kinWord (n+1) s Φ + 2·cgap·cnPlus s Φ .

The second term is exactly the `ε_T`-gap of FS's `eq:appTB`
(`c_gap = ½ε_T(1+π⁻²)⁻¹(dℓ)⁻²`), so the `1/s²`-loss is free in FS's regime. -/
theorem diagWWord_le_kinWord_gap {n : ℕ} {s c cgap K : ℝ} (hs : 0 < s) (hc : 0 ≤ c)
    (hK : 0 ≤ K)
    (hgrad : ∀ x : ℝ³,
      (∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2) ≤ K / s ^ 2)
    (hpay : 2 * (K / s ^ 2) ≤ cgap)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hsupp : tsupport Φ ⊆ abox (n + 1) s) :
    diagWWord s c cgap (n + 1) Φ
      ≤ 2 * chiSup ^ 2 * kinWord (n + 1) s Φ + 2 * cgap * cnPlus s Φ := by
  have hB0 : 0 ≤ K / s ^ 2 := by positivity
  have h1 := diagWWord_le_kinWord_add_cnPlus (n := n) (c := c) (cgap := cgap)
    (B := K / s ^ 2) hs hc hB0 hgrad hΦ hsupp
  have hcn : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have h2 : (2 * (K / s ^ 2) + cgap) * cnPlus s Φ ≤ 2 * cgap * cnPlus s Φ := by
    have hle : 2 * (K / s ^ 2) + cgap ≤ 2 * cgap := by linarith
    exact mul_le_mul_of_nonneg_right hle hcn
  linarith [h1, h2]

end Work.BlockBound4

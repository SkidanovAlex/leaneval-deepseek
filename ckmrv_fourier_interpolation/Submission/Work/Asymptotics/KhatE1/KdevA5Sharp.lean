import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevA5
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Asymptotics.KhatE1.KdevA4Book
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Core.EisensteinThreeTerm
import Submission.Work.Asymptotics.KhatE1Core.jq_second_order
import Submission.Work.Asymptotics.funnelTailBasic

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

open Work.Asymptotics.KhatE1Core (Big)

/-!
# The sharp funnel bound for the `E(z)^5`-coefficient `KdevA5`

`KdevA5 ℓ τ = (3456π)⁻¹·N5` is the `E(z)^5`-coefficient of the sharp funnel residual
`Wres = Kdev8Bracket - 2·KdevE2·E(z)²` (verified numerically against the kernel model to
`≥ 19` digits at two values of `τ`), with

`N5 = R8_p4 + γ·24·E1combo8 + Dev8Raw5 + (j-720)·Dev8Raw3`,   `γ = (j-720)² - 179280 - 24j`.

## The proof

Write `q = qParamFun τ`, `Λ = πiτ + cuspC ℓ`, `j = jInvariantFun τ`, `E(z) = Ept z`, and let
`P = ψ₂E₆/E₄`, `Q = ψ₂E₁₄/Δ = jP`.  The exact `j`-decomposition of `N5` (verified by `ring`) is

  `N5 = S₃j³ + S₂j² + S₁j + S₀`,
  `S₃ = 24(ψ₄-P)`, `S₂ = 27648E₄ - 52704ψ₄ + 38880P`,
  `S₁ = -47738880E₄ + 24402960ψ₄ - 10855440P`, `S₀ = (54253283328/5)E₄ - 753214464ψ₄`.

The form is chosen so that the two leading cancellations are *exact* identities of truncated
polynomials in `q, Λ` (both `ring`-provable): with `jq = j·q` and the truncated atoms
`E₄ᵗ = 1+240q+2160q²`, `ψ₄ᵗ = 2Λ-(288Λ+744)q-(1824Λ+25972)q²`,
`(E₆/E₄)ᵗ = 1-744q+159768q²`, `Pᵗ = ψ₂ᵗ(E₆/E₄)ᵗ`, `jqᵗ = 1+744q` and the corresponding
`Sᵢᵗ`, one has, with `Ũ := S₃(jq) + qS₂`:

* `Ũᵗ := S₃ᵗ·jqᵗ + qS₂ᵗ = q²·𝕌`,  `𝕌 = 47738880 - 27095040Λ + O(q)`;
* `(jqᵗ)²𝕌 + jqᵗ·S₁ᵗ = q·𝕎`,  `𝕎 = -5403472128 - 5706436608Λ + O(q)`.

Since `q³N5 = (jq)²Ũ + q²(jq)S₁ + q³S₀` and the atom deviations are `O(q³)`, this gives
`q³N5 = O((scale τ)^N q³)`, i.e. `N5 = O((scale τ)^N)` — which is more than the requested
`O(‖q(τ)‖^{-1/2}(scale τ)^N(1+t)^M)` because `‖q‖ ≤ 1` on the funnel.
-/

private def qF (τ : ℍ) : ℂ := Work.Kernels.qParamFun τ

/-- `πiτ + cuspC ℓ`. -/
private def LamF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Asymptotics.KhatE1Core.cuspLin ℓ τ

/-- The numerator `N5` of `KdevA5` (the bracket before the factor `(3456π)⁻¹`). -/
private def N5 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Asymptotics.Compact.R8_p4 ℓ τ
    + ((Work.Kernels.jInvariantFun τ - 720) ^ 2 - 179280 - 24 * Work.Kernels.jInvariantFun τ)
        * (24 * Work.Asymptotics.E1combo8 ℓ τ)
    + Dev8Raw5 ℓ τ τ
    + (Work.Kernels.jInvariantFun τ - 720) * Dev8Raw3 ℓ τ τ

/-- `P = ψ₂·E₆/E₄`. -/
private def Pf (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ

private def S3f (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  24 * (Work.Kernels.psi4 ℓ τ - Pf ℓ τ)
private def S2f (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  27648 * Work.Kernels.E4Fun τ - 52704 * Work.Kernels.psi4 ℓ τ + 38880 * Pf ℓ τ
private def S1f (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  -47738880 * Work.Kernels.E4Fun τ + 24402960 * Work.Kernels.psi4 ℓ τ - 10855440 * Pf ℓ τ
private def S0f (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (54253283328 / 5 : ℂ) * Work.Kernels.E4Fun τ - 753214464 * Work.Kernels.psi4 ℓ τ

/-- The exact `j`-decomposition of `N5`. -/
private lemma N5_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) (hE4 : Work.Kernels.E4Fun τ ≠ 0) :
    N5 ℓ τ = S3f ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 3
      + S2f ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 2
      + S1f ℓ τ * Work.Kernels.jInvariantFun τ + S0f ℓ τ := by
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [N5, S3f, S2f, S1f, S0f, Pf, Work.Asymptotics.E1combo8, Dev8Raw3, Dev8Raw5,
    Work.Asymptotics.Compact.R8_p4, Work.Kernels.jInvariantFun, Work.Kernels.E14Fun,
    psi2E14oD]
  field_simp
  ring

/-! ## §2  The truncated atoms and the two exact cancellation identities -/

private def E4t (τ : ℍ) : ℂ := 1 + 240 * qF τ + 2160 * (qF τ) ^ 2
private def E6t (τ : ℍ) : ℂ := 1 - 504 * qF τ - 16632 * (qF τ) ^ 2
private def psi2t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ + (48 * LamF ℓ τ + 408) * qF τ + (48 * LamF ℓ τ + 2636) * (qF τ) ^ 2
private def psi4t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ - (288 * LamF ℓ τ + 744) * qF τ - (1824 * LamF ℓ τ + 25972) * (qF τ) ^ 2
private def E6oE4t (τ : ℍ) : ℂ := 1 - 744 * qF τ + 159768 * (qF τ) ^ 2
private def Pt (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := psi2t ℓ τ * E6oE4t τ
private def jqt (τ : ℍ) : ℂ := 1 + 744 * qF τ

private def S3t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := 24 * (psi4t ℓ τ - Pt ℓ τ)
private def S2t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  27648 * E4t τ - 52704 * psi4t ℓ τ + 38880 * Pt ℓ τ
private def S1t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  -47738880 * E4t τ + 24402960 * psi4t ℓ τ - 10855440 * Pt ℓ τ
private def S0t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (54253283328 / 5 : ℂ) * E4t τ - 753214464 * psi4t ℓ τ

/-- `𝕌 = q⁻²(S₃ᵗ·jqᵗ + q·S₂ᵗ)`, an explicit polynomial in `q, Λ`. -/
private def UU (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (47738880 - 27095040 * LamF ℓ τ)
    + qF τ * (-6879045888 + 5848492032 * LamF ℓ τ)
    + (qF τ) ^ 2 * (1319117177088 + 160295334912 * LamF ℓ τ)
    + (qF τ) ^ 3 * (8854224970752 + 161230196736 * LamF ℓ τ)

/-- `𝕎 = q⁻¹((jqᵗ)²·𝕌 + jqᵗ·S₁ᵗ)`, an explicit polynomial in `q, Λ`. -/
private def WW (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (-5403472128 - 5706436608 * LamF ℓ τ)
    + qF τ * (-5289410301696 - 2860081892352 * LamF ℓ τ)
    + (qF τ) ^ 2 * (-640353587323392 + 1067376902160384 * LamF ℓ τ)
    + (qF τ) ^ 3 * (228155580664487424 + 27237149826693120 * LamF ℓ τ)
    + (qF τ) ^ 4 * (1499749002392481792 + 27309541773459456 * LamF ℓ τ)

/-- **First cancellation**: `S₃ᵗ·jqᵗ + q·S₂ᵗ = q²·𝕌`. -/
private lemma UU_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    S3t ℓ τ * jqt τ + qF τ * S2t ℓ τ = (qF τ) ^ 2 * UU ℓ τ := by
  simp only [S3t, S2t, E4t, psi4t, Pt, psi2t, E6oE4t, jqt, UU]
  ring

/-- **Second cancellation**: `(jqᵗ)²·𝕌 + jqᵗ·S₁ᵗ = q·𝕎`. -/
private lemma WW_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    (jqt τ) ^ 2 * UU ℓ τ + jqt τ * S1t ℓ τ = qF τ * WW ℓ τ := by
  simp only [UU, WW, S1t, psi4t, Pt, psi2t, E6oE4t, E4t, jqt]
  ring

/-! ## §3  The `O(q²)`-truncations and the `Big` calculus -/

/-- `‖q(τ)‖ ≤ 1/2` on the funnel. -/
private lemma qF_norm_le_half (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) : ‖qF τ‖ ≤ 1 / 2 := by
  rw [qF, Work.Asymptotics.norm_qParamFun]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have h4 : Real.log 2 ≤ 2 * Real.pi * τ.im := by
    nlinarith [Real.pi_gt_three, hlog, hτ.2]
  calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(Real.log 2)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

private lemma qF_big : Big 1 (fun τ : ℍ => qF τ) := by
  refine ⟨1, 0, one_pos, le_rfl, fun τ _ => ?_⟩
  simp only [qF, Real.rpow_zero, mul_one, one_mul, pow_one, le_refl]

private lemma LamF_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => LamF ℓ τ) := by
  refine Big.of_scale (C := Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖ + 1) (N := 1)
    (by positivity) (by norm_num) (fun τ _ => ?_)
  rw [Real.rpow_one, LamF, Work.Asymptotics.KhatE1Core.cuspLin]
  exact Work.Asymptotics.KhatE1.kdevA4_cuspLin_le ℓ τ

namespace Big0

private lemma add {f g : ℍ → ℂ} (hf : Big 0 f) (hg : Big 0 g) :
    Big 0 (fun τ => f τ + g τ) := Big.mono (Big.add hf hg) (by norm_num)

private lemma sub {f g : ℍ → ℂ} (hf : Big 0 f) (hg : Big 0 g) :
    Big 0 (fun τ => f τ - g τ) := Big.mono (Big.sub hf hg) (by norm_num)

private lemma mul {f g : ℍ → ℂ} (hf : Big 0 f) (hg : Big 0 g) :
    Big 0 (fun τ => f τ * g τ) := Big.mono (Big.mul hf hg) (by norm_num)

private lemma cmul (c : ℂ) {f : ℍ → ℂ} (hf : Big 0 f) : Big 0 (fun τ => c * f τ) :=
  Big.const_mul c hf

private lemma const (c : ℂ) : Big 0 (fun _ : ℍ => c) := Big.const c

private lemma qpow (a : ℕ) : Big 0 (fun τ : ℍ => (qF τ) ^ a) :=
  Big.mono (Big.pow qF_big a) (Nat.zero_le _)

private lemma Lpow (ℓ : Work.Kernels.LogLambdaData) (b : ℕ) :
    Big 0 (fun τ : ℍ => (LamF ℓ τ) ^ b) :=
  Big.mono (Big.pow (LamF_big ℓ) b) (Nat.zero_le _)

/-- A monomial `c·qᵃ·Λᵇ` is `Big 0`. -/
private lemma mono (ℓ : Work.Kernels.LogLambdaData) (c : ℂ) (a b : ℕ) :
    Big 0 (fun τ : ℍ => c * (qF τ) ^ a * (LamF ℓ τ) ^ b) :=
  Big0.mul (Big.const_mul c (Big0.qpow a)) (Big0.Lpow ℓ b)

end Big0

private lemma E4t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => E4t τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (1 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0 + (240 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (2160 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [E4t]; ring)

private lemma E6t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => E6t τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (1 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0 + (-504 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (-16632 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [E6t]; ring)

private lemma jqt_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => jqt τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (1 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0 + (744 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [jqt]; ring)

private lemma E6oE4t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => E6oE4t τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (1 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0 + (-744 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (159768 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [E6oE4t]; ring)

private lemma psi2t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => psi2t ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (2 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 1 + (408 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (48 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 1 + (2636 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0
        + (48 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 1) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [psi2t]; ring)

private lemma psi4t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => psi4t ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (2 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 1 + (-744 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (-288 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 1 + (-25972 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0
        + (-1824 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 1) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [psi4t]; ring)

private lemma Pt_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => Pt ℓ τ) := by
  have h := Big0.mul (psi2t_big ℓ) (E6oE4t_big ℓ)
  exact Big.congr h (fun τ => by simp only [Pt])


/-- `S₃ᵗ/q`, the explicit cofactor of `q` in `S₃ᵗ`. -/
private def S3tq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (-27648 + 27648 * LamF ℓ τ)
    + qF τ * (6598656 - 6856704 * LamF ℓ τ)
    + (qF τ) ^ 2 * (-1517379840 - 183195648 * LamF ℓ τ)
    + (qF τ) ^ 3 * (-10107562752 - 184052736 * LamF ℓ τ)

private lemma S3tq_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => S3tq ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (-27648 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0 + (27648 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 1
        + (6598656 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (-6856704 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 1
        + (-1517379840 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0
        + (-183195648 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 1
        + (-10107562752 : ℂ) * (qF τ) ^ 3 * (LamF ℓ τ) ^ 0
        + (-184052736 : ℂ) * (qF τ) ^ 3 * (LamF ℓ τ) ^ 1) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [S3tq]; ring)

/-- `S₃ᵗ = O(‖q‖(scale τ)^N)`. -/
private lemma S3t_big (ℓ : Work.Kernels.LogLambdaData) : Big 1 (fun τ : ℍ => S3t ℓ τ) := by
  have h : Big 1 (fun τ : ℍ => qF τ * S3tq ℓ τ) := Big.mul qF_big (S3tq_big ℓ)
  refine Big.congr h (fun τ => ?_)
  simp only [S3t, S3tq, Pt, E6oE4t, psi4t, psi2t]
  ring

private lemma S2t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => S2t ℓ τ) := by
  have h : Big 0 (fun τ : ℍ => 27648 * E4t τ - 52704 * psi4t ℓ τ + 38880 * Pt ℓ τ) :=
    Big0.add (Big0.sub (Big0.cmul 27648 (E4t_big ℓ)) (Big0.cmul 52704 (psi4t_big ℓ)))
      (Big0.cmul 38880 (Pt_big ℓ))
  exact Big.congr h (fun τ => by simp only [S2t])

private lemma S1t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => S1t ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      -47738880 * E4t τ + 24402960 * psi4t ℓ τ - 10855440 * Pt ℓ τ) :=
    Big0.sub (Big0.add (Big0.cmul (-47738880) (E4t_big ℓ)) (Big0.cmul 24402960 (psi4t_big ℓ)))
      (Big0.cmul 10855440 (Pt_big ℓ))
  exact Big.congr h (fun τ => by simp only [S1t])

private lemma S0t_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => S0t ℓ τ) := by
  have h : Big 0 (fun τ : ℍ => (54253283328 / 5 : ℂ) * E4t τ - 753214464 * psi4t ℓ τ) :=
    Big0.sub (Big0.cmul (54253283328 / 5 : ℂ) (E4t_big ℓ)) (Big0.cmul 753214464 (psi4t_big ℓ))
  exact Big.congr h (fun τ => by simp only [S0t])

private lemma UU_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => UU ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (47738880 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0
        + (-27095040 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 1
        + (-6879045888 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (5848492032 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 1
        + (1319117177088 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0
        + (160295334912 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 1
        + (8854224970752 : ℂ) * (qF τ) ^ 3 * (LamF ℓ τ) ^ 0
        + (161230196736 : ℂ) * (qF τ) ^ 3 * (LamF ℓ τ) ^ 1) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [UU]; ring)

private lemma WW_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => WW ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (-5403472128 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 0
        + (-5706436608 : ℂ) * (qF τ) ^ 0 * (LamF ℓ τ) ^ 1
        + (-5289410301696 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 0
        + (-2860081892352 : ℂ) * (qF τ) ^ 1 * (LamF ℓ τ) ^ 1
        + (-640353587323392 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 0
        + (1067376902160384 : ℂ) * (qF τ) ^ 2 * (LamF ℓ τ) ^ 1
        + (228155580664487424 : ℂ) * (qF τ) ^ 3 * (LamF ℓ τ) ^ 0
        + (27237149826693120 : ℂ) * (qF τ) ^ 3 * (LamF ℓ τ) ^ 1
        + (1499749002392481792 : ℂ) * (qF τ) ^ 4 * (LamF ℓ τ) ^ 0
        + (27309541773459456 : ℂ) * (qF τ) ^ 4 * (LamF ℓ τ) ^ 1) := by
    repeat' first | apply Big0.add | exact Big0.mono ℓ _ _ _
  exact Big.congr h (fun τ => by simp only [WW]; ring)


/-! ## §4  The atom deviations -/

/-- `jq = j(τ)·q(τ)`. -/
private def jqF (τ : ℍ) : ℂ := Work.Kernels.jInvariantFun τ * qF τ

private lemma E4_dev : Big 3 (fun τ : ℍ => Work.Kernels.E4Fun τ - E4t τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.e4ThreeTerm
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  simp only []
  have h1 := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have hgoal : Work.Kernels.E4Fun τ - E4t τ
      = Work.Kernels.E4Fun τ - 1 - 240 * qF τ - 2160 * (qF τ) ^ 2 := by
    simp only [E4t]; ring
  rw [hgoal]
  simpa only [qF, Real.rpow_zero, mul_one] using h1

private lemma E6_dev : Big 3 (fun τ : ℍ => Work.Kernels.E6Fun τ - E6t τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.e6ThreeTerm
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  simp only []
  have h1 := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have hgoal : Work.Kernels.E6Fun τ - E6t τ
      = Work.Kernels.E6Fun τ - 1 + 504 * qF τ + 16632 * (qF τ) ^ 2 := by
    simp only [E6t]; ring
  rw [hgoal]
  simpa only [qF, Real.rpow_zero, mul_one] using h1

private lemma psi2_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => Work.Kernels.psi2 ℓ τ - psi2t ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  simp only []
  have h1 := (h τ hτ).1
  have hgoal : Work.Kernels.psi2 ℓ τ - psi2t ℓ τ
      = Work.Kernels.psi2 ℓ τ - 2 * LamF ℓ τ - (48 * LamF ℓ τ + 408) * qF τ
          - (48 * LamF ℓ τ + 2636) * (qF τ) ^ 2 := by
    simp only [psi2t]; ring
  rw [hgoal]
  simpa only [qF, LamF, Work.Asymptotics.KhatE1Core.cuspLin] using h1

private lemma psi4_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => Work.Kernels.psi4 ℓ τ - psi4t ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  simp only []
  have h1 := (h τ hτ).2
  have hgoal : Work.Kernels.psi4 ℓ τ - psi4t ℓ τ
      = Work.Kernels.psi4 ℓ τ - 2 * LamF ℓ τ + (288 * LamF ℓ τ + 744) * qF τ
          + (1824 * LamF ℓ τ + 25972) * (qF τ) ^ 2 := by
    simp only [psi4t]; ring
  rw [hgoal]
  simpa only [qF, LamF, Work.Asymptotics.KhatE1Core.cuspLin] using h1

private lemma jq_dev : Big 2 (fun τ : ℍ => jqF τ - jqt τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.jq_second_order
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  simp only []
  have h1 := h τ hτ.2
  have hgoal : jqF τ - jqt τ
      = Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ
          - 1 - 744 * Work.Kernels.qParamFun τ := by
    simp only [jqF, qF, jqt]; ring
  rw [hgoal]
  simpa only [qF, Real.rpow_zero, mul_one] using h1

private lemma jqF_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => jqF τ) := by
  refine Big.congr (Big.mono (Big.add jq_dev (jqt_big ℓ)) ?_) (fun τ => by simp only [jqF]; ring)
  norm_num


private lemma E4_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
  Big.congr (Big.mono (Big.add E4_dev (E4t_big ℓ)) (by norm_num))
    (fun τ => by ring)

private lemma E6_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => Work.Kernels.E6Fun τ) :=
  Big.congr (Big.mono (Big.add E6_dev (E6t_big ℓ)) (by norm_num))
    (fun τ => by ring)

private lemma psi2_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) :=
  Big.congr (Big.mono (Big.add (psi2_dev ℓ) (psi2t_big ℓ)) (by norm_num))
    (fun τ => by ring)

private lemma psi4_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) :=
  Big.congr (Big.mono (Big.add (psi4_dev ℓ) (psi4t_big ℓ)) (by norm_num))
    (fun τ => by ring)

private lemma E4Fun_ne_zero (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    Work.Kernels.E4Fun τ ≠ 0 := by
  intro h0
  have h := Work.FunnelNumerics.E4_sub_one_le τ hτ.2
  rw [h0] at h
  norm_num at h

private lemma E4_inv_big : Big 0 (fun τ : ℍ => (Work.Kernels.E4Fun τ)⁻¹) := by
  refine Big.of_bdd (by norm_num : (0 : ℝ) < 2) (fun τ hτ => ?_)
  have h1 : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun τ‖ := by
    have h := abs_norm_sub_norm_le (Work.Kernels.E4Fun τ) 1
    rw [norm_one] at h
    have hle := Work.FunnelNumerics.E4_sub_one_le τ hτ.2
    have h2 := abs_le.mp (le_trans h hle)
    linarith [h2.1]
  rw [norm_inv]
  have h3 : (2 : ℝ)⁻¹ ≤ ‖Work.Kernels.E4Fun τ‖ := by norm_num at h1 ⊢; linarith
  exact (inv_le_comm₀ (by norm_num : (0 : ℝ) < 2)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) h1)).mp h3

private lemma E6oE4t_mul_E4t_dev :
    Big 3 (fun τ : ℍ => E6oE4t τ * E4t τ - E6t τ) := by
  refine ⟨36737280 + 345098880, 0, by norm_num, le_rfl, fun τ hτ => ?_⟩
  simp only []
  have hgoal : E6oE4t τ * E4t τ - E6t τ
      = (36737280 : ℂ) * (qF τ) ^ 3 + (345098880 : ℂ) * (qF τ) ^ 4 := by
    simp only [E6oE4t, E4t, E6t]; ring
  have hq1 : ‖qF τ‖ ≤ 1 := Big.qnorm_le_one τ hτ
  have h0 : (0 : ℝ) ≤ ‖qF τ‖ := norm_nonneg _
  have h2 : ‖(36737280 : ℂ) * (qF τ) ^ 3 + (345098880 : ℂ) * (qF τ) ^ 4‖
      ≤ (36737280 + 345098880) * ‖qF τ‖ ^ 3 := by
    have h3 : ‖(36737280 : ℂ) * (qF τ) ^ 3‖ ≤ 36737280 * ‖qF τ‖ ^ 3 := by
      rw [norm_mul, norm_pow]
      norm_num
    have h4 : ‖(345098880 : ℂ) * (qF τ) ^ 4‖ ≤ 345098880 * ‖qF τ‖ ^ 3 := by
      rw [norm_mul, norm_pow]
      have h6 : ‖(345098880 : ℂ)‖ = 345098880 := by norm_num
      rw [h6]
      have h5 : ‖qF τ‖ ^ 4 ≤ ‖qF τ‖ ^ 3 := by nlinarith [h0, hq1, pow_nonneg h0 3]
      exact mul_le_mul_of_nonneg_left h5 (by norm_num)
    refine le_trans (norm_add_le _ _) ?_
    linarith
  rw [hgoal, Real.rpow_zero, mul_one]
  exact h2


private lemma E6oE4_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ - E6oE4t τ) := by
  have hB : Big 3 (fun τ : ℍ => Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ * E6oE4t τ) := by
    have h1 : Big 3 (fun τ : ℍ =>
        (E6oE4t τ * E4t τ - E6t τ) + E6oE4t τ * (Work.Kernels.E4Fun τ - E4t τ)) :=
      Big.mono (Big.add E6oE4t_mul_E4t_dev (Big.mul (E6oE4t_big ℓ) E4_dev)) (by norm_num)
    have h1' : Big 3 (fun τ : ℍ => E6oE4t τ * Work.Kernels.E4Fun τ - E6t τ) :=
      Big.congr h1 (fun τ => by ring)
    have h2 : Big 3 (fun τ : ℍ =>
        (Work.Kernels.E6Fun τ - E6t τ) - (E6oE4t τ * Work.Kernels.E4Fun τ - E6t τ)) :=
      Big.mono (Big.sub E6_dev h1') (by norm_num)
    exact Big.congr h2 (fun τ => by ring)
  have hdiv : Big 3 (fun τ : ℍ =>
      (Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ * E6oE4t τ) * (Work.Kernels.E4Fun τ)⁻¹) :=
    Big.mono (Big.mul hB E4_inv_big) (by norm_num)
  refine Big.congr_on hdiv (fun τ hτ => ?_)
  have h0 := E4Fun_ne_zero τ hτ
  field_simp

private lemma E6oE4_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) :=
  Big.congr (Big.mono (Big.add (E6oE4_dev ℓ) (E6oE4t_big ℓ)) (by norm_num))
    (fun τ => by ring)

private lemma P_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => Pf ℓ τ - Pt ℓ τ) := by
  have h : Big 3 (fun τ : ℍ =>
      (Work.Kernels.psi2 ℓ τ - psi2t ℓ τ) * (Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
        + psi2t ℓ τ * (Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ - E6oE4t τ)) :=
    Big.mono (Big.add (Big.mul (psi2_dev ℓ) (E6oE4_big ℓ)) (Big.mul (psi2t_big ℓ) (E6oE4_dev ℓ)))
      (by norm_num)
  exact Big.congr h (fun τ => by simp only [Pf, Pt]; ring)

private lemma S3_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => S3f ℓ τ - S3t ℓ τ) := by
  have h : Big 3 (fun τ : ℍ =>
      24 * (Work.Kernels.psi4 ℓ τ - psi4t ℓ τ) - 24 * (Pf ℓ τ - Pt ℓ τ)) :=
    Big.mono (Big.sub (Big.const_mul 24 (psi4_dev ℓ)) (Big.const_mul 24 (P_dev ℓ))) (by norm_num)
  exact Big.congr h (fun τ => by simp only [S3f, S3t]; ring)

private lemma S2_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => S2f ℓ τ - S2t ℓ τ) := by
  have h : Big 3 (fun τ : ℍ =>
      27648 * (Work.Kernels.E4Fun τ - E4t τ) - 52704 * (Work.Kernels.psi4 ℓ τ - psi4t ℓ τ)
        + 38880 * (Pf ℓ τ - Pt ℓ τ)) :=
    Big.mono (Big.add (Big.sub (Big.const_mul 27648 E4_dev) (Big.const_mul 52704 (psi4_dev ℓ)))
      (Big.const_mul 38880 (P_dev ℓ))) (by norm_num)
  exact Big.congr h (fun τ => by simp only [S2f, S2t]; ring)

private lemma S1_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => S1f ℓ τ - S1t ℓ τ) := by
  have h : Big 3 (fun τ : ℍ =>
      -47738880 * (Work.Kernels.E4Fun τ - E4t τ) + 24402960 * (Work.Kernels.psi4 ℓ τ - psi4t ℓ τ)
        - 10855440 * (Pf ℓ τ - Pt ℓ τ)) :=
    Big.mono (Big.sub (Big.add (Big.const_mul (-47738880) E4_dev) (Big.const_mul 24402960 (psi4_dev ℓ)))
      (Big.const_mul 10855440 (P_dev ℓ))) (by norm_num)
  exact Big.congr h (fun τ => by simp only [S1f, S1t]; ring)

private lemma S0f_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => S0f ℓ τ) := by
  have h : Big 0 (fun τ : ℍ =>
      (54253283328 / 5 : ℂ) * Work.Kernels.E4Fun τ - 753214464 * Work.Kernels.psi4 ℓ τ) :=
    Big.mono (Big.sub (Big.const_mul (54253283328 / 5 : ℂ) (E4_big ℓ))
      (Big.const_mul 753214464 (psi4_big ℓ))) (by norm_num)
  exact Big.congr h (fun τ => by simp only [S0f])

private lemma jqdiff_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => (jqF τ) ^ 2 - (jqt τ) ^ 2) := by
  have h : Big 2 (fun τ : ℍ => (jqF τ - jqt τ) * (jqF τ + jqt τ)) :=
    Big.mono (Big.mul jq_dev (Big.mono (Big.add (jqF_big ℓ) (jqt_big ℓ)) (Nat.zero_le _)))
      (by norm_num)
  exact Big.congr h (fun τ => by ring)

/-! ## §5  The assembly -/

/-- `Ũ = S₃(qj) + qS₂`. -/
private def U17 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := S3f ℓ τ * jqF τ + qF τ * S2f ℓ τ
/-- `Ũᵗ = S₃ᵗ·jqᵗ + qS₂ᵗ`. -/
private def U17t (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := S3t ℓ τ * jqt τ + qF τ * S2t ℓ τ

private lemma U17t_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    U17t ℓ τ = (qF τ) ^ 2 * UU ℓ τ := UU_eq ℓ τ

private lemma jqF_sq_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => (jqF τ) ^ 2) :=
  Big.mono (Big.pow (jqF_big ℓ) 2) (Nat.zero_le _)

private lemma deltaU_dev (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => U17 ℓ τ - U17t ℓ τ) := by
  have h : Big 3 (fun τ : ℍ => (S3f ℓ τ - S3t ℓ τ) * jqF τ + S3t ℓ τ * (jqF τ - jqt τ)
      + qF τ * (S2f ℓ τ - S2t ℓ τ)) :=
    Big.mono (Big.add (Big.add (Big.mul (S3_dev ℓ) (jqF_big ℓ)) (Big.mul (S3t_big ℓ) jq_dev))
      (Big.mul qF_big (S2_dev ℓ))) (by norm_num)
  exact Big.congr h (fun τ => by simp only [U17, U17t]; ring)

private lemma N5_cube (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ)
    (hE4 : Work.Kernels.E4Fun τ ≠ 0) :
    (qF τ) ^ 3 * N5 ℓ τ = (jqF τ) ^ 2 * U17 ℓ τ + (qF τ) ^ 2 * jqF τ * S1f ℓ τ
      + (qF τ) ^ 3 * S0f ℓ τ := by
  have hq : qF τ ≠ 0 := fun h0 => Work.Asymptotics.qParamFun_ne_zero' τ (by simpa [qF] using h0)
  have h := N5_eq ℓ τ hE4
  have hj : Work.Kernels.jInvariantFun τ = jqF τ / qF τ := by rw [jqF]; field_simp
  rw [h]
  have step1 : (qF τ) ^ 3 * (S3f ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 3
        + S2f ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 2
        + S1f ℓ τ * Work.Kernels.jInvariantFun τ + S0f ℓ τ)
      = (jqF τ) ^ 3 * S3f ℓ τ + qF τ * (jqF τ) ^ 2 * S2f ℓ τ
        + (qF τ) ^ 2 * jqF τ * S1f ℓ τ + (qF τ) ^ 3 * S0f ℓ τ := by
    rw [hj]
    field_simp [hq]

  rw [step1]
  simp only [U17, jqF]
  ring


private lemma N5_big (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => N5 ℓ τ) := by
  -- ## the truncated part of the residual
  have hV1 : Big 3 (fun τ : ℍ => (jqF τ) ^ 2 * U17t ℓ τ + (qF τ) ^ 2 * jqF τ * S1t ℓ τ) := by
    have hA : Big 3 (fun τ : ℍ => (qF τ) ^ 3 * WW ℓ τ) :=
      Big.mono (Big.mul (Big.pow qF_big 3) (WW_big ℓ)) (by norm_num)
    have hB : Big 3 (fun τ : ℍ => (qF τ) ^ 2 * ((jqF τ) ^ 2 - (jqt τ) ^ 2) * UU ℓ τ) :=
      Big.mono (Big.mul (Big.mul (Big.pow qF_big 2) (jqdiff_dev ℓ)) (UU_big ℓ)) (by norm_num)
    have hC : Big 3 (fun τ : ℍ => (qF τ) ^ 2 * (jqF τ - jqt τ) * S1t ℓ τ) :=
      Big.mono (Big.mul (Big.mul (Big.pow qF_big 2) jq_dev) (S1t_big ℓ)) (by norm_num)
    have hABC : Big 3 (fun τ : ℍ => (qF τ) ^ 3 * WW ℓ τ
        + (qF τ) ^ 2 * ((jqF τ) ^ 2 - (jqt τ) ^ 2) * UU ℓ τ
        + (qF τ) ^ 2 * (jqF τ - jqt τ) * S1t ℓ τ) :=
      Big.congr (Big.add (Big.add hA hB) hC) (fun τ => by ring)
    refine Big.congr hABC (fun τ => ?_)
    have h1 : U17t ℓ τ = (qF τ) ^ 2 * UU ℓ τ := U17t_eq ℓ τ
    have h2 : (jqt τ) ^ 2 * UU ℓ τ + jqt τ * S1t ℓ τ = qF τ * WW ℓ τ := WW_eq ℓ τ
    have key : (jqF τ) ^ 2 * ((qF τ) ^ 2 * UU ℓ τ) + (qF τ) ^ 2 * jqF τ * S1t ℓ τ
        = (qF τ) ^ 2 * (qF τ * WW ℓ τ + ((jqF τ) ^ 2 - (jqt τ) ^ 2) * UU ℓ τ
            + (jqF τ - jqt τ) * S1t ℓ τ) := by
      rw [← h2]; ring
    rw [h1, key]
    ring
  -- ## the deviation part
  have hV2 : Big 3 (fun τ : ℍ => (jqF τ) ^ 2 * (U17 ℓ τ - U17t ℓ τ)
      + (qF τ) ^ 2 * jqF τ * (S1f ℓ τ - S1t ℓ τ) + (qF τ) ^ 3 * S0f ℓ τ) := by
    have hA : Big 3 (fun τ : ℍ => (jqF τ) ^ 2 * (U17 ℓ τ - U17t ℓ τ)) :=
      Big.mono (Big.mul (jqF_sq_big ℓ) (deltaU_dev ℓ)) (by norm_num)
    have hB : Big 3 (fun τ : ℍ => (qF τ) ^ 2 * jqF τ * (S1f ℓ τ - S1t ℓ τ)) :=
      Big.mono (Big.mul (Big.mul (Big.pow qF_big 2) (jqF_big ℓ)) (S1_dev ℓ)) (by norm_num)
    have hC : Big 3 (fun τ : ℍ => (qF τ) ^ 3 * S0f ℓ τ) :=
      Big.mono (Big.mul (Big.pow qF_big 3) (S0f_big ℓ)) (by norm_num)
    exact Big.congr (Big.add (Big.add hA hB) hC) (fun τ => by ring)
  -- ## assemble
  have hV : Big 3 (fun τ : ℍ => (jqF τ) ^ 2 * U17 ℓ τ + (qF τ) ^ 2 * jqF τ * S1f ℓ τ
      + (qF τ) ^ 3 * S0f ℓ τ) :=
    Big.congr (Big.add hV1 hV2) (fun τ => by ring)
  have hVq : Big 3 (fun τ : ℍ => (qF τ) ^ 3 * N5 ℓ τ) :=
    Big.congr_on hV (fun τ hτ => (N5_cube ℓ τ (E4Fun_ne_zero τ hτ)).symm)
  obtain ⟨C, N, hC, hN, hf⟩ := hVq
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  simp only []
  have hq3 : 0 < ‖qF τ‖ ^ 3 := by
    apply pow_pos; rw [qF, norm_pos_iff]; exact Work.Asymptotics.qParamFun_ne_zero' τ
  have h1 := hf τ hτ
  have h2 : ‖(qF τ) ^ 3 * N5 ℓ τ‖ = ‖qF τ‖ ^ 3 * ‖N5 ℓ τ‖ := by rw [norm_mul, norm_pow]
  rw [h2] at h1
  have h3 : C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3
      = ‖qF τ‖ ^ 3 * (C * (Work.Kernels.scale τ) ^ N) := by rw [qF]; ring
  rw [h3] at h1
  have h4 := le_of_mul_le_mul_left h1 hq3
  simpa only [pow_zero, mul_one] using h4

/-- **The `E(z)^5`-coefficient of the sharp funnel residual is `O(‖q(τ)‖^{-1/2})`.** -/
theorem KdevA5Sharp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖KdevA5 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ)
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, hC, hN, hN5⟩ := N5_big ℓ
  refine ⟨‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * C, N, 0,
    mul_pos (norm_pos_iff.mpr (inv_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)))) hC, hN, le_rfl, ?_⟩
  intro τ z t hτ ht h1z h2z hzt
  have hK : KdevA5 ℓ τ z = (((3456 : ℂ) * (Real.pi : ℂ))⁻¹) * N5 ℓ τ := by
    simp only [KdevA5, N5, Dev8Raw3, Dev8Raw5]
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := Big.qnorm_le_one τ hτ
  have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_pos_iff]; exact Work.Asymptotics.qParamFun_ne_zero' τ
  have hqinv : (1 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hqpos hq1 (by norm_num)
  have hbase : (0 : ℝ) ≤ C * (Work.Kernels.scale τ) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N)
  have hfin : ‖N5 ℓ τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ)
      * (Work.Kernels.scale τ) ^ N := by
    have h0 : ‖N5 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
      have h := hN5 τ hτ
      simpa only [pow_zero, mul_one] using h
    calc ‖N5 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := h0
      _ = (C * (Work.Kernels.scale τ) ^ N) * 1 := by ring
      _ ≤ (C * (Work.Kernels.scale τ) ^ N) * ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_left hqinv hbase
      _ = C * ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ) * (Work.Kernels.scale τ) ^ N := by ring
  have hone : (1 + t) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  rw [hK, norm_mul]
  calc ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * ‖N5 ℓ τ‖
      ≤ ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖
          * (C * ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ) * (Work.Kernels.scale τ) ^ N) :=
        mul_le_mul_of_nonneg_left hfin (norm_nonneg _)
    _ = (‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * C)
          * ‖Work.Kernels.qParamFun τ‖ ^ (-(1 / 2) : ℝ) * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ (0 : ℝ) := by rw [hone]; ring

end
end Work.Asymptotics.KhatE1

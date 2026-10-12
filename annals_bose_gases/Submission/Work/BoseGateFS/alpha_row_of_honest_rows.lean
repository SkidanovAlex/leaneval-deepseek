import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.alpha_lip_abs2
import Submission.Work.BoseGateFS.tauTilde_lip
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.alpha_row_of_honest_rows` — the K3 row at the honest rows

This is the `hα`-row of the honest-rows gate (`FINDINGS_honestRows.md` §3) in the
form in which the *caller* of `HonestGateFinal` has it: instead of the FS §11 rows
of the honest model, the hypotheses are the four things the gate really consumes —

* `Ŵ₁`'s pointwise `L¹` row `|Ŵ₁(k)| ≤ 16πa` (`hW1le`) and the calibrated row
  `|Ŵ₁(k)| ≤ K₀a` (`hW1leK`),
* `Ŵ₁`'s mode-level Lipschitz row (`hW1grad`),
* the `τ̃`-régime row `(2dsℓ)⁻¹ ≤ (1/4)(4K_Ha)⁻¹` (`hρ₀`), which is what places
  the two arguments of `tauTilde_lip` above the threshold `ρ₀ = (4K_Ha)⁻¹` of
  `F.PHq`,
* the `τ`-domination on `P_H^q` (`hτdom`), which supplies both the `τ̃`-lower
  bound (`cτ = 1/2`) and the two `P_H^q` quadratic rows `𝒜 ≥ ‖k‖²/2`,
  `2|ℬ| ≤ 𝒜` (`Work.BoseGateFS.A_ge_of_taurad`),

and the conclusion is K3 with the absolute constant
`10¹²(16π + C_g + 2 + 1)⁴(1 + 1/(1/2))⁴(1 + 1/a)⁴` on the *repointed*
environment `KzEnvAt E ρ`, valid for every admissible density
`ρ ∈ [μ/2, 3μ/2]`.

The proof is the assembly of the three already-proved pieces:

1. `Work.BoseGateFS.tauTilde_lip` at `ρ₀ = (4K_Ha)⁻¹` (this is the only place
   where `FSParamsView` is used: `d = X⁶ ≤ 1`, `s = X > 0`, `ε_T = X^{23/4} ≤ 1`
   give the two régime rows `hA1`, `hA2` from `hρ₀`), with `htau` converting
   `E.tau` into `τ̃`;
2. the `τ`-lower bound `(1/2)‖q‖² ≤ τ q` on `P_H^q` from `hτdom` (the term
   `3ρK₀a` is dropped, it is nonnegative);
3. `Work.BoseGateFS.alpha_lip_abs2` at `E := KzEnvAt E ρ` with `Cw := 16π`,
   `Cg`, `Cτ := 2`, `cτ := 1/2`, using `Work.BoseFixR.KzEnvAt`'s definitional
   shape for `𝒜, ℬ`, `A_ge_of_taurad` for the quadratic rows, and
   `(KzEnvAt E ρ).rho = ρ` for the repointed density.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseGateFS

/-- `KzEnvAt`'s derived density: `(KzEnvAt E ρ).rho = ρ` for `ρ ≥ 0` and `ℓ ≠ 0`.
(`Work.BoseFixR.KzEnvAt` only changes `z`, `A`, `B`, so `rho = z²/ℓ³` becomes `ρ`.) -/
lemma kzEnvAt_rho_of_nonneg_gen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {E : Work.BoseB7.Q3Env Mode} {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (Work.BoseFixR.KzEnvAt E ρ).rho = ρ := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  show (Real.sqrt (ρ * E.ell ^ 3)) ^ 2 / E.ell ^ 3 = ρ
  rw [Real.sq_sqrt (by positivity), mul_div_assoc, div_self (pow_ne_zero 3 (ne_of_gt hℓ)),
    mul_one]

set_option maxHeartbeats 0 in
theorem alpha_row_of_honest_rows {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode}
    (hv : Work.BoseB7.FSParamsView E) {K₀ Cg : ℝ} (hK₀ : 0 ≤ K₀) (hCg0 : 0 ≤ Cg)
    (hKHa : 1 ≤ E.KH * E.aScat)
    (hW1le : ∀ k : Mode, |E.W1 k| ≤ 16 * Real.pi * E.aScat)
    (hW1leK : ∀ k : Mode, |E.W1 k| ≤ K₀ * E.aScat)
    (hW1grad : ∀ p q : Mode, |E.W1 p - E.W1 q| ≤ Cg * E.aScat * ‖F.kmom p - F.kmom q‖)
    (hρ₀ : (2 * E.d * E.s * E.ell)⁻¹ ≤ (1 / 4) * (4 * E.KH * E.aScat)⁻¹)
    {φ : ℝ → ℝ} (hφge : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r)
    (hφquad : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ r : ℝ, 2 ≤ r → φ r = (r - 3 / 2) ^ 2 + c₀)
    (htau : ∀ k : Mode, E.tau k = Work.BoseGateFS.tauTilde φ E.eT E.s E.d E.ell (F.kmom k))
    (hτdom : ∀ ρ : ℝ, 0 ≤ ρ → E.mu / 2 ≤ ρ → ρ ≤ 3 * E.mu / 2 →
      ∀ q : Mode, F.PHq E.KH E.aScat q →
        ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q) :
    ∀ ρ : ℝ, 0 ≤ ρ → E.mu / 2 ≤ ρ → ρ ≤ 3 * E.mu / 2 →
      ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
        |(Work.BoseFixR.KzEnvAt E ρ).alpha p - (Work.BoseFixR.KzEnvAt E ρ).alpha q|
          ≤ 10 ^ 12 * (16 * Real.pi + Cg + 2 + 1) ^ 4 * (1 + 1 / (1 / 2 : ℝ)) ^ 4
              * (1 + 1 / E.aScat) ^ 4 * E.lille * (E.KH * E.aScat)
              * ‖F.kmom p - F.kmom q‖ := by
  intro ρ hρ0 hρlo hρhi p q hp hq
  have ha : 0 < E.aScat := hv.a_pos
  have hKH_pos : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hρE : (Work.BoseFixR.KzEnvAt E ρ).rho = ρ := kzEnvAt_rho_of_nonneg_gen hρ0 hℓ
  -- ## 0. the `τ̃`-régime rows of the threshold bundle
  have hd0 : 0 < E.d := by rw [hv.d_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hd1 : E.d ≤ 1 := by
    rw [hv.d_eq]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  have hs0 : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have heT0 : 0 ≤ E.eT := by rw [hv.eT_eq]; exact (Work.BoseBox.fsXp_pos hv.t_pos).le
  have heT1 : E.eT ≤ 1 := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  have hXpos : 0 < 2 * E.d * E.s * E.ell := by positivity
  have hYpos : 0 < 4 * E.KH * E.aScat := by positivity
  have hcong : (1 / 4 : ℝ) * (4 * E.KH * E.aScat)⁻¹
      = (4 * (4 * E.KH * E.aScat))⁻¹ := by
    rw [mul_inv, mul_inv]
    ring
  have hprod : 4 * (4 * E.KH * E.aScat) ≤ 2 * E.d * E.s * E.ell := by
    have h := hρ₀
    rw [hcong] at h
    exact (inv_le_inv₀ hXpos (by positivity)).mp h
  have hA1 : (E.d * E.s * E.ell)⁻¹ ≤ (4 * E.KH * E.aScat)⁻¹ := by
    refine (inv_le_inv₀ (by positivity) hYpos).mpr ?_
    linarith [hprod, hYpos.le]
  have hA2 : 3 * ((1 - E.eT) * (2 * E.s * E.ell)⁻¹ + E.eT * (2 * E.d * E.s * E.ell)⁻¹)
      ≤ (4 * E.KH * E.aScat)⁻¹ := by
    have h2s : (2 * E.s * E.ell)⁻¹ ≤ (2 * E.d * E.s * E.ell)⁻¹ := by
      refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
      nlinarith [hd1, hs0.le, hℓ.le, hd0.le]
    have hsum : (1 - E.eT) * (2 * E.s * E.ell)⁻¹ + E.eT * (2 * E.d * E.s * E.ell)⁻¹
        ≤ (2 * E.d * E.s * E.ell)⁻¹ := by
      have hBnn : (0 : ℝ) ≤ (2 * E.d * E.s * E.ell)⁻¹ := by positivity
      have h1 : (1 - E.eT) * (2 * E.s * E.ell)⁻¹
          ≤ (1 - E.eT) * (2 * E.d * E.s * E.ell)⁻¹ :=
        mul_le_mul_of_nonneg_left h2s (by linarith)
      have h3 : (1 - E.eT) * (2 * E.d * E.s * E.ell)⁻¹
          ≤ 1 * (2 * E.d * E.s * E.ell)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hBnn
      linarith [h1, h3]
    have h3b : 3 * (2 * E.d * E.s * E.ell)⁻¹ ≤ (4 * E.KH * E.aScat)⁻¹ := by
      have hinn : (0 : ℝ) ≤ (4 * E.KH * E.aScat)⁻¹ := by positivity
      nlinarith [hρ₀, hinn]
    linarith [hsum, h3b]
  -- ## 1. the `τ`-Lipschitz row of K3, from `tauTilde_lip`
  have htau_grad : ∀ p' q' : Mode, F.PHq E.KH E.aScat p' → F.PHq E.KH E.aScat q' →
      |(Work.BoseFixR.KzEnvAt E ρ).tau p' - (Work.BoseFixR.KzEnvAt E ρ).tau q'|
        ≤ 2 * (‖F.kmom p'‖ + ‖F.kmom q'‖) * ‖F.kmom p' - F.kmom q'‖ := by
    intro p' q' hp' hq'
    have hp'' : (4 * E.KH * E.aScat)⁻¹ ≤ ‖F.kmom p'‖ := by
      rw [show (4 * E.KH * E.aScat)⁻¹ = 1 / (4 * E.KH * E.aScat) from (one_div _).symm]
      exact hp'
    have hq'' : (4 * E.KH * E.aScat)⁻¹ ≤ ‖F.kmom q'‖ := by
      rw [show (4 * E.KH * E.aScat)⁻¹ = 1 / (4 * E.KH * E.aScat) from (one_div _).symm]
      exact hq'
    have hlip := Work.BoseGateFS.tauTilde_lip (φ := φ) hφge hφquad heT0 heT1 hs0 hd0 hd1 hℓ
      hA1 hA2 hp'' hq''
    rwa [← htau p', ← htau q'] at hlip
  -- ## 2. the `τ`-lower bound on `P_H^q`, from `hτdom`
  have htau_lb : ∀ q' : Mode, F.PHq E.KH E.aScat q' →
      (1 / 2) * ‖F.kmom q'‖ ^ 2 ≤ (Work.BoseFixR.KzEnvAt E ρ).tau q' := by
    intro q' hq'
    have h1 := hτdom ρ hρ0 hρlo hρhi q' hq'
    have h2 : (0 : ℝ) ≤ 3 * ρ * K₀ * E.aScat :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) hK₀) ha.le
    show (1 / 2) * ‖F.kmom q'‖ ^ 2 ≤ E.tau q'
    linarith
  -- ## 3. the two quadratic rows on `P_H^q`
  have hAgeAB := A_ge_of_taurad (F := F) (E := E) (K₀ := K₀) hW1leK hρ0
    (fun q' hq' => hτdom ρ hρ0 hρlo hρhi q' hq')
  have hlille : (Work.BoseFixR.KzEnvAt E ρ).lille
      = (Work.BoseFixR.KzEnvAt E ρ).mu * (Work.BoseFixR.KzEnvAt E ρ).aScat ^ 3
        * (Work.BoseFixR.KzEnvAt E ρ).KH ^ 2 := by
    show Work.BoseB7.lille (Work.BoseFixR.KzEnvAt E ρ).mu (Work.BoseFixR.KzEnvAt E ρ).aScat
      (Work.BoseFixR.KzEnvAt E ρ).KH = _
    rw [Work.BoseB7.lille]
  -- ## 4. K3 at `KzEnvAt E ρ`, with the absolute constant
  have hres := alpha_lip_abs2 (F := F) (E := Work.BoseFixR.KzEnvAt E ρ)
    (Cw := 16 * Real.pi) (Cg := Cg) (Cτ := 2) (cτ := 1 / 2)
    (by positivity) hCg0 (by norm_num) (by norm_num)
    hKH_pos ha hKHa hlille
    (by rw [hρE]; exact hρ0) (by rw [hρE]; exact hρhi)
    (fun k => hW1le k) (fun p' q' => hW1grad p' q') htau_grad htau_lb
    (fun k => by rw [hρE]; rfl) (fun k => by rw [hρE]; rfl)
    hAgeAB.1 hAgeAB.2 p q hp hq
  exact hres

end Work.BoseGateFS

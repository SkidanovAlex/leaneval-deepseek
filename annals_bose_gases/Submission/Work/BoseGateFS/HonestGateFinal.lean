import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.viewFS_of_gate
import Submission.Work.BoseFixB1S.admRhoOfCloseCondFS
import Submission.Work.BoseGateFS.GateThresholdsExist
import Submission.Work.BoseGateFS.HonRowsExtra
import Submission.Work.BoseGateFS.LowCut_deriv_bound
import Submission.Work.BoseGateFS.Reserve
import Submission.Work.BoseGateFS.alpha_row_of_honest_rows
import Submission.Work.BoseGateFS.honE_count_PL
import Submission.Work.BoseGateFS.honE_hatChiSq_form_upper
import Submission.Work.BoseGateFS.honE_sum_hatChiSq
import Submission.Work.BoseGateFS.honE_tail_hatChiSq
import Submission.Work.BoseGateFS.honW1_lip
import Submission.Work.BoseGateFS.uvCut_W1_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.HonestGateFinal` — the honest gate from the FS rows

**The node's main theorem** (`exists_honestGateFS_of_fsRows`) delivers
`∃ K₀ b₀, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFS v h fc fu K₀ b₀` at **one absolute** pair
`(K₀, b₀)`, valid for every honest mode choice `HM` and every cube size `N ≥ Ng`.

Inputs (see `FINDINGS_honestRows.md`): FS §4's régime for the potential, the
parameter bundle `GateThresholds v h fc fu R`, and five FS §11/§12 rows, each at
an **absolute** constant:

* `hα` — K3 on `P_H^q` (`Work.BoseGateFS.alpha_lip_abs2` supplies it with
  `Cα = 10¹²(16π + Cg + 3)⁴·9⁴(1+1/a)⁴` once the `τ̃`-rows and the mode-level
  Lipschitz row of `Ŵ₁` are available).  The constant does *not* mention the mode
  set, which is what "one ABSOLUTE `K₀`" requires;
* `hW1grad` — the mode-level Lipschitz row of the honest `Ŵ₁` (the *pointwise
  power decay* of `Ŵ₁` is false for a general nonnegative radial `v` with the
  corpus's a.e. scattering solution, `Work.BoseB7AK/FINDING_W1rows.md` §3);
* `hsumW1sq` — FS §11's `eq:I2-integral` (the `L¹` row alone gives only `≍ Λ_N`,
  `FINDINGS_honestRows.md` §2);
* `hint` — FS §11's K5; `hq2` — FS §11's `eq:Q3Cancels` (the `½·dNumOpR` reserve
  is free, `Reserve`).

Everything else — the χ-rows, `Ŵ₁ω(0)`, FS's low-momentum positivity, the kinetic
domination, `A_ge`/`ABq` and the box-model equation — is *derived*.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

set_option maxHeartbeats 2000000

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-- `KzEnvAt`'s derived density: `(KzEnvAt E ρ).rho = ρ` for `ρ ≥ 0`. -/
lemma KzEnvAt_rho_of_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {E : Q3Env Mode} {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (KzEnvAt E ρ).rho = ρ := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  show (Real.sqrt (ρ * E.ell ^ 3)) ^ 2 / E.ell ^ 3 = ρ
  rw [Real.sq_sqrt (by positivity), mul_div_assoc, div_self (pow_ne_zero 3 (ne_of_gt hℓ)),
    mul_one]

/-- **The global `|ℬ| ≤ 𝒜`** at an environment of the honest shape: on `P_H^q` it
is the bundle's row `ABq`, off it FS's low-momentum positivity `W1low` makes both
`ℬ` and `𝒜` nonnegative. -/
lemma AB_global_hon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} {E : Q3Env Mode}
    (hρ : 0 ≤ E.rho) (hABq : ∀ k : Mode, F.PHq E.KH E.aScat k → 2 * |E.B k| ≤ E.A k)
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k)
    (htau0 : ∀ k : Mode, 0 ≤ E.tau k) (hA : ∀ k, E.A k = E.tau k + E.rho * E.W1 k)
    (hB : ∀ k, E.B k = E.rho * E.W1 k) :
    ∀ k : Mode, |E.B k| ≤ E.A k := by
  intro k
  by_cases hk : F.PHq E.KH E.aScat k
  · have h2 := hABq k hk
    have h3 : (0 : ℝ) ≤ |E.B k| := abs_nonneg _
    linarith
  · have hk' : ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) := le_of_lt (not_le.mp hk)
    have hW : 0 ≤ E.W1 k := hW1low k hk'
    have hBnn : 0 ≤ E.B k := by rw [hB k]; exact mul_nonneg hρ hW
    rw [abs_of_nonneg hBnn, hA k, hB k]
    linarith [htau0 k]

/-- `lille` at `KzEnvAt`: the definitional form used by `alpha_lip_abs2`. -/
lemma KzEnvAt_lille {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {E : Work.BoseB7.Q3Env Mode} {ρ : ℝ} :
    (KzEnvAt E ρ).lille = (KzEnvAt E ρ).mu * (KzEnvAt E ρ).aScat ^ 3 * (KzEnvAt E ρ).KH ^ 2 := by
  show Work.BoseB7.lille (KzEnvAt E ρ).mu (KzEnvAt E ρ).aScat (KzEnvAt E ρ).KH = _
  rw [Work.BoseB7.lille]

/-- **The node's main theorem.** -/
theorem exists_honestGateFS_of_fsRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut}
    (R Cws Kint : ℝ) (hR : 0 < R)
    (hCws0 : 0 ≤ Cws) (hKint0 : 0 ≤ Kint)
    (hav : 0 < a v) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : GateThresholds v h fc fu R)
    (hsumW1sq : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ q ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
              ((honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
                (honE v h fc fu HM μ).aScat),
            (honE v h fc fu HM μ).W1 q ^ 2 / ‖(honF v h fc fu HM μ).kmom q‖ ^ 2
        ≤ Cws * (honE v h fc fu HM μ).aScat)
    (hint : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
        |ρ * (honE v h fc fu HM μ).W1omega0
          - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
              (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
        ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹)
    (hq2 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
        2 * ρ * (honE v h fc fu HM μ).W1omega0
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
          ≤ (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).Q2ex (KzEnvAt (honE v h fc fu HM μ) ρ))
            + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
                ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFS v h fc fu K₀ b₀ := by
  classical
  obtain ⟨Kχ, hKχ1, Cchi, Csum, Ctail, Cwt, hCchi0, hCsum0, hCtail0, hCwt0, hK1χ, hK2χ,
    hchi, hsuminv, htailinv,
    (_hwt : ∀ {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (kmom : Mode → EuclideanSpace ℝ (Fin 3))
      (hlat : Work.BoseK15.OnDualLattice ℓ kmom),
      (∑ q ∈ Work.BoseB7.excited Mode, (1 + ‖kmom q‖) ^ (-(4 : ℝ))) ≤ Cwt * ℓ ^ 3)⟩ :=
    Work.BoseK15.exists_constants
  obtain ⟨M, hM0, hM⟩ := LowCut_deriv_bound fu
  set Cg : ℝ := 16 * Real.pi * R + 16 * Real.pi * M with hCgdef
  have hCg0 : 0 ≤ Cg := by rw [hCgdef]; positivity
  set Cα : ℝ := 10 ^ 12 * (16 * Real.pi + Cg + 2 + 1) ^ 4 * (1 + 1 / (1 / 2 : ℝ)) ^ 4
    * (1 + 1 / (a v)) ^ 4 with hCαdef
  have hCχ0 : 0 ≤ Cα := by rw [hCαdef]; positivity
  set K₀ : ℝ := max (max Kχ 8) (max (max Cg Cws) (max Kint (max Cα (16 * Real.pi)))) with hK₀def
  have hKχK : Kχ ≤ K₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have h8K : (8 : ℝ) ≤ K₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCgK : Cg ≤ K₀ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCwsK : Cws ≤ K₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hKintK : Kint ≤ K₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCαK : Cα ≤ K₀ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have h16K : 16 * Real.pi ≤ K₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hK₀0 : (0 : ℝ) ≤ K₀ := by
    rw [hK₀def]
    exact le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 8) (le_max_right _ _)) (le_max_left _ _)
  have hK1 : Cchi * 8 ^ (2 * Work.BoseK15.decayOrder) ≤ K₀ := le_trans hK1χ hKχK
  have hK23 : Cchi * (Csum + Ctail) ≤ K₀ := le_trans hK2χ hKχK
  have hK3 : Cchi * Csum ≤ K₀ :=
    le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCtail0) hCchi0) hK23
  refine ⟨K₀, 1 / 32, hK₀0, by norm_num, ?_⟩
  obtain ⟨tGe, htGe0, htGe⟩ := exists_hon_tau K₀ hK₀0
  refine honestGateFS_of_rows hK₀0 (by norm_num) hthr.Ng (min hthr.εg tGe)
    (lt_min hthr.pos htGe0) (le_trans (min_le_left _ _) hthr.le_one) ?_ ?_ ?_
  · intro HM hN μ hμ hε
    rw [honE_b HM μ]
    norm_num
  · intro HM hN μ hμ hε ρ hclose
    exact Work.BoseFixB1S.admRho_of_closeCondFS (honE v h fc fu HM μ) hav hμ rfl
      (le_trans hε (le_trans (min_le_left _ _) hthr.le_one)) hclose
  · intro HM hN μ hμ hε
    have hε' : μ * a v ^ 3 ≤ hthr.εg := le_trans hε (min_le_left _ _)
    have hμa1 : μ * a v ^ 3 ≤ 1 := le_trans hε' hthr.le_one
    obtain ⟨hN1, hN2, hN3, hN4⟩ := hthr.cube HM hN μ hμ hε'
    obtain ⟨h1ℓ, hR2, hRℓ, hdil323, hS1, hsmall⟩ := hthr.dil HM hN μ hμ hε'
    have hvFSP : FSParamsView (honE v h fc fu HM μ) :=
      (nonempty_fsParamsView_HonestBoxFam (HM := HM) (μ := μ) hμ hav hμa1).some
    have h4κ : 4 * ((honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
        ≤ uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := hN3
    let S : HonSetup v h fc fu HM μ := ⟨hav, hμ, hvFSP, h4κ⟩
    have ht_eq : S.hv.t = μ * a v ^ 3 := by rw [← S.hv.mu_eq]; rfl
    have hthrT : S.hv.t ≤ tGe := by
      rw [ht_eq]
      exact le_trans hε (min_le_right _ _)
    -- the potential rows
    have hW1abs : ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p|
          ≤ 16 * Real.pi * a v :=
      fun p => Work.BoseB7AK.W1rows.W1hat_abs_le hR (Work.BoseBoxFock.ellH_pos v μ)
        hv_nonneg hvrad hv_supp h hRℓ p
    have hW1even : ∀ p : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (-p)
          = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p :=
      (Work.BoseB7AK.W1rows.W1hat_even_contDiff hR (Work.BoseBoxFock.ellH_pos v μ)
        hv_nonneg hvrad hv_supp h hRℓ).1
    obtain ⟨hW1om0nn, hW1om0le16⟩ := honE_W1omega0 S hR hv_nonneg hvrad hv_supp hRℓ
    have hW1om0le : (honE v h fc fu HM μ).W1omega0
        ≤ 16 * Real.pi * (honE v h fc fu HM μ).aScat := by
      rw [honE_aScat]
      exact hW1om0le16
    have hW1low : ∀ k : Lab (HM μ).N,
        ‖(honF v h fc fu HM μ).kmom k‖
            ≤ 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) →
          0 ≤ (honE v h fc fu HM μ).W1 k := by
      exact honE_W1low S hR hv_nonneg hvrad hv_supp hRℓ (by rw [mul_assoc]; exact hR2) hN2
    -- the τ-domination
    have hsmall' : (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
        / ((honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell) ≤ 1 / 32 := by
      have hh := hsmall
      rw [mul_comm (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat] at hh
      exact hh
    have hτdom := htGe (F := honF v h fc fu HM μ) (T := honT v h fc fu HM μ)
      (honE_tau HM μ) S.hv hthrT (by simpa only [honE] using hsmall')
    have ht0 : (0 : ℝ) < hvFSP.t := by
      rw [← hvFSP.mu_eq]
      show (0 : ℝ) < μ * a v ^ 3
      exact mul_pos hμ (pow_pos hav 3)
    have ht1 : hvFSP.t ≤ 1 := by
      rw [← hvFSP.mu_eq]
      show μ * a v ^ 3 ≤ 1
      exact hμa1
    have heT0' : (0 : ℝ) ≤ (honE v h fc fu HM μ).eT := by
      rw [hvFSP.eT_eq]
      exact Work.BoseBox.fsXp_nonneg ht0.le
    have heT1'' : (honE v h fc fu HM μ).eT ≤ 1 := by
      rw [hvFSP.eT_eq]
      exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num : (0:ℝ) ≤ 23/4)
    have hτ0 : ∀ k : Lab (HM μ).N, 0 ≤ (honE v h fc fu HM μ).tau k := by
      intro k
      rw [honE_tau HM μ k]
      exact tauSm_nonneg _ _ _ _ heT0' heT1'' _
    -- the `P_H^q` rows and K3
    have hW1le16 : ∀ k : Lab (HM μ).N,
        |(honE v h fc fu HM μ).W1 k| ≤ 16 * Real.pi * (honE v h fc fu HM μ).aScat := by
      intro k
      rw [honE_W1_apply S k]
      have h0 : (0 : ℝ) ≤ uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          ((honF v h fc fu HM μ).kmom k) := fu.nonneg _
      have h1 : uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          ((honF v h fc fu HM μ).kmom k) ≤ 1 := fu.le_one _
      have h2 := Work.BoseB7AK.W1rows.W1hat_abs_le hR (Work.BoseBoxFock.ellH_pos v μ)
        hv_nonneg hvrad hv_supp h hRℓ ((honF v h fc fu HM μ).kmom k)
      calc |uvCut fu _ _ * Work.BoseFixR.chat _ _| ≤ |Work.BoseFixR.chat _ _| := by
            rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_of_nonneg h0]; exact h1)
        _ ≤ 16 * Real.pi * a v := h2
        _ = 16 * Real.pi * (honE v h fc fu HM μ).aScat := by rw [honE_aScat]
    have hW1leFull : ∀ k : Lab (HM μ).N,
        |(honE v h fc fu HM μ).W1 k| ≤ K₀ * (honE v h fc fu HM μ).aScat :=
      fun k => le_trans (hW1le16 k) (mul_le_mul_of_nonneg_right h16K (le_of_lt hvFSP.a_pos))
    -- **the mode-level Lipschitz row of the honest `Ŵ₁`**, *derived*: the UV-cut
    -- profile is Lipschitz (`LowCut_deriv_bound`) with the un-slacked gradient
    -- bound of `Ŵ₁` (`fderiv_chat_W1fun_le`), so `honW1_lip` applies.
    have hW1gradRow : ∀ p q : Lab (HM μ).N,
        |(honE v h fc fu HM μ).W1 p - (honE v h fc fu HM μ).W1 q|
          ≤ Cg * (honE v h fc fu HM μ).aScat
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖ := by
      intro p q
      have hlip := honW1_lip (v := v) (h := h) fu (R := R) (M := M) hR hM0 hM
        (Work.BoseBoxFock.ellH_pos v μ) hN1 hv_nonneg hvrad hv_supp hRℓ
        ((honF v h fc fu HM μ).kmom p) ((honF v h fc fu HM μ).kmom q)
      rw [honE_W1_apply S p, honE_W1_apply S q, honE_aScat, hCgdef]
      exact hlip
    -- the honest parameters of the kinetic rows
    have hs0 : 0 < (honE v h fc fu HM μ).s := by
      rw [hvFSP.s_eq]; exact Work.BoseBox.fsXp_pos ht0
    have hd0 : 0 < (honE v h fc fu HM μ).d := by
      rw [hvFSP.d_eq]; exact Work.BoseBox.fsXp_pos ht0
    have hd1 : (honE v h fc fu HM μ).d ≤ 1 := by
      rw [hvFSP.d_eq]; exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
    have hℓ0 : 0 < (honE v h fc fu HM μ).ell := Work.BoseB7.ell_pos _ hvFSP
    have hY0 : 0 < 4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat :=
      mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hvFSP.one_le_KH))
        hvFSP.a_pos
    have hαrow : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ p q : Lab (HM μ).N,
        (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat p →
        (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
        |(KzEnvAt (honE v h fc fu HM μ) ρ).alpha p
            - (KzEnvAt (honE v h fc fu HM μ) ρ).alpha q|
          ≤ K₀ * (honE v h fc fu HM μ).lille
              * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖ := by
      intro ρ hρ p q hp hq
      have hnn : (0 : ℝ) ≤ (honE v h fc fu HM μ).lille
          * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
          * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖ :=
        mul_nonneg (mul_nonneg (lille_nonneg hvFSP) (mul_nonneg
          (le_trans zero_le_one hvFSP.one_le_KH) (le_of_lt hvFSP.a_pos))) (norm_nonneg _)
      have hρE : (KzEnvAt (honE v h fc fu HM μ) ρ).rho = ρ :=
        KzEnvAt_rho_of_nonneg hρ.1 (Work.BoseB7.ell_pos _ hvFSP)
      -- ## K3 at the honest model: `alpha_row_of_honest_rows` (the abstract row)
      have hres := alpha_row_of_honest_rows (F := honF v h fc fu HM μ)
        (E := honE v h fc fu HM μ) hvFSP hK₀0 hCg0
        (hthr.dilKH HM hN μ hμ hε')
        (fun k => hW1le16 k) (fun k => hW1leFull k)
        (fun p' q' => hW1gradRow p' q')
        (hthr.dilTau HM hN μ hμ hε')
        Work.BoseBoxFock.tauProf_spec.2.2.1
        Work.BoseBoxFock.tauProf_spec.2.2.2.2.2
        (fun k => (honE_tau HM μ k).trans (tauSm_eq_tauTilde _ _ _ _ _))
        (fun ρ' h0 h1 h2 q' hq' => hτdom ρ' ⟨h0, h1, h2⟩ q' hq')
        ρ hρ.1 hρ.2.1 hρ.2.2 p q hp hq
      calc |(KzEnvAt (honE v h fc fu HM μ) ρ).alpha p
            - (KzEnvAt (honE v h fc fu HM μ) ρ).alpha q|
          ≤ Cα * (honE v h fc fu HM μ).lille
              * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖ := by
            rw [hCαdef]
            exact hres
        _ = Cα * ((honE v h fc fu HM μ).lille
              * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖) := by ring
        _ ≤ K₀ * ((honE v h fc fu HM μ).lille
              * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖) :=
            mul_le_mul_of_nonneg_right hCαK hnn
        _ = K₀ * (honE v h fc fu HM μ).lille
              * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖ := by ring
    have hsumW1sqK : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ q ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
              ((honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
                (honE v h fc fu HM μ).aScat),
            (honE v h fc fu HM μ).W1 q ^ 2 / ‖(honF v h fc fu HM μ).kmom q‖ ^ 2
        ≤ K₀ * (honE v h fc fu HM μ).aScat := by
      have hh := hsumW1sq HM μ hμ
      have h2 := mul_le_mul_of_nonneg_right hCwsK (le_of_lt hvFSP.a_pos)
      linarith [hh, h2]
    have hintRow : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
        |ρ * (honE v h fc fu HM μ).W1omega0
          - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
              (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
        ≤ K₀ * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹ := by
      intro ρ hρ
      have hnn : (0 : ℝ) ≤ ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹ :=
        mul_nonneg (mul_nonneg hρ.1 (le_of_lt hvFSP.a_pos)) (inv_nonneg.mpr
          (le_trans zero_le_one hvFSP.one_le_KH))
      have hh := hint HM μ hμ ρ hρ
      have h2 := mul_le_mul_of_nonneg_right hKintK hnn
      calc |ρ * (honE v h fc fu HM μ).W1omega0
            - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
              ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
                (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
          ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹ := hh
        _ = Kint * (ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹) := by ring
        _ ≤ K₀ * (ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹) := h2
        _ = K₀ * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹ := by ring
    have hABq : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ q : Lab (HM μ).N,
        (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
        2 * |(KzEnvAt (honE v h fc fu HM μ) ρ).B q| ≤ (KzEnvAt (honE v h fc fu HM μ) ρ).A q :=
      fun ρ hρ q hq =>
        (A_ge_of_taurad (E := honE v h fc fu HM μ) (K₀ := K₀) hW1leFull hρ.1
          (fun q hq => hτdom ρ hρ q hq)).2 q hq
    have hq2row : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
        2 * ρ * (honE v h fc fu HM μ).W1omega0
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
          ≤ (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).Q2ex (KzEnvAt (honE v h fc fu HM μ) ρ))
            + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
                ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))
            + (1 / 2) * (honF v h fc fu HM μ).qw Ψ
                ((honF v h fc fu HM μ).dNumOpR (KzEnvAt (honE v h fc fu HM μ) ρ)
                  (fun k => rHi (honF v h fc fu HM μ) (honE v h fc fu HM μ) k
                    ∧ ¬ (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
                        (honE v h fc fu HM μ).aScat k)) := by
      intro ρ hρ Ψ
      have hρE : (KzEnvAt (honE v h fc fu HM μ) ρ).rho = ρ :=
        KzEnvAt_rho_of_nonneg hρ.1 (Work.BoseB7.ell_pos _ hvFSP)
      refine q2exLowerR_of_q2exLower (E := honE v h fc fu HM μ)
        (F := honF v h fc fu HM μ) (T := honT v h fc fu HM μ)
        (fun k => AB_global_hon (F := honF v h fc fu HM μ)
          (E := KzEnvAt (honE v h fc fu HM μ) ρ) (by rw [hρE]; exact hρ.1)
          (hABq ρ hρ) hW1low hτ0
          (fun k => by rw [hρE]; rfl)
          (fun k => by rw [hρE]; rfl) k) Ψ ?_
      exact hq2 HM μ hμ ρ hρ Ψ
    -- the χ-rows
    have hKL : 1 ≤ (honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL := by
      have h := mul_le_mul hvFSP.one_le_Kl hvFSP.one_le_KL (by norm_num : (0:ℝ) ≤ 1)
        (le_trans zero_le_one hvFSP.one_le_Kl)
      simpa using h
    have hM : (honE v h fc fu HM μ).intM + 3 ≤ 2 * Work.BoseK15.decayOrder := by
      rw [hvFSP.intM_eq]
      norm_num [Work.BoseK15.decayOrder, Work.BoseBox.mValue]
    have hhatChi_small := honE_hatChi_small S hCchi0 hchi hK1
    have hccrX_small := honE_ccrX_small S hCchi0 hchi hK1 hS1
    have hsum := honE_sum_hatChiSq S hCchi0 hchi hsuminv hK3
    have htail := honE_tail_hatChiSq S hCchi0 hCtail0 hchi hsuminv htailinv hKL hM hK23
    have hform := honE_hatChiSq_form_upper S hCchi0 hchi hsuminv hK3
    have hcount := honE_count_PL S h8K hKL
    -- assemble
    have hmax : max (16 * Real.pi) (16 * Real.pi) ≤ K₀ := by
      rw [max_self]
      exact h16K
    exact honestRows_of_rows
      ((exists_KinkFS_honest S (16 * Real.pi) (16 * Real.pi) hW1abs hW1even
        hW1om0nn hW1om0le).mono hmax)
      S.hv hτdom hW1low (fun i j => hon_box HM μ S.hμ S.hav i j)
      hαrow hintRow hq2row hhatChi_small hccrX_small hsum htail hform hcount hsumW1sqK


/-- **`HonestGateFS`, unconditionally.**  Combining the main theorem with the
(now proved) inhabitation of the parameter bundle
(`GateThresholdsExist.exists_gateThresholds`): from FS §4's régime and the three
FS §11/§12 rows at absolute constants, the design's `HonestGateFS v h fc fu K₀ b₀`
holds at one absolute pair `(K₀, b₀)`.  The K3 row and the mode-level Lipschitz
row of `Ŵ₁` are *derived* (`alpha_lip_abs2`, `honW1_lip`), so only the three
genuine FS §11/§12 inputs are hypotheses. -/
theorem exists_honestGateFS {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut}
    (R Cws Kint : ℝ) (hR : 0 < R)
    (hCws0 : 0 ≤ Cws) (hKint0 : 0 ≤ Kint)
    (hav : 0 < a v) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hsumW1sq : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ q ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
              ((honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
                (honE v h fc fu HM μ).aScat),
            (honE v h fc fu HM μ).W1 q ^ 2 / ‖(honF v h fc fu HM μ).kmom q‖ ^ 2
        ≤ Cws * (honE v h fc fu HM μ).aScat)
    (hint : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
        |ρ * (honE v h fc fu HM μ).W1omega0
          - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
              (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
        ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹)
    (hq2 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
        2 * ρ * (honE v h fc fu HM μ).W1omega0
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
          ≤ (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).Q2ex (KzEnvAt (honE v h fc fu HM μ) ρ))
            + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
                ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFS v h fc fu K₀ b₀ :=
  exists_honestGateFS_of_fsRows R Cws Kint hR hCws0 hKint0 hav hv_nonneg
    hvrad hv_supp (exists_gateThresholds fc fu hav R).some hsumW1sq hint hq2

end Work.BoseGateFS

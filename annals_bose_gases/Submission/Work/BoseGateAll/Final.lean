import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseGateAll.Honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.Final` — `exists_honestGateFSAll_of_fsRows` and the row-level assembly

The port of `Submission/Work/BoseGateFS/HonestGateFinal.lean`'s
`exists_honestGateFS_of_fsRows` to the corrected `Q₂^{ex,all}` row.  Everything is
transcribed verbatim except the `Q₂^ex` row:

* the corpus consumes `hq2 : 2ρŴ₁ω(0)⟨Gop⟩ ≤ ⟨Q2ex (KzEnvAt E ρ)⟩ + (b/400)⟨gapOpT⟩`
  (with the reserve added by `Reserve.q2exLowerR_of_q2exLower` in the last step);
* here `hq2All` is the corpus row with `Q2exAll` in place of `Q2ex` — exactly the
  content of `Work.BoseRowQ2.RowQ2AllRegimeN` — and **no reserve is needed**: the
  frozen `Q3KernelFSAll.q2exLowerR` carries the reserve, and it is added inside
  `GateInputAll.toQ3KernelFSAll` by `Reserve.qw_dNumOpR_nonneg`.

The main result is `exists_honestGateFSAll_of_fsRows`; the row-level forms
(`exists_honestGateFSAll_of_rows`, `…_of_regime_rows`) share its single body.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases
open Work.BoseGateFS

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The row-level assembly.**  From

* the honest §11 row `hrow1` (FS `eq:I2-integral`, `sum_W1sq`),
* FS §11's K5 row `hrow2` (`intOne`),
* the corrected row 3 `hrow3All` (FS `eq:Q3Cancels` with `Q₂^{ex,all}`, no reserve
  and no label restriction),

one absolute constant `Cws` paid by the LHS of row 1, one absolute constant `Kint`
paid by the LHS of K5, and the small-parameter bundle `hthr`, we get the honest
gate `HonestGateFSAll v h fc fu K₀ b₀` at one absolute pair `(K₀, b₀)`.

This is the single body of the port: `exists_honestGateFSAll_of_fsRows` and
`exists_honestGateFSAll_of_regime_rows` are its two wrappers. -/
theorem exists_honestGateFSAll_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut}
    (R Cws Kint : ℝ) (hR : 0 < R)
    (hCws0 : 0 ≤ Cws) (hKint0 : 0 ≤ Kint)
    (hav : 0 < a v) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : GateThresholds v h fc fu R)
    (hrow1 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, hthr.Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ hthr.εg →
        (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ q ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
                ((honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
                  (honE v h fc fu HM μ).aScat),
              (honE v h fc fu HM μ).W1 q ^ 2 / ‖(honF v h fc fu HM μ).kmom q‖ ^ 2
          ≤ Cws * (honE v h fc fu HM μ).aScat)
    (hrow2 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, hthr.Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ hthr.εg → ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
        |ρ * (honE v h fc fu HM μ).W1omega0
          - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
              (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
        ≤ Kint * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹)
    (hrow3All : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, hthr.Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ hthr.εg → ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
        ∀ Ψ : (honF v h fc fu HM μ).H,
          2 * ρ * (honE v h fc fu HM μ).W1omega0
              * (honF v h fc fu HM μ).qw Ψ
                  ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
            ≤ (honF v h fc fu HM μ).qw Ψ
                ((honF v h fc fu HM μ).Q2exAll
                  (KzEnvAt (honE v h fc fu HM μ) ρ))
              + ((honE v h fc fu HM μ).b / 400)
                  * (honF v h fc fu HM μ).qw Ψ
                      ((honT v h fc fu HM μ).gapOpT
                        (KzEnvAt (honE v h fc fu HM μ) ρ))) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ := by
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
  have hCαnn : 0 ≤ Cα := by rw [hCαdef]; positivity
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
  refine honestGateFSAll_of_rows hK₀0 (by norm_num) hthr.Ng (min hthr.εg tGe)
    (lt_min hthr.pos htGe0) (le_trans (min_le_left _ _) hthr.le_one) ?_ ?_ ?_
  · intro HM hN μ hμ hε
    rw [Work.BoseGateFS.honE_b HM μ]
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
      rw [Work.BoseGateFS.honE_aScat]
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
      (Work.BoseGateFS.honE_tau HM μ) S.hv hthrT (by simpa only [honE] using hsmall')
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
      rw [Work.BoseGateFS.honE_tau HM μ k]
      exact Work.BoseGateFS.tauSm_nonneg _ _ _ _ heT0' heT1'' _
    -- the `P_H^q` rows and K3
    have hW1le16 : ∀ k : Lab (HM μ).N,
        |(honE v h fc fu HM μ).W1 k| ≤ 16 * Real.pi * (honE v h fc fu HM μ).aScat := by
      intro k
      rw [Work.BoseGateFS.honE_W1_apply S k]
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
        _ = 16 * Real.pi * (honE v h fc fu HM μ).aScat := by rw [Work.BoseGateFS.honE_aScat]
    have hW1leFull : ∀ k : Lab (HM μ).N,
        |(honE v h fc fu HM μ).W1 k| ≤ K₀ * (honE v h fc fu HM μ).aScat :=
      fun k => le_trans (hW1le16 k) (mul_le_mul_of_nonneg_right h16K (le_of_lt hvFSP.a_pos))
    -- **the mode-level Lipschitz row of the honest `Ŵ₁`**
    have hW1gradRow : ∀ p q : Lab (HM μ).N,
        |(honE v h fc fu HM μ).W1 p - (honE v h fc fu HM μ).W1 q|
          ≤ Cg * (honE v h fc fu HM μ).aScat
              * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖ := by
      intro p q
      have hlip := honW1_lip (v := v) (h := h) fu (R := R) (M := M) hR hM0 hM
        (Work.BoseBoxFock.ellH_pos v μ) hN1 hv_nonneg hvrad hv_supp hRℓ
        ((honF v h fc fu HM μ).kmom p) ((honF v h fc fu HM μ).kmom q)
      rw [Work.BoseGateFS.honE_W1_apply S p, Work.BoseGateFS.honE_W1_apply S q,
        Work.BoseGateFS.honE_aScat, hCgdef]
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
        (fun k => (Work.BoseGateFS.honE_tau HM μ k).trans (Work.BoseGateFS.tauSm_eq_tauTilde _ _ _ _ _))
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
      have hh := hrow1 HM hN μ hμ hε'
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
      have hh := hrow2 HM hN μ hμ hε' ρ hρ
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
    -- **the corrected row 3** (reserve-free, window-restricted): `hrow3All` is
    -- already in the right form, so the window hypothesis is discarded.
    have hq2rowAll : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
        (honT v h fc fu HM μ).NWindow (honE v h fc fu HM μ).bigM Ψ →
        2 * ρ * (honE v h fc fu HM μ).W1omega0
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
          ≤ (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).Q2exAll (KzEnvAt (honE v h fc fu HM μ) ρ))
            + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
                ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ)) :=
      fun ρ hρ Ψ _ => hrow3All HM hN μ hμ hε' ρ hρ Ψ
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
    exact honestRowsAll_of_rows
      ((exists_KinkFS_honest S (16 * Real.pi) (16 * Real.pi) hW1abs hW1even
        hW1om0nn hW1om0le).mono hmax)
      S.hv hτdom hW1low (fun i j => hon_box HM μ S.hμ S.hav i j)
      hαrow hintRow hq2rowAll hhatChi_small hccrX_small hsum htail hform hcount hsumW1sqK

/-! ## 2. The two wrappers -/

/-- **`exists_honestGateFSAll_of_fsRows`**: the FS §11/§12 rows at absolute
constants, at any cube size and diluteness (no régime restriction), give the
honest `All` gate.  This is the port of
`Work.BoseGateFS.exists_honestGateFS_of_fsRows`, with `hq2` at `Q₂^{ex,all}`. -/
theorem exists_honestGateFSAll_of_fsRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
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
    (hq2All : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
        2 * ρ * (honE v h fc fu HM μ).W1omega0
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
          ≤ (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).Q2exAll (KzEnvAt (honE v h fc fu HM μ) ρ))
            + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
                ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ :=
  exists_honestGateFSAll_of_rows R Cws Kint hR hCws0 hKint0 hav hv_nonneg hvrad hv_supp
    hthr
    (fun HM _ μ hμ hε => hsumW1sq HM μ hμ)
    (fun HM _ μ hμ hε ρ hρ => hint HM μ hμ ρ hρ)
    (fun HM _ μ hμ hε ρ hρ Ψ => hq2All HM μ hμ ρ hρ Ψ)

/-- **`exists_honestGateFSAll_of_regime_rows`**: rows 1, 2, 3 in the dilute régime
at a free cube size `Ng` and threshold `εg` (the forms in which the FS §4 régime
and the interface supply them) give the honest `All` gate; the port of
`Work.BoseRowsFS.exists_honestGateFS_of_regime_rows`. -/
theorem exists_honestGateFSAll_of_regime_rows
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (Cws : ℝ) (hCws : 0 ≤ Cws)
    (hrow1 : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, hthr.Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
        (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ q ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
                ((Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                  (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                  (Work.BoseRowsFS.honE v h fc fu HM μ).aScat),
              (Work.BoseRowsFS.honE v h fc fu HM μ).W1 q ^ 2
                / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom q‖ ^ 2
          ≤ Cws * (Work.BoseRowsFS.honE v h fc fu HM μ).aScat)
    (Kint : ℝ) (hKint : 0 ≤ Kint)
    (hrow2 : Work.BoseRowsFS.RowIntOneRegimeN (h := h) (fc := fc) (fu := fu) hthr.Ng R hthr.εg Kint)
    (hrow3All : Work.BoseRowQ2.RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu)
      hthr.Ng R hthr.εg) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ :=
  exists_honestGateFSAll_of_rows R Cws Kint hR hCws hKint hav hv_nonneg hvrad hv_supp
    hthr hrow1 hrow2 hrow3All

/-- **The `All` gate, unconditionally.**  Combining `exists_honestGateFSAll_of_fsRows`
with the (proved) inhabitation of the small-parameter bundle
(`GateThresholdsExist.exists_gateThresholds`): from FS §4's régime and the three
FS §11/§12 rows at absolute constants, `HonestGateFSAll v h fc fu K₀ b₀` holds at
one absolute pair `(K₀, b₀)`.  The K3 row and the mode-level Lipschitz row of `Ŵ₁`
are *derived* (as in the corpus's `exists_honestGateFS`), so the three genuine
inputs are `hsumW1sq` (FS `eq:I2-integral`), `hint` (K5) and `hq2All` (FS
`eq:Q3Cancels` with `Q₂^{ex,all}`, i.e. `RowQ2All`). -/
theorem exists_honestGateFSAll {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
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
    (hq2All : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
        2 * ρ * (honE v h fc fu HM μ).W1omega0
            * (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
          ≤ (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).Q2exAll (KzEnvAt (honE v h fc fu HM μ) ρ))
            + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
                ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))) :
    ∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ HonestGateFSAll v h fc fu K₀ b₀ :=
  exists_honestGateFSAll_of_fsRows R Cws Kint hR hCws0 hKint0 hav hv_nonneg
    hvrad hv_supp (exists_gateThresholds fc fu hav R).some hsumW1sq hint hq2All

end Work.BoseGateAll

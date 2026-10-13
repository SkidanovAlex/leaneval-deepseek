import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0_mem6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SepParts
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.gamQfun_jet_continuousOn
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.sep_mem6_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas -/

/-- `z ↦ L₁₂(f)(z)` is `C⁶` on `(0,∞)` whenever `f` is smooth on the open quadrant and honest
at order seven.  This is the finite-order replacement of the `ctx`-hypothesis
`SmoothOpen (fun z _ => L₁₂ f z)` of the sibling. -/
private theorem contDiffOn_six_L12 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
  have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα hα1 hfsm hm7 (by norm_num)
  refine (h.of_le (by norm_num)).congr (fun z _ => ?_)
  exact (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm

/-- The joint `C⁶`-smoothness on the open quadrant of a separable product `a(θ)·ρ(z)`, from
`C⁶`-smoothness of the two one-variable factors. -/
private theorem contDiffOn_uncurry_sep {a : ℝ → ℝ} {ρ : ℝ → ℝ}
    (ha : ContDiffOn ℝ 6 a (Set.Ioo 0 (Real.pi / 2)))
    (hρ : ContDiffOn ℝ 6 ρ (Set.Ioi 0)) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a θ * ρ z)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0 :=
    ha.comp contDiffOn_snd (fun p hp => hp.2)
  have h2 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => ρ p.1) Work.FTS.EllipticEst.Q0 :=
    hρ.comp contDiffOn_fst (fun p hp => hp.1)
  have hfun : Function.uncurry (fun z θ => a θ * ρ z)
      = (fun p : ℝ × ℝ => a p.2) * (fun p : ℝ × ℝ => ρ p.1) := rfl
  rw [hfun]
  exact h1.mul h2

/-- **Continuity of the `ℋ⁶`-integrand of a separable product**, from `C⁶`-smoothness of the
two factors: the continuity hypothesis of `sep_mem6_open`. -/
private theorem continuousOn_HkIntegrand_sep6_priv {α : ℝ} {a : ℝ → ℝ} {ρ : ℝ → ℝ}
    (ha : ContDiffOn ℝ 6 a (Set.Ioo 0 (Real.pi / 2)))
    (hρ : ContDiffOn ℝ 6 ρ (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * ρ z) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hQd : Work.FTS.CoercivityFix.Transfer.E2pkg.Qd = Work.FTS.EllipticEst.Q0 := rfl
  have hun : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a θ * ρ z))
      Work.FTS.CoercivityFix.Transfer.E2pkg.Qd := by
    rw [hQd]
    exact contDiffOn_uncurry_sep ha hρ
  have hbc := Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn
    (G := fun z θ => a θ * ρ z) hun
  have hcont := Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont
    hbc α
  rw [hQd] at hcont
  exact hcont

-- The `ℋ⁶`-memberships of the six `f`-dependent pieces of the `N₀`-row, at the bare-`f`
-- interface (`H6Adm α f` + `HkMem α 7 f`), i.e. WITHOUT the hypothesis
-- `SmoothOpen (fun z _ => L₁₂ f z)` that the sibling `H6Pair6Aux.H6N0Aux.hkmem_N0pieces_own`
-- carries.  They are needed to split the slot pairing of `N₀` into its pieces.
--
-- ROUTE.  `H6Adm α f` gives `SmoothOpen f`, `HkMem α 6 f`, `L₁₂ f 0 = 0`.  The sibling
-- `H6Rows/N0pair6Aux/N0_mem6.lean` contains a full lane proof of the membership of the *sum*
-- of the pieces under exactly these hypotheses, and the same lanes give the pieces:
--   * `NP3 = (1/α)·(L₁₂ f · f)`, `NP4b = (3/(2α))·(L₁₂ f · D_θ f)`,
--     `NP5b = (-1)·(c₂ₘ · L₁₂ f · D_z f)`: the radial-multiplier route
--     `H6Rows.N0pair6Aux.HkMem_radial_mul6` with `X := L₁₂ f`, which needs only
--     `ContDiffOn ℝ 6 (L₁₂ f) (Ioi 0)` (`UopHk.contDiffOn_L12_k α 7 f` plus
--     `H2.constructionL12_eq_ellipticL12`) and the jet bound `|DzdIter j (L₁₂ f)| ≤ C₆·HkNorm α 6 f`,
--     `j ≤ 6` (`H6Pair6Aux.L12Sup6`); scalar factors via `LocData.HkMem_const_mul`, and for
--     `NP5b` group the θ-only factor `c₂ₘ` with the radial coefficient (see `N0coefA6_WlInf6`).
--   * `NP4a = (3/(2α))·(L₁₂ f · D_θ F_*)`, `NP5a = (-1)·(L₁₂ f · (c₂ₘ·D_z F_*))`: same route
--     with `ψ := D_θ F_*` resp. `ψ := c₂ₘ·D_z F_*`.  CAVEAT: `DthFstar_W6`/`c2mDzFstar_W6`
--     give only `WlInfMem α 6`, so get `HkMem α 6 ψ` from
--     `H6Pair6Aux.N0SlotSplitAux.HkMem_mul_of_WlInf6` using the `F_*`-factor as the `𝒲^{6,∞}`
--     factor and the other factor (`F_*` resp. `c₂ₘ·F_*`) as `HQo`, OR via a decay majorant.
--   * `NP6 = (-1)·(c₂ₘ·L₁₂(F_*)·D_z f)`: `HkMem_mul_of_WlInf6` with coefficient
--     `c₂ₘ·L₁₂(F_*)` (`c2m_L12Fstar_W6`: `WlInfMem α 6` and `WlInf α 6 ≤ Cα`) against
--     `D_z f` (`HkMem α 6 (D_z f)` from `HkMem α 7 f`, `IPGen.HkMem_Dz_le`).
--
-- IMPLEMENTATION NOTE (added by the prover).  `NP3`, `NP4b` and `NP5b` are the radial-multiplier
-- pieces (`HkMem_radial_mul6` with `X = L₁₂ f`, whose only smoothness input is
-- `ContDiffOn ℝ 6 (L₁₂ f) (Ioi 0)` from `UopHk.contDiffOn_L12_k`), `NP6` is the `𝒲^{6,∞}`-product
-- with `N0coefA6_WlInf6`.  `NP4a` and `NP5a` are *not* obtainable with the radial multiplier
-- alone (neither `D_θF_*` nor `c₂ₘ·D_zF_*` lies in `ℋ⁶`: both are `~ z` near `z = 0` while the
-- weight `w ~ z^{-2}`); they are handled by the *separated-product* route of
-- `N0SepParts.N04a_mem`/`N05a_mem`, with the two `SmoothOpen (L₁₂ f)`-inputs replaced by the
-- finite-order data: `∂_θF_* = α(Γ'/c)φ`, `D_zF_* = α(Γ/c)D_zφ` with `φ = FM.Fstar`, so
-- `(3/(2α))·L₁₂(f)·D_θF_*` and `-L₁₂(f)·(c₂ₘ·D_zF_*)` are the separable products `a(θ)·ρ(z)`
-- with `ρ = L₁₂(f)·φ` resp. `ρ = L₁₂(f)·D_zφ` and `a = (3α/(2c))·q·Γ` resp. `a = -(α/c)·c₂ₘ·Γ`;
-- the membership of a separable product with only `C⁶`-inputs is the engine `sep_mem6_open`
-- (with its continuity hypothesis supplied by `continuousOn_HkIntegrand_sep6_priv`).
theorem N0piecesMem6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.StrongPersist.H6Adm α f) (hm7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4a α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5a α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α f) := by
  obtain ⟨hfsm, hm6⟩ := hf.reg
  have h0 : Work.Construction.L12 f 0 = 0 := hf.l12
  have hcg : 0 < Work.Spaces.c α := by linarith [(Work.Spaces.c_bounds α hα hα1).1]
  -- ## the radial factor `L₁₂ f`
  obtain ⟨C₆, hC₆pos, hC₆⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  have hΛcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
    contDiffOn_six_L12 hα hα1 hfsm hm7
  have hΛjet : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    fun j hj z hz => hC₆ α f hα hα1 hfsm hm6 hm7 h0 j hj z hz
  have hΛB : 0 ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hC₆pos.le (Work.Spaces.HkNorm_nonneg α 6 f)
  have hΛslot : ∀ b : ℕ, b ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z
        * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7
    intro b hb
    refine ((hC₁ α f hα hα1 hfsm hm6 hm7 h0 b (by omega)).1).congr
      (Eventually.of_forall fun z => ?_)
    ring
  -- the radial multiplier
  have hradial : ∀ (ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen ψ →
      Work.Spaces.HkMem α 6 ψ →
      Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 f z * ψ z θ) :=
    fun ψ hψsm hψmem =>
      HkMem_radial_mul6 α (C₆ * Work.Spaces.HkNorm α 6 f)
        (fun z => Work.Construction.L12 f z) ψ hα hΛB hΛcd hΛjet hψsm hψmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ## `NP3 = (1/α)·(L₁₂ f·f)`
    have h1 : Work.Spaces.HkMem α 6
        (fun z θ => (1 / α) * (Work.Construction.L12 f z * f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (1 / α) (hradial f hfsm hm6)
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (1 / α) * (Work.Construction.L12 f z * f z θ)) (fun z θ _ => ?_) h1
    rfl
  · -- ## `NP4a = (3/(2α))·(L₁₂ f·D_θ F_*)`
    obtain ⟨M₂, hM₂pos, hM₂⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
    obtain ⟨hFj6, -⟩ := Work.FTS.StrongPersist.H6Pair6Aux.Fstar_jets_shift M₂ hM₂
    have hslot1 : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter j
          (fun z => Work.Construction.L12 f z * Work.FM.Fstar z) z * Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz :=
      Work.FTS.StrongPersist.H6Pair6Aux.slots_radial_mul
        (X := fun z => Work.Construction.L12 f z) (r := fun z => Work.FM.Fstar z) (M := M₂)
        hΛcd (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_contDiffOn 6) hΛslot
        (fun m hm z hz => hFj6 m (by omega) z (le_of_lt hz))
    have ha4cd : ContDiffOn ℝ 6
        (fun θ : ℝ => (3 * α / (2 * Work.Spaces.c α))
          * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.contDiffOn_gamQfun α
          (3 * α / (2 * Work.Spaces.c α))).of_le (by simp [Work.Stability.smoothOrder])).congr (fun θ _ => by ring)
    have hr4cd : ContDiffOn ℝ 6
        (fun z : ℝ => Work.Construction.L12 f z * Work.FM.Fstar z) (Set.Ioi 0) :=
      hΛcd.mul (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_contDiffOn 6)
    have ha40 : ∀ θ ∈ Work.Spaces.Iθ,
        |(3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ)|
          ≤ |3 * α / (2 * Work.Spaces.c α)| * (4 / 3) := by
      intro θ hθ
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun, abs_le]
        constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hqG : |Work.Spaces.qfun θ * Work.Spaces.Gam α θ| ≤ 4 / 3 := by
        rw [abs_mul, abs_of_nonneg hG0]
        calc |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ (4 / 3) * 1 :=
              mul_le_mul hq hG1 hG0 (by norm_num)
          _ = 4 / 3 := by ring
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hqG (abs_nonneg _)
    have ha41 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        ((Work.Spaces.dthU^[i]) (fun θ' => (3 * α / (2 * Work.Spaces.c α))
            * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ')) θ) ^ 2
          ≤ ((3 * α / (2 * Work.Spaces.c α)) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2)
            * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
      have hinterior : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ((Work.Spaces.dthU^[i]) (fun θ' => (3 * α / (2 * Work.Spaces.c α))
              * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ')) θ) ^ 2
            ≤ ((3 * α / (2 * Work.Spaces.c α)) ^ 2
                * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2)
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
        intro i hi1 hi6 θ hθo
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθo.1])
            (by linarith [hθo.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
        have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
        have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
        have hjet : |(Work.Spaces.dthU^[i])
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ|
            ≤ Work.FTS.StrongPersist.H6Pair6Aux.gamqK * (Real.sin (2 * θ)) ^ (α / 5) := by
          have h := Work.FTS.StrongPersist.H6Pair6Aux.GamQfun_dthU_Iθ α hα hα1 i hi6 θ hθI
          rw [show (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)
              = fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t from by
            funext t; ring] at h
          exact h.trans (mul_le_mul_of_nonneg_left hGle
            Work.FTS.StrongPersist.H6Pair6Aux.gamqK_nonneg)
        have hsq : ((Work.Spaces.dthU^[i])
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2
            ≤ (Work.FTS.StrongPersist.H6Pair6Aux.gamqK
                * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hjet 2
          rwa [sq_abs] at h2
        have hconst : (Work.Spaces.dthU^[i])
            (fun θ' => (3 * α / (2 * Work.Spaces.c α))
              * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ'))
            = fun θ' => (3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
                (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ' :=
          Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_const_mul
            (3 * α / (2 * Work.Spaces.c α))
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) i
        rw [hconst]
        calc ((3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
              (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2
            = (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * ((Work.Spaces.dthU^[i])
                (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2 := by ring
          _ ≤ (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * (Work.FTS.StrongPersist.H6Pair6Aux.gamqK
                  * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
              rw [mul_pow, Work.FTS.StrongPersist.H6Pair6Aux.sq_sin_rpow hsin]
              ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_sq_le_sin_aux (κ := α / 5)
        (B1 := (3 * α / (2 * Work.Spaces.c α)) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2) (by positivity) hinterior
    have hmem := sep_mem6_open (α := α) (κ := α / 5)
      (B0 := |3 * α / (2 * Work.Spaces.c α)| * (4 / 3))
      (B1 := (3 * α / (2 * Work.Spaces.c α)) ^ 2
        * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2)
      (a := fun θ => (3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
      (ρ := fun z => Work.Construction.L12 f z * Work.FM.Fstar z)
      (by positivity) (by positivity) (by simp only [Work.Spaces.gam]; linarith)
      ha40 ha41 (continuousOn_HkIntegrand_sep6_priv ha4cd hr4cd) hslot1
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => ((3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z * Work.FM.Fstar z)) (fun z θ hzθ => ?_) hmem
    have hz : 0 < z := hzθ.1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hzθ.2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    show ((3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z * Work.FM.Fstar z)
      = Work.FTS.StrongPersist.H6Pair6Aux.NP4a α f z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP4a, Work.FTS.StrongPersist.H6Pair6Aux.NA4,
      Work.Spaces.Dth]
    rw [Work.FTS.StrongPersist.H6Pair6Aux.pth_Fstar_eq α z θ hθ]
    have hα0 : α ≠ 0 := ne_of_gt hα
    have hc0 : Work.Spaces.c α ≠ 0 := ne_of_gt hcg
    have h2α : (2 : ℝ) * α ≠ 0 := by positivity
    have h2c : (2 : ℝ) * Work.Spaces.c α ≠ 0 := by positivity
    have hkey : Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
        = α * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.s2_deriv_Gam_Iθ α hα hθI]
      ring
    have hA : (3 / (2 * α)) * (Work.Construction.L12 f z
          * (Real.sin (2 * θ) * (α * (deriv (Work.Spaces.Gam α) θ / Work.Spaces.c α)
            * Work.FM.Fstar z)))
        = (3 / (2 * α)) * α * (Work.Spaces.c α)⁻¹
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
          * (Work.Construction.L12 f z * Work.FM.Fstar z) := by ring
    rw [hA, hkey]
    first
      | (field_simp; ring)
      | field_simp
  · -- ## `NP4b = (3/(2α))·(L₁₂ f·D_θ f)`
    have hψmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
      Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 6) (f := f) (by linarith) hfsm hm7
    have h1 : Work.Spaces.HkMem α 6
        (fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α))
        (hradial (Work.Spaces.Dth f) hfsm.Dth hψmem)
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ))
      (fun z θ _ => ?_) h1
    rfl
  · -- ## `NP5a = (-1)·(L₁₂ f·(c₂ₘ·D_z F_*))`
    obtain ⟨M₂, hM₂pos, hM₂⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
    obtain ⟨-, hFj6'⟩ := Work.FTS.StrongPersist.H6Pair6Aux.Fstar_jets_shift M₂ hM₂
    obtain ⟨D, hDpos, hD⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
    have hslot2 : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z =>
          Work.Construction.L12 f z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z) z
            * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      Work.FTS.StrongPersist.H6Pair6Aux.slots_radial_mul
        (X := fun z => Work.Construction.L12 f z)
        (r := fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z) (M := M₂)
        hΛcd (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_shift_contDiffOn 6) hΛslot
        (fun m hm z hz => hFj6' m (by omega) z hz)
    have ha5cd : ContDiffOn ℝ 6
        (fun θ : ℝ => -(α / Work.Spaces.c α)
          * (Work.Construction.c2m θ * Work.Spaces.Gam α θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 6 (fun θ : ℝ => Work.Construction.c2m θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m.contDiffOn).of_le (by simp [Work.Stability.smoothOrder])
      have h2 : ContDiffOn ℝ 6 (fun θ : ℝ => Work.Spaces.Gam α θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_Gam_Ioo α).of_le (by simp [Work.Stability.smoothOrder])
      have hc : ContDiffOn ℝ 6 (fun _ : ℝ => -(α / Work.Spaces.c α))
          (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const
      have h12 : ContDiffOn ℝ 6
          (fun θ : ℝ => Work.Construction.c2m θ * Work.Spaces.Gam α θ)
          (Set.Ioo 0 (Real.pi / 2)) := h1.mul h2
      exact hc.mul h12
    have hr5cd : ContDiffOn ℝ 6
        (fun z : ℝ => Work.Construction.L12 f z
          * Work.Elliptic.DzdIter 1 Work.FM.Fstar z) (Set.Ioi 0) :=
      hΛcd.mul (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_shift_contDiffOn 6)
    have ha50 : ∀ θ ∈ Work.Spaces.Iθ,
        |-(α / Work.Spaces.c α) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ)|
          ≤ |α / Work.Spaces.c α| * 2 := by
      intro θ hθ
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hc2G : |Work.Construction.c2m θ * Work.Spaces.Gam α θ| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg hG0]
        calc |Work.Construction.c2m θ| * Work.Spaces.Gam α θ ≤ 2 * 1 :=
              mul_le_mul (Work.FTS.StrongPersist.H6Pair6Aux.abs_c2m_le_two θ) hG1 hG0
                (by norm_num)
          _ = 2 := by ring
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left hc2G (abs_nonneg _)
    have ha51 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        ((Work.Spaces.dthU^[i]) (fun θ' => -(α / Work.Spaces.c α)
            * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ')) θ) ^ 2
          ≤ ((α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
            * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
      have hinterior : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ((Work.Spaces.dthU^[i]) (fun θ' => -(α / Work.Spaces.c α)
              * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ')) θ) ^ 2
            ≤ ((α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
        intro i hi1 hi6 θ hθo
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθo.1])
            (by linarith [hθo.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
        have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
        have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
        have hbd : |(Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
            ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) :=
          hD α hα hα1 i hi1 hi6 θ hθo
        have hsin2 : Real.sin (2 * θ) ^ 2 + α ≤ 2 := by
          have h1 := Real.sin_sq_le_one (2 * θ)
          linarith
        have h3 : 0 ≤ Real.sin (2 * θ) ^ 2 + α := by
          nlinarith [sq_nonneg (Real.sin (2 * θ)), hα.le]
        have h4 : 0 ≤ D * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_nonneg hDpos.le (Real.rpow_nonneg (le_of_lt hsin) _)
        have hstep : |(Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
            ≤ 2 * D * (Real.sin (2 * θ)) ^ (α / 5) := by
          calc |(Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
              ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := hbd
            _ ≤ D * (Real.sin (2 * θ)) ^ (α / 5) * 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hGle hDpos.le) hsin2 h3 h4
            _ = 2 * D * (Real.sin (2 * θ)) ^ (α / 5) := by ring
        have hsq : ((Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2
            ≤ (2 * D * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hstep 2
          rwa [sq_abs] at h2
        have hconst : (Work.Spaces.dthU^[i])
            (fun θ' => -(α / Work.Spaces.c α)
              * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ'))
            = fun θ' => -(α / Work.Spaces.c α) * (Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ' :=
          Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_const_mul (-(α / Work.Spaces.c α))
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) i
        rw [hconst]
        calc ((-(α / Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
              (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2
            = (α / Work.Spaces.c α) ^ 2
              * ((Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2 := by ring
          _ ≤ (α / Work.Spaces.c α) ^ 2
              * (2 * D * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
              rw [mul_pow, Work.FTS.StrongPersist.H6Pair6Aux.sq_sin_rpow hsin]
              ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_sq_le_sin_aux (κ := α / 5)
        (B1 := (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2) (by positivity) hinterior
    have hmem := sep_mem6_open (α := α) (κ := α / 5)
      (B0 := |α / Work.Spaces.c α| * 2)
      (B1 := (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
      (a := fun θ => -(α / Work.Spaces.c α)
        * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
      (ρ := fun z => Work.Construction.L12 f z
        * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
      (by positivity) (by positivity) (by simp only [Work.Spaces.gam]; linarith)
      ha50 ha51 (continuousOn_HkIntegrand_sep6_priv ha5cd hr5cd) hslot2
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (-(α / Work.Spaces.c α)
        * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z
          * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)) (fun z θ hzθ => ?_) hmem
    have hz : 0 < z := hzθ.1
    show (-(α / Work.Spaces.c α) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
      = Work.FTS.StrongPersist.H6Pair6Aux.NP5a α f z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5a, Work.FTS.StrongPersist.H6Pair6Aux.NA5]
    rw [Work.FTS.StrongPersist.H6Pair6Aux.Dz_Fstar_eq α z θ hz]
    ring
  · -- ## `NP5b = (-1)·(c₂ₘ·L₁₂ f·D_z f)`
    have hψsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
      Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_neg
          (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
            Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)) hfsm.Dz
    have hψmem : Work.Spaces.HkMem α 6
        (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
      Work.FTS.StrongPersist.H6Pair6Aux.c2m_Dz_mem hα hα1 hfsm hm7
    have h1 : Work.Spaces.HkMem α 6
        (fun z θ => Work.Construction.L12 f z
          * (-(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ)) :=
      hradial (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) hψsm hψmem
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => Work.Construction.L12 f z
        * (-(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ)) (fun z θ _ => ?_) h1
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5b]
    ring
  · -- ## `NP6 = (-1)·(c₂ₘ·L₁₂(F_*)·D_z f)`
    obtain ⟨CA, hCApos, hN0coef⟩ :=
      Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
    obtain ⟨hN0coefsm, hN0coefw, -⟩ := hN0coef α hα hα1
    have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
      Work.FTS.IPGen.HkMem_Dz_le hfsm hm7
    have hmul : Work.Spaces.HkMem α 6
        (fun z θ => (-(2 * α / (1 + z)) * Work.Construction.c2m θ)
          * Work.Spaces.Dz f z θ) :=
      Work.FTS.StrongPersist.H6Pair6Aux.HkMem_mul_of_WlInf6 hα hα1 hN0coefsm hN0coefw
        hfsm.Dz hDzmem
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (-(2 * α / (1 + z)) * Work.Construction.c2m θ)
        * Work.Spaces.Dz f z θ) (fun z θ hzθ => ?_) hmul
    have hz : 0 ≤ z := le_of_lt hzθ.1
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP6, Work.FTS.StrongPersist.H6Pair6Aux.NA6]
    rw [Work.Construction.L12_Fstar_eq hα hα1 hz]
    ring

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux

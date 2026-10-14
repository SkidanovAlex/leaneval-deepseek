import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Base
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.EpsWPBounds
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Row6.fkFacts7
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.THL.cs7_rop_split
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.HQo_dynRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-!
# `HQo α 4 (dynRHS … τ)` — the transfer-derivative right-hand side

`HQo α 4 f = SmoothOpen f ∧ HkMem α 4 f`, and the nonlinear part of the scheme's right-hand side
is `dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ`.

* `SmoothOpen`: `smoothOpen_dynRHS_of_classC` at the class-`C` slice `slice (JfamP ρ ε g) τ`
  (available since `τ ∈ Icc 0 τ` and `hτ : 0 < τ`).
* `HkMem α 4`: `epsWP α ρ ε Φs E g τ` unfolds definitionally to
  `dynLin α (JfamP ρ ε g) τ + dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ`
  (`PZeroScheme.lean`), so `HkMem α 4 (dynRHS … τ)` follows from `ℋ⁴`-honesty of the two
  summands by `GalBasis.hkMem_sub_open` plus the pointwise identity
  `(dynLin + dynRHS) - dynLin = dynRHS` (`HkMem_congr_Q0`).
  * `HkMem α 4 (dynLin … τ)`: `EpsE4Thr.regQo_LGammaT` at `hw` gives `HkMem α 4 (𝓛_Γ^T _)`,
    transferred to `dynLin = -𝓛_Γ^T` by `GalBasis.hkMem_neg_open`.
  * `HkMem α 4 (epsWP … τ)`: `epsWP_hkMem4_bnd` at `T := τ`, `s := τ`.  That lemma states its
    `hEll`-packages and its `ℋ⁶`-size hypothesis with the *same* constant, whereas here `hEll`
    uses `Ce` and the `ℓ⁶`-bound uses `B`; both `EllPkgGo` and `EllPkgK` are monotone in the
    package constant (`EllPkgGo_mono_const` / `EllPkgK_mono_const` below), so instantiating at
    `max Ce B` reconciles the two.
-/

/-- `EllPkgGo` is monotone in its package constant: the four size fields have the shape
`… ≤ Ce * (nonnegative factor)`. -/
theorem EllPkgGo_mono_const {α Ce Ce' : ℝ} (hα : 0 ≤ α) {g Φg : Work.FTS.Galerkin.Fn}
    (h : Ce ≤ Ce') (hp : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.rpow_nonneg hα _) hX
  refine ⟨hp.sol, hp.smooth, ⟨hp.R.1, ?_⟩, ⟨hp.U.1, ?_⟩, ⟨hp.V.1, ?_⟩, hp.vanishU,
    ⟨hp.Vth.1, ?_⟩⟩
  · exact le_trans hp.R.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.U.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.V.2 (mul_le_mul_of_nonneg_right h hX)
  · refine le_trans hp.Vth.2 ?_
    calc Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g
        = Ce * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) := mul_assoc _ _ _
      _ ≤ Ce' * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right h hA
      _ = Ce' * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g := (mul_assoc _ _ _).symm

/-- `EllPkgK` is monotone in its package constant: the three size fields have the shape
`… ≤ Ce * HkNorm α k g`. -/
theorem EllPkgK_mono_const {α Ce Ce' : ℝ} {k : ℕ} {g Φg : Work.FTS.Galerkin.Fn}
    (h : Ce ≤ Ce') (hp : Work.FTS.ClassC.EllPkgK α k Ce g Φg) :
    Work.FTS.ClassC.EllPkgK α k Ce' g Φg := by
  have hX : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  refine ⟨hp.sol, hp.smooth, ⟨hp.R.1, ?_⟩, ⟨hp.U.1, ?_⟩, ⟨hp.V.1, ?_⟩⟩
  · exact le_trans hp.R.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.U.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.V.2 (mul_le_mul_of_nonneg_right h hX)

theorem HQo_dynRHS {α C₀ B Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {ε τ : ℝ}
    (hτ : 0 < τ) (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 τ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 τ, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ B) :
    Work.FTS.VocabO.HQo α 4 (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) τ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hτmem : τ ∈ Set.Icc (0 : ℝ) τ := ⟨hτ.le, le_rfl⟩
  have hw : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) := hC τ hτmem
  have hell : Work.FTS.VocabO.EllPkgGo α Ce
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) := (hEll _ hw).1
  refine ⟨?_, ?_⟩
  · exact Work.FTS.StrongEps.smoothOpen_dynRHS_of_classC hα0 hα1 hw hell hstar
  · -- reconcile the two constants: packages at `Ce`, `ℋ⁶`-size at `B`
    have hCeB : Ce ≤ max Ce B := le_max_left _ _
    have hBle : B ≤ max Ce B := le_max_right _ _
    have hEllB : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α (max Ce B) u (E u) ∧
          Work.FTS.ClassC.EllPkgK α 6 (max Ce B) u (E u) :=
      fun u hu => ⟨EllPkgGo_mono_const hα0.le hCeB (hEll u hu).1,
        EllPkgK_mono_const hCeB (hEll u hu).2⟩
    have hb6B : ∀ s ∈ Set.Icc (0 : ℝ) τ, Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ max Ce B :=
      fun s hs => le_trans (hb6 s hs) hBle
    obtain ⟨KW, _hKW, hbnd⟩ :=
      Work.FTS.StrongEps.epsWP_hkMem4_bnd (α := α) (C₀ := C₀) (Ce := max Ce B) (Cs := Cs)
        (T := τ) (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε)
        hα hEllB hstar hml hC hb4 hb6B
    -- the two summands, and `epsWP = dynLin + dynRHS` definitionally
    have hEpssmo : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) :=
      Work.FTS.StrongEps.smoothOpen_epsWP (C₀ := C₀) (T := τ) hα hEllB hstar hC τ hτmem
    have hEpsmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) :=
      (hbnd τ hτmem).1
    have hLGT := Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT (α := α)
      (x := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) hα hw
    have hlinsmo : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.FTS.GalBasis.smoothOpen_neg hLGT.1
    have hlinmem : Work.Spaces.HkMem α 4
        (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.FTS.GalBasis.hkMem_neg_open α 4 hLGT.2.1
    have hsub : Work.Spaces.HkMem α 4
        (fun z θ => Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ
          - Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ) :=
      Work.FTS.GalBasis.hkMem_sub_open α 4 hEpssmo hlinsmo hEpsmem hlinmem
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsub
      (fun z _hz θ _hθ => ?_)
    show Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ
        - Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
      = Work.FTS.Galerkin.dynRHS α
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
          (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
    simp only [Work.FTS.StrongEps.epsWP]
    ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.N_b6_rad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.N_b6_rad` — the four radial pieces `NBlk α w Φs Φg k`, `k ∈ {12,13,14,15}`, at level 6

The four pieces are

* `k = 12`: `-½ · (FK w · D_θ w)` (both factors `w`-derived),
* `k = 13`: `-½ · (D_θ F_* · FK w)`,
* `k = 14`: `-½ · ((-2α) hKer · D_θ w)`,
* `k = 15`: `-½ · (FK F_* · D_θ F_*)`.

See `Route.lean` and `NOTES_N_b6_route.md` for the place of these four pieces in the level-6
semi-tame estimate of the `N`-block.  All four bounds are linear in `1 + HkSq α 7 w` (with a
coefficient depending only on `α`, `C₀`, `Ce`, `Cs`), which is stronger than the stated
`K(1+HkSq α 7 w) + K(1+HkSq α 6 w)²`.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn)
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Small helpers -/

/-- `HkSq α k F` is the square of `HkNorm α k F`. -/
private theorem hkSq_eq_norm_sq (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k F = (Work.Spaces.HkNorm α k F) ^ 2 := by
  rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]

/-- `HkSq α 4 w = (Xn α w)²`, definitionally in `Xn`. -/
private theorem hkSq_four_eq_Xn_sq (α : ℝ) (w : Fn) :
    Work.Spaces.HkSq α 4 w = (Work.FTS.Nonlin.Xn α w) ^ 2 := by
  have h : Work.FTS.Nonlin.Xn α w = Work.Spaces.HkNorm α 4 w := rfl
  rw [h, ← hkSq_eq_norm_sq]

/-- `(HkNorm α 6 w)² = HkSq α 6 w`. -/
private theorem hkN_six_sq (α : ℝ) (w : Fn) :
    (Work.Spaces.HkNorm α 6 w) ^ 2 = Work.Spaces.HkSq α 6 w :=
  (hkSq_eq_norm_sq α 6 w).symm

/-- For `m ≤ 4` the `ℋ^m`-energy of `w` is `α`-small: `HkSq α m w ≤ C₀'²α⁴`. -/
private theorem hkSq_le_four {α C₀ : ℝ} {w : Fn}
    (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) {m : ℕ} (hm : m ≤ 4)
    (hmem : Work.Spaces.HkMem α 4 w) :
    Work.Spaces.HkSq α m w ≤ (max C₀ 0) ^ 2 * α ^ 4 := by
  have h1 : Work.Spaces.HkSq α m w ≤ Work.Spaces.HkSq α 4 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α hm hmem
  have h2 : Work.Spaces.HkSq α 4 w ≤ (max C₀ 0 * α ^ 2) ^ 2 := by
    rw [hkSq_four_eq_Xn_sq α w]
    refine pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) ?_ 2
    exact le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg α))
  refine le_trans h1 (le_trans h2 (le_of_eq ?_))
  ring

/-- Absorbing a piece bound `x ≤ Kx (1 + H7)` into the statement's shape. -/
private theorem absorb {Ksum Kx H7 H6 x : ℝ} (hKx : Kx ≤ Ksum) (hKs : 0 ≤ Ksum) (h7 : 0 ≤ H7)
    (h6 : 0 ≤ H6) (hx : x ≤ Kx * (1 + H7)) :
    x ≤ Ksum * (1 + H7) + Ksum * (1 + H6) ^ 2 := by
  have h1 : 0 ≤ 1 + H7 := by linarith
  have h3 : Kx * (1 + H7) ≤ Ksum * (1 + H7) := mul_le_mul_of_nonneg_right hKx h1
  have h2 : 0 ≤ Ksum * (1 + H6) ^ 2 := mul_nonneg hKs (sq_nonneg _)
  linarith

/-- The `𝒲^{6,∞}`-priced level-6 product rule `hknorm_mul_of_WlInf6_cd6`, with the (proved but
hidden) threshold made explicit: it holds for every `0 < α ≤ 1`. -/
private theorem mulWl :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨Real.sqrt ((7 * Cz + 49 * Cm) * 42701), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α f g hα hα1 hfs hfw hgs hgm
  exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_aux6 hα hα1 hfs hfw hgs hgm
    hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' => hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)

/-! ## The piece `k = 13`: `-½ · (D_θ F_* · FK w)` -/

private theorem b13 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 13)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmul, hCmulpos, hmul⟩ := mulWl
  obtain ⟨Cd, hCdpos, hDth⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C6, hC6pos, hFK6⟩ := Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
  obtain ⟨Cfp, Xi, Cpow, hCfppos, hXipos, hCpownn, hFpfacts⟩ :=
    Work.FTS.StrongPersist.H6Row6.fkFacts7
  -- the smoothness and `𝒲^{6,∞}`-data of `D_θF_*`
  have hDthCD : ContDiffOn ℝ 6
      (Function.uncurry (Work.Spaces.Dth (Work.Construction.Fstar α)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth.of_le
      (by simp [Work.Stability.smoothOrder])
  obtain ⟨hDthMemW, hDthW⟩ := hDth α hα0 hα1
  set B : ℝ := Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ 2) * C6 with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCmulpos.le (Real.rpow_nonneg hα0.le _))
      (mul_nonneg hCdpos.le (sq_nonneg α))) hC6pos.le
  refine ⟨(1 / 4) * B ^ 2 + 1, by positivity, ?_⟩
  intro w Φs Φg hw
  have hmem6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  obtain ⟨hFKCD, hFKmem4, hFKn4, hFKmem6, hFKn6, hFKpt⟩ :=
    hFpfacts hα0 hα1 w ⟨hw.reg, hmem6w⟩ hw.mem hw.l12
  have hFK6b : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
      ≤ C6 * Work.Spaces.HkNorm α 6 w := hFK6 α hα0 hα1 w hw.reg hmem6w
  obtain ⟨hmemProd, hProd⟩ := hmul hα0 hα1 hDthCD hDthMemW hFKCD hFKmem6
  have hmain : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * Work.Construction.FK w z) ≤ B * Work.Spaces.HkNorm α 6 w := by
    refine le_trans hProd ?_
    have h1 : Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ Cd * α ^ 2 :=
      hDthW
    have hnn : 0 ≤ Cmul * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCmulpos.le (Real.rpow_nonneg hα0.le _)
    have hstep : Cmul * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ 2) * (C6 * Work.Spaces.HkNorm α 6 w) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hnn) hFK6b
        (Work.Spaces.HkNorm_nonneg α 6 _) ?_
      exact mul_nonneg (mul_nonneg hCmulpos.le (Real.rpow_nonneg hα0.le _))
        (mul_nonneg hCdpos.le (sq_nonneg α))
    calc Cmul * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ 2) * (C6 * Work.Spaces.HkNorm α 6 w) := hstep
      _ = B * Work.Spaces.HkNorm α 6 w := by rw [hBdef]; ring_nf
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 13)
      = (1 / 4) * (Work.Spaces.HkNorm α 6
          (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
            * Work.Construction.FK w z)) ^ 2 := by
    rw [show Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 13
        = fun z θ => (-(1 / 2)) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
            * Work.Construction.FK w z) from rfl]
    rw [Work.FTS.StrongEps.HkSq_const_mul,
      hkSq_eq_norm_sq α 6 (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * Work.Construction.FK w z)]
    ring
  rw [hsq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hb2 : (B * Work.Spaces.HkNorm α 6 w) ^ 2 = B ^ 2 * Work.Spaces.HkSq α 6 w := by
    rw [mul_pow, hkN_six_sq α w]
  have h1 : (1 / 4) * (Work.Spaces.HkNorm α 6
        (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * Work.Construction.FK w z)) ^ 2 ≤ (1 / 4) * (B * Work.Spaces.HkNorm α 6 w) ^ 2 := by
    have h := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hmain 2
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have h2 : (1 / 4) * (B * Work.Spaces.HkNorm α 6 w) ^ 2
      = (1 / 4) * B ^ 2 * Work.Spaces.HkSq α 6 w := by rw [hb2]; ring
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hw.mem
  have h3 : (1 / 4) * B ^ 2 * Work.Spaces.HkSq α 6 w ≤ (1 / 4) * B ^ 2 * (1 + Work.Spaces.HkSq α 7 w) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have h4 : (1 / 4) * B ^ 2 * (1 + Work.Spaces.HkSq α 7 w)
      ≤ ((1 / 4) * B ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    linarith
  calc (1 / 4) * (Work.Spaces.HkNorm α 6
        (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * Work.Construction.FK w z)) ^ 2
      ≤ (1 / 4) * (B * Work.Spaces.HkNorm α 6 w) ^ 2 := h1
    _ = (1 / 4) * B ^ 2 * Work.Spaces.HkSq α 6 w := h2
    _ ≤ (1 / 4) * B ^ 2 * (1 + Work.Spaces.HkSq α 7 w) := h3
    _ ≤ ((1 / 4) * B ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w) := h4

/-! ## The piece `k = 14`: `-½ · ((-2α) hKer · D_θ w)` -/

private theorem b14 {α C₀ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmag, hCmagpos, hmaj⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FTS.StrongEps.E4R3.Nblock6.RadCoeffJets
  set Bc : ℝ := Cc * (2 * α) with hBcdef
  have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
  set C4 : ℝ := (max C₀ 0) ^ 2 * α ^ 4 with hC4def
  have hC4nn : 0 ≤ C4 := by rw [hC4def]; positivity
  refine ⟨(1 / 4) * Cmag * (Bc ^ 2 * (1 + C4)) + 1, by positivity, ?_⟩
  intro w Φs Φg hw hXw
  set X : ℝ → ℝ := fun z => (-(2 * α)) * Work.Spaces.hKer z with hXdef
  set f : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.Dth w z θ with hfdef
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hXcd : ContDiffOn ℝ 6 X (Set.Ioi 0) := by
    rw [hXdef]; exact hCc.2.2.2 (-(2 * α))
  have hXjet : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j X z| ≤ Bc := by
    intro j hj z hz
    have h := hCc.2.2.1 (-(2 * α)) j hj z hz
    have habs : |(-(2 * α))| = 2 * α := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [habs] at h
    rw [hXdef, hBcdef]
    exact h
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := by rw [hfdef]; exact hw.reg.Dth
  have hmf : Work.Spaces.HkMem α 6 f := by
    rw [hfdef]
    exact Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hw.mem
  have hmain := hmaj α X f Bc Bc hXcd hsmf hmf hBcnn hBcnn
    (fun j hj z hz => hXjet j (by omega) z hz)
    (fun j hj z hz => hXjet j hj z hz)
  have h6 : Work.Spaces.HkSq α 6 f ≤ Work.Spaces.HkSq α 7 w := by
    rw [hfdef]
    exact Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 6 hw.mem
  have h2 : Work.Spaces.HkSq α 2 f ≤ C4 := by
    rw [hfdef, hC4def]
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 2
      (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 3 (by norm_num) hw.mem)) ?_
    exact hkSq_le_four hXw (m := 3) (by norm_num) hmem4w
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14)
      = (1 / 4) * Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ) := by
    rw [show Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14
        = fun z θ => (1 / 2) * (X z * f z θ) from rfl]
    rw [Work.FTS.StrongEps.HkSq_const_mul]
    ring
  rw [hsq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hB2 : (0 : ℝ) ≤ Bc ^ 2 := sq_nonneg Bc
  have hb1 : Bc ^ 2 * Work.Spaces.HkSq α 6 f ≤ Bc ^ 2 * Work.Spaces.HkSq α 7 w :=
    mul_le_mul_of_nonneg_left h6 hB2
  have hb2 : Bc ^ 2 * Work.Spaces.HkSq α 2 f ≤ Bc ^ 2 * C4 := mul_le_mul_of_nonneg_left h2 hB2
  have hstep1 : (1 / 4) * Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4))) := by
    have hsum : Bc ^ 2 * Work.Spaces.HkSq α 6 f + Bc ^ 2 * Work.Spaces.HkSq α 2 f
        ≤ Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4) := by linarith
    have h1 : Cmag * (Bc ^ 2 * Work.Spaces.HkSq α 6 f + Bc ^ 2 * Work.Spaces.HkSq α 2 f)
        ≤ Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)) :=
      mul_le_mul_of_nonneg_left hsum hCmagpos.le
    refine le_trans (le_trans (mul_le_mul_of_nonneg_left hmain (by norm_num)) ?_) le_rfl
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hstep2 : (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)))
      ≤ (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) := by
    have hkey : Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)
        ≤ Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w)) := by
      refine mul_le_mul_of_nonneg_left ?_ hB2
      nlinarith [h7nn, hC4nn]
    calc (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)))
        = (1 / 4 * Cmag) * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)) := by ring
      _ ≤ (1 / 4 * Cmag) * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) := by ring
  have hstep3 : (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w)))
      = ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4))) * (1 + Work.Spaces.HkSq α 7 w) := by ring
  have hstep4 : ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4))) * (1 + Work.Spaces.HkSq α 7 w)
      ≤ ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    linarith
  calc (1 / 4) * Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4))) := hstep1
    _ ≤ (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) := hstep2
    _ = ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4))) * (1 + Work.Spaces.HkSq α 7 w) := hstep3
    _ ≤ ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := hstep4

/-! ## The piece `k = 15`: `-½ · (FK F_* · D_θ F_*)` -/

private theorem b15 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn},
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 15)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmag, hCmagpos, hmaj⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FTS.StrongEps.E4R3.Nblock6.RadCoeffJets
  obtain ⟨Cslot, hCslotpos, hslot⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  obtain ⟨-, hDthSlot, -⟩ := hslot α ⟨hα0, hα1⟩
  obtain ⟨hfsm, hfmem, hfnorm⟩ := hDthSlot
  set X : ℝ → ℝ := fun z => -α / (1 + z) with hXdef
  set f : ℝ → ℝ → ℝ :=
    fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ with hfdef
  set Bc : ℝ := Cc * α with hBcdef
  set P : ℝ := (Cslot * α ^ (-(1 : ℝ))) ^ 2 with hPdef
  have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  refine ⟨Cmag * (Bc ^ 2 * (2 * P)) + 1, by positivity, ?_⟩
  intro w Φs Φg
  have hXcd : ContDiffOn ℝ 6 X (Set.Ioi 0) := by
    rw [hXdef]; exact hCc.2.1 (-α)
  have hXjet : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j X z| ≤ Bc := by
    intro j hj z hz
    have h := hCc.1 (-α) j hj z hz
    rw [abs_neg, abs_of_pos hα0] at h
    rw [hXdef, hBcdef]
    exact h
  have hmain := hmaj α X f Bc Bc hXcd hfsm hfmem hBcnn hBcnn
    (fun j hj z hz => hXjet j (by omega) z hz)
    (fun j hj z hz => hXjet j hj z hz)
  have h6f : Work.Spaces.HkSq α 6 f ≤ P := by
    rw [hPdef, hkSq_eq_norm_sq α 6 f]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 f) hfnorm 2
  have h2f : Work.Spaces.HkSq α 2 f ≤ P :=
    le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hfmem) h6f
  have heq : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 15
      = fun z θ => X z * f z θ := by
    funext z θ
    simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, hXdef, hfdef]
    rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα0 hα1]
    by_cases hz : (1 : ℝ) + z = 0
    · have hz1 : z = -1 := by linarith
      subst hz1
      norm_num
    · field_simp <;> ring
  rw [heq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hB2 : (0 : ℝ) ≤ Bc ^ 2 := sq_nonneg Bc
  have hb1 : Bc ^ 2 * Work.Spaces.HkSq α 6 f ≤ Bc ^ 2 * P := mul_le_mul_of_nonneg_left h6f hB2
  have hb2 : Bc ^ 2 * Work.Spaces.HkSq α 2 f ≤ Bc ^ 2 * P := mul_le_mul_of_nonneg_left h2f hB2
  have hstep1 : Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ Cmag * (Bc ^ 2 * (2 * P)) := by
    have hsum : Bc ^ 2 * Work.Spaces.HkSq α 6 f + Bc ^ 2 * Work.Spaces.HkSq α 2 f
        ≤ Bc ^ 2 * (2 * P) := by linarith
    exact le_trans hmain (mul_le_mul_of_nonneg_left hsum hCmagpos.le)
  have hstep2 : Cmag * (Bc ^ 2 * (2 * P)) ≤ (Cmag * (Bc ^ 2 * (2 * P)) + 1)
      * (1 + Work.Spaces.HkSq α 7 w) := by
    have h1 : Cmag * (Bc ^ 2 * (2 * P)) ≤ Cmag * (Bc ^ 2 * (2 * P)) + 1 := by linarith
    have h2 : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
    calc Cmag * (Bc ^ 2 * (2 * P)) ≤ Cmag * (Bc ^ 2 * (2 * P)) + 1 := h1
      _ ≤ (Cmag * (Bc ^ 2 * (2 * P)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
          nth_rewrite 1 [show Cmag * (Bc ^ 2 * (2 * P)) + 1
              = (Cmag * (Bc ^ 2 * (2 * P)) + 1) * 1 from (mul_one _).symm]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact le_trans hstep1 hstep2

/-! ## The piece `k = 12`: `-½ · (FK w · D_θ w)` -/

private theorem b12 {α C₀ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cper, hCperpos, hper⟩ := Work.FTS.StrongEps.E4R3.Nblock6.RadPer
  obtain ⟨Cj, hCjpos, hjet⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  set C0m : ℝ := max C₀ 0 with hC0mdef
  have hC0mnn : 0 ≤ C0m := by rw [hC0mdef]; exact le_max_right _ _
  set Q : ℝ := C0m ^ 2 * α ^ 4 with hQdef
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  refine ⟨(1 / 4) * Cper * (7 * (Cj * Q)) + 1, by positivity, ?_⟩
  intro w Φs Φg hw hXw
  -- the datum `f = D_θ w`
  have hsmf : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hw.reg.Dth
  have hm6f : Work.Spaces.HkMem α 6 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hw.mem
  -- the radial factor `FK w` is `C⁶` on `(0,∞)`
  have hCD2 : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK w z))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.co6_FK_radial hα0 hα1 hw.reg hw.mem
  have hXcd : ContDiffOn ℝ 6 (fun z => Work.Construction.FK w z) (Set.Ioi 0) := by
    have hφ : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi (0 : ℝ)) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have hmap : Set.MapsTo (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi (0 : ℝ))
        Work.FTS.EllipticEst.Q0 := fun z hz =>
      ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩
    exact (hCD2.comp hφ hmap).congr (fun z _ => rfl)
  -- the a.e. jet bounds
  have hjet' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ b : ℕ, b ≤ 6 →
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK w z) z) ^ 2
        ≤ Cj * Work.Spaces.HkSq α (b + 1) w := by
    have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ∀ b ∈ Finset.range 7,
        (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK w z) z) ^ 2
          ≤ Cj * Work.Spaces.HkSq α (b + 1) w := by
      rw [Finset.eventually_all]
      intro b hb7
      have hb6 : b ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hb7)
      have h := hjet hα0 hw.reg
        (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem) hw.mem b hb6
      simpa only [Work.Elliptic.DzIter_rad] using h
    refine h1.mono (fun z hz b hb6 => hz b (Finset.mem_range.mpr (by omega)))
  have hB0 : ∀ b : ℕ, 0 ≤ Cj * Work.Spaces.HkSq α (b + 1) w := fun b =>
    mul_nonneg hCjpos.le (Work.Spaces.HkSq_nonneg α (b + 1) w)
  have hmain := hper hXcd hsmf hm6f hB0 hjet'
  -- the per-`b` bound
  have hterm : ∀ b ∈ Finset.range 7,
      (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w)
        ≤ Cj * Q * (1 + Work.Spaces.HkSq α 7 w) := by
    intro b hb7
    have hb6 : b ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hb7)
    have hD : Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α (7 - b) w := by
      have h := Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 (6 - b)
        (Work.FTS.OpenPkg.HkMem_mono_open hw.reg (6 - b + 1) (by omega) hw.mem)
      rwa [show 6 - b + 1 = 7 - b from by omega] at h
    have hDnn : 0 ≤ Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w) :=
      Work.Spaces.HkSq_nonneg α (6 - b) _
    have hleft : (0 : ℝ) ≤ Cj * Work.Spaces.HkSq α (b + 1) w :=
      mul_nonneg hCjpos.le (Work.Spaces.HkSq_nonneg α (b + 1) w)
    have step1 : (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w)
        ≤ (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w :=
      mul_le_mul_of_nonneg_left hD hleft
    by_cases hb3 : b ≤ 3
    · -- `b ≤ 3`: the `ℋ^{b+1}`-factor is `α`-small
      have hS : Work.Spaces.HkSq α (b + 1) w ≤ Q := by
        rw [hQdef]
        exact hkSq_le_four hXw (m := b + 1) (by omega)
          (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem)
      have hT : Work.Spaces.HkSq α (7 - b) w ≤ 1 + Work.Spaces.HkSq α 7 w := by
        have h := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (show 7 - b ≤ 7 by omega) hw.mem
        linarith [Work.Spaces.HkSq_nonneg α 7 w]
      have h1 : (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w
          ≤ (Cj * Q) * (1 + Work.Spaces.HkSq α 7 w) := by
        refine mul_le_mul ?_ hT (Work.Spaces.HkSq_nonneg α (7 - b) w) ?_
        · exact mul_le_mul_of_nonneg_left hS hCjpos.le
        · exact mul_nonneg hCjpos.le hQnn
      exact le_trans step1 h1
    · -- `4 ≤ b`: the `ℋ^{7-b}`-factor is `α`-small
      have hS : Work.Spaces.HkSq α (7 - b) w ≤ Q := by
        rw [hQdef]
        exact hkSq_le_four hXw (m := 7 - b) (by omega)
          (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem)
      have hT : Work.Spaces.HkSq α (b + 1) w ≤ 1 + Work.Spaces.HkSq α 7 w := by
        have h := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (show b + 1 ≤ 7 by omega) hw.mem
        linarith [Work.Spaces.HkSq_nonneg α 7 w]
      have h1 : (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w
          ≤ (Cj * Q) * (1 + Work.Spaces.HkSq α 7 w) := by
        calc (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w
            ≤ (Cj * (1 + Work.Spaces.HkSq α 7 w)) * Q := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left hT hCjpos.le) hS
                (Work.Spaces.HkSq_nonneg α (7 - b) w)
                (mul_nonneg hCjpos.le (by linarith [Work.Spaces.HkSq_nonneg α 7 w]))
          _ = (Cj * Q) * (1 + Work.Spaces.HkSq α 7 w) := by ring
      exact le_trans step1 h1
  have hsum : (∑ b ∈ Finset.range 7,
        (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w))
      ≤ 7 * (Cj * Q * (1 + Work.Spaces.HkSq α 7 w)) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12)
      = (1 / 4) * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.FK w z * Work.Spaces.Dth w z θ) := by
    rw [show Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12
        = fun z θ => (-(1 / 2)) * (Work.Construction.FK w z * Work.Spaces.Dth w z θ) from rfl]
    rw [Work.FTS.StrongEps.HkSq_const_mul]
    ring
  rw [hsq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hbig : Work.Spaces.HkSq α 6
        (fun z θ => Work.Construction.FK w z * Work.Spaces.Dth w z θ)
      ≤ Cper * (7 * (Cj * Q * (1 + Work.Spaces.HkSq α 7 w))) := by
    refine le_trans hmain (mul_le_mul_of_nonneg_left hsum hCperpos.le)
  calc (1 / 4) * Work.Spaces.HkSq α 6
        (fun z θ => Work.Construction.FK w z * Work.Spaces.Dth w z θ)
      ≤ (1 / 4) * (Cper * (7 * (Cj * Q * (1 + Work.Spaces.HkSq α 7 w)))) :=
        mul_le_mul_of_nonneg_left hbig (by norm_num)
    _ = ((1 / 4) * Cper * (7 * (Cj * Q))) * (1 + Work.Spaces.HkSq α 7 w) := by ring
    _ ≤ ((1 / 4) * Cper * (7 * (Cj * Q)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        linarith

/-! ## The target -/

theorem N_b6_rad : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({12, 13, 14, 15} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
  intro C₀ Ce Cs α hαIoc
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαIoc
  obtain ⟨K12, hK12pos, hb12⟩ := b12 (C₀ := C₀) hα0 hα1
  obtain ⟨K13, hK13pos, hb13⟩ := b13 hα0 hα1
  obtain ⟨K14, hK14pos, hb14⟩ := b14 (C₀ := C₀) hα0 hα1
  obtain ⟨K15, hK15pos, hb15⟩ := b15 hα0 hα1
  have hKsum : 0 ≤ K12 + K13 + K14 + K15 + 1 := by linarith
  refine ⟨K12 + K13 + K14 + K15 + 1, by linarith, ?_⟩
  intro Φs w Φg hw hXw hz hell hK6 hstar k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact absorb (Kx := K12) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb12 hw hXw)
  · exact absorb (Kx := K13) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb13 hw)
  · exact absorb (Kx := K14) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb14 hw hXw)
  · exact absorb (Kx := K15) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb15)

end Work.FTS.StrongEps.E4R3.Nblock6
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.N0_N_Transport_pt_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem N0_N_Transport_pt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
        {ε τ C₀ B : ℝ} {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ B →
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ|
          ≤ C * (1 + C₀) * (1 + B) / Real.sin (2 * θ)) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ)
            z θ| ≤ C * (1 + C₀) * (1 + B) / Real.sin (2 * θ)) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Coercivity.Transport (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            z θ| ≤ C * (1 + C₀) * (1 + B) / Real.sin (2 * θ)) := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongEps.L12_abs_le_Xn
  obtain ⟨C7, hC7nn, hC7⟩ := Work.FTS.StrongEps.FK_abs_le_of_classC
  refine ⟨1000 * (CL + 1) + (30000 + 200 * C7) + 4, by linarith, ?_⟩
  intro α hαι ρ Φs E ε τ C₀ B g Maj hDec hC hXn hB
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  -- the nonnegativity of the two interface constants
  have hC₀0 : 0 ≤ C₀ := by
    have h1 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have h2 : 0 ≤ C₀ * α ^ 2 := le_trans h1 hXn
    by_contra hlt
    push_neg at hlt
    have h3 : 0 < α ^ 2 := pow_pos hα0 2
    have h4 : C₀ * α ^ 2 < 0 := mul_neg_of_neg_of_pos hlt h3
    linarith
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  -- the slot data of the interface (extracted before the `set`s rewrite it)
  obtain ⟨-, hWval, hWDz, hWDth, hSlotR, hSlotU, hSlotV⟩ := pt_EpsDecay_slots hDec
  -- the projected slice, the residual stream function and the full profile
  set W : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hWdef
  set Φg : ℝ → ℝ → ℝ :=
    Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ
    with hΦgdef
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ with hFdef
  have hFdec : F = fun z θ => Work.Construction.Fstar α z θ + W z θ := by
    rw [hFdef, hWdef]
    funext z θ
    rfl
  have hCS : Work.FTS.EllipticEst.SmoothOpen W := hC.reg
  have hWC4 : Work.Spaces.HkMem α 4 W :=
    Work.FTS.OpenPkg.HkMem_mono_open hCS 4 (by norm_num) hC.mem
  have hCS4 : Work.FTS.VocabO.HQo α 4 W := ⟨hCS, hWC4⟩
  have hL12W : ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12 W z| ≤ CL * (C₀ * α ^ 2) := by
    intro z hz
    refine le_trans (hCL α hα0 W hCS4 z hz.le) ?_
    exact mul_le_mul_of_nonneg_left hXn hCLpos.le
  have hFKW : ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK W z| ≤ C7 * B := hC7 α B hαι hC hB
  have hΞ := pt_Xi_slots hαι hCS hWC4 hSlotR hSlotU hSlotV
  -- the three blocks
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    refine le_trans (pt_N0_le hαι hC₀0 hB0 hCLpos hCS hFdec hWval hWDz hWDth hL12W
      z hz θ hθ) ?_
    have hs2pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    apply div_le_div_of_nonneg_right _ hs2pos.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1000 * (CL + 1)
        ≤ 1000 * (CL + 1) + (30000 + 200 * C7) + 4) (by linarith))
      (by linarith)
  · intro z hz θ hθ
    refine le_trans (pt_N_le hαι hC₀0 hB0 hC7nn hCS hWC4 hFdec hWval hWDz hWDth hFKW hΞ
      z hz θ hθ) ?_
    have hs2pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    apply div_le_div_of_nonneg_right _ hs2pos.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (30000 + 200 * C7)
        ≤ 1000 * (CL + 1) + (30000 + 200 * C7) + 4) (by linarith))
      (by linarith)
  · intro z hz θ hθ
    refine le_trans (pt_Transport_le hC₀0 hB0 hWDth z hz θ hθ) ?_
    have hs2pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    apply div_le_div_of_nonneg_right _ hs2pos.le
    have hCL1 : 0 ≤ 1000 * (CL + 1) := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [hCL1, hC7nn] : (3 : ℝ)
        ≤ 1000 * (CL + 1) + (30000 + 200 * C7) + 4) (by linarith))
      (by linarith)

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.BasicFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The angular traces of the difference of the right-hand side -/

/-- **The angular traces of `Δ = profRHS α Φs E W₁ − profRHS α Φs E W₂` vanish** at both
endpoints, for every `z > 0`.  This is what feeds `TraceToEpsMem` at the difference profile. -/
theorem DiffTraces {α Ce Cs : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W₁ W₂ : Fn} {E : Fn → Fn}
    (hW₁ : Work.FTS.ClassC.ClassC α W₁) (hW₂ : Work.FTS.ClassC.ClassC α W₂)
    (hell₁ : Work.FTS.VocabO.EllPkgGo α Ce W₁ (E W₁))
    (hell₂ : Work.FTS.VocabO.EllPkgGo α Ce W₂ (E W₂))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  obtain ⟨h1₁, h2₁⟩ := ProfRHSTraces hα hW₁ hell₁ hstar
  obtain ⟨h1₂, h2₂⟩ := ProfRHSTraces hα hW₂ hell₂ hstar
  exact ⟨fun z hz => by simpa using (h1₁ z hz).sub (h1₂ z hz),
    fun z hz => by simpa using (h2₁ z hz).sub (h2₂ z hz)⟩

/-! ## The single-function energy bound for the projection -/

/-- **The projection `P₀` preserves the weighted space `X` and its energy**, up to the fixed
constant `2 + B·C₁²/pzNorm²`: `EpsMem α (Pz f)` and `EpsSq α (Pz f) ≤ C · EpsSq α f` for
`SmoothOpen f`, `HkMem α 4 f` and `EpsMem α f`. -/
theorem EpsSq_Pz_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.StrongEps.EpsMem α f →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Pz f) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Pz f)
        ≤ C * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bump_of_smoothOpen
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.EpsSqTools.L12_le_sqrt_EpsSq
  have hpz : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨2 + B * C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2, ?_, ?_⟩
  · have h1 : 0 ≤ B * C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 :=
      div_nonneg (mul_nonneg hBpos.le (sq_nonneg _)) (sq_nonneg _)
    linarith
  intro α hα f hsm hm hmem
  set c : ℝ := Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm with hcdef
  have hpt : ∀ z θ : ℝ, Work.FTS.StrongEps.Pz f z θ = f z θ - c * Work.FTS.StrongEps.bump z θ := by
    intro z θ
    rw [Work.FTS.StrongEps.Pz_apply, hcdef]
  obtain ⟨hmem', hbd'⟩ := hB α hα f c hsm hmem
  have hcsq : c ^ 2 ≤ C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2
      * Work.FTS.StrongEps.EpsSq α f := by
    have hL := hC₁ α hα f hmem 0 (Set.mem_Ici.mpr le_rfl)
    have hS : 0 ≤ Work.FTS.StrongEps.EpsSq α f := Work.FTS.StrongEps.EpsSq_nonneg α f
    rw [hcdef]
    have h2 : (Work.Construction.L12 f 0) ^ 2 ≤ C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α f := by
      have h3 : (Work.Construction.L12 f 0) ^ 2
          ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α f)) ^ 2 := by
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (Work.Construction.L12 f 0)) hL 2
      rwa [mul_pow, Real.sq_sqrt hS] at h3
    calc (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm) ^ 2
        = (Work.Construction.L12 f 0) ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 := by rw [div_pow]
      _ ≤ (C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α f) / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right h2 (pow_pos hpz 2).le
      _ = C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 * Work.FTS.StrongEps.EpsSq α f := by ring
  refine ⟨Work.FTS.StrongEps.EpsSqTools.EpsMem_congr (fun z θ => (hpt z θ).symm) hmem', ?_⟩
  rw [Work.FTS.StrongEps.EpsSq_congr (fun z θ => hpt z θ)]
  calc Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - c * Work.FTS.StrongEps.bump z θ)
      ≤ 2 * Work.FTS.StrongEps.EpsSq α f + B * c ^ 2 := hbd'
    _ ≤ 2 * Work.FTS.StrongEps.EpsSq α f
        + B * (C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 * Work.FTS.StrongEps.EpsSq α f) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcsq hBpos.le)
    _ = (2 + B * C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2) * Work.FTS.StrongEps.EpsSq α f := by ring

/-! ## The `ℋ⁶`-size of the projected-mollified profile, and monotonicity in `B` -/


/-- **The `ℋ⁶`-size of `W_u = Pz (J_ε u)` is proportional to `B`**, with the loss
`(γ−1)^{-1}(C/ε)⁶`: `|W_u|_{ℋ⁶} ≤ C/(γ−1)·(C/ε)⁶·B` for `ProfileData α C₀ B ε ρ u`.  This is the
`ℋ⁶`-companion of `WpUniformBound` and is what allows `XDataClean`/`ProfRHSEpsData` (whose size
hypothesis is stated at the *profile*) to be applied at `W_u`, where only the datum's `ℋ⁶`-bound
`|u|_{ℋ⁶} ≤ B` is available. -/
theorem WpSixBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {C₀ B : ℝ}, 0 ≤ B →
      ∀ {u : Fn}, ProfileData α C₀ B ε ρ u →
      Work.Spaces.HkNorm α 6 (Wp ρ ε u)
        ≤ C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B := by
  obtain ⟨CF, hCFpos, hPF⟩ := ProfileFacts ρ hρ
  refine ⟨max 1 CF, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α hα ε hε C₀ B hB u hd
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα.1
    linarith
  set C : ℝ := max 1 CF with hCdef
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCFle : CF ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hCF0 : 0 ≤ CF := hCFpos.le
  have hε0 : 0 ≤ ε := hε.1.le
  have hCe0 : 0 ≤ C / ε := div_nonneg (le_trans zero_le_one hC1) hε0
  obtain ⟨-, hsq_u, h6, -, -, -, hm7, -⟩ := hPF α hα ε hε hd
  have h1 : Work.Spaces.HkSq α 1 u ≤ B ^ 2 := by
    have h := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num : 1 ≤ 6) hd.hkmem
    rw [show Work.Spaces.HkSq α 6 u = (Work.Spaces.HkNorm α 6 u) ^ 2 from by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 u)]] at h
    exact le_trans h (pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 u) hd.hknorm 2)
  have hEps : Work.FTS.StrongEps.EpsSq α u
      ≤ C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 := by
    have hcoef : CF / (Work.Spaces.gam α - 1) ^ 2 ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
      div_le_div_of_nonneg_right hCFle (pow_pos hγpos 2).le
    calc Work.FTS.StrongEps.EpsSq α u
        ≤ CF / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u := hsq_u
      _ ≤ CF / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hCF0 (pow_pos hγpos 2).le)
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg B)
  have h6' : Work.Spaces.HkSq α 6 (Wp ρ ε u)
      ≤ C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) := by
    have hbase : CF / ε ≤ C / ε := div_le_div_of_nonneg_right hCFle hε0
    have hp : (CF / ε) ^ 12 ≤ (C / ε) ^ 12 :=
      pow_le_pow_left₀ (div_nonneg hCF0 hε0) hbase 12
    have hCC : CF * (CF / ε) ^ 12 ≤ C * (C / ε) ^ 12 :=
      mul_le_mul hCFle hp (pow_nonneg (div_nonneg hCF0 hε0) 12) (le_trans zero_le_one hC1)
    calc Work.Spaces.HkSq α 6 (Wp ρ ε u)
        ≤ CF * (CF / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α u := h6
      _ ≤ CF * (CF / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hEps
            (mul_nonneg hCF0 (pow_nonneg (div_nonneg hCF0 hε0) 12))
      _ ≤ C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_right hCC
            (mul_nonneg (div_nonneg (le_trans zero_le_one hC1) (pow_pos hγpos 2).le) (sq_nonneg B))
  have hY2 : (C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B) ^ 2
      = C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) := by
    rw [show C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B
        = C / (Work.Spaces.gam α - 1) * ((C / ε) ^ 6 * B) from by ring]
    rw [mul_pow, div_pow, mul_pow, ← pow_mul (C / ε) 6 2]
    ring
  have hfin : C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B
      = max 1 CF / (Work.Spaces.gam α - 1) * (max 1 CF / ε) ^ 6 * B := by rw [hCdef]
  rw [← hfin]
  calc Work.Spaces.HkNorm α 6 (Wp ρ ε u)
      = Real.sqrt (Work.Spaces.HkSq α 6 (Wp ρ ε u)) := rfl
    _ ≤ Real.sqrt ((C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [hY2]; exact h6')
    _ = C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B := Real.sqrt_sq (by positivity)

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

theorem ProfRHSEpsData {α C₀ Ce Cs B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ R : ℝ, 0 < R ∧ ∀ {W : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W → Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 W ≤ B →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) ≤ R := by
  classical
  -- ## the profile data of `profRHS`: smooth, honest, of bounded `ℋ⁴`-size
  obtain ⟨CX, hCX, hX⟩ :=
    XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := B) hα hEll hstar hml hB
  -- ## the trace-to-`ε`-space transfer
  obtain ⟨C, hCpos, hTE⟩ := Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
  -- ## `γ - 1 = α/10 > 0`
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]
    linarith [hα.1]
  have hcoefnn : 0 ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
    div_nonneg hCpos.le (sq_nonneg _)
  refine ⟨C / (Work.Spaces.gam α - 1) ^ 2 * (CX + 1), ?_, ?_⟩
  · have h1 : 0 < (Work.Spaces.gam α - 1) ^ 2 := pow_pos hgam1 2
    positivity
  · intro W hW hXn hHk
    obtain ⟨hso, hmem4, hsq4⟩ := hX hW hXn hHk
    have hmem1 : Work.Spaces.HkMem α 1 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) :=
      Work.FTS.OpenPkg.HkMem_mono_open hso 1 (by norm_num) hmem4
    obtain ⟨ht1, ht2⟩ :=
      ProfRHSTraces (α := α) (Ce := Ce) (Cs := Cs) hα hW (hEll W hW).1 hstar
    obtain ⟨hem, hesq⟩ := hTE α hα _ hso hmem1 ht1 ht2
    refine ⟨hem, ?_⟩
    have hmono : Work.Spaces.HkSq α 1 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W)
        ≤ Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) :=
      Work.FTS.StrongLWP.HkSq_mono_of_mem (k := 4) (k' := 1) (by norm_num) hmem4
    calc Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * Work.Spaces.HkSq α 1 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) := hesq
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) :=
          mul_le_mul_of_nonneg_left hmono hcoefnn
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2 * (CX + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoefnn
          linarith

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.epsWP_hyp_bounds_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option maxHeartbeats 1600000

theorem epsWP_hyp_bounds_fam {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {G : ℕ → Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ Ce) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Work.Spaces.Iz,
        |Work.Construction.L12 (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
        |Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Construction.FK (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z| ≤ B) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
        |Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftau α
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
          (Work.Construction.N α (Work.Construction.Ftau α
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))| ≤ B) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨CL, hCLpos, hCL⟩ := L12_abs_le_Xn
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  obtain ⟨CF, hCF0, hCF⟩ := Work.FTS.StrongEps.FK_abs_le_of_classC
  obtain ⟨CZ, hCZpos, hCZ⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨K0, hK0pos, hN0z⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN0 (α := α) hα (C₀ := C₀) (B := Ce)
  obtain ⟨K1, hK1pos, hN1z⟩ :=
    Work.FTS.StrongEps.ClassCRHS.HkMemXnN (α := α) hα (C₀ := C₀) (B := Ce) (Ce := Ce) (Cs := Cs)
      (Φs := Φs)
  have hX0 : 0 ≤ max (C₀ * α ^ 2) 0 := le_max_right _ _
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  refine ⟨⟨CL * max (C₀ * α ^ 2) 0 + 1, by positivity, ?_⟩,
    ⟨CT * max (C₀ * α ^ 2) 0 + 1, by positivity, ?_⟩,
    ⟨CF * max Ce 0 + 1, by positivity, ?_⟩,
    ⟨CZ * (K0 + K1) + 1, by positivity, ?_⟩⟩
  · -- `L₁₂` of the slice, uniformly in `n`
    intro n s hs z hz
    have hCw := hC n s hs
    have hf : Work.FTS.VocabO.HQo α 4 (slice (JfamP ρ (ε n) (G n)) s) :=
      ⟨hCw.reg, Work.FTS.OpenPkg.HkMem_mono_open hCw.reg 4 (by norm_num) hCw.mem⟩
    have h1 := hCL α hα0 _ hf z hz
    have h2 : Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε n) (G n)) s) ≤ max (C₀ * α ^ 2) 0 :=
      le_trans (hb4 n s hs) (le_max_left _ _)
    have h3 := mul_le_mul_of_nonneg_left h2 hCLpos.le
    have h4 : 0 ≤ CL * max (C₀ * α ^ 2) 0 := mul_nonneg hCLpos.le hX0
    linarith
  · -- `L₁₂(Transport ·)(0)` of the slice, uniformly in `n`
    intro n s hs
    have hCw := hC n s hs
    have hm4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ (ε n) (G n)) s) :=
      Work.FTS.OpenPkg.HkMem_mono_open hCw.reg 4 (by norm_num) hCw.mem
    have h1 := hCT α _ hα0 hα1 hm4
    have h2 : Work.Spaces.HkNorm α 4 (slice (JfamP ρ (ε n) (G n)) s) ≤ max (C₀ * α ^ 2) 0 :=
      le_trans (hb4 n s hs) (le_max_left _ _)
    have h3 := mul_le_mul_of_nonneg_left h2 hCTpos.le
    have h4 : 0 ≤ CT * max (C₀ * α ^ 2) 0 := mul_nonneg hCTpos.le hX0
    linarith
  · -- `FK` of the slice, uniformly in `n`
    intro n s hs z hz
    have h1 := hCF α (max Ce 0) hα (hC n s hs)
      (le_trans (hb6 n s hs) (le_max_left _ _)) z hz
    have h2 : 0 ≤ CF * max Ce 0 := mul_nonneg hCF0 hCe0
    linarith
  · -- `mubar` of the slice, uniformly in `n`
    intro n s hs
    set w : Fn := slice (JfamP ρ (ε n) (G n)) s with hw
    have hCw : Work.FTS.ClassC.ClassC α w := hC n s hs
    have hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 := hb4 n s hs
    have hBw : Work.Spaces.HkNorm α 6 w ≤ Ce := hb6 n s hs
    have hellw : Work.FTS.VocabO.EllPkgGo α Ce w (E w) := (hEll w hCw).1
    have hsmo := Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hCw hellw hstar
    obtain ⟨hmemN0, hbndN0⟩ := hN0z hCw hXw hBw
    obtain ⟨hmemN1, hbndN1⟩ := hN1z hCw hXw hBw hellw hstar
    have hN0Q : Work.FTS.VocabO.HQo α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
      ⟨hsmo.2.2.2.1, hmemN0⟩
    have hN1Q : Work.FTS.VocabO.HQo α 4
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
      ⟨hsmo.2.2.2.2, hmemN1⟩
    have hL0 := hCZ α hα0 hα1 _ hN0Q
    have hL1 := hCZ α hα0 hα1 _ hN1Q
    have hF : Work.Construction.Ftau α (JfamP ρ (ε n) (G n)) s = Work.Construction.Ftot α w := by
      funext z θ
      rw [hw]
      rfl
    have hPhi : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ (ε n) (G n))) s
        = fun z θ => Φs z θ + E w z θ := by
      funext z θ
      rw [hw]
      rfl
    rw [hF, hPhi]
    have hmb : Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ))
        = Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0 := rfl
    rw [hmb]
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hXn1 : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ)) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    refine le_trans (abs_add_le _ _) ?_
    have hstep : |Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α w) w) 0|
          + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ)) 0|
        ≤ CZ * K0 + CZ * K1 := by
      refine add_le_add (le_trans hL0 (mul_le_mul_of_nonneg_left hbndN0 hCZpos.le))
        (le_trans hL1 (mul_le_mul_of_nonneg_left hbndN1 hCZpos.le))
    have hfin : CZ * K0 + CZ * K1 ≤ CZ * (K0 + K1) + 1 := by
      nlinarith [hCZpos.le, hK0pos.le, hK1pos.le]
    linarith

end Work.FTS.StrongEps

end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.vz7_thHol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.L.vz7_thHol` — the `θ`-Hölder modulus of the transport coefficient `Vz7`

A7 of the leaf plan (`THL/Leaves.lean`), in the namespace of this file.

`Vz7 = (1−μ) + L₁₂(F(τ))·c2m + 2α𝒱(Φ̃(τ))` is a *sum*, so its `θ`-modulus is the sum of the
moduli of the three terms:

* `1−μ` is `θ`-independent;
* the middle term is `L₁₂(F(τ))(z)·(c2m θ − c2m θ')`; `c2m = (3cos 2θ − 1)/2` is `3`-Lipschitz,
  and `|L₁₂ F(τ)(z)| ≤ CL` uniformly on the horizon (`RXT.Sys.L12FK_family_jets`, from the
  `LimApprox` clause of `DynOK'` alone — this is why the middle term needs no `z`-locality);
* the last term splits over `Φ̃(τ) = Φ̃_* + Φ̃_pert` on the open quadrant
  (`RXT.v2_phiTil_split` + `RXT.v2_vop_add_at`), and the two halves are the star/perturbation
  Hölder moduli of leaves **A4v** (`THL.vopStar_theta_holder`, exponent `pExp α/5`) and **A5v**
  (`THL.vopPert_theta_holder`, exponent `pExp α/20`, with the harmless factor `min z 1 ≤ 1`).

The two exponents are unified by the elementary `rpow`-shift lemma `vz7_rpow_shift_le`
(`d^a ≤ (π/2)^{a−β} d^β` for `0 ≤ d ≤ π/2`, `0 < β ≤ a`) at `a = 1` (the `c2m` term) and at
`a = pExp α/5` (the star term).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- the statement's binders `hμ`, `hSol`, `hEll` are intentionally unused by the proof
set_option linter.unusedVariables false

/-! ## §1 Two elementary one-dimensional inputs -/

/-- **The `rpow`-shift.** For a base `d` in `[0, π/2]` and exponents `0 < β ≤ a`, the larger
exponent costs only the constant `(π/2)^{a−β}`. -/
theorem vz7_rpow_shift_le {d β a : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ Real.pi / 2)
    (hβ : 0 < β) (hβa : β ≤ a) :
    d ^ a ≤ (Real.pi / 2) ^ (a - β) * d ^ β := by
  rcases eq_or_lt_of_le hd0 with h | h
  · rw [← h, Real.zero_rpow (by linarith : a ≠ 0), Real.zero_rpow hβ.ne']
    positivity
  · have h1 : d ^ a = d ^ (a - β + β) := by rw [sub_add_cancel]
    rw [h1, Real.rpow_add h]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd0 hd (by linarith))
      (Real.rpow_nonneg hd0 β)

/-- `c2m = (3cos 2θ − 1)/2` is `3`-Lipschitz. -/
theorem vz7_abs_c2m_sub_le (θ θ' : ℝ) :
    |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 3 * |θ - θ'| := by
  have h1 : |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ 2 * |θ - θ'| := by
    have h := Real.lipschitzWith_cos.dist_le_mul (2 * θ) (2 * θ')
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
    rw [show (2 : ℝ) * θ - 2 * θ' = 2 * (θ - θ') from by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  have h2 : Work.Construction.c2m θ - Work.Construction.c2m θ'
      = (3 / 2) * (Real.cos (2 * θ) - Real.cos (2 * θ')) := by
    rw [Work.Construction.c2m_eq_half, Work.Construction.c2m_eq_half]
    ring
  rw [h2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  calc (3 / 2) * |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ (3 / 2) * (2 * |θ - θ'|) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 3 * |θ - θ'| := by ring

/-! ## §2 The `𝒱`-slot of `Φ̃(τ)` splits over star + perturbation -/

theorem vz7_vop_phiTil_split {α C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop
        (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (slice g τ) (E (slice g τ))) z θ := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  intro z θ hz hθ hθ2
  have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- the pointwise split on the open quadrant
  have hpt : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ z' θ'
        = Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs z' θ'
          + Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z' θ' := by
    intro z' θ' hz' hθ' hθ'2
    exact Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z' θ'
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hθ'2⟩)
  -- the two pieces are smooth enough to add the slots
  have h1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hαG hαG1 hStar).forall 1
  have h2 : ContDiffOn ℝ 1
      (Function.uncurry (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
          (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn (α := α) (C₀ := C₀) hα hα13 hEL3 hOK τ
      hτ).of_le (by norm_num)
  rw [Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hpt z θ hz hθ hθ2,
    Work.FTS_RegExport.RXT.v2_vop_add_at h1 h2 hq]

/-! ## §3 The target -/

theorem vz7_thHol {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, Work.FTS.RegExportIface.ThHol
      (Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
      S (Work.FTS.Regularity.pExp α / 20) := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- the star modulus (A4v)
  obtain ⟨Cv, hCv0, hA4v⟩ :=
    Work.FTS_RegExport.THL.vopStar_theta_holder (αG := Work.FTS.Regularity.pExp α) hαG hαG1 hStar
  -- the abbreviations of the interface
  have hGR : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)
      = Work.FTS.RegExportIface.RXT.GR α g := rfl
  have hΦR : Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)
      = Work.FTS.RegExportIface.RXT.ΦR α Φs E g := rfl
  have hμR : Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g
      = Work.FTS.RegExportIface.RXT.μR α Φs E g := rfl
  intro S hS
  -- the perturbation modulus (A5v) and the `L₁₂`-bound at the horizon `S`
  obtain ⟨Mp, hMp0, hA5v⟩ :=
    Work.FTS_RegExport.THL.vopPert_theta_holder hα hα13 hEll hEL3 hSol hOK S hS
  obtain ⟨CL, hCL0, -, hL12bd, -, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (α := α) (C₀ := C₀) hα hα13 hOK.2 S hS
  -- the Hölder exponent
  set β : ℝ := Work.FTS.Regularity.pExp α / 20 with hβdef
  have hβ : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β ≤ 1 := by rw [hβdef]; linarith
  have h520 : β ≤ Work.FTS.Regularity.pExp α / 5 := by rw [hβdef]; linarith
  intro z₀ hz₀
  refine ⟨CL * (3 * (Real.pi / 2) ^ (1 - β))
      + 2 * Work.FTS.Regularity.pExp α
        * (Cv * (Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) + Mp),
    ?_, 1, one_pos, ?_⟩
  · -- nonnegativity of the constant
    exact add_nonneg
      (mul_nonneg hCL0 (mul_nonneg (by norm_num) (Real.rpow_nonneg hpi.le _)))
      (mul_nonneg (by linarith)
        (add_nonneg (mul_nonneg hCv0 (Real.rpow_nonneg hpi.le _)) hMp0))
  · intro τ hτ z hz _hzd θ hθ θ' hθ'
    have hτ0 : 0 ≤ τ := hτ.1
    rw [hGR, hΦR, hμR]
    -- the angle control
    have hΔ : |θ - θ'| ≤ Real.pi / 2 := by
      rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
    have hrnn : 0 ≤ |θ - θ'| ^ β := Real.rpow_nonneg (abs_nonneg _) β
    -- the `rpow` shifts
    have hshift1 : |θ - θ'| ≤ (Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β := by
      simpa using vz7_rpow_shift_le (d := |θ - θ'|) (β := β) (a := 1) (abs_nonneg _) hΔ hβ hβ1
    have hshift5 : |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 5)
        ≤ (Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β :=
      vz7_rpow_shift_le (abs_nonneg _) hΔ hβ h520
    -- the `c2m` factor
    have hc2m : |Work.Construction.c2m θ - Work.Construction.c2m θ'|
        ≤ 3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β) := by
      calc |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 3 * |θ - θ'| :=
            vz7_abs_c2m_sub_le θ θ'
        _ ≤ 3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β) :=
            mul_le_mul_of_nonneg_left hshift1 (by norm_num)
    -- the split of the `𝒱`-slot at the two angles
    have hsp := vz7_vop_phiTil_split (C₀ := C₀) (Cs := Cs) hα hα13 hEL3 hStar hOK hτ0
      z θ hz hθ.1 hθ.2
    have hsp' := vz7_vop_phiTil_split (C₀ := C₀) (Cs := Cs) hα hα13 hEL3 hStar hOK hτ0
      z θ' hz hθ'.1 hθ'.2
    -- the two halves of the `𝒱`-difference
    have hA := hA4v z hz θ hθ θ' hθ'
    have hB := hA5v τ hτ z hz θ hθ θ' hθ'
    have hstar : |Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
          - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ'|
        ≤ Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β) :=
      hA.trans (mul_le_mul_of_nonneg_left hshift5 hCv0)
    have hpert : |Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (slice g τ) (E (slice g τ))) z θ
          - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (slice g τ) (E (slice g τ))) z θ'| ≤ Mp * |θ - θ'| ^ β := by
      calc _ ≤ Mp * min z 1 * |θ - θ'| ^ β := hB
        _ ≤ Mp * 1 * |θ - θ'| ^ β :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right _ _) hMp0) hrnn
        _ = Mp * |θ - θ'| ^ β := by ring
    have hvop : |Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
          - Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ'|
        ≤ Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β)
          + Mp * |θ - θ'| ^ β := by
      rw [hsp, hsp']
      have heq : (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
            + Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ)
          - (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ'
            + Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ')
          = (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ
            - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs) z θ')
            + (Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ
            - Work.Construction.Vop (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (slice g τ) (E (slice g τ))) z θ') := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add hstar hpert)
    -- the two terms of `Vz7`
    have hL12 := hL12bd τ hτ z hz
    have hterm1 : |Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          * (Work.Construction.c2m θ - Work.Construction.c2m θ')|
        ≤ CL * (3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β)) := by
      rw [abs_mul]
      exact mul_le_mul hL12 hc2m (abs_nonneg _) hCL0
    have hterm2 : |2 * Work.FTS.Regularity.pExp α
          * (Work.Construction.Vop
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
            - Work.Construction.Vop
              (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g)
                (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ')|
        ≤ 2 * Work.FTS.Regularity.pExp α
          * (Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β)
            + Mp * |θ - θ'| ^ β) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Work.FTS.Regularity.pExp α)]
      exact mul_le_mul_of_nonneg_left hvop (by linarith)
    -- assemble
    have hdiff : Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.μR α Φs E g)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
        - Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.μR α Φs E g)
          (Work.FTS.RegExportIface.RXT.GR α g)
          (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ' τ
        = Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            * (Work.Construction.c2m θ - Work.Construction.c2m θ')
          + 2 * Work.FTS.Regularity.pExp α
            * (Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
              - Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ') := by
      simp only [Work.FTS.RegExportIface.Vz7]
      ring
    rw [hdiff]
    calc |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            * (Work.Construction.c2m θ - Work.Construction.c2m θ')
          + 2 * Work.FTS.Regularity.pExp α
            * (Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
              - Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ')|
        ≤ |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
            * (Work.Construction.c2m θ - Work.Construction.c2m θ')|
          + |2 * Work.FTS.Regularity.pExp α
            * (Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
              - Work.Construction.Vop
                (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g)
                  (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ')| := abs_add_le _ _
      _ ≤ CL * (3 * ((Real.pi / 2) ^ (1 - β) * |θ - θ'| ^ β))
          + 2 * Work.FTS.Regularity.pExp α
            * (Cv * ((Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) * |θ - θ'| ^ β)
              + Mp * |θ - θ'| ^ β) := add_le_add hterm1 hterm2
      _ = (CL * (3 * (Real.pi / 2) ^ (1 - β))
            + 2 * Work.FTS.Regularity.pExp α
              * (Cv * (Real.pi / 2) ^ (Work.FTS.Regularity.pExp α / 5 - β) + Mp))
          * |θ - θ'| ^ β := by ring

end Work.FTS_RegExport.THL.L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.cs7_theta_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS_RegExport.THL

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (gS tauExt)
open Work.FTS.RegExportIface (cs7 psiR phiTil)
open Work.FTS.Final (maxMu)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS_RegExport.RXT (v2_PhiT)
open Work.Construction (Rop PhiTil Ftau Fstar FK)
open Work.FTS.VocabO2 (PhiTs)

/-- Power comparison with a shifted weight: for `0 < P`, `0 ≤ t ≤ P` and `0 < p` with `q ≤ p`,
`t ^ p ≤ P ^ (p - q) * t ^ q`. -/
private lemma rpow_le_const_mul_rpow {P t p q : ℝ} (hP : 0 < P) (ht : 0 ≤ t) (htP : t ≤ P)
    (hp : 0 < p) (hpq : 0 ≤ p - q) :
    t ^ p ≤ P ^ (p - q) * t ^ q := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hp)]
    exact mul_nonneg (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg le_rfl q)
  · have hdec : t ^ p = t ^ (p - q) * t ^ q := by
      rw [← Real.rpow_add h, show p - q + q = p by ring]
    rw [hdec]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht htP hpq) (Real.rpow_nonneg ht q)

theorem cs7_theta_holder {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
            (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ τ
          - Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
            (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) z θ' τ|
          ≤ K * |θ - θ'| ^ (Work.FTS.Regularity.pExp α / 20) := by
  intro S hS
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- ### the star slot of `ℛ` (A4) at `αG = pExp α`
  obtain ⟨Csta, hCsta0, hSta⟩ :=
    ropStar_theta_holder (αG := pExp α) (Cs := Cs) hαG hαG1 hStar
  -- ### the perturbation slot of `ℛ` (A5)
  obtain ⟨M, hM0, hPert⟩ :=
    ropPert_theta_holder (α := α) (Ce := Ce) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hSol hOK S hS
  -- ### the uniform bound on the angular moment `𝔽K(F(τ))`
  obtain ⟨CFK, hCFK0, hFK1, -, -, -, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK.2 S hS
  have hFKb : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z| ≤ CFK := by
    intro τ hτ z hz
    simpa only [Work.Spaces.DzIter_zero] using hFK1 τ hτ 0 (by norm_num) z hz
  have hPpos : (0:ℝ) < Real.pi / 2 := by positivity
  refine ⟨2 * (Real.pi / 2) ^ (1 - pExp α / 20) * CFK
      + 2 * Csta * (Real.pi / 2) ^ (3 * (pExp α / 20))
      + 2 * M, ?_, ?_⟩
  · -- ### nonnegativity of the constant
    have h1 : (0:ℝ) ≤ (Real.pi / 2) ^ (1 - pExp α / 20) := Real.rpow_nonneg hPpos.le _
    have h2 : (0:ℝ) ≤ (Real.pi / 2) ^ (3 * (pExp α / 20)) := Real.rpow_nonneg hPpos.le _
    exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) hCFK0)
        (mul_nonneg (mul_nonneg (by norm_num) hCsta0) h2))
      (mul_nonneg (by norm_num) hM0)
  · -- ### the Hölder estimate
    intro τ hτ z hz θ hθ θ' hθ'
    have hε0 : (0:ℝ) ≤ pExp α / 20 := div_nonneg hαG.le (by norm_num)
    have hε1 : pExp α / 20 ≤ 1 := by
      rw [Work.FTS.Regularity.pExp]; linarith
    have hΔ0 : (0:ℝ) ≤ |θ - θ'| := abs_nonneg _
    have hΔP : |θ - θ'| ≤ Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [hθ.1, hθ.2, hθ'.1, hθ'.2]
    have hΔε0 : (0:ℝ) ≤ |θ - θ'| ^ (pExp α / 20) := Real.rpow_nonneg hΔ0 _
    -- ## the two exponent comparisons
    have hconv_sin : |θ - θ'|
        ≤ (Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20) := by
      simpa using rpow_le_const_mul_rpow (P := Real.pi / 2) (t := |θ - θ'|) (p := 1)
        (q := pExp α / 20) hPpos hΔ0 hΔP (by norm_num) (by linarith)
    have hpq : pExp α / 5 - pExp α / 20 = 3 * (pExp α / 20) := by
      rw [Work.FTS.Regularity.pExp]; ring
    have hconv_star : |θ - θ'| ^ (pExp α / 5)
        ≤ (Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20) := by
      have h := rpow_le_const_mul_rpow (P := Real.pi / 2) (t := |θ - θ'|) (p := pExp α / 5)
        (q := pExp α / 20) hPpos hΔ0 hΔP (div_pos hαG (by norm_num)) (by rw [hpq]; positivity)
      rwa [hpq] at h
    -- ## the `sin²` term
    have hsin : |Real.sin θ ^ 2 - Real.sin θ' ^ 2| ≤ 2 * |θ - θ'| := by
      have hs : Real.sin θ ^ 2 - Real.sin θ' ^ 2
          = (Real.sin θ - Real.sin θ') * (Real.sin θ + Real.sin θ') := by ring
      rw [hs, abs_mul]
      have h1 : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := Real.abs_sin_sub_sin_le θ θ'
      have h2 : |Real.sin θ + Real.sin θ'| ≤ 2 := by
        calc |Real.sin θ + Real.sin θ'| ≤ |Real.sin θ| + |Real.sin θ'| := abs_add_le _ _
          _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one θ) (Real.abs_sin_le_one θ')
          _ = 2 := by norm_num
      calc |Real.sin θ - Real.sin θ'| * |Real.sin θ + Real.sin θ'|
          ≤ |θ - θ'| * 2 := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
        _ = 2 * |θ - θ'| := by ring
    have hsin2 : |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
        ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) := by
      calc |Real.sin θ ^ 2 - Real.sin θ' ^ 2| ≤ 2 * |θ - θ'| := hsin
        _ ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) :=
            mul_le_mul_of_nonneg_left hconv_sin (by norm_num)
    -- ## the definitional identity for `cs7` (the `θ`-free terms cancel)
    have hKey : cs7 (pExp α) (maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
          (psiR α Φs E (tauExt g)) z θ τ
        - cs7 (pExp α) (maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
          (psiR α Φs E (tauExt g)) z θ' τ
        = (Real.sin θ ^ 2 - Real.sin θ' ^ 2) * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z
          - 2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                 - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ') := by
      have hφ : ∀ a b : ℝ,
          Rop (pExp α) (phiTil (pExp α) (gS α (tauExt g)) (psiR α Φs E (tauExt g)) τ) a b
            = Rop (pExp α) (v2_PhiT α Φs E g τ) a b := fun a b => rfl
      simp only [cs7]
      simp only [hφ]
      ring
    -- ## the `ℛ`-difference: split into star + perturbation and apply A4/A5
    have hRop : |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
          - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'|
        ≤ Csta * ((Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20))
          + M * |θ - θ'| ^ (pExp α / 20) := by
      have hsub : Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'
          = (Rop (pExp α) (PhiTs (pExp α) Φs) z θ - Rop (pExp α) (PhiTs (pExp α) Φs) z θ')
            + (Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
               - Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ') := by
        rw [cs7_rop_split hα hα13 hEL3 hStar hOK τ hτ.1 z θ hz hθ.1 hθ.2,
          cs7_rop_split hα hα13 hEL3 hStar hOK τ hτ.1 z θ' hz hθ'.1 hθ'.2]
        ring
      have htri : |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'|
          ≤ |Rop (pExp α) (PhiTs (pExp α) Φs) z θ - Rop (pExp α) (PhiTs (pExp α) Φs) z θ'|
            + |Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
               - Rop (pExp α) (PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ'| := by
        rw [hsub]
        exact abs_add_le _ _
      refine le_trans htri (add_le_add ?_ ?_)
      · exact le_trans (hSta z hz θ hθ θ' hθ') (mul_le_mul_of_nonneg_left hconv_star hCsta0)
      · refine le_trans (hPert τ hτ z hz θ hθ θ' hθ') ?_
        have hstep : M * min z 1 * |θ - θ'| ^ (pExp α / 20)
            ≤ M * |θ - θ'| ^ (pExp α / 20) := by
          have h1 : M * min z 1 ≤ M * 1 := mul_le_mul_of_nonneg_left (min_le_right z 1) hM0
          rw [mul_one] at h1
          exact mul_le_mul_of_nonneg_right h1 hΔε0
        exact hstep
    -- ## the two summands of the difference
    have hFKterm : |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
          * |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z|
        ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) * CFK :=
      mul_le_mul hsin2 (hFKb τ hτ z hz) (abs_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hPpos.le _) hΔε0))
    have h2term : 2 * |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
          - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'|
        ≤ 2 * (Csta * ((Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20))
          + M * |θ - θ'| ^ (pExp α / 20)) :=
      mul_le_mul_of_nonneg_left hRop (by norm_num)
    -- ## the triangle inequality and the final normalisation
    have hcomb : |(Real.sin θ ^ 2 - Real.sin θ' ^ 2)
            * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z
          - 2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                 - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')|
        ≤ 2 * ((Real.pi / 2) ^ (1 - pExp α / 20) * |θ - θ'| ^ (pExp α / 20)) * CFK
          + 2 * (Csta * ((Real.pi / 2) ^ (3 * (pExp α / 20)) * |θ - θ'| ^ (pExp α / 20))
              + M * |θ - θ'| ^ (pExp α / 20)) := by
      have h1 : |(Real.sin θ ^ 2 - Real.sin θ' ^ 2)
            * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z|
          = |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
            * |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z| := abs_mul _ _
      have h2 : |(2:ℝ) * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')|
          = 2 * |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
            - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'| := by
        rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]
      have htri : |(Real.sin θ ^ 2 - Real.sin θ' ^ 2)
              * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z
            - 2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                   - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')|
          ≤ |Real.sin θ ^ 2 - Real.sin θ' ^ 2|
              * |FK (Ftau (pExp α) (gS α (tauExt g)) τ) z|
            + 2 * |Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
                   - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'| := by
        rw [abs_sub_le_iff]
        constructor <;>
          linarith [h1, h2,
            le_abs_self ((Real.sin θ ^ 2 - Real.sin θ' ^ 2)
              * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z),
            neg_abs_le ((Real.sin θ ^ 2 - Real.sin θ' ^ 2)
              * FK (Ftau (pExp α) (gS α (tauExt g)) τ) z),
            le_abs_self (2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
              - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ')),
            neg_abs_le (2 * (Rop (pExp α) (v2_PhiT α Φs E g τ) z θ
              - Rop (pExp α) (v2_PhiT α Φs E g τ) z θ'))]
      exact le_trans htri (add_le_add hFKterm h2term)
    rw [hKey]
    refine le_trans hcomb (le_of_eq ?_)
    ring

end Work.FTS_RegExport.THL
end
end

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_E_of_EllLimOK3
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.morrey_five_slots
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsHlim4
import Submission.Work.FTS.StrongEps.EpsLocalPStar.StatResidual
import Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.ExistsLimG_of_horizon_pkgs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The glue of the per-horizon packages

The hypotheses of `ExistsLimG_of_horizon_pkgs` provide, for every horizon `Tn N`, a limit package
for the *clamped* limit curve `clampQ (F N) g₀` of that horizon, and the coherence `hcoh` of the
curves `F N` on the overlaps of the horizons.  This file builds the single global family

  `g := clampQ (fun τ => F (ι τ) τ) g₀`  (`ι τ` a horizon index covering `τ`),

and shows that on every horizon `[0,T]` it agrees with the curve of any covering piece; then every
clause of `EpsLimPkg` transports, because `EpsLimPkg` only ever looks at the family on `[0,T]`
(the `dbd`-clause looks at the honest `τ`-derivative, which is a local notion, so agreement on
`[0,T]` at an *interior* time `τ ∈ (0,T)` already suffices). -/

/-- **`gdot` only sees the family near the evaluation time.**  If two families agree on the closed
interval `[0,T]` and `τ` is an interior point of it, then their `τ`-derivatives at `τ` agree. -/
theorem gdot_eq_of_agreeOn_Icc {g g' : Fam} {T τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) T)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z θ, g z θ s = g' z θ s) :
    Work.FTS.Galerkin.gdot g τ = Work.FTS.Galerkin.gdot g' τ := by
  funext z θ
  exact Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (Icc_mem_nhds hτ.1 hτ.2) (fun s hs => h s hs z θ))

/-- **The clamped curves of the covering pieces agree on the horizon.**  Let `ι` be any map from
times to horizon indices with `τ ≤ Ts (ι τ)`, `N` a piece covering `[0,T]` (`T ≤ Ts N`), and `Fs`
a family of curves coherent on the overlaps of the horizons (the hypothesis `hcoh` of
`ExistsLimG_of_horizon_pkgs`).  Then on `[0,T]` the clamped curve of the *selected* horizon `ι s`
coincides with the clamped curve of the piece `N`. -/
theorem clampQ_horizon_agree {Fs : ℕ → ℝ → Fn} {g₀ : Fn} {Ts : ℕ → ℝ} {ι : ℝ → ℕ} {T : ℝ}
    {N : ℕ} (hι : ∀ τ : ℝ, τ ≤ Ts (ι τ)) (hTN : T ≤ Ts N)
    (hcoh : ∀ m n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) (min (Ts m) (Ts n)), ∀ z θ,
      (z, θ) ∈ Work.Construction.Qd → Fs m τ z θ = Fs n τ z θ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z θ,
      clampQ (fun τ => Fs (ι τ) τ) g₀ z θ s = clampQ (Fs N) g₀ z θ s := by
  intro s hs z θ
  by_cases hzb : z ∈ Set.Ioi (0 : ℝ)
  · by_cases hθb : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · rw [clampQ_of_mem (F := fun τ => Fs (ι τ) τ) hzb hθb,
        clampQ_of_mem (F := Fs N) hzb hθb]
      exact hcoh (ι s) N s ⟨hs.1, le_min (hι s) (le_trans hs.2 hTN)⟩ z θ ⟨hzb, hθb⟩
    · rw [clampQ_of_not_mem_θ (F := fun τ => Fs (ι τ) τ) hzb hθb,
        clampQ_of_not_mem_θ (F := Fs N) hzb hθb]
  · rw [clampQ_of_not_mem_z (F := fun τ => Fs (ι τ) τ) hzb,
      clampQ_of_not_mem_z (F := Fs N) hzb]

/-- **The limit package is a property of the family on `[0,T]`.**  If two families have the same
slices at every `τ ∈ [0,T]`, then one carries `EpsLimPkg` on `[0,T]` iff the other does.

Every clause of `EpsLimPkg` is a statement about the slices `slice g τ`, `τ ∈ [0,T]`
(`init`/`law`/`eqT`/`c4`/`mem4`/`bd4`/`vanish`/`limApprox` read the slice at a single `τ`, `c1` and
`cont` read a whole interval of them), except `dbd`, which reads the honest `τ`-derivative
`gdot g τ` at `τ ∈ (0,T)`; there the equality of the *functions* on `[0,T]` is a neighbourhood
property of the interior point `τ`, hence the derivatives agree (`gdot_eq_of_agreeOn_Icc`). -/
theorem EpsLimPkg_congr_of_slice_eqOn {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g g' : Fam} (hT : 0 < T)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) T, slice g τ = slice g' τ)
    (hp : EpsLimPkg α C₀ K Cd T Φs E g₀ g) :
    EpsLimPkg α C₀ K Cd T Φs E g₀ g' := by
  have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z θ, g z θ τ = g' z θ τ :=
    fun τ hτ z θ => congrFun (congrFun (h τ hτ) z) θ
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  refine
    { init := fun z θ => (hpt 0 hzero z θ).symm.trans (hp.init z θ)
      law := fun τ h1 h2 => ?_
      eqT := fun τ h1 h2 z θ hzθ => ?_
      c1 := hp.c1.congr (fun p hp' => ?_)
      c4 := fun τ h1 h2 => by
        simpa only [← h τ ⟨h1, h2⟩] using hp.c4 τ h1 h2
      cont := fun z θ hzθ => (hp.cont z θ hzθ).congr (fun τ hτ => (hpt τ hτ z θ).symm)
      mem4 := fun τ h1 h2 => by
        simpa only [← h τ ⟨h1, h2⟩] using hp.mem4 τ h1 h2
      bd4 := fun τ h1 h2 => by
        simpa only [← h τ ⟨h1, h2⟩] using hp.bd4 τ h1 h2
      bd6 := by
        obtain ⟨B, hB⟩ := hp.bd6
        exact ⟨B, fun τ h1 h2 => by
          simpa only [← h τ ⟨h1, h2⟩] using hB τ h1 h2⟩
      vanish := fun τ h1 h2 z hz => ?_
      dbd := fun τ h1 h2 => ?_
      limApprox := fun T' h1 h2 => ?_ }
  · -- `law`
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨h1, h2⟩
    rw [← Work.FTS.StrongGlobal.Ftau_congr (h τ hτ),
      ← Work.FTS.StrongGlobal.slice_PsiCan_congr (h τ hτ)]
    exact hp.law τ h1 h2
  · -- `eqT`
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨h1, h2⟩
    have hfun : ∀ s ∈ Set.Icc (0 : ℝ) T, g' z θ s = g z θ s :=
      fun s hs => (hpt s hs z θ).symm
    have hg := (hp.eqT τ h1 h2 z θ hzθ).congr hfun (hfun τ hτ)
    rwa [rhsFun_congr (h τ hτ)] at hg
  · -- `c1`
    exact (hpt p.2.2 ⟨le_of_lt hp'.2.2.1, le_of_lt hp'.2.2.2⟩ p.1 p.2.1).symm
  · -- `vanish`
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨h1, h2⟩
    obtain ⟨h0, h1'⟩ := hp.vanish τ h1 h2 z hz
    exact ⟨by rwa [hpt τ hτ z 0] at h0, by rwa [hpt τ hτ z (π / 2)] at h1'⟩
  · -- `dbd`
    have hgd : Work.FTS.Galerkin.gdot g' τ = Work.FTS.Galerkin.gdot g τ :=
      gdot_eq_of_agreeOn_Icc (g := g') (g' := g) ⟨h1, h2⟩
        (fun s hs z θ => (hpt s hs z θ).symm)
    rw [hgd]
    exact hp.dbd τ h1 h2
  · -- `limApprox`
    obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := hp.limApprox T' h1 h2
    refine ⟨gn, B, L, hb, hlip, ?_, ?_⟩
    · intro τ hτ j i hji z θ hzθ
      have hτ' : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, le_trans hτ.2 h2⟩
      simpa only [h τ hτ'] using hjet τ hτ j i hji z θ hzθ
    · intro τ hτ
      have hτ' : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, le_trans hτ.2 h2⟩
      simpa only [Work.FTS.StrongGlobal.muDyn_congr (h τ hτ')] using hmu τ hτ

/-- **E5 (new form) from the per-horizon packages.**  From a monotone covering family of horizons
`Tn` and, at every horizon, a limit package for the clamped limit curve of that horizon — the
curves being coherent on the overlaps — one gets a *single* global family carrying the package on
every horizon.

The family is `clampQ (fun τ => F (ι τ) τ) g₀` where `ι τ` is a horizon covering `τ` (chosen from
`hcov` at `|τ| + 1`, so that it is defined for every real `τ`); on every horizon `[0,T]` it
coincides with the piece covering `T`, by coherence (`clampQ_horizon_agree`), and the package
transports (`EpsLimPkg_congr_of_slice_eqOn`). -/
theorem ExistsLimG_of_horizon_pkgs {α C₀ K : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {Tn : ℕ → ℝ} {F : ℕ → ℝ → Work.FTS.Galerkin.Fn}
    (hTn : ∀ N : ℕ, 0 < Tn N) (hmono : Monotone Tn)
    (hcov : ∀ T : ℝ, 0 < T → ∃ N : ℕ, T ≤ Tn N)
    (hcoh : ∀ m n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) (min (Tn m) (Tn n)), ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd → F m τ z θ = F n τ z θ)
    (hpkg : ∀ N : ℕ, ∀ T : ℝ, 0 < T → T ≤ Tn N →
      ∃ Cd : ℝ, 0 < Cd ∧
        Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd T Φs E g₀ (Work.FTS.StrongEps.clampQ (F N) g₀)) :
    ∃ g : Work.FTS.Galerkin.Fam, ∀ T : ℝ, 0 < T → ∃ Cd : ℝ, 0 < Cd ∧
      Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd T Φs E g₀ g := by
  classical
  -- a horizon index covering every time: chosen at `|τ| + 1`, so that it is defined (and the
  -- covering property holds) for *every* real `τ`, not only for `τ ≥ 0`.
  have hpos : ∀ τ : ℝ, 0 < |τ| + 1 := fun τ => by have := abs_nonneg τ; linarith
  let ι : ℝ → ℕ := fun τ => Classical.choose (hcov (|τ| + 1) (hpos τ))
  have hι : ∀ τ : ℝ, τ ≤ Tn (ι τ) := fun τ =>
    le_trans (by have := le_abs_self τ; linarith)
      (Classical.choose_spec (hcov (|τ| + 1) (hpos τ)))
  refine ⟨Work.FTS.StrongEps.clampQ (fun τ => F (ι τ) τ) g₀, fun T hT => ?_⟩
  obtain ⟨N, hTN⟩ := hcov T hT
  obtain ⟨Cd, hCd, hpk⟩ := hpkg N (Tn N) (hTn N) le_rfl
  refine ⟨Cd, hCd, ?_⟩
  have hpkT : Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd T Φs E g₀
      (Work.FTS.StrongEps.clampQ (F N) g₀) :=
    Work.FTS.StrongEps.EpsLimPkg.mono hTN hpk hT.le
  refine EpsLimPkg_congr_of_slice_eqOn hT (fun s hs => ?_) hpkT
  funext z θ
  simpa only [Work.FTS.Galerkin.slice_apply] using
    (clampQ_horizon_agree (Fs := F) (Ts := Tn) (ι := ι) (N := N) hι hTN hcoh s hs z θ).symm

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.PkgOfHlim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.EllipticEst (Q0 SmoothOpen smoothOpen_iff_forall)
open Work.FTS.Nonlin (Xn)
open Work.FTS.StrongGlobal (Xn6 IsBslSolPos)
open Work.FTS.ClassC (ClassC)
open Work.FTS.VocabO (EllPkgGo)
open Work.FTS.VocabO2 (StarPkgo2)
open Work.Spaces (mixed HkMem HkNorm HkIntegrand Iz Iθ)
open Work.Construction (Qd Ftau)
open Work.FTS.StrongEps (clampQ epsRHSP rhsFun EpsLimPkg ConvLocUnifH6 LimApproxOn
  EllLimOK3 MuLamOK IsEpsSolP IsSmoothKernel Jeps JfamP EpsRegP)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The per-horizon E5 assembly, with the Gap-2 supply clause.**  This is the statement of
`EpsLimPkg_of_horizon` plus the one hypothesis its `eqT` row needs and the other hypotheses do not
determine (`hlim`, the pointwise identification `epsRHSP → rhsFun`; see the module header). -/
theorem EpsLimPkg_of_horizon_of_hlim {α C₀ K Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam} {K' : ℕ → ℝ} {ι : ℕ → ℕ → ℕ}
    {F : ℕ → ℝ → Work.FTS.Galerkin.Fn}
    (n : ℕ) (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, ClassC α u → EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hELL3 : EllLimOK3 α E)
    (hvan : ∀ z : ℝ, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hL12g₀ : Work.Construction.L12 g₀ 0 = 0)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc 0 1)
    (hε0 : Filter.Tendsto e Filter.atTop (nhds 0))
    (hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (hι : StrictMono (ι n)) (hadm : ∀ k : ℕ, n ≤ ι n k)
    (hconv : ∀ τ ∈ Set.Icc 0 (Tn n),
      ConvLocUnifH6 α (K' n) (fun k => slice (G n (ι n k)) τ) (F n τ))
    (hT : 0 < T) (hTT : T ≤ Tn n)
    (hcontR : ∀ z θ : ℝ, (z, θ) ∈ Qd →
      ContinuousOn (fun s : ℝ => rhsFun α Φs E (clampQ (F n) g₀) s z θ) (Set.Icc 0 T))
    (hWc : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        rhsFun α Φs E (clampQ (F n) g₀) p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hdbd : ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ : ℝ, 0 < τ → τ < T →
      HkMem α 3 (gdot (clampQ (F n) g₀) τ) ∧ HkNorm α 3 (gdot (clampQ (F n) g₀) τ) ≤ Cd)
    (hapx : ∀ T' : ℝ, 0 < T' → T' ≤ T → LimApproxOn α C₀ T' Φs E (clampQ (F n) g₀))
    (hlim : ∀ p : ℝ × ℝ, p ∈ Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun k : ℕ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
        Filter.atTop (nhds (rhsFun α Φs E (clampQ (F n) g₀) s p.1 p.2))) :
    ∃ Cd' : ℝ, 0 < Cd' ∧ EpsLimPkg α C₀ K Cd' T Φs E g₀ (clampQ (F n) g₀) := by
  classical
  have hTn : 0 < Tn n := Tn_pos n
  -- ## the tower instances along the extraction
  have htw : ∀ k : ℕ, TowerAt α C₀ ρ Φs E g₀ n (e (ι n k)) (K' n) (G n (ι n k)) :=
    fun k => hTower n (ι n k) (hadm k)
  have hεI : ∀ k : ℕ, e (ι n k) ∈ Set.Ioc 0 1 := fun k => hεe (ι n k)
  have hεp : ∀ k : ℕ, 0 < e (ι n k) := fun k => (hεI k).1
  have hε0' : Filter.Tendsto (fun k : ℕ => e (ι n k)) Filter.atTop (nhds 0) :=
    hε0.comp (hι.tendsto_atTop)
  have hK'0 : 0 ≤ K' n := le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (G n n) 0))
    ((hTower n n le_rfl).hb6 0 ⟨le_rfl, hTn.le⟩)
  have hsmK : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n), ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (slice (G n (ι n k)) σ)) Work.FTS.StrongEps.Quad :=
    fun k σ hσ m => (smoothOpen_iff_forall _).mp ((htw k).hsm σ hσ) m
  have hmem6 : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n), HkMem α 6 (slice (G n (ι n k)) σ) :=
    fun k σ hσ => (htw k).hmem6 σ hσ
  have hb6K : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n), Xn6 α (slice (G n (ι n k)) σ) ≤ K' n :=
    fun k σ hσ => (htw k).hb6 σ hσ
  have hCq : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      ClassC α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) := fun k σ hσ => (htw k).hC σ hσ
  have hb4q : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Xn α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) ≤ C₀ * α ^ 2 :=
    fun k σ hσ => (htw k).hb4 σ hσ
  have hmem4q : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      HkMem α 4 (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) :=
    fun k σ hσ => (htw k).hmem4p σ hσ
  -- ## the projected `ℋ⁶`-bound, at the enlarged elliptic constant
  obtain ⟨A, hA0, hA⟩ := Work.FTS.StrongEps.HkNorm_JfamP_le (ρ := ρ) hρ
  have hEll' : ∀ u : Fn, ClassC α u →
      EllPkgGo α (max Ce (A * K' n)) u (E u) ∧
        Work.FTS.ClassC.EllPkgK α 6 (max Ce (A * K' n)) u (E u) :=
    fun u hu => ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1 (le_max_left _ _),
      Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2 (le_max_left _ _)⟩
  have hb6p : ∀ k : ℕ, ∀ σ ∈ Set.Icc (0 : ℝ) (Tn n),
      Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) σ) ≤ max Ce (A * K' n) := by
    intro k σ hσ
    have h1 := hA (α := α) (ε := e (ι n k)) hα (hεI k) (g := G n (ι n k)) (s := σ)
      (fun m => hsmK k σ hσ m) (hmem6 k σ hσ)
    exact le_trans (le_trans h1.2 (mul_le_mul_of_nonneg_left (hb6K k σ hσ) hA0))
      (le_max_right _ _)
  -- ## the convergence package to the clamped limit
  have hconvC : ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      ConvLocUnifH6 α (K' n) (fun k => slice (G n (ι n k)) τ)
        (slice (clampQ (F n) g₀) τ) :=
    fun τ hτ => Work.FTS.StrongEps.E5Asm.ConvLocUnifH6.clampQ_congr (hconv τ hτ)
  have hconv0 : ∀ p : ℝ × ℝ, p ∈ Q0 → ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun k : ℕ => G n (ι n k) p.1 p.2 σ) Filter.atTop
        (nhds (clampQ (F n) g₀ p.1 p.2 σ)) :=
    fun p hp σ hσ => ConvLocUnifH6.conv_pt (hconvC σ ⟨hσ.1, le_trans hσ.2 hTT⟩) hp
  -- ## horizon-`T` restrictions
  have hsmKT : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ, ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (slice (G n (ι n k)) τ)) Work.FTS.StrongEps.Quad :=
    fun τ hτ k m => hsmK k τ ⟨hτ.1, le_trans hτ.2 hTT⟩ m
  have hmem6T : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ, HkMem α 6 (slice (G n (ι n k)) τ) :=
    fun τ hτ k => hmem6 k τ ⟨hτ.1, le_trans hτ.2 hTT⟩
  have hb6KT : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ, Xn6 α (slice (G n (ι n k)) τ) ≤ K' n :=
    fun τ hτ k => hb6K k τ ⟨hτ.1, le_trans hτ.2 hTT⟩
  have hCqT : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ClassC α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) :=
    fun τ hτ k => hCq k τ ⟨hτ.1, le_trans hτ.2 hTT⟩
  have hb4qT : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      Xn α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) ≤ C₀ * α ^ 2 :=
    fun τ hτ k => hb4q k τ ⟨hτ.1, le_trans hτ.2 hTT⟩
  have hmem4qT : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      HkMem α 4 (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) :=
    fun τ hτ k => hmem4q k τ ⟨hτ.1, le_trans hτ.2 hTT⟩
  have hb6pT : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) ≤ max Ce (A * K' n) :=
    fun τ hτ k => hb6p k τ ⟨hτ.1, le_trans hτ.2 hTT⟩
  -- ## `init`, `vanish`, `c4`, `bd6`
  have h_init : ∀ z θ : ℝ, clampQ (F n) g₀ z θ 0 = g₀ z θ :=
    E5_init (T := Tn n) (B := K' n) (G := fun k => G n (ι n k)) (φ := id) (F := F n)
      (fun k => (htw k).hsol) (hconv 0 ⟨le_rfl, hTn.le⟩)
  have h_vanish : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → ∀ z : ℝ, 0 ≤ z →
      clampQ (F n) g₀ z 0 τ = 0 ∧ clampQ (F n) g₀ z (π / 2) τ = 0 :=
    fun _ _ _ z hz => E5_vanish (F := F n) (g₀ := g₀) hvan _ z hz
  have h_c4 : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T →
      ContDiffOn ℝ 4 (Function.uncurry (slice (clampQ (F n) g₀) τ)) Q0 :=
    fun τ hτ0 hτT => E5_c4 (B := K' n) (G := fun k => G n (ι n k)) (φ := id) (F := F n)
      (fun σ hσ => hconv σ ⟨hσ.1, le_trans hσ.2 hTT⟩) τ ⟨hτ0, hτT⟩
  have h_bd6 : ∃ B' : ℝ, ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → Xn6 α (slice (clampQ (F n) g₀) τ) ≤ B' := by
    obtain ⟨B', hB'⟩ := E5_bd6 (B := K' n) (G := fun k => G n (ι n k)) (φ := id) (F := F n)
      (fun τ hτ => (hconv τ ⟨hτ.1, le_trans hτ.2 hTT⟩).toLev0)
    exact ⟨B', fun τ h1 h2 => hB' τ ⟨h1, h2⟩⟩
  -- ## `cont`
  have hcont_n : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
        (Set.Icc 0 (Tn n)) :=
    fun k p hp => Work.FTS.StrongEps.continuousOn_epsRHSP_of_regP hTn (htw k).hsol
      (htw k).toEpsRegP p hp
  have hbdd_n : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Q0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) (Tn n), ∀ p ∈ K,
        |epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2| ≤ C :=
    fun K hK hKQ => hbdd_of_mem_compact (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n))
      (Cs := Cs) (T := Tn n) (ρ := ρ) (Φs := Φs) (E := E)
      (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k)) hα hρ hεI hTn.le
      hc₁ hc₂ hEll' hstar hml hCq hb4q hb6p hK hKQ
  have hlip0 : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ p ∈ K,
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
        |slice (G n (ι n k)) τ p.1 p.2 - slice (G n (ι n k)) τ' p.1 p.2| ≤ C * |τ - τ'| := by
    intro K hK hKQ
    obtain ⟨C, hC0, hC⟩ := Work.FTS.StrongEps.EpsProfileLip (T := Tn n) (ρ := ρ) (Φs := Φs)
      (E := E) (g₀ := g₀) (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k))
      (fun k => (htw k).hsol) hcont_n hbdd_n K hK hKQ
    exact ⟨C, hC0, fun k p hp τ hτ τ' hτ' =>
      hC k p hp τ ⟨hτ.1, le_trans hτ.2 hTT⟩ τ' ⟨hτ'.1, le_trans hτ'.2 hTT⟩⟩
  have h_cont : ∀ z θ : ℝ, (z, θ) ∈ Qd → ContinuousOn (fun τ : ℝ => clampQ (F n) g₀ z θ τ)
      (Set.Icc 0 T) :=
    E5_cont (B := K' n) (G := fun k => G n (ι n k)) (F := F n)
      (fun τ hτ => (hconv τ ⟨hτ.1, le_trans hτ.2 hTT⟩).toLev0) hlip0
  -- ## `bd4`, `mem4`: the mollified and projected families
  have hJ : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Q0 →
      ∀ j i : ℕ, j + i ≤ 4 →
      TendstoUniformlyOn (fun k : ℕ => fun p : ℝ × ℝ =>
          mixed j i (Jeps ρ (e (ι n k)) (slice (G n (ι n k)) τ)) p.1 p.2)
        (fun p : ℝ × ℝ => mixed j i (F n τ) p.1 p.2) Filter.atTop K :=
    fun τ hτ K hK hKQ j i hji => Work.FTS.StrongEps.E5Aux.mixed_Jeps_tendstoUniformlyOn
      (ρ := ρ) hρ.moll (fun k => hsmK k τ ⟨hτ.1, le_trans hτ.2 hTT⟩)
      (hconv τ ⟨hτ.1, le_trans hτ.2 hTT⟩) hεp hε0' hK hKQ hji
  have hl12T : ∀ τ ∈ Set.Icc (0 : ℝ) T, Filter.Tendsto (fun k : ℕ =>
      Work.Construction.L12 (Jeps ρ (e (ι n k)) (slice (G n (ι n k)) τ)) 0) Filter.atTop
        (nhds 0) :=
    -- the unmollified zero mode is conserved along each `ε`-solution (the C2 leaf
    -- `L12_slice_eq_zero_of_hkMem`) and the mollifier error is `O(ε k)`
    -- (`L12_Jeps_slice_tendsto_of_zero`); gathered in `E5G.HL12RawTower`
    fun τ hτ => HL12RawTower (α := α) (C₀ := C₀) (Ce := max Ce (A * K' n)) (Cs := Cs)
      (T := Tn n) (B := K' n) hα hρ hc₁ hc₂ hEll' hstar hml hεI hε0' hTn hL12g₀
      (fun k => (htw k).hsol) (fun k => (htw k).hjoint) (fun k σ hσ => (htw k).hsm σ hσ)
      hmem6 hb6K hCq hb4q hb6p ⟨hτ.1, le_trans hτ.2 hTT⟩
  have h_bd4 : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → Xn α (slice (clampQ (F n) g₀) τ) ≤ C₀ * α ^ 2 :=
    fun τ h1 h2 => E5_bd4_JfamP (B := K' n) (C₀ := C₀) (T := T) (ρ := ρ) (g₀ := g₀)
      (G := fun k => G n (ι n k)) (φ := id) (ε := fun k => e (ι n k)) (F := F n) hρ hsmKT
      (fun σ hσ => hconv σ ⟨hσ.1, le_trans hσ.2 hTT⟩) hεp hJ hl12T hmem4qT hb4qT τ ⟨h1, h2⟩
  have hsmJ : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ, ∀ m : ℕ,
      ContDiffOn ℝ m (Function.uncurry (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ)) Q0 :=
    fun τ hτ k m => (hCqT τ hτ k).reg.forall m
  have hmem6P : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      HkMem α 6 (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) :=
    fun τ hτ k => Work.FTS.OpenPkg.HkMem_mono_open (hCqT τ hτ k).reg 6 (by norm_num)
      (hCqT τ hτ k).mem
  have hz : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z ∈ Iz, ∃ Bz : ℝ, ∀ k : ℕ,
      (∫ θ in Iθ, HkIntegrand α 4 (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) z θ) ≤ Bz :=
    fun τ hτ z hz' => Work.FTS.StrongEps.hz_of_classC_JfamP (α := α) (B := K' n) (ρ := ρ)
      (G := fun k => G n (ι n k)) (ε := fun k => e (ι n k)) (τ := τ) hα hρ hK'0 hεI
      (fun k m => hsmK k τ ⟨hτ.1, le_trans hτ.2 hTT⟩ m)
      (fun k => hmem6 k τ ⟨hτ.1, le_trans hτ.2 hTT⟩)
      (fun k => hb6K k τ ⟨hτ.1, le_trans hτ.2 hTT⟩)
      (fun k => hCq k τ ⟨hτ.1, le_trans hτ.2 hTT⟩) z hz'
  -- the constant dominating both the limit's `ℋ⁶`-size and the projected one
  have hconvB : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLocUnifH6 α (max (K' n) (max Ce (A * K' n))) (fun k => slice (G n (ι n k)) τ) (F n τ) :=
    fun τ hτ => ⟨(hconv τ ⟨hτ.1, le_trans hτ.2 hTT⟩).conv,
      (hconv τ ⟨hτ.1, le_trans hτ.2 hTT⟩).contDiffOn,
      le_trans (hconv τ ⟨hτ.1, le_trans hτ.2 hTT⟩).hkNorm_le (le_max_left _ _)⟩
  have hconvCB : ∀ τ ∈ Set.Icc (0 : ℝ) T, ConvLocUnifH6 α (max (K' n) (max Ce (A * K' n)))
      (fun k => slice (G n (ι n k)) τ) (slice (clampQ (F n) g₀) τ) :=
    fun τ hτ => Work.FTS.StrongEps.E5Asm.ConvLocUnifH6.clampQ_congr (hconvB τ hτ)
  have hb6pT2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      Xn6 α (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) ≤ max (K' n) (max Ce (A * K' n)) :=
    fun τ hτ k => le_trans (hb6pT τ hτ k) (le_max_right _ _)
  have h_mem4 : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → HkMem α 4 (slice (clampQ (F n) g₀) τ) :=
    fun τ hτ0 hτT => (E5_mem4_JfamP (B := max (K' n) (max Ce (A * K' n))) (T := T) (ρ := ρ)
      (g₀ := g₀) (G := fun k => G n (ι n k)) (φ := id) (ε := fun k => e (ι n k)) (F := F n)
      hρ hsmKT hconvB hεp hJ hl12T hsmJ hmem6P hb6pT2 hz τ ⟨hτ0, hτT⟩).1
  -- ## `law`
  have hslot : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Qd →
      Filter.Tendsto (fun k : ℕ =>
          mixed j i (slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ) z θ) Filter.atTop
        (nhds (mixed j i (slice (clampQ (F n) g₀) τ) z θ)) :=
    fun τ hτ j i hji z θ hzθ => Work.FTS.StrongEps.mixed_JfamP_tendsto (ρ := ρ)
      (g := clampQ (F n) g₀) (G := fun k => G n (ι n k)) hρ
      (fun k m => hsmK k τ ⟨hτ.1, le_trans hτ.2 hTT⟩ m)
      (hconvC τ ⟨hτ.1, le_trans hτ.2 hTT⟩) hεp hε0' (hl12T τ hτ) hzθ hji
  have h_law : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T →
      IsBslSolPos α (Ftau α (clampQ (F n) g₀) τ)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (clampQ (F n) g₀)) τ) := by
    intro τ hτ0 hτT
    have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ0, hτT⟩
    have hB0 : 0 ≤ max Ce (A * K' n) :=
      le_trans (Work.Spaces.HkNorm_nonneg α 6 (slice (JfamP ρ (e (ι n 0)) (G n (ι n 0))) 0))
        (hb6p 0 0 ⟨le_rfl, hTn.le⟩)
    refine Work.FTS.StrongEps.E5Law (α := α) (Cs := Cs) (B := max Ce (A * K' n)) (τ := τ)
      (g := clampQ (F n) g₀) (fn := fun k => slice (JfamP ρ (e (ι n k)) (G n (ι n k))) τ)
      (f := slice (clampQ (F n) g₀) τ) hstar (EllLimOK3.toEllLimOK hELL3)
      (fun k => hCqT τ hτ k) (fun k => hb6pT τ hτ k)
      ((hconvC τ ⟨hτ0, le_trans hτT hTT⟩).contDiffOn)
      (fun j i hji z θ hzθ => hslot τ hτ j i hji z θ hzθ) ?_ rfl
    exact Work.FTS.StrongEps.contDiffOn_two_E_of_EllLimOK3 hELL3 (fun k => hCqT τ hτ k)
      (fun k => hb6pT τ hτ k) (hconvC τ ⟨hτ0, le_trans hτT hTT⟩).contDiffOn
      (fun j i hji z θ hzθ => hslot τ hτ j i hji z θ hzθ)
  -- ## `eqT`
  have h_eqT : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → ∀ z θ : ℝ, (z, θ) ∈ Qd →
      HasDerivWithinAt (fun s : ℝ => clampQ (F n) g₀ z θ s)
        (rhsFun α Φs E (clampQ (F n) g₀) τ z θ) (Set.Icc 0 T) τ := by
    intro τ hτ0 hτT z θ hzθ
    have hcontT : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Q0 →
        ContinuousOn (fun s : ℝ => epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2)
          (Set.Icc 0 T) :=
      fun k p hp => (hcont_n k p hp).mono (Set.Icc_subset_Icc le_rfl hTT)
    have hbddT : ∀ p : ℝ × ℝ, p ∈ Q0 → ∃ C : ℝ, ∀ k : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
        |epsRHSP α ρ (e (ι n k)) Φs E (G n (ι n k)) s p.1 p.2| ≤ C := by
      intro p hp
      have hKQ : ({p} : Set (ℝ × ℝ)) ⊆ Q0 := by
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact hp
      obtain ⟨C, _hC0, hC⟩ := hbdd_n {p} isCompact_singleton hKQ
      exact ⟨C, fun k s hs => hC k s ⟨hs.1, le_trans hs.2 hTT⟩ p (Set.mem_singleton p)⟩
    exact Work.FTS.StrongEps.EpsLimVolterraP (α := α) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (g₀ := g₀) (ε := fun k => e (ι n k)) (G := fun k => G n (ι n k))
      (g := clampQ (F n) g₀) hT (fun k => IsEpsSolP_mono (htw k).hsol hTT) hcontT hlim hbddT
      hconv0 (fun p hp => hcontR p.1 p.2 hp) (z, θ) hzθ τ ⟨hτ0, hτT⟩
  -- ## `c1`
  have h_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => clampQ (F n) g₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T) := by
    obtain ⟨Bd, hBd⟩ := h_bd6
    have hW : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ p : ℝ × ℝ, p ∈ Qd →
        HasDerivWithinAt (fun s : ℝ => clampQ (F n) g₀ p.1 p.2 s)
          (rhsFun α Φs E (clampQ (F n) g₀) τ p.1 p.2) (Set.Icc 0 T) τ :=
      fun τ hτ p hp => h_eqT τ hτ.1 hτ.2 p.1 p.2 hp
    have hWc' : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        rhsFun α Φs E (clampQ (F n) g₀) p.2.2 p.1 p.2.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T) :=
      hWc.mono (Set.prod_mono Subset.rfl (Set.prod_mono Subset.rfl Set.Ioo_subset_Icc_self))
    refine Work.FTS.StrongEps.E5Aux.c1_of_locUnif_slots_lip
      (G := fun _ : ℕ => clampQ (F n) g₀) (F := fun τ : ℝ => slice (clampQ (F n) g₀) τ)
      (W := fun τ : ℝ => rhsFun α Φs E (clampQ (F n) g₀) τ) (α := α) (B := Bd) (T := T)
      hT ?_ ?_ hW hWc'
    · intro τ hτ
      exact convLocUnifH6_const (α := α) (B := Bd) (f := slice (clampQ (F n) g₀) τ)
        (hconvC τ ⟨hτ.1, le_trans hτ.2 hTT⟩).contDiffOn
        (hBd τ hτ.1 hτ.2)
    · intro K hK hKQ
      obtain ⟨L, hL0, hL⟩ := limMixedBndsOn hα.1 hα.2 (hapx T hT le_rfl)
      exact ⟨L, hL0, fun _ j i hji p hp τ hτ τ' hτ' =>
        (hL τ hτ τ' hτ' j i (by omega) p.1 p.2 (hKQ hp).1 (hKQ hp).2.1 (hKQ hp).2.2).2⟩
  -- ## the package
  obtain ⟨Cd, hCd0, hdbd'⟩ := hdbd
  exact ⟨Cd, hCd0,
    { init := h_init
      law := h_law
      eqT := h_eqT
      c1 := h_c1
      c4 := h_c4
      cont := h_cont
      mem4 := h_mem4
      bd4 := h_bd4
      bd6 := h_bd6
      vanish := h_vanish
      dbd := fun τ h1 h2 => hdbd' τ h1 h2
      limApprox := fun T' h1 h2 => hapx T' h1 h2 }⟩

end Work.FTS.StrongEps.E5G
end
end

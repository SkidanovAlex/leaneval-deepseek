import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseBoxFock.TauProf
import Submission.Work.BoseFixB1.slidingBC_holds
import Submission.Work.BoseFixB1.windowBridge_holds
import Submission.Work.BoseFixB1B.perBoxIntegrated
import Submission.Work.BoseFixB1B.trimOffInterior
import Submission.Work.BoseFixB1B.w1MassB_integral_le_holds
import Submission.Work.BoseFixB1S.flatArmSlidingDefs
import Submission.Work.BoseFixR.HonestFacts
import Submission.Work.BoseFixR.RB67CanonGuarded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Defs` — FS §8 `eq:Hamilton2ndQuant` (box ↔ Fock): the vocabulary

Design document: `BOSE_BOXFOCK_LEAD.md` (curric-46, 2026-10-04).  This module is the
**vocabulary** of the subproject `Submission/Work/BoseBoxFock/`: the definitions of the
design's §§1–8, with the three inline obligations **proved** (not `sorry`ed):

* `kmomLab_neg` — the momentum label is odd under negation;
* `exists_tauProf` — an explicit smooth monotone kinetic profile `τ̃ ≤ τ`
  (proved in `Submission.Work.BoseBoxFock.TauProf`, imported here);
* `tildeDataHon`'s `NH_nonneg` — `n₊^H = (1/32)Σ η_H a†a ≥ 0` (a sum of `bomb`-squares).

This file is `sorry`-free and is the module every other file of the subproject imports.

Summary of the corrections relative to `Work.BoseFixR.Defs`:
* `KzBog` is **half** of FS's `𝒦^Bog` (`¼` instead of `½` per `k`) and its `𝒞`-term misses the
  factor `ℓ³` (`χ̂_Λ(k) = ℓ³χ̂(kℓ)`): `KzBogFS` is FS `eq:BogHamPositive-1` exactly;
* the honest model is pinned: periodic lattice cube `Lab N`, coordinates of the *actual*
  `L²(Λ)` vectors `Q(e^{ikx}χ_Λ)`, `e^{isx}θ` (`HonestModes`), `n₊^H` realised on the
  χ-modes (`(1/32)Σ η_H a†a`, not B4's `totNumOp`), `τ̃` smooth, `Ŵ₁` with a UV cut-off,
  and the χ-label `0` (the vector `Qχ_Λ`, not the condensate) kept in the Bogoliubov sums;
* the `§10` gate `Q3KernelFS` guards `kmom_sub`/`hasKernel` by `W₁ k ≠ 0` (the unguarded row
  is unsatisfiable on every finite lattice: `KmomSubFalse.lean`), allows `supp f_L ⊆ 2P_L`
  (FS's own support), and gives `q2exLower` a reserve `½·dNumOpR` off `P_H^q`;
* the Bessel conjunct is `n₊^χ ≤ Cn·N` with `Cn ≤ 16` (honest `Cn = ‖χ‖∞² ≤ 48/π`).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The chosen kinetic profile of `exists_tauProf` (`Submission.Work.BoseBoxFock.TauProf`). -/
def tauProf : ℝ → ℝ := tauPhi

/-- The specification of `tauProf` (LEAD 10-08: `tauProf := tauPhi`; the conjuncts are those of
`exists_tauProf`, so `.2.2.1`-style projections are unchanged). -/
theorem tauProf_spec : ContDiff ℝ (⊤ : ℕ∞) tauProf ∧ Monotone tauProf ∧
    (∀ r, (max 0 (r - 2)) ^ 2 ≤ tauProf r) ∧ (∀ r, tauProf r ≤ (max 0 (r - 1)) ^ 2) ∧
    (∀ r, r ≤ 1 → tauProf r = 0) ∧
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ r, 2 ≤ r → tauProf r = (r - 3 / 2) ^ 2 + c₀ :=
  ⟨tauPhi_contDiff, tauPhi_mono, tauPhi_ge, tauPhi_le, tauPhi_zero_of_le_one,
    ⟨∫ t, t ^ 2 * tauKer t, tauKer_moment2_nonneg, tauPhi_quad⟩⟩


/-! ## 1. The periodic lattice cube -/

/-- Mode labels: the cube `{-N,…,N}³` of the box lattice `(2π/ℓ)ℤ³`, as a finite group. -/
abbrev Lab (N : ℕ) : Type := Fin 3 → ZMod (2 * N + 1)

/-- The centred integer vector of a label. -/
def labVec (N : ℕ) (n : Lab N) : Fin 3 → ℤ := fun i => (n i).valMinAbs

/-- The physical momentum `2πn/ℓ` of a label (`Work.BoseB4.vec n = 2πn`). -/
def kmomLab (ℓ : ℝ) (N : ℕ) (n : Lab N) : ℝ³ := ℓ⁻¹ • Work.BoseB4.vec (labVec N n)

/-- On `ZMod (2N+1)` (odd modulus) the least-absolute representative is odd. -/
lemma valMinAbs_neg_odd (N : ℕ) (x : ZMod (2 * N + 1)) :
    (-x).valMinAbs = -x.valMinAbs := by
  apply ZMod.valMinAbs_neg_of_ne_half
  intro h
  have hx : x.val < 2 * N + 1 := ZMod.val_lt x
  omega

lemma labVec_neg (N : ℕ) (n : Lab N) : labVec N (-n) = -labVec N n := by
  funext i
  show ((-n) i).valMinAbs = -(n i).valMinAbs
  rw [Pi.neg_apply]
  exact valMinAbs_neg_odd N (n i)

lemma vec_neg (m : Fin 3 → ℤ) : Work.BoseB4.vec (-m) = -Work.BoseB4.vec m := by
  ext i
  simp [Work.BoseB4.vec]

/-- Odd modulus: `valMinAbs (-x) = -valMinAbs x`, hence the momentum is odd. -/
theorem kmomLab_neg (ℓ : ℝ) (N : ℕ) (n : Lab N) : kmomLab ℓ N (-n) = -kmomLab ℓ N n := by
  unfold kmomLab
  rw [labVec_neg, vec_neg, smul_neg]

/-! ## 2. The kernel pins of the honest model -/

/-- **The smoothed kinetic symbol** `τ̃ ≤ τ` (FS `def:tau` with the kinks at
`|k| = ½(sℓ)⁻¹, ½(dsℓ)⁻¹` mollified).  `0 ≤ |k|² − τ̃(k) ≤ 2|k|/(dsℓ)` (`IntKernel.tau_PH`). -/
def tauSm (eT s d ℓ : ℝ) (k : ℝ³) : ℝ :=
  (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (‖k‖ / (2 * s * ℓ)⁻¹)
    + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (‖k‖ / (2 * d * s * ℓ)⁻¹)

/-- The UV cut-off `ζ_Λ(k) = f_u(|k|/Λ)` (a `LowCut`: `1` on `|k| ≤ Λ`, `0` on `|k| ≥ 2Λ`). -/
def uvCut (fu : LowCut) (Λ : ℝ) (k : ℝ³) : ℝ := fu.f (‖k‖ / Λ)

/-- The cut-off radius at lattice size `N`: `Λ_N = (2π/ℓ)·N/4`, so `supp Ŵ₁ζ ⊆ {|k| ≤ πN/ℓ}`
stays a quarter-cube away from the boundary (no wrap for `s ∈ 2P_L`). -/
def uvRad (ℓ : ℝ) (N : ℕ) : ℝ := 2 * π / ℓ * (N : ℝ) / 4

/-! ## 3. The honest mode data -/

/-- The box side used by the mode data: `sideAt μ (a v)` whenever it is positive (always, at
admissible `μ`), `1` otherwise (this only makes the family total). -/
def ellH (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := if 0 < sideAt μ (a v) then sideAt μ (a v) else 1

theorem ellH_pos (v : ℝ³ → ℝ) (μ : ℝ) : 0 < ellH v μ := by
  unfold ellH; split_ifs with h
  · exact h
  · exact one_pos

/-- A `LowCut` is bounded by `1` (`Antitone`, `f = 1` on `(-∞,1]`). -/
theorem _root_.Work.BoseBoxFix.LowCut.le_one (fc : LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  rcases lt_or_ge s 1 with h | h
  · rw [fc.one s h.le]
  · calc fc.f s ≤ fc.f 1 := fc.anti h
      _ = 1 := fc.one 1 le_rfl

/-- A `LowCut` is nonnegative (`Antitone`, `f = 0` on `[2,∞)`). -/
theorem _root_.Work.BoseBoxFix.LowCut.nonneg (fc : LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  rcases lt_or_ge s 2 with h | h
  · calc (0 : ℝ) = fc.f 2 := (fc.zero 2 le_rfl).symm
      _ ≤ fc.f s := fc.anti h.le
  · rw [fc.zero s h]

/-- **The honest box modes at chemical potential `μ`**: coordinates in `ℝ^m` (index `0` the
condensate `ℓ^{-3/2}θ`) of the *actual* `L²(Λ)` vectors
`ℓ^{-3/2}Q(e^{ikx}χ_Λ)` (χ-modes, `f`) and `ℓ^{-3/2}e^{isx}θ` (θ-modes, `g`) for every label of
the cube `Lab N`, with their exact (real) Gram matrix.  The Gram matrix is the complex one
(all inner products are real because `χ` is even), so the `ℂ`-linear extension of
`vector ↦ coordinates` is an isometry (`BF3c`). -/
structure HonestModes (v : ℝ³ → ℝ) (μ : ℝ) where
  N : ℕ
  m : ℕ
  [hm : NeZero m]
  f : Lab N → Fin m → ℝ
  g : Lab N → Fin m → ℝ
  hf : ∀ i j, Work.BoseB4.gram (f i) (f j)
    = Work.BoseB7.ccrKernel (ellH v μ) Work.BoseK15.corpusBox.hatChiSq
        Work.BoseK15.corpusBox.hatChi (kmomLab (ellH v μ) N i) (kmomLab (ellH v μ) N j)
  hg : ∀ s t, s ≠ 0 → t ≠ 0 → Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0
  hcross : ∀ s k, Work.BoseB4.gram (g s) (f k)
    = Work.BoseK15.corpusBox.hatChi
        (ellH v μ • (kmomLab (ellH v μ) N k - kmomLab (ellH v μ) N s))
  /-- the condensate coordinate is free (`Q(·) ⊥ θ`, `e^{isx}θ ⊥ θ` for `s ≠ 0`). -/
  hf0 : ∀ k, f k 0 = 0
  hg0 : ∀ s, s ≠ 0 → g s 0 = 0
  /-- the realisation is the coordinate map of the physical vectors (needed only by `BF3`):
  the `realIP`-Gram of the physical family equals the coordinate Gram. -/
  hphys : ∀ i j, Work.BoseB4.gram (f i) (f j)
    = (ellH v μ) ^ (-(3 : ℤ)) * Work.BoseK15.corpusBox.realIP
        (Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N i))
        (Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N j))

attribute [instance] HonestModes.hm

/-- FS's `n₊^H` threshold profile on the χ-modes: `η_H(k) = 1 − f_u(|k|/(2κ))`, i.e. `0` for
`|k| ≤ 2κ`, `1` for `|k| ≥ 4κ`, with `κ = K_L√(μa) = (d²ℓ)⁻¹`. -/
def etaH (fu : LowCut) (κ : ℝ) (k : ℝ³) : ℝ := 1 - fu.f (‖k‖ / (2 * κ))

lemma etaH_nonneg (fu : LowCut) (κ : ℝ) (k : ℝ³) : 0 ≤ etaH fu κ k := by
  unfold etaH; linarith [fu.le_one (‖k‖ / (2 * κ))]

lemma etaH_le_one (fu : LowCut) (κ : ℝ) (k : ℝ³) : etaH fu κ k ≤ 1 := by
  unfold etaH; linarith [fu.nonneg (‖k‖ / (2 * κ))]

/-- `bomb m` is linear in its first argument (a scalar pulls out). -/
lemma bomb_smul_apply {m : ℕ} (c : ℝ) (z y : Work.BoseB4.RealFock m) :
    Work.BoseB4.bomb m (c • z) y = c * Work.BoseB4.bomb m z y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- A nonnegative combination of `bomb`-nonnegative operators is `bomb`-nonnegative. -/
lemma bomb_sum_smul_nonneg {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (A : ι → Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)
    (hc : ∀ k ∈ s, 0 ≤ c k) (hA : ∀ k ∈ s, ∀ y, 0 ≤ Work.BoseB4.bomb m (A k y) y)
    (y : Work.BoseB4.RealFock m) :
    0 ≤ Work.BoseB4.bomb m ((∑ k ∈ s, c k • A k) y) y := by
  have h1 : (∑ k ∈ s, c k • A k) y = ∑ k ∈ s, c k • (A k y) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.smul_apply]
  have h2 : Work.BoseB4.bomb m ((∑ k ∈ s, c k • A k) y) y
      = ∑ k ∈ s, c k * Work.BoseB4.bomb m (A k y) y := by
    rw [h1, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [bomb_smul_apply]
  rw [h2]
  exact Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk) (hA k hk y)

/-- The `NH` of `tildeDataHon` is a nonnegative combination of `bomb`-squares:
`(1/32)Σ_k η_H(k)a_k†a_k ≥ 0`. -/
lemma tildeNH_nonneg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → ℝ³) (m : ℕ) (f : Mode → Fin m → ℝ) (fu : LowCut) (κ : ℝ)
    (y : Work.BoseB4.RealFock m) :
    0 ≤ Work.BoseB4.bomb m
      (((1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode, etaH fu κ (kmom k) •
        (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))) y) y := by
  have hsum : 0 ≤ Work.BoseB4.bomb m
      ((∑ k ∈ Work.BoseB7.excited Mode, etaH fu κ (kmom k) •
        (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))) y) y :=
    bomb_sum_smul_nonneg (s := Work.BoseB7.excited Mode)
      (fun k => etaH fu κ (kmom k))
      (fun k => (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k)))
      (fun k _ => etaH_nonneg fu κ (kmom k))
      (fun k _ z => by
        rw [LinearMap.comp_apply, Work.BoseB4.CreOf_annOf_adjoint]
        exact Work.BoseB4.Bomb_self_nonneg _) y
  have hsplit : ((1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode, etaH fu κ (kmom k) •
        (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))) y
      = (1 / 32 : ℝ) • ((∑ k ∈ Work.BoseB7.excited Mode, etaH fu κ (kmom k) •
        (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))) y) :=
    LinearMap.smul_apply _ _ _
  rw [hsplit, bomb_smul_apply]
  exact mul_nonneg (by norm_num) hsum

/-- The `θ`-mode data with **FS's `n₊^H` realised on the χ-modes**:
`NH = (1/32)Σ_k η_H(k) a_k†a_k`, which is `≤ n₊^H_phys + (tiny)·n₊` (BF3, row `gapH`:
`χ η_H(p) χ ≤ 2‖χ‖∞²·1_{(κ,∞)}(√−Δ) + O((κℓ)^{-∞})`, `‖χ‖∞² ≤ 16`).  B4's `tildeData` sets
`NH := totNumOp`, i.e. the `ε_T(dℓ)⁻²` gap on *every* excited particle (`X^{-6.25}` times the
Bogoliubov scale): that freezes the modes below `√γ` and makes the honest domination false. -/
def tildeDataHon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {ℓ : ℝ} (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (m : ℕ)
    (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq Work.BoseK15.corpusBox.hatChi
          (kmom i) (kmom j))
    (hg : ∀ s t : Mode, s ≠ 0 → t ≠ 0 → Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (fu : LowCut) (κ : ℝ) :
    Work.BoseB7A.TildeData (Work.BoseB4.boxFockData Work.BoseK15.corpusBox kmom hkmom m f hf) :=
  { ta := fun s => Work.BoseB4.annOf m (g s)
    taDag := fun s => Work.BoseB4.creOf m (g s)
    taDag_adjoint := fun s x y => Work.BoseB4.CreOf_annOf_adjoint (g s) x y
    ta_comm := fun s t => Work.BoseB4.AnnOf_ann_comm (g s) (g t)
    taDag_comm := fun s t => Work.BoseB4.CreOf_cre_comm (g s) (g t)
    ta_ccr := fun s t hs ht => by
      have h := Work.BoseB4.AnnOf_creOf_ccr (g s) (g t)
      rw [hg s t hs ht] at h
      exact h
    ta_a_comm := fun s k => Work.BoseB4.AnnOf_ann_comm (g s) (f k)
    ccrX := fun s k => Work.BoseB4.gram (g s) (f k)
    ta_aDag := fun s k => Work.BoseB4.AnnOf_creOf_ccr (g s) (f k)
    N := Work.BoseB4.totNumOp m
    NH := (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode,
      etaH fu κ (kmom k) • (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))
    N_symm := fun x y => Work.BoseB4.totNumOp_symm m x y
    N_nonneg := fun x => Work.BoseB4.totNumOp_nonneg m x
    NH_nonneg := fun x => tildeNH_nonneg kmom m f fu κ x
    N_a := fun k => Work.BoseB4.totNumOp_comp_annOf m (f k)
    N_aDag := fun k => Work.BoseB4.totNumOp_comp_creOf m (f k)
    N_ta := fun s => Work.BoseB4.totNumOp_comp_annOf m (g s)
    N_taDag := fun s => Work.BoseB4.totNumOp_comp_creOf m (g s)
    ta_le_N := fun S hS Φ =>
      Work.BoseB4.bessel_le_totNumOp_sum_comp g S (fun s hs t ht => hg s t (hS s hs) (hS t ht)) Φ }

/-- **The honest `Q3Env`**: `KzEnvFs` with the smoothed `τ̃` and the UV-cut `Ŵ₁ζ_{Λ_N}`. -/
def KzEnvHon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (F : Work.BoseB7.FockData Mode) (fc fu : LowCut)
    (N : ℕ) : Work.BoseB7.Q3Env Mode :=
  let E := KzEnvFs v h μ F fc
  let P := paramsAt μ (a v)
  let ℓ := sideAt μ (a v)
  let W1z : Mode → ℝ := fun k => uvCut fu (uvRad ℓ N) (F.kmom k) * chat (W1fun v h ℓ) (F.kmom k)
  let τt : Mode → ℝ := fun k => tauSm P.eT P.s P.d ℓ (F.kmom k)
  { E with
    W1 := W1z
    tau := τt
    A := fun k => τt k + μ * W1z k
    B := fun k => μ * W1z k }

/-- **The honest family** (one `KzDatum` per `μ`, from a choice `HM` of honest data). -/
def HonestBoxFam (v : ℝ³ → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) : ℝ → KzDatum :=
  fun μ =>
    let ℓ := ellH v μ
    let F := Work.BoseB4.boxFockData Work.BoseK15.corpusBox (kmomLab ℓ (HM μ).N)
      (kmomLab_neg ℓ (HM μ).N) (HM μ).m (HM μ).f (HM μ).hf
    { Mode := Lab (HM μ).N
      F := F
      E := KzEnvHon v h μ F fc fu (HM μ).N
      gHat0 := 8 * π * a v
      T := tildeDataHon (kmomLab ℓ (HM μ).N) (kmomLab_neg ℓ (HM μ).N) (HM μ).m (HM μ).f
        (HM μ).g (HM μ).hf (HM μ).hg fu
        (((paramsAt μ (a v)).Kl * (paramsAt μ (a v)).d ^ 2) ^ (-(1 : ℝ)) * Real.sqrt (μ * a v)) }

/-! ## 4. FS's substituted Hamiltonian, correctly normalised -/

/-- **FS `eq:BogHamPositive-1` (with `𝒬₁(z)` folded in, `eq:SimplifyKz`)**:
`𝒦^Bog = ½Σ_k[𝒜(n_k+n_{-k}) + ℬ(a_ka_{-k}+h.c.) + 𝒞(a_k+a_k†+a_{-k}+a_{-k}†)]`,
`𝒞(k) = ℓ⁻³(ρ−μ)Ŵ₁(0)χ̂_Λ(k)z = (ρ−μ)Ŵ₁(0)χ̂(kℓ)z`.  (`Work.BoseFixR.KzBog` has `¼` and
`ℓ⁻³χ̂(kℓ)`: it is `½𝒦^Bog` with a `1/(2ℓ³)`-scaled `𝒬₁`.) -/
def KzBogFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) : F.H →ₗ[ℝ] F.H :=
  let z : ℝ := Real.sqrt (ρ * E.ell ^ 3)
  ∑ k : Mode, (1 / 2 : ℝ) •
    ((E.tau k + ρ * E.W1 k) • (F.nOp k + F.nOp (-k))
      + (ρ * E.W1 k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
      + ((ρ - E.mu) * E.W1 0 * E.hatChi k * z) •
          (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)))

/-- **FS `eq:Kz`** with the correct `𝒦^Bog` (all other groups as `Work.BoseFixR.KzOp`). -/
def KzOpFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) : F.H →ₗ[ℝ] F.H :=
  ((E.b / (2 * E.ell ^ 2)) • T.N)
    + ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH)
    + ((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
        + (1 / 2) * ρ ^ 2 * E.W1omega0)) • (1 : F.H →ₗ[ℝ] F.H))
    + KzBogFS F E ρ
    + (((ρ - E.mu) * E.W1 0) • ∑ k : Mode, F.nOp k)
    + T.linOpT (KzEnvAt E ρ)
    + F.Q2ex (KzEnvAt E ρ)
    + T.Q3T (KzEnvAt E ρ)

def KzValFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) : ℝ :=
  ⨅ (f : {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0}),
    F.qw f.1 (KzOpFS F T E gHat0 ρ) / F.normSq f.1

def _root_.Work.BoseFixR.KzDatum.valFS (D : KzDatum) (ρ : ℝ) : ℝ := KzValFS D.F D.T D.E D.gHat0 ρ

/-! ## 5. The guarded §10 gate -/

/-- The region kept for `§10` and the `q2exLower` reserve: `|k| ≥ ½K_L√(μa)` (`= ½(d²ℓ)⁻¹`). -/
def RHi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : Work.BoseB7.FockData Mode)
    (E : Work.BoseB7.Q3Env Mode) (k : Mode) : Prop :=
  E.KL * Real.sqrt (E.mu * E.aScat) / 2 ≤ ‖F.kmom k‖

instance {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : Work.BoseB7.FockData Mode)
    (E : Work.BoseB7.Q3Env Mode) : DecidablePred (RHi F E) :=
  fun k => Classical.dec _

/-- **The honest `§10` kernel interface** (`Work.BoseK15.Q3Kernel'` with four rows repaired):
* `kmom_sub`, `hasKernel` only where `Ŵ₁(k) ≠ 0` — the unguarded rows are unsatisfiable on
  any finite lattice (`KmomSubFalse.kmom_sub_unsat`); every `Q₃` term carries `Ŵ₁(k)`;
* `fL_supp` with FS's support `|s| ≤ 2K_L√(μa)` (`f = 0` only on `[2,∞)`);
* `q2exLower` with a reserve `½·dNumOpR` on `RHi ∖ P_H^q`: the model's `n₊^H` starts at
  `2K_L√(μa)` (it must stay below the physical `n₊^H`, whose threshold is `K_L√(μa)`), so the
  θ-content of `Gop` at `|s| ∈ [K_L√(μa), 4K_L√(μa)]` is paid by the kinetic energy there
  (`τ̃ ≥ K_L²μa/8`, coefficient needed `≤ X^{18}`), which no `§10` estimate uses. -/
structure Q3KernelFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  A_even : ∀ k, E.A (-k) = E.A k
  B_even : ∀ k, E.B (-k) = E.B k
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  AB : ∀ k, |E.B k| ≤ E.A k
  A_ge : ∀ q, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  fL_supp2 : ∀ s, E.fL s ≠ 0 → ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat))
  kmom_subW : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.kmom (s - k) = F.kmom s - F.kmom k
  kmom_subL : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → F.kmom (s - s') = F.kmom s - F.kmom s'
  hasKernelW : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → E.W1 j ≠ 0 →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hasKernel_noWrap : ∀ i j, Work.BoseK15.NoWrap F.kmom i j →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * Work.BoseB7A.eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * Work.BoseB7A.eta E
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s) ∧
      ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s)
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s)
  count_PL : (((Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
    ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_hatChiSq : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (Work.BoseB7.excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat
  alpha_lip : ∀ p q, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |E.alpha p - E.alpha q| ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  intOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ K₀ * E.rho * E.aScat * E.KH⁻¹
  q2exLowerR : ∀ Ψ : F.H, 2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)
      + (1 / 2) * F.qw Ψ (F.dNumOpR E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k))

/-! ## 5b. The corrected close threshold (design `F9`)

FS `eq:Close`'s threshold carries a universal constant.  The design's `F9` fixes it at
`μK_ℓ⁻²/(2¹⁴π)`: the `n₀n₊` row `(ρ−μ)Ŵ₁(0)·n₊` is absorbed into the *gap* via
`|ρ−μ|·16πa·16·N ≤ (b/4ℓ²)N`, which needs exactly this constant (the `c`-number slot that
absorbed it in the old interface is consumed by the `κ`-sum, `eq:Combined1`); §9's far bound
holds for *any* fixed constant, so the far/close partition stays valid.

The FS-specific statements below (`RViewFS`, `RB5FS`, `RB67FS`, `BogOpBoundFS`,
`HonestGateAtFS`) use these corrected conditions.  (`Work.BoseBogFS.closeThresholdFS` is a
second, identical copy made by the `BOG` subproject before this one existed.) -/

/-- FS `eq:Close`'s threshold with FS's universal constant `1/(2¹⁴π)`. -/
def closeThresholdFS (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi)

/-- `eq:Close` at the corrected threshold: `|ρ_z − μ| ≤ μK_ℓ⁻²/(2¹⁴π)`. -/
def CloseCondFS (v : ℝ³ → ℝ) (μ ρ : ℝ) : Prop := |ρ - μ| ≤ closeThresholdFS v μ

/-- The complement of `CloseCondFS` (FS §9's far region at the corrected threshold). -/
def FarCondFS (v : ℝ³ → ℝ) (μ ρ : ℝ) : Prop := closeThresholdFS v μ ≤ |ρ - μ|

/-! ## 6. The corrected view -/

/-- **The corrected view.**  Changes against `Work.BoseFixR.RView`:
(i) `E.tau` pinned to the smoothed `τ̃`; (ii) `E.W1` pinned to `ζ·Ŵ₁` at some cut-off radius
`Λ ≥ 4K_L√(μa)` (so `supp f_L` and `supp ζ` cannot wrap); (iii) `T.NH` pinned to the χ-mode
`n₊^H`; (iv) the Bessel conjunct over **all** χ-labels with an absolute cap `Cn ≤ 16`;
(v) the gate is `Q3KernelFS`. -/
def RViewFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : Prop :=
  Nonempty (Work.BoseB7.FSParamsView E) ∧ E.mu = μ ∧ E.aScat = a v
    ∧ E.ell = ell v μ ∧ E.bigM = bigM (paramsAt μ (a v)) (a v) μ
    ∧ E.b = (paramsAt μ (a v)).b ∧ E.d = (paramsAt μ (a v)).d
    ∧ E.s = (paramsAt μ (a v)).s ∧ E.eT = (paramsAt μ (a v)).eT
    ∧ E.intM = (paramsAt μ (a v)).M ∧ gHat0 = 8 * π * a v
    ∧ E.tau = (fun k => tauSm (paramsAt μ (a v)).eT (paramsAt μ (a v)).s
        (paramsAt μ (a v)).d (ell v μ) (F.kmom k))
    ∧ E.A = (fun k => E.tau k + E.rho * E.W1 k)
    ∧ E.B = (fun k => E.rho * E.W1 k)
    ∧ (∃ (fu : LowCut) (Λ : ℝ), 4 * (E.KL * Real.sqrt (E.mu * E.aScat)) ≤ Λ ∧
        E.W1 = (fun k => uvCut fu Λ (F.kmom k) * chat (W1fun v h (ell v μ)) (F.kmom k)))
    ∧ E.W1omega = (fun k => chat (W1omegaFun v h (ell v μ)) (F.kmom k))
    ∧ E.W1omega0 = chat (W1omegaFun v h (ell v μ)) 0
    ∧ E.hatChi = (fun k => chat (chiFun (ell v μ)) (F.kmom k)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ E.hatChiSq = (fun k =>
        chat (fun z => chiFun (ell v μ) z ^ 2) (F.kmom k)
          / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ (∃ fc : LowCut, E.fL = (fun k => fLFS fc E.KL E.mu E.aScat (F.kmom k)))
    ∧ (∃ fu : LowCut, T.NH = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode,
        etaH fu (E.KL * Real.sqrt (E.mu * E.aScat)) (F.kmom k) • F.nOp k)
    ∧ (∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧
        ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    ∧ (∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b
        ∧ ∀ ρ : ℝ, CloseCondFS v μ ρ → Q3KernelFS K₀ F T (KzEnvAt E ρ))

def _root_.Work.BoseFixR.KzDatum.viewFS (D : KzDatum) (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) : Prop :=
  RViewFS v h μ D.F D.T D.E D.gHat0

/-! ## 7. The residuals in the corrected vocabulary -/

/-- **R-B4box (FS §8) at the concrete box model `HM`** (FS assume `eq:apriorinn+`; here only
its consequence `n ≤ 2μℓ³`, supplied by `NodeB1B`). -/
def RB4boxDomAt (v : ℝ³ → ℝ) (h : ScatSol v) (R J : ℝ) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        (n : ℝ) ≤ 2 * μ * sideAt μ (a v) ^ 3 →
        IsLowB v h J μ n Φ →
        SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ : X n → ℝ) →
        (⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1 * normB v μ n Φ)
          ≤ wordB v h μ n Φ + errKafz v R μ C * normB v μ n Φ

/-- … for every honest model whose lattice cube is at least `Nmin μ`. -/
def RB4boxDomFS (v : ℝ³ → ℝ) (h : ScatSol v) (R J : ℝ) (fc fu : LowCut) : Prop :=
  ∃ Nmin : ℝ → ℕ, ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Nmin μ ≤ (HM μ).N) →
    RB4boxDomAt v h R J fc fu HM

/-- FS §9 at a family, corrected vocabulary (`RB5` with `KzOpFS`, `viewFS`). -/
def RB5FS (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → FarCondFS v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      FarBound v μ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOpFS (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-- FS §10+§11 close case at a family, corrected vocabulary. -/
def RB67FS (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
    ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ → ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
      CloseBoundR v R μ C ρ * (D μ).F.normSq f
        ≤ (D μ).F.qw f (KzOpFS (D μ).F (D μ).T (D μ).E (D μ).gHat0 ρ)

/-- **FS `eq:Combined1` (`thm:BogHamDiag` + `lem:BogIntegral`), corrected.**  Against
`Work.BoseFixR.BogOpBound`: (i) `KzBogFS` (the honest `𝒦^Bog`); (ii) the diagonal reserve is
`dNumOpR` on `RHi` only — with the `𝒞`-term the unshifted `Σ_{all k}𝒟b†b` cannot be split
off (the linear word is `O(μK_ℓ⁻²a√(μℓ³)√𝓜)`, `X^{-116}` times LHY, on window states); FS
complete it into the shifted `b+c` on the low modes, which is then dropped as `≥ 0`, and
`c_k = O(χ̂(kℓ))` is negligible on `RHi`; (iii) the `κ`-sum's `½(ρ−μ)²ℓ³ĝ(0)` is on the
right (FS cancel it against the `c`-number). -/
def BogOpBoundFS (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ) (RHi (D μ).F (KzEnvAt (D μ).E ρ)))
          ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0
                + (1 / 2) * (ρ - μ) ^ 2 * (D μ).E.ell ^ 3 * (D μ).gHat0) * (D μ).F.normSq f

/-- `thm:Control3Q`'s word with the diagonal reserve on `RHi` (the `§10` estimates use
`P_H ⊆ P_H^q ⊆ RHi`; the `q2exLowerR` reserve lives in `RHi ∖ P_H^q`). -/
def controlWordHi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.dNumOpR E (RHi F E) + T.Q3T E + F.Q2ex E + T.linOpT E + (E.b / 50) • T.gapOpT E

/-- **`thm:Control3Q` re-delivery request (BoseB7A/B7AK)** at the guarded gate. -/
def Control3QFS (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
    ∀ {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : Work.BoseB7.FockData.{0, 0} Mode) (T : Work.BoseB7A.TildeData F)
      (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
      hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFS K₀ F T E →
      ∀ Φ : F.H, T.NWindow E.bigM Φ →
        -(C * Work.BoseB7A.controlErrA E) * F.normSq Φ ≤ F.qw Φ (controlWordHi T E)

/-- **The honest §10 gate** at one absolute pair `(K₀,b₀)`, on `{μa³ ≤ ε₀}`. -/
def HonestGateAtFS (v : ℝ³ → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (ε₀ K₀ b₀ : ℝ) : Prop :=
  0 ≤ K₀ ∧ 0 < b₀ ∧
    (∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ → b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b) ∧
    (∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      Q3KernelFS K₀ (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
        (KzEnvAt (HonestBoxFam v h fc fu HM μ).E ρ))

/-- **The gate holds at every honest model with a large enough cube** (BoseK15 re-delivery:
`K15Input`/`Q3Kernel'_of_box` with the four repaired rows; `Ng` makes the UV tails of
`intOne`/`omega_lattice`/`sum_diff` below `K₀aK_H⁻¹`, `K₀a²/ℓ`). -/
def HonestGateFS (v : ℝ³ → ℝ) (h : ScatSol v) (fc fu : LowCut) (K₀ b₀ : ℝ) : Prop :=
  ∃ (Ng : ℝ → ℕ) (εg : ℝ), 0 < εg ∧ εg ≤ 1 ∧
    ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Ng μ ≤ (HM μ).N) →
      HonestGateAtFS v h fc fu HM εg K₀ b₀

/-! ## 8. The bridge `eq:Hamilton2ndQuant` (nodes BF2–BF6) -/

section Model
variable {m : ℕ} [NeZero m]

open Work.BoseB4

/-- `n₀ = a₀†a₀` on the model. -/
def n0 : RealFock m →ₗ[ℝ] RealFock m := (cre m 0).comp (ann m 0)

/-- **FS `eq:HLambdaSecond` on the honest model** (superposition modes; `Work.BoseB4.H2nd` uses
orthonormal basis modes, `Fin m`-negation and the `ℓ⁻³`-typo of FS's `n₀n₊` row, so it is
*not* this operator).  Rows: kinetic `Σ τ̃ a†a`; gap `(b/2ℓ²)n₊`; `n₊^H`-gap (`NH` of
`tildeDataHon`); contact (with `Ŵ₁ω(0)` for `ĝω(0)`, cost `C(R/ℓ)²` absorbed in BF3);
chemical; `(Ŵ₁+Ŵ₁ω)a₀†a†aa₀`; Bogoliubov pairs; the `χ̂`-linear rows (χ-modes for `𝒬₁`,
θ-modes for `𝒬₁^ex`); the `n₀n₊` row; the cubic `Q̃₃`.  Its anti-Wick symbol on the
zero-condensate slice at `z = √(ρℓ³)` is `KzOpFS(ρ)` plus the `eq:subst-z` remainders. -/
def H2ndF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (NH : RealFock m →ₗ[ℝ] RealFock m) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  let a := fun k => annOf m (f k)
  let ad := fun k => creOf m (f k)
  let ta := fun s => annOf m (g s)
  let tad := fun s => creOf m (g s)
  let a0 := ann m 0
  let a0d := cre m 0
  let ex := Work.BoseB7.excited Mode
  let L0 : RealFock m →ₗ[ℝ] RealFock m :=
    (E.ell ^ (-(3 : ℝ)) * E.W1 0) • n0 - (E.mu * E.W1 0) • (1 : RealFock m →ₗ[ℝ] RealFock m)
  let L1 : RealFock m →ₗ[ℝ] RealFock m := (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • n0
  (∑ k : Mode, E.tau k • (ad k ∘ₗ a k))
  + (E.b / (2 * E.ell ^ 2)) • (totNumOp m - n0)
  + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • NH
  + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)) * (gHat0 + E.W1omega0)) • (a0d ∘ₗ a0d ∘ₗ a0 ∘ₗ a0)
  - (E.mu * gHat0) • n0
  + (E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, (E.W1 k + E.W1omega k) • (a0d ∘ₗ ad k ∘ₗ a k ∘ₗ a0)
  + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, E.W1 k •
      (a0d ∘ₗ a0d ∘ₗ a k ∘ₗ a (-k) + ad k ∘ₗ ad (-k) ∘ₗ a0 ∘ₗ a0)
  + ∑ k : Mode, E.hatChi k • (L0 ∘ₗ ad k ∘ₗ a0 + a0d ∘ₗ a k ∘ₗ L0)
  + ∑ s ∈ ex, E.hatChiSq s • (L1 ∘ₗ tad s ∘ₗ a0 + a0d ∘ₗ ta s ∘ₗ L1)
  + (L0 + L1) ∘ₗ (∑ k : Mode, ad k ∘ₗ a k)
  + (E.ell ^ (-(3 : ℝ))) • ∑ s ∈ ex, ∑ k ∈ PHs, (E.fL s * E.W1 k) •
      (a0d ∘ₗ tad s ∘ₗ a (s - k) ∘ₗ a k + ad k ∘ₗ ad (s - k) ∘ₗ ta s ∘ₗ a0)

/-- The excited (non-condensate) number `n₊^V = N − n₀` of the model. -/
def nExc : RealFock m →ₗ[ℝ] RealFock m := totNumOp m - n0

/-- The **excited window** of a model vector (before the `c`-number substitution the
condensate is macroscopically occupied, so `T.NWindow` is the wrong notion): `Ψ` is a finite
sum of `nExc`-eigenvectors with eigenvalues `≤ 𝓜`, and has at most `n` particles. -/
def ExcWindow (M : ℝ) (n : ℕ) (Ψ : RealFock m) : Prop :=
  (∃ φ : ℕ → RealFock m, (∀ j : ℕ, nExc (φ j) = (j : ℝ) • φ j) ∧
    Ψ = ∑ j ∈ Finset.range (⌊M⌋₊ + 1), φ j) ∧
  ∀ α ∈ Ψ.support, α.sum (fun _ k => k) ≤ n

end Model

/-- The model Hamiltonian of the honest datum at `μ`. -/
def H2ndHon (v : ℝ³ → ℝ) (h : ScatSol v) (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ)
    (μ : ℝ) : Work.BoseB4.RealFock (HM μ).m →ₗ[ℝ] Work.BoseB4.RealFock (HM μ).m :=
  H2ndF (HM μ).f (HM μ).g (HonestBoxFam v h fc fu HM μ).T.NH
    ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (HonestBoxFam v h fc fu HM μ).E (8 * π * a v)

end Work.BoseBoxFock

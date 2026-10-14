import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_helpers
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
-- ===== merged: Submission.Work.FTS.EpsEngine.H4FepsLim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps.EpsLocalPStar (iter)
open Work.FTS.EpsEngine (epsIter epsLim)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`(H4)(b)` for `Feps`, completely unconditional** (the per-`z` bound `hz` is produced by the
proved child `perz_iter_feps_le`, and the datum's is by `HkIntegrand_perz_le_noTraces`). -/
theorem HkMem_epsLim_feps {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {g₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen g₀) (h₀mem : Work.Spaces.HkMem α 6 g₀)
    (hδ : 0 ≤ δ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (epsIter α ρ ε Φs E g₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E g₀ n) s z θ - slice (epsIter α ρ ε Φs E g₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E g₀ n) s z θ - slice (epsIter α ρ ε Φs E g₀ m) s z θ)
        ≤ q ^ n)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsIter α ρ ε Φs E g₀ (n + 1)) s z θ
        = g₀ z θ + Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E g₀ n s) z θ
          - epsC α ρ ε Φs E g₀ n s * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun N : ℕ => slice (epsIter α ρ ε Φs E g₀ N) s z θ)
        Filter.atTop (nhds (slice (epsLim α ρ ε Φs E g₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    Work.Spaces.HkMem α 4 (slice (epsLim α ρ ε Φs E g₀) τ) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_perz_le_noTraces
  have h0perz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g₀ z θ) ≤ Bz :=
    fun z hz => ⟨Cz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α g₀) ^ 2,
      hCz α g₀ hα h0 h₀mem z hz⟩
  have hzit := perz_iter_feps_le (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
    (Lw := Lw) (ε := ε) (τ := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    hρ hα hε hε1 hR hLw hτ.1 hEll hstar hml
    (fun n s hs => hP n s ⟨hs.1, le_trans hs.2 hτ.2⟩)
    (fun n s hs t ht => hEq n s ⟨hs.1, le_trans hs.2 hτ.2⟩ t ⟨ht.1, le_trans ht.2 hτ.2⟩)
    h0perz
  have hmem4 : Work.Spaces.HkMem α 4 g₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open h0 4 (by norm_num) h₀mem
  exact HkMem_epsLim_noTraces (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (g₀ := g₀)
    hα hρ hε hε1 hEll hstar hml hR hLw h0 hmem4 hδ hq0 hq1 hP hEq hpair hmoll hconv hτ
    (fun z hz => hzit z hz)

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.perz_iter_feps_le_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter)
open Work.Spaces (HkIntegrand HkSq HkNorm HkMem Iz Iθ HkIntegrand_nonneg HkNorm_nonneg)

set_option maxHeartbeats 1600000

theorem perz_iter_feps_le_six {α C₀ Ce Cs R Lw ε τ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (hτ : 0 ≤ τ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 τ →
      Work.FTS.EpsEngine.XBall α ρ ε R C₀
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 τ → ∀ t : ℝ, t ∈ Set.Icc 0 τ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) s z θ
        - Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (h0 : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g₀ z θ) ≤ Bz) :
    ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) τ)
        z θ) ≤ Bz := by
  -- the per-curve right-hand-side data, uniform in the Picard index, at level `6`
  obtain ⟨B, _hBpos, hdata⟩ :=
    RHSDataFepsSix.exists_RHSData_feps_six (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hτ hEll hstar hml
  have hdat : ∀ k : ℕ, RHSData α 6 τ B (Feps α ρ ε Φs E) g₀ k :=
    fun k => hdata k (fun s hs => hP k s hs) (fun s hs t ht => hEq k s hs t ht)
  -- the uniform `ℋ⁸`-size of the right-hand side
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball8 (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  -- the trace-free per-`z` bound for `ℋ⁶`-profiles
  obtain ⟨Cperz, hCperzpos, hCperz⟩ := HkIntegrand_perz_six_noTraces
  intro z hz
  obtain ⟨Bz0, hBz0⟩ := h0 z hz
  set Cz : ℝ := Cperz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 with hCzdef
  have hCzpos : 0 < Cz := by
    rw [hCzdef]
    have h1 : (0 : ℝ) < 1 + (Work.Spaces.w z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < (1 + Ce') ^ 2 := by positivity
    exact mul_pos (mul_pos hCperzpos h1) h2
  refine ⟨2 * max Bz0 0 + 2 * τ ^ 2 * Cz + 1, ?_⟩
  -- (1) the angular energy of the right-hand side along the `k`-th curve is bounded by `Cz`
  have hRHS : ∀ (k : ℕ) (s : ℝ), s ∈ Set.Icc 0 τ →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) z θ) ≤ Cz := by
    intro k s hs
    obtain ⟨hsm, hmem8, hbd8⟩ := hFeps (slice (iter (Feps α ρ ε Φs E) g₀ k) s) (hP k s hs)
    have h1 := hCperz α hα hsm hmem8 z hz
    have h2 : (1 + Work.Spaces.HkNorm α 8
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s))) ^ 2
        ≤ (1 + Ce') ^ 2 := by
      have hXn : 0 ≤ Work.Spaces.HkNorm α 8
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) :=
        HkNorm_nonneg α 8 _
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) z θ)
        ≤ Cperz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.Spaces.HkNorm α 8
                (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s))) ^ 2 := h1
      _ ≤ Cperz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cz := by rw [hCzdef]
  -- (2) the primitive of the right-hand side has an honest angular energy at `z`, `≤ τ² Cz`
  have hprim : ∀ k : ℕ,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 6
          (fun z θ => ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) z θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) z θ)
        ≤ τ ^ 2 * Cz := by
    intro k
    exact Work.FTS.EpsEngine.PerzPrim.intervalIntegral_perz_le (α := α) (k := 6) (T := τ)
      (τ := τ) (Cz := Cz) (z := z)
      (H := fun s z θ => Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ)
      hτ ⟨hτ, le_rfl⟩ hτ
      (fun s hs => (hdat k).smo s hs)
      (fun s hs => (hdat k).mem s hs)
      (fun j i hji z' θ' hzθ => (hdat k).meas j i hji z' θ' hzθ)
      (fun K hK hKQ => (hdat k).sup K hK hKQ)
      (fun s hs => hRHS k s hs) hCzpos.le hz
  -- (3) `g₀` is smooth on the open quadrant
  have hg0sm : Work.FTS.EllipticEst.SmoothOpen g₀ := by
    have h := (hP 0 τ ⟨hτ, le_rfl⟩).smoothOpen
    rwa [show slice (iter (Feps α ρ ε Φs E) g₀ 0) τ = g₀ from by funext z θ; rfl] at h
  -- (4) the bound for every iterate
  intro n
  cases n with
  | zero =>
    have hslice0 : slice (iter (Feps α ρ ε Φs E) g₀ 0) τ = g₀ := by
      funext z θ; rfl
    rw [hslice0]
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g₀ z θ) ≤ max Bz0 0 :=
      le_trans hBz0 (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ τ ^ 2 * Cz := mul_nonneg (sq_nonneg τ) hCzpos.le
    have h3 : (0 : ℝ) ≤ max Bz0 0 := le_max_right _ _
    linarith
  | succ k =>
    have heq : slice (iter (Feps α ρ ε Φs E) g₀ (k + 1)) τ
        = fun z θ => g₀ z θ + ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
      rfl
    rw [heq]
    have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => ∫ s in (0 : ℝ)..τ,
        Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) :=
      smoothOpen_increment hg0sm (hP (k + 1) τ ⟨hτ, le_rfl⟩).smoothOpen
    have hmain := Work.FTS.EpsEngine.PerzPrim.integral_HkIntegrand_add_le (α := α) (k := 6)
      (f := g₀) (g := fun z θ => ∫ s in (0 : ℝ)..τ,
        Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ)
      hg0sm hQsm hz (B := max Bz0 0) (b := τ ^ 2 * Cz)
      (le_trans hBz0 (le_max_left _ _)) (le_max_right _ _) (hprim k).1 (hprim k).2
      (mul_nonneg (sq_nonneg τ) hCzpos.le)
    exact le_trans hmain (by linarith)

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.FlowOfXBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Flow5Leaves/FlowOfXBall.lean` — OPEN LEAF-A `epsFlowP_of_xball` (producer of `EpsFlowP`)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §2, §4.3; REVIEW (a), F4).  TRUE at
fixed `ε` (constants may depend on `ε`, `R`, the packages and the solution).

Route: `Feps w = P₀ J_ε profRHS(P₀ J_ε w)`.
* `rhs`, `rhsBdd`: `EpsEngine.Feps_data_of_xball8` (`SmoothOpen`, `HkMem 8`, `HkNorm 8 ≤ Ce8` on the
  `XBall`) + monotonicity to level 6.
* `wp`: `epsWP τ = profRHS(W)`, `XDataClean` gives `HkMem 4`, lifted by `HkMem_Jeps`.
* `rhsCont`: `Feps u − Feps v = Pz(J_ε Δ)` (`Jeps_sub_eq`, `Pz_sub_eq`, `L12_sub_HkMem`); the
  pre-mollified bound `EpsMem Δ ∧ EpsSq Δ ≤ K·EpsSq(u−v)` is inside `ConjTwoSq` (lines 115–152:
  `DeltaXnBound`, `DiffTraces`, `TraceToEpsMem`) — expose it as `ConjTwoSq_pre`; then
  `HkSq_JepsPz_le` at k = 6, plus the curve's `EpsSq`-Lipschitz bound.
* curve `EpsSq`-Lipschitz: Volterra identity by FTC (continuity of `τ ↦ epsRHSP τ z θ` from
  `WeakRHS.continuousOn_epsRHSP_joint`), then `EpsSq_intervalIntegral_le_gen` with the `hbd` of
  `EpsRHSPLipX_Sq`.
* `deriv`: `rem = ∫_τ^s (Feps g_r − Feps g_τ) dr` priced by `HkMem_intervalIntegralPerz`, gates from
  `Feps_gates_six`/`perz_Feps_six`.  Cautions: (i) that lemma quantifies over the whole window, so
  apply it to the reparametrised family `r ↦ H(τ+r)` on `[0, s−τ]` (symmetrically for `s < τ`);
  (ii) the joint measurability is needed for the DIFFERENCE family — expose the slot-level `hjoint`
  inside `hjoint_HkIntegrand_epsRHSP_fam_of_gate`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr
open Work.FTS.StrongEps.EpsE4Thr.E4R4 (rawE6 IP6o)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **OPEN LEAF-A (producer): a regular solution whose slices stay in a fixed `X`-ball carries
`EpsFlowP`** (at fixed `ε`, with the packages and `MuLamOK` at the ball radius `C₁`).  See the
module docstring for the route.  No `ε`-uniformity is claimed. -/
theorem epsFlowP_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {h₀ : Fn} {g : Fam}
    (hα : α ∈ Ioc (0 : ℝ) 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : IsEpsSolP α ρ ε δ Φs E h₀ g) (hreg : EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (slice g τ)) :
    EpsFlowP α ρ ε δ Φs E g :=
  Work.FTS.StrongEps.EpsE4Thr.Leaves.epsFlowP_of_xball hα hρ hε hε1 hR hEll hstar hml hδ hsol
    hreg hX

end Work.FTS.StrongEps.EpsE4Thr.E4R5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.exists_limG_core =====
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

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E5 with the `StarCore` hypothesis** — the frozen leaf `exists_limG` with
`StarPkgo2 α Cs Φs` replaced by `StarCore α Cs Φs` and `0 < Cs` added. -/
theorem exists_limG_core {C₀ Ce Cs : ℝ} : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    EllLimOK3 α E → Work.FTS.VocabO2.StarCore α Cs Φs → 0 < Cs → MuLamOK α C₀ Φs E →
    EpsUniformMem α ρ Φs E g₀ C₀ K → ExistsLimG α C₀ K Φs E g₀ := by
  classical
  obtain ⟨α₀, C3, Cpow, hα₀pos, hC3pos, hCpow, hL3all⟩ :=
    Work.FTS.StrongPersist.L3Data_exists
  set α₂ : ℝ := min (α₀ / 2) (1 / 8) with hα₂def
  have hα₂pos : 0 < α₂ := lt_min (by linarith) (by norm_num)
  have hα₂half : α₂ ≤ α₀ / 2 := min_le_left _ _
  have hα₂eight : α₂ ≤ 1 / 8 := min_le_right _ _
  refine ⟨α₂, hα₂pos, ?_⟩
  intro α hα K ρ Φs E g₀ hρ hEll hELL3 hcore hCs hml hU
  -- the inner thresholds (strictly above the leaf's `α₂`)
  have hα₀' : α < α₀ := lt_of_le_of_lt (le_trans hα.2 hα₂half) (by linarith)
  have hαquarter : α < 1 / 4 := lt_of_le_of_lt (le_trans hα.2 hα₂eight) (by norm_num)
  set α₂' : ℝ := min α₀ (1 / 4) with hα₂'def
  have hα₂'pos : 0 < α₂' := lt_min hα₀pos (by norm_num)
  have hα₂'quarter : α₂' ≤ 1 / 4 := min_le_right _ _
  have hα_lt : α < α₂' := lt_min hα₀' hαquarter
  have hL3 : Work.FTS.StrongPersist.L3Data α₂' Ce C3 Cpow :=
    { pos := ⟨hC3pos, hα₂'pos, hCpow⟩
      lin := fun β hβ f hf =>
        (hL3all Ce).lin β ⟨hβ.1, le_trans hβ.2 (min_le_left _ _)⟩ f hf
      rhs := fun β hβ E' Φs' Φ f Cs' μ lam M hell hadm hXn hmu hlam =>
        (hL3all Ce).rhs β ⟨hβ.1, le_trans hβ.2 (min_le_left _ _)⟩
          E' Φs' Φ f Cs' μ lam M hell hadm hXn hmu hlam }
  exact ExistsLimG_of_core (α₂ := α₂') (α₄ := (α + α₂') / 2)
    hα₂'pos hα₂'quarter ⟨hα.1, le_of_lt hα_lt⟩ (by linarith) (by linarith)
    hL3 hρ hEll hELL3 hcore hCs hml hU

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


/-- **The slice `θ ↦ (E g) z θ` is continuous on `[0,π/2]`**: on the open interval by
`SmoothOpen`, at the endpoints because the prescribed (junk) values `0` are the one-sided
limits (`BoxAux.tendsto_Eg_at_zero`, `BoxAux.tendsto_Eg_at_pi_half`). -/
theorem sliceContinuousOn {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {E : Fn →ₗ[ℝ] Fn}
    (hE : Ctx α Ce E) {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => (E g) z θ) (Set.Icc 0 (π / 2)) := by
  have hSsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hcontIoo : ContinuousOn (fun θ => (E g) z θ) (Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ hSsm hz).continuousOn
  have hval0 : (E g) z 0 = 0 := (hE g hg).1.1.2.1 z
  have hval1 : (E g) z (π / 2) = 0 := (hE g hg).1.1.2.2.1 z
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hIci : ContinuousWithinAt (fun θ => (E g) z θ) (Set.Ici 0) 0 := by
      rw [← continuousWithinAt_Ioi_iff_Ici]
      show Tendsto (fun θ => (E g) z θ) (𝓝[Set.Ioi 0] 0) (𝓝 ((E g) z 0))
      rw [hval0]
      exact Work.FTS_EllLimOK.ProducerH.BoxAux.tendsto_Eg_at_zero hα hα4 hE hg hz
    have hmem : Set.Ici (0 : ℝ) ∈ 𝓝[Set.Icc 0 (π / 2)] 0 := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Set.Ioo (-1) (π / 2 + 1), ?_, ?_⟩
      · exact Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < π / 2 + 1 by linarith [Real.pi_pos])
      · intro x hx
        exact hx.2.1
    exact ContinuousWithinAt.mono_of_mem_nhdsWithin (s := Set.Icc 0 (π / 2))
      (t := Set.Ici 0) hIci hmem
  · rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      have hIic : ContinuousWithinAt (fun θ => (E g) z θ) (Set.Iic (π / 2)) (π / 2) := by
        rw [← continuousWithinAt_Iio_iff_Iic]
        show Tendsto (fun θ => (E g) z θ) (𝓝[Set.Iio (π / 2)] (π / 2)) (𝓝 ((E g) z (π / 2)))
        rw [hval1]
        exact Work.FTS_EllLimOK.ProducerH.BoxAux.tendsto_Eg_at_pi_half hα hα4 hE hg hz
      have hmem : Set.Iic (π / 2) ∈ 𝓝[Set.Icc 0 (π / 2)] (π / 2) := by
        refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
          ⟨Set.Ioo (-1) (π / 2 + 1), ?_, ?_⟩
        · exact Ioo_mem_nhds (show (-1 : ℝ) < π / 2 by linarith [Real.pi_pos])
            (show (π / 2) < π / 2 + 1 by linarith)
        · intro x hx
          exact hx.2.2
      exact ContinuousWithinAt.mono_of_mem_nhdsWithin (s := Set.Icc 0 (π / 2))
        (t := Set.Iic (π / 2)) hIic hmem
    · exact ((hcontIoo.continuousWithinAt ⟨h0, hp⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨h0, hp⟩)).continuousWithinAt

end Work.FTS_EllLimOK.ProducerH.H2
end
end

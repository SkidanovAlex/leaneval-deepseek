import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.epsSqLip_of_xball
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkDerivWithin_of_xball
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsSqTools.Pointwise
import Submission.Work.FTS.StrongEps.H5.HkMemXnN5
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.AKSlot
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
-- ===== merged: Submission.Work.FTS.EpsEngine.perz_iter_feps_le =====
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

theorem perz_iter_feps_le {α C₀ Ce Cs R Lw ε τ : ℝ} {ρ : ℝ × ℝ → ℝ}
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
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g₀ z θ) ≤ Bz) :
    ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter (Work.FTS.EpsEngine.Feps α ρ ε Φs E) g₀ n) τ)
        z θ) ≤ Bz := by
  -- the per-curve right-hand-side data, uniform in the Picard index
  obtain ⟨B, _hBpos, hdata⟩ :=
    exists_RHSData_feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hτ hEll hstar hml
  have hdat : ∀ k : ℕ, RHSData α 4 τ B (Feps α ρ ε Φs E) g₀ k :=
    fun k => hdata k (fun s hs => hP k s hs) (fun s hs t ht => hEq k s hs t ht)
  -- the uniform `ℋ⁶`-size of the right-hand side
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  -- the trace-free per-`z` bound for `ℋ⁶`-profiles
  obtain ⟨Cperz, hCperzpos, hCperz⟩ := HkIntegrand_perz_le_noTraces
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
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) z θ) ≤ Cz := by
    intro k s hs
    obtain ⟨hsm, hmem6, hbd6⟩ := hFeps (slice (iter (Feps α ρ ε Φs E) g₀ k) s) (hP k s hs)
    have h1 := hCperz α _ hα hsm hmem6 z hz
    have h2 : (1 + Work.FTS.StrongGlobal.Xn6 α
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s))) ^ 2
        ≤ (1 + Ce') ^ 2 := by
      have hXn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) :=
        HkNorm_nonneg α 6 _
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s)) z θ)
        ≤ Cperz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α
                (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s))) ^ 2 := h1
      _ ≤ Cperz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cz := by rw [hCzdef]
  -- (2) the primitive of the right-hand side has an honest angular energy at `z`, `≤ τ² Cz`
  have hprim : ∀ k : ℕ,
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 4
          (fun z θ => ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) z θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ) z θ)
        ≤ τ ^ 2 * Cz := by
    intro k
    exact Work.FTS.EpsEngine.PerzPrim.intervalIntegral_perz_le (α := α) (k := 4) (T := τ)
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
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g₀ z θ) ≤ max Bz0 0 :=
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
    have hmain := Work.FTS.EpsEngine.PerzPrim.integral_HkIntegrand_add_le (α := α) (k := 4)
      (f := g₀) (g := fun z θ => ∫ s in (0 : ℝ)..τ,
        Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ k) s) z θ)
      hg0sm hQsm hz (B := max Bz0 0) (b := τ ^ 2 * Cz)
      (le_trans hBz0 (le_max_left _ _)) (le_max_right _ _) (hprim k).1 (hprim k).2
      (mul_nonneg (sq_nonneg τ) hCzpos.le)
    exact le_trans hmain (by linarith)

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.ExistsLimG_of_core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem ExistsLimG_of_core {α₂ α₄ α C₀ K Ce Cs C3 Cpow : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1 / 4) (hα : α ∈ Set.Ioc (0 : ℝ) α₂)
    (hα₄ : α < α₄) (hα₄2 : α₄ ≤ α₂)
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E) (hcore : Work.FTS.VocabO2.StarCore α Cs Φs)
    (hCs : 0 < Cs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hU : Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K) :
    Work.FTS.StrongEps.ExistsLimG α C₀ K Φs E g₀ := by
  -- ## the two star packages are *derived* from `StarCore`: the level-four package
  -- (`StarPkgo2OfCore`) and the level-six package (`StarPkg6OfCore`), each at a constant
  -- multiple of `Cs`, the constants being universal (the `α ≤ 1/4` range is what licenses
  -- them, and `α ∈ Ioc 0 α₂`, `α₂ ≤ 1/4` give it).
  obtain ⟨C₁, _hC₁, hP⟩ := Work.FTS.PhiStar.StarPkgo2OfCore
  obtain ⟨C₂, _hC₂, hP6⟩ := Work.FTS.StrongPersist.StarPkg6OfCore
  have hα0 : 0 < α := hα.1
  have hα14 : α ≤ 1 / 4 := le_trans hα.2 hα₂1
  exact ExistsLimG_assembly (Cs := C₁ * Cs) (Cs6 := C₂ * Cs)
    hα₂ hα₂1 hα hα₄ hα₄2 hL3 hρ hEll hELL3
    (hP α Cs Φs hα0 hα14 hCs hcore) (hP6 α Cs Φs hα0 hα14 hCs hcore) hml hU

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.epsFlowP_of_xball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/Leaves/epsFlowP_of_xball.lean` — LEAF-A, the flow-regularity producer

The five fields of `EpsFlowP α ρ ε δ Φs E g` for a regular solution of the projected `ε`-scheme
whose slices stay in the `X`-ball at a fixed radius:

* `rhs`/`rhsBdd`/`wp` — from the profile-level data `Feps_data_of_xball` (`rhs`, `rhsBdd`) and
  `XDataClean` + `HkMem_Jeps` (`wp`); proved here as `rhs_data_of_xball`;
* `rhsCont` — the `ℋ⁶`-continuity of the right-hand side along the curve; proved here as
  `hkContWithin_of_xball` from the `ℋ⁶`-Lipschitz bound `hkSqFepsSub_le` and the `EpsSq`-Lipschitz
  bound `epsSqLip_of_xball` of the curve;
* `deriv` — the `ℋ⁶`-differentiability of the flow, proved as
  `FlowBits.hkDerivWithin_of_xball` from the pointwise Volterra identity `volterra_of_xball`,
  `epsSqLip_of_xball` and the continuity of the right-hand side.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `rhs`, `rhsBdd` and `wp` clauses -/

/-- **The `rhs`/`rhsBdd`/`wp` clauses of `EpsFlowP`** from the `X`-ball data of the slices.

`epsRHSP α ρ ε Φs E g τ = Feps α ρ ε Φs E (slice g τ)` is `SmoothOpen`, `ℋ⁶`-honest and of
`ℋ⁶`-size at most the profile-level constant `Ce'` of `Feps_data_of_xball` (uniform in `τ`), and
the un-projected mollified pre-right-hand side `J_ε (epsWP … τ)` is `ℋ⁴`-honest — the profile
`W = Wp ρ ε (slice g τ)` is `ℋ⁶`-bounded by `exists_Wp_bound_of_EpsMem`, `XDataClean` makes
`profRHS α Φs E W` `ℋ⁴`-honest, and the mollifier preserves `ℋ⁴` (`HkMem_Jeps`). -/
theorem rhs_data_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {h₀ : Fn} {g : Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (slice g τ)) :
    (∀ τ ∈ Set.Icc 0 δ, Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) ∧
    (∃ B : ℝ,
      ∀ τ ∈ Set.Icc 0 δ, Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) ≤ B) ∧
    (∀ τ ∈ Set.Icc 0 δ,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ))) := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Work.FTS.EpsEngine.Feps_data_of_xball (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs) (R := R)
      (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  obtain ⟨CW, hCWpos, hWp⟩ := Work.FTS.StrongEps.EpsLocalPStar.exists_Wp_bound_of_EpsMem ρ hρ
  set BW : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBWdef
  have hBW0 : 0 ≤ BW := by
    rw [hBWdef]
    have hr : 0 ≤ CW / ε := div_nonneg hCWpos.le hε.le
    positivity
  obtain ⟨RX, hRXpos, hXd⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₁) (B := BW)
      (Φs := Φs) (E := E) hα hEll hstar hml hBW0
  refine ⟨?_, ⟨Ce', ?_⟩, ?_⟩
  · intro τ hτ
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice]
    exact ⟨(hFeps _ (hX τ hτ)).1, (hFeps _ (hX τ hτ)).2.1⟩
  · intro τ hτ
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice]
    exact (hFeps _ (hX τ hτ)).2.2
  · intro τ hτ
    have hW : Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε (slice g τ)) ≤ BW := by
      have h := hWp α hα ε ⟨hε, hε1⟩ R hR (slice g τ) (hX τ hτ).smoothOpen (hX τ hτ).mem
        (hX τ hτ).sq_le 6 le_rfl
      rw [hBWdef]
      exact h
    obtain ⟨hsm, hmem4, -⟩ :=
      hXd (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε (slice g τ)) (hX τ hτ).classC (hX τ hτ).ball hW
    have hsm' : ∀ n : ℕ,
        ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε (slice g τ)))) Work.FTS.StrongEps.Quad :=
      fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm n
    have hmemJ := Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsm' hmem4
    rw [Work.FTS.StrongEps.EpsE4Thr.epsWP_eq_profRHS]
    exact hmemJ

/-! ## The `rhsCont` clause -/

/-- **The `ℋ⁶`-continuity of the scheme's right-hand side along the curve.**  The right-hand side
at the fake time `s` is `Feps α ρ ε Φs E (slice g s)`, so the `ℋ⁶`-Lipschitz bound
`HkSq α 6 (Feps u − Feps v) ≤ Cl · EpsSq (u − v)` on the `X`-ball and the `EpsSq`-Lipschitz bound
`EpsSq (slice s − slice τ) ≤ Lw (s−τ)²` of the curve give
`HkNorm α 6 (…s − …τ) ≤ √(Cl Lw) |s − τ|`; the `HQo α 6` clause of the difference is
`smoothOpen_subP` + `HkMem_sub_open`. -/
theorem hkContWithin_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {h₀ : Fn} {g : Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (slice g τ))
    {Cl : ℝ} (hCl : 0 ≤ Cl)
    (hLip : ∀ u v : Fn, Work.FTS.EpsEngine.XBall α ρ ε R C₁ u →
      Work.FTS.EpsEngine.XBall α ρ ε R C₁ v →
      Work.Spaces.HkSq α 6 (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ Cl * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    {Lw : ℝ} (hLw : 0 ≤ Lw)
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => slice g s z θ - slice g t z θ) ≤ Lw * (s - t) ^ 2) :
    ∀ τ ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsE4Thr.E4R5.HkContWithin α 6
      (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g) (Set.Icc 0 δ) τ := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Work.FTS.EpsEngine.Feps_data_of_xball (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs) (R := R)
      (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  intro τ hτ η hη
  have hlr : ∀ s ∈ Set.Icc 0 δ,
      (fun z θ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ
          - Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ z θ)
        = fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g τ) z θ := by
    intro s hs
    funext z θ
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E g s,
      Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E g τ]
  by_cases hz : Cl * Lw = 0
  · -- the degenerate case: the difference is `ℋ⁶`-small with constant zero
    refine ⟨1, one_pos, fun s hs _ => ?_⟩
    rw [hlr s hs]
    have h1 := hLip (slice g s) (slice g τ) (hX s hs) (hX τ hτ)
    have h2 := hEq s hs τ hτ
    have hSq0 : Work.Spaces.HkSq α 6 (fun z θ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g τ) z θ) ≤ 0 := by
      refine le_trans h1 ?_
      calc Cl * Work.FTS.StrongEps.EpsSq α (fun z θ => slice g s z θ - slice g τ z θ)
          ≤ Cl * (Lw * (s - τ) ^ 2) := mul_le_mul_of_nonneg_left h2 hCl
        _ = (Cl * Lw) * (s - τ) ^ 2 := by ring
        _ = 0 := by rw [hz, zero_mul]
    constructor
    · exact ⟨Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP (hFeps _ (hX s hs)).1
          (hFeps _ (hX τ hτ)).1,
        Work.FTS.EllipticEst.HkMem_sub_open (hFeps _ (hX s hs)).1 (hFeps _ (hX τ hτ)).1
          (hFeps _ (hX s hs)).2.1 (hFeps _ (hX τ hτ)).2.1⟩
    · rw [Work.Spaces.HkNorm]
      have h0 : Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g τ) z θ)) = 0 :=
        Real.sqrt_eq_zero_of_nonpos hSq0
      rw [h0]
      linarith
  · have hCLpos : 0 < Cl * Lw := lt_of_le_of_ne (mul_nonneg hCl hLw) (Ne.symm hz)
    have hsqpos : 0 < Real.sqrt (Cl * Lw) := Real.sqrt_pos.mpr hCLpos
    refine ⟨η / Real.sqrt (Cl * Lw), div_pos hη hsqpos, fun s hs hsd => ?_⟩
    rw [hlr s hs]
    have h1 := hLip (slice g s) (slice g τ) (hX s hs) (hX τ hτ)
    have h2 := hEq s hs τ hτ
    constructor
    · exact ⟨Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP (hFeps _ (hX s hs)).1
          (hFeps _ (hX τ hτ)).1,
        Work.FTS.EllipticEst.HkMem_sub_open (hFeps _ (hX s hs)).1 (hFeps _ (hX τ hτ)).1
          (hFeps _ (hX s hs)).2.1 (hFeps _ (hX τ hτ)).2.1⟩
    · rw [Work.Spaces.HkNorm]
      have hSq : Work.Spaces.HkSq α 6 (fun z θ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g τ) z θ)
          ≤ Cl * (Lw * (s - τ) ^ 2) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 hCl)
      have hsqrt : Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ =>
            Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ
              - Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g τ) z θ))
          ≤ Real.sqrt (Cl * Lw) * |s - τ| := by
        refine le_trans (Real.sqrt_le_sqrt hSq) ?_
        rw [show Cl * (Lw * (s - τ) ^ 2) = (Cl * Lw) * (s - τ) ^ 2 by ring,
          Real.sqrt_mul (mul_nonneg hCl hLw) ((s - τ) ^ 2), Real.sqrt_sq_eq_abs]
      refine le_trans hsqrt ?_
      have hcalc : Real.sqrt (Cl * Lw) * (η / Real.sqrt (Cl * Lw)) = η := by
        field_simp
      rw [← hcalc]
      exact le_of_lt (mul_lt_mul_of_pos_left hsd hsqpos)

/-! ## The target -/

theorem epsFlowP_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ)) :
    Work.FTS.StrongEps.EpsE4Thr.E4R5.EpsFlowP α ρ ε δ Φs E g := by
  obtain ⟨Lw, hLwpos, hEq⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.epsSqLip_of_xball (α := α) (C₁ := C₁) (Ce := Ce)
      (Cs := Cs) (R := R) (ε := ε) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀) (g := g)
      hα hρ hε hε1 hR hEll hstar hml hδ hsol hreg hX
  have hvol :=
    Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.volterra_of_xball (α := α) (C₁ := C₁) (Ce := Ce)
      (Cs := Cs) (R := R) (ε := ε) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀) (g := g)
      hα hρ hε hε1 hR hEll hstar hml hδ hsol hreg hX
  obtain ⟨Cl, hClpos, hLip⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le (α := α) (C₁ := C₁) (Ce := Ce)
      (Cs := Cs) (R := R) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hR hEll hstar hml
  obtain ⟨hrhs, hrhsBdd, hwp⟩ :=
    rhs_data_of_xball (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε) (δ := δ)
      (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀) (g := g) hα hρ hε hε1 hR hEll hstar hml hreg hX
  have hcont :=
    hkContWithin_of_xball (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε) (δ := δ)
      (ρ := ρ) (Φs := Φs) (E := E) (h₀ := h₀) (g := g) hα hρ hε hε1 hR hEll hstar hml hδ hreg hX
      hClpos.le hLip hLwpos.le hEq
  have hderiv :=
    Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkDerivWithin_of_xball (α := α) (C₁ := C₁)
      (Ce := Ce) (Cs := Cs) (R := R) (ε := ε) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E)
      (h₀ := h₀) (g := g) hα hρ hε hε1 hR hEll hstar hml hδ hreg hX hvol (Lw := Lw) hLwpos.le hEq
      hcont
  exact ⟨hrhs, hrhsBdd, hcont, hderiv, hwp⟩

end Work.FTS.StrongEps.EpsE4Thr.Leaves
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_helpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.ProducerH.pkgMemSqH_helpers`

Elementary helpers for the producer `pkgMemSqH_of_ellClassOk` (the `L2` field `PkgMemSqH` of
`RulingELF.ProducerH`): monotonicity of `SlotBd`, the level-`0` `ℋ`-integrand in factored form,
the pointwise domination of `HkIntegrand α 0` under sums and under division by `cos θ`,
homogeneity, and the scaling limit `t² S ≤ C(1+tX)² ∀ t > 0 ⟹ S ≤ C X²` together with the two
arithmetic bookkeeping lemmas used in the assembly.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `SlotBd` and the level-`0` integrand -/

/-- `SlotBd` is monotone in the bound. -/
theorem SlotBd_mono {α : ℝ} {Φ : Fn} {M M' : ℝ} (h : Work.FTS.StreamBdryIface.SlotBd α Φ M)
    (hMM' : M ≤ M') : Work.FTS.StreamBdryIface.SlotBd α Φ M' := by
  intro z θ hz
  obtain ⟨h1, h2, h3⟩ := h z θ hz
  exact ⟨fun j hj => le_trans (h1 j hj) hMM', le_trans h2 hMM', fun j hj => le_trans (h3 j hj) hMM'⟩

/-- The level-`0` integrand is the square of one explicit factor. -/
theorem HkIntegrand_zero_factor (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
  Work.FTS_EllLimOK.HkIntegrand_zero_eq α f z θ

/-- Pointwise: `HkIntegrand α 0 (a+b) ≤ 2 HkIntegrand α 0 a + 2 HkIntegrand α 0 b`. -/
theorem HkIntegrand_zero_add_le (α : ℝ) (a b : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ + b z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ := by
  rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor, HkIntegrand_zero_factor]
  set c : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hc
  nlinarith [sq_nonneg ((a z θ + b z θ) * c), sq_nonneg ((a z θ - b z θ) * c),
    sq_nonneg (a z θ * c), sq_nonneg (b z θ * c)]

/-- Pointwise: dividing by `cos θ` does not decrease the level-`0` integrand. -/
theorem HkIntegrand_zero_le_cosDiv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => F z θ / Real.cos θ) z θ := by
  rcases eq_or_ne (Real.cos θ) 0 with hc | hc
  · have hsin : Real.sin (2 * θ) = 0 := by rw [Real.sin_two_mul, hc, mul_zero]
    have hc0 : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hsin, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
    rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor, hc0]
    simp
  · have hcos2 : (Real.cos θ) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
    rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor]
    have h1 : (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((F z θ / Real.cos θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          * (Real.cos θ) ^ 2 := by
      field_simp
    rw [h1]
    exact mul_le_of_le_one_right (sq_nonneg _) hcos2

/-- Pointwise: the level-`0` integrand is homogeneous of degree `2`. -/
theorem HkIntegrand_zero_smul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (c • f) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 f z θ := by
  rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The level-`0` slice integral is homogeneous of degree `2`. -/
theorem integral_HkIntegrand_zero_smul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (c • f) z θ)
      = c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    simp only [HkIntegrand_zero_smul])

/-! ## Scaling and arithmetic -/

/-- Scaling: from `t^2 * S ≤ C * (1 + t*X)^2` for all `t > 0`, conclude `S ≤ C * X^2`. -/
theorem scale_limit {C S X : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ^ 2 * S ≤ C * (1 + t * X) ^ 2) :
    S ≤ C * X ^ 2 := by
  have hnat : ∀ n : ℕ, S ≤ C * (1 / ((n : ℝ) + 1) + X) ^ 2 := by
    intro n
    have ht : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := h _ ht
    have h2 : ((1 : ℝ) / ((n : ℝ) + 1) + X) = (1 + ((n : ℝ) + 1) * X) / ((n : ℝ) + 1) := by
      field_simp
    rw [h2, div_pow, show C * ((1 + ((n : ℝ) + 1) * X) ^ 2 / ((n : ℝ) + 1) ^ 2)
        = (C * (1 + ((n : ℝ) + 1) * X) ^ 2) / ((n : ℝ) + 1) ^ 2 from by ring]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)).mpr (by nlinarith [h1])
  have hlim : Filter.Tendsto
      (fun n : ℕ => C * (1 / ((n : ℝ) + 1) + X) ^ 2) Filter.atTop (𝓝 (C * X ^ 2)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) + X) Filter.atTop (𝓝 (0 + X)) :=
      h1.add tendsto_const_nhds
    have h3 : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1) + X) ^ 2) Filter.atTop
        (𝓝 ((0 + X) ^ 2)) := h2.pow 2
    have h4 := h3.const_mul C
    simpa using h4
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hnat

/-- Arithmetic: `s ≤ CC * (1 + X)^2` from the two per-piece bounds. -/
theorem norm_arith {CC CB CT Ce X s : ℝ} (hCB : 0 ≤ CB) (hCT : 0 ≤ CT) (hX : 0 ≤ X)
    (h1 : s ≤ 2 * (CB * (Ce * X) ^ 2) + 2 * (CT * (1 + X) ^ 2))
    (hCC : 2 * CB * Ce ^ 2 + 2 * CT ≤ CC) : s ≤ CC * (1 + X) ^ 2 := by
  have hX1 : 0 ≤ (1 + X) ^ 2 := by positivity
  have h2 : (Ce * X) ^ 2 ≤ Ce ^ 2 * (1 + X) ^ 2 := by
    nlinarith [sq_nonneg Ce, sq_nonneg X, hX, sq_nonneg (1 + X)]
  have hmul : CB * (Ce * X) ^ 2 ≤ CB * (Ce ^ 2 * (1 + X) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hCB
  have hfac : 2 * (CB * (Ce ^ 2 * (1 + X) ^ 2)) + 2 * (CT * (1 + X) ^ 2)
      = (2 * CB * Ce ^ 2 + 2 * CT) * (1 + X) ^ 2 := by ring
  have hsum : 2 * (CB * (Ce * X) ^ 2) + 2 * (CT * (1 + X) ^ 2)
      ≤ (2 * CB * Ce ^ 2 + 2 * CT) * (1 + X) ^ 2 := by
    rw [← hfac]; linarith [hmul]
  exact le_trans (le_trans h1 hsum) (mul_le_mul_of_nonneg_right hCC hX1)

/-- Arithmetic: the per-slice combination. -/
theorem slice_arith {CC CB CS K Ce X z a b M2 U2 : ℝ}
    (hCB : 0 ≤ CB) (hCS : 0 ≤ CS) (hz : 0 < z) (hX : 0 ≤ X)
    (h1 : a ≤ CB * (1 + 1 / z) * (M2 + U2))
    (h2 : b ≤ CS * (1 + 1 / z) * X ^ 2)
    (hM2 : M2 ≤ K ^ 2 * Ce ^ 2 * (1 + X) ^ 2)
    (hU2 : U2 ≤ Ce ^ 2 * (1 + X) ^ 2)
    (hCC : 2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS ≤ CC) :
    2 * a + 2 * b ≤ CC * (1 + 1 / z) * (1 + X) ^ 2 := by
  have hcoef : 0 ≤ 1 + 1 / z := by positivity
  have hX1 : 0 ≤ (1 + X) ^ 2 := by positivity
  have hX2 : X ^ 2 ≤ (1 + X) ^ 2 := by nlinarith [hX]
  have hMU : M2 + U2 ≤ (K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2 := by
    have e : K ^ 2 * Ce ^ 2 * (1 + X) ^ 2 + Ce ^ 2 * (1 + X) ^ 2
        = (K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2 := by ring
    linarith [hM2, hU2, e]
  have hC1 : CB * (1 + 1 / z) * (M2 + U2)
      ≤ CB * (1 + 1 / z) * ((K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2) := by
    have h0 : 0 ≤ CB * (1 + 1 / z) := mul_nonneg hCB hcoef
    exact mul_le_mul_of_nonneg_left hMU h0
  have hC2 : CS * (1 + 1 / z) * X ^ 2 ≤ CS * (1 + 1 / z) * (1 + X) ^ 2 := by
    have h0 : 0 ≤ CS * (1 + 1 / z) := mul_nonneg hCS hcoef
    exact mul_le_mul_of_nonneg_left hX2 h0
  calc 2 * a + 2 * b
      ≤ 2 * (CB * (1 + 1 / z) * (M2 + U2)) + 2 * (CS * (1 + 1 / z) * X ^ 2) := by linarith
    _ ≤ 2 * (CB * (1 + 1 / z) * ((K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2))
          + 2 * (CS * (1 + 1 / z) * (1 + X) ^ 2) := by linarith [hC1, hC2]
    _ = (2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS) * (1 + 1 / z) * (1 + X) ^ 2 := by ring
    _ ≤ CC * (1 + 1 / z) * (1 + X) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hcoef) hX1

end Work.FTS_EllLimOK.ProducerH
end
end

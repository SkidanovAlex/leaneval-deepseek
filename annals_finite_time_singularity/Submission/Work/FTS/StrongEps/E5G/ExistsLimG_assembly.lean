import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.HkMemLimFam
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.StrongEps.E5G.PkgOfHlim
import Submission.Work.FTS.StrongEps.E5G.hdbd_of_tower
import Submission.Work.FTS.StrongEps.E5G.hlim_slots_of_tower
import Submission.Work.FTS.StrongEps.E5G.morrey_five_slots
import Submission.Work.FTS.StrongEps.E5G.weak_slots_tendsto_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_shiftSing_eq_PhiTil_add
import Submission.Work.FTS_RegExport.Vz7Eslot
-- ===== merged: Submission.Work.FTS.EllSol.existsEllSolC_of_threshold =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.existsEllSolC_of_threshold` (curric-46 lead install, 2026-10-10)

Route (b) of `cbc/fts_final_redesign.md` §G5: `existsEllSolC_classC_of` with the hypothesis
"`EllClassOk 8` for all `α ≤ 1/4`" replaced by "for all `α ≤ α₁`, some `α₁ > 0`" — the shape
that A2 (`Work.FTS.ClassC.ellClassOk_exists_of_classC`) delivers. Same proof, threshold
`min α₀ α₁`. PROVED; does not use `vthTransfer_classC`.

`ExistsEllSolC` from A2 is then `existsEllSolC_of_threshold ClassC.ellClassOk_exists_of_classC`
(see `Submission.Work.FTS.FinalV2.WireSkeleton`, `existsEllSolC_routeB`).
-/

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsIncData =====
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

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.H4Feps =====
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

/-- **`(H4)(a)` for `Feps`, trace-free.**  If the `n`-th Picard curve of the projected scheme stays
in `XBall` and is `EpsSq`-Lipschitz in the fake time, then every raw Picard slice at `τ` is
`ℋ⁴`-honest, with `HkNorm α 4 ≤ HkNorm α 4 g₀ + B τ`. -/
theorem HkMem_iter_feps {α C₀ Ce Cs R Lw ε δ τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (h0smo : Work.FTS.EllipticEst.SmoothOpen g₀) (h0mem : Work.Spaces.HkMem α 4 g₀)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hτδ : τ ≤ δ)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (iter (Feps α ρ ε Φs E) g₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (iter (Feps α ρ ε Φs E) g₀ n) s z θ
          - slice (iter (Feps α ρ ε Φs E) g₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      Work.Spaces.HkMem α 4 (slice (iter (Feps α ρ ε Φs E) g₀ n) τ) ∧
      Work.Spaces.HkNorm α 4 (slice (iter (Feps α ρ ε Φs E) g₀ n) τ)
        ≤ Work.Spaces.HkNorm α 4 g₀ + B * τ := by
  obtain ⟨B, hBpos, hRH⟩ :=
    exists_RHSData_feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := δ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hδ hEll hstar hml
  refine ⟨B, hBpos, ?_⟩
  exact HkMem_iter_all (α := α) (B := B) (F := Feps α ρ ε Φs E) (h₀ := g₀) (k := 4)
    (T := δ) (τ := τ) hτ hτδ hδ hBpos.le h0smo h0mem
    (fun n => (hP n τ ⟨hτ, hτδ⟩).smoothOpen)
    (fun n => hRH n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht))

/-- **`(H4)(b)` for `Feps`, trace-free.**  The limit slice is `ℋ⁴`-honest, given the per-`z` bound
`hz` of the iterates (uniform in the Picard index) — which is *not* a trace condition. -/
theorem HkMem_epsLim_noTraces {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {g₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen g₀) (h₀mem : Work.Spaces.HkMem α 4 g₀)
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
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (slice (epsIter α ρ ε Φs E g₀ n) τ) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 (slice (epsLim α ρ ε Φs E g₀) τ) := by
  obtain ⟨B, hBpos, hRH⟩ :=
    exists_RHSData_feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := δ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hδ hEll hstar hml
  have hiter := HkMem_iter_all (α := α) (B := B)
    (F := Feps α ρ ε Φs E) (h₀ := g₀) (k := 4) (T := δ) (τ := τ)
    hτ.1 hτ.2 hδ hBpos.le h0 h₀mem
    (fun n => (hP n τ hτ).smoothOpen)
    (fun n => hRH n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht))
  have hbd : ∀ n : ℕ,
      Work.Spaces.HkNorm α 4 (slice (iter (Feps α ρ ε Φs E) g₀ n) τ)
        ≤ Work.Spaces.HkNorm α 4 g₀ + B * τ := fun n => (hiter n).2
  have hslot := tendsto_mixed_epsIter_limFam (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := g₀)
    hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hmoll hconv hτ
  have hsmf : Work.FTS.EllipticEst.SmoothOpen (slice (epsLim α ρ ε Φs E g₀) τ) :=
    smoothOpen_limFam_slice (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
      (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := g₀)
      hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hmoll hconv hτ
  exact (Work.FTS.EpsEngine.HkMem_limFam_of_slot_conv (α := α)
    (B := Work.Spaces.HkNorm α 4 g₀ + B * τ) (F := Feps α ρ ε Φs E) (h₀ := g₀) (k := 4)
    (τ := τ)
    (fun n => (hiter n).1) hbd
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hP n τ hτ).smoothOpen 4)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmf 4)
    (fun j i hji z θ hzq => hslot j i hji z θ hzq.1 hzq.2) hz).1

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem ExistsLimG_assembly {α₂ α₄ α C₀ K Ce Cs Cs6 C3 Cpow : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1 / 4) (hα : α ∈ Set.Ioc (0 : ℝ) α₂)
    (hα₄ : α < α₄) (hα₄2 : α₄ ≤ α₂)
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hU : Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K) :
    Work.FTS.StrongEps.ExistsLimG α C₀ K Φs E g₀ := by
  classical
  -- ## the parameter range
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := by linarith [hα.2, hα₄2, hα₂1]
  have hαI1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα0, hα1⟩
  have hα₄0 : 0 < α₄ := lt_trans hα0 hα₄
  have hα₄1 : α₄ ≤ 1 := by linarith [hα₄2, hα₂1]
  have hαIα₄ : α ∈ Set.Ioc (0 : ℝ) α₄ := ⟨hα0, le_of_lt hα₄⟩
  obtain ⟨hc₁, hc₂⟩ := Work.Spaces.c_bounds α hα0 hα1
  -- ## the datum clauses carried by the interface
  have hvan := hU.1
  have hL12g₀ := hU.2.1
  -- ## smoothness of `Φs` from the star package
  have hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φs).mp hstar.smooth 1
  -- ## the tower of `ε`-solutions, with the decay majorant
  obtain ⟨e, G, K', Maj, hεe, hε0, hMaj, hTD⟩ :=
    tower_exists_decay (α := α) (C₀ := C₀) (K := K) (ρ := ρ) (Φs := Φs) (E := E)
      (g₀ := g₀) hU
  have hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k) :=
    fun n k h => (hTD n k h).1
  have hDec : ∀ n k : ℕ, n ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n) :=
    fun n k h => (hTD n k h).2
  -- ## the nested extraction and the coherence of the horizons
  obtain ⟨ι, F, hιmono, hlow, hnest, hconv⟩ :=
    tower_extract (α := α) (C₀ := C₀) (K := K) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
      (E := E) (g₀ := g₀) (e := e) (G := G) (K' := K') hαI1 hρ hc₁ hc₂ hEll hstar hml
      hεe hTower
  have hcoh := tower_coherent (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
    (E := E) (g₀ := g₀) (e := e) (G := G) (K' := K') (ι := ι) (F := F)
    hαI1 hρ hEll hstar hml hεe hTower hιmono hlow hnest hconv
  -- ## the glue: one family carrying the package on every horizon
  refine ExistsLimG_of_horizon_pkgs (α := α) (C₀ := C₀) (K := K) (Φs := Φs) (E := E)
    (g₀ := g₀) (Tn := Tn) (F := F) Tn_pos Tn_mono ?_ ?_ ?_
  · -- the horizons cover every positive time
    intro T _hT
    refine ⟨Nat.ceil T, ?_⟩
    have h := Nat.le_ceil T
    simp only [Tn]
    linarith
  · -- coherence of the limit curves on the overlaps
    intro m n τ hτ z θ hzθ
    exact hcoh m n τ hτ z θ hzθ.1 hzθ.2
  · -- the per-horizon package
    intro N T hT hTN
    have hιN : StrictMono (ι N) := hιmono N
    have hadmN : ∀ k : ℕ, N ≤ ι N k := fun k => le_trans (Nat.le_add_right N k) (hlow N k)
    have hDecN : ∀ k : ℕ, N ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Tn N),
        EpsDecay α ρ Φs E (e k) τ (G N k) (Maj N) := fun k hk => hDec N k hk
    -- the slot convergence of the scheme's right-hand side along the tower
    have hslots := hlim_slots_of_tower (n := N) (T := T) (hα := hαI1) (hρ := hρ)
      (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hstar6 := hstar6)
      (hml := hml) (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe)
      (hε0 := hε0) (hTower := hTower) (hMaj := hMaj) (hDec := hDecN) (hι := hιN)
      (hadm := hadmN) (hconv := hconv N) (hT := hT) (hTT := hTN)
    -- the `ℋ³`-bound of `∂_τ` at the limit
    have hdbd := hdbd_of_tower (n := N) (hα₄ := hα₄0) (hα₄1 := hα₄1) (hα := hαIα₄)
      (hρ := hρ) (hL3 := hL3) (hα₂ := hα) (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll)
      (hstar := hstar) (hstar6 := hstar6) (hml := hml) (hELL3 := hELL3) (hsmΦ := hsmΦ)
      (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0) (hTower := hTower) (hMaj := hMaj)
      (hDec := hDecN) (hι := hιN) (hadm := hadmN) (hconv := hconv N) (hT := hT)
      (hTT := hTN) (hslots := hslots)
    exact EpsLimPkg_of_horizon_full (n := N) (Fc := F N) (hα₄ := hα₄0) (hα₄1 := hα₄1)
      (hα := hαIα₄) (hρ := hρ) (hL3 := hL3) (hα₂ := hα) (hvan := hvan) (hc₁ := hc₁)
      (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hstar6 := hstar6) (hml := hml)
      (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0)
      (hTower := hTower) (hMaj := hMaj) (hDec := hDecN) (hι := hιN) (hadm := hadmN)
      (hconv := hconv N) (hT := hT) (hTT := hTN) (hdbd := hdbd)

end Work.FTS.StrongEps.E5G
end

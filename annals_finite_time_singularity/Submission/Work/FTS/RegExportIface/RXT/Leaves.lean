import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.cone_max_aux
import Submission.Work.FTS.RegExportIface.RXT.LeafAux.spatial_expand
import Submission.Work.FTS.RegExportIface.RXT.LeafAux.logcoord_facts
import Submission.Work.FTS.RegExportIface.RXT.LeafAux.landau_1d
import Submission.Work.FTS.RegExportIface.RXT.LeafAux.loc_sup4
import Submission.Work.FTS.RegExportIface.RXT.LeafAux.cone_induction
import Submission.Work.FTS.RegExportIface.RXT.LeafAux.step_classical
import Submission.Work.FTS.RegExportIface.RXT.LeafDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegExportIface.RXT.Leaves` — the leaf statements of RX-T / RX-St1 (curric-46, 2026-10-10)

Installed from `cbc/fts_rxt_leafplans.lean` (plans: `cbc/fts_rxt_leafplans.md`; check + install
report: `cbc/fts_rxt_install.md`). Every leaf is a named `theorem … := by sorry`; `st1Export'` (S10)
is PROVED from S8 + S9. Imports only `RegExportIface.Defs` (so `Producers` may later import this file
and close `transport_weighted := transport_weighted'`, `st1Export := st1Export'`).

* RX-T  (= `Producers.transport_weighted`) = T6 `transport_weighted'`, route T5b + T3 + T1 (T2, T5a).
* RX-St1 (= `Producers.st1Export`, restated with `hμ : ClockBd`) = S10 `st1Export'` = S9 ∘ S8; S8 uses
  the VECTOR, INTEGRATED cone principle T4 + T5c on the six components `idx`, and S1–S7, X1, S4.
* RX-T0 (`Producers.dtau_mixed`) is OFF the St1 path.

Dispatch rounds (plan §4): (1) T1 T2 S2 T5a S3a S1 S7 X1; (2) T3 T4 S3 S4; (3) T5b → T6, T5c, S5b,
S5c; (4) S5a, S6; (5) S8, S9 (S10 done).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS.RegExportIface.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG St1Class)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## Part T — the cone maximum principle (log coordinates `s = log z`, `ψ = log tan θ`) -/


-- **T1** (real induction over shrinking cones `|s-s₀|,|ψ-ψ₀| ≤ A(τ₀-τ)`) is declared in
-- `Submission.Work.FTS.RegExportIface.RXT.LeafAux.cone_induction` (imported above): the statement
-- is byte-for-byte the leaf's, the proof is ported from the `Work.FTS_RegExport` mirror (its only
-- workshop dependency is `RXT/cone_max_aux.lean`, which itself imports just `Mathlib`).

-- **T2** (uniform first-order expansion in space on compact boxes; two 1-D MVTs + Heine–Cantor)
-- is declared in
-- `Submission.Work.FTS.RegExportIface.RXT.LeafAux.spatial_expand` (imported above): the
-- statement is byte-for-byte the leaf's, the proof is ported from the `Work.FTS_RegExport` mirror.


-- **T3** (the classical step for the frozen scalar RX-T: `q = p - h·(a,b)(p,τ+h)`) is declared in
-- `Submission.Work.FTS.RegExportIface.RXT.LeafAux.step_classical` (imported above): the statement
-- is byte-for-byte the leaf's, the proof is ported from the `Work.FTS_RegExport` mirror.

/-- **T4** the integrated step (vector; coefficients only continuous in `τ`, sources only
integrable): `q = p - ∫_τ^{τ+h}(a,b)(p,σ)dσ`. Used by St1. -/
theorem step_integrated {n : ℕ} {φ φs φψ R : Fin n → ℝ → ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ → ℝ}
    {T A C F : ℝ}
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φ k p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ Icc 0 T))
    (hs : ∀ k s ψ, ∀ τ ∈ Icc (0:ℝ) T, HasDerivAt (fun s' => φ k s' ψ τ) (φs k s ψ τ) s)
    (hψ : ∀ k s ψ, ∀ τ ∈ Icc (0:ℝ) T, HasDerivAt (fun ψ' => φ k s ψ' τ) (φψ k s ψ τ) ψ)
    (hcs : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φs k p.1 p.2.1 p.2.2) (univ ×ˢ univ ×ˢ Icc 0 T))
    (hcψ : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φψ k p.1 p.2.1 p.2.2)
      (univ ×ˢ univ ×ˢ Icc 0 T))
    (hab : ∀ s ψ, ContinuousOn (fun τ => a s ψ τ) (Icc 0 T) ∧ ContinuousOn (fun τ => b s ψ τ) (Icc 0 T))
    (hA : ∀ s ψ τ, τ ∈ Icc (0:ℝ) T → |a s ψ τ| ≤ A ∧ |b s ψ τ| ≤ A)
    (hRi : ∀ k s ψ, IntervalIntegrable (fun τ => R k s ψ τ) volume 0 T)
    (hRb : ∀ k s ψ τ, τ ∈ Icc (0:ℝ) T → |R k s ψ τ| ≤ C * ∑ j, |φ j s ψ τ| + F)
    (hId : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ T →
      φ k s ψ τ₂ - φ k s ψ τ₁
        = ∫ σ in τ₁..τ₂, (R k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ))) :
    ConeStep n φ T A (n * C) F := by
  sorry

-- **T5a** (the log coordinates and the log-derivatives of the weight `ω = z²Γ/(1+z)²`) is
-- declared in `Submission.Work.FTS.RegExportIface.RXT.LeafAux.logcoord_facts` (imported above):
-- the statement is byte-for-byte the leaf's, the proof assembles the mirror-area facts
-- `Work.FTS_RegExport.RXT.logcoord_facts` and `Work.FTS_RegExport.RXT.omega_facts` (both proved,
-- and both in modules that do **not** import `Leaves`).

/-- **T5b** pull-back of the frozen RX-T data to `φ(s,ψ,τ) = u(eˢ, arctan eᵠ, τ)/ω`, in the form
consumed by T3 (`a = Vz`, `b = 2Vθ/sin2θ`, `c' = cs + 2Vz/(1+z) + 2α·c2m·Vθ/sin2θ`, `f = σ/ω`). -/
theorem transport_pullback {S M K₀ Kσ : ℝ} (hα : 0 < α) (hS : 0 < S)
    {u Vz Vθ cs σ : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hEq : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => u z θ s)
        (σ z θ τ - (Vz z θ τ * Work.Spaces.Dz (fun z θ => u z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => u z θ τ) z θ + cs z θ τ * u z θ τ)) τ)
    (hVz : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → 0 ≤ Vz z θ τ ∧ Vz z θ τ ≤ M)
    (hVθ : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ))
    (hcs : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → |cs z θ τ| ≤ M)
    (hσ : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → |σ z θ τ| ≤ Kσ * ω α z θ)
    (h0 : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |u z θ 0| ≤ K₀ * ω α z θ) :
    0 ≤ M ∧ 0 ≤ K₀ ∧ 0 ≤ Kσ ∧
    ConeStep 1 (fun _ s ψ τ => u (Real.exp s) (Real.arctan (Real.exp ψ)) τ
        / ω α (Real.exp s) (Real.arctan (Real.exp ψ))) S (2 * M) (M * (3 + 4 * α)) Kσ ∧
    (∀ s ψ, ContinuousOn (fun τ => u (Real.exp s) (Real.arctan (Real.exp ψ)) τ
        / ω α (Real.exp s) (Real.arctan (Real.exp ψ))) (Icc 0 S)) := by
  sorry

/-- **T5c** the weighted, vector, integrated maximum principle in `(z,θ)` (T4 + T1 after the
pull-back of T5a). `wz = D_z w`, `wθ = D_θ w`, `b = Vθ/sin 2θ`. -/
theorem weighted_integrated_mp {n : ℕ} {w wz wθ R : Fin n → ℝ → ℝ → ℝ → ℝ}
    {Vz b : ℝ → ℝ → ℝ → ℝ} {S M C K₀ Kσ : ℝ} (hα : 0 < α) (hS : 0 < S)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => w k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hz : ∀ k z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      HasDerivAt (fun z' => w k z' θ τ) (wz k z θ τ / z) z)
    (hθ : ∀ k z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      HasDerivAt (fun θ' => w k z θ' τ) (wθ k z θ τ / Real.sin (2 * θ)) θ)
    (hcz : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wz k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hcθ : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wθ k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContinuousOn (fun τ => Vz z θ τ) (Icc 0 S) ∧ ContinuousOn (fun τ => b z θ τ) (Icc 0 S))
    (hVb : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      |Vz z θ τ| ≤ M ∧ |b z θ τ| ≤ M)
    (hRi : ∀ k z θ, 0 < z → 0 < θ → θ < π / 2 →
      IntervalIntegrable (fun τ => R k z θ τ) volume 0 S)
    (hRb : ∀ k z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      |R k z θ τ| ≤ C * ∑ j, |w j z θ τ| + Kσ * ω α z θ)
    (hId : ∀ k z θ τ₁ τ₂, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      w k z θ τ₂ - w k z θ τ₁
        = ∫ σ in τ₁..τ₂, (R k z θ σ - (Vz z θ σ * wz k z θ σ + b z θ σ * wθ k z θ σ)))
    (h0 : ∀ k z θ, 0 < z → 0 < θ → θ < π / 2 → |w k z θ 0| ≤ K₀ * ω α z θ) :
    ∃ K : ℝ, ∀ k z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc (0:ℝ) S →
      |w k z θ τ| ≤ K * ω α z θ := by
  sorry

/-- **T6 = frozen RX-T** (`Producers.transport_weighted`, verbatim): T5b (with T3 inside) gives the
`ConeStep` with `C = M(3+4α)`, `F = Kσ`; T1 with `K := 2M(3+4α)`, then monotonicity in `τ`
(`M, Kσ ≥ 0` from T5b). `hlip` is unused. -/
theorem transport_weighted' {S M K₀ Kσ : ℝ} (hα : 0 < α) (hS : 0 < S)
    {u Vz Vθ cs σ : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hEq : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => u z θ s)
        (σ z θ τ - (Vz z θ τ * Work.Spaces.Dz (fun z θ => u z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => u z θ τ) z θ + cs z θ τ * u z θ τ)) τ)
    (hVz : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → 0 ≤ Vz z θ τ ∧ Vz z θ τ ≤ M)
    (hVθ : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S →
      |Vθ z θ τ| ≤ M * Real.sin (2 * θ))
    (hlip : ∀ τ ∈ Icc 0 S, ∀ L₁ > 0, ∃ K : NNReal, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ)) (Set.Ioi L₁ ×ˢ Set.Ioo (0:ℝ) (π / 2)))
    (hcs : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → |cs z θ τ| ≤ M)
    (hσ : ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S → |σ z θ τ| ≤ Kσ * ω α z θ)
    (h0 : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |u z θ 0| ≤ K₀ * ω α z θ) :
    ∃ K : ℝ, ∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Icc 0 S →
      |u z θ τ| ≤ Real.exp (K * S) * (K₀ + S * Kσ) * ω α z θ := by
  sorry

/-! ## Part S — RX-St1 -/



/-- **X1 (cross-item, RX-VP owner)**: `vanish0` to order 2. -/
theorem velVanish2 (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (pExp α) (phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ)),
          Work.Construction.Vop (phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ),
          fun z θ => Work.Construction.Uop (pExp α) (phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1 := by
  sorry

-- **S1** (local `C⁴` bound of the strong solution, uniform in `τ ∈ [0,T]`; LocUnif Morrey) is
-- declared in `Submission.Work.FTS.RegExportIface.RXT.LeafAux.loc_sup4` (imported above): the
-- statement is the leaf's, the proof is ported from the `Work.FTS_RegExport` mirror.

-- **S2** (the 1-D Landau inequality) is declared in
-- `Submission.Work.FTS.RegExportIface.RXT.LeafAux.landau_1d` (imported above): the statement is
-- byte-for-byte the leaf's, the proof is ported from the `Work.FTS_RegExport` mirror.

/-- **S3a** `D_θ` commutes past `D_z^j` on `C⁴` slices (port of `Dth_DzIter_eqOn`). -/
theorem Dth_mixed_C4 {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (j i : ℕ) (hji : j + i ≤ 3)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2) :
    Work.Spaces.Dth (Work.Spaces.mixed j i f) z θ = Work.Spaces.mixed j (i + 1) f z θ := by
  exact Work.FTS_RegExport.C4.Dth_mixed_eq_C4 hf j i (by omega) hz ⟨hθ, hθ'⟩

/-- **S3** joint continuity of the order-≤3 jets on the slab up to `τ = 0` (S1 + S2 + RX-A2). -/
theorem jc3 (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Fam} (hOK : DynOK' (pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∀ j i : ℕ, j + i ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) T) := by
  sorry

/-- **S4** spatial `C²` of the coefficient slices (from `psiCan_C3` + `C³` of `L₁₂(F)`). -/
theorem coeff_C2 (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hEL3 : EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hOK : DynOK' (pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => VR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => bR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => cR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 := by
  sorry

/-- **S5b** the differentiated equation, pointwise (Leibniz; commutators bounded by `dbnd`). -/
theorem gdot_system {S : ℝ} (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Fam}
    (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hVP : VelPkg (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) S)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => VR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => bR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => cR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0)
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ s)
        (-(VR α Φs E g z θ τ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ) z θ
          + Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ) z θ
          + cR α Φs E g z θ τ * Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ)) τ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ k : Fin 6, ∀ z θ σ, 0 < z → 0 < θ → θ < π / 2 → 0 < σ → σ ≤ S →
      |Work.Spaces.mixed (idx k).1 (idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ
        + (VR α Φs E g z θ σ * Work.Spaces.mixed ((idx k).1 + 1) (idx k).2 (slice g σ) z θ
          + bR α Φs E g z θ σ * Work.Spaces.mixed (idx k).1 ((idx k).2 + 1) (slice g σ) z θ)
        + Work.Spaces.mixed (idx k).1 (idx k).2 (SigR α Φs E g σ) z θ|
        ≤ Cc * ∑ j : Fin 6, |Work.Spaces.mixed (idx j).1 (idx j).2 (slice g σ) z θ| := by
  sorry


/-- **S5c** `∂_τg = −(Vz·D_zF + Vθ·∂_θF + cs·F)` is spatially `C²` with local bounds
(S1 + S4 + `VelPkg.dbnd`). -/
theorem gdot_regular {S : ℝ} (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Fam}
    (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hVP : VelPkg (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) S)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => VR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => bR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => cR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0)
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ s)
        (-(VR α Φs E g z θ τ
            * Work.Spaces.Dz (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ) z θ
          + Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (fun z θ => Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ) z θ
          + cR α Φs E g z θ τ * Work.FTS.Regularity.profFull α (extG (GR α g)) z θ τ)) τ) :
    GdotLoc S g := by
  sorry

/-- **S5a** the integrated identity for the six components (FTC + differentiation under `∫`;
measurability of `σ ↦ D^β ∂_τg` by iterated limits of difference quotients of `measurable_deriv`). -/
theorem mixed_integral_identity {S : ℝ} (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Fam}
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g) (hG : GdotLoc S g) :
    ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → ∀ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      Work.Spaces.mixed (idx k).1 (idx k).2 (slice g τ₂) z θ
        - Work.Spaces.mixed (idx k).1 (idx k).2 (slice g τ₁) z θ
      = ∫ σ in τ₁..τ₂, Work.Spaces.mixed (idx k).1 (idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ := by
  sorry

/-- **S6** the forcing is `O(ω)` with all six derivatives (`Σ = Γ·κz/(1+z)³·Q`, `Q = (A+B)+z(B−A)`,
`A+B = O(z)` by RX-B, RX-A2w, X1). -/
theorem forcing_bound {S : ℝ} (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Fam}
    (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hVP : VelPkg (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g) S)
    (hV2 : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (pExp α) (phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ)),
          Work.Construction.Vop (phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ),
          fun z θ => Work.Construction.Uop (pExp α) (phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => VR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => bR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => cR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0)
    (hL12 : ∀ τ : ℝ, 0 ≤ τ → Work.Construction.L12 (slice g τ) 0 = 0)
    (hw : ∃ C : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < π / 2 → |Work.Spaces.mixed b a (slice g τ) z θ| ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :
    ∃ KS : ℝ, 0 ≤ KS ∧ ∀ k : Fin 6, ∀ z θ σ, 0 < z → 0 < θ → θ < π / 2 → 0 ≤ σ → σ ≤ S →
      |Work.Spaces.mixed (idx k).1 (idx k).2 (SigR α Φs E g σ) z θ| ≤ KS * ω α z θ := by
  sorry

/-- **S7** the datum is `O(ω)` with all six derivatives. -/
theorem datum_bound (hα : 0 < α) (hα13 : α ≤ 1 / 3) {L β : ℝ} (hL : 1 ≤ L) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (idx k).1 (idx k).2 (Work.FTS.LocData6.locG6 (pExp α) L β) z θ|
        ≤ K₀ * ω α z θ := by
  sorry

/-- **S8** the weighted bound for the six components (T5c on S3, S5a, S5b, S6, S7). -/
theorem weighted_system (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, ∃ K : ℝ, ∀ k : Fin 6, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (idx k).1 (idx k).2 (slice g τ) z θ| ≤ K * ω α z θ := by
  sorry

/-- **S9** the St1 class from the weighted bounds (pure real analysis). -/
theorem st1_of_weighted (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Fam}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) {S K : ℝ} (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (idx k).1 (idx k).2 (slice g τ) z θ| ≤ K * ω α z θ) :
    St1Class α S (gS α (tauExt g)) := by
  sorry

/-- **S10 = RX-St1, restated** (= `Producers.st1Export` as restated 10-10 with `hμ : ClockBd`). PROVED
from S8 + S9. -/
theorem st1Export' (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, St1Class α S (gS α (tauExt g)) := by
  intro S hS
  obtain ⟨K, hK⟩ := weighted_system hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  exact st1_of_weighted hα hα13 hOK.1.1 hS hK

end Work.FTS.RegExportIface.RXT

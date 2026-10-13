import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXT0.DtauGeo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauFinal` — the assembly of RX-T0 from its two black boxes

The two inputs (both delegated, both stated for the RX-T0 hypothesis bundle):

* `hRHS` — joint continuity on the slab of the `≤ 2` mixed jets of the transport expression
  `RHS α Φs E g σ` (the `HkIntegrand`-free version of "`gdot`'s jets are continuous");
* `hSlab` — the abstract slab `C¹`-lemma (`RXT0.slabC1`).

The assembly below produces exactly the RX-T0 conclusion, with the integral identity
`dtau_hId` and the Fréchet data `dtau_hasFDerivAt`/`dtau_Lcont`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- **RX-T0, assembled from the two black boxes.** -/
theorem dtau_mixed_proto (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g)
    (hRHS : ∀ S > 0, ∀ b a : ℕ, a + b ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed b a
          (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    (hSlab : ∀ {S : ℝ}, 0 < S → ∀ {f : ℝ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ → ℝ}
        {L : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ},
      ContinuousOn (fun p : ℝ × ℝ × ℝ => A p.1 p.2.1 p.2.2)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) →
      (∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
        f z θ τ = f z θ 0 + ∫ σ in (0:ℝ)..τ, A z θ σ) →
      (∀ p ∈ Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S),
        HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2 p.2.2) (L p) (p.1, p.2.1)) →
      ContinuousOn L (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) →
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) ∧
      ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ < S →
        HasDerivAt (fun s => f z θ s) (A z θ τ) τ) :
    ∀ S > 0, ∀ b a : ℕ, a + b ≤ 2 →
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed b a (slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) ∧
      ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
        HasDerivAt (fun s => Work.Spaces.mixed b a (slice g s) z θ)
          (Work.Spaces.mixed b a (gdot g τ) z θ) τ := by
  intro S hS b a hba
  -- the C¹ part on the horizon `S`
  have hC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed b a (slice g p.2.2) p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) :=
    (hSlab hS (hRHS S hS b a hba)
      (fun z θ τ hz hθ hθ2 hτ0 hτS =>
        dtau_hId (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
          hα hα13 hEll hEL3 hStar hSol hOK hμ hS hba z θ τ hz hθ hθ2 hτ0 hτS)
      (dtau_hasFDerivAt (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hOK hS hba)
      (dtau_Lcont (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS hba)).1
  refine ⟨hC1, fun z θ τ hz hθ hθ2 hτ0 hτS => ?_⟩
  -- the τ-derivative on the horizon `S + 1` (so that `τ` is interior)
  have hS1 : (0:ℝ) < S + 1 := by linarith
  have hτS1 : τ < S + 1 := by linarith
  have hder := (hSlab (S := S + 1) hS1 (hRHS (S + 1) hS1 b a hba)
      (fun z' θ' τ' hz' hθ' hθ2' hτ0' hτ'S' =>
        dtau_hId (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
          hα hα13 hEll hEL3 hStar hSol hOK hμ hS1 hba z' θ' τ' hz' hθ' hθ2' hτ0' hτ'S')
      (dtau_hasFDerivAt (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hOK hS1 hba)
      (dtau_Lcont (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS1 hba)).2
  have hmain := hder z θ τ hz hθ hθ2 hτ0 hτS1
  -- identify the transport expression with `gdot`
  have heq : Work.Spaces.mixed b a (gdot g τ) z θ
      = Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g τ) z θ :=
    dtau_jet_eq (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ hS1 ⟨hτ0, le_of_lt hτS1⟩ hba
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)
  rw [← heq] at hmain
  exact hmain

end Work.FTS_RegExport.RXT0

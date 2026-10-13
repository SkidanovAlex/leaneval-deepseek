/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/EpsClass.lean` — the class `P` of the Volterra engine for the
# concrete right-hand side of the projected `ε`-scheme

This module fixes the *profile* interface between the abstract engine
`Work.FTS.EpsEngine.exists_volterra_v4` and the projected `ε`-scheme:

* `Feps` — the τ-independent right-hand side `Pz (J_ε (profRHS α Φs E (Pz (J_ε u))))` of the
  projected scheme, together with the identification `epsRHSP … g τ = Feps (slice g τ)`
  (`EpsLocalPStar.epsRHPSlice_eq_profRHS` + `epsRHSP_eq_slice`);
* `EpsClass C₁ B` — the class `P` of the engine: the *gate* hypotheses of
  `EpsLocalPStar.EpsRHSPLipX` (`SmoothOpen`, `HkMem α 6`, `HkNorm α 6 ≤ B`, the class-`C` ball at
  `C₁`) at a radius `C₁` and an `ℋ⁶`-size `B`;
* `BddLip_of_epsClass` — the engine's hypotheses `hbd`/`hlip` for `Feps`, produced from the proved
  gate `EpsRHSPLipX` (with one constant `L` for both clauses);
* `IsEpsSolP_of_v4` — the conversion of the engine's conclusion into the scheme's `IsEpsSolP`.

**Note on the radius.**  `EpsRHSPLipX` needs `MuLamOK α C Φs E` *at the radius `C` of the ball it
is applied to*.  The engine runs at the radius `C₁` of the class `EpsClass C₁ B`, so the
instantiation must supply `MuLamOK α C₁ Φs E`; the frozen local step supplies only
`MuLamOK α C₀ Φs E` at the radius `C₀` of its datum ball, whence the *room* problem documented in
`NOTES_VolterraV4.md` §3 (`C₁ > C₀` is needed).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX
import Submission.Work.FTS.EpsEngine.VolterraV4Main

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

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **The right-hand side of the projected `ε`-scheme as a map on profiles** (τ-free form):
`Pz (J_ε (profRHS α Φs E (Pz (J_ε u))))`. -/
noncomputable def Feps (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) : Fn → Fn :=
  fun u => Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u))))

/-- The scheme's right-hand side is `Feps` at the slice: `epsRHSP … g τ = Feps (slice g τ)`. -/
theorem epsRHSP_eq_Feps_slice (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    epsRHSP α ρ ε Φs E g τ = Feps α ρ ε Φs E (slice g τ) := by
  rw [epsRHSP_eq_slice α ρ ε Φs E τ g,
    Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E τ (slice g τ)]
  rfl

/-- `Feps` at the constant family: `Feps u = epsRHPSlice … τ u`. -/
theorem Feps_eq_epsRHPSlice (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (τ : ℝ) (u : Fn) :
    Feps α ρ ε Φs E u = epsRHPSlice α ρ ε Φs E τ u := by
  rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E τ u]
  rfl

/-- **The class `P` of the engine** for the projected `ε`-scheme: open-quadrant smoothness,
`ℋ⁶`-honesty, an `ℋ⁶`-size bound `B`, the class-`C` clause of the projected mollified profile, and
its ball bound at the radius `C₁`.  These are exactly the hypotheses of the gate `EpsRHSPLipX`. -/
def EpsClass (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (C₁ B : ℝ) (u : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen u ∧ Work.Spaces.HkMem α 6 u ∧ Work.Spaces.HkNorm α 6 u ≤ B ∧
    Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) ∧ Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u)) ≤ C₁ * α ^ 2

theorem EpsClass.smoothOpen {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε C₁ B : ℝ} {u : Fn}
    (h : EpsClass α ρ ε C₁ B u) : Work.FTS.EllipticEst.SmoothOpen u := h.1

theorem EpsClass.hkMem {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε C₁ B : ℝ} {u : Fn}
    (h : EpsClass α ρ ε C₁ B u) : Work.Spaces.HkMem α 6 u := h.2.1

theorem EpsClass.hkNorm {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε C₁ B : ℝ} {u : Fn}
    (h : EpsClass α ρ ε C₁ B u) : Work.Spaces.HkNorm α 6 u ≤ B := h.2.2.1

theorem EpsClass.classC {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε C₁ B : ℝ} {u : Fn}
    (h : EpsClass α ρ ε C₁ B u) : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) := h.2.2.2.1

theorem EpsClass.ball {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε C₁ B : ℝ} {u : Fn}
    (h : EpsClass α ρ ε C₁ B u) : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u)) ≤ C₁ * α ^ 2 := h.2.2.2.2

/-- `EpsClass` is monotone in the ball radius and in the `ℋ⁶`-size. -/
theorem EpsClass.mono {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε C₁ C₁' B B' : ℝ} {u : Fn}
    (h : EpsClass α ρ ε C₁ B u) (hC : C₁ ≤ C₁') (hB : B ≤ B') : EpsClass α ρ ε C₁' B' u :=
  ⟨h.1, h.2.1, le_trans h.2.2.1 hB, h.2.2.2.1,
    le_trans h.2.2.2.2 (mul_le_mul_of_nonneg_right hC (sq_nonneg α))⟩

/-- **The engine's `hbd`/`hlip` for `Feps`**, produced from the gate `EpsRHSPLipX`: a single
constant `L > 0` with `EpsMem (Feps u) ∧ EpsSq (Feps u) ≤ L` and
`EpsSq (Feps u − Feps v) ≤ L · EpsSq (u − v)` on `EpsClass C₁ B`. -/
theorem BddLip_of_epsClass {α C₁ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₁ Φs E) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧
      (∀ u : Fn, EpsClass α ρ ε C₁ B u → EpsMem α (Feps α ρ ε Φs E u) ∧
        EpsSq α (Feps α ρ ε Φs E u) ≤ L) ∧
      (∀ u v : Fn, EpsClass α ρ ε C₁ B u → EpsClass α ρ ε C₁ B v →
        EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
          ≤ L * EpsSq α (fun z θ => u z θ - v z θ)) := by
  obtain ⟨L, hLpos, h1, h2⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs)
      (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hB
  refine ⟨L, hLpos, ?_, ?_⟩
  · intro u hu
    obtain ⟨hmem, hbd⟩ := h1 0 u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2
    rw [← Feps_eq_epsRHPSlice α ρ ε Φs E 0 u] at hmem hbd
    exact ⟨hmem, hbd⟩
  · intro u v hu hv
    have h := h2 0 u v hu.1 hv.1 hu.2.1 hv.2.1 hu.2.2.1 hv.2.2.1 hu.2.2.2.1 hv.2.2.2.1
      hu.2.2.2.2 hv.2.2.2.2
    rwa [← Feps_eq_epsRHPSlice α ρ ε Φs E 0 u, ← Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h

/-- **The engine's conclusion is the scheme's `IsEpsSolP`**: a family with the initial value and the
fake-time derivative `Feps (slice h τ)` is a `P₀`-solution of the projected `ε`-scheme. -/
theorem IsEpsSolP_of_v4 {α ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {h : Fam}
    (h0 : ∀ z θ, h z θ 0 = g₀ z θ)
    (hder : ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 δ →
      HasDerivWithinAt (fun s => h z θ s) (Feps α ρ ε Φs E (slice h τ) z θ) (Set.Icc 0 δ) τ) :
    IsEpsSolP α ρ ε δ Φs E g₀ h := by
  refine ⟨h0, ?_⟩
  intro z θ τ hz hθ hτ
  have hh := hder z θ τ hz hθ hτ
  rwa [← epsRHSP_eq_Feps_slice α ρ ε Φs E h τ] at hh

end Work.FTS.EpsEngine

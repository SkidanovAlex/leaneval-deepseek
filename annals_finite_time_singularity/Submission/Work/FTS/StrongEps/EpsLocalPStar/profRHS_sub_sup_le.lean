import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsRLX.ConjTwo
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_RegExport.RXR5L.coef_tau_lip
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.Spaces.bt_integral_weight_id
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsClass =====
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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The size half of the `X`-ball gate.**  For the parameters of the projected `ε`-scheme there
is a constant `L₁ > 0` such that for every `u` in the ball

  `SmoothOpen u`, `EpsMem α u`, `EpsSq α u ≤ R`, `ClassC α (Wp ρ ε u)`, `Xn α (Wp ρ ε u) ≤ C₀α²`

one has `EpsMem α (epsRHPSlice α ρ ε Φs E 0 u) ∧ EpsSq α (epsRHPSlice α ρ ε Φs E 0 u) ≤ L₁`.

The proof is `EpsRLX.ConjOne` with the datum's `ℋ⁶`-bound replaced by the profile bound
`exists_Wp_bound_of_EpsMem` (at `k = 6`): `W := Wp ρ ε u` is admissible for
`XDataClean`/`ProfRHSEpsData` with the size `BS = C_W (C_W/ε)⁶ (1+R)`. -/
theorem ConjOneSq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧ ∀ u : Fn,
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.StrongEps.EpsMem α u →
      Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ≤ L := by
  -- ## the profile size furnished by the ball data
  obtain ⟨CW, hCWpos, hCW⟩ := exists_Wp_bound_of_EpsMem (ρ := ρ) hρ
  set BS : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBSdef
  have hBS0 : 0 ≤ BS := by rw [hBSdef]; positivity
  have hW6 : ∀ (u : Fn), Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.StrongEps.EpsMem α u →
      Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS :=
    fun u hu hmem hEps => by
      rw [hBSdef]
      exact hCW α hα ε ⟨hε, hε1⟩ R hR u hu hmem hEps 6 (by norm_num)
  -- ## the data of the pre-mollified right-hand side, at the enlarged size
  obtain ⟨_, -, hRXdata⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := BS)
      hα hEll hstar hml hBS0
  obtain ⟨R₂, hR₂pos, hR₂⟩ :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := BS) hα hEll hstar hml hBS0
  obtain ⟨CP, hCPpos, hCP⟩ := Work.FTS.StrongEps.EpsRLX.EpsSq_Pz_le
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le ρ hρ
  obtain ⟨CM, -, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  refine ⟨max 1 (CP * CJ * R₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu hmem hEps hclu hxnu
  -- ## the profile and the pre-mollified right-hand side
  set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
  set Φ : Fn := profRHS α Φs E W with hΦdef
  have hclW : Work.FTS.ClassC.ClassC α W := hclu
  have hxnW : Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 := hxnu
  have hWb : Work.Spaces.HkNorm α 6 W ≤ BS := hW6 u hu hmem hEps
  obtain ⟨hXsm, hXmem, -⟩ := hRXdata hclW hxnW hWb
  obtain ⟨hXepsMem, hXepsSq⟩ := hR₂ hclW hxnW hWb
  -- ## the mollified pre-mollified profile
  have hsmΦ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hXsm
  have hJsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmΦ
  have hJmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmΦ hXmem
  have hJepsMem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    (hCM α hα ε hε hε1 Φ hsmΦ hXepsMem).1
  have hJepsSq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ)
      ≤ CJ * Work.FTS.StrongEps.EpsSq α Φ := by
    have h := hCJ α hα ε ⟨hε, hε1⟩ Φ hsmΦ hXepsMem 0 0 (by norm_num)
    have h1 : Work.FTS.StrongEps.EpsSq α
        (Work.Spaces.mixed 0 0 (Work.FTS.StrongEps.Jeps ρ ε Φ))
        = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    have h2 : CJ * (CJ / ε) ^ (2 * (0 + 0)) * Work.FTS.StrongEps.EpsSq α Φ
        = CJ * Work.FTS.StrongEps.EpsSq α Φ := by norm_num
    rw [h1, h2] at h
    exact h
  obtain ⟨hPzMem, hPzSq⟩ := hCP α hα (Work.FTS.StrongEps.Jeps ρ ε Φ) hJsm hJmem hJepsMem
  have hslice : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
    rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS]
  refine ⟨?_, ?_⟩
  · rw [hslice]; exact hPzMem
  · rw [hslice]
    calc Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ))
        ≤ CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := hPzSq
      _ ≤ CP * (CJ * Work.FTS.StrongEps.EpsSq α Φ) :=
          mul_le_mul_of_nonneg_left hJepsSq hCPpos.le
      _ = CP * CJ * Work.FTS.StrongEps.EpsSq α Φ := by ring
      _ ≤ CP * CJ * R₂ := mul_le_mul_of_nonneg_left hXepsSq (mul_nonneg hCPpos.le hCJpos.le)
      _ ≤ max 1 (CP * CJ * R₂) := le_max_right _ _

theorem EpsRHSPLipX_Sq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.StrongEps.EpsMem α u →
        Work.FTS.StrongEps.EpsSq α u ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ≤ L) ∧
      (∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        Work.FTS.StrongEps.EpsMem α u →
        Work.FTS.StrongEps.EpsSq α u ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
        Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
          ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  obtain ⟨L₁, hL₁pos, hL₁⟩ := ConjOneSq (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hEll hstar hml hR
  obtain ⟨L₂, hL₂pos, hL₂⟩ := ConjTwoSq (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hEll hstar hml hR
  refine ⟨max L₁ L₂, lt_of_lt_of_le hL₁pos (le_max_left L₁ L₂), ?_, ?_⟩
  · intro u hu hmem hEps hcl hxn
    obtain ⟨hmem', hbd⟩ := hL₁ u hu hmem hEps hcl hxn
    exact ⟨hmem', le_trans hbd (le_max_left L₁ L₂)⟩
  · intro u v hu hv hmu hEu hclu hxnu hmv hEv hclv hxnv hmuv
    refine le_trans (hL₂ u v hu hv hmu hEu hclu hxnu hmv hEv hclv hxnv hmuv) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right L₁ L₂)
      (Work.FTS.StrongEps.EpsSq_nonneg α (fun z θ => u z θ - v z θ))

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Auxiliary facts about the profile maps

Four elementary tools that the sup-norm estimate of the scheme's right-hand side needs:

* `pointwise_le_HkNorm` — the trace-free `ℋ⁴ → L^∞` trade-off with an *explicit* constant
  (`v2_hkMem_pointwise_min` at the slot `(b,a) = (0,0)`, the harmless `min z 1`-factor being
  dropped);
* `smoothOpen_Pz`, `hkMem_Pz` — the projection `P₀ f = f − (L₁₂ f 0/L₁₂ bump 0)•bump` preserves
  smoothness on the open quadrant and `ℋᵏ`-membership;
* `Wp_sub_eq_mem` — the additivity `W_ε u − W_ε v = W_ε (u − v)` of the projected mollifier
  (`EpsRLX.Wp_sub_eq`) under the *weaker* regularity `SmoothOpen ∧ HkMem α 4` that the difference
  of two right-hand sides supplies (`DeltaXnBound` only gives `HkMem α 4`). -/

/-- **The trace-free `ℋ⁴ → L^∞` trade-off**, with an explicit (universal) constant.  For a datum
which is `C^∞` on the open quadrant and honestly in `ℋ⁴`, every value on the open quadrant is
bounded by a universal multiple of `|f|_{ℋ⁴}`. -/
theorem pointwise_le_HkNorm {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 4 f → ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ C * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C, hC0, hbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  refine ⟨C, hC0, ?_⟩
  intro f hf hm z θ hz hθ0 hθ1
  have h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf 4
  have h := hbd f h4 hm 0 0 (by norm_num) z θ hz hθ0 hθ1
  have h' : |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.pthIter_zero] using h
  calc |f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := h'
    _ ≤ C * 1 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right z 1) hC0)
          (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = C * Work.Spaces.HkNorm α 4 f := by ring

/-- The projection `P₀` preserves smoothness on the open quadrant. -/
theorem smoothOpen_Pz {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Pz f) := by
  have heq : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    ring
  rw [heq]
  exact Work.FTS.NonlinRows.smoothOpen_add hf
    (Work.FTS.NonlinRows.smoothOpen_const_mul _ Work.FTS.StrongEps.smoothOpen_bump)

/-- The projection `P₀` preserves `ℋᵏ`-membership. -/
theorem hkMem_Pz {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Pz f) := by
  have heq : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
    ring
  rw [heq]
  exact Work.FTS.EllipticEst.HkMem_add_open hf
    (Work.FTS.NonlinRows.smoothOpen_const_mul _ Work.FTS.StrongEps.smoothOpen_bump) hm
    (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _
      (Work.FTS.StrongEps.PZeroAux.hkMem_bump α k))

/-- **Additivity of the projected mollifier `W_ε` at `ℋ⁴`-regularity**: the difference of the two
projected-mollified profiles is the projected-mollified profile of the difference.  This is
`EpsRLX.Wp_sub_eq` with the `ℋ⁶`-hypotheses weakened to `ℋ⁴` (only the latter is available for the
difference of two right-hand sides). -/
theorem Wp_sub_eq_mem {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {u v : Fn}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α 4 u) (hmv : Work.Spaces.HkMem α 4 v) :
    Work.FTS.StrongEps.EpsRLX.Wp ρ ε u - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε (fun z θ => u z θ - v z θ) := by
  have huc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hu
  have hvc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hv
  have hsmu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε huc
  have hsmv : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hvc
  have hmemu : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε huc hmu
  have hmemv : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hvc hmv
  have hL : Work.Construction.L12
        (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ) 0
      = Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hsmu hsmv hmemu hmemv 0
      (Set.mem_Ici.mpr le_rfl)
  have hJ : Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hu hv
  show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
      - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ))
  calc Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.StrongEps.Pz
          (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
            - Work.FTS.StrongEps.Jeps ρ ε v z θ) :=
        Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL
    _ = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ)) := by
        rw [show (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
              - Work.FTS.StrongEps.Jeps ρ ε v z θ)
            = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) from hJ]


end Work.FTS.StrongEps.EpsLocalPStar
end

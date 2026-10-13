import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.EpsEngine.FepsData
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsRLX.XDataClean
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrderFlow
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EllipticEst.HkMem_sub_open
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bumpP
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.volterra_of_xball
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.epsSqLip_of_xball
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkDerivWithin_of_xball

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

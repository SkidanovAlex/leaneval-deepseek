import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_RegExport.RXR5L.coef_tau_lip
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.THL.cs7_theta_holder
-- ===== merged: Submission.Work.FTS.EpsEngine.FepsData =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `Pz` preserves `ℋ^k`-membership -/

/-- **The projection preserves `ℋ^k`-membership.**  `Pz f = f - (L₁₂ f 0 / pzNorm) • bump` and
`bump` is compactly supported and smooth, so `HkMem` transfers by `HkMem_add_open`. -/
theorem HkMem_Pz_of {α : ℝ} {k : ℕ} {f : Fn}
    (hsmo : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (Work.FTS.StrongEps.Pz f) := by
  set c : ℝ := -(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm) with hc
  have hb : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.PZeroAux.classC_Pz_hkMem_bump α k
  have hcm : Work.Spaces.HkMem α k (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen c hb
  have hscm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen c Work.FTS.StrongEps.smoothOpen_bump
  have hPz : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + c * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc]
    ring
  rw [hPz]
  exact Work.FTS.EllipticEst.HkMem_add_open (α := α) (k := k) hsmo hscm hmem hcm

/-! ## The `ℋ⁶`-data of `Feps` on the `XBall` class -/

/-- **The `ℋ⁶`-data of `Feps` on the `XBall` class.**  There is a constant `Ce' > 0`, depending on
`α, ε, C₀, Ce, Cs, R` (but *not* on the profile `u`), such that for every `u` in the `XBall`
invariant the right-hand side `Feps α ρ ε Φs E u` is `SmoothOpen`, `ℋ⁶`-honest, and of
`ℋ⁶`-size at most `Ce'`. -/
theorem Feps_data_of_xball {α C₀ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ Ce' : ℝ, 0 < Ce' ∧ ∀ u : Fn, XBall α ρ ε R C₀ u →
      Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkMem α 6 (Feps α ρ ε Φs E u) ∧
      Work.Spaces.HkNorm α 6 (Feps α ρ ε Φs E u) ≤ Ce' := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  have hratio : 0 ≤ CJ / ε := div_nonneg hCJpos.le hε.le
  have hK60 : 0 ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
    mul_nonneg (mul_nonneg hCJpos.le (pow_nonneg hratio _)) hR
  -- the `ℋ⁶`-bound `B` of the projected mollified profile `W = Pz (J_ε u)`, uniform in `u`
  obtain ⟨CX, hCX, hX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  obtain ⟨RP, hRP, hProf⟩ :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R)) (Φs := Φs) (E := E)
      hα hEll hstar hml (Real.sqrt_nonneg _)
  refine ⟨Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * RP), ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (mul_pos (mul_pos hCJpos (pow_pos (div_pos hCJpos hε) _)) hRP)
  · intro u hu
    -- ## the `XBall` data
    have husmo : Work.FTS.EllipticEst.SmoothOpen u := hu.smoothOpen
    have humem : Work.FTS.StrongEps.EpsMem α u := hu.mem
    have husq : Work.FTS.StrongEps.EpsSq α u ≤ R := hu.sq_le
    have huC : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) :=
      hu.classC
    have huball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u))
        ≤ C₀ * α ^ 2 := hu.ball
    have husmQuad : ∀ n : ℕ,
        ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp husmo
    set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
    -- ## the `ℋ⁶`-bound of `W`
    have hW6 : Work.Spaces.HkNorm α 6 W
        ≤ Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) := by
      have h := hCJ α hα ε hε hε1 6 (by norm_num) u husmo humem
      have hle : Work.Spaces.HkSq α 6 W ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
        le_trans h (mul_le_mul_of_nonneg_left husq
          (mul_nonneg hCJpos.le (pow_nonneg hratio _)))
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt hle
    -- ## the pre-mollified right-hand side
    set g : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hgdef
    obtain ⟨hgsmo, hgmem4, -⟩ := hX (W := W) huC huball hW6
    obtain ⟨hgmeme, hgsq⟩ := hProf (W := W) huC huball hW6
    have hgsmQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hgsmo
    -- ## the mollified gain `ℋ⁴ → ℋ⁶`
    have hJ6 : Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 4 2 (by norm_num)
        ε hε g hgsmQuad hgmem4
    have hJsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε g) :=
      Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hgsmQuad
    have hFeps : Feps α ρ ε Φs E u = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε g) :=
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hFeps]
      exact smoothOpen_Pz_of_smoothOpen hJsmo
    · rw [hFeps]
      exact HkMem_Pz_of hJsmo hJ6
    · rw [hFeps, Work.Spaces.HkNorm]
      refine Real.sqrt_le_sqrt ?_
      exact (hCJ α hα ε hε hε1 6 (by norm_num) g hgsmo hgmeme).trans
        (mul_le_mul_of_nonneg_left hgsq (mul_nonneg hCJpos.le (pow_nonneg hratio _)))

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkMemIterAll =====
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

open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The per-curve data of the right-hand side -/

/-- **The data of the right-hand side along the `n`-th Picard curve** `s ↦ slice (iter F h₀ n) s`:
the seven hypotheses of `Work.FTS.EpsEngine.HkMem_intervalIntegralPerz`, held uniformly over the
curve.  This is the honest residue of (H4)(a) after `NOTES_perz_intervalIntegral.md`. -/
structure RHSData (α : ℝ) (k : ℕ) (T B : ℝ) (F : Fn → Fn) (h₀ : Fn) (n : ℕ) : Prop where
  smo : ∀ s ∈ Set.Icc (0 : ℝ) T,
    Work.FTS.EllipticEst.SmoothOpen (F (slice (iter F h₀ n) s))
  mem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α k (F (slice (iter F h₀ n) s))
  bd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α k (F (slice (iter F h₀ n) s)) ≤ B
  meas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (F (slice (iter F h₀ n) s)) z θ)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
  joint : MeasureTheory.AEStronglyMeasurable
    (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k (F (slice (iter F h₀ n) p.1)) p.2.1 p.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
  sup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
      |Work.Spaces.mixed j i (F (slice (iter F h₀ n) s)) q.1 q.2| ≤ C
  perz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
    (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (F (slice (iter F h₀ n) s)) z θ) ≤ Cz

/-! ## The induction over the Picard iterates -/

/-- **The smoothness of the increment, from the smoothness of the next slice.**  If the
`(n+1)`-st slice `h₀ + ∫₀^τ F ∘ slice (iter n)` is `SmoothOpen` and so is `h₀`, then the
increment itself is `SmoothOpen` — the `hIsmo` input of `HkMem_iter_succ_of_data`. -/
theorem smoothOpen_increment {F : Fn → Fn} {h₀ : Fn} {τ : ℝ} {n : ℕ}
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hsmo : Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ (n + 1)) τ)) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ) := by
  have hsub := Work.FTS.EllipticEst.smoothOpen_sub hsmo h₀smo
  have hfun : (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
      = fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := by
    funext z θ
    rw [show slice (iter F h₀ (n + 1)) τ z θ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ from by
      rw [Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
      rfl]
    ring
  rwa [hfun] at hsub

/-- **(H4)(a) iterated: every Picard slice is `ℋ^k`-honest**, with the norm bound
`HkNorm α k (slice (iter F h₀ n) τ) ≤ HkNorm α k h₀ + B * τ` (the same `B` for all `n`, from the
uniform right-hand-side data). -/
theorem HkMem_iter_all {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {T τ : ℝ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (h₀mem : Work.Spaces.HkMem α k h₀)
    (hsmo : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ n) τ))
    (hdata : ∀ n : ℕ, RHSData α k T B F h₀ n) :
    ∀ n : ℕ, Work.Spaces.HkMem α k (slice (iter F h₀ n) τ) ∧
      Work.Spaces.HkNorm α k (slice (iter F h₀ n) τ) ≤ Work.Spaces.HkNorm α k h₀ + B * τ := by
  intro n
  induction n with
  | zero =>
      have hE : slice (iter F h₀ 0) τ = h₀ := rfl
      refine ⟨?_, ?_⟩
      · rw [hE]; exact h₀mem
      · rw [hE]
        exact le_add_of_nonneg_right (mul_nonneg hB hτ)
  | succ n ih =>
      exact HkMem_iter_succ_of_data (F := F) (h₀ := h₀) (k := k) (T := T) (τ := τ) (n := n)
        hτ hτT hT hB h₀smo h₀mem (smoothOpen_increment h₀smo (hsmo (n + 1)))
        (hdata n).smo (hdata n).mem (hdata n).bd (hdata n).meas (hdata n).joint (hdata n).sup
        (hdata n).perz

/-! ## The limit -/

/-- **(H4)(b): the limit slice is `ℋ^k`-honest.**  Fatou along the Picard iterates
(`Work.FTS.StrongEps.HkMem_of_tendsto`): the hypotheses are the iterate-wise membership and norm
bound (from `HkMem_iter_all`), the `C^k`-regularity of the iterates and of the limit, the
pointwise **slot** convergence of the iterates to the limit, and the per-`z` bound (uniform in
`n`, which `HkMem_iter_all` supplies). -/
theorem HkMem_limFam_of_slot_conv {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {τ : ℝ}
    (hiter : ∀ n : ℕ, Work.Spaces.HkMem α k (slice (iter F h₀ n) τ))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α k (slice (iter F h₀ n) τ) ≤ B)
    (hsmG : ∀ n : ℕ, ContDiffOn ℝ k (Function.uncurry (slice (iter F h₀ n) τ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsmf : ContDiffOn ℝ k (Function.uncurry (slice (limFam F h₀) τ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (slice (iter F h₀ n) τ) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i (slice (limFam F h₀) τ) z θ)))
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (slice (iter F h₀ n) τ) z θ) ≤ Bz) :
    Work.Spaces.HkMem α k (slice (limFam F h₀) τ) ∧
      Work.Spaces.HkNorm α k (slice (limFam F h₀) τ) ≤ B :=
  Work.FTS.StrongEps.HkMem_of_tendsto (k := k) (m := k) le_rfl hsmG hsmf hconv hiter hb hz

/-! ## The two ball clauses of the local step, with (H4) supplied -/



end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.SmoothOpenIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Convolution
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsLocalPStar
set_option maxHeartbeats 1600000 in
/-- (C) **pointwise Lipschitz bound of the PRE-mollified right-hand side** on the `X`-ball:
`|profRHS(Wp u) − profRHS(Wp v)|(z,θ) ≤ C √EpsSq(u−v)`, uniformly on the open quadrant.
(Same hypotheses as `profRHS_sub_sup_le_Sq`; the proof is its first half.) -/
theorem profRHS_pre_sub_pt_le_Sq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (_hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Fn},
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.StrongEps.EpsMem α u → Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
          - profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  obtain ⟨K₁, hK₁pos, hK₁⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨CD, hCDpos, hCD⟩ := HkSq_Wp_sub_le_weak (α := α) hρ hα hε hε1
  obtain ⟨Cpt, hCpt0, hCpt⟩ := pointwise_le_HkNorm (α := α) hα0 hα1
  set BS : ℝ := Real.sqrt (CH * (CH / ε) ^ 10 * R) + 1 with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]; have := Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R); linarith
  have hWp5 : ∀ {w : Fn}, Work.FTS.EllipticEst.SmoothOpen w → Work.FTS.StrongEps.EpsMem α w →
      Work.FTS.StrongEps.EpsSq α w ≤ R →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w) ≤ BS := by
    intro w hsw hmw hrw
    have hfac : 0 ≤ CH * (CH / ε) ^ 10 := by positivity
    have hle : Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)
        ≤ CH * (CH / ε) ^ 10 * R :=
      le_trans (hCH α hα ε hε hε1 5 (by norm_num) w hsw hmw)
        (mul_le_mul_of_nonneg_left hrw hfac)
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hle) ?_
    rw [hBSdef]; linarith
  set Q : ℝ := Real.sqrt CD with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set M₀ : ℝ := 1 + 2 * BS with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  refine ⟨max 1 (Cpt * K₁ * M₀ ^ 2 * Q), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hsu hsv hmu hru hmv hrv hclu hclv hxnu hxnv z θ hz hθ0 hθ1
  set d : Fn := fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ with hddef
  obtain ⟨hΔsm, hΔmem4, hΔxn⟩ := hK₁
    (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
    (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclu hclv hxnu hxnv
  have hDd : Work.Spaces.HkSq α 5 d
      ≤ CD * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    rw [hddef]; exact hCD hsu hsv hmu hmv hclu hclv
  have hQbd : Work.Spaces.HkNorm α 5 d
      ≤ Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    rw [Work.Spaces.HkNorm, hQdef, ← Real.sqrt_mul hCDpos.le]
    exact Real.sqrt_le_sqrt hDd
  have hWu := hWp5 hsu hmu hru
  have hWv := hWp5 hsv hmv hrv
  have h1 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have h2 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hM2 : (1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2 ≤ M₀ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by rw [hM₀def]; linarith) 2
  have hZ : 0 ≤ Work.Spaces.HkNorm α 5 d := Work.Spaces.HkNorm_nonneg α 5 d
  have hKM : 0 ≤ K₁ * M₀ ^ 2 := mul_nonneg hK₁pos.le (pow_nonneg hM₀0 2)
  have hpt := hCpt hΔsm hΔmem4 hz hθ0 hθ1
  have hfinal : |profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
          - profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ|
      ≤ (Cpt * K₁ * M₀ ^ 2 * Q)
        * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    calc _ ≤ Cpt * Work.Spaces.HkNorm α 4 (fun z θ =>
            profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
              - profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ) := hpt
      _ ≤ Cpt * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) := by
          refine mul_le_mul_of_nonneg_left (le_trans hΔxn ?_) hCpt0
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hK₁pos.le) hZ
      _ ≤ Cpt * (K₁ * M₀ ^ 2
            * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQbd hKM) hCpt0
      _ = _ := by ring
  exact le_trans hfinal (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

end Work.FTS.StrongEps.EpsLocalPStar

namespace Work.FTS.EpsEngine.SORuling

open Work.FTS.StrongEps

set_option autoImplicit false

/-- (A) mollified form ⟹ `SmoothOpen`. -/
theorem smoothOpen_of_mollForm {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    {h₀ Ψ u : Fn} {c : ℝ} (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hΨ : Continuous (logPull Ψ))
    (hu : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      u z θ = h₀ z θ + Jeps ρ ε Ψ z θ - c * bump z θ) :
    Work.FTS.EllipticEst.SmoothOpen u := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have hJ : ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε Ψ)) Work.FTS.EllipticEst.Q0 :=
    Jeps_contDiffOn ρ hρ hε hΨ.locallyIntegrable n
  have h0n := h0.forall n
  have hb := Work.FTS.StrongEps.smoothOpen_bump.forall n
  have hsum : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Function.uncurry h₀ p + Function.uncurry (Jeps ρ ε Ψ) p - c * Function.uncurry bump p)
      Work.FTS.EllipticEst.Q0 :=
    (h0n.add hJ).sub (contDiffOn_const.mul hb)
  refine hsum.congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
  simp only [Function.uncurry_apply_pair]
  exact hu z θ hp'.1 ⟨hp'.2.1, hp'.2.2⟩

/-- (B) Fubini: the time integral commutes with a compactly supported continuous kernel. -/
theorem conv_intervalIntegral_swap {k : ℝ × ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {H : ℝ → ℝ × ℝ → ℝ}
    (hH : Continuous (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2)) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : ℝ × ℝ) :
    IntervalIntegrable (fun s => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H s) x)
        volume 0 τ ∧
      (∫ s in (0 : ℝ)..τ, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H s) x)
        = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (fun y => ∫ s in (0 : ℝ)..τ, H s y)) x := by
  set f : ℝ → ℝ × ℝ → ℝ := fun s t => k t * H s (x - t) with hfdef
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hfdef]
    exact (hk.comp continuous_snd).mul
      (hH.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd)))
  set K := tsupport k with hK
  have hKc : IsCompact K := hks
  have hon : IntegrableOn (Function.uncurry f) (Icc 0 τ ×ˢ K) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hfc.continuousOn.integrableOn_compact (isCompact_Icc.prod hKc)
  have hon2 : IntegrableOn (Function.uncurry f) (Ioc 0 τ ×ˢ (univ : Set (ℝ × ℝ)))
      (volume.prod volume) := by
    refine (hon.mono_set (prod_mono Ioc_subset_Icc_self le_rfl)).of_forall_sdiff_eq_zero
      (measurableSet_Ioc.prod MeasurableSet.univ) ?_
    rintro ⟨s, t⟩ ⟨⟨hs, -⟩, hnot⟩
    have ht : t ∉ K := fun ht => hnot ⟨hs, ht⟩
    simp only [Function.uncurry_apply_pair, hfdef, image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioc 0 τ)).prod volume) := by
    have := hon2
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at this
    exact this
  have hswap := MeasureTheory.integral_integral_swap hint
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ]
    have h1 := hint.integral_prod_left
    refine h1.congr (Eventually.of_forall fun s => ?_)
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hfdef,
      Function.uncurry_apply_pair]
  · rw [intervalIntegral.integral_of_le hτ]
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simp only [hfdef] at hswap
    rw [hswap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [intervalIntegral.integral_of_le hτ, integral_const_mul]

/-- (D) joint continuity, in log coordinates, of a family that is continuous on `Q0` slice-wise and
uniformly Lipschitz in the time parameter (time clamped to `[0,τ]`). -/
theorem continuous_logPull_family {G : ℝ → Fn} {τ : ℝ} (hτ : 0 ≤ τ) {K : NNReal}
    (hcont : ∀ s ∈ Icc 0 τ, ContinuousOn (Function.uncurry (G s)) Work.FTS.EllipticEst.Q0)
    (hlip : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |G s z θ - G t z θ| ≤ K * |s - t|) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G (projIcc 0 τ hτ q.1 : ℝ)) q.2) := by
  refine continuous_prod_of_continuous_lipschitzWith _ K (fun a => ?_) (fun x => ?_)
  · have hc := hcont _ (projIcc 0 τ hτ a).2
    exact ContinuousOn.comp_continuous hc continuous_logMap_quad.1 continuous_logMap_quad.2
  · refine LipschitzWith.of_dist_le_mul (fun s t => ?_)
    have hmem := continuous_logMap_quad.2 x
    have h1 := hlip _ (projIcc 0 τ hτ s).2 _ (projIcc 0 τ hτ t).2 _ _ hmem.1 ⟨hmem.2.1, hmem.2.2⟩
    have h2 : dist (projIcc 0 τ hτ s) (projIcc 0 τ hτ t) ≤ 1 * dist s t :=
      (LipschitzWith.projIcc hτ).dist_le_mul s t
    rw [Real.dist_eq]
    rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq, one_mul] at h2
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 K.2)

/-- (E) **one Picard step preserves `SmoothOpen`** (generic form): if the integrand has the mollified
form `F (slice W s) = J_ε (G s) − c s · bump` on `Q0` with `G` jointly continuous (log coordinates,
time clamped), and the integrand is interval-integrable in `s` at every point (the `cont(n)` component
of the proved `iter_cont_meas`), then `h₀ + ∫₀^τ F (slice W s) ds` is `SmoothOpen`. -/
theorem smoothOpen_picard_slice {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    {h₀ : Fn} {F : Fn → Fn} {W : Fam} {G : ℝ → Fn} {c : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hF : ∀ s ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      F (slice W s) z θ = Jeps ρ ε (G s) z θ - c s * bump z θ)
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G (projIcc 0 τ hτ q.1 : ℝ)) q.2))
    (hFint : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun s => F (slice W s) z θ) volume 0 τ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice W s) z θ) := by
  set Gp : ℝ → Fn := fun s => G (projIcc 0 τ hτ s : ℝ) with hGp
  set Ψ : Fn := fun z θ => ∫ s in (0 : ℝ)..τ, Gp s z θ with hΨdef
  have hlogΨ : logPull Ψ = fun x => ∫ s in (0 : ℝ)..τ, logPull (Gp s) x := rfl
  have hΨ : Continuous (logPull Ψ) := by
    rw [hlogΨ]
    have hc : Continuous (Function.uncurry (fun (x : ℝ × ℝ) (s : ℝ) => logPull (Gp s) x)) :=
      hG.comp continuous_swap
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 τ
  refine smoothOpen_of_mollForm hρ hε (c := ∫ s in (0 : ℝ)..τ, c s) h0 hΨ ?_
  intro z θ hz hθ
  have hB := conv_intervalIntegral_swap (k := Jker ρ ε) (contDiff_Jker ρ hρ ε 0).continuous
    (hasCompactSupport_Jker ρ hρ hε) (H := fun s => logPull (Gp s)) hG hτ (sOf z, zetaOf θ)
  have hJs : (fun s => Jeps ρ ε (Gp s) z θ) = fun s =>
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull (Gp s)) (sOf z, zetaOf θ) :=
    funext fun s => Jeps_eq_conv ρ ε _ hz hθ
  have hJΨ : Jeps ρ ε Ψ z θ = (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => ∫ s in (0 : ℝ)..τ, logPull (Gp s) y)) (sOf z, zetaOf θ) := by
    rw [Jeps_eq_conv ρ ε Ψ hz hθ, hlogΨ]
  have hA : IntervalIntegrable (fun s => Jeps ρ ε (Gp s) z θ) volume 0 τ := by
    rw [hJs]; exact hB.1
  have hAint : ∫ s in (0 : ℝ)..τ, Jeps ρ ε (Gp s) z θ = Jeps ρ ε Ψ z θ := by
    rw [hJs, hB.2, hJΨ]
  have hFeq : ∀ s ∈ Set.uIcc (0 : ℝ) τ,
      F (slice W s) z θ = Jeps ρ ε (Gp s) z θ - c s * bump z θ := by
    intro s hs
    rw [Set.uIcc_of_le hτ] at hs
    have hp : (projIcc 0 τ hτ s : ℝ) = s := by rw [projIcc_of_mem hτ hs]
    simp only [hGp, hp]
    exact hF s hs z θ hz hθ
  have hcb : ∫ s in (0 : ℝ)..τ, c s * bump z θ
      = ∫ s in (0 : ℝ)..τ, (Jeps ρ ε (Gp s) z θ - F (slice W s) z θ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    show c s * bump z θ = Jeps ρ ε (Gp s) z θ - F (slice W s) z θ
    rw [hFeq s hs]; ring
  have hsub := intervalIntegral.integral_sub hA (hFint z θ hz hθ)
  have hmc : ∫ s in (0 : ℝ)..τ, c s * bump z θ = (∫ s in (0 : ℝ)..τ, c s) * bump z θ :=
    intervalIntegral.integral_mul_const _ _
  show h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice W s) z θ
    = h₀ z θ + Jeps ρ ε Ψ z θ - (∫ s in (0 : ℝ)..τ, c s) * bump z θ
  linarith [hcb, hsub, hmc, hAint]

/-- (F) **`hkeepIter`'s `SmoothOpen` clause, concretely** (the `XBall` class): if the `n`-th Picard
iterate stays in `XBall` on `[0,δ]`, is `EpsSq`-Lipschitz in time (the Minkowski bound of the engine,
`EpsSq (w_s − w_t) ≤ L (s−t)²`), and its integrand is interval-integrable at each point (the `cont(n)`
component of `iter_cont_meas`), then every slice of the `(n+1)`-st iterate is `SmoothOpen`. -/
theorem smoothOpen_iter_succ_XBall {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (n : ℕ)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hP : ∀ s ∈ Icc 0 δ, XBall α ρ ε R C₀
      (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))
    (hEq : ∀ s ∈ Icc 0 δ, ∀ t ∈ Icc 0 δ, EpsSq α (fun z θ =>
      slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s z θ
        - slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hFint : ∀ τ ∈ Icc 0 δ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun s => Feps α ρ ε Φs E
        (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ) volume 0 τ)
    {τ : ℝ} (hτ : τ ∈ Icc 0 δ) :
    Work.FTS.EllipticEst.SmoothOpen
      (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) := by
  set w : ℝ → Fn := fun s =>
    slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s with hw
  set G : ℝ → Fn := fun s =>
    Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε (w s))) with hGdef
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsLocalPStar.profRHS_pre_sub_pt_le_Sq
    (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hEll hstar hml hR
  have hsub : ∀ s ∈ Icc 0 τ, s ∈ Icc 0 δ := fun s hs => ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hcont : ∀ s ∈ Icc 0 τ, ContinuousOn (Function.uncurry (G s)) Work.FTS.EllipticEst.Q0 :=
    fun s hs => ((smoothOpen_profRHS_of_classC hα hEll hstar
      (hP s (hsub s hs)).classC).forall 0).continuousOn
  set K : NNReal := ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg _)⟩ with hK
  have hlip : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |G s z θ - G t z θ| ≤ K * |s - t| := by
    intro s hs t ht z θ hz hθ
    have hPs := hP s (hsub s hs)
    have hPt := hP t (hsub t ht)
    have h1 := hC hPs.smoothOpen hPt.smoothOpen hPs.mem hPs.sq_le hPt.mem hPt.sq_le
      hPs.classC hPt.classC hPs.ball hPt.ball z θ hz hθ.1 hθ.2
    have h2 : Real.sqrt (EpsSq α (fun z θ => w s z θ - w t z θ)) ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s (hsub s hs) t (hsub t ht))
    calc |G s z θ - G t z θ| ≤ C * Real.sqrt (EpsSq α (fun z θ => w s z θ - w t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (K : ℝ) * |s - t| := by
          show C * (Real.sqrt Lw * |s - t|) = (C * Real.sqrt Lw) * |s - t|; ring
  have hG := continuous_logPull_family hτ.1 hcont hlip
  have hF : ∀ s ∈ Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Feps α ρ ε Φs E (w s) z θ = Jeps ρ ε (G s) z θ
        - (Work.Construction.L12 (Jeps ρ ε (G s)) 0 / pzNorm) * bump z θ := by
    intro s _ z θ _ _
    show Pz (Jeps ρ ε (G s)) z θ = _
    rw [Pz_apply]
  exact smoothOpen_picard_slice (W := Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n)
    hρ hε hτ.1 h0 hF hG (hFint τ hτ)

end Work.FTS.EpsEngine.SORuling
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps
open Work.FTS.EpsEngine
open Work.FTS.GalFields (Xn5)
open Work.Spaces (HkSq HkNorm HkMem HkSq_nonneg HkNorm_nonneg)
open Work.FTS.Nonlin (Xn)
open Work.FTS.EllipticEst (SmoothOpen smoothOpen_iff_forall)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem hkSqFepsSub_le {α C₁ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Work.FTS.Galerkin.Fn,
      Work.FTS.EpsEngine.XBall α ρ ε R C₁ u → Work.FTS.EpsEngine.XBall α ρ ε R C₁ v →
      Work.Spaces.HkSq α 6 (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ C * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε
  -- ## the five constants of the proof
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CD, hCDpos, hCD⟩ := Work.FTS.StrongEps.EpsLocalPStar.HkSq_Wp_sub_le_of_ClassC ρ hρ
  obtain ⟨CW, hCWpos, hCW⟩ := Work.FTS.StrongEps.EpsLocalPStar.exists_Wp_bound_of_EpsMem ρ hρ
  obtain ⟨CP, hCPpos, hCP⟩ :=
    Work.FTS.EpsEngine.profRHSDiffEpsSq (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  -- ## the uniform `ℋ⁶`-size `BS` of a projected-mollified profile of the ball
  set BS : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]
    have h1 : 0 ≤ CW / ε := div_nonneg hCWpos.le hε0.le
    exact mul_nonneg (mul_nonneg hCWpos.le (pow_nonneg h1 6)) (by linarith)
  -- ## the composite constant
  set Λ : ℝ := CP * (K * (1 + 2 * BS) ^ 2) ^ 2 * CD * (CD / ε) ^ 12 with hΛdef
  -- ## the a-priori data of the pre-mollified profile, at the size `BS`
  obtain ⟨_, -, hXData⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₁) (B := BS)
      hα hEll hstar hml hBS0
  refine ⟨max 1 (CH * (CH / ε) ^ 12 * Λ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hu hv
  -- ## the honest membership of the datum difference
  have hak_u : Work.FTS.StrongEps.EpsSqTools.AK α u :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry (Work.Spaces.aesm_of_continuousOn_Qd
      (Function.uncurry u)
      (((smoothOpen_iff_forall u).mp (XBall.smoothOpen hu)) 0).continuousOn)
  have hak_v : Work.FTS.StrongEps.EpsSqTools.AK α v :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry (Work.Spaces.aesm_of_continuousOn_Qd
      (Function.uncurry v)
      (((smoothOpen_iff_forall v).mp (XBall.smoothOpen hv)) 0).continuousOn)
  have hmem_uv : EpsMem α (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hak_u hak_v (XBall.mem hu) (XBall.mem hv)
  set S : ℝ := EpsSq α (fun z θ => u z θ - v z θ) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact EpsSq_nonneg α _
  -- ## the `ℋ⁵`-size of the profile difference
  have hdSq : HkSq α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) ≤ CD * (CD / ε) ^ 12 * S := by
    rw [hSdef]
    exact hCD α hα ε ⟨hε0, hε1⟩ (XBall.smoothOpen hu) (XBall.smoothOpen hv)
      (XBall.classC hu) (XBall.classC hv) hmem_uv
  have hd5 : (Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2 ≤ CD * (CD / ε) ^ 12 * S := by
    rw [Work.FTS.GalFields.Xn5, HkNorm, Real.sq_sqrt (HkSq_nonneg α 5 _)]
    exact hdSq
  -- ## the uniform sizes of the two profiles
  have hWu5 : Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR u (XBall.smoothOpen hu) (XBall.mem hu) (XBall.sq_le hu)
      5 (by norm_num)
  have hWv5 : Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR v (XBall.smoothOpen hv) (XBall.mem hv) (XBall.sq_le hv)
      5 (by norm_num)
  have hWu6 : HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR u (XBall.smoothOpen hu) (XBall.mem hu) (XBall.sq_le hu)
      6 (by norm_num)
  have hWv6 : HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR v (XBall.smoothOpen hv) (XBall.mem hv) (XBall.sq_le hv)
      6 (by norm_num)
  have hMle : 1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ 1 + 2 * BS := by linarith
  have hM0 : 0 ≤ 1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := by
    have h1 : 0 ≤ Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) := HkNorm_nonneg α 5 _
    have h2 : 0 ≤ Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := HkNorm_nonneg α 5 _
    linarith
  -- ## the difference of the pre-mollified right-hand sides
  set Δ : Fn := fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
      - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ with hΔdef
  obtain ⟨hΔsm0, hΔmem40, hΔxn0⟩ :=
    hK (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)
      (XBall.classC hu) (XBall.classC hv) (XBall.ball hu) (XBall.ball hv)
  have hΔsm : SmoothOpen Δ := by rw [hΔdef]; exact hΔsm0
  have hΔmem4 : HkMem α 4 Δ := by rw [hΔdef]; exact hΔmem40
  have hΔxn : Xn α Δ ≤ K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
      * Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) := by
    rw [hΔdef]; exact hΔxn0
  obtain ⟨hΔmemE0, hΔSqE0⟩ :=
    hCP (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)
      (XBall.classC hu) (XBall.classC hv) (XBall.ball hu) (XBall.ball hv)
  have hΔmem : EpsMem α Δ := by rw [hΔdef]; exact hΔmemE0
  have hΔSq : EpsSq α Δ ≤ CP * (Xn α Δ) ^ 2 := by rw [hΔdef]; exact hΔSqE0
  -- ## the squared `ℋ⁴`-size of `Δ`
  have hkey : (Xn α Δ) ^ 2 ≤ (K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S) := by
    have h1 : (Xn α Δ) ^ 2
        ≤ (K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
              + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
            * Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
                - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2 :=
      pow_le_pow_left₀ (HkNorm_nonneg α 4 Δ) hΔxn 2
    have h2 : K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
          + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2 ≤ K * (1 + 2 * BS) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hMle 2) hKpos.le
    have h3 : (K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
              + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
            * Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
                - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2
        ≤ (K * (1 + 2 * BS) ^ 2) ^ 2
          * (Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
              - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hKpos.le (sq_nonneg _)) h2 2) (sq_nonneg _)
    exact h1.trans (h3.trans (mul_le_mul_of_nonneg_left hd5 (sq_nonneg _)))
  have hΔSq_le : EpsSq α Δ
      ≤ CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S)) :=
    hΔSq.trans (mul_le_mul_of_nonneg_left hkey hCPpos.le)
  -- ## the `ℋ⁶`-bound of the mollified projected difference
  have hfin0 : HkSq α 6 (Pz (Jeps ρ ε Δ)) ≤ CH * (CH / ε) ^ 12 * EpsSq α Δ :=
    hCH α hα ε hε0 hε1 6 (by norm_num) Δ hΔsm hΔmem
  have hfin1 : HkSq α 6 (Pz (Jeps ρ ε Δ))
      ≤ CH * (CH / ε) ^ 12
        * (CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S))) :=
    hfin0.trans (mul_le_mul_of_nonneg_left hΔSq_le (by positivity))
  -- ## the identification `Feps u − Feps v = Pz (J_ε Δ)`
  have hsmΦu : SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (XBall.classC hu) (XBall.ball hu) hWu6).1
  have hsmΦv : SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (XBall.classC hv) (XBall.ball hv) hWv6).1
  have hmemΦu : HkMem α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (XBall.classC hu) (XBall.ball hu) hWu6).2.1
  have hmemΦv : HkMem α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (XBall.classC hv) (XBall.ball hv) hWv6).2.1
  have hJsu : SmoothOpen (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) :=
    smoothOpen_Jeps ρ hρ hε0 ((smoothOpen_iff_forall _).mp hsmΦu)
  have hJsv : SmoothOpen (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) :=
    smoothOpen_Jeps ρ hρ hε0 ((smoothOpen_iff_forall _).mp hsmΦv)
  have hJmu : HkMem α 4 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) :=
    HkMem_Jeps hρ.moll hα hε0 ((smoothOpen_iff_forall _).mp hsmΦu) hmemΦu
  have hJmv : HkMem α 4 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) :=
    HkMem_Jeps hρ.moll hα hε0 ((smoothOpen_iff_forall _).mp hsmΦv) hmemΦv
  have hFu : Feps α ρ ε Φs E u = Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) := rfl
  have hFv : Feps α ρ ε Φs E v = Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) := rfl
  have hJsub : Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))
      - Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))
      = Jeps ρ ε (fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
        - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ) :=
    Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε0 hsmΦu hsmΦv
  have hL12 : Work.Construction.L12 (fun z θ => Jeps ρ ε
        (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) z θ
      - Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) z θ) 0
      = Work.Construction.L12 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) 0
        - Work.Construction.L12 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJsu hJsv hJmu hJmv 0 (by simp [Work.Spaces.Iz])
  have hPzsub : Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)))
      - Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)))
      = Pz (Jeps ρ ε (fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
        - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ)) := by
    rw [Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL12]
    exact congrArg Pz hJsub
  have hident : (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ) = Pz (Jeps ρ ε Δ) := by
    have hh : (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        = Feps α ρ ε Φs E u - Feps α ρ ε Φs E v := rfl
    rw [hh, hFu, hFv]
    rw [hΔdef]
    exact hPzsub
  -- ## the assembly
  have harith : CH * (CH / ε) ^ 12
        * (CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S)))
      = (CH * (CH / ε) ^ 12 * Λ) * S := by
    rw [hΛdef]; ring
  rw [hident]
  calc HkSq α 6 (Pz (Jeps ρ ε Δ))
      ≤ CH * (CH / ε) ^ 12
          * (CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S))) := hfin1
    _ = (CH * (CH / ε) ^ 12 * Λ) * S := harith
    _ ≤ max 1 (CH * (CH / ε) ^ 12 * Λ) * S := mul_le_mul_of_nonneg_right (le_max_right _ _) hS0

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end

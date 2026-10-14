import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_LocDatum3a.L12_Jeps_locG6
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.r1Block.regExport_hVop
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS.EpsEngine.LimSmoothOpenEngine =====
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
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **`hpair` from the a-priori bounds**: the ordered geometric pair bound of two Picard iterates,
in the form consumed by `smoothOpen_limFam_slice`, from the two components `hB0`/`hBK` of
`iter_bounds_v4`. -/
theorem epsPair_of_iter_bounds {α δ q : ℝ} {F : Fn → Fn} {h₀ : Fn} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hB0 : ∀ M : ℕ, 1 ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (iter F h₀ M) s z θ - h₀ z θ) ≤ q)
    (hBK : ∀ (M K : ℕ), 1 ≤ K → K ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (iter F h₀ M) s z θ - slice (iter F h₀ K) s z θ) ≤ q ^ (K + 1)) :
    ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      EpsSq α (fun z θ => slice (iter F h₀ n) s z θ - slice (iter F h₀ m) s z θ) ≤ q ^ n := by
  intro n m s hs hnm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hzero : (fun z θ => slice (iter F h₀ 0) s z θ
          - slice (iter F h₀ 0) s z θ) = fun _ _ => (0 : ℝ) := by
        funext z θ; simp
      rw [hzero, EpsSq_zero, pow_zero]
      norm_num
    · rw [EpsSq_sub_comm, pow_zero]
      refine (hB0 m hm s hs).trans hq1.le
  · rw [EpsSq_sub_comm]
    refine (hBK m n hn hnm s hs).trans ?_
    exact pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ n)

/-- **The `SmoothOpen` clause of `hlimP`** from the engine's data: the `X`-ball invariant `hP`, the
time-Lipschitz bound `hEq`, the a-priori bounds `hB0`/`hBK`/`hwpt` of `iter_bounds_v4`, and the
point integrability `hFint` of the scheme's right-hand side. -/
theorem smoothOpen_limFam_slice_of_iter_bounds {α C₀ R Ce Cs Lw δ q Cpt : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀) (hq0 : 0 ≤ q) (hq1 : q < 1) (hCpt : 0 ≤ Cpt)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (epsIter α ρ ε Φs E h₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ n) s z θ
        - slice (epsIter α ρ ε Φs E h₀ n) t z θ) ≤ Lw * (s - t) ^ 2)
    (hB0 : ∀ M : ℕ, 1 ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ M) s z θ - h₀ z θ) ≤ q)
    (hBK : ∀ (M K : ℕ), 1 ≤ K → K ≤ M → ∀ s : ℝ, s ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ M) s z θ
        - slice (epsIter α ρ ε Φs E h₀ K) s z θ) ≤ q ^ (K + 1))
    (hwpt : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |wseq (Feps α ρ ε Φs E) h₀ n s z θ| ≤ δ * Cpt * (Real.sqrt q) ^ n)
    (hFint : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun σ => Feps α ρ ε Φs E
        (slice (epsIter α ρ ε Φs E h₀ n) σ) z θ) volume 0 s)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    Work.FTS.EllipticEst.SmoothOpen (slice (epsLim α ρ ε Φs E h₀) τ) := by
  have hpair := epsPair_of_iter_bounds (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀) hq0 hq1 hB0 hBK
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqrt1 : Real.sqrt q < 1 := by
    have h2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
    nlinarith
  have hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Tendsto (fun N : ℕ => slice (epsIter α ρ ε Φs E h₀ N) s z θ) atTop
        (𝓝 (slice (epsLim α ρ ε Φs E h₀) s z θ)) :=
    tendsto_slice_iter_limFam (F := Feps α ρ ε Φs E) (h₀ := h₀) hCpt hsqrt0 hsqrt1 hwpt
  have hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n s) z θ
          - epsC α ρ ε Φs E h₀ n s * bump z θ :=
    fun n s hs z θ hz hθ =>
      slice_iter_succ_mollForm n hα hρ hε hε1 hEll hstar hml hR hLw h0 (hP n) (hEq n)
        (hFint n) hs hz hθ
  exact smoothOpen_limFam_slice hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1
    hP hEq hpair hmoll hconv hτ

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaUnifAdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The angular weight `sin(2θ)^{1-γ}` is nonnegative on the open angular interval. -/
private lemma sinTwo_rpow_nonneg {α θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi / 2) :
    0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])) _

/-- **The uniform angular flatness `ThetaUnif` is closed under addition** (of profiles smooth on
the open quadrant).  This is the `ε`-`δ` bookkeeping of the mollifier: the angular traces of a sum
are the sums of the traces, and `(A + B)² ≤ 2A² + 2B²` splits the tolerance `ε'` into the two
halves `ε'/2`. -/
theorem ThetaUnifAdd {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h1 : Work.FTS.EpsEngine.ThetaUnif α k f) (h2 : Work.FTS.EpsEngine.ThetaUnif α k g) :
    Work.FTS.EpsEngine.ThetaUnif α k (fun z θ => f z θ + g z θ) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hFG : (fun z θ => f z θ + g z θ) = (f + g) := by
    funext z θ
    simp only [Pi.add_apply]
  rw [hFG]
  refine ⟨?_, ?_⟩
  · -- the `θ → 0⁺` end
    intro a b hab ε' hε'
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h1.t0 a b hab (ε' / 4) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := h2.t0 a b hab (ε' / 4) (by linarith)
    refine ⟨min (min δ₁ δ₂) (Real.pi / 4),
      lt_min (lt_min hδ₁pos hδ₂pos) (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθ hθδ z hz
    have hθπ : θ < Real.pi / 2 := by
      have h : θ < Real.pi / 4 := lt_of_lt_of_le hθδ (min_le_right _ _)
      linarith [Real.pi_pos]
    have hθ₁ : θ < δ₁ :=
      lt_of_lt_of_le hθδ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hθ₂ : θ < δ₂ :=
      lt_of_lt_of_le hθδ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn hV
      (hf (a + b)) (hg (a + b)) a b le_rfl (z, θ) ⟨hz, hθ, hθπ⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      sinTwo_rpow_nonneg hθ hθπ
    have hsq : (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ 2 * (Work.Spaces.mixed b a f z θ) ^ 2
          + 2 * (Work.Spaces.mixed b a g z θ) ^ 2 := by
      rw [hadd]
      nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ)]
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (Work.Spaces.mixed b a f z θ) ^ 2
              + 2 * (Work.Spaces.mixed b a g z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hs
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
      _ ≤ 2 * (ε' / 4) + 2 * (ε' / 4) := by
          linarith [hδ₁ θ hθ hθ₁ z hz, hδ₂ θ hθ hθ₂ z hz]
      _ = ε' := by ring
  · -- the `θ → (π/2)⁻` end
    intro a b hab ε' hε'
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h1.t1 a b hab (ε' / 4) (by linarith)
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := h2.t1 a b hab (ε' / 4) (by linarith)
    refine ⟨min (min δ₁ δ₂) (Real.pi / 4),
      lt_min (lt_min hδ₁pos hδ₂pos) (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθπ hθδ z hz
    have hδle₁ : min (min δ₁ δ₂) (Real.pi / 4) ≤ δ₁ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hδle₂ : min (min δ₁ δ₂) (Real.pi / 4) ≤ δ₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hθ₁ : Real.pi / 2 - δ₁ < θ :=
      lt_of_le_of_lt (by linarith [hδle₁]) hθδ
    have hθ₂ : Real.pi / 2 - δ₂ < θ :=
      lt_of_le_of_lt (by linarith [hδle₂]) hθδ
    have hθpos : 0 < θ := by
      have h' : Real.pi / 2 - Real.pi / 4
          ≤ Real.pi / 2 - min (min δ₁ δ₂) (Real.pi / 4) := by
        linarith [min_le_right (min δ₁ δ₂) (Real.pi / 4)]
      linarith [Real.pi_pos]
    have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn hV
      (hf (a + b)) (hg (a + b)) a b le_rfl (z, θ) ⟨hz, hθpos, hθπ⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      sinTwo_rpow_nonneg hθpos hθπ
    have hsq : (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ 2 * (Work.Spaces.mixed b a f z θ) ^ 2
          + 2 * (Work.Spaces.mixed b a g z θ) ^ 2 := by
      rw [hadd]
      nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ)]
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (f + g) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (2 * (Work.Spaces.mixed b a f z θ) ^ 2
              + 2 * (Work.Spaces.mixed b a g z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hs
      _ = 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2) := by ring
      _ ≤ 2 * (ε' / 4) + 2 * (ε' / 4) := by
          linarith [hδ₁ θ hθπ hθ₁ z hz, hδ₂ θ hθπ hθ₂ z hz]
      _ = ε' := by ring

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaUnifInterval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false



/-- **The elementary averaging arithmetic.**  If `|x| ≤ √(εt/B)·L` with `B > 0`, `εt > 0`,
`L ≥ 0` and `εt·L² ≤ ε'`, then `B·x² ≤ ε'`.  (Here `x = ∫_a^b g` and `√(εt/B)` is the supremum
bound on `|g s|` coming from `B·(g s)² ≤ εt`.) -/
private lemma core_bound {B εt ε' x L : ℝ} (hB : 0 < B) (hεt : 0 < εt) (hL : 0 ≤ L)
    (hεtL : εt * L ^ 2 ≤ ε') (hx : |x| ≤ Real.sqrt (εt / B) * L) : B * x ^ 2 ≤ ε' := by
  have hM0 : 0 ≤ Real.sqrt (εt / B) := Real.sqrt_nonneg _
  have hMsq : Real.sqrt (εt / B) ^ 2 = εt / B := Real.sq_sqrt (le_of_lt (div_pos hεt hB))
  have hx2 : x ^ 2 ≤ (Real.sqrt (εt / B) * L) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have h2 : B * x ^ 2 ≤ B * (Real.sqrt (εt / B) * L) ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 (le_of_lt hB)
  have h3 : B * (Real.sqrt (εt / B) * L) ^ 2 = εt * L ^ 2 := by
    rw [mul_pow, hMsq]
    field_simp
  linarith [h2, h3]


end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaUnifJeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false




end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.hjoint_HkIntegrand_epsRHSP_fam_of_gate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The theorem -/

theorem hjoint_HkIntegrand_epsRHSP_fam_of_gate {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {ε : ℝ} {g : Work.FTS.Galerkin.Fam} {k : ℕ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ) ≤ Lw * (s - t) ^ 2) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  classical
  -- the slice-determined profile family
  set B : ℝ → ℝ → ℝ → ℝ := fun s => Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) with hB
  -- ## Step 1: the slotwise measurability in the fake time (the sibling gate)
  have hslot : ∀ (j i : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (B s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro j i z θ hz hθ
    have h := hmeas_slot_epsRHSP_fam_of_gate hα hρ hε hε1 hEll hstar hml hR hLw hP hEq
      j i hz hθ
    simpa only [hB, epsRHSP_eq_Feps_slice] using h
  -- ## Step 2: each slice is `C^∞` on the open quadrant
  have hsm : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (B s) := fun s hs =>
    smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (u := Work.FTS.Galerkin.slice g s) hα hρ hε hEll hstar (hP s hs).classC
  -- ## Step 3: the truncated integrand family
  let H : ℝ → ℝ → ℝ → ℝ := fun s z θ =>
    if s ∈ Set.Icc 0 δ then
      (if (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) then
        Work.Spaces.HkIntegrand α k (B s) z θ
      else 0)
    else 0
  -- ### continuity on the open quadrant, for every `s ∈ [0,δ]`
  have hcont : ∀ s ∈ Set.Icc 0 δ, ContinuousOn (fun q : ℝ × ℝ => H s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro s hs
    have hq : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (B s) q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hsm s hs).continuousOn_HkIntegrand α k
    refine hq.congr ?_
    intro q hq'
    have hq'' : (q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := hq'
    dsimp only [H]
    rw [if_pos hs, if_pos hq'']
  -- ### vanishing outside the open quadrant
  have hzero : ∀ s ∈ Set.Icc 0 δ, ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → H s q.1 q.2 = 0 := by
    intro s hs q hq
    have hq' : ¬ ((q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hq
    dsimp only [H]
    rw [if_pos hs, if_neg hq']
  -- ### measurability in `s`, at every fixed `(z,θ)`
  have hmeas : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => H s q.1 q.2)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro q
    by_cases hq : q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
    · have hslotq : MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) q.1 q.2)
          (MeasureTheory.volume.restrict (Set.Icc 0 δ)) :=
        aesm_HkIntegrand_of_slots (fun j i => hslot j i q.1 q.2 hq.1 hq.2)
      have h1 : MeasureTheory.AEStronglyMeasurable
          ((Set.Icc 0 δ).indicator (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) q.1 q.2))
          MeasureTheory.volume :=
        MeasAlt.aesm_indicator_of_aesm_restrict measurableSet_Icc hslotq
      refine (h1.mono_measure Measure.restrict_le_self).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      rw [Set.indicator_of_mem hs]
      have hq'' : (q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := hq
      dsimp only [H]
      rw [if_pos hs, if_pos hq'']
    · have hconst : (fun s : ℝ => H s q.1 q.2) = fun _ : ℝ => (0 : ℝ) := by
        funext s
        by_cases hs : s ∈ Set.Icc 0 δ
        · have hq' : ¬ ((q.1, q.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hq
          dsimp only [H]
          rw [if_pos hs, if_neg hq']
        · dsimp only [H]
          rw [if_neg hs]
      rw [hconst]
      exact aestronglyMeasurable_const
  -- ## Step 4: Carathéodory on the horizon
  have hbig := aesm_uncurry_restricted (A := Set.Icc 0 δ) measurableSet_Icc (g := H)
    hcont hzero hmeas
  have hle : (MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ (MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod MeasureTheory.volume :=
    Measure.prod_mono le_rfl
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  refine (hbig.mono_measure hle).congr ?_
  -- ## Step 5: a.e. comparison with the statement's integrand
  -- a.e. `θ` lies in the open interval, a.e. `z` is positive
  have hz_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
    have h : MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Work.Spaces.Iz]
      exact (Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
    rw [h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hth_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    have h : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ]
      exact (Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))).symm
    rw [h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hQae : ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (s := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)).mpr ?_
    filter_upwards [hz_ae] with z hz
    filter_upwards [hth_ae] with θ hθ
    exact ⟨hz, hθ⟩
  have haeA : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))), p.1 ∈ Set.Icc 0 δ := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : ℝ × (ℝ × ℝ) | p.1 ∈ Set.Icc 0 δ})
      (measurableSet_Icc.preimage measurable_fst)).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    exact Filter.Eventually.of_forall fun q => hs
  have haeQ : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))),
      (p.2.1, p.2.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : ℝ × (ℝ × ℝ) | (p.2.1, p.2.2) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)})
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet.preimage measurable_snd)).mpr ?_
    refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [hQae] with q hq
    exact hq
  filter_upwards [haeA, haeQ] with p hpA hpQ
  dsimp only [H]
  rw [if_pos hpA, if_pos hpQ, hB, epsRHSP_eq_Feps_slice]

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS_RegExport.Vz7Eslot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.Vz7Eslot` — the producers from ONE quantitative clause instead of `hVop`

`Vz7Split.lean` shows that the frozen field `VelPkg.vz0` is *equivalent* to the axial-strain sign
bound `hVop` (i.e. assuming `hVop` assumes the conclusion).  This file replaces that assumption by
a clause that is **strictly weaker** and **satisfiable by the construction**:

    ESlotBd α Cs g E  :  ∃ CE,
      (∀ τ z θ, 0 ≤ τ → quadrant → |V(E (slice g τ)) z θ| ≤ CE·pExp α)      -- the elliptic slot
      ∧ 4·pExp α + 2·Cs·(pExp α)² + 2·CE·(pExp α)² ≤ 1/2                    -- the tie

where `Cs` is the constant of the frozen `hStar`.  The first conjunct is the elliptic `V`-slot of
`EllPkgK` (`HkNorm αG 6 (V(ΦTil u (Eu))) ≤ Ce·HkNorm αG 6 u`) with the `pExp α` factor *kept*
(so at the wire's `pExp α ≤ 2.4·10⁻⁸` any explicitly bounded constant satisfies it), and the second
is pure arithmetic on the wire's numbers.

Main results:

* `Work.FTS_RegExport.hVop_of_ESlotBd` — **`hVop` from `ESlotBd`** (so the sign bound is *derived*,
  not assumed), via `vz7_nonneg_wire_of_star` (star slot discharged from `hStar.VW`, elliptic slot
  from the clause, arithmetic from the tie) and the closed form of `Vz7`;
* `Work.FTS_RegExport.velPkg_of_ESlotBd`, `…r5Parts_of_ESlotBd`, `…regExport_of_ESlotBd` — the three
  producers of `RegExportIface/Producers.lean` at the frozen binder list with `ESlotBd` as the
  **single** extra hypothesis, obtained by feeding `hVop_of_ESlotBd` into the already proved
  `velPkg_proved_noHdat` / `r5Parts_hVP` / `regExport_hVop`.

Consequently the whole remaining content of `RX-VP` is the existence of a uniform `αG`-rate bound
on `V(E (slice g τ))` with a modest constant — a *single* elliptic estimate, uniform in `τ`, and
not a positivity assumption.  See `NOTES_FINAL.md` §20.
-/

set_option linter.unusedVariables false

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The single quantitative clause that replaces `hVop`.**  `ESlotBd α Cs g E` says: the elliptic
`V`-slot `V(E (slice g τ))` is uniformly `O(pExp α)` (first conjunct) and the resulting arithmetic
criterion (second conjunct, with the star constant `Cs`) holds. -/
def ESlotBd (α Cs : ℝ) (g : Fam) (E : Fn → Fn) : Prop :=
  ∃ CE : ℝ, (∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (E (slice g τ)) z θ| ≤ CE * Work.FTS.Regularity.pExp α)
    ∧ 4 * Work.FTS.Regularity.pExp α
        + 2 * Cs * (Work.FTS.Regularity.pExp α) ^ 2
        + 2 * CE * (Work.FTS.Regularity.pExp α) ^ 2 ≤ 1 / 2

/-- **`hVop` from `ESlotBd`.**  The pointwise axial-strain lower bound of the producer `velPkg`
follows from the clause, with no positivity assumption. -/
theorem hVop_of_ESlotBd {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hcl : ESlotBd α Cs g ⇑E) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        ≤ 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ := by
  obtain ⟨CE, hVeu, htie⟩ := hcl
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the pointwise slice identity on the quadrant
  have hslice : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ
        = Φs z θ + E (slice g τ) z θ := by
    intro τ a b hτ' ha hb hb2
    have h1 := Work.FTS_RegExport.RXT.slice_PhiR_eq (α := α) (Φs := Φs) (E := E) (g := g)
      hτ' ha hb hb2
    show slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ a b = Φs a b + E (slice g τ) a b
    rw [h1]
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.FinalV2.slice_tauExt g hτ']
  -- smoothness of the whole slice and of its two summands
  have hsmΦs : ContDiffOn ℝ 3 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φs).mp hStar.smooth 3
  have hsmEu : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (Function.uncurry (E (slice g τ))) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ'
    have hsm : ContDiffOn ℝ 3 (Function.uncurry (slice
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)) Work.FTS.EllipticEst.Q0 :=
      Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
        (Φs := Φs) (E := E) (g := g) hEL3 hStar hOK τ hτ'
    exact (hsm.sub hsmΦs).congr (fun p hp =>
      (show E (slice g τ) p.1 p.2 = slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ p.1 p.2
          - Φs p.1 p.2 by
        have h1 := hslice τ p.1 p.2 hτ' hp.1 hp.2.1 hp.2.2
        show E (slice g τ) p.1 p.2 = slice (Work.FTS.RegExportIface.psiR α Φs E
          (Work.FTS.FinalV2.tauExt g)) τ p.1 p.2 - Φs p.1 p.2
        rw [h1]; ring))
  -- differentiability of the three `θ`-slices at every point of the quadrant
  have hdΦ : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => slice
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ') θ := by
    intro τ a b hτ' ha hb hb2
    exact Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice
      (f := slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)
      (Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
        (Φs := Φs) (E := E) (g := g) hEL3 hStar hOK τ hτ') ha hb hb2
  have hdΦs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => Φs z θ') θ := fun a b ha hb hb2 =>
    Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice hsmΦs ha hb hb2
  have hdu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => E (slice g τ) z θ') θ := fun τ a b hτ' ha hb hb2 =>
    Work.FTS_RegExport.RXVP.NoHdat.vz7_differentiableAt_tslice (hsmEu τ hτ') ha hb hb2
  -- the clock bound, in the `maxMu` form of the producer
  have hmu : ∀ τ : ℝ, 0 ≤ τ →
      |Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2 := by
    intro s hs
    have h : Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E g) g s
        = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g s := by
      simp only [Work.FTS.Final.maxMu, max_eq_left hs]
    rw [h]
    exact hμ.1 s hs
  -- the star slot, from the frozen `hStar.VW`
  have hVstar := starVop_pointwise_le (α := Work.FTS.Regularity.pExp α) (Cs := Cs)
    (Φs := Φs) hStar.VW.1 hStar.VW.2
  -- `vz0` at every point, from the sharp split and the criterion
  have hvz0 := vz7_nonneg_wire_of_star (αG := Work.FTS.Regularity.pExp α) (Cs := Cs) (CE := CE)
    (μ := Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
      (Work.FTS.Nonlin.PsiCan Φs E g) g)
    (G := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
    (Φ := Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
    (Φs := Φs) (u := fun τ => E (slice g τ))
    hαG hαG1 hStar.VW.1 hStar.VW.2 hmu hslice hdΦ hdΦs hdu hVeu htie
  -- the closed form turns it into the lower bound on `V`
  intro z θ τ hz hθ hθ2 hτ
  have hcf := Work.FTS_RegExport.RXVP.NoHdat.vz7_eq_of_vop
    (αG := Work.FTS.Regularity.pExp α) hαG
    (μ := Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
    (G := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
    (Φ := Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
    (z := z) (θ := θ) (τ := τ) hθ hθ2 (hdΦ τ z θ hτ hz hθ hθ2)
  have h0 := hvz0 τ z θ hτ hz hθ hθ2
  linarith [hcf, h0]



/-- **`regExport` (the assembly item, (7″)) from `ESlotBd`**: the frozen binder list plus the
single clause. -/
theorem regExport_of_ESlotBd {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hclock : (∀ τ : ℝ, 0 ≤ τ →
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α))
    (hcl : ESlotBd α Cs g ⇑E) :
    ∀ S > 0, Work.FTS.RegPkgGal.RegPkg' α S
      (Work.FTS.RegPkgGal.Avort (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.Bdyn (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.extG (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :=
  Work.FTS_RegExport.r1Block.regExport_hVop (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hclock
    (hVop_of_ESlotBd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK (Work.FTS.RegExportIface.ClockBd.of_clock hclock) hcl)

end Work.FTS_RegExport
end
end

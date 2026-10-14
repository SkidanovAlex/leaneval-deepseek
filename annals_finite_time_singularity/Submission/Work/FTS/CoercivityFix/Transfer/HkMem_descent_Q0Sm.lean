import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Elementaries -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`
(the extra term being `F 0`). -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- `D_z^i(D_z X) = D_z^{i+1} X` (definitional, from `D_z^{i+1} = D_z^i ∘ D_z`). -/
private lemma DzIter_Dz_eq_prv (i : ℕ) (X : Fn) :
    Work.Spaces.DzIter i (Work.Spaces.Dz X) = Work.Spaces.DzIter (i + 1) X := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-- **Both `ℋ`-weights vanish at an angle with `sin(2θ) = 0`**: the pure weight is a
division by `sin(2θ)^{η/2}` (with `η/2 ≠ 0`) and the mixed weight `W = w · sin(2θ)^{-γ/2}`
carries the factor `sin(2θ)^{-γ/2}` (with `γ/2 ≠ 0`).  Hence the whole `ℋ^k`-integrand
vanishes there, for every function. -/
private lemma HkIntegrand_eq_zero_of_sin_zero {α : ℝ} (hα : 0 < α) {k : ℕ} {f : Fn}
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs]
    exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
  have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [hs]
    refine Real.zero_rpow ?_
    have hg : 0 < Work.Spaces.gam α := by
      simp only [Work.Spaces.gam]
      linarith
    linarith
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, h1, h2, div_zero,
    mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

/-! ## Commutation of `D_z` with the iterates of `D_θ` on the open quadrant

The finite-order counterpart of `Work.Spaces.DzDthIterCommOn` (`SmoothNbhd`) and of
`QuadPorts.DzDthIterCommOn_quad` (`SmoothQuad` on the strip `(-1,∞) × (0,π/2)`): here `X`
is only `C^N` on the quadrant `Qd`, so the step from angular order `i` to `i+1` needs
`D_θ^i X` to be `C²`, i.e. `i + 1 ≤ N` — exactly the hypothesis carried below. -/

/-- The partial `∂_z` depends only on a neighbourhood of the point.  (Local copy of the
sibling statement, kept here so that the coercivity cone does not import `Work.R1G9`.) -/
private theorem pz_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ q ∈ U, f q.1 q.2 = g q.1 q.2) {Z Θ : ℝ} (hq : (Z, Θ) ∈ U) :
    Work.Spaces.pz f Z Θ = Work.Spaces.pz g Z Θ := by
  have hmem : U ∈ 𝓝 (Z, Θ) := hU.mem_nhds hq
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hev : ∀ᶠ z' in 𝓝 Z, (z', Θ) ∈ U := by
    refine Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun z' hz => hsub ?_⟩
    simpa [Metric.mem_ball, Prod.dist_eq] using hz
  have hev2 : (fun z' => f z' Θ) =ᶠ[𝓝 Z] (fun z' => g z' Θ) :=
    hev.mono fun z' hz => h (z', Θ) hz
  have := Filter.EventuallyEq.deriv_eq hev2
  simpa [Work.Spaces.pz] using this

/-- The partial `∂_θ` depends only on a neighbourhood of the point. -/
private theorem pth_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ∀ q ∈ U, f q.1 q.2 = g q.1 q.2) {Z Θ : ℝ} (hq : (Z, Θ) ∈ U) :
    Work.Spaces.pth f Z Θ = Work.Spaces.pth g Z Θ := by
  have hmem : U ∈ 𝓝 (Z, Θ) := hU.mem_nhds hq
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hev : ∀ᶠ θ' in 𝓝 Θ, (Z, θ') ∈ U := by
    refine Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun θ' hθ => hsub ?_⟩
    simpa [Metric.mem_ball, Prod.dist_eq] using hθ
  have hev2 : (fun θ' => f Z θ') =ᶠ[𝓝 Θ] (fun θ' => g Z θ') :=
    hev.mono fun θ' hθ => h (Z, θ') hθ
  have := Filter.EventuallyEq.deriv_eq hev2
  simpa [Work.Spaces.pth] using this

private lemma DthIter_Dz_comm_Qd {N : ℕ} {X : Fn} (h : Q0Sm N X) :
    ∀ i : ℕ, i + 1 ≤ N →
      Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
        (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X))) Qd := by
  intro i
  induction i with
  | zero => intro _ y _; rfl
  | succ i ih =>
      intro hi y hy
      -- `D_θ^i X` is `C²` at `y`, because `i + 2 ≤ N`
      have hN : i ≤ N := by omega
      have hC : ContDiffOn ℝ (((N - i : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DthIter i X)) Qd :=
        contDiffOn_DthIter_nat isOpen_Qd i (N - i) (by
          have h' : (((i + (N - i) : ℕ)) : WithTop ℕ∞) = (((N : ℕ)) : WithTop ℕ∞) := by
            rw [Nat.add_sub_of_le hN]
          rw [h']
          exact h)
      have h2le : (2 : WithTop ℕ∞) ≤ (((N - i : ℕ)) : WithTop ℕ∞) := by
        have : 2 ≤ N - i := by omega
        exact_mod_cast this
      have hY : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i X)) (y.1, y.2) :=
        (hC.contDiffAt (isOpen_Qd.mem_nhds hy)).of_le h2le
      have hIH : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X))) Qd := ih (by omega)
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) y.1 y.2
        = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i X)) y.1 y.2
      rw [show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) y.1 y.2 from by
            show Real.sin (2 * y.2)
                * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) y.1 y.2
              = Real.sin (2 * y.2)
                * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) y.1 y.2
            rw [pth_congr_of_isOpen isOpen_Qd hIH hy]]
      exact (Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i X) hY).symm

/-- Congruence of the iterated radial operator `D_z^j` on an open set. -/
private lemma DzIter_congr_of_isOpen {F G : Fn} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro y hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j F) y.1 y.2
        = y.1 * Work.Spaces.pz (Work.Spaces.DzIter j G) y.1 y.2
      rw [pz_congr_of_isOpen hV ih hy]

/-- **The index shift on the open quadrant**, at finite order: for `i + 1 ≤ N` and `X`
of class `Q0Sm N`, the mixed derivative of angular order `i` of `D_z X` is the mixed
derivative of order `(j+1, i)` of `X`. -/
private lemma mixed_Dz_shift_Qd {N : ℕ} {X : Fn} (h : Q0Sm N X) {i j : ℕ} (hi : i + 1 ≤ N)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ = Work.Spaces.mixed (j + 1) i X z θ := by
  have hy : (z, θ) ∈ Qd := ⟨hz, hθ⟩
  have hcongr :=
    DzIter_congr_of_isOpen isOpen_Qd (DthIter_Dz_comm_Qd h i hi) j hy
  have h1 : Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ := hcongr
  have h2 : Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i X))
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i X) := by
    rw [Work.Spaces.DzIter_add_right]
    rfl
  rw [h1, h2]
  rfl

/-! ## Pointwise domination of the `ℋ^m`-integrand of `D_z X` -/

/-- **The domination, inside the open quadrant.**  Every summand of
`HkIntegrand α m (D_z X)` is a summand of `HkIntegrand α (m+1) X`: the pure summands by
`D_z^i(D_z X) = D_z^{i+1} X`, the mixed summands by the index shift `mixed_Dz_shift_Qd`
(whose hypothesis `i + 1 ≤ m + 1` is exactly `1 ≤ i`). -/
private lemma HkIntegrand_Dz_le_succ_Qd (α : ℝ) (m : ℕ) {X : Fn} (h : Q0Sm (m + 1) X)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
      ≤ Work.Spaces.HkIntegrand α (m + 1) X z θ := by
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
      = (∑ i ∈ Finset.range (m + 1),
            (Work.Spaces.DzIter i (Work.Spaces.Dz X) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j ≤ m
              then (Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (m + 1) X z θ
      = (∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (m + 2), ∑ b ∈ Finset.range (m + 2),
            (if 1 ≤ a ∧ a + b ≤ m + 1
              then (Work.Spaces.mixed b a X z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (m + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz X) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le m
      (fun a => (Work.Spaces.DzIter a X z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq_prv i X])
  have h2 : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed j i (Work.Spaces.Dz X) z θ * W) ^ 2 else 0))
      = (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
              (if 1 ≤ i ∧ i + j ≤ m
                then (Work.Spaces.mixed (j + 1) i X z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [ite_eq_left hc, ite_eq_left hc]
      rw [mixed_Dz_shift_Qd h (by omega) hz hθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hkey := Work.Coercivity.SumShiftZ_le m
    (fun a b => (Work.Spaces.mixed b a X z θ * W) ^ 2) (fun a b => sq_nonneg _)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (m + 2), (Work.Spaces.DzIter a X z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-- **The domination on the closed domain.**  Inside the open quadrant it is
`HkIntegrand_Dz_le_succ_Qd`; at `z = 0` both integrands vanish (the radial weight), and at
the angular endpoints `sin(2θ) = 0` kills both integrands as well. -/
private lemma HkIntegrand_Dz_le_succ (α : ℝ) (hα : 0 < α) (m : ℕ) {X : Fn}
    (h : Q0Sm (m + 1) X) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α m (Work.Spaces.Dz X) z θ
      ≤ Work.Spaces.HkIntegrand α (m + 1) X z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
  · by_cases hθin : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · exact HkIntegrand_Dz_le_succ_Qd α m h hzpos hθin
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθin
      rw [HkIntegrand_eq_zero_of_sin_zero hα hs, HkIntegrand_eq_zero_of_sin_zero hα hs]

/-! ## The theorem -/

theorem HkMem_descent_Q0Sm (α : ℝ) (hα : 0 < α) (m : ℕ) {X : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.Q0Sm (m + 1) X)
    (hm : Work.Spaces.HkMem α (m + 1) X) :
    Work.Spaces.HkMem α m X ∧ Work.Spaces.HkMem α m (Work.Spaces.Dth X)
      ∧ Work.Spaces.HkMem α m (Work.Spaces.Dz X) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.LocData.HkMem_of_majorant α m
      (f := X) (M := fun z θ => Work.Spaces.HkIntegrand α (m + 1) X z θ)
      ((h.mono (Nat.le_succ m)).continuousOn_HkIntegrand α) hm.1 hm.2
      (fun z hz θ hθ => Work.Coercivity.HkIntegrand_le_succ α m X z θ)
  · exact Work.FTS.LocData.HkMem_of_majorant α m
      (f := Work.Spaces.Dth X) (M := fun z θ => Work.Spaces.HkIntegrand α (m + 1) X z θ)
      (h.dth.continuousOn_HkIntegrand α) hm.1 hm.2
      (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα m X z θ hz hθ)
  · exact Work.FTS.LocData.HkMem_of_majorant α m
      (f := Work.Spaces.Dz X) (M := fun z θ => Work.Spaces.HkIntegrand α (m + 1) X z θ)
      (h.dz.continuousOn_HkIntegrand α) hm.1 hm.2
      (fun z hz θ hθ => HkIntegrand_Dz_le_succ α hα m h z θ hz hθ)

end Work.FTS.CoercivityFix.Transfer

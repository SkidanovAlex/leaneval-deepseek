/-
# The GALERKIN area: inhabitation obligations and non-vacuity certificates

The lead's rule for this node is that **every interface structure must come with an inhabitation
obligation**.  This module records, for each structure of the area, what is known:

* `DataAdm` — inhabited by the zero datum for every `α` (`Inhabit.dataAdm_zero`); combined with
  `L₁₂(0)(0) = 0` and `|0|_{ℋ⁴} = 0 ≤ α²` this shows that the *data* hypotheses of the existence
  theorem are satisfiable (`exists_small_data`);
* `RegPkg` — inhabited by the zero family (`Inhabit.regPkg_zero`, `exists_regPkg`);
* the dynamic equation itself — satisfiable at `α = 0` by the zero family
  (`Inhabit.isDynEqOn_zero_alpha`, `exists_dynEqOn`);
* the Galerkin scheme — the raw orthonormality of the test sequence is *inconsistent with a
  degenerate test function*: the inner-product structure forces `IP 0 0 = 0 ≠ 1`, so `φ 0 ≠ 0`
  (`IP_zero_zero`, `phi_ne_zero_of_orth`, `DynInputs.phi_ne_zero`); the scheme therefore really is a
  nondegenerate orthonormal sequence, and its existence is the Gram–Schmidt step of audit N6 step 2.

What is *not* discharged here, and cannot be: the a-priori bundle `DynInputs` has fields
(`hCoeffBound`, `hCompact`, `hLimit`) whose inhabitation is exactly the paper's §Modulation
a-priori estimate and compactness argument — N5, N4 and N1.  Likewise `IsH4Inner` is inhabited only
once N2 (`Work.Coercivity.HkIPStep_isHkIP`) supplies the admissible inner product on `ℋ⁴`.  The
zero-datum computations below are exactly the boundary of what is provable before N1/N2/N4/N5 land;
they are recorded so that no structure of this area is introduced without a consistency check.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Basic
import Submission.Work.FTS.GalerkinFix.Defs
import Submission.Work.FTS.Galerkin.Hilbert
import Submission.Work.FTS.Galerkin.Inhabit.dataAdm_zero
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.Galerkin.Inhabit.isDynEqOn_zero_alpha

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## The zero function: degenerate computations -/

/-- The iterated `D_z`-derivative of the zero function is zero. -/
theorem DzIter_zero_fun (i : ℕ) : Spaces.DzIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Spaces.DzIter_succ, ih]
    funext z θ
    simp [Spaces.Dz, Spaces.pz]

/-- The iterated `D_θ`-derivative of the zero function is zero. -/
theorem DthIter_zero_fun (i : ℕ) : Spaces.DthIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Spaces.DthIter_succ, ih]
    funext z θ
    simp [Spaces.Dth, Spaces.pth]

/-- Every mixed `D`-derivative of the zero function is zero. -/
theorem mixed_zero_fun (j i : ℕ) : Spaces.mixed j i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  rw [Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

/-- The `ℋ^k`-integrand of the zero function vanishes identically. -/
theorem HkIntegrand_zero_fun (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Spaces.HkIntegrand α k (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Spaces.HkIntegrand, DzIter_zero_fun, mixed_zero_fun]

/-- The `ℋ^k`-norm squared of the zero function vanishes. -/
theorem HkSq_zero_fun (α : ℝ) (k : ℕ) : Spaces.HkSq α k (fun _ _ => (0 : ℝ)) = 0 := by
  simp [Spaces.HkSq, HkIntegrand_zero_fun]

/-- The `ℋ^k`-norm of the zero function vanishes. -/
theorem HkNorm_zero_fun (α : ℝ) (k : ℕ) : Spaces.HkNorm α k (fun _ _ => (0 : ℝ)) = 0 := by
  simp [Spaces.HkNorm, HkSq_zero_fun]

/-- The operator `L₁₂` of the fundamental model vanishes on the zero function. -/
theorem L12_zero_fun (z : ℝ) : Construction.L12 (fun _ _ => (0 : ℝ)) z = 0 := by
  simp [Construction.L12, Construction.L12dens, FM.L12, FM.L12dens]

/-! ## Inhabitation of the data and regularity structures -/

/-- **The data hypotheses of the existence theorem are satisfiable**: the zero datum lies in the
corrected admissible class `DataAdm α g₀ = LocData.DataAdm α g₀ ∧ L₁₂(g₀)(0) = 0 ∧ RegQ α 5 g₀`
(interface fix of 2026-10-03) and is within `α²` in `ℋ⁴`. -/
theorem exists_small_data (α : ℝ) :
    ∃ g₀ : Fn, DataAdm α g₀ ∧ Spaces.HkNorm α 4 g₀ ≤ α ^ 2 :=
  ⟨fun _ _ => 0, Inhabit.dataAdm_zero α, by rw [HkNorm_zero_fun]; positivity⟩

/-- **`RegPkg` is inhabited** for every `α`. -/
theorem exists_regPkg (α : ℝ) : ∃ G : Fam, RegPkg α G :=
  ⟨fun _ _ _ => 0, Inhabit.regPkg_zero α⟩

/-- **The dynamic modulated equation is satisfiable**: at `α = 0` the zero family (with zero
stream function) solves it.  This is the consistency check that the equation `IsDynEqOn` is not
self-contradictory; the general (`α > 0`) solution is what the existence theorem of this area
produces from the bundle. -/
theorem exists_dynEqOn : ∃ G Φ : Fam, IsDynEqOn 0 Φ G :=
  ⟨fun _ _ _ => 0, fun _ _ _ => 0, Inhabit.isDynEqOn_zero_alpha⟩

/-! ## The Galerkin scheme is nondegenerate -/

/-- The inner-product structure forces `IP 0 0 = 0`. -/
theorem IP_zero_zero {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) :
    IP (0 : Fn) (0 : Fn) = 0 := by
  have hh : (0 : Fn) = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [hh]
  exact h.IP_zero_snd (fun _ _ : ℝ => (0 : ℝ))

/-- **No test function of an `IP`-orthonormal Galerkin basis can vanish.**  This is the formal
content of "the span of the first `n` modes is `n`-dimensional": orthonormality forces
`φ 0 ≠ 0`, so a Galerkin scheme is a genuine (nondegenerate) orthonormal sequence. -/
theorem phi_ne_zero_of_orth {α : ℝ} {IP : Fn → Fn → ℝ} (hIP : IsH4Inner α IP) {φ : ℕ → Fn}
    (horth : ∀ i j : ℕ, IP (φ i) (φ j) = if i = j then 1 else 0) : φ 0 ≠ 0 := by
  intro h
  have h1 : IP (φ 0) (φ 0) = 1 := by simpa using horth 0 0
  have h2 : IP (0 : Fn) (0 : Fn) = 0 := IP_zero_zero hIP
  rw [h] at h1
  rw [h2] at h1
  exact one_ne_zero h1.symm

/-- The inner-product structure of `UnifIP` forces `IP α 0 0 = 0` (linearity in the first argument
at the scalar `0`, applied to the regular class, of which `0` is a member). -/
theorem UnifIP_zero_zero {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : Work.FTS.Nonlin.UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hreg : Work.FTS.Nonlin.RegQ α 4 (0 : Fn)) : IP α 0 0 = 0 := by
  change IP α (fun _ _ : ℝ => (0 : ℝ)) (fun _ _ : ℝ => (0 : ℝ)) = 0
  have h := hIP.smul_fst α hα (0 : ℝ) (fun _ _ : ℝ => (0 : ℝ)) (fun _ _ : ℝ => (0 : ℝ))
    hreg hreg
  have h0 : (fun z θ : ℝ => (0 : ℝ) * (fun _ _ : ℝ => (0 : ℝ)) z θ)
      = (fun _ _ : ℝ => (0 : ℝ)) := by
    funext z θ
    simp
  rw [h0] at h
  linarith [h]

/-- **No test function of an `IP`-orthonormal Galerkin basis can vanish**, in the corrected
`UnifIP` interface: orthonormality forces `φ 0 ≠ 0`, so a Galerkin scheme is a genuine
(nondegenerate) orthonormal sequence. -/
theorem phi_ne_zero_of_galBasis {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ}
    (hIP : Work.FTS.Nonlin.UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    {φ : ℕ → Fn} (horth : ∀ i j : ℕ, IP α (φ i) (φ j) = if i = j then 1 else 0)
    (hreg : Work.FTS.Nonlin.RegQ α 4 (0 : Fn)) : φ 0 ≠ 0 := by
  intro h
  have h1 : IP α (φ 0) (φ 0) = 1 := by simpa using horth 0 0
  have h2 : IP α (0 : Fn) (0 : Fn) = 0 := UnifIP_zero_zero hIP hα hreg
  rw [h, h2] at h1
  exact one_ne_zero h1.symm

/-- The Galerkin basis of a bundle is nondegenerate.  (The hypothesis that the zero profile lies in
the regular class is automatic once the Galerkin span is known to be contained in `GalClass`;
see `Submission/Work/FTS/GalerkinFix/RegQApi.lean`.) -/
theorem DynInputs.phi_ne_zero {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputs Law α g₀ C₀) (hα : α ∈ Set.Ioc 0 hin.α₂)
    (hreg : Work.FTS.Nonlin.RegQ α 4 (0 : Fn)) : hin.φ 0 ≠ 0 :=
  phi_ne_zero_of_galBasis hin.hIP hα hin.hφ.orth hreg

end Work.FTS.Galerkin

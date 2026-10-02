/-
# `Work.NAKANE2` — Nakane's local homeomorphism (R1) for the tricorn parameter map

This file fixes the vocabulary of the area.  The headline is
`Work.NAKANE2.phiLocalHomeo : Work.NAKANE.PhiLocalHomeo` (file `Main.lean`), proved by the
inverse function theorem from

* (B1) `HasStrictFDerivAt ℝ Φ c₀` (file `Far/Basic.lean`),
* (S) a Lipschitz Shishikura surgery section (file `Surgery/LipschitzSection.lean`),
* (D1) `deriv (varphiCrit c₀) c₀ ≠ 0` (file `Deriv/VarphiCritDeriv.lean`),
* (D2) `surjective_of_lipschitzSection` (file `IFT/Section.lean`),
* (D3) `HasStrictFDerivAt.toOpenPartialHomeomorph` (file `IFT/LocalHomeo.lean`).

## Vocabulary

* Surgery side: `G`, `Gcrit`, `W`, `V`, `chiC`, `sig`, `gv`, `glueMuW`, `SurgeryData`.
* Far-series side: `critZ`, `farTerm`, `farSeries`, `farB`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.Assembly
import Submission.Work.NAKANE.PhiContinuity
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.NAKANE.BottcherJoint
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Contraction.norm_bottcherSeries_sub_le
import Submission.Work.Bottcher.Inverse.deriv_bottcher_ne_zero_of_far
import Submission.Work.ParamRaysCrit.All
import Submission.Work.MRMT.Found.M
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.FBif.Glue
import Submission.Work.FBif.glueMu_invariant
import Submission.Work.FBif.norm_glueMu_le
import Submission.Work.FBif.measurable_glueMu
import Submission.Work.FBif.principal_decay_bound
import Submission.Work.FBif.Liouville

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory
open scoped Topology ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace Work.NAKANE2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The parameter Böttcher map -/

/-- The parameter Böttcher map `Φ c = φ_c(c)` (junk value `0` on the mandelbar). -/
abbrev Phi : ℂ → ℂ := Work.ParamRays.Phi

/-- The mandelbar (the connectedness locus). -/
abbrev Mb : Set ℂ := Work.NAKANE.Mb

theorem Phi_eq_varphiCrit {c : ℂ} (hc : c ∉ Mb) : Phi c = Work.Bottcher.varphiCrit c c :=
  Work.NAKANE.Phi_eq_varphiCrit hc

/-! ## The critical value of the Green function and the conformal region `W` -/

/-- The Green function of `T_{c₀}`, in the `greenFun` formulation of `Work.ParamRays`. -/
def G (c₀ z : ℂ) : ℝ := Work.ParamRays.greenFun c₀ z

/-- The potential of the critical value, `G_{c₀}(c₀) = 2 G_{c₀}(0) > 0` for `c₀ ∉ Mb`. -/
def Gcrit (c₀ : ℂ) : ℝ := Work.ParamRays.greenFun c₀ c₀

theorem Gcrit_eq_two_paramPotential (c₀ : ℂ) :
    Gcrit c₀ = 2 * Work.ParamRays.paramPotential c₀ := by
  have h := Work.ParamRays.greenFun_orbit c₀ 0 1
  rw [Work.ParamRays.orbit_one, Work.Bottcher.Tantibar_zero] at h
  simpa [Gcrit, Work.ParamRays.paramPotential, pow_one] using h

theorem Gcrit_pos {c₀ : ℂ} (hc₀ : c₀ ∉ Mb) : 0 < Gcrit c₀ := by
  rw [Gcrit_eq_two_paramPotential]
  exact mul_pos two_pos (Work.ParamRays.paramPotential_pos hc₀)

/-- The forward-invariant conformal region `W = {G_{c₀} > (3/4) G_{c₀}(c₀)}`. -/
def W (c₀ : ℂ) : Set ℂ := {z : ℂ | 3 / 4 * Gcrit c₀ < G c₀ z}

theorem mem_W {c₀ z : ℂ} : z ∈ W c₀ ↔ 3 / 4 * Gcrit c₀ < G c₀ z := Iff.rfl

/-- `V = T_{c₀}⁻¹ (ball c₀ (2 ρ))`: the points whose image under `T_{c₀}` lies in the ball on
which the bump is `1`. -/
def V (c₀ : ℂ) (ρ : ℝ) : Set ℂ := {z : ℂ | Tantibar c₀ z ∈ Metric.ball c₀ (2 * ρ)}

theorem mem_V {c₀ : ℂ} {ρ : ℝ} {z : ℂ} :
    z ∈ V c₀ ρ ↔ Tantibar c₀ z ∈ Metric.ball c₀ (2 * ρ) := Iff.rfl

/-! ## The Shishikura bump deformation -/

/-- The bump function viewed as a `ℂ`-valued map (so that its Fréchet derivative makes sense on
`ℂ`). -/
def chiC (c₀ : ℂ) (χ : ContDiffBump c₀) : ℂ → ℂ := fun z => (χ z : ℂ)

/-- The Shishikura deformation `σ_v z = z + χ z · v`. -/
def sig (c₀ : ℂ) (χ : ContDiffBump c₀) (v z : ℂ) : ℂ := z + chiC c₀ χ z * v

/-- The deformed map `g_v = σ_v ∘ T_{c₀}` of the surgery. -/
def gv (c₀ : ℂ) (χ : ContDiffBump c₀) (v : ℂ) : ℂ → ℂ :=
  fun z => sig c₀ χ v (Tantibar c₀ z)

theorem gv_apply (c₀ : ℂ) (χ : ContDiffBump c₀) (v z : ℂ) :
    gv c₀ χ v z = Tantibar c₀ z + chiC c₀ χ (Tantibar c₀ z) * v := rfl

/-- The invariant Beltrami coefficient obtained by pulling `0` back along the `F`-orbit until its
first entrance into the forward-invariant conformal region `W`.  This is the variant of
`Work.FBif.glueMu` in which the far region `{R ≤ ‖·‖}` is replaced by the (bounded-complement)
set `W`. -/
noncomputable def glueMuW (F : ℂ → ℂ) (W : Set ℂ) : ℂ → ℂ :=
  fun z => if h : ∃ n : ℕ, (F^[n]) z ∈ W then Work.FBif.pullIter F (Nat.find h) z else 0

theorem glueMuW_of_hit {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ}
    (h : ∃ n : ℕ, (F^[n]) z ∈ W) : glueMuW F W z = Work.FBif.pullIter F (Nat.find h) z :=
  dif_pos h

theorem glueMuW_of_not_hit {F : ℂ → ℂ} {W : Set ℂ} {z : ℂ}
    (h : ¬ ∃ n : ℕ, (F^[n]) z ∈ W) : glueMuW F W z = 0 := dif_neg h

/-! ## The surgery datum -/

/-- A complete set of surgery data at a parameter `c₀ ∉ Mb`: the radius `ρ` of the bump, the bump
`χ` itself, a bound `Λ` for the derivative of `χ` (as a `ℂ`-valued function), and a radius `R₀`
carrying the complement of the conformal region `W`.

The band condition says that the closed ball of radius `3ρ` about `c₀` lies in the annulus
`{7 g₀ / 8 < G < 9 g₀ / 8}`; this is what makes the two-step surgery work
(`V ∩ W = ∅` and `g_v V ⊆ W`). -/
structure SurgeryData (c₀ : ℂ) where
  /-- the radius of the bump -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- the bump, of radii `ρ/2 < ρ` -/
  χ : ContDiffBump c₀
  hrIn : χ.rIn = ρ / 2
  hrOut : χ.rOut = ρ
  /-- a bound for the Fréchet derivative of `χ` -/
  Λ : ℝ
  hΛ1 : 1 ≤ Λ
  hΛ : ∀ z : ℂ, ‖fderiv ℝ (chiC c₀ χ) z‖ ≤ Λ
  /-- a radius carrying the complement of `W` -/
  R₀ : ℝ
  hR₀ : 0 < R₀
  /-- the band condition -/
  hband : Metric.closedBall c₀ (3 * ρ) ⊆
    {z : ℂ | 7 / 8 * Gcrit c₀ < G c₀ z ∧ G c₀ z < 9 / 8 * Gcrit c₀}
  /-- the complement of `W` is bounded -/
  hWc : (W c₀)ᶜ ⊆ Metric.closedBall 0 R₀

/-- The band condition forces the potential of the critical value to be positive. -/
theorem SurgeryData.Gcrit_pos {c₀ : ℂ} (D : SurgeryData c₀) : 0 < Gcrit c₀ := by
  have hmem : c₀ ∈ Metric.closedBall c₀ (3 * D.ρ) := by
    rw [Metric.mem_closedBall, dist_self]
    linarith [D.hρ]
  have h := D.hband hmem
  have h1 : 7 / 8 * Gcrit c₀ < Gcrit c₀ := h.1
  linarith

/-- Consequently a surgery datum can only exist off the mandelbar. -/
theorem SurgeryData.notMem_Mb {c₀ : ℂ} (D : SurgeryData c₀) : c₀ ∉ Mb := by
  intro hc
  have h0 : Work.ParamRays.paramPotential c₀ = 0 :=
    (Work.ParamRays.paramPotential_eq_zero_iff c₀).mpr hc
  have h1 := D.Gcrit_pos
  rw [Gcrit_eq_two_paramPotential] at h1
  linarith

/-- The radius of the surgery: `min (ρ/2) (1/(4Λ))`. -/
noncomputable def rConst {c₀ : ℂ} (D : SurgeryData c₀) : ℝ := min (D.ρ / 2) (1 / (4 * D.Λ))

/-- The Lipschitz constant of the surgery section: `24 Λ (R₀ + 1)²`. -/
noncomputable def Kconst {c₀ : ℂ} (D : SurgeryData c₀) : ℝ :=
  24 * D.Λ * (D.R₀ + 1) ^ 2

theorem rConst_pos {c₀ : ℂ} (D : SurgeryData c₀) : 0 < rConst D := by
  refine lt_min (by linarith [D.hρ]) ?_
  have : 0 < 4 * D.Λ := by linarith [D.hΛ1]
  positivity

theorem rConst_lt_ρ {c₀ : ℂ} (D : SurgeryData c₀) : rConst D < D.ρ := by
  have h1 : rConst D ≤ D.ρ / 2 := min_le_left _ _
  linarith [D.hρ]

theorem norm_mul_Λ_le {c₀ : ℂ} (D : SurgeryData c₀) {v : ℂ} (hv : ‖v‖ < rConst D) :
    ‖v‖ * D.Λ ≤ 1 / 4 := by
  have h2 : rConst D ≤ 1 / (4 * D.Λ) := min_le_right _ _
  have hΛpos : 0 < D.Λ := by linarith [D.hΛ1]
  have h4 : 0 < 4 * D.Λ := by linarith
  have h5 : ‖v‖ ≤ 1 / (4 * D.Λ) := le_of_lt (lt_of_lt_of_le hv h2)
  have h6 : ‖v‖ * (4 * D.Λ) ≤ 1 := by
    rwa [le_div_iff₀ h4] at h5
  nlinarith [h6, hΛpos]

theorem norm_lt_half_ρ {c₀ : ℂ} (D : SurgeryData c₀) {v : ℂ} (hv : ‖v‖ < rConst D) :
    ‖v‖ < D.ρ / 2 :=
  lt_of_lt_of_le hv (min_le_left _ _)

/-! ## The far product formula on the critical orbit -/

/-- The critical orbit `k ↦ p_{c}^{k}(c)` of the holomorphic second iterate. -/
def critZ (c : ℂ) (k : ℕ) : ℂ := (Work.Bottcher.pMap c)^[k] c

@[simp] theorem critZ_zero (c : ℂ) : critZ c 0 = c := rfl

theorem critZ_succ (c : ℂ) (k : ℕ) :
    critZ c (k + 1) = Work.Bottcher.pMap c (critZ c k) := by
  rw [critZ, Function.iterate_succ_apply']
  rfl

theorem critZ_add (c : ℂ) (m n : ℕ) :
    critZ c (m + n) = (Work.Bottcher.pMap c)^[n] (critZ c m) := by
  rw [critZ, critZ, Nat.add_comm m n, Function.iterate_add_apply]

/-- The `n`-th term of the Böttcher series based at the `N`-th critical-orbit point:
`4^{-(n+1)} log (normFactor c (critZ c (N+n)))`. -/
noncomputable def farTerm (N : ℕ) (c : ℂ) (n : ℕ) : ℂ :=
  Work.Bottcher.bottcherTerm c n (critZ c N)

/-- The Böttcher series based at the `N`-th critical-orbit point; for `N` large enough
`Work.Bottcher.bottcher c (critZ c N)` is the true Böttcher coordinate there. -/
noncomputable def farSeries (N : ℕ) (c : ℂ) : ℂ := ∑' n : ℕ, farTerm N c n

/-- The explicit product formula `bottcher c ((pMap c)^[N] c)` at the far critical-orbit point,
written in terms of `farSeries`. -/
noncomputable def farB (N : ℕ) (c : ℂ) : ℂ := critZ c N * Complex.exp (farSeries N c)

theorem farSeries_eq_bottcherSeries (N : ℕ) (c : ℂ) :
    farSeries N c = Work.Bottcher.bottcherSeries c (critZ c N) := rfl

theorem farB_eq_bottcher (N : ℕ) (c : ℂ) :
    farB N c = Work.Bottcher.bottcher c (critZ c N) := rfl

theorem farTerm_eq (N n : ℕ) (c : ℂ) :
    farTerm N c n = Work.Bottcher.bottcherTerm c n (critZ c N) := rfl

/-- The `N`-th far iterate lies on the critical orbit; unfolding for `n`:
`(pMap c)^[n] (critZ c N) = critZ c (N + n)`. -/
theorem pMap_iterate_critZ (c : ℂ) (n N : ℕ) :
    (Work.Bottcher.pMap c)^[n] (critZ c N) = critZ c (N + n) := by
  rw [critZ, critZ, Nat.add_comm N n, Function.iterate_add_apply]

end Work.NAKANE2

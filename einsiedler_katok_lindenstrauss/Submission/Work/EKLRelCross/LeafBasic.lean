import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLRelCross.leafwise_component` — C5: existence of leafwise measures (Pisa §5–6)

Component C5 of the frozen EKL contract is

`Work.EKLContract.P_Leafwise`,
and the planned deliverable (ROUTE_LEAD, table row C5) is `Work.EKLContract.P_X3 → P_Leafwise`.

This file is the assembly.  The pieces it needs are stated in this namespace:

* `locallyFree_of`         — local freeness of every subgroup action, from `P_X3`;
* `ae_free_orbit`          — (U2) a.e. free `U`-orbits, from Poincaré recurrence + local
                             freeness (Pisa 7.12);
* `leafwise_exists`        — existence of a leafwise system for `(μ,U,t0)` (Pisa Thm 6.3);
* `leafwise_unique`        — (U1);
* `leafwise_crossSection`  — (U3);
* `leafwise_invariant`     — (U4);
* `leafwise_propor`        — (U5) = EKL (8);
* `leafwise_luzin`         — (U6);
* `leafwise_acovariant`    — (U7) = EKL (4)/Pisa 7.16;
* `leafwise_ergodic`       — (U8);
* `leafwise_entropy_cs`    — (U9) = EKL (9).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract
open Work.EKLContract.Lemmas

/-! ## Local freeness -/

/-- **Local freeness** (Pisa 6.1): from `P_X3`, for every compact `K` there is `δ > 0` such that
elements of `V δ` move no point of `K` to itself.  This is the fourth clause of `P_X3` with
`h = 1`. -/
theorem locallyFree_of (h2 : P_X3) (K : Set X3) (hK : IsCompact K) :
    ∃ δ > 0, ∀ x ∈ K, ∀ g ∈ V δ, g • x = x → g = 1 := by
  obtain ⟨δ, hδ, hinj⟩ := h2.2.2.2.1 K hK
  exact ⟨δ, hδ, fun x hx g hg hgx =>
    hinj x hx g hg 1 (V_open_one δ hδ).2 (by rw [hgx, one_smul])⟩

/-! ## `aDiag` and powers -/

theorem aDiag_nsmul (n : ℕ) (t : Fin 3 → ℝ) : aDiag (n • t) = aDiag t ^ n := by
  induction n with
  | zero => simp [aDiag_zero]
  | succ k ih =>
    rw [succ_nsmul, ← aDiag_add, ih, pow_succ]

/-! ## (U2): a.e. free orbits -/

/-- **Poincaré recurrence for the contracting element.**  For a probability measure `μ` preserved
by `x ↦ aDiag t0 • x`, almost every point `x` satisfies: every neighbourhood of `x` is visited
infinitely often by the forward orbit of `x`. -/
theorem ae_frequently_visit (μ : Measure X3) [IsProbabilityMeasure μ]
    (t0 : Fin 3 → ℝ) (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ) :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x,
      ∃ᶠ n in atTop, (fun y : X3 => aDiag t0 • y)^[n] x ∈ s :=
  (ht0.conservative).ae_frequently_mem_of_mem_nhds

/-- **(U2): a.e. free orbits** (Pisa 7.12).  If `μ` is a probability measure preserved by the
contracting element `α^{t₀}` and `U` is `A`-normalised and contracted by `α^{t₀}`, then for
`μ`-a.e. `x` the orbit map `u ↦ u • x` is injective on `U`.

Proof (Pisa 7.13): if `u ≠ 1` fixes `x`, then `α^{nt₀} u α^{-nt₀} ≠ 1` fixes `α^{nt₀}x` for all
`n`, and these conjugates converge to `1`; Poincaré recurrence produces `n` with `α^{nt₀}x` back
in a compact neighbourhood of `x`, where local freeness forbids that. -/
theorem ae_free_orbit (h2 : P_X3) (μ : Measure X3) [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1)) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := by
  filter_upwards [ae_frequently_visit μ t0 ht0] with x hx
  intro u hu hux
  by_contra hne
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨δ, hδ, hloc⟩ := locallyFree_of h2 K hKc
  have hV : V δ ∈ 𝓝 (1 : SL3) := (V_open_one δ hδ).1.mem_nhds (V_open_one δ hδ).2
  have hev : ∀ᶠ n in atTop, aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹ ∈ V δ :=
    (hcontr u hu).eventually_mem hV
  have hfreq : ∃ᶠ n in atTop, (fun y : X3 => aDiag t0 • y)^[n] x ∈ interior K :=
    hx (interior K) (interior_mem_nhds.mpr hKn)
  obtain ⟨n, hnK, hnV⟩ := (hfreq.and_eventually hev).exists
  have hfix : (aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) • ((fun y : X3 => aDiag t0 • y)^[n] x)
      = (fun y : X3 => aDiag t0 • y)^[n] x := by
    rw [smul_iterate, mul_smul, mul_smul, inv_smul_smul, hux]
  have hconj : aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹ = 1 :=
    hloc _ (interior_subset hnK) _ hnV hfix
  exact hne (by
    calc u = (aDiag t0 ^ n)⁻¹ * (aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) * (aDiag t0 ^ n) := by
          group
      _ = 1 := by rw [hconj]; group)


/-! ## Plaques of a subgroup -/

/-- The open sup-metric ball of radius `R` around the identity, inside `U`. -/
def Uball (U : Subgroup SL3) (R : ℝ) : Set SL3 :=
  {g | g ∈ U ∧ ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
    - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < R}

/-- The closed sup-metric ball of radius `R` around the identity, inside `U`. -/
def Ucl (U : Subgroup SL3) (R : ℝ) : Set SL3 :=
  {g | g ∈ U ∧ ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
    - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R}

/-- The plaque of `U`-radius `R` through `x`. -/
def Upla (U : Subgroup SL3) (R : ℝ) (x : X3) : Set X3 :=
  (fun g : SL3 => g • x) '' (Uball U R)

/-- The closed plaque of `U`-radius `R` through `x`. -/
def Uclpla (U : Subgroup SL3) (R : ℝ) (x : X3) : Set X3 :=
  (fun g : SL3 => g • x) '' (Ucl U R)

theorem Box1_eq_Ucl (U : Subgroup SL3) : Box1 U = Ucl U 1 := rfl

theorem Uball_subset_Ucl (U : Subgroup SL3) (R : ℝ) : Uball U R ⊆ Ucl U R :=
  fun g hg => ⟨hg.1, fun i j => le_of_lt (hg.2 i j)⟩

theorem one_mem_Uball (U : Subgroup SL3) {R : ℝ} (hR : 0 < R) : (1 : SL3) ∈ Uball U R := by
  refine ⟨U.one_mem, fun i j => ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]
  exact hR

theorem Upla_subset_orbit (U : Subgroup SL3) (R : ℝ) (x : X3) :
    Upla U R x ⊆ (fun g : SL3 => g • x) '' (U : Set SL3) := by
  rintro y ⟨g, hg, rfl⟩
  exact ⟨g, hg.1, rfl⟩

theorem mem_Upla_iff {U : Subgroup SL3} {R : ℝ} {x y : X3} :
    y ∈ Upla U R x ↔ ∃ g ∈ Uball U R, g • x = y := Iff.rfl


/-! ## Wiring: `P_X3` supplies the standing assumptions of Pisa §6 -/

/-- `P_X3` gives the topological standing assumptions of Pisa §6 on `X₃`. -/
theorem secondCountableTopology_X3 (h2 : P_X3) : SecondCountableTopology X3 := by
  haveI : PolishSpace X3 := h2.2.1
  infer_instance

theorem standardBorelSpace_X3 (h2 : P_X3) : StandardBorelSpace X3 := by
  haveI : PolishSpace X3 := h2.2.1
  infer_instance

/-- **Local freeness** (Pisa 6.1) in the form used by the fleet's C5 development. -/
theorem locallyFree_of_PX3 (h2 : P_X3) (U : Subgroup SL3) : Work.EKLComp.LocallyFree U := by
  intro K hK
  obtain ⟨δ, hδ, h⟩ := locallyFree_of h2 K hK
  exact ⟨δ, hδ, fun x hx u _ hu hux => h x hx u hu hux⟩

/-- The contraction hypothesis of `P_Leafwise` is `Work.EKLComp.ContractU`. -/
theorem contractU_of (U : Subgroup SL3) (t0 : Fin 3 → ℝ)
    (h : ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1)) :
    Work.EKLComp.ContractU U t0 := h

end Work.EKLRelCross

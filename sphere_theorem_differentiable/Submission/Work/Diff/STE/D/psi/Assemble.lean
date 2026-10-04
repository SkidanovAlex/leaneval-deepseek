/-
# Layer D: assembly of `ContDiffAt ℝ 1 psi 0`

This file assembles the proof that the Galerkin vector field

  `psi hLC D ρ ε c hg = if (g₀ + genMap D ε c) is positive definite then (1/2) J ρ ε (P (g₀ + genMap D ε c)) else 0`

is `C¹` at `0`.  It is the top of the Layer D development:

* `Work.Diff.STE.D.psiConc` (`psi/Basic.lean`) is the explicit chart expression of the first branch
  of `psi`, and `psi =ᶠ[𝓝 0] psiConc` (`psi/Equiv.lean`);
* the `z`-th coefficient of `psiConc` is `(1/2) · scoeff ρ ε (Fz · c) q`, and the localised
  component `Fz` is affine in the jets of `g₀ + genMap D ε c` (`psi/Core.lean`);
* the Fourier coefficient `scoeff` is ℝ-linear on functions supported in the half-open cube
  (`Work.Diff.STE.B3.scoeff_add_of_support`, `scoeff_smul_of_support`, `scoeff_finset_sum_smul`) and
  bounded by `|ρ (ε • m)| · sup |·|` there (`Work.Diff.STE.B3.abs_scoeff_le`).

The analytic content of the last two steps is delegated:

* `Work.Diff.STE.D.psi.abs_Fz_sub_le` — the second order Taylor bound for `Fz`,
* `Work.Diff.STE.D.psi.abs_Ufun_sub_le` — the uniform Lipschitz bound for `c₀ ↦ Ufun … c₀`,
* `Work.Diff.STE.D.psi.continuous_Fz`, `Work.Diff.STE.D.psi.continuous_Ufun` — the continuity of
  the two localised components (needed to apply the linearity of `scoeff`).

## Main results

* `Work.Diff.STE.D.hasFDerivAt_psiConc_z` — on the positivity ball, `psiConc · z` is differentiable
  with derivative `psiConcDeriv · z`;
* `Work.Diff.STE.D.continuousAt_psiConcDeriv_z` — the candidate derivative is continuous there;
* `Work.Diff.STE.D.contDiffAt_psiConc` — `ContDiffAt ℝ 1 psiConc 0`.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.D.psi.Equiv
import Submission.Work.Diff.STE.B3.abs_scoeff_le
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.B3.scoeff_smul_of_support
import Submission.Work.Diff.STE.B3.scoeff_finset_sum_smul
import Submission.Work.Diff.STE.D.psi.continuous_Fz
import Submission.Work.Diff.STE.D.psi.continuous_Ufun
import Submission.Work.Diff.STE.D.psi.abs_Fz_sub_le
import Submission.Work.Diff.STE.D.psi.abs_Ufun_sub_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## 1. The half-open cube, the localised components and their supports -/

/-- The half-open cube `(-1/2, 1/2]ⁿ`, the fundamental domain of the localised components. -/
def cube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))

/-- The defining equation of the localised component `Fz`, as a rewriting lemma. -/
@[simp] lemma Fz_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    Fz (I := I) (M := M) g₀ D ε z c y =
      D.R z.1 (secChart (I := I) (M := M) g₀
        (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ z.1))
        z.2.1 z.2.2.1 y := rfl

/-- The defining equation of the directional integrand `Ufun`, as a rewriting lemma. -/
@[simp] lemma Ufun_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    Ufun (I := I) (M := M) g₀ D ε z z' c₀ y =
      D.psi z.1 y * Real.sqrt (D.dens z.1 y) *
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y))
            * (pPhiFunD (E := E)
                  (jetPairOf (I := I) (M := M) g₀ D ε (D.x₀ z.1) c₀
                    (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))
                  (jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                    (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) j k := rfl

/-- The support of a sum is contained in any set containing both supports. -/
lemma support_add_subset {β : Type*} {T : Set β} {f g : β → ℝ}
    (hf : Function.support f ⊆ T) (hg : Function.support g ⊆ T) :
    Function.support (f + g) ⊆ T := by
  intro x hx
  by_contra hxT
  have h1 : f x = 0 := by by_contra h; exact hxT (hf h)
  have h2 : g x = 0 := by by_contra h; exact hxT (hg h)
  exact hx (by rw [Pi.add_apply, h1, h2, add_zero])

/-- The support of a difference is contained in any set containing both supports. -/
lemma support_sub_subset₂ {β : Type*} {T : Set β} {f g : β → ℝ}
    (hf : Function.support f ⊆ T) (hg : Function.support g ⊆ T) :
    Function.support (f - g) ⊆ T := by
  intro x hx
  by_contra hxT
  have h1 : f x = 0 := by by_contra h; exact hxT (hf h)
  have h2 : g x = 0 := by by_contra h; exact hxT (hg h)
  exact hx (by rw [Pi.sub_apply, h1, h2, sub_zero])

/-- The support of `f - g - h` is contained in any set containing the three supports. -/
lemma support_sub_subset {β : Type*} {T : Set β} {f g h : β → ℝ}
    (hf : Function.support f ⊆ T) (hg : Function.support g ⊆ T) (hh : Function.support h ⊆ T) :
    Function.support (fun x => f x - g x - h x) ⊆ T := by
  intro x hx
  by_contra hxT
  have h1 : f x = 0 := by by_contra h; exact hxT (hf h)
  have h2 : g x = 0 := by by_contra h; exact hxT (hg h)
  have h3 : h x = 0 := by by_contra h; exact hxT (hh h)
  exact hx (show f x - g x - h x = 0 by rw [h1, h2, h3]; ring)

/-- The support of a finite pointwise sum of real functions is contained in any set containing all
the summands' supports. -/
lemma support_finset_sum_subset {ι β : Type*} (s : Finset ι) {T : Set β} (f : ι → β → ℝ)
    (h : ∀ i ∈ s, Function.support (f i) ⊆ T) :
    Function.support (fun x => ∑ i ∈ s, f i x) ⊆ T := by
  intro x hx
  by_contra hxT
  refine hx (Finset.sum_eq_zero fun i hi => ?_)
  by_contra hne
  exact hxT (h i hi hne)

/-- The support of the localised component `Fz … c` lies in the half-open cube. -/
lemma support_Fz_subset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Function.support (Fz (I := I) (M := M) g₀ D ε z c) ⊆ cube (Module.finrank ℝ E) := by
  rw [Function.support_subset_iff]
  intro y hy
  rw [cube, Set.mem_pi]
  intro j _
  rw [Set.mem_Ioc]
  have hχ : D.χ z.1 y ≠ 0 := by
    intro h0
    exact hy (by
      simp only [Fz_apply, Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.psi, h0, zero_mul])
  have hmem := D.hχsupp z.1 hχ
  have hIoo := Set.mem_pi.mp hmem j (Set.mem_univ j)
  rw [Set.mem_Ioo] at hIoo
  exact ⟨hIoo.1, le_of_lt hIoo.2⟩

/-- The support of the directional integrand `Ufun … c₀` lies in the half-open cube. -/
lemma support_Ufun_subset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Function.support (Ufun (I := I) (M := M) g₀ D ε z z' c₀) ⊆ cube (Module.finrank ℝ E) := by
  rw [Function.support_subset_iff]
  intro y hy
  rw [cube, Set.mem_pi]
  intro j _
  rw [Set.mem_Ioc]
  have hψ : D.psi z.1 y ≠ 0 := by
    intro h0
    exact hy (by simp only [Ufun_apply, h0, zero_mul])
  have hχ : D.χ z.1 y ≠ 0 := fun h0 => hψ (by simp only [Work.Diff.STE.B3Data.psi, h0, zero_mul])
  have hmem := D.hχsupp z.1 hχ
  have hIoo := Set.mem_pi.mp hmem j (Set.mem_univ j)
  rw [Set.mem_Ioo] at hIoo
  exact ⟨hIoo.1, le_of_lt hIoo.2⟩

/-! ## 2. The positivity radius -/

/-- **The positivity set of `psi` contains a ball around `0`.** -/
lemma exists_isPos_ball (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      ‖c‖ < δ → IsPos (I := I) (M := M) g₀ D ε c := by
  have h : {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
      IsPos (I := I) (M := M) g₀ D ε c} ∈
      𝓝 (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :=
    eventually_posDef (I := I) (M := M) D ε
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ, hδ, fun c hc => hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  exact hc

/-! ## 3. The linearised perturbation, the remainder and the candidate derivative -/

/-- The linearised perturbation of the localised component along `c - c₀`. -/
noncomputable def psiLin (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun y => ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y

/-- The second order Taylor remainder of the localised component. -/
noncomputable def psiRem (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun y => Fz (I := I) (M := M) g₀ D ε z c y - Fz (I := I) (M := M) g₀ D ε z c₀ y
    - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y

/-- The defining equation of the linearised perturbation, as an equality of functions. -/
lemma psiLin_eq (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    psiLin (I := I) (M := M) g₀ D ε z c₀ c =
      fun y => ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y := rfl

/-- The defining equation of the linearised perturbation, pointwise. -/
@[simp] lemma psiLin_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    psiLin (I := I) (M := M) g₀ D ε z c₀ c y =
      ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y := rfl

/-- The defining equation of the remainder, as an equality of functions. -/
lemma psiRem_eq (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    psiRem (I := I) (M := M) g₀ D ε z c₀ c =
      fun y => Fz (I := I) (M := M) g₀ D ε z c y - Fz (I := I) (M := M) g₀ D ε z c₀ y
        - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y := rfl

/-- The defining equation of the remainder, pointwise. -/
@[simp] lemma psiRem_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    psiRem (I := I) (M := M) g₀ D ε z c₀ c y =
      Fz (I := I) (M := M) g₀ D ε z c y - Fz (I := I) (M := M) g₀ D ε z c₀ y
        - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y := rfl

/-- **The candidate derivative of the `z`-th coefficient of `psiConc`.**  The `z'`-th coefficient
enters through the directional derivative integrand `Ufun`; it is a `ContinuousLinearMap` because it
is a finite linear combination of the coordinate functionals `c ↦ c z'`. -/
noncomputable def psiConcDeriv (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ] ℝ :=
  ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (ContinuousLinearMap.proj z').smulRight
      ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2)

/-! ## 4. Step 1: differentiability of the coefficients -/

theorem hasFDerivAt_psiConc_z (g₀ : Submission.Diff.SMet I M)
    (hg : ChartData (I := I) (M := M) (g₀.inner))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      ‖c₀‖ < δ →
      HasFDerivAt (fun c => psiConc (I := I) (M := M) g₀ D ρ ε c z)
        (psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c₀) c₀ := by
  classical
  obtain ⟨δ₂, C₂, hδ₂, hC₂, hTay⟩ :=
    Work.Diff.STE.D.psi.abs_Fz_sub_le (I := I) (M := M) hg D ε z
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_isPos_ball (I := I) (M := M) D ε
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun c₀ hc₀ => ?_⟩
  have hc₀₂ : ‖c₀‖ < δ₂ := lt_of_lt_of_le hc₀ (min_le_left _ _)
  have hc₀₀ : ‖c₀‖ < δ₀ := lt_of_lt_of_le hc₀ (min_le_right _ _)
  have hp₀ : IsPos (I := I) (M := M) g₀ D ε c₀ := hpos c₀ hc₀₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε' hε'
  set P : ℝ := |ρ (ε • fun i => ((z.2.2.2.1.1 i : ℤ) : ℝ))| with hP
  have hPnn : 0 ≤ P := by rw [hP]; exact abs_nonneg _
  have hPC : 0 < P * C₂ + 1 := by nlinarith [hPnn, hC₂]
  set δ : ℝ := min (min (δ₂ - ‖c₀‖) (δ₀ - ‖c₀‖)) (2 * ε' / (P * C₂ + 1)) with hδ
  have hδle : δ ≤ 2 * ε' / (P * C₂ + 1) := by rw [hδ]; exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (lt_min (sub_pos.mpr hc₀₂) (sub_pos.mpr hc₀₀))
      (div_pos (by linarith) hPC)
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) hδpos)
    (fun d hd => ?_)
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hd
  have hd₁ : ‖d‖ < δ₂ - ‖c₀‖ :=
    lt_of_lt_of_le hd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd₂ : ‖d‖ < δ₀ - ‖c₀‖ :=
    lt_of_lt_of_le hd (le_trans (min_le_left _ _) (min_le_right _ _))
  set c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ := c₀ + d with hc
  have hsub : c - c₀ = d := by rw [hc]; simp
  have hcd : ‖c - c₀‖ = ‖d‖ := by rw [hsub]
  have hcn : ‖c‖ < δ₀ := by
    rw [hc]
    calc ‖c₀ + d‖ ≤ ‖c₀‖ + ‖d‖ := norm_add_le _ _
      _ < δ₀ := by linarith
  have hpc : IsPos (I := I) (M := M) g₀ D ε c := hpos c hcn
  have hc₂ : ‖c - c₀‖ < δ₂ := by
    rw [hcd]
    exact lt_of_lt_of_le hd₁ (by linarith [norm_nonneg c₀])
  -- the Taylor bound for the remainder
  have hR : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
      |psiRem (I := I) (M := M) g₀ D ε z c₀ c y| ≤ C₂ * ‖c - c₀‖ ^ 2 := by
    intro y
    simp only [psiRem_apply]
    exact hTay c₀ hc₀₂ hp₀ c hc₂ hpc y
  -- continuity and supports of the pieces
  have hcont_c : Continuous (Fz (I := I) (M := M) g₀ D ε z c) :=
    Work.Diff.STE.D.psi.continuous_Fz (I := I) (M := M) hg D ε z c hpc
  have hcont_c₀ : Continuous (Fz (I := I) (M := M) g₀ D ε z c₀) :=
    Work.Diff.STE.D.psi.continuous_Fz (I := I) (M := M) hg D ε z c₀ hp₀
  have hcont_Slam : Continuous (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y) := by
    refine continuous_finsetSum Finset.univ (fun z' _ => ?_)
    exact continuous_const.mul
      (Work.Diff.STE.D.psi.continuous_Ufun (I := I) (M := M) hg D ε z z' c₀ hp₀)
  have hcont_S : Continuous (psiLin (I := I) (M := M) g₀ D ε z c₀ c) := by
    rw [psiLin_eq]
    exact hcont_Slam
  have hcont_R : Continuous (psiRem (I := I) (M := M) g₀ D ε z c₀ c) := by
    rw [psiRem_eq]
    exact (hcont_c.sub hcont_c₀).sub hcont_Slam
  have hsupp_c : Function.support (Fz (I := I) (M := M) g₀ D ε z c) ⊆ cube (Module.finrank ℝ E) :=
    support_Fz_subset (I := I) (M := M) D ε z c
  have hsupp_c₀ : Function.support (Fz (I := I) (M := M) g₀ D ε z c₀) ⊆ cube (Module.finrank ℝ E) :=
    support_Fz_subset (I := I) (M := M) D ε z c₀
  have hsupp_Slam : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Ufun (I := I) (M := M) g₀ D ε z z' c₀ y)
      ⊆ cube (Module.finrank ℝ E) := by
    refine support_finset_sum_subset Finset.univ _ (fun z' _ => ?_)
    refine subset_trans ?_ (support_Ufun_subset (I := I) (M := M) D ε z z' c₀)
    intro y hy h0
    exact hy (by simp only [h0, mul_zero])
  have hsupp_S : Function.support (psiLin (I := I) (M := M) g₀ D ε z c₀ c) ⊆
      cube (Module.finrank ℝ E) := by
    rw [psiLin_eq]
    exact hsupp_Slam
  have hsupp_R : Function.support (psiRem (I := I) (M := M) g₀ D ε z c₀ c) ⊆
      cube (Module.finrank ℝ E) := by
    rw [psiRem_eq]
    exact support_sub_subset hsupp_c hsupp_c₀ hsupp_Slam
  -- the algebraic decomposition
  have hFz_add : Fz (I := I) (M := M) g₀ D ε z c
      = Fz (I := I) (M := M) g₀ D ε z c₀
        + (psiLin (I := I) (M := M) g₀ D ε z c₀ c
          + psiRem (I := I) (M := M) g₀ D ε z c₀ c) := by
    funext y
    simp only [psiLin_apply, psiRem_apply, Pi.add_apply]
    ring
  have hS : Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (psiLin (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2
      = ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2 := by
    have heq : psiLin (I := I) (M := M) g₀ D ε z c₀ c
        = ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') • Ufun (I := I) (M := M) g₀ D ε z z' c₀ := by
      rw [psiLin_eq]
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact Work.Diff.STE.B3.scoeff_finset_sum_smul Finset.univ ρ ε z.2.2.2
      (fun z' => c z' - c₀ z') (fun z' => Ufun (I := I) (M := M) g₀ D ε z z' c₀)
      (fun z' _ => Work.Diff.STE.D.psi.continuous_Ufun (I := I) (M := M) hg D ε z z' c₀ hp₀)
      (fun z' _ => support_Ufun_subset (I := I) (M := M) D ε z z' c₀)
  have hA : Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (Fz (I := I) (M := M) g₀ D ε z c) z.2.2.2
      = Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (Fz (I := I) (M := M) g₀ D ε z c₀) z.2.2.2
        + Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (psiLin (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2
        + Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (psiRem (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2 := by
    have h1 := Work.Diff.STE.B3.scoeff_add_of_support ρ ε
      (Fz (I := I) (M := M) g₀ D ε z c₀)
      (psiLin (I := I) (M := M) g₀ D ε z c₀ c
        + psiRem (I := I) (M := M) g₀ D ε z c₀ c)
      hcont_c₀ (hcont_S.add hcont_R) hsupp_c₀ (support_add_subset hsupp_S hsupp_R) z.2.2.2
    have h2 := Work.Diff.STE.B3.scoeff_add_of_support ρ ε
      (psiLin (I := I) (M := M) g₀ D ε z c₀ c)
      (psiRem (I := I) (M := M) g₀ D ε z c₀ c)
      hcont_S hcont_R hsupp_S hsupp_R z.2.2.2
    rw [hFz_add, h1, h2]
    ring
  have hderiv : psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c₀ (c - c₀)
      = (1 / 2 : ℝ) * ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2 := by
    simp only [psiConcDeriv, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z' _ => ?_)
    ring
  have hjFC : ∀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (secChart (I := I) (M := M) g₀
          (addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c)) (D.x₀ z.1)) z
      = Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (Fz (I := I) (M := M) g₀ D ε z c) z.2.2.2 := by
    intro c
    rfl
  have hbody : psiConc (I := I) (M := M) g₀ D ρ ε c z
        - psiConc (I := I) (M := M) g₀ D ρ ε c₀ z
        - psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c₀ (c - c₀)
      = (1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (psiRem (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2 := by
    rw [psiConc_apply, psiConc_apply, hjFC c, hjFC c₀, hA, hS, hderiv]
    ring
  -- the final estimate
  have hSD : |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
      (psiRem (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2| ≤ P * (C₂ * ‖c - c₀‖ ^ 2) := by
    rw [hP]
    exact Work.Diff.STE.B3.abs_scoeff_le ρ ε (psiRem (I := I) (M := M) g₀ D ε z c₀ c)
      hcont_R hsupp_R z.2.2.2 (C₂ * ‖c - c₀‖ ^ 2) (mul_nonneg hC₂ (sq_nonneg _)) hR
  have hfac : 0 ≤ (1 / 2 : ℝ) * P * C₂ := mul_nonneg (mul_nonneg (by norm_num) hPnn) hC₂
  have hε'' : (1 / 2 : ℝ) * P * C₂ * δ ≤ ε' := by
    have h1 : (1 / 2 : ℝ) * P * C₂ * δ ≤ (1 / 2 : ℝ) * P * C₂ * (2 * ε' / (P * C₂ + 1)) :=
      mul_le_mul_of_nonneg_left hδle hfac
    have h2 : (1 / 2 : ℝ) * P * C₂ * (2 * ε' / (P * C₂ + 1))
        = (P * C₂) * ε' / (P * C₂ + 1) := by ring
    have h3 : (P * C₂) * ε' / (P * C₂ + 1) ≤ ε' := by
      rw [div_le_iff₀ hPC]
      nlinarith [hPnn, hC₂, hε'.le, mul_nonneg hPnn hC₂]
    linarith [h1, h2, h3]
  have hgoal : psiConc (I := I) (M := M) g₀ D ρ ε c z
        - psiConc (I := I) (M := M) g₀ D ρ ε c₀ z
        - psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c₀ d
      = (1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (psiRem (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2 := by
    rw [← hsub]
    exact hbody
  change ‖psiConc (I := I) (M := M) g₀ D ρ ε c z
      - psiConc (I := I) (M := M) g₀ D ρ ε c₀ z
      - psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c₀ d‖ ≤ ε' * ‖d‖
  rw [hgoal, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)), Real.norm_eq_abs]
  calc (1 / 2 : ℝ) * |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (psiRem (I := I) (M := M) g₀ D ε z c₀ c) z.2.2.2|
      ≤ (1 / 2 : ℝ) * (P * (C₂ * ‖c - c₀‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hSD (by norm_num)
    _ = (1 / 2 : ℝ) * P * C₂ * ‖d‖ ^ 2 := by rw [hcd]; ring
    _ ≤ (1 / 2 : ℝ) * P * C₂ * (δ * ‖d‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (le_of_lt hd) (norm_nonneg _)
    _ = ((1 / 2 : ℝ) * P * C₂ * δ) * ‖d‖ := by ring
    _ ≤ ε' * ‖d‖ := mul_le_mul_of_nonneg_right hε'' (norm_nonneg _)

/-! ## 5. Step 2: continuity of the candidate derivative -/

theorem continuousAt_psiConcDeriv_z (g₀ : Submission.Diff.SMet I M)
    (hg : ChartData (I := I) (M := M) (g₀.inner))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      ‖c₀‖ < δ →
      ContinuousAt (fun c => psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c) c₀ := by
  classical
  -- the Lipschitz data for the directional integrands, one pair at a time
  have hstep : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 ≤ p.2 ∧
        ∀ (c₀ c₁ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
          ‖c₀‖ < p.1 → ‖c₁‖ < p.1 → IsPos (I := I) (M := M) g₀ D ε c₀ →
          IsPos (I := I) (M := M) g₀ D ε c₁ →
          ∀ y : Fin (Module.finrank ℝ E) → ℝ,
            |Ufun (I := I) (M := M) g₀ D ε z z' c₀ y
              - Ufun (I := I) (M := M) g₀ D ε z z' c₁ y| ≤ p.2 * ‖c₀ - c₁‖ := by
    intro z'
    obtain ⟨δ, C, h1, h2, h3⟩ := Work.Diff.STE.D.psi.abs_Ufun_sub_le (I := I) (M := M) hg D ε z z'
    exact ⟨(δ, C), h1, h2, h3⟩
  choose p hp using hstep
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_isPos_ball (I := I) (M := M) D ε
  -- a common radius
  have hex : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ z', δ ≤ (p z').1 := by
    by_cases hne : (Finset.univ : Finset (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)).Nonempty
    · refine ⟨min ((Finset.univ : Finset (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)).inf'
          hne (fun z' => (p z').1)) δ₀, lt_min ?_ hδ₀, min_le_right _ _, fun z' => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro z' _
        exact (hp z').1
      · exact le_trans (min_le_left _ _) (Finset.inf'_le (fun z' => (p z').1) (Finset.mem_univ z'))
    · refine ⟨δ₀, hδ₀, le_refl _, fun z' => absurd ⟨z', Finset.mem_univ z'⟩ hne⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁δ₀, hδ₁le⟩ := hex
  set Q : ℝ := |ρ (ε • fun i => ((z.2.2.2.1.1 i : ℤ) : ℝ))| with hQ
  have hQnn : 0 ≤ Q := by rw [hQ]; exact abs_nonneg _
  refine ⟨δ₁, hδ₁pos, fun c₀ hc₀ => ?_⟩
  have hp₀c₀ : IsPos (I := I) (M := M) g₀ D ε c₀ := hpos c₀ (lt_of_lt_of_le hc₀ hδ₁δ₀)
  -- the scalar coefficients are continuous at `c₀`
  have hscal : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContinuousAt (fun c => Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (Ufun (I := I) (M := M) g₀ D ε z z' c) z.2.2.2) c₀ := by
    intro z'
    rw [Metric.continuousAt_iff]
    intro ε'' hε''
    refine ⟨min (δ₁ - ‖c₀‖) (ε'' / (Q * (p z').2 + 1)), lt_min (sub_pos.mpr hc₀) ?_, ?_⟩
    · have hp2 : 0 ≤ Q * (p z').2 := mul_nonneg hQnn (hp z').2.1
      exact div_pos hε'' (by linarith)
    · intro c hc
      rw [dist_eq_norm] at hc
      rw [Real.dist_eq]
      have hc₁ : ‖c - c₀‖ < δ₁ - ‖c₀‖ := lt_of_lt_of_le hc (min_le_left _ _)
      have hc₂ : ‖c - c₀‖ < ε'' / (Q * (p z').2 + 1) := lt_of_lt_of_le hc (min_le_right _ _)
      have hcn : ‖c‖ < δ₁ := by
        calc ‖c‖ = ‖c₀ + (c - c₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖c₀‖ + ‖c - c₀‖ := norm_add_le _ _
          _ < δ₁ := by linarith
      have hpc : IsPos (I := I) (M := M) g₀ D ε c := hpos c (lt_of_lt_of_le hcn hδ₁δ₀)
      have hcn' : ‖c‖ < (p z').1 := lt_of_lt_of_le hcn (hδ₁le z')
      have hc₀' : ‖c₀‖ < (p z').1 := lt_of_lt_of_le hc₀ (hδ₁le z')
      have hcontUc : Continuous (Ufun (I := I) (M := M) g₀ D ε z z' c) :=
        Work.Diff.STE.D.psi.continuous_Ufun (I := I) (M := M) hg D ε z z' c hpc
      have hcontUc₀ : Continuous (Ufun (I := I) (M := M) g₀ D ε z z' c₀) :=
        Work.Diff.STE.D.psi.continuous_Ufun (I := I) (M := M) hg D ε z z' c₀ hp₀c₀
      -- additivity of `scoeff` for the difference
      have hdiff : Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c) z.2.2.2
          - Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2
          = Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c
              - Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2 := by
        have h1 := Work.Diff.STE.B3.scoeff_add_of_support ρ ε
          (Ufun (I := I) (M := M) g₀ D ε z z' c₀)
          (Ufun (I := I) (M := M) g₀ D ε z z' c - Ufun (I := I) (M := M) g₀ D ε z z' c₀)
          hcontUc₀ (hcontUc.sub hcontUc₀)
          (support_Ufun_subset (I := I) (M := M) D ε z z' c₀)
          (support_sub_subset₂ (support_Ufun_subset (I := I) (M := M) D ε z z' c)
            (support_Ufun_subset (I := I) (M := M) D ε z z' c₀)) z.2.2.2
        rw [show Ufun (I := I) (M := M) g₀ D ε z z' c₀
              + (Ufun (I := I) (M := M) g₀ D ε z z' c
                - Ufun (I := I) (M := M) g₀ D ε z z' c₀)
              = Ufun (I := I) (M := M) g₀ D ε z z' c from by
            funext y; simp only [Pi.add_apply, Pi.sub_apply]; ring] at h1
        linarith [h1]
      have hbound : |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c
              - Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2|
          ≤ Q * ((p z').2 * ‖c - c₀‖) := by
        rw [hQ]
        refine Work.Diff.STE.B3.abs_scoeff_le ρ ε
          (Ufun (I := I) (M := M) g₀ D ε z z' c - Ufun (I := I) (M := M) g₀ D ε z z' c₀)
          (hcontUc.sub hcontUc₀)
          (support_sub_subset₂ (support_Ufun_subset (I := I) (M := M) D ε z z' c)
            (support_Ufun_subset (I := I) (M := M) D ε z z' c₀))
          z.2.2.2 ((p z').2 * ‖c - c₀‖) (mul_nonneg (hp z').2.1 (norm_nonneg _))
          (fun y => by
            simp only [Pi.sub_apply]
            rw [abs_sub_comm, norm_sub_rev]
            exact (hp z').2.2 c₀ c hc₀' hcn' hp₀c₀ hpc y)
      rw [hdiff]
      have hfac : 0 ≤ Q * (p z').2 := mul_nonneg hQnn (hp z').2.1
      calc |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c
              - Ufun (I := I) (M := M) g₀ D ε z z' c₀) z.2.2.2|
          ≤ Q * ((p z').2 * ‖c - c₀‖) := hbound
        _ = (Q * (p z').2) * ‖c - c₀‖ := by ring
        _ < ε'' := by
            have h3 : (Q * (p z').2) * (ε'' / (Q * (p z').2 + 1)) < ε'' := by
              rw [mul_div_assoc']
              rw [div_lt_iff₀ (by linarith : 0 < Q * (p z').2 + 1)]
              nlinarith [hfac, hε'']
            exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hc₂) hfac) h3
  -- assemble
  have hterm : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContinuousAt (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        ((ContinuousLinearMap.proj z' :
          (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ] ℝ)).smulRight
        ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (Ufun (I := I) (M := M) g₀ D ε z z' c) z.2.2.2)) c₀ := by
    intro z'
    have h1 : (fun c => ((ContinuousLinearMap.proj z' :
          (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ] ℝ)).smulRight
          ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c) z.2.2.2))
        = fun c => ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (Ufun (I := I) (M := M) g₀ D ε z z' c) z.2.2.2)
          • (((ContinuousLinearMap.proj z' :
              (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ] ℝ)).smulRight 1) := by
      funext c
      ext v
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
      ring
    rw [h1]
    exact ((hscal z').const_mul (1 / 2)).smul continuousAt_const
  have hsum : (fun c => psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c)
      = fun c => ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (ContinuousLinearMap.proj z').smulRight
            ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
              (Ufun (I := I) (M := M) g₀ D ε z z' c) z.2.2.2) := by
    funext c
    rw [psiConcDeriv]
  rw [hsum]
  exact tendsto_finsetSum Finset.univ (fun z' _ => (hterm z').tendsto)

/-! ## 6. Step 3: assembly -/

theorem contDiffAt_psiConc (g₀ : Submission.Diff.SMet I M)
    (hg : ChartData (I := I) (M := M) (g₀.inner))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) :
    ContDiffAt ℝ 1 (psiConc (I := I) (M := M) g₀ D ρ ε) 0 := by
  rw [contDiffAt_pi]
  intro z
  obtain ⟨δ₁, hδ₁, h1⟩ := hasFDerivAt_psiConc_z (I := I) (M := M) g₀ hg D ρ ε z
  obtain ⟨δ₂, hδ₂, h2⟩ := continuousAt_psiConcDeriv_z (I := I) (M := M) g₀ hg D ρ ε z
  refine contDiffAt_one_iff.mpr ⟨fun c => psiConcDeriv (I := I) (M := M) g₀ D ρ ε z c,
    {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ | ‖c‖ < min δ₁ δ₂}, ?_, ?_, ?_⟩
  · refine Metric.mem_nhds_iff.mpr ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun c hc => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hc
    exact hc
  · intro c hc
    exact (h2 c (lt_of_lt_of_le hc (min_le_right _ _))).continuousWithinAt
  · intro c hc
    exact h1 c (lt_of_lt_of_le hc (min_le_left _ _))

end

end Work.Diff.STE.D

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.Prelim` — the sliding-box geometry and the one-particle count

The first two steps of the proof of `Work.BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac`:

* `dlBox_eq_Box3`: the sliding box `dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` is the
  axis-parallel box `Box3 (boxLo ℓ d u) (boxHi ℓ d u)` with all sides `≤ ℓ*d`;
* `cnPlusBoxInd_one_eq`: at one particle the FS-faithful excited count is the local mean-free
  mass, `cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) (φ ∘ proj) = ∫_{B(u)}(φ - m_u)²`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The sliding box as an axis-parallel box -/

/-- Lower corner of the box `dlBox ℓ d u` in coordinate `j`. -/
def boxLo (ℓ d : ℝ) (u : ℝ³) (j : Fin 3) : ℝ :=
  max (-(ℓ / 2)) (((ℓ * d) • u) j - ℓ * d / 2)

/-- Upper corner of the box `dlBox ℓ d u` in coordinate `j`. -/
def boxHi (ℓ d : ℝ) (u : ℝ³) (j : Fin 3) : ℝ :=
  min (ℓ / 2) (((ℓ * d) • u) j + ℓ * d / 2)

lemma dlBox_eq_Box3 (ℓ d : ℝ) (u : ℝ³) :
    dlBox ℓ d u = Box3 (boxLo ℓ d u) (boxHi ℓ d u) := by
  ext x
  simp only [dlBox, Box3, Set.mem_inter_iff, Set.mem_setOf_eq, mem_acube_iff, boxLo, boxHi,
    Set.mem_Icc, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩ j
    have h1a := (h1 j).1
    have h1b := (h1 j).2
    have h2a := (h2 j).1
    have h2b := (h2 j).2
    refine ⟨?_, ?_⟩
    · rw [max_le_iff]; exact ⟨by linarith, by linarith⟩
    · rw [le_min_iff]; exact ⟨by linarith, by linarith⟩
  · intro h
    refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
    · have hb := (h j).1
      have ha := le_max_left (-(ℓ / 2)) (ℓ * d * u.ofLp j - ℓ * d / 2)
      linarith
    · have hb := (h j).2
      have ha := min_le_left (ℓ / 2) (ℓ * d * u.ofLp j + ℓ * d / 2)
      linarith
    · have hb := (h j).1
      have ha := le_max_right (-(ℓ / 2)) (ℓ * d * u.ofLp j - ℓ * d / 2)
      linarith
    · have hb := (h j).2
      have ha := min_le_right (ℓ / 2) (ℓ * d * u.ofLp j + ℓ * d / 2)
      linarith

/-- Every side of the sliding box is at most `ℓ*d`. -/
lemma boxHi_sub_boxLo_le {ℓ d : ℝ} (u : ℝ³) (j : Fin 3) :
    boxHi ℓ d u j - boxLo ℓ d u j ≤ ℓ * d := by
  have h1 : boxHi ℓ d u j ≤ ((ℓ * d) • u) j + ℓ * d / 2 := min_le_right _ _
  have h2 : ((ℓ * d) • u) j - ℓ * d / 2 ≤ boxLo ℓ d u j := le_max_right _ _
  linarith

/-- The corpus box mass is the real volume of the sliding box. -/
lemma boxMass_eq_volBox (ℓ d : ℝ) (u : ℝ³) :
    Work.SmallBoxSliding.boxMass ℓ d u = volBox (dlBox ℓ d u) := by
  rw [volBox]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u

/-! ## 2. The one-particle excited count is the local mean-free mass -/

/-- The `X 1`-state `fun x => φ (x 0)` evaluated at an updated configuration. -/
lemma update_zero_eq {φ : ℝ³ → ℝ} {x : Submission.BoseGases.X 1} {z : ℝ³} :
    (fun y : Submission.BoseGases.X 1 => φ (y 0)) (Function.update x 0 z) = φ z := by
  have h : Function.update x 0 z = fun _ : Fin 1 => z := by
    funext i
    rw [Fin.eq_zero i]
    exact Function.update_self 0 z x
  rw [h]

/-- **The one-particle excited count is the local mean-free mass.** -/
theorem cnPlusBoxInd_one_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (φ : ℝ³ → ℝ) (hφ : Continuous φ) (u : ℝ³) :
    Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
        (fun x : Submission.BoseGases.X 1 => φ (x 0))
      = ∫ z in dlBox ℓ d u,
          (φ z - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ w in dlBox ℓ d u, φ w) ^ 2 := by
  classical
  set A : Set ℝ³ := dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolA
  set m : ℝ := (1 / volA) * ∫ w in A, φ w with hm
  rw [Work.UBBInputs8.cnPlusBoxInd, Fin.sum_univ_one]
  have hAmeas : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hstep : ∀ x : Submission.BoseGases.X 1,
      Work.UBBInputs8.boxQInd volA A 0 (fun y : Submission.BoseGases.X 1 => φ (y 0)) x
        = A.indicator (fun _ => (1 : ℝ)) (x 0) * (φ (x 0) - m) := by
    intro x
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have hupd : (∫ z in A, (fun y : Submission.BoseGases.X 1 => φ (y 0))
          (Function.update x 0 z)) = ∫ z in A, φ z := by
      refine MeasureTheory.setIntegral_congr_fun hAmeas (fun z _ => ?_)
      exact update_zero_eq
    rw [hupd, ← hm]
    ring
  have hsquare : ∀ x : Submission.BoseGases.X 1,
      (Work.UBBInputs8.boxQInd volA A 0 (fun y : Submission.BoseGases.X 1 => φ (y 0)) x) ^ 2
        = A.indicator (fun z => (φ z - m) ^ 2) (x 0) := by
    intro x
    rw [hstep x]
    by_cases hx : (x 0) ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
  rw [MeasureTheory.setIntegral_congr_fun (abox_measurable 1 ℓ) (fun x _ => hsquare x)]
  rw [Work.KinPSuperadd.integral_abox_one_slot
    (fun x : Submission.BoseGases.X 1 => A.indicator (fun z => (φ z - m) ^ 2) (x 0))]
  simp only [Fin.default_eq_zero]
  have hsub : A ⊆ acube ℓ := fun z hz => (mem_dlBox_iff ℓ d u z).1 hz |>.1
  have hkey : (∫ z in acube ℓ, A.indicator (fun z => (φ z - m) ^ 2) z)
      = ∫ z in A, (φ z - m) ^ 2 := by
    rw [← MeasureTheory.integral_indicator (acube_measurable ℓ),
      ← MeasureTheory.integral_indicator hAmeas]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ acube ℓ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (fun h => hz (hsub h))]
  simpa using hkey

end Work.BoseFixB1P

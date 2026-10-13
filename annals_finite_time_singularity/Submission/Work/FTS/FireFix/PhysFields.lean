/-
# `Work.FTS.FireFix.PhysFields` — the velocity data of the reconstruction (oddness, curl, datum)

This module completes the *data* of the firing theorem for the negated physical vorticity
`ω := −physOmega α A B g C` (design correction 1):

* `neg_physOmega_isOdd` — the reconstructed velocity `u = physVel ω` is odd at every physical time
  `t ∈ [0, C.T)`: the slice of `ω` is the swirl field `W(ρ(x),θ(x)) • e_θ(x)` whose angular scalar
  is odd in `θ` (the profile is the odd extension of `F_* + g`), so
  `Work.FTS.Physical.isOdd_physVel_of_swirlShape` applies;
* `neg_physOmega_curl_div` — the curl and divergence clauses of the reconstruction, from the swirl
  Biot–Savart law `Work.FTS.BSSwirl.BiotSavartSwirl` (`hBS`, the honest replacement for the *false*
  `Work.LWP.BiotSavartLaw` of `FTS_NOTBSL.lean.txt`), applied slicewise to the per-strip bundle's
  `HolderWith` and support clauses;
* `neg_physOmega_datum_holder` — the `C^{1,α}` datum `IsContDiffHolder ℝ α (u · 0)`, by restricting
  the joint `C^{1,α}` strip statement of the space–time Schauder estimate to the time slice `t = 0`
  (`Prime.physVel_isContDiffHolder.isContDiffHolder_slice`).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.FireFix.PhysData
import Submission.Work.FTS.Physical.BiotSavart.isOdd_physVel_of_swirlShape
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Regularity (pExp gSlice physVort)
open Work.FTS.BSSwirl (swirlField)
open Work.FTS.Physical (PhysClock)

/-! ## The `(ρ,θ)`-dictionary at a point -/

theorem rhoP_radial_axial (x : R3) :
    Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.rho x := by
  rw [Work.Cyl.rhoP, Work.Cyl.rho, Work.Cyl.radial_sq]

theorem thetaP_radial_axial (x : R3) :
    Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) = Work.Cyl.theta x := rfl

/-! ## The swirl scalar of the (negated) physical vorticity -/

/-- **The swirl scalar of the negated physical vorticity slice.**  For a fake time `τ`, the slice
`x ↦ −physOmega α A B g C x t` (with `τ = clockInv C t`) is the swirl field of

  `negSwirlScalar α τ A B g ρ θ = −((A τ)⁻¹ · profile (3α) (g·τ) (ρ^{3α}/B τ) θ)`,

in the `(ρ,θ)` coordinates of the cylinder. -/
noncomputable def negSwirlScalar (α τ : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (ρ θ : ℝ) : ℝ :=
  -((A τ)⁻¹ * Work.ConstructionInstance.profile (pExp α) (gSlice g τ)
      (ρ ^ pExp α / B τ) θ)

/-- The pointwise form of the swirl representation, in the meridian coordinates `(ρ(x),θ(x))`. -/
theorem neg_physOmega_slice_eq {α : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (x : R3) (t : ℝ) :
    - Work.FTS.Physical.physOmega α A B g C x t
      = negSwirlScalar α (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x := by
  rw [Work.FTS.Physical.physOmega_apply, Work.FTS.Regularity.physVort_apply,
    Work.ConstructionInstance.omegaSz_apply, negSwirlScalar, neg_smul, smul_smul]

/-- The slice `x ↦ −physOmega α A B g C x t` is the swirl field of `negSwirlScalar`, in the
`(radial, axial)` coordinates in which `Work.FTS.BSSwirl.BiotSavartSwirl` is stated. -/
theorem neg_physOmega_swirlShape {α : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (t : ℝ) :
    (fun x : R3 => - Work.FTS.Physical.physOmega α A B g C x t)
      = swirlField (fun r a => negSwirlScalar α (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) := by
  funext x
  rw [Work.FTS.BSSwirl.swirlField_apply, rhoP_radial_axial, thetaP_radial_axial]
  exact neg_physOmega_slice_eq x t

/-- **The swirl scalar is odd in the angle**: `negSwirlScalar α τ A B g ρ (−θ) = −…`.  This is the
oddness of the profile `profile (3α) (g·τ)` (the odd extension of `F_* + g`), which holds because
the perturbation vanishes at `θ = 0` (`VanishTheta`). -/
theorem negSwirlScalar_odd {α τ : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (hα : α ≠ 0) (hvt : ∀ z : ℝ, gSlice g τ z 0 = 0) (ρ θ : ℝ) :
    negSwirlScalar α τ A B g ρ (-θ) = - negSwirlScalar α τ A B g ρ θ := by
  have hp : pExp α ≠ 0 := by
    rw [pExp]
    intro h
    exact hα (by linarith)
  rw [negSwirlScalar, negSwirlScalar, Work.ConstructionInstance.profile_odd hp hvt]
  ring

/-! ## Oddness of the reconstructed velocity -/

/-- **Oddness of the reconstructed velocity at every physical time** (for the signed vorticity
`ω = −physOmega`).  The slice of `ω` is a swirl field whose angular scalar is odd in the angle, so
`Work.FTS.Physical.isOdd_physVel_of_swirlShape` gives the oddness of `u = physVel ω`. -/
theorem neg_physOmega_isOdd {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    {t : ℝ} (ht : t ∈ Set.Ico 0 C.T) :
    IsOdd ((Work.FTS.Physical.physVel
      (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) · t) := by
  have hTpos : 0 < C.T := Work.FTS.Physical.Clock.T_pos C
  set S : ℝ := (t + C.T) / 2 with hSdef
  have hS : S ∈ Set.Ioo (0 : ℝ) C.T :=
    ⟨by rw [hSdef]; linarith [ht.1, ht.2], by rw [hSdef]; linarith [ht.2]⟩
  have htSle : t ≤ S := by rw [hSdef]; linarith [ht.2]
  set Sel : ℝ := Work.FTS.Physical.clockInv C S with hSeldef
  have hSelpos : 0 < Sel := by
    rw [hSeldef]; exact Work.FTS.Physical.clockInv_pos_of_pos C hS
  have hsel : Work.FTS.RegPkgGal.RegPkg' (α : ℝ) Sel A B g := hreg Sel hSelpos
  have hτmem : Work.FTS.Physical.clockInv C t ∈ Set.Icc (0 : ℝ) Sel := by
    refine ⟨Work.FTS.Physical.clockInv_nonneg C ht, ?_⟩
    rw [hSeldef]
    exact Work.FTS.Physical.clockInv_mono C ht ⟨hS.1.le, hS.2⟩ htSle
  have hvt : ∀ z : ℝ, gSlice g (Work.FTS.Physical.clockInv C t) z 0 = 0 :=
    fun z => (hsel.hvt _ hτmem).1 z
  refine Work.FTS.Physical.isOdd_physVel_of_swirlShape
    (W := negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g) ?_ ?_
  · intro x
    exact neg_physOmega_slice_eq x t
  · refine negSwirlScalar_odd ?_ hvt
    have hαpos : 0 < (α : ℝ) := (hreg 1 one_pos).hα
    intro h0
    rw [h0] at hαpos
    exact lt_irrefl 0 hαpos

/-! ## The curl and divergence clauses -/

/-- **The curl and divergence clauses of the reconstruction** (design §1, item 7a): for the swirl
Biot–Savart law `hBS`, the Biot–Savart field of the negated physical vorticity inverts its curl and
is divergence-free at every physical time.

Proof: on the strip `[0,S]`, `S = (t + C.T)/2`, the per-strip bundle supplies both the `HolderWith`
datum and the support of the slice; the slice *is* a swirl field (`neg_physOmega_swirlShape`), so
`BiotSavartSwirl` applies. -/
theorem neg_physOmega_curl_div {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hBS : Work.FTS.BSSwirl.BiotSavartSwirl)
    (hbun : ∀ S' ∈ Set.Ioo 0 C.T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α
        (fun x t => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) R S') :
    (∀ t ∈ Set.Ico 0 C.T, ∀ x : R3,
        vorticity (fun y => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t) x
          = - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) ∧
      (∀ t ∈ Set.Ico 0 C.T, div (fun y => Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t) = 0) := by
  constructor
  · intro t ht x
    set S : ℝ := (t + C.T) / 2 with hSdef
    have hS : S ∈ Set.Ioo (0 : ℝ) C.T :=
      ⟨by rw [hSdef]; linarith [ht.1, ht.2], by rw [hSdef]; linarith [ht.2]⟩
    have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1, by rw [hSdef]; linarith [ht.2]⟩
    obtain ⟨R, hb⟩ := hbun S hS
    obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩, -, -⟩ := hb
    have hholder : HolderWith H α (swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
      exact hH t htS
    have hsupp' : ∀ y : R3, swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) y ≠ 0 → ‖y‖ ≤ R := by
      intro y hy
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
        at hy
      have h := hsupp t htS y hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    obtain ⟨hc, -⟩ := hBS (fun r a => negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t)
      A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) H α R hα hα1 hholder hsupp'
    have hfun : (fun y : R3 => Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t)
        = Work.LWP.biotSavart (swirlField (fun r a => negSwirlScalar (α : ℝ)
            (Work.FTS.Physical.clockInv C t) A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      funext y
      simp only [Work.FTS.Physical.physVel_apply,
        neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
    rw [hfun]
    have hx : - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t
        = swirlField (fun r a => negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t)
            A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) x :=
      congrFun (neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t) x
    rw [hx]
    exact hc x
  · intro t ht
    set S : ℝ := (t + C.T) / 2 with hSdef
    have hS : S ∈ Set.Ioo (0 : ℝ) C.T :=
      ⟨by rw [hSdef]; linarith [ht.1, ht.2], by rw [hSdef]; linarith [ht.2]⟩
    have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1, by rw [hSdef]; linarith [ht.2]⟩
    obtain ⟨R, hb⟩ := hbun S hS
    obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩, -, -⟩ := hb
    have hholder : HolderWith H α (swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
      exact hH t htS
    have hsupp' : ∀ y : R3, swirlField (fun r a =>
        negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t) A B g
          (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) y ≠ 0 → ‖y‖ ≤ R := by
      intro y hy
      rw [← neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
        at hy
      have h := hsupp t htS y hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    obtain ⟨-, hd⟩ := hBS (fun r a => negSwirlScalar (α : ℝ) (Work.FTS.Physical.clockInv C t)
      A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a)) H α R hα hα1 hholder hsupp'
    have hfun : (fun y : R3 => Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t)
        = Work.LWP.biotSavart (swirlField (fun r a => negSwirlScalar (α : ℝ)
            (Work.FTS.Physical.clockInv C t) A B g (Work.Cyl.rhoP r a) (Work.Cyl.thetaP r a))) := by
      funext y
      simp only [Work.FTS.Physical.physVel_apply,
        neg_physOmega_swirlShape (α := (α : ℝ)) (A := A) (B := B) (g := g) (C := C) t]
    rw [hfun]
    funext x
    exact hd x

/-- **The `C^{1,α}` datum of the reconstruction** (for `ω = −physOmega`): the restriction of the
joint `C^{1,α}` strip statement of the space–time Schauder estimate to the time slice `t = 0`. -/
theorem neg_physOmega_datum_holder {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : PhysClock}
    (hbun : ∀ S' ∈ Set.Ioo 0 C.T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α
        (fun x t => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x t) R S') :
    IsContDiffHolder ℝ α ((Work.FTS.Physical.physVel
      (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) · 0) := by
  have hTpos : 0 < C.T := Work.FTS.Physical.Clock.T_pos C
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S ∈ Set.Ioo (0 : ℝ) C.T :=
    ⟨C.T / 2, ⟨by linarith, by linarith⟩⟩
  obtain ⟨R, hb⟩ := hbun S hS
  have hstrip := Work.FTS.Physical.isContDiffHolderOn_physVel (α := α) hα hα1 hS.1 hb
  have hslice := Prime.isContDiffHolder_slice (S := S) (τ := 0)
    ⟨le_rfl, hS.1.le⟩ α hstrip
  simpa only [Function.uncurry, Work.FTS.Physical.physVel_apply] using hslice

end Work.FTS.FireFix

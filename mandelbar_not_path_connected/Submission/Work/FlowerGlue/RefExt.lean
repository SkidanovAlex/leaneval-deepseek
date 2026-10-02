/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FlowerGlue.RefCoord
import Submission.Work.FlowerGlue.cyl_rigid

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.RefExt` — the Écalle extension of `E.φa` to the reference petal

This file implements steps 1–4 of the transfer of `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md`
§1.2: given a reference coordinate `R : RefCoord d` and an abstract Écalle datum
`E : EcalleData d`, we

* `eN`, `phiTilde` — extend `E.φa` from `E.Pa` to the reference petal `R.P` by pulling back along
  the dynamics: `φ̃ z := E.φa (F^[n] z) - n` for `n` large enough that `F^[n] z ∈ E.Pa`;
* `phiTilde_eq_of_mem_Pa` — the value is `E.φa (F^[n] z) - n` for **every** `n` with
  `F^[n] z ∈ E.Pa` (`φa_shift` + the Abel iterate `Pa_abel_iterate`);
* `phiTilde_injOn`, `phiTilde_differentiableOn` — `φ̃` is injective and holomorphic on `R.P`
  (injectivity from `E.φa_inj` and `R.inj`; holomorphy because near `z₀ ∈ R.P` the extension
  agrees with the honest `E.φa ∘ F^[eN z₀] - eN z₀`);
* `U`, `psi` — the image `U = R.φ '' R.P` of the petal and the section `ψ = φ̃ ∘ R.φ⁻¹` of `R.φ`
  over it;
* `phi_local_inv`, `isOpen_U` — a holomorphic local inverse of `R.φ` (the inverse function
  theorem), whence `U` is open;
* `psi_shift`, `psi_injOn`, `psi_differentiableOn` — `ψ` is `1`-equivariant, injective and
  holomorphic on `U`;
* `TN`, `T` — the `1`-equivariant entire comparison map `T`, defined from the cylinder saturation
  `R.sat` by `T ζ = ψ (ζ + TN ζ) - TN ζ`;
* `T_eq`, `T_per`, `T_inj`, `T_phi`, `T_differentiable` — `T` is well defined independently of the
  choice of the saturation index, `1`-equivariant, injective, entire, and `T (R.φ z) = φ̃ z`;
* `exists_const` — consequently `Work.FlowerGlue.cyl_rigid` gives `φ̃ z = R.φ z + s`.
-/

open scoped Topology
open Filter Set Function
open Classical

namespace Work.FlowerGlue

open Work.EL (RootParabolic F)

noncomputable section

variable {c : ℂ} {d : RootParabolic c}

/-! ## 1. The extension of `E.φa` to the reference petal -/

/-- Every orbit of a point of the reference petal eventually enters the attracting petal `E.Pa`. -/
theorem entrance_orbit (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ} (hz : z ∈ R.P) :
    ∃ N : ℕ, ∀ n ≥ N, (F c)^[n] z ∈ E.Pa := by
  have hP : ∀ n : ℕ, (F c)^[n] z ∈ R.P := fun n => R.mapsTo.iterate n hz
  have hne : ∀ n : ℕ, (F c)^[n] z ≠ d.z₁ := fun n h => R.z₁_not_mem (h ▸ hP n)
  obtain ⟨n₀, hn₀⟩ := E.enters z (R.tendsto z hz) hne
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hnk : (F c)^[n] z = (F c)^[k] ((F c)^[n₀] z) := by
    rw [hk, add_comm n₀ k, Function.iterate_add_apply]
  rw [hnk]
  exact E.mapsTo_Pa.iterate k hn₀

/-- A valid entrance time of the orbit of `z` in the attracting petal `E.Pa`. -/
def eN (R : RefCoord d) (E : Work.FQC.EcalleData d) (z : ℂ) : ℕ :=
  if h : z ∈ R.P then Classical.choose (entrance_orbit R E h) else 0

theorem eN_spec (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ} (hz : z ∈ R.P) :
    ∀ n ≥ eN R E z, (F c)^[n] z ∈ E.Pa := by
  have h := Classical.choose_spec (entrance_orbit R E hz)
  rwa [eN, dif_pos hz]

/-- The extension of `E.φa` from `E.Pa` to the reference petal `R.P`, obtained by pulling back
along the dynamics. -/
def phiTilde (R : RefCoord d) (E : Work.FQC.EcalleData d) (z : ℂ) : ℂ :=
  if h : z ∈ R.P then E.φa ((F c)^[eN R E z] z) - (eN R E z : ℂ) else 0

theorem phiTilde_spec (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ} (hz : z ∈ R.P) :
    phiTilde R E z = E.φa ((F c)^[eN R E z] z) - (eN R E z : ℂ) := by
  rw [phiTilde, dif_pos hz]

/-- The Abel equation for `R.φ` along the orbit. -/
theorem R_shift_iterate (R : RefCoord d) {z : ℂ} (hz : z ∈ R.P) (k : ℕ) :
    R.φ ((F c)^[k] z) = R.φ z + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', R.shift _ (R.mapsTo.iterate k hz), ih]
    push_cast
    ring

/-- The Abel iterate of `E.φa` on the petal: `E.φa (F^[k] w) = E.φa w + k` for `w ∈ E.Pa`. -/
theorem Pa_abel_iterate (E : Work.FQC.EcalleData d) {w : ℂ} (hw : w ∈ E.Pa) (k : ℕ) :
    E.φa ((F c)^[k] w) = E.φa w + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', E.φa_shift _ (E.mapsTo_Pa.iterate k hw), ih]
    push_cast
    ring

/-- The extension `φ̃` is given by `E.φa (F^[n] z) - n` for **every** `n` with `F^[n] z ∈ E.Pa`. -/
theorem phiTilde_eq_of_mem_Pa (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ}
    (hz : z ∈ R.P) (n : ℕ) (hn : (F c)^[n] z ∈ E.Pa) :
    phiTilde R E z = E.φa ((F c)^[n] z) - n := by
  have hK : (F c)^[eN R E z] z ∈ E.Pa := eN_spec R E hz _ le_rfl
  have h1 : E.φa ((F c)^[eN R E z + n] z) = E.φa ((F c)^[n] z) + (eN R E z : ℂ) := by
    rw [Function.iterate_add_apply]
    exact Pa_abel_iterate E hn _
  have h2 : E.φa ((F c)^[eN R E z + n] z) = E.φa ((F c)^[eN R E z] z) + (n : ℂ) := by
    rw [show (F c)^[eN R E z + n] z = (F c)^[n] ((F c)^[eN R E z] z) from by
      rw [add_comm (eN R E z) n, Function.iterate_add_apply]]
    exact Pa_abel_iterate E hK _
  have h2' : E.φa ((F c)^[eN R E z] z) = E.φa ((F c)^[eN R E z + n] z) - (n : ℂ) := by
    rw [h2]; ring
  rw [phiTilde_spec R E hz, h2', h1]
  ring

/-- The Abel equation for the extension `φ̃` at one step. -/
theorem phiTilde_shift (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ} (hz : z ∈ R.P) :
    phiTilde R E (F c z) = phiTilde R E z + 1 := by
  have hzP : F c z ∈ R.P := R.mapsTo hz
  have hmem : (F c)^[eN R E z + 1] z ∈ E.Pa := eN_spec R E hz _ (Nat.le_succ _)
  have hmem' : (F c)^[eN R E z] (F c z) ∈ E.Pa := by
    have h := hmem
    rw [Function.iterate_succ_apply] at h
    exact h
  have harg : (F c)^[eN R E z] (F c z) = (F c)^[eN R E z + 1] z :=
    Function.iterate_succ_apply (F c) (eN R E z) z
  rw [phiTilde_eq_of_mem_Pa R E hzP (eN R E z) hmem',
      phiTilde_eq_of_mem_Pa R E hz (eN R E z + 1) hmem, harg]
  push_cast
  ring

/-- The Abel equation for the extension `φ̃` along the orbit. -/
theorem phiTilde_shift_iterate (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ}
    (hz : z ∈ R.P) (m : ℕ) :
    phiTilde R E ((F c)^[m] z) = phiTilde R E z + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', phiTilde_shift R E (R.mapsTo.iterate m hz), ih]
    push_cast
    ring

/-- The extension `φ̃` is injective on the reference petal. -/
theorem phiTilde_injOn (R : RefCoord d) (E : Work.FQC.EcalleData d) :
    Set.InjOn (phiTilde R E) R.P := by
  intro z hz z' hz' heq
  set K : ℕ := max (eN R E z) (eN R E z') with hK
  have hzK : (F c)^[K] z ∈ E.Pa := eN_spec R E hz K (by rw [hK]; exact le_max_left _ _)
  have hz'K : (F c)^[K] z' ∈ E.Pa := eN_spec R E hz' K (by rw [hK]; exact le_max_right _ _)
  have h1 : phiTilde R E z = E.φa ((F c)^[K] z) - (K : ℂ) :=
    phiTilde_eq_of_mem_Pa R E hz K hzK
  have h2 : phiTilde R E z' = E.φa ((F c)^[K] z') - (K : ℂ) :=
    phiTilde_eq_of_mem_Pa R E hz' K hz'K
  have h3 : E.φa ((F c)^[K] z) = E.φa ((F c)^[K] z') := by
    rw [h1, h2] at heq
    have := congrArg (fun u : ℂ => u + (K : ℂ)) heq
    simpa using this
  have h4 := E.φa_inj hzK hz'K h3
  have h5 : R.φ ((F c)^[K] z) = R.φ ((F c)^[K] z') := by rw [h4]
  rw [R_shift_iterate R hz K, R_shift_iterate R hz' K] at h5
  exact R.inj hz hz' (add_right_cancel h5)

/-- The extension `φ̃` is holomorphic on the reference petal. -/
theorem phiTilde_differentiableOn (R : RefCoord d) (E : Work.FQC.EcalleData d) :
    DifferentiableOn ℂ (phiTilde R E) R.P := by
  intro z₀ hz₀
  have hN₀ : (F c)^[eN R E z₀] z₀ ∈ E.Pa := eN_spec R E hz₀ _ le_rfl
  have hFdiff : Differentiable ℂ (F c) := by
    show Differentiable ℂ (Work.Landing.Tsq c)^[5]
    have h : Differentiable ℂ (Work.Landing.Tsq c) := by
      have he : Work.Landing.Tsq c = fun z : ℂ => (z ^ 2 + star c) ^ 2 + c := rfl
      rw [he]; fun_prop
    exact h.iterate 5
  have hV : (fun z : ℂ => (F c)^[eN R E z₀] z) ⁻¹' E.Pa ∈ 𝓝 z₀ :=
    ((hFdiff.iterate _).continuous.continuousAt).preimage_mem_nhds (E.isOpen_Pa.mem_nhds hN₀)
  have hdiff : DifferentiableAt ℂ
      (fun z : ℂ => E.φa ((F c)^[eN R E z₀] z) - (eN R E z₀ : ℂ)) z₀ := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (F c)^[eN R E z₀] z) z₀ :=
      (hFdiff.iterate _).differentiableAt
    have h2 : DifferentiableAt ℂ E.φa ((F c)^[eN R E z₀] z₀) :=
      E.φa_diff.differentiableAt (E.isOpen_Pa.mem_nhds hN₀)
    exact (h2.comp z₀ h1).sub_const _
  have hev : phiTilde R E =ᶠ[𝓝 z₀]
      fun z : ℂ => E.φa ((F c)^[eN R E z₀] z) - (eN R E z₀ : ℂ) := by
    filter_upwards [hV, R.isOpen.mem_nhds hz₀] with z hzPa hzP
    exact phiTilde_eq_of_mem_Pa R E hzP _ hzPa
  exact (hdiff.congr_of_eventuallyEq hev).differentiableWithinAt

/-! ## 2. The section `ψ = φ̃ ∘ R.φ⁻¹` over the image of the petal -/

/-- The image of the reference petal under the reference coordinate. -/
def U (R : RefCoord d) : Set ℂ := R.φ '' R.P

/-- The section of `R.φ` over `U`, composed with the extension `φ̃`. -/
def psi (R : RefCoord d) (E : Work.FQC.EcalleData d) : ℂ → ℂ :=
  fun w => phiTilde R E (Function.invFunOn R.φ R.P w)

theorem psi_apply (R : RefCoord d) (E : Work.FQC.EcalleData d) {w : ℂ} (hw : w ∈ U R) :
    Function.invFunOn R.φ R.P w ∈ R.P ∧ R.φ (Function.invFunOn R.φ R.P w) = w := by
  have h : ∃ z ∈ R.P, R.φ z = w := hw
  exact ⟨Function.invFunOn_mem h, Function.invFunOn_eq h⟩

/-- The section `ψ` inverts `R.φ` in the sense that `ψ (R.φ z) = φ̃ z`. -/
theorem psi_phi (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ} (hz : z ∈ R.P) :
    psi R E (R.φ z) = phiTilde R E z := by
  have h : ∃ z' ∈ R.P, R.φ z' = R.φ z := ⟨z, hz, rfl⟩
  have hz' : Function.invFunOn R.φ R.P (R.φ z) = z :=
    R.inj (Function.invFunOn_mem h) hz (Function.invFunOn_eq h)
  rw [psi, hz']

/-- A holomorphic local inverse of the reference coordinate at a point of the petal, together
with the fact that it maps into the petal. -/
theorem phi_local_inv (R : RefCoord d) {z₀ : ℂ} (hz₀ : z₀ ∈ R.P) :
    ∃ σ : ℂ → ℂ, AnalyticAt ℂ σ (R.φ z₀) ∧ σ (R.φ z₀) = z₀ ∧
      (∀ᶠ w in 𝓝 (R.φ z₀), R.φ (σ w) = w) ∧ (∀ᶠ w in 𝓝 (R.φ z₀), σ w ∈ R.P) := by
  have hφan : AnalyticAt ℂ R.φ z₀ := R.diff.analyticAt (R.isOpen.mem_nhds hz₀)
  have hderiv : deriv R.φ z₀ ≠ 0 := R.deriv_ne z₀ hz₀
  set σ : ℂ → ℂ :=
    HasStrictDerivAt.localInverse R.φ (deriv R.φ z₀) z₀ hφan.hasStrictDerivAt hderiv with hσdef
  have hσan : AnalyticAt ℂ σ (R.φ z₀) := hφan.analyticAt_localInverse hderiv
  have hσ0 : σ (R.φ z₀) = z₀ :=
    HasStrictFDerivAt.localInverse_apply_image
      (hf := hφan.hasStrictDerivAt.hasStrictFDerivAt_equiv hderiv)
  have hσr : ∀ᶠ w in 𝓝 (R.φ z₀), R.φ (σ w) = w :=
    HasStrictDerivAt.eventually_right_inverse (hf := hφan.hasStrictDerivAt) (hf' := hderiv)
  have hσmem : ∀ᶠ w in 𝓝 (R.φ z₀), σ w ∈ R.P := by
    have hcont : ContinuousAt σ (R.φ z₀) := hσan.continuousAt
    have hmem : R.P ∈ 𝓝 (σ (R.φ z₀)) := by rw [hσ0]; exact R.isOpen.mem_nhds hz₀
    exact hcont.preimage_mem_nhds hmem
  exact ⟨σ, hσan, hσ0, hσr, hσmem⟩

/-- The image of the reference petal under the reference coordinate is open. -/
theorem isOpen_U (R : RefCoord d) : IsOpen (U R) := by
  rw [isOpen_iff_mem_nhds]
  intro w₀ hw₀
  obtain ⟨z₀, hz₀P, hz₀w⟩ := hw₀
  obtain ⟨σ, hσan, hσ0, hσr, hσmem⟩ := phi_local_inv R hz₀P
  have hσr' : ∀ᶠ w in 𝓝 w₀, R.φ (σ w) = w := by rwa [hz₀w] at hσr
  have hσmem' : ∀ᶠ w in 𝓝 w₀, σ w ∈ R.P := by rwa [hz₀w] at hσmem
  have hev : ∀ᶠ w in 𝓝 w₀, w ∈ U R := by
    filter_upwards [hσr', hσmem'] with w h1 h2
    exact ⟨σ w, h2, h1⟩
  exact Filter.eventually_iff.mp hev

/-- `U` is closed under positive integer translations. -/
theorem mem_U_add (R : RefCoord d) {w : ℂ} (hw : w ∈ U R) (m : ℕ) : w + m ∈ U R := by
  obtain ⟨z, hzP, hzw⟩ := hw
  exact ⟨(F c)^[m] z, R.mapsTo.iterate m hzP, by rw [R_shift_iterate R hzP m, hzw]⟩

/-- The section `ψ` is `1`-equivariant on `U`. -/
theorem psi_shift (R : RefCoord d) (E : Work.FQC.EcalleData d) {w : ℂ} (hw : w ∈ U R) (m : ℕ) :
    psi R E (w + m) = psi R E w + m := by
  obtain ⟨z, hzP, hzw⟩ := hw
  have hwU : ∃ z' ∈ R.P, R.φ z' = w := ⟨z, hzP, hzw⟩
  have h1 : Function.invFunOn R.φ R.P w = z :=
    R.inj (Function.invFunOn_mem hwU) hzP ((Function.invFunOn_eq hwU).trans hzw.symm)
  have hwm : R.φ ((F c)^[m] z) = w + m := by
    rw [R_shift_iterate R hzP m, hzw]
  have h2 : Function.invFunOn R.φ R.P (w + m) = (F c)^[m] z :=
    R.inj (Function.invFunOn_mem ⟨(F c)^[m] z, R.mapsTo.iterate m hzP, hwm⟩)
      (R.mapsTo.iterate m hzP)
      ((Function.invFunOn_eq ⟨(F c)^[m] z, R.mapsTo.iterate m hzP, hwm⟩).trans hwm.symm)
  simp only [psi]
  rw [h1, h2, phiTilde_shift_iterate R E hzP m]

/-- The section `ψ` is injective on `U`. -/
theorem psi_injOn (R : RefCoord d) (E : Work.FQC.EcalleData d) :
    Set.InjOn (psi R E) (U R) := by
  intro w hw w' hw' heq
  have h1 := (psi_apply R E hw).2
  have h2 := (psi_apply R E hw').2
  have h3 : Function.invFunOn R.φ R.P w = Function.invFunOn R.φ R.P w' :=
    phiTilde_injOn R E (psi_apply R E hw).1 (psi_apply R E hw').1 heq
  rw [← h1, ← h2, h3]

/-- The section `ψ` is holomorphic on `U`. -/
theorem psi_differentiableOn (R : RefCoord d) (E : Work.FQC.EcalleData d) :
    DifferentiableOn ℂ (psi R E) (U R) := by
  intro w₀ hw₀
  have hw₀' : ∃ z ∈ R.P, R.φ z = w₀ := hw₀
  obtain ⟨z₀, hz₀P, hz₀w⟩ := hw₀'
  obtain ⟨σ, hσan, hσ0, hσr, hσmem⟩ := phi_local_inv R hz₀P
  have hσr' : ∀ᶠ w in 𝓝 w₀, R.φ (σ w) = w := by rwa [hz₀w] at hσr
  have hσmem' : ∀ᶠ w in 𝓝 w₀, σ w ∈ R.P := by rwa [hz₀w] at hσmem
  have hσ0' : σ w₀ = z₀ := by rw [← hz₀w]; exact hσ0
  have hσd : DifferentiableAt ℂ σ w₀ := by rw [← hz₀w]; exact hσan.differentiableAt
  have hder : DifferentiableAt ℂ (phiTilde R E) (σ w₀) :=
    (phiTilde_differentiableOn R E).differentiableAt
      (R.isOpen.mem_nhds (by rw [hσ0']; exact hz₀P))
  have hcomp : DifferentiableAt ℂ (fun w => phiTilde R E (σ w)) w₀ :=
    hder.comp w₀ hσd
  refine (hcomp.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hσr', hσmem', (isOpen_U R).mem_nhds hw₀] with w hright hmem hwU
  simp only [psi]
  have hinv : Function.invFunOn R.φ R.P w = σ w :=
    R.inj (Function.invFunOn_mem (show ∃ z ∈ R.P, R.φ z = w from hwU)) hmem
      ((Function.invFunOn_eq (show ∃ z ∈ R.P, R.φ z = w from hwU)).trans hright.symm)
  rw [hinv]

/-! ## 3. The `1`-equivariant entire comparison map `T` -/

/-- A saturation index: `ζ + TN R ζ ∈ U`. -/
def TN (R : RefCoord d) (ζ : ℂ) : ℕ := Classical.choose (R.sat ζ)

theorem TN_spec (R : RefCoord d) (ζ : ℂ) {n : ℕ} (hn : TN R ζ ≤ n) : ζ + n ∈ U R :=
  Classical.choose_spec (R.sat ζ) n hn

/-- The comparison map of the cylinder: `T ζ = ψ (ζ + TN ζ) - TN ζ`. -/
def T (R : RefCoord d) (E : Work.FQC.EcalleData d) : ℂ → ℂ :=
  fun ζ => psi R E (ζ + (TN R ζ : ℂ)) - (TN R ζ : ℂ)

/-- `T` is independent of the choice of the saturation index. -/
theorem T_eq (R : RefCoord d) (E : Work.FQC.EcalleData d) (ζ : ℂ) {n : ℕ}
    (hn : ζ + n ∈ U R) : T R E ζ = psi R E (ζ + n) - n := by
  have hN : ζ + (TN R ζ : ℂ) ∈ U R := TN_spec R ζ le_rfl
  rcases le_total (TN R ζ) n with h | h
  · have hcast : ζ + (TN R ζ : ℂ) + ((n - TN R ζ : ℕ) : ℂ) = ζ + (n : ℂ) := by
      rw [Nat.cast_sub h]; ring
    have h1 : psi R E (ζ + n) = psi R E (ζ + TN R ζ) + (n - TN R ζ : ℕ) := by
      have := psi_shift R E hN (n - TN R ζ)
      rwa [hcast] at this
    rw [T, h1, Nat.cast_sub h]
    ring
  · have hcast : ζ + (n : ℂ) + ((TN R ζ - n : ℕ) : ℂ) = ζ + (TN R ζ : ℂ) := by
      rw [Nat.cast_sub h]; ring
    have h1 : psi R E (ζ + TN R ζ) = psi R E (ζ + n) + (TN R ζ - n : ℕ) := by
      have := psi_shift R E hn (TN R ζ - n)
      rwa [hcast] at this
    rw [T, h1, Nat.cast_sub h]
    ring

/-- `T` is `1`-equivariant. -/
theorem T_per (R : RefCoord d) (E : Work.FQC.EcalleData d) (ζ : ℂ) :
    T R E (ζ + 1) = T R E ζ + 1 := by
  have hN : ζ + (TN R ζ : ℂ) ∈ U R := TN_spec R ζ le_rfl
  have hcast : ζ + (TN R ζ : ℂ) + ((1 : ℕ) : ℂ) = ζ + 1 + (TN R ζ : ℂ) := by
    push_cast; ring
  have h1 : ζ + 1 + (TN R ζ : ℂ) ∈ U R := by
    have h := mem_U_add R hN 1
    rwa [hcast] at h
  rw [T_eq R E (ζ + 1) h1, T_eq R E ζ hN]
  have hshift : psi R E (ζ + 1 + (TN R ζ : ℂ)) = psi R E (ζ + (TN R ζ : ℂ)) + 1 := by
    have := psi_shift R E hN 1
    rw [hcast] at this
    simpa using this
  rw [hshift]
  ring

/-- `T` is injective. -/
theorem T_inj (R : RefCoord d) (E : Work.FQC.EcalleData d) : Function.Injective (T R E) := by
  intro ζ ζ' heq
  set K : ℕ := max (TN R ζ) (TN R ζ') with hK
  have h1 : ζ + (K : ℂ) ∈ U R := TN_spec R ζ (by rw [hK]; exact le_max_left _ _)
  have h2 : ζ' + (K : ℂ) ∈ U R := TN_spec R ζ' (by rw [hK]; exact le_max_right _ _)
  rw [T_eq R E ζ h1, T_eq R E ζ' h2] at heq
  have h3 : psi R E (ζ + (K : ℂ)) = psi R E (ζ' + (K : ℂ)) := by
    have := congrArg (fun u : ℂ => u + (K : ℂ)) heq
    simpa using this
  exact add_right_cancel (psi_injOn R E h1 h2 h3)

/-- `T` inverts the reference coordinate: `T (R.φ z) = φ̃ z`. -/
theorem T_phi (R : RefCoord d) (E : Work.FQC.EcalleData d) {z : ℂ} (hz : z ∈ R.P) :
    T R E (R.φ z) = phiTilde R E z := by
  have hmem : R.φ z ∈ U R := ⟨z, hz, rfl⟩
  have hU : R.φ z + (TN R (R.φ z) : ℂ) ∈ U R := TN_spec R (R.φ z) le_rfl
  rw [T_eq R E (R.φ z) hU]
  have hshift := psi_shift R E hmem (TN R (R.φ z))
  rw [hshift, psi_phi R E hz]
  ring

/-- `T` is entire. -/
theorem T_differentiable (R : RefCoord d) (E : Work.FQC.EcalleData d) :
    Differentiable ℂ (T R E) := by
  intro ζ
  set N := TN R ζ with hNdef
  have hU : ζ + (N : ℂ) ∈ U R := TN_spec R ζ le_rfl
  have hpsi : DifferentiableAt ℂ (psi R E) (ζ + (N : ℂ)) :=
    (psi_differentiableOn R E).differentiableAt ((isOpen_U R).mem_nhds hU)
  have hcomp : DifferentiableAt ℂ (fun ζ' => psi R E (ζ' + (N : ℂ)) - (N : ℂ)) ζ :=
    ((hpsi.comp ζ (differentiableAt_id.add_const (N : ℂ))).sub_const _)
  refine hcomp.congr_of_eventuallyEq ?_
  have hV : (fun ζ' => ζ' + (N : ℂ)) ⁻¹' U R ∈ 𝓝 ζ :=
    ((continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
      ((isOpen_U R).mem_nhds hU))
  filter_upwards [hV] with ζ' hζ'
  exact T_eq R E ζ' (n := N) hζ'

/-! ## 4. Cylinder rigidity applied to `T` -/

/-- **The extension `φ̃` differs from the reference coordinate by a constant.** -/
theorem exists_const (R : RefCoord d) (E : Work.FQC.EcalleData d) :
    ∃ s : ℂ, ∀ z ∈ R.P, phiTilde R E z = R.φ z + s := by
  obtain ⟨s, hs⟩ := cyl_rigid (T_differentiable R E) (T_inj R E) (T_per R E)
  exact ⟨s, fun z hz => by rw [← T_phi R E hz, hs (R.φ z)]⟩

end

end Work.FlowerGlue

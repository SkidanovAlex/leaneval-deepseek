/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/mixed_sub_Jeps.lean`

**The mixed slot of the mollifier difference.**  For a profile `f` which is `C^n` on the open
quadrant `Quad = (0,∞) × (0,π/2)` for every finite `n`, every admissible mollifier kernel `ρ`
(merely *continuous*: `IsMollKernel ρ`), every `ε > 0`, every `j i : ℕ` and every point
`(z,θ)` of the open quadrant,

  `D_z^j D_θ^i (J_ε f - f) = J_ε (D_z^j D_θ^i f) - D_z^j D_θ^i f`,

i.e. the mixed slot `D_z^jD_θ^i` of the mollifier *difference* is the difference of the slots.

Two ingredients:

* **`mixed_Jeps`** (`Submission/Work/FTS/StrongEps/mixed_Jeps.lean`): `J_ε` commutes with every
  `D_z^jD_θ^i` on the open quadrant (this needs no smoothness of the kernel `ρ`, only
  `IsMollKernel ρ`, because the derivatives are pushed onto the *profile* and the kernel is
  compactly supported);
* **slotwise subtraction.**  `D_z` and `D_θ` are `deriv`-based, so the subtraction identity for
  the iterated operators has to be proved level by level with `deriv_sub`, and therefore needs
  differentiability of the slices of `D_z^k (D_θ^i (J_ε f))` on `(0,∞)`, resp. of the
  `θ`-slices of `D_θ^m (J_ε f)` on `(0,π/2)`.

Those differentiability facts are free here, even for a merely *continuous* kernel: on the open
quadrant the iterates of `J_ε f` are *equal* to `J_ε` of the corresponding iterates of `f`
(`DthIter_mixed_Jeps`, `DzIter_Jeps_of_smooth`), and the slices of `J_ε g` are differentiable
with an explicit derivative for every `g` smooth on the quadrant
(`hasDerivAt_Jeps_slice_z`, `hasDerivAt_Jeps_slice_th`), both of which only differentiate
*under the integral* over the support of the kernel.  (`J_ε f` itself is *not* `C¹` for a merely
continuous `ρ`, so the `C^∞`-based subtraction `SmoothOpen.mixed_sub_open` does **not** apply.)

The three general subtraction lemmas are stated for arbitrary pairs of profiles with the
appropriate `DifferentiableOn` slice hypotheses, so that they apply to `(J_ε f, f)`; they are the
differentiability-based analogues of `Work.FTS.EllipticEst.SmoothOpen.mixed_sub_open`.

Everything here is `sorry`-free.  (The file opens the `Real` notation scope because the
statement writes the angle bound as `θ ∈ Set.Ioo 0 (π / 2)`: with `autoImplicit = false` in this
workspace a bare `π` is not an identifier, so `open scoped Real` is what makes it denote
`Real.pi` as intended — the same convention as `Work.FTS.StrongEps.mixed_add`.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.Dth_Jeps
import Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_z
import Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_th
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## Slotwise subtraction of the iterated operators -/

/-- **Slotwise subtraction of the iterated `D_z`-operator.**  If the `z`-slices of the iterates
`D_z^k A`, `D_z^k B` (at the fixed angle `θ`) are differentiable on `(0,∞)` for every `k ≤ j`,
then `D_z^j` is subtractive at `(z,θ)`.

(`D_z = z∂_z` is a `deriv`-based operator, so the induction has to produce the differentiability
of the slices from the hypotheses at each level; this is where the `DifferentiableOn` hypotheses
are used.) -/
theorem msj_DzIter_sub_of_diffOn :
    ∀ (j : ℕ) {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, 0 < z →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ) (Set.Ioi 0)) →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ) (Set.Ioi 0)) →
      Work.Spaces.DzIter j (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DzIter j A z θ - Work.Spaces.DzIter j B z θ
  | 0, _, _, _, _, _, _, _ => rfl
  | j + 1, A, B, z, θ, hz, hA, hB => by
    have hzmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
    have hA' : ∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ)
        (Set.Ioi 0) := fun k hk => hA k (le_trans hk (Nat.le_succ j))
    have hB' : ∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ)
        (Set.Ioi 0) := fun k hk => hB k (le_trans hk (Nat.le_succ j))
    have heq : (fun z' => Work.Spaces.DzIter j (fun z θ => A z θ - B z θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter j A z' θ - Work.Spaces.DzIter j B z' θ) := by
      filter_upwards [hzmem] with z' hz'
      exact msj_DzIter_sub_of_diffOn j hz' hA' hB'
    have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j A z' θ) z :=
      (hA' j le_rfl).differentiableAt hzmem
    have hdB : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j B z' θ) z :=
      (hB' j le_rfl).differentiableAt hzmem
    have hd : deriv (fun z' => Work.Spaces.DzIter j A z' θ - Work.Spaces.DzIter j B z' θ) z
        = deriv (fun z' => Work.Spaces.DzIter j A z' θ) z
          - deriv (fun z' => Work.Spaces.DzIter j B z' θ) z := deriv_sub hdA hdB
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [heq.deriv_eq, hd]
    ring

/-- **Slotwise subtraction of the iterated `D_θ`-operator.**  The `θ`-analogue of
`msj_DzIter_sub_of_diffOn`. -/
theorem msj_DthIter_sub_of_diffOn :
    ∀ (i : ℕ) {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, θ ∈ Set.Ioo 0 (π / 2) →
      (∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k A z θ')
        (Set.Ioo 0 (π / 2))) →
      (∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k B z θ')
        (Set.Ioo 0 (π / 2))) →
      Work.Spaces.DthIter i (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DthIter i A z θ - Work.Spaces.DthIter i B z θ
  | 0, _, _, _, _, _, _, _ => rfl
  | i + 1, A, B, z, θ, hθ, hA, hB => by
    have hθmem : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hA' : ∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k A z θ')
        (Set.Ioo 0 (π / 2)) := fun k hk => hA k (le_trans hk (Nat.le_succ i))
    have hB' : ∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k B z θ')
        (Set.Ioo 0 (π / 2)) := fun k hk => hB k (le_trans hk (Nat.le_succ i))
    have heq : (fun θ' => Work.Spaces.DthIter i (fun z θ => A z θ - B z θ) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter i A z θ' - Work.Spaces.DthIter i B z θ') := by
      filter_upwards [hθmem] with θ' hθ'
      exact msj_DthIter_sub_of_diffOn i hθ' hA' hB'
    have hdA : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter i A z θ') θ :=
      (hA' i le_rfl).differentiableAt hθmem
    have hdB : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter i B z θ') θ :=
      (hB' i le_rfl).differentiableAt hθmem
    have hd : deriv (fun θ' => Work.Spaces.DthIter i A z θ' - Work.Spaces.DthIter i B z θ') θ
        = deriv (fun θ' => Work.Spaces.DthIter i A z θ') θ
          - deriv (fun θ' => Work.Spaces.DthIter i B z θ') θ := deriv_sub hdA hdB
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq, hd]
    ring

/-- **Slotwise subtraction of the mixed operators `D_z^j D_θ^i`.**  Given the differentiability of
the `z`-slices of `D_z^k (D_θ^i ·)` (`k ≤ j`) and of the `θ`-slices of `D_θ^m ·` (`m ≤ i`) for
both profiles, the mixed slot of the difference is the difference of the mixed slots. -/
theorem msj_mixed_sub_of_diffOn (j i : ℕ) :
    ∀ {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      (∀ k ≤ j, DifferentiableOn ℝ
        (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i A) z' θ) (Set.Ioi 0)) →
      (∀ k ≤ j, DifferentiableOn ℝ
        (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i B) z' θ) (Set.Ioi 0)) →
      (∀ z' : ℝ, 0 < z' → ∀ m ≤ i, DifferentiableOn ℝ
        (fun θ' => Work.Spaces.DthIter m A z' θ') (Set.Ioo 0 (π / 2))) →
      (∀ z' : ℝ, 0 < z' → ∀ m ≤ i, DifferentiableOn ℝ
        (fun θ' => Work.Spaces.DthIter m B z' θ') (Set.Ioo 0 (π / 2))) →
      Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ := by
  intro A B z θ hz hθ hAz hBz hAθ hBθ
  have hsubθ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Spaces.DthIter i (fun z θ => A z θ - B z θ) z' θ'
        = Work.Spaces.DthIter i A z' θ' - Work.Spaces.DthIter i B z' θ' :=
    fun z' θ' hz' h1 h2 =>
      msj_DthIter_sub_of_diffOn i (A := A) (B := B) (z := z') (θ := θ') ⟨h1, h2⟩
        (fun m hm => hAθ z' hz' m hm) (fun m hm => hBθ z' hz' m hm)
  have hcongr := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => A z θ - B z θ))
    (G := fun z θ => Work.Spaces.DthIter i A z θ - Work.Spaces.DthIter i B z θ)
    hsubθ j z θ hz hθ.1 hθ.2
  have hadd := msj_DzIter_sub_of_diffOn j hz hAz hBz
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## The differentiability of the slots of `J_ε f` -/

/-- The `θ`-slices of the `D_θ`-iterates of `J_ε f` are differentiable, for `f` smooth on the
open quadrant and any admissible (merely continuous) kernel. -/
theorem msj_Jeps_slots_diffOn_theta (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    ∀ z : ℝ, 0 < z → ∀ m ≤ i,
      DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter m (Jeps ρ ε f) z θ')
        (Set.Ioo 0 (π / 2)) := by
  intro z hz m _
  intro θ' hθ'
  have hF : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := f) (fun n => hf n)
  have hev : (fun θ'' => Work.Spaces.DthIter m (Jeps ρ ε f) z θ'')
      =ᶠ[𝓝 θ'] (fun θ'' => Jeps ρ ε (Work.Spaces.DthIter m f) z θ'') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ'] with θ'' hθ''
    have hp : (z, θ'') ∈ Quad := ⟨hz, hθ''⟩
    exact DthIter_mixed_Jeps ρ hρ hε hf m hp
  have hd : DifferentiableAt ℝ (fun θ'' => Jeps ρ ε (Work.Spaces.DthIter m f) z θ'') θ' :=
    (hasDerivAt_Jeps_slice_th ρ hρ hε (fun n => (hF.DthIter m).forall n) hz hθ')
      |>.differentiableAt
  exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt

/-- The `z`-slices of the `D_z`-iterates of `D_θ^i (J_ε f)` are differentiable, for `f` smooth on
the open quadrant and any admissible (merely continuous) kernel. -/
theorem msj_Jeps_slots_diffOn_z (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    ∀ k ≤ j, DifferentiableOn ℝ
      (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i (Jeps ρ ε f)) z' θ)
      (Set.Ioi 0) := by
  intro k _
  intro z' hz'
  have hF : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := f) (fun n => hf n)
  have hev : (fun z'' => Work.Spaces.DzIter k (Work.Spaces.DthIter i (Jeps ρ ε f)) z'' θ)
      =ᶠ[𝓝 z'] (fun z'' => Jeps ρ ε (Work.Spaces.mixed k i f) z'' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
    have hp : (z'', θ) ∈ Quad := ⟨hz'', hθ⟩
    exact (Work.FTS.TransportS.DzIter_congrOn isOpen_Quad
        (DthIter_mixed_Jeps ρ hρ hε hf i) k hp).trans
      (DzIter_Jeps_of_smooth ρ hρ hε ((smQ_of_forall_nat hf).DthIter i) k hp)
  have hd : DifferentiableAt ℝ (fun z'' => Jeps ρ ε (Work.Spaces.mixed k i f) z'' θ) z' :=
    (hasDerivAt_Jeps_slice_z ρ hρ hε (fun n => (hF.mixed k i).forall n) hz' hθ)
      |>.differentiableAt
  exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt

/-! ## The target -/

theorem mixed_sub_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i f) z θ
        - Work.Spaces.mixed j i f z θ := by
  have hF : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := f) (fun n => hf n)
  -- the slotwise subtraction `D_z^jD_θ^i (J_ε f - f) = D_z^jD_θ^i (J_ε f) - D_z^jD_θ^i f`
  have hAz := msj_Jeps_slots_diffOn_z ρ hρ hε hf hz hθ j i
  have hBz : ∀ k ≤ j, DifferentiableOn ℝ
      (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i f) z' θ) (Set.Ioi 0) :=
    fun k _ => ((hF.mixed k i).curry_z hθ).differentiableOn (by simp [Work.Stability.smoothOrder])
  have hAθ := msj_Jeps_slots_diffOn_theta ρ hρ hε hf i
  have hBθ : ∀ z' : ℝ, 0 < z' → ∀ m ≤ i, DifferentiableOn ℝ
      (fun θ' => Work.Spaces.DthIter m f z' θ') (Set.Ioo 0 (π / 2)) :=
    fun z' hz' m _ =>
      ((hF.DthIter m).curry_θ hz').differentiableOn (by simp [Work.Stability.smoothOrder])
  have hsub := msj_mixed_sub_of_diffOn j i (A := Jeps ρ ε f) (B := f) hz hθ hAz hBz hAθ hBθ
  -- and the commutativity `D_z^jD_θ^i (J_ε f) = J_ε (D_z^jD_θ^i f)`
  have hA := mixed_Jeps ρ hρ hε hf hz hθ j i
  rw [hsub, hA]

end Work.FTS.StrongEps.DiffAux

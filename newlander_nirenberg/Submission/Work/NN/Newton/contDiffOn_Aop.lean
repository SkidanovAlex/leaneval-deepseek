import Mathlib
import Submission.Work.NN.Newton.pushforward_setup

/-!
# Smoothness of the pushed-forward perturbation `Aop A v`

This file proves `Work.NN.Newton.contDiffOn_Aop`: if the perturbation `A` and every component
`v l` of the correction are `C^m` on the polydisc `Pd n R` for every `m`, and if the endomorphism
`1 - DvCLM v z` is invertible for every `z ∈ Pd n R`, then the pushed-forward perturbation

`Aop A v z = Bop A v z ∘ (1 - DvCLM v z)⁻¹`

is `C^m` on `Pd n R` for every `m`.

The proof splits into three independent smoothness statements:

* `contDiffOn_Aop_dvclm`: `z ↦ DvCLM v z` is `C^m` for every `m` (one order is spent on
  `fderiv` and the componentwise derivatives are reassembled with `ContinuousLinearMap.piEquivL`);
* `contDiffOn_Aop_ringinv`: on a set where every value of `1 - A z` is a unit of the Banach
  algebra `X →L[ℝ] X`, the map `z ↦ Ring.inverse (1 - A z)` is `C^m` for every `m` (this is the
  analyticity of inversion at a unit, `contDiffAt_ringInverse`);
* `contDiffOn_Aop_bop`: the defect `Bop A v z` is a difference of products of the smooth families
  `z ↦ 1 - DvCLM v z`, `z ↦ Jstd z + A z` and the constant family `z ↦ Jstd z`, hence smooth.

The target is then the product `Bop A v · * Minv v ·` in the Banach algebra of endomorphisms
of `ℂⁿ` (multiplication there *is* composition).
-/

noncomputable section

open scoped ContDiff
open Set

namespace Work.NN.Newton

/-- If every component `v l` is `C^m` on the polydisc for every `m`, then so is the
componentwise derivative `DvCLM v`. -/
lemma contDiffOn_Aop_dvclm {n : ℕ} {R : ℝ} {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l : Fin n, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n R)) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.NN.Newton.DvCLM v) (Work.NN.Newton.Pd n R) := by
  intro m
  -- each component has a `C^m` derivative on the (open) polydisc
  have h1 : ∀ l : Fin n, ContDiffOn ℝ m (fun z => fderiv ℝ (v l) z) (Work.NN.Newton.Pd n R) :=
    fun l => (hv l (m + 1)).fderiv_of_isOpen (Work.NN.Newton.isOpen_Pd n R) (by norm_num)
  -- hence the whole family, as a map into the product of the dual spaces
  have h2 : ContDiffOn ℝ m (fun z : Work.NN.Core.Cn n => fun l => fderiv ℝ (v l) z)
      (Work.NN.Newton.Pd n R) := contDiffOn_pi.2 h1
  -- and the product of dual spaces is identified with the dual of `ℂⁿ`
  have h3 : ContDiffOn ℝ m
      (fun z => ContinuousLinearMap.piEquivL ℝ (Work.NN.Core.Cn n) (fun _ : Fin n => ℂ)
        (fun l => fderiv ℝ (v l) z)) (Work.NN.Newton.Pd n R) :=
    (ContinuousLinearMap.piEquivL ℝ (Work.NN.Core.Cn n) (fun _ : Fin n => ℂ)).contDiff.comp_contDiffOn
      h2
  refine h3.congr ?_
  intro z _
  rw [Work.NN.Newton.DvCLM]
  rfl

/-- Inversion composed with `1 - A ·` is `C^m` wherever `1 - A z` is a unit of the Banach
algebra `X →L[ℝ] X`. -/
lemma contDiffOn_Aop_ringinv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {P : Set X} {A : X → (X →L[ℝ] X)}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A P)
    (hunit : ∀ z ∈ P, IsUnit ((1 : X →L[ℝ] X) - A z)) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun z => Ring.inverse ((1 : X →L[ℝ] X) - A z)) P := by
  intro m z hz
  -- inversion is `C^m` at a unit
  have hInvc : ContDiffAt ℝ m Ring.inverse ((1 : X →L[ℝ] X) - A z) := by
    obtain ⟨u, hu⟩ := hunit z hz
    have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) u
    rw [hu] at h
    exact h
  have hB : ContDiffWithinAt ℝ m (fun y => (1 : X →L[ℝ] X) - A y) P z :=
    contDiffWithinAt_const.sub (hA m z hz)
  exact (hInvc.contDiffWithinAt).comp z hB (fun y _ => mem_univ _)

/-- The defect `Bop A v` is smooth of every order on the polydisc. -/
lemma contDiffOn_Aop_bop {n : ℕ} {R : ℝ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Newton.Pd n R))
    (hDv : ∀ m : ℕ, ContDiffOn ℝ m (Work.NN.Newton.DvCLM v) (Work.NN.Newton.Pd n R)) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun z => Work.NN.Newton.Bop A v z) (Work.NN.Newton.Pd n R) := by
  intro m
  -- the standard structure is a constant family
  have hJc : ContDiffOn ℝ m (fun z : Work.NN.Core.Cn n => Work.NN.Core.JstdCn n z)
      (Work.NN.Newton.Pd n R) := by
    refine (contDiffOn_const (c := Work.NN.Core.JstdCn n (0 : Work.NN.Core.Cn n)) :
      ContDiffOn ℝ m (fun _ : Work.NN.Core.Cn n => Work.NN.Core.JstdCn n (0 : Work.NN.Core.Cn n))
        (Work.NN.Newton.Pd n R)).congr ?_
    intro z _
    rfl
  -- `(1 - DvCLM v ·) ∘ (Jstd + A ·)`
  have h1 : ContDiffOn ℝ m (fun z => ((1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
      - Work.NN.Newton.DvCLM v z) * (Work.NN.Core.JstdCn n z + A z)) (Work.NN.Newton.Pd n R) :=
    (contDiffOn_const.sub (hDv m)).mul (hJc.add (hA m))
  -- `Jstd ∘ (1 - DvCLM v ·)`
  have h2 : ContDiffOn ℝ m (fun z => Work.NN.Core.JstdCn n z
      * ((1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) - Work.NN.Newton.DvCLM v z))
      (Work.NN.Newton.Pd n R) :=
    hJc.mul (contDiffOn_const.sub (hDv m))
  exact (h1.sub h2).congr (fun z _ => rfl)

theorem contDiffOn_Aop {n : ℕ} {R : ℝ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Work.NN.Newton.Pd n R))
    (hv : ∀ l : Fin n, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n R))
    (hunit : ∀ z ∈ Work.NN.Newton.Pd n R, IsUnit (1 - Work.NN.Newton.DvCLM v z)) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun z => Work.NN.Newton.Aop A v z) (Work.NN.Newton.Pd n R) := by
  intro m
  have hDv : ∀ m : ℕ, ContDiffOn ℝ m (Work.NN.Newton.DvCLM v) (Work.NN.Newton.Pd n R) :=
    contDiffOn_Aop_dvclm hv
  have hBop : ContDiffOn ℝ m (fun z => Work.NN.Newton.Bop A v z) (Work.NN.Newton.Pd n R) :=
    contDiffOn_Aop_bop hA hDv m
  have hMinv : ContDiffOn ℝ m (fun z => Work.NN.Newton.Minv v z) (Work.NN.Newton.Pd n R) := by
    have h := contDiffOn_Aop_ringinv (P := Work.NN.Newton.Pd n R) (A := Work.NN.Newton.DvCLM v)
      hDv hunit m
    exact h.congr (fun z _ => rfl)
  -- `Aop A v z = Bop A v z * Minv v z` in the Banach algebra of endomorphisms of `ℂⁿ`
  exact (hBop.mul hMinv).congr (fun z _ => rfl)

end Work.NN.Newton

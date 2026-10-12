import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two-coordinate peel of the centred-box integral

`lintegral_pair_abox` computes the `lintegral` over the `n`-particle centred box of a function
that sees only the slots `i ≠ j`: it factors as the one-particle cube volume raised to the power
`n - 2`, times the double integral over the centred cube.

The route (all of it explicit here, no input beyond `Mathlib` and the corpus definitions in
`CentreBox`/`Potential`):

* `lintegral_pi_coord_aux` — one-coordinate peel of `Measure.pi`: the `i`-th marginal of a
  product measure integrates `G (x i)` against `(ν univ)^m * ∫⁻ G dν`.  Proof:
  `MeasureTheory.measurePreserving_piFinSuccAbove` + `lintegral_prod_symm` + `lintegral_const`
  + `Measure.pi_univ`.
* `lintegral_pi_pair_aux` — two-coordinate peel: peel the slot `i`, Tonelli, then apply the
  one-coordinate peel to the remaining slot `j'` with `i.succAbove j' = j`.
* `quasiMeasurePreserving_pair_eval_aux` — the pair-evaluation map `x ↦ (x i, x j)` is
  quasi-measure-preserving `π ν → ν.prod ν`; this is what transports the a.e.-hypothesis about
  `φ` (which speaks about `volume.prod volume`) to the box.
* assembly: replace `φ` by its measurable hull, apply the peel, and transport the two one-body
  integrals along `μ.prod μ ≤ volume.prod volume`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB2.Pot

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **One-coordinate peel.**  Integrating a function of a single coordinate of a product measure
gives the total mass to the power of the number of the remaining coordinates times the
one-particle integral. -/
theorem lintegral_pi_coord_aux {m : ℕ} {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [SigmaFinite ν] (i : Fin (m + 1)) {G : α → ENNReal} (hG : Measurable G) :
    (∫⁻ x : Fin (m + 1) → α, G (x i) ∂(Measure.pi (fun _ : Fin (m + 1) => ν)))
      = (ν Set.univ) ^ m * (∫⁻ a, G a ∂ν) := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i)
      (Measure.pi (fun _ : Fin (m + 1) => ν)) (ν.prod (Measure.pi (fun _ : Fin m => ν))) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (m + 1) => ν) i
  have hF : Measurable (fun q : α × (Fin m → α) => G q.1) := hG.comp measurable_fst
  have hstep : (∫⁻ x : Fin (m + 1) → α, G (x i) ∂(Measure.pi (fun _ : Fin (m + 1) => ν)))
      = ∫⁻ q : α × (Fin m → α), G q.1 ∂(ν.prod (Measure.pi (fun _ : Fin m => ν))) :=
    hmp.lintegral_comp hF
  rw [hstep, lintegral_prod_symm (f := fun q : α × (Fin m → α) => G q.1) hF.aemeasurable]
  simp only [lintegral_const]
  rw [Measure.pi_univ, Finset.prod_const, Finset.card_fin, mul_comm]

/-- **Two-coordinate peel.**  A function of two distinct coordinates of a product measure
integrates to the total mass of the remaining coordinates times the double integral. -/
theorem lintegral_pi_pair_aux {m : ℕ} {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [SigmaFinite ν] (i j : Fin (m + 2)) (hij : i ≠ j) {H : α → α → ENNReal}
    (hH : Measurable (Function.uncurry H)) :
    (∫⁻ x : Fin (m + 2) → α, H (x i) (x j) ∂(Measure.pi (fun _ : Fin (m + 2) => ν)))
      = (ν Set.univ) ^ m * (∫⁻ a, ∫⁻ b, H a b ∂ν ∂ν) := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  have hmp1 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => α) i)
      (Measure.pi (fun _ : Fin (m + 2) => ν))
      (ν.prod (Measure.pi (fun _ : Fin (m + 1) => ν))) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (m + 2) => ν) i
  have hG1 : Measurable (fun q : α × (Fin (m + 1) → α) => H q.1 (q.2 j')) := by fun_prop
  have h1 : (∫⁻ x : Fin (m + 2) → α, H (x i) (x (i.succAbove j'))
        ∂(Measure.pi (fun _ : Fin (m + 2) => ν)))
      = ∫⁻ q : α × (Fin (m + 1) → α), H q.1 (q.2 j')
          ∂(ν.prod (Measure.pi (fun _ : Fin (m + 1) => ν))) :=
    hmp1.lintegral_comp hG1
  rw [hj'] at h1
  rw [h1, lintegral_prod (f := fun q : α × (Fin (m + 1) → α) => H q.1 (q.2 j'))
      hG1.aemeasurable]
  have hQ : ∀ a : α, (∫⁻ y : Fin (m + 1) → α, H a (y j')
        ∂(Measure.pi (fun _ : Fin (m + 1) => ν))) = (ν Set.univ) ^ m * ∫⁻ b, H a b ∂ν := by
    intro a
    have hGa : Measurable (fun c : α => H a c) := by fun_prop
    exact lintegral_pi_coord_aux ν j' hGa
  simp only [hQ]
  rw [lintegral_const_mul _ (hH.lintegral_prod_right : Measurable (fun a => ∫⁻ b, H a b ∂ν))]

/-- If `i ≠ j` then `n ≥ 2`. -/
lemma two_le_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) : 2 ≤ n := by
  by_contra h
  refine hij (Fin.ext ?_)
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  omega

/-- **Two distinct coordinates of a product measure.**  The map `x ↦ (x i, x j)` pushes
`Measure.pi (fun _ => ν)` to an absolutely continuous measure w.r.t. `ν.prod ν`. -/
theorem quasiMeasurePreserving_pair_eval_aux {n : ℕ} {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SigmaFinite ν] {i j : Fin n} (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : Fin n → α => (x i, x j))
      (Measure.pi (fun _ : Fin n => ν)) (ν.prod ν) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := two_le_of_ne hij; omega⟩
  refine ⟨?_, ?_⟩
  · fun_prop
  · refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hs0
    have he : Measurable (fun x : Fin (m + 2) → α => (x i, x j)) := by fun_prop
    rw [Measure.map_apply he hs]
    set H : α → α → ENNReal := fun a b => s.indicator (1 : α × α → ENNReal) (a, b)
      with hHdef
    have hHall : Function.uncurry H = s.indicator (1 : α × α → ENNReal) := by
      rw [hHdef]; funext p; rfl
    have hHmeas : Measurable (Function.uncurry H) := by
      rw [hHall]; exact Measurable.indicator measurable_const hs
    have hpre : MeasurableSet ((fun x : Fin (m + 2) → α => (x i, x j)) ⁻¹' s) := he hs
    have hkey : (Measure.pi (fun _ : Fin (m + 2) => ν))
          ((fun x : Fin (m + 2) → α => (x i, x j)) ⁻¹' s)
        = ∫⁻ x : Fin (m + 2) → α, H (x i) (x j) ∂(Measure.pi (fun _ : Fin (m + 2) => ν)) := by
      rw [← lintegral_indicator_one hpre]
      apply lintegral_congr
      intro x
      by_cases hx : (x i, x j) ∈ s
      · simp [hHdef, Set.indicator_of_mem hx,
          Set.indicator_of_mem (show x ∈ (fun x : Fin (m + 2) → α => (x i, x j)) ⁻¹' s from hx)]
      · simp [hHdef, Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show x ∉ (fun x : Fin (m + 2) → α => (x i, x j)) ⁻¹' s from hx)]
    have hprod : (∫⁻ a, ∫⁻ b, H a b ∂ν ∂ν) = (ν.prod ν) s := by
      have h2 : (∫⁻ p : α × α, Function.uncurry H p ∂(ν.prod ν)) = (ν.prod ν) s := by
        simpa [hHall] using lintegral_indicator_one (μ := ν.prod ν) hs
      rw [lintegral_prod (f := Function.uncurry H) hHmeas.aemeasurable] at h2
      simpa [Function.uncurry] using h2
    rw [hkey, lintegral_pi_pair_aux ν i j hij hHmeas, hprod, hs0, mul_zero]

/-- **Two-coordinate peel of the centred box integral.** -/
theorem lintegral_pair_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ENNReal}
    (hφ : MeasureTheory.AEStronglyMeasurable (Function.uncurry φ)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) :
    (∫⁻ x : Submission.BoseGases.X n, φ (x i) (x j)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
      = ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.acube ℓ)) ^ (n - 2)
        * (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3), φ a b
            ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))
            ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := two_le_of_ne hij; omega⟩
  set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hν
  set ν₀ : Measure (E3 × E3) := (volume : Measure E3).prod (volume : Measure E3) with hν₀
  have hbox : (volume : Measure (Fin (k + 2) → E3)).restrict
        (Submission.BoseGases.abox (k + 2) ℓ)
      = Measure.pi (fun _ : Fin (k + 2) => ν) := by
    rw [hν]; exact Submission.BoseGases.restrict_abox_eq_pi (k + 2) ℓ
  rw [hbox]
  have hA : AEMeasurable (Function.uncurry φ) ν₀ := by rw [hν₀]; exact hφ.aemeasurable
  set G : E3 × E3 → ENNReal := AEMeasurable.mk (Function.uncurry φ) hA with hGdef
  have hGmeas : Measurable G := by rw [hGdef]; exact hA.measurable_mk
  have hGeq : Function.uncurry φ =ᵐ[ν₀] G := by rw [hGdef]; exact hA.ae_eq_mk
  have hle : ν.prod ν ≤ ν₀ := by
    rw [hν₀, hν]
    exact Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Fin (k + 2) → E3 => (x i, x j))
      (Measure.pi (fun _ : Fin (k + 2) => ν)) ν₀ :=
    (quasiMeasurePreserving_pair_eval_aux ν hij).mono_right
      (Measure.absolutelyContinuous_of_le hle)
  have hae : (fun x : Fin (k + 2) → E3 => φ (x i) (x j))
      =ᵐ[Measure.pi (fun _ : Fin (k + 2) => ν)] (fun x => G (x i, x j)) := by
    have h := hqmp.ae_eq hGeq
    filter_upwards [h] with x hx
    simpa [Function.uncurry] using hx
  rw [lintegral_congr_ae hae,
    lintegral_pi_pair_aux ν i j hij (H := fun a b => G (a, b)) hGmeas]
  have hR : (∫⁻ a : E3, ∫⁻ b : E3, G (a, b) ∂ν ∂ν)
      = (∫⁻ a : E3, ∫⁻ b : E3, φ a b ∂ν ∂ν) := by
    have h₂ : Function.uncurry φ =ᵐ[ν.prod ν] G :=
      (Measure.absolutelyContinuous_of_le hle).ae_eq hGeq
    have h₃ := Measure.ae_ae_eq_of_ae_eq_uncurry (f := φ) (g := fun a b => G (a, b)) h₂
    apply lintegral_congr_ae
    filter_upwards [h₃] with a ha
    exact (lintegral_congr_ae ha).symm
  rw [hR, hν, Measure.restrict_apply_univ, Nat.add_sub_cancel]

end Work.BoseFixB2.Pot

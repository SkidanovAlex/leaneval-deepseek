import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.theta_window
import Submission.Work.BoseDict.boxRealise_dGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.BombNExcDefs` — the model-side vocabulary of the `nExc` row

The target `Work.BoseBoxFock.bomb_nExc_eq_cnPlusC` pairs the model's excited number operator
`nExc = totNumOp m − n₀` with the box's excited count `cnPlusC`.  The bridge is the
second-quantisation dictionary `Work.BoseDict.bomb_dGamma_slot`:

    `bomb Ψ (dGamma T Ψ) = re (cIPn d Θ (boxSlotSum e T Θ))`,   `Θ = boxRealise e d Ψ`,

so the whole row is the single model-side identity

    `nExc = dGamma m (boxT0 m)`,   `boxT0 := 1 − |e_vec 0⟩⟨e_vec 0|`

(then `boxSlotSum e boxT0 Θ = boxSlotSum e 1 Θ − Σ_j boxSlotOf e e₀ e₀ j Θ`, and the box side
takes over).  This file supplies the vocabulary and that identity, so that the box-side lemmas
about `boxSlotSum`/`boxSlotOf` can be stated without any model-side content.

Everything here is elementary finite-dimensional algebra on the multi-index model
`RealFock m = (Fin m →₀ ℕ) →₀ ℝ`; nothing is delegated and nothing is left open.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. `dGamma` is linear in the one-particle operator -/

/-- `dGamma` respects subtraction in the one-particle operator (immediate from the defining
double sum `dGamma T = ∑_{ij} (T e_j)_i • a_i† a_j`). -/
theorem dGamma_sub {m : ℕ} (T1 T2 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    dGamma m (T1 - T2) = dGamma m T1 - dGamma m T2 := by
  have h1 : ∀ (i j : Fin m), (T1 - T2) (evec m j) i • (cre m i).comp (ann m j)
      = T1 (evec m j) i • (cre m i).comp (ann m j)
        - T2 (evec m j) i • (cre m i).comp (ann m j) := by
    intro i j
    rw [LinearMap.sub_apply, Pi.sub_apply]
    exact sub_smul (T1 (evec m j) i) (T2 (evec m j) i) ((cre m i).comp (ann m j))
  have hinner : ∀ i : Fin m,
      (∑ j : Fin m, (T1 - T2) (evec m j) i • (cre m i).comp (ann m j))
        = (∑ j : Fin m, T1 (evec m j) i • (cre m i).comp (ann m j))
          - (∑ j : Fin m, T2 (evec m j) i • (cre m i).comp (ann m j)) := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => h1 i j)]
    exact Finset.sum_sub_distrib (s := Finset.univ)
      (fun j => T1 (evec m j) i • (cre m i).comp (ann m j))
      (fun j => T2 (evec m j) i • (cre m i).comp (ann m j))
  simp only [dGamma, hinner]
  exact Finset.sum_sub_distrib (s := Finset.univ)
      (fun i => ∑ j : Fin m, T1 (evec m j) i • (cre m i).comp (ann m j))
      (fun i => ∑ j : Fin m, T2 (evec m j) i • (cre m i).comp (ann m j))

/-- The second quantisation of the rank-one operator `|e_l⟩⟨e_l|` (`v ↦ (v l) • e_l`) is the
mode number operator `a_l† a_l`. -/
theorem dGamma_rankOne {m : ℕ} [NeZero m] (l : Fin m) :
    dGamma m (LinearMap.smulRight (LinearMap.proj l : (Fin m → ℝ) →ₗ[ℝ] ℝ) (evec m l))
      = modeNumOp m l := by
  have hval : ∀ j : Fin m,
      (LinearMap.smulRight (LinearMap.proj l : (Fin m → ℝ) →ₗ[ℝ] ℝ) (evec m l)) (evec m j)
        = (if j = l then (1 : ℝ) else 0) • evec m l := by
    intro j
    rw [LinearMap.smulRight_apply, LinearMap.proj_apply, evec, Pi.single_apply]
    by_cases h : l = j
    · subst h; simp
    · have h' : ¬ (j = l) := fun hh => h hh.symm
      simp [h, h']
  simp only [dGamma, hval]
  have hstep : ∀ (i j : Fin m),
      ((if j = l then (1 : ℝ) else 0) • evec m l) i • (cre m i).comp (ann m j)
        = (if j = l then (evec m l i) else 0) • (cre m i).comp (ann m j) := by
    intro i j
    rw [Pi.smul_apply]
    by_cases h : j = l <;> simp [h]
  have hstep2 : ∀ (i j : Fin m),
      (if j = l then (evec m l i) else 0) • (cre m i).comp (ann m j)
        = if j = l then (evec m l i) • (cre m i).comp (ann m j) else 0 := by
    intro i j
    by_cases h : j = l <;> simp [h]
  simp only [hstep, hstep2, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have hstep3 : ∀ i : Fin m,
      (evec m l i) • (cre m i).comp (ann m l)
        = if i = l then (cre m i).comp (ann m l) else 0 := by
    intro i
    rw [evec, Pi.single_apply]
    by_cases h : i = l <;> simp [h]
  simp only [hstep3]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rfl

/-! ## 2. The operator `boxT0 = 1 − |e₀⟩⟨e₀|` and `nExc = dGamma boxT0` -/

/-- The one-particle operator whose second quantisation is the excited number of the model:
`boxT0 = 1 − |e_vec 0⟩⟨e_vec 0|`, i.e. `v ↦ v − (v 0) • e_vec 0`. -/
noncomputable def boxT0 (m : ℕ) [NeZero m] : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  1 - LinearMap.smulRight (LinearMap.proj (0 : Fin m)) (evec m 0)

/-- The defining value of `boxT0`. -/
theorem boxT0_apply (m : ℕ) [NeZero m] (v : Fin m → ℝ) :
    boxT0 m v = v - (v 0) • evec m 0 := rfl

/-- The matrix elements of `boxT0` at the coordinate vectors. -/
theorem boxT0_evec (m : ℕ) [NeZero m] (j i : Fin m) :
    boxT0 m (evec m j) i
      = (if i = j then (1 : ℝ) else 0)
        - (if j = 0 then (1 : ℝ) else 0) * (if i = 0 then (1 : ℝ) else 0) := by
  rw [boxT0_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, evec, Pi.single_apply]
  by_cases hj : j = 0 <;> by_cases hi : i = 0 <;> simp [hj, hi, eq_comm]

/-- **The model identity of the `nExc` row**: the excited number operator `nExc = N − n₀` of the
model is the second quantisation of `boxT0 = 1 − |e₀⟩⟨e₀|`. -/
theorem nExc_eq_dGamma_boxT0 {m : ℕ} [NeZero m] :
    nExc = dGamma m (boxT0 m) := by
  have h : boxT0 m
      = (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
        - LinearMap.smulRight (LinearMap.proj (0 : Fin m) : (Fin m → ℝ) →ₗ[ℝ] ℝ) (evec m 0) :=
    rfl
  rw [h, dGamma_sub, DGamma_one, dGamma_rankOne]
  rfl

/-! ## 3. `totNumOp` on the degree-`d` part -/

/-- The degree of a multi-index, as a real number, is the sum of its components. -/
theorem cast_sum_eq_sum_cast {m : ℕ} (α : Fin m →₀ ℕ) :
    ((α.sum (fun _ k => k) : ℕ) : ℝ) = ∑ i : Fin m, ((α i : ℕ) : ℝ) := by
  rw [Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
  rw [Finsupp.notMem_support_iff.mp hx, Nat.cast_zero]

/-- **`totNumOp` acts by the degree on the degree-`d` part** of the Fock space. -/
theorem totNumOp_eq_deg {m d : ℕ} (Ψ : RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    totNumOp m Ψ = (d : ℝ) • Ψ := by
  have hexp : Ψ = ∑ α ∈ Ψ.support, Ψ α • Finsupp.single α (1 : ℝ) := by
    conv_lhs => rw [← Finsupp.sum_single Ψ]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun α _ => by rw [Finsupp.smul_single]; simp
  conv_lhs => rw [hexp]
  conv_rhs => rw [hexp, Finset.smul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [map_smul, totNumOp_single, ← cast_sum_eq_sum_cast, hΨ α hα, smul_smul, smul_smul, mul_comm]

/-! ## 4. The box image of the identity operator: `boxSlotSum e 1 Θ = d • Θ`

`boxRealise` is the dictionary's isometry (`Work.BoseDict.boxRealise_dGamma`), so
`boxSlotSum e 1 Θ = boxRealise e d (dGamma m 1 Ψ) = boxRealise e d (totNumOp m Ψ)`, and since
`Ψ` sits in the degree-`d` sector, `totNumOp m Ψ = d • Ψ` and the claim follows from the
`ℝ`-linearity of `boxRealise`.  This is the step that replaces the (unproved in this file)
slot-wise resolution of the identity `Σ_l boxSlotOf e e_l e_l j Θ = Θ` by the single
degree identity. -/
theorem boxSlotSum_one_eq_smul {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp,
      (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : RealFock m) (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    Work.BoseDict.boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
        (Work.BoseDict.boxRealise e d Ψ)
      = (d : ℝ) • Work.BoseDict.boxRealise e d Ψ := by
  rw [← Work.BoseDict.boxRealise_dGamma he hbdd hsupp
      (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Ψ hΨ, DGamma_one,
    totNumOp_eq_deg Ψ hΨ, map_smul]

end Work.BoseBoxFock

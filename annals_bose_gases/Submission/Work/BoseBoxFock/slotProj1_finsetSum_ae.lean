import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FibreProjDefs
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## The singleton identification `slotProj1 e i = slotProj e {i}`

`slotInt e S Φ x = ∫ z : ↑S → Ω, (∏ i ∈ S, PV e (x i) (z i)) · Φ (x[S ↦ z])` is an integral
over the *function space* `↑S → Ω`, while `slotProj1 e i Φ x = ∫ w : Ω, PV e (x i) w ·
Φ (update x i w)` integrates directly over `Ω`.  For the singleton `S = {i}` the two are related
by the measure preserving equivalence `MeasurableEquiv.funUnique ↑{i} Ω` (a function on a
subsingleton index type is its value at the unique index), which is the content of
`slotProj_singleton_eq_slotProj1'`.  Since `MeasurePreserving.integral_comp'` holds for *every*
integrand, no hypothesis on the modes or on the state is needed.
-/

/-- Overwriting the singleton slot `{i}` with the constant fibre `fun _ ↦ w` is the update of the
slot `i` by `w`. -/
theorem updateFinset_singleton_eq_update_aux {n : ℕ} (i : Fin n) (x : Fin n → Ω) (w : Ω) :
    Function.updateFinset x ({i} : Finset (Fin n))
      (fun _ : ↥({i} : Finset (Fin n)) => w) = Function.update x i w := by
  funext j
  rw [Function.updateFinset_def, Function.update_apply]
  simp only [Finset.mem_singleton]
  by_cases hj : j = i <;> simp [hj]

/-- **`slotProj1 e i` is the slot projection at the singleton slot set `{i}`**, for an arbitrary
state: the two integrals differ by the measure preserving change of variables
`MeasurableEquiv.funUnique ↥{i} Ω`. -/
theorem slotProj_singleton_eq_slotProj1_aux {m n : ℕ} (e : Fin m → Ω → ℂ) (i : Fin n)
    (Φ : (Fin n → Ω) → ℂ) :
    slotProj e ({i} : Finset (Fin n)) Φ = slotProj1 e i Φ := by
  funext x
  rw [slotProj_eq_slotInt, slotInt, slotProj1]
  rw [← (volume_preserving_funUnique (↥({i} : Finset (Fin n))) Ω).integral_comp'
      (f := MeasurableEquiv.funUnique (↥({i} : Finset (Fin n))) Ω)
      (fun w : Ω => PV e (x i) w * Φ (Function.update x i w))]
  apply integral_congr_ae
  filter_upwards with z
  set φ := MeasurableEquiv.funUnique (↥({i} : Finset (Fin n))) Ω with hφ
  have hzj : ∀ j : ↥({i} : Finset (Fin n)), z j = φ z := by
    intro j
    rw [hφ, MeasurableEquiv.funUnique_apply, Unique.eq_default j]
  have hz' : z = fun _ => φ z := funext hzj
  have hprod : (∏ j : ↥({i} : Finset (Fin n)), PV e (x j.1) (z j)) = PV e (x i) (φ z) := by
    rw [Fintype.prod_subsingleton (fun j : ↥({i} : Finset (Fin n)) => PV e (x j.1) (z j))
      (default : ↥({i} : Finset (Fin n)))]
    rw [hzj default]
    rfl
  have hupd : Function.updateFinset x ({i} : Finset (Fin n)) z
      = Function.update x i (φ z) := by
    have h1 : Function.updateFinset x ({i} : Finset (Fin n)) z
        = Function.updateFinset x ({i} : Finset (Fin n)) (fun _ => φ z) :=
      congrArg (fun z' : ↥({i} : Finset (Fin n)) → Ω =>
        Function.updateFinset x ({i} : Finset (Fin n)) z') hz'
    rw [h1, updateFinset_singleton_eq_update_aux]
  rw [hprod, hupd]

theorem slotProj1_finsetSum_ae {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (i : Fin n) {ι : Type*} (s : Finset ι)
    {Θ : ι → (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘ : ∀ k ∈ s, MeasureTheory.MemLp (Θ k) ⊤) :
    (fun x => Work.BoseBoxFock.slotProj1 e i (fun y => ∑ k ∈ s, Θ k y) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
            (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ k ∈ s, Work.BoseBoxFock.slotProj1 e i (Θ k) x) := by
  have h := slotProj_finsetSum_ae (ℓ := ℓ) (e := e) hbdd hsupp
    ({i} : Finset (Fin n)) s hΘ
  have h1 : (fun x => Work.BoseBoxFock.slotProj1 e i (fun y => ∑ k ∈ s, Θ k y) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
            (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => slotProj e ({i} : Finset (Fin n)) (fun y => ∑ k ∈ s, Θ k y) x) :=
    Filter.Eventually.of_forall
      (fun x => (congrFun (slotProj_singleton_eq_slotProj1_aux e i _) x).symm)
  have h2 : (fun x => ∑ k ∈ s, slotProj e ({i} : Finset (Fin n)) (Θ k) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
            (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ k ∈ s, slotProj1 e i (Θ k) x) :=
    Filter.Eventually.of_forall
      (fun x => Finset.sum_congr rfl (fun k _ =>
        congrFun (slotProj_singleton_eq_slotProj1_aux e i (Θ k)) x))
  exact h1.trans (h.trans h2)

end Work.BoseBoxFock

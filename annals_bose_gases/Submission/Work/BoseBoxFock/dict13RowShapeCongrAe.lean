import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13RowShapeCongrAe` — the row shape depends only on the a.e. class of `e`

`Work.BoseBoxFock.rowShape13 Θ A B K p` is the triple integral

    ∫ x, ∫ y, ∫ u, star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)

of the block-I shape of the `Q₂` row.  Its kernel enters at `(x p.2, y)`.

Here `K = qmqKernel ℓ e` is the `Q M Q` kernel of the pair kernel `e` (`qmqDefs`):

    qmqKernel ℓ e w y = e w y − ℓ⁻³∫_{acube}e w · − ℓ⁻³∫_{acube}e · y + ℓ⁻⁶∬_{acube²}e ,
    qmqRowB ℓ e w := ℓ⁻³∫_{acube}e w ·,   qmqRowC ℓ e y := ℓ⁻³∫_{acube}e · y,
    qmqRowD ℓ e   := ℓ⁻⁶∬_{acube²}e .

The theorem recorded here is the **a.e.-congruence** of the shape in the kernel: if
`Function.uncurry e₁ =ᵐ Function.uncurry e₂` for the product of two copies of Lebesgue measure on
`ℝ³`, then `rowShape13 Θ A B (qmqKernel ℓ e₁) p = rowShape13 Θ A B (qmqKernel ℓ e₂) p` — for
**every** `Θ, A, B, p` (in particular no support hypothesis on `Θ` is needed, and the diagonal
`p.1 = p.2` is covered).  This is the first half of the "`rowShape13` only depends on the a.e.
class of `k`" step of the `L¹`-dictionary `dict13_L1` (see the module docstring of `dict13Aux`).

## The argument

1. **Each `Q M Q` row is a.e.-congruent in `e`.**  `qmqRowB ℓ e = ℓ⁻³∫_{acube}↑(e w ·)` is
   `e`-a.e.-determined: `Measure.ae_ae_eq_of_ae_eq_uncurry` turns the product-measure hypothesis
   into `∀ᵐ w, e₁ w =ᵐ e₂ w`, and `(volume.restrict (acube ℓ)) ≪ volume` plus
   `integral_congr_ae` finish (after pushing through the coercion `ℝ → ℂ`).
   `qmqRowC ℓ e = qmqRowB ℓ (swap e)` (`rfl`), and the same statement for `swap e` follows from
   `MeasurePreserving.Prod.swap` through `QuasiMeasurePreserving.ae_eq`.  `qmqRowD ℓ e` carries no
   variable at all: its two double integrals agree because the hypothesis transfers to
   `(volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ)) ≪ volume.prod volume`.
   Hence `qmqKernel ℓ e₁ =ᵐ qmqKernel ℓ e₂` on `volume.prod volume`, using the a.e.-`fst`/`snd`
   transports `Measure.quasiMeasurePreserving_fst`/`_snd`.

2. **The `x`-integral may be tested at `x p.2`.**  A function `f` of `w : E3` which vanishes a.e.
   pulls back to an a.e.-vanishing function of the `i`-th coordinate of `x : Fin n → E3`: for
   `T` with `volume T = 0` one has `volume {x | x i ∈ T} = 0`, since `{x | x i ∈ T}` is the box
   `Set.univ.pi (fun k => if k = i then T else Set.univ)` of the product measure and
   `Measure.pi_pi` makes its measure the product of its factors, one of which is `0`.  (This holds
   for **arbitrary** `T`, no measurability needed — the thesis below is stated with the raw outer
   measure.)  Concretely: `∀ᵐ w, P w  ⟹  ∀ᵐ x, P (x i)`.

3. **Assembly.**  `Measure.ae_ae_of_ae_prod` gives the slice form `∀ᵐ w, ∀ᵐ y, K₁ w y = K₂ w y`,
   step 2 with `i = p.2` gives `∀ᵐ x, ∀ᵐ y, K₁ (x p.2) y = K₂ (x p.2) y`, and three nested
   `integral_congr_ae` (the innermost one is pointwise in `u`) close the shape identity.

Everything here is `sorry`-free and axiom-clean.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

set_option autoImplicit false

/-! ## 1. Auxiliary a.e. toolkit -/

/-- An a.e. statement transfers from `ν` to any measure absolutely continuous w.r.t. `ν`. -/
private lemma dict13RowShape_ae_of_ac {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}
    (h : μ ≪ ν) {p : α → Prop} (hp : ∀ᵐ x ∂ν, p x) : ∀ᵐ x ∂μ, p x :=
  Filter.Eventually.filter_mono (Measure.AbsolutelyContinuous.ae_le h) hp

/-- The `i`-th coordinate slice of a null set of `E3` is null in the product measure on
`Fin n → E3`.  Stated for the raw outer measure, so no measurability of `T` is needed:
`{x | x i ∈ T}` is the box `Set.univ.pi (fun k => if k = i then T else Set.univ)` and
`Measure.pi_pi` evaluates its measure as a product having the factor `volume T = 0`. -/
theorem dict13RowShape_piEval_preimage_null {n : ℕ} (i : Fin n) (T : Set E3)
    (hT : (volume : Measure E3) T = 0) :
    (volume : Measure (Xn n)) ((fun x => x i) ⁻¹' T) = 0 := by
  have hset : (fun x : Xn n => x i) ⁻¹' T
      = Set.univ.pi (fun k => if k = i then T else Set.univ) := by
    ext x; simp [Set.mem_pi]
  rw [hset]
  show (Measure.pi fun _ : Fin n => (volume : Measure E3))
      (Set.univ.pi fun k => if k = i then T else Set.univ) = 0
  rw [Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [hT]

/-- A property holding a.e. on `E3` holds a.e. at the `i`-th coordinate of `Fin n → E3`. -/
theorem dict13RowShape_ae_piEval {n : ℕ} (i : Fin n) {p : E3 → Prop}
    (h : ∀ᵐ w ∂(volume : Measure E3), p w) :
    ∀ᵐ x ∂(volume : Measure (Xn n)), p (x i) := by
  rw [ae_iff] at h ⊢
  exact dict13RowShape_piEval_preimage_null i _ h

/-! ## 2. The three `Q M Q` rows are a.e.-congruent in the pair kernel -/

/-- The first box average `qmqRowB ℓ e w = ℓ⁻³∫_{acube}e w ·` depends only on the a.e. class
of `e`. -/
theorem qmqRowB_congrAe {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      Function.uncurry e₂) :
    qmqRowB ℓ e₁ =ᵐ[(volume : Measure E3)] qmqRowB ℓ e₂ := by
  have hslice := Measure.ae_ae_eq_of_ae_eq_uncurry h
  filter_upwards [hslice] with w hw
  simp only [qmqRowB]
  congr 1
  refine integral_congr_ae ?_
  exact Filter.EventuallyEq.fun_comp
    (dict13RowShape_ae_of_ac
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) hw)
    (fun r : ℝ => (r : ℂ))

/-- The second box average is the first one of the swapped kernel: `qmqRowC ℓ e = qmqRowB ℓ (swap e)`
(this is `rfl`). -/
theorem qmqRowC_eq_qmqRowB_swap (ℓ : ℝ) (e : E3 → E3 → ℝ) :
    qmqRowC ℓ e = qmqRowB ℓ (fun a b => e b a) := rfl

/-- The second box average `qmqRowC ℓ e y = ℓ⁻³∫_{acube}e · y` also depends only on the a.e. class
of `e`: it is the first average of the swapped kernel, and swapping the two variables preserves the
hypothesis because `Prod.swap` is measure preserving for `volume.prod volume`. -/
theorem qmqRowC_congrAe {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      Function.uncurry e₂) :
    qmqRowC ℓ e₁ =ᵐ[(volume : Measure E3)] qmqRowC ℓ e₂ := by
  rw [qmqRowC_eq_qmqRowB_swap ℓ e₁, qmqRowC_eq_qmqRowB_swap ℓ e₂]
  refine qmqRowB_congrAe (ℓ := ℓ) ?_
  exact (Measure.measurePreserving_swap (μ := (volume : Measure E3))
    (ν := (volume : Measure E3))).quasiMeasurePreserving.ae_eq h

/-- The constant row `qmqRowD ℓ e = ℓ⁻⁶∬_{acube²}e` is congruent (not merely a.e.): the hypothesis
transfers to the product of the two restricted measures, which is absolutely continuous in the
product of the two Lebesgue measures. -/
theorem qmqRowD_congrAe {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      Function.uncurry e₂) :
    qmqRowD ℓ e₁ = qmqRowD ℓ e₂ := by
  have hprod : Function.uncurry e₁
      =ᵐ[((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))] Function.uncurry e₂ :=
    dict13RowShape_ae_of_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)) h
  have hslice := Measure.ae_ae_eq_of_ae_eq_uncurry hprod
  simp only [qmqRowD]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hslice] with w hw
  refine integral_congr_ae ?_
  exact Filter.EventuallyEq.fun_comp hw (fun r : ℝ => (r : ℂ))

/-! ## 3. The `Q M Q` kernel is a.e.-congruent in the pair kernel -/

/-- `qmqKernel ℓ e = e − qmqRowB ℓ e − qmqRowC ℓ e + qmqRowD ℓ e` depends only on the a.e. class
of `e` (each of the four rows is congruent, the two variable rows a.e. in the corresponding
variable). -/
theorem qmqKernel_congrAe {ℓ : ℝ} {e₁ e₂ : E3 → E3 → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      Function.uncurry e₂) :
    (fun z : E3 × E3 => qmqKernel ℓ e₁ z.1 z.2)
      =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      (fun z : E3 × E3 => qmqKernel ℓ e₂ z.1 z.2) := by
  have hB := qmqRowB_congrAe (ℓ := ℓ) h
  have hC := qmqRowC_congrAe (ℓ := ℓ) h
  have hD := qmqRowD_congrAe (ℓ := ℓ) h
  have h' : (fun z : E3 × E3 => e₁ z.1 z.2)
      =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      (fun z : E3 × E3 => e₂ z.1 z.2) := h
  have hB' : (fun z : E3 × E3 => qmqRowB ℓ e₁ z.1)
      =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      (fun z : E3 × E3 => qmqRowB ℓ e₂ z.1) := by
    simpa only [Function.comp_def] using Measure.quasiMeasurePreserving_fst.ae_eq hB
  have hC' : (fun z : E3 × E3 => qmqRowC ℓ e₁ z.2)
      =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      (fun z : E3 × E3 => qmqRowC ℓ e₂ z.2) := by
    simpa only [Function.comp_def] using Measure.quasiMeasurePreserving_snd.ae_eq hC
  filter_upwards [h', hB', hC', Filter.Eventually.of_forall (fun _ => hD)] with z he hb hc hd
  simp only [qmqKernel]
  rw [he, hb, hc, hd]

/-! ## 4. The shape is congruent -/

/-- **The block-I shape only sees `e` through its a.e. class.**  No hypothesis on `Θ, A, B` is
needed (no measurability, no bound, no support) and no restriction on the pair `p` (in particular
`p.1 = p.2` is allowed): the kernel argument of the shape is `(x p.2, y)`, and for a.e. `x` the
slice `qmqKernel ℓ e₁ (x p.2) =ᵐ qmqKernel ℓ e₂ (x p.2)` holds by step 1 + step 2. -/
theorem dict13RowShapeCongrAe {n : ℕ} {ℓ : ℝ} {Θ : Submission.BoseGases.X n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {p : Fin n × Fin n}
    {e₁ e₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))] Function.uncurry e₂) :
    Work.BoseBoxFock.rowShape13 Θ A B (Work.BoseBoxFock.qmqKernel ℓ e₁) p
      = Work.BoseBoxFock.rowShape13 Θ A B (Work.BoseBoxFock.qmqKernel ℓ e₂) p := by
  have hK := qmqKernel_congrAe (ℓ := ℓ) h
  have hslice : ∀ᵐ w ∂(volume : Measure E3), ∀ᵐ y ∂(volume : Measure E3),
      qmqKernel ℓ e₁ w y = qmqKernel ℓ e₂ w y := Measure.ae_ae_of_ae_prod hK
  have hx := dict13RowShape_ae_piEval p.2 hslice
  simp only [rowShape13]
  refine integral_congr_ae ?_
  filter_upwards [hx] with x hxx
  refine integral_congr_ae ?_
  filter_upwards [hxx] with y hyy
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only []
  rw [hyy]

end Work.BoseBoxFock

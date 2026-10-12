import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRow_pairSlot_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aQ_aQ_sym_box`

Self-adjointness of the *product* `QᵢQⱼ` (`i ≠ j`) of the slot complement projections
`Qᵢ = 1 − Pᵢ` (`Pᵢ` = mean over the centred cube `acube ℓ`) for the box pairing

    ⟨f, w⟩ = ∫ x in abox n ℓ, f x * w x .

The two slots `i ≠ j` act on *different* coordinates, so `Qᵢ` and `Qⱼ` commute
(`Work.BoseBoxFock.Weak.aQ_comm_fun`) and each is self-adjoint over the box
(`Work.BoseBoxFock.Weak.aQ_sym_box`); hence the product is self-adjoint:

    ∫ (Qᵢ Qⱼ g)·v = ∫ g·(Qᵢ Qⱼ v) .

The requested statement is the **mixed** version: `g` is only *measurable and bounded*
(the state class of the box ↔ model bridge, cf. `weakAux`), while `v` is *continuous* —
and a continuous `v : (ℝ³)ⁿ → ℝ` need not be globally bounded, since the configuration
space is not compact.  `Weak.aQ_sym_box` requires *global* bounds on both factors, so the
bridge used here is the **box truncation**

    boxTrunc ℓ v = 1_{abox n ℓ} · v ,

which is globally bounded (`boxTrunc_abs_le`) and measurable (`boxTrunc_measurable`) and
agrees with `v` on the box.  Every operator expression occurring in the box pairing at a
point `x ∈ abox n ℓ` depends on its argument only through values on `abox n ℓ`: `Pᵢ`
averages over `y ∈ acube ℓ` and `Function.update x i y ∈ abox n ℓ`
(`Submission.BoseGases.update_mem_abox`).  That box-locality is the content of
`aP_eq_of_eqOn_abox`, `aQ_eq_of_eqOn_abox`, `aQ_boxTrunc_eq` and `aQ_aQ_boxTrunc_eq`,
and it lets the pair `(g, boxTrunc ℓ v)` be fed to the globally-bounded theory.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open Submission.BoseGases

set_option linter.unusedVariables false

/-! ## 1. The box truncation of a state -/

/-- The truncation of a state to the centred box `abox n ℓ`. -/
noncomputable def boxTrunc {n : ℕ} (ℓ : ℝ) (F : X n → ℝ) : X n → ℝ :=
  (abox n ℓ).indicator F

/-- The box truncation of a measurable state is measurable. -/
lemma boxTrunc_measurable {n : ℕ} (ℓ : ℝ) {F : X n → ℝ} (hF : Measurable F) :
    Measurable (boxTrunc ℓ F) := hF.indicator (abox_measurable n ℓ)

/-- The box truncation agrees with the state on the box. -/
lemma boxTrunc_apply_of_mem {n : ℕ} {ℓ : ℝ} {F : X n → ℝ} {x : X n} (hx : x ∈ abox n ℓ) :
    boxTrunc ℓ F x = F x := Set.indicator_of_mem hx F

/-- A bound of a state *on the box* bounds its box truncation on all of `Ωᴺ`. -/
lemma boxTrunc_abs_le {n : ℕ} {ℓ : ℝ} {F : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x ∈ abox n ℓ, |F x| ≤ C) : ∀ x, |boxTrunc ℓ F x| ≤ C := by
  intro x
  by_cases hx : x ∈ abox n ℓ
  · rw [boxTrunc_apply_of_mem hx]; exact hb x hx
  · rw [boxTrunc, Set.indicator_of_notMem hx F]; simpa using hC

/-! ## 2. Box locality of the slot operators -/

/-- **The slot mean is box local**: two states agreeing on `abox n ℓ` have the same fibre
mean there (for an *arbitrary* pair of states; only the values on the box are used). -/
lemma aP_eq_of_eqOn_abox {n : ℕ} {ℓ : ℝ} {i : Fin n} {F G : X n → ℝ}
    (h : ∀ z ∈ abox n ℓ, F z = G z) {x : X n} (hx : x ∈ abox n ℓ) :
    aP ℓ i F x = aP ℓ i G x := by
  unfold aP
  congr 1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ y ∂(volume.restrict (acube ℓ)),
      F (Function.update x i y) = G (Function.update x i y) := by
    rw [ae_restrict_iff' (acube_measurable ℓ)]
    exact ae_of_all volume (fun y hy => h _ (update_mem_abox i hx hy))
  exact hae

/-- **`Qᵢ = 1 − Pᵢ` is box local**: the difference of two box-local functions. -/
lemma aQ_eq_of_eqOn_abox {n : ℕ} {ℓ : ℝ} {i : Fin n} {F G : X n → ℝ}
    (h : ∀ z ∈ abox n ℓ, F z = G z) {x : X n} (hx : x ∈ abox n ℓ) :
    aQ ℓ i F x = aQ ℓ i G x := by
  unfold aQ
  rw [h x hx, aP_eq_of_eqOn_abox h hx]

/-- `Qᵢ` of a box truncation is `Qᵢ` of the state, on the box. -/
lemma aQ_boxTrunc_eq {n : ℕ} {ℓ : ℝ} {i : Fin n} (F : X n → ℝ) {x : X n}
    (hx : x ∈ abox n ℓ) : aQ ℓ i (boxTrunc ℓ F) x = aQ ℓ i F x :=
  aQ_eq_of_eqOn_abox (fun z hz => boxTrunc_apply_of_mem hz) hx

/-- The two-slot complement of a box truncation is the two-slot complement of the state,
on the box. -/
lemma aQ_aQ_boxTrunc_eq {n : ℕ} {ℓ : ℝ} {i j : Fin n} (F : X n → ℝ) {x : X n}
    (hx : x ∈ abox n ℓ) : aQ ℓ i (aQ ℓ j (boxTrunc ℓ F)) x = aQ ℓ i (aQ ℓ j F) x :=
  aQ_eq_of_eqOn_abox (fun z hz => aQ_boxTrunc_eq F hz) hx

/-! ## 3. The two-slot symmetry for globally bounded states -/

/-- **Self-adjointness of `QᵢQⱼ` (`i ≠ j`) over the box**, for globally bounded measurable
states: `Qᵢ` and `Qⱼ` commute (`Weak.aQ_comm_fun`) and each is self-adjoint
(`Weak.aQ_sym_box`), so the product is. -/
theorem aQ_aQ_sym_box_bounded {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ Ψ : X n → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) :
    (∫ x in abox n ℓ, aQ ℓ i (aQ ℓ j Φ) x * Ψ x)
      = ∫ x in abox n ℓ, Φ x * aQ ℓ i (aQ ℓ j Ψ) x := by
  have hQjm : Measurable (aQ ℓ j Φ) := Weak.aQ_measurable j hΦm
  have hQjb : ∀ x, |aQ ℓ j Φ x| ≤ 2 * C := Weak.aQ_abs_le hℓ j hC hΦb
  have hQim : Measurable (aQ ℓ i Ψ) := Weak.aQ_measurable i hΨm
  have hQib : ∀ x, |aQ ℓ i Ψ x| ≤ 2 * D := Weak.aQ_abs_le hℓ i hD hΨb
  have h2C : 0 ≤ 2 * C := by linarith
  have h2D : 0 ≤ 2 * D := by linarith
  calc (∫ x in abox n ℓ, aQ ℓ i (aQ ℓ j Φ) x * Ψ x)
      = ∫ x in abox n ℓ, aQ ℓ j Φ x * aQ ℓ i Ψ x :=
        Weak.aQ_sym_box hℓ i h2C hD hQjm hQjb hΨm hΨb
    _ = ∫ x in abox n ℓ, Φ x * aQ ℓ j (aQ ℓ i Ψ) x :=
        Weak.aQ_sym_box hℓ j hC h2D hΦm hΦb hQim hQib
    _ = ∫ x in abox n ℓ, Φ x * aQ ℓ i (aQ ℓ j Ψ) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        rw [Weak.aQ_comm_fun hℓ hij hD hΨm hΨb]

/-! ## 4. The requested statement -/

theorem aQ_aQ_sym_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {v : Submission.BoseGases.X n → ℝ} (hvc : Continuous v)
    {g : Submission.BoseGases.X n → ℝ} (hgm : Measurable g) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgb : ∀ x, |g x| ≤ Cg) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aQ ℓ j g) x * v x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          g x * Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aQ ℓ j v) x := by
  obtain ⟨Cv, hCv⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hvc.continuousOn
  have hCv0 : 0 ≤ max Cv 0 := le_max_right _ _
  have hvb : ∀ x ∈ abox n ℓ, |v x| ≤ max Cv 0 := by
    intro x hx
    have h1 : ‖v x‖ ≤ Cv := hCv x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  have htrm : Measurable (boxTrunc ℓ v) := boxTrunc_measurable ℓ hvc.measurable
  have htrb : ∀ x, |boxTrunc ℓ v x| ≤ max Cv 0 := boxTrunc_abs_le hCv0 hvb
  -- replace `v` by its box truncation on the left
  have hstep1 : (∫ x in abox n ℓ, aQ ℓ i (aQ ℓ j g) x * v x)
      = ∫ x in abox n ℓ, aQ ℓ i (aQ ℓ j g) x * boxTrunc ℓ v x := by
    refine integral_congr_ae ?_
    have hae : ∀ᵐ x ∂(volume.restrict (abox n ℓ)),
        aQ ℓ i (aQ ℓ j g) x * v x = aQ ℓ i (aQ ℓ j g) x * boxTrunc ℓ v x := by
      rw [ae_restrict_iff' (abox_measurable n ℓ)]
      exact ae_of_all volume (fun x hx => by rw [boxTrunc_apply_of_mem hx])
    exact hae
  -- replace `v` by its box truncation on the right
  have hstep3 : (∫ x in abox n ℓ, g x * aQ ℓ i (aQ ℓ j (boxTrunc ℓ v)) x)
      = ∫ x in abox n ℓ, g x * aQ ℓ i (aQ ℓ j v) x := by
    refine integral_congr_ae ?_
    have hae : ∀ᵐ x ∂(volume.restrict (abox n ℓ)),
        g x * aQ ℓ i (aQ ℓ j (boxTrunc ℓ v)) x = g x * aQ ℓ i (aQ ℓ j v) x := by
      rw [ae_restrict_iff' (abox_measurable n ℓ)]
      exact ae_of_all volume (fun x hx => by rw [aQ_aQ_boxTrunc_eq v hx])
    exact hae
  rw [hstep1, aQ_aQ_sym_box_bounded hℓ hij hCg hCv0 hgm hgb htrm htrb, hstep3]

end Work.BoseBoxFock

end

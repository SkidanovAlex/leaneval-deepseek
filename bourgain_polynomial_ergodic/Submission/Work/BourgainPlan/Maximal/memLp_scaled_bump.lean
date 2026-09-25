import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.iw_superset

namespace Work.BourgainPlan.Maximal

open MeasureTheory

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The fundamental domain `Ioc (-1/2) (1/2]` carries a finite measure. -/
private instance instIsFiniteMeasureRestrictIocNegHalf :
    IsFiniteMeasure (volume.restrict (Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1))) :=
  isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

/-- A function read along the canonical lift `iwRep` **is** the `Ioc (-1/2) (1/2]`-lift of the
same function: `ξ ↦ g (iwRep ξ) = AddCircle.liftIoc 1 (-1/2) g`.  This is definitional, both
sides being `ξ ↦ g ((equivIoc 1 (-1/2) ξ : ℝ))`. -/
lemma comp_iwRep_eq_liftIoc (g : ℝ → ℂ) :
    (fun ξ : Circ => g (iwRep ξ)) = AddCircle.liftIoc (1 : ℝ) (-(1/2)) g := rfl

/-- The canonical lift lands in its defining half-open interval `Ioc (-1/2) (1/2]`. -/
lemma iwRep_mem_Ioc (ξ : Circ) : iwRep ξ ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1) :=
  (AddCircle.equivIoc (1 : ℝ) (-(1/2)) ξ).2

/-- The canonical lift is bounded by `1/2` in absolute value. -/
lemma abs_iwRep_le (ξ : Circ) : |iwRep ξ| ≤ 1 / 2 := by
  have h := iwRep_mem_Ioc ξ
  rw [Set.mem_Ioc] at h
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The canonical lift `iwRep` is a section of the quotient map `ℝ → 𝕋`. -/
lemma coe_iwRep (ξ : Circ) : ((iwRep ξ : ℝ) : Circ) = ξ := by
  have := AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := -(1/2)) (y := ξ)
  simpa only [iwRep, AddCircle.liftIoc, Set.domRestrict_def, Function.comp_apply] using this

/-- The norm of a circle point is the absolute value of its canonical lift. -/
lemma norm_eq_abs_iwRep (ξ : Circ) : ‖ξ‖ = |iwRep ξ| := by
  have h := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (x := iwRep ξ) one_ne_zero).mpr
    (by simpa using abs_iwRep_le ξ)
  rwa [coe_iwRep ξ] at h

/-- **The `L^∞`-membership and the narrow support of a scaled bump symbol** — the two structural hypotheses of `IWSupersetBound` for the level bumps `η_n` of the MST route: if `η` is continuous with `η x = 0` for `|x| ≥ 1/2` and `1 ≤ |c|`, then `ξ ↦ η (c * iwRep ξ)` is the continuous circle function `AddCircle.liftIoc 1 (-1/2) (fun x => η (c * x))` (its two endpoint values vanish), hence `MemLp ⊤`, and it is supported in the ball of radius `1/(2|c|)`. -/
theorem memLp_scaled_bump {η : ℝ → ℂ} {c : ℝ} (hc : 1 ≤ |c|) (hcont : Continuous η)
    (hsupp : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        η (c * Work.BourgainPlan.Maximal.iwRep ξ)) ⊤ (AddCircle.haarAddCircle (T := 1)) ∧
    (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      1 / (2 * |c|) < ‖ξ‖ → η (c * Work.BourgainPlan.Maximal.iwRep ξ) = 0) := by
  constructor
  · -- the symbol is the `Ioc (-1/2) (1/2]`-lift of the rescaled bump `x ↦ η (c x)`
    rw [comp_iwRep_eq_liftIoc (fun x : ℝ => η (c * x))]
    -- that rescaled bump is continuous, hence bounded on the compact fundamental domain
    have hcs : Continuous (fun x : ℝ => η (c * x)) :=
      hcont.comp (continuous_const.mul continuous_id)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Set.Icc (-(1/2) : ℝ) (-(1/2) + 1)) (hcs.continuousOn)
    have hsm : AEStronglyMeasurable (fun x : ℝ => η (c * x))
        (volume.restrict (Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1))) := hcs.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1))),
        ‖(fun x : ℝ => η (c * x)) x‖ ≤ C :=
      (ae_restrict_mem measurableSet_Ioc).mono
        (fun x hx => hC x (Set.Ioc_subset_Icc_self hx))
    exact (MemLp.memLp_liftIoc (T := 1) (t := -(1/2))
      (MemLp.of_bound hsm C hbound)).haarAddCircle
  · -- narrow support: `‖ξ‖ = |iwRep ξ|` and `1 ≤ |c|`
    intro ξ hξ
    rw [norm_eq_abs_iwRep] at hξ
    refine hsupp (c * iwRep ξ) ?_
    rw [abs_mul]
    have h2 : (0 : ℝ) < 2 * |c| := by linarith [abs_nonneg c, hc]
    have hlt : (1 : ℝ) < |iwRep ξ| * (2 * |c|) := (div_lt_iff₀ h2).mp hξ
    linarith

end

end Work.BourgainPlan.Maximal

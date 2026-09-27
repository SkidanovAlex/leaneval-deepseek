import Mathlib
import Submission.Work.OneDim.Defs

/-!
# Open arcs in a 1-manifold and reparametrisation

An *open arc* in a 1-manifold `C` is the image of an injective global local diffeomorphism
`ℝ → C`.  This file collects the basic facts about open arcs that are used to run Zorn's lemma
on the poset of open arcs (ordered by inclusion) and to reparametrise arcs so that they are
defined on all of `ℝ`.
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-- An **open arc** in `C`: the image of an injective global local diffeomorphism `ℝ → C`. -/
def IsOpenArc (A : Set C) : Prop :=
  ∃ γ : ℝ → C, Function.Injective γ ∧
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ ∧ A = Set.range γ

theorem IsOpenArc.isOpen {A : Set C} (h : IsOpenArc A) : IsOpen A := by
  obtain ⟨γ, -, hld, rfl⟩ := h
  exact hld.isOpen_range

theorem IsOpenArc.nonempty {A : Set C} (h : IsOpenArc A) : A.Nonempty := by
  obtain ⟨γ, -, -, rfl⟩ := h
  exact ⟨γ 0, Set.mem_range_self 0⟩

theorem IsOpenArc.isPreconnected {A : Set C} (h : IsOpenArc A) : IsPreconnected A := by
  obtain ⟨γ, -, hld, rfl⟩ := h
  rw [← Set.image_univ]
  exact isPreconnected_univ.image γ hld.contMDiff.continuous.continuousOn

/-! ## Surjective local diffeomorphisms `ℝ → I` onto an open interval `I` -/

/-- The logistic-type diffeomorphism `ℝ → (a,b)`, `t ↦ a + (b-a)/(1 + e^{-t})`. -/
def logisticPD (a b : ℝ) (hab : a < b) :
    PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ sm :=
  { toPartialEquiv :=
      { toFun := fun t : ℝ => a + (b - a) * (1 / (1 + Real.exp (-t)))
        invFun := fun s : ℝ => Real.log ((s - a) / (b - s))
        source := Set.univ
        target := Set.Ioo a b
        map_source' := by
          intro t _
          have h : (0:ℝ) < 1 / (1 + Real.exp (-t)) := by positivity
          have h2 : 1 / (1 + Real.exp (-t)) < 1 := by
            rw [div_lt_one (by positivity)]; linarith [Real.exp_pos (-t)]
          constructor <;> nlinarith [hab]
        map_target' := by intro s _; trivial
        left_inv' := by
          intro t _
          have h1 : (1:ℝ) + Real.exp (-t) ≠ 0 := by positivity
          have hba : b - a ≠ 0 := by linarith
          have h3 : (1:ℝ) - 1/(1+Real.exp (-t)) = Real.exp (-t)/(1+Real.exp (-t)) := by
            field_simp; ring
          have key : (1/(1+Real.exp (-t))) / (1 - 1/(1+Real.exp (-t))) = Real.exp t := by
            rw [h3, one_div (1 + Real.exp (-t)), div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
            rw [mul_comm (Real.exp (-t))⁻¹ (1 + Real.exp (-t)), ← mul_assoc,
              inv_mul_cancel₀ h1, one_mul]
            rw [← Real.exp_neg, neg_neg]
          have harg : (a + (b - a) * (1/(1+Real.exp (-t))) - a)
              / (b - (a + (b - a) * (1/(1+Real.exp (-t)))))
              = (1/(1+Real.exp (-t)))/(1 - 1/(1+Real.exp (-t))) := by
            rw [show a + (b - a) * (1/(1+Real.exp (-t))) - a
                  = (b - a) * (1/(1+Real.exp (-t))) by ring,
                show b - (a + (b - a) * (1/(1+Real.exp (-t))))
                  = (b - a) * (1 - 1/(1+Real.exp (-t))) by ring,
                mul_div_mul_left _ _ hba]
          rw [harg, key, Real.log_exp]
        right_inv' := by
          intro s hs
          have hsa : (0:ℝ) < s - a := by linarith [hs.1]
          have hbs : (0:ℝ) < b - s := by linarith [hs.2]
          have hx : (0:ℝ) < (s - a)/(b - s) := div_pos hsa hbs
          rw [Real.exp_neg, Real.exp_log hx]
          field_simp
          ring }
    open_source := isOpen_univ
    open_target := isOpen_Ioo
    contMDiffOn_toFun := by
      rw [contMDiffOn_iff_contDiffOn]
      apply ContDiff.contDiffOn
      have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 1 + Real.exp (-t)) :=
        contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)
      exact contDiff_const.add
        (contDiff_const.mul (ContDiff.div contDiff_const hexp (fun x => by positivity)))
    contMDiffOn_invFun := by
      rw [contMDiffOn_iff_contDiffOn]
      apply ContDiffOn.log
      · apply ContDiffOn.div
        · fun_prop
        · fun_prop
        · intro s hs; linarith [hs.2]
      · intro s hs; apply div_ne_zero <;> linarith [hs.1, hs.2] }

theorem isLocalDiffeomorph_logistic (a b : ℝ) (hab : a < b) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
      (fun t : ℝ => a + (b - a) * (1 / (1 + Real.exp (-t)))) := by
  intro x
  exact PartialDiffeomorph.isLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ)
    (modelWithCornersSelf ℝ ℝ) sm (logisticPD a b hab) (Set.mem_univ x)

/-- The diffeomorphism `ℝ → (a,∞)`, `t ↦ a + e^t`. -/
def expShiftPD (a : ℝ) :
    PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ sm :=
  { toPartialEquiv :=
      { toFun := fun t : ℝ => a + Real.exp t
        invFun := fun s : ℝ => Real.log (s - a)
        source := Set.univ
        target := Set.Ioi a
        map_source' := by intro t _; exact lt_add_of_pos_right a (Real.exp_pos t)
        map_target' := by intro s _; trivial
        left_inv' := by
          intro t _
          rw [add_sub_cancel_left, Real.log_exp]
        right_inv' := by
          intro s hs
          have hsa : a < s := hs
          rw [Real.exp_log (by linarith : (0:ℝ) < s - a)]
          ring }
    open_source := isOpen_univ
    open_target := isOpen_Ioi
    contMDiffOn_toFun := by
      rw [contMDiffOn_iff_contDiffOn]
      exact (contDiff_const.add Real.contDiff_exp).contDiffOn
    contMDiffOn_invFun := by
      rw [contMDiffOn_iff_contDiffOn]
      apply ContDiffOn.log
      · fun_prop
      · intro s hs; have hsa : a < s := hs; linarith }

theorem isLocalDiffeomorph_expShift (a : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
      (fun t : ℝ => a + Real.exp t) := by
  intro x
  exact PartialDiffeomorph.isLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ)
    (modelWithCornersSelf ℝ ℝ) sm (expShiftPD a) (Set.mem_univ x)

/-- The diffeomorphism `ℝ → (-∞,b)`, `t ↦ b - e^{-t}`. -/
def expNegShiftPD (b : ℝ) :
    PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ sm :=
  { toPartialEquiv :=
      { toFun := fun t : ℝ => b - Real.exp (-t)
        invFun := fun s : ℝ => - Real.log (b - s)
        source := Set.univ
        target := Set.Iio b
        map_source' := by intro t _; exact sub_lt_self b (Real.exp_pos (-t))
        map_target' := by intro s _; trivial
        left_inv' := by
          intro t _
          rw [sub_sub_cancel, Real.log_exp, neg_neg]
        right_inv' := by
          intro s hs
          have h : (0:ℝ) < b - s := by linarith [show s < b from hs]
          rw [show - (- Real.log (b - s)) = Real.log (b - s) by ring, Real.exp_log h]
          ring }
    open_source := isOpen_univ
    open_target := isOpen_Iio
    contMDiffOn_toFun := by
      rw [contMDiffOn_iff_contDiffOn]
      exact (contDiff_const.sub (Real.contDiff_exp.comp contDiff_neg)).contDiffOn
    contMDiffOn_invFun := by
      rw [contMDiffOn_iff_contDiffOn]
      apply ContDiffOn.neg
      apply ContDiffOn.log
      · fun_prop
      · intro s hs; have hsb : s < b := hs; linarith }

theorem isLocalDiffeomorph_expNegShift (b : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
      (fun t : ℝ => b - Real.exp (-t)) := by
  intro x
  exact PartialDiffeomorph.isLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ)
    (modelWithCornersSelf ℝ ℝ) sm (expNegShiftPD b) (Set.mem_univ x)

theorem isLocalDiffeomorph_id :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm (id : ℝ → ℝ) :=
  (Diffeomorph.refl (modelWithCornersSelf ℝ ℝ) ℝ sm).isLocalDiffeomorph


/-! ## Ranges of the explicit interval diffeomorphisms -/

theorem range_logistic (a b : ℝ) (hab : a < b) :
    Set.range (fun t : ℝ => a + (b - a) * (1 / (1 + Real.exp (-t)))) = Set.Ioo a b := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact (logisticPD a b hab).toPartialEquiv.map_source' (Set.mem_univ t)
  · intro hy
    exact ⟨Real.log ((y - a) / (b - y)), (logisticPD a b hab).toPartialEquiv.right_inv' hy⟩

theorem range_expShift (a : ℝ) :
    Set.range (fun t : ℝ => a + Real.exp t) = Set.Ioi a := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact lt_add_of_pos_right a (Real.exp_pos t)
  · intro hy
    refine ⟨Real.log (y - a), ?_⟩
    show a + Real.exp (Real.log (y - a)) = y
    rw [Real.exp_log (by show (0:ℝ) < y - a; linarith [show a < y from hy])]
    ring

theorem range_expNegShift (b : ℝ) :
    Set.range (fun t : ℝ => b - Real.exp (-t)) = Set.Iio b := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact sub_lt_self b (Real.exp_pos (-t))
  · intro hy
    refine ⟨- Real.log (b - y), ?_⟩
    show b - Real.exp (-(- Real.log (b - y))) = y
    rw [show -(- Real.log (b - y)) = Real.log (b - y) by ring,
      Real.exp_log (by show (0:ℝ) < b - y; linarith [show y < b from hy])]
    ring

theorem injective_logistic (a b : ℝ) (hab : a < b) :
    Function.Injective (fun t : ℝ => a + (b - a) * (1 / (1 + Real.exp (-t)))) := by
  intro t s hts
  have hba : (b - a) ≠ 0 := by linarith
  have h1 : (1 / (1 + Real.exp (-t))) = (1 / (1 + Real.exp (-s))) := by
    have h := hts
    simp only at h
    exact mul_left_cancel₀ hba (by linarith)
  have h2 : Real.exp (-t) = Real.exp (-s) := by
    rw [one_div, one_div, inv_inj] at h1
    linarith
  have h3 : -t = -s := Real.exp_injective h2
  linarith

theorem injective_expShift (a : ℝ) :
    Function.Injective (fun t : ℝ => a + Real.exp t) := by
  intro t s hts
  exact Real.exp_injective (by linarith)

theorem injective_expNegShift (b : ℝ) :
    Function.Injective (fun t : ℝ => b - Real.exp (-t)) := by
  intro t s hts
  have h2 : Real.exp (-t) = Real.exp (-s) := by linarith
  have h3 := Real.exp_injective h2
  linarith

end Work.OneDim

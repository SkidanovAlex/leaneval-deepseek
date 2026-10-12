import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.SlotProjAux
import Submission.Work.BoseBoxFock.cIPn_sum_aPC_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aPC_slotProj1_comm_ne`

The box slot mean `aPC ℓ i` (the mean over the cube `acube ℓ` of the state with the slot `i`
replaced) commutes with the single-slot projection `slotProj1 e j` at a **different** slot
`i ≠ j`, almost everywhere for the Lebesgue measure on the configuration space.

The proof has three parts.

* **The pointwise computation.**  Both compositions are nested integrals over the slot `i`
  (`y ∈ acube ℓ`) and over the slot `j` (`w`, against `PV e (x j) w`).  Since `i ≠ j` the two
  `Function.update`s commute (`Function.update_comm`), so both sides are the same double
  integral read in the two possible orders; the exchange is `integral_integral_swap`
  (`MeasureTheory.integral_integral_swap`), applied to a state `Ψ'` that is *strongly
  measurable and everywhere bounded* — then the integrand is dominated by
  `‖PV e (x j) w‖ · C`, and `w ↦ PV e (x j) w` is integrable because the modes are supported
  in the box `boxL ℓ` (of finite measure) and are a.e. bounded (`MemLp ⊤`).

* **Transfer to the honest state.**  For an only-`MemLp ⊤` state `Ψ` we pick the bounded
  strongly measurable representative `Ψ'` of `Ψ` and use that both operators are insensitive
  to null modifications of the state: `aPC` and `slotProj1` are integrals against the
  insertion map `x ↦ x[i ↦ y]`, and a null set of configurations pulls back to a null set of
  the product measure (`Work.BoseBoxFock.prod_update_preimage_null`), so Fubini
  (`Measure.ae_ae_of_ae_prod`) plus `integral_congr_ae` transfers the a.e. equality.

* **Assembly** by transitivity of `=ᵐ`.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 0. The a.e. bound of an `L^∞` state -/

/-- A state in `L^∞` is a.e. bounded by a nonnegative constant. -/
private theorem ae_bound_of_memLp_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f (⊤ : ENNReal) μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have h1 : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]; exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h1
  rw [Filter.eventually_map] at hC
  exact ⟨C, C.coe_nonneg, Filter.Eventually.mono hC fun x hx => by exact_mod_cast hx⟩

/-! ## 1. The operators are insensitive to null modifications of the state

Both `aPC ℓ i` and `slotProj1 e j` read the state only along the insertion map
`(x, y) ↦ x[i ↦ y]`; a (measurable) null set of configurations pulls back to a null set of
the product measure, so a.e. equal states give a.e. equal images. -/

/-- **`aPC` is insensitive to null modifications.**  For the *full* Lebesgue measure on the
configuration space. -/
private theorem aPC_congr_ae_of_ae_eq {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1))
    {Θ Θ' : (Fin (n + 1) → Ω) → ℂ}
    (h : Θ =ᵐ[(volume : Measure (Fin (n + 1) → Ω))] Θ') :
    aPC ℓ i Θ =ᵐ[(volume : Measure (Fin (n + 1) → Ω))] aPC ℓ i Θ' := by
  have hD : (volume : Measure (Fin (n + 1) → Ω)) {x | ¬ (Θ x = Θ' x)} = 0 := ae_iff.mp h
  obtain ⟨D', hsub, hD'm, hD'0⟩ := exists_measurable_superset_of_null hD
  have hprod : ((volume : Measure (Fin (n + 1) → Ω)).prod (volume : Measure Ω))
      {p : (Fin (n + 1) → Ω) × Ω | Function.update p.1 i p.2 ∈ D'} = 0 :=
    prod_update_preimage_null i hD'm hD'0
  have hae : ∀ᵐ p ∂((volume : Measure (Fin (n + 1) → Ω)).prod (volume : Measure Ω)),
      ¬ (Function.update p.1 i p.2 ∈ D') := by
    rw [ae_iff]; simpa using hprod
  have hiter : ∀ᵐ x ∂(volume : Measure (Fin (n + 1) → Ω)),
      ∀ᵐ y ∂(volume : Measure Ω), ¬ (Function.update x i y ∈ D') :=
    Measure.ae_ae_of_ae_prod hae
  filter_upwards [hiter] with x hx
  unfold aPC
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_mono Measure.restrict_le_self hx] with y hy
  by_contra hne
  exact hy (hsub hne)

/-- **`slotProj1` is insensitive to null modifications.**  For the *full* Lebesgue measure on
the configuration space. -/
private theorem slotProj1_congr_ae_of_ae_eq {m n : ℕ} (e : Fin m → Ω → ℂ) (j : Fin (n + 1))
    {Θ Θ' : (Fin (n + 1) → Ω) → ℂ}
    (h : Θ =ᵐ[(volume : Measure (Fin (n + 1) → Ω))] Θ') :
    slotProj1 e j Θ =ᵐ[(volume : Measure (Fin (n + 1) → Ω))] slotProj1 e j Θ' := by
  have hD : (volume : Measure (Fin (n + 1) → Ω)) {x | ¬ (Θ x = Θ' x)} = 0 := ae_iff.mp h
  obtain ⟨D', hsub, hD'm, hD'0⟩ := exists_measurable_superset_of_null hD
  have hprod : ((volume : Measure (Fin (n + 1) → Ω)).prod (volume : Measure Ω))
      {p : (Fin (n + 1) → Ω) × Ω | Function.update p.1 j p.2 ∈ D'} = 0 :=
    prod_update_preimage_null j hD'm hD'0
  have hae : ∀ᵐ p ∂((volume : Measure (Fin (n + 1) → Ω)).prod (volume : Measure Ω)),
      ¬ (Function.update p.1 j p.2 ∈ D') := by
    rw [ae_iff]; simpa using hprod
  have hiter : ∀ᵐ x ∂(volume : Measure (Fin (n + 1) → Ω)),
      ∀ᵐ y ∂(volume : Measure Ω), ¬ (Function.update x j y ∈ D') :=
    Measure.ae_ae_of_ae_prod hae
  filter_upwards [hiter] with x hx
  unfold slotProj1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hx] with y hy
  rw [show Θ (Function.update x j y) = Θ' (Function.update x j y) from by
    by_contra hne
    exact hy (hsub hne)]

/-! ## 2. The main theorem -/

theorem aPC_slotProj1_comm_ne (ℓ : ℝ) (hℓ : 0 < ℓ) {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΨ : MeasureTheory.MemLp Ψ ⊤) :
    (fun x => Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.slotProj1 e j Ψ) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3)))]
      (fun x => Work.BoseBoxFock.slotProj1 e j (Work.BoseBoxFock.aPC ℓ i Ψ) x) := by
  classical
  -- the configuration space has at least one particle
  have hNpos : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hNpos)
  subst hn
  -- ## 2a. A bounded strongly measurable representative `Ψ'` of `Ψ`
  obtain ⟨C, hC0, hCb⟩ := ae_bound_of_memLp_top hΨ
  obtain ⟨g, hgsm, hgeq⟩ := hΨ.aestronglyMeasurable
  have hSmeas : MeasurableSet {z : Fin (n + 1) → Ω | ‖g z‖ ≤ C} :=
    measurableSet_le hgsm.measurable.norm measurable_const
  set Ψ' : (Fin (n + 1) → Ω) → ℂ := fun z => if ‖g z‖ ≤ C then g z else 0 with hΨ'def
  have hΨ'sm : StronglyMeasurable Ψ' := by
    show StronglyMeasurable fun z : Fin (n + 1) → Ω => if ‖g z‖ ≤ C then g z else 0
    exact hgsm.ite hSmeas stronglyMeasurable_const
  have hΨ'bdd : ∀ z, ‖Ψ' z‖ ≤ C := by
    intro z
    by_cases hz : ‖g z‖ ≤ C
    · show ‖(if ‖g z‖ ≤ C then g z else 0)‖ ≤ C
      rw [if_pos hz]; exact hz
    · show ‖(if ‖g z‖ ≤ C then g z else 0)‖ ≤ C
      rw [if_neg hz, norm_zero]; exact hC0
  have hΨeq : Ψ =ᵐ[(volume : Measure (Fin (n + 1) → Ω))] Ψ' := by
    filter_upwards [hgeq, hCb] with z h1 h2
    have hz : ‖g z‖ ≤ C := by rw [← h1]; exact h2
    show Ψ z = (if ‖g z‖ ≤ C then g z else 0)
    rw [if_pos hz]
    exact h1
  -- ## 2b. The pointwise identity for the bounded representative
  have hpoint : ∀ x : Fin (n + 1) → Ω,
      aPC ℓ i (slotProj1 e j Ψ') x = slotProj1 e j (aPC ℓ i Ψ') x := by
    intro x
    haveI hfin : IsFiniteMeasure ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
    set F : Ω → Ω → ℂ := fun w y =>
      PV e (x j) w * Ψ' (Function.update (Function.update x j w) i y) with hF
    have hFdef : ∀ w y, F w y = PV e (x j) w * Ψ' (Function.update (Function.update x j w) i y) :=
      fun w y => rfl
    -- integrability of the joint integrand
    have hInt : MeasureTheory.Integrable (Function.uncurry F)
        ((volume : Measure Ω).prod ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ))) := by
      -- `w ↦ PV e (x j) w` is integrable
      have hPV : MeasureTheory.Integrable (fun w : Ω => PV e (x j) w) (volume : Measure Ω) := by
        choose Cl _hCl0 hCl using fun l : Fin m => ae_bound_of_memLp_top (hbdd l)
        set B : ℝ := ∑ l : Fin m, ‖e l (x j)‖ * Cl l with hBdef
        have hgInt : MeasureTheory.Integrable
            (fun w : Ω => (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => B) w)
            (volume : Measure Ω) := by
          rw [integrable_indicator_iff (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)]
          refine integrableOn_const ?_
          rw [Work.BoseB4.BoxData.volume_boxL _ hℓ]
          exact ENNReal.ofReal_ne_top
        have hfmeas : AEStronglyMeasurable (fun w : Ω => PV e (x j) w) (volume : Measure Ω) := by
          have h0 : AEStronglyMeasurable
              (∑ l : Fin m, (fun _ : Ω => e l (x j)) * (star (e l))) (volume : Measure Ω) :=
            Finset.aestronglyMeasurable_sum Finset.univ
              (fun l _ => aestronglyMeasurable_const.mul (((hbdd l).aestronglyMeasurable).star))
          rw [show (fun w : Ω => PV e (x j) w)
              = ∑ l : Fin m, (fun _ : Ω => e l (x j)) * (star (e l)) from by
            funext w
            simp only [PV, Finset.sum_apply, Pi.mul_apply, Pi.star_apply]]
          exact h0
        refine hgInt.mono' hfmeas ?_
        filter_upwards [Filter.eventually_all.mpr hCl] with w hw
        by_cases hwb : w ∈ Work.BoseK15.corpusBox.boxL ℓ
        · rw [Set.indicator_of_mem hwb]
          calc ‖PV e (x j) w‖ ≤ ∑ l : Fin m, ‖e l (x j) * star (e l w)‖ := by
                rw [PV]; exact norm_sum_le Finset.univ _
            _ = ∑ l : Fin m, ‖e l (x j)‖ * ‖e l w‖ := by simp
            _ ≤ ∑ l : Fin m, ‖e l (x j)‖ * Cl l :=
                Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hw l) (norm_nonneg _)
            _ = B := by rw [hBdef]
        · rw [Set.indicator_of_notMem hwb]
          rw [PV_eq_zero_of_factors e (fun l => by
            by_contra hne
            exact hwb (hsupp l (Function.mem_support.mpr hne))), norm_zero]
      have h1 : MeasureTheory.Integrable (fun p : Ω × Ω => PV e (x j) p.1 * (1 : ℂ))
          ((volume : Measure Ω).prod ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ))) :=
        hPV.mul_prod (integrable_const (1 : ℂ))
      have h2 : AEStronglyMeasurable
          (fun p : Ω × Ω => Ψ' (Function.update (Function.update x j p.1) i p.2))
          ((volume : Measure Ω).prod ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ))) :=
        (hΨ'sm.comp_measurable (by fun_prop)).aestronglyMeasurable
      have h3 : ∀ᵐ p ∂((volume : Measure Ω).prod
            ((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ))),
          ‖Ψ' (Function.update (Function.update x j p.1) i p.2)‖ ≤ C :=
        Filter.Eventually.of_forall fun p => hΨ'bdd _
      refine (h1.mul_bdd h2 h3).congr ?_
      filter_upwards with p
      simp only [Function.uncurry, hFdef, mul_one]
    have hswap : (∫ w, ∫ y, F w y
          ∂((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) ∂(volume : Measure Ω))
        = ∫ y, ∫ w, F w y
          ∂(volume : Measure Ω) ∂((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.integral_integral_swap hInt
    have hL : aPC ℓ i (slotProj1 e j Ψ') x
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) *
          ∫ y, ∫ w, F w y
            ∂(volume : Measure Ω) ∂((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) := by
      unfold aPC
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      unfold slotProj1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [Function.update_of_ne (Ne.symm hij) y x, Function.update_comm hij y w x]
    have hR : slotProj1 e j (aPC ℓ i Ψ') x
        = ((1 / ℓ ^ 3 : ℝ) : ℂ) *
          ∫ w, ∫ y, F w y
            ∂((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)) ∂(volume : Measure Ω) := by
      unfold slotProj1
      rw [show (∫ w : Ω, PV e (x j) w * aPC ℓ i Ψ' (Function.update x j w))
          = ∫ w : Ω, ((1 / ℓ ^ 3 : ℝ) : ℂ) *
              (PV e (x j) w *
                ∫ y in Submission.BoseGases.acube ℓ,
                  Ψ' (Function.update (Function.update x j w) i y)) from by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with w
        unfold aPC
        ring]
      rw [MeasureTheory.integral_const_mul]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [show (∫ y, F w y ∂((volume : Measure Ω).restrict (Submission.BoseGases.acube ℓ)))
          = ∫ y in Submission.BoseGases.acube ℓ,
              PV e (x j) w * Ψ' (Function.update (Function.update x j w) i y) from
        integral_congr_ae (Filter.Eventually.of_forall fun y => hFdef w y)]
      rw [MeasureTheory.integral_const_mul]
    rw [hL, hR, hswap]
  -- ## 2c. Transfer to `Ψ` and assemble
  have hΨeq' : Ψ' =ᵐ[(volume : Measure (Fin (n + 1) → Ω))] Ψ := hΨeq.symm
  have hcong1 : (fun x => aPC ℓ i (slotProj1 e j Ψ) x)
      =ᵐ[(volume : Measure (Fin (n + 1) → Ω))]
      (fun x => aPC ℓ i (slotProj1 e j Ψ') x) :=
    aPC_congr_ae_of_ae_eq i (slotProj1_congr_ae_of_ae_eq e j hΨeq)
  have hcong2 : (fun x => slotProj1 e j (aPC ℓ i Ψ') x)
      =ᵐ[(volume : Measure (Fin (n + 1) → Ω))]
      (fun x => slotProj1 e j (aPC ℓ i Ψ) x) :=
    slotProj1_congr_ae_of_ae_eq e j (aPC_congr_ae_of_ae_eq i hΨeq')
  have hmid : (fun x => aPC ℓ i (slotProj1 e j Ψ') x)
      =ᵐ[(volume : Measure (Fin (n + 1) → Ω))]
      (fun x => slotProj1 e j (aPC ℓ i Ψ') x) :=
    Filter.Eventually.of_forall hpoint
  exact hcong1.trans (hmid.trans hcong2)

end Work.BoseBoxFock

end

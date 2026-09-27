import Mathlib
import Submission.Work.EKLC6Core.UBoxDef
import Submission.Work.EKLC6Core.log_mass_conjBox_eq_sum
import Submission.Work.EKLC6Core.box_UBox_comparison
import Submission.Work.EKLComp.prove_Birkhoff

/-!
# `EKLC6Core.box_mass_asymptotic_condExp` — Pisa 7.18 for an `A`-invariant (not ergodic) `μ`

This is the non-ergodic counterpart of `Work.EKLC6Core.box_mass_asymptotic` (which assumes
`A`-ergodicity): for an `A`-invariant probability `μ` the exponential growth rate of the masses
of the conjugated entry boxes is the *conditional expectation* of the pointwise information
`growthFun (Uminus t) ν t` with respect to the σ-algebra of invariants of the `aDiag t`-action:

`(1/n) log ν x (aDiag (-n t) · UBox U R · aDiag (n t)) → E[growthFun | invariants (aDiag t ·)] x`
for `μ`-a.e. `x` and every `R ≥ 1`.

The proof is the same Birkhoff-average computation as in `box_mass_asymptotic`
(Pisa 7.16 + 7.18: the boxes telescope along the orbit), with `Work.EKLComp.birkhoff_all`
supplying the pointwise limit `condExp (invariants T) μ g` directly, instead of using ergodicity
to identify it with a constant.  In particular no invariance of the limit is needed: the
entrywise box `conjBy (-n t) (UBox U R)` is sandwiched between the two *conjugated boxes*
`conjBox U (-n t)` and `conjBox U (-(n+K) t)`, and both logarithmic masses have the same
Birkhoff average as limit.

The elementary helpers below (`bmce_logMass`, `bmce_log_mass_le`, …) are local copies of the
corresponding tools of `box_mass_asymptotic`; they are repeated here so that this module does
not depend on that one.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Local tools (copies of the elementary box calculus) -/

/-- The logarithm of the `ν x`-mass of the conjugated box `conjBox (Uminus t) w`. -/
def bmce_logMass (t : Fin 3 → ℝ) (ν : X3 → Measure SL3) (w : Fin 3 → ℝ) (x : X3) : ℝ :=
  Real.log ((ν x (conjBox (Uminus t) w)).toReal)

/-- The `UBox`-box of a leaf-wise system is compact, hence has finite `ν x`-mass. -/
theorem bmce_isCompact_conjBy_UBox (t : Fin 3 → ℝ) {R : ℝ} (hR : 0 ≤ R) (w : Fin 3 → ℝ) :
    IsCompact (conjBy w (UBox (Uminus t) R)) :=
  (isCompact_UBox (U := Uminus t) (uminus_isHoro t).1.1 hR).image
    ((continuous_const.mul continuous_id).mul continuous_const)

/-- Logarithmic monotonicity of box masses: if `B₁^U ⊆ A ⊆ B` and `B` has finite `ν x`-mass,
then `log ν x A ≤ log ν x B`. -/
theorem bmce_log_mass_le {μ : Measure X3} {ν : X3 → Measure SL3} {X' : Set X3}
    {t : Fin 3 → ℝ} (hL : IsLeafwise μ (Uminus t) ν X') {x : X3} (hx : x ∈ X')
    {A B : Set SL3} (hAB : A ⊆ B) (hA : Box1 (Uminus t) ⊆ A) (hBfin : ν x B < ⊤) :
    Real.log ((ν x A).toReal) ≤ Real.log ((ν x B).toReal) := by
  have hmono : ν x A ≤ ν x B := measure_mono hAB
  have hAfin : ν x A < ⊤ := lt_of_le_of_lt hmono hBfin
  have h1 : (1 : ℝ≥0∞) ≤ ν x A := by
    rw [← hL.normalised x hx]
    exact measure_mono hA
  have hpos : (0 : ℝ) < (ν x A).toReal := by
    have h2 : (1 : ℝ) ≤ (ν x A).toReal := by
      simpa using ENNReal.toReal_mono hAfin.ne h1
    linarith
  exact Real.log_le_log hpos (ENNReal.toReal_mono hBfin.ne hmono)

/-- `B₁^U` sits inside every box with a non-positive parameter. -/
theorem bmce_box1_subset_conjBox_neg_nsmul (t : Fin 3 → ℝ) (n : ℕ) :
    Box1 (Uminus t) ⊆ conjBox (Uminus t) (-(((n : ℝ)) • t)) := by
  have hmono := box_facts_monotone (uminus_isHoro t).1 (uminus_isHoro t).2 (Nat.zero_le n)
  simpa using hmono

/-- A Cesàro-shift lemma: if the averages `m⁻¹ Σ_{j<m} u j` converge to `a`, so do the averages
along a sequence `φ` with `φ n → ∞` and `φ n / n → 1`. -/
theorem bmce_tendsto_inv_mul_sum_shift {u : ℕ → ℝ} {a : ℝ} {φ : ℕ → ℕ}
    (hu : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * ∑ j ∈ Finset.range m, u j) atTop (𝓝 a))
    (hφtop : Tendsto φ atTop atTop)
    (hφratio : Tendsto (fun n : ℕ => (φ n : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (φ n), u j) atTop (𝓝 a) := by
  have hA : Tendsto (fun n : ℕ => (φ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (φ n), u j) atTop (𝓝 a) :=
    hu.comp hφtop
  have hprod : Tendsto (fun n : ℕ =>
      ((φ n : ℝ) * (n : ℝ)⁻¹) * ((φ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (φ n), u j))
      atTop (𝓝 (1 * a)) := hφratio.mul hA
  rw [one_mul] at hprod
  refine hprod.congr' (Eventually.of_forall fun n => ?_)
  by_cases h : φ n = 0
  · simp [h]
  · have hφ : (φ n : ℝ) ≠ 0 := by exact_mod_cast h
    calc ((φ n : ℝ) * (n : ℝ)⁻¹) * ((φ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (φ n), u j)
        = ((φ n : ℝ) * (φ n : ℝ)⁻¹) * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range (φ n), u j) := by
          ring
      _ = (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (φ n), u j := by rw [mul_inv_cancel₀ hφ, one_mul]

/-! ## The main theorem -/

theorem box_mass_asymptotic_condExp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    {R : ℝ} (hR : 2 ≤ R) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log ((ν x (Work.EKLC6Core.conjBy
        (-(((n : ℝ)) • t)) (Work.EKLC6Core.UBox (Work.EKLC6Core.Uminus t) R))).toReal))
      Filter.atTop (nhds (MeasureTheory.condExp (MeasurableSpace.invariants
        (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)) μ
        (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) x)) := by
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  set g : X3 → ℝ := growthFun (Uminus t) ν t with hg
  set T : X3 → X3 := fun x => aDiag t • x with hT
  have hmp : MeasurePreserving T μ μ := hAinv t
  set L : X3 → ℝ := condExp (MeasurableSpace.invariants T) μ g with hLdef
  have hBox1UBox : Box1 (Uminus t) ⊆ UBox (Uminus t) R := (box_UBox_comparison t hR1).1
  obtain ⟨KU, hKU⟩ := (box_UBox_comparison t hR1).2
  -- the a.e. orbit conditions
  have haeX' : ∀ᵐ x ∂μ, x ∈ X' :=
    MeasureTheory.ae_iff.mpr (by simpa [Set.compl_def] using hL.conull)
  have haeX'' : ∀ᵐ x ∂μ, x ∈ X'' :=
    MeasureTheory.ae_iff.mpr (by simpa [Set.compl_def] using hX'')
  have haeX : ∀ᵐ x ∂μ, x ∈ X' ∩ X'' := haeX'.and haeX''
  have hae_orbit : ∀ᵐ x ∂μ, ∀ j : ℕ, aDiag (((j : ℝ)) • t) • x ∈ X' ∩ X'' := by
    refine MeasureTheory.ae_all_iff.mpr (fun j => ?_)
    exact (hAinv (((j : ℝ)) • t)).quasiMeasurePreserving.ae haeX
  -- (A) the telescoping identity
  have htel : ∀ᵐ x ∂μ, ∀ n : ℕ, bmce_logMass t ν (-(((n : ℝ)) • t)) x
      = ∑ j ∈ Finset.range n, g (T^[j + 1] x) := by
    refine MeasureTheory.ae_all_iff.mpr (fun n => ?_)
    filter_upwards [hae_orbit] with x hx
    have h := log_mass_conjBox_eq_sum t hL hcov n x (fun j _ => hx j)
    rw [show bmce_logMass t ν (-(((n : ℝ)) • t)) x
        = Real.log ((ν x (conjBox (Uminus t) (-(((n : ℝ)) • t)))).toReal) from rfl, h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hvec : (((j + 1 : ℕ) : ℝ) • t : Fin 3 → ℝ) = ((j : ℝ) + 1) • t := by
      rw [show (((j + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) by push_cast; ring]
    simp only [hg, hT]
    rw [iterate_aDiag, hvec]
  -- (B) the Birkhoff averages converge to `L`
  have hbirk : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA T g n x) atTop (𝓝 (L x)) := by
    filter_upwards [Work.EKLComp.birkhoff_all μ T hmp g hint] with x hx
    simpa [L] using hx
  -- (C) the shifted averages
  have hAtend : ∀ᵐ x ∂μ,
      Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * ∑ j ∈ Finset.range m, g (T^[j + 1] x))
        atTop (𝓝 (L x)) := by
    filter_upwards [hbirk] with x hx
    have hsumid : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), g (T^[k] x)) - g x
        = ∑ j ∈ Finset.range n, g (T^[j + 1] x) := by
      intro n
      rw [Finset.sum_range_succ', Function.iterate_zero_apply]
      ring
    have hinv0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g (T^[k] x))
        atTop (𝓝 (L x)) := by
      have hbirk' : Tendsto (fun n : ℕ => Work.EKLComp.Birkhoff.birkA T g (n + 1) x)
          atTop (𝓝 (L x)) := hx.comp (tendsto_add_atTop_nat 1)
      have hratio : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
        have h2 : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add hinv0
        rw [add_zero] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      have hprod : Tendsto (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹) * Work.EKLComp.Birkhoff.birkA T g (n + 1) x)
          atTop (𝓝 (1 * L x)) := hratio.mul hbirk'
      rw [one_mul] at hprod
      have heq : (fun n : ℕ =>
            (((n + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹) * Work.EKLComp.Birkhoff.birkA T g (n + 1) x)
          = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g (T^[k] x)) := by
        funext n
        rw [Work.EKLComp.Birkhoff.birkA_def]
        by_cases hn : n = 0
        · subst hn; simp
        · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
          have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          field_simp
      rw [heq] at hprod
      exact hprod
    have h2 : Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * (∑ k ∈ Finset.range (n + 1), g (T^[k] x)) - (n : ℝ)⁻¹ * g x)
        atTop (𝓝 (L x)) := by
      have h := h1.sub (hinv0.mul_const (g x))
      simpa using h
    have heq2 : (fun n : ℕ => (n : ℝ)⁻¹ * (∑ k ∈ Finset.range (n + 1), g (T^[k] x))
          - (n : ℝ)⁻¹ * g x)
        = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, g (T^[j + 1] x)) := by
      funext n
      rw [← mul_sub, hsumid n]
    rw [heq2] at h2
    exact h2
  -- (D) rewrite the telescoping identity in `bmce_logMass` form
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-(((n : ℝ)) • t)) x)
        atTop (𝓝 (L x)) := by
    filter_upwards [hAtend, htel] with x hA ht
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-(((n : ℝ)) • t)) x)
        = (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, g (T^[j + 1] x)) := by
      funext n
      rw [ht n]
    rw [← heq] at hA
    exact hA
  -- (E) the `KU`-shift of the same limit
  have hlimS : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-((((n + KU : ℕ) : ℝ)) • t)) x)
        atTop (𝓝 (L x)) := by
    filter_upwards [hAtend, htel] with x hA ht
    have hinv0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hφtop : Tendsto (fun n : ℕ => n + KU) atTop atTop := tendsto_add_atTop_nat KU
    have hφratio : Tendsto (fun n : ℕ => (((n + KU : ℕ) : ℝ)) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => 1 + (KU : ℝ) * (n : ℝ)⁻¹) atTop
          (𝓝 (1 + (KU : ℝ) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul hinv0)
      rw [mul_zero, add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
      rw [Nat.cast_add]
      field_simp
    have hmain := bmce_tendsto_inv_mul_sum_shift hA hφtop hφratio
    have heq : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + KU), g (T^[j + 1] x))
        = (fun n : ℕ => (n : ℝ)⁻¹ * bmce_logMass t ν (-((((n + KU : ℕ) : ℝ)) • t)) x) := by
      funext n
      rw [ht (n + KU)]
    rw [heq] at hmain
    exact hmain
  -- (F) the final sandwich with the `UBox`-box
  have hsubLow : ∀ n : ℕ, conjBox (Uminus t) (-(((n : ℝ)) • t))
      ⊆ conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R) :=
    fun n => conjBy_mono (-(((n : ℝ)) • t)) hBox1UBox
  have hsubUp : ∀ n : ℕ, conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R)
      ⊆ conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t)) := by
    intro n
    have hstep : UBox (Uminus t) R ⊆ conjBox (Uminus t) (-(((KU : ℕ) : ℝ) • t)) := by
      have h := conjBy_mono (-(((KU : ℕ) : ℝ) • t)) (hKU KU le_rfl)
      rwa [conjBy_neg_conjBy] at h
    have h2 := conjBy_mono (-(((n : ℝ)) • t)) hstep
    have h3 : conjBy (-(((n : ℝ)) • t)) (conjBox (Uminus t) (-(((KU : ℕ) : ℝ) • t)))
        = conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t)) := by
      rw [← conjBox_add]
      congr 1
      ext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rwa [h3] at h2
  filter_upwards [haeX, hlim, hlimS] with x hxX hxlim hxupU
  have hgoal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log
      ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R))).toReal)) atTop (𝓝 (L x)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hxlim hxupU ?_ ?_
    · filter_upwards with n
      have hfin : ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R)) < ⊤ :=
        (hL.radon x hxX.1).lt_top_of_isCompact (bmce_isCompact_conjBy_UBox t hR0 _)
      have hle := bmce_log_mass_le hL hxX.1 (hsubLow n)
        (bmce_box1_subset_conjBox_neg_nsmul t n) hfin
      have hle' : Real.log ((ν x (conjBox (Uminus t) (-(((n : ℝ)) • t)))).toReal)
          ≤ Real.log ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R))).toReal) := hle
      exact mul_le_mul_of_nonneg_left hle' (inv_nonneg.mpr (Nat.cast_nonneg n))
    · filter_upwards with n
      have hfin : ν x (conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t))) < ⊤ :=
        (conjBox_mass_pos hL hU _ hxX.1).2
      have hA : Box1 (Uminus t) ⊆ conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R) :=
        (bmce_box1_subset_conjBox_neg_nsmul t n).trans (hsubLow n)
      have hle := bmce_log_mass_le hL hxX.1 (hsubUp n) hA hfin
      have hle' : Real.log ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) R))).toReal)
          ≤ Real.log ((ν x (conjBox (Uminus t) (-((((n + KU : ℕ) : ℝ)) • t)))).toReal) := hle
      exact mul_le_mul_of_nonneg_left hle' (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact hgoal

end Work.EKLC6Core

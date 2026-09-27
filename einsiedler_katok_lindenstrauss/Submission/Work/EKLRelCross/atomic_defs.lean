import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.box_iInter_conjBox
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.box_facts
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.dirac_of_mass
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLProd.aDiag_nsmul

/-!
# `Work.EKLRelCross.atomic_defs` — vocabulary for the atomic case of the ergodic dichotomy

This module collects the definitions and the *elementary* (algebraic) lemmas used by
`Work.EKLRelCross.atomic_trivial_of_covariant`: the conjugating maps
`Ψ_n = (aDiag t₀ⁿ)⁻¹ · · (aDiag t₀ⁿ)` along the negative `aDiag t₀`-orbit, their entry formula,
and the identification of the preimage of the box `Box1 U` with the conjugated box
`conjBox U (n t₀)`.

It also supplies *sorry-free* versions (`conjBox_subset_box1`, `box1_subset_conjBox_neg`) of the
two inclusions stated by `Work.EKLC6Core.box_conjBox_subset` (that file still contains a
`sorry`), so that consumers do not inherit `sorryAx`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- `Ψ_n (g) = (aDiag t₀ⁿ)⁻¹ · g · aDiag t₀ⁿ`, conjugation by the inverse power of the diagonal
element.  This is the map under which the `A`-covariance transports `ν x` to
`ν ((aDiag t₀ⁿ)⁻¹ • x)`. -/
def relPsi (t0 : Fin 3 → ℝ) (n : ℕ) : SL3 → SL3 :=
  fun g => (aDiag t0 ^ n)⁻¹ * g * aDiag t0 ^ n

/-- `Ψ_n` is also conjugation by `aDiag (-(n t₀))`. -/
lemma relPsi_eq_aDiag (t0 : Fin 3 → ℝ) (n : ℕ) (g : SL3) :
    relPsi t0 n g = aDiag (-(((n:ℝ)) • t0)) * g * (aDiag (-(((n:ℝ)) • t0)))⁻¹ := by
  unfold relPsi
  rw [Work.EKLC6Core.aDiag_neg_real_nsmul t0 n, inv_inv]

/-- **Entry formula.**  `Ψ_n` multiplies the `(i,j)`-entry by `e^{n(t₀ⱼ - t₀ᵢ)}`. -/
lemma relPsi_apply (t0 : Fin 3 → ℝ) (n : ℕ) (g : SL3) (i j : Fin 3) :
    (relPsi t0 n g : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp ((n:ℝ) * (t0 j - t0 i)) * (g : Matrix (Fin 3) (Fin 3) ℝ) i j :=
  Work.EKLC6Core.boxi_conj_pow_apply_inv t0 n g i j

lemma continuous_relPsi (t0 : Fin 3 → ℝ) (n : ℕ) : Continuous (relPsi t0 n) := by
  unfold relPsi; fun_prop

lemma measurable_relPsi (t0 : Fin 3 → ℝ) (n : ℕ) : Measurable (relPsi t0 n) :=
  (continuous_relPsi t0 n).measurable

/-- The preimage of the box `Box1 U` under `Ψ_n` is the conjugated box `conjBox U (n t₀)`. -/
lemma relPsi_preimage_box1 (U : Subgroup SL3) (t0 : Fin 3 → ℝ) (n : ℕ) :
    relPsi t0 n ⁻¹' (Box1 U) = Work.EKLC6Core.conjBox U (((n:ℝ)) • t0) := by
  have h := Work.EKLC6Core.preimage_conj_neg (((n:ℝ)) • t0) (Box1 U)
  have hfun : relPsi t0 n
      = fun g => aDiag (-(((n:ℝ)) • t0)) * g * (aDiag (-(((n:ℝ)) • t0)))⁻¹ :=
    funext (relPsi_eq_aDiag t0 n)
  rw [hfun]
  exact h

/-- Conjugation by `aDiag t` multiplies the entry `(i,j)` by `e^{tᵢ - tⱼ}`. -/
lemma conjBy_entry (t : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    (aDiag t * g * (aDiag t)⁻¹ : SL3) i j = Real.exp (t i - t j) * g i j :=
  Work.EKLC6Core.boxi_conj_apply t g i j

/-! ## The two box inclusions, without `sorry` -/

/-- **Contraction shrinks the box.**  If `t` contracts `U` then `conjBox U t ⊆ Box1 U`. -/
lemma conjBox_subset_box1 {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) :
    Work.EKLC6Core.conjBox U t ⊆ Box1 U := by
  rintro g ⟨h, hh, rfl⟩
  refine ⟨hU.2.1 t h hh.1, fun i j => ?_⟩
  rw [conjBy_entry]
  by_cases hij : i = j
  · subst hij
    rw [sub_self, Real.exp_zero, one_mul, Matrix.one_apply_eq]
    have h1 := hh.2 i i
    rw [Matrix.one_apply_eq] at h1
    exact h1
  · rw [Matrix.one_apply_ne hij, sub_zero]
    by_cases hle : t j ≤ t i
    · have hzero : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
      rw [Work.EKLC6Core.box_facts_entry_eq_one hcontr hh.1 hle, hzero, mul_zero, abs_zero]
      norm_num
    · have hhab : |(h : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
        have h1 := hh.2 i j
        rw [Matrix.one_apply_ne hij, sub_zero] at h1
        exact h1
      have hlt' : t i < t j := not_le.mp hle
      calc |Real.exp (t i - t j) * (h : Matrix (Fin 3) (Fin 3) ℝ) i j|
          = Real.exp (t i - t j) * |(h : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (t i - t j) * 1 := by gcongr
        _ = Real.exp (t i - t j) := mul_one _
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

/-- **Expansion enlarges the box.**  If `t` contracts `U` then `Box1 U ⊆ conjBox U (-t)`. -/
lemma box1_subset_conjBox_neg {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) :
    Box1 U ⊆ Work.EKLC6Core.conjBox U (-t) := by
  intro g hg
  rw [Work.EKLC6Core.conjBox, Work.EKLC6Core.conjBy, Set.mem_image]
  refine ⟨aDiag t * g * (aDiag t)⁻¹, ⟨hU.2.1 t g hg.1, ?_⟩, ?_⟩
  · intro i j
    rw [conjBy_entry]
    by_cases hij : i = j
    · subst hij
      rw [sub_self, Real.exp_zero, one_mul, Matrix.one_apply_eq]
      have h1 := hg.2 i i
      rw [Matrix.one_apply_eq] at h1
      exact h1
    · rw [Matrix.one_apply_ne hij, sub_zero]
      by_cases hle : t j ≤ t i
      · have hzero : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
        rw [Work.EKLC6Core.box_facts_entry_eq_one hcontr hg.1 hle, hzero, mul_zero, abs_zero]
        norm_num
      · have hhab : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
          have h1 := hg.2 i j
          rw [Matrix.one_apply_ne hij, sub_zero] at h1
          exact h1
        have hlt' : t i < t j := not_le.mp hle
        calc |Real.exp (t i - t j) * (g : Matrix (Fin 3) (Fin 3) ℝ) i j|
            = Real.exp (t i - t j) * |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          _ ≤ Real.exp (t i - t j) * 1 := by gcongr
          _ = Real.exp (t i - t j) := mul_one _
          _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  · have h1 : aDiag (-t) * aDiag t = 1 := aDiag_neg_mul t
    calc aDiag (-t) * (aDiag t * g * (aDiag t)⁻¹) * (aDiag (-t))⁻¹
        = (aDiag (-t) * aDiag t) * g * (aDiag (-t) * aDiag t)⁻¹ := by group
      _ = g := by rw [h1]; group

/-- The decreasing family `n ↦ conjBox U (n t)` (a consequence of `conjBox U t ⊆ Box1 U`). -/
lemma conjBox_antitone {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) :
    Antitone (fun n : ℕ => Work.EKLC6Core.conjBox U (((n:ℝ)) • t)) := by
  have hsub : Work.EKLC6Core.conjBox U t ⊆ Box1 U := conjBox_subset_box1 hU hcontr
  apply antitone_nat_of_succ_le
  intro n
  have hvec : ((((n + 1 : ℕ) : ℝ)) • t) = (n : ℝ) • t + t := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    push_cast
    ring
  calc Work.EKLC6Core.conjBox U ((((n + 1 : ℕ) : ℝ)) • t)
      = Work.EKLC6Core.conjBy ((n : ℝ) • t) (Work.EKLC6Core.conjBox U t) := by
        rw [hvec, Work.EKLC6Core.conjBox_add]
    _ ⊆ Work.EKLC6Core.conjBy ((n : ℝ) • t) (Box1 U) :=
        Work.EKLC6Core.conjBy_mono _ hsub
    _ = Work.EKLC6Core.conjBox U (((n:ℝ)) • t) := rfl

/-- The conjugated boxes `conjBox U (n t)` shrink to `{1}`. -/
lemma conjBox_iInter_eq_singleton {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) :
    (⋂ n : ℕ, Work.EKLC6Core.conjBox U (((n:ℝ)) • t)) = {1} :=
  Work.EKLC6Core.box_iInter_conjBox hU hcontr

end Work.EKLRelCross

end

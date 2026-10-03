/-
# The unconditional (`l₂ = 0`) single-scale estimate of the mixed right case

Target: `Work.KMTPlan.A6.BoundedHMain.loMixedRSingleScaleUncond`, the paper's §6 model
approximation (`mod-approx`) at the arithmetic heights `(l₁, 0)`, `l₁ ≥ 1`, in the *unconditional*
form

  `‖ mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n ‖_{ℓ^p} ≤ C(Λ) · modelWeight A ρ l₁ 0 k₁ k₂ ·
      ⌊a n⌋⁻¹ · ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,   `p = (p₁⁻¹+p₂⁻¹)⁻¹`,

with **no** `AreaA1` hypothesis, for **every** `ρ ∈ (0,1]` (not only `ρ ≤ ρ₀`), and with an
exponent `A` that is **uniform** in `C₀` and in `ρ`.

This is the `∀ ρ ≤ 1` / uniform-`A` strengthening of
`Work.KMTAreas.A7.LoMixedRSingleScale` (`LoMixedRSingleScaleStatement`), whose chain
(`LoAbsorb`, `LoMixedRMass`, `LoMixedRSingleScaleOfMass`) is formalised in the workspace but
carries an explicit `ρ₀` in its statements.  The strengthening is *already* in the mathematics of
that chain: `Work.KMTAreas.A7.AbsorbHolds` and `Work.KMTAreas.A7.LoAbsorb` prove the absorption
of the arithmetic factors with the *fixed* exponent `A = 2`, valid for all `0 < ρ ≤ 1` (their
proofs only use `0 < ρ` and `ρ ≤ 1`; the `ρ₀` of their *statements* is an artifact, instantiated to
`1` inside the proofs), and `Work.KMTAreas.A7.LoFibreMass` is completely `ρ`-free.  Accordingly:

* `absorbAux` below — the absorption, re-stated for all `ρ ≤ 1` (the body is that of
  `Work.KMTAreas.A7.AbsorbHolds`, with the threshold of the statement specialised to `1`);
* `rmassAux` — the resulting `ℓ¹(ℤ²)` mass bound, re-stated for all `ρ ≤ 1` (the body is that of
  `Work.KMTAreas.A7.loMixedRMass_of`, whose two uses of the threshold — `ρ ≤ ρ₀` and `ρ ≤ 1` —
  are here merged into the single hypothesis `ρ ≤ 1`);
* `loMixedRSingleScaleAll` — the `ℓ^p` bookkeeping of
  `Work.KMTAreas.A7.LoMixedRSingleScaleOfMass`, which uses neither `AreaA1` nor the smallness of
  `ρ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedRSingleScaleOfMass
import Submission.Work.KMTAreas.A7.AbsorbHolds

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.BoundedHMain

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-- **The `l₂ = 0` single-scale `ℓ¹(ℤ²)` mass bound for *every* `ρ ∈ (0,1]`, with a uniform
exponent.**

This is `Work.KMTAreas.A7.LoMixedRMassStatement` with the existential `ρ₀` replaced by `1`.  It is
the form of the §6 `mod-approx` mass bound consumed by the `ℓ^p` bookkeeping below. -/
def LoMixedRMassAll (P : Polynomial ℤ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ≥0 → ℝ≥0,
    (∀ (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ k₁ k₂ : ℕ) (n : ℕ),
        loGuard ρ C₀ a l₁ 0 k₁ k₂ n →
        Summable fun p : ℤ × ℤ => ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
            - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖) ∧
    (∀ (C₀ : ℕ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ k₁ k₂ : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        1 ≤ l₁ →
        ∀ n : ℕ, loGuard ρ C₀ a l₁ 0 k₁ k₂ n →
          (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
              - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            ≤ (C Λ : ℝ) * modelWeight A ρ l₁ 0 k₁ k₂ * ((Nat.floor (a n) : ℕ) : ℝ)⁻¹)

/-- **Absorption of the arithmetic factors of the mass bound, uniformly in `ρ ∈ (0,1]`.**

The arithmetic factors `#(ℚ/ℤ)_{≤l₁} · q² · (1 + Sval²) · 2^{k₁+dk₂}` of the per-fibre mass bound
are absorbed into `modelWeight A ρ l₁ 0 k₁ k₂` with the *fixed* exponent `A = 2`, for every
`0 < ρ ≤ 1`.  (`mag-lem`(ii),(iii), i.e. `iw_height_card_le` and the sharp element bound
`iwP_element_le_sharp`; body of `Work.KMTAreas.A7.AbsorbHolds` with the threshold set to `1`.) -/
theorem absorbAux (P : Polynomial ℤ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ q k₁ k₂ : ℕ), q ∈ iwP ρ l₁ →
        ((iwArithFreqs ρ l₁).card : ℝ) * (q : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
        ≤ C * modelWeight A ρ l₁ 0 k₁ k₂ := by
  refine ⟨2, by norm_num, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C₂₀, hC₂₀pos, hC₂₀⟩ := Work.Analysis.IonescuWainger.iw_height_card_le hρ
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.KMTPlan.A6.iwP_element_le_sharp ρ hρ hρ1
  set C₂ : ℝ := max 1 C₂₀ with hC₂def
  have hC₂1 : (1:ℝ) ≤ C₂ := le_max_left _ _
  have hC₂pos : (0:ℝ) < C₂ := lt_of_lt_of_le one_pos hC₂1
  have hC₂ : ∀ l : ℕ, ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)
      ≤ C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l:ℝ))) := fun l =>
    (hC₂₀ l).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hCqnn : (0:ℝ) ≤ Cq := hCqpos.le
  obtain ⟨K, hK0, hK⟩ := exp_dominates_poly_half ρ hρ hρ1 (2*Cq) (3*((P.natDegree:ℝ)+1)) 4
      (by positivity) (by positivity) (by norm_num)
  refine ⟨C₂ * (2:ℝ)^K, by positivity, ?_⟩
  intro l₁ q k₁ k₂ hq
  set Ln : ℕ := max (max l₁ k₁) k₂ with hLndef
  have hl₁ : l₁ ≤ Ln := by rw [hLndef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hk₁ : k₁ ≤ Ln := by rw [hLndef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hk₂ : k₂ ≤ Ln := by rw [hLndef]; exact le_max_right _ _
  set X : ℝ := Cq * (1 + (l₁:ℝ) * (2:ℝ)^(ρ*(l₁:ℝ)/2) + (l₁:ℝ)) with hXdef
  have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
      ≤ C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ))) := hC₂ l₁
  have hqR : (q:ℝ) ≤ (2:ℝ)^X := by rw [hXdef]; exact hCq l₁ q hq
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast Work.Analysis.IonescuWainger.pos_of_mem_iwP hq
  have hq2 : (q:ℝ)^2 ≤ (2:ℝ)^(2*X) := by
    have h := pow_le_pow_left₀ hqpos.le hqR 2
    rwa [show ((2:ℝ)^X)^2 = (2:ℝ)^(2*X) from by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring] at h
  have hsv : (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := sval_term_bound P Ln k₁ k₂ hk₁ hk₂
  have hstep1 : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2
        * (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X)
        * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := by
    rw [show ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2
          * (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
        = (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2)
          * ((1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)) from by ring]
    refine mul_le_mul (mul_le_mul hcard hq2 (by positivity) (by positivity)) hsv
      (by positivity) (by positivity)
  have hp1 : (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ))) * (2:ℝ)^(2*X)
      = (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X) :=
    (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
  have hp2 : (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X) * (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ))
      = (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) :=
    (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
  have hnat : (2:ℝ)^(3*(P.natDegree+1)*Ln + 4)
      = (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ)) :=
    (Real.rpow_natCast (2:ℝ) _).symm
  have hEeq : (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X)
        * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4)
      = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) := by
    calc (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X) * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4)
        = C₂ * ((2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ))) * (2:ℝ)^(2*X)) * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := by
          ring
      _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X) * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := by rw [hp1]
      _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X)
            * (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ)) := by rw [hnat]
      _ = C₂ * ((2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X)
            * (2:ℝ)^(((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ))) := by ring
      _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) := by
          rw [hp2]
  have hcast : (((3*(P.natDegree+1)*Ln + 4 : ℕ) : ℝ))
      = 3*((P.natDegree:ℝ)+1)*(Ln:ℝ) + 4 := by push_cast; ring
  have hexp : (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ))
      ≤ (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)) + K) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    have h1 : (2:ℝ)^(ρ*(l₁:ℝ)) ≤ (2:ℝ)^(ρ*(Ln:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have h : (l₁:ℝ) ≤ (Ln:ℝ) := by exact_mod_cast hl₁
        nlinarith [hρ])
    have h2 : 2*X ≤ 2*Cq*(1 + (Ln:ℝ)*(2:ℝ)^(ρ*(Ln:ℝ)/2) + (Ln:ℝ)) := by
      rw [hXdef]
      have hl₁R : (l₁:ℝ) ≤ (Ln:ℝ) := by exact_mod_cast hl₁
      have hy : (2:ℝ)^(ρ*(l₁:ℝ)/2) ≤ (2:ℝ)^(ρ*(Ln:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ])
      have hprod : (l₁:ℝ) * (2:ℝ)^(ρ*(l₁:ℝ)/2) ≤ (Ln:ℝ) * (2:ℝ)^(ρ*(Ln:ℝ)/2) :=
        mul_le_mul hl₁R hy (by positivity) (by positivity)
      have h1' : 1 + (l₁:ℝ) * (2:ℝ)^(ρ*(l₁:ℝ)/2) + (l₁:ℝ)
          ≤ 1 + (Ln:ℝ) * (2:ℝ)^(ρ*(Ln:ℝ)/2) + (Ln:ℝ) := by linarith
      nlinarith [h1', hCqnn]
    have h3 := hK Ln
    rw [hcast]
    linarith [h1, h2, h3]
  have hfinal : (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)) + K)
      = (2:ℝ)^K * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ))) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    ring
  have hmodel : Work.KMTAreas.A7.modelWeight 2 ρ l₁ 0 k₁ k₂
      = ((1+(Ln:ℝ))^(2:ℝ)) * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ))) := by
    simp only [Work.KMTAreas.A7.modelWeight, lmaxR_zero_l2, ← hLndef]
  have h1sq : (1:ℝ) ≤ (1+(Ln:ℝ))^(2:ℝ) :=
    Real.one_le_rpow (by linarith : (1:ℝ) ≤ 1 + (Ln:ℝ)) (by norm_num)
  calc ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q:ℝ)^2
        * (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)))) * (2:ℝ)^(2*X)
        * (2:ℝ)^(3*(P.natDegree+1)*Ln + 4) := hstep1
    _ = C₂ * (2:ℝ)^((2:ℝ)^(ρ*(l₁:ℝ)) + 2*X + ((3*(P.natDegree+1)*Ln + 4 : ℕ):ℝ)) := hEeq
    _ ≤ C₂ * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)) + K) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = C₂ * (2:ℝ)^K * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ))) := by rw [hfinal]; ring
    _ ≤ C₂ * (2:ℝ)^K * (((1+(Ln:ℝ))^(2:ℝ)) * (2:ℝ)^(2 * (2:ℝ)^(ρ*(Ln:ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_left (by positivity) h1sq
    _ = (C₂ * (2:ℝ)^K) * Work.KMTAreas.A7.modelWeight 2 ρ l₁ 0 k₁ k₂ := by
        rw [hmodel]

/-- **The `l₂ = 0` single-scale `ℓ¹(ℤ²)` mass bound for every `ρ ∈ (0,1]`.**

From the `ρ`-free per-fibre bound `Work.KMTAreas.A7.FibreMassStatement` and the all-`ρ` absorption
of `absorbAux`, the concrete kernel `hiKconc ρ P a l₁ 0 k₁ k₂ n` (the §6 model kernel vanishes at
`l₂ = 0`) is summable on the guard scales, with mass at most
`C(Λ) · modelWeight A ρ l₁ 0 k₁ k₂ · ⌊a n⌋⁻¹`, for every `0 < ρ ≤ 1`.  (Body of
`Work.KMTAreas.A7.loMixedRMass_of`: the dependence on the threshold enters only through
`ρ ≤ ρ₀` and `ρ ≤ 1`, which here collapse to the single hypothesis `ρ ≤ 1`.) -/
theorem rmassAux (P : Polynomial ℤ)
    (hF : Work.KMTAreas.A7.FibreMassStatement P)
    (hAbs : ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ q k₁ k₂ : ℕ), q ∈ iwP ρ l₁ →
        ((iwArithFreqs ρ l₁).card : ℝ) * (q : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
        ≤ C * modelWeight A ρ l₁ 0 k₁ k₂) :
    LoMixedRMassAll P := by
  classical
  obtain ⟨Cf, hCfpos, hFb⟩ := hF
  obtain ⟨A, hA0, hAb⟩ := hAbs
  have hCf0 : 0 ≤ Cf := hCfpos.le
  refine ⟨A, hA0, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨Ca, hCapos, hCab⟩ := hAb ρ hρ hρ1
  have hCa0 : 0 ≤ Ca := hCapos.le
  refine ⟨fun _ => ⟨Cf * Ca * 100, by positivity⟩, ?_, ?_⟩
  · intro C₀ a l₁ k₁ k₂ n _
    have hz : hiKmod ρ P a l₁ 0 k₁ k₂ n = 0 := hiKmod_lo2 ρ P a l₁ k₁ k₂ n
    rw [hz]
    simp only [Pi.zero_apply, sub_zero]
    exact summable_hiKconc ρ P a l₁ 0 k₁ k₂ n
  · intro C₀ a Λ l₁ k₁ k₂ _ _ ha1 hl₁ n _
    have hz : hiKmod ρ P a l₁ 0 k₁ k₂ n = 0 := hiKmod_lo2 ρ P a l₁ k₁ k₂ n
    have hc : hiKconc ρ P a l₁ 0 k₁ k₂ n = hiKconcN ρ P (Nat.floor (a n)) l₁ 0 k₁ k₂ :=
      hiKconc_eq ρ hρ hρ1 P a l₁ 0 k₁ k₂ n
    rw [hz, hc]
    simp only [Pi.zero_apply, sub_zero]
    set N : ℕ := Nat.floor (a n) with hNdef
    have hNpos : 0 < N := by
      rw [hNdef]
      exact Nat.floor_pos.mpr (by exact_mod_cast ha1 n)
    have hN1 : 1 ≤ N := by omega
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    set Γ : Finset Work.Analysis.IonescuWainger.Circle := diffFreqs ρ l₁ with hΓdef
    have hΓsub : ∀ α ∈ Γ, α ∈ iwArithFreqs ρ l₁ :=
      fun α hα => diffFreqs_subset_iwArithFreqs ρ l₁ hα
    have hne : ∀ α ∈ Γ, α ≠ (0 : Work.Analysis.IonescuWainger.Circle) := by
      intro α hα h0
      exact (hΓdef ▸ zero_not_mem_diffFreqs ρ hl₁) (h0 ▸ hα)
    have hqspec : ∀ α ∈ Γ, ∃ q : ℕ, q ∈ iwP ρ l₁ ∧ q • α = 0 :=
      fun α hα => mem_iwArithFreqs.mp (hΓsub α hα)
    let qα : Work.Analysis.IonescuWainger.Circle → ℕ :=
      fun α => if h : α ∈ Γ then (hqspec α h).choose else 1
    have hqα_mem : ∀ α (h : α ∈ Γ), qα α ∈ iwP ρ l₁ := by
      intro α h
      dsimp only [qα]
      rw [dif_pos h]
      exact (hqspec α h).choose_spec.1
    have hqα_smul : ∀ α (h : α ∈ Γ), qα α • α = 0 := by
      intro α h
      dsimp only [qα]
      rw [dif_pos h]
      exact (hqspec α h).choose_spec.2
    set Qmax : ℕ := (iwP ρ l₁).max' ⟨1, one_mem_iwP ρ l₁⟩ with hQmaxdef
    have hqα_le : ∀ α ∈ Γ, qα α ≤ Qmax := by
      intro α hα
      rw [hQmaxdef]
      exact Finset.le_max' _ _ (hqα_mem α hα)
    have hfibMass : ∀ α ∈ Γ,
        Summable (fun p : ℤ × ℤ => ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        ∧ (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
          ≤ Cf * (qα α : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) :=
      fun α hα => hFb N (qα α) k₁ k₂ α hN1 (pos_of_mem_iwP (hqα_mem α hα))
        (hqα_smul α hα) (hne α hα)
    have hstep1 : ∀ α ∈ Γ, (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        ≤ Cf * (Qmax : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) := by
      intro α hα
      refine (hfibMass α hα).2.trans ?_
      have hsq : (qα α : ℝ) ^ 2 ≤ (Qmax : ℝ) ^ 2 := by
        have h : (qα α : ℝ) ≤ (Qmax : ℝ) := by exact_mod_cast hqα_le α hα
        have h0 : (0 : ℝ) ≤ (qα α : ℝ) := by positivity
        nlinarith [h, h0]
      have hK0 : 0 ≤ (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) := by positivity
      have h20 : 0 ≤ (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by positivity
      have hA1 : Cf * (qα α : ℝ) ^ 2 ≤ Cf * (Qmax : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hCf0
      have hA2 : Cf * (qα α : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          ≤ Cf * (Qmax : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hA1 hK0
      have hA3 : Cf * (qα α : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
          ≤ Cf * (Qmax : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) :=
        mul_le_mul_of_nonneg_right hA2 h20
      exact div_le_div_of_nonneg_right hA3 hNposR.le
    have hstep2 : (∑ α ∈ Γ, Cf * (Qmax : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ))
        = (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hQmax_mem : Qmax ∈ iwP ρ l₁ := by
      rw [hQmaxdef]
      exact Finset.max'_mem _ _
    have hstep3 : (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ))
        ≤ Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂ * (N : ℝ)⁻¹ := by
      have hmod0 : 0 ≤ Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂ :=
        Work.KMTAreas.A7.modelWeight_nonneg A ρ hA0 l₁ 0 k₁ k₂
      have hQ0 : 0 ≤ (Qmax : ℝ) ^ 2 := sq_nonneg _
      have hP20 : 0 ≤ (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by positivity
      have hS20 : 0 ≤ (Work.A7.Sval P k₁ k₂) ^ 2 := sq_nonneg _
      have hS2div : (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) ≤ (Work.A7.Sval P k₁ k₂) ^ 2 := by
        rw [div_le_iff₀ hNposR]
        nlinarith [hS20, hN1R]
      have h1SN : (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          ≤ (1 + (Work.A7.Sval P k₁ k₂) ^ 2) := by linarith
      have hGc : (Γ.card : ℝ) ≤ ((iwArithFreqs ρ l₁).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hΓsub
      have hGc0 : (0 : ℝ) ≤ (Γ.card : ℝ) := Nat.cast_nonneg _
      have hIc0 : (0 : ℝ) ≤ ((iwArithFreqs ρ l₁).card : ℝ) := Nat.cast_nonneg _
      have hkey : (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))
          ≤ Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) := by
        have hg : (Γ.card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            ≤ ((iwArithFreqs ρ l₁).card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2) :=
          mul_le_mul hGc h1SN (by positivity) hIc0
        have e1 : (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))
            ≤ Cf * ((iwArithFreqs ρ l₁).card : ℝ) * (Qmax : ℝ) ^ 2
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by
          calc (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
                * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))
              = Cf * (Qmax : ℝ) ^ 2 * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
                * ((Γ.card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))) := by ring
            _ ≤ Cf * (Qmax : ℝ) ^ 2 * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
                * (((iwArithFreqs ρ l₁).card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)) :=
                mul_le_mul_of_nonneg_left hg (by positivity)
            _ = Cf * ((iwArithFreqs ρ l₁).card : ℝ) * (Qmax : ℝ) ^ 2
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
                * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by ring
        have e2 : Cf * ((iwArithFreqs ρ l₁).card : ℝ) * (Qmax : ℝ) ^ 2
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
            ≤ Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) := by
          have h := hCab l₁ Qmax k₁ k₂ hQmax_mem
          refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h hCf0)
          ring
        exact e1.trans e2
      calc (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ))
          = ((Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))) / (N : ℝ) := by ring
        _ ≤ (Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) * 100) / (N : ℝ) :=
            div_le_div_of_nonneg_right
              (hkey.trans (by
                have h0 : 0 ≤ Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) :=
                  mul_nonneg hCf0 (mul_nonneg hCa0 hmod0)
                nlinarith [h0])) hNposR.le
        _ = Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂ * (N : ℝ)⁻¹ := by
            rw [div_eq_mul_inv]; ring
    have hstepC : ∀ α ∈ Γ, (∑' p : ℤ × ℤ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖) :=
      fun α hα => (ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hfibMass α hα).1).symm
    have hstepB : (∑' p : ℤ × ℤ, ∑ α ∈ Γ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        = ∑ α ∈ Γ, ∑' p : ℤ × ℤ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖ :=
      Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    have hbig : (∑' p : ℤ × ℤ, ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖)
        ≤ ENNReal.ofReal (Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂
            * (N : ℝ)⁻¹) := by
      calc (∑' p : ℤ × ℤ, ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖)
          ≤ ∑' p : ℤ × ℤ, ∑ α ∈ Γ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖ := by
            refine ENNReal.tsum_le_tsum (fun p => ?_)
            refine le_trans (ENNReal.ofReal_le_ofReal
              (hiKconcN_fibre_lo2 ρ P N l₁ k₁ k₂ p.1 p.2)) ?_
            rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => norm_nonneg _)]
        _ = ∑ α ∈ Γ, ∑' p : ℤ × ℤ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖ := hstepB
        _ = ∑ α ∈ Γ, ENNReal.ofReal (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖) :=
            Finset.sum_congr rfl (fun α hα => hstepC α hα)
        _ = ENNReal.ofReal (∑ α ∈ Γ, ∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖) :=
            (ENNReal.ofReal_sum_of_nonneg (fun α _ =>
              tsum_nonneg (fun p => norm_nonneg _))).symm
        _ ≤ ENNReal.ofReal (Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂
              * (N : ℝ)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact (Finset.sum_le_sum hstep1).trans (hstep2.le.trans hstep3)
    have hsumKc : Summable (fun p : ℤ × ℤ => ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖) := by
      have hne : (∑' p : ℤ × ℤ, ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbig
      have h1 := ENNReal.summable_toReal (f := fun p : ℤ × ℤ =>
        ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖) hne
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using h1
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCf0 hCa0)
        (by norm_num)) (Work.KMTAreas.A7.modelWeight_nonneg A ρ hA0 l₁ 0 k₁ k₂))
        (inv_nonneg.mpr hNposR.le)
    · rw [ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) hsumKc]
      exact hbig

/-- **The unconditional single-scale estimate of the mixed right case** (the `ℓ^p` bookkeeping).

From the all-`ρ` `ℓ¹(ℤ²)` mass bound `LoMixedRMassAll P` one gets, for every `ρ ∈ (0,1]`, every
`l₁ ≥ 1` and all `f, g`,

  `‖ mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n ‖_{ℓ^p} ≤ C(Λ) · modelWeight A ρ l₁ 0 k₁ k₂ ·
      ⌊a n⌋⁻¹ ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,

with the exponent `A` of the mass bound (independent of `ρ` and `C₀`).  On the guard the column is
`bilinOp (hiKconc …) f g`, the §6 model kernel vanishes at `l₂ = 0`, `BilinOpLp` (Young) converts
the mass bound into the `ℓ^p` bound, and the two degenerate cases (`eLpNorm = ⊤` / `= 0`) are
handled separately. -/
theorem loMixedRSingleScaleAll (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) (hmass : LoMixedRMassAll P) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ≥0 → ℝ≥0,
        ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          1 ≤ l₁ → ∀ n : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  classical
  obtain ⟨A, hA, H⟩ := hmass
  refine ⟨A, hA, ?_⟩
  intro C₀ hC₀ ρ hρ hρ1
  obtain ⟨C, hsumm, hbound⟩ := H ρ hρ hρ1
  refine ⟨fun Λ => max (C Λ) 1, ?_⟩
  intro a Λ l₁ k₁ k₂ f g hΛ ha ha1 hl₁ n
  have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₁)
  have hp₂0 : p₂ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₂)
  have hN1 : 1 ≤ Nat.floor (a n) := Nat.floor_pos.mpr (ha1 n)
  have hw1 : (1 : ℝ) ≤ modelWeight A ρ l₁ 0 k₁ k₂ := by
    rw [modelWeight]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by linarith [lmaxR_nonneg l₁ 0 k₁ k₂]) hA)
      (Real.one_le_rpow (by norm_num) (by positivity))
  have hw0 : 0 ≤ modelWeight A ρ l₁ 0 k₁ k₂ := le_trans zero_le_one hw1
  have hCnn : (0 : ℝ) ≤ (C Λ : ℝ) := by positivity
  set Xe : ENNReal := ((max (C Λ) 1 : ℝ≥0) : ENNReal)
    * ENNReal.ofReal (modelWeight A ρ l₁ 0 k₁ k₂)
    * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹) with hXe
  have hXe0 : Xe ≠ 0 := by
    rw [hXe]
    refine mul_ne_zero (mul_ne_zero (ENNReal.coe_ne_zero.mpr ?_) ?_) ?_
    · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right (C Λ) 1))
    · exact ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hw1)
    · refine ENNReal.ofReal_ne_zero_iff.mpr ?_
      exact inv_pos.mpr (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ Xe * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    by_cases hfin : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count < ⊤
        ∧ MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count < ⊤
    · obtain ⟨hf, hg⟩ := hfin
      have hfBd : Work.KMTAreas.A5.BoundedZ f := Work.KMTAreas.A5.boundedZ_of_memLp hp₁
        (MeasureTheory.memLp_iff.mpr (hf))
      have hgBd : Work.KMTAreas.A5.BoundedZ g := Work.KMTAreas.A5.boundedZ_of_memLp hp₂
        (MeasureTheory.memLp_iff.mpr (hg))
      by_cases hguard : loGuard ρ C₀ a l₁ 0 k₁ k₂ n
      · have hmain : ∀ x : ℤ, mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x
            = bilinOp (hiKconc ρ P a l₁ 0 k₁ k₂ n) f g x := by
          intro x
          rw [mainPartTuple_apply, if_pos hguard]
          exact varpPiece_eq_bilinOp_hiKconc (ρ := ρ) (P := P) (a := a) (l₁ := l₁) (l₂ := 0)
            (k₁ := k₁) (k₂ := k₂) (n := n) (f := f) (g := g) hfBd hgBd x
        have heq : MeasureTheory.eLpNorm (fun x : ℤ =>
              mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            = MeasureTheory.eLpNorm (fun x : ℤ =>
                bilinOp (hiKconc ρ P a l₁ 0 k₁ k₂ n) f g x)
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count := by
          congr 1
          funext x
          exact hmain x
        rw [heq]
        have hp_eq : p₁⁻¹ + p₂⁻¹ = ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
        have hp1' : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
        have hKc : Summable fun p : ℤ × ℤ => ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖ :=
          summable_hiKconc ρ P a l₁ 0 k₁ k₂ n
        have hmass_n : (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
              - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            ≤ (C Λ : ℝ) * modelWeight A ρ l₁ 0 k₁ k₂ * ((Nat.floor (a n) : ℕ) : ℝ)⁻¹ :=
          hbound C₀ a Λ l₁ k₁ k₂ hΛ ha ha1 hl₁ n hguard
        have htsum_eq : (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
              - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            = ∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖ := by
          refine tsum_congr (fun p => ?_)
          rw [loMixedR_hiKmod_apply_eq_zero ρ P a l₁ k₁ k₂ n p.1 p.2, sub_zero]
        have hof : ENNReal.ofReal (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            ≤ Xe := by
          rw [← htsum_eq, hXe]
          refine (ENNReal.ofReal_le_ofReal hmass_n).trans ?_
          rw [ENNReal.ofReal_mul (mul_nonneg hCnn hw0), ENNReal.ofReal_mul hCnn,
            ENNReal.ofReal_coe_nnreal]
          exact mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.mpr (le_max_left (C Λ) 1)) le_rfl)
            le_rfl
        refine (BilinOpLp (K := hiKconc ρ P a l₁ 0 k₁ k₂ n)
          (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (p₁ := p₁) (p₂ := p₂) hp_eq hp1' hKc f g).trans ?_
        exact mul_le_mul' (mul_le_mul' hof le_rfl) le_rfl
      · have hzero : (fun x : ℤ => mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x) = 0 := by
          funext x
          rw [mainPartTuple_apply, if_neg hguard]
          rfl
        rw [hzero]
        simp
    · rcases not_and_or.mp hfin with hf | hg
      · have hftop : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = ⊤ :=
          eq_top_iff.mpr (not_lt.mp hf)
        by_cases hg0 : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0
        · have hgz : g = 0 := loMixedR_eq_zero_of_eLpNorm_count_eq_zero hp₂0 hg0
          rw [hgz]
          have hz : (fun x : ℤ => mainPartTuple ρ P C₀ a f 0 l₁ 0 k₁ k₂ n x) = 0 := by
            funext y
            exact loMixedR_mainPartTuple_zero_right ρ P C₀ a f l₁ 0 k₁ k₂ n y
          rw [hz]
          simp
        · have hgne : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count ≠ 0 := hg0
          rw [hftop, ENNReal.mul_top hXe0, ENNReal.top_mul hgne]
          exact le_top
      · have hgtop : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤ :=
          eq_top_iff.mpr (not_lt.mp hg)
        by_cases hf0 : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0
        · have hfz : f = 0 := loMixedR_eq_zero_of_eLpNorm_count_eq_zero hp₁0 hf0
          rw [hfz]
          have hz : (fun x : ℤ => mainPartTuple ρ P C₀ a 0 g l₁ 0 k₁ k₂ n x) = 0 := by
            funext y
            exact loMixedR_mainPartTuple_zero_left ρ P C₀ a g l₁ 0 k₁ k₂ n y
          rw [hz]
          simp
        · have hfne : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count ≠ 0 := hf0
          rw [hgtop, ENNReal.mul_top (mul_ne_zero hXe0 hfne)]
          exact le_top
  rw [hXe] at hgoal
  exact hgoal

/-- **The all-`ρ` mass bound.**  It combines the `ρ`-free per-fibre bound
`Work.KMTAreas.A7.LoFibreMass` with the all-`ρ` absorption `absorbAux`. -/
theorem loMixedRMassAll (P : Polynomial ℤ) : LoMixedRMassAll P :=
  rmassAux P (Work.KMTAreas.A7.LoFibreMass P) (absorbAux P)


theorem loMixedRSingleScaleUncond (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ≥0 → ℝ≥0,
        ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          1 ≤ l₁ → ∀ n : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
  loMixedRSingleScaleAll P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum (loMixedRMassAll P)

end

end Work.KMTPlan.A6.BoundedHMain

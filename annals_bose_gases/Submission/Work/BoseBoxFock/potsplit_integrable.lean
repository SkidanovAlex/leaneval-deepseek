import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.bf3a_kin
import Submission.Work.BoseBoxFock.integrableOn_frags
import Submission.Work.BoseBoxFock.potsplit_pair_agree_int
import Submission.Work.BoseBoxFock.qLHSword_eq_mu_add_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.potsplit_integrable` — FS `lem:potsplit`/`eq:potsplit` at the integrability level

The corpus proves the potential splitting (FS `lem:potsplit`, `eq:potsplit`)

    qLHSword ℓ μ w w1 Φ = q0word ℓ μ w1 w2 Φ + q1word ℓ μ w1 w2 Φ + q2word ℓ μ w1 w2 Φ
        + q3word ℓ w1 Φ + q4word ℓ w om Φ

for **continuous** kernels `w, om` (`Submission.BoseGases.potsplit_expect`,
`Submission/PotWords.lean`) and for the **chosen** `L¹` kernels (`Submission.BoseGases.potsplit_chosen`,
`Submission/PotChosen.lean`).  The present module proves the same identity for *abstract* kernels
satisfying only the pointwise relations `w₁ = w(1−ω)`, `w₂ = w(1−ω²)` and the *integrability*
hypotheses

* `hfib` : `x ↦ ∫_{acube ℓ} w₁(xᵢ,y) dy` integrable on `abox N ℓ`, each slot `i`,
* `hW`, `hW1`, `hW2` : `w(xᵢ,xⱼ)`, `w₁(xᵢ,xⱼ)`, `w₂(xᵢ,xⱼ)` integrable on `abox N ℓ`, each `i ≠ j`,

for a continuous state `Φ` (so that all the projection coefficients `aP`, `aQ` are continuous, hence
bounded on the compact box).  No continuity of `w, w1, w2, ω` is assumed.

## Structure of the proof (mirroring the corpus interfaces)

* `Work.BoseBoxFock.integrableOn_frags` (`Submission/Work/BoseBoxFock/integrableOn_frags.lean`):
  integrability of the seven per-pair fragment integrands `fg0 … fg4`; the point is `fg4 = ½·(q4B)²·w`
  with `q4B = D + ω·U`, which is *not* a bounded coefficient times `w` (ω need not be bounded) — but
  `(q4B)²·w = D²·w + 2·D·U·(w − w₁) + U²·(w − w₂)` pointwise, and each of those three pieces is a
  continuous coefficient times an integrable function.
* `Work.BoseBoxFock.potsplit_pair_agree_int`: the per-pair agreement, with the fourteen fragment
  integrabilities as hypotheses (`integral_add` + `potsplit_pair_pointwise`).
* `Work.BoseBoxFock.qLHSword_eq_mu_add_pair`: the LHS decomposition
  `qLHSword = −μ Σᵢ muPhi i + ½ Σ_{p ∈ pairSet} ∫ Φ² w(x_{p.1},x_{p.2})`.
* below: the μ-layer (`potsplit_mu_agree_int`, `mu_sum_agree_int`) and the final assembly.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

/-- The per-slot μ-weight identity with integrability hypotheses in place of continuity:
`muP + muQP + muQP + muQ = muPhi`, where `muPhi = ∫ Φ²·(∫_y w₁(xᵢ,y) dy)`.
Every integrand is a continuous coefficient (`aP`, `aQ`, `Φ`, all continuous since `Φ` is)
times the integrable fibre, so `MeasureTheory.IntegrableOn.continuousOn_mul` supplies the four
integrabilities, and `(aP + aQ)² = Φ²` pointwise does the rest. -/
theorem potsplit_mu_agree_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i : Fin N}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hfib : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Submission.BoseGases.muP ℓ w1 Φ i + Submission.BoseGases.muQP ℓ w1 Φ i
        + Submission.BoseGases.muQP ℓ w1 Φ i + Submission.BoseGases.muQ ℓ w1 Φ i
      = Submission.BoseGases.muPhi ℓ w1 Φ i := by
  let f : Submission.BoseGases.X N → ℝ :=
    fun x => Submission.BoseGases.w1Fibre ℓ w1 (x i)
  have hfint : IntegrableOn f (Submission.BoseGases.abox N ℓ) volume := by
    simpa only [f] using hfib
  have hPc : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i Φ x) :=
    Submission.BoseGases.aP_continuous hℓ i hΦc
  have hQc : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aQ ℓ i Φ x) := by
    change Continuous (Φ - Submission.BoseGases.aP ℓ i Φ)
    exact hΦc.sub hPc
  have h0 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x) (Submission.BoseGases.abox N ℓ) volume :=
    IntegrableOn.continuousOn_mul (hPc.pow 2).continuousOn hfint
      (Submission.BoseGases.abox_compact N hℓ)
  have h1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x)
      (Submission.BoseGases.abox N ℓ) volume :=
    IntegrableOn.continuousOn_mul (hQc.mul hPc).continuousOn hfint
      (Submission.BoseGases.abox_compact N hℓ)
  have h2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 * f x) (Submission.BoseGases.abox N ℓ) volume :=
    IntegrableOn.continuousOn_mul (hQc.pow 2).continuousOn hfint
      (Submission.BoseGases.abox_compact N hℓ)
  have is1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x
        + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x)
      (Submission.BoseGases.abox N ℓ) volume := h0.add h1
  have is2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x
        + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
        + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x)
      (Submission.BoseGases.abox N ℓ) volume := is1.add h1
  have hpoint : (fun x : Submission.BoseGases.X N =>
      (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x
        + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
        + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
        + (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 * f x)
      = fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * f x := by
    funext x
    have hlin : Submission.BoseGases.aP ℓ i Φ x + Submission.BoseGases.aQ ℓ i Φ x = Φ x := by
      unfold Submission.BoseGases.aQ
      ring
    have hb : (Submission.BoseGases.aP ℓ i Φ x) ^ 2
        + 2 * (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x)
        + (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 = (Φ x) ^ 2 := by
      rw [← hlin]
      ring
    calc
      (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x
          + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
          + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
          + (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 * f x
          = ((Submission.BoseGases.aP ℓ i Φ x) ^ 2
              + 2 * (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x)
              + (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) * f x := by
            ring
      _ = (Φ x) ^ 2 * f x := by rw [hb]
  calc
    Submission.BoseGases.muP ℓ w1 Φ i + Submission.BoseGases.muQP ℓ w1 Φ i
        + Submission.BoseGases.muQP ℓ w1 Φ i + Submission.BoseGases.muQ ℓ w1 Φ i
        = (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x)
            + (∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x)
            + (∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x)
            + (∫ x in Submission.BoseGases.abox N ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 * f x) := by
          unfold Submission.BoseGases.muP Submission.BoseGases.muQP Submission.BoseGases.muQ
          rfl
    _ = (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * f x
            + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
            + (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * f x
            + (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 * f x) := by
          rw [← integral_add h0 h1]
          rw [← integral_add is1 h1]
          rw [← integral_add is2 h2]
    _ = Submission.BoseGases.muPhi ℓ w1 Φ i := by
          unfold Submission.BoseGases.muPhi
          rw [← hpoint]

/-- Aggregation of the μ-layer over the slots: `Σᵢ muP + 2Σᵢ muQP + Σᵢ muQ = Σᵢ muPhi`. -/
theorem mu_sum_agree_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hfib : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∑ i : Fin N, Submission.BoseGases.muP ℓ w1 Φ i)
        + 2 * (∑ i : Fin N, Submission.BoseGases.muQP ℓ w1 Φ i)
        + (∑ i : Fin N, Submission.BoseGases.muQ ℓ w1 Φ i)
      = ∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i := by
  calc
    (∑ i : Fin N, Submission.BoseGases.muP ℓ w1 Φ i)
        + 2 * (∑ i : Fin N, Submission.BoseGases.muQP ℓ w1 Φ i)
        + (∑ i : Fin N, Submission.BoseGases.muQ ℓ w1 Φ i)
        = (∑ i : Fin N, Submission.BoseGases.muP ℓ w1 Φ i)
            + (∑ i : Fin N, 2 * Submission.BoseGases.muQP ℓ w1 Φ i)
            + (∑ i : Fin N, Submission.BoseGases.muQ ℓ w1 Φ i) := by
          rw [Finset.mul_sum]
    _ = ∑ i : Fin N, ((Submission.BoseGases.muP ℓ w1 Φ i
            + 2 * Submission.BoseGases.muQP ℓ w1 Φ i)
            + Submission.BoseGases.muQ ℓ w1 Φ i) := by
          rw [← Finset.sum_add_distrib]
          rw [← Finset.sum_add_distrib]
    _ = ∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i := by
          apply Finset.sum_congr rfl
          intro i _
          have h := potsplit_mu_agree_int (N := N) (ℓ := ℓ) hℓ (i := i) hΦc (hfib i)
          rw [← h]
          ring

/-- **FS `lem:potsplit`/`eq:potsplit` at the integrability level.**  For abstract kernels
`w, w1, w2, ω` satisfying the pointwise relations `w₁ = w(1−ω)`, `w₂ = w(1−ω²)` and the
integrability hypotheses `hfib`, `hW`, `hW1`, `hW2` (and a continuous state `Φ`), the potential
word splits into the five `𝒬`-words.  The proof is the corpus assembly
(`Submission.BoseGases.potsplit_chosen`'s structure) with the four pieces

* `qLHSword_eq_mu_add_pair` — the LHS split `−μ Σᵢ muPhi i + ½ Σ_p ∫ Φ² w`,
* the pure unfolding identity `five words = pairrawSum − μ(Σ muP + 2Σ muQP + Σ muQ)`,
* `pairrawSum = ½ Σ_p ∫ Φ² w` via `pairrawSum_eq_noCont`, `pairSet_swap_sum` and the per-pair
  agreement `potsplit_pair_agree_int` (whose fourteen fragment integrabilities come from
  `integrableOn_frags` at the pair and the reversed pair),
* `mu_sum_agree_int` — `Σ muP + 2Σ muQP + Σ muQ = Σ muPhi`. -/
theorem potsplit_integrable {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwsym : ∀ x y, w x y = w y x)
    (homsym : ∀ x y, om x y = om y x)
    (hw1rel : ∀ x y, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hfib : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hW : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => w (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hW1 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => w1 (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hW2 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => w2 (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ =
      Submission.BoseGases.q0word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q1word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q2word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q3word (N := N) ℓ w1 Φ
        + Submission.BoseGases.q4word (N := N) ℓ w om Φ := by
  -- (i) the LHS is the μ-part plus the pair part (integrability hypotheses only)
  have hLHS := qLHSword_eq_mu_add_pair (N := N) (ℓ := ℓ) (μ := μ) hℓ hΦc hfib hW
  -- (ii) the five words: pair parts (the raw seven sums) + μ parts (pure unfolding)
  have hwords : Submission.BoseGases.q0word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q1word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q2word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q3word (N := N) ℓ w1 Φ
        + Submission.BoseGases.q4word (N := N) ℓ w om Φ
      = Submission.BoseGases.pairrawSum ℓ w w1 w2 om Φ
        - μ * ((∑ i : Fin N, Submission.BoseGases.muP ℓ w1 Φ i)
          + 2 * (∑ i : Fin N, Submission.BoseGases.muQP ℓ w1 Φ i)
          + (∑ i : Fin N, Submission.BoseGases.muQ ℓ w1 Φ i)) := by
    unfold Submission.BoseGases.q0word Submission.BoseGases.q1word Submission.BoseGases.q2word
      Submission.BoseGases.q3word Submission.BoseGases.q4word
    simp [Submission.BoseGases.muP, Submission.BoseGases.muQP, Submission.BoseGases.muQ,
      Submission.BoseGases.pairrawSum]
    ring
  -- (iii) the pair sums telescope into half the `Φ²`-sums
  have hpairsum : Submission.BoseGases.pairrawSum ℓ w w1 w2 om Φ
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      Submission.BoseGases.pairrawSum ℓ w w1 w2 om Φ
          = (1 / 2) * (Submission.BoseGases.pairrawSum ℓ w w1 w2 om Φ
              + ∑ p ∈ Submission.BoseGases.pairSet N,
                  Submission.BoseGases.pairInts ℓ w w1 w2 om Φ p.2 p.1) := by
            rw [Submission.BoseGases.pairrawSum_eq_noCont hℓ w w1 w2 om Φ]
            rw [Submission.BoseGases.pairSet_swap_sum
              (fun p : Fin N × Fin N => Submission.BoseGases.pairInts ℓ w w1 w2 om Φ p.1 p.2)]
            ring
      _ = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            rw [Submission.BoseGases.pairrawSum_eq_noCont hℓ w w1 w2 om Φ]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
            exact potsplit_pair_agree_int (N := N) (ℓ := ℓ) hℓ hpne hwsym homsym hw1rel hw2rel
              hΦc
              (integrableOn_frags (N := N) (ℓ := ℓ) hℓ hw1rel hw2rel hΦc hpne
                (hW p.1 p.2 hpne) (hW1 p.1 p.2 hpne) (hW2 p.1 p.2 hpne))
              (integrableOn_frags (N := N) (ℓ := ℓ) hℓ hw1rel hw2rel hΦc (Ne.symm hpne)
                (hW p.2 p.1 (Ne.symm hpne)) (hW1 p.2 p.1 (Ne.symm hpne))
                (hW2 p.2 p.1 (Ne.symm hpne)))
  -- (iv) the μ sums
  have hmusum := mu_sum_agree_int (N := N) (ℓ := ℓ) hℓ hΦc hfib
  calc
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ
        = - μ * (∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i)
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := hLHS
    _ = - μ * (∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i)
          + Submission.BoseGases.pairrawSum ℓ w w1 w2 om Φ := by
          rw [hpairsum]
    _ = Submission.BoseGases.q0word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q1word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q2word (N := N) ℓ μ w1 w2 Φ
        + Submission.BoseGases.q3word (N := N) ℓ w1 Φ
        + Submission.BoseGases.q4word (N := N) ℓ w om Φ := by
          rw [hwords]
          rw [← hmusum]
          ring

end Work.BoseBoxFock

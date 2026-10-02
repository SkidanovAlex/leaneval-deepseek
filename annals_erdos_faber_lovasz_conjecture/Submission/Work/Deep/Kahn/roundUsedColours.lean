import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.UsedColoursSetup
import Submission.Work.Deep.Kahn.keptEvidenceLipCert
import Submission.Work.Deep.Kahn.keptEvidenceMeanVarAlt
import Submission.Work.Deep.Kahn.numBounds
import Submission.Work.Deep.Kahn.probGtCertifiable

/-!
# The `usedColours` estimate of the regularised one-round nibble

The vocabulary and the structural lemmas live in `Submission.Work.Deep.Kahn.UsedColoursSetup`,
the law of the statistic `X ω = #(keptEvidence K e ω)` (mean and variance) in
`Submission.Work.Deep.Kahn.keptEvidenceMeanVar`, its sensitivity and certificates in
`Submission.Work.Deep.Kahn.keptEvidenceLipCert`, and the abstract tail bound (Talagrand via
certificates, with the level of the typical set obtained from the mean and the variance) in
`Submission.Work.Deep.Kahn.probGtCertifiable`.  This module assembles them into the target
estimate `Work.Deep.Kahn.roundUsedColours`.

## The argument

* **Reduction.**  If `e` is not kept, every colour of `L e` used at `e` has an activated
  witness, so `|L e ∩ usedColours ω e| ≤ #(keptEvidence K e ω) = X ω`
  (`Work.Deep.Kahn.card_usedColours_le_keptEvidence`).
* **Mean.**  `E X = Λ (1 - (1-1/(KΛ))^{C(D-1)}) ≤ Λ (1 - retention Λ C D K)`, because each of
  the `C(D-1)` witnesses of a colour `γ ∈ L e` names `γ` with probability `1/(KΛ)`
  (`Work.Deep.Kahn.card_colWit`).
* **Variance.**  `Var X ≤ E X`: the colours of `L e` are pairwise negatively correlated (the
  fact that an edge names a single colour makes the two "box" events overlap favourably).
* **Tail.**  `X` is `1`-Lipschitz and `2`-certifiable, so `Work.Deep.Kahn.probGtCertifiable`
  applies, with the typical set obtained from the mean and the variance and the level
  `θ = Λ (1 - retention) + η Λ`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

/-- **The `usedColours` estimate** (the target lemma). -/
theorem roundUsedColours {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Dmin : ℝ, 0 < Dmin ∧ ∀ (n c : ℕ)
      (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗]
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ) [NeZero K],
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      Dmin ≤ (D : ℝ) →
      Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
      ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
      ∀ e : 𝓗,
        Work.Deep.Conc.prob {ω : Work.Deep.Kahn.Round.Space K 𝓗 L |
          ¬ Work.Deep.Kahn.Round.kept ω e ∧
            (Λ : ℝ) * (1 - Work.Deep.Kahn.retention Λ C D K) + η * (Λ : ℝ) <
              (((L e) ∩ Work.Deep.Kahn.Round.usedColours ω e).card : ℝ)}
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := by
  refine ⟨(10 : ℝ) ^ 30, by norm_num, ?_⟩
  intro n c 𝓗 _ L D Λ K _ hD1 hΛ1 hK2 hηK h16C hlin hsize hlist hdeg hDΛ hΛD hDmin
    hlogDK hKlog hCKη e
  -- ### notation
  set θ : ℝ := (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) with hθdef
  -- ### the round space has nonempty coordinates
  have hΛpos : 0 < Λ := lt_of_lt_of_le Nat.zero_lt_one hΛ1
  have hne : ∀ f : 𝓗, Nonempty (Round.Coord K 𝓗 L f) := fun f =>
    ⟨(0, ⟨0, by rw [hlist f]; exact hΛpos⟩)⟩
  -- ### the numerical side conditions
  have hηinv : η⁻¹ ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
    refine le_trans ?_ hCKη
    have h1 : (0 : ℝ) ≤ (C : ℝ) + (K : ℝ) := by positivity
    linarith
  obtain ⟨hbig0, h16, hθ1, hθle⟩ := numBounds (C := C) (D := D) (Λ := Λ) (K := K)
    hε hη hD1 hΛ1 hK2 hηK hDΛ hDmin hηinv
  -- ### mean and variance of the statistic `ω ↦ #(keptEvidence K e ω)`
  obtain ⟨hmean, hvarle⟩ := keptEvidenceMeanVarAlt (C := C) (D := D) (Λ := Λ) (K := K)
    (L := L) (𝓗 := 𝓗) (e := e) hΛ1 hlin hsize hdeg hlist
  -- ### sensitivity and certificates
  obtain ⟨hlip, hcert⟩ := keptEvidence_lip_cert (K := K) (L := L) (𝓗 := 𝓗) e
  -- ### the mean hypothesis of the tail bound
  have hmean2 : Work.Deep.Conc.expect
      (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ))
      ≤ θ - η * (Λ : ℝ) := by
    rw [hθdef]
    linarith [hmean]
  -- ### the variance hypothesis of the tail bound
  have hvar2 : 2 * Work.Deep.Conc.expect (fun f : Round.Space K 𝓗 L =>
      (((keptEvidence K e f).card : ℝ) -
        Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
          ((keptEvidence K e ω).card : ℝ))) ^ 2) + 2
      ≤ (η * (Λ : ℝ)) ^ 2 / 4 := by
    have hretnn : (0 : ℝ) ≤ retention Λ C D K := by
      rw [retention]
      apply pow_nonneg
      have hKpos : (0 : ℝ) < (K : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
      have hle : (1 : ℝ) / (K : ℝ) / (Λ : ℝ) ≤ 1 := by
        rw [div_div, div_le_one (by positivity)]
        have h1 : (1 : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
        have h2 : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
        nlinarith
      linarith
    have hEXle : Work.Deep.Conc.expect
        (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ)) ≤ (Λ : ℝ) := by
      refine le_trans hmean ?_
      nlinarith [hretnn, (by positivity : (0:ℝ) ≤ (Λ:ℝ))]
    have hΛR : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
    have hmul : 16 * (Λ : ℝ) ≤ η ^ 2 * (Λ : ℝ) * (Λ : ℝ) :=
      mul_le_mul_of_nonneg_right h16 (by positivity : (0:ℝ) ≤ (Λ:ℝ))
    nlinarith [hvarle, hEXle, hmul, hΛR]
  -- ### the exponent hypothesis of the tail bound
  have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ1
  have hbig : (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 2 ≤ (η * (Λ : ℝ)) ^ 2 / (32 * θ) := by
    refine le_trans hbig0 ?_
    have h32 : (0 : ℝ) < 32 * θ := by positivity
    have h64 : (0 : ℝ) < (64 : ℝ) := by norm_num
    rw [le_div_iff₀ h32,
      show η ^ 2 * (Λ : ℝ) / 64 * (32 * θ) = η ^ 2 * (Λ : ℝ) * (32 * θ) / 64 by ring,
      div_le_iff₀ h64]
    nlinarith [hθle]
  -- ### the tail bound
  have hmain : Work.Deep.Conc.prob {f : ∀ f : 𝓗, Round.Coord K 𝓗 L f |
        θ < (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ)) f}
      ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) :=
    probGtCertifiable (π := fun f : 𝓗 => Round.Coord K 𝓗 L f) hne
      (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ)) hη
      (Nat.cast_nonneg Λ) hθ1 hmean2 hvar2 hlip hcert hbig
  -- ### the event inclusion
  have hsub : {ω : Round.Space K 𝓗 L |
        ¬ Round.kept ω e ∧ θ < (((L e) ∩ Round.usedColours ω e).card : ℝ)}
      ⊆ {ω : Round.Space K 𝓗 L | θ < ((keptEvidence K e ω).card : ℝ)} := by
    intro ω hω
    obtain ⟨hk, hlt⟩ := hω
    have h1 := card_usedColours_le_keptEvidence (L := L) (K := K) (e := e) hk
    have h2 : (((L e) ∩ Round.usedColours ω e).card : ℝ)
        ≤ ((keptEvidence K e ω).card : ℝ) := by exact_mod_cast h1
    exact lt_of_lt_of_le hlt h2
  calc Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
        ¬ Round.kept ω e ∧
          (Λ : ℝ) * (1 - retention Λ C D K) + η * (Λ : ℝ) <
            (((L e) ∩ Round.usedColours ω e).card : ℝ)}
      = Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
          ¬ Round.kept ω e ∧ θ < (((L e) ∩ Round.usedColours ω e).card : ℝ)} := by
        rw [hθdef]
    _ ≤ Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
          θ < ((keptEvidence K e ω).card : ℝ)} := Work.Deep.Conc.prob_mono hsub
    _ ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) := hmain

end

end Work.Deep.Kahn

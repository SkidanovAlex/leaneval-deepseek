import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleWSetup
import Submission.Work.Deep.Kahn.roundKeptUnactDefs
import Submission.Work.Deep.Kahn.keptUnactMean
import Submission.Work.Deep.Kahn.keptUnactCert
import Submission.Work.Deep.Kahn.keptUnactThresh
import Submission.Work.Deep.Kahn.keptUnactTail
import Submission.Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand

/-!
# `Work.Deep.Kahn.roundKeptUnact`

The concentration of the *unactivated survivors* colour-degree count `keptUnactCount ω x γ`
(the paper's `keptUnactColsRV`; Kang--Kelly--Kühn--Methuku--Osthus, arXiv:2109.11438,
Lemma `lemma:concentrations`), in the form consumed by the one-round nibble:

  `prob (badKeptSet C D Λ η x γ) ≤ exp (-D^{1/4}) / 2`.

The three ingredients are the exact first moment `keptUnactMean`, the certificate condition
`keptUnactCert` and the numeric side conditions `keptUnactThresh`/`keptUnactTail`, combined by
the Bruhn--Joos concentration inequality `BruhnJoos.bruhn_joos_talagrand` applied directly to
`keptUnactCount` (an increase of the count is certified by the counted edge together with a
chosen blocker).  No exceptional set is needed: unlike a blocker of an activated edge, a blocker
of an unactivated edge never contains `x`, so its fibre has size at most `C` unconditionally.

`Dmin = 10^100` is a uniform threshold: the estimates only use `C + K + η⁻¹ ≤ D^{1/9}`,
`K ≥ 2`, `Λ ≥ D` and `log D ≤ K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

open Work.Deep.Kahn.Round

theorem roundKeptUnact {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Dmin : ℝ, 0 < Dmin ∧
    Dmin ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ (1000 : ℕ) ∧
    ∀ (n c : ℕ)
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
      ∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badKeptSet (K := K) (L := L) C D Λ η x γ)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := by
  refine ⟨(10 : ℝ) ^ 100, by positivity, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ((C : ℝ) + η⁻¹ + ε⁻¹ + 1) ^ (1000 : ℕ) := by positivity
    have h2 : (10 : ℝ) ^ 100 ≤ (10 : ℝ) ^ (1000 : ℕ) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by norm_num : 100 ≤ 1000)
    exact le_trans h2 (le_add_of_nonneg_left h1)
  · intro n c 𝓗 _instF L D Λ K _instK hD1 hΛ1 hK2 hηK _h16C hlin hsize hlist hdeg hDΛ _hΛD
      hDmin _hlogK _hKlog hCKη x γ hxγ
    classical
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
      exact_mod_cast this
    have hne : ∀ e : 𝓗, Nonempty (Coord K 𝓗 L e) :=
      fun e => ⟨(0, ⟨0, by rw [hlist e]; omega⟩)⟩
    haveI : Nonempty (Space K 𝓗 L) := ⟨fun i => Classical.choice (hne i)⟩
    have hcol : (colThru (L := L) x γ).card = D := colThru_card (L := L) hdeg hxγ
    -- the first moment
    have hmean : Work.Deep.Conc.expect (fun ω : Space K 𝓗 L => (keptUnactCount ω x γ : ℝ))
        = (D : ℝ) * (1 - 1 / (K : ℝ))
          * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((C - 1) * (D - 1)) :=
      keptUnactMean (K := K) (L := L) hlin hsize hdeg hlist hxγ
    -- the threshold comparison
    have hthresh := keptUnactThresh (C := C) (D := D) (Λ := Λ) (K := K) (ε := ε) (η := η)
      hC hε hη hD1 hΛ1 hK2 hηK hDΛ hDmin hCKη
    -- the numeric side conditions
    obtain ⟨ht_lt, htail⟩ := keptUnactTail (C := C) (D := D) (K := K) (η := η)
      hη hD1 hK2 hDmin hCKη
    -- the certificate
    have hcert : ∀ (u : ℝ), 0 < u → ∀ ω : Space K 𝓗 L, ω ∉ (∅ : Set (Space K 𝓗 L)) →
        ∃ I : Finset 𝓗, I.card ≤ 2 * D ∧
          ∀ ω' : Space K 𝓗 L, ω' ∉ (∅ : Set (Space K 𝓗 L)) →
            ((I.filter (fun i : 𝓗 => ω i ≠ ω' i)).card : ℝ) < u / ((C : ℝ) + 2) →
              (keptUnactCount ω' x γ : ℝ) < (keptUnactCount ω x γ : ℝ) + u := by
      intro u hu ω _
      obtain ⟨I, hIcard, hI⟩ := keptUnactCert (K := K) (L := L) hlin hsize x γ u hu ω
      refine ⟨I, ?_, ?_⟩
      · rw [hcol] at hIcard
        omega
      · intro ω' _ hdis
        exact hI ω' hdis
    -- boundedness of the statistic
    have hsup : ∀ ω : Space K 𝓗 L, |(keptUnactCount ω x γ : ℝ)| ≤ (D : ℝ) := by
      intro ω
      have h1 : keptUnactCount ω x γ ≤ (colThru (L := L) x γ).card :=
        keptUnactCount_le_colThru_card ω x γ
      have h2 : (keptUnactCount ω x γ : ℝ) ≤ (D : ℝ) := by
        rw [← hcol]; exact_mod_cast h1
      have h3 : (0 : ℝ) ≤ (keptUnactCount ω x γ : ℝ) := by positivity
      rw [abs_le]
      exact ⟨by linarith, h2⟩
    have hM1 : (1 : ℝ) ≤ (D : ℝ) :=
      le_trans (by norm_num : (1 : ℝ) ≤ (10 : ℝ) ^ 100) hDmin
    have hc1 : (1 : ℝ) ≤ (C : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (C : ℝ) := by positivity
      linarith
    have hexc : Work.Deep.Conc.prob (∅ : Set (Space K 𝓗 L)) ≤ 1 / (D : ℝ) ^ 2 := by
      rw [Work.Deep.Conc.prob_empty]
      positivity
    have hbj := Work.Deep.Conc.BruhnJoos.bruhn_joos_talagrand (ι := 𝓗)
      (π := fun e : 𝓗 => Coord K 𝓗 L e) hne
      (fun ω : Space K 𝓗 L => (keptUnactCount ω x γ : ℝ))
      (D : ℝ) hM1 hsup ((C : ℝ) + 2) hc1 (2 * D) (by omega) (∅ : Set (Space K 𝓗 L))
      hexc hcert
    have ht : 50 * ((C : ℝ) + 2) * Real.sqrt (((2 * D : ℕ) : ℝ)) < η * (D : ℝ) / 8 := by
      rw [show (((2 * D : ℕ) : ℝ)) = 2 * (D : ℝ) by push_cast; ring]
      exact ht_lt
    have hbj_t := hbj (η * (D : ℝ) / 8) ht
    -- the bad event is contained in a deviation event
    have hmono : Work.Deep.Kahn.Round.badKeptSet (K := K) (L := L) C D Λ η x γ
        ⊆ {ω : Space K 𝓗 L |
            η * (D : ℝ) / 8 ≤
              |(keptUnactCount ω x γ : ℝ)
                - Work.Deep.Conc.expect (fun ω : Space K 𝓗 L =>
                    (keptUnactCount ω x γ : ℝ))|} := by
      intro ω hω
      rw [Work.Deep.Kahn.Round.badKeptSet, Set.mem_ofPred_eq] at hω
      have h1 : Work.Deep.Conc.expect (fun ω : Space K 𝓗 L => (keptUnactCount ω x γ : ℝ))
          + η * (D : ℝ) / 8
          ≤ (1 - 1 / (K : ℝ)) * retentionU Λ C D K * (D : ℝ) + η * (D : ℝ) / 4 := by
        rw [hmean]
        linarith [hthresh]
      have h2 : η * (D : ℝ) / 8
          ≤ |(keptUnactCount ω x γ : ℝ)
              - Work.Deep.Conc.expect (fun ω : Space K 𝓗 L =>
                  (keptUnactCount ω x γ : ℝ))| := by
        refine le_trans ?_ (le_abs_self _)
        linarith
      simpa only [Set.mem_ofPred_eq] using h2
    -- the exponential comparison
    have hprob_empty : Work.Deep.Conc.prob (∅ : Set (Space K 𝓗 L)) = 0 :=
      Work.Deep.Conc.prob_empty
    have hexp : 4 * Real.exp
          (-(η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (((2 * D : ℕ) : ℝ))))
        + 4 * Work.Deep.Conc.prob (∅ : Set (Space K 𝓗 L))
        ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := by
      rw [show (((2 * D : ℕ) : ℝ)) = 2 * (D : ℝ) by push_cast; ring, hprob_empty]
      have htail' : 4 * Real.exp
            (-(η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ))))
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := by
        rw [show -(η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ)))
            = -((η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ)))) by ring]
        exact htail
      linarith [htail']
    calc Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badKeptSet (K := K) (L := L) C D Λ η x γ)
        ≤ Work.Deep.Conc.prob {ω : Space K 𝓗 L |
            η * (D : ℝ) / 8 ≤
              |(keptUnactCount ω x γ : ℝ)
                - Work.Deep.Conc.expect (fun ω : Space K 𝓗 L =>
                    (keptUnactCount ω x γ : ℝ))|} :=
          Work.Deep.Conc.prob_mono hmono
      _ ≤ 4 * Real.exp
            (-(η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (((2 * D : ℕ) : ℝ))))
          + 4 * Work.Deep.Conc.prob (∅ : Set (Space K 𝓗 L)) := hbj_t
      _ ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := hexp

end

end Work.Deep.Kahn

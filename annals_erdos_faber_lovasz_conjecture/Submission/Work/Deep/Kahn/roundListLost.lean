import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleWSetup
import Submission.Work.Deep.Kahn.roundUsedColours
import Submission.Work.Deep.Kahn.UsedColoursSetup
import Submission.Work.Deep.Kahn.keptEvidenceLipCert
import Submission.Work.Deep.Kahn.keptEvidenceMeanVarAlt
import Submission.Work.Deep.Kahn.keptEvidenceLaw
import Submission.Work.Deep.Kahn.numBounds
import Submission.Work.Deep.Kahn.probGtCertifiable

/-!
# The list-loss estimate of the regularised one-round nibble

This module proves `Work.Deep.Kahn.roundListLost`: in the *regularised* setting of the
one-round nibble (every edge of `𝓗` has exactly `C` vertices, every list `L e` has exactly
`Λ` colours and every *occurring* colour degree is exactly `D`), the probability that an edge
`e` loses more than `Λ (1 - retention Λ C D K) + η Λ` colours in one wasteful round is at
most `exp (-D ^ (1/4))`.

The statistic is `Round.lost ω e`, the set of colours of **activated** edges meeting `e`
(the wasteful procedure of Reed--Sudakov, for which `retention` is calibrated).  The proof
reduces it to the statistic `#(keptEvidence K e ω)` already analysed in this chapter:

* `Round.lost ω e ⊆ keptEvidence K e ω ∪ {Round.colour ω e}`, hence
  `#(Round.lost ω e) ≤ #(keptEvidence K e ω) + 1` (`card_lost_le_keptEvidence`);
* `#(keptEvidence K e ·)` has mean `≤ Λ (1 - retention)` (`keptEvidenceMeanVarAlt`),
  variance `≤` its mean, is `1`-Lipschitz and `2`-certifiable (`keptEvidence_lip_cert`);
* the abstract certified Talagrand bound `probGtCertifiable` is therefore applicable at the
  level `θ = Λ (1 - retention) + η Λ - 1` with slack `η Λ / 2`.  The numerical side
  conditions (`roundListNum`, `roundListTheta`) come from `η⁻¹ ≤ D ^ (1/9)`, `Λ ≥ (1+ε) D`
  and `D ≥ 10 ^ 30`, which give `η² Λ ≥ D ^ (7/9)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ} {K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
  {L : 𝓗 → Finset (Fin c)}

/-- The numerical estimates of one round needed for the list-loss bound: `ηΛ` is large,
`η² Λ` dominates the constant `64`, and `256 (D ^ (1/4) + log 2) ≤ η² Λ`.  All three come
from `η ≥ D ^ (-1/9)`, `Λ ≥ (1+ε) D ≥ D` and `D ≥ 10 ^ 30`, which give
`η² Λ ≥ D ^ (7/9) ≥ D ^ (1/2) ≥ 10 ^ 15`. -/
lemma roundListNum {C D Λ K : ℕ} {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hD1 : 1 ≤ D) (hΛ1 : 1 ≤ Λ) (hK2 : 2 ≤ K)
    (hηK : η * (K : ℝ) ≤ 1)
    (hDΛ : (1 + ε) * (D : ℝ) ≤ (Λ : ℝ))
    (hD : (10 : ℝ) ^ 30 ≤ (D : ℝ))
    (hηinv : η⁻¹ ≤ (D : ℝ) ^ ((1 : ℝ) / 9)) :
    (4 : ℝ) ≤ η * (Λ : ℝ) ∧ (64 : ℝ) ≤ η ^ 2 * (Λ : ℝ) ∧
      256 * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 2) ≤ η ^ 2 * (Λ : ℝ) := by
  have hD0 : (0:ℝ) < (D:ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hD1)
  have hD1R : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD1
  have hDnonneg : (0:ℝ) ≤ (D:ℝ) := le_of_lt hD0
  have hLxD : (D:ℝ) ≤ (Λ:ℝ) := by
    have h1 : (1:ℝ) ≤ 1 + ε := by linarith
    calc (D:ℝ) = 1 * (D:ℝ) := (one_mul _).symm
      _ ≤ (1+ε) * (D:ℝ) := mul_le_mul_of_nonneg_right h1 hDnonneg
      _ ≤ (Λ:ℝ) := hDΛ
  have hD9pos : (0:ℝ) < (D:ℝ) ^ ((1:ℝ)/9) := Real.rpow_pos_of_pos hD0 _
  have hηinvpos : (0:ℝ) < η⁻¹ := inv_pos.mpr hη
  have hηgeinv : ((D:ℝ)^((1:ℝ)/9))⁻¹ ≤ η := by
    have h := inv_anti₀ hηinvpos hηinv
    rwa [inv_inv] at h
  have h8 : (D:ℝ)^((8:ℝ)/9) ≤ η * (Λ:ℝ) := by
    have h89 : (D:ℝ)^((8:ℝ)/9) = ((D:ℝ)^((1:ℝ)/9))⁻¹ * (D:ℝ) := by
      have he : ((8:ℝ)/9) = (1:ℝ) - (1:ℝ)/9 := by norm_num
      rw [he, Real.rpow_sub hD0, Real.rpow_one, div_eq_mul_inv]
      exact mul_comm _ _
    rw [h89]
    exact mul_le_mul hηgeinv hLxD hDnonneg (le_of_lt hη)
  have hη2a : ((D:ℝ) ^ ((2:ℝ)/9))⁻¹ ≤ η ^ 2 := by
    have hstep : ((D:ℝ) ^ ((1:ℝ)/9))⁻¹ * ((D:ℝ) ^ ((1:ℝ)/9))⁻¹ ≤ η * η :=
      mul_le_mul hηgeinv hηgeinv (le_of_lt (inv_pos.mpr hD9pos)) (le_of_lt hη)
    have he : ((2:ℝ)/9) = (1:ℝ)/9 + (1:ℝ)/9 := by norm_num
    have h2a : (D:ℝ) ^ ((2:ℝ)/9) = (D:ℝ) ^ ((1:ℝ)/9) * (D:ℝ) ^ ((1:ℝ)/9) := by
      rw [he, Real.rpow_add hD0]
    rw [h2a, mul_inv, pow_two]
    exact hstep
  have h7 : (D:ℝ)^((7:ℝ)/9) ≤ η^2 * (Λ:ℝ) := by
    have h79 : (D:ℝ) ^ ((7:ℝ)/9) = ((D:ℝ) ^ ((2:ℝ)/9))⁻¹ * (D:ℝ) := by
      have he : ((7:ℝ)/9) = (1:ℝ) - (2:ℝ)/9 := by norm_num
      rw [he, Real.rpow_sub hD0, Real.rpow_one, div_eq_mul_inv]
      exact mul_comm _ _
    rw [h79]
    exact mul_le_mul hη2a hLxD hDnonneg (sq_nonneg η)
  have hsqrt : (10:ℝ)^15 ≤ Real.sqrt (D:ℝ) := by
    have h30 : ((10:ℝ)^15)^2 = (10:ℝ)^30 := by norm_num
    calc (10:ℝ)^15 = Real.sqrt (((10:ℝ)^15)^2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt ((10:ℝ)^30) := by rw [h30]
      _ ≤ Real.sqrt (D:ℝ) := Real.sqrt_le_sqrt hD
  have hhalf : (10:ℝ)^15 ≤ (D:ℝ)^((1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow] at hsqrt
    exact hsqrt
  refine ⟨?_, ?_, ?_⟩
  · have h3 : (D:ℝ)^((1:ℝ)/2) ≤ (D:ℝ)^((8:ℝ)/9) :=
      Real.rpow_le_rpow_of_exponent_le hD1R (by norm_num)
    linarith [h3, h8, hhalf, (by norm_num : (4:ℝ) ≤ (10:ℝ)^15)]
  · have h3 : (D:ℝ)^((1:ℝ)/2) ≤ (D:ℝ)^((7:ℝ)/9) :=
      Real.rpow_le_rpow_of_exponent_le hD1R (by norm_num)
    linarith [h3, h7, hhalf, (by norm_num : (64:ℝ) ≤ (10:ℝ)^15)]
  · have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hD14_1 : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hD1R (by norm_num)
    have hD14pos : (0:ℝ) < (D:ℝ)^((1:ℝ)/4) := Real.rpow_pos_of_pos hD0 _
    have h512 : (512:ℝ) ≤ (D:ℝ)^((1:ℝ)/2) := by
      linarith [hhalf, (by norm_num : (512:ℝ) ≤ (10:ℝ)^15)]
    have hstep1 : 256 * ((D:ℝ)^((1:ℝ)/4) + Real.log 2) ≤ 512 * (D:ℝ)^((1:ℝ)/4) := by
      nlinarith [hlog, hD14_1]
    have hstep2 : 512 * (D:ℝ)^((1:ℝ)/4) ≤ (D:ℝ)^((3:ℝ)/4) := by
      have h34 : (D:ℝ)^((3:ℝ)/4) = (D:ℝ)^((1:ℝ)/4) * (D:ℝ)^((1:ℝ)/2) := by
        have he : ((3:ℝ)/4) = (1:ℝ)/4 + (1:ℝ)/2 := by norm_num
        rw [he, Real.rpow_add hD0]
      rw [h34]
      have := mul_le_mul_of_nonneg_right h512 hD14pos.le
      linarith [this]
    have hstep3 : (D:ℝ)^((3:ℝ)/4) ≤ (D:ℝ)^((7:ℝ)/9) :=
      Real.rpow_le_rpow_of_exponent_le hD1R (by norm_num)
    linarith [hstep1, hstep2, hstep3, h7]

/-- The level `θ = Λ (1 - retention) + η Λ - 1` of the list-loss tail bound lies in
`[1, 2 Λ]`, and the retention factor lies in `[0,1]`. -/
lemma roundListTheta {C D Λ K : ℕ} {η : ℝ}
    (hη : 0 < η) (hΛ1 : 1 ≤ Λ) (hK2 : 2 ≤ K)
    (hηK : η * (K : ℝ) ≤ 1) (h4 : (4:ℝ) ≤ η * (Λ:ℝ)) :
    (1:ℝ) ≤ (Λ:ℝ) * (1 - retention Λ C D K) + η*(Λ:ℝ) - 1 ∧
    (Λ:ℝ) * (1 - retention Λ C D K) + η*(Λ:ℝ) - 1 ≤ 2*(Λ:ℝ) ∧
    (0:ℝ) ≤ retention Λ C D K ∧ retention Λ C D K ≤ 1 := by
  have hΛ1R : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ1
  have hK1R : (1:ℝ) ≤ (K:ℝ) := by
    have h : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
    linarith
  have hbase0 : (0:ℝ) ≤ 1 - (1/(K:ℝ))/(Λ:ℝ) := by
    have hKL1 : (1:ℝ) ≤ (K:ℝ) * (Λ:ℝ) := by
      have h := mul_le_mul hK1R hΛ1R (by norm_num : (0:ℝ) ≤ 1) (Nat.cast_nonneg K)
      simpa using h
    have h1 : (1/(K:ℝ))/(Λ:ℝ) = ((K:ℝ)*(Λ:ℝ))⁻¹ := by
      rw [one_div, div_eq_mul_inv, mul_inv]
    rw [h1]
    have h2 : ((K:ℝ)*(Λ:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hKL1
    linarith
  have hbase1 : 1 - (1/(K:ℝ))/(Λ:ℝ) ≤ 1 :=
    sub_le_self _ (div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg K))
      (Nat.cast_nonneg Λ))
  have hs0 : (0:ℝ) ≤ retention Λ C D K := by rw [retention]; exact pow_nonneg hbase0 _
  have hs1 : retention Λ C D K ≤ 1 := by rw [retention]; exact pow_le_one₀ hbase0 hbase1
  have hηle1 : η ≤ 1 := by
    have h : η * (2:ℝ) ≤ η * (K:ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hK2) (le_of_lt hη)
    linarith
  have hΛnn : (0:ℝ) ≤ (Λ:ℝ) := Nat.cast_nonneg Λ
  have h1 : (0:ℝ) ≤ (Λ:ℝ) * (1 - retention Λ C D K) :=
    mul_nonneg hΛnn (by linarith)
  have h2 : (Λ:ℝ) * (1 - retention Λ C D K) ≤ (Λ:ℝ) := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - retention Λ C D K ≤ 1) hΛnn
    rwa [mul_one] at this
  have h3 : η * (Λ:ℝ) ≤ (Λ:ℝ) := by
    have := mul_le_mul_of_nonneg_right hηle1 hΛnn
    rwa [one_mul] at this
  exact ⟨by linarith, by linarith, hs0, hs1⟩

/-- A colour lost by `e` is either witnessed by an activated edge `≠ e`, or is the colour of
`e` itself. -/
lemma lost_subset_keptEvidence [Fintype 𝓗] [NeZero K] (e : 𝓗) (ω : Round.Space K 𝓗 L) :
    Round.lost ω e ⊆ keptEvidence K e ω ∪ {Round.colour ω e} := by
  intro γ hγ
  rw [Round.mem_lost] at hγ
  obtain ⟨hγL, g, hag, hcol, hint⟩ := hγ
  rcases eq_or_ne g e with hge | hge
  · subst hge
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hcol.symm)
  · refine Finset.mem_union_left _ ?_
    rw [keptEvidence, mem_classEvidence]
    exact ⟨hγL, g, hge, hint, hag, by rw [idxOf, ← round_colour_eq_idxColour ω g]; exact hcol⟩

/-- The number of colours lost by `e` is at most the number of colours named by an activated
witness of `e`, plus one (for the colour of `e` itself). -/
lemma card_lost_le_keptEvidence [Fintype 𝓗] [NeZero K] (e : 𝓗) (ω : Round.Space K 𝓗 L) :
    ((Round.lost ω e).card : ℝ) ≤ ((keptEvidence K e ω).card : ℝ) + 1 := by
  have h1 : (Round.lost ω e).card ≤ (keptEvidence K e ω ∪ {Round.colour ω e}).card :=
    Finset.card_le_card (lost_subset_keptEvidence e ω)
  have h2 : (keptEvidence K e ω ∪ {Round.colour ω e}).card
      ≤ (keptEvidence K e ω).card + 1 := by
    calc (keptEvidence K e ω ∪ {Round.colour ω e}).card
        ≤ (keptEvidence K e ω).card + ({Round.colour ω e} : Finset (Fin c)).card :=
          Finset.card_union_le _ _
      _ = (keptEvidence K e ω).card + 1 := by simp
  have h3 : (Round.lost ω e).card ≤ (keptEvidence K e ω).card + 1 := le_trans h1 h2
  have h4 : (((Round.lost ω e).card : ℕ) : ℝ) ≤ (((keptEvidence K e ω).card + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr h3
  push_cast at h4
  linarith

/-- **The list-loss estimate** (the target lemma). -/
theorem roundListLost {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
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
      ∀ e : 𝓗,
        Work.Deep.Conc.prob (Work.Deep.Kahn.Round.badListSet (K := K) (L := L) C D Λ η e)
          ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := by
  refine ⟨(10:ℝ)^30, by norm_num, ?_, ?_⟩
  · have h2 : (10:ℝ)^30 ≤ (10:ℝ)^(1000:ℕ) :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 10) (by norm_num : 30 ≤ 1000)
    have h1 : (0:ℝ) ≤ ((C:ℝ) + η⁻¹ + ε⁻¹ + 1)^(1000:ℕ) := by positivity
    exact le_trans h2 (le_add_of_nonneg_left h1)
  · intro n c 𝓗 _ L D Λ K _ hD1 hΛ1 hK2 hηK h16C hlin hsize hlist hdeg hDΛ hΛD hDmin
      hlogDK hKlog hCKη e
    have hΛpos : 0 < Λ := lt_of_lt_of_le Nat.zero_lt_one hΛ1
    have hne : ∀ f : 𝓗, Nonempty (Round.Coord K 𝓗 L f) := fun f =>
      ⟨(0, ⟨0, by rw [hlist f]; exact hΛpos⟩)⟩
    have hηinv : η⁻¹ ≤ (D:ℝ)^((1:ℝ)/9) := by
      refine le_trans ?_ hCKη
      have h1 : (0:ℝ) ≤ (C:ℝ) + (K:ℝ) := by positivity
      linarith
    obtain ⟨h4, h64, h256⟩ := roundListNum (C:=C) (D:=D) (Λ:=Λ) (K:=K)
      hε hη hD1 hΛ1 hK2 hηK hDΛ hDmin hηinv
    obtain ⟨hθ1, hθ2, hret0, hret1⟩ := roundListTheta (C:=C) (D:=D) (Λ:=Λ) (K:=K)
      hη hΛ1 hK2 hηK h4
    obtain ⟨hmean, hvarle⟩ := keptEvidenceMeanVarAlt (C:=C) (D:=D) (Λ:=Λ) (K:=K)
      (L:=L) (𝓗:=𝓗) (e:=e) hΛ1 hlin hsize hdeg hlist
    obtain ⟨hlip, hcert⟩ := keptEvidence_lip_cert (K:=K) (L:=L) (𝓗:=𝓗) e
    set θv : ℝ := (Λ:ℝ) * (1 - retention Λ C D K) + η * (Λ:ℝ) - 1 with hθv
    have hsub : Round.badListSet (K:=K) (L:=L) C D Λ η e ⊆
        {ω : Round.Space K 𝓗 L | θv < ((keptEvidence K e ω).card : ℝ)} := by
      intro ω hω
      have hω' : (Λ:ℝ) * (1 - retention Λ C D K) + η * (Λ:ℝ)
          < ((Round.lost ω e).card : ℝ) := hω
      have hc := card_lost_le_keptEvidence (K:=K) (L:=L) e ω
      have hineq : (Λ:ℝ) * (1 - retention Λ C D K) + η * (Λ:ℝ) - 1
          < ((keptEvidence K e ω).card : ℝ) := by linarith
      show θv < ((keptEvidence K e ω).card : ℝ)
      rw [hθv]
      exact hineq
    have hmean' : Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
        ((keptEvidence K e ω).card : ℝ)) ≤ θv - (η/2) * (Λ:ℝ) := by
      have hkey : θv - (η/2)*(Λ:ℝ) = (Λ:ℝ)*(1 - retention Λ C D K) + η*(Λ:ℝ)/2 - 1 := by
        simp only [hθv]; ring
      rw [hkey]
      linarith [hmean, h4]
    have hvar' : 2 * Work.Deep.Conc.expect (fun f : Round.Space K 𝓗 L =>
        (((keptEvidence K e f).card : ℝ) - Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
          ((keptEvidence K e ω).card : ℝ))) ^ 2) + 2 ≤ ((η/2) * (Λ:ℝ)) ^ 2 / 4 := by
      have hEXle : Work.Deep.Conc.expect (fun ω : Round.Space K 𝓗 L =>
          ((keptEvidence K e ω).card : ℝ)) ≤ (Λ:ℝ) := by
        refine le_trans hmean ?_
        nlinarith [hret0, Nat.cast_nonneg (α := ℝ) Λ]
      have hΛR : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ1
      have hkey : 2 * (Λ:ℝ) + 2 ≤ ((η/2) * (Λ:ℝ)) ^ 2 / 4 := by
        rw [show ((η/2) * (Λ:ℝ)) ^ 2 / 4 = η^2 * (Λ:ℝ)^2 / 16 by ring]
        nlinarith [h64, hΛR, sq_nonneg η]
      nlinarith [hvarle, hEXle, hkey]
    have hbig' : (D:ℝ)^((1:ℝ)/4) + Real.log 2 ≤ ((η/2) * (Λ:ℝ))^2 / (32 * θv) := by
      have hθpos : 0 < θv := by simp only [hθv]; linarith [hθ1]
      have hnum : (D:ℝ)^((1:ℝ)/4) + Real.log 2 ≤ η^2 * (Λ:ℝ) / 256 := by linarith [h256]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 32 * θv)]
      have hθ2' : θv ≤ 2 * (Λ:ℝ) := by simp only [hθv]; exact hθ2
      have hstep1 : ((D:ℝ)^((1:ℝ)/4) + Real.log 2) * (32 * θv)
          ≤ (η^2 * (Λ:ℝ)/256) * (32 * θv) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      have hstep2 : (η^2 * (Λ:ℝ)/256) * (32 * θv)
          ≤ (η^2 * (Λ:ℝ)/256) * (32 * (2*(Λ:ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith [hθ2']) (by positivity)
      have hstep3 : (η^2 * (Λ:ℝ)/256) * (32 * (2*(Λ:ℝ))) = ((η/2) * (Λ:ℝ))^2 := by ring
      linarith [hstep1, hstep2, hstep3]
    have hθ1' : 1 ≤ θv := by simp only [hθv]; exact hθ1
    have hmain : Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L |
        θv < ((keptEvidence K e ω).card : ℝ)} ≤ Real.exp (-((D:ℝ)^((1:ℝ)/4))) :=
      probGtCertifiable (π := fun f : 𝓗 => Round.Coord K 𝓗 L f) hne
        (fun ω : Round.Space K 𝓗 L => ((keptEvidence K e ω).card : ℝ)) (by linarith : (0:ℝ) < η/2)
        (Nat.cast_nonneg Λ) hθ1' hmean' hvar' hlip hcert hbig'
    calc Work.Deep.Conc.prob (Round.badListSet (K:=K) (L:=L) C D Λ η e)
        ≤ Work.Deep.Conc.prob {ω : Round.Space K 𝓗 L | θv < ((keptEvidence K e ω).card : ℝ)} :=
          Work.Deep.Conc.prob_mono hsub
      _ ≤ Real.exp (-((D:ℝ)^((1:ℝ)/4))) := hmain

end

end Work.Deep.Kahn

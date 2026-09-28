import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Main.parts
import Submission.Work.HP.Q44Main.conj1_basic
import Submission.Work.HP.Q44Main.conj1_Nc
import Submission.Work.HP.Q44Main.witSet_ncard_le
import Submission.Work.HP.MDEstimates.latT_sum
import Submission.Work.HP.MDEstimates.latS_sum_irred
import Submission.Work.HP.Q44Main.latS_sum_red
import Submission.Work.HP.MDEstimates.reducible_forms

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
open Classical
namespace Work.HP.Q44Main
open Work.HP

/-- **First half of `quartic44`, `ℓ^{(1)}`-convenient route.** The unconditional
`ℓ^{(1)}` bound obtained from the witness decomposition and the T/S per-lattice counts. -/
theorem L1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M →
      (ell44 1 Z Δ M : ℝ)
        ≤ C * (M ^ 70 * Z ^ 4 * Δ ^ ((7 : ℝ) / 2) + M ^ 70 * Z ^ 6 * Δ ^ ((3 : ℝ) / 2)
              + M ^ 70 * Z ^ 4 * Δ ^ ((11 : ℝ) / 3) + M ^ 40 * Z ^ 4 * Δ ^ 3
              + M ^ 40 * Z ^ 6 * Δ ^ 2)
            * Real.log (2 * Δ) ^ 2 := by
  obtain ⟨CT, hCTpos, hCT⟩ := MDEstimates.latT_sum
  obtain ⟨CSi, hCSipos, hCSi⟩ := MDEstimates.latS_sum_irred
  obtain ⟨CSr, hCSrpos, hCSr⟩ := latS_sum_red
  obtain ⟨Kw, hKwpos, hKw⟩ := witSet_ncard_le
  obtain ⟨Kr, hKrpos, hKr⟩ := MDEstimates.reducible_forms
  obtain ⟨CTT, hCTTpos, hCTT⟩ := q44_perlat_T
  refine ⟨max (max (Kw * CSi) (Kr * CSr)) (CTT * Kw * CT) + 1, by positivity, ?_⟩
  intro Z Δ M hZ hΔ hM
  classical
  set W : Finset (Mon 4 4 → ℤ) := (witSet_finite M).toFinset with hW
  set Tw : Submodule ℤ (Fin 5 → ℤ) → ℝ :=
    fun L => (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2 with hTw
  have hlog0 : (0:ℝ) ≤ Real.log (2 * Δ) ^ 2 := sq_nonneg _
  -- ### step 1 + 2
  have hstep1 : (ell44 1 Z Δ M : ℝ)
      ≤ ∑ c ∈ W, (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ) :=
    ell44_one_le_witsum Z Δ M hZ
  have hstep2 : (∑ c ∈ W, (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ))
      ≤ ∑ c ∈ W, ((∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ))
          + (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ))) :=
    Finset.sum_le_sum (fun c _ => Nc_le' Z Δ c)
  -- ### S-part per c
  have hSper : ∀ c ∈ W,
      (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ))
        ≤ (if Irreducible (formOf 4 4 c)
            then CSi * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2
            else CSr * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2) := by
    intro c hc
    have hcne : c ≠ 0 := by
      rw [hW, Set.Finite.mem_toFinset] at hc; exact hc.1
    have hper : (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ))
        ≤ ∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((ballCount L Z : ℝ)) ^ 2 :=
      Finset.sum_le_sum (fun L _ => q44_perlat_S L Z)
    have hhyps : ∀ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L),
        IsPrimLat L ∧ rk L = 3 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ Z ∧ lam L 2 ≤ Z ∧ c ∈ vanishOn L := by
      intro L hL
      rw [Finset.mem_filter] at hL
      obtain ⟨hLU, hLv⟩ := hL
      obtain ⟨h1, h2, h3, h4, h5⟩ := Ufam_spec hLU
      exact ⟨h1, h2, h3, h4, h5, hLv⟩
    by_cases hirr : Irreducible (formOf 4 4 c)
    · rw [if_pos hirr]
      exact hper.trans (hCSi Z Δ hZ hΔ c hirr _ hhyps)
    · rw [if_neg hirr]
      exact hper.trans (hCSr Z Δ hZ hΔ c hcne hirr _ hhyps)
  -- ### T-part per c
  have hTper : ∀ c ∈ W,
      (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ))
        ≤ ∑ L ∈ Ufam Z Δ, (if c ∈ vanishOn L then 0 else CTT * Tw L) := by
    intro c _
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun L hL => ?_)
    by_cases h : c ∈ vanishOn L
    · rw [if_neg (by intro hc; exact hc h), if_pos h]
    · rw [if_pos h, if_neg h]
      exact le_trans (hCTT L (Ufam_spec hL).2.1 c h Z hZ) (le_of_eq (by rw [hTw]; ring))
  have hUfin : ∀ L ∈ Ufam Z Δ, L ∈ Ufam Z Δ := fun L h => h
  -- ### W card bounds
  have hWcard_nat : W.card = (witSet M).ncard := by
    rw [hW, ← Set.ncard_eq_toFinset_card (witSet M) (witSet_finite M)]
  have hWcard : ((W.card : ℕ) : ℝ) ≤ Kw * M ^ 70 := by
    rw [hWcard_nat]; exact hKw M hM
  have hWcardIrred : (((W.filter (fun c => Irreducible (formOf 4 4 c))).card : ℕ) : ℝ) ≤ Kw * M ^ 70 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) hWcard
  have hRfin : ({c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M ∧ ¬ Irreducible (formOf 4 4 c)} : Set _).Finite :=
    (witSet_finite M).subset (fun c hc => ⟨hc.1, hc.2.1⟩)
  have hWcardRed : (((W.filter (fun c => ¬ Irreducible (formOf 4 4 c))).card : ℕ) : ℝ) ≤ Kr * M ^ 40 := by
    have hsub : ((W.filter (fun c => ¬ Irreducible (formOf 4 4 c)) : Finset _) : Set _) ⊆
        ({c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M ∧ ¬ Irreducible (formOf 4 4 c)} : Set _) := by
      intro c hc
      rw [Finset.mem_coe, Finset.mem_filter, hW, Set.Finite.mem_toFinset] at hc
      exact ⟨hc.1.1, hc.1.2, hc.2⟩
    have hle := Set.ncard_le_ncard hsub hRfin
    rw [Set.ncard_coe_finset] at hle
    exact le_trans (by exact_mod_cast hle) (hKr M hM)
  -- ### S-part total
  have hStot : (∑ c ∈ W, (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))
      ≤ (Kw * M ^ 70) * (CSi * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
        + (Kr * M ^ 40) * (CSr * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2) := by
    have hsplit : (∑ c ∈ W, (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))
        = (∑ c ∈ W.filter (fun c => Irreducible (formOf 4 4 c)),
              (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))
          + (∑ c ∈ W.filter (fun c => ¬ Irreducible (formOf 4 4 c)),
              (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ))) := by
      rw [← Finset.sum_filter_add_sum_filter_not W (fun c => Irreducible (formOf 4 4 c))
        (fun c => (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))]
    rw [hsplit]
    refine add_le_add ?_ ?_
    · have h1 : (∑ c ∈ W.filter (fun c => Irreducible (formOf 4 4 c)),
            (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))
          ≤ ∑ c ∈ W.filter (fun c => Irreducible (formOf 4 4 c)),
              (CSi * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2) := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        have := hSper c (Finset.mem_filter.mp hc).1
        rwa [if_pos (Finset.mem_filter.mp hc).2] at this
      refine h1.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hWcardIrred (by positivity)
    · have h1 : (∑ c ∈ W.filter (fun c => ¬ Irreducible (formOf 4 4 c)),
            (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))
          ≤ ∑ c ∈ W.filter (fun c => ¬ Irreducible (formOf 4 4 c)),
              (CSr * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2) := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        have := hSper c (Finset.mem_filter.mp hc).1
        rwa [if_neg (Finset.mem_filter.mp hc).2] at this
      refine h1.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hWcardRed (by positivity)
  -- ### T-part total
  have hTtot : (∑ c ∈ W, (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ)))
      ≤ (Kw * M ^ 70) * (CTT * CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) := by
    have h1 : (∑ c ∈ W, (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ)))
        ≤ ∑ c ∈ W, ∑ L ∈ Ufam Z Δ, (if c ∈ vanishOn L then 0 else CTT * Tw L) :=
      Finset.sum_le_sum hTper
    have h2 : (∑ c ∈ W, ∑ L ∈ Ufam Z Δ, (if c ∈ vanishOn L then 0 else CTT * Tw L))
        ≤ ∑ L ∈ Ufam Z Δ, ((W.card : ℕ) : ℝ) * (CTT * Tw L) := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum (fun L _ => ?_)
      have heq : (∑ x ∈ W, if x ∈ vanishOn L then 0 else CTT * Tw L)
          = ∑ x ∈ W.filter (fun x => x ∉ vanishOn L), (CTT * Tw L) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : x ∈ vanishOn L
        · rw [if_pos hx, if_neg (by intro hc; exact hc hx)]
        · rw [if_neg hx, if_pos hx]
      rw [heq, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (by rw [hTw]; positivity)
    refine h1.trans (h2.trans ?_)
    have hbag : (∑ L ∈ Ufam Z Δ, ((W.card : ℕ) : ℝ) * (CTT * Tw L))
        = ((W.card : ℕ) : ℝ) * (CTT * ∑ L ∈ Ufam Z Δ, Tw L) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hbag]
    have h4 : (∑ L ∈ Ufam Z Δ, Tw L) ≤ CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2 :=
      hCT Z Δ hZ hΔ (Ufam Z Δ) (fun L hL => Ufam_spec hL)
    have hCTpos' : (0:ℝ) ≤ CTT * CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2 := by positivity
    calc ((W.card : ℕ) : ℝ) * (CTT * ∑ L ∈ Ufam Z Δ, Tw L)
        = (((W.card : ℕ) : ℝ) * CTT) * (∑ L ∈ Ufam Z Δ, Tw L) := by ring
      _ ≤ ((Kw * M ^ 70) * CTT) * (CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hWcard hCTTpos.le) h4 (by positivity) (by positivity)
      _ = (Kw * M ^ 70) * (CTT * CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) := by ring
  -- ### final assembly
  set Cc : ℝ := max (max (Kw * CSi) (Kr * CSr)) (CTT * Kw * CT) + 1 with hCc
  have hCcKw : Kw * CSi ≤ Cc := by
    rw [hCc]
    have a := le_max_left (Kw * CSi) (Kr * CSr)
    have b := le_max_left (max (Kw * CSi) (Kr * CSr)) (CTT * Kw * CT)
    linarith
  have hCcKr : Kr * CSr ≤ Cc := by
    rw [hCc]
    have a := le_max_right (Kw * CSi) (Kr * CSr)
    have b := le_max_left (max (Kw * CSi) (Kr * CSr)) (CTT * Kw * CT)
    linarith
  have hCcCT : CTT * Kw * CT ≤ Cc := by
    rw [hCc]
    have b := le_max_right (max (Kw * CSi) (Kr * CSr)) (CTT * Kw * CT)
    linarith
  have key : (Kw * M ^ 70) * (CSi * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
        + (Kr * M ^ 40) * (CSr * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2)
        + (Kw * M ^ 70) * (CTT * CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2)
      ≤ Cc * ((M ^ 70 * Z ^ 4 * Δ ^ ((7:ℝ)/2) + M ^ 70 * Z ^ 6 * Δ ^ ((3:ℝ)/2))
          + M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3)
          + (M ^ 40 * Z ^ 4 * Δ ^ 3 + M ^ 40 * Z ^ 6 * Δ ^ 2)) * Real.log (2*Δ)^2 := by
    have e1 : (Kw * M ^ 70) * (CSi * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
        = (Kw * CSi) * (M ^ 70 * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2) := by ring
    have e2 : (Kr * M ^ 40) * (CSr * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2)
        = (Kr * CSr) * (M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2) := by ring
    have e3 : (Kw * M ^ 70) * (CTT * CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2)
        = (CTT * Kw * CT) * (M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) := by ring
    have t1 : (Kw * CSi) * (M ^ 70 * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
        ≤ Cc * (M ^ 70 * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2) :=
      mul_le_mul_of_nonneg_right hCcKw (by positivity)
    have t2 : (Kr * CSr) * (M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2)
        ≤ Cc * (M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2) :=
      mul_le_mul_of_nonneg_right hCcKr (by positivity)
    have t3 : (CTT * Kw * CT) * (M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2)
        ≤ Cc * (M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) :=
      mul_le_mul_of_nonneg_right hCcCT (by positivity)
    have hsum : (Kw * CSi) * (M ^ 70 * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
          + (Kr * CSr) * (M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2)
          + (CTT * Kw * CT) * (M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2)
        ≤ Cc * (M ^ 70 * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
          + Cc * (M ^ 40 * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2)
          + Cc * (M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) := by linarith [t1, t2, t3]
    rw [e1, e2, e3]
    refine hsum.trans (le_of_eq ?_)
    ring
  calc (ell44 1 Z Δ M : ℝ)
      ≤ ∑ c ∈ W, (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p ∈ Q44Pair Z Δ ∧ c ∈ Gam 4 4 p.1 p.2} : Set _).ncard : ℝ) := hstep1
    _ ≤ ∑ c ∈ W, ((∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ))
          + (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ))) := hstep2
    _ = (∑ c ∈ W, (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∈ vanishOn L), ((pairSetS L Z).ncard : ℝ)))
        + (∑ c ∈ W, (∑ L ∈ (Ufam Z Δ).filter (fun L => c ∉ vanishOn L), ((pairSetT L c Z).ncard : ℝ))) :=
        Finset.sum_add_distrib
    _ ≤ ((Kw * M ^ 70) * (CSi * (Z ^ 4 * Δ ^ ((7:ℝ)/2) + Z ^ 6 * Δ ^ ((3:ℝ)/2)) * Real.log (2*Δ)^2)
          + (Kr * M ^ 40) * (CSr * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2*Δ)^2))
        + (Kw * M ^ 70) * (CTT * CT * Z ^ 4 * Δ ^ ((11:ℝ)/3) * Real.log (2*Δ)^2) :=
        add_le_add hStot hTtot
    _ ≤ Cc * ((M ^ 70 * Z ^ 4 * Δ ^ ((7:ℝ)/2) + M ^ 70 * Z ^ 6 * Δ ^ ((3:ℝ)/2))
          + M ^ 70 * Z ^ 4 * Δ ^ ((11:ℝ)/3)
          + (M ^ 40 * Z ^ 4 * Δ ^ 3 + M ^ 40 * Z ^ 6 * Δ ^ 2)) * Real.log (2*Δ)^2 := key
    _ = Cc * (M ^ 70 * Z ^ 4 * Δ ^ ((7 : ℝ) / 2) + M ^ 70 * Z ^ 6 * Δ ^ ((3 : ℝ) / 2)
              + M ^ 70 * Z ^ 4 * Δ ^ ((11 : ℝ) / 3) + M ^ 40 * Z ^ 4 * Δ ^ 3
              + M ^ 40 * Z ^ 6 * Δ ^ 2)
            * Real.log (2 * Δ) ^ 2 := by ring

end Work.HP.Q44Main

import Mathlib
import Submission.Work.Prop36SW.roundStmtW
import Submission.Work.Peluse.Prop36SW.roundUnpeel
import Submission.Work.Peluse.Prop36SW.peelStrengthLower
import Submission.Work.Peluse.Prop36SW.roundBase

/-!
# `roundPeelAuxW`: the round of the §5 chain with window bounds

`Work.Peluse.Prop36SW.RoundStmtW m` (`roundStmtW.lean`) is `RoundStmtT m` with the existential
bundle extended by three data-independent constants `c₀ > 0`, `E₀ : ℕ`, `C₁ ≥ 1` and the two window
bounds

    `∀ s, c₀ · γ^{E₀} · M₁ · M₂ ≤ Lw s`   and   `∀ s, (Lw s : ℝ) ≤ C₁ · M₁ · M₂`.

This file proves

    `Work.Prop36SW.roundPeelAuxW : PeluseLadderA → ∀ m, RoundStmtW (m+1)`

by replaying the proof of the proved `Work.Prop36SW.roundPeelAuxT` with the two window conjuncts
carried through (the level bound `T` and the main box-norm bound are *verbatim* those of `T`):

* `roundPeelStepW` — the peel branch.  The peeled slot's window is `L' = ⌊γ' M₁ M₂⌋` with
  `γ' = γ^K/C₀`.  Lower bound: the threshold gives `2 ≤ γ' M₁` (as in `roundPeelStepT`), hence
  `x := γ'M₁M₂ ≥ 2 M₂ ≥ 2`, and `⌊x⌋ ≥ x - 1 ≥ x/2`, i.e. `L' ≥ γ^K M₁M₂/(2C₀)`; upper bound:
  `L' ≤ γ'M₁M₂ ≤ M₁M₂/C₀` because `γ ≤ 1`.  The inherited slots use the induction hypothesis's two
  bounds, transported along `γ₁ ≥ cc₂ γ^{Ae}`.
* `roundInfeasibleStepW` — the non-peelable branch, where the round's window is `Lw ≡ ⌊γ'M₁M₂⌋`;
  there the lower bound uses `L' ≥ M₂ ≥ 1`, i.e. `x ≥ 1`, and `⌊x⌋ ≥ x/2` for `x ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-! ## Window arithmetic

The two facts about `⌊·⌋` used for the lower window bound: `⌊x⌋ ≤ x`, and `x/2 ≤ ⌊x⌋` for `1 ≤ x`
(for `1 ≤ x ≤ 2` the floor is at least `1 ≥ x/2`, for `x ≥ 2` it is at least `x - 1 ≥ x/2`). -/

/-- `⌊x⌋₊ ≤ x` for `0 ≤ x`. -/
private lemma toNat_floor_le {x : ℝ} (hx : 0 ≤ x) :
    (((⌊x⌋).toNat : ℕ) : ℝ) ≤ x := by
  have h2 : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have hcast : (((⌊x⌋).toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]
  rw [hcast]
  exact Int.floor_le x

/-- `x / 2 ≤ ⌊x⌋₊` for `1 ≤ x`. -/
private lemma half_le_toNat_floor {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (((⌊x⌋).toNat : ℕ) : ℝ) := by
  have h0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have h2 : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr h0
  have hcast : (((⌊x⌋).toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]
  rw [hcast]
  rcases le_or_gt x 2 with h | h
  · have h3 : (1 : ℤ) ≤ ⌊x⌋ := (Int.le_floor (a := x) (z := 1)).mpr (by push_cast; exact hx)
    have h1 : (1 : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h3
    linarith
  · have h1 := Int.sub_one_lt_floor x
    linarith

/-! ## Arithmetic helpers (private copies of the ones of `roundPeelAuxT.lean`) -/

/-- `γ · (γ^K/C) = γ^(K+1)/C`. -/
private lemma mul_powK_div (γ C : ℝ) (K : ℕ) : γ * (γ ^ K / C) = γ ^ (K + 1) / C := by
  rw [← mul_div_assoc, ← pow_succ']

/-- `(γ^(K+1)/C)^(-K) = C^K · γ^(-K(K+1))`. -/
private lemma zpow_neg_div (γ C : ℝ) (K : ℕ) :
    (γ ^ (K + 1) / C) ^ (-(K : ℤ)) = C ^ K * γ ^ (-((K * (K + 1) : ℕ) : ℤ)) := by
  have hpow : (γ ^ (K + 1) / C) ^ K = γ ^ ((K + 1) * K) / C ^ K := by
    rw [div_pow, pow_mul]
  rw [zpow_neg, zpow_natCast, hpow, inv_div, div_eq_mul_inv]
  rw [show (γ ^ ((K + 1) * K))⁻¹ = γ ^ (-(((K + 1) * K : ℕ) : ℤ)) by
    rw [← zpow_natCast, ← zpow_neg]]
  congr 2
  push_cast
  ring

/-- The window factor is at least `2`: `(Cn · γ^(-Mn)) · (γ^K/C₀) ≥ 2` when `Cn ≥ 2C₀` and
`Mn ≥ K` (and `0 < γ ≤ 1`). -/
private lemma window_ge_two (γ C₀ Cn : ℝ) (K Mn : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hC₀ : 0 < C₀) (hCn : 2 * C₀ ≤ Cn) (hMn : K ≤ Mn) :
    (2 : ℝ) ≤ (Cn * γ ^ (-(Mn : ℤ))) * (γ ^ K / C₀) := by
  have hz : (1 : ℝ) ≤ γ ^ K * γ ^ (-(Mn : ℤ)) := by
    have h := zpow_le_zpow_right_of_le_one₀ hγ0 hγ1
      (show ((K : ℤ) - Mn) ≤ 0 from by omega)
    rw [zpow_sub₀ (ne_of_gt hγ0),
      show (γ : ℝ) ^ (K : ℤ) = γ ^ K by rw [zpow_natCast],
      div_eq_mul_inv,
      show (γ ^ (Mn : ℤ))⁻¹ = γ ^ (-(Mn : ℤ)) by rw [← zpow_neg]] at h
    simpa using h
  have h1 : 2 * (γ ^ (-(Mn : ℤ)) * γ ^ K) ≤ (Cn * γ ^ (-(Mn : ℤ))) * (γ ^ K / C₀) := by
    rw [← mul_div_assoc, le_div_iff₀ hC₀]
    have h2 : (2 * (γ ^ (-(Mn : ℤ)) * γ ^ K)) * C₀
        = (2 * C₀) * (γ ^ (-(Mn : ℤ)) * γ ^ K) := by ring
    rw [h2, show Cn * γ ^ (-(Mn : ℤ)) * γ ^ K
        = Cn * (γ ^ (-(Mn : ℤ)) * γ ^ K) by ring]
    exact mul_le_mul_of_nonneg_right hCn (by positivity)
  have h3 : (2 : ℝ) ≤ 2 * (γ ^ (-(Mn : ℤ)) * γ ^ K) := by
    have h := hz
    rw [mul_comm] at h
    linarith
  linarith

/-- The ladder's non-degeneracy at the per-peel window: `C₀(γ γ')^(-K) ≤ Cn γ^(-Mn)` for
`γ' = γ^K/C₀`, `Cn ≥ C₀^(K+1)`, `Mn ≥ K(K+1)`. -/
private lemma nondeg_of (γ C₀ Cn : ℝ) (K Mn : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hC₀ : 0 < C₀)
    (hCn : C₀ ^ (K + 1) ≤ Cn) (hMn : K * (K + 1) ≤ Mn) :
    C₀ * (γ * (γ ^ K / C₀)) ^ (-(K : ℤ)) ≤ Cn * γ ^ (-(Mn : ℤ)) := by
  have hmul : γ * (γ ^ K / C₀) = γ ^ (K + 1) / C₀ := mul_powK_div γ C₀ K
  rw [hmul, zpow_neg_div]
  have hmono : γ ^ (-((K * (K + 1) : ℕ) : ℤ)) ≤ γ ^ (-(Mn : ℤ)) :=
    zpow_le_zpow_right_of_le_one₀ hγ0 hγ1 (by
      have h : ((K * (K + 1) : ℕ) : ℤ) ≤ (Mn : ℤ) := by exact_mod_cast hMn
      omega)
  have hrew : C₀ * (C₀ ^ K * γ ^ (-((K * (K + 1) : ℕ) : ℤ)))
      = C₀ ^ (K + 1) * γ ^ (-((K * (K + 1) : ℕ) : ℤ)) := by
    rw [pow_succ]; ring
  rw [hrew]
  exact mul_le_mul hCn hmono (zpow_nonneg hγ0.le _)
    (le_of_lt (lt_of_lt_of_le (by positivity) hCn))

/-- `card (Slot ι (fun _ => 1)) = card ι`. -/
private lemma card_slot_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    Fintype.card (Slot ι (fun _ => 1)) = Fintype.card ι := by
  simp only [Slot, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, smul_eq_mul]
  simp

/-- The cardinality of `PeelSlot s₀` is one less than the cardinality of the slot type. -/
private lemma card_peelSlot {ι : Type} [Fintype ι] [DecidableEq ι]
    (s₀ : Slot ι (fun _ => 1)) :
    Fintype.card (PeelSlot s₀) + 1 = Fintype.card (Slot ι (fun _ => 1)) := by
  have h1 : 0 < Fintype.card (Slot ι (fun _ => 1)) := Fintype.card_pos_iff.mpr ⟨s₀⟩
  rw [Fintype.card_subtype_compl (fun x : Slot ι (fun _ => 1) => x = s₀),
    Fintype.card_subtype_eq]
  omega

/-! ## Index-type helpers for the infeasible round -/

/-- **Cardinality of the direction index when only one slot is active.**  For `t s = L` at the single
slot `s₀` and `t s = 0` elsewhere, the total number of directions is `L`. -/
private lemma card_sigma_fin_ite {ι : Type} [Fintype ι] [DecidableEq ι] (s₀ : ι) (L : ℕ) :
    Fintype.card (Σ s : ι, Fin (if s = s₀ then L else 0)) = L := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_ite_eq' Finset.univ s₀ (fun _ => L)]
  simp

/-- **The slot of any direction is the active one.**  If the multiplicities `t` vanish off `s₀`, then
every direction index `i` of the sigma type `Σ s, Fin (t s)` has first component `s₀`. -/
private lemma fst_equivFin_sigma_of_single {ι : Type} [Fintype ι] [DecidableEq ι]
    {t : ι → ℕ} (s₀ : ι) (h : ∀ s, s ≠ s₀ → t s = 0) :
    ∀ i : Fin (Fintype.card (Σ s : ι, Fin (t s))),
      ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 = s₀ := by
  intro i
  obtain ⟨s, j⟩ := (Fintype.equivFin (Σ s : ι, Fin (t s))).symm i
  show s = s₀
  by_contra hne
  haveI : IsEmpty (Fin (t s)) := by rw [h s hne]; infer_instance
  exact isEmptyElim j

/-! ## The peelable case -/

/-- **The peel branch of the round, with the level bound and the window bounds.**  At the datum
`(ι, kω, p, Dc)` with `Fintype.card ι = m+2` and a *peelable* slot `s₀`, the induction hypothesis
`RoundStmtW (m+1)` at the peeled slot type `PeelSlot s₀` gives the round's conclusion together with a
data-independent bound `T = max t' T'` for the multiplicities, the level `t'` (the ladder's) and the
two window bounds (the peeled slot's window `⌊γ'M₁M₂⌋`, the other slots' the sub-round's). -/
theorem roundPeelStepW (h : Work.Peluse.C46.PeluseLadderA) (m : ℕ)
    (ih : Work.Peluse.Prop36SW.RoundStmtW (m + 1))
    {ι : Type} [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι = m + 2)
    (n : ℕ) (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (Dc : ℕ)
    (s₀ : Slot ι (fun _ => 1))
    (hB : 1 ≤ Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀)) :
    ∃ (C : ℝ) (E : ℕ) (Cn : ℝ) (Mn : ℕ) (T : ℕ) (c₀ : ℝ) (E₀ : ℕ) (C₁ : ℝ),
      0 < C ∧ 0 < Cn ∧ 1 ≤ Mn ∧ 1 ≤ T ∧ 0 < c₀ ∧ 1 ≤ C₁ ∧
      ∀ (M₁ M₂ N : ℕ) (A : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℤ → ℂ) (γ : ℝ),
        Work.Peluse.Prop36SW.LStateAbs kω p M₁ M₂ N Dc A g γ →
        Cn * γ ^ (-(Mn : ℤ)) ≤ (M₂ : ℝ) →
        ∃ (t : ι → ℕ) (Lw : ι → ℕ) (N' : ℕ),
          (∀ s : ι, t s ≤ T) ∧
          1 ≤ Fintype.card (Σ s : ι, Fin (t s)) ∧ (∀ s : ι, M₂ ≤ Lw s) ∧ N ≤ N' ∧
          (∀ s : ι, c₀ * γ ^ E₀ * (M₁ : ℝ) * (M₂ : ℝ) ≤ (Lw s : ℝ)) ∧
          (∀ s : ι, (Lw s : ℝ) ≤ C₁ * (M₁ : ℝ) * (M₂ : ℝ)) ∧
          C * γ ^ E ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
            Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
              (fun i => Work.Peluse.arithIcc
                (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
                (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1))
              (Work.Peluse.symIcc N') (g a) := by
  obtain ⟨K, C₀, t', c, hK, hC₀, ht', hc, H⟩ :=
    h (k := fun _ : ι => 1) (p := fun i a'' => |p i a''|) kω Dc
  have key : ∀ s : ι, s ≠ s₀.1 → (⟨s, 0⟩ : Slot ι (fun _ => 1)) ≠ s₀ := by
    intro s hs hc
    exact hs (by simpa using congrArg (fun x : Slot ι (fun _ => 1) => x.1) hc)
  have key2 : ∀ x : Slot ι (fun _ => 1), x.1 = s₀.1 → x = s₀ :=
    fun x hx => Sigma.ext hx (heq_of_eq (Subsingleton.elim _ _))
  have hcardP : Fintype.card (PeelSlot s₀) = m + 1 := by
    have h := card_peelSlot s₀
    rw [card_slot_one, hcard] at h
    omega
  obtain ⟨C', E', Cn', Mn', T', c₀', E₀', C₁', hC'pos, hCn'pos, hMn'1, hT'1, hc₀'0, hC₁'1, ih'⟩ :=
    ih (PeelSlot s₀) hcardP (n + 2 * t') (peelKω kω s₀) (peelPFin p t' s₀) Dc
  set Q : ℕ := Fintype.card (ConclIdx s₀ kω t') with hQ
  set sh : ℕ := Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀) with hsh
  set Ae : ℕ := K * (K + 1) * 2 ^ Q with hAe
  obtain ⟨cc₂, hcc₂0, hcc₂⟩ := peelStrengthLower Dc K t' Q sh C₀ c hC₀ hc
  set CnCmd : ℝ := max (Cn' * cc₂ ^ (-(Mn' : ℤ))) (max (2 * (C₀ : ℝ)) ((C₀ : ℝ) ^ (K + 1)))
    with hCnCmd
  set c₀W : ℝ := min (1 / (2 * (C₀ : ℝ))) (c₀' * cc₂ ^ E₀') with hc₀W
  set E₀W : ℕ := max K (Ae * E₀') with hE₀W
  set C₁W : ℝ := max (max 1 (1 / (C₀ : ℝ))) C₁' with hC₁W
  have hAe1 : 1 ≤ Ae := by
    rw [hAe]
    have h2 : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
    have h3 : 1 ≤ K + 1 := by omega
    calc (1 : ℕ) = 1 * 1 * 1 := by ring
      _ ≤ K * (K + 1) * 2 ^ Q := Nat.mul_le_mul (Nat.mul_le_mul hK h3) h2
  refine ⟨C' * cc₂ ^ E', Ae * E', CnCmd, Ae * Mn', max t' T', c₀W, E₀W, C₁W,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hC'pos (pow_pos hcc₂0 _)
  · rw [hCnCmd]
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * (C₀ : ℝ))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ Ae * Mn' := Nat.mul_le_mul hAe1 hMn'1
  · exact le_trans ht' (le_max_left _ _)
  · rw [hc₀W]
    exact lt_min (by positivity) (mul_pos hc₀'0 (pow_pos hcc₂0 _))
  · rw [hC₁W]
    exact le_trans (le_max_left (1 : ℝ) (1 / (C₀ : ℝ))) (le_max_left _ _)
  intro M₁ M₂ N A g γ hst hthr
  have hstkeep : LStateAbs kω p M₁ M₂ N Dc A g γ := hst
  obtain ⟨hγ0, hγ1, hM₂1, hM₂M₁, hN1, hM₁M₂N, hp, hpl, hpa, hg1, hg2, hfam⟩ := hstkeep
  -- the level threshold
  have hthr' : CnCmd * γ ^ (-((Ae * Mn' : ℕ) : ℤ)) ≤ (M₂ : ℝ) := hthr
  have hCnBig : (C₀ : ℝ) ^ (K + 1) ≤ CnCmd := by
    rw [hCnCmd]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCn2 : 2 * (C₀ : ℝ) ≤ CnCmd := by
    rw [hCnCmd]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCnCn' : Cn' * cc₂ ^ (-(Mn' : ℤ)) ≤ CnCmd := by
    rw [hCnCmd]; exact le_max_left _ _
  -- the window factor and the ladder threshold
  set γ' : ℝ := γ ^ K / (C₀ : ℝ) with hγ'def
  have hγ'0 : 0 < γ' := by rw [hγ'def]; positivity
  have hC₀γ' : C₀ * γ' = γ ^ K := by rw [hγ'def]; field_simp
  have hMn_ge : K * (K + 1) ≤ Ae * Mn' := by
    have h2 : 1 ≤ 2 ^ Q := Nat.one_le_two_pow
    calc K * (K + 1) = K * (K + 1) * 1 := (mul_one _).symm
      _ ≤ K * (K + 1) * 2 ^ Q := Nat.mul_le_mul_left _ h2
      _ = Ae := by rw [hAe]
      _ ≤ Ae * Mn' := Nat.le_mul_of_pos_right _ hMn'1
  have hMnK : K ≤ Ae * Mn' := le_trans (by nlinarith : K ≤ K * (K + 1)) hMn_ge
  have hnd : C₀ * (γ * γ') ^ (-(K : ℤ)) ≤ (M₂ : ℝ) := by
    rw [hγ'def]
    exact le_trans (nondeg_of γ C₀ CnCmd K (Ae * Mn') hγ0 hγ1 hC₀ hCnBig hMn_ge) hthr'
  -- the ladder, applied to `|p|`
  have habs := (lstateAbsAbsIff (kω := kω) p M₁ M₂ N Dc A g γ).mp hst
  have hfamAbs := habs.2.2.2.2.2.2.2.2.2.2.2
  have hconclAbs := H A M₁ M₂ N γ γ' g hM₂1 hM₂M₁ hN1 hM₁M₂N hγ0 hγ1 hγ'0 (le_of_eq hC₀γ')
    (fun i a ha => abs_pos.mpr (hp i a ha))
    (fun i a ha => hpl i a ha)
    (fun i a ha => by simpa only [abs_abs] using hpa i a ha)
    (fun a ha x => hg1 a ha x) (fun a ha => hg2 a ha) hnd hfamAbs s₀
  -- the sign transfer of the conclusion
  have hconcl : c * (γ * γ') ^ K ≤ ((A.card : ℝ))⁻¹
      * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
        Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
          (fun i => conclDirG p M₁ M₂ γ' s₀ t' a b
            ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
          (Work.Peluse.symIcc N) (g a) := by
    have hsum : (∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun i => conclDirG (fun i a'' => |p i a''|) M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
            (Work.Peluse.symIcc N) (g a))
        = (∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun i => conclDirG p M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
            (Work.Peluse.symIcc N) (g a)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      exact (sum_paramBox_boxNorm_conclDirG_abs kω p M₁ M₂ γ' s₀ t' a
        (Work.Peluse.symIcc N) (g a)).symm
    rw [← hsum]
    exact hconclAbs
  -- the window condition of the peeled slot
  have hM₁big : CnCmd * γ ^ (-((Ae * Mn' : ℕ) : ℤ)) ≤ (M₁ : ℝ) :=
    le_trans hthr' (by exact_mod_cast hM₂M₁)
  have hbig : (2 : ℝ) ≤ γ' * (M₁ : ℝ) := by
    have h := window_ge_two γ C₀ CnCmd K (Ae * Mn') hγ0 hγ1 hC₀ hCn2 hMnK
    have h2 : (CnCmd * γ ^ (-((Ae * Mn' : ℕ) : ℤ))) * γ' ≤ (M₁ : ℝ) * γ' :=
      mul_le_mul_of_nonneg_right hM₁big hγ'0.le
    rw [← hγ'def] at h
    linarith [h, h2]
  have hM₂win : M₂ ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
    have hfloor : (M₂ : ℤ) ≤ ⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋ := by
      refine Int.le_floor.mpr ?_
      have h2 : 2 * (M₂ : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := by nlinarith [hbig, hM₂1]
      push_cast
      linarith
    omega
  have hLwin : 1 ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := le_trans hM₂1 hM₂win
  -- the peel
  have hst' := lstatePeelFin kω p M₁ M₂ N Dc A g γ γ' (c * (γ * γ') ^ K) t' s₀
    hst hγ'0 (mul_pos hc (pow_pos (mul_pos hγ0 hγ'0) K)) ht' hLwin hB hconcl
  -- the new strength
  set γ₁ : ℝ := min ((((Work.Peluse.symIcc N).card : ℝ) /
      ((Work.Peluse.symIcc (peelN N Dc t' γ')).card : ℝ)) ^ (1 / (2 : ℝ) ^ sh) *
      (c * (γ * γ') ^ K) ^ (2 ^ Q)) 1 with hγ₁def
  have hγ₁ge : cc₂ * γ ^ Ae ≤ γ₁ := by
    rw [hγ₁def, hAe]
    exact hcc₂ N γ hN1 hγ0 hγ1
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le (mul_pos hcc₂0 (pow_pos hγ0 Ae)) hγ₁ge
  have hγ₁1 : γ₁ ≤ 1 := by rw [hγ₁def]; exact min_le_right _ _
  have hγpart : (γ ^ Ae) ^ (-(Mn' : ℤ)) = γ ^ (-((Ae * Mn' : ℕ) : ℤ)) := by
    rw [← zpow_natCast γ Ae, ← zpow_mul]
    congr 1
    push_cast
    ring
  -- the threshold at the peeled level
  have hthrInner : Cn' * γ₁ ^ (-(Mn' : ℤ)) ≤ (M₂ : ℝ) := by
    have hb1 : cc₂ * γ ^ Ae ≤ 1 :=
      le_trans (hcc₂ N γ hN1 hγ0 hγ1) (min_le_right _ _)
    have h2 : γ₁ ^ (-(Mn' : ℤ)) ≤ (cc₂ * γ ^ Ae) ^ (-(Mn' : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hγ₁ge Mn')
    have h4 : (cc₂ * γ ^ Ae) ^ (-(Mn' : ℤ))
        = cc₂ ^ (-(Mn' : ℤ)) * γ ^ (-((Ae * Mn' : ℕ) : ℤ)) := by
      rw [mul_zpow, hγpart]
    calc Cn' * γ₁ ^ (-(Mn' : ℤ))
        ≤ Cn' * (cc₂ * γ ^ Ae) ^ (-(Mn' : ℤ)) := mul_le_mul_of_nonneg_left h2 hCn'pos.le
      _ = Cn' * (cc₂ ^ (-(Mn' : ℤ)) * γ ^ (-((Ae * Mn' : ℕ) : ℤ))) := by rw [h4]
      _ = Cn' * cc₂ ^ (-(Mn' : ℤ)) * γ ^ (-((Ae * Mn' : ℕ) : ℤ)) := by ring
      _ ≤ CnCmd * γ ^ (-((Ae * Mn' : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_right hCnCn' (by positivity)
      _ ≤ (M₂ : ℝ) := hthr'
  -- the peeled round
  obtain ⟨trest, Lrest, N'', hboundt, hmm, hLrestM₂, hN₁N'', hLrestLow, hLrestUp, hinner⟩ :=
    ih' M₁ M₂ (peelN N Dc t' γ') (shiftSetFin p M₁ M₂ A γ' t' s₀) (peelGFin t' g) γ₁
      hst' hthrInner
  -- the reindexed multiplicities and windows
  set t : ι → ℕ := fun s => if h : s = s₀.1 then t'
    else trest ⟨⟨s, 0⟩, key s h⟩ with htdef
  set Lw : ι → ℕ := fun s => if h : s = s₀.1 then (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat
    else Lrest ⟨⟨s, 0⟩, key s h⟩ with hLwdef
  have ht0 : t s₀.1 = t' := by rw [htdef]; exact dif_pos rfl
  have hL0 : Lw s₀.1 = (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
    rw [hLwdef]; exact dif_pos rfl
  have ht'' : ∀ s : PeelSlot s₀, t s.1.1 = trest s := by
    intro s
    rw [htdef]
    dsimp only
    split_ifs with hc
    · exact absurd (key2 s.1 hc) s.2
    · congr 1
      exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))
  have hLw'' : ∀ s : PeelSlot s₀, Lw s.1.1 = Lrest s := by
    intro s
    rw [hLwdef]
    dsimp only
    split_ifs with hc
    · exact absurd (key2 s.1 hc) s.2
    · congr 1
      exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))
  refine ⟨t, Lw, N'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [htdef]; dsimp only
    split_ifs with h
    · exact le_max_left _ _
    · exact le_trans (hboundt ⟨⟨s, 0⟩, key s h⟩) (le_max_right _ _)
  · exact Fintype.card_pos_iff.mpr ⟨⟨s₀.1, ⟨0, by rw [ht0]; omega⟩⟩⟩
  · intro s; rw [hLwdef]; dsimp only; split_ifs with h
    · exact hM₂win
    · exact hLrestM₂ _
  · exact le_trans (Nat.le_mul_of_pos_right N (by omega)) hN₁N''
  · -- the lower window bound
    intro s
    rw [hLwdef]; dsimp only; split_ifs with hs
    · -- the peeled slot
      have hx1 : (1 : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
        have hM₂1' : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM₂1
        have h2 : (2 : ℝ) * (M₂ : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) :=
          mul_le_mul_of_nonneg_right hbig (by positivity)
        linarith
      have hstep : c₀W * γ ^ E₀W * (M₁ : ℝ) * (M₂ : ℝ)
          ≤ (γ' * (M₁ : ℝ) * (M₂ : ℝ)) / 2 := by
        have hMnn : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
        have hA : min (1 / (2 * (C₀ : ℝ))) (c₀' * cc₂ ^ E₀') * γ ^ (max K (Ae * E₀'))
            ≤ (1 / (2 * (C₀ : ℝ))) * γ ^ K :=
          mul_le_mul (min_le_left _ _)
            (pow_le_pow_of_le_one hγ0.le hγ1 (le_max_left _ _))
            (pow_nonneg hγ0.le _) (by positivity)
        have key : c₀W * γ ^ E₀W * (M₁ : ℝ) * (M₂ : ℝ)
            = (min (1 / (2 * (C₀ : ℝ))) (c₀' * cc₂ ^ E₀') * γ ^ (max K (Ae * E₀')))
              * ((M₁ : ℝ) * (M₂ : ℝ)) := by rw [hc₀W, hE₀W]; ring
        have key2 : (γ' * (M₁ : ℝ) * (M₂ : ℝ)) / 2
            = ((1 / (2 * (C₀ : ℝ))) * γ ^ K) * ((M₁ : ℝ) * (M₂ : ℝ)) := by
          rw [hγ'def]; ring
        rw [key, key2]
        exact mul_le_mul_of_nonneg_right hA hMnn
      exact le_trans hstep (half_le_toNat_floor hx1)
    · -- an inherited slot
      have hlow := hLrestLow ⟨⟨s, 0⟩, key s hs⟩
      refine le_trans ?_ hlow
      have hMnn : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
      have hstep1 : min (1 / (2 * (C₀ : ℝ))) (c₀' * cc₂ ^ E₀') * γ ^ (max K (Ae * E₀'))
          ≤ (c₀' * cc₂ ^ E₀') * γ ^ (Ae * E₀') :=
        mul_le_mul (min_le_right _ _)
          (pow_le_pow_of_le_one hγ0.le hγ1 (le_max_right _ _))
          (pow_nonneg hγ0.le _) (by positivity)
      have hstep2 : (c₀' * cc₂ ^ E₀') * γ ^ (Ae * E₀') ≤ c₀' * γ₁ ^ E₀' := by
        have hpow1 : (cc₂ * γ ^ Ae) ^ E₀' ≤ γ₁ ^ E₀' :=
          pow_le_pow_left₀ (by positivity) hγ₁ge E₀'
        calc (c₀' * cc₂ ^ E₀') * γ ^ (Ae * E₀')
            = c₀' * (cc₂ * γ ^ Ae) ^ E₀' := by rw [mul_pow, ← pow_mul]; ring
          _ ≤ c₀' * γ₁ ^ E₀' := mul_le_mul_of_nonneg_left hpow1 hc₀'0.le
      have key : c₀W * γ ^ E₀W * (M₁ : ℝ) * (M₂ : ℝ)
          = (min (1 / (2 * (C₀ : ℝ))) (c₀' * cc₂ ^ E₀') * γ ^ (max K (Ae * E₀')))
            * ((M₁ : ℝ) * (M₂ : ℝ)) := by rw [hc₀W, hE₀W]; ring
      have key2 : c₀' * γ₁ ^ E₀' * (M₁ : ℝ) * (M₂ : ℝ)
          = (c₀' * γ₁ ^ E₀') * ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
      rw [key, key2]
      exact mul_le_mul_of_nonneg_right (le_trans hstep1 hstep2) hMnn
  · -- the upper window bound
    intro s
    rw [hLwdef]; dsimp only; split_ifs with hs
    · -- the peeled slot
      have hLle : ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) :=
        toNat_floor_le (by positivity)
      have hMnn : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
      have h1 : γ' * (M₁ : ℝ) * (M₂ : ℝ) ≤ ((M₁ : ℝ) * (M₂ : ℝ)) / C₀ := by
        rw [hγ'def]
        rw [show γ ^ K / C₀ * (M₁ : ℝ) * (M₂ : ℝ)
            = (γ ^ K * ((M₁ : ℝ) * (M₂ : ℝ))) / C₀ by ring]
        exact div_le_div_of_nonneg_right
          (mul_le_of_le_one_left hMnn (pow_le_one₀ hγ0.le hγ1)) hC₀.le
      have h2 : ((M₁ : ℝ) * (M₂ : ℝ)) / C₀ ≤ C₁W * ((M₁ : ℝ) * (M₂ : ℝ)) := by
        have hle : C₀⁻¹ ≤ C₁W := by
          rw [hC₁W]
          simpa [one_div] using le_trans (le_max_right (1 : ℝ) (1 / (C₀ : ℝ)))
            (le_max_left _ _)
        have h3 : ((M₁ : ℝ) * (M₂ : ℝ)) * C₀⁻¹ ≤ ((M₁ : ℝ) * (M₂ : ℝ)) * C₁W :=
          mul_le_mul_of_nonneg_left hle hMnn
        rw [div_eq_mul_inv]
        exact le_trans h3 (le_of_eq (mul_comm ((M₁ : ℝ) * (M₂ : ℝ)) C₁W))
      exact le_trans hLle (le_trans h1 (by simpa only [mul_assoc] using h2))
    · -- an inherited slot
      have hup := hLrestUp ⟨⟨s, 0⟩, key s hs⟩
      refine le_trans hup ?_
      have hMnn : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
      have hle : C₁' ≤ C₁W := by rw [hC₁W]; exact le_max_right _ _
      have key1 : C₁' * (M₁ : ℝ) * (M₂ : ℝ) = C₁' * ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
      have key2 : C₁W * (M₁ : ℝ) * (M₂ : ℝ) = C₁W * ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
      rw [key1, key2]
      exact mul_le_mul_of_nonneg_right hle hMnn
  · refine le_trans ?_ (roundUnpeel (n := n) (p := p) (M₁ := M₁) (M₂ := M₂) (A := A)
      (g := g) (γ₀ := γ') (t' := t') s₀ trest Lrest t Lw N'' (C' * γ₁ ^ E')
      ht0 hL0 ht'' hLw'' hmm (fun a ha => hp s₀.1 a ha)
      (fun a ha => ⟨N, hg2 a ha⟩) hinner)
    have h2 : (cc₂ * γ ^ Ae) ^ E' ≤ γ₁ ^ E' := pow_le_pow_left₀ (by positivity) hγ₁ge E'
    have h3 : cc₂ ^ E' * γ ^ (Ae * E') = (cc₂ * γ ^ Ae) ^ E' := by
      rw [mul_pow, ← pow_mul]
    calc C' * cc₂ ^ E' * γ ^ (Ae * E') = C' * (cc₂ ^ E' * γ ^ (Ae * E')) := by ring
      _ = C' * (cc₂ * γ ^ Ae) ^ E' := by rw [h3]
      _ ≤ C' * γ₁ ^ E' := mul_le_mul_of_nonneg_left h2 hC'pos.le

/-! ## The non-peelable case -/

/-- **The infeasible case of the round, with the level bound and the window bounds.**  Same body as
`Work.Prop36SW.roundInfeasibleStepT`, but the round's witness `t s₀ = t'`, `t s = 0` (`s ≠ s₀`) is
bounded by the ladder's own (data-independent) `t'`, and the single window `Lw ≡ ⌊γ'M₁M₂⌋` is bounded
below by `γ^K M₁M₂/(2C₀)` and above by `M₁M₂/C₀`. -/
theorem roundInfeasibleStepW (h : Work.Peluse.C46.PeluseLadderA)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (n : ℕ) (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) (Dc : ℕ)
    (hkar : ∀ ω : Work.Peluse.UControl.SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0) :
    ∃ (C : ℝ) (E : ℕ) (Cn : ℝ) (Mn : ℕ) (T : ℕ) (c₀ : ℝ) (E₀ : ℕ) (C₁ : ℝ),
      0 < C ∧ 0 < Cn ∧ 1 ≤ Mn ∧ 1 ≤ T ∧ 0 < c₀ ∧ 1 ≤ C₁ ∧
      ∀ (M₁ M₂ N : ℕ) (A : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℤ → ℂ) (γ : ℝ),
        Work.Peluse.Prop36SW.LStateAbs kω p M₁ M₂ N Dc A g γ →
        Cn * γ ^ (-(Mn : ℤ)) ≤ (M₂ : ℝ) →
        ∃ (t : ι → ℕ) (Lw : ι → ℕ) (N' : ℕ),
          (∀ s : ι, t s ≤ T) ∧
          1 ≤ Fintype.card (Σ s : ι, Fin (t s)) ∧ (∀ s : ι, M₂ ≤ Lw s) ∧ N ≤ N' ∧
          (∀ s : ι, c₀ * γ ^ E₀ * (M₁ : ℝ) * (M₂ : ℝ) ≤ (Lw s : ℝ)) ∧
          (∀ s : ι, (Lw s : ℝ) ≤ C₁ * (M₁ : ℝ) * (M₂ : ℝ)) ∧
          C * γ ^ E ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
            Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
              (fun i => Work.Peluse.arithIcc
                (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
                (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1))
              (Work.Peluse.symIcc N') (g a) := by
  obtain ⟨K, C₀, t', c, hK, hC₀, ht', hc, hlad⟩ :=
    h (k := fun _ : ι => 1) (kω := kω) (p := fun i (a : Fin n → ℤ) => |p i a|) (D := Dc)
  have hcardC : Fintype.card (ConclIdx s₀ kω t') = t' :=
    card_conclIdx_of_notMem kω s₀ hkar t'
  set L : ℕ := Fintype.card (ConclIdx s₀ kω t') with hLdef
  have hLt' : L = t' := by rw [hLdef]; exact hcardC
  have hL1 : 1 ≤ L := by rw [hLt']; exact ht'
  refine ⟨(c / C₀ ^ K) ^ (2 ^ L), K * (K + 1) * 2 ^ L, C₀ ^ (K + 1), K * (K + 1), t',
    1 / (2 * C₀), K, max 1 (1 / C₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · have : 0 < K * (K + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  · exact ht'
  · positivity
  · exact le_max_left (1 : ℝ) (1 / C₀)
  · intro M₁ M₂ N A g γ hst hnd
    have hstabs : LStateAbs kω (fun i (a : Fin n → ℤ) => |p i a|) M₁ M₂ N Dc A g γ :=
      (lstateAbsAbsIff p M₁ M₂ N Dc A g γ).mp hst
    obtain ⟨hγ0, hγ1, hM2, hM21, hN, hM1M2N, hpne, hple_abs, hpabs, hsup, hsupp, hfam_p⟩ := hst
    obtain ⟨-, -, -, -, -, -, hpne_abs, hple_abs2, hpabs2, hsup2, hsupp2, hfam_abs⟩ := hstabs
    -- ### the window factor `γ' := γ^K/C₀`
    set γ' : ℝ := γ ^ K / C₀ with hγ'def
    have hγ'pos : 0 < γ' := by rw [hγ'def]; positivity
    have hsmall : C₀ * γ' ≤ γ ^ K := by
      rw [hγ'def]
      rw [show C₀ * (γ ^ K / C₀) = γ ^ K from by
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm C₀ (γ ^ K), mul_assoc,
          mul_inv_cancel₀ (ne_of_gt hC₀), mul_one]]
    have hpow : γ * γ' = γ ^ (K + 1) / C₀ := by
      rw [hγ'def, ← mul_div_assoc, ← pow_succ']
    have hzpow : (γ ^ (K + 1) / C₀) ^ (-(K : ℤ))
        = C₀ ^ K * γ ^ (-((K * (K + 1) : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, div_pow]
      rw [show (γ ^ (K + 1)) ^ K = γ ^ (K * (K + 1)) from by
        rw [← pow_mul]; congr 1; ring]
      have hγinv : (γ ^ (K * (K + 1)))⁻¹ = γ ^ (-((K * (K + 1) : ℕ) : ℤ)) := by
        rw [← zpow_natCast, ← zpow_neg]
      rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hγinv]
    have hnondeg : C₀ * (γ * γ') ^ (-(K : ℤ)) ≤ (M₂ : ℝ) := by
      have hbase : γ * γ' = γ ^ (K + 1) / C₀ := hpow
      rw [hbase, hzpow]
      rw [show C₀ * (C₀ ^ K * γ ^ (-((K * (K + 1) : ℕ) : ℤ)))
          = C₀ ^ (K + 1) * γ ^ (-((K * (K + 1) : ℕ) : ℤ)) from by
        rw [← mul_assoc, ← pow_succ']]
      exact hnd
    -- ### the ladder
    have hconcl := hlad A M₁ M₂ N γ γ' g hM2 hM21 hN hM1M2N hγ0 hγ1 hγ'pos hsmall
      (fun i a ha => abs_pos.mpr (fun h0 => hpne i a ha (by simp [h0])))
      (fun i a ha => hple_abs i a ha)
      (fun i a ha => by simpa [abs_abs] using hpabs i a ha)
      hsup hsupp hnondeg hfam_abs s₀
    have hconcl' : c * (γ * γ') ^ K ≤ (A.card : ℝ)⁻¹
        * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
        * ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun j => Work.Peluse.Prop36SW.conclDirG (fun i (a : Fin n → ℤ) => |p i a|) M₁ M₂ γ'
              s₀ t' a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
            (Work.Peluse.symIcc N) (g a) := hconcl
    -- ### the `|p|`-sum equals the `p`-sum
    have hsum_abs_p : (∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun j => Work.Peluse.Prop36SW.conclDirG (fun i (a : Fin n → ℤ) => |p i a|) M₁ M₂ γ'
              s₀ t' a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
            (Work.Peluse.symIcc N) (g a))
        = ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun j => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j)) (Work.Peluse.symIcc N) (g a) := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [sum_paramBox_boxNorm_conclDirG_abs kω p M₁ M₂ γ' s₀ t' a (Work.Peluse.symIcc N) (g a)]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have hcc : (fun j => Work.Peluse.Prop36SW.conclDirG (fun s _ => |p s a|) M₁ M₂ γ' s₀ t' a b
            ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
          = (fun j => Work.Peluse.Prop36SW.conclDirG (fun i (a : Fin n → ℤ) => |p i a|) M₁ M₂ γ'
              s₀ t' a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j)) := by
        funext j
        rcases (Fintype.equivFin (ConclIdx s₀ kω t')).symm j with u | ⟨ω, r⟩ <;> rfl
      rw [hcc]
    -- ### the collapse of the `p`-summand
    have hcoll : ∀ a ∈ A, (∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun j => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j)) (Work.Peluse.symIcc N) (g a))
        = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) *
            Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
              (Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
              (Work.Peluse.symIcc N) (g a) := by
      intro a ha
      have hterm : ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun j => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j)) (Work.Peluse.symIcc N) (g a)
          = Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
              (Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
              (Work.Peluse.symIcc N) (g a) :=
        fun b hb => boxNorm_conclDir_eq_uNorm kω s₀ hkar p M₁ M₂ γ' t' a b _ (g a)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    -- ### the averaged bound at strength `c(γγ')^K`
    have hkb : (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)) ≠ 0 := by
      have : 0 < (paramBox (k := fun _ : ι => 1) M₂).card := by
        refine Finset.card_pos.mpr ⟨fun _ => 0, ?_⟩
        rw [paramBox, Fintype.mem_piFinset]
        intro s
        rw [Finset.mem_Ioo]
        constructor <;> omega
      exact_mod_cast this.ne'
    set L' : ℕ := (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat with hL'def
    have huNorm : ∀ a : Fin n → ℤ, Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
          (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a)
        = (Work.Peluse.uNormPow (Fintype.card (ConclIdx s₀ kω t'))
            (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a))
          ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) := fun a => rfl
    set X : (Fin n → ℤ) → ℝ := fun a =>
      Work.Peluse.uNormPow (Fintype.card (ConclIdx s₀ kω t'))
        (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a) with hXdef
    have hsum : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * ∑ a ∈ A,
          Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
            (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a)
        = ∑ a ∈ A, ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) *
          Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
            (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a) := by
      rw [Finset.mul_sum]
    have hmain : c * (γ * γ') ^ K ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
        Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
          (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a) := by
      have h1 : c * (γ * γ') ^ K ≤ (A.card : ℝ)⁻¹
          * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
          * ∑ a ∈ A, ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) *
              Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
                (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a) := by
        rw [hsum_abs_p] at hconcl'
        rw [Finset.sum_congr rfl (fun a ha => hcoll a ha)] at hconcl'
        exact hconcl'
      refine le_trans h1 ?_
      set S : ℝ := ∑ a ∈ A, Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
          (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a) with hSdef
      rw [← hsum]
      rw [show (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
            * (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * S)
          = (A.card : ℝ)⁻¹ * S from by
        rw [mul_assoc ((A.card : ℝ)⁻¹) ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
            (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * S),
          ← mul_assoc ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
            ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) S,
          inv_mul_cancel₀ hkb, one_mul]]
    -- ### Jensen over the parameter set `A`
    have hX0 : ∀ a, 0 ≤ X a := by intro a; rw [hXdef]; exact norm_nonneg _
    have hX1 : ∀ a : ↥A, X a.1 ≤ 1 := by
      intro a
      have hb : X a.1 = Work.Peluse.boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
          (fun _ : Fin (Fintype.card (ConclIdx s₀ kω t')) => Work.Peluse.arithIcc (p s₀.1 a.1) L')
          (Work.Peluse.symIcc N) (g a.1) := rfl
      rw [hb]
      refine Work.Peluse.BoxNorm.boxNormPow_le_one (hsup a.1 a.2) (fun x hx => ?_)
      refine hsupp a.1 a.2 x ?_
      simp only [Work.Peluse.symIcc, Finset.mem_Icc, not_and, not_le] at hx
      omega
    have hα0 : 0 < 1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t'))) := by positivity
    have hα1 : 1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t'))) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hJ := inv_card_mul_sum_rpow_le (ι := ↥A)
      (α := 1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) (β := 1)
      hα0 hα1 one_pos le_rfl (fun a : ↥A => X a.1) (fun a => hX0 a.1) (fun a => hX1 a)
    have hcardA : (Fintype.card ↥A : ℝ) = (A.card : ℝ) := by simp
    have hXsum : (∑ a : ↥A, X a.1) = ∑ a ∈ A, X a := by
      rw [← Finset.sum_attach A]; rfl
    have hXpow : (∑ a : ↥A, (X a.1) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))))
        = ∑ a ∈ A, (X a) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) := by
      rw [← Finset.sum_attach A]; rfl
    have hkey : c * (γ * γ') ^ K
        ≤ ((A.card : ℝ)⁻¹ * ∑ a ∈ A, X a) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) := by
      have h4 : ∀ a ∈ A, (X a) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t'))))
          = Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
              (Work.Peluse.arithIcc (p s₀.1 a) L') (Work.Peluse.symIcc N) (g a) := by
        intro a ha
        rw [huNorm a]
      have h3 : c * (γ * γ') ^ K ≤ (A.card : ℝ)⁻¹
          * ∑ a ∈ A, (X a) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) := by
        rw [Finset.sum_congr rfl h4]
        exact hmain
      have hJ'' : (A.card : ℝ)⁻¹ * ∑ a ∈ A, (X a) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t'))))
          ≤ ((A.card : ℝ)⁻¹ * ∑ a ∈ A, X a) ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) := by
        have h := hJ
        rw [hcardA, hXpow, hXsum, mul_one] at h
        exact h
      exact le_trans h3 hJ''
    -- ### raise to the `2^L`-th power
    have hLpos : (0 : ℝ) < c * (γ * γ') ^ K :=
      mul_pos hc (pow_pos (mul_pos hγ0 hγ'pos) K)
    have havg0 : 0 ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, X a := by
      refine mul_nonneg (by positivity) ?_
      exact Finset.sum_nonneg (fun a _ => hX0 a)
    have hfinal : (c * (γ * γ') ^ K) ^ (2 ^ L) ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, X a := by
      have h1 := pow_le_pow_left₀ (le_of_lt hLpos) hkey (2 ^ L)
      have h2 : (((A.card : ℝ)⁻¹ * ∑ a ∈ A, X a)
            ^ (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t'))))) ^ (2 ^ L)
          = (A.card : ℝ)⁻¹ * ∑ a ∈ A, X a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul havg0]
        have hexp : (1 / ((2 : ℝ) ^ (Fintype.card (ConclIdx s₀ kω t')))) * ((2 ^ L : ℕ) : ℝ) = 1 := by
          rw [hLdef]
          push_cast
          field_simp
        rw [hexp, Real.rpow_one]
      rw [← h2]
      exact h1
    -- ### the final assembly
    have hCγ : (c / C₀ ^ K) ^ (2 ^ L) * γ ^ (K * (K + 1) * 2 ^ L)
        = (c * (γ * γ') ^ K) ^ (2 ^ L) := by
      have hid : c * (γ * γ') ^ K = (c / C₀ ^ K) * γ ^ (K * (K + 1)) := by
        rw [hpow, div_pow]
        rw [show (γ ^ (K + 1)) ^ K = γ ^ (K * (K + 1)) from by
          rw [← pow_mul]; congr 1; ring]
        ring
      rw [hid, mul_pow, ← pow_mul]
    set t : ι → ℕ := fun s => if s = s₀.1 then L else 0 with htdef
    set Lw : ι → ℕ := fun _ => L' with hLwdef
    have hcard_sigma : Fintype.card (Σ s : ι, Fin (t s)) = L := by
      rw [htdef]
      exact card_sigma_fin_ite s₀.1 L
    have hLw : ∀ s : ι, M₂ ≤ Lw s := by
      intro s
      show M₂ ≤ L'
      rw [hL'def]
      rw [show γ' = γ ^ K / C₀ from hγ'def]
      exact roundWindowGe hC₀ hγ0 hγ1 hK hM2 hM21 hnd
    have hround_eq : ∀ a : Fin n → ℤ,
        Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
          (fun i => Work.Peluse.arithIcc
            (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
            (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1))
          (Work.Peluse.symIcc N) (g a) = X a := by
      intro a
      have hfam : (fun i : Fin (Fintype.card (Σ s : ι, Fin (t s))) =>
            Work.Peluse.arithIcc (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
              (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1))
          = fun _ : Fin (Fintype.card (Σ s : ι, Fin (t s))) =>
              Work.Peluse.arithIcc (p s₀.1 a) L' := by
        funext i
        rw [fst_equivFin_sigma_of_single s₀.1 (fun s hs => by rw [htdef]; exact if_neg hs) i]
      rw [hfam, Work.Peluse.Concat.boxNormPow_cast hcard_sigma]
      rfl
    have hLle : (L' : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
      rw [hL'def]
      exact toNat_floor_le (by positivity)
    refine ⟨t, Lw, N, ?_, ?_, hLw, le_rfl, ?_, ?_, ?_⟩
    · intro s
      rw [htdef]; dsimp only
      split_ifs with h
      · omega
      · exact Nat.zero_le _
    · rw [hcard_sigma]
      exact hL1
    · -- the lower window bound
      intro s
      show (1 / (2 * C₀)) * γ ^ K * (M₁ : ℝ) * (M₂ : ℝ) ≤ (L' : ℝ)
      have hx1 : (1 : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := by
        have h1 : (1 : ℝ) ≤ (L' : ℝ) := by
          have h2 : (1 : ℕ) ≤ Lw s := le_trans hM2 (hLw s)
          have h3 : Lw s = L' := rfl
          rw [h3] at h2
          exact_mod_cast h2
        linarith [hLle]
      have key : (1 / (2 * C₀)) * γ ^ K * (M₁ : ℝ) * (M₂ : ℝ)
          = (γ' * (M₁ : ℝ) * (M₂ : ℝ)) / 2 := by rw [hγ'def]; ring
      rw [key]
      exact half_le_toNat_floor hx1
    · -- the upper window bound
      intro s
      show (L' : ℝ) ≤ max 1 (1 / C₀) * (M₁ : ℝ) * (M₂ : ℝ)
      have hMnn : (0 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by positivity
      have h1 : γ' * (M₁ : ℝ) * (M₂ : ℝ) ≤ ((M₁ : ℝ) * (M₂ : ℝ)) / C₀ := by
        rw [hγ'def]
        rw [show γ ^ K / C₀ * (M₁ : ℝ) * (M₂ : ℝ)
            = (γ ^ K * ((M₁ : ℝ) * (M₂ : ℝ))) / C₀ by ring]
        exact div_le_div_of_nonneg_right
          (mul_le_of_le_one_left hMnn (pow_le_one₀ hγ0.le hγ1)) hC₀.le
      have h2 : ((M₁ : ℝ) * (M₂ : ℝ)) / C₀ ≤ (max 1 (1 / C₀)) * ((M₁ : ℝ) * (M₂ : ℝ)) := by
        have hle : C₀⁻¹ ≤ max 1 (1 / C₀) := by
          simpa [one_div] using le_max_right (1 : ℝ) (1 / C₀)
        calc ((M₁ : ℝ) * (M₂ : ℝ)) / C₀ = ((M₁ : ℝ) * (M₂ : ℝ)) * C₀⁻¹ := by
              rw [div_eq_mul_inv]
          _ ≤ ((M₁ : ℝ) * (M₂ : ℝ)) * (max 1 (1 / C₀)) :=
              mul_le_mul_of_nonneg_left hle hMnn
          _ = (max 1 (1 / C₀)) * ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
      calc (L' : ℝ) ≤ γ' * (M₁ : ℝ) * (M₂ : ℝ) := hLle
        _ ≤ ((M₁ : ℝ) * (M₂ : ℝ)) / C₀ := h1
        _ ≤ (max 1 (1 / C₀)) * ((M₁ : ℝ) * (M₂ : ℝ)) := h2
        _ = max 1 (1 / C₀) * (M₁ : ℝ) * (M₂ : ℝ) := by ring
    · rw [hCγ, ← Finset.sum_congr rfl (fun a _ => (hround_eq a).symm)]
      exact hfinal

/-! ## The round, assembled -/

/-- **The round of the §5 chain at every slot type, with a level bound and window bounds.** -/
theorem roundPeelAuxW (h : Work.Peluse.C46.PeluseLadderA) :
    ∀ m : ℕ, Work.Peluse.Prop36SW.RoundStmtW (m + 1) := by
  intro m
  induction m with
  | zero =>
      intro ι _ _ hcard n kω p Dc
      have hpos : 0 < Fintype.card ι := by omega
      haveI : Nonempty ι := Fintype.card_pos_iff.mp hpos
      set s₀ : Slot ι (fun _ => 1) := ⟨Classical.arbitrary ι, 0⟩ with hs₀
      exact Work.Prop36SW.roundInfeasibleStepW h s₀ n kω p Dc
        (Work.Peluse.Prop36SW.kar_of_card_one (by simpa using hcard) kω s₀)
  | succ m ih =>
      intro ι _ _ hcard n kω p Dc
      have hpos : 0 < Fintype.card ι := by omega
      haveI : Nonempty ι := Fintype.card_pos_iff.mp hpos
      set s₀ : Slot ι (fun _ => 1) := ⟨Classical.arbitrary ι, 0⟩ with hs₀
      by_cases hB : 1 ≤ Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀)
      · exact roundPeelStepW h m ih hcard n kω p Dc s₀ hB
      · refine Work.Prop36SW.roundInfeasibleStepW h s₀ n kω p Dc ?_
        intro ω hω
        by_contra hne
        have h1 : 1 ≤ Fintype.card
            (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀) :=
          Fintype.card_pos_iff.mpr ⟨⟨⟨ω.1, ω.2, hω⟩, ⟨0, Nat.pos_of_ne_zero hne⟩⟩⟩
        omega

end

end Work.Prop36SW

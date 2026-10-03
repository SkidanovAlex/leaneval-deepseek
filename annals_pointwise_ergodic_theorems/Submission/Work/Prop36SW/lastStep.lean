import Mathlib
import Submission.Work.Prop36SW.chainDefs
import Submission.Work.Prop36SW.roundPeelAuxW
import Submission.Work.Peluse.Prop36SW.lstateSpread
import Submission.Work.Peluse.Prop36SW.spreadBack
import Submission.Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink_slot
import Submission.Work.Peluse.Prop36SW.roundRegroup
import Submission.Work.Prop36SW.LStateBoxAbsIff
import Submission.Work.Prop36SW.LStateBoxMonoAmbient
import Submission.Work.Prop36SW.inflateMultiplicities
import Submission.Work.Prop36SW.pFlat_dirBound

/-!
# `lastStep`: the endgame of the §5 chain

From the round statements `Work.Peluse.Prop36SW.RoundStmtW (m+1)` (one per level) we produce the
endgame `Work.Prop36SW.LastStep D d c Λ kω` of the chain: the round applied at **slot level `0`**,
where the coefficient `pFlat D d c 0 Λ` is the *constant* `Λ · d · c` (`pFlat_zero` below).  The
round's conclusion is then already a `uNormPow` up to

* a level change: the round's level `card (Σ s, Fin (t s))` is data-dependent, and must be raised to
  the data-independent level `S := card (Σ s : D.S 1, Fin T)` (`T` the round's level bound) --
  `level_raise_uniform`, the uniform-constant form of the Gowers–Cauchy–Schwarz level raise;
* a common window: the round's windows `Lw s` depend on the slot, and are shrunk to their minimum
  `Lw₀` (`boxNormPow_arithIcc_shrink_slot`), which is also what supplies the conclusion's window
  lower bound `c₀ γ^{e₀} (H+1)^d` (through the round's window lower bound and the state's
  `c_h γ^{e_h} (H+1)^{d-1} ≤ M₁`);
* a fixed ambient: the round's output ambient `N'` is enlarged so that the directions
  `Λ d c [Lw s]` fit in the window -- a datum-independent constant, since `|Λdc| M₁ M₂ ≤ N` and
  `Lw s ≤ C₁ M₁ M₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-- **`pFlat` at slot level `0`.**  There `D.dir d c 0 _ _ = c`, so the coefficient is the constant
`Λ · d · c`. -/
private lemma pFlat_zero (D : IdxDatum) (d : ℕ) (c : ℤ) (Λ : ℕ) (s : D.S 1)
    (x : Fin (nD D 1) → ℤ) : pFlat D d c 0 Λ s x = ((Λ * d : ℕ) : ℤ) * c := by
  simp only [pFlat, IdxDatum.dir]
  push_cast
  ring

/-- The elements of an arithmetic progression `c[L]`. -/
private lemma mem_arithIcc' {c : ℤ} {L : ℕ} {z : ℤ} (hz : z ∈ arithIcc c L) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ L ∧ z = c * (j : ℤ) := by
  rw [arithIcc, Finset.mem_image] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  rw [Finset.mem_Icc] at hj
  exact ⟨j, hj.1, hj.2, rfl⟩

/-- The cardinality of `Σ s : ι, Fin T`. -/
private lemma card_sigma_fin' (ι : Type) [Fintype ι] (T : ℕ) :
    Fintype.card (Σ _s : ι, Fin T) = Fintype.card ι * T := by
  rw [Fintype.card_sigma]
  simp [Finset.sum_const, smul_eq_mul]

/-! ## The level raise with a uniform constant -/

/-- **Level raising for the box-norm power, with a constant uniform in the source level.**  If the
directions of `Q` contain those of `P` (along an injection `e`), then raising the level from `t` to
`S` costs only `(1/2)^{2^S - 1}` and the exponent `2^S`, *independently of `t`* (whereas
`boxNormPow_le_of_inj` costs `2^{2^{S-t}-1}` and `2^{S-t}`).  The point is that the source norm is
`≤ 1`, so `b^{2^{S-t}} ≥ b^{2^S}`. -/
private lemma level_raise_uniform {N S t : ℕ} (hN : 0 < N) {f : ℤ → ℂ}
    (hsup : ∀ x : ℤ, x ∉ symIcc N → f x = 0)
    (hbdd1 : ∀ x : ℤ, ‖f x‖ ≤ 1)
    {P : Fin t → Finset ℤ} {Q : Fin S → Finset ℤ} (e : Fin t ↪ Fin S)
    (he : ∀ i, Q (e i) = P i) (ht : t ≤ S)
    (hQne : ∀ i : Fin S, (Q i).Nonempty)
    (hbdd : ∀ (i : Fin S) (z : ℤ), z ∈ Q i → |z| ≤ (N : ℤ)) :
    (1 / 2 : ℝ) ^ (2 ^ S - 1) * (boxNormPow t P (symIcc N) f) ^ (2 ^ S)
      ≤ boxNormPow S Q (symIcc N) f := by
  set b : ℝ := boxNormPow t P (symIcc N) f with hbdef
  set B : ℝ := boxNormPow S Q (symIcc N) f with hBdef
  have hb0 : 0 ≤ b := by rw [hbdef]; exact norm_nonneg _
  have hb1 : b ≤ 1 := by
    rw [hbdef]
    exact Work.Peluse.BoxNorm.boxNormPow_le_one hbdd1 hsup
  have hB0 : 0 ≤ B := by rw [hBdef]; exact norm_nonneg _
  have hmain : b ^ (2 ^ (S - t)) ≤ 2 ^ (2 ^ (S - t) - 1) * B := by
    rw [hbdef, hBdef]
    exact boxNormPow_le_of_inj hN f hsup S t ht P Q e he hQne hbdd
  have hkle : 2 ^ (S - t) ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hbpow : b ^ (2 ^ S) ≤ b ^ (2 ^ (S - t)) := pow_le_pow_of_le_one hb0 hb1 hkle
  have hcle : 2 ^ (S - t) - 1 ≤ 2 ^ S - 1 := by
    have h1 : 1 ≤ 2 ^ (S - t) := Nat.one_le_two_pow
    omega
  have hc1 : (1 / 2 : ℝ) ^ (2 ^ S - 1) ≤ (1 / 2 : ℝ) ^ (2 ^ (S - t) - 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcle
  have hc2 : (1 / 2 : ℝ) ^ (2 ^ (S - t) - 1) = ((2 : ℝ) ^ (2 ^ (S - t) - 1))⁻¹ := by
    rw [← inv_pow]
    norm_num
  have hdiv : (1 / 2 : ℝ) ^ (2 ^ (S - t) - 1) * b ^ (2 ^ (S - t)) ≤ B := by
    rw [hc2]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (S - t) - 1) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hmain (le_of_lt (inv_pos.mpr h2))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2), one_mul] at h3
  calc (1 / 2 : ℝ) ^ (2 ^ S - 1) * b ^ (2 ^ S)
      ≤ (1 / 2 : ℝ) ^ (2 ^ S - 1) * b ^ (2 ^ (S - t)) :=
        mul_le_mul_of_nonneg_left hbpow (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ (2 ^ (S - t) - 1) * b ^ (2 ^ (S - t)) :=
        mul_le_mul_of_nonneg_right hc1 (pow_nonneg hb0 _)
    _ ≤ B := hdiv

theorem lastStep (hW : ∀ m : ℕ, Work.Peluse.Prop36SW.RoundStmtW (m + 1))
    (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (Λ : ℕ)
    (kω : Work.Peluse.UControl.SlotSet (D.S 1) (fun _ => 1) → ℕ)
    (hk : 1 ≤ Fintype.card (D.S 1)) (hd : 2 ≤ d) :
    Work.Prop36SW.LastStep D d c Λ kω := by
  classical
  -- ## the round's constants at slot level `0`
  obtain ⟨C_r, E_r, Cn_r, Mn_r, T_r, c₀_r, E₀_r, C₁_r, hC_r, hCn_r, hMn_r, hT_r, hc₀_r, hC₁_r,
    hround⟩ :=
    (Nat.sub_add_cancel hk ▸ hW (Fintype.card (D.S 1) - 1)) (D.S 1) rfl
      (nD D 1) kω (pFlat D d c 0 Λ) 1
  -- ## the fixed level, and the constants
  set T : ℕ := max T_r 2 with hTdef
  have hT2 : 2 ≤ T := le_max_right _ _
  have hTrT : T_r ≤ T := le_max_left _ _
  set S : ℕ := Fintype.card (Σ _s : D.S 1, Fin T) with hSdef
  have hS2 : 2 ≤ S := by
    rw [hSdef, card_sigma_fin']
    calc 2 = 1 * 2 := by norm_num
      _ ≤ Fintype.card (D.S 1) * T := Nat.mul_le_mul hk hT2
  obtain ⟨C_s, hC_s_pos, hC_s⟩ :=
    Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink_slot (t := S) hS2
  set κ : ℤ := ((Λ * d : ℕ) : ℤ) * c with hκdef
  set Dl : ℝ := 2 * (Nat.ceil C₁_r : ℝ) + 3 with hDldef
  have hDlpos : 0 < Dl := by rw [hDldef]; positivity
  set C_lev : ℝ := (1 / 2 : ℝ) ^ (2 ^ S - 1) * (C_r / Dl) ^ (2 ^ S)
    * (3 / 4 : ℝ) ^ (E_r * 2 ^ S) with hC_levdef
  have hC_lev_pos : 0 < C_lev := by
    rw [hC_levdef]
    exact mul_pos (mul_pos (pow_pos (by norm_num) _)
      (pow_pos (div_pos hC_r hDlpos) _)) (pow_pos (by norm_num) _)
  refine ⟨C_s * C_lev, E_r * 2 ^ S, S, Cn_r, Mn_r, ?_, hS2, hCn_r, hMn_r, ?_⟩
  · exact mul_pos hC_s_pos hC_lev_pos
  intro c_h e_h hch0 hch1
  refine ⟨c₀_r * (3 / 4 : ℝ) ^ E₀_r * c_h, E₀_r + e_h, ?_, by omega, ?_⟩
  · positivity
  intro H hH M₁ N f γ hst hM1 hwin hNamb hgood hthr
  -- ## the state, spread to the good set
  set A : Finset (Fin (nD D 1) → ℤ) := Abox D 1 H with hAdef
  set A' : Finset (Fin (nD D 1) → ℤ) :=
    A.filter (fun a => ∀ i, pFlat D d c 0 Λ i a ≠ 0) with hA'def
  have hγ0 : 0 < γ := hst.1
  have hγ1 : γ ≤ 1 := hst.2.1
  have hspread : LStateAbs kω (pFlat D d c 0 Λ) M₁ (H + 1) N 1 A' (fun _ => f) (3 * γ / 4) :=
    lstateSpread kω (pFlat D d c 0 Λ) M₁ (H + 1) N 1 A (fun _ => f) γ hst hγ0 hgood
  have hspreadK := hspread
  obtain ⟨hγ0', hγ1', hM₂1, hM₂M₁, hN1le, hM₁M₂N, hpne, hpl, hpa, hg1, hg2, hfam⟩ := hspreadK
  -- ## the round at slot level `0`
  obtain ⟨t, Lw, N₁, htb, hpos1, hLwge, hNle, hwinlo, hwinhi, hrc⟩ :=
    hround M₁ (H + 1) N A' (fun _ => f) (3 * γ / 4) hspread
      (by rw [Nat.cast_add, Nat.cast_one]; exact hthr)
  -- ## the coefficient is constant on the parameter box, so the average is a single term
  set nt : ℕ := Fintype.card (Σ _s : D.S 1, Fin (t _s)) with hntdef
  set Ψ : ℝ := boxNormPow nt
    (fun i => arithIcc κ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1))
    (symIcc N₁) f with hΨdef
  have hsummand : ∀ a ∈ A', boxNormPow nt
      (fun i => arithIcc (pFlat D d c 0 Λ
        ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1 a)
        (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1))
      (symIcc N₁) f = Ψ := by
    intro a ha
    have hf : (fun i => arithIcc (pFlat D d c 0 Λ
          ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1 a)
          (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1))
        = (fun i => arithIcc κ
          (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1)) := by
      funext i
      rw [pFlat_zero]
    rw [hf]
  have hrc' : C_r * (3 * γ / 4) ^ E_r ≤ ((A'.card : ℝ))⁻¹ * ∑ a ∈ A', Ψ :=
    hrc.trans_eq (by rw [Finset.sum_congr rfl hsummand])
  have hA'card : A'.card ≠ 0 := by
    intro h0
    have hA'e : A' = ∅ := Finset.card_eq_zero.mp h0
    have hz : ((A'.card : ℝ))⁻¹ * ∑ a ∈ A', Ψ = 0 := by simp [hA'e]
    have hpos : 0 < C_r * (3 * γ / 4) ^ E_r :=
      mul_pos hC_r (pow_pos (by positivity) _)
    rw [hz] at hrc'
    linarith
  have hsingle : C_r * (3 * γ / 4) ^ E_r ≤ Ψ := by
    have hcard : ((A'.card : ℝ)) ≠ 0 := by exact_mod_cast hA'card
    rw [Finset.sum_const, nsmul_eq_mul] at hrc'
    have h1 : ((A'.card : ℝ))⁻¹ * ((A'.card : ℝ) * Ψ) = Ψ := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    rw [h1] at hrc'
    exact hrc'
  have hA'ne : A'.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hA'card)
  obtain ⟨a₀, ha₀⟩ := hA'ne
  obtain ⟨s₀⟩ : Nonempty (D.S 1) := Fintype.card_pos_iff.mp (by omega)
  -- ## the direction bound and the enlarged ambient
  have hκM : ((|κ| : ℤ) : ℝ) * (M₁ : ℝ) * ((H + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h := hpl s₀ a₀ ha₀
    have hp : pFlat D d c 0 Λ s₀ a₀ = κ := pFlat_zero D d c Λ s₀ a₀
    rw [hp] at h
    exact_mod_cast h
  set N₂ : ℕ := max N₁ (Nat.ceil C₁_r * N + 1) with hN₂def
  have hN₁N₂ : N₁ ≤ N₂ := le_max_left _ _
  have hNN₂ : N ≤ N₂ := le_trans hNle hN₁N₂
  have hN₂pos : 0 < N₂ := lt_of_lt_of_le (by omega : 0 < N) hNN₂
  have hceil : C₁_r * (N : ℝ) ≤ (N₂ : ℝ) := by
    have h3 : ((Nat.ceil C₁_r : ℕ) : ℝ) * (N : ℝ) ≤ (N₂ : ℝ) := by
      have h4 : Nat.ceil C₁_r * N ≤ N₂ := by
        rw [hN₂def]
        exact le_trans (Nat.le_add_right _ 1) (le_max_right _ _)
      calc ((Nat.ceil C₁_r : ℕ) : ℝ) * (N : ℝ)
          = ((Nat.ceil C₁_r * N : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (N₂ : ℝ) := by exact_mod_cast h4
    exact le_trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C₁_r) (Nat.cast_nonneg N)) h3
  have hfit : ∀ s : D.S 1, ((|κ| : ℤ) : ℝ) * (Lw s : ℝ) ≤ (N₂ : ℝ) := by
    intro s
    have h1 : (Lw s : ℝ) ≤ C₁_r * (M₁ : ℝ) * ((H + 1 : ℕ) : ℝ) := hwinhi s
    have h2 : (0 : ℝ) ≤ ((|κ| : ℤ) : ℝ) := by positivity
    calc ((|κ| : ℤ) : ℝ) * (Lw s : ℝ)
        ≤ ((|κ| : ℤ) : ℝ) * (C₁_r * (M₁ : ℝ) * ((H + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = C₁_r * (((|κ| : ℤ) : ℝ) * (M₁ : ℝ) * ((H + 1 : ℕ) : ℝ)) := by ring
      _ ≤ C₁_r * (N : ℝ) := mul_le_mul_of_nonneg_left hκM (by linarith : (0 : ℝ) ≤ C₁_r)
      _ ≤ (N₂ : ℝ) := hceil
  have hratio : (1 : ℝ) / Dl ≤ ((symIcc N₁).card : ℝ) / ((symIcc N₂).card : ℝ) := by
    have hc1 : ((symIcc N₁).card : ℝ) = 2 * (N₁ : ℝ) + 1 := by
      rw [card_symIcc]; push_cast; ring
    have hc2 : ((symIcc N₂).card : ℝ) = 2 * (N₂ : ℝ) + 1 := by
      rw [card_symIcc]; push_cast; ring
    rw [hc1, hc2, hDldef]
    have hN₂le : N₂ ≤ N₁ + (Nat.ceil C₁_r * N + 1) := by
      rw [hN₂def]
      exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have hN₂cast : (N₂ : ℝ) ≤ (N₁ : ℝ) + ((Nat.ceil C₁_r : ℝ) * (N : ℝ) + 1) := by
      have hcast : (N₂ : ℝ) ≤ (((N₁ + (Nat.ceil C₁_r * N + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hN₂le
      push_cast at hcast
      linarith
    have hNleR : (N : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNle
    have hceilR : (0 : ℝ) ≤ (Nat.ceil C₁_r : ℝ) := Nat.cast_nonneg _
    have hN₁R : (0 : ℝ) ≤ (N₁ : ℝ) := Nat.cast_nonneg _
    rw [div_le_div_iff₀ (show (0 : ℝ) < 2 * (Nat.ceil C₁_r : ℝ) + 3 by positivity)
      (show (0 : ℝ) < 2 * (N₂ : ℝ) + 1 by positivity)]
    nlinarith [hN₂cast, hNleR, hceilR, hN₁R]
  have hLw1 : ∀ s : D.S 1, 1 ≤ Lw s := fun s => le_trans (by omega : 1 ≤ H + 1) (hLwge s)
  -- ## the level raise and the shrink
  have hntS : nt ≤ S := by
    rw [hntdef, hSdef]
    simp only [Fintype.card_sigma, Fintype.card_fin]
    exact Finset.sum_le_sum (fun s _ => le_trans (htb s) hTrT)
  obtain ⟨e, he⟩ := blockInjFinSigma t T (fun s => le_trans (htb s) hTrT)
  have he' : ∀ i : Fin nt,
      (fun j : Fin S => arithIcc κ
        (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm j).1)) (e i)
      = (fun j : Fin nt => arithIcc κ
        (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm j).1)) i := by
    intro i
    show arithIcc κ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm (e i)).1)
        = arithIcc κ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm i).1)
    rw [he i]
  have hQtne : ∀ i : Fin S, (arithIcc κ
      (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1)).Nonempty :=
    fun i => inflate_arithIcc_nonempty (hLw1 _)
  have hQtbdd : ∀ (i : Fin S) (z : ℤ),
      z ∈ arithIcc κ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1) →
      |z| ≤ (N₂ : ℤ) := by
    intro i z hz
    obtain ⟨j, hj1, hj2, rfl⟩ := mem_arithIcc' hz
    have hjR : (j : ℝ) ≤ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1 : ℝ) := by
      exact_mod_cast hj2
    have habs : |κ * (j : ℤ)| = (|κ| : ℤ) * (j : ℤ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (j : ℤ))]
    rw [habs]
    have h1 : ((|κ| : ℤ) * (j : ℤ) : ℤ) ≤ (N₂ : ℤ) := by
      have h2 : (((|κ| : ℤ) * (j : ℤ) : ℤ) : ℝ) ≤ (N₂ : ℝ) := by
        have hcast : (((|κ| : ℤ) * (j : ℤ) : ℤ) : ℝ) = ((|κ| : ℤ) : ℝ) * (j : ℝ) := by
          push_cast; ring
        rw [hcast]
        calc ((|κ| : ℤ) : ℝ) * (j : ℝ)
            ≤ ((|κ| : ℤ) : ℝ) * ((Lw _ : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hjR (by positivity)
          _ ≤ (N₂ : ℝ) := hfit _
      exact_mod_cast h2
    exact h1
  have hlr := level_raise_uniform (N := N₂) (S := S) (t := nt) hN₂pos
    (fun x hx => hg2 a₀ ha₀ x (by
      have hx' : ¬ |x| ≤ (N₂ : ℤ) := fun h => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr h)
      have hlt : (N₂ : ℤ) < |x| := lt_of_not_ge hx'
      have hNN₂Z : (N : ℤ) ≤ (N₂ : ℤ) := by exact_mod_cast hNN₂
      have hlt' : (N : ℤ) < (x.natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; linarith
      exact_mod_cast hlt'))
    (hg1 a₀ ha₀)
    (P := fun j : Fin nt => arithIcc κ
      (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm j).1))
    (Q := fun j : Fin S => arithIcc κ
      (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm j).1))
    e he' hntS hQtne hQtbdd
  -- ## the window ratio, the common window, and the shrink
  have hΨ₂ : (C_r / Dl) * (3 * γ / 4) ^ E_r
      ≤ boxNormPow nt (fun j => arithIcc κ
        (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm j).1)) (symIcc N₂) f := by
    have hww : boxNormPow nt (fun j => arithIcc κ
          (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm j).1)) (symIcc N₂) f
        = (((symIcc N₁).card : ℝ) / ((symIcc N₂).card : ℝ)) * Ψ := by
      rw [hΨdef]
      exact boxNormPow_window_ratio nt _ (symIcc N₂) (symIcc N₁) f ⟨0, by simp [symIcc]⟩
    rw [hww]
    have h1 : (C_r / Dl) * (3 * γ / 4) ^ E_r
        = (1 / Dl) * (C_r * (3 * γ / 4) ^ E_r) := by ring
    rw [h1]
    calc (1 / Dl) * (C_r * (3 * γ / 4) ^ E_r)
        ≤ (((symIcc N₁).card : ℝ) / ((symIcc N₂).card : ℝ))
            * (C_r * (3 * γ / 4) ^ E_r) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ (((symIcc N₁).card : ℝ) / ((symIcc N₂).card : ℝ)) * Ψ :=
          mul_le_mul_of_nonneg_left hsingle (by positivity)
  have hne_img : ((Finset.univ : Finset (Fin S)).image
      (fun i => Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1)).Nonempty :=
    Finset.image_nonempty.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set Lw₀ : ℕ := ((Finset.univ : Finset (Fin S)).image
      (fun i => Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1)).min' hne_img
    with hLw₀def
  have hLw₀le : ∀ i : Fin S, Lw₀ ≤ Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1 :=
    fun i => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hLw₀mem : Lw₀ ∈ ((Finset.univ : Finset (Fin S)).image
      (fun i => Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1)) :=
    Finset.min'_mem _ hne_img
  obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hLw₀mem
  have hLw₀pos : 1 ≤ Lw₀ := by
    rw [← hi₀]
    exact hLw1 _
  have hshrink := hC_s (fun _ : Fin S => κ) (fun _ : Fin S => Lw₀)
      (fun i : Fin S => Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i).1)
      (fun _ => hLw₀pos) (fun i => hLw₀le i) (symIcc N₂) f
      (Work.Peluse.FinSuppZ.of_supportIn (hg2 a₀ ha₀))
  -- ## assembly
  have hfinal : C_s * C_lev * γ ^ (E_r * 2 ^ S)
      ≤ uNormPow S (arithIcc κ Lw₀) (symIcc N₂) f := by
    have hClev_eq : C_lev * γ ^ (E_r * 2 ^ S)
        = (1 / 2 : ℝ) ^ (2 ^ S - 1) * ((C_r / Dl) * (3 * γ / 4) ^ E_r) ^ (2 ^ S) := by
      have h1 : ((C_r / Dl) * (3 * γ / 4) ^ E_r) ^ (2 ^ S)
          = (C_r / Dl) ^ (2 ^ S) * (3 / 4 : ℝ) ^ (E_r * 2 ^ S) * γ ^ (E_r * 2 ^ S) := by
        rw [mul_pow, ← pow_mul]
        rw [show (3 * γ / 4 : ℝ) = (3 / 4) * γ by ring]
        rw [mul_pow]
        ring
      rw [hC_levdef, h1]
      ring
    have h2 : ((C_r / Dl) * (3 * γ / 4) ^ E_r) ^ (2 ^ S)
        ≤ (boxNormPow nt (fun j => arithIcc κ
          (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm j).1)) (symIcc N₂) f)
            ^ (2 ^ S) :=
      pow_le_pow_left₀ (by positivity) hΨ₂ _
    have hU : C_lev * γ ^ (E_r * 2 ^ S)
        ≤ boxNormPow S (fun j : Fin S => arithIcc κ
          (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm j).1)) (symIcc N₂) f := by
      calc C_lev * γ ^ (E_r * 2 ^ S)
          = (1 / 2 : ℝ) ^ (2 ^ S - 1)
              * ((C_r / Dl) * (3 * γ / 4) ^ E_r) ^ (2 ^ S) := hClev_eq
        _ ≤ (1 / 2 : ℝ) ^ (2 ^ S - 1) * (boxNormPow nt (fun j => arithIcc κ
              (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin (t _s))).symm j).1))
              (symIcc N₂) f) ^ (2 ^ S) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ boxNormPow S (fun j : Fin S => arithIcc κ
              (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm j).1)) (symIcc N₂) f := hlr
    calc C_s * C_lev * γ ^ (E_r * 2 ^ S)
        = C_s * (C_lev * γ ^ (E_r * 2 ^ S)) := by ring
      _ ≤ C_s * boxNormPow S (fun j : Fin S => arithIcc κ
            (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm j).1)) (symIcc N₂) f :=
          mul_le_mul_of_nonneg_left hU (le_of_lt hC_s_pos)
      _ ≤ uNormPow S (arithIcc κ Lw₀) (symIcc N₂) f := hshrink
  refine ⟨Lw₀, N₂, hNN₂, ?_, ?_⟩
  · rw [← hi₀]
    have h1 := hwinlo ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i₀).1
    have h2 : (3 * γ / 4) ^ E₀_r = (3 / 4 : ℝ) ^ E₀_r * γ ^ E₀_r := by
      rw [show (3 * γ / 4 : ℝ) = (3 / 4) * γ by ring, mul_pow]
    have h3 : ((H : ℝ) + 1) ^ (d - 1) * ((H : ℝ) + 1) = ((H : ℝ) + 1) ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    have h4 : ((H + 1 : ℕ) : ℝ) = (H : ℝ) + 1 := by push_cast; ring
    have h1' : (c₀_r * (3 / 4 : ℝ) ^ E₀_r * γ ^ E₀_r) * (M₁ : ℝ) * ((H : ℝ) + 1)
        ≤ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i₀).1 : ℝ) := by
      have h := h1
      rw [h2, h4] at h
      linarith [h]
    calc c₀_r * (3 / 4 : ℝ) ^ E₀_r * c_h * γ ^ (E₀_r + e_h) * ((H : ℝ) + 1) ^ d
        = (c₀_r * (3 / 4 : ℝ) ^ E₀_r * γ ^ E₀_r)
            * ((c_h * γ ^ e_h * ((H : ℝ) + 1) ^ (d - 1)) * ((H : ℝ) + 1)) := by
          rw [pow_add, ← h3]; ring
      _ ≤ (c₀_r * (3 / 4 : ℝ) ^ E₀_r * γ ^ E₀_r) * ((M₁ : ℝ) * ((H : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hwin (by positivity)) (by positivity)
      _ = (c₀_r * (3 / 4 : ℝ) ^ E₀_r * γ ^ E₀_r) * (M₁ : ℝ) * ((H : ℝ) + 1) := by ring
      _ ≤ (Lw ((Fintype.equivFin (Σ _s : D.S 1, Fin T)).symm i₀).1 : ℝ) := h1'
  · exact hfinal

end

end Work.Prop36SW

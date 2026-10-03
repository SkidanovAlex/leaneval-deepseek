import Mathlib
import Submission.Work.Prop36SW.chainDefs
import Submission.Work.Prop36SW.roundPeelAuxW
import Submission.Work.Prop36SW.roundRegroupNoPar
import Submission.Work.Prop36SW.boxNorm_famIdx_le_of_le
import Submission.Work.Peluse.Prop36SW.lstateSpread
import Submission.Work.Peluse.Prop36SW.spreadBack
import Submission.Work.Prop36SW.shrinkExplicit
import Submission.Work.Prop36SW.dirBoundsNew

/-!
# The round of the §5 chain: completing `roundToNextState` (`RoundStep`)

This file proves `Work.Prop36SW.roundToNextStateS`, the state-to-state round of the §5 chain
(`Work.Prop36SW.RoundStep`), completing the partial proof kept in
`Submission/Work/Prop36SW/roundToNext.lean` (`roundToNextState_wip`).

Steps 1–3 (spread to the good set, the strengthened round `RoundStmtW`, spread back) are copied
from that file.  The new content is steps 4–6:

* **shrink** the round's per-slot windows `Lw s` to the common window
  `M₁' := min (min_s Lw s) (M₁ (H+1))` via the (explicit-constant) level-`≥2` shrink
  `boxNormPow_arithIcc_shrink_slot`; when the round's level is `1`, first apply the
  Gowers–Cauchy–Schwarz level raise `two_mul_boxNormPow_succ_ge_complex` in the *last* coordinate
  (where the direction set is the already-shrunk `arithIcc q M₁'`, hence bounded) and then the
  level-`2` shrink (`boxNormPow_one_raise_shrink`);
* **regroup** with `roundRegroupNoPar` (the window must be a common `peelL M₁ M₂ γw`, arranged by
  `γw := M₁'/(M₁ M₂)`);
* **replace** the data-dependent multiplicity `t''` by the data-independent constant `TT`
  (`boxNorm_famIdx_le_of_le`), and assemble the `LStateBox` conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators

namespace Work.Prop36SW

noncomputable section

open Work.Peluse
open Work.Peluse.UControl
open Work.Peluse.Prop36SW

/-! ## The level-`1` raise followed by the level-`2` shrink -/

/-- **The raise-and-shrink step of the round at level `1`.**

For a single arithmetic progression `q[Lbig]` whose level-`1` box-norm power is known, the
Gowers–Cauchy–Schwarz level raise is applied with the *shrunk* direction set `q[Lsmall]` in the
**last** coordinate (so that only `|z| ≤ N` for `z ∈ q[Lsmall]` is needed), and the level-`2`
coordinatewise shrink (`boxNormPow_arithIcc_shrink_slot` at `t = 2`) replaces `q[Lbig]` by
`q[Lsmall]`:

`(‖f‖_{□¹_{q[Lbig]}(N)})² ≤ 32 · ‖f‖_{□²_{q[Lsmall],q[Lsmall]}(N)}`. -/
theorem boxNormPow_one_raise_shrink (q : ℤ) (Lbig Lsmall : ℕ) (hLs : Lsmall ≤ Lbig)
    (hL1 : 1 ≤ Lsmall) (hLb : 1 ≤ Lbig) (N : ℕ) (hN : 0 < N) (f : ℤ → ℂ)
    (hbdd : ∀ z ∈ arithIcc q Lsmall, |z| ≤ (N : ℤ))
    (hsupp : SupportIn f N) :
    (boxNormPow 1 (fun _ : Fin 1 => arithIcc q Lbig) (symIcc N) f) ^ 2
      ≤ 32 * boxNormPow 2 (fun _ : Fin 2 => arithIcc q Lsmall) (symIcc N) f := by
  classical
  have hsupp' : ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
    intro x hx
    apply hsupp
    have hx' : ¬ |x| ≤ (N : ℤ) := fun hle => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hle)
    have h2 : (N : ℤ) < |x| := lt_of_not_ge hx'
    have h3 : (N : ℤ) < (x.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact h2
    exact_mod_cast h3
  set Q : Fin 2 → Finset ℤ := fun i => if i = 0 then arithIcc q Lbig else arithIcc q Lsmall with hQ
  have hQne : ∀ i : Fin 2, (Q i).Nonempty := by
    intro i
    have h : Q i = if i = 0 then arithIcc q Lbig else arithIcc q Lsmall := by rw [hQ]
    rw [h]
    by_cases hi : i = 0
    · rw [if_pos hi]
      exact Finset.card_pos.mp (by simpa using Work.Peluse.Prop36SW.arithIcc_card_pos q hLb)
    · rw [if_neg hi]
      exact Finset.card_pos.mp (by simpa using Work.Peluse.Prop36SW.arithIcc_card_pos q hL1)
  have hlast : Q (Fin.last 1) = arithIcc q Lsmall := by
    rw [hQ]
    simp [Fin.last]
  have hbd : ∀ z ∈ Q (Fin.last 1), |z| ≤ (N : ℤ) := by
    intro z hz
    rw [hlast] at hz
    exact hbdd z hz
  have hgcs := Work.Peluse.Concat.two_mul_boxNormPow_succ_ge_complex (n := 1) Q hN f hQne hbd hsupp'
  have h1fam : (fun i : Fin 1 => Q i.castSucc) = fun _ : Fin 1 => arithIcc q Lbig := by
    funext i
    have hii : i = 0 := Subsingleton.elim i 0
    subst hii
    rw [hQ]
    simp
  rw [h1fam] at hgcs
  have hsh := Work.Prop36SW.shrinkExplicit (t := 2) (by norm_num) (fun _ : Fin 2 => q)
    (fun _ : Fin 2 => Lsmall) (fun i : Fin 2 => if i = 0 then Lbig else Lsmall)
    (fun _ => hL1) (fun i => by fin_cases i <;> simp [hLs]) (symIcc N) f ⟨N, hsupp⟩
  have hQeq : (fun i : Fin 2 => arithIcc q (if i = 0 then Lbig else Lsmall)) = Q := by
    funext i
    rw [hQ]
    by_cases h : i = 0 <;> simp [h]
  rw [hQeq] at hsh
  norm_num at hsh
  nlinarith [hgcs, hsh, norm_nonneg (boxNormPow 2 Q (symIcc N) f)]

theorem roundToNextStateS (hW : ∀ m : ℕ, Work.Peluse.Prop36SW.RoundStmtW (m + 1))
    (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) (Λ : ℕ)
    (kω : Work.Peluse.UControl.SlotSet (D.S (m + 2)) (fun _ => 1) → ℕ)
    (hk : 1 ≤ Fintype.card (D.S (m + 2))) (hm : m + 2 ≤ d)
    (hΛ : Λ ≤ Nat.factorial (d - 1)) :
    Work.Prop36SW.RoundStep D d c m Λ kω := by
  classical
  -- ## the round's data-independent constants
  obtain ⟨C_r, E_r, Cn_r, Mn_r, T_r, c₀, E₀, C₁, hC_r, hCn_r, hMn_r, hT_r, hc₀, hC₁, hround⟩ :=
    (Nat.sub_add_cancel hk ▸ hW (Fintype.card (D.S (m + 2)) - 1)) (D.S (m + 2)) rfl
      (nD D (m + 2)) kω (pFlat D d c (m + 1) Λ) 1
  -- ## the constants we produce
  set S2 : ℕ := Fintype.card (D.S (m + 2)) with hS2def
  set TT : ℕ := 2 * T_r * S2 + 2 with hTTdef
  set Dr : ℝ := C_r * (3 / 4 : ℝ) ^ E_r with hDrdef
  have hDrpos : 0 < Dr := by rw [hDrdef]; positivity
  set Cc : ℝ := (4 : ℝ) ^ (-(TT : ℤ)) *
    min (Dr / 4) (min (Dr ^ 2 / 256) 1) with hCcdef
  have hCcpos : 0 < Cc := by
    rw [hCcdef]
    exact mul_pos (by positivity) (lt_min (by linarith) (lt_min (by positivity) (by norm_num)))
  have hCcle1 : Cc ≤ 1 := by
    rw [hCcdef]
    have h1 : (4 : ℝ) ^ (-(TT : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))
    have h2 : min (Dr / 4) (min (Dr ^ 2 / 256) 1) ≤ 1 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith [h1, h2, le_of_lt hCcpos, (by positivity : (0:ℝ) ≤ (4:ℝ) ^ (-(TT:ℤ)))]
  have hTT1 : 1 ≤ TT := by rw [hTTdef]; omega
  have hTT2 : 2 ≤ TT := by rw [hTTdef]; omega
  have hS2pos : 0 < S2 := by rw [hS2def]; omega
  refine ⟨Cc, 2 * E_r, Cn_r, Mn_r, TT, min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2, max E₀ 1,
      hCcpos, hCn_r, hMn_r, hTT1, ?_, le_max_right _ _, ?_⟩
  · -- `0 < c₁`
    have h1 : 0 < min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 := lt_min (by positivity) (by norm_num)
    linarith
  · -- the state-to-state step
    intro H hH M₁ N f γ hst hM₁inv hNinv hgood hthr
    have hst' := hst
    obtain ⟨hγ0, hγ1, hM₂1, hM₂M₁, hN1, hM₁M₂, hdir1, hdir2, hbdd, hsup, hfam⟩ := hst
    have hH1 : 1 ≤ H + 1 := by omega
    have hM₁1 : 1 ≤ M₁ := le_trans hM₂1 hM₂M₁
    have hM₁2 : 2 ≤ M₁ := le_trans (by omega : 2 ≤ H + 1) hM₂M₁
    set A : Finset (Fin (nD D (m + 2)) → ℤ) := Abox D (m + 2) H with hA
    set A' : Finset (Fin (nD D (m + 2)) → ℤ) :=
      A.filter (fun a => ∀ i, pFlat D d c (m + 1) Λ i a ≠ 0) with hA'
    -- ## 1. the good-set spread
    have hspread : LStateAbs kω (pFlat D d c (m + 1) Λ) M₁ (H + 1) N 1 A' (fun _ => f)
        (3 * γ / 4) :=
      lstateSpread kω (pFlat D d c (m + 1) Λ) M₁ (H + 1) N 1 A (fun _ => f) γ hst' hγ0 hgood
    -- ## 2. the strengthened round on the good set
    obtain ⟨t, Lw, N₁, htb, hpos1, hLwge, hN1le, hwinlo, hwinhi, hroundc⟩ :=
      hround M₁ (H + 1) N A' (fun _ => f) (3 * γ / 4) hspread
        (by rw [Nat.cast_add, Nat.cast_one]; exact hthr)
    let nn : ℕ := Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (t s)))
    let ef : (Sigma (fun s : D.S (m + 2) => Fin (t s))) ≃ Fin nn :=
      Fintype.equivFin (Sigma (fun s : D.S (m + 2) => Fin (t s)))
    let Qf : (Fin (nD D (m + 2)) → ℤ) → Fin nn → Finset ℤ := fun a i =>
      arithIcc (pFlat D d c (m + 1) Λ (ef.symm i).1 a) (Lw (ef.symm i).1)
    have hroundc' : C_r * (3 * γ / 4) ^ E_r ≤ (A'.card : ℝ)⁻¹ *
        ∑ a ∈ A', boxNormPow nn (Qf a) (symIcc N₁) f := hroundc
    have hnn1 : 1 ≤ nn := hpos1
    -- ## 3. the spread back to the full box
    have hA'sub : A' ⊆ A := by rw [hA']; exact Finset.filter_subset _ _
    have hdiff : A \ A' = A.filter (fun a => ∃ i, pFlat D d c (m + 1) Λ i a = 0) := by
      rw [hA']
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨ha, hna⟩
        refine ⟨ha, ?_⟩
        by_contra hcon
        push_neg at hcon
        exact hna ⟨ha, hcon⟩
      · rintro ⟨ha, i, hi⟩
        refine ⟨ha, ?_⟩
        rintro ⟨-, hall⟩
        exact hall i hi
    have hcard2 : (A.card : ℝ) ≤ 2 * (A'.card : ℝ) := by
      have hgood' : 4 * ((A \ A').card : ℝ) ≤ γ * (A.card : ℝ) := by rw [hdiff]; exact hgood
      have hcast : ((A \ A').card : ℝ) + (A'.card : ℝ) = (A.card : ℝ) := by
        rw [← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hA'sub]
      have hx : ((A \ A').card : ℝ) ≤ (A.card : ℝ) / 4 := by
        nlinarith [hgood', hγ1, Nat.cast_nonneg (α := ℝ) A.card]
      linarith
    have hhalf := filter_average_ge_half A A' (fun a => boxNormPow nn (Qf a) (symIcc N₁) f)
      hA'sub (fun a _ => norm_nonneg _) hcard2
    have hStr0 : C_r / 2 * (3 / 4 : ℝ) ^ E_r * γ ^ E_r ≤
        (A.card : ℝ)⁻¹ * ∑ a ∈ A, boxNormPow nn (Qf a) (symIcc N₁) f := by
      have h1 : C_r / 2 * (3 / 4 : ℝ) ^ E_r * γ ^ E_r
          = (1 / 2) * (C_r * (3 * γ / 4) ^ E_r) := by
        rw [show (3 * γ / 4 : ℝ) = (3 / 4) * γ by ring, mul_pow]; ring
      rw [h1]
      calc (1 / 2) * (C_r * (3 * γ / 4) ^ E_r)
          = (C_r * (3 * γ / 4) ^ E_r) / 2 := by ring
        _ ≤ ((A'.card : ℝ)⁻¹ * ∑ a ∈ A', boxNormPow nn (Qf a) (symIcc N₁) f) / 2 := by
            linarith [hroundc']
        _ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, boxNormPow nn (Qf a) (symIcc N₁) f := hhalf
    set X : ℝ := C_r / 2 * (3 / 4 : ℝ) ^ E_r * γ ^ E_r with hXdef
    have hStr0X : X ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, boxNormPow nn (Qf a) (symIcc N₁) f := by
      rw [hXdef]; exact hStr0
    have hXpos : 0 < X := by rw [hXdef]; positivity
    have hγpow : γ ^ (2 * E_r) ≤ γ ^ E_r := pow_le_pow_of_le_one hγ0.le hγ1 (by omega)
    -- ## the ambient conditions on `f`
    have hpar_ne : (D.parBox (m + 2) H).Nonempty := by
      refine ⟨fun j s => 0, ?_⟩
      rw [Work.Peluse.UControl.IdxDatum.mem_parBox]
      intro j s; constructor <;> omega
    obtain ⟨a₀, ha₀⟩ := hpar_ne
    have hAne : A.Nonempty := by
      rw [hA, Abox]
      exact ⟨encD D (m + 2) a₀, Finset.mem_image.mpr ⟨a₀, ha₀, rfl⟩⟩
    have hAcard1 : (1 : ℝ) ≤ (A.card : ℝ) := by
      have h : 0 < A.card := Finset.card_pos.mpr hAne
      have h2 : (1 : ℕ) ≤ A.card := by omega
      exact_mod_cast h2
    obtain ⟨a₀', ha₀'⟩ := hAne
    have hSupN : SupportIn f N := hsup a₀' ha₀'
    have hFbdd : ∀ x : ℤ, ‖f x‖ ≤ 1 := hbdd a₀' ha₀'
    have hSupN₁ : SupportIn f N₁ := SupportIn.mono hSupN hN1le
    have hSupN₁' : ∀ x : ℤ, x ∉ symIcc N₁ → f x = 0 := by
      intro x hx
      refine hSupN₁ x ?_
      have h1 : ¬ |x| ≤ (N₁ : ℤ) := fun hle => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hle)
      have h2 : (N₁ : ℤ) < |x| := lt_of_not_ge h1
      have h3 : (N₁ : ℤ) < (x.natAbs : ℤ) := by rwa [Int.natCast_natAbs]
      exact_mod_cast h3
    have hN1pos : 0 < N₁ := lt_of_lt_of_le (by omega : 0 < N) hN1le
    have hHcastR : ((H + 1 : ℕ) : ℝ) = (H : ℝ) + 1 := by push_cast; ring
    -- ## the common window `M₁'` of the next state
    haveI hS2ne : Nonempty (D.S (m + 2)) := Fintype.card_pos_iff.mp (by omega)
    have hWne : ((Finset.univ : Finset (D.S (m + 2))).image Lw).Nonempty :=
      Finset.image_nonempty.mpr Finset.univ_nonempty
    set W₀ : ℕ := ((Finset.univ : Finset (D.S (m + 2))).image Lw).min' hWne with hW₀def
    set M₁' : ℕ := min W₀ (M₁ * (H + 1)) with hM₁'def
    have hM₁'leW : ∀ s : D.S (m + 2), M₁' ≤ Lw s := by
      intro s
      refine le_trans (min_le_left _ _) ?_
      rw [hW₀def]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩)
    have hM₁'le2 : M₁' ≤ M₁ * (H + 1) := min_le_right _ _
    have hM₁'geH : H + 1 ≤ M₁' := by
      refine le_min ?_ ?_
      · rw [hW₀def]
        refine Finset.le_min' _ hWne _ (fun b hb => ?_)
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hb
        exact hLwge s
      · exact Nat.le_mul_of_pos_left _ hM₁1
    have hM₁'ge2 : 2 ≤ M₁' := le_trans (by omega : 2 ≤ H + 1) hM₁'geH
    have hM₁'ge1 : 1 ≤ M₁' := le_trans (by norm_num : 1 ≤ 2) hM₁'ge2
    have hM₁'le2R : (M₁' : ℝ) ≤ (M₁ : ℝ) * ((H : ℝ) + 1) := by
      have h := hM₁'le2
      have h' : ((M₁' : ℕ) : ℝ) ≤ ((M₁ * (H + 1) : ℕ) : ℝ) := by exact_mod_cast h
      simpa using h'
    /- the lower bound on the new window -/
    have hc₁A : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1
        ≤ c₀ * (3 / 4 : ℝ) ^ E₀ * γ ^ E₀ := by
      have h1 : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 ≤ c₀ * (3 / 4 : ℝ) ^ E₀ := by
        have h2 := min_le_left (c₀ * (3 / 4 : ℝ) ^ E₀) 1
        have h3 : 0 < min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 := lt_min (by positivity) (by norm_num)
        linarith
      have h2 : γ ^ max E₀ 1 ≤ γ ^ E₀ := pow_le_pow_of_le_one hγ0.le hγ1 (le_max_left _ _)
      exact mul_le_mul h1 h2 (pow_nonneg hγ0.le _) (by positivity)
    have hc₁B : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1 ≤ 1 := by
      have h1 : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 ≤ 1 := by
        have h2 := min_le_right (c₀ * (3 / 4 : ℝ) ^ E₀) 1
        linarith
      have h2 : γ ^ max E₀ 1 ≤ 1 := pow_le_one₀ hγ0.le hγ1
      exact mul_le_one₀ h1 (pow_nonneg hγ0.le _) h2
    have hM₁'low : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1 * (M₁ : ℝ)
        * ((H : ℝ) + 1) ≤ (M₁' : ℝ) := by
      have hmem : W₀ ∈ ((Finset.univ : Finset (D.S (m + 2))).image Lw) := by
        rw [hW₀def]; exact Finset.min'_mem _ _
      obtain ⟨sW, -, hsW⟩ := Finset.mem_image.mp hmem
      have h1 : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1 * (M₁ : ℝ)
          * ((H : ℝ) + 1) ≤ (W₀ : ℝ) := by
        rw [← hsW]
        have h5 : c₀ * (3 / 4 : ℝ) ^ E₀ * γ ^ E₀ * (M₁ : ℝ) * ((H : ℝ) + 1)
            ≤ (Lw sW : ℝ) := by
          have h6 : c₀ * (3 * γ / 4) ^ E₀ * (M₁ : ℝ) * ((H : ℝ) + 1) ≤ (Lw sW : ℝ) := by
            simpa only [hHcastR] using hwinlo sW
          calc c₀ * (3 / 4 : ℝ) ^ E₀ * γ ^ E₀ * (M₁ : ℝ) * ((H : ℝ) + 1)
              = c₀ * (3 * γ / 4) ^ E₀ * (M₁ : ℝ) * ((H : ℝ) + 1) := by
                rw [show (3 * γ / 4 : ℝ) = (3 / 4) * γ by ring, mul_pow]; ring
            _ ≤ (Lw sW : ℝ) := h6
        calc min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1 * (M₁ : ℝ) * ((H : ℝ) + 1)
            = (min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1) * ((M₁ : ℝ) * ((H : ℝ) + 1)) := by
              ring
          _ ≤ (c₀ * (3 / 4 : ℝ) ^ E₀ * γ ^ E₀) * ((M₁ : ℝ) * ((H : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hc₁A (by positivity)
          _ = c₀ * (3 / 4 : ℝ) ^ E₀ * γ ^ E₀ * (M₁ : ℝ) * ((H : ℝ) + 1) := by ring
          _ ≤ (Lw sW : ℝ) := h5
      have h2 : min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1 * (M₁ : ℝ)
          * ((H : ℝ) + 1) ≤ ((M₁ * (H + 1) : ℕ) : ℝ) := by
        calc min (c₀ * (3 / 4 : ℝ) ^ E₀) 1 / 2 * γ ^ max E₀ 1 * (M₁ : ℝ) * ((H : ℝ) + 1)
            ≤ 1 * (M₁ : ℝ) * ((H : ℝ) + 1) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ (H:ℝ) + 1)
              exact mul_le_mul_of_nonneg_right hc₁B (Nat.cast_nonneg _)
          _ = ((M₁ * (H + 1) : ℕ) : ℝ) := by push_cast; ring
      rw [hM₁'def, Nat.cast_min]
      exact le_min h1 h2
    /- ## 4–6: the level/ window handling, the regrouping and the multiplicity replacement -/
    set γw : ℝ := (M₁' : ℝ) / ((M₁ : ℝ) * ((H : ℝ) + 1)) with hγwdef
    have hM₁M₂pos : (0 : ℝ) < (M₁ : ℝ) * ((H : ℝ) + 1) := by positivity
    have hpeel : Work.Peluse.Prop36SW.peelL M₁ (H + 1) γw = M₁' := by
      rw [Work.Peluse.Prop36SW.peelL, hγwdef, hHcastR]
      have h2 : (M₁' : ℝ) / ((M₁ : ℝ) * ((H : ℝ) + 1)) * (M₁ : ℝ) * ((H : ℝ) + 1)
          = (M₁' : ℝ) := by
        field_simp
      rw [h2, Int.floor_natCast]
      simp
    -- the level/window step: reduce to a family bound at the common window `M₁'`
    have key : ∃ (t'' : D.S (m + 2) → ℕ) (Y : ℝ), 0 < Y ∧
        Cc * γ ^ (2 * E_r) ≤ Y ∧
        (∀ s : D.S (m + 2), t'' s ≤ 2 * T_r) ∧
        2 * Y ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
          boxNormPow (Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (t'' s))))
            (fun i => arithIcc (pFlat D d c (m + 1) Λ
              ((Fintype.equivFin (Sigma (fun s : D.S (m + 2) => Fin (t'' s)))).symm i).1 a) M₁')
            (symIcc N₁) f := by
      by_cases h2nn : 2 ≤ nn
      · -- ## the round's level is at least `2`: shrink the windows directly
        have hnnTT : nn ≤ TT := by
          have h1 : nn = ∑ s : D.S (m + 2), t s := by
            rw [show nn = Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (t s))) from rfl,
              Fintype.card_sigma]
            exact Finset.sum_congr rfl (fun s _ => Fintype.card_fin _)
          rw [h1]
          calc ∑ s : D.S (m + 2), t s ≤ ∑ _s : D.S (m + 2), T_r :=
                Finset.sum_le_sum (fun s _ => htb s)
            _ = S2 * T_r := by rw [Finset.sum_const, Finset.card_univ, hS2def, smul_eq_mul]
            _ ≤ TT := by
                rw [hTTdef]
                calc S2 * T_r = T_r * S2 := by ring
                  _ ≤ 2 * (T_r * S2) := Nat.le_mul_of_pos_left _ (by norm_num)
                  _ = 2 * T_r * S2 := by ring
                  _ ≤ 2 * T_r * S2 + 2 := Nat.le_add_right _ _
        have h4 : (4 : ℝ) ^ (-(TT : ℤ)) ≤ (4 : ℝ) ^ (-(nn : ℤ)) := by
          refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 4) ?_
          have h : (nn : ℤ) ≤ (TT : ℤ) := by exact_mod_cast hnnTT
          omega
        have hshrink : ∀ a : Fin (nD D (m + 2)) → ℤ,
            (4 : ℝ) ^ (-(nn : ℤ)) * boxNormPow nn (Qf a) (symIcc N₁) f
              ≤ boxNormPow nn (fun i : Fin nn =>
                  arithIcc (pFlat D d c (m + 1) Λ (ef.symm i).1 a) M₁') (symIcc N₁) f := by
          intro a
          exact Work.Prop36SW.shrinkExplicit h2nn (fun i => pFlat D d c (m + 1) Λ (ef.symm i).1 a)
            (fun _ => M₁') (fun i => Lw (ef.symm i).1) (fun _ => hM₁'ge1)
            (fun i => hM₁'leW (ef.symm i).1) (symIcc N₁) f ⟨N₁, hSupN₁⟩
        have hstep : (4 : ℝ) ^ (-(nn : ℤ)) * X ≤
            (A.card : ℝ)⁻¹ * ∑ a ∈ A,
              boxNormPow nn (fun i : Fin nn =>
                arithIcc (pFlat D d c (m + 1) Λ (ef.symm i).1 a) M₁') (symIcc N₁) f := by
          refine le_trans (mul_le_mul_of_nonneg_left hStr0X (by positivity)) ?_
          calc (4 : ℝ) ^ (-(nn : ℤ)) * ((A.card : ℝ)⁻¹ *
                ∑ a ∈ A, boxNormPow nn (Qf a) (symIcc N₁) f)
              = (A.card : ℝ)⁻¹ * ((4 : ℝ) ^ (-(nn : ℤ)) *
                ∑ a ∈ A, boxNormPow nn (Qf a) (symIcc N₁) f) := by ring
            _ = (A.card : ℝ)⁻¹ * ∑ a ∈ A,
                  (4 : ℝ) ^ (-(nn : ℤ)) * boxNormPow nn (Qf a) (symIcc N₁) f := by
                rw [Finset.mul_sum]
            _ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
                  boxNormPow nn (fun i : Fin nn =>
                    arithIcc (pFlat D d c (m + 1) Λ (ef.symm i).1 a) M₁') (symIcc N₁) f :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hshrink a))
                  (by positivity)
        have hCcA : Cc * γ ^ (2 * E_r) ≤ (4 : ℝ) ^ (-(nn : ℤ)) * X / 2 := by
          have hmin : min (Dr / 4) (min (Dr ^ 2 / 256) 1) ≤ Dr / 4 := min_le_left _ _
          have hX : X = (Dr / 2) * γ ^ E_r := by rw [hXdef, hDrdef]; ring
          calc Cc * γ ^ (2 * E_r)
              = ((4 : ℝ) ^ (-(TT : ℤ)) * min (Dr / 4) (min (Dr ^ 2 / 256) 1)) * γ ^ (2 * E_r) := by
                rw [hCcdef]
            _ ≤ ((4 : ℝ) ^ (-(nn : ℤ)) * (Dr / 4)) * γ ^ E_r := by
                apply mul_le_mul
                · exact mul_le_mul h4 hmin (by positivity) (by positivity)
                · exact hγpow
                · positivity
                · positivity
            _ = (4 : ℝ) ^ (-(nn : ℤ)) * X / 2 := by rw [hX]; ring
        refine ⟨t, (4 : ℝ) ^ (-(nn : ℤ)) * X / 2, by positivity, hCcA, fun s => ?_, ?_⟩
        · exact le_trans (htb s) (by omega)
        · linarith [hstep]
      · -- ## the round's level is `1`: raise to level `2`, then shrink
        have hnn1eq : nn = 1 := by omega
        haveI hsub : Subsingleton (Sigma (fun s : D.S (m + 2) => Fin (t s))) :=
          Fintype.card_le_one_iff_subsingleton.mp (by omega)
        obtain ⟨u₀⟩ := (Fintype.card_pos_iff.mp
          (show 0 < Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (t s))) by omega) :
            Nonempty (Sigma (fun s : D.S (m + 2) => Fin (t s))))
        have hu₀ : 1 ≤ t u₀.1 := by have := u₀.2.isLt; omega
        have hcol : ∀ i : Fin nn, (ef.symm i).1 = u₀.1 := fun i =>
          congrArg Sigma.fst (Subsingleton.elim (ef.symm i) u₀)
        have hbddQ : ∀ a ∈ A, ∀ z ∈ arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁',
            |z| ≤ (N₁ : ℤ) := by
          intro a ha z hz
          obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
          obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
          have hdir : |pFlat D d c (m + 1) Λ u₀.1 a| * (M₁ : ℤ) * ((H + 1 : ℕ) : ℤ) ≤ (N : ℤ) :=
            hdir1 u₀.1 a ha
          have hdirH : |pFlat D d c (m + 1) Λ u₀.1 a| * (M₁ : ℤ) * ((H : ℤ) + 1) ≤ (N : ℤ) := by
            simpa using hdir
          have hM₁'le : (M₁' : ℤ) ≤ (M₁ : ℤ) * ((H : ℤ) + 1) := by
            have := hM₁'le2
            push_cast
            exact_mod_cast this
          have h1 : |pFlat D d c (m + 1) Λ u₀.1 a| * (M₁' : ℤ) ≤ (N : ℤ) := by
            calc |pFlat D d c (m + 1) Λ u₀.1 a| * (M₁' : ℤ)
                ≤ |pFlat D d c (m + 1) Λ u₀.1 a| * ((M₁ : ℤ) * ((H : ℤ) + 1)) :=
                  mul_le_mul_of_nonneg_left hM₁'le (abs_nonneg _)
              _ = |pFlat D d c (m + 1) Λ u₀.1 a| * (M₁ : ℤ) * ((H : ℤ) + 1) := by ring
              _ ≤ (N : ℤ) := hdirH
          calc |z| = |pFlat D d c (m + 1) Λ u₀.1 a * (k : ℤ)| := by rw [hkz]
            _ = |pFlat D d c (m + 1) Λ u₀.1 a| * (k : ℤ) := by
                rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg k)]
            _ ≤ |pFlat D d c (m + 1) Λ u₀.1 a| * (M₁' : ℤ) :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast hk2) (abs_nonneg _)
            _ ≤ (N : ℤ) := h1
            _ ≤ (N₁ : ℤ) := by exact_mod_cast hN1le
        -- the level-one form of the round's bound
        have hbnn : ∀ a : Fin (nD D (m + 2)) → ℤ,
            boxNormPow nn (Qf a) (symIcc N₁) f
              = boxNormPow 1 (fun _ : Fin 1 =>
                  arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f := by
          intro a
          have hQfeq : Qf a
              = fun _ : Fin nn => arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1) := by
            funext i
            show arithIcc (pFlat D d c (m + 1) Λ (ef.symm i).1 a) (Lw (ef.symm i).1)
              = arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)
            rw [hcol i]
          rw [hQfeq, hnn1eq]
        have hStr1 : X ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
            boxNormPow 1 (fun _ : Fin 1 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f := by
          refine le_trans hStr0X ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum (fun a _ => le_of_eq (hbnn a))
        -- the level-`2` bound with the shrunk window
        have hpt : ∀ a ∈ A,
            (boxNormPow 1 (fun _ : Fin 1 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f) ^ 2
              ≤ 32 * boxNormPow 2 (fun _ : Fin 2 =>
                  arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f := by
          intro a ha
          refine boxNormPow_one_raise_shrink (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1) M₁'
            (hM₁'leW u₀.1) hM₁'ge1 (le_trans (by omega : 1 ≤ H + 1) (hLwge u₀.1))
            N₁ hN1pos f ?_ hSupN₁
          intro z hz
          exact hbddQ a ha z hz
        -- Cauchy–Schwarz in the parameters
        have hAle : 0 < (A.card : ℝ) := lt_of_lt_of_le (by norm_num) hAcard1
        have h1 : (A.card : ℝ) * X ≤ ∑ a ∈ A,
            boxNormPow 1 (fun _ : Fin 1 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f := by
          have h2 : (A.card : ℝ) * X ≤ (A.card : ℝ) * ((A.card : ℝ)⁻¹ *
              ∑ a ∈ A, boxNormPow 1 (fun _ : Fin 1 =>
                arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f) :=
            mul_le_mul_of_nonneg_left hStr1 (le_of_lt hAle)
          have h3 : (A.card : ℝ) * ((A.card : ℝ)⁻¹ *
              ∑ a ∈ A, boxNormPow 1 (fun _ : Fin 1 =>
                arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f)
              = ∑ a ∈ A, boxNormPow 1 (fun _ : Fin 1 =>
                arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hAle), one_mul]
          rwa [h3] at h2
        have h3 : ((A.card : ℝ) * X) ^ 2 ≤ (A.card : ℝ) * ∑ a ∈ A,
            (boxNormPow 1 (fun _ : Fin 1 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f) ^ 2 :=
          le_trans (pow_le_pow_left₀ (by positivity) h1 2) sq_sum_le_card_mul_sum_sq
        have h4 : ∑ a ∈ A, (boxNormPow 1 (fun _ : Fin 1 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) (Lw u₀.1)) (symIcc N₁) f) ^ 2
            ≤ 32 * ∑ a ∈ A, boxNormPow 2 (fun _ : Fin 2 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun a ha => hpt a ha)
        have h5 : ((A.card : ℝ) * X) ^ 2 ≤ (A.card : ℝ) * (32 * ∑ a ∈ A,
            boxNormPow 2 (fun _ : Fin 2 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f) :=
          le_trans h3 (mul_le_mul_of_nonneg_left h4 (by positivity))
        have h6 : (A.card : ℝ) * X ^ 2 ≤ 32 * ∑ a ∈ A,
            boxNormPow 2 (fun _ : Fin 2 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f := by
          have h7 : ((A.card : ℝ) * X) ^ 2
              = (A.card : ℝ) * ((A.card : ℝ) * X ^ 2) := by ring
          rw [h7] at h5
          exact (mul_le_mul_iff_of_pos_left hAle).mp h5
        have hY2 : X ^ 2 / 32 ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
            boxNormPow 2 (fun _ : Fin 2 =>
              arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 32)]
          rw [show ((A.card : ℝ)⁻¹ * ∑ a ∈ A, boxNormPow 2 (fun _ : Fin 2 =>
                arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f) * 32
              = (32 * ∑ a ∈ A, boxNormPow 2 (fun _ : Fin 2 =>
                arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁') (symIcc N₁) f) / (A.card : ℝ) by
            ring]
          rw [le_div_iff₀ hAle]
          linarith [h6]
        -- the identification with the `Σ`-family
        have hcard2' : Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (2 * t s))) = 2 := by
          rw [Fintype.card_sigma]
          have h1 : ∀ s : D.S (m + 2), Fintype.card (Fin (2 * t s)) = 2 * t s :=
            fun s => Fintype.card_fin _
          simp only [h1]
          have hsum : ∑ s : D.S (m + 2), t s = 1 := by
            have h2 : nn = ∑ s : D.S (m + 2), t s := by
              rw [show nn = Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (t s))) from rfl,
                Fintype.card_sigma]
              exact Finset.sum_congr rfl (fun s _ => Fintype.card_fin _)
            omega
          rw [← Finset.mul_sum, hsum]
          norm_num
        have hfam2 : ∀ a : Fin (nD D (m + 2)) → ℤ,
            boxNormPow 2 (fun _ : Fin 2 => arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁')
                (symIcc N₁) f
              = boxNormPow (Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (2 * t s))))
                  (fun i => arithIcc (pFlat D d c (m + 1) Λ
                    ((Fintype.equivFin (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))).symm i).1 a) M₁')
                  (symIcc N₁) f := by
          intro a
          have hf : (fun i : Fin (Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))) =>
                arithIcc (pFlat D d c (m + 1) Λ
                  ((Fintype.equivFin (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))).symm i).1 a) M₁')
              = fun _ : Fin (Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))) =>
                  arithIcc (pFlat D d c (m + 1) Λ u₀.1 a) M₁' := by
            funext i
            have hv : 0 < t ((Fintype.equivFin
                (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))).symm i).1 := by
              have h := ((Fintype.equivFin
                (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))).symm i).2.isLt
              omega
            have h2 := Subsingleton.elim
              (⟨((Fintype.equivFin (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))).symm i).1,
                ⟨0, hv⟩⟩ : Sigma (fun s : D.S (m + 2) => Fin (t s))) u₀
            rw [congrArg Sigma.fst h2]
          rw [hf, hcard2']
        have hfinal : X ^ 2 / 32 ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A,
            boxNormPow (Fintype.card (Sigma (fun s : D.S (m + 2) => Fin (2 * t s))))
              (fun i => arithIcc (pFlat D d c (m + 1) Λ
                ((Fintype.equivFin (Sigma (fun s : D.S (m + 2) => Fin (2 * t s)))).symm i).1 a) M₁')
              (symIcc N₁) f := by
          refine le_trans hY2 ?_
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
          exact le_of_eq (hfam2 a)
        refine ⟨fun s => 2 * t s, X ^ 2 / 64, by positivity, ?_, fun s => ?_, ?_⟩
        · -- the constant
          have hmin : min (Dr / 4) (min (Dr ^ 2 / 256) 1) ≤ Dr ^ 2 / 256 :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          have hX : X = (Dr / 2) * γ ^ E_r := by rw [hXdef, hDrdef]; ring
          calc Cc * γ ^ (2 * E_r)
              = ((4 : ℝ) ^ (-(TT : ℤ)) * min (Dr / 4) (min (Dr ^ 2 / 256) 1)) * γ ^ (2 * E_r) := by
                rw [hCcdef]
            _ ≤ (Dr ^ 2 / 256) * γ ^ (2 * E_r) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                calc (4 : ℝ) ^ (-(TT : ℤ)) * min (Dr / 4) (min (Dr ^ 2 / 256) 1)
                    ≤ 1 * (Dr ^ 2 / 256) := by
                      apply mul_le_mul
                      · rw [zpow_neg, zpow_natCast]
                        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))
                      · exact hmin
                      · positivity
                      · norm_num
                  _ = Dr ^ 2 / 256 := one_mul _
            _ = X ^ 2 / 64 := by
                rw [hX]
                have h3 : ((Dr / 2) * γ ^ E_r) ^ 2 / 64 = Dr ^ 2 / 256 * (γ ^ E_r) ^ 2 := by ring
                rw [h3, ← pow_mul]
                ring_nf
        · exact Nat.mul_le_mul_left 2 (htb s)
        · linarith [hfinal]
    obtain ⟨t'', Y, hYpos, hCγ, ht''le2, hYle⟩ := key
    -- ## the regrouping
    have hreg := Work.Prop36SW.roundRegroupNoPar (D := D) (d := d) (c := c) (n := m) (Λ := Λ)
      (M₁ := M₁) (M₂ := H + 1) (H := H) (N := N₁) (hH := rfl) (f := f) (γ := 2 * Y) (γw := γw)
      (t := t'') (hL := by rw [hpeel]; exact hM₁'ge1) (hγ := by linarith) (hf1 := hFbdd)
      (hfs := hSupN₁) (h := by rw [hpeel]; exact hYle)
    rw [hpeel] at hreg
    -- ## the multiplicity replacement
    have hS2ge1 : 1 ≤ S2 := by omega
    have h2TrTT : 2 * T_r ≤ TT := by
      rw [hTTdef]
      calc 2 * T_r = 2 * T_r * 1 := by ring
        _ ≤ 2 * T_r * S2 := Nat.mul_le_mul_left _ hS2ge1
        _ ≤ 2 * T_r * S2 + 2 := Nat.le_add_right _ _
    have hle_kω' : ∀ ω : SlotSet (D.S (m + 1)) (fun _ => 1),
        regroupKω D (m + 1) t'' ω ≤ regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT) ω := by
      intro ω
      have h1 : regroupKω D (m + 1) t'' ω
          = ∑ s ∈ Finset.univ.filter (fun s : D.S (m + 1 + 1) => D.par (m + 1) s =
              ⟨ω.1.image (fun x => x.1), Finset.image_nonempty.mpr ω.2⟩), t'' s := rfl
      have h2 : regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT) ω
          = ∑ s ∈ Finset.univ.filter (fun s : D.S (m + 1 + 1) => D.par (m + 1) s =
              ⟨ω.1.image (fun x => x.1), Finset.image_nonempty.mpr ω.2⟩), TT := rfl
      rw [h1, h2]
      exact Finset.sum_le_sum (fun s _ => le_trans (ht''le2 s) h2TrTT)
    have hpt : ∀ a'' ∈ Abox D (m + 1) H,
        ∀ b ∈ paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1),
        boxNorm (Fintype.card (FamIdx (regroupKω D (m + 1) t'')))
          (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
            ((Fintype.equivFin (FamIdx (regroupKω D (m + 1) t''))).symm i)) (symIcc N₁) f
        ≤ 2 * boxNorm (Fintype.card (FamIdx
            (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT))))
          (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
            ((Fintype.equivFin (FamIdx
              (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)))).symm i)) (symIcc N₁) f := by
      intro a'' ha'' b hb
      refine Work.Prop36SW.boxNorm_famIdx_le_of_le
        (kω := regroupKω D (m + 1) t'')
        (kω' := regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)) hle_kω'
        (pFlat D d c m (Λ * (d - (m + 1)))) M₁' N₁ a'' b f hN1pos ?_ ?_ ?_
      · intro j
        change (arithIcc (∑ s ∈ ((Fintype.equivFin (FamIdx
            (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)))).symm j).1.1,
            pFlat D d c m (Λ * (d - (m + 1))) s.1 a'' * b s) M₁').Nonempty
        exact Finset.card_pos.mp (by simpa using
          Work.Peluse.Prop36SW.arithIcc_card_pos _ hM₁'ge1)
      · intro j z hz
        have h := (Work.Prop36SW.dirBoundsNew D d c m Λ H M₁ M₁' N hm hΛ hM₁inv hM₁'le2 hNinv).2
          (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)) a'' b ha'' hb j z hz
        exact le_trans h (by exact_mod_cast hN1le)
      · exact hSupN₁'
    have hsum : (∑ a'' ∈ Abox D (m + 1) H, ∑ b ∈ paramBox
            (k := fun _ : D.S (m + 1) => 1) (H + 1),
          boxNorm (Fintype.card (FamIdx (regroupKω D (m + 1) t'')))
            (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
              ((Fintype.equivFin (FamIdx (regroupKω D (m + 1) t''))).symm i)) (symIcc N₁) f)
        ≤ 2 * ∑ a'' ∈ Abox D (m + 1) H, ∑ b ∈ paramBox
            (k := fun _ : D.S (m + 1) => 1) (H + 1),
          boxNorm (Fintype.card (FamIdx
              (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT))))
            (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
              ((Fintype.equivFin (FamIdx
                (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)))).symm i)) (symIcc N₁) f := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a'' ha''
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun b hb => hpt a'' ha'' b hb)
    have hinfl : 2 * Y ≤ 2 * (((Abox D (m + 1) H).card : ℝ)⁻¹ *
        ((paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
        ∑ a'' ∈ Abox D (m + 1) H, ∑ b ∈ paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1),
          boxNorm (Fintype.card (FamIdx (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT))))
            (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
              ((Fintype.equivFin (FamIdx
                (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)))).symm i)) (symIcc N₁) f) := by
      have hK : (0 : ℝ) ≤ ((Abox D (m + 1) H).card : ℝ)⁻¹ *
          ((paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1)).card : ℝ)⁻¹ := by positivity
      calc 2 * Y ≤ ((Abox D (m + 1) H).card : ℝ)⁻¹ *
            ((paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
            (∑ a'' ∈ Abox D (m + 1) H, ∑ b ∈ paramBox
              (k := fun _ : D.S (m + 1) => 1) (H + 1),
              boxNorm (Fintype.card (FamIdx (regroupKω D (m + 1) t'')))
                (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
                  ((Fintype.equivFin (FamIdx (regroupKω D (m + 1) t''))).symm i)) (symIcc N₁) f) := hreg
        _ ≤ ((Abox D (m + 1) H).card : ℝ)⁻¹ *
            ((paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
            (2 * ∑ a'' ∈ Abox D (m + 1) H, ∑ b ∈ paramBox
              (k := fun _ : D.S (m + 1) => 1) (H + 1),
              boxNorm (Fintype.card (FamIdx
                  (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT))))
                (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
                  ((Fintype.equivFin (FamIdx
                    (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)))).symm i)) (symIcc N₁) f) :=
              mul_le_mul_of_nonneg_left hsum hK
        _ = 2 * (((Abox D (m + 1) H).card : ℝ)⁻¹ *
            ((paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
            ∑ a'' ∈ Abox D (m + 1) H, ∑ b ∈ paramBox
              (k := fun _ : D.S (m + 1) => 1) (H + 1),
              boxNorm (Fintype.card (FamIdx
                  (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT))))
                (fun i => pDirFamG (pFlat D d c m (Λ * (d - (m + 1)))) M₁' a'' b
                  ((Fintype.equivFin (FamIdx
                    (regroupKω D (m + 1) (fun _ : D.S (m + 2) => TT)))).symm i)) (symIcc N₁) f) := by
              ring
    -- ## the ambient bounds for the new state
    have hM₂'leN : (M₁' : ℝ) * (((H + 1 : ℕ)) : ℝ) ≤ (N₁ : ℝ) := by
      have hstep1 : (M₁' : ℝ) * ((H : ℝ) + 1) ≤ ((H : ℝ) + 1) ^ (d - m) := by
        calc (M₁' : ℝ) * ((H : ℝ) + 1)
            ≤ ((M₁ : ℝ) * ((H : ℝ) + 1)) * ((H : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hM₁'le2R (by positivity)
          _ = (M₁ : ℝ) * ((H : ℝ) + 1) ^ 2 := by ring
          _ ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_right hM₁inv (by positivity)
          _ = ((H : ℝ) + 1) ^ (d - m) := by
              rw [← pow_add]; congr 1; omega
      have hstep2 : ((H : ℝ) + 1) ^ (d - m) ≤ ((H : ℝ) + 1) ^ d := by
        have hH1' : (1 : ℝ) ≤ (H : ℝ) + 1 := by
          have : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
          linarith
        exact pow_le_pow_right₀ hH1' (by omega)
      have hstep3 : ((H : ℝ) + 1) ^ d ≤ (N₁ : ℝ) := by
        have h3 : (1:ℝ) ≤ Work.Prop36SW.ambK D d c := Work.Prop36SW.one_le_ambK D d c
        have h4 : ((H : ℝ) + 1) ^ d ≤ Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d := by
          nlinarith [h3, pow_nonneg (by positivity : (0:ℝ) ≤ (H:ℝ) + 1) d]
        have hN1leR : (N : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN1le
        linarith [h4, hNinv, hN1leR]
      calc (M₁' : ℝ) * (((H + 1 : ℕ)) : ℝ) = (M₁' : ℝ) * ((H : ℝ) + 1) := by
            rw [hHcastR]
        _ ≤ (N₁ : ℝ) := le_trans hstep1 (le_trans hstep2 hstep3)
    have hdirN : ∀ (s : D.S (m + 1)) (a : Fin (nD D (m + 1)) → ℤ),
        a ∈ Abox D (m + 1) H →
        |pFlat D d c m (Λ * (d - (m + 1))) s a| * (M₁' : ℤ) * (((H + 1 : ℕ)) : ℤ) ≤ (N₁ : ℤ) := by
      intro s a ha
      have h1 := (Work.Prop36SW.dirBoundsNew D d c m Λ H M₁ M₁' N hm hΛ hM₁inv hM₁'le2 hNinv).1 s a ha
      have h2 : ((H + 1 : ℕ) : ℤ) = (H : ℤ) + 1 := by push_cast; ring
      rw [h2]
      exact le_trans h1 (by exact_mod_cast hN1le)
    -- ## the assembly
    refine ⟨M₁', N₁, min Y 1, ?_, ?_, ?_, ?_, hM₁'ge2, hN1le, ?_, ?_⟩
    · exact lt_min hYpos (by norm_num)
    · exact min_le_right _ _
    · exact_mod_cast hM₁'le2
    · exact hM₁'low
    · refine le_min hCγ ?_
      calc Cc * γ ^ (2 * E_r) ≤ 1 * 1 :=
            mul_le_mul hCcle1 (pow_le_one₀ hγ0.le hγ1) (pow_nonneg hγ0.le _) (by norm_num)
        _ = 1 := one_mul 1
    · refine ⟨?_, ?_, hH1, hM₁'geH, by omega, hM₂'leN, ?_, ?_, (fun a _ x => hFbdd x),
        (fun a _ => hSupN₁), ?_⟩
      · exact lt_min hYpos (by norm_num)
      · exact min_le_right _ _
      · exact hdirN
      · intro i a ha
        simpa using hdirN i a ha
      · refine le_trans (min_le_left _ _) ?_
        linarith [hinfl]

end

end Work.Prop36SW

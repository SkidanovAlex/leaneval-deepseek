import Mathlib
import Submission.Work.Peluse.UControl.levCoord
import Submission.Work.Peluse.UControl.levTerminal
import Submission.Work.Peluse.UControl.levelCompareGen
import Submission.Work.Peluse.UControl.petLevelAux
import Submission.Work.Peluse.UControl.petChapter5_of_levelChainV3_aux

/-!
# The terminal analysis of the level chain

The last step of the level chain of `petChapter5Holds`: once the combinatorial part has produced the
level-`(d-1)` state `X' = W.step (Sum.inr 0) h₀ hh` (where `W` is the pre-closing state of the last
round, with a single class and all its slots of degree `2`), the analytic data of the chain is
transported along `Reach Y W`, the closing step is applied explicitly — its set of `y`-constant
children is *empty* (`petStepConstsClosing`), so the base function of the terminal state is the
reference slot function — and the terminal comparison `levelCompareGen` produces the output.

`/tmp` is not writable in this sandbox: `export TMPDIR=$PWD/.tmpdir` before any Lean invocation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

/-- **The terminal analysis of the level chain.**  See the module docstring. -/
theorem levelChainFinal {dd : ℕ} (hdd : 3 ≤ dd) {n : ℕ} (Y : HistData dd n) (lc : ℤ)
    (Lw : ℕ) (hLw : 1 ≤ Lw) (hLw1 : 1 ≤ Lw + 1) (N' : ℕ → ℕ) (P' : ℕ → ℕ → Finset ℕ)
    (c' : ℕ → ℕ → ℕ)
    (hsub' : ∀ i, ∀ k, k < N' (i + 1) → P' i k ⊆ Finset.range (N' i))
    (hne' : ∀ i, ∀ k, k < N' (i + 1) → (P' i k).Nonempty)
    (W : HistData dd Lw) (h₀ : Fin Lw → Bool)
    (hh : ((Sum.inr 0 : InitIdx dd), h₀) ∈ W.H)
    (f₀' : Fin (Lw + 1) → Bool) (A' : Finset (Fin (Lw + 1)))
    (atoms' : {s // s ∈ A'} → MvPolynomial (Fin (Lw + 1)) ℤ)
    (hDinv : LevDInv dd lc (dd - 1) (Lw + 1) hLw1 N' P' c'
      (W.step (Sum.inr 0) h₀ hh) f₀')
    (hcube' : LevCube dd 1 (Lw + 1) A' f₀' atoms' (W.step (Sum.inr 0) h₀ hh))
    (hAlvl : A' = lvlSet N' c' (Lw + 1) (dd - 1) hLw1)
    (hJ : petStepConsts (W.toSym).S ⟨((Sum.inr 0 : InitIdx dd), h₀), hh⟩ = ∅)
    (hWreach : Reach Y W)
    (Nstep : ℕ) (hNstep1 : 1 ≤ Nstep) (C₀ : ℝ) (hC0 : (3 : ℝ) ^ (Lw + 1) ≤ C₀)
    (hNstep : Nstep = (Lw + 1) - n)
    (hDcard : 2 ≤ Fintype.card ((levDatumOf N' P' hsub' hne').I (dd - 1)))
    (Nx Mw : ℕ) (γ' : ℝ) (Ftop : ℤ → ℂ) (F : (Y.toSym).S.ι → ℤ → ℂ)
    (g : WinTower ⌊γ' * (Mw : ℝ)⌋.toNat n → ℤ → ℂ) (c Dsb : ℕ) (B : ℝ)
    (hNx : 1 ≤ Nx) (hGb : ∀ i x, ‖F i x‖ ≤ 1) (hGs : ∀ i, SupportIn (F i) Nx)
    (hgb : ∀ a x, ‖g a x‖ ≤ 1) (hgs : ∀ a, SupportIn (g a) Nx)
    (hM : 1 ≤ Mw) (hH : 1 ≤ ⌊γ' * (Mw : ℝ)⌋.toNat) (hc : Nstep + 1 ≤ c)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hwin : ∀ k < Nstep, γ' ≤ petChainLevel B k ^ 2 /
      (20000 * ((((2 : ℕ) ^ k * Dsb : ℕ) : ℝ) + 1)))
    (hSB : (histPet Y ⌊γ' * (Mw : ℝ)⌋.toNat F g).toState.ShiftBound Nx Mw c Dsb)
    (htop : ∀ i, (∀ x, F i x = Ftop x) ∨ (∀ x, F i x = star (Ftop x)))
    (hg : ∃ c₀ : Bool, ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x))
    (hlam : B ≤ (histPet Y ⌊γ' * (Mw : ℝ)⌋.toNat F g).toState.lam Nx Mw) :
    ∃ (b : Fin (Fintype.card ((levDatumOf N' P' hsub' hne').I (dd - 1))) → Bool)
      (β : (levDatumOf N' P' hsub' hne').Idx dd →
        Fin (Fintype.card ((levDatumOf N' P' hsub' hne').I (dd - 1))) → ℤ),
      (∀ a ∈ (levDatumOf N' P' hsub' hne').parBox dd ⌊γ' * (Mw : ℝ)⌋.toNat,
          ∀ i : Fin (Fintype.card ((levDatumOf N' P' hsub' hne').I (dd - 1))),
          ∀ y ∈ Finset.Icc 1 Mw,
            |petDir (levDatumOf N' P' hsub' hne') dd lc a i * (y : ℤ) + β a i|
              ≤ (((2 ^ Nstep * Dsb : ℕ)) : ℤ) * (Nx : ℤ)) ∧
      petChainLevel B Nstep ≤ C₀ * linFamAvg (levDatumOf N' P' hsub' hne') dd lc Nx Mw
        ⌊γ' * (Mw : ℝ)⌋.toNat Ftop b β := by
  classical
  -- ## the numbers
  have hγ'0 : 0 < γ' := by
    have h1 : (1 : ℤ) ≤ ⌊γ' * (Mw : ℝ)⌋ := by
      by_contra hcon
      push Not at hcon
      have hz : ⌊γ' * (Mw : ℝ)⌋.toNat = 0 := Int.toNat_of_nonpos (by omega)
      omega
    have h2 : (1 : ℝ) ≤ γ' * (Mw : ℝ) := by
      have h2' : ((1 : ℤ) : ℝ) ≤ γ' * (Mw : ℝ) := Int.le_floor.mp h1
      simpa using h2'
    have h3 : (1 : ℝ) ≤ (Mw : ℝ) := by exact_mod_cast hM
    nlinarith
  have hBpos : 0 < B := by
    by_contra hcon
    push Not at hcon
    have hBz : B = 0 := le_antisymm hcon hB0
    have h0 := hwin 0 (by omega)
    rw [hBz, petChainLevel_zero] at h0
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div] at h0
    linarith
  have hγ'1 : γ' ≤ 1 := by
    have h0 := hwin 0 (by omega)
    have h1 : petChainLevel B 0 ^ 2 ≤ 1 := by
      rw [petChainLevel_zero]
      nlinarith [hB1, hBpos.le]
    have h2 : (1 : ℝ) ≤ 20000 * ((((2 : ℕ) ^ 0 * Dsb : ℕ) : ℝ) + 1) := by
      have h3 : (0 : ℝ) ≤ ((((2 : ℕ) ^ 0 * Dsb : ℕ) : ℝ)) := by positivity
      linarith
    calc γ' ≤ petChainLevel B 0 ^ 2 / (20000 * ((((2 : ℕ) ^ 0 * Dsb : ℕ) : ℝ) + 1)) := h0
      _ ≤ petChainLevel B 0 ^ 2 / 1 := div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h2
      _ ≤ 1 := by rw [div_one]; exact h1
  -- ## the analytic transfer along `Reach Y W`
  have hWn : n ≤ Lw := reach_length_le hWreach
  have hwinW : ∀ k < Lw - n, γ' ≤ petChainLevel B k ^ 2 /
      (20000 * ((((2 : ℕ) ^ k * Dsb : ℕ) : ℝ) + 1)) := by
    intro k hk
    exact hwin k (by omega)
  have hcW : (Lw - n) + 1 ≤ c := by omega
  obtain ⟨F'', g'', hF''b, hF''s, hg''b, hg''s, hlamW, hSBW, htopW⟩ :=
    reachAnalyticTop Y W hWreach Nx Mw c Dsb γ' B Ftop F g hNx (by omega) hγ'0 hγ'1 hH
      hBpos hB1 hcW hGb hGs hgb hgs hwinW hSB hlam htop
  -- ## the closing step
  have hSB'' : (histPet (W.step (Sum.inr 0) h₀ hh) ⌊γ' * (Mw : ℝ)⌋.toNat
      (levNextF W (Sum.inr 0) h₀ hh F'') (levNextg W (Sum.inr 0) h₀ hh
        ⌊γ' * (Mw : ℝ)⌋.toNat F'' g'')).toState.ShiftBound Nx Mw (c - Nstep)
          ((2 : ℕ) ^ Nstep * Dsb) := by
    have h1 := levStepAnalytic_sb_named W (Sum.inr 0) h₀ hh Nx Mw (c - (Lw - n))
      ((2 : ℕ) ^ (Lw - n) * Dsb) γ' F'' g'' hγ'0 hγ'1 (by omega) hSBW
    refine shiftBound_mono ?_ ?_ h1
    · omega
    · have h3 : 2 * (2 ^ (Lw - n) * Dsb) = 2 ^ Nstep * Dsb := by
        have h4 : Nstep = (Lw - n) + 1 := by omega
        rw [h4, pow_succ]
        ring
      exact le_of_eq h3
  have hlam' : petChainLevel B Nstep ≤
      (histPet (W.step (Sum.inr 0) h₀ hh) ⌊γ' * (Mw : ℝ)⌋.toNat
        (levNextF W (Sum.inr 0) h₀ hh F'') (levNextg W (Sum.inr 0) h₀ hh
          ⌊γ' * (Mw : ℝ)⌋.toNat F'' g'')).toState.lam Nx Mw := by
    have hwin0 : γ' ≤ (petChainLevel B (Lw - n)) ^ 2 /
        (20000 * ((((2 : ℕ) ^ (Lw - n) * Dsb : ℕ) : ℝ) + 1)) := hwin (Lw - n) (by omega)
    have h1 := levStepAnalytic_lam_named W (Sum.inr 0) h₀ hh Nx Mw (c - (Lw - n))
      ((2 : ℕ) ^ (Lw - n) * Dsb) γ' (petChainLevel B (Lw - n)) F'' g''
      hNx (by omega) hγ'0 hH (by omega) (petChainLevel_pos B hBpos _)
      (petChainLevel_le_one B hBpos hB1 _) hF''b hF''s hg''b hg''s hwin0 hSBW hlamW
    have h2 : petChainLevel (petChainLevel B (Lw - n)) 1 = petChainLevel B Nstep := by
      rw [petChainLevel_add, show (Lw - n) + 1 = Nstep from by omega]
    rwa [h2] at h1
  -- ## the forms of the terminal functions
  have htop' : ∀ i, (∀ x, levNextF W (Sum.inr 0) h₀ hh F'' i x = Ftop x) ∨
      (∀ x, levNextF W (Sum.inr 0) h₀ hh F'' i x = star (Ftop x)) :=
    levNextF_form W (Sum.inr 0) h₀ hh F'' htopW
  have hg' : ∃ c₀ : Bool, ∀ a x,
      levNextg W (Sum.inr 0) h₀ hh ⌊γ' * (Mw : ℝ)⌋.toNat F'' g'' a x =
        (if c₀ then star (Ftop x) else Ftop x) := by
    rcases htopW ⟨((Sum.inr 0 : InitIdx dd), h₀), hh⟩ with hc₀ | hc₀
    · refine ⟨false, fun a x => ?_⟩
      rw [levNextg_eq_ref W (Sum.inr 0) h₀ hh F'' g'' hJ a x]
      simpa using hc₀ x
    · refine ⟨true, fun a x => ?_⟩
      rw [levNextg_eq_ref W (Sum.inr 0) h₀ hh F'' g'' hJ a x]
      simpa using hc₀ x
  -- ## the terminal comparison
  have htower := levTowerIdxProps hDinv hsub' hne' ⌊γ' * (Mw : ℝ)⌋.toNat
  have hcard : ((levDatumOf N' P' hsub' hne').parBox dd ⌊γ' * (Mw : ℝ)⌋.toNat).card
      ≤ (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) ^ (Lw + 1 + 1) := by
    have h1 : (levDatumOf N' P' hsub' hne').parBox dd ⌊γ' * (Mw : ℝ)⌋.toNat
        ⊆ (Finset.univ : Finset (Fin (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) ×
            WinTower ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1))).image
          (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat) := by
      intro a ha
      obtain ⟨p, hp⟩ := htower.2.1 a ha
      exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩
    calc ((levDatumOf N' P' hsub' hne').parBox dd ⌊γ' * (Mw : ℝ)⌋.toNat).card
        ≤ ((Finset.univ : Finset (Fin (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) ×
            WinTower ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1))).image
              (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat)).card := Finset.card_le_card h1
      _ ≤ (Finset.univ : Finset (Fin (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) ×
            WinTower ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1))).card := Finset.card_image_le
      _ = (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) * Fintype.card (WinTower ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1)) := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      _ = (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) * (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) ^ (Lw + 1) := by
          rw [card_WinTower]
      _ = (2 * ⌊γ' * (Mw : ℝ)⌋.toNat + 1) ^ (Lw + 1 + 1) := by rw [pow_succ]; ring
  obtain ⟨islot, hislot⟩ := levSlotEquivExists hDinv hsub' hne' hcube' hAlvl
  -- the constant term `β`
  let β : (levDatumOf N' P' hsub' hne').Idx dd → ((W.step (Sum.inr 0) h₀ hh).toSym).S.ι → ℤ :=
    fun a i => MvPolynomial.eval
      (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1)
        (levTowerOf hDinv ⌊γ' * (Mw : ℝ)⌋.toNat a))
      (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 0)
  have hβ0 : ∀ a a' : (levDatumOf N' P' hsub' hne').Idx dd,
      (∀ (j : Fin dd), j ≠ ⟨0, by omega⟩ → a j = a' j) →
      ∀ i : ((W.step (Sum.inr 0) h₀ hh).toSym).S.ι, β a i = β a' i := by
    intro a a' haa i
    have ht : levTowerOf hDinv ⌊γ' * (Mw : ℝ)⌋.toNat a
        = levTowerOf hDinv ⌊γ' * (Mw : ℝ)⌋.toNat a' := by
      show towerOf ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) _ = _
      congr 1
      funext k
      refine congrFun (haa ⟨coordLvl hDinv k, _⟩ ?_) _
      intro hc
      have h1 := coordLvl_one_le hDinv k
      have h2 : coordLvl hDinv k = 0 := congrArg Fin.val hc
      omega
    show MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1)
        (levTowerOf hDinv ⌊γ' * (Mw : ℝ)⌋.toNat a))
        (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 0)
      = MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1)
        (levTowerOf hDinv ⌊γ' * (Mw : ℝ)⌋.toNat a'))
        (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 0)
    rw [ht]
  -- the identification of the slot polynomials with the datum's directions
  have heval : ∀ (i : ((W.step (Sum.inr 0) h₀ hh).toSym).S.ι)
      (t : WinTower ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1)) (y : ℤ),
      ((Polynomial.map (MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t))
          (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2))).eval y)
        = petDir (levDatumOf N' P' hsub' hne') dd lc
            (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)) (islot i) * y
          + β (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)) i := by
    intro i t y
    have hmemH : i.1 ∈ (W.step (Sum.inr 0) h₀ hh).H := i.2
    have hmemL : i.1 ∈ LevH dd (Lw + 1) A' f₀' := by
      rw [← hcube'.1]; exact hmemH
    obtain ⟨hi1, hicube, hine⟩ := mem_LevH.mp hmemL
    have hdeg : (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2)).natDegree = 1 := by
      rw [hi1]
      exact (hcube'.2 i.1.2 hicube hine).1
    have hp : ((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2)
        = Polynomial.C (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 1) * Polynomial.X
          + Polynomial.C (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
    rw [hp]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hconst : β (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)) i
        = MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t)
            (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 0) := by
      show MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1)
          (levTowerOf hDinv ⌊γ' * (Mw : ℝ)⌋.toNat
            (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)))) _ = _
      rw [levTowerOf_towerIdx]
    have hlin : MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t)
        (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 1)
        = petDir (levDatumOf N' P' hsub' hne') dd lc
            (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)) (islot i) := by
      have hw : ((Fintype.equivFin ((levDatumOf N' P' hsub' hne').I (dd - 1))).symm (islot i)).val.map
          ⟨fun s : (levDatumOf N' P' hsub' hne').S (dd - 1) => s.1,
            fun a b hab => Fin.ext hab⟩ = idxSet N' c' (Lw + 1) (dd - 1) hLw1 i.1.2 := by
        rw [Finset.map_eq_image]
        exact hislot i
      have hdir := levCoeffOneEval (dd := dd) (L := Lw + 1) (H := ⌊γ' * (Mw : ℝ)⌋.toNat)
        hDinv hsub' hne' hcube' hAlvl i
        ((Fintype.equivFin ((levDatumOf N' P' hsub' hne').I (dd - 1))).symm (islot i)) hw t
      -- the evaluation of `φ` is the one at the tower point
      have hφ : (fun k : Fin (Lw + 1) =>
            (fun k : ℕ => if h : k < Lw + 1 then
              WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t ⟨k, h⟩ else 0) (k : ℕ))
          = WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t := by
        funext k
        simp only [dif_pos k.2]
      have h1 : MvPolynomial.eval (WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t)
            (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 1)
          = MvPolynomial.eval (fun k : ℕ => if h : k < Lw + 1 then
              WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t ⟨k, h⟩ else 0)
            (MvPolynomial.rename Fin.val (((W.step (Sum.inr 0) h₀ hh).Q i.1.1 i.1.2).coeff 1)) := by
        rw [MvPolynomial.eval_rename]
        rw [show ((fun k : ℕ => if h : k < Lw + 1 then
            WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t ⟨k, h⟩ else 0) ∘ Fin.val)
            = WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t from hφ]
      rw [h1, hdir]
      -- the parameter families agree at the levels `1,…,dd-1` (`dir` never reads level `0`)
      have hdir2 := IdxDatum.dir_congr (D := levDatumOf N' P' hsub' hne') dd lc (dd - 1)
        ((Fintype.equivFin ((levDatumOf N' P' hsub' hne').I (dd - 1))).symm (islot i))
        (fun j s => (fun k : ℕ => if h : k < Lw + 1 then
            WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t ⟨k, h⟩ else 0) (c' j s.1))
        ((levDatumOf N' P' hsub' hne').pad dd
          (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)))
        (by
          intro j hj1 hj2 s
          have hj0 : j ≠ 0 := by omega
          have hcb : c' j s.1 < Lw + 1 := hDinv.cbound j hj1 hj2 s.1 s.2
          have hlt : j < dd := by omega
          show (if h : c' j s.1 < Lw + 1 then
              WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t ⟨c' j s.1, h⟩ else 0)
            = (levDatumOf N' P' hsub' hne').pad dd
                (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t)) j s
          rw [dif_pos hcb, IdxDatum.pad, dif_pos hlt]
          show WinTower.param ⌊γ' * (Mw : ℝ)⌋.toNat (Lw + 1) t ⟨c' j s.1, hcb⟩
            = levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat (0, t) ⟨j, hlt⟩ s
          simp only [levTowerIdx, dif_neg hj0])
      rw [hdir2]
      rfl
    rw [hconst, hlin]
  -- ## the comparison
  obtain ⟨b, hshift, havg⟩ :=
    levelCompareGen (dd := dd) (L := Lw + 1) (by omega) ⌊γ' * (Mw : ℝ)⌋.toNat
      (levDatumOf N' P' hsub' hne') lc A' f₀' atoms' (W.step (Sum.inr 0) h₀ hh) hcube'
      (levTowerIdx hDinv ⌊γ' * (Mw : ℝ)⌋.toNat)
      (fun p => levTowerIdx_zero hDinv ⌊γ' * (Mw : ℝ)⌋.toNat p (by omega))
      (fun k k' t j hj => levTowerIdx_indep hDinv ⌊γ' * (Mw : ℝ)⌋.toNat k k' t
        (fun hc => hj (Fin.ext hc)))
      htower.1 htower.2.1 htower.2.2 hcard Nx Mw Ftop
      (levNextF W (Sum.inr 0) h₀ hh F'') (levNextg W (Sum.inr 0) h₀ hh
        ⌊γ' * (Mw : ℝ)⌋.toNat F'' g'') htop' hg' islot β hβ0 heval hSB'' (by omega)
      hlam'
  refine ⟨b, fun a i => β a (islot.symm i), ?_, ?_⟩
  · intro a ha i y hy
    exact hshift a ha i y hy
  · exact le_trans havg (mul_le_mul_of_nonneg_right hC0
      (linFamAvg_nonneg (levDatumOf N' P' hsub' hne') dd lc Nx Mw
        ⌊γ' * (Mw : ℝ)⌋.toNat Ftop b (fun a i => β a (islot.symm i))))

end

end Work.Peluse.UControl

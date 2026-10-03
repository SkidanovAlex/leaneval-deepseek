import Mathlib
import Submission.Work.Peluse.UControl.petLevelFinal

/-!
# The level chain of the PET chapter (`PetLevelChain` for `2 ≤ P.natDegree`)

**This file is complete** (sorry-free): `petLevelChainGen` is the level chain of
`Work.Peluse.UControl.petChapter5Holds`, proved from the auxiliary modules
`petLevelAux.lean`, `petLevelFinal.lean` and `petLevelChain_quadratic.lean`.

## The assembly

* `d = P.natDegree = 2`: `petLevelChain_quadratic`.
* `d ≥ 3`: from a `Phase1Terminal` state `Y`,
  * `levDInv_init` + `phase1Terminal_levCube` + `phase1Terminal_levIndep` present `Y` as the level-`1`
    state of the level chain (the atoms are transported from `Finset.univ` to
    `lvlSet (initN n) (initC n) n 1 hL1`, which is `univ` by `lvlSet_init`);
  * `levDatumIterateMid (d-3)` iterates the round (Peluse's Lemma 4.8) to level `d-2`;
  * `levRoundExposed` applies the *last* round with its closing step **exposed**: it returns the
    pre-closing state `W` (one class, all slots of degree `2`), the `Reach`-chain to it, and the
    terminal data `X' = W.step (Sum.inr 0) h₀ hh`, `f₀'`, `atoms'`;
  * `levDInvStep` + `lvlSet_step` give the terminal `LevDInv`-state at level `d-1`, hence the datum
    `D = levDatumOf N' P' hsub hne`, its index cardinality (`card_I`, `lvlSet_card_le`) and the
    tower data of `levelChainFinal`;
  * `levelChainFinal` runs the terminal analysis: the analytic data is transported along
    `Reach Y W` (`reachAnalyticTop`, which also keeps the `Ftop`-form of the slot functions), the
    closing step is applied explicitly (`levStepAnalytic_{lam,sb}_named`), and the base function of
    the terminal state is a *single* slot function because the closing step has **no** `y`-constant
    children (`petStepConstsClosing`); the terminal comparison `levelCompareGen` then produces the
    output `b`, `β`.

The two points that made the terminal analysis delicate are recorded in
`NOTES_petLevelChain_session20.md` §2-§3: the `Reach`-closure does not expose the last step's
`petStepConsts`, and the terminal comparison needs the base function in the `Ftop`-form.  Both are
handled by exposing the closing step at the level of the *round* (`levRoundExposed`), which is the
one place where the round's internal invariant (`LevInv`) is available.

-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The level chain** (Peluse's Lemma 4.8 iterated `d-2` times) for `2 ≤ P.natDegree`:
the phase-1 terminal state is the level-`1` state, the round is iterated to level `d-2`, the last
round is applied with its closing step exposed, and the analytic data is transported along the
`Reach`-chain to the pre-closing state; the closing step then produces the terminal functions, whose
`Ftop`-form (slots and base) is what the terminal comparison consumes. -/
theorem petLevelChainGen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) : PetLevelChain P := by
  classical
  by_cases h2 : P.natDegree = 2
  · exact petLevelChain_quadratic P h2
  have hd3 : 3 ≤ P.natDegree := by omega
  intro n hn lc Y hT
  -- ################ 1. the level-1 state ################
  have hL1 : 1 ≤ n := by omega
  have hLinit : lvlSet (initN n) (initC n) n 1 hL1 = Finset.univ := lvlSet_init n hL1
  have h1inv : LevDInv P.natDegree lc 1 n hL1 (initN n) (initP n) (initC n) Y 0 :=
    levDInv_init (d := P.natDegree) hL1 hT
  have hcube0 : LevCube P.natDegree (P.natDegree - 1) n (Finset.univ : Finset (Fin n)) 0
      (levInitAtoms P.natDegree n lc) Y := phase1Terminal_levCube (d := P.natDegree) (lc := lc) hT
  have hlcne : lc ≠ 0 := by
    intro hlc0
    have hne : ∃ h : Fin n → Bool, h ≠ 0 := by
      refine ⟨fun i => decide (i = (⟨0, by omega⟩ : Fin n)), ?_⟩
      intro hcon
      have h1 := congrFun hcon (⟨0, by omega⟩ : Fin n)
      simp at h1
    obtain ⟨h, hh⟩ := hne
    obtain ⟨-, -, hdeg, hlc_eq⟩ := hT.1 _ (hT.2 h hh)
    have hpoly : Y.Q (Sum.inr 0) h ≠ 0 := by
      intro h0
      rw [h0] at hdeg
      simp at hdeg
      omega
    have hlcY : (Y.Q (Sum.inr 0) h).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpoly
    rw [hlc_eq, hlc0, MvPolynomial.C_0, mul_zero, zero_mul] at hlcY
    exact hlcY rfl
  have hlc0 : MvPolynomial.C ((P.natDegree : ℤ) * lc) ≠ (0 : MvPolynomial (Fin n) ℤ) :=
    MvPolynomial.C_ne_zero.mpr
      (mul_ne_zero (by exact_mod_cast (by omega : P.natDegree ≠ 0)) hlcne)
  have hind0 : LevIndep n (Finset.univ : Finset (Fin n)) (levInitAtoms P.natDegree n lc) :=
    phase1Terminal_levIndep (d := P.natDegree) (n := n) (lc := lc) hlc0
  have hatomsum : ∀ h : Fin n → Bool,
      atomSum (lvlSet (initN n) (initC n) n 1 hL1)
          (fun s => levInitAtoms P.natDegree n lc ⟨s.1, Finset.mem_univ s.1⟩) h
        = atomSum (Finset.univ : Finset (Fin n)) (levInitAtoms P.natDegree n lc) h := by
    intro h
    rw [atomSum, atomSum]
    refine Fintype.sum_equiv
      (Equiv.subtypeEquivRight (fun x => by simp only [hLinit, Finset.mem_univ]))
      (fun s => if h s.1 then levInitAtoms P.natDegree n lc ⟨s.1, Finset.mem_univ s.1⟩ else 0)
      (fun s => if h s.1 then levInitAtoms P.natDegree n lc s else 0) ?_
    intro s
    rfl
  have hcube₁ : LevCube P.natDegree (P.natDegree - 1) n (lvlSet (initN n) (initC n) n 1 hL1) 0
      (fun s => levInitAtoms P.natDegree n lc ⟨s.1, Finset.mem_univ s.1⟩) Y := by
    refine ⟨?_, ?_⟩
    · rw [hLinit]
      exact hcube0.1
    · intro h hh hne
      obtain ⟨hdeg, hlc⟩ := hcube0.2 h (by rw [← hLinit]; exact hh) hne
      exact ⟨hdeg, by rw [hlc, hatomsum h]⟩
  have hind₁ : LevIndep n (lvlSet (initN n) (initC n) n 1 hL1)
      (fun s => levInitAtoms P.natDegree n lc ⟨s.1, Finset.mem_univ s.1⟩) := by
    intro h h' hh hh' hsum
    refine hind0 h h' (by rw [← hLinit]; exact hh) (by rw [← hLinit]; exact hh') ?_
    rw [← hatomsum h, ← hatomsum h']
    exact hsum
  have hc2 : 2 ≤ (lvlSet (initN n) (initC n) n 1 hL1).card := by
    rw [hLinit]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  -- ################ 2. the iteration to level `d - 2` ################
  obtain ⟨L₂, hL₂, N₂, P₂, c₂, X₂, f₂, atoms₂, h2inv, h2cube, h2ind, h2card, h2reach⟩ :=
    levDatumIterateMid (d := P.natDegree) (lc := lc) hd (P.natDegree - 3)
      1 n hL1 (initN n) (initP n) (initC n) Y 0
      (fun s => levInitAtoms P.natDegree n lc ⟨s.1, Finset.mem_univ s.1⟩)
      (by omega) hc2 h1inv hcube₁ hind₁
  -- ################ 3. the last round, with its closing step exposed ################
  obtain ⟨M, σ, W, hh, hWinv, hWalldeg, h3M, hreachW, hPne, hf0false, hatoms, hind', hcube'⟩ :=
    levRoundExposed P.natDegree 2 L₂ (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂ atoms₂ h2ind
      (le_refl 2) h2card X₂ h2cube
  -- ################ 4. the terminal datum ################
  have hLw : 1 ≤ L₂ + M := by omega
  have hLw1 : 1 ≤ L₂ + M + 1 := by omega
  have hcube'' : LevCube P.natDegree (P.natDegree - (P.natDegree - 2) - 1) (L₂ + M + 1)
      (freshFin L₂ (M + 1)) (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) (M + 1) 0)
      (closingAtoms (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) atoms₂ 2 M σ)
      (W.step (Sum.inr 0) (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) M 0) hh) := by
    have he : P.natDegree - (P.natDegree - 2) - 1 = 1 := by omega
    rw [he]
    exact hcube'
  have hDinv0 : LevDInv P.natDegree lc ((P.natDegree - 2) + 1) (L₂ + M + 1) hLw1
      (stepN N₂ (M + 1) (P.natDegree - 2))
      (stepPAll h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
        (freshSet (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) σ))
      (stepC c₂ L₂ (P.natDegree - 2))
      (W.step (Sum.inr 0) (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) M 0) hh)
      (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) (M + 1) 0) :=
    levDInvStep hL₂ hLw1 h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
      (fun s hs => hf0false ⟨s, hs⟩)
      (atoms := atoms₂)
      (by rw [show P.natDegree - (P.natDegree - 2) = 2 from by omega]; exact h2cube)
      hPne
      (by
        rw [show (P.natDegree : ℤ) - ((P.natDegree - 2 : ℕ) : ℤ) = 2 from by omega]
        exact hatoms)
      hcube''
  have hlvl : (P.natDegree - 2) + 1 = P.natDegree - 1 := by omega
  have hDinv : LevDInv P.natDegree lc (P.natDegree - 1) (L₂ + M + 1) hLw1
      (stepN N₂ (M + 1) (P.natDegree - 2))
      (stepPAll h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
        (freshSet (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) σ))
      (stepC c₂ L₂ (P.natDegree - 2))
      (W.step (Sum.inr 0) (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) M 0) hh)
      (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) (M + 1) 0) := by
    convert hDinv0 using 1
    omega
  have hlvlset : lvlSet (stepN N₂ (M + 1) (P.natDegree - 2)) (stepC c₂ L₂ (P.natDegree - 2))
        (L₂ + M + 1) (P.natDegree - 1) hLw1 = freshFin L₂ (M + 1) := by
    have h := lvlSet_step (N := N₂) (c := c₂) (j := P.natDegree - 2)
      (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1)) hLw1
    rw [← hlvl]
    exact h
  have hcardlvl : 2 ≤ (lvlSet (stepN N₂ (M + 1) (P.natDegree - 2))
      (stepC c₂ L₂ (P.natDegree - 2)) (L₂ + M + 1) (P.natDegree - 1) hLw1).card := by
    rw [hlvlset, card_freshFin]
    omega
  have hDcard : 2 ≤ Fintype.card ((levDatumOf (stepN N₂ (M + 1) (P.natDegree - 2))
      (stepPAll h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
        (freshSet (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) σ))
      (levDInv_sub hDinv) (levDInv_ne hDinv)).I (P.natDegree - 1)) := by
    have h3 : 2 ≤ (stepN N₂ (M + 1) (P.natDegree - 2)) (P.natDegree - 1) := by
      have h4 := lvlSet_card_le (d := P.natDegree) (N := stepN N₂ (M + 1) (P.natDegree - 2))
        (c := stepC c₂ L₂ (P.natDegree - 2)) (L := L₂ + M + 1) (j := P.natDegree - 1) hLw1
      rw [hlvlset, card_freshFin] at h4
      omega
    have h5 : 4 ≤ 2 ^ (stepN N₂ (M + 1) (P.natDegree - 2)) (P.natDegree - 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (stepN N₂ (M + 1) (P.natDegree - 2)) (P.natDegree - 1) :=
            Nat.pow_le_pow_right (by norm_num) h3
    rw [card_I]
    have h7 : Fintype.card ((levDatumOf (stepN N₂ (M + 1) (P.natDegree - 2))
        (stepPAll h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
          (freshSet (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) σ))
        (levDInv_sub hDinv) (levDInv_ne hDinv)).S (P.natDegree - 1))
        = (stepN N₂ (M + 1) (P.natDegree - 2)) (P.natDegree - 1) :=
      Fintype.card_fin _
    rw [h7]
    omega
  -- ################ 5. the level chain data ################
  have hL₂n : n ≤ L₂ := reach_length_le h2reach
  refine ⟨max 1 (L₂ + M + 1 - n),
    levDatumOf (stepN N₂ (M + 1) (P.natDegree - 2))
      (stepPAll h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
        (freshSet (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) σ))
      (levDInv_sub hDinv) (levDInv_ne hDinv),
    (3 : ℝ) ^ (L₂ + M + 1), by omega, ?_, hDcard, ?_⟩
  · exact one_le_pow₀ (by norm_num)
  · -- ################ 6. the analytic data and the terminal analysis ################
    intro Nx Mw γ' Ftop G g c Dsb B hNx hGb hGs hgb hgs hM hH hcNstep hB0 hB1
      hwin hSB htop hg hlam
    refine levelChainFinal (dd := P.natDegree) hd3 (n := n) Y lc (L₂ + M) hLw hLw1
      (stepN N₂ (M + 1) (P.natDegree - 2))
      (stepPAll h2inv (rfl : freshFin L₂ (M + 1) = freshFin L₂ (M + 1))
        (freshSet (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) σ))
      (stepC c₂ L₂ (P.natDegree - 2))
      (levDInv_sub hDinv) (levDInv_ne hDinv)
      W (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) M 0) hh
      (slotHist (histOf (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) f₂
        (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂)) (M + 1) 0)
      (freshFin L₂ (M + 1))
      (closingAtoms (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) atoms₂ 2 M σ)
      hDinv hcube' hlvlset.symm
      (petStepConstsClosing hWinv h2ind (le_refl 2) hWalldeg
        (rfl : ({lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂} : Finset (Finset (Fin L₂)))
          = {lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂})
        ((hWinv.top_mem (lvlSet N₂ c₂ L₂ (P.natDegree - 2) hL₂) hWinv.memA
          (0 : Fin M → Bool)).1))
      (Reach.trans h2reach hreachW) (max 1 (L₂ + M + 1 - n)) (by omega)
      ((3 : ℝ) ^ (L₂ + M + 1)) (le_refl _) (by omega) hDcard
      Nx Mw γ' Ftop G g c Dsb B hNx hGb hGs hgb hgs hM hH hcNstep hB0 hB1
      hwin hSB htop hg hlam

end

end Work.Peluse.UControl

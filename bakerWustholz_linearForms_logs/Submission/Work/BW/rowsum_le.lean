import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.sysRow_height_bound
import Submission.Work.BW.card_auxIdx
import Submission.Work.BW.card_eqnS
import Submission.Work.BW.card_multIdx
import Submission.Work.BW.sum_eqnIdx_abs
import Submission.Work.BW.Mu_ge_Me

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- `#(AuxEqnIdx r S T) = (2S+1)·#(MultIdx r T)`. -/
theorem card_eqnIdx (r S T : ℕ) :
    Fintype.card (AuxEqnIdx r S T) = (2 * S + 1) * Fintype.card (MultIdx r T) := by
  simp only [AuxEqnIdx, Fintype.card_prod]
  rw [card_eqnS]

/-- The sum of `|s|` over the equation index set, as a real number. -/
theorem sum_abs_eqnIdx (r S T : ℕ) :
    ∑ e : AuxEqnIdx r S T, (((|(e.1 : ℤ)| : ℤ)) : ℝ)
      = (Fintype.card (MultIdx r T) : ℝ) * ((S : ℝ) * ((S : ℝ) + 1)) := by
  have hc := congrArg (fun z : ℤ => (z : ℝ)) (sum_eqnIdx_abs r S T)
  push_cast at hc
  rw [← hc]
  exact Finset.sum_congr rfl (fun e _ => by simp only [Int.cast_abs])

/-- Final real arithmetic of `rowsum_le`. -/
private theorem rowsum_arith {dK dF dN MUp ME rho l X Y Sig2 : ℝ}
    (hK : 0 ≤ dK) (hd : dN = dK * dF) (hden : 0 < MUp - ME)
    (hrho : rho = ME / (MUp - ME))
    (hSig2 : Sig2 ≤ dF * (ME * (X + Y))) :
    dK * (1 / (MUp - ME) * (ME * (1 / 2 * dF * l) + Sig2))
      ≤ 1 / 2 * dN * rho * l + dN * rho * (X + Y) := by
  subst hd
  rw [hrho]
  have hpos : 0 ≤ 1 / (MUp - ME) := le_of_lt (div_pos one_pos hden)
  have h1 : dK * (1 / (MUp - ME) * (ME * (1 / 2 * dF * l) + Sig2))
      ≤ dK * (1 / (MUp - ME) * (ME * (1 / 2 * dF * l) + dF * (ME * (X + Y)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) hpos) hK
  refine le_trans h1 (le_of_eq ?_)
  ring_nf

theorem rowsum_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (ι : Fin (r - 1) → Fin n) :
    let d : ℕ := Module.finrank ℚ K
    let h : ℕ := ph (hL b d) v
    let D : ℝ := pD r d σ
    let S : ℕ := pS r d h
    let Mu : ℕ := Fintype.card (AuxIdx r h (pD0 r d σ) (pDj r d σ))
    let Me : ℕ := Fintype.card (AuxEqnIdx r S (pT r d σ))
    let rho : ℝ := (Me : ℝ) / ((Mu : ℝ) - Me)
    (Module.finrank ↥(auxField α') K : ℝ) * ((1 / ((Mu : ℝ) - Me)) *
        ∑ e : AuxEqnIdx r S (pT r d σ),
          ((1 / 2) * (Module.finrank ℚ ↥(auxField α') : ℝ) * Real.log (Mu : ℝ)
            + Height.logHeight (fun lm => sysRow b k L ι α' h (pD0 r d σ) (pDj r d σ) e lm)))
      ≤ (1 / 2) * (d : ℝ) * rho * Real.log (Mu : ℝ)
        + (d : ℝ) * rho * (1.7 * (h : ℝ) * (11.75 * r * D)
            + (D / d) * ((S : ℝ) * (S + 1) / (2 * (S : ℝ) + 1))) := by
  dsimp only
  -- Abbreviations for the scalar quantities.
  set dNR : ℝ := (Module.finrank ℚ K : ℝ) with hdNR
  set dF : ℝ := (Module.finrank ℚ (auxField α') : ℝ) with hdF
  set dK : ℝ := (Module.finrank (auxField α') K : ℝ) with hdK
  set hN : ℕ := ph (hL b (Module.finrank ℚ K)) v with hhN
  set D : ℝ := pD r (Module.finrank ℚ K) σ with hD
  set D0 : ℕ := pD0 r (Module.finrank ℚ K) σ with hD0
  set Dj : Fin r → ℕ := pDj r (Module.finrank ℚ K) σ with hDj
  set S0 : ℕ := pS r (Module.finrank ℚ K) hN with hS0
  set T : ℕ := pT r (Module.finrank ℚ K) σ with hT
  set Mu : ℕ := Fintype.card (AuxIdx r hN D0 Dj) with hMu
  set Me : ℕ := Fintype.card (AuxEqnIdx r S0 T) with hMe
  set l : ℝ := Real.log (Mu : ℝ) with hl
  set rho : ℝ := (Me : ℝ) / ((Mu : ℝ) - Me) with hrho
  set X : ℝ := 1.7 * (hN : ℝ) * (11.75 * (r : ℝ) * D) with hX
  set Y : ℝ := D / dNR * ((S0 : ℝ) * ((S0 : ℝ) + 1) / (2 * (S0 : ℝ) + 1)) with hY
  -- Positivity of the degree of `K` over `F = auxField α'`.
  have hdKpos : 0 < dK := by
    rw [hdK]
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank (auxField α') K)
  -- The degree identity `[K:ℚ] = [K:F]·[F:ℚ]`.
  have hd : dNR = dK * dF := by
    have h := Module.finrank_mul_finrank ℚ (auxField α') K
    rw [hdNR, hdK, hdF, ← h]
    push_cast
    ring
  -- Every row of the §13 system has bounded height.
  have hrow : ∀ e : AuxEqnIdx r S0 T,
      Height.logHeight (fun lm => sysRow b k L ι α' hN D0 Dj e lm)
        ≤ dF * (X + (((|(e.1 : ℤ)| : ℤ)) : ℝ) * D / dNR) := by
    intro e
    have h := sysRow_height_bound φ α b k c hst hr v L α' σ hBH ι e
    simpa only [hdF, hX, hD, hdNR, hhN, hD0, hDj] using h
  -- `Me < Mu`, hence the Siegel denominator is positive.
  have hMuMeR : 0 < (Mu : ℝ) - (Me : ℝ) := by
    have h19 : 19 ≤ hN := by rw [hhN]; exact ph_ge_nineteen φ α b k c v hst
    have hσ1 : ∀ j, (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ σ j := by
      intro j
      exact le_trans (one_div_finrank_le_hmod (α' j) (lamP φ α v L j))
        (hBH.2.2.2.2.2.1 j)
    have hlt : Me < Mu := by
      have h := (Mu_ge_Me (K := K) r hN hr h19 σ hσ1).2
      have h2 : Fintype.card (AuxEqnIdx r S0 T) < hN * (D0 + 1) * ∏ j, (Dj j + 1) := by
        simpa only [hS0, hT, hD0, hDj] using h
      rw [hMe, hMu, card_auxIdx]
      exact h2
    have hcast : ((Mu - Me : ℕ) : ℝ) = (Mu : ℝ) - (Me : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    rw [← hcast]
    exact_mod_cast (Nat.sub_pos_of_lt hlt)
  -- Abbreviate the sum of the row heights.
  obtain ⟨Sig2, hSig2def⟩ : ∃ z : ℝ, z = ∑ e : AuxEqnIdx r S0 T,
      Height.logHeight (fun lm => sysRow b k L ι α' hN D0 Dj e lm) := ⟨_, rfl⟩
  -- The sum of the row heights is bounded by `dF·(Me·(X+Y))`.
  have hsum1 : Sig2 ≤ ∑ e : AuxEqnIdx r S0 T,
      dF * (X + (((|(e.1 : ℤ)| : ℤ)) : ℝ) * D / dNR) := by
    rw [hSig2def]
    exact Finset.sum_le_sum (fun e _ => hrow e)
  have hSig2 : Sig2 ≤ dF * (Me * (X + Y)) := by
    refine le_trans hsum1 (le_of_eq ?_)
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hMe]
    have hMeQ : (Me : ℝ) * ((S0 : ℝ) * ((S0 : ℝ) + 1) / (2 * (S0 : ℝ) + 1))
        = (Fintype.card (MultIdx r T) : ℝ) * ((S0 : ℝ) * ((S0 : ℝ) + 1)) := by
      have hS : (2 * (S0 : ℝ) + 1) ≠ 0 := by positivity
      rw [hMe, card_eqnIdx r S0 T]
      push_cast
      field_simp
    have hsumg : ∑ e : AuxEqnIdx r S0 T, (((|(e.1 : ℤ)| : ℤ)) : ℝ) * D / dNR
        = (Me : ℝ) * Y := by
      have h1 : ∑ e : AuxEqnIdx r S0 T, (((|(e.1 : ℤ)| : ℤ)) : ℝ) * D / dNR
          = ∑ e : AuxEqnIdx r S0 T, (((|(e.1 : ℤ)| : ℤ)) : ℝ) * (D / dNR) :=
        Finset.sum_congr rfl (fun e _ => mul_div_assoc _ _ _)
      have h2 : ∑ e : AuxEqnIdx r S0 T, (((|(e.1 : ℤ)| : ℤ)) : ℝ) * (D / dNR)
          = (∑ e : AuxEqnIdx r S0 T, (((|(e.1 : ℤ)| : ℤ)) : ℝ)) * (D / dNR) := by
        rw [Finset.sum_mul]
      rw [h1, h2, sum_abs_eqnIdx, ← hMeQ, hY]
      ring
    rw [hsumg]
    ring
  -- Split the sum in the goal.
  have hsplit : ∑ e : AuxEqnIdx r S0 T,
        (1 / 2 * dF * l + Height.logHeight (fun lm => sysRow b k L ι α' hN D0 Dj e lm))
      = (Me : ℝ) * (1 / 2 * dF * l) + Sig2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← hMe, ← hSig2def]
  have key : dK * (1 / ((Mu : ℝ) - Me) * ((Me : ℝ) * (1 / 2 * dF * l) + Sig2))
      ≤ 1 / 2 * dNR * rho * l + dNR * rho * (X + Y) :=
    rowsum_arith (le_of_lt hdKpos) hd hMuMeR hrho hSig2
  rw [hsplit]
  exact key

end Work.BW

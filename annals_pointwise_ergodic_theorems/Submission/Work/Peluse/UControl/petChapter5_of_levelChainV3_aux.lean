import Mathlib
import Submission.Work.Peluse.UControl.petHistInit_hw
import Submission.Work.Peluse.UControl.petChapter5_quadratic
import Submission.Work.Peluse.UControl.petLevelChain_quadratic
import Submission.Work.Peluse.UControl.terminalShiftBoundL
import Submission.Work.Peluse.UControl.card_I

/-!
# `PetChapter5` from the `V3` level chain

The assembly of the PET chapter `PetChapter5` from the current (2026-09-29 23:15) statement of
`PetLevelChain` (`PetLevelChainDefs.lean`): `Nstep ≥ 1` is *produced* by the chain, its window
condition `hwin` is indexed by `Nstep`, and the shift clause of its conclusion carries the constant
`2 ^ Nstep * Dsb` (no `Cpet` term).

The proof runs the phase-1 chain (`petHistInit_inv`, `histPhase1RunInv`, `histPhase1Inv`) plus the
closing step (`histCloseLinkWin`) to the terminal state, applies the level chain there, and then does
the box-average comparison (`linFamAvg_radius_le`, `linFamAvg_clip_le`) and the window arithmetic
(`petWindowBookkeeping`), with the corner `petCornerZero` in the regime where the chain's window is
empty.

The chain is run at the level `B := petChainLevel γ (petTermLen P hd + 1)` (the terminal level of
the phase-1 chain, which is exactly what `histCloseLinkWin` produces), at the window

  `γ' := min (petWindow γ Dw (petTermLen P hd + 1 + Nstep)) δ'`,

where `Dw := max D₀ Dsb` is the maximum of the coarse shift constant `D₀` of the phase-1 chain and
the sharp constant `Dsb := Cs * (Nstep+1)^d * ⌈A⌉₊` supplied by `hSBsharp` for the terminal state.
`petWindow γ Dw nwin` satisfies the chain's window condition `hwin` (its defining value is the
`k = Nstep - 1` instance and the quotients `petChainLevel B k^2 / (20000 (2^k Dsb + 1))` decrease in
`k`), and `petWindow` is antitone in both the index and the shift constant, so `γ' ≤ petWindow γ D₀
(petTermLen P hd + 1)` is the window hypothesis of `histCloseLinkWin`.  Since
`petWindow ≥ δ'/Cpw` (`petWindow_ratio_le`) and `γ' = min (petWindow) δ'`, the two boxes
`parBox ⌊γ'M⌋ ≤ parBox ⌊δ'M⌋` have comparable cardinality, which is what makes the transfer of
`linFamAvg` lossless up to the constant `Cpw`.

The only two inputs are the hypotheses of the statement: the sharp shift bound of the terminal state
(`hSBsharp`, a generalisation of session 16's `terminalShiftBound_of_coeffBd` to an arbitrary range
`c`), and the shell bound of the datum's directions (`hShell`, the hypothesis
`petDir_abs_leH`/`IdxDatum.dir_abs_leH` prove unconditionally).
-/

set_option maxHeartbeats 16000000

namespace Work.Peluse.UControl

noncomputable section

open scoped BigOperators
open Polynomial
/-- `petChainLevel` composes: `n` steps from `a` steps is `a + n` steps. -/
lemma petChainLevel_add (γ : ℝ) (a b : ℕ) :
    petChainLevel (petChainLevel γ a) b = petChainLevel γ (a + b) := by
  induction b with
  | zero => simp
  | succ b ih => rw [petChainLevel_succ, ih, ← Nat.add_assoc, petChainLevel_succ]

/-- The chain window is nonincreasing in the chain length. -/
lemma petWindow_succ_le (γ : ℝ) (D n : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    petWindow γ D (n + 1) ≤ petWindow γ D n := by
  have hmono : petChainLevel γ n ^ 2 / (20000 * (((2 ^ n * D : ℕ) : ℝ) + 1)) ≤
      petChainLevel γ (n - 1) ^ 2 / (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1)) :=
    petChainWindowLevel_antitone γ D hγ0 hγ1 (Nat.sub_le n 1)
  have h1 : petWindow γ D (n + 1)
      = min 1 (petChainLevel γ n ^ 2 / (20000 * (((2 ^ n * D : ℕ) : ℝ) + 1))) := by
    rw [petWindow, Nat.add_sub_cancel]
  have h2 : petWindow γ D n
      = min 1 (petChainLevel γ (n - 1) ^ 2
          / (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1))) := rfl
  rw [h1, h2]
  exact min_le_min_left _ hmono


/-- A power of a nonzero number, one lower. -/
lemma pow_pred_mul_inv {x : ℝ} (hx : x ≠ 0) (m : ℕ) : x ^ (m + 1) * x⁻¹ = x ^ m := by
  rw [pow_succ, mul_assoc, mul_inv_cancel₀ hx, mul_one]

/-- **The shell arithmetic.**  For `d ≥ 2`, `A ≥ 1`, `0 < γ ≤ 1`, `M^d ≤ A γ⁻¹ N` and
`A δ' ≤ γ^K` with `K ≥ 1`, the conclusion's window satisfies `H^{d-1}·M ≤ N` with
`H = ⌊δ'M⌋`. -/
lemma shell_arith {d : ℕ} (hd2 : 2 ≤ d) {N M : ℕ} {A γ δ' : ℝ} {K : ℕ}
    (hA : 1 ≤ A) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ'0 : 0 < δ') (hK : 1 ≤ K)
    (hAδ : A * δ' ≤ γ ^ K)
    (hsc : (M : ℝ) ^ d ≤ A * γ⁻¹ * (N : ℝ)) :
    ((⌊δ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) ^ (d - 1) * (M : ℝ) ≤ (N : ℝ) := by
  have hAnn : (0 : ℝ) ≤ A := by linarith
  have hAp : (0 : ℝ) < A := by linarith
  have hγK : γ ^ K ≤ γ := by
    have := pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 hK
    simpa using this
  have hγA : γ ≤ A := le_trans hγ1 hA
  have hHnn : (0 : ℝ) ≤ ((⌊δ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  -- the window bound `H ≤ γ^K M / A`
  have hδle : δ' ≤ γ ^ K / A := by
    rw [le_div_iff₀ hAp]; linarith [hAδ]
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hH1 : ((⌊δ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) ≤ γ ^ K * (M : ℝ) / A := by
    calc _ ≤ δ' * (M : ℝ) := toNat_floor_cast_le (mul_nonneg (le_of_lt hδ'0) hMnn)
      _ ≤ (γ ^ K / A) * (M : ℝ) := mul_le_mul_of_nonneg_right hδle hMnn
      _ = γ ^ K * (M : ℝ) / A := by ring
  -- the power bound
  have hstep1 : ((⌊δ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) ^ (d - 1) * (M : ℝ)
      ≤ (γ ^ K * (M : ℝ) / A) ^ (d - 1) * (M : ℝ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hHnn hH1 (d - 1)) hMnn
  have hγd : (γ ^ K) ^ (d - 1) ≤ γ ^ (d - 1) := by
    rw [← pow_mul]
    refine pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 ?_
    calc d - 1 = (d - 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (d - 1) * K := Nat.mul_le_mul_left _ hK
      _ = K * (d - 1) := Nat.mul_comm _ _
  have hMpow : (M : ℝ) ^ (d - 1) * (M : ℝ) = (M : ℝ) ^ d := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  have hstep2 : (γ ^ K * (M : ℝ) / A) ^ (d - 1) * (M : ℝ)
      ≤ γ ^ (d - 1) * (M : ℝ) ^ d / A ^ (d - 1) := by
    have hL : (γ ^ K * (M : ℝ) / A) ^ (d - 1) * (M : ℝ)
        = (γ ^ K) ^ (d - 1) * (M : ℝ) ^ d / A ^ (d - 1) := by
      rw [div_pow, mul_pow, div_mul_eq_mul_div, mul_assoc, hMpow]
    rw [hL]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hγd (pow_nonneg hMnn d)) (pow_pos hAp _).le
  -- the final arithmetic
  have hfin : γ ^ (d - 1) * (M : ℝ) ^ d / A ^ (d - 1) ≤ (N : ℝ) := by
    have hAdpos : (0 : ℝ) < A ^ (d - 1) := pow_pos hAp _
    rw [div_le_iff₀ hAdpos]
    have h1 : γ ^ (d - 1) * (M : ℝ) ^ d
        ≤ γ ^ (d - 1) * (A * γ⁻¹ * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hsc (pow_nonneg (le_of_lt hγ0) _)
    refine le_trans h1 ?_
    have hγsub : γ ^ (d - 1) * γ⁻¹ = γ ^ (d - 2) := by
      have h : d - 1 = (d - 2) + 1 := by omega
      rw [h, pow_pred_mul_inv (ne_of_gt hγ0)]
    have h2 : γ ^ (d - 1) * (A * γ⁻¹ * (N : ℝ))
        = γ ^ (d - 2) * A * (N : ℝ) := by
      rw [← hγsub]; ring
    rw [h2]
    have h3 : γ ^ (d - 2) ≤ A ^ (d - 2) := pow_le_pow_left₀ (le_of_lt hγ0) hγA (d - 2)
    have h4 : γ ^ (d - 2) * A * (N : ℝ) ≤ A ^ (d - 2) * A * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_right h3 hAnn
      have := mul_le_mul_of_nonneg_right this hNnn
      linarith [this]
    refine le_trans h4 ?_
    have h5 : A ^ (d - 2) * A = A ^ (d - 1) := by
      rw [← pow_succ]; congr 1; omega
    rw [h5, mul_comm]
  exact le_trans hstep1 (le_trans hstep2 hfin)


/-- `γ^K` is dominated by a power of `2000` times the chain level at any `k` with `2^k ≤ K`. -/
lemma pow_le_chainLevel (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {K k : ℕ} (hK : 2 ^ k ≤ K) :
    γ ^ K ≤ 2000 ^ (2 ^ k) * petChainLevel γ k := by
  have h1 : γ ^ K ≤ γ ^ (2 ^ k) := pow_le_pow_of_le_one hγ0.le hγ1 hK
  have h2 : (2000 : ℝ) ^ (2 ^ k - 1) * petChainLevel γ k = γ ^ (2 ^ k) := by
    rw [petChainLevel_eq, mul_comm]
    exact div_mul_cancel₀ _ (by positivity)
  have h4 : (2000 : ℝ) ^ (2 ^ k - 1) ≤ (2000 : ℝ) ^ (2 ^ k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h5 : (0 : ℝ) ≤ petChainLevel γ k := petChainLevel_nonneg γ hγ0.le k
  calc γ ^ K ≤ γ ^ (2 ^ k) := h1
    _ = (2000 : ℝ) ^ (2 ^ k - 1) * petChainLevel γ k := h2.symm
    _ ≤ (2000 : ℝ) ^ (2 ^ k) * petChainLevel γ k := mul_le_mul_of_nonneg_right h4 h5

/-- `linFamAvg` is nonnegative. -/
lemma linFamAvg_nonneg (D : IdxDatum) (l : ℕ) (c : ℤ) (N M H : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) :
    0 ≤ linFamAvg D l c N M H f b β := by
  rw [linFamAvg_eq]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun a _ => by simp only [linFib]; exact norm_nonneg _))

/-- The cardinality ratio of the two parameter boxes. -/
lemma parBox_card_ratio (D : IdxDatum) (l Hc Hδ : ℕ) :
    (((D.parBox l Hc).card : ℕ) : ℝ) / (((D.parBox l Hδ).card : ℕ) : ℝ)
      = (((2 * Hc + 1 : ℕ) : ℝ) / ((2 * Hδ + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) := by
  rw [parBox_card, parBox_card, Nat.cast_pow, Nat.cast_pow, ← div_pow]

/-- The chain level is nonincreasing in the number of steps. -/
lemma petChainLevel_succ_le (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (n : ℕ) :
    petChainLevel γ (n + 1) ≤ petChainLevel γ n := by
  rw [petChainLevel_succ]
  have hpos : 0 < petChainLevel γ n := petChainLevel_pos γ hγ0 n
  have hle1 : petChainLevel γ n ≤ 1 := petChainLevel_le_one γ hγ0 hγ1 n
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2000)]
  nlinarith

/-- The chain level is antitone in the number of steps. -/
lemma petChainLevel_anti {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    Antitone (petChainLevel γ) :=
  antitone_nat_of_succ_le (petChainLevel_succ_le γ hγ0 hγ1)

/-- `petWindow` is nonincreasing in the shift constant. -/
lemma petWindow_anti_D (γ : ℝ) {D D' : ℕ} (h : D ≤ D') (n : ℕ) :
    petWindow γ D' n ≤ petWindow γ D n := by
  rw [petWindow, petWindow]
  refine min_le_min_left 1 ?_
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have hcast : (((2 ^ (n - 1) * D : ℕ) : ℝ)) ≤ (((2 ^ (n - 1) * D' : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul_left (2 ^ (n - 1)) h
  nlinarith

/-- `petWindow` is nonincreasing in the index (a longer chain has a smaller window). -/
lemma petWindow_anti_index (γ : ℝ) (D : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    Antitone (petWindow γ D) :=
  antitone_nat_of_succ_le (petWindow_succ_le γ D · hγ0 hγ1)

theorem petChapter5_of_levelChainV3_aux (P : Polynomial ℤ) (h : PetLevelChain P)
    (hSBsharp : ∀ (hd : 2 ≤ P.natDegree), ∃ Cs : ℕ, 1 ≤ Cs ∧
      ∀ (N M c : ℕ) (A γ γ' : ℝ),
        1 ≤ N → 1 ≤ A → 0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 → γ' ≤ γ →
        1 ≤ (M : ℝ) * γ → (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) → 1 ≤ c →
        ∀ (G : ((histTerminal P hd).toSym).S.ι → ℤ → ℂ)
          (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat ((histTerminal P hd).toSym).nv → ℤ → ℂ),
        (histPet (histTerminal P hd) ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound N M c
          (Cs * c ^ P.natDegree * ⌈A⌉₊))
    (hShell : ∀ (E : IdxDatum) (l : ℕ), 1 ≤ l → ∀ (c : ℤ),
        ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (H : ℕ), 1 ≤ H →
          ∀ (a : E.Idx l) (i : Fin (Fintype.card (E.I (l - 1)))),
          a ∈ E.parBox l H → ((|petDir E l c a i| : ℤ) : ℝ) ≤ Cs * (H : ℝ) ^ (l - 1)) :
    PetChapter5 P := by
  classical
  by_cases hd2 : 2 ≤ P.natDegree
  · -- ====================== the main case `d ≥ 2` ======================
    unfold PetChapter5
    have hd1 : 1 ≤ P.natDegree := by omega
    have hPne : P ≠ 0 := by intro h0; rw [h0] at hd2; simp at hd2
    have hlc0 : P.leadingCoeff ≠ 0 := fun h0 => hPne (Polynomial.leadingCoeff_eq_zero.mp h0)
    have hTerm := histTerminal_phase1Terminal P hd2 hlc0
    -- the level chain at the terminal state of the phase-1 chain
    obtain ⟨Nstep, D, C₀, hNstep1, hC0, hDcard, hmain⟩ :=
      h (petTermLen P hd2 + 1) (two_le_petTermLen_add_one P hd2) P.leadingCoeff
        (histTerminal P hd2) hTerm
    -- the sharp shift bound of the terminal state and the shell bound of the datum
    obtain ⟨Cs, hCs1, hSBsharp'⟩ := hSBsharp hd2
    obtain ⟨Csh, hCsh0, hShell'⟩ := hShell D P.natDegree hd1 P.leadingCoeff
    -- the constants of the chapter (all produced before `A`)
    set nwin : ℕ := petTermLen P hd2 + 1 + Nstep with hnwindef
    have hnwin1 : 1 ≤ nwin := by omega
    set W : ℝ := max 1 (max ((1 + (qSp P : ℝ)) * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree)
      (((⌈Cs⌉₊ * (Nstep + 1) ^ P.natDegree : ℕ) : ℝ))) with hWdef
    have hW1 : 1 ≤ W := le_max_left _ _
    have hWbase_le : (1 + (qSp P : ℝ)) * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree ≤ W :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hWCs_le : ((⌈Cs⌉₊ * (Nstep + 1) ^ P.natDegree : ℕ) : ℝ) ≤ W :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    set Cpw : ℝ := petWinConst nwin W with hCpwdef
    have hCpw1 : 1 ≤ Cpw := by
      rw [hCpwdef, petWinConst]
      have h2 : (1 : ℝ) ≤ (2000 : ℝ) ^ (2 ^ nwin) := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ (20000 : ℝ) := by norm_num
      have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ nwin := one_le_pow₀ (by norm_num)
      have h5 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h6 : (1 : ℝ) ≤ (2000 : ℝ) ^ (2 ^ nwin) * 20000 :=
        one_le_mul_of_one_le_of_one_le h2 h3
      have h7 : (1 : ℝ) ≤ (2000 : ℝ) ^ (2 ^ nwin) * 20000 * (2 : ℝ) ^ nwin :=
        one_le_mul_of_one_le_of_one_le h6 h4
      have h8 : (1 : ℝ) ≤ (2000 : ℝ) ^ (2 ^ nwin) * 20000 * (2 : ℝ) ^ nwin * 2 :=
        one_le_mul_of_one_le_of_one_le h7 h5
      exact one_le_mul_of_one_le_of_one_le h8 hW1
    set npar : ℕ := ∑ j : Fin P.natDegree, Fintype.card (D.S j) with hnpar
    set Kc : ℕ := ⌈2 * Cpw⌉₊ with hKcdef
    set CstA : ℝ := 2000 ^ (2 ^ nwin) * C₀ * (3 * Cpw) ^ npar with hCstAdef
    have hCstA1 : 1 ≤ CstA := by
      rw [hCstAdef]
      have h1 : (1 : ℝ) ≤ 2000 ^ (2 ^ nwin) := one_le_pow₀ (by norm_num)
      have h2 : (1 : ℝ) ≤ C₀ := hC0
      have h3 : (1 : ℝ) ≤ 3 * Cpw := by linarith
      have h4 : (1 : ℝ) ≤ (3 * Cpw) ^ npar := one_le_pow₀ h3
      have h5 : (1 : ℝ) ≤ C₀ * (3 * Cpw) ^ npar := one_le_mul_of_one_le_of_one_le h2 h4
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ 2000 ^ (2 ^ nwin) * (C₀ * (3 * Cpw) ^ npar) :=
            mul_le_mul h1 h5 (by norm_num) (by positivity)
        _ = 2000 ^ (2 ^ nwin) * C₀ * (3 * Cpw) ^ npar := by ring
    set CstB : ℝ := ((2 * Kc + 1 : ℕ) : ℝ) ^ npar
      * 3 ^ (Fintype.card (D.I (P.natDegree - 1))) with hCstBdef
    have hCstB1 : 1 ≤ CstB := by
      rw [hCstBdef]
      have h1 : (1 : ℝ) ≤ ((2 * Kc + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ 2 * Kc + 1 := by omega
        exact_mod_cast this
      have h2 : (1 : ℝ) ≤ ((2 * Kc + 1 : ℕ) : ℝ) ^ npar := one_le_pow₀ h1
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (Fintype.card (D.I (P.natDegree - 1))) :=
        one_le_pow₀ (by norm_num)
      exact one_le_mul_of_one_le_of_one_le h2 h3
    set Cst₁ : ℝ := max CstA CstB with hCst₁def
    have hCst₁1 : 1 ≤ Cst₁ := le_trans hCstA1 (le_max_left _ _)
    set K₀ : ℕ := max (2 ^ nwin)
      (max (2 ^ nwin + 2) (Fintype.card (D.I (P.natDegree - 1)) + 1)) with hK₀def
    have hK₀pow : 2 ^ nwin ≤ K₀ := le_max_left _ _
    have hK₀win : 2 ^ nwin + 2 ≤ K₀ := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK₀corner : Fintype.card (D.I (P.natDegree - 1)) + 1 ≤ K₀ :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hK₀2 : 2 ≤ K₀ := le_trans (Nat.le_add_left 2 _) hK₀win
    have hK₀1 : 1 ≤ K₀ := le_trans (by norm_num : (1 : ℕ) ≤ 2) hK₀2
    set Cne₀ : ℕ := 2 ^ Nstep * Cs * (Nstep + 1) ^ P.natDegree * 2 + ⌈Csh⌉₊ + 1 with hCne₀def
    have hCne₀1 : 1 ≤ Cne₀ := by rw [hCne₀def]; exact Nat.le_add_left 1 _
    have hceilA : ∀ {A : ℝ}, 1 ≤ A → ((⌈A⌉₊ : ℕ) : ℝ) ≤ 2 * A := by
      intro A hA
      have h1 : ((⌈A⌉₊ : ℕ) : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    refine ⟨D, hDcard, Cne₀, K₀, Cst₁, hCne₀1, hK₀2, hCst₁1, ?_⟩
    intro A hA
    have hA1 : 1 ≤ A := hA
    set cc : ℕ := Nstep + 1 with hccdef
    have hcc1 : 1 ≤ cc := by omega
    set Dsb : ℕ := Cs * cc ^ P.natDegree * ⌈A⌉₊ with hDsbdef
    have hAceil1 : 1 ≤ ⌈A⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    have hDsb1 : 1 ≤ Dsb := by
      rw [hDsbdef]
      have h2 : (1 : ℕ) ≤ cc ^ P.natDegree := one_le_pow₀ (by omega)
      calc (1 : ℕ) = 1 * 1 * 1 := by ring
        _ ≤ Cs * cc ^ P.natDegree * ⌈A⌉₊ := Nat.mul_le_mul (Nat.mul_le_mul hCs1 h2) hAceil1
    set Cne : ℕ := 2 ^ Nstep * Dsb + ⌈Csh⌉₊ with hCnedef
    have hCne1 : 1 ≤ Cne := by
      rw [hCnedef]
      have h1 : (1 : ℕ) ≤ 2 ^ Nstep * Dsb := by
        have h2 : (1 : ℕ) ≤ 2 ^ Nstep := one_le_pow₀ (by norm_num)
        calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
          _ ≤ 2 ^ Nstep * Dsb := Nat.mul_le_mul h2 hDsb1
      exact le_trans h1 (Nat.le_add_right _ _)
    have hCnele : (Cne : ℝ) ≤ (Cne₀ : ℝ) * A := by
      have hceil := hceilA hA1
      have hCne_eq : (Cne : ℝ)
          = ((2 ^ Nstep * Cs * cc ^ P.natDegree : ℕ) : ℝ) * ((⌈A⌉₊ : ℕ) : ℝ)
            + ((⌈Csh⌉₊ : ℕ) : ℝ) := by
        rw [hCnedef, hDsbdef]; push_cast; ring
      have hCne₀_eq : (Cne₀ : ℝ)
          = ((2 ^ Nstep * Cs * cc ^ P.natDegree : ℕ) : ℝ) * 2 + ((⌈Csh⌉₊ : ℕ) : ℝ) + 1 := by
        rw [hCne₀def, hccdef]; push_cast; ring
      rw [hCne_eq, hCne₀_eq]
      have hA0 : (0 : ℝ) ≤ A := by linarith
      have hnn : (0 : ℝ) ≤ ((2 ^ Nstep * Cs * cc ^ P.natDegree : ℕ) : ℝ) := Nat.cast_nonneg _
      have hCshnn : (0 : ℝ) ≤ ((⌈Csh⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hceil, hnn, hCshnn, hA0, hA1]
    refine ⟨K₀, hK₀2, le_rfl, Cst₁, hCst₁1, le_rfl, Cne, hCne1, hCnele, ?_⟩
    intro N M F γ δ' hdeg2 hN1 hM1 hsc1 hsc2 hγ0 hγ1 hδ'0 hAδ hHδ hFb hFs hΛ
    set Ftop : ℤ → ℂ := F ⟨P.natDegree, Nat.lt_succ_self _⟩ with hFtopdef
    have hN0 : 0 < N := by omega
    have hM0 : 0 < M := by omega
    -- elementary consequences of the hypotheses
    have hδ'M2 : (2 : ℝ) ≤ δ' * (M : ℝ) := two_le_of_toNat_le hHδ
    have hδ'le : δ' ≤ γ ^ K₀ / A := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < A)]
      linarith [hAδ]
    have hγK₀γ : γ ^ K₀ ≤ γ := by simpa using pow_le_pow_of_le_one hγ0.le hγ1 hK₀1
    have hδ'leγ : δ' ≤ γ := by
      refine le_trans hδ'le ?_
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < A)]
      nlinarith [hγK₀γ, hA, hγ0.le]
    have hMγ : 1 ≤ (M : ℝ) * γ := by
      have h2 : δ' * (M : ℝ) ≤ (γ ^ K₀ / A) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hδ'le (by positivity)
      have h3 : (γ ^ K₀ / A) * (M : ℝ) ≤ γ * (M : ℝ) := by
        have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        have h4 : (γ ^ K₀ / A) ≤ γ := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < A)]
          nlinarith [hγK₀γ, hA, hγ0.le]
        exact mul_le_mul_of_nonneg_right h4 hMnn
      have h5 : (2 : ℝ) ≤ γ * (M : ℝ) := le_trans hδ'M2 (le_trans h2 h3)
      linarith [h5]
    -- the window of the conclusion
    set Hδ : ℕ := ⌊δ' * (M : ℝ)⌋.toNat with hHδdef
    have hHδ1 : 1 ≤ Hδ := by rw [hHδdef]; exact le_trans (by norm_num) hHδ
    have hshellbox : ((Hδ : ℕ) : ℝ) ^ (P.natDegree - 1) * (M : ℝ) ≤ (N : ℝ) := by
      rw [hHδdef]
      exact shell_arith hd2 hA hγ0 hγ1 hδ'0 hK₀1 hAδ hsc2
    -- the level of the chain and the shift constants
    set B : ℝ := petChainLevel γ (petTermLen P hd2 + 1) with hBdef
    have hB0 : 0 ≤ B := petChainLevel_nonneg γ hγ0.le _
    have hB1 : B ≤ 1 := petChainLevel_le_one γ hγ0 hγ1 _
    set D₀ : ℕ := Nat.ceil (((1 + (qSp P : ℝ))
      * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * (A / γ)) with hD₀def
    have hD₀1 : 1 ≤ D₀ := by
      rw [hD₀def]
      refine Nat.one_le_ceil_iff.mpr ?_
      have h1 : (1 : ℝ) ≤ 1 + (qSp P : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) (qSp P); linarith
      have h2 : (1 : ℝ) ≤ ((petTermLen P hd2 + 1 : ℕ) : ℝ) := by
        have h3 : (1 : ℕ) ≤ petTermLen P hd2 + 1 := by omega
        exact_mod_cast h3
      have h3 : (1 : ℝ) ≤ ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree := one_le_pow₀ h2
      have h4 : (1 : ℝ) ≤ A / γ := by rw [le_div_iff₀ hγ0]; linarith
      have h5 : (1 : ℝ) ≤ (1 + (qSp P : ℝ))
          * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree :=
        one_le_mul_of_one_le_of_one_le h1 h3
      exact lt_of_lt_of_le zero_lt_one (one_le_mul_of_one_le_of_one_le h5 h4)
    have hD₀le : (D₀ : ℝ) ≤ 2 * W * A / γ := by
      have hx1 : (1 : ℝ) ≤ ((1 + (qSp P : ℝ))
          * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * (A / γ) := by
        have h1 : (1 : ℝ) ≤ 1 + (qSp P : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) (qSp P); linarith
        have h2 : (1 : ℝ) ≤ ((petTermLen P hd2 + 1 : ℕ) : ℝ) := by
          have h3 : (1 : ℕ) ≤ petTermLen P hd2 + 1 := by omega
          exact_mod_cast h3
        have h3 : (1 : ℝ) ≤ ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree := one_le_pow₀ h2
        have h4 : (1 : ℝ) ≤ A / γ := by rw [le_div_iff₀ hγ0]; linarith
        have h5 : (1 : ℝ) ≤ (1 + (qSp P : ℝ))
            * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree :=
          one_le_mul_of_one_le_of_one_le h1 h3
        exact one_le_mul_of_one_le_of_one_le h5 h4
      have hceil : ((⌈((1 + (qSp P : ℝ))
            * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * (A / γ)⌉₊ : ℕ) : ℝ)
          ≤ 2 * (((1 + (qSp P : ℝ))
            * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * (A / γ)) := by
        have hlt := Nat.ceil_lt_add_one (le_trans zero_le_one hx1)
        linarith [hlt, hx1]
      have hmain' : ((D₀ : ℕ) : ℝ) ≤ 2 * W * A / γ := by
        rw [hD₀def]
        have hstep : 2 * (((1 + (qSp P : ℝ))
              * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * (A / γ))
            ≤ 2 * W * A / γ := by
          have h2 : 2 * (((1 + (qSp P : ℝ))
                * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * (A / γ))
              = 2 * ((1 + (qSp P : ℝ))
                * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree) * A / γ := by ring
          rw [h2]
          have h3 : 2 * ((1 + (qSp P : ℝ))
                * ((petTermLen P hd2 + 1 : ℕ) : ℝ) ^ P.natDegree)
              ≤ 2 * W := by linarith [hWbase_le]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (by linarith)) hγ0.le
        linarith [hceil, hstep]
      exact hmain'
    have hDsble : (Dsb : ℝ) ≤ 2 * W * A / γ := by
      have h1 : (Dsb : ℝ) ≤ ((⌈Cs⌉₊ * cc ^ P.natDegree : ℕ) : ℝ) * ((⌈A⌉₊ : ℕ) : ℝ) := by
        have h2 : (Cs : ℝ) * (cc : ℝ) ^ P.natDegree
            ≤ (⌈Cs⌉₊ : ℝ) * (cc : ℝ) ^ P.natDegree := by
          have h3 : (Cs : ℝ) ≤ (⌈Cs⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil Cs
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
        have hDsbR : (Dsb : ℝ) = (Cs : ℝ) * (cc : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) := by
          rw [hDsbdef]; push_cast; ring
        rw [hDsbR]
        calc (Cs : ℝ) * (cc : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ)
            ≤ (⌈Cs⌉₊ : ℝ) * (cc : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) :=
              mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
          _ = ((⌈Cs⌉₊ * cc ^ P.natDegree : ℕ) : ℝ) * ((⌈A⌉₊ : ℕ) : ℝ) := by push_cast; ring
      have h2 : ((⌈Cs⌉₊ * cc ^ P.natDegree : ℕ) : ℝ) * ((⌈A⌉₊ : ℕ) : ℝ) ≤ W * (2 * A) := by
        have hceil := hceilA hA1
        exact mul_le_mul hWCs_le hceil (Nat.cast_nonneg _) (by linarith)
      have h3 : W * (2 * A) ≤ 2 * W * A / γ := by
        rw [le_div_iff₀ hγ0]
        nlinarith [hW1, hA1, hγ1, hγ0]
      linarith [h1, h2, h3]
    set Dw : ℕ := max D₀ Dsb with hDwdef
    have hDw1 : 1 ≤ Dw := le_trans hD₀1 (le_max_left _ _)
    have hDwle : (Dw : ℝ) ≤ 2 * W * A / γ := by
      rw [hDwdef]; push_cast
      exact max_le hD₀le hDsble
    -- the window of the chain
    set γ' : ℝ := min (petWindow γ Dw nwin) δ' with hγ'def
    have hγ'0 : 0 < γ' := by
      rw [hγ'def]
      exact lt_min (petWindow_pos γ Dw nwin hγ0 hγ1 hnwin1 hDw1) hδ'0
    have hγ'1 : γ' ≤ 1 := by
      rw [hγ'def]
      exact le_trans (min_le_left _ _) (petWindow_le_one γ Dw nwin)
    have hγ'leγ : γ' ≤ γ := by
      rw [hγ'def]
      exact le_trans (min_le_left _ _) (petWindow_le_gamma γ Dw nwin hγ0 hγ1 hnwin1)
    have hγ'leδ : γ' ≤ δ' := by rw [hγ'def]; exact min_le_right _ _
    have hγ'lePW : γ' ≤ petWindow γ Dw nwin := by rw [hγ'def]; exact min_le_left _ _
    set Hc : ℕ := ⌊γ' * (M : ℝ)⌋.toNat with hHcdef
    -- the shell bound for the parameters outside the chain's window
    have shellBd : ∀ (a : D.Idx P.natDegree) (ha : a ∈ D.parBox P.natDegree Hδ)
        (i : Fin (Fintype.card (D.I (P.natDegree - 1)))) (y : ℕ) (hy : y ∈ Finset.Icc 1 M),
        |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ)| ≤ (Cne : ℤ) * (N : ℤ) := by
      intro a ha i y hy
      have hCs : |((petDir D P.natDegree P.leadingCoeff a i : ℤ) : ℝ)|
          ≤ Csh * (Hδ : ℝ) ^ (P.natDegree - 1) := by
        rw [← Int.cast_abs]
        exact hShell' Hδ hHδ1 a i ha
      have hyM : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).2
      have hy0 : (0 : ℤ) ≤ (y : ℤ) := by omega
      have hyR : (y : ℝ) ≤ (M : ℝ) := by exact_mod_cast hyM
      have hyR0 : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
      have hkey : |((petDir D P.natDegree P.leadingCoeff a i : ℤ) : ℝ)| * (y : ℝ)
          ≤ (Cne : ℝ) * (N : ℝ) := by
        have h1 : |((petDir D P.natDegree P.leadingCoeff a i : ℤ) : ℝ)| * (y : ℝ)
            ≤ (Csh * (Hδ : ℝ) ^ (P.natDegree - 1)) * (M : ℝ) :=
          mul_le_mul hCs hyR hyR0 (mul_nonneg hCsh0 (pow_nonneg (Nat.cast_nonneg Hδ) _))
        have h2 : (Csh * (Hδ : ℝ) ^ (P.natDegree - 1)) * (M : ℝ) ≤ Csh * (N : ℝ) := by
          calc (Csh * (Hδ : ℝ) ^ (P.natDegree - 1)) * (M : ℝ)
              = Csh * ((Hδ : ℝ) ^ (P.natDegree - 1) * (M : ℝ)) := by ring
            _ ≤ Csh * (N : ℝ) := mul_le_mul_of_nonneg_left hshellbox hCsh0
        have h4 : Csh * (N : ℝ) ≤ ((⌈Csh⌉₊ : ℕ) : ℝ) * (N : ℝ) := by
          have hc := Nat.le_ceil Csh
          have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          nlinarith [hc, hNnn]
        have h5 : ((⌈Csh⌉₊ : ℕ) : ℝ) * (N : ℝ) ≤ (Cne : ℝ) * (N : ℝ) := by
          have h6 : (⌈Csh⌉₊ : ℕ) ≤ Cne := by
            rw [hCnedef]; exact Nat.le_add_left _ _
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast h6) (Nat.cast_nonneg N)
        linarith [h1, h2, h4, h5]
      have hgoal : |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ)|
          = ((|petDir D P.natDegree P.leadingCoeff a i| : ℤ) : ℤ) * (y : ℤ) := by
        rw [abs_mul, abs_of_nonneg hy0]
      rw [hgoal]
      have hcast : ((((|petDir D P.natDegree P.leadingCoeff a i| : ℤ)) * (y : ℤ) : ℤ) : ℝ)
          = |((petDir D P.natDegree P.leadingCoeff a i : ℤ) : ℝ)| * (y : ℝ) := by
        rw [Int.cast_mul, Int.cast_abs]
        push_cast
        ring
      have hfin : ((((|petDir D P.natDegree P.leadingCoeff a i| : ℤ)) * (y : ℤ) : ℤ) : ℝ)
          ≤ ((Cne : ℤ) : ℝ) * ((N : ℤ) : ℝ) := by
        rw [hcast]
        push_cast
        exact hkey
      exact_mod_cast hfin
    by_cases hcase : 2 ≤ petWindow γ Dw nwin * (M : ℝ)
    · -- ======================= Case A: the PET chain =======================
      have hγ'M : 2 ≤ γ' * (M : ℝ) := by
        rw [hγ'def, min_mul_of_nonneg _ _ (by positivity)]
        exact le_min hcase hδ'M2
      have hHc1 : 1 ≤ Hc := by
        rw [hHcdef]
        exact le_trans (by norm_num) (toNat_floor_two_le hγ'M)
      have hmm : petTermLen P hd2 = histLen (petHistInitState P (by omega)) := petTermLen_eq P hd2
      -- the analytic chain of the phase-1 part
      have hSB₀ : (Work.Peluse.UControl.PetStep.LambdaMDPetState N M P F).ShiftBound N M
          (petTermLen P hd2 + 1) D₀ := by
        have h := lambdaMDShiftBound N M P F (petTermLen P hd2 + 1) A γ hN0 hM0 hA hγ0
          (by omega) hsc2
        rw [hD₀def]; exact h
      have hinv : HistInv N M γ' (petHistInit P (by omega)) (fun i => petInitSlotF P F i.1.1)
          (petInitBase ⌊γ' * (M : ℝ)⌋.toNat P F) γ D₀ (petTermLen P hd2 + 1) := by
        refine petHistInit_inv P (by omega) N M F γ γ' D₀ (petTermLen P hd2 + 1) hN0 hM0
          hγ0 hγ1 hγ'0 hγ'1 ?_ ?_ hD₀1 ?_ hSB₀ hHc1 ?_ hΛ
        · intro i x; exact hFb i x
        · intro i; exact hFs i
        · rw [hmm]; exact le_rfl
        · intro k hk
          refine le_trans ?_ (petHistInit_hw P (by omega) γ D₀ hγ0 hγ1 hD₀1 k hk)
          refine le_trans hγ'lePW ?_
          calc petWindow γ Dw nwin ≤ petWindow γ D₀ nwin := petWindow_anti_D γ (le_max_left _ _) nwin
            _ ≤ petWindow γ D₀ (petTermLen P hd2 + 1) :=
                petWindow_anti_index γ D₀ hγ0 hγ1 (by omega)
            _ = petWindow γ D₀ (histLen (petHistInitState P (by omega)) + 1) := by rw [hmm]
            _ ≤ petWindow γ D₀ (histLen (petHistInitState P (by omega))) :=
                petWindow_succ_le γ D₀ _ hγ0 hγ1
      obtain ⟨B0, G, g, hinv2, hG⟩ := histPhase1RunInv N M γ' (petHistInit P (by omega))
        (petInitSlotF P F) (fun i => petInitSlotF P F i.1.1) (petInitBase _ P F) γ D₀
        (petTermLen P hd2 + 1) hinv (fun i x => rfl)
      have hPh1 : Phase1 P.natDegree (phase1Chain (petHistInitState P (by omega))).1
          P.leadingCoeff (phase1Chain (petHistInitState P (by omega))).2 :=
        histPhase1Inv hd2 P.leadingCoeff _ (petHistInit_phase1 P (by omega))
      have hdone : Phase1Done (phase1Chain (petHistInitState P (by omega))).2 :=
        phase1Chain_done hd2 P.leadingCoeff _ (petHistInit_phase1 P (by omega))
      have htop : ∀ i : ((phase1Chain (petHistInitState P (by omega))).2.toSym).S.ι,
          (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)) := by
        intro i
        have hi : i.1.1 = (Sum.inr 0 : InitIdx P.natDegree) := hdone i.1 i.2
        by_cases hB : B0 i
        · right
          intro x
          rw [hG i x, if_pos hB, hi]
          rfl
        · left
          intro x
          rw [hG i x, if_neg hB, hi]
          rfl
      have hwinclw : γ' ≤ (petChainLevel γ (histLen (petHistInitState P (by omega)))) ^ 2
          / (20000 * (((2 ^ histLen (petHistInitState P (by omega)) * D₀ : ℕ) : ℝ) + 1)) := by
        have h1 : γ' ≤ petWindow γ D₀ (histLen (petHistInitState P (by omega)) + 1) := by
          refine le_trans hγ'lePW ?_
          calc petWindow γ Dw nwin ≤ petWindow γ D₀ nwin := petWindow_anti_D γ (le_max_left _ _) nwin
            _ ≤ petWindow γ D₀ (petTermLen P hd2 + 1) :=
                petWindow_anti_index γ D₀ hγ0 hγ1 (by omega)
            _ = petWindow γ D₀ (histLen (petHistInitState P (by omega)) + 1) := by rw [hmm]
        have h2 : petWindow γ D₀ (histLen (petHistInitState P (by omega)) + 1)
            = min 1 ((petChainLevel γ (histLen (petHistInitState P (by omega)))) ^ 2
              / (20000 * (((2 ^ histLen (petHistInitState P (by omega)) * D₀ : ℕ) : ℝ) + 1))) := by
          rw [petWindow, Nat.add_sub_cancel]
        rw [h2] at h1
        exact le_trans h1 (min_le_right _ _)
      obtain ⟨G₂, g₂, hT₂, hlam₂, hSB₂, htop₂, hg₂⟩ :=
        histCloseLinkWin N M γ' P.leadingCoeff (phase1Chain (petHistInitState P (by omega))).2
          hPh1 hdone hd2 hlc0 Ftop G g
          (petChainLevel γ (histLen (petHistInitState P (by omega))))
          (2 ^ histLen (petHistInitState P (by omega)) * D₀)
          (petTermLen P hd2 + 1 - histLen (petHistInitState P (by omega))) hinv2 htop hwinclw
      -- the sharp shift bound of the terminal state at range `cc`
      have hSBsharpA : (histPet (histTerminal P hd2) ⌊γ' * (M : ℝ)⌋.toNat G₂ g₂).toState.ShiftBound
          N M cc Dsb :=
        hSBsharp' N M cc A γ γ' hN1 hA1 hγ0 hγ1 hγ'0 hγ'1 hγ'leγ hMγ hsc2 hcc1 G₂ g₂
      -- the correlation bound at the terminal state
      have hlam' : B ≤ (histPet (histTerminal P hd2) ⌊γ' * (M : ℝ)⌋.toNat G₂ g₂).toState.lam N M := by
        have h1 := hlam₂
        rw [petChainLevel_add γ (histLen (petHistInitState P (by omega))) 1, ← hmm] at h1
        rw [hBdef]
        exact h1
      -- the chain's window condition
      have hwin : ∀ k : ℕ, k < Nstep →
          γ' ≤ petChainLevel B k ^ 2 / (20000 * (((2 ^ k * Dsb : ℕ) : ℝ) + 1)) := by
        intro k hk
        refine le_trans hγ'lePW ?_
        have hcomp : petChainLevel B k = petChainLevel γ (petTermLen P hd2 + 1 + k) := by
          rw [hBdef]; exact petChainLevel_add γ (petTermLen P hd2 + 1) k
        have hkn : petTermLen P hd2 + 1 + k ≤ nwin - 1 := by rw [hnwindef]; omega
        have hkn' : k ≤ nwin - 1 := le_trans (Nat.le_add_left k (petTermLen P hd2 + 1)) hkn
        rw [hcomp]
        refine le_trans (min_le_right _ _) ?_
        have hnum : petChainLevel γ (nwin - 1) ≤ petChainLevel γ (petTermLen P hd2 + 1 + k) :=
          petChainLevel_anti hγ0 hγ1 hkn
        have hden : 20000 * (((2 ^ k * Dsb : ℕ) : ℝ) + 1)
            ≤ 20000 * (((2 ^ (nwin - 1) * Dw : ℕ) : ℝ) + 1) := by
          have h1 : 2 ^ k * Dsb ≤ 2 ^ (nwin - 1) * Dw := by
            have h2 : 2 ^ k ≤ 2 ^ (nwin - 1) := Nat.pow_le_pow_right (by norm_num) hkn'
            have h3 : Dsb ≤ Dw := le_max_right _ _
            exact Nat.mul_le_mul h2 h3
          have h4 : ((2 ^ k * Dsb : ℕ) : ℝ) ≤ ((2 ^ (nwin - 1) * Dw : ℕ) : ℝ) :=
            Nat.cast_le.mpr h1
          push_cast at h4 ⊢
          linarith
        have hsq : petChainLevel γ (nwin - 1) ^ 2
            ≤ petChainLevel γ (petTermLen P hd2 + 1 + k) ^ 2 :=
          pow_le_pow_left₀ (petChainLevel_nonneg γ hγ0.le _) hnum 2
        have hstep1 : petChainLevel γ (nwin - 1) ^ 2
              / (20000 * (((2 ^ (nwin - 1) * Dw : ℕ) : ℝ) + 1))
            ≤ petChainLevel γ (nwin - 1) ^ 2
              / (20000 * (((2 ^ k * Dsb : ℕ) : ℝ) + 1)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
        have hstep2 : petChainLevel γ (nwin - 1) ^ 2
              / (20000 * (((2 ^ k * Dsb : ℕ) : ℝ) + 1))
            ≤ petChainLevel γ (petTermLen P hd2 + 1 + k) ^ 2
              / (20000 * (((2 ^ k * Dsb : ℕ) : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hsq (by positivity)
        exact le_trans hstep1 hstep2
      have hG₂b : ∀ i : ((histTerminal P hd2).toSym).S.ι, ∀ x : ℤ, ‖G₂ i x‖ ≤ 1 := by
        intro i x
        rcases htop₂ i with h | h
        · rw [h]; exact hFb ⟨P.natDegree, Nat.lt_succ_self _⟩ x
        · rw [h]; simpa using hFb ⟨P.natDegree, Nat.lt_succ_self _⟩ x
      have hG₂s : ∀ i : ((histTerminal P hd2).toSym).S.ι, SupportIn (G₂ i) N := by
        intro i x hx
        rcases htop₂ i with h | h
        · rw [h]; exact hFs ⟨P.natDegree, Nat.lt_succ_self _⟩ x hx
        · rw [h]; simpa using hFs ⟨P.natDegree, Nat.lt_succ_self _⟩ x hx
      obtain ⟨c₀, hc₀⟩ := hg₂
      have hg₂b : ∀ a : WinTower ⌊γ' * (M : ℝ)⌋.toNat
          ((histTerminal P hd2).toSym).nv, ∀ x : ℤ, ‖g₂ a x‖ ≤ 1 := by
        intro a x
        rw [hc₀ a x]
        split_ifs
        · simpa using hFb ⟨P.natDegree, Nat.lt_succ_self _⟩ x
        · exact hFb ⟨P.natDegree, Nat.lt_succ_self _⟩ x
      have hg₂s : ∀ a : WinTower ⌊γ' * (M : ℝ)⌋.toNat
          ((histTerminal P hd2).toSym).nv, SupportIn (g₂ a) N := by
        intro a x hx
        rw [hc₀ a x]
        split_ifs
        · simpa using hFs ⟨P.natDegree, Nat.lt_succ_self _⟩ x hx
        · exact hFs ⟨P.natDegree, Nat.lt_succ_self _⟩ x hx
      obtain ⟨b, β, hβshift, havg⟩ :=
        hmain N M γ' Ftop G₂ g₂ cc Dsb B hN1 hG₂b hG₂s hg₂b hg₂s hM1 hHc1 le_rfl hB0 hB1 hwin
          hSBsharpA htop₂ ⟨c₀, hc₀⟩ hlam'
      -- the clipped constant term
      set β' : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ :=
        fun a i => if a ∈ D.parBox P.natDegree Hc then β a i else 0 with hβ'def
      refine ⟨b, β', ?_, ?_⟩
      · -- the shift bound
        intro a ha i y hy
        by_cases hain : a ∈ D.parBox P.natDegree Hc
        · have h1 := hβshift a hain i y hy
          have h2 : β' a i = β a i := by rw [hβ'def]; simp only [hain, ↓reduceIte]
          rw [h2]
          have hleNat : 2 ^ Nstep * Dsb ≤ Cne := by
            rw [hCnedef]; exact Nat.le_add_right _ _
          have hleZ : ((2 ^ Nstep * Dsb : ℕ) : ℤ) ≤ (Cne : ℤ) := by exact_mod_cast hleNat
          have hNnnZ : (0 : ℤ) ≤ (N : ℤ) := by omega
          exact le_trans h1 (mul_le_mul_of_nonneg_right hleZ hNnnZ)
        · have h2 : β' a i = 0 := by rw [hβ'def]; simp only [hain, ↓reduceIte]
          rw [h2, add_zero]
          exact shellBd a ha i y hy
      · -- the average bound
        have hHcle : Hc ≤ Hδ := by
          rw [hHcdef, hHδdef]
          exact toNat_floor_le_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hγ'leδ (by positivity : (0 : ℝ) ≤ (M : ℝ)))
        have hclip := linFamAvg_clip_le (l := P.natDegree) D P.leadingCoeff N M Ftop b β hHcle
        have hratio : (1 / (3 * Cpw)) ^ npar
            ≤ (((D.parBox P.natDegree Hc).card : ℕ) : ℝ)
              / (((D.parBox P.natDegree Hδ).card : ℕ) : ℝ) := by
          rw [parBox_card_ratio]
          refine pow_le_pow_left₀ (by positivity) ?_ _
          by_cases hwinle : petWindow γ Dw nwin ≤ δ'
          · have hγ'eq : γ' = petWindow γ Dw nwin := by rw [hγ'def]; exact min_eq_left hwinle
            have hHceq : Hc = ⌊petWindow γ Dw nwin * (M : ℝ)⌋.toNat := by rw [hHcdef, hγ'eq]
            rw [hHceq]
            have hDδ : ((Hδ : ℕ) : ℝ) ≤ δ' * (M : ℝ) := by
              rw [hHδdef]
              exact toNat_floor_cast_le (by positivity)
            have hdM1 : (1 : ℝ) ≤ δ' * (M : ℝ) := by linarith [hδ'M2]
            have hHc' : petWindow γ Dw nwin * (M : ℝ) - 1
                ≤ ((⌊petWindow γ Dw nwin * (M : ℝ)⌋.toNat : ℕ) : ℝ) :=
              sub_one_le_toNat_floor (by positivity)
            have hr : 1 / Cpw ≤ petWindow γ Dw nwin / δ' := by
              have h := petWindow_ratio_le γ Dw nwin A W δ' K₀ hγ0 hγ1 hA hnwin1 hDw1 hW1 hDwle
                hδ'0 (by rw [le_div_iff₀ (by linarith : (0 : ℝ) < A)]; linarith [hAδ]) hK₀win
              have h2 : petWinConst nwin W = Cpw := hCpwdef.symm
              rw [h2] at h
              have h3 : (0 : ℝ) < Cpw := by rw [← h2]; exact petWinConst_pos _ (by linarith)
              rw [div_le_iff₀ h3] at h
              rw [div_le_div_iff₀ h3 hδ'0]
              linarith [h]
            have hr' : 1 / Cpw
                ≤ (petWindow γ Dw nwin * (M : ℝ)) / (δ' * (M : ℝ)) := by
              have hMne : (M : ℝ) ≠ 0 := by positivity
              rw [show petWindow γ Dw nwin * (M : ℝ) / (δ' * (M : ℝ))
                  = petWindow γ Dw nwin / δ' from by field_simp]
              exact hr
            have hb := box_ratio_le Cpw (petWindow γ Dw nwin * (M : ℝ)) (δ' * (M : ℝ))
              ⌊petWindow γ Dw nwin * (M : ℝ)⌋.toNat Hδ
              hCpw1 hDδ hHc' hcase hdM1 hr'
            simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hb
          · have hγ'eq : γ' = δ' := by
              rw [hγ'def]; exact min_eq_right (le_of_lt (lt_of_not_ge hwinle))
            have hHceq : Hc = Hδ := by rw [hHcdef, hHδdef, hγ'eq]
            rw [hHceq]
            rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 3 * Cpw) (by positivity)]
            nlinarith [hCpw1, (Nat.cast_nonneg Hδ : (0 : ℝ) ≤ (Hδ : ℝ))]
        have htrans : (1 / (3 * Cpw)) ^ npar
              * linFamAvg D P.natDegree P.leadingCoeff N M Hc Ftop b β
            ≤ linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' := by
          have hβ'eq : (fun a i => if a ∈ D.parBox P.natDegree Hc then β a i else 0) = β' :=
            hβ'def.symm
          rw [hβ'eq] at hclip
          exact le_trans (mul_le_mul_of_nonneg_right hratio
            (linFamAvg_nonneg D P.natDegree P.leadingCoeff N M Hc Ftop b β)) hclip
        have hLc : linFamAvg D P.natDegree P.leadingCoeff N M Hc Ftop b β
            ≤ (3 * Cpw) ^ npar
              * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' := by
          have h3 : (0 : ℝ) ≤ (3 * Cpw) ^ npar := by positivity
          calc linFamAvg D P.natDegree P.leadingCoeff N M Hc Ftop b β
              = (3 * Cpw) ^ npar * ((1 / (3 * Cpw)) ^ npar
                  * linFamAvg D P.natDegree P.leadingCoeff N M Hc Ftop b β) := by
                rw [← mul_assoc, ← mul_pow]
                have h4 : (3 * Cpw) * (1 / (3 * Cpw)) = 1 := by
                  field_simp
                rw [h4, one_pow, one_mul]
            _ ≤ (3 * Cpw) ^ npar
                  * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' :=
                mul_le_mul_of_nonneg_left htrans h3
        have hchain : petChainLevel γ nwin
            ≤ C₀ * linFamAvg D P.natDegree P.leadingCoeff N M Hc Ftop b β := by
          have h1 : petChainLevel B Nstep = petChainLevel γ (petTermLen P hd2 + 1 + Nstep) := by
            rw [hBdef]; exact petChainLevel_add γ (petTermLen P hd2 + 1) Nstep
          rw [hnwindef, ← h1]
          exact havg
        have hLδnn : (0 : ℝ) ≤ linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' :=
          linFamAvg_nonneg D P.natDegree P.leadingCoeff N M Hδ Ftop b β'
        have hpow : γ ^ K₀ ≤ 2000 ^ (2 ^ nwin) * petChainLevel γ nwin :=
          pow_le_chainLevel γ hγ0 hγ1 hK₀pow
        have hstep : 2000 ^ (2 ^ nwin) * petChainLevel γ nwin
            ≤ 2000 ^ (2 ^ nwin) * (C₀ * (3 * Cpw) ^ npar
              * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β') := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc petChainLevel γ nwin
              ≤ C₀ * linFamAvg D P.natDegree P.leadingCoeff N M Hc Ftop b β := hchain
            _ ≤ C₀ * ((3 * Cpw) ^ npar
                  * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β') :=
                mul_le_mul_of_nonneg_left hLc (le_trans zero_le_one hC0)
            _ = C₀ * (3 * Cpw) ^ npar
                  * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' := by ring
        calc γ ^ K₀ ≤ 2000 ^ (2 ^ nwin) * petChainLevel γ nwin := hpow
          _ ≤ 2000 ^ (2 ^ nwin) * (C₀ * (3 * Cpw) ^ npar
                * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β') := hstep
          _ = CstA * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' := by
              rw [hCstAdef]; ring
          _ ≤ Cst₁ * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b β' :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hLδnn
    · -- ======================= Case B: the corner =======================
      have hsmall : petWindow γ Dw nwin * (M : ℝ) < 2 := lt_of_not_ge hcase
      have hHδKc : Hδ ≤ Kc := by
        have hsmall' : petWindow γ Dw nwin * ((M : ℝ) / 2) < 1 := by linarith
        have hle := hist_le_of_small_window γ Dw nwin A δ' ((M : ℝ) / 2) W K₀
          hγ0 hγ1 hA hnwin1 hDw1 hW1 hDwle hδ'0
          (by rw [le_div_iff₀ (by linarith : (0 : ℝ) < A)]; linarith [hAδ]) hK₀win
          (by positivity) hsmall'
        have h2 : petWinConst nwin W = Cpw := hCpwdef.symm
        rw [h2] at hle
        have h1 : δ' * (M : ℝ) ≤ 2 * Cpw := by linarith [hle]
        rw [hKcdef, hHδdef]
        have h3 : ((⌊δ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) ≤ δ' * (M : ℝ) :=
          toNat_floor_cast_le (by positivity)
        have h4 : (2 * Cpw) ≤ ((⌈2 * Cpw⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        exact_mod_cast le_trans h3 (le_trans h1 h4)
      -- the corner datum
      set t : ℕ := 2 ^ (Fintype.card (D.S (P.natDegree - 1)) - 1) with htdef
      have hs2 : 2 ≤ Fintype.card (D.S (P.natDegree - 1)) := by
        have h2 : 3 ≤ 2 ^ Fintype.card (D.S (P.natDegree - 1)) := by
          have h1 := hDcard
          rw [card_I] at h1
          omega
        by_contra hc
        push_neg at hc
        have h4 : Fintype.card (D.S (P.natDegree - 1)) = 0
            ∨ Fintype.card (D.S (P.natDegree - 1)) = 1 := by omega
        rcases h4 with h4 | h4 <;> rw [h4] at h2 <;> norm_num at h2
      have ht1 : 1 ≤ t := by
        rw [htdef]
        have h : 1 ≤ Fintype.card (D.S (P.natDegree - 1)) - 1 := by omega
        exact Nat.one_le_two_pow
      have htm : Fintype.card (D.I (P.natDegree - 1)) = 2 * t - 1 := by
        rw [card_I, htdef]
        have h : 2 * 2 ^ (Fintype.card (D.S (P.natDegree - 1)) - 1)
            = 2 ^ Fintype.card (D.S (P.natDegree - 1)) := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [h]
      obtain ⟨b, -, hcorner⟩ := petCornerZero (l := P.natDegree) D P.leadingCoeff N M Hδ Kc Ftop t γ
        htm ht1 hd2 hN1 hM1 hHδKc (hFs ⟨P.natDegree, Nat.lt_succ_self _⟩) hγ0
        (gamma_mul_le_sum_symIcc hN0 hFb hFs hΛ)
      refine ⟨b, fun _ _ => 0, ?_, ?_⟩
      · intro a ha i y hy
        rw [add_zero]
        exact shellBd a ha i y hy
      · -- the average bound
        have h2t : 2 * t = Fintype.card (D.I (P.natDegree - 1)) + 1 := by omega
        have hK₀2t : 2 * t ≤ K₀ := by rw [h2t]; exact hK₀corner
        have hLnn : (0 : ℝ) ≤ linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b (fun _ _ => 0) :=
          linFamAvg_nonneg D P.natDegree P.leadingCoeff N M Hδ Ftop b (fun _ _ => 0)
        have hCstBeq : (((2 * Kc + 1 : ℕ) : ℝ) ^ npar * 3 ^ (2 * t - 1)) = CstB := by
          rw [hCstBdef]
          congr 2
          omega
        calc γ ^ K₀ ≤ γ ^ (2 * t) := pow_le_pow_of_le_one hγ0.le hγ1 hK₀2t
          _ ≤ (((2 * Kc + 1 : ℕ) : ℝ) ^ npar * 3 ^ (2 * t - 1))
                * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b (fun _ _ => 0) := hcorner
          _ = CstB * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b (fun _ _ => 0) := by
              rw [hCstBeq]
          _ ≤ Cst₁ * linFamAvg D P.natDegree P.leadingCoeff N M Hδ Ftop b (fun _ _ => 0) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hLnn

  · -- ====================== the degenerate case `d ≤ 1` ======================
    unfold PetChapter5
    refine ⟨twoDatum, ?_, 1, 2, 1, le_rfl, by norm_num, le_rfl, ?_⟩
    · have h : P.natDegree - 1 = 0 := by omega
      rw [h]
      exact twoDatum_card_I_zero
    · intro A hA
      refine ⟨2, le_rfl, le_rfl, 1, le_rfl, le_rfl, 1, le_rfl, ?_, ?_⟩
      · have hA0 : (0 : ℝ) ≤ A := by linarith
        push_cast
        linarith
      · intro N M F γ δ' hdeg2
        exact absurd hdeg2 (by omega)

end

end Work.Peluse.UControl

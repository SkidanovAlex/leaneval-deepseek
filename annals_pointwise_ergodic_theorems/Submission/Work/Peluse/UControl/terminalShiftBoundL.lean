import Mathlib
import Submission.Work.Peluse.UControl.terminalShiftBound_of_coeffBd
import Submission.Work.Peluse.UControl.phase1TerminalCoeffBd

/-!
# The shift bound of the terminal state at an arbitrary range

`terminalShiftBound_of_coeffBd` proves `ShiftBound N M 1 (Cne · ⌈A⌉₊)` at the terminal state
`histTerminal P hd` of the phase-1 chain — i.e. for `|z| ≤ M`.  The level chain of
`PetLevelChain` consumes the *range* `c = Nstep + 1` (each PET step halves the range:
`PetState.ShiftBound.step`), so this file generalises the constant: for `|z| ≤ cM` the value of a
terminal slot polynomial is at most `Cs · c^d · ⌈A⌉₊ · N`.

The engine is the coefficient bound `coeffBd`: with `B = γM ≥ 1`, the `j`-th coefficient is at most
`C(γM)^{d-j}`, so `|Q(a,z)| ≤ Σ_{j<d} C(γM)^{d-j}(cM)^j ≤ d·C·c^{d-1}·γ·M^d ≤ d·C·c^{d-1}·A·N`,
using `M^d ≤ A γ⁻¹ N`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-- **The evaluation bound at range `c`.**  If every evaluated coefficient of `Q` is bounded by
`C·B^{d-j}` on the box `|a_s| ≤ B` (`coeffBd`), and `B = γM`, then on `|z| ≤ cM` the value of `Q`
is at most `d·C·c^{d-1}·γ·M^d`. -/
theorem absEval_le_of_coeffBd_range {n d : ℕ} (hd1 : 1 ≤ d) {C γ M : ℝ} {c : ℕ}
    {Q : Polynomial (MvPolynomial (Fin n) ℤ)} (hC : coeffBd d C Q) (hB : 1 ≤ γ * M)
    {a : Fin n → ℤ} (ha : ∀ s, |a s| ≤ γ * M) {z : ℤ} (hz : |z| ≤ (c : ℤ) * M)
    (hM0 : 0 ≤ M) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hc1 : 1 ≤ c)
    (hdeg : Q.natDegree ≤ d - 1) :
    (|(Polynomial.eval z (Q.map (MvPolynomial.eval a)) : ℤ)| : ℝ)
      ≤ (d : ℝ) * C * (c : ℝ) ^ (d - 1) * γ * M ^ d := by
  classical
  have hγM1 : 0 < γ * M := lt_of_lt_of_le zero_lt_one hB
  have hC0 : 0 ≤ C := by
    have h := hC (γ * M) hB a ha d
    rw [show d - d = 0 from Nat.sub_self d, pow_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  rw [show Polynomial.eval z (Q.map (MvPolynomial.eval a))
      = (Q.map (MvPolynomial.eval a)).eval z from rfl]
  set Qa : Polynomial ℤ := Q.map (MvPolynomial.eval a) with hQa
  have hdegQa : Qa.natDegree ≤ d - 1 := by
    rw [hQa]
    exact le_trans Polynomial.natDegree_map_le hdeg
  have hzR : ((|z| : ℤ) : ℝ) ≤ (c : ℝ) * M := by exact_mod_cast hz
  have hterm : ∀ i ∈ Finset.range d,
      |((Qa.coeff i : ℤ) : ℝ)| * |(z : ℝ)| ^ i ≤ C * γ * (c : ℝ) ^ (d - 1) * M ^ d := by
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    have hcoeff : |((Qa.coeff i : ℤ) : ℝ)| ≤ C * (γ * M) ^ (d - i) := by
      have h := hC (γ * M) hB a ha i
      rw [Int.norm_eq_abs] at h
      rw [hQa, Polynomial.coeff_map]
      exact h
    have hzi : |(z : ℝ)| ^ i ≤ ((c : ℝ) * M) ^ i := by
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ i
      calc |(z : ℝ)| = ((|z| : ℤ) : ℝ) := (Int.cast_abs).symm
        _ ≤ (c : ℝ) * M := hzR
    have hgam : γ ^ (d - i) ≤ γ := by
      have h1 : γ ^ (d - i) ≤ γ ^ 1 :=
        pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 (by omega)
      simpa using h1
    have hci : (c : ℝ) ^ i ≤ (c : ℝ) ^ (d - 1) :=
      pow_le_pow_right₀ hcR (by omega)
    have hMd : M ^ (d - i) * M ^ i = M ^ d := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hid)]
    have hsplit : (γ * M) ^ (d - i) * ((c : ℝ) * M) ^ i
        = (γ ^ (d - i) * (c : ℝ) ^ i) * M ^ d := by
      calc (γ * M) ^ (d - i) * ((c : ℝ) * M) ^ i
          = (γ ^ (d - i) * M ^ (d - i)) * ((c : ℝ) ^ i * M ^ i) := by
            rw [mul_pow, mul_pow]
        _ = (γ ^ (d - i) * (c : ℝ) ^ i) * (M ^ (d - i) * M ^ i) := by ring
        _ = (γ ^ (d - i) * (c : ℝ) ^ i) * M ^ d := by rw [hMd]
    have h2 : γ ^ (d - i) * (c : ℝ) ^ i ≤ γ * (c : ℝ) ^ (d - 1) :=
      mul_le_mul hgam hci (by positivity) (le_of_lt hγ0)
    have hstep : (γ * M) ^ (d - i) * ((c : ℝ) * M) ^ i
        ≤ γ * (c : ℝ) ^ (d - 1) * M ^ d := by
      rw [hsplit]
      calc (γ ^ (d - i) * (c : ℝ) ^ i) * M ^ d
          ≤ (γ * (c : ℝ) ^ (d - 1)) * M ^ d :=
            mul_le_mul_of_nonneg_right h2 (pow_nonneg hM0 d)
        _ = γ * (c : ℝ) ^ (d - 1) * M ^ d := by ring
    calc |((Qa.coeff i : ℤ) : ℝ)| * |(z : ℝ)| ^ i
        ≤ (C * (γ * M) ^ (d - i)) * ((c : ℝ) * M) ^ i :=
          mul_le_mul hcoeff hzi (pow_nonneg (abs_nonneg _) i)
            (mul_nonneg hC0 (pow_nonneg (le_of_lt hγM1) _))
      _ = C * ((γ * M) ^ (d - i) * ((c : ℝ) * M) ^ i) := by ring
      _ ≤ C * (γ * (c : ℝ) ^ (d - 1) * M ^ d) := mul_le_mul_of_nonneg_left hstep hC0
      _ = C * γ * (c : ℝ) ^ (d - 1) * M ^ d := by ring
  have hmain : (|(Qa.eval z : ℤ)| : ℝ)
      ≤ ∑ i ∈ Finset.range d, C * γ * (c : ℝ) ^ (d - 1) * M ^ d := by
    have hcast : ((Qa.eval z : ℤ) : ℝ)
        = ∑ i ∈ Finset.range (Qa.natDegree + 1), ((Qa.coeff i : ℤ) : ℝ) * (z : ℝ) ^ i := by
      have h := Polynomial.eval_eq_sum_range (p := Qa) (x := z)
      have h' := congrArg (fun t : ℤ => (t : ℝ)) h
      push_cast at h'
      exact h'
    calc (|(Qa.eval z : ℤ)| : ℝ) = |((Qa.eval z : ℤ) : ℝ)| := rfl
      _ ≤ ∑ i ∈ Finset.range (Qa.natDegree + 1),
            |((Qa.coeff i : ℤ) : ℝ)| * |(z : ℝ)| ^ i := by
          rw [hcast]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
          intro i _
          rw [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ Finset.range d, C * γ * (c : ℝ) ^ (d - 1) * M ^ d := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Finset.sum_le_sum ?_)
          · intro i hi
            simp only [Finset.mem_range] at hi ⊢
            omega
          · intro i _ _
            exact mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)
          · intro i hi
            exact hterm i hi
  have hfinal : ∑ i ∈ Finset.range d, C * γ * (c : ℝ) ^ (d - 1) * M ^ d
      = (d : ℝ) * C * (c : ℝ) ^ (d - 1) * γ * M ^ d := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hfinal] at hmain
  exact hmain

/-- **The shift bound of the terminal state at range `c`.** -/
theorem terminalShiftBoundL (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ Cs : ℕ, 1 ≤ Cs ∧ ∀ (N M c : ℕ) (A γ γ' : ℝ),
      1 ≤ N → 1 ≤ A → 0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 → γ' ≤ γ →
      1 ≤ (M : ℝ) * γ → (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) → 1 ≤ c →
      ∀ (G : ((histTerminal P hd).toSym).S.ι → ℤ → ℂ)
        (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat ((histTerminal P hd).toSym).nv → ℤ → ℂ),
      (histPet (histTerminal P hd) ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound N M c
        (Cs * c ^ P.natDegree * ⌈A⌉₊) := by
  have hd1 : 1 ≤ P.natDegree := by omega
  obtain ⟨C, hC1, hcoeff⟩ := phase1TerminalCoeffBd P hd
  have hP0 : P ≠ 0 := by
    intro h0; rw [h0] at hd; simp at hd
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hphase := histTerminal_phase1Terminal P hd hlc
  have hdeg : ∀ x ∈ (histTerminal P hd).H,
      ((histTerminal P hd).Q x.1 x.2).natDegree ≤ P.natDegree - 1 :=
    fun x hx => le_of_eq (hphase.1 x hx).2.2.1
  set Cs : ℕ := max 1 ⌈C * (P.natDegree : ℝ)⌉₊ with hCsDef
  refine ⟨Cs, ?_, ?_⟩
  · rw [hCsDef]; exact le_max_left _ _
  · intro N M c A γ γ' hN1 hA1 hγ0 hγ1 hγ'0 hγ'1 hγ'γ hMγ hMd hc1 G g
    have hB : 1 ≤ γ * (M : ℝ) := by rw [mul_comm]; exact hMγ
    have hHreal : ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) ≤ γ * (M : ℝ) := by
      have h1 : ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) ≤ γ' * (M : ℝ) :=
        floor_toNat_le_of_nonneg (by positivity)
      have h2 : γ' * (M : ℝ) ≤ γ * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hγ'γ (by positivity)
      linarith
    refine (hstSlotsBound_toPetP ((histTerminal P hd).toSym).S G g).mpr ?_
    intro a i z hz
    set Q : Polynomial (MvPolynomial (Fin ((histTerminal P hd).toSym.nv)) ℤ) :=
      ((histTerminal P hd).toSym).S.P i with hQ
    set ap : Fin ((histTerminal P hd).toSym.nv) → ℤ :=
      WinTower.param ⌊γ' * (M : ℝ)⌋.toNat ((histTerminal P hd).toSym.nv) a with hap
    set x : ℤ := Polynomial.eval z (Q.map (MvPolynomial.eval ap)) with hx
    have hzR : ((|z| : ℤ) : ℝ) ≤ (c : ℝ) * (M : ℝ) := by
      have h : |z| ≤ (c : ℤ) * (M : ℤ) := hz
      exact_mod_cast h
    have ha : ∀ s, |ap s| ≤ γ * (M : ℝ) := by
      intro s
      rw [hap]
      have h1 : ((|WinTower.param ⌊γ' * (M : ℝ)⌋.toNat
            ((histTerminal P hd).toSym.nv) a s| : ℤ) : ℝ)
          ≤ ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℝ) := by
        exact_mod_cast WinTower.param_abs_le ⌊γ' * (M : ℝ)⌋.toNat
          ((histTerminal P hd).toSym.nv) a s
      linarith
    have hq : coeffBd P.natDegree C Q := by rw [hQ]; exact hcoeff i.1 i.2
    have hqd : Q.natDegree ≤ P.natDegree - 1 := by rw [hQ]; exact hdeg i.1 i.2
    have hmain : |(x : ℝ)| ≤ (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1)
        * γ * (M : ℝ) ^ P.natDegree := by
      rw [hx]
      exact absEval_le_of_coeffBd_range hd1 hq hB ha hzR (by positivity) hγ0 hγ1 hc1 hqd
    have hnonneg : 0 ≤ (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity))
        (le_of_lt hγ0)
    have hstep1 : (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ
          * (M : ℝ) ^ P.natDegree
        ≤ (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ
          * (A * γ⁻¹ * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hMd hnonneg
    have hcancel : γ * (A * γ⁻¹ * (N : ℝ)) = A * (N : ℝ) := by field_simp
    have hstep2 : (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ
          * (A * γ⁻¹ * (N : ℝ))
        = (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * A * (N : ℝ) := by
      rw [show (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ
            * (A * γ⁻¹ * (N : ℝ))
          = (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1)
            * (γ * (A * γ⁻¹ * (N : ℝ))) by ring, hcancel]
      ring
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hpow : (c : ℝ) ^ (P.natDegree - 1) ≤ (c : ℝ) ^ P.natDegree :=
      pow_le_pow_right₀ hcR (by omega)
    have hdcC : (P.natDegree : ℝ) * C ≤ (Cs : ℝ) := by
      have h1 : ⌈C * (P.natDegree : ℝ)⌉₊ ≤ Cs := by rw [hCsDef]; exact le_max_right _ _
      have h2 : C * (P.natDegree : ℝ) ≤ (⌈C * (P.natDegree : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : C * (P.natDegree : ℝ) ≤ (Cs : ℝ) := le_trans h2 (by exact_mod_cast h1)
      simpa [mul_comm] using h3
    have hstep3 : (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * A * (N : ℝ)
        ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) * (N : ℝ) := by
      have hdCd : (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * A
          ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) := by
        have h1 : (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * A
            ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree * A := by
          have h2 : (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1)
              ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree := by
            calc (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1)
                ≤ (Cs : ℝ) * (c : ℝ) ^ (P.natDegree - 1) :=
                  mul_le_mul_of_nonneg_right hdcC (by positivity)
              _ ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree :=
                  mul_le_mul_of_nonneg_left hpow (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (by linarith)
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left (Nat.le_ceil A) (by positivity)
      exact mul_le_mul_of_nonneg_right hdCd (by positivity)
    have hfin : |(x : ℝ)| ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) * (N : ℝ) := by
      calc |(x : ℝ)|
          ≤ (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ
              * (M : ℝ) ^ P.natDegree := hmain
        _ ≤ (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * γ
              * (A * γ⁻¹ * (N : ℝ)) := hstep1
        _ = (P.natDegree : ℝ) * C * (c : ℝ) ^ (P.natDegree - 1) * A * (N : ℝ) := hstep2
        _ ≤ (Cs : ℝ) * (c : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) * (N : ℝ) := hstep3
    have hgoalR : (((|x| : ℤ) : ℝ)
        ≤ ((((Cs * c ^ P.natDegree * ⌈A⌉₊ : ℕ) : ℤ) * (N : ℤ)) : ℝ)) := by
      have hx' : ((|x| : ℤ) : ℝ) = |(x : ℝ)| := Int.cast_abs
      rw [hx']
      have hR : ((((Cs * c ^ P.natDegree * ⌈A⌉₊ : ℕ) : ℤ) * (N : ℤ)) : ℝ)
          = (Cs : ℝ) * (c : ℝ) ^ P.natDegree * (⌈A⌉₊ : ℝ) * (N : ℝ) := by
        push_cast
        ring
      rw [hR]
      exact hfin
    exact_mod_cast hgoalR

end

end Work.Peluse.UControl

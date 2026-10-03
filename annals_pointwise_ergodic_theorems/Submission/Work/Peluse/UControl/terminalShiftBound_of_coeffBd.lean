import Mathlib
import Submission.Work.Peluse.UControl.petShiftDefs
import Submission.Work.Peluse.UControl.histCloseLinkWin

/-!
# The sharp shift bound at the terminal state of the phase-1 chain

`Work.Peluse.UControl.histTerminal P hd` is the state reached by the phase-1 chain of `P` after
the closing step (Peluse's Lemma 4.5).  Its live slots are the `(P, h)` with `h ≠ 0`, of `y`-degree
`d - 1` and leading coefficient `C d · C (lc P) · shift h` (`Phase1Terminal`, `HistPhase1.lean`).

This file proves that the *coefficient bound* `coeffBd d C Q` at the terminal state implies the
*sharp shift bound* `ShiftBound N M 1 (Cne · ⌈A⌉₊)` — i.e. `|Q i a z| ≤ Cne · ⌈A⌉₊ · N` for
`|z| ≤ M` — whenever

* `1 ≤ M γ` and `M^d ≤ A γ⁻¹ N` (`γ` is the correlation scale of the chain, §5 of the paper);

the constant is `Cne = max 1 ⌈C d⌉₊`, independent of `A`, `N`, `M`.

The engine is the coefficient bound: with `B = γM ≥ 1` the box condition `|a_s| ≤ γM` is met, so
`|Q_j(a)| ≤ C B^{d-j}`, and since `natDegree Q = d - 1` the value of `Q` at `|z| ≤ M` is at most
`C Σ_{j<d} (γM)^{d-j} M^j = C M^d Σ_{j<d} γ^{d-j} ≤ C d γ M^d ≤ C d A N` using `M^d ≤ A γ⁻¹ N`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-! ## Elementary auxiliary facts -/

/-- For `x ≥ 0` the natural value of the floor is at most `x`. -/
lemma floor_toNat_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ x := by
  have h0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have h1 : ((⌊x⌋.toNat : ℤ) : ℝ) ≤ x := by
    rw [Int.toNat_of_nonneg h0]
    exact Int.floor_le x
  exact h1

/-- Every coordinate of `WinTower.param H n a` is a window position, hence bounded by `H`. -/
theorem WinTower.param_abs_le (H : ℕ) : ∀ n (a : WinTower H n) (j : Fin n),
    |WinTower.param H n a j| ≤ (H : ℤ) := by
  intro n
  induction n with
  | zero => intro a j; exact j.elim0
  | succ n ih =>
    intro a j
    obtain ⟨a', k⟩ := a
    refine Fin.lastCases ?_ ?_ j
    · rw [WinTower.param_last]
      exact abs_le.mpr (PetStep.winVal_mem H k)
    · intro i
      rw [WinTower.param_castSucc]
      exact ih a' i

/-! ## The coefficient bound implies the pointwise bound -/

/-- **The evaluation bound.**  If every evaluated coefficient of `Q` is bounded by
`C · B^{d-j}` on the box `|a_s| ≤ B` (`coeffBd`), and `B = γM`, then on `|z| ≤ M` the value of `Q`
is at most `d · C · γ · M^d`. -/
theorem absEval_le_of_coeffBd {n d : ℕ} (hd1 : 1 ≤ d) {C γ M : ℝ}
    {Q : Polynomial (MvPolynomial (Fin n) ℤ)} (hC : coeffBd d C Q) (hB : 1 ≤ γ * M)
    {a : Fin n → ℤ} (ha : ∀ s, |a s| ≤ γ * M) {z : ℤ} (hz : |z| ≤ M)
    (hM0 : 0 ≤ M) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hdeg : Q.natDegree ≤ d - 1) :
    (|(Polynomial.eval z (Q.map (MvPolynomial.eval a)) : ℤ)| : ℝ) ≤ (d : ℝ) * C * γ * M ^ d := by
  classical
  have hγM1 : 0 < γ * M := lt_of_lt_of_le zero_lt_one hB
  have hC0 : 0 ≤ C := by
    have h := hC (γ * M) hB a ha d
    rw [show d - d = 0 from Nat.sub_self d, pow_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  rw [show Polynomial.eval z (Q.map (MvPolynomial.eval a))
      = (Q.map (MvPolynomial.eval a)).eval z from rfl]
  set Qa : Polynomial ℤ := Q.map (MvPolynomial.eval a) with hQa
  have hdegQa : Qa.natDegree ≤ d - 1 := by
    rw [hQa]
    exact le_trans Polynomial.natDegree_map_le hdeg
  have hterm : ∀ i ∈ Finset.range d,
      |((Qa.coeff i : ℤ) : ℝ)| * |(z : ℝ)| ^ i ≤ C * γ * M ^ d := by
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    have hcoeff : |((Qa.coeff i : ℤ) : ℝ)| ≤ C * (γ * M) ^ (d - i) := by
      have h := hC (γ * M) hB a ha i
      rw [Int.norm_eq_abs] at h
      rw [hQa, Polynomial.coeff_map]
      exact h
    have hzi : |(z : ℝ)| ^ i ≤ M ^ i := by
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ i
      rw [← Int.cast_abs]
      exact hz
    have hgam : γ ^ (d - i) ≤ γ := by
      have h1 : γ ^ (d - i) ≤ γ ^ 1 :=
        pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 (by omega)
      simpa using h1
    have hkey : (γ * M) ^ (d - i) * M ^ i = γ ^ (d - i) * M ^ d := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt hid)]
    have hstep : (γ * M) ^ (d - i) * M ^ i ≤ γ * M ^ d := by
      rw [hkey]
      exact mul_le_mul_of_nonneg_right hgam (pow_nonneg hM0 d)
    calc |((Qa.coeff i : ℤ) : ℝ)| * |(z : ℝ)| ^ i
        ≤ (C * (γ * M) ^ (d - i)) * M ^ i :=
          mul_le_mul hcoeff hzi (pow_nonneg (abs_nonneg _) i)
            (mul_nonneg hC0 (pow_nonneg (le_of_lt hγM1) _))
      _ = C * ((γ * M) ^ (d - i) * M ^ i) := by ring
      _ ≤ C * (γ * M ^ d) := mul_le_mul_of_nonneg_left hstep hC0
      _ = C * γ * M ^ d := by ring
  have hmain : (|(Qa.eval z : ℤ)| : ℝ) ≤ ∑ i ∈ Finset.range d, C * γ * M ^ d := by
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
      _ ≤ ∑ i ∈ Finset.range d, C * γ * M ^ d := by
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Finset.sum_le_sum ?_)
          · intro i hi
            simp only [Finset.mem_range] at hi ⊢
            omega
          · intro i _ _
            exact mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)
          · intro i hi
            exact hterm i hi
  have hfinal : ∑ i ∈ Finset.range d, C * γ * M ^ d = (d : ℝ) * C * γ * M ^ d := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hfinal] at hmain
  exact hmain

/-! ## The sharp shift bound -/

theorem terminalShiftBound_of_coeffBd (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C : ℝ) (hC : 1 ≤ C)
    (hcoeff : ∀ x ∈ (Work.Peluse.UControl.histTerminal P hd).H,
      Work.Peluse.UControl.coeffBd P.natDegree C ((Work.Peluse.UControl.histTerminal P hd).Q x.1 x.2)) :
    ∃ Cne : ℕ, 1 ≤ Cne ∧ ∀ (N M : ℕ) (A γ γ' : ℝ),
      1 ≤ N → 1 ≤ A → 0 < γ → γ ≤ 1 → 0 < γ' → γ' ≤ 1 → γ' ≤ γ →
      1 ≤ (M : ℝ) * γ → (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) →
      ∀ (G : ((Work.Peluse.UControl.histTerminal P hd).toSym).S.ι → ℤ → ℂ)
        (g : Work.Peluse.UControl.WinTower ⌊γ' * (M : ℝ)⌋.toNat
              (Work.Peluse.UControl.histTerminal P hd).toSym.nv → ℤ → ℂ),
      (Work.Peluse.UControl.histPet (Work.Peluse.UControl.histTerminal P hd)
          ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound N M 1 (Cne * ⌈A⌉₊) := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hP0 : P ≠ 0 := by
    intro h
    rw [h] at hd
    simp at hd
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hphase := histTerminal_phase1Terminal P hd hlc
  have hdeg : ∀ x ∈ (histTerminal P hd).H,
      ((histTerminal P hd).Q x.1 x.2).natDegree ≤ P.natDegree - 1 :=
    fun x hx => le_of_eq (hphase.1 x hx).2.2.1
  set Cne : ℕ := max 1 ⌈C * (P.natDegree : ℝ)⌉₊ with hCneDef
  refine ⟨Cne, ?_, ?_⟩
  · rw [hCneDef]; exact le_max_left _ _
  · intro N M A γ γ' hN1 hA1 hγ0 hγ1 hγ'0 hγ'1 hγ'γ hMγ hMd G g
    have hB : 1 ≤ γ * ↑M := by rw [mul_comm]; exact hMγ
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
    have hzM : |z| ≤ (M : ℤ) := by simpa using hz
    have hzR : ((|z| : ℤ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hzM
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
    have hmain : |(x : ℝ)| ≤ (P.natDegree : ℝ) * C * γ * (M : ℝ) ^ P.natDegree := by
      rw [hx]
      exact absEval_le_of_coeffBd hd1 hq hB ha hzR (by positivity) hγ0 hγ1 hqd
    have hnonneg : 0 ≤ (P.natDegree : ℝ) * C * γ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (le_of_lt hγ0)
    have hstep1 : (P.natDegree : ℝ) * C * γ * (M : ℝ) ^ P.natDegree
        ≤ (P.natDegree : ℝ) * C * γ * (A * γ⁻¹ * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hMd hnonneg
    have hcancel : γ * (A * γ⁻¹ * (N : ℝ)) = A * (N : ℝ) := by
      field_simp
    have hstep2 : (P.natDegree : ℝ) * C * γ * (A * γ⁻¹ * (N : ℝ))
        = (P.natDegree : ℝ) * C * A * (N : ℝ) := by
      rw [show (P.natDegree : ℝ) * C * γ * (A * γ⁻¹ * (N : ℝ))
            = (P.natDegree : ℝ) * C * (γ * (A * γ⁻¹ * (N : ℝ))) by ring, hcancel]
      ring
    have hdcC : (P.natDegree : ℝ) * C ≤ (Cne : ℝ) := by
      have h1 : ⌈C * (P.natDegree : ℝ)⌉₊ ≤ Cne := by
        rw [hCneDef]; exact le_max_right _ _
      have h2 : C * (P.natDegree : ℝ) ≤ (⌈C * (P.natDegree : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : C * (P.natDegree : ℝ) ≤ (Cne : ℝ) := le_trans h2 (by exact_mod_cast h1)
      simpa [mul_comm] using h3
    have hstep3 : (P.natDegree : ℝ) * C * A * (N : ℝ)
        ≤ (Cne : ℝ) * (⌈A⌉₊ : ℝ) * (N : ℝ) := by
      have h1 : (P.natDegree : ℝ) * C * A ≤ (Cne : ℝ) * (⌈A⌉₊ : ℝ) :=
        mul_le_mul hdcC (Nat.le_ceil A) (le_trans zero_le_one hA1) (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hfin : |(x : ℝ)| ≤ (Cne : ℝ) * (⌈A⌉₊ : ℝ) * (N : ℝ) := by
      calc |(x : ℝ)| ≤ (P.natDegree : ℝ) * C * γ * (M : ℝ) ^ P.natDegree := hmain
        _ ≤ (P.natDegree : ℝ) * C * γ * (A * γ⁻¹ * (N : ℝ)) := hstep1
        _ = (P.natDegree : ℝ) * C * A * (N : ℝ) := hstep2
        _ ≤ (Cne : ℝ) * (⌈A⌉₊ : ℝ) * (N : ℝ) := hstep3
    have hgoalR : (((|x| : ℤ) : ℝ)
        ≤ ((((Cne * ⌈A⌉₊ : ℕ) : ℤ) * (N : ℤ)) : ℝ)) := by
      have hx' : ((|x| : ℤ) : ℝ) = |(x : ℝ)| := Int.cast_abs
      rw [hx']
      have hR : ((((Cne * ⌈A⌉₊ : ℕ) : ℤ) * (N : ℤ)) : ℝ)
          = (Cne : ℝ) * (⌈A⌉₊ : ℝ) * (N : ℝ) := by push_cast; ring
      rw [hR]
      exact hfin
    exact_mod_cast hgoalR
end

end Work.Peluse.UControl

import Mathlib
import Submission.Work.Peluse.UControl.PetChainSetup

/-!
# The invariant of the analytic PET chain

`PetState.lam_step` turns `γ ≤ lam C` into `γ²/2000 ≤ lam (C.step i₀ H)`; running it along the
combinatorial chain `SymState.chain` produces the analytic chain.  This file fixes the invariant
that is threaded along that chain (`PetInv`), the state after one link (`petNext`), and the
elementary facts about them (1-boundedness, support, the mass of `ν`).

The window data are: `N` and `M` (the scales), the *fixed* window radius `γ'` (all the steps use the
same window, the paper's `A_k = ((-γ'M, γ'M))^k`), the height `H = ⌊γ'M⌋`, the current shift constant
`D` and the current range constant `c`.  The *window condition* is
`γ' ≤ petChainLevel γ k ^ 2 / (20000 * (2^k * D + 1))` for every `k < chainLen X` (the *remaining*
chain length; the bound `k ≤ chainLen X` is essential: `petChainLevel γ k → 0` as `k → ∞`, so the
unbounded condition would force `γ' ≤ 0`).  The step at level `γ` needs it at `k = 0`, and it is
preserved by the passage `(γ, D) ↦ (petChainLevel γ 1, 2D)` because the level after one more step is
`petChainLevel γ 1`, the shift bound doubles, and `chainLen (stepMin X _) = chainLen X - 1`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

/-- The invariant of the analytic PET chain at the symbolic state `X`: the window data, the
boundedness and support of the base and slot functions, the correlation bound `γ ≤ lam` and the
shift bound `ShiftBound N M c D`, together with the window condition for every step count. -/
structure PetInv {d : ℕ} (N M : ℕ) (γ' : ℝ) (X : SymState d)
    (F : (SymState.dropC X).S.ι → ℤ → ℂ) (f : WinTower ⌊γ' * (M : ℝ)⌋.toNat X.nv → ℤ → ℂ)
    (γ : ℝ) (D c : ℕ) : Prop where
  hN : 0 < N
  hM : 0 < M
  hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat
  hγ'0 : 0 < γ'
  hγ'1 : γ' ≤ 1
  hγ0 : 0 < γ
  hγ1 : γ ≤ 1
  hc : chainLen X + 1 ≤ c
  hD : 1 ≤ D
  hFb : ∀ i x, ‖F i x‖ ≤ 1
  hFs : ∀ i, SupportIn (F i) N
  hfb : ∀ a x, ‖f a x‖ ≤ 1
  hfs : ∀ a, SupportIn (f a) N
  hlam : γ ≤ ((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.lam N M
  hSB : ((SymState.dropC X).S.toPetP ⌊γ' * (M : ℝ)⌋.toNat F f).toState.ShiftBound N M c D
  hw : ∀ k : ℕ, k < chainLen X →
    γ' ≤ petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1))

/-- The slot functions of the state after one link of the chain: the `stepF` of the old ones,
restricted to the slots that are not dropped. -/
noncomputable def petNextF {d : ℕ} (X : SymState d)
    (hE : (Finset.univ : Finset (SymState.dropC X).S.ι).Nonempty)
    (F : (SymState.dropC X).S.ι → ℤ → ℂ) :
    (SymState.dropC (SymState.stepMin X hE)).S.ι → ℤ → ℂ :=
  toPetP_stepF (SymState.dropC X).S (SymState.minSlot X hE) F (SymState.consts (SymState.stepMin X hE))

/-- The base function of the state after one link of the chain. -/
noncomputable def petNextf {d : ℕ} (X : SymState d)
    (hE : (Finset.univ : Finset (SymState.dropC X).S.ι).Nonempty) (H : ℕ)
    (F : (SymState.dropC X).S.ι → ℤ → ℂ) (f : WinTower H X.nv → ℤ → ℂ) :
    WinTower H (X.nv + 1) → ℤ → ℂ :=
  toPetP_stepf (SymState.dropC X).S (SymState.minSlot X hE) H F f
    (SymState.consts (SymState.stepMin X hE))

/-! ## Elementary facts about the next state -/

lemma stepF_bdd {ι : Type*} (F : ι → ℤ → ℂ) (hF : ∀ i x, ‖F i x‖ ≤ 1) (j : ι × Bool) :
    ∀ x, ‖stepF F j x‖ ≤ 1 := by
  intro x
  rw [stepF]
  split
  · simpa using hF j.1 x
  · simpa using hF j.1 x

lemma stepF_supp {ι : Type*} (F : ι → ℤ → ℂ) {N : ℕ} (hF : ∀ i, SupportIn (F i) N)
    (j : ι × Bool) : SupportIn (stepF F j) N := by
  intro x hx
  rw [stepF]
  split
  · simp [hF j.1 x hx]
  · exact hF j.1 x hx

lemma toPetP_stepF_bdd {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (F : S.ι → ℤ → ℂ)
    (J : Finset (S.step i₀).ι) (hF : ∀ i x, ‖F i x‖ ≤ 1) :
    ∀ i x, ‖toPetP_stepF S i₀ F J i x‖ ≤ 1 := by
  intro i x
  rw [toPetP_stepF_apply]
  exact stepF_bdd F hF i.1.1 x

lemma toPetP_stepF_supp {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (F : S.ι → ℤ → ℂ)
    (J : Finset (S.step i₀).ι) {N : ℕ} (hF : ∀ i, SupportIn (F i) N) :
    ∀ i, SupportIn (toPetP_stepF S i₀ F J i) N := by
  intro i
  rw [toPetP_stepF_apply]
  exact stepF_supp F hF i.1.1

lemma toPetP_stepf_bdd {n H : ℕ} (S : PetStateSym n) (i₀ : S.ι) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (J : Finset (S.step i₀).ι)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) :
    ∀ a x, ‖toPetP_stepf S i₀ H F f J a x‖ ≤ 1 := by
  intro a x
  have h1 : ((S.toPetP H F f).step i₀ H).f a x = F i₀ x := rfl
  have h2 : (((S.toPetP H F f).step i₀ H).drop J).f a x
      = ((S.toPetP H F f).step i₀ H).f a x
        * ∏ i ∈ J, ((S.toPetP H F f).step i₀ H).F i
            (x + (((S.toPetP H F f).step i₀ H).P i a).eval 0) := rfl
  rw [toPetP_stepf, h2, h1, norm_mul]
  refine le_trans (mul_le_mul (hF i₀ x) (Finset.norm_prod_le _ _) (norm_nonneg _) zero_le_one) ?_
  rw [one_mul]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [show ((S.toPetP H F f).step i₀ H).F i = fun y => stepF F i.1 y from rfl]
  exact stepF_bdd F hF i.1 _

lemma toPetP_stepf_supp {n H : ℕ} (S : PetStateSym n) (i₀ : S.ι) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (J : Finset (S.step i₀).ι)
    {N : ℕ} (hF : ∀ i, SupportIn (F i) N) :
    ∀ a, SupportIn (toPetP_stepf S i₀ H F f J a) N := by
  intro a x hx
  have h2 : (((S.toPetP H F f).step i₀ H).drop J).f a x
      = ((S.toPetP H F f).step i₀ H).f a x
        * ∏ i ∈ J, ((S.toPetP H F f).step i₀ H).F i
            (x + (((S.toPetP H F f).step i₀ H).P i a).eval 0) := rfl
  rw [toPetP_stepf, h2]
  rw [show ((S.toPetP H F f).step i₀ H).f a x = F i₀ x from rfl, hF i₀ x hx, zero_mul]

lemma PetStateP.drop_sum_nu (S : PetStateP) (J : Finset S.ι) :
    ∑ a : (S.drop J).Ω, (S.drop J).ν a = ∑ a : S.Ω, S.ν a := Finset.sum_congr rfl (fun a _ => rfl)

lemma PetStateP.step_nu_sum {S : PetStateP} (i₀ : S.ι) {H : ℕ} (hH : 1 ≤ H)
    (h1 : ∑ a : S.Ω, S.ν a = 1) : ∑ a : (S.step i₀ H).Ω, (S.step i₀ H).ν a = 1 := by
  have := PetState.sum_step_ν S.toState i₀ hH h1
  exact this

lemma PetStateP.step_nu_nonneg {S : PetStateP} (i₀ : S.ι) {H : ℕ} (h0 : ∀ a, 0 ≤ S.ν a) :
    ∀ a, 0 ≤ (S.step i₀ H).ν a := by
  intro a
  exact mul_nonneg (h0 a.1) (Work.Peluse.PET.pet_muL_nonneg H _)

lemma PetStateP.drop_nu_nonneg {S : PetStateP} (J : Finset S.ι) (h0 : ∀ a, 0 ≤ S.ν a) :
    ∀ a, 0 ≤ (S.drop J).ν a := fun a => h0 a

end

end Work.Peluse.UControl

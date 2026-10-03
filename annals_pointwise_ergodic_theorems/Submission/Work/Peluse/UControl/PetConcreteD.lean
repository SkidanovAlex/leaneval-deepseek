import Mathlib
import Submission.Work.Peluse.UControl.petSymDropWeight
import Submission.Work.Peluse.UControl.petWinTowerSumNu

/-!
# The concrete polynomial PET state attached to a symbolic state

`PetStateSym.toPet` (`PetConcrete.lean`) attaches to a symbolic state `S` a concrete `PetState`
whose parameters are the points of the window tower `WinTower H n`, whose shifts are the slot
polynomials evaluated at the tower point, and whose weights are the tower weights.  This file
generalises it in the two ways the *chain* needs:

* the result is a `PetStateP` (the state carrying its shift *polynomials*), so that the constant
  slots can be dropped with `PetStateP.drop`, and so that the shift identity is a polynomial
  identity;
* the base function may depend on the parameter (the chain's base function is `F_{i₀}` times the
  product of the *constant* slots of the new state, and the constant term of a slot polynomial
  depends on the parameter).

The main content is `toPetP_step_P` (the shift polynomials of the stepped symbolic state are those
of `PetStateP.step`) and `toPetP_step_lam`, plus the dropped version `toPetP_stepDrop_lam` and the
transfers of the shift bound (`toPetP_step_SB`).  The parameter types
`WinTower H (n+1) = WinTower H n × Fin (2*H+1)`, the weights `WinTower.nu` and the slot functions
`stepF` are the same on the two sides *by definition*.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl.PetStep

noncomputable section

open Work.Peluse.UControl

/-- The concrete polynomial state attached to a symbolic state, with an `a`-dependent base
function. -/
def PetStateSym.toPetP {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) : PetStateP where
  Ω := WinTower H n
  ι := S.ι
  finΩ := inferInstance
  decΩ := inferInstance
  finι := S.finι
  decι := S.decι
  P := fun i a => (S.P i).map (MvPolynomial.eval (WinTower.param H n a))
  f := f
  F := F
  ν := fun a => WinTower.nu H n a

@[simp] lemma PetStateSym.toPetP_P {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (i : S.ι) (a : WinTower H n) :
    (S.toPetP H F f).P i a = (S.P i).map (MvPolynomial.eval (WinTower.param H n a)) := rfl

@[simp] lemma PetStateSym.toPetP_F {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (i : S.ι) : (S.toPetP H F f).F i = F i := rfl

@[simp] lemma PetStateSym.toPetP_f {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) : (S.toPetP H F f).f = f := rfl

@[simp] lemma PetStateSym.toPetP_nu {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (a : WinTower H n) : (S.toPetP H F f).ν a = WinTower.nu H n a := rfl

/-- The slot functions of the state obtained by stepping and dropping. -/
def toPetP_stepF {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (F : S.ι → ℤ → ℂ)
    (J : Finset (S.step i₀).ι) : (Work.Peluse.UControl.PetStateSym.dropSym (S.step i₀) J).ι → ℤ → ℂ :=
  fun i => stepF F i.1.1

lemma toPetP_stepF_apply {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (F : S.ι → ℤ → ℂ)
    (J : Finset (S.step i₀).ι) (i : (Work.Peluse.UControl.PetStateSym.dropSym (S.step i₀) J).ι) :
    toPetP_stepF S i₀ F J i = stepF F i.1.1 := rfl

/-- The base function of the state obtained by stepping and dropping. -/
def toPetP_stepf {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (J : Finset (S.step i₀).ι) :
    WinTower H (n + 1) → ℤ → ℂ :=
  fun a x => (((S.toPetP H F f).step i₀ H).drop J).f a x

/-- **The shift identity of the PET step, as a polynomial identity.** -/
theorem toPetP_step_P_pair {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (j : (S.step i₀).ι)
    (a : WinTower H n) (k : Fin (2 * H + 1)) :
    (((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).P j (a, k))
      = ((S.toPetP H F f).step i₀ H).P j (a, k) := by
  have hv : (MvPolynomial.eval (WinTower.param H (n + 1) (a, k)) :
        MvPolynomial (Fin (n + 1)) ℤ →+* ℤ).comp
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom
      = (MvPolynomial.eval (WinTower.param H n a) : MvPolynomial (Fin n) ℤ →+* ℤ) := by
    have hv' : (WinTower.param H (n + 1) (a, k)) ∘ Fin.castSucc = WinTower.param H n a := by
      funext i
      exact WinTower.param_castSucc H n a k i
    refine RingHom.ext fun q => ?_
    show MvPolynomial.eval (WinTower.param H (n + 1) (a, k)) (MvPolynomial.rename Fin.castSucc q)
        = MvPolynomial.eval (WinTower.param H n a) q
    rw [MvPolynomial.eval_rename, hv']
  have hc : (MvPolynomial.eval (WinTower.param H (n + 1) (a, k)))
      (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℤ) = PetStep.winVal H k := by
    rw [MvPolynomial.eval_X]
    exact WinTower.param_last H n a k
  simp only [PetStateSym.toPetP, PetStateSym.step, PetStateP.step]
  rw [Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_map, hv, Polynomial.map_map, hv,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  congr 1
  by_cases h : j.1.2 = true <;> simp [h, hc]

/-- The shift identity at an arbitrary tower parameter. -/
theorem toPetP_step_P {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (j : (S.step i₀).ι) (a : WinTower H (n + 1)) :
    ((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).P j a
      = ((S.toPetP H F f).step i₀ H).P j a :=
  toPetP_step_P_pair S i₀ H F f j a.1 a.2

/-- The `Q` of `PetStateP.step` is the `Q` of `PetState.step`, pointwise. -/
lemma PetStateP.step_toState_Q (S : PetStateP) (i₀ : S.ι) (H : ℕ) (j : (S.step i₀ H).ι)
    (a : S.Ω × Fin (2 * H + 1)) (y : ℤ) :
    (S.step i₀ H).toState.Q j a y = (S.toState.step i₀ H).Q j a y := by
  simp only [PetStateP.step, PetState.step, PetStateP.toState, PetStep.stepQ,
    Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  by_cases h : (j.1).2 = true <;> simp [h]

/-- The shift bound transfers from `PetState.toState.step` to `PetStateP.step`. -/
lemma PetStateP.step_ShiftBound (S : PetStateP) (i₀ : S.ι) (H N M c D : ℕ)
    (h : (S.toState.step i₀ H).ShiftBound N M c D) :
    (S.step i₀ H).toState.ShiftBound N M c D := by
  intro j a z hz
  rw [PetStateP.step_toState_Q S i₀ H j a z]
  exact h j a z hz

/-- The shift bound transfers to the concrete state of the stepped symbolic state. -/
theorem toPetP_step_SB {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) {N M c D : ℕ}
    (h : ((S.toPetP H F f).toState.step i₀ H).ShiftBound N M c D) :
    ((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).toState.ShiftBound
      N M c D := by
  intro j a z hz
  have h1 : ((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).toState.Q j a z
      = ((S.toPetP H F f).step i₀ H).toState.Q j a z := by
    show (((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).P j a).eval z
        = ((((S.toPetP H F f).step i₀ H).P j a)).eval z
    rw [toPetP_step_P S i₀ H F f j a]
  rw [h1]
  exact PetStateP.step_ShiftBound (S.toPetP H F f) i₀ H N M c D h j a z hz

/-- **The `lam` identity of the PET step** (before the constant slots are dropped). -/
theorem toPetP_step_lam {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H N M : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) :
    ((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).lam N M
      = ((S.toPetP H F f).step i₀ H).lam N M := by
  classical
  unfold PetStateP.lam
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hν : ((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).ν a
      = ((S.toPetP H F f).step i₀ H).ν a := rfl
  rw [hν]
  refine congrArg (fun t : ℝ => ((S.toPetP H F f).step i₀ H).ν a * t) ?_
  refine congrArg (fun z : ℂ => ‖z‖) ?_
  refine congrArg (fun z : ℂ => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
  refine tsum_congr (fun x => ?_)
  refine congrArg (fun z : ℂ => ((S.toPetP H F f).step i₀ H).f a x * z) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [toPetP_step_P S i₀ H F f j a]
  rfl

/-- **The `lam` identity of the PET step, after dropping the constant slots.** -/
theorem toPetP_stepDrop_lam {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H N M : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (J : Finset (S.step i₀).ι) :
    (((Work.Peluse.UControl.PetStateSym.dropSym (S.step i₀) J).toPetP H (toPetP_stepF S i₀ F J)
        (toPetP_stepf S i₀ H F f J)).lam N M)
      = (((S.toPetP H F f).step i₀ H).drop J).lam N M := by
  classical
  unfold PetStateP.lam
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hν : ((Work.Peluse.UControl.PetStateSym.dropSym (S.step i₀) J).toPetP H
        (toPetP_stepF S i₀ F J) (toPetP_stepf S i₀ H F f J)).ν a
      = ((((S.toPetP H F f).step i₀ H).drop J)).ν a := rfl
  rw [hν]
  refine congrArg (fun t : ℝ => ((((S.toPetP H F f).step i₀ H).drop J)).ν a * t) ?_
  refine congrArg (fun z : ℂ => ‖z‖) ?_
  refine congrArg (fun z : ℂ => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
  refine tsum_congr (fun x => ?_)
  refine congrArg (fun z : ℂ => ((((S.toPetP H F f).step i₀ H).drop J)).f a x * z) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [show (((Work.Peluse.UControl.PetStateSym.dropSym (S.step i₀) J).toPetP H
        (toPetP_stepF S i₀ F J) (toPetP_stepf S i₀ H F f J)).P j a)
      = ((S.step i₀).toPetP H (fun j x => stepF F j.1 x) (fun _ x => F i₀ x)).P j.1 a from rfl,
    toPetP_step_P S i₀ H F f j.1 a]
  rfl

/-- A polynomial whose degree is zero is constant. -/
lemma eval_eq_eval_zero_of_natDegree_eq_zero {p : Polynomial ℤ} (h : p.natDegree = 0) (y : ℤ) :
    p.eval y = p.eval 0 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero h]
  simp

/-- **The constancy hypothesis of the drop**: the slots of the *symbolic* state whose polynomial is
constant in `y` become `y`-constant polynomials in the concrete stepped state. -/
theorem toPetP_step_drop_hc {n : ℕ} (S : PetStateSym n) (i₀ : S.ι) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (J : Finset (S.step i₀).ι)
    (hJ : ∀ j ∈ J, ((S.step i₀).P j).natDegree = 0) :
    ∀ j ∈ J, ∀ a : WinTower H (n + 1), ∀ y : ℤ,
      (((S.toPetP H F f).step i₀ H).P j a).eval y
        = (((S.toPetP H F f).step i₀ H).P j a).eval 0 := by
  intro j hj a y
  rw [← toPetP_step_P S i₀ H F f j a]
  refine eval_eq_eval_zero_of_natDegree_eq_zero ?_ y
  exact le_antisymm (le_trans Polynomial.natDegree_map_le (le_of_eq (hJ j hj))) (Nat.zero_le _)

/-- The `ν` of the tower is a probability weight. -/
theorem toPetP_sum_nu {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (hH : 1 ≤ H) :
    (∑ a : WinTower H n, (S.toPetP H F f).ν a) = 1 :=
  WinTower.sum_nu H hH n

/-- The `ν` of the tower is nonnegative. -/
theorem toPetP_nu_nonneg {n : ℕ} (S : PetStateSym n) (H : ℕ) (F : S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) (a : WinTower H n) : 0 ≤ (S.toPetP H F f).ν a :=
  WinTower.nu_nonneg H n a

end

end Work.Peluse.UControl.PetStep

import Mathlib
import Submission.Work.Peluse.UControl.petStepAvgRepair
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The iterable PET step and the PET-state vocabulary

`Work.Peluse.UControl.petChapter5Holds` asks for `PetChapter5 P`, i.e. Peluse's Lemma 4.9
(`arXiv:1909.00309`, §4) for the configuration `(x, x+y, x+y², …, x+y^{d-1}, x+P(y))`,
`d = P.natDegree`.  Lemma 4.9 is obtained from `d-2` applications of Lemma 4.8 and one of Lemma 4.7,
each of which is an iteration of the "PET step" (Lemma 4.2).  The engine of one PET step is already
on disk and sorry-free (`Work.Peluse.UControl.petStepAvgRepair`, the averaged form of
`Work.Peluse.PET.pet_step`); this file supplies what a *chain* of steps needs:

* `petStepGen` — the same step, but with the *shift bound* stated on a range `|z| ≤ c·M` and with
  the extra conclusion that the shifts of the *next* state satisfy the same kind of bound (with
  `c ↦ c-1`, `D ↦ 2D`).  This is what makes the step iterable: the next state evaluates the old
  shifts at `y + εh`, `|h| ≤ H ≤ M`, i.e. at `y ∈ [1-M, 2M]`;
* `PetState` — the vocabulary of a state (`Q`, `f`, `F`, `ν`) together with its *correlation*
  `PetState.lam` and the *step* `PetState.step`.  `ΛMD N M P F` is the correlation of the initial
  state `(Ω = Unit, ι = Fin d ↦ (X^{i+1}, P), f = F_0, F i = F_{i+1}, ν = 1)`, so the PET chain of
  Lemma 4.9 is a chain of `PetState.step`s, and the final state's slots are linear in `y` with
  leading coefficients the datum's `A_{d-1}`.

`/tmp` is not writable in this sandbox: build logs go to `$PWD/.tmpdir`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl.PetStep

open Work.Peluse

/-! ## 1. The iterable PET step -/

/-- **The PET step with a range-aware shift bound.**  This is
`Work.Peluse.UControl.petStepAvgRepair` with the hypothesis `|Q i a z| ≤ D·N` recorded on the range
`|z| ≤ c·M` (rather than `z ∈ [1,M]`), together with the conclusion that the shifts of the *next*
state satisfy the same kind of bound on the range `|z| ≤ (c-1)·M` with the constant `2D`.

The strengthening is what the iteration needs, because the next state's shift is
`Q i (z + εh) - Q i₀ z` with `|h| ≤ H ≤ M`. -/
theorem petStepGen {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {N M c D : ℕ} {γ γ' : ℝ}
    (Q : ι → Ω → ℤ → ℤ) (f : Ω → ℤ → ℂ) (F : ι → ℤ → ℂ) (ν : Ω → ℝ)
    (hc : 1 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ')
    (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    (hγ'γ : γ' ≤ γ ^ 2 / (20000 * ((D : ℝ) + 1)))
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hf : ∀ a x, ‖f a x‖ ≤ 1) (hfs : ∀ a, SupportIn (f a) N)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, SupportIn (F i) N)
    (hQ : ∀ i a, ∀ z : ℤ, |z| ≤ (c : ℤ) * (M : ℤ) → |Q i a z| ≤ (D : ℤ) * (N : ℤ))
    (hLam : γ ≤ ∑ a, ν a * ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f a x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))‖) :
    (γ ^ 2 / 2000 ≤ ∑ a, ν a *
        ∑ h ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋).toNat,
          Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h *
            ‖((N : ℂ) * (M : ℂ))⁻¹ *
              ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
                ∑ y ∈ Finset.Icc 1 M,
                  ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                    Work.Peluse.UControl.PetStep.stepF F j.1
                      (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖) ∧
    (∀ (j : {j : ι × Bool // j ≠ (i₀, false)}) (a : Ω), ∀ h ∈ Finset.Icc
        (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋).toNat, ∀ z : ℤ,
        |z| ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) →
          |Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) z| ≤ ((2 * D : ℕ) : ℤ) * (N : ℤ)) := by
  classical
  have hγ'1 : γ' ≤ 1 := by
    have hd : (0 : ℝ) < 20000 * ((D : ℝ) + 1) := by positivity
    have hγ2 : γ ^ 2 ≤ 1 := by nlinarith [hγ, hγ1]
    have h1 : γ ^ 2 / (20000 * ((D : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hHle_aux : ((⌊γ' * (M : ℝ)⌋ : ℤ)) ≤ (M : ℤ) := by
    have h1 : (⌊γ' * (M : ℝ)⌋ : ℝ) ≤ γ' * (M : ℝ) := Int.floor_le _
    have h2 : γ' * (M : ℝ) ≤ 1 * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hγ'1 (by positivity)
    have h3 : (⌊γ' * (M : ℝ)⌋ : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast h3
  constructor
  · refine Work.Peluse.UControl.petStepAvgRepair (Ω := Ω) (ι := ι) i₀ (Cne := D)
      (Q := Q) (f := f) (F := F) (ν := ν) hN hM hγ hγ' hν0 hν1 hγ'γ hH hf hfs hF hFs
      (fun i a y hy => hQ i a (y : ℤ) (by
        have hy2 : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).2
        have hc1 : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
        have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
        have habs : |(y : ℤ)| = (y : ℤ) := abs_of_nonneg (by positivity)
        rw [habs]
        calc (y : ℤ) ≤ (M : ℤ) := hy2
          _ ≤ (c : ℤ) * (M : ℤ) := by nlinarith)) hLam
  · intro j a h hh z hz
    have habs : |h| ≤ ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℤ) := by
      have h1 : (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ) : ℤ) ≤ h := (Finset.mem_Icc.mp hh).1
      have h2 : h ≤ (⌊γ' * (M : ℝ)⌋.toNat : ℤ) := (Finset.mem_Icc.mp hh).2
      rw [abs_le]
      exact ⟨h1, h2⟩
    have hHM : ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℤ) ≤ (M : ℤ) := by
      have hnn : (0 : ℤ) ≤ ⌊γ' * (M : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
      rw [Int.toNat_of_nonneg hnn]
      exact hHle_aux
    have hz' : |z + h| ≤ (c : ℤ) * (M : ℤ) := by
      have h1 : |z| ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) := hz
      have h2 : ((c - 1 : ℕ) : ℤ) + 1 ≤ (c : ℤ) := by
        have : (c - 1 : ℕ) + 1 ≤ c := by omega
        exact_mod_cast this
      have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
      calc |z + h| ≤ |z| + |h| := abs_add_le _ _
        _ ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) + ((⌊γ' * (M : ℝ)⌋.toNat : ℕ) : ℤ) := by linarith
        _ ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) + (M : ℤ) := by linarith
        _ = (((c - 1 : ℕ) : ℤ) + 1) * (M : ℤ) := by ring
        _ ≤ (c : ℤ) * (M : ℤ) := by nlinarith
    have hz'' : |z| ≤ (c : ℤ) * (M : ℤ) := by
      have h2 : ((c - 1 : ℕ) : ℤ) ≤ (c : ℤ) := by
        have : (c - 1 : ℕ) ≤ c := by omega
        exact_mod_cast this
      have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
      calc |z| ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) := hz
        _ ≤ (c : ℤ) * (M : ℤ) := by nlinarith
    have hQi : |Q j.1.1 a (z + h)| ≤ (D : ℤ) * (N : ℤ) := hQ j.1.1 a (z + h) hz'
    have hQi₀ : |Q i₀ a z| ≤ (D : ℤ) * (N : ℤ) := hQ i₀ a z hz''
    have h2D : ((2 * D : ℕ) : ℤ) = 2 * (D : ℤ) := by push_cast; ring
    have hstep : Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) z
        = (if j.1.2 then Q j.1.1 a (z + h) - Q i₀ a z else Q j.1.1 a z - Q i₀ a z) := rfl
    rw [hstep]
    split_ifs
    · calc |Q j.1.1 a (z + h) - Q i₀ a z| ≤ |Q j.1.1 a (z + h)| + |Q i₀ a z| := abs_sub _ _
        _ ≤ (D : ℤ) * (N : ℤ) + (D : ℤ) * (N : ℤ) := by linarith
        _ = ((2 * D : ℕ) : ℤ) * (N : ℤ) := by rw [h2D]; ring
    · calc |Q j.1.1 a z - Q i₀ a z| ≤ |Q j.1.1 a z| + |Q i₀ a z| := abs_sub _ _
        _ ≤ (D : ℤ) * (N : ℤ) + (D : ℤ) * (N : ℤ) := by
            have := hQ j.1.1 a z hz''
            linarith
        _ = ((2 * D : ℕ) : ℤ) * (N : ℤ) := by rw [h2D]; ring

/-! ## 2. The PET-state vocabulary -/

/-- The parametrisation of the window `[-H,H]` by `Fin (2H+1)` (`k ↦ k - H`). -/
def winVal (H : ℕ) (k : Fin (2 * H + 1)) : ℤ := (k : ℤ) - (H : ℤ)

lemma winVal_mem (H : ℕ) (k : Fin (2 * H + 1)) :
    -(H : ℤ) ≤ winVal H k ∧ winVal H k ≤ (H : ℤ) := by
  have h1 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
  have h2 : (k : ℤ) < (2 * H + 1 : ℕ) := by exact_mod_cast k.isLt
  refine ⟨?_, ?_⟩ <;> simp only [winVal] <;> omega

/-- Sums over `Fin (2H+1)` transport to sums over the symmetric interval `[-H,H]` along `winVal`. -/
lemma sum_winVal_eq_sum_Icc (H : ℕ) (f : ℤ → ℝ) :
    ∑ k : Fin (2 * H + 1), f (winVal H k) = ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), f h := by
  refine Finset.sum_bij (fun k _ => winVal H k) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_Icc.mpr (winVal_mem H k)
  · intro k1 _ k2 _ h
    have h' : (k1 : ℤ) = (k2 : ℤ) := by
      simp only [winVal] at h
      omega
    exact Fin.ext (by exact_mod_cast h')
  · intro h hh
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hh
    refine ⟨⟨Int.toNat (h + H), ?_⟩, Finset.mem_univ _, ?_⟩
    · have h0 : (0 : ℤ) ≤ h + H := by omega
      have h1 : h + H < (2 * H + 1 : ℕ) := by omega
      omega
    · simp only [winVal]
      have h0 : (0 : ℤ) ≤ h + H := by omega
      rw [Int.toNat_of_nonneg h0]; ring
  · intro k _
    rfl

lemma sum_winVal_muL (H : ℕ) (hH : 1 ≤ H) :
    ∑ k : Fin (2 * H + 1), Work.Peluse.muL H (winVal H k) = 1 := by
  rw [sum_winVal_eq_sum_Icc H]
  exact Work.Peluse.PET.sum_muL_Icc H hH

/-- A **PET state**: a finite parameter set `Ω` with weights `ν` (a probability measure), a finite
slot set `ι`, shift functions `Q i a y` (slot `i`, parameter `a`, `y`-variable), slot functions
`F i`; the *base* function is `f a` and may depend on the parameter.  Peluse's §4 chain starts from
the state of `LambdaMD`, and each PET step produces a new state. -/
structure PetState where
  Ω : Type
  ι : Type
  finΩ : Fintype Ω
  decΩ : DecidableEq Ω
  finι : Fintype ι
  decι : DecidableEq ι
  Q : ι → Ω → ℤ → ℤ
  f : Ω → ℤ → ℂ
  F : ι → ℤ → ℂ
  ν : Ω → ℝ

attribute [instance] PetState.finΩ PetState.decΩ PetState.finι PetState.decι

/-- The **correlation** of a PET state:
`Σ_a ν a ‖(NM)⁻¹ Σ_x f a x Σ_{y∈[1,M]} ∏_i F i (x+Q i a y)‖`.  `‖LambdaMD N M P F‖` is the
correlation of the initial state of the chain. -/
noncomputable def PetState.lam (S : PetState) (N M : ℕ) : ℝ :=
  ∑ a : S.Ω, S.ν a * ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, S.f a x *
    ∑ y ∈ Finset.Icc 1 M, ∏ i : S.ι, S.F i (x + S.Q i a (y : ℤ))‖

/-- The **shift-bound invariant** of a state at scale `M`: every shift is bounded by `D·N` on the
range `|z| ≤ c·M`.  A chain of `n` PET steps needs `c ≥ n` and `D = 2^n·D₀` (each step halves the
range and doubles the constant), which is why the invariant carries a range. -/
def PetState.ShiftBound (S : PetState) (N M c D : ℕ) : Prop :=
  ∀ i a z, |z| ≤ (c : ℤ) * (M : ℤ) → |S.Q i a z| ≤ (D : ℤ) * (N : ℤ)

/-- The **PET step** of a state at the distinguished slot `i₀`, with window `H`: the new state has
slots `ι' = {j : ι × Bool // j ≠ (i₀,false)}`, parameters `Ω × Fin (2H+1)` with the weight
`ν a · μ_H h` (`h = k - H`), base function `F i₀` and shifts
`stepQ Q i₀ j (a,h) y = Q j.1 (y + εh) - Q i₀ y`. -/
noncomputable def PetState.step (S : PetState) (i₀ : S.ι) (H : ℕ) : PetState where
  Ω := S.Ω × Fin (2 * H + 1)
  ι := {j : S.ι × Bool // j ≠ (i₀, false)}
  finΩ := inferInstance
  decΩ := inferInstance
  finι := inferInstance
  decι := inferInstance
  Q := fun j a y => Work.Peluse.UControl.PetStep.stepQ S.Q i₀ j (a.1, winVal H a.2) y
  f := fun _ x => S.F i₀ x
  F := fun j x => Work.Peluse.UControl.PetStep.stepF S.F j.1 x
  ν := fun a => S.ν a.1 * Work.Peluse.muL H (winVal H a.2)

/-- The weight of a stepped state sums to one (given `Σ ν = 1` and `H ≥ 1`). -/
theorem PetState.sum_step_ν (S : PetState) (i₀ : S.ι) {H : ℕ} (hH : 1 ≤ H)
    (hν1 : ∑ a, S.ν a = 1) : ∑ a, (S.step i₀ H).ν a = 1 := by
  classical
  have hfun : ∀ a : S.Ω × Fin (2 * H + 1),
      (S.step i₀ H).ν a = S.ν a.1 * Work.Peluse.muL H (winVal H a.2) := fun a => rfl
  calc ∑ a : S.Ω × Fin (2 * H + 1), (S.step i₀ H).ν a
      = ∑ a : S.Ω × Fin (2 * H + 1),
          S.ν a.1 * Work.Peluse.muL H (winVal H a.2) := by
        exact Finset.sum_congr rfl (fun a _ => hfun a)
    _ = ∑ a : S.Ω, ∑ k : Fin (2 * H + 1),
          S.ν a * Work.Peluse.muL H (winVal H k) :=
        Fintype.sum_prod_type _
    _ = ∑ a : S.Ω, S.ν a * ∑ k : Fin (2 * H + 1),
          Work.Peluse.muL H (winVal H k) := by
        exact Finset.sum_congr rfl (fun a _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ a : S.Ω, S.ν a := by rw [sum_winVal_muL H hH]; simp
    _ = 1 := hν1

/-- **The step inequality in the state vocabulary.**  If the correlation of `S` is at least `γ`, the
correlation of `S.step i₀ H` (`H = ⌊γ'M⌋`) is at least `γ²/2000`.  This is `petStepGen` plus the
reindexing of the parameters `Ω × Fin (2H+1)` against the window sum `∑_{h ∈ [-H,H]}`. -/
theorem PetState.lam_step (S : PetState) (i₀ : S.ι) {N M c D : ℕ} {γ γ' : ℝ}
    (hc : 1 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ')
    (hν0 : ∀ a, 0 ≤ S.ν a) (hν1 : ∑ a, S.ν a = 1)
    (hγ'γ : γ' ≤ γ ^ 2 / (20000 * ((D : ℝ) + 1)))
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hf : ∀ a x, ‖S.f a x‖ ≤ 1) (hfs : ∀ a, SupportIn (S.f a) N)
    (hF : ∀ i x, ‖S.F i x‖ ≤ 1) (hFs : ∀ i, SupportIn (S.F i) N)
    (hQ : S.ShiftBound N M c D)
    (hLam : γ ≤ S.lam N M) :
    γ ^ 2 / 2000 ≤ (S.step i₀ (⌊γ' * (M : ℝ)⌋.toNat)).lam N M := by
  classical
  let g : S.Ω → ℤ → ℝ := fun a h => ‖((N : ℂ) * (M : ℂ))⁻¹ *
      ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase S.F i₀ (a, h) x *
        ∑ y ∈ Finset.Icc 1 M,
          ∏ j : {j : S.ι × Bool // j ≠ (i₀, false)},
            Work.Peluse.UControl.PetStep.stepF S.F j.1
              (x + Work.Peluse.UControl.PetStep.stepQ S.Q i₀ j (a, h) (y : ℤ))‖
  have hstep : (S.step i₀ (⌊γ' * (M : ℝ)⌋.toNat)).lam N M
      = ∑ a : S.Ω, S.ν a * ∑ h ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ))
          (⌊γ' * (M : ℝ)⌋.toNat), Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h * g a h := by
    have h1 : (S.step i₀ (⌊γ' * (M : ℝ)⌋.toNat)).lam N M
        = ∑ a : S.Ω × Fin (2 * ⌊γ' * (M : ℝ)⌋.toNat + 1),
            S.ν a.1 * Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat
              (winVal ⌊γ' * (M : ℝ)⌋.toNat a.2) *
              g a.1 (winVal ⌊γ' * (M : ℝ)⌋.toNat a.2) :=
      Finset.sum_congr rfl (fun a _ => rfl)
    rw [h1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h3 : (∑ k : Fin (2 * ⌊γ' * (M : ℝ)⌋.toNat + 1),
          S.ν a * Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat
            (winVal ⌊γ' * (M : ℝ)⌋.toNat k) *
            g a (winVal ⌊γ' * (M : ℝ)⌋.toNat k))
        = ∑ h ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋.toNat),
            S.ν a * Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h * g a h := by
      rw [← sum_winVal_eq_sum_Icc ⌊γ' * (M : ℝ)⌋.toNat
        (fun h => S.ν a * Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h * g a h)]
    rw [h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hstep]
  exact (petStepGen (Ω := S.Ω) (ι := S.ι) i₀ (Q := S.Q) (f := S.f) (F := S.F)
    (ν := S.ν) (c := c) (D := D) (γ := γ) (γ' := γ') hc hN hM hγ hγ1 hγ' hν0 hν1 hγ'γ
    hH hf hfs hF hFs hQ hLam).1

/-- The shift-bound invariant is preserved by a PET step, with `c ↦ c-1` and `D ↦ 2D`. -/
theorem PetState.ShiftBound.step (S : PetState) (i₀ : S.ι) {N M c D H : ℕ} (hc : 1 ≤ c)
    (hHM : (H : ℤ) ≤ (M : ℤ)) (hQ : S.ShiftBound N M c D) :
    (S.step i₀ H).ShiftBound N M (c - 1) (2 * D) := by
  intro j a z hz
  have habs : |winVal H a.2| ≤ (H : ℤ) := by
    obtain ⟨h1, h2⟩ := winVal_mem H a.2
    rw [abs_le]; exact ⟨h1, h2⟩
  have hz1 : |z + winVal H a.2| ≤ (c : ℤ) * (M : ℤ) := by
    have h2 : ((c - 1 : ℕ) : ℤ) + 1 ≤ (c : ℤ) := by
      have : (c - 1 : ℕ) + 1 ≤ c := by omega
      exact_mod_cast this
    have hM0 : (0 : ℤ) ≤ (M : ℤ) := by omega
    calc |z + winVal H a.2| ≤ |z| + |winVal H a.2| := abs_add_le _ _
      _ ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) + (H : ℤ) := by linarith
      _ ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) + (M : ℤ) := by linarith
      _ = (((c - 1 : ℕ) : ℤ) + 1) * (M : ℤ) := by ring
      _ ≤ (c : ℤ) * (M : ℤ) := by nlinarith
  have hz2 : |z| ≤ (c : ℤ) * (M : ℤ) := by
    have h2 : ((c - 1 : ℕ) : ℤ) ≤ (c : ℤ) := by
      have : (c - 1 : ℕ) ≤ c := by omega
      exact_mod_cast this
    have hM0 : (0 : ℤ) ≤ (M : ℤ) := by omega
    calc |z| ≤ ((c - 1 : ℕ) : ℤ) * (M : ℤ) := hz
      _ ≤ (c : ℤ) * (M : ℤ) := by nlinarith
  have h2D : ((2 * D : ℕ) : ℤ) = 2 * (D : ℤ) := by push_cast; ring
  have hstep : (S.step i₀ H).Q j a z = Work.Peluse.UControl.PetStep.stepQ S.Q i₀ j
      (a.1, winVal H a.2) z := rfl
  rw [hstep]
  have hsq : Work.Peluse.UControl.PetStep.stepQ S.Q i₀ j (a.1, winVal H a.2) z
      = (if j.1.2 then S.Q j.1.1 a.1 (z + winVal H a.2) - S.Q i₀ a.1 z
          else S.Q j.1.1 a.1 z - S.Q i₀ a.1 z) := rfl
  rw [hsq]
  have hj1 : |S.Q j.1.1 a.1 (z + winVal H a.2)| ≤ (D : ℤ) * (N : ℤ) :=
    hQ j.1.1 a.1 _ hz1
  have hj2 : |S.Q j.1.1 a.1 z| ≤ (D : ℤ) * (N : ℤ) := hQ j.1.1 a.1 _ hz2
  have hi : |S.Q i₀ a.1 z| ≤ (D : ℤ) * (N : ℤ) := hQ i₀ a.1 _ hz2
  split_ifs
  · calc |S.Q j.1.1 a.1 (z + winVal H a.2) - S.Q i₀ a.1 z|
        ≤ |S.Q j.1.1 a.1 (z + winVal H a.2)| + |S.Q i₀ a.1 z| := abs_sub _ _
      _ ≤ (D : ℤ) * (N : ℤ) + (D : ℤ) * (N : ℤ) := by linarith
      _ = ((2 * D : ℕ) : ℤ) * (N : ℤ) := by rw [h2D]; ring
  · calc |S.Q j.1.1 a.1 z - S.Q i₀ a.1 z| ≤ |S.Q j.1.1 a.1 z| + |S.Q i₀ a.1 z| := abs_sub _ _
      _ ≤ (D : ℤ) * (N : ℤ) + (D : ℤ) * (N : ℤ) := by linarith
      _ = ((2 * D : ℕ) : ℤ) * (N : ℤ) := by rw [h2D]; ring

/-! ## 3. The initial state of the chain (`LambdaMD`) -/

/-- The **initial PET state** of the chain for `LambdaMD N M P F`: the parameter set is trivial
(`Fin 1`), the slots are `Fin (d-1) ⊕ Fin 1` with shifts `y^{i+1}` (`Sum.inl`) and `P.eval y`
(`Sum.inr`), the base function is `F 0` and the slot functions are `F (i+1)`.  (The slot type is a
sum rather than `Fin d` so that the product over the slots splits *definitionally* into the paper's
`∏_{i<d-1} · F_d`; `Fin 1` rather than `PUnit` so that the singleton evaluations
`Fin.sum_univ_one`/`Fin.prod_univ_one` apply without instance search.)

The identity `(LambdaMDPetState N M P F).lam N M = ‖LambdaMD N M P F‖` is delegated
(`Submission/Work/Peluse/UControl/petChainMD.lean`): it is pure `Fin`/`Sum` product bookkeeping. -/
noncomputable def LambdaMDPetState (N M : ℕ) (P : Polynomial ℤ)
    (F : Fin (P.natDegree + 1) → ℤ → ℂ) : PetState where
  Ω := Fin 1
  ι := Fin (P.natDegree - 1) ⊕ Fin 1
  finΩ := inferInstance
  decΩ := inferInstance
  finι := inferInstance
  decι := inferInstance
  Q := fun j (_ : Fin 1) y => match j with
    | Sum.inl i => y ^ (i.val + 1)
    | Sum.inr _ => P.eval y
  f := fun _ => F ⟨0, Nat.succ_pos _⟩
  F := fun j => match j with
    | Sum.inl i => F ⟨i.val + 1, by have := i.isLt; omega⟩
    | Sum.inr _ => F ⟨P.natDegree, Nat.lt_succ_self _⟩
  ν := fun _ => 1

/-! ## 4. The PET order on weight vectors (the termination measure of the chain) -/

/-- **The PET weight-vector order**: at the largest index where two weight vectors differ, the
first is smaller.  (Peluse, §4: `V(Q) ≺ V(Q')` iff at the largest degree `d` with
`V(Q)_d ≠ V(Q')_d` one has `V(Q)_d < V(Q')_d`.)  This is the lexicographic order on the *reversed*
tuple, hence a well-order.  The termination of the PET chain (Lemmas 4.7/4.8) is the statement that
each step *lowers* this vector. -/
def petLt {d : ℕ} (u v : Fin (d + 1) → ℕ) : Prop :=
  ∃ j : Fin (d + 1), u j < v j ∧ ∀ k : Fin (d + 1), j < k → u k = v k

-- The identity `(LambdaMDPetState N M P F).lam N M = ‖LambdaMD N M P F‖` is the next
-- bookkeeping step of the chain (delegated path `Peluse/UControl/petChainMD`); it needs care with
-- the singleton instances (`Fin.sum_univ_one` / `Fintype.prod_sum_type` / `Fin.prod_univ_one`).

-- The well-foundedness of `petLt` (delegated path `Peluse/UControl/petChainWF`) is the
-- termination measure of the PET chain; it is the lexicographic order read from the top
-- coordinate, so it is reduced to the lex order on `ℕ × (Fin d → ℕ)` (Mathlib's
-- `WellFounded.prod_lex`) or proved directly by the double induction on
-- `(top value, rest)` -- the only obstacle is that `WellFounded` does not reduce for
-- function application in this Mathlib, so the induction has to go through `WellFounded.apply`
-- / `acc_def`.

/-! ## 5. States carrying the *polynomial* shifts (so that the weight vector is computable) -/

/-- A PET state together with the *polynomials* of its shifts (`PetState.Q` is their evaluation).
This is what makes Peluse's weight vector (`PetStateP.weight`) available: the PET step must be seen
to *lower* it, which is the termination argument of Lemmas 4.7/4.8. -/
structure PetStateP where
  Ω : Type
  ι : Type
  finΩ : Fintype Ω
  decΩ : DecidableEq Ω
  finι : Fintype ι
  decι : DecidableEq ι
  P : ι → Ω → Polynomial ℤ
  f : Ω → ℤ → ℂ
  F : ι → ℤ → ℂ
  ν : Ω → ℝ

attribute [instance] PetStateP.finΩ PetStateP.decΩ PetStateP.finι PetStateP.decι

/-- The evaluation state of a polynomial PET state. -/
noncomputable def PetStateP.toState (S : PetStateP) : PetState where
  Ω := S.Ω
  ι := S.ι
  finΩ := S.finΩ
  decΩ := S.decΩ
  finι := S.finι
  decι := S.decι
  Q := fun i a y => (S.P i a).eval y
  f := S.f
  F := S.F
  ν := S.ν

/-- Peluse's **weight vector** at a parameter: `V j` is the number of *distinct leading
coefficients* among the slots whose shift has degree `j`. -/
noncomputable def PetStateP.weight (S : PetStateP) (a : S.Ω) (d : ℕ) : Fin (d + 1) → ℕ :=
  fun j => (((Finset.univ : Finset S.ι).filter
      (fun i => (S.P i a).natDegree = (j : ℕ))).image
        (fun i => (S.P i a).leadingCoeff)).card

/-- The PET step on polynomial states: the slot `(i,ε)` gets the polynomial
`P i (X + εh) - P i₀` (`h` the new parameter), the base function is `F i₀` and the slot functions
are `F i` or its conjugate. -/
noncomputable def PetStateP.step (S : PetStateP) (i₀ : S.ι) (H : ℕ) : PetStateP where
  Ω := S.Ω × Fin (2 * H + 1)
  ι := {j : S.ι × Bool // j ≠ (i₀, false)}
  finΩ := inferInstance
  decΩ := inferInstance
  finι := inferInstance
  decι := inferInstance
  P := fun j a => (S.P j.1.1 a.1).comp
      (Polynomial.X + Polynomial.C (if j.1.2 then winVal H a.2 else 0)) - S.P i₀ a.1
  f := fun _ x => S.F i₀ x
  F := fun j x => Work.Peluse.UControl.PetStep.stepF S.F j.1 x
  ν := fun a => S.ν a.1 * Work.Peluse.muL H (winVal H a.2)

/-- The correlation of a polynomial state (the same formula as `PetState.lam`, with the shifts
evaluated from the polynomials). -/
noncomputable def PetStateP.lam (S : PetStateP) (N M : ℕ) : ℝ :=
  ∑ a : S.Ω, S.ν a * ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, S.f a x *
    ∑ y ∈ Finset.Icc 1 M, ∏ i : S.ι, S.F i (x + (S.P i a).eval (y : ℤ))‖

theorem PetStateP.lam_eq (S : PetStateP) (N M : ℕ) :
    S.toState.lam N M = S.lam N M := rfl

-- The bridge `(S.step i₀ H).lam N M = (S.toState.step i₀ H).lam N M` (the step commutes with the
-- evaluation at the level of correlations) is the remaining glue between the polynomial states of
-- this section and the analysis; the pointwise identities for `P` and `Q` are
-- `Polynomial.eval_comp`/`eval_add` on the one side and `stepQ` on the other, so it is a
-- `Finset.sum_congr`/`tsum_congr` rewrite (careful: `simp` must *not* unfold `PetStateP.step` /
-- `PetState.step` before the pointwise lemmas are applied).

/-- **Dropping the constant slots.**  If `J` is a set of slots whose polynomials are constant in
`y` (hypothesis `hc`), removing them from the index set and multiplying their — now `y`-independent —
values into the base function leaves the correlation unchanged.  This is the paper's
`J_k = ((J_{k-1} \ {j : deg Q_j = 0}) × {0,1}) \ {(i_{0,k-1},0)}`: the degree-`0` slots are absorbed
into `f` so that the weight-vector decrease (`petChainWeight`) applies. -/
noncomputable def PetStateP.drop (S : PetStateP) (J : Finset S.ι) : PetStateP where
  Ω := S.Ω
  ι := {i : S.ι // i ∈ Jᶜ}
  finΩ := S.finΩ
  decΩ := S.decΩ
  finι := inferInstance
  decι := inferInstance
  P := fun i a => S.P i.1 a
  f := fun a x => S.f a x * ∏ i ∈ J, S.F i (x + (S.P i a).eval 0)
  F := fun i x => S.F i.1 x
  ν := S.ν

-- The lemma `(S.drop J).lam N M = S.lam N M` (the constant slots can be absorbed into the base
-- function without changing the correlation) is delegated, path `Peluse/UControl/petChainDrop`; the
-- product splitting is `Finset.prod_mul_prod_compl` + `Finset.prod_subtype` (with `drop`'s index type
-- `{i : S.ι // i ∈ Jᶜ}` chosen so that the subtype predicate is *literally* `· ∈ Jᶜ`).

end Work.Peluse.UControl.PetStep

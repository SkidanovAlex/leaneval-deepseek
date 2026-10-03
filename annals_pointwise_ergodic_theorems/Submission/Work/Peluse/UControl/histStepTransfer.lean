import Mathlib
import Submission.Work.Peluse.UControl.HistInv

/-!
# `histStepTransfer`: the history successor carries the correlation and shift bound of `histNextPet`

One step of the history-indexed PET chain is taken at the *deterministic* selection
`HistData.sel`; the successor state `histStep X hnl` of the history chain and the "step and drop"
state `histNextPet X hnl H F f` of the analytic chain are indexed by two *different* (but
equivalent) slot types: the live slots of the history step are the pairs `(j, h')` such that
`(j, Fin.init h')` was live, `h'` is not the distinguished dropped continuation, and the shift
polynomial of `(j,h')` is non-constant, whereas `histNextPet` keeps the slots of the *symbolic*
step `X.2.toSym.S.step ⟨sel, mem⟩` that are not `y`-constant.

The slot bijection `HistData.stepIdx` identifies the two index types and carries the slot
polynomials to each other (`HistData.stepIdx_P`).  Consequently the correlation `lam` and the shift
bound `ShiftBound` of the two concrete states coincide, which is the content of this file.

This is the `histStepLam`/`histStepSB` identification promised in the docstring of `HistInv`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

/-! ## Transfer along a slot relabelling -/

/-- The `ShiftBound` of the concrete state of a symbolic state, read off the slot polynomials (the
shift bound only involves the shift polynomials, not the slot or base functions). -/
def hstSlotsBound {k : ℕ} (S : PetStateSym k) (H N M c D : ℕ) : Prop :=
  ∀ a : WinTower H k, ∀ i : S.ι, ∀ z : ℤ, |z| ≤ (c : ℤ) * (M : ℤ) →
    |((S.P i).map (MvPolynomial.eval (WinTower.param H k a))).eval z| ≤ (D : ℤ) * (N : ℤ)

/-- `hstSlotsBound` is the shift bound of the concrete state of the symbolic state. -/
lemma hstSlotsBound_toPetP {k H N M c D : ℕ} (S : PetStateSym k) (F : S.ι → ℤ → ℂ)
    (f : WinTower H k → ℤ → ℂ) :
    (S.toPetP H F f).toState.ShiftBound N M c D ↔ hstSlotsBound S H N M c D := by
  constructor
  · intro h a i z hz
    exact h i a z hz
  · intro h i a z hz
    exact h a i z hz

/-- `hstSlotsBound` transfers along a slot relabelling that fixes the slot polynomials. -/
lemma hstSlotsBound_congr {k H N M c D : ℕ} {S T : PetStateSym k} (e : S.ι ≃ T.ι)
    (hP : ∀ i, T.P (e i) = S.P i) :
    hstSlotsBound T H N M c D ↔ hstSlotsBound S H N M c D := by
  constructor
  · intro h a i z hz
    have h1 := h a (e i) z hz
    rw [hP i] at h1
    exact h1
  · intro h a j z hz
    have h1 := h a (e.symm j) z hz
    have hj : T.P j = S.P (e.symm j) := by
      have h2 := hP (e.symm j)
      rwa [e.apply_symm_apply j] at h2
    rw [← hj] at h1
    exact h1

/-- The correlation of the concrete state of a symbolic state depends on the slot polynomials and
the slot functions only through the index type: a relabelling of the slots that fixes the
polynomials and the slot functions does not change `lam`. -/
lemma hstLam_equiv {k H : ℕ} (N M : ℕ) (S T : PetStateSym k) (e : S.ι ≃ T.ι)
    (hP : ∀ i, T.P (e i) = S.P i)
    (F₁ : S.ι → ℤ → ℂ) (F₂ : T.ι → ℤ → ℂ) (hF : ∀ i, F₂ (e i) = F₁ i)
    (f₁ f₂ : WinTower H k → ℤ → ℂ) (hf : ∀ a, f₁ a = f₂ a) :
    (S.toPetP H F₁ f₁).lam N M = (T.toPetP H F₂ f₂).lam N M := by
  classical
  simp only [PetStateP.lam, PetStateSym.toPetP]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hf a]
  refine congrArg (fun t : ℝ => WinTower.nu H k a * t) ?_
  refine congrArg Norm.norm ?_
  refine congrArg (fun t : ℂ => ((N : ℂ) * (M : ℂ))⁻¹ * t) ?_
  refine tsum_congr (fun x => ?_)
  refine congrArg (fun t : ℂ => f₂ a x * t) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Fintype.prod_equiv e
    (fun i : S.ι => F₁ i (x + ((S.P i).map
      (MvPolynomial.eval (WinTower.param H k a))).eval (y : ℤ)))
    (fun j : T.ι => F₂ j (x + ((T.P j).map
      (MvPolynomial.eval (WinTower.param H k a))).eval (y : ℤ))) (fun i => ?_)
  rw [hF i, hP i]

/-- The shift bound of the *dropped* concrete step is the `hstSlotsBound` of the symbolic drop
(the `drop` keeps the shift polynomials, only the index type shrinks). -/
lemma hstStepDrop_iff {k H N M c D : ℕ} (S : PetStateSym k) (i₀ : S.ι)
    (J : Finset (S.step i₀).ι) (F : S.ι → ℤ → ℂ) (f : WinTower H k → ℤ → ℂ) :
    (((S.toPetP H F f).step i₀ H).drop J).toState.ShiftBound N M c D
      ↔ hstSlotsBound (PetStateSym.dropSym (S.step i₀) J) H N M c D := by
  have key : ∀ (j : (S.step i₀).ι) (a : WinTower H (k + 1)) (z : ℤ),
      Polynomial.eval z (((S.toPetP H F f).step i₀ H).P j a)
      = Polynomial.eval z (Polynomial.map (MvPolynomial.eval (WinTower.param H (k + 1) a))
          ((S.step i₀).P j)) :=
    fun j a z => congrArg (fun q => Polynomial.eval z q)
      (toPetP_step_P S i₀ H F f j a).symm
  constructor
  · intro h a j z hz
    have h1 : |(Polynomial.eval z (((S.toPetP H F f).step i₀ H).P j.1 a))| ≤ (D : ℤ) * (N : ℤ) :=
      h j a z hz
    rw [key j.1 a z] at h1
    exact h1
  · intro h j a z hz
    show |(Polynomial.eval z (((S.toPetP H F f).step i₀ H).P j.1 a))| ≤ (D : ℤ) * (N : ℤ)
    have h1 : |(Polynomial.eval z (Polynomial.map
        (MvPolynomial.eval (WinTower.param H (k + 1) a)) ((S.step i₀).P j.1)))| ≤ (D : ℤ) * (N : ℤ) :=
      h a j z hz
    rw [key j.1 a z]
    exact h1

/-! ## The slot bijection of one history step -/

/-- The slot map `HistData.stepIdx` of one history step is injective. -/
lemma hst_stepIdx_injective {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) : Function.Injective (X.stepIdx i₀ h₀ hh) := by
  intro x y h
  have h1 : (X.stepIdx i₀ h₀ hh x).1 = (X.stepIdx i₀ h₀ hh y).1 := congrArg Subtype.val h
  have hfst : (X.stepIdx i₀ h₀ hh x).1.1 = (X.stepIdx i₀ h₀ hh y).1.1 := congrArg Prod.fst h1
  have hsnd : (X.stepIdx i₀ h₀ hh x).1.2 = (X.stepIdx i₀ h₀ hh y).1.2 := congrArg Prod.snd h1
  have hinit : Fin.init x.1.2 = Fin.init y.1.2 := by
    have h' := congrArg (fun z : (X.toSym).S.ι => z.1.2) hfst
    simpa [HistData.stepIdx] using h'
  have hlast : x.1.2 (Fin.last n) = y.1.2 (Fin.last n) := by
    simpa [HistData.stepIdx] using hsnd
  have h1st : x.1.1 = y.1.1 := by
    have h' := congrArg (fun z : (X.toSym).S.ι => z.1.1) hfst
    simpa [HistData.stepIdx] using h'
  refine Subtype.ext (Prod.ext h1st ?_)
  rw [← Fin.snoc_init_self (q := x.1.2), ← Fin.snoc_init_self (q := y.1.2), hinit, hlast]

/-- **The slot bijection of one history step.**  The live slots of the history step are exactly the
non-constant slots of the symbolic step, and the two slot polynomials agree along `HistData.stepIdx`
(`HistData.stepIdx_P`). -/
noncomputable def hstStepEquiv {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) :
    ((X.step i₀ h₀ hh).toSym).S.ι ≃
      (PetStateSym.dropSym ((X.toSym).S.step ⟨(i₀, h₀), hh⟩)
        (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).ι :=
  Equiv.ofBijective
    (fun x => ⟨X.stepIdx i₀ h₀ hh x, by
      rw [Finset.mem_compl]
      intro hmem
      have hx : x.1 ∈ X.stepH i₀ h₀ := x.2
      simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨-, -, hdeg⟩ := hx
      have h0 : (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P
          (X.stepIdx i₀ h₀ hh x)).natDegree = 0 := by
        have hmem' : X.stepIdx i₀ h₀ hh x ∈ Finset.univ.filter (fun j =>
            (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P j).natDegree = 0) := hmem
        exact (Finset.mem_filter.mp hmem').2
      have hdeg' : 1 ≤ (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P
          (X.stepIdx i₀ h₀ hh x)).natDegree := by
        rw [X.stepIdx_P i₀ h₀ hh x]
        exact hdeg
      omega⟩)
    ⟨fun x y h => hst_stepIdx_injective X i₀ h₀ hh (Subtype.ext_iff.mp h), fun b => by
      have hle : (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P b.1).natDegree ≤ d :=
        step_natDegree_le (X.toSym).S ⟨(i₀, h₀), hh⟩ (X.toSym).hd b.1
      have hbne : (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P b.1).natDegree ≠ 0 := by
        intro h0
        exact (Finset.mem_compl.mp b.2) (Finset.mem_filter.mpr
          ⟨Finset.mem_univ b.1, h0⟩)
      have hj : 1 ≤ ((⟨(((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P b.1).natDegree,
          Nat.lt_succ_of_le hle⟩ : Fin (d + 1)) : ℕ) :=
        Nat.one_le_iff_ne_zero.mpr hbne
      obtain ⟨a, -, ha⟩ := X.stepIdx_surj i₀ h₀ hh hj b.1 rfl
      exact ⟨a, Subtype.ext ha⟩⟩

/-! ## The two transfers of one history step -/

/-- **The correlation of the history successor is that of `histNextPet`.**  The transfer is along
the slot bijection `hstStepEquiv` together with `toPetP_stepDrop_lam`. -/
lemma hstLamGen {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (H N M : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) :
    (((X.step i₀ h₀ hh).toSym).S.toPetP H
        (fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1))
        (fun a x => ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
            (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x)).lam N M
      = ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
            (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).lam N M := by
  have hP : ∀ i : ((X.step i₀ h₀ hh).toSym).S.ι,
      (PetStateSym.dropSym ((X.toSym).S.step ⟨(i₀, h₀), hh⟩)
        (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).P (hstStepEquiv X i₀ h₀ hh i)
        = ((X.step i₀ h₀ hh).toSym).S.P i := by
    intro i
    show ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P (X.stepIdx i₀ h₀ hh i)
        = X.stepQ i₀ h₀ i.1.1 i.1.2
    exact X.stepIdx_P i₀ h₀ hh i
  have hF : ∀ i : ((X.step i₀ h₀ hh).toSym).S.ι,
      toPetP_stepF (X.toSym).S ⟨(i₀, h₀), hh⟩ F
          (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩) (hstStepEquiv X i₀ h₀ hh i)
        = (fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1)) i := fun i => rfl
  have hf : ∀ a : WinTower H (n + 1),
      (fun a x => ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
            (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x) a
        = toPetP_stepf (X.toSym).S ⟨(i₀, h₀), hh⟩ H F f
            (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩) a := fun a => rfl
  have h1 := hstLam_equiv N M ((X.step i₀ h₀ hh).toSym).S
    (PetStateSym.dropSym ((X.toSym).S.step ⟨(i₀, h₀), hh⟩) (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩))
    (hstStepEquiv X i₀ h₀ hh) hP
    (fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1))
    (toPetP_stepF (X.toSym).S ⟨(i₀, h₀), hh⟩ F
      (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)) hF
    (fun a x => ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
        (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x)
    (toPetP_stepf (X.toSym).S ⟨(i₀, h₀), hh⟩ H F f
      (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)) hf
  have h2 := toPetP_stepDrop_lam (X.toSym).S ⟨(i₀, h₀), hh⟩ H N M F f
    (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)
  exact h1.trans h2

/-- **The shift bound of the history successor is that of `histNextPet`.** -/
lemma hstSBGen {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (H N M c D : ℕ) (F : (X.toSym).S.ι → ℤ → ℂ)
    (f : WinTower H n → ℤ → ℂ) :
    ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
        (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).toState.ShiftBound N M c D
      ↔ (((X.step i₀ h₀ hh).toSym).S.toPetP H
          (fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1))
          (fun a x => ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
              (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x)).toState.ShiftBound
          N M c D := by
  have hP : ∀ i : ((X.step i₀ h₀ hh).toSym).S.ι,
      (PetStateSym.dropSym ((X.toSym).S.step ⟨(i₀, h₀), hh⟩)
        (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).P (hstStepEquiv X i₀ h₀ hh i)
        = ((X.step i₀ h₀ hh).toSym).S.P i := by
    intro i
    show ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P (X.stepIdx i₀ h₀ hh i)
        = X.stepQ i₀ h₀ i.1.1 i.1.2
    exact X.stepIdx_P i₀ h₀ hh i
  exact (hstStepDrop_iff (X.toSym).S ⟨(i₀, h₀), hh⟩
      (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩) F f).trans
    ((hstSlotsBound_congr (hstStepEquiv X i₀ h₀ hh) hP).trans
      (hstSlotsBound_toPetP ((X.step i₀ h₀ hh).toSym).S
        (fun x => stepF F ((X.stepIdx i₀ h₀ hh x).1))
        (fun a x => ((((X.toSym).S.toPetP H F f).step ⟨(i₀, h₀), hh⟩ H).drop
            (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x)).symm)

theorem histStepTransfer {d : ℕ} (H N M c D : ℕ) (X : HState d) (hnl : HState.Go X)
    (F : (X.2.toSym).S.ι → ℤ → ℂ) (f : WinTower H X.1 → ℤ → ℂ) :
    ((histPet (histStep X hnl).2 H (histNextF X hnl F) (histNextf X hnl H F f)).toState.lam N M
        = (histNextPet X hnl H F f).toState.lam N M)
      ∧ ((histNextPet X hnl H F f).toState.ShiftBound N M c D
        ↔ (histPet (histStep X hnl).2 H (histNextF X hnl F) (histNextf X hnl H F f)).toState.ShiftBound
            N M c D) := by
  constructor
  · rw [PetStateP.lam_eq, PetStateP.lam_eq]
    exact hstLamGen X.2 (X.2.sel (histHne X hnl)).1 (X.2.sel (histHne X hnl)).2
      (X.2.sel_mem_H (histHne X hnl)) H N M F f
  · exact hstSBGen X.2 (X.2.sel (histHne X hnl)).1 (X.2.sel (histHne X hnl)).2
      (X.2.sel_mem_H (histHne X hnl)) H N M c D F f

end

end Work.Peluse.UControl

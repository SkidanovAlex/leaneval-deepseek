/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/WordTransfer.lean` — from *slot* data to *word* data

`WordEnergy.energyDeriv_IPiter_le` reduces the level energy identity of the `ε`-scheme to the
`H1IP`-energy derivative of every **slot word** family `τ ↦ X (x τ)` with `X` of length at most
`n`.  The slot data that the scheme actually produces is available for the *canonical* words
`mixed j i = D_z^j D_θ^i` only (that is the form of `hasDerivWithinAt_mixed_JfamP_final`).

This module bridges the two:

* `mixed_Dth_shift` — `mixed j i (D_θ f) = mixed j (i+1) f` (pure composition, no regularity);
* `mixed_Dz_shift` — `mixed j i (D_z f) = mixed (j+1) i f` on the open quadrant, for `f` smooth
  there (this is the one place where the commutation `D_θ (D_z f) = D_z (D_θ f)` is used);
* `energyDeriv_H1IP_of_word` — the structural induction on `IsWordLe n X` transporting the slot
  data to an arbitrary word, using `WordCongr.H1IP_congr_Q0` and `WordCongr.EnergyDeriv_congr`;
* `energyDeriv_IP4_of_mixed` / `energyDeriv_IP6_of_mixed` — the two instances consumed by the two
  halves of `AprioriP`: slots of order `≤ 3` for the level-four pairing `IP4`, slots of order
  `≤ 5` for the level-six pairing `IP6`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordEnergy
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The two shift identities for the canonical slot words -/

/-- **The `D_θ`-shift is free**: `D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
theorem mixed_Dth_shift (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f :=
  congrArg (fun g : ℝ → ℝ → ℝ => Work.Spaces.DzIter j g)
    (Work.Spaces.DthIter_add_right i 1 f)

/-- Iterates of `D_z` are local: if two profiles agree on an open set, so do their `D_z`-iterates
(any order). -/
theorem DzIter_eqOn_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro p hp
      have hz : Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DzIter j g') p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Function.uncurry]
      rw [hz]

/-- **The `D_z`-shift on the open quadrant**: for `f` smooth on `Q0`,
`D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` there.  This is the only place where the commutation
of `D_θ` with the iterates of `D_z` is needed. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
        = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 (Work.FTS.EllipticEst.smoothOpen_iff_forall f |>.1 hf) 1 i
  intro z θ hq
  have h2 : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.mixed 1 i f) z θ :=
    DzIter_eqOn_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm j hq
  have h3 : Work.Spaces.DzIter j (Work.Spaces.mixed 1 i f) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ :=
    congrArg (fun g : ℝ → ℝ → ℝ => g z θ)
      (Work.Spaces.DzIter_add_right j 1 (Work.Spaces.DthIter i f)).symm
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [h2, h3]

/-! ## The structural induction -/

/-- **Slot data at order `≤ n` produces the `H1IP`-energy derivative of every word of length
`≤ n`.**  The induction is structural in the word; the `D_θ`-step is pure composition
(`mixed_Dth_shift`), while the `D_z`-step uses the congruence of `H1IP` on the open quadrant
(`WordCongr.H1IP_congr_Q0`) because the two words only agree there. -/
theorem energyDeriv_H1IP_of_word {α τ T : ℝ} (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T) :
    ∀ n : ℕ, ∀ X : Fn → Fn, IsWordLe n X → ∀ (v : ℝ → Fn) (vd : Fn),
      (∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (v s)) →
      Work.FTS.EllipticEst.SmoothOpen vd →
      (∀ j i : ℕ, j + i ≤ n →
        Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α)
          (fun s => Work.Spaces.mixed j i (v s)) (Work.Spaces.mixed j i vd) τ) →
      Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α)
        (fun s => X (v s)) (X vd) τ := by
  intro n X hX
  induction hX with
  | id =>
      intro v vd hsm hsmd hj
      simpa using hj 0 0 (by omega)
  | dth hY ih =>
      intro v vd hsm hsmd hj
      refine ih (fun s => Work.Spaces.Dth (v s)) (Work.Spaces.Dth vd)
        (fun s hs => (hsm s hs).Dth) hsmd.Dth ?_
      intro j i hji
      have houter := hj j (i + 1) (by omega)
      simpa only [mixed_Dth_shift] using houter
  | dz hY ih =>
      intro v vd hsm hsmd hj
      refine ih (fun s => Work.Spaces.Dz (v s)) (Work.Spaces.Dz vd)
        (fun s hs => (hsm s hs).Dz) hsmd.Dz ?_
      intro j i hji
      refine EnergyDeriv_congr (hj (j + 1) i (by omega)) ?_ ?_
      · filter_upwards [Icc_mem_nhds hτIoo.1 hτIoo.2] with s hs
        exact H1IP_congr_Q0 α
          (fun z θ hq => (mixed_Dz_shift (hsm s hs) j i z θ hq).symm)
          (fun z θ hq => (mixed_Dz_shift (hsm s hs) j i z θ hq).symm)
      · exact H1IP_congr_Q0 α
          (fun z θ hq => (mixed_Dz_shift hsmd j i z θ hq).symm)
          (fun z θ hq => (mixed_Dz_shift (hsm τ ⟨hτIoo.1.le, hτIoo.2.le⟩) j i z θ hq).symm)

/-! ## The two instances consumed by `AprioriP` -/

/-- **The level-four energy identity from canonical slot data.**  Slots `D_z^j D_θ^i` of order
`j + i ≤ 3` (the words of length `≤ 3` that the three-fold recursion `IP4 = IPiter 3` needs)
give the `IP4`-energy derivative of the family. -/
theorem energyDeriv_IP4_of_mixed {α : ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) {x : ℝ → Fn} {xdot : Fn}
    {τ T : ℝ} (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (x s))
    (hsmd : Work.FTS.EllipticEst.SmoothOpen xdot)
    (h : ∀ j i : ℕ, j + i ≤ 3 →
      Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α)
        (fun s => Work.Spaces.mixed j i (x s)) (Work.Spaces.mixed j i xdot) τ) :
    Work.FTS.StrongPersist.EnergyDeriv
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) x xdot τ :=
  energyDeriv_IP4_le α c₁ c₂ c₁' c₂' c₁'' c₂''
    (fun X hX => energyDeriv_H1IP_of_word (T := T) hτIoo 3 X hX x xdot hsm hsmd h)

/-- **The level-six energy identity from canonical slot data.**  Slots of order `j + i ≤ 5` give
the `IP6`-energy derivative of the family. -/
theorem energyDeriv_IP6_of_mixed {α : ℝ} (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ)
    {x : ℝ → Fn} {xdot : Fn} {τ T : ℝ} (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (x s))
    (hsmd : Work.FTS.EllipticEst.SmoothOpen xdot)
    (h : ∀ j i : ℕ, j + i ≤ 5 →
      Work.FTS.StrongPersist.EnergyDeriv (Work.Coercivity.H1IP α)
        (fun s => Work.Spaces.mixed j i (x s)) (Work.Spaces.mixed j i xdot) τ) :
    Work.FTS.StrongPersist.EnergyDeriv
      (Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α) x xdot τ :=
  energyDeriv_IP6_le α e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂''
    (fun X hX => energyDeriv_H1IP_of_word (T := T) hτIoo 5 X hX x xdot hsm hsmd h)

end Work.FTS.StrongEps.EpsE4Thr

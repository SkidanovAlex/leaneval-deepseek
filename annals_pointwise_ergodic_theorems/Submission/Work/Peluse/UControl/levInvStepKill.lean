import Mathlib
import Submission.Work.Peluse.UControl.levRoundBase
import Submission.Work.Peluse.UControl.levStepRef

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

variable {d D L : ℕ}

/-! ## Auxiliary facts about the atom sums

The class-reduction step uses the *independence* of the atoms only through the following two
consequences of `subSum_inj`: the renamed atom sums are injective on the subsets of `A`, hence two
distinct classes give distinct differences `liftSub r ω - liftSub r σ`. -/

/-- The renamed atom sums `liftSub r ·` are injective on the subsets of `A` when the atoms are
independent. -/
lemma liftSub_inj {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    {r : ℕ} (hind : LevIndep L A atoms) {ω ω' : Finset (Fin L)} (hω : ω ⊆ A) (hω' : ω' ⊆ A)
    (h : liftSub A atoms r ω = liftSub A atoms r ω') : ω = ω' := by
  have hinj : Function.Injective
      (MvPolynomial.rename (Fin.castLE (Nat.le_add_right L r)) :
        MvPolynomial (Fin L) ℤ → MvPolynomial (Fin (L + r)) ℤ) :=
    MvPolynomial.rename_injective _ (Fin.castLE_injective _)
  exact subSum_inj hind hω hω' (hinj h)

/-- Two distinct classes have distinct differences `liftSub r ω - liftSub r σ`. -/
lemma liftSub_sub_ne {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    {r : ℕ} (hind : LevIndep L A atoms) {σ ω ω' : Finset (Fin L)}
    (hω : ω ⊆ A) (hω' : ω' ⊆ A) (hne : ω ≠ ω') :
    liftSub A atoms r ω - liftSub A atoms r σ ≠ liftSub A atoms r ω' - liftSub A atoms r σ := by
  intro h
  have h1 : liftSub A atoms r ω = liftSub A atoms r ω' := by
    have h2 := congrArg (fun p => p + liftSub A atoms r σ) h
    simpa using h2
  exact hne (liftSub_inj hind hω hω' h1)

/-- **The class-reduction step of the round** (Peluse's Lemma 4.6 in the `LevInv` bookkeeping).

Context.  `LevInv d D A f₀ atoms r K σ X` (defined in
`Submission/Work/Peluse/UControl/levRoundDefs.lean`) is the invariant of one round of Peluse's
Lemma 4.8: `K` is the set of *alive classes* (subsets `ω ⊆ A`, described by the histories
`histOf A f₀ ω`), `σ j` is the shift in force at time `j`, the live slots of degree `D` are exactly
the `(Sum.inr 0, slotHist (histOf A f₀ ω) r w)` with `ω ∈ K`, their leading coefficients are
`liftSub A atoms r ω - liftSub A atoms r (σ (last r))`, and the `(D-1)`-coefficients of the class
`A` satisfy the recursion recorded in the field `coeff_diff`.

Assertion.  If moreover **every** live slot has degree exactly `D` (`halldeg`), the atoms are
independent (`hind`), and `ω₀ ∈ K` with `ω₀ ≠ A`, then stepping at the representative
`(Sum.inr 0, slotHist (histOf A f₀ ω₀) r 0)` of the class `ω₀` maintains the invariant with one
class fewer and the reference moved to `ω₀`: `K' = K.erase ω₀`, `σ' = Fin.snoc σ ω₀`.

Why this is the right statement.  All slots have degree `D`, so the step's effect on the top slots
is `λ_h - λ_{ω₀}`: the class `ω₀` cancels its own leading coefficient (its descendants drop below
degree `D`), while every other class `ω ≠ ω₀` survives with `natDegree = D` and leading coefficient
`liftSub r ω - liftSub r ω₀` — here `hind` is used: `subSum_inj` (`levRoundHolds.lean`) shows that
distinct subsets of `A` have distinct atom sums, so the two leading coefficients differ and nothing
cancels.  The `(D-1)`-coefficient recursion of the surviving class `A` is *unchanged in form*:
`histRen` of the old recursion plus the `ε`-term `D • (λ_A · a_new)`, with
`λ_A = liftSub r A - liftSub r (σ (last r))` — this is exactly the stand-alone lemma
`Work.Peluse.UControl.levCoeffStep` (`levRoundHolds.lean`), which is `LevInv.coeff_diff`'s
computation for *any* step of the round (hydra or class reduction).  Note that the new sum
`∑ j : Fin (r+1), … σ' (Fin.castSucc j) …` has `σ' (Fin.castSucc j) = σ j`, so `levCoeffStep`'s
conclusion (phrased with the *old* `σ`) matches after `Fin.snoc_castSucc`.

Useful lemmas already on disk (`Submission/Work/Peluse/UControl/`): `levCoeffStep`,
`step_coeff_child_diff`, `stepQ_natDegree_le_max`, `step_top_child`, `step_die_child`,
`mem_stepH_iff`, `step_Q`, `init_snoc_eq`, `slotHist_snoc`, `slotHist_natAdd` (in `slotHist_natAdd`),
`subSum_inj`, `histRen_liftSub`, `histRen_X_natAdd`, `histOf_inj`, `subSum_eq_atomSum`,
`natDegree_sub_eq_of_lc_ne` (`levStepRef.lean`), `natDegree_sub_lt_of_lc_eq` (`HistPhase1.lean`),
`Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`, `mem_LevH` (`levCubeDefs.lean`).

The proof of the `coeff_diff` field is identical to the one in `levInv_step_hydra`
(`levRoundHolds.lean`, last field): `rw [step_Q, step_Q]`, apply `levCoeffStep` with the class-`A`
slot data from `hinv.top_mem A hinv.memA`, then `Finset.sum_congr` + `Fin.snoc_castSucc`. -/
theorem levInvStepKill {d D L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} {r : ℕ}
    {K : Finset (Finset (Fin L))} {σ : Fin (r + 1) → Finset (Fin L)}
    {X : HistData d (L + r)} (hinv : LevInv d D A f₀ atoms r K σ X)
    (hind : LevIndep L A atoms)
    (halldeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D)
    {ω₀ : Finset (Fin L)} (hω : ω₀ ∈ K) (hωA : ω₀ ≠ A) :
    LevInv d D A f₀ atoms (r + 1) (K.erase ω₀) (Fin.snoc σ ω₀)
      (X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) r 0)
        ((hinv.top_mem ω₀ hω (0 : Fin r → Bool)).1)) := by
  classical
  set i₀ : InitIdx d := (Sum.inr 0) with hi₀
  set h₀ : Fin (L + r) → Bool := slotHist (histOf A f₀ ω₀) r 0 with hh₀
  have hmem0 : (i₀, h₀) ∈ X.H := by
    rw [hi₀, hh₀]
    exact (hinv.top_mem ω₀ hω (0 : Fin r → Bool)).1
  have hD1 : 1 ≤ D :=
    le_trans (X.hnc (i₀, h₀) hmem0) (le_of_eq (halldeg (i₀, h₀) hmem0))
  change LevInv d D A f₀ atoms (r + 1) (K.erase ω₀) (Fin.snoc σ ω₀) (X.step i₀ h₀ hmem0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `subK`
    intro ω hω'
    exact hinv.subK ω (Finset.mem_of_mem_erase hω')
  · -- `nonemptyK`
    intro ω hω'
    exact hinv.nonemptyK ω (Finset.mem_of_mem_erase hω')
  · -- `memA`
    exact Finset.mem_erase.mpr ⟨fun h => hωA h.symm, hinv.memA⟩
  · -- `sigma_zero`
    rw [show (0 : Fin ((r + 1) + 1)) = Fin.castSucc (0 : Fin (r + 1)) from Fin.ext rfl,
      Fin.snoc_castSucc]
    exact hinv.sigma_zero
  · -- `sigma_sub`
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact hinv.sigma_sub k
    · rw [Fin.snoc_last]
      exact hinv.subK ω₀ hω
  · -- `sigma_ne`
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact hinv.sigma_ne k
    · rw [Fin.snoc_last]
      exact hωA
  · -- `degLe`: both parents have degree `D`, hence so does the child
    intro x hx
    have hx' : x ∈ X.stepH i₀ h₀ := hx
    rw [mem_stepH_iff X i₀ h₀ x] at hx'
    obtain ⟨hxH, -, -⟩ := hx'
    change (X.stepQ i₀ h₀ x.1 x.2).natDegree ≤ D
    refine le_trans (stepQ_natDegree_le_max X i₀ h₀ x.1 x.2) (max_le ?_ ?_)
    · exact le_of_eq (halldeg _ hxH)
    · exact le_of_eq (halldeg _ hmem0)
  · -- `top_mem`: the class `ω ≠ ω₀` survives, with the reference moved to `ω₀`
    intro ω hω' w
    have hωK : ω ∈ K := Finset.mem_of_mem_erase hω'
    have hωne : ω ≠ ω₀ := (Finset.mem_erase.mp hω').1
    have hωA' : ω ⊆ A := hinv.subK ω hωK
    have hω₀A : ω₀ ⊆ A := hinv.subK ω₀ hω
    have hpar_hist : slotHist (histOf A f₀ ω) (r + 1) w
        = Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w))
            (w (Fin.last r)) := by
      conv_lhs => rw [← Fin.snoc_init_self (q := w)]
      exact slotHist_snoc _ _ _
    have hinit : Fin.init (slotHist (histOf A f₀ ω) (r + 1) w)
        = slotHist (histOf A f₀ ω) r (Fin.init w) := by
      rw [hpar_hist]
      exact Fin.init_snoc _ _
    set A' := (((X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω) r (Fin.init w))).map
          (histRen (L + r))).comp
        (Polynomial.X + Polynomial.C (stepShift (slotHist (histOf A f₀ ω) (r + 1) w))))
      with hA'def
    set B' := ((X.Q (Sum.inr 0) h₀).map (histRen (L + r))) with hB'def
    have hA'deg : A'.natDegree = D := by
      rw [hA'def, histComp_natDegree]
      exact (hinv.top_mem ω hωK (Fin.init w)).2.1
    have hB'deg : B'.natDegree = D := by
      rw [hB'def, histMap_natDegree]
      exact halldeg _ hmem0
    have hA'lc : A'.leadingCoeff
        = histRen (L + r) (liftSub A atoms r ω - liftSub A atoms r (σ (Fin.last r))) := by
      rw [hA'def, histComp_leadingCoeff]
      exact congrArg (histRen (L + r)) (hinv.top_mem ω hωK (Fin.init w)).2.2
    have hB'lc : B'.leadingCoeff
        = histRen (L + r) (liftSub A atoms r ω₀ - liftSub A atoms r (σ (Fin.last r))) := by
      rw [hB'def, histMap_leadingCoeff]
      exact congrArg (histRen (L + r)) (hinv.top_mem ω₀ hω 0).2.2
    have hne_lc : A'.leadingCoeff ≠ B'.leadingCoeff := by
      rw [hA'lc, hB'lc]
      intro hh
      exact liftSub_sub_ne (σ := σ (Fin.last r)) (ω := ω) (ω' := ω₀) hind hωA' hω₀A hωne
        (histRen_injective (L + r) hh)
    obtain ⟨hdegC, hlcC⟩ := natDegree_sub_eq_of_lc_ne hA'deg hB'deg hne_lc
    have hsub : X.stepQ i₀ h₀ (Sum.inr 0) (slotHist (histOf A f₀ ω) (r + 1) w) = A' - B' := by
      rw [hA'def, hB'def, stepQ_eq, hinit]
    have hdeg_child :
        (X.stepQ i₀ h₀ (Sum.inr 0) (slotHist (histOf A f₀ ω) (r + 1) w)).natDegree = D := by
      rw [hsub]
      exact hdegC
    have hlc_child :
        (X.stepQ i₀ h₀ (Sum.inr 0) (slotHist (histOf A f₀ ω) (r + 1) w)).leadingCoeff
          = liftSub A atoms (r + 1) ω - liftSub A atoms (r + 1) ω₀ := by
      rw [hsub, hlcC, hA'lc, hB'lc]
      simp only [map_sub, histRen_liftSub]
      ring
    have hmemC : ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ ω) (r + 1) w) ∈ X.stepH i₀ h₀ := by
      rw [mem_stepH_iff X i₀ h₀]
      refine ⟨?_, ?_, ?_⟩
      · rw [hinit]
        exact (hinv.top_mem ω hωK (Fin.init w)).1
      · intro heq
        have h1 : Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w))
              (w (Fin.last r)) = Fin.snoc (α := fun _ => Bool) h₀ false := by
          have hh := congrArg Prod.snd heq
          rwa [hpar_hist] at hh
        have h2 : slotHist (histOf A f₀ ω) r (Fin.init w) = h₀ := by
          have h3 := congrArg (fun f : Fin (L + r + 1) → Bool => Fin.init f) h1
          simpa [init_snoc_eq, Fin.init_snoc] using h3
        have h4 : histOf A f₀ ω = histOf A f₀ ω₀ := by
          have h5 : slotHist (histOf A f₀ ω) r (Fin.init w)
              = slotHist (histOf A f₀ ω₀) r 0 := by
            rw [h2, hh₀]
          funext i
          have h6 := congrFun h5 (Fin.castAdd r i)
          simpa [slotHist_castAdd] using h6
        exact hωne (histOf_inj hωA' hω₀A h4)
      · rw [hdeg_child]
        exact hD1
    refine ⟨hmemC, ?_, ?_⟩
    · rw [step_Q X i₀ h₀ hmem0 (Sum.inr 0, slotHist (histOf A f₀ ω) (r + 1) w)]
      exact hdeg_child
    · rw [step_Q X i₀ h₀ hmem0 (Sum.inr 0, slotHist (histOf A f₀ ω) (r + 1) w)]
      rw [hlc_child, Fin.snoc_last]
  · -- `top_only`: only the classes `ω ≠ ω₀` survive at degree `D`
    intro x hx hxdeg
    have hx' : x ∈ X.stepH i₀ h₀ := hx
    rw [mem_stepH_iff X i₀ h₀ x] at hx'
    obtain ⟨hxH, hxne, -⟩ := hx'
    obtain ⟨x1, x2⟩ := x
    simp only at hxH hxne hxdeg
    have hpar : (X.Q x1 (Fin.init x2)).natDegree = D := halldeg _ hxH
    obtain ⟨hx1, ω, hωK, w, hxw⟩ :=
      hinv.top_only (x1, Fin.init x2) hxH (le_of_eq hpar.symm)
    simp only at hx1 hxw
    have hωne : ω ≠ ω₀ := by
      intro hωeq
      have hxdeg' : D ≤ (X.stepQ i₀ h₀ x1 x2).natDegree := hxdeg
      have hlc_eq : (X.Q x1 (Fin.init x2)).leadingCoeff = (X.Q i₀ h₀).leadingCoeff := by
        rw [hx1, hxw, hωeq, hh₀]
        exact (hinv.top_mem ω₀ hω w).2.2.trans ((hinv.top_mem ω₀ hω 0).2.2).symm
      have hlt := step_die_child X i₀ h₀ x1 x2 hD1 hpar (halldeg _ hmem0) hlc_eq
      omega
    refine ⟨hx1, ω, Finset.mem_erase.mpr ⟨hωne, hωK⟩,
      Fin.snoc w (x2 (Fin.last (L + r))), ?_⟩
    change x2 = slotHist (histOf A f₀ ω) (r + 1) (Fin.snoc w (x2 (Fin.last (L + r))))
    conv_lhs => rw [← Fin.snoc_init_self (q := x2)]
    rw [show (Fin.init x2 : Fin (L + r) → Bool) = slotHist (histOf A f₀ ω) r w from hxw,
      ← slotHist_snoc]
    rfl
  · -- `coeff_diff`: the stand-alone coefficient lemma `levCoeffStep`
    intro w
    have hA_deg : ∀ u : Fin r → Bool,
        (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r u)).natDegree = D :=
      fun u => halldeg _ (hinv.top_mem A hinv.memA u).1
    have hA_lead : ∀ u : Fin r → Bool,
        (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r u)).coeff D
          = liftSub A atoms r A - liftSub A atoms r (σ (Fin.last r)) := fun u => by
      rw [← (hinv.top_mem A hinv.memA u).2.1, Polynomial.coeff_natDegree]
      exact (hinv.top_mem A hinv.memA u).2.2
    rw [step_Q X i₀ h₀ hmem0 (Sum.inr 0, slotHist (histOf A f₀ A) (r + 1) w),
      step_Q X i₀ h₀ hmem0 (Sum.inr 0, slotHist (histOf A f₀ A) (r + 1) 0)]
    rw [levCoeffStep (X := X) (Sum.inr 0) h₀ hA_deg hA_lead hinv.coeff_diff w]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.snoc_castSucc]

end

end Work.Peluse.UControl

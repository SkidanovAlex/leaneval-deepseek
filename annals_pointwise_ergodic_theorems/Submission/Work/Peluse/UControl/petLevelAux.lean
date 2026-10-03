import Mathlib
import Submission.Work.Peluse.UControl.levReachAnalytic
import Submission.Work.Peluse.UControl.levelCompareDefs
import Submission.Work.Peluse.UControl.levDInvStep

/-!
# Auxiliary lemmas of the level chain of `petChapter5Holds`

This file collects the four ingredients of the assembly of `petLevelChainGen`:

* `petStepConstsClosing` — the closing step of a round has *no* `y`-constant children, i.e.
  `petStepConsts` is empty there.  This is what makes the base function of the terminal state a
  *single* slot function of the pre-closing state (and hence of the `Ftop`-form).
* `reachAnalyticTop` — `reach_analytic` (`levReachAnalytic.lean`) with the extra conjunct that the
  slot functions stay of the `Ftop`-form (`Ftop` or its conjugate, pointwise).
* `levRoundExposed` — one round of Peluse's Lemma 4.8 with the *closing step exposed*: the
  pre-closing state `W`, its `LevInv`-structure (with the single class `{A}` and all slots of degree
  exactly `D`), `Reach X W`, and the terminal data written out in terms of `W`.
* `levDatumIterateMid` — the iteration of the round from level `1` to level `d - 2` (instead of
  `d - 1`), so that the *last* round can be applied through `levRoundExposed`.

`/tmp` is not writable in this sandbox: `export TMPDIR=$PWD/.tmpdir` before any Lean invocation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial
open Work.Peluse.UControl.PetStep

attribute [local instance] Classical.propDecidable

variable {d D L : ℕ}

/-! ## 1. The closing step has no `y`-constant children -/

/-- The bridge between the slot polynomials of the *symbolic* step and the `stepQ` of the history
step: at a child `((a,h),ε)` the symbolic polynomial is `X.stepQ i₀ h₀ a (snoc h ε)`. -/
lemma stepP_toSym_step {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (j : ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).ι) :
    ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P j
      = X.stepQ i₀ h₀ j.1.1.1.1 (Fin.snoc j.1.1.1.2 j.1.2) := by
  simp only [HistData.toSym, PetStateSym.step, HistData.stepQ, Fin.init_snoc, Fin.snoc_last]
  rfl

/-- **The closing step has no `y`-constant children.**  If the round state has the single class
`{A}`, all its slots of degree exactly `D ≥ 2`, then stepping at the representative of the class `A`
(the closing step) produces children of degree `≥ 1` only. -/
theorem petStepConstsClosing {d D L r : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} {K : Finset (Finset (Fin L))}
    {σ : Fin (r + 1) → Finset (Fin L)} {X : HistData d (L + r)}
    (hinv : LevInv d D A f₀ atoms r K σ X) (hind : LevIndep L A atoms) (hD : 2 ≤ D)
    (halldeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D) (hK : K = {A})
    (h : ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) r 0) ∈ X.H) :
    petStepConsts (X.toSym).S ⟨((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) r 0), h⟩ = ∅ := by
  classical
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨j, hj⟩
  simp only [petStepConsts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hdeg := hj
  -- the parent slot is live and of degree `D`, hence of the canonical form
  have hmem : j.1.1.1 ∈ X.H := j.1.1.2
  have hdegD : (X.Q j.1.1.1.1 j.1.1.1.2).natDegree = D := halldeg _ hmem
  obtain ⟨ha, ω, hω, w, hw⟩ := hinv.top_only j.1.1.1 hmem (le_of_eq hdegD.symm)
  have hωA : ω = A := by
    have h1 : ω ∈ ({A} : Finset (Finset (Fin L))) := by rw [← hK]; exact hω
    simpa using h1
  -- the child is not the excluded one, hence its history is nonzero
  have hu : Fin.snoc w j.1.2 ≠ (0 : Fin (r + 1) → Bool) := by
    intro hcontra
    apply j.2
    have hw0 : w = 0 := by
      funext i
      have h1 := congrFun hcontra (Fin.castSucc i)
      rw [Fin.snoc_castSucc] at h1
      exact h1
    have hε : j.1.2 = false := by
      have h1 := congrFun hcontra (Fin.last r)
      rw [Fin.snoc_last] at h1
      exact h1
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      exact Prod.ext ha (by rw [hw, hωA, hw0])
    · exact hε
  -- the degree of the child
  have hcl := levClosingCoeff (D := D) (X := X) hinv hind hD halldeg hK (Fin.snoc w j.1.2) hu
  have hne : (((X.toSym).S.step
      ⟨((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) r 0), h⟩).P j).natDegree ≠ 0 := by
    rw [stepP_toSym_step X (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) h j, ha, hw, hωA,
      ← slotHist_snoc (histOf A f₀ A) w j.1.2]
    show (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
      (slotHist (histOf A f₀ A) (r + 1) (Fin.snoc w j.1.2))).natDegree ≠ 0
    rw [hcl.1]
    omega
  exact hne hdeg

/-! ## 2. The analytic transfer with the `Ftop`-form of the slots -/

/-- The successor's slot functions stay of the `Ftop`-form. -/
lemma levNextF_form {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (F : (X.toSym).S.ι → ℤ → ℂ) {Ftop : ℤ → ℂ}
    (hF : ∀ i, (∀ x, F i x = Ftop x) ∨ (∀ x, F i x = star (Ftop x))) :
    ∀ i, (∀ x, levNextF X i₀ h₀ hh F i x = Ftop x) ∨
      (∀ x, levNextF X i₀ h₀ hh F i x = star (Ftop x)) := by
  intro i
  rcases hF (X.stepIdx i₀ h₀ hh i).1.1 with h | h
  · by_cases hε : (X.stepIdx i₀ h₀ hh i).1.2 = true
    · right
      intro x
      simp only [levNextF, stepF, hε, if_true]
      exact congrArg star (h x)
    · left
      intro x
      simp only [levNextF, stepF, hε, if_false]
      exact h x
  · by_cases hε : (X.stepIdx i₀ h₀ hh i).1.2 = true
    · left
      intro x
      simp only [levNextF, stepF, hε, if_true]
      rw [h x, star_star]
    · right
      intro x
      simp only [levNextF, stepF, hε, if_false]
      exact h x

/-- **The analytic transfer along a chain of PET steps, with the `Ftop`-form of the slots.**
`reach_analytic` (`levReachAnalytic.lean`) with one extra hypothesis and one extra conclusion
conjunct: if every slot function of the initial state is pointwise `Ftop` or pointwise
`star Ftop`, then so is every slot function of the terminal state. -/
theorem reachAnalyticTop {d : ℕ} :
    ∀ {L L' : ℕ} (X : HistData d L) (X' : HistData d L') (hr : Reach X X')
      (N M c Dsb : ℕ) (γ' B : ℝ) (Ftop : ℤ → ℂ) (F : (X.toSym).S.ι → ℤ → ℂ)
      (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat L → ℤ → ℂ),
      0 < N → 0 < M → 0 < γ' → γ' ≤ 1 → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat → 0 < B → B ≤ 1 →
      (L' - L) + 1 ≤ c →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
      (∀ a x, ‖g a x‖ ≤ 1) → (∀ a, SupportIn (g a) N) →
      (∀ k < L' - L, γ' ≤ petChainLevel B k ^ 2 / (20000 * ((((2 : ℕ) ^ k * Dsb : ℕ) : ℝ) + 1))) →
      (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb →
      B ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.lam N M →
      (∀ i, (∀ x, F i x = Ftop x) ∨ (∀ x, F i x = star (Ftop x))) →
      ∃ (F' : (X'.toSym).S.ι → ℤ → ℂ)
        (g' : WinTower ⌊γ' * (M : ℝ)⌋.toNat L' → ℤ → ℂ),
        (∀ i x, ‖F' i x‖ ≤ 1) ∧ (∀ i, SupportIn (F' i) N) ∧
        (∀ a x, ‖g' a x‖ ≤ 1) ∧ (∀ a, SupportIn (g' a) N) ∧
        petChainLevel B (L' - L) ≤ (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.lam N M ∧
        (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.ShiftBound N M (c - (L' - L))
          ((2 : ℕ) ^ (L' - L) * Dsb) ∧
        (∀ i, (∀ x, F' i x = Ftop x) ∨ (∀ x, F' i x = star (Ftop x))) := by
  intro L L' X X' hr
  refine Reach.rec (motive := fun {L L'} (X : HistData d L) (X' : HistData d L')
      (_ : Reach X X') =>
      ∀ (N M c Dsb : ℕ) (γ' B : ℝ) (Ftop : ℤ → ℂ) (F : (X.toSym).S.ι → ℤ → ℂ)
        (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat L → ℤ → ℂ),
        0 < N → 0 < M → 0 < γ' → γ' ≤ 1 → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat → 0 < B → B ≤ 1 →
        (L' - L) + 1 ≤ c →
        (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
        (∀ a x, ‖g a x‖ ≤ 1) → (∀ a, SupportIn (g a) N) →
        (∀ k < L' - L, γ' ≤ petChainLevel B k ^ 2 /
          (20000 * ((((2 : ℕ) ^ k * Dsb : ℕ) : ℝ) + 1))) →
        (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.ShiftBound N M c Dsb →
        B ≤ (histPet X ⌊γ' * (M : ℝ)⌋.toNat F g).toState.lam N M →
        (∀ i, (∀ x, F i x = Ftop x) ∨ (∀ x, F i x = star (Ftop x))) →
        ∃ (F' : (X'.toSym).S.ι → ℤ → ℂ)
          (g' : WinTower ⌊γ' * (M : ℝ)⌋.toNat L' → ℤ → ℂ),
          (∀ i x, ‖F' i x‖ ≤ 1) ∧ (∀ i, SupportIn (F' i) N) ∧
          (∀ a x, ‖g' a x‖ ≤ 1) ∧ (∀ a, SupportIn (g' a) N) ∧
          petChainLevel B (L' - L) ≤ (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.lam N M ∧
          (histPet X' ⌊γ' * (M : ℝ)⌋.toNat F' g').toState.ShiftBound N M (c - (L' - L))
            ((2 : ℕ) ^ (L' - L) * Dsb) ∧
          (∀ i, (∀ x, F' i x = Ftop x) ∨ (∀ x, F' i x = star (Ftop x)))) ?_ ?_ hr
  · -- `refl`
    intro L X N M c Dsb γ' B Ftop F g _ _ _ _ _ _ _ _ hFb hFs hfb hfs _ hSB hlam htop
    exact ⟨F, g, hFb, hFs, hfb, hfs, by simpa using hlam, by simpa using hSB, htop⟩
  · -- `step`
    intro L X i₀ h₀ hh L' Z hrest ih
    intro N M c Dsb γ' B Ftop F g hN hM hγ'0 hγ'1 hH hB0 hB1 hc hFb hFs hfb hfs hw hSB hlam htop
    have hlen := reach_length_le hrest
    have hc1 : 1 ≤ c := by omega
    have hw0 : γ' ≤ B ^ 2 / (20000 * ((Dsb : ℝ) + 1)) := by
      simpa using hw 0 (by omega)
    have hlam₁ := levStepAnalytic_lam_named X i₀ h₀ hh N M c Dsb γ' B F g
      hN hM hγ'0 hH hc1 hB0 hB1 hFb hFs hfb hfs hw0 hSB hlam
    have hSB₁ := levStepAnalytic_sb_named X i₀ h₀ hh N M c Dsb γ' F g hγ'0 hγ'1
      (by omega) hSB
    have hFb₁ : ∀ i x, ‖levNextF X i₀ h₀ hh F i x‖ ≤ 1 := levNextF_bdd X i₀ h₀ hh F hFb
    have hFs₁ : ∀ i, SupportIn (levNextF X i₀ h₀ hh F i) N := levNextF_supp X i₀ h₀ hh F hFs
    have hfb₁ : ∀ a x, ‖levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g a x‖ ≤ 1 :=
      levNextg_bdd X i₀ h₀ hh _ F g hFb
    have hfs₁ : ∀ a, SupportIn (levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g a) N :=
      levNextg_supp X i₀ h₀ hh _ F g hFs
    have hB0₁ : 0 < petChainLevel B 1 := petChainLevel_pos B hB0 1
    have hB1₁ : petChainLevel B 1 ≤ 1 := petChainLevel_le_one B hB0 hB1 1
    have hw₁ : ∀ k < L' - (L + 1), γ' ≤ petChainLevel (petChainLevel B 1) k ^ 2 /
        (20000 * ((((2 : ℕ) ^ k * (2 * Dsb) : ℕ) : ℝ) + 1)) := by
      intro k hk
      have h2 := hw (k + 1) (by omega)
      have h3 : petChainLevel (petChainLevel B 1) k = petChainLevel B (k + 1) :=
        petChainLevel_div B k
      have h4 : (((2 : ℕ) ^ (k + 1) * Dsb : ℕ) : ℝ) = (((2 : ℕ) ^ k * (2 * Dsb) : ℕ) : ℝ) := by
        push_cast [pow_succ]
        ring
      simpa [← h3, ← h4] using h2
    have hc₁ : (L' - (L + 1)) + 1 ≤ c - 1 := by omega
    obtain ⟨F₂, g₂, hFb₂, hFs₂, hfb₂, hfs₂, hlam₂, hSB₂, htop₂⟩ :=
      ih N M (c - 1) (2 * Dsb) γ' (petChainLevel B 1) Ftop
        (levNextF X i₀ h₀ hh F) (levNextg X i₀ h₀ hh ⌊γ' * (M : ℝ)⌋.toNat F g)
        hN hM hγ'0 hγ'1 hH hB0₁ hB1₁ hc₁ hFb₁ hFs₁ hfb₁ hfs₁ hw₁ hSB₁ hlam₁
        (levNextF_form X i₀ h₀ hh F htop)
    refine ⟨F₂, g₂, hFb₂, hFs₂, hfb₂, hfs₂, ?_, ?_, htop₂⟩
    · have h2 := hlam₂
      have h2' := (petChainLevel_div B (L' - (L + 1))) ▸ h2
      convert h2' using 2
      omega
    · have h2 := hSB₂
      have h5 : (c - 1) - (L' - (L + 1)) = c - (L' - L) := by omega
      have h7 : L' - L = (L' - (L + 1)) + 1 := by omega
      have h6 : ((2 : ℕ) ^ (L' - (L + 1)) * (2 * Dsb) : ℕ) = ((2 : ℕ) ^ (L' - L) * Dsb : ℕ) := by
        rw [h7, pow_succ]
        ring
      simpa [h5, h6] using h2

/-! ## 3. The round with the closing step exposed -/

/-- **One round of Peluse's Lemma 4.8 with the closing step exposed.**  The output is the *pre-closing*
state `W` (with the single class `{A}`, all slots of degree exactly `D`), the `Reach`-chain to it,
and the closing step's terminal data written out explicitly. -/
theorem levRoundExposed (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) (hind : LevIndep L A atoms) (hD : 2 ≤ D)
    (hAcard : 2 ≤ A.card) (X : HistData d L) (hX : LevCube d D L A f₀ atoms X) :
    ∃ (M : ℕ) (σ : Fin (M + 1) → Finset (Fin L)) (W : HistData d (L + M))
      (hh : ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) M 0) ∈ W.H),
      LevInv d D A f₀ atoms M {A} σ W ∧
      (∀ x ∈ W.H, (W.Q x.1 x.2).natDegree = D) ∧
      3 ≤ M + 1 ∧
      Reach X W ∧
      (∀ s : {s : Fin (L + (M + 1)) // s ∈ freshFin L (M + 1)}, (freshSet A σ s).Nonempty) ∧
      (∀ s : {s : Fin (L + (M + 1)) // s ∈ freshFin L (M + 1)},
        slotHist (histOf A f₀ A) (M + 1) 0 s.1 = false) ∧
      (∀ s : {s : Fin (L + (M + 1)) // s ∈ freshFin L (M + 1)},
        closingAtoms A atoms D M σ s = MvPolynomial.C (D : ℤ) *
          ((∑ s' ∈ freshSet A σ s,
              MvPolynomial.rename (Fin.castLE (Nat.le_add_right L (M + 1))) (atoms s'))
            * MvPolynomial.X s.1)) ∧
      LevIndep (L + (M + 1)) (freshFin L (M + 1)) (closingAtoms A atoms D M σ) ∧
      LevCube d (D - 1) (L + (M + 1)) (freshFin L (M + 1))
        (slotHist (histOf A f₀ A) (M + 1) 0) (closingAtoms A atoms D M σ)
        (W.step (Sum.inr 0) (slotHist (histOf A f₀ A) M 0) hh) := by
  classical
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hD1 : 1 ≤ D := by omega
  have hD0 : 0 < D := by omega
  have hinit := levInvInit (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms) hind hD1 hAne hX
  let S : RState d D L A f₀ atoms :=
    ⟨0, X, Finset.univ.filter (fun ω : Finset (Fin L) => ω ⊆ A ∧ ω.Nonempty),
      (fun _ => ∅), hinit⟩
  obtain ⟨S', hreach, halldeg, hK, hcard⟩ :=
    loop_spec_card (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms) hind
      (fun {r K σ X} hinv halldeg' {ω₀} hω hωA =>
        levInvStepKill (d := d) (D := D) (A := A) (f₀ := f₀) (atoms := atoms)
          hinv hind halldeg' hω hωA) S
  have hspec := closingAtomsSpec (A := A) (atoms := atoms) (f₀ := f₀) hind S'.inv.sigma_sub
    S'.inv.sigma_ne hD0
  have hmem : ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) S'.r 0) ∈ S'.X.H :=
    (S'.inv.top_mem A S'.inv.memA (0 : Fin S'.r → Bool)).1
  have hKcard : S.K.card = 2 ^ A.card - 1 := by
    have hSK : S.K = A.powerset.erase ∅ := by
      ext ω
      constructor
      · intro h
        rw [Finset.mem_filter] at h
        exact Finset.mem_erase.mpr
          ⟨Finset.nonempty_iff_ne_empty.mp h.2.2, Finset.mem_powerset.mpr h.2.1⟩
      · intro h
        rw [Finset.mem_erase] at h
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_powerset.mp h.2,
            Finset.nonempty_iff_ne_empty.mpr h.1⟩
    rw [hSK, Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.empty_subset A)),
      Finset.card_powerset]
  have hSr : S.r = 0 := rfl
  have h3M : 3 ≤ S'.r + 1 := by
    have hKA : S'.K.card = 1 := by rw [hK]; simp
    rw [hKA, hSr, hKcard] at hcard
    have h4 : 4 ≤ 2 ^ A.card := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hAcard
      simpa using h
    omega
  refine ⟨S'.r, S'.σ, S'.X, hmem, hK ▸ S'.inv, halldeg, h3M, hreach, ?_, ?_, ?_, hspec.1, ?_⟩
  · -- the killed classes are proper subsets of `A`, so `freshSet A σ s` is nonempty
    intro s
    unfold freshSet
    refine Finset.image_nonempty.mpr ?_
    rw [Finset.attach_nonempty_iff]
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    exact S'.inv.sigma_ne (freshIdx s)
      (Finset.Subset.antisymm (S'.inv.sigma_sub (freshIdx s))
        (Finset.sdiff_eq_empty_iff_subset.mp hcon))
  · -- the frozen vector of the output is false on the fresh coordinates
    intro s
    have h1 : (Fin.natAdd L (freshIdx (L := L) (r := S'.r + 1) s) :
        Fin (L + (S'.r + 1))) = s.1 := natAdd_freshIdx s
    rw [← h1, slotHist_natAdd]
    rfl
  · -- the closing atoms are the definition's
    intro s
    rfl
  · -- the closing step
    exact levRoundClosing (A := A) (f₀ := f₀) (atoms := atoms) S'.inv hind hD halldeg hK

/-! ## 4. The iteration of the round up to level `d - 2` -/

/-- **The iteration of the round, stopped at level `d - 2`.**  From a `LevDInv`-state at level `j`
with `j + k = d - 2` one reaches, by `k` rounds, a `LevDInv`-state at level `d - 2` whose `LevCube`
state has degree `2` and whose parameter set is non-degenerate. -/
theorem levDatumIterateMid {d : ℕ} {lc : ℤ} (hd : 2 ≤ d) (k : ℕ) :
    ∀ (j L : ℕ) (hL : 1 ≤ L) (N : ℕ → ℕ) (P : ℕ → ℕ → Finset ℕ) (c : ℕ → ℕ → ℕ)
      (X : HistData d L) (f₀ : Fin L → Bool)
      (atoms : {s : Fin L // s ∈ lvlSet N c L j hL} → MvPolynomial (Fin L) ℤ),
      j + k = d - 2 →
      2 ≤ (lvlSet N c L j hL).card →
      LevDInv d lc j L hL N P c X f₀ →
      LevCube d (d - j) L (lvlSet N c L j hL) f₀ atoms X →
      LevIndep L (lvlSet N c L j hL) atoms →
      ∃ (L' : ℕ) (hL' : 1 ≤ L') (N' : ℕ → ℕ) (P' : ℕ → ℕ → Finset ℕ) (c' : ℕ → ℕ → ℕ)
        (X' : HistData d L') (f₀' : Fin L' → Bool)
        (atoms' : {s : Fin L' // s ∈ lvlSet N' c' L' (d - 2) hL'} → MvPolynomial (Fin L') ℤ),
        LevDInv d lc (d - 2) L' hL' N' P' c' X' f₀' ∧
        LevCube d 2 L' (lvlSet N' c' L' (d - 2) hL') f₀' atoms' X' ∧
        LevIndep L' (lvlSet N' c' L' (d - 2) hL') atoms' ∧
        2 ≤ (lvlSet N' c' L' (d - 2) hL').card ∧ Reach X X' := by
  induction k with
  | zero =>
      intro j L hL N P c X f₀ atoms hj hcard h1 h2 h3
      have hj' : j = d - 2 := by omega
      subst hj'
      have h2' : LevCube d 2 L (lvlSet N c L (d - 2) hL) f₀ atoms X := by
        rw [show d - (d - 2) = 2 from by omega] at h2
        exact h2
      exact ⟨L, hL, N, P, c, X, f₀, atoms, h1, h2', h3, hcard, Reach.refl X⟩
  | succ k ih =>
      intro j L hL N P c X f₀ atoms hj hcard h1 h2 h3
      have hjd : j < d - 2 := by omega
      have hD : 2 ≤ d - j := by omega
      obtain ⟨Nnew, A', f₀', Pround, atoms', X', hA', hf0', hcard', hPne, hat, hindep, hcube,
        hreach⟩ :=
        levRoundUHolds d (d - j) L (lvlSet N c L j hL) f₀ atoms h3 hD X h2
      have hL' : 1 ≤ L + Nnew := by omega
      have hat' : ∀ s, atoms' s = MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
          ((∑ s' ∈ Pround s, MvPolynomial.rename (Fin.castLE (Nat.le_add_right L Nnew)) (atoms s'))
            * MvPolynomial.X s.1) := by
        intro s
        rw [hat s, show (((d - j : ℕ)) : ℤ) = (d : ℤ) - (j : ℤ) from Nat.cast_sub (by omega)]
      have hstep := levDInvStep hL hL' h1 hA' hf0' h2 hPne hat' hcube
      have hset : lvlSet (stepN N Nnew j) (stepC c L j) (L + Nnew) (j + 1) hL' = A' :=
        lvlSet_step (N := N) (c := c) (j := j) hA' hL'
      subst hset
      have hcube' : LevCube d (d - (j + 1)) (L + Nnew)
          (lvlSet (stepN N Nnew j) (stepC c L j) (L + Nnew) (j + 1) hL') f₀' atoms' X' := by
        rw [show d - j - 1 = d - (j + 1) from (Nat.sub_succ d j).symm] at hcube
        exact hcube
      have hcard2 : 2 ≤ (lvlSet (stepN N Nnew j) (stepC c L j) (L + Nnew) (j + 1) hL').card :=
        hcard' hcard
      obtain ⟨L'', hL'', N'', P'', c'', X'', f₀'', atoms'', hiter, hcube'', hind'', hcard3,
        hreach3⟩ :=
        ih (j + 1) (L + Nnew) hL' (stepN N Nnew j) (stepPAll h1 hA' Pround) (stepC c L j)
          X' f₀' atoms' (by omega) hcard2 hstep hcube' hindep
      exact ⟨L'', hL'', N'', P'', c'', X'', f₀'', atoms'', hiter, hcube'', hind'', hcard3,
        Reach.trans hreach hreach3⟩

/-! ## 5. Two elementary tools of the assembly -/

/-- Dropping the empty set of slots does not change the base function. -/
lemma PetStateP.drop_empty_f (S : PetStateP) (a : S.Ω) (x : ℤ) :
    (S.drop ∅).f a x = S.f a x := by
  show S.f a x * ∏ i ∈ (∅ : Finset S.ι), S.F i (x + (S.P i a).eval 0) = S.f a x
  rw [Finset.prod_empty, mul_one]

/-- With no `y`-constant children, the base function of one PET step is the reference slot function
(no factor is absorbed into the base). -/
lemma levNextg_eq_ref {d n H : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (F : (X.toSym).S.ι → ℤ → ℂ) (g : WinTower H n → ℤ → ℂ)
    (hJ : petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩ = ∅) (a : WinTower H (n + 1)) (x : ℤ) :
    levNextg X i₀ h₀ hh H F g a x = F ⟨(i₀, h₀), hh⟩ x := by
  have h1 : levNextg X i₀ h₀ hh H F g a x
      = (((X.toSym).S.toPetP H F g).step ⟨(i₀, h₀), hh⟩ H).f a x := by
    show ((((X.toSym).S.toPetP H F g).step ⟨(i₀, h₀), hh⟩ H).drop
      (petStepConsts (X.toSym).S ⟨(i₀, h₀), hh⟩)).f a x = _
    rw [hJ]
    exact PetStateP.drop_empty_f (((X.toSym).S.toPetP H F g).step ⟨(i₀, h₀), hh⟩ H) a x
  rw [h1]
  rfl

/-- The shift bound is monotone: a smaller range and a larger constant give a weaker statement. -/
lemma shiftBound_mono {S : PetState} {N M c₁ c₂ D₁ D₂ : ℕ} (hc : c₂ ≤ c₁) (hD : D₁ ≤ D₂)
    (h : S.ShiftBound N M c₁ D₁) : S.ShiftBound N M c₂ D₂ := by
  intro i a z hz
  have hc' : (c₂ : ℤ) ≤ (c₁ : ℤ) := by exact_mod_cast hc
  have hD' : (D₁ : ℤ) ≤ (D₂ : ℤ) := by exact_mod_cast hD
  have hM : (0 : ℤ) ≤ (M : ℤ) := by omega
  have hN : (0 : ℤ) ≤ (N : ℤ) := by omega
  have hz' : |z| ≤ (c₁ : ℤ) * (M : ℤ) := le_trans hz (by nlinarith)
  have h1 := h i a z hz'
  calc |S.Q i a z| ≤ (D₁ : ℤ) * (N : ℤ) := h1
    _ ≤ (D₂ : ℤ) * (N : ℤ) := by nlinarith

/-- The cardinality of the window tower. -/
lemma card_WinTower (H : ℕ) : ∀ L : ℕ, Fintype.card (WinTower H L) = (2 * H + 1) ^ L := by
  intro L
  induction L with
  | zero => rw [pow_zero]; exact Fintype.card_fin 1
  | succ L ih =>
    rw [pow_succ]
    calc Fintype.card (WinTower H (L + 1))
        = Fintype.card (WinTower H L) * Fintype.card (Fin (2 * H + 1)) := Fintype.card_prod _ _
      _ = (2 * H + 1) ^ L * (2 * H + 1) := by rw [ih, Fintype.card_fin]

/-- The attachments of a `LevDInv`-state, extended above the top level (where they are vacuous). -/
lemma levDInv_sub {d : ℕ} {lc : ℤ} {L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc (d - 1) L hL N P c X f₀) :
    ∀ i, ∀ k, k < N (i + 1) → P i k ⊆ Finset.range (N i) := by
  intro i k hk
  by_cases hi : i ≤ d - 1
  · exact h.Psub i hi k hk
  · have hz : N (i + 1) = 0 := h.Ntop (i + 1) (by omega)
    omega

lemma levDInv_ne {d : ℕ} {lc : ℤ} {L : ℕ} {hL : 1 ≤ L} {N : ℕ → ℕ} {P : ℕ → ℕ → Finset ℕ}
    {c : ℕ → ℕ → ℕ} {X : HistData d L} {f₀ : Fin L → Bool}
    (h : LevDInv d lc (d - 1) L hL N P c X f₀) :
    ∀ i, ∀ k, k < N (i + 1) → (P i k).Nonempty := by
  intro i k hk
  by_cases hi : i ≤ d - 1
  · exact h.Pne i hi k hk
  · have hz : N (i + 1) = 0 := h.Ntop (i + 1) (by omega)
    omega

lemma lvlSet_card_le {d L : ℕ} {N : ℕ → ℕ} {c : ℕ → ℕ → ℕ} {j : ℕ} (hL : 1 ≤ L) :
    (lvlSet N c L j hL).card ≤ N j := by
  rw [lvlSet]
  calc (((Finset.range (N j)).attach).image (fun s => ptFin c L j s.1 hL)).card
      ≤ ((Finset.range (N j)).attach).card := Finset.card_image_le
    _ = N j := by simp

/-- `IdxDatum.dir` only depends on the parameters at the levels `1,…,j`. -/
lemma IdxDatum.dir_congr (D : IdxDatum) (l : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (w : D.I j) (a b : (i : ℕ) → D.S i → ℤ),
      (∀ i, 1 ≤ i → i ≤ j → ∀ s, a i s = b i s) → D.dir l c j w a = D.dir l c j w b := by
  intro j
  induction j with
  | zero => intro w a b _; simp only [IdxDatum.dir]
  | succ j ih =>
    intro w a b h
    rw [IdxDatum.dir_succ, IdxDatum.dir_succ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih (D.par j s) a b (fun i hi1 hij => h i hi1 (by omega)),
      h (j + 1) (by omega) (by omega) s]
end

end Work.Peluse.UControl

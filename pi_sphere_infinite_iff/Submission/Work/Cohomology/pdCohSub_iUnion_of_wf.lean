import Mathlib
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.subsingleton_pdCohSub_iUnion_of_isLimitClosed

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# The transfinite union step for relative cohomology, from its limit-continuous case

`Work.Cohomology.subsingleton_pdCohSub_iUnion_of_isLimitClosed` proves the transfinite union step
for an increasing family of open sets that is *continuous at its limit indices*.  An arbitrary
increasing well-ordered family `W : Γ → Set X` is reduced to that case by replacing it with its
"regularisation"

  `B γ := ⋃ δ < γ, W δ`,

which is increasing, open, limit-continuous *by construction*, and has the same total union.  The
family `B` is analysed by well-founded recursion on `γ`:

* if `γ` has no predecessor, `B γ = ∅`;
* if `γ` has a maximal predecessor `δ`, then `B γ = W δ` and the hypothesis gives `H^j(B γ) = 0`
  directly;
* if `γ` has predecessors but no maximal predecessor, `B γ = ⋃ δ < γ, B δ` and the limit-continuous
  case applies to the family `(B δ)_{δ < γ}` (whose members satisfy the induction hypothesis).

This yields the transfinite union step in the form used by the Thom vanishing argument,
`H^j(⋃ γ, W γ, ·) = 0` for `j ≤ d` from `H^j(W γ, W γ ∩ A) = 0`.
-/

namespace Work.Cohomology

noncomputable section

/-- **The transfinite union step**: for an increasing well-ordered family `W : Γ → Set X` of open
sets, vanishing of `H^j(W γ, W γ ∩ A)` for all `γ` and all `j ≤ d` implies vanishing of
`H^j(⋃ γ, W γ, ⋃ γ, W γ ∩ A)` for all `j ≤ d`. -/
theorem subsingleton_pdCohSub_iUnion_of_wf {X : Type} [TopologicalSpace X] (A : Set X)
    {Γ : Type} [LinearOrder Γ] [WellFoundedLT Γ] (W : Γ → Set X)
    (hopen : ∀ i, IsOpen (W i)) (hmono : Monotone W) (d : ℕ)
    (h : ∀ i j, j ≤ d → Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (W i) j)) :
    ∀ j, j ≤ d → Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (⋃ i, W i) j) := by
  classical
  -- the regularisation `B γ = ⋃ δ < γ, W δ`
  let B : Γ → Set X := fun γ => ⋃ δ < γ, W δ
  have hBopen : ∀ γ, IsOpen (B γ) := by
    intro γ
    exact isOpen_iUnion fun δ => isOpen_iUnion fun _ : δ < γ => hopen δ
  have hBmono : Monotone B := by
    intro γ γ' hγγ' x hx
    simp only [B, Set.mem_iUnion] at hx ⊢
    obtain ⟨δ, hδ, hx⟩ := hx
    exact ⟨δ, lt_of_lt_of_le hδ hγγ', hx⟩
  -- `B` is limit-continuous
  have hBcont : ∀ γ, (∃ δ, δ < γ) → (∀ δ, δ < γ → ∃ ε, δ < ε ∧ ε < γ) →
      B γ = ⋃ δ < γ, B δ := by
    intro γ _ hlim
    ext x
    simp only [B, Set.mem_iUnion]
    constructor
    · rintro ⟨δ, hδ, hx⟩
      obtain ⟨ε, hδε, hεγ⟩ := hlim δ hδ
      exact ⟨ε, hεγ, δ, hδε, hx⟩
    · rintro ⟨δ, hδ, ε, hεδ, hx⟩
      exact ⟨ε, lt_trans hεδ hδ, hx⟩
  -- every regularised piece is acyclic in degrees `≤ d`
  have hPB : ∀ γ, ∀ j ≤ d, Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (B γ) j) := by
    intro γ
    refine WellFoundedLT.induction (motive := fun γ : Γ => ∀ j ≤ d,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (B γ) j)) γ ?_
    intro γ ih j hj
    by_cases hsucc : ∃ δ, δ < γ ∧ ∀ ε, ε < γ → ε ≤ δ
    · -- a maximal predecessor `δ`: `B γ = W δ`
      obtain ⟨δ, hδγ, hmax⟩ := hsucc
      have hBW : B γ = W δ := by
        ext x
        simp only [B, Set.mem_iUnion]
        constructor
        · rintro ⟨δ', hδ'γ, hx⟩
          exact hmono (hmax δ' hδ'γ) hx
        · rintro hx
          exact ⟨δ, hδγ, hx⟩
      rw [hBW]
      exact h δ j hj
    · -- no maximal predecessor
      have hlim : ∀ δ, δ < γ → ∃ ε, δ < ε ∧ ε < γ := by
        intro δ hδ
        by_contra hcon
        have hcon' : ∀ ε, ε < γ → ε ≤ δ := by
          intro ε hε
          by_contra hle
          exact hcon ⟨ε, lt_of_not_ge hle, hε⟩
        exact hsucc ⟨δ, hδ, hcon'⟩
      by_cases hpred : ∃ δ : Γ, δ < γ
      · -- a limit index
        have hBγ : B γ = ⋃ δ < γ, B δ := hBcont γ hpred hlim
        have hcont_sub : ∀ γ' : ↥(Set.Iio γ), (∃ δ' : ↥(Set.Iio γ), δ' < γ') →
            (∀ δ' : ↥(Set.Iio γ), δ' < γ' → ∃ ε' : ↥(Set.Iio γ), δ' < ε' ∧ ε' < γ') →
            B γ'.1 = ⋃ δ' < γ', B δ'.1 := by
          intro γ' hγ'pred hγ'lim
          have hγ'pred' : ∃ δ : Γ, δ < γ'.1 := by
            obtain ⟨δ', hδ'⟩ := hγ'pred
            exact ⟨δ'.1, hδ'⟩
          have hγ'lim' : ∀ δ, δ < γ'.1 → ∃ ε, δ < ε ∧ ε < γ'.1 := by
            intro δ hδ
            obtain ⟨ε', hε'⟩ := hγ'lim ⟨δ, lt_trans hδ γ'.2⟩ hδ
            exact ⟨ε'.1, hε'.1, hε'.2⟩
          rw [hBcont γ'.1 hγ'pred' hγ'lim']
          ext x
          constructor
          · intro hx
            obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hδγ, hx'⟩ := Set.mem_iUnion.mp hδ
            exact Set.mem_iUnion.mpr
              ⟨⟨δ, lt_trans hδγ γ'.2⟩, Set.mem_iUnion.mpr ⟨hδγ, hx'⟩⟩
          · intro hx
            obtain ⟨δ', hδ'⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hδ'γ, hx'⟩ := Set.mem_iUnion.mp hδ'
            exact Set.mem_iUnion.mpr ⟨δ'.1, Set.mem_iUnion.mpr ⟨hδ'γ, hx'⟩⟩
        have hun : (⋃ δ : ↥(Set.Iio γ), B δ.1) = B γ := by
          rw [hBγ]
          ext x
          constructor
          · intro hx
            obtain ⟨δ, hx'⟩ := Set.mem_iUnion.mp hx
            exact Set.mem_iUnion.mpr ⟨δ.1, Set.mem_iUnion.mpr ⟨δ.2, hx'⟩⟩
          · intro hx
            obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hδγ, hx'⟩ := Set.mem_iUnion.mp hδ
            exact Set.mem_iUnion.mpr ⟨⟨δ, hδγ⟩, hx'⟩
        have hL := subsingleton_pdCohSub_iUnion_of_isLimitClosed A
          (fun δ : ↥(Set.Iio γ) => B δ.1) (fun δ => hBopen δ.1)
          (fun a b hab => hBmono hab) hcont_sub d (fun δ j hj => ih δ.1 δ.2 j hj)
        rw [← hun]
        exact hL j hj
      · -- no predecessor: `B γ = ∅`
        have hBemp : B γ = ∅ := by
          ext x
          constructor
          · intro hx
            obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hδγ, -⟩ := Set.mem_iUnion.mp hδ
            exact absurd ⟨δ, hδγ⟩ hpred
          · intro hx
            exact (Set.mem_empty_iff_false x).mp hx |>.elim
        have hcont_sub : ∀ γ' : ↥(Set.Iio γ), (∃ δ' : ↥(Set.Iio γ), δ' < γ') →
            (∀ δ' : ↥(Set.Iio γ), δ' < γ' → ∃ ε' : ↥(Set.Iio γ), δ' < ε' ∧ ε' < γ') →
            B γ'.1 = ⋃ δ' < γ', B δ'.1 := by
          intro γ' hγ'pred _
          obtain ⟨δ', hδ'⟩ := hγ'pred
          exact absurd (show ∃ δ : Γ, δ < γ from ⟨δ'.1, lt_trans hδ' γ'.2⟩) hpred
        have hun : (⋃ δ : ↥(Set.Iio γ), B δ.1) = B γ := by
          rw [hBemp]
          ext x
          constructor
          · intro hx
            obtain ⟨δ, -⟩ := Set.mem_iUnion.mp hx
            exact absurd ⟨δ.1, δ.2⟩ hpred
          · intro hx
            exact (Set.mem_empty_iff_false x).mp hx |>.elim
        have hL := subsingleton_pdCohSub_iUnion_of_isLimitClosed A
          (fun δ : ↥(Set.Iio γ) => B δ.1) (fun δ => hBopen δ.1)
          (fun a b hab => hBmono hab) hcont_sub d (fun δ j hj => ih δ.1 δ.2 j hj)
        rw [← hun]
        exact hL j hj
  -- final: the union over all of `Γ`
  intro j hj
  by_cases htop : ∃ t : Γ, ∀ γ, γ ≤ t
  · -- a maximum `t`: the union is `W t`
    obtain ⟨t, ht⟩ := htop
    have hun : (⋃ i, W i) = W t := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact hmono (ht i) hxi
      · intro hx
        exact Set.mem_iUnion.mpr ⟨t, hx⟩
    rw [hun]
    exact h t j hj
  · -- no maximum: the regularisation has the same union
    have hunWB : (⋃ γ, B γ) = ⋃ γ, W γ := by
      ext x
      constructor
      · intro hx
        obtain ⟨γ, hxγ⟩ := Set.mem_iUnion.mp hx
        obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hxγ
        obtain ⟨-, hxδ⟩ := Set.mem_iUnion.mp hδ
        exact Set.mem_iUnion.mpr ⟨δ, hxδ⟩
      · intro hx
        obtain ⟨γ, hxγ⟩ := Set.mem_iUnion.mp hx
        have hex : ∃ γ' : Γ, γ < γ' := by
          by_contra hcon
          exact htop ⟨γ, fun γ' => le_of_not_gt (fun h => hcon ⟨γ', h⟩)⟩
        obtain ⟨γ', hγ'⟩ := hex
        refine Set.mem_iUnion.mpr ⟨γ', ?_⟩
        exact Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion.mpr ⟨hγ', hxγ⟩⟩
    have hL := subsingleton_pdCohSub_iUnion_of_isLimitClosed A B hBopen hBmono hBcont d hPB
    rw [hunWB] at hL
    exact hL j hj

end

end Work.Cohomology

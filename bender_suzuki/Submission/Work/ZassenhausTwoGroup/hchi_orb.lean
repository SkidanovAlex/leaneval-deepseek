import Mathlib
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.Clifford.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.hchi_orb`

Feit's exceptional characters of Theorem 2 (see `FeitThm2.lean`) are attached to the elements
`ζ ∈ Irr Q`, `ζ ≠ 1`, but they are *shadows of the induction*: two non-trivial irreducible
characters of `Q` that induce the same character of `G` (i.e. that lie in the same `D`-orbit,
`D = twoPoint H t`) receive the same exceptional character, and characters inducing *different*
characters of `G` receive different exceptional characters.  In other words the map
`ζ ↦ Ind_Q^G ζ` can be used to *index* the exceptional characters:

> there is `χ : (↥Q → ℂ) → G → ℂ` such that, on the non-trivial irreducible characters of `Q`,
> `χ` is irreducible, injective across the fibres of `Ind_Q^G`, and constant on each fibre.

This is the statement the count of Feit's §3 needs (it lets one talk about "the exceptional
character of an orbit" and count exceptional characters by counting orbits).

## Proof

`FeitThm2Prop` supplies a family `χ₀` of exceptional characters together with the value relation
of Theorem 2,

`z_{ζ'} · Ind_Q^G ζ - z_ζ · Ind_Q^G ζ' = ε (z_{ζ'} · χ₀ ζ - z_ζ · χ₀ ζ')`  whenever
`Ind_Q^G ζ ≠ Ind_Q^G ζ'` (`z_ζ = ζ(1)`).

* **Injectivity.**  Evaluating at `g = 1` and using `Ind_Q^G ζ 1 = [G : Q] · ζ(1)`
  (`Work.Induction.indFun_apply_one`) kills the left-hand side; since `ε = ±1 ≠ 0` and
  `χ₀ ζ 1 = irrDeg (χ₀ ζ) ≠ 0`, one gets `ζ(1) = ζ'(1)`, and then the value relation itself gives
  `Ind_Q^G ζ = Ind_Q^G ζ'` — a contradiction.  This is `inj_aux` below.
* **Constancy.**  Rather than prove that `χ₀` is already constant on the fibres of `Ind_Q^G`, we
  replace `χ₀` by its "pull-back along `Ind_Q^G`": choose one representative of each value of
  `Ind_Q^G` on `{ζ ∈ Irr Q | ζ ≠ 1}` and set `χ ζ := χ₀` of the representative of `Ind_Q^G ζ`.
  Then `χ` is constant on the fibres by construction and injective across them because of the
  injectivity of `χ₀` just established.  (`Classical.choose` on the *value* of `Ind_Q^G`, not on
  `ζ`, is what makes the construction canonical in `Ind_Q^G ζ`.)
-/

namespace Work.ZassenhausTwoGroup

/-- **Injectivity of Feit's exceptional characters across distinct induced characters.**

`χ₀` is Feit's family of exceptional characters, satisfying the value relation (1) of Theorem 2
and taking non-trivial irreducible characters of `Q` to irreducible characters of `G`.  Then
`χ₀` separates the fibres of `ζ ↦ Ind_Q^G ζ` on the non-trivial irreducible characters of `Q`.

The proof evaluates the value relation at `1`, where the left-hand side
`z_{ζ'} · [G:Q] · z_ζ - z_ζ · [G:Q] · z_{ζ'}` vanishes: `(z_{ζ'} - z_ζ) · χ₀ ζ 1 = 0` forces
`z_ζ = z_{ζ'}` (as `χ₀ ζ 1 = irrDeg (χ₀ ζ) ≠ 0`), and then the value relation at an arbitrary
`g`, read with `χ₀ ζ = χ₀ ζ'`, gives `Ind_Q^G ζ = Ind_Q^G ζ'`. -/
private lemma inj_aux {G : Type} [Group G] [Fintype G] (Q : Subgroup G) [Fintype ↥Q]
    {ε : ℤ} {χ₀ : (↥Q → ℂ) → G → ℂ}
    (hdiff : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' →
      ∀ g : G, (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g
        = (ε : ℂ) * ((ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g))
    (hIrr : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ₀ ζ ∈ Work.CharCore.Irr G)
    (hε : ε = 1 ∨ ε = -1)
    {ζ ζ' : ↥Q → ℂ} (hζ : ζ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ ≠ 1)
    (hζ' : ζ' ∈ Work.CharCore.Irr ↥Q) (hζ'1 : ζ' ≠ 1)
    (hNI : Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ') : χ₀ ζ ≠ χ₀ ζ' := by
  intro hχeq
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hz1 : ζ 1 ≠ 0 := by
    have h := Work.CharCore.irrDeg_ne_zero hζ
    rwa [← Work.CharCore.irrDeg_spec hζ] at h
  have hφ0 : χ₀ ζ 1 ≠ 0 := by
    have h := Work.CharCore.irrDeg_ne_zero (hIrr ζ hζ hζ1)
    rwa [← Work.CharCore.irrDeg_spec (hIrr ζ hζ hζ1)] at h
  -- the value relation at the identity: the left hand side is `z_{ζ'} [G:Q] z_ζ - z_ζ [G:Q] z_{ζ'} = 0`
  have hg1 := hdiff ζ hζ hζ1 ζ' hζ' hζ'1 hNI 1
  rw [Work.Induction.indFun_apply_one Q ζ, Work.Induction.indFun_apply_one Q ζ'] at hg1
  have hz0 : (ζ' 1 - ζ 1) * χ₀ ζ 1 = 0 := by
    have h0 : (ζ' 1) * ((Q.index : ℂ) * ζ 1) - (ζ 1) * ((Q.index : ℂ) * ζ' 1) = 0 := by ring
    rw [h0] at hg1
    have hX : (ζ' 1) * χ₀ ζ 1 - (ζ 1) * χ₀ ζ' 1 = 0 := by
      rcases mul_eq_zero.mp hg1.symm with h | h
      · exact absurd h hε0
      · exact h
    rw [← hχeq] at hX
    linear_combination hX
  have hz : ζ' 1 = ζ 1 := sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_right hφ0)
  -- with `z_ζ = z_{ζ'}` the value relation at an arbitrary `g` collapses to `z_ζ (Ind ζ - Ind ζ') = 0`
  refine hNI (funext fun g => ?_)
  have hgg := hdiff ζ hζ hζ1 ζ' hζ' hζ'1 hNI g
  have hL : (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g = 0 := by
    rw [hgg, hχeq, hz]; ring
  have hL' : ζ 1 * Work.Induction.indFun Q ζ g - ζ 1 * Work.Induction.indFun Q ζ' g = 0 := by
    rw [hz] at hL; exact hL
  have hfac : ζ 1 * (Work.Induction.indFun Q ζ g - Work.Induction.indFun Q ζ' g) = 0 := by
    rw [mul_sub]; exact hL'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hz1)

theorem hchi_orb {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card Q - 1)
    (h2 : FeitThm2Prop) :
    ∃ χ : (↥Q → ℂ) → G → ℂ,
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ ζ ∈ Work.CharCore.Irr G) ∧
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
        Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → χ ζ ≠ χ ζ') ∧
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
        Work.Induction.indFun Q ζ = Work.Induction.indFun Q ζ' → χ ζ = χ ζ') := by
  obtain ⟨ε, hε, c, χ₀, hIrr, hdiff, hvan, hval, hconst⟩ := h2 G H Q t h hZ hQ2 hne
  classical
  -- `FeitThm2Prop` mentions `Irr ↥Q` with the `Fintype` instance synthesised from `[Fintype G]`,
  -- while the statement of this theorem uses the explicit `[Fintype ↥Q]`; `Fintype` is a
  -- subsingleton, so the two `Irr ↥Q` agree and memberships transport.
  have transferIrr : ∀ {i₁ i₂ : Fintype ↥Q} {ζ : ↥Q → ℂ},
      (ζ ∈ @Work.CharCore.Irr ↥Q _ i₁) → (ζ ∈ @Work.CharCore.Irr ↥Q _ i₂) := by
    intro i₁ i₂ ζ hζ
    rw [@Subsingleton.elim (Fintype ↥Q) (Fintype.subsingleton ↥Q) i₁ i₂] at hζ
    exact hζ
  have hIrr' : ∀ ζ ∈ (Work.CharCore.Irr ↥Q : Finset (↥Q → ℂ)), ζ ≠ 1 →
      χ₀ ζ ∈ Work.CharCore.Irr G := by
    intro ζ hζ hζ1
    exact hIrr ζ (transferIrr hζ) hζ1
  have hdiff' : ∀ ζ ∈ (Work.CharCore.Irr ↥Q : Finset (↥Q → ℂ)), ζ ≠ 1 →
      ∀ ζ' ∈ (Work.CharCore.Irr ↥Q : Finset (↥Q → ℂ)), ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' →
      ∀ g : G, (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g
        = (ε : ℂ) * ((ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g) := by
    intro ζ hζ hζ1 ζ' hζ' hζ'1 hNI g
    exact hdiff ζ (transferIrr hζ) hζ1 ζ' (transferIrr hζ') hζ'1 hNI g
  -- the non-trivial irreducible characters of `Q`, as a finset
  let S : Finset (↥Q → ℂ) := (Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)
  -- a chosen representative of each value taken by `ζ ↦ Ind_Q^G ζ` on `S`
  let rep : (G → ℂ) → (↥Q → ℂ) := fun Ξ =>
    if h : ∃ ζ ∈ S, Work.Induction.indFun Q ζ = Ξ then Classical.choose h else 0
  have rep_spec : ∀ Ξ : G → ℂ, (∃ ζ ∈ S, Work.Induction.indFun Q ζ = Ξ) →
      rep Ξ ∈ S ∧ Work.Induction.indFun Q (rep Ξ) = Ξ := by
    intro Ξ hΞ
    simp only [rep, dite_eq_left hΞ]
    exact Classical.choose_spec hΞ
  have key : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 →
      rep (Work.Induction.indFun Q ζ) ∈ Work.CharCore.Irr ↥Q ∧
      rep (Work.Induction.indFun Q ζ) ≠ 1 ∧
      Work.Induction.indFun Q (rep (Work.Induction.indFun Q ζ)) = Work.Induction.indFun Q ζ := by
    intro ζ hζ hζ1
    have hζS : ζ ∈ S := by simp only [S, Finset.mem_filter]; exact ⟨hζ, hζ1⟩
    have h := rep_spec (Work.Induction.indFun Q ζ) ⟨ζ, hζS, rfl⟩
    exact ⟨(Finset.mem_filter.mp h.1).1, (Finset.mem_filter.mp h.1).2, h.2⟩
  refine ⟨fun ζ => χ₀ (rep (Work.Induction.indFun Q ζ)), ?_, ?_, ?_⟩
  · intro ζ hζ hζ1
    exact hIrr' _ (key ζ hζ hζ1).1 (key ζ hζ hζ1).2.1
  · intro ζ hζ hζ1 ζ' hζ' hζ'1 hInd
    exact inj_aux Q hdiff' hIrr' hε (key ζ hζ hζ1).1 (key ζ hζ hζ1).2.1
      (key ζ' hζ' hζ'1).1 (key ζ' hζ' hζ'1).2.1 (by
        rw [(key ζ hζ hζ1).2.2, (key ζ' hζ' hζ'1).2.2]
        exact hInd)
  · intro ζ hζ hζ1 ζ' hζ' hζ'1 hInd
    simp only [hInd]

end Work.ZassenhausTwoGroup

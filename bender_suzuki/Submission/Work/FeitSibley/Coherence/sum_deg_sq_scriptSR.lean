import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The sum of squared degrees over `𝒮(R)` (Peterfalvi II, Appendice XII)

For the Feit–Sibley data `h : FSData G` and a subgroup `R ≤ Q` normalised by `H`
(so that `R ⊴ H`), the set

`𝒮(R) = scriptSR h.H h.Q1 R = {χ ∈ Irr H | Q₁ ⊄ ker χ,  R ≤ ker χ}`

of irreducible characters of `H` satisfies

`∑_{χ ∈ 𝒮(R)} χ(1)² = [H : R] - [H : R·Q₁]`.

The mechanism is the standard "kernel counting".  The characters of a finite group trivial on
a *normal* subgroup `N` are exactly the inflations of the irreducibles of the quotient, so their
degree squares sum to `[G : N]` (`Work.CohApps.sum_irr_deg_sq_le_ker`).  Since `Q₁ ⊴ H` as well
(`Work.FeitSibley.FSData.Q1_normal_in_H`), for a character trivial on `R` the conditions
"`R ≤ ker χ`" and "`Q₁ ⊄ ker χ`" unfold into "trivial on `R`" and "not trivial on `R ⊔ Q₁`",
giving the difference of the two indices.

## Contents

* `sum_irr_deg_sq_kernel_diff`: the abstract counting lemma — for normal `A ≤ B` in a finite
  group `G`,
  `∑_{χ ∈ Irr G, A ≤ ker χ, ¬ B ≤ ker χ} χ(1)² = [G : A] - [G : B]`;
* `scriptSR_eq_filter`: rewrites `scriptSR h.H h.Q1 R` as the corresponding filter of
  `Irr ↥h.H`;
* `sum_deg_sq_scriptSR`: the requested statement.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

/-- **Kernel counting.**  For normal subgroups `A ≤ B` of a finite group `G`, the sum of the
squares of the degrees of the irreducible characters of `G` that are trivial on `A` but not on
`B` is `[G : A] - [G : B]`.

Indeed the characters trivial on `N` contribute `[G : N]` (`sum_irr_deg_sq_le_ker`), and
`A ≤ B` makes the set of characters trivial on `B` a subset of the set of those trivial on `A`,
so the required sum is the difference. -/
theorem sum_irr_deg_sq_kernel_diff {G : Type} [Group G] [Fintype G]
    (A B : Subgroup G) [A.Normal] [B.Normal] (hAB : A ≤ B) :
    ∑ χ ∈ (Work.CharCore.Irr G).filter
        (fun χ => (A : Set G) ⊆ Work.CharCore.charKernel χ ∧
          ¬ (B : Set G) ⊆ Work.CharCore.charKernel χ),
      (Work.CharCore.irrDeg χ : ℝ) ^ 2 = (A.index : ℝ) - (B.index : ℝ) := by
  classical
  have hBA : (Work.CharCore.Irr G).filter (fun χ => (B : Set G) ⊆ Work.CharCore.charKernel χ)
      ⊆ (Work.CharCore.Irr G).filter (fun χ => (A : Set G) ⊆ Work.CharCore.charKernel χ) := by
    intro χ hχ
    simp only [Finset.mem_filter] at hχ ⊢
    exact ⟨hχ.1, fun x hx => hχ.2 (hAB hx)⟩
  have heq : (Work.CharCore.Irr G).filter
        (fun χ => (A : Set G) ⊆ Work.CharCore.charKernel χ ∧
          ¬ (B : Set G) ⊆ Work.CharCore.charKernel χ)
      = (Work.CharCore.Irr G).filter (fun χ => (A : Set G) ⊆ Work.CharCore.charKernel χ)
        \ (Work.CharCore.Irr G).filter (fun χ => (B : Set G) ⊆ Work.CharCore.charKernel χ) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hsd := Finset.sum_sdiff (f := fun χ => (Work.CharCore.irrDeg χ : ℝ) ^ 2) hBA
  rw [heq]
  have h1 := Work.CohApps.sum_irr_deg_sq_le_ker (G := G) A
  have h2 := Work.CohApps.sum_irr_deg_sq_le_ker (G := G) B
  linarith [hsd, h1, h2]

/-- **`𝒮(R)` as a filter of `Irr H`.**  For the Feit–Sibley data `h` and `R ≤ Q`
(so that `R ≤ H` and `Q₁ ≤ H`), the set `𝒮(R)` of irreducible characters of `H` which are
non-trivial on `Q₁` and trivial on `R` is also described by the two conditions
"trivial on `R`" and "not trivial on `R ⊔ Q₁`". -/
theorem scriptSR_eq_filter {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R : Subgroup G) (hR : R ≤ h.Q) :
    Work.FeitSibley.scriptSR h.H h.Q1 R =
      (Work.CharCore.Irr ↥h.H).filter
        (fun χ => (R.subgroupOf h.H : Set ↥h.H) ⊆ Work.CharCore.charKernel χ ∧
          ¬ ((R ⊔ h.Q1).subgroupOf h.H : Set ↥h.H) ⊆ Work.CharCore.charKernel χ) := by
  classical
  have hRH : R ≤ h.H := le_trans hR h.Q_le_H
  have hQ1H : h.Q1 ≤ h.H := le_trans h.Q1_le_Q h.Q_le_H
  -- `R ⊔ Q₁` sits inside `H`, so inside `H` it is the join of the two pieces
  have hN2eq : (R ⊔ h.Q1).subgroupOf h.H
      = R.subgroupOf h.H ⊔ h.Q1.subgroupOf h.H :=
    Subgroup.subgroupOf_sup hRH hQ1H
  -- the pointwise key: given `χ ∈ Irr H` trivial on `R`,
  -- "non-trivial on `Q₁`" is "not trivial on `R ⊔ Q₁`"
  have key : ∀ χ : ↥h.H → ℂ, χ ∈ Work.CharCore.Irr ↥h.H →
      (∀ x : ↥h.H, x ∈ R.subgroupOf h.H → χ x = χ 1) →
      ((∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ χ x ≠ χ 1) ↔
        ¬ ((R ⊔ h.Q1).subgroupOf h.H : Set ↥h.H) ⊆ Work.CharCore.charKernel χ) := by
    intro χ hirr hRtriv
    constructor
    · rintro ⟨x, hxQ1, hxne⟩ hsub
      exact hxne (hsub (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hxQ1)))
    · intro hnot
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      -- `charKernel χ` is the underlying set of a subgroup `K0` of `H`
      obtain ⟨K0, _hK0norm, hK0eq⟩ := Work.CharCore.charKernel_subgroup hirr
      have hRle : R.subgroupOf h.H ≤ K0 := by
        intro x hx
        show x ∈ (K0 : Set ↥h.H)
        rw [hK0eq]
        exact hRtriv x hx
      have hQ1le : h.Q1.subgroupOf h.H ≤ K0 := by
        intro x hx
        show x ∈ (K0 : Set ↥h.H)
        rw [hK0eq]
        exact hcon x (Subgroup.mem_subgroupOf.mp hx)
      have hsup : R.subgroupOf h.H ⊔ h.Q1.subgroupOf h.H ≤ K0 := sup_le hRle hQ1le
      apply hnot
      intro x hx
      rw [hN2eq] at hx
      have hx' : x ∈ (K0 : Set ↥h.H) := hsup hx
      rwa [hK0eq] at hx'
  ext χ
  rw [Work.FeitSibley.scriptSR, Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hirr, hex⟩, hRtriv⟩
    refine ⟨hirr, ?_, ?_⟩
    · intro x hx
      exact hRtriv x (Subgroup.mem_subgroupOf.mp hx)
    · exact (key χ hirr (fun x hx => hRtriv x (Subgroup.mem_subgroupOf.mp hx))).mp hex
  · rintro ⟨hirr, hRsub, hNsub⟩
    refine ⟨⟨hirr, ?_⟩, ?_⟩
    · exact (key χ hirr (fun x hx => hRsub (Subgroup.mem_subgroupOf.mpr hx))).mpr hNsub
    · intro x hx
      exact hRsub (Subgroup.mem_subgroupOf.mpr hx)

/-- **The sum of squared degrees over `𝒮(R)`.**  For the Feit–Sibley data `h` and a subgroup
`R ≤ Q` normalised by `H` (hence normal in `H`),

`∑_{χ ∈ 𝒮(R)} χ(1)² = [H : R] - [H : R·Q₁]`.

The characters in `𝒮(R)` are exactly the irreducibles of `H` trivial on the normal subgroup `R`
but not on the normal subgroup `R ⊔ Q₁` (`scriptSR_eq_filter`); both `R` and `Q₁` are normal in
`H` (`h.Q1_normal_in_H`), so the abstract kernel-counting lemma
`sum_irr_deg_sq_kernel_diff` applies. -/
theorem sum_deg_sq_scriptSR {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R : Subgroup G) (hR : R ≤ h.Q) (hRn : h.H ≤ Subgroup.normalizer (R : Set G)) :
    ∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R, ((Work.CharCore.irrDeg χ : ℝ)) ^ 2
      = ((R.subgroupOf h.H).index : ℝ) - (((R ⊔ h.Q1).subgroupOf h.H).index : ℝ) := by
  classical
  have hRH : R ≤ h.H := le_trans hR h.Q_le_H
  have hQ1H : h.Q1 ≤ h.H := le_trans h.Q1_le_Q h.Q_le_H
  -- normality of the three subgroups of `H` entering the counting lemma
  haveI hR'norm : (R.subgroupOf h.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRn
  haveI hQ1'norm : (h.Q1.subgroupOf h.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.Q1_normal_in_H
  haveI hN2norm : ((R ⊔ h.Q1).subgroupOf h.H).Normal := by
    rw [Subgroup.subgroupOf_sup hRH hQ1H]
    exact Subgroup.sup_normal _ _
  rw [scriptSR_eq_filter h R hR]
  exact sum_irr_deg_sq_kernel_diff (R.subgroupOf h.H) ((R ⊔ h.Q1).subgroupOf h.H)
    (Subgroup.subgroupOf_mono h.H le_sup_left)

end Work.FeitSibley.Coherence

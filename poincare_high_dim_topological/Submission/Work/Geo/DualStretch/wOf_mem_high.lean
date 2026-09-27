/-
A6 `Geo/DualStretch` — `wOf_mem_high`.

For a finite geometric simplicial complex `P` in `E n = ℝⁿ` and a point `x ∈ P.space`, consider the
barycentric-subdivision data of `Defs.lean`: the mass `massG P hP x τ` carried by the subdivision
simplex indexed by the level set `τ`, its splitting into a *low* part (`LowFace β p τ`, i.e.
`τ.card ≤ p + 1`) and a *high* part, and the two endpoints

  `uOf β p P hP x = (1 - S)⁻¹ • A(x)`,   `wOf β p P hP x = S⁻¹ • B(x)`

of the join segment through `x`.  Here `S = SOf β p P hP x` is the total high mass and `A`, `B` are
the low and high parts of `x`.  The point of this file is

  `wOf β p P hP x ∈ High P p`   whenever `0 < S`,

i.e. the high endpoint of the join segment lies in the *dual* `(n-p-1)`-skeleton of `P` (`High P p`
is the union, over chains `T` of faces of `P` with at least `p+2` vertices, of the simplices spanned
by the barycentres of the members of `T`).

The mathematics is one sentence.  `S > 0` forces some non-low level set `τ` to carry positive mass,
and then `wOf x` is the convex combination

  `wOf x = ∑_{τ ∈ supp} (massG τ / S) • bary τ`

over the *support* `supp = {τ ∈ cands | ¬ LowFace β p τ ∧ 0 < massG τ}` of `massG`.  The support is
a chain of faces of `P` (`massG_api`), every member has `p + 2 ≤ τ.card` by construction, and the
coefficients are non-negative and sum to `1`; hence `wOf x` lies in the simplex spanned by the
barycentres of `supp`, which is one of the simplices defining `High P p`.

The only imported API used in the end is the bundle `massG_api`, supplying the chain property of the
support and the fact that positive mass forces the level set to be a face of `P`.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.massG_api

open Set Metric
open scoped Classical

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.Geo.DualStretch

variable {n : ℕ}

/-- **The support of `massG` at `x`.**  The level sets `τ` of the barycentric subdivision of `x`
which are not low (`¬ LowFace β p τ`, i.e. `p + 2 ≤ τ.card`) and carry positive mass.  These index
exactly the barycentric-subdivision simplices of `x` whose barycentre is a vertex of `High P p`. -/
noncomputable def massSupp (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n) :
    Finset (Finset (PL.E n)) :=
  (cands P hP).filter (fun τ => ¬ LowFace β p τ ∧ 0 < massG P hP x τ)

lemma mem_massSupp (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n)
    (τ : Finset (PL.E n)) :
    τ ∈ massSupp P hP β p x ↔ τ ∈ cands P hP ∧ ¬ LowFace β p τ ∧ 0 < massG P hP x τ := by
  rw [massSupp, Finset.mem_filter]

/-- `massG` is non-negative (it is a clamped quantity). -/
lemma massG_nonneg (P : PL.Cx n) (hP : P.faces.Finite) (x : PL.E n) (τ : Finset (PL.E n)) :
    0 ≤ massG P hP x τ := by
  rw [massG]
  exact le_max_left _ _

/-- **`SOf` as the total mass of the support.**  Level sets which are low, or which carry no mass,
contribute nothing to the total high mass. -/
theorem SOf_eq_sum_massSupp (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n) :
    SOf β p P hP x = ∑ τ ∈ massSupp P hP β p x, massG P hP x τ := by
  classical
  have h1 : (∑ τ ∈ massSupp P hP β p x, massG P hP x τ)
      = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ := by
    refine Finset.sum_subset ?_ ?_
    · intro τ hτ
      exact Finset.mem_filter.mpr ⟨((mem_massSupp P hP β p x τ).mp hτ).1,
        ((mem_massSupp P hP β p x τ).mp hτ).2.1⟩
    · intro τ hτF hτnotT
      have hτC : τ ∈ cands P hP := (Finset.mem_filter.mp hτF).1
      have hL : ¬ LowFace β p τ := (Finset.mem_filter.mp hτF).2
      have hnp : ¬ 0 < massG P hP x τ := fun hpos =>
        hτnotT (Finset.mem_filter.mpr ⟨hτC, hL, hpos⟩)
      exact le_antisymm (not_lt.mp hnp) (massG_nonneg P hP x τ)
  have h2 : (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ)
      = SOf β p P hP x := by
    have h3 : (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ)
        = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ),
          (if LowFace β p τ then 0 else massG P hP x τ) :=
      Finset.sum_congr rfl (fun τ hτ => by rw [if_neg (Finset.mem_filter.mp hτ).2])
    rw [h3, SOf]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro τ hτC hτnotF
    rw [if_pos ?_]
    by_contra hL
    exact hτnotF (Finset.mem_filter.mpr ⟨hτC, hL⟩)
  exact (h1.trans h2).symm

/-- **`BOf` as the barycentric combination over the support.**  The high part of `x` is
`∑_{τ ∈ supp} massG τ • bary τ`. -/
theorem BOf_eq_sum_massSupp (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n) :
    BOf β p P hP x = ∑ τ ∈ massSupp P hP β p x, massG P hP x τ • bary τ := by
  classical
  have h1 : (∑ τ ∈ massSupp P hP β p x, massG P hP x τ • bary τ)
      = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ),
          massG P hP x τ • bary τ := by
    refine Finset.sum_subset ?_ ?_
    · intro τ hτ
      exact Finset.mem_filter.mpr ⟨((mem_massSupp P hP β p x τ).mp hτ).1,
        ((mem_massSupp P hP β p x τ).mp hτ).2.1⟩
    · intro τ hτF hτnotT
      have hτC : τ ∈ cands P hP := (Finset.mem_filter.mp hτF).1
      have hL : ¬ LowFace β p τ := (Finset.mem_filter.mp hτF).2
      have hnp : ¬ 0 < massG P hP x τ := fun hpos =>
        hτnotT (Finset.mem_filter.mpr ⟨hτC, hL, hpos⟩)
      have hz : massG P hP x τ = 0 := le_antisymm (not_lt.mp hnp) (massG_nonneg P hP x τ)
      rw [hz, zero_smul]
  have h2 : (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ • bary τ)
      = BOf β p P hP x := by
    have h3 : (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ),
          massG P hP x τ • bary τ)
        = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ),
          (if LowFace β p τ then 0 else massG P hP x τ • bary τ) :=
      Finset.sum_congr rfl (fun τ hτ => by rw [if_neg (Finset.mem_filter.mp hτ).2])
    rw [h3, BOf]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro τ hτC hτnotF
    rw [if_pos ?_]
    by_contra hL
    exact hτnotF (Finset.mem_filter.mpr ⟨hτC, hL⟩)
  exact (h1.trans h2).symm

/-- **The high endpoint is a convex combination of the support's barycentres.**  For any `x`,

  `wOf β p P hP x = ∑_{τ ∈ supp} (massG τ / SOf) • bary τ`. -/
theorem wOf_eq_sum_massSupp (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n) :
    wOf β p P hP x =
      ∑ τ ∈ massSupp P hP β p x, (massG P hP x τ / SOf β p P hP x) • bary τ := by
  classical
  by_cases hS : SOf β p P hP x = 0
  · rw [wOf, if_pos hS]
    refine (Finset.sum_eq_zero (fun τ _ => ?_)).symm
    rw [hS, div_zero, zero_smul]
  · rw [wOf, if_neg hS, BOf_eq_sum_massSupp, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    rw [smul_smul]
    have : (SOf β p P hP x)⁻¹ * massG P hP x τ = massG P hP x τ / SOf β p P hP x := by
      rw [div_eq_mul_inv, mul_comm]
    rw [this]

theorem wOf_mem_high {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ} {x : PL.E n}
    (hx : x ∈ P.space) (hS : 0 < Work.Geo.DualStretch.SOf β p P hP x) :
    Work.Geo.DualStretch.wOf β p P hP x ∈ Work.Geo.DualStretch.High P p := by
  classical
  obtain ⟨hnn, hsumone, hsumx, hzero, hchain, hfaces⟩ := massG_api P hP hx
  set T : Finset (Finset (PL.E n)) := massSupp P hP β p x with hT
  have hmemT : ∀ τ, τ ∈ T ↔ τ ∈ cands P hP ∧ ¬ LowFace β p τ ∧ 0 < massG P hP x τ := by
    intro τ; rw [hT]; exact mem_massSupp P hP β p x τ
  have hSOf : SOf β p P hP x = ∑ τ ∈ T, massG P hP x τ := by
    rw [hT]; exact SOf_eq_sum_massSupp P hP β p x
  have hBOf : BOf β p P hP x = ∑ τ ∈ T, massG P hP x τ • bary τ := by
    rw [hT]; exact BOf_eq_sum_massSupp P hP β p x
  have hwOf : wOf β p P hP x =
      ∑ τ ∈ T, (massG P hP x τ / SOf β p P hP x) • bary τ := by
    rw [hT]; exact wOf_eq_sum_massSupp P hP β p x
  have hne : SOf β p P hP x ≠ 0 := ne_of_gt hS
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact hfaces τ ((hmemT τ).mp (Finset.mem_coe.mp hτ)).2.2
  · rw [Finset.nonempty_iff_ne_empty]
    intro hTempty
    rw [hTempty] at hSOf
    simp at hSOf
    linarith
  · intro σ hσ τ hτ
    exact hchain σ ((hmemT σ).mp (Finset.mem_coe.mp hσ)).1
      τ ((hmemT τ).mp (Finset.mem_coe.mp hτ)).1
      ((hmemT σ).mp (Finset.mem_coe.mp hσ)).2.2 ((hmemT τ).mp (Finset.mem_coe.mp hτ)).2.2
  · intro σ hσ
    have h1 : ¬ (σ.card ≤ p + 1) := ((hmemT σ).mp (Finset.mem_coe.mp hσ)).2.1
    omega
  · rw [PL.simp]
    have hsum1 : ∑ τ ∈ T, massG P hP x τ / SOf β p P hP x = 1 := by
      rw [← Finset.sum_div, ← hSOf, div_self hne]
    have hcoeff : ∀ τ ∈ T, 0 ≤ massG P hP x τ / SOf β p P hP x :=
      fun τ _ => div_nonneg (massG_nonneg P hP x τ) (le_of_lt hS)
    have hcm : T.centerMass (fun τ => massG P hP x τ / SOf β p P hP x) bary
        ∈ convexHull ℝ ((T.image bary : Finset (PL.E n)) : Set (PL.E n)) :=
      Finset.centerMass_mem_convexHull (t := T) (w := _) hcoeff (by rw [hsum1]; norm_num)
        (z := bary) (fun τ hτ => Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ, hτ, rfl⟩))
    rw [Finset.centerMass_eq_of_sum_1 T bary hsum1] at hcm
    rw [hwOf]
    exact hcm

end Work.Geo.DualStretch

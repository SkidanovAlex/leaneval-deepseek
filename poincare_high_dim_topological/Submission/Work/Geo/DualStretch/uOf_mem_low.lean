/-
A6 `Geo/DualStretch` — the low endpoint of the join segment lies in the `p`-skeleton.

`Low P p` is the `p`-skeleton of `P`, the union of the simplices of the faces with at most `p + 1`
vertices.  The claim proved here is that the low endpoint `uOf β p P hP x` of the join segment
through a point `x ∈ P.space` belongs to it, as soon as the high mass `SOf β p P hP x` is `< 1`
(so that `uOf` is the renormalised low part and not the degenerate value `0`).

The argument is exactly the mirror image of the one in `wOf_mem_high`:

* the low endpoint is the barycentric combination `∑_{τ ∈ L} (massG τ / (1 - S)) • bary τ` of the
  low level sets `L` of positive mass (`uOf_eq_sum_massSuppLow`, `massSuppLow`);
* by `massG_api` all the level sets of positive mass are nested (`massG_pos_chain`), and each of
  them is a face of `P`; a maximal one `τ₀ ∈ L` (maximal for `⊆`, equivalently for cardinality)
  therefore contains all the others;
* every `bary τ` (`τ ∈ L`) lies in `PL.simp τ ⊆ PL.simp τ₀`, and `PL.simp τ₀` is convex, so the
  whole convex combination lies in `PL.simp τ₀` with `τ₀` a face of `P` of `≤ p + 1` vertices.

The only imported API used at the end is the bundle `massG_api`, supplying non-negativity, the total
mass `∑_{τ ∈ cands} massG τ = 1`, the chain property of the support and the fact that a level set of
positive mass is a face of `P`.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.massG_api

open Set Metric
open scoped Classical

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.Geo.DualStretch

variable {n : ℕ}

/-! ### The low support of `massG` -/

/-- **The low support of `massG` at `x`.**  The level sets `τ` of the barycentric subdivision of
`x` which are low (`LowFace β p τ`, i.e. `τ.card ≤ p + 1`) and carry positive mass.  These are
exactly the barycentric-subdivision simplices of `x` whose barycentre is a vertex of `Low P p`. -/
noncomputable def massSuppLow (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n) :
    Finset (Finset (PL.E n)) :=
  (cands P hP).filter (fun τ => LowFace β p τ ∧ 0 < massG P hP x τ)

lemma mem_massSuppLow (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n)
    (τ : Finset (PL.E n)) :
    τ ∈ massSuppLow P hP β p x ↔
      τ ∈ cands P hP ∧ LowFace β p τ ∧ 0 < massG P hP x τ := by
  simp only [massSuppLow, Finset.mem_filter]

/-- **`AOf` as the barycentric combination over the low support.**  The low part of `x` is
`∑_{τ ∈ supp} massG τ • bary τ`: low level sets of zero mass contribute nothing, and non-low ones
do not occur in `AOf` at all. -/
theorem AOf_eq_sum_massSuppLow (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ)
    (x : PL.E n) :
    AOf β p P hP x = ∑ τ ∈ massSuppLow P hP β p x, massG P hP x τ • bary τ := by
  classical
  have h1 : (∑ τ ∈ massSuppLow P hP β p x, massG P hP x τ • bary τ)
      = ∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ),
          massG P hP x τ • bary τ := by
    refine Finset.sum_subset ?_ ?_
    · intro τ hτ
      exact Finset.mem_filter.mpr ⟨((mem_massSuppLow P hP β p x τ).mp hτ).1,
        ((mem_massSuppLow P hP β p x τ).mp hτ).2.1⟩
    · intro τ hτF hτnotT
      have hτC : τ ∈ cands P hP := (Finset.mem_filter.mp hτF).1
      have hL : LowFace β p τ := (Finset.mem_filter.mp hτF).2
      have hnp : ¬ 0 < massG P hP x τ := fun hpos =>
        hτnotT (Finset.mem_filter.mpr ⟨hτC, hL, hpos⟩)
      have hz : massG P hP x τ = 0 := le_antisymm (not_lt.mp hnp) (by rw [massG]; exact le_max_left _ _)
      rw [hz, zero_smul]
  have h2 : (∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ),
        massG P hP x τ • bary τ) = AOf β p P hP x := by
    rw [AOf, ← Finset.sum_filter]
  exact (h1.trans h2).symm

/-- **The low endpoint is a convex combination of the low support's barycentres.**  For any `x`,
whenever `SOf β p P hP x ≠ 1`,

  `uOf β p P hP x = ∑_{τ ∈ supp} (massG τ / (1 - SOf)) • bary τ`. -/
theorem uOf_eq_sum_massSuppLow (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n)
    (h : SOf β p P hP x ≠ 1) :
    uOf β p P hP x =
      ∑ τ ∈ massSuppLow P hP β p x, (massG P hP x τ / (1 - SOf β p P hP x)) • bary τ := by
  classical
  have hne : 1 - SOf β p P hP x ≠ 0 := by intro h0; exact h (by linarith)
  rw [uOf, if_neg hne, AOf_eq_sum_massSuppLow, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have hcoe : (1 - SOf β p P hP x)⁻¹ * massG P hP x τ
      = massG P hP x τ / (1 - SOf β p P hP x) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [smul_smul, hcoe]

/-- **The total low mass.**  The masses of the low level sets add up to `1 - SOf`, the complement
of the total high mass. -/
theorem sum_massSuppLow_eq_one_sub_SOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ)
    {x : PL.E n} (hx : x ∈ P.space) :
    ∑ τ ∈ massSuppLow P hP β p x, massG P hP x τ = 1 - SOf β p P hP x := by
  classical
  obtain ⟨hnn, hsumone, -, -, -, -⟩ := massG_api P hP hx
  have hSfilt : SOf β p P hP x
      = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ := by
    have h3 : SOf β p P hP x
        = ∑ τ ∈ cands P hP,
            (if (fun τ => ¬ LowFace β p τ) τ then massG P hP x τ else 0) := by
      rw [SOf]
      exact Finset.sum_congr rfl (fun τ _ => by by_cases h : LowFace β p τ <;> simp [h])
    rw [h3, Finset.sum_filter]
  have h1 : (∑ τ ∈ massSuppLow P hP β p x, massG P hP x τ)
      = ∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ), massG P hP x τ := by
    refine Finset.sum_subset ?_ ?_
    · intro τ hτ
      exact Finset.mem_filter.mpr ⟨((mem_massSuppLow P hP β p x τ).mp hτ).1,
        ((mem_massSuppLow P hP β p x τ).mp hτ).2.1⟩
    · intro τ hτF hτnotT
      have hτC : τ ∈ cands P hP := (Finset.mem_filter.mp hτF).1
      have hL : LowFace β p τ := (Finset.mem_filter.mp hτF).2
      have hnp : ¬ 0 < massG P hP x τ := fun hpos =>
        hτnotT (Finset.mem_filter.mpr ⟨hτC, hL, hpos⟩)
      exact le_antisymm (not_lt.mp hnp) (hnn τ hτC)
  have h2 : (∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ), massG P hP x τ)
      + (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact hsumone
  rw [h1, hSfilt] at *
  linarith

theorem uOf_mem_low {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β α : ℝ}
    (hsp : P.space = PL.closedCube β) (hαβ : α < β) {p : ℕ} {x : PL.E n} (hx : x ∈ P.space)
    (hxα : x ∈ PL.closedCube α) (hS : Work.Geo.DualStretch.SOf β p P hP x < 1) :
    Work.Geo.DualStretch.uOf β p P hP x ∈ Work.Geo.DualStretch.Low P p := by
  classical
  obtain ⟨hnn, -, -, -, hchain, hfaces⟩ := massG_api P hP hx
  set T : Finset (Finset (PL.E n)) := massSuppLow P hP β p x with hT
  have hmemT : ∀ τ : Finset (PL.E n),
      τ ∈ T ↔ τ ∈ cands P hP ∧ LowFace β p τ ∧ 0 < massG P hP x τ := by
    intro τ
    rw [hT, mem_massSuppLow]
  have hsumT : ∑ τ ∈ T, massG P hP x τ = 1 - SOf β p P hP x := by
    rw [hT]
    exact sum_massSuppLow_eq_one_sub_SOf P hP β p hx
  have hne : SOf β p P hP x ≠ 1 := by linarith
  have huOf : uOf β p P hP x
      = ∑ τ ∈ T, (massG P hP x τ / (1 - SOf β p P hP x)) • bary τ := by
    rw [hT]
    exact uOf_eq_sum_massSuppLow P hP β p x hne
  have hpos1 : 0 < 1 - SOf β p P hP x := by linarith
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have h := hsumT
    rw [hemp] at h
    simp at h
    linarith
  obtain ⟨τ₀, hτ₀T, hmax⟩ := Finset.exists_max_image T (fun τ => τ.card) hTne
  have hτ₀ : τ₀ ∈ cands P hP ∧ LowFace β p τ₀ ∧ 0 < massG P hP x τ₀ := (hmemT τ₀).mp hτ₀T
  have hsub : ∀ τ ∈ T, τ ⊆ τ₀ := by
    intro τ hτ
    have hτ' : τ ∈ cands P hP ∧ LowFace β p τ ∧ 0 < massG P hP x τ := (hmemT τ).mp hτ
    rcases hchain τ hτ'.1 τ₀ hτ₀.1 hτ'.2.2 hτ₀.2.2 with h | h
    · exact h
    · have heq : τ₀ = τ := Finset.eq_of_subset_of_card_le h (hmax τ hτ)
      rw [heq]
  have hconv : Convex ℝ (PL.simp τ₀) := by
    rw [PL.simp]
    exact convex_convexHull ℝ _
  refine ⟨τ₀, hfaces τ₀ hτ₀.2.2, hτ₀.2.1, ?_⟩
  rw [huOf]
  refine Convex.sum_mem hconv ?_ ?_ ?_
  · intro τ hτ
    exact div_nonneg (hnn τ ((hmemT τ).mp hτ).1) (le_of_lt hpos1)
  · rw [← Finset.sum_div, hsumT]
    exact div_self (sub_ne_zero.mpr (Ne.symm hne))
  · intro τ hτ
    exact PL.simp_mono (hsub τ hτ)
      (bary_mem_simp (Geometry.SimplicialComplex.nonempty_of_mem_faces (hfaces τ ((hmemT τ).mp hτ).2.2)))

end Work.Geo.DualStretch

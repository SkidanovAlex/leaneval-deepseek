/-
  WilG4a / CD / `germDefs` — the vocabulary of the target `Work.WilG4a.CD.fibGerm_mem`.

  For a family `f : ℝᵖ → ℝ → ℝ` the *fibre-germ set* is

    `fibGerm f j = {z : ℝ^{p+1} | ∃ ρ > 0, ∀ t, t ≠ z(last) → |t - z(last)| < ρ →
      Fin.snoc (Fin.init z) t ∈ smoothLocus f j}`,

  i.e. the points whose *punctured* fibre neighbourhood lies in the interior of the joint `C^j`
  locus.  The `Ω`-membership of this set is a first-order formula construction over the real
  numbers in the single ambient space `ℝ^{p+3}` with the coordinate blocks

    `(z | δ | t)`,  `p+1 + 1 + 1 = p+3`,

  `z` on coordinates `0,…,p`, `δ = z (cdl p)` on coordinate `p+1` and `t = z (cyl p)` on
  coordinate `p+2`.  The vocabulary:

  * `germBody p X` is the conjunction of the three atoms of the *negated* body:
    `t ≠ z(last)` (`bTneX p`), `(t - z(last))² < δ²` (`inflCell p`, from `Work.WilG4a.CD.Defs`)
    and the pullback `σ(z,t) ∈ X` along `iotaInfl p` (`Work.WilG5.coordPre`), where
    `σ(z,t) = Fin.snoc (Fin.init z) t` (this is `Work.WilG4a.CD.iota_pull`);
  * `germAux p X` is the `Ω`-construction
    `projLast ({δ > 0} ∩ (projLast (germBody p X))ᶜ)`: project `t` away, complement (this is
    `∀ t`), adjoin `δ > 0`, project `δ` away (this is `∃ δ > 0`).

  The two mathematical facts about this vocabulary live in sibling modules:

  * `Work.WilG4a.CD.germAux_mem` — the `Ω`-membership of `germAux p X` for `X ∈ S.Ω`;
  * `Work.WilG4a.CD.fibGerm_eq_germAux` — `fibGerm f j = germAux p (badLocus f j)`.

  This file only fixes the notation and records the coordinatised reading of `germAux`.
-/
import Mathlib
import Submission.Work.WilG4a.CD.inflated_mem
import Submission.Work.WilG4a.CD.fibDerivDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## 1. The vocabulary -/

/-- The atom `t ≠ z(last)` in `ℝ^{p+3}` (coordinates `(z | δ | t)`). -/
def bTneX (p : ℕ) : Set (Fin (p + 3) → ℝ) := {u | u (cyl p) ≠ u (czt p)}

/-- The body of the formula defining the fibre germ: `t ≠ z(last)` and `(t - z(last))² < δ²`
and the fibre point `Fin.snoc (Fin.init z) t` lying in `X`.  All read in `ℝ^{p+3}` with
coordinates `(z | δ | t)`. -/
def germBody (p : ℕ) (X : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 3) → ℝ) :=
  bTneX p ∩ inflCell p ∩ Work.WilG5.coordPre (iotaInfl p) X

/-- The `Ω`-construction of the punctured fibre germ: project `t` away, complement (this is
`∀ t`), adjoin `δ > 0`, project `δ` away (this is `∃ δ > 0`). -/
def germAux (p : ℕ) (X : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast (posHalf_y (p + 2) (Fin.last (p + 1)) ∩ (projLast (germBody p X))ᶜ)

/-! ## 2. Reading the three atoms at a point `(z, δ, t)` -/

/-- The atom `t ≠ z(last)` at the point `Fin.snoc (Fin.snoc z δ) t`. -/
lemma mem_bTneX (p : ℕ) (z : Fin (p + 1) → ℝ) (δ t : ℝ) :
    Fin.snoc (Fin.snoc z δ) t ∈ bTneX p ↔ t ≠ z (Fin.last p) := by
  simp [bTneX, czt, cyl]

/-- The pullback atom `σ(z,t) ∈ X` (`σ(z,t) = Fin.snoc (Fin.init z) t`) at the point
`Fin.snoc (Fin.snoc z δ) t`. -/
lemma mem_coordPre_iotaInfl (p : ℕ) (X : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ)
    (δ t : ℝ) :
    Fin.snoc (Fin.snoc z δ) t ∈ Work.WilG5.coordPre (iotaInfl p) X ↔
      Fin.snoc (Fin.init z) t ∈ X := by
  simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq]
  rw [iota_pull]

/-- The coordinatised reading of `germAux p X`. -/
theorem mem_germAux {p : ℕ} (X : Set (Fin (p + 1) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ germAux p X ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      ¬ (t ≠ z (Fin.last p) ∧ (t - z (Fin.last p)) ^ 2 < δ ^ 2 ∧
        Fin.snoc (Fin.init z) t ∈ X) := by
  constructor
  · rintro ⟨δ, hmem⟩
    rw [Set.mem_inter_iff, Set.mem_compl_iff] at hmem
    obtain ⟨hpos, hnot⟩ := hmem
    have hδ : 0 < δ := by simpa [posHalf_y] using hpos
    refine ⟨δ, hδ, fun t ht => ?_⟩
    obtain ⟨htne, htsq, htX⟩ := ht
    apply hnot
    refine ⟨t, ?_⟩
    rw [germBody, Set.mem_inter_iff, Set.mem_inter_iff]
    exact ⟨⟨(mem_bTneX p z δ t).mpr htne, (mem_inflCell_snoc p z δ t).mpr htsq⟩,
      (mem_coordPre_iotaInfl p X z δ t).mpr htX⟩
  · rintro ⟨δ, hδ, hall⟩
    refine ⟨δ, ?_⟩
    rw [Set.mem_inter_iff, Set.mem_compl_iff]
    refine ⟨by simpa [posHalf_y] using hδ, ?_⟩
    rintro ⟨t, ht⟩
    rw [germBody, Set.mem_inter_iff, Set.mem_inter_iff] at ht
    obtain ⟨⟨hb, hi⟩, hc⟩ := ht
    exact hall t ⟨(mem_bTneX p z δ t).mp hb, (mem_inflCell_snoc p z δ t).mp hi,
      (mem_coordPre_iotaInfl p X z δ t).mp hc⟩

end Work.WilG4a.CD

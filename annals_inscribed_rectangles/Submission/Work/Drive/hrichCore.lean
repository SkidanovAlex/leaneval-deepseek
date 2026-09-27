import Mathlib
import Submission.Work.Drive.blockZeroCoset
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.projTimesLine

/-!
# The linear-algebra core of `hrich` for the corrected ends-clause family

`ENCODED_GENERIC_DEAD.md` §0–§2 (second version) reduces the richness `hrich` of the parametrised Sard
for `Work.Drive.encFamQ0` to two facts about the *reaches* of the three parameter blocks at a zero of
the charted triple-difference map:

* `R₀ ⊆ ℝ⁴` — the reach of block `0`: it consists of *class* directions only (block `0`'s level is the
  constant `c₀`), and contains `W₀ ⊕ 0` with `W₀ ⊆ ℝ³` the `2`-dimensional reach produced by the
  domain shear `Sh_{q₀}` of `H` (and all of `ℝ³` when the class perturbation `p` is alive);
* `R₁ ⊆ ℝ⁴`, `R₂ ⊆ ℝ⁴` — the reaches of the two plane blocks: `A' ⊕ ℝe₃` and `B' ⊕ ℝe₃`, where
  `A' , B' ⊆ ℝ³` are the class reaches (the charted images of `range (mfderiv A …)`) and `e₃` is the
  level direction supplied by the twist `θ`;
* the parameter blocks are **independent**, so the triple map `(D₀,D₁,D₂)` is onto `R₀ × R₁ × R₂`.

This file proves the two purely linear-algebraic consequences that close the argument:

* `exists_mem_inter_cosets_cls` — the coset lemma lifted to `ℝ⁴ = ℝ³ ⊕ ℝe₃` in the exact shape in which
  the reaches occur: `R₀` has level `0` and `R₁`, `R₂` have full level;
* `surjective_pair_sub_of_coset` — **the closer**: if the reaches satisfy the coset condition and the
  triple is onto `R₀ × R₁ × R₂`, then `(D₀ − D₁, D₀ − D₂)` is onto `ℝ⁴ × ℝ⁴`, which (by
  `Work.Drive.TParity.surjective_fderiv_chartDiff3_of_block`'s derivative computation) is exactly
  `hrich`'s conclusion.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. The coordinate splitting of `ℝ⁴ = ℝ³ ⊕ ℝ e₃` -/

/-- The class coordinates of `ℝ⁴` — the first factor of the splitting `ℝ⁴ ≅ ℝ³ × ℝ` realised by
`Work.Drive.psiLin` (whose **last** coordinate is the level, `Work.Drive.psiLin_fourth_coord`). -/
def clsCLM : Tgt 4 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 3)) ℝ).comp
    (psiLin.symm : Tgt 4 →L[ℝ] (EuclideanSpace ℝ (Fin 3) × ℝ))

/-- The level coordinate of `ℝ⁴`. -/
def lvlCLM : Tgt 4 →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 3)) ℝ).comp
    (psiLin.symm : Tgt 4 →L[ℝ] (EuclideanSpace ℝ (Fin 3) × ℝ))

@[simp] lemma clsCLM_psiLin (w : EuclideanSpace ℝ (Fin 3)) (l : ℝ) :
    clsCLM (psiLin (w, l)) = w := by
  simp [clsCLM, ContinuousLinearEquiv.symm_apply_apply]

@[simp] lemma lvlCLM_psiLin (w : EuclideanSpace ℝ (Fin 3)) (l : ℝ) :
    lvlCLM (psiLin (w, l)) = l := by
  simp [lvlCLM, ContinuousLinearEquiv.symm_apply_apply]

/-- The class directions with zero level, for a subspace `W ⊆ ℝ³`. -/
def lift0 (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : Submodule ℝ (Tgt 4) :=
  W.comap clsCLM.toLinearMap ⊓ lvlCLM.ker

/-- The class directions of `W` with arbitrary level. -/
def liftAll (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : Submodule ℝ (Tgt 4) :=
  W.comap clsCLM.toLinearMap

@[simp] lemma mem_lift0 {W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))} {z : Tgt 4} :
    z ∈ lift0 W ↔ clsCLM z ∈ W ∧ lvlCLM z = 0 := Iff.rfl

@[simp] lemma mem_liftAll {W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))} {z : Tgt 4} :
    z ∈ liftAll W ↔ clsCLM z ∈ W := Iff.rfl

/-- **The coset lemma in the form in which the reaches occur.**  If `R₀` is the lift of `W₀` with zero
level and `R₁`, `R₂` are the lifts of `A'`, `B'` with arbitrary level, and `A' ⊔ B' = ⊤`,
`W₀ ⊔ (A' ⊓ B') = ⊤`, then for all `w₁ w₂ : ℝ⁴` there is `a ∈ R₀` with `a - w₁ ∈ R₁` and
`a - w₂ ∈ R₂`. -/
theorem exists_coset_mem_lift (W₀ A' B' : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hA : A' ⊔ B' = ⊤) (hW : W₀ ⊔ (A' ⊓ B') = ⊤) (w₁ w₂ : Tgt 4) :
    ∃ a ∈ lift0 W₀, a - w₁ ∈ liftAll A' ∧ a - w₂ ∈ liftAll B' := by
  obtain ⟨w, hwW, hw₁, hw₂⟩ :=
    exists_mem_inter_cosets_of_sup_eq_top W₀ A' B' hA hW (clsCLM w₁) (clsCLM w₂)
  refine ⟨psiLin (w, 0), ?_, ?_, ?_⟩
  · rw [mem_lift0]
    exact ⟨by simpa using hwW, by simp⟩
  · rw [mem_liftAll]
    simp only [map_sub, clsCLM_psiLin]
    exact hw₁
  · rw [mem_liftAll]
    simp only [map_sub, clsCLM_psiLin]
    exact hw₂

/-! ## 2. The closer -/

/-- **The closer of `hrich`.**  Let `D₀, D₁, D₂` be the parameter derivatives of the three charted
chains at a zero, and `R₀, R₁, R₂` submodules containing their ranges.  If

* the triple `(D₀, D₁, D₂)` is onto `R₀ × R₁ × R₂` (which holds for a product parameter space whose
  blocks act on the three chains independently), and
* the coset condition `∀ w₁ w₂, ∃ a ∈ R₀, a - w₁ ∈ R₁ ∧ a - w₂ ∈ R₂` holds,

then the difference map `(D₀ − D₁, D₀ − D₂)` is onto `ℝ⁴ × ℝ⁴`. -/
theorem surjective_pair_sub_of_coset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D₀ D₁ D₂ : E →L[ℝ] Tgt 4) (R₀ R₁ R₂ : Submodule ℝ (Tgt 4))
    (h0 : D₀.range ≤ R₀) (h1 : D₁.range ≤ R₁) (h2 : D₂.range ≤ R₂)
    (hreal : ∀ a ∈ R₀, ∀ b ∈ R₁, ∀ c ∈ R₂, ∃ u : E, D₀ u = a ∧ D₁ u = b ∧ D₂ u = c)
    (hcoset : ∀ w₁ w₂ : Tgt 4, ∃ a ∈ R₀, a - w₁ ∈ R₁ ∧ a - w₂ ∈ R₂) :
    Function.Surjective (fun u : E => (D₀ u - D₁ u, D₀ u - D₂ u)) := by
  intro p
  obtain ⟨w₁, w₂⟩ := p
  obtain ⟨a, haR, hb, hc⟩ := hcoset w₁ w₂
  obtain ⟨u, hu₀, hu₁, hu₂⟩ := hreal a haR (a - w₁) hb (a - w₂) hc
  refine ⟨u, ?_⟩
  show (D₀ u - D₁ u, D₀ u - D₂ u) = (w₁, w₂)
  rw [hu₀, hu₁, hu₂]
  simp

end

end Work.Drive

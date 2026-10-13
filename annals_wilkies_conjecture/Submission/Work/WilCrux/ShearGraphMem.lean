import Mathlib
import Submission.Work.WilCrux.Defs
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.ParCompGraphMem
import Submission.Work.WilG4c.FamGraphPolyComb
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## The index map of the shear

`shearFam g e φ` turned into a single function of the already-ungrouped variable
`z : Fin (m + n₁ + n₂) → ℝ` reads `(v, u)` off `z` (parameters first, then the fibre
variable).  The *index map* below assembles the corresponding point of `ℝ^{m+N}` (the ambient
space of the family `g`), i.e. it is `(v,u) ↦ sheetPt e v (φ v + u)`. -/

/-- The index map of the shear: `(v,u) ↦ sheetPt e v (φ v + u)`, with `(v,u)` read off the
ungrouped variable `z`. -/
def shearIdx {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)) :
    (Fin (m + n1 + n2) → ℝ) → (Fin (m + N) → ℝ) :=
  fun z => sheetPt e (fun i : Fin (m + n1) => z (Fin.castAdd n2 i))
    (φ (fun i : Fin (m + n1) => z (Fin.castAdd n2 i)) + fun j : Fin n2 => z (Fin.natAdd (m + n1) j))

/-- The uncurried joint function of `shearFam g e φ` is the uncurried joint function of `g`
precomposed with `shearIdx e φ`. -/
theorem pcgm_compGFam_shearFam_eq {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)) :
    Work.WilG4c.pcgm_compGFam (shearFam g e φ)
      = Work.WilG4c.pcgm_compGFam g ∘ shearIdx e φ := by
  funext z
  simp only [Work.WilG4c.pcgm_compGFam, Function.comp_def, shearIdx, shearFam,
    sheetPt_castAdd, sheetPt_natAdd]

/-- The graph of the sheared family is the graph of the composite of the uncurried family `g`
with the index map `shearIdx`. -/
theorem famGraph_shearFam_eq {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)) :
    CG.famGraph (shearFam g e φ)
      = graphOf (Work.WilG4c.pcgm_compGFam g ∘ shearIdx e φ) := by
  rw [← Work.WilG4c.pcgm_graphOf_compGFam (f := shearFam g e φ),
    pcgm_compGFam_shearFam_eq]

/-! ## Two `Ω`-closure lemmas for graphs -/

/-- **Sum of two `Ω`-definable graphs.**  If the graphs of `H₀, H₁ : ℝ^M → ℝ` are
`Ω Fᵢ Dᵢ`-definable then so is the graph of `H₀ + H₁`, with format `F₀ + F₁ + A` and degree
`C * ((D₀ + D₁) + 1) + C` for constants `A, C` depending only on `S` and `M`.

This is `Work.WilG4c.FamGraphPolyComb` at `k = 2` with `P = X 0 + X 1`. -/
theorem graphOf_add_mem (S : WilkiesDesign.SOMin) (M : ℕ) :
    ∃ A C : ℕ, ∀ (F0 F1 D0 D1 : ℕ) (H0 H1 : (Fin M → ℝ) → ℝ),
    graphOf H0 ∈ S.Ω F0 D0 (M+1) → graphOf H1 ∈ S.Ω F1 D1 (M+1) →
    graphOf (fun x => H0 x + H1 x) ∈
      S.Ω (F0 + F1 + A) (C * ((D0 + D1) + 1) + C) (M+1) := by
  obtain ⟨A, C, hpoly⟩ := Work.WilG4c.FamGraphPolyComb S M 2
  refine ⟨A, C, fun F0 F1 D0 D1 H0 H1 h0 h1 => ?_⟩
  have hF : ∀ i : Fin 2, graphOf (![H0, H1] i) ∈
      S.Ω (![F0, F1] i) (![D0, D1] i) (M + 1) := by
    intro i; fin_cases i <;> simpa using (by assumption)
  have hP := hpoly ![F0, F1] ![D0, D1] ![H0, H1]
    (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) hF
  have hfun : (fun x : Fin M → ℝ => MvPolynomial.eval (fun i => ![H0, H1] i x)
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)) =
      (fun x => H0 x + H1 x) := by
    funext x; simp [MvPolynomial.eval_add]
  rw [hfun] at hP
  have hsumF : (∑ i : Fin 2, ![F0, F1] i) = F0 + F1 := by rw [Fin.sum_univ_two]; simp
  have hsumD : (∑ i : Fin 2, ![D0, D1] i) = D0 + D1 := by rw [Fin.sum_univ_two]; simp
  rw [hsumF, hsumD] at hP
  refine Work.WilG1.Omega.mono hP le_rfl ?_
  have htd : (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [max_le_iff]
    exact ⟨le_of_eq (MvPolynomial.totalDegree_X 0), le_of_eq (MvPolynomial.totalDegree_X 1)⟩
  have h1 : (D0 + D1) + (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ (D0 + D1) + 1 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left C h1) C

/-- **Pullback of a graph along the projection to the first `m+n₁` coordinates.**  If the graph
of `ψ : ℝ^{m+n₁} → ℝ` is `Ω F' D'`-definable then so is the graph of
`z ↦ ψ (z ∘ castAdd n₂)`, with format `F' + (m+n₁+n₂+1) + C₁` and degree `D' + (m+n₁) + C₂`
for constants `C₁, C₂` depending only on `S`, `m`, `n₁`, `n₂`.

This is the rectangular composition lemma `Work.WilG4c.graphOfCompGen` applied with the
coordinate projection `z ↦ z ∘ castAdd n₂`, all of whose coordinate graphs are hyperplanes. -/
theorem graphOf_pull_castAdd (S : WilkiesDesign.SOMin) (m n1 n2 F' D' : ℕ) :
    ∃ Fp Dp, ∀ (ψ : (Fin (m + n1) → ℝ) → ℝ),
      graphOf ψ ∈ S.Ω F' D' (m + n1 + 1) →
      graphOf (fun z : Fin (m + n1 + n2) → ℝ =>
          ψ (fun i : Fin (m + n1) => z (Fin.castAdd n2 i)))
        ∈ S.Ω Fp Dp (m + n1 + n2 + 1) := by
  obtain ⟨C₁, C₂, hgen⟩ := Work.WilG4c.graphOfCompGen S (m + n1) (m + n1 + n2)
  refine ⟨F' + (m + n1 + n2 + 1) + C₁, D' + (m + n1) * 1 + C₂, fun ψ hψ => ?_⟩
  simpa only [Function.comp_def] using
    (hgen F' (m + n1 + n2 + 1) D' 1 ψ (fun z i => z (Fin.castAdd n2 i)) hψ
      (fun i => Work.WilG4c.pcgm_graphOf_projCoord_mem S (m + n1 + n2) (Fin.castAdd n2 i)))

/-- Every `i : Fin (m+n)` is either a `castAdd` or a `natAdd`. -/
lemma exists_eq_castAdd_or_eq_natAdd {m n : ℕ} (i : Fin (m + n)) :
    (∃ i' : Fin m, i = Fin.castAdd n i') ∨ (∃ i' : Fin n, i = Fin.natAdd m i') := by
  refine Fin.addCases (motive := fun i => (∃ i' : Fin m, i = Fin.castAdd n i') ∨
    (∃ i' : Fin n, i = Fin.natAdd m i')) (fun i' => Or.inl ⟨i', rfl⟩) (fun i' => Or.inr ⟨i', rfl⟩) i

/-! ## The coordinate graphs of the index map -/

/-- **Every coordinate of `shearIdx e φ` has an `Ω`-definable graph.**  The `m` parameter
coordinates are plain coordinate projections; the `N` fibre coordinates are either coordinate
projections (when the corresponding entry of `e` is a band coordinate) or a sum of the
pullback of `graphOf (φ · k)` along the projection to the first `m+n₁` coordinates and a
coordinate projection (when it is a graph coordinate). -/
theorem graphOf_shearIdx_coord_mem (S : WilkiesDesign.SOMin) (m n1 n2 N : ℕ) (F' D' : ℕ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ))
    (hφ : ∀ j : Fin n2, graphOf (fun v => φ v j) ∈ S.Ω F' D' (m + n1 + 1)) :
    ∃ F2 D2 : ℕ, ∀ j : Fin (m + N),
      graphOf (fun z : Fin (m + n1 + n2) → ℝ => shearIdx e φ z j) ∈
        S.Ω F2 D2 (m + n1 + n2 + 1) := by
  obtain ⟨A, C, hsum⟩ := graphOf_add_mem S (m + n1 + n2)
  obtain ⟨Fp, Dp, hpull⟩ := graphOf_pull_castAdd S m n1 n2 F' D'
  refine ⟨max (m + n1 + n2 + 1) (Fp + (m + n1 + n2 + 1) + A),
    max 1 (C * ((Dp + 1) + 1) + C), ?_⟩
  intro j
  refine Fin.addCases (motive := fun j => graphOf
      (fun z : Fin (m + n1 + n2) → ℝ => shearIdx e φ z j) ∈
      S.Ω (max (m + n1 + n2 + 1) (Fp + (m + n1 + n2 + 1) + A))
        (max 1 (C * ((Dp + 1) + 1) + C)) (m + n1 + n2 + 1)) ?_ ?_ j
  · -- the `m` parameter coordinates: plain coordinate projections
    intro i
    have hfun : (fun z : Fin (m + n1 + n2) → ℝ => shearIdx e φ z (Fin.castAdd N i))
        = (fun z => z (Fin.castAdd n2 (Fin.castAdd n1 i))) := by
      funext z
      simp only [shearIdx, sheetPt_castAdd]
    rw [hfun]
    exact Work.WilG1.Omega.mono
      (Work.WilG4c.pcgm_graphOf_projCoord_mem S (m + n1 + n2) (Fin.castAdd n2 (Fin.castAdd n1 i)))
      (le_max_left _ _) (le_max_left _ _)
  · -- the `N` fibre coordinates
    intro j'
    rcases exists_eq_castAdd_or_eq_natAdd (e j') with ⟨k', hk⟩ | ⟨k'', hk⟩
    · -- a band coordinate: a plain coordinate projection
      have hfun : (fun z : Fin (m + n1 + n2) → ℝ => shearIdx e φ z (Fin.natAdd m j'))
          = (fun z => z (Fin.castAdd n2 (Fin.natAdd m k'))) := by
        funext z
        simp only [shearIdx, sheetPt_natAdd, hk, Fin.append_left]
      rw [hfun]
      exact Work.WilG1.Omega.mono
        (Work.WilG4c.pcgm_graphOf_projCoord_mem S (m + n1 + n2) (Fin.castAdd n2 (Fin.natAdd m k')))
        (le_max_left _ _) (le_max_left _ _)
    · -- a graph coordinate: the sum of a pulled-back coordinate graph and a projection
      have hfun : (fun z : Fin (m + n1 + n2) → ℝ => shearIdx e φ z (Fin.natAdd m j'))
          = (fun z => φ (fun i : Fin (m + n1) => z (Fin.castAdd n2 i)) k''
              + z (Fin.natAdd (m + n1) k'')) := by
        funext z
        simp only [shearIdx, sheetPt_natAdd, hk, Fin.append_right, Pi.add_apply]
      rw [hfun]
      refine Work.WilG1.Omega.mono
        (hsum Fp (m + n1 + n2 + 1) Dp 1
          (fun z : Fin (m + n1 + n2) → ℝ => φ (fun i : Fin (m + n1) => z (Fin.castAdd n2 i)) k'')
          (fun z : Fin (m + n1 + n2) → ℝ => z (Fin.natAdd (m + n1) k''))
          (hpull (fun v : Fin (m + n1) → ℝ => φ v k'') (hφ k''))
          (Work.WilG4c.pcgm_graphOf_projCoord_mem S (m + n1 + n2) (Fin.natAdd (m + n1) k'')))
        (le_max_right _ _) (le_max_right _ _)

/-- **N3b (`Omega`-membership of the sheared family).**  If the graph of `g` is `Omega`-definable
and every coordinate `φ · j` has an `Omega`-definable graph, then the graph of the sheared family
is `Omega`-definable, with format and degree depending only on the inputs.

Proof: `famGraph (shearFam g e φ)` is the graph of `(v,u) ↦ g (w(v)) (reindex (φ v + u))`; it is
`famGraph g` composed with the definable map `(v,u) ↦ (w(v), reindex (block v + φ v + u))`, built
from coordinate projections, the reindexing `e` and the *additions* `block v + φ v + u`
(the pattern of `Work.WilG4c.graphOfCompGen` and the `WilG4a`/`WilG5` substitution and linear
combination lemmas). -/
theorem ShearGraphMem (S : WilkiesDesign.SOMin) {m n1 n2 N F D F' D' : ℕ}
    (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (hg : WilkiesDesign.CG.famGraph g ∈ S.Ω F D (m + N + 1))
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ))
    (hφ : ∀ j : Fin n2, WilkiesDesign.graphOf (fun v => φ v j) ∈ S.Ω F' D' (m + n1 + 1)) :
    ∃ F'' D'' : ℕ, WilkiesDesign.CG.famGraph (Work.WilCrux.shearFam g e φ)
      ∈ S.Ω F'' D'' (m + n1 + n2 + 1) := by
  obtain ⟨F2, D2, hcoord⟩ := graphOf_shearIdx_coord_mem S m n1 n2 N F' D' e φ hφ
  obtain ⟨C₁, C₂, hcomp⟩ := Work.WilG4c.graphOfCompGen S (m + N) (m + n1 + n2)
  refine ⟨F + F2 + C₁, D + (m + N) * D2 + C₂, ?_⟩
  have hg' : graphOf (Work.WilG4c.pcgm_compGFam g) ∈ S.Ω F D (m + N + 1) := by
    rw [Work.WilG4c.pcgm_graphOf_compGFam]; exact hg
  have hthis := hcomp F F2 D D2 (Work.WilG4c.pcgm_compGFam g) (shearIdx e φ) hg' hcoord
  rw [famGraph_shearFam_eq]
  exact hthis

end Work.WilCrux

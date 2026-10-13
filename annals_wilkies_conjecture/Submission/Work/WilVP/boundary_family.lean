import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilC4.paramBnd_definable
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC4.encard_le_of_not_altChain
import Submission.Work.WilC4.mono_real
import Submission.Work.WilC4.paramFibre_definable

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilVP

/-! ## Slicing a definable family of subsets of the line

If `D ⊆ ℝ^{k+1}` is `∅`-definable then, for every parameter tuple `c : Fin k → ℝ`, the sliced set
`{x : ℝ | Fin.cons x c ∈ D}` is `∅`-definable (as a subset of the line).  This is the
"parameters become constants" trick: write the slice as the projection along `Fin k` of the
pullback of `D` along an index map, intersected with the equations fixing the parameters. -/

/-- The index map `Fin (k+1) → Fin 1 ⊕ Fin k` sending `0 ↦ inl 0` and `j+1 ↦ inr j`. -/
def sτ (k : ℕ) : Fin (k + 1) → Fin 1 ⊕ Fin k :=
  Fin.cons (Sum.inl 0) (fun j : Fin k => Sum.inr j)

/-- `sτ` reindexes a split tuple `(v, u)` into the concatenated tuple `(v 0, u)`. -/
lemma sτ_comp {k : ℕ} (v : Fin 1 → ℝ) (u : Fin k → ℝ) :
    (Sum.elim v u) ∘ sτ k = Fin.cons (v 0) u := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- The slice `{x : ℝ | Fin.cons x c ∈ D}` of a `∅`-definable `D ⊆ ℝ^{k+1}` is `∅`-definable. -/
lemma slice_definable₁ {k : ℕ} {D : Set (Fin (k + 1) → ℝ)}
    (hD : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc D) (c : Fin k → ℝ) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ D} := by
  rw [Set.Definable₁]
  -- pull `D` back along the index map
  have h1 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : Fin 1 ⊕ Fin k → ℝ | w ∘ sτ k ∈ D} :=
    hD.preimage_comp (sτ k)
  -- the equations fixing the parameters
  have h2 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {w : Fin 1 ⊕ Fin k → ℝ | ∀ j : Fin k, w (Sum.inr j) = c j} := by
    rw [show {w : Fin 1 ⊕ Fin k → ℝ | ∀ j : Fin k, w (Sum.inr j) = c j}
        = ⋂ j, {w : Fin 1 ⊕ Fin k → ℝ | w (Sum.inr j) = c j} from by ext w; simp]
    exact Set.definable_iInter_of_finite
      (fun j => Work.WilC4.empty_definable_coord_eq (Sum.inr j) (c j))
  have hQ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      ({w : Fin 1 ⊕ Fin k → ℝ | w ∘ sτ k ∈ D} ∩
        {w : Fin 1 ⊕ Fin k → ℝ | ∀ j : Fin k, w (Sum.inr j) = c j}) := h1.inter h2
  -- project the parameters away
  have hproj := hQ.exists_of_finite (α := Fin 1) (β := Fin k)
  have hset : {v : Fin 1 → ℝ | ∃ u : Fin k → ℝ, Sum.elim v u ∈
        ({w : Fin 1 ⊕ Fin k → ℝ | w ∘ sτ k ∈ D} ∩
          {w : Fin 1 ⊕ Fin k → ℝ | ∀ j : Fin k, w (Sum.inr j) = c j})} =
      {v : Fin 1 → ℝ | v 0 ∈ {x : ℝ | Fin.cons x c ∈ D}} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨u, hu1, hu2⟩
      have huc : u = c := funext fun j => hu2 j
      rw [sτ_comp v u, huc] at hu1
      exact hu1
    · intro hv
      exact ⟨c, by rw [sτ_comp v c]; exact hv, fun j => rfl⟩
  rw [hset] at hproj
  exact hproj

/-- Boundary points of a definable family of subsets of the line: the family
`{(x,c) : x` is a boundary point (`Work.WilC2.IsBnd`) of the `c`-fibre of `D`}
is `∅`-definable and has uniformly at most `N` points per fibre.
Definability is `Work.WilC4.paramBnd_definable` (with `n := k`, whose conclusion is literally the
first conjunct); uniform finiteness follows the pattern of `Work.WilC4.ulpm_mono_param`:
`Set.empty_definable_iff` gives a formula, `Work.WilC4.exists_alt_bound` bounds the number of
alternating chains uniformly (reindex the `Fin (k+1)` formula into `Fin k ⊕ Fin 1`),
`Work.WilC4.encard_le_of_not_altChain` needs the finiteness of each fibre, which is
`Work.WilC4.bnd_finite_of_definable` applied to the ∅-definable substituted fibre (the
`Work.WilC4.paramFibre_definable` trick: parameters become constants). -/
theorem boundary_family {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels) {D : Set (Fin (k + 1) → ℝ)}
    (hD : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc D) :
    ∃ N : ℕ, (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
        {p : Fin (k + 1) → ℝ | Work.WilC2.IsBnd {x | Fin.cons x (Fin.tail p) ∈ D} (p 0)} ∧
      ∀ c : Fin k → ℝ, {x : ℝ | Work.WilC2.IsBnd {x' | Fin.cons x' c ∈ D} x}.encard ≤ N := by
  have hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (k + 1) → ℝ | Work.WilC2.IsBnd (Work.WilC4.Pfib1 D p) (p 0)} :=
    Work.WilC4.paramBnd_definable (n := k) hD
  set B : Set (Fin (k + 1) → ℝ) :=
    {p : Fin (k + 1) → ℝ | Work.WilC2.IsBnd (Work.WilC4.Pfib1 D p) (p 0)} with hBdef
  have hBd : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B := hB
  -- reindex `Fin (k+1)` as `Fin k ⊕ Fin 1` (the first coordinate is `p 0`)
  set g : Fin (k + 1) → Fin k ⊕ Fin 1 :=
    Fin.cases (Sum.inr 0) (fun j : Fin k => Sum.inl j) with hg
  set B' : Set ((Fin k ⊕ Fin 1) → ℝ) :=
    (fun v : (Fin k ⊕ Fin 1) → ℝ => v ∘ g) ⁻¹' B with hB'
  have hB'd : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B' := by
    rw [hB']
    exact hBd.preimage_comp g
  obtain ⟨φ, hφ⟩ := Set.empty_definable_iff.mp hB'd
  obtain ⟨N, hN⟩ := Work.WilC4.exists_alt_bound hOM φ
  refine ⟨N, ?_, ?_⟩
  · show (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (k + 1) → ℝ | Work.WilC2.IsBnd {x | Fin.cons x (Fin.tail p) ∈ D} (p 0)}
    exact hB
  · intro c
    -- the boundary fibre of the slice, hence finite
    have hslice : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc {x : ℝ | Fin.cons x c ∈ D} :=
      slice_definable₁ hD c
    have hfin : {x : ℝ | Work.WilC2.IsBnd {x' : ℝ | Fin.cons x' c ∈ D} x}.Finite :=
      Work.WilC4.bnd_finite_of_definable hOM hslice
    -- the fibre of `B` at `c` is exactly that boundary set
    have hS : {x : ℝ | Fin.cons x c ∈ B} =
        {x : ℝ | Work.WilC2.IsBnd {x' : ℝ | Fin.cons x' c ∈ D} x} := by
      ext x
      rw [hBdef]
      simp only [Set.mem_ofPred_eq]
      rw [Work.WilC4.Pfib1_cons D x c]
      simp
    -- the formula realising `B'` cuts out the fibres of `B`
    have hc : {t : ℝ | φ.Realize (Sum.elim c (fun _ : Fin 1 => t))} =
        {t : ℝ | Fin.cons t c ∈ B} := by
      have hφ' : ∀ w : (Fin k ⊕ Fin 1) → ℝ, (w ∈ B' ↔ φ.Realize w) := by
        intro w
        rw [hφ]
        exact Iff.rfl
      have hcg : ∀ t : ℝ, (Sum.elim c (fun _ : Fin 1 => t)) ∘ g = Fin.cons t c := by
        intro t
        funext i
        induction i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      ext t
      simp only [Set.mem_ofPred_eq]
      rw [← hφ' (Sum.elim c (fun _ : Fin 1 => t)), hB', Set.mem_preimage, hcg t]
    have hnc : ¬ Work.WilC4.AltChain N
        {x : ℝ | Work.WilC2.IsBnd {x' : ℝ | Fin.cons x' c ∈ D} x} := by
      rw [← hS, ← hc]
      exact hN c
    exact Work.WilC4.encard_le_of_not_altChain hfin hnc

end Work.WilVP

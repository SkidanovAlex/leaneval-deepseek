/-
  WilC4/critFibreOrd : the fibres of the four parametric germ families `PMonoLm`, `PMonoHm`,
  `PMonoLp`, `PMonoHp` are finite unions of order-convex sets.

  `PMonoLm Y ⊆ ℝ^{k+1}` (for `Y ⊆ ℝ^{k+2}`) is `∅`-definable by hypothesis.  The fibre
  `{x : ℝ | Fin.cons x c ∈ PMonoLm Y}` at a parameter tuple `c` is then also `∅`-definable:
  the language `LRc` names every real by a constant symbol, so substituting the constants for
  the parameters keeps the defining formula parameter-free.  O-minimality of `ℝ`
  (`oMin_ordConnected_set`, from `mono_real`) then decomposes every `∅`-definable subset of `ℝ`
  into finitely many order-convex pieces.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC4.mono_real

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The index map `Fin (n+1) → Fin 1 ⊕ Fin n`

`cfoτ n` sends `0 ↦ Sum.inl 0` and `j+1 ↦ Sum.inr j`; it is the reindexing along which the
one-dimensional fibre of an `(n+1)`-ary set is computed (the `Fin 1` summand carries the
argument, the `Fin n` summand the parameters). -/

/-- `cfoτ n` sends `0 ↦ Sum.inl 0` and `j+1 ↦ Sum.inr j`. -/
def cfoτ (n : ℕ) : Fin (n + 1) → Fin 1 ⊕ Fin n :=
  Fin.cons (Sum.inl 0) (fun j : Fin n => Sum.inr j)

/-- Composing a split vector `Sum.elim v c` with `cfoτ n` rebuilds the `Fin.cons`-vector
`Fin.cons (v 0) c`. -/
lemma cfoτ_sumElim (n : ℕ) (v : Fin 1 → ℝ) (c : Fin n → ℝ) :
    Sum.elim v c ∘ cfoτ n = Fin.cons (v 0) c := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-! ## 2. Fibres of `∅`-definable subsets of `ℝ^{n+1}` -/

/-- The fibre `{x | Fin.cons x c ∈ S}` of a `∅`-definable set `S ⊆ ℝ^{n+1}` is `∅`-definable:
`S` is fibred by splitting the last `n` coordinates off and then existentially projecting them
back, and the coordinates of `c` are handled by the constant symbols of `LRc`. -/
theorem fibre1_definable {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable LRc S) (c : Fin n → ℝ) :
    (∅ : Set ℝ).Definable₁ LRc {x : ℝ | Fin.cons x c ∈ S} := by
  have hA : (∅ : Set ℝ).Definable LRc {g : Fin 1 ⊕ Fin n → ℝ | g ∘ cfoτ n ∈ S} :=
    hS.preimage_comp (cfoτ n)
  have hB : (∅ : Set ℝ).Definable LRc
      {g : Fin 1 ⊕ Fin n → ℝ | ∀ j : Fin n, g (Sum.inr j) = c j} := by
    rw [← Set.iInter_ofPred]
    exact Set.definable_iInter_of_finite
      (fun j : Fin n => empty_definable_coord_eq (Sum.inr j) (c j))
  have hproj := (hA.inter hB).exists_of_finite (α := Fin 1) (β := Fin n)
  have hset : {v : Fin 1 → ℝ | ∃ u : Fin n → ℝ,
        Sum.elim v u ∈ ({g : Fin 1 ⊕ Fin n → ℝ | g ∘ cfoτ n ∈ S} ∩
          {g : Fin 1 ⊕ Fin n → ℝ | ∀ j : Fin n, g (Sum.inr j) = c j})}
      = {v : Fin 1 → ℝ | Fin.cons (v 0) c ∈ S} := by
    ext v
    constructor
    · rintro ⟨u, hu, huc⟩
      have huc' : u = c := funext fun j => huc j
      rw [huc'] at hu
      simp only [Set.mem_ofPred_eq] at hu
      rw [cfoτ_sumElim n v c] at hu
      simpa only [Set.mem_ofPred_eq] using hu
    · intro hv
      refine ⟨c, ?_, fun _ => rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [cfoτ_sumElim n v c]
      exact hv
  rw [hset] at hproj
  exact hproj

/-! ## 3. The theorem -/

theorem critFibreOrd {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ))
    (hLm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y))
    (hHm : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y))
    (hLp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y))
    (hHp : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y))
    (c : Fin k → ℝ) :
    (∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoLm Y} = ⋃₀ (s : Set (Set ℝ))) ∧
    (∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoHm Y} = ⋃₀ (s : Set (Set ℝ))) ∧
    (∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoLp Y} = ⋃₀ (s : Set (Set ℝ))) ∧
    (∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
        {x : ℝ | Fin.cons x c ∈ PMonoHp Y} = ⋃₀ (s : Set (Set ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact oMin_ordConnected_set hOM (fibre1_definable hLm c)
  · exact oMin_ordConnected_set hOM (fibre1_definable hHm c)
  · exact oMin_ordConnected_set hOM (fibre1_definable hLp c)
  · exact oMin_ordConnected_set hOM (fibre1_definable hHp c)

end Work.WilC4

import Mathlib
import Submission.Work.WilC4.ParamMonoDefs

namespace Work.WilC4

/-! ## The index map and the extended family

The fibre `Pfibre Y c` is the projection along the `Fin n` parameters of the set of tuples
`u : (Fin 2 ⊕ Fin n) → ℝ` whose reindexing along `Qτ n` lies in `Y` and whose parameter
coordinates are the coordinates of `c`. -/

/-- The index map `Fin (n+2) → Fin 2 ⊕ Fin n` sending `0 ↦ inl 0`, `1 ↦ inl 1` and
`j+2 ↦ inr j`. -/
def Qτ (n : ℕ) : Fin (n + 2) → Fin 2 ⊕ Fin n :=
  Fin.cons (Sum.inl 0) (Fin.cons (Sum.inl 1) (fun j : Fin n => Sum.inr j))

/-- `Qτ` reindexes a split tuple `(v, u)` into the concatenated tuple `(v 0, v 1, u)`. -/
lemma Qτ_comp_elim {n : ℕ} (v : Fin 2 → ℝ) (u : Fin n → ℝ) :
    Sum.elim v u ∘ Qτ n = Fin.cons (v 0) (Fin.cons (v 1) u) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => rfl

/-- The extended relation: `u` is `(argument, value, parameters)` of `Y`, with the parameters
prescribed by `c`. -/
def QS {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) (c : Fin n → ℝ) : Set ((Fin 2 ⊕ Fin n) → ℝ) :=
  {u | u ∘ Qτ n ∈ Y ∧ ∀ j : Fin n, u (Sum.inr j) = c j}

/-- `Pfibre Y c` is the projection of `QS Y c` along the `Fin n` parameters. -/
lemma exists_elim_QS {n : ℕ} (Y : Set (Fin (n + 2) → ℝ)) (c : Fin n → ℝ) :
    {v : Fin 2 → ℝ | ∃ u : Fin n → ℝ, Sum.elim v u ∈ QS Y c} = Pfibre Y c := by
  ext v
  simp only [Set.mem_ofPred_eq, QS, Pfibre]
  constructor
  · rintro ⟨u, hu1, hu2⟩
    rw [Qτ_comp_elim v u] at hu1
    have huc : u = c := funext hu2
    rw [huc] at hu1
    exact hu1
  · intro hv
    exact ⟨c, by rw [Qτ_comp_elim v c]; exact hv, fun j => rfl⟩

/-- Prove in namespace `Work.WilC4` (declaration name `Work.WilC4.paramFibre_definable`) in the file
`Submission/Work/WilC4/paramFibre_definable.lean`.  The individual fibre relation of a `∅`-definable
family is again `∅`-definable: writing the index map `τ : Fin (n+2) → Fin 2 ⊕ Fin n` that sends
`0 ↦ inl 0`, `1 ↦ inl 1`, `j+2 ↦ inr j`, the set `Pfibre Y c` is the projection (along the `Fin n`
parameters) of `{u : (Fin 2 ⊕ Fin n) → ℝ | u ∘ τ ∈ Y ∧ ∀ j, u (inr j) = c j}`.  Use
`Work.WilC4.empty_definable_coord_eq` for the coordinate equations (all constants of `LRc` are
`∅`-definable names of reals) and `Definable.preimage_comp`, `Definable.exists_of_finite`. -/
theorem paramFibre_definable {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (c : Fin n → ℝ) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Pfibre Y c) := by
  -- the pullback of `Y` along the index map
  have h1 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {u : (Fin 2 ⊕ Fin n) → ℝ | u ∘ Qτ n ∈ Y} :=
    hY.preimage_comp (Qτ n)
  -- the coordinate equations `u (inr j) = c j`
  have h2 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {u : (Fin 2 ⊕ Fin n) → ℝ | ∀ j : Fin n, u (Sum.inr j) = c j} := by
    rw [show {u : (Fin 2 ⊕ Fin n) → ℝ | ∀ j : Fin n, u (Sum.inr j) = c j}
        = ⋂ j, {u : (Fin 2 ⊕ Fin n) → ℝ | u (Sum.inr j) = c j} from by ext u; simp]
    exact Set.definable_iInter_of_finite
      (fun j => empty_definable_coord_eq (Sum.inr j) (c j))
  have hQS : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (QS Y c) := h1.inter h2
  -- project along the `Fin n` parameters
  have hproj := hQS.exists_of_finite (α := Fin 2) (β := Fin n)
  rwa [exists_elim_QS] at hproj

end Work.WilC4

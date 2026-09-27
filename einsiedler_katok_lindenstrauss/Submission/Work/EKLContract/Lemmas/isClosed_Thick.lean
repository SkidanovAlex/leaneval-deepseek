import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# `Thick ρ` is closed

`Thick ρ = {x : X₃ | ¬ HasShortVec x ρ}` is the set of lattices whose shortest nonzero vector
has sup-norm `≥ ρ` (component `C2` of the frozen interface asserts it is *compact*, by Mahler).

Here we prove the purely topological half, `IsClosed (Thick ρ)`: its complement
`{x | HasShortVec x ρ}` is open.

The argument is short.  Write `S m ρ = {g : SL₃(ℝ) | ∀ i, |(g m) i| < ρ}` for the (open) set of
group elements sending the integral vector `m` into the open `sup`-norm ball of radius `ρ`.  Then

  `HasShortVec x ρ ↔ x ∈ ⋃_{m ≠ 0} mkX '' S m ρ`,

because `HasShortVec` is *defined* by the existence of a representative `g` with `mkX g = x`
together with a nonzero `m` whose image `g m` is short.  Each `S m ρ` is open (the map
`g ↦ (g m) i` is continuous, and `<` is an open condition), the projection
`mkX : SL₃(ℝ) → X₃` is an **open** map (quotient by the subgroup `Γ₃`), and an arbitrary union
of open sets is open.
-/

open Matrix

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-- The projection `mkX : SL₃(ℝ) → X₃ = SL₃(ℝ)/Γ₃` is an open map: the quotient of a topological
group by a subgroup is an open quotient map (the quotient map is `QuotientGroup.mk`). -/
theorem thick_isOpenMap_mkX : IsOpenMap (mkX : SL3 → X3) := by
  have h : (mkX : SL3 → X3) = QuotientGroup.mk := rfl
  rw [h]
  exact QuotientGroup.isOpenMap_coe

/-- For an integral vector `m`, the set of group elements `g` for which every coordinate of
`g m` has absolute value `< ρ`.  This is the inverse image under `mkX` of the set of lattices
having `m` as a vector of sup-norm `< ρ`. -/
def shortVecPreimage (m : Fin 3 → ℤ) (ρ : ℝ) : Set SL3 :=
  {g | ∀ i, |Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) (fun j => (m j : ℝ)) i| < ρ}

/-- `shortVecPreimage m ρ` is open: `g ↦ g m` is continuous (matrix–vector product), absolute
value and the comparison `< ρ` preserve openness. -/
theorem isOpen_shortVecPreimage (m : Fin 3 → ℤ) (ρ : ℝ) : IsOpen (shortVecPreimage m ρ) := by
  have hcont : Continuous (fun g : SL3 =>
      Matrix.mulVec ((g : Matrix (Fin 3) (Fin 3) ℝ)) (fun j => (m j : ℝ))) :=
    Continuous.matrix_mulVec continuous_subtype_val continuous_const
  have hset : shortVecPreimage m ρ = ⋂ i : Fin 3,
      {g : SL3 |
        |(Matrix.mulVec ((g : Matrix (Fin 3) (Fin 3) ℝ)) (fun j => (m j : ℝ))) i| < ρ} := by
    ext g; simp [shortVecPreimage]
  rw [hset]
  refine isOpen_iInter_of_finite (fun i => ?_)
  exact isOpen_lt (continuous_abs.comp ((continuous_apply i).comp hcont)) continuous_const

/-- `HasShortVec x ρ` is exactly membership of `x` in the union, over nonzero integral `m`, of
the images `mkX '' shortVecPreimage m ρ`. -/
theorem hasShortVec_iff_mem_iUnion (x : X3) (ρ : ℝ) :
    HasShortVec x ρ ↔
      x ∈ ⋃ m : {m : Fin 3 → ℤ // m ≠ 0}, mkX '' (shortVecPreimage (m : Fin 3 → ℤ) ρ) := by
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨g, hg, m, hm, hshort⟩
    exact ⟨⟨m, hm⟩, g, hshort, hg⟩
  · rintro ⟨⟨m, hm⟩, g, hshort, hg⟩
    exact ⟨g, hg, m, hm, hshort⟩

/-- The complement of `Thick ρ` is open, hence `Thick ρ` is closed. -/
theorem isClosed_Thick (ρ : ℝ) : IsClosed (Work.EKLContract.Thick ρ) := by
  have hopen : IsOpen {x : X3 | HasShortVec x ρ} := by
    have h1 : {x : X3 | HasShortVec x ρ} =
        ⋃ m : {m : Fin 3 → ℤ // m ≠ 0}, mkX '' (shortVecPreimage (m : Fin 3 → ℤ) ρ) := by
      ext x
      exact hasShortVec_iff_mem_iUnion x ρ
    rw [h1]
    refine isOpen_iUnion (fun m => ?_)
    exact thick_isOpenMap_mkX _ (isOpen_shortVecPreimage _ _)
  have hcompl : Thick ρ = {x : X3 | HasShortVec x ρ}ᶜ := by
    ext x; simp [Thick]
  rw [hcompl]
  exact hopen.isClosed_compl

end Work.EKLContract.Lemmas


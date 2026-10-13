import Mathlib
import Submission.Work.DSMX0U.Tower

/-!
# DSMX0U — the model complex `P`, its terms, and the components of `P ⟶ C`

This file builds the `ℤ`-indexed cochain complex

  `towerModel hstep M s₀ = (towerComplex hstep M s₀).extend (embeddingUpIntLE M)`

of `A`-modules: its term in degree `i` is `G_k = (tower k).G` if `i = levelDeg M k - 1` for some
`k : ℕ` (equivalently `i ≤ M`), and `0` otherwise.  Thus the model is bounded above
(`towerModel_isZero_of_gt`); its terms are finitely generated free when the cells' terms are (see
`isBddFinFree_towerModel`).

This file also defines the *components* `towerModelMapF hstep M s₀ i : (towerModel …).X i ⟶ C.X i`
of the map from the model to `C`: on the term of level `k` (in degree `M - k`) it is the map
`(tower k).φ` of the cell, transported along the canonical isomorphisms of the model and of `C`.
The basic property is `towerModelMapF_of_choose`, which describes the component in a degree which
is the degree of a level through an explicit witness of that degree.

The existence of a chain map `towerModel hstep M s₀ ⟶ C` with these components (assuming that the
map of the base cell into `C` lands in the cycles of `C`, `TowerBaseCycle` — which holds for the
base cell produced by `exists_baseCell`) is proved in
`Submission/Work/DSMX0U/exists_towerModelMap.lean`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits
open scoped Classical

universe a

set_option maxHeartbeats 800000

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- The embedding `embeddingUpIntLE M` sends `k` to `M - k`. -/
theorem embeddingUpIntLE_apply (M : ℤ) (k : ℕ) :
    (ComplexShape.embeddingUpIntLE M).f k = M - (k : ℤ) := by
  unfold ComplexShape.embeddingUpIntLE
  rfl

/-- The embedding `embeddingUpIntLE M` places the level `k` of the tower in the degree
`levelDeg M k - 1 = M - k`. -/
theorem levelDeg_embed (M : ℤ) (k : ℕ) :
    (ComplexShape.embeddingUpIntLE M).f k = levelDeg M k - 1 := by
  rw [embeddingUpIntLE_apply, levelDeg_cur]

/-- **The model complex**: the tower extended along `embeddingUpIntLE M`, i.e. with the level `k`
of the tower placed in degree `M - k`, and zero above `M`. -/
noncomputable def towerModel (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : CochainComplex (ModuleCat.{a} A) ℤ :=
  (towerComplex hstep M s₀).extend (ComplexShape.embeddingUpIntLE M)

/-- The canonical isomorphism between the term of the model in degree `levelDeg M k - 1 = M - k`
and the term of level `k` of the tower. -/
noncomputable abbrev towerModelXIso (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (towerModel hstep M s₀).X (levelDeg M k - 1) ≅ (tower hstep M s₀ k).G A :=
  HomologicalComplex.extendXIso (towerComplex hstep M s₀) (ComplexShape.embeddingUpIntLE M)
    (levelDeg_embed M k)

/-- The model vanishes in degrees above `M`. -/
theorem towerModel_isZero_of_gt (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) {i : ℤ} (hi : M < i) : IsZero ((towerModel hstep M s₀).X i) :=
  HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingUpIntLE M) i
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff M i).mpr hi)

/-- The differential of the model in the degrees of two consecutive levels. -/
theorem towerModel_d (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (towerModel hstep M s₀).d (levelDeg M (k + 1) - 1) (levelDeg M k - 1) =
      (towerModelXIso hstep M s₀ (k + 1)).hom ≫ towerD (hstep := hstep) (M := M) (s₀ := s₀) k ≫
        (towerModelXIso hstep M s₀ k).inv := by
  unfold towerModel
  rw [HomologicalComplex.extend_d_eq (towerComplex hstep M s₀) (ComplexShape.embeddingUpIntLE M)
    (levelDeg_embed M (k + 1)) (levelDeg_embed M k)]
  simp only [ChainComplex.of_d]

/-! ## Which level sits in a given degree -/

/-- The level of the tower sitting in degree `i`, when there is one (i.e. when `i ≤ M`); it is
arbitrary (equal to `0`) when there is none. -/
noncomputable def levelOf (M : ℤ) (i : ℤ) : ℕ :=
  if h : ∃ k : ℕ, levelDeg M k - 1 = i then h.choose else 0

theorem levelOf_spec (M : ℤ) (i : ℤ) (h : ∃ k : ℕ, levelDeg M k - 1 = i) :
    levelDeg M (levelOf M i) - 1 = i := by
  rw [levelOf]
  exact dif_pos h ▸ h.choose_spec

theorem levelOf_eq_zero_of_notMem (M : ℤ) (i : ℤ) (h : ¬ ∃ k : ℕ, levelDeg M k - 1 = i) :
    levelOf M i = 0 := by
  rw [levelOf, dif_neg h]

/-- A level is determined by the degree it sits in. -/
theorem levelOf_eq_of (M : ℤ) (k : ℕ) : levelOf M (levelDeg M k - 1) = k := by
  have hspec : levelDeg M (levelOf M (levelDeg M k - 1)) - 1 = levelDeg M k - 1 :=
    levelOf_spec M (levelDeg M k - 1) ⟨k, rfl⟩
  have h1 : levelDeg M (levelOf M (levelDeg M k - 1)) - 1
      = M - (levelOf M (levelDeg M k - 1) : ℤ) := levelDeg_cur M _
  have h2 : levelDeg M k - 1 = M - (k : ℤ) := levelDeg_cur M k
  have h3 : (levelOf M (levelDeg M k - 1) : ℤ) = (k : ℤ) := by omega
  exact_mod_cast h3

/-- Every degree `i ≤ M` is the degree of some level. -/
theorem exists_levelOf_le (M : ℤ) (i : ℤ) (hi : i ≤ M) : ∃ k : ℕ, levelDeg M k - 1 = i := by
  refine ⟨(M - i).toNat, ?_⟩
  rw [levelDeg_eq]
  have h : ((M - i).toNat : ℤ) = M - i := Int.toNat_of_nonneg (by omega)
  omega

/-- A degree which is not the degree of any level is above `M`. -/
theorem gt_of_not_exists_levelOf (M : ℤ) (i : ℤ) (h : ¬ ∃ k : ℕ, levelDeg M k - 1 = i) :
    M < i := by
  by_contra hle
  exact h (exists_levelOf_le M i (not_lt.mp hle))

/-! ## The components of the map `towerModel ⟶ C` -/

/-- The component in degree `i` of the map from the model to `C`: on the term of level `k` it is
`(tower k).φ`, transported so as to land in the degree `i` of `C`; it is `0` in degrees above
`M`. -/
noncomputable def towerModelMapF (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (i : ℤ) : (towerModel hstep M s₀).X i ⟶ C.X i :=
  if hi : ∃ k : ℕ, levelDeg M k - 1 = i then
    (HomologicalComplex.XIsoOfEq (towerModel hstep M s₀) (hi.choose_spec.symm)).hom ≫
      (towerModelXIso hstep M s₀ hi.choose).hom ≫
      (tower hstep M s₀ hi.choose).φ A ≫
      (C.XIsoOfEq (hi.choose_spec)).hom
  else 0

/-- The component of the model map in a degree which is the degree of a level, expressed through
an explicit witness of that degree.  (In degrees which are not the degree of any level — i.e.
above `M` — the component is `0`, see `towerModelMapF_eq_zero_of_gt`.) -/
theorem towerModelMapF_of_choose (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) {i : ℤ} (hi : ∃ m : ℕ, levelDeg M m - 1 = i) :
    towerModelMapF hstep M s₀ i =
      (HomologicalComplex.XIsoOfEq (towerModel hstep M s₀) (hi.choose_spec.symm)).hom ≫
        (towerModelXIso hstep M s₀ hi.choose).hom ≫
        (tower hstep M s₀ hi.choose).φ A ≫
        (C.XIsoOfEq (hi.choose_spec)).hom := by
  unfold towerModelMapF
  rw [dif_pos hi]

/-- The component of the model map in a degree above `M` is zero. -/
theorem towerModelMapF_eq_zero_of_gt (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s)
    (M : ℤ) (s₀ : Cell A C c₀ (M + 1)) {i : ℤ} (hi : M < i) :
    towerModelMapF hstep M s₀ i = 0 := by
  unfold towerModelMapF
  have h : ¬ ∃ k : ℕ, levelDeg M k - 1 = i := by
    rintro ⟨k, hk⟩
    rw [levelDeg_eq] at hk
    omega
  rw [dif_neg h]

/-- **The hypothesis on the base cell** needed for the chain-map condition of the model map: the
map of the base cell into `C` lands in the cycles of `C` in degree `M`.  For the base cell
produced by `exists_baseCell` (where `β = 0` and `σ` lands in the cycles) this is immediate. -/
def TowerBaseCycle (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : Prop :=
  (tower hstep M s₀ 0).φ A ≫ C.d (levelDeg M 0 - 1) (levelDeg M 0) = 0

end Work.DSMX0U

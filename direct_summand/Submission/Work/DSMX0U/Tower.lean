import Mathlib
import Submission.Work.DSMX0U.Cells
import Submission.Work.DSMX0U.cell_d_comm

/-!
# DSMX0U — the tower as a chain complex, and the comparison with `C`

This file packages the tower of cells (`Work.DSMX0U.tower`) as a `ℕ`-indexed chain complex

  `towerComplex hstep M s₀ :  … ⟶ G_{k+1} ⟶ G_k ⟶ … ⟶ G_0`,

whose `k`-th term `G_k = (tower k).G` sits in cohomological degree `levelDeg M k - 1 = M - k`,
together with the `ℕ`-indexed chain complex

  `levelComplex C M : … ⟶ C^{M-k-1} ⟶ C^{M-k} ⟶ …`

whose `k`-th term is `C^{M-k}` (in the same degree), and the chain map
`towerMap hstep M s₀ : towerComplex ⟶ levelComplex` whose `k`-th component is the map
`(tower k).φ : G_k ⟶ C^{M-k}` into `C`.

The point of working in the `ℕ`-indexed world is that *everything here is definitional*:
the `k`-th term of `levelComplex` is literally `C.X (levelDeg M k - 1)`, which is the target of
`(tower k).φ`, and the chain-map condition is literally `Cell.d_comm` at level `k+1`
(`tower_φprev` turns `(tower (k+1)).φprev` into `(tower k).φ`).  The transport to the `ℤ`-indexed
model complex `P = towerComplex.extend (embeddingUpIntLE M)` is done in
`Submission/Work/DSMX0U/Model.lean`.

The quasi-isomorphism `QuasiIso (towerMap hstep M s₀)` is the core homological computation
(`Submission/Work/DSMX0U/towerQuasiIso.lean`): it compares the homology of the tower at level `k`
with `H^{M-k}(C)`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 800000

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
variable {q : ℤ}

/-! ## The range of the differential of a cell -/

/-- The range of the differential of a cell is exactly the excess kernel of the next level up:
the differential kills the generators and covers `Kprev` through the surjection `cov`. -/
theorem Cell.range_dHom (s : Cell A C c₀ q) : LinearMap.range (s.dHom A) = s.Kprev := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨p, rfl⟩
    simp [Cell.dHom, LinearMap.coprod_apply]
  · intro y hy
    obtain ⟨r, hr⟩ := s.hcov ⟨y, hy⟩
    refine ⟨(0, r), ?_⟩
    have h : s.dHom A ((0 : ↥s.gen), r) = ((s.cov r : ↥s.Kprev) : ↥s.Gprev) := by
      simp [Cell.dHom, LinearMap.coprod_apply]
    rw [h, hr]

/-- The excess kernel of a cell is contained in the kernel of its differential. -/
theorem Cell.K_le_ker (s : Cell A C c₀ q) : s.K A ≤ LinearMap.ker (s.dHom A) :=
  inf_le_left

/-! ## The tower differentials compose to zero -/

theorem towerD_comp (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (towerD (hstep := hstep) (M := M) (s₀ := s₀) (k + 1))
        (towerD (hstep := hstep) (M := M) (s₀ := s₀) k) = 0 := by
  rw [show CategoryTheory.CategoryStruct.comp
        (towerD (hstep := hstep) (M := M) (s₀ := s₀) (k + 1))
        (towerD (hstep := hstep) (M := M) (s₀ := s₀) k) =
      ModuleCat.ofHom (((tower hstep M s₀ (k + 1)).dHom A) ∘ₗ
        ((tower hstep M s₀ (k + 2)).dHom A)) from rfl]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  have hmem : (towerD (hstep := hstep) (M := M) (s₀ := s₀) (k + 1)) x ∈
      (tower hstep M s₀ (k + 1)).K A := by
    rw [← tower_Kprev (hstep := hstep) (M := M) (s₀ := s₀) (k + 1),
      ← Cell.range_dHom (s := tower hstep M s₀ (k + 2))]
    exact ⟨x, rfl⟩
  exact Cell.K_le_ker (s := tower hstep M s₀ (k + 1)) hmem

/-! ## The `ℕ`-indexed complexes -/

/-- **The tower as a chain complex**: the `k`-th term is `G_k = (tower k).G` and the `k`-th
differential is the differential of level `k+1` into level `k`. -/
@[reducible]
noncomputable def towerComplex (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : ChainComplex (ModuleCat.{a} A) ℕ :=
  ChainComplex.of (fun k => (tower hstep M s₀ k).G A)
    (fun k => towerD (hstep := hstep) (M := M) (s₀ := s₀) k)
    (fun k => towerD_comp hstep M s₀ k)

/-- **The piece of `C` at the levels of the tower**: the `k`-th term is `C.X (levelDeg M k - 1)`,
i.e. `C^{M-k}`, with the differentials of `C`. -/
@[reducible]
noncomputable def levelComplex (C : CochainComplex (ModuleCat.{a} A) ℤ) (M : ℤ) :
    ChainComplex (ModuleCat.{a} A) ℕ :=
  ChainComplex.of (fun k => C.X (levelDeg M k - 1))
    (fun k => C.d (levelDeg M (k + 1) - 1) (levelDeg M k - 1))
    (fun _ => HomologicalComplex.d_comp_d C _ _ _)

@[simp]
theorem towerComplex_X (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (towerComplex hstep M s₀).X k = (tower hstep M s₀ k).G A := rfl

@[simp]
theorem levelComplex_X (C : CochainComplex (ModuleCat.{a} A) ℤ) (M : ℤ) (k : ℕ) :
    (levelComplex C M).X k = C.X (levelDeg M k - 1) := rfl

@[simp]
theorem towerComplex_d (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (towerComplex hstep M s₀).d (k + 1) k = towerD (hstep := hstep) (M := M) (s₀ := s₀) k := by
  unfold towerComplex
  exact ChainComplex.of_d (fun k => (tower hstep M s₀ k).G A)
    (fun k => towerD (hstep := hstep) (M := M) (s₀ := s₀) k) k

@[simp]
theorem levelComplex_d (C : CochainComplex (ModuleCat.{a} A) ℤ) (M : ℤ) (k : ℕ) :
    (levelComplex C M).d (k + 1) k =
      C.d (levelDeg M (k + 1) - 1) (levelDeg M k - 1) := by
  unfold levelComplex
  exact ChainComplex.of_d (fun k => C.X (levelDeg M k - 1))
    (fun k => C.d (levelDeg M (k + 1) - 1) (levelDeg M k - 1)) k

/-! ## The chain map `towerComplex ⟶ levelComplex` -/

/-- **The map from the tower to `C`**, whose `k`-th component is the map `(tower k).φ` from the
term of level `k` to `C^{M-k}`.  It is a chain map by `Cell.d_comm` (at level `k+1`). -/
@[reducible]
noncomputable def towerMap (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) : towerComplex hstep M s₀ ⟶ levelComplex C M where
  f k := (tower hstep M s₀ k).φ A
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    rw [← hij]
    simp only [ChainComplex.of_d]
    exact (cell_d_comm (s := tower hstep M s₀ (j + 1))).symm

@[simp]
theorem towerMap_f (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (towerMap hstep M s₀).f k = (tower hstep M s₀ k).φ A := rfl

end Work.DSMX0U

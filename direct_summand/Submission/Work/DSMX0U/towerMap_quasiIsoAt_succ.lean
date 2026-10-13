import Mathlib
import Submission.Work.DSMX0U.Tower
import Submission.Work.DSMX0U.cell_K_eq
import Submission.Work.DSMX0U.tower_range_d

/-!
# `Work.DSMX0U.towerMap_quasiIsoAt_succ`

The comparison map `towerMap hstep M s₀ : towerComplex hstep M s₀ ⟶ levelComplex C M`
(`Submission/Work/DSMX0U/Tower.lean`) sends the level `k` of the cell tower, which sits in
cohomological degree `M - k`, to `C^{M-k}` by the map `(tower k).φ` of the cell.  This file
proves that it is a quasi-isomorphism in every degree `k + 1` of the `ℕ`-indexed complexes.

Concretely, in degree `k + 1` the relevant short complexes are

  `G_{k+2} --(towerD (k+1))--> G_{k+1} --(towerD k)--> G_k`

for the tower and

  `C^{M-k-2} --(C.d)--> C^{M-k-1} --(C.d)--> C^{M-k}`

for the levels of `C`; the map of short complexes is `ψ` with components
`(tower (k+2)).φ`, `(tower (k+1)).φ`, `(tower k).φ`.  Its left homology data is computed
concretely (`moduleCatLeftHomologyData`): the cycles of the tower in degree `k+1` are the pairs
`(x, y)` with `cov y = 0`, the boundaries are `Cell.K (tower (k+1))`, and on the `C`-side the
cycles are the cycles of `C` in degree `M - k - 1` modulo boundaries.

The induced map on homology `H_{k+1}(towerComplex) ⟶ H^{M-k-1}(C)` is
`(x, y) ↦ [iCycles (σ x) + β y]`; it is surjective by `Cell.hσ` of level `k + 1` (the generators
hit all classes modulo boundaries) and injective by `hcov` of level `k + 1` (the relations cover
exactly `Cell.K`), using `tower_range_d`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

namespace TowerMapQI

/-! ## The two degrees of the short complex

In degree `k + 1` of the (cohomological) complexes we are looking at the terms

  `X_{k+2} = C^{M-k-2}`, `X_{k+1} = C^{M-k-1}`, `X_k = C^{M-k}`,

so the lower degree is `M - k - 2 = levelDeg M (k+2) - 1` and the middle degree is
`M - k - 1 = levelDeg M (k+1) - 1`.  We write them as `bot M k` and `mid M k`, using
`levelDeg M (k+1)` (rather than `levelDeg M k - 1`) so that all the degree expressions of the
cells of level `k+1` and `k+2` unfold definitionally to them. -/

/-- The degree `M - k - 1` of the middle term. -/
abbrev mid (M : ℤ) (k : ℕ) : ℤ := levelDeg M (k + 1) - 1

/-- The degree `M - k - 2` of the lower term. -/
abbrev bot (M : ℤ) (k : ℕ) : ℤ := levelDeg M (k + 1) - 1 - 1

/-! ## The two short complexes and the map between them -/

/-- The short complex of the tower in degree `k + 1`. -/
noncomputable abbrev scT (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) : ShortComplex (ModuleCat.{a} A) :=
  ShortComplex.mk (towerD (hstep := hstep) (M := M) (s₀ := s₀) (k + 1))
    (towerD (hstep := hstep) (M := M) (s₀ := s₀) k) (towerD_comp hstep M s₀ k)

/-- The short complex of the levels of `C` in degree `k + 1`. -/
noncomputable abbrev scC (M : ℤ) (k : ℕ) : ShortComplex (ModuleCat.{a} A) :=
  ShortComplex.mk (C.d (bot M k) (mid M k)) (C.d (mid M k) (levelDeg M (k + 1)))
    (HomologicalComplex.d_comp_d C _ _ _)

/-- The concrete left homology data of the tower's short complex. -/
noncomputable abbrev hT (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (scT (C := C) (c₀ := c₀) hstep M s₀ k).LeftHomologyData :=
  (scT (C := C) (c₀ := c₀) hstep M s₀ k).moduleCatLeftHomologyData

/-- The concrete left homology data of the short complex of `C`. -/
noncomputable abbrev hC (M : ℤ) (k : ℕ) : (scC (C := C) M k).LeftHomologyData :=
  (scC (C := C) M k).moduleCatLeftHomologyData

/-- **The map of short complexes in degree `k + 1`**: the three components of the tower map
`(tower (k+2)).φ`, `(tower (k+1)).φ`, `(tower k).φ`.  The two squares are `Cell.d_comm` at
level `k+2` and at level `k+1`. -/
noncomputable def psi (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    scT (C := C) (c₀ := c₀) hstep M s₀ k ⟶ scC (C := C) M k where
  τ₁ := (tower hstep M s₀ (k + 2)).φ A
  τ₂ := (tower hstep M s₀ (k + 1)).φ A
  τ₃ := (tower hstep M s₀ k).φ A
  comm₁₂ := (cell_d_comm (tower hstep M s₀ (k + 2))).symm
  comm₂₃ := (cell_d_comm (tower hstep M s₀ (k + 1))).symm

/-! ## Elementary computations with the concrete left homology data -/

/-- An element of `LinearMap.ker S.g` is in the range of `moduleCatToCycles` iff its underlying
element is in the range of `S.f`. -/
theorem mem_range_moduleCatToCycles_iff (S : ShortComplex (ModuleCat.{a} A))
    (y : ↥S.moduleCatLeftHomologyData.K) :
    y ∈ LinearMap.range S.moduleCatToCycles ↔ y.1 ∈ LinearMap.range S.f.hom := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- The projection `π` of the concrete left homology data is the quotient map. -/
theorem pi_eq_mk (S : ShortComplex (ModuleCat.{a} A))
    (y : ↥S.moduleCatLeftHomologyData.K) :
    S.moduleCatLeftHomologyData.π y = Submodule.Quotient.mk y :=
  calc S.moduleCatLeftHomologyData.π y
      = (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.π) y := rfl
    _ = S.moduleCatToCycles.range.mkQ y :=
        congrFun (congrArg DFunLike.coe (ShortComplex.moduleCatLeftHomologyData_π_hom S)) y
    _ = Submodule.Quotient.mk y := Submodule.mkQ_apply _ _

/-- The inclusion `i` of the concrete left homology data is the inclusion of the cycles. -/
theorem i_eq_subtype (S : ShortComplex (ModuleCat.{a} A))
    (y : ↥S.moduleCatLeftHomologyData.K) :
    (S.moduleCatLeftHomologyData.i y : ↥S.X₂) = y.1 :=
  calc (S.moduleCatLeftHomologyData.i y : ↥S.X₂)
      = (ModuleCat.Hom.hom S.moduleCatLeftHomologyData.i) y := rfl
    _ = (LinearMap.ker S.g.hom).subtype y :=
        congrFun (congrArg DFunLike.coe (ShortComplex.moduleCatLeftHomologyData_i_hom S)) y
    _ = y.1 := rfl

/-- The second component of `ψ` is `(tower (k+1)).φ`; on elements it is `φHom`. -/
theorem psi_τ₂_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) (u : ↥(scT (C := C) (c₀ := c₀) hstep M s₀ k).X₂) :
    (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂ u =
      (tower hstep M s₀ (k + 1)).φHom A u := rfl

/-- The second differential of `scT` is the differential of the cell of level `k+1`. -/
theorem scT_g_hom (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (scT (C := C) (c₀ := c₀) hstep M s₀ k).g.hom =
      (tower hstep M s₀ (k + 1)).dHom A := rfl

/-- The first differential of `scT` is the differential of the cell of level `k+2`. -/
theorem scT_f_hom (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (scT (C := C) (c₀ := c₀) hstep M s₀ k).f.hom =
      (tower hstep M s₀ (k + 2)).dHom A := rfl

/-- The differential of a cell kills the generators. -/
theorem cell_dHom_pair_zero {q : ℤ} (s : Cell A C c₀ q) (x : ↥s.gen) :
    s.dHom A ((x, 0) : ↥s.gen × ↥s.rel) = 0 := by
  simp only [Cell.dHom, LinearMap.coprod_apply, map_zero, LinearMap.zero_apply, add_zero]

/-- The map of a cell sends a generator to the corresponding cycle. -/
theorem cell_φHom_pair_zero {q : ℤ} (s : Cell A C c₀ q) (x : ↥s.gen) :
    s.φHom A ((x, 0) : ↥s.gen × ↥s.rel) = (C.iCycles (q - 1)).hom (s.σ.hom x) := by
  simp only [Cell.φHom, LinearMap.coprod_apply, LinearMap.comp_apply, map_zero, add_zero]

/-! ## The induced maps on cycles and on homology -/

/-- The map on cycles induced by `ψ`, obtained by restricting `(tower (k+1)).φ` to the cycles. -/
noncomputable def phiK (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (hT (C := C) (c₀ := c₀) hstep M s₀ k).K ⟶ (hC (C := C) M k).K :=
  (hC (C := C) M k).liftK
    ((hT (C := C) (c₀ := c₀) hstep M s₀ k).i ≫ (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂)
    (by
      rw [Category.assoc, (psi (C := C) (c₀ := c₀) hstep M s₀ k).comm₂₃, ← Category.assoc,
        (hT (C := C) (c₀ := c₀) hstep M s₀ k).wi, zero_comp])

theorem phiK_commi (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    phiK (C := C) (c₀ := c₀) hstep M s₀ k ≫ (hC (C := C) M k).i =
      (hT (C := C) (c₀ := c₀) hstep M s₀ k).i ≫
        (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂ :=
  (hC (C := C) M k).liftK_i _ _

/-- The value of `phiK` on an element: it is `(tower (k+1)).φ` applied to the underlying
element. -/
theorem phiK_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ)
    (x : ↥(hT (C := C) (c₀ := c₀) hstep M s₀ k).K) :
    (phiK (C := C) (c₀ := c₀) hstep M s₀ k x).1 =
      (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂ x.1 := by
  have h1 : ((hC (C := C) M k).i (phiK (C := C) (c₀ := c₀) hstep M s₀ k x) :
      ↥(scC (C := C) M k).X₂) =
      (phiK (C := C) (c₀ := c₀) hstep M s₀ k x).1 := i_eq_subtype _ _
  have h3 : (hC (C := C) M k).i (phiK (C := C) (c₀ := c₀) hstep M s₀ k x) =
      (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂
        ((hT (C := C) (c₀ := c₀) hstep M s₀ k).i x) := by
    have h := congrArg
      (fun (g : (hT (C := C) (c₀ := c₀) hstep M s₀ k).K ⟶ (scC (C := C) M k).X₂) => g x)
      (phiK_commi (C := C) (c₀ := c₀) hstep M s₀ k)
    rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  have h4 : ((hT (C := C) (c₀ := c₀) hstep M s₀ k).i x : ↥(scT (C := C) (c₀ := c₀) hstep M s₀ k).X₂) =
      x.1 := i_eq_subtype _ _
  rw [← h1, h3, h4]

/-- The difference formula for `phiK`. -/
theorem phiK_sub_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ)
    (x y : ↥(hT (C := C) (c₀ := c₀) hstep M s₀ k).K) :
    (phiK (C := C) (c₀ := c₀) hstep M s₀ k x -
        phiK (C := C) (c₀ := c₀) hstep M s₀ k y).1 =
      (tower hstep M s₀ (k + 1)).φHom A (x.1 - y.1) := by
  rw [Submodule.coe_sub, phiK_apply, phiK_apply, psi_τ₂_apply, psi_τ₂_apply]
  rw [← map_sub]

theorem phiK_commf' (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (hT (C := C) (c₀ := c₀) hstep M s₀ k).f' ≫ phiK (C := C) (c₀ := c₀) hstep M s₀ k =
      (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₁ ≫ (hC (C := C) M k).f' := by
  refine (cancel_mono (hC (C := C) M k).i).mp ?_
  calc (((hT (C := C) (c₀ := c₀) hstep M s₀ k).f' ≫
          phiK (C := C) (c₀ := c₀) hstep M s₀ k) ≫ (hC (C := C) M k).i)
      = (hT (C := C) (c₀ := c₀) hstep M s₀ k).f' ≫
          (phiK (C := C) (c₀ := c₀) hstep M s₀ k ≫ (hC (C := C) M k).i) :=
        Category.assoc _ _ _
    _ = (hT (C := C) (c₀ := c₀) hstep M s₀ k).f' ≫
          ((hT (C := C) (c₀ := c₀) hstep M s₀ k).i ≫
            (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂) := by
        rw [phiK_commi]
    _ = ((hT (C := C) (c₀ := c₀) hstep M s₀ k).f' ≫
          (hT (C := C) (c₀ := c₀) hstep M s₀ k).i) ≫
            (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂ := (Category.assoc _ _ _).symm
    _ = (scT (C := C) (c₀ := c₀) hstep M s₀ k).f ≫
          (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₂ := by
        rw [(hT (C := C) (c₀ := c₀) hstep M s₀ k).f'_i]
    _ = (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₁ ≫
          (scC (C := C) M k).f :=
        ((psi (C := C) (c₀ := c₀) hstep M s₀ k).comm₁₂).symm
    _ = (psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₁ ≫
          ((hC (C := C) M k).f' ≫ (hC (C := C) M k).i) := by
        rw [(hC (C := C) M k).f'_i]
    _ = ((psi (C := C) (c₀ := c₀) hstep M s₀ k).τ₁ ≫ (hC (C := C) M k).f') ≫
          (hC (C := C) M k).i := (Category.assoc _ _ _).symm

/-- The map on homology induced by `ψ`. -/
noncomputable def phiH (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (hT (C := C) (c₀ := c₀) hstep M s₀ k).H ⟶ (hC (C := C) M k).H :=
  (hT (C := C) (c₀ := c₀) hstep M s₀ k).descH
    (phiK (C := C) (c₀ := c₀) hstep M s₀ k ≫ (hC (C := C) M k).π)
    (by
      rw [← Category.assoc, phiK_commf' (C := C) (c₀ := c₀) hstep M s₀ k, Category.assoc,
        (hC (C := C) M k).f'_π, comp_zero])

/-- The defining property of `phiH`. -/
theorem pi_phiH (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (hT (C := C) (c₀ := c₀) hstep M s₀ k).π ≫ phiH (C := C) (c₀ := c₀) hstep M s₀ k =
      phiK (C := C) (c₀ := c₀) hstep M s₀ k ≫ (hC (C := C) M k).π :=
  (hT (C := C) (c₀ := c₀) hstep M s₀ k).π_descH _ _

/-- The left homology map data of `ψ`. -/
noncomputable def gammaH (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    ShortComplex.LeftHomologyMapData (psi (C := C) (c₀ := c₀) hstep M s₀ k)
      (hT (C := C) (c₀ := c₀) hstep M s₀ k) (hC (C := C) M k) where
  φK := phiK (C := C) (c₀ := c₀) hstep M s₀ k
  φH := phiH (C := C) (c₀ := c₀) hstep M s₀ k
  commi := phiK_commi (C := C) (c₀ := c₀) hstep M s₀ k
  commf' := phiK_commf' (C := C) (c₀ := c₀) hstep M s₀ k
  commπ := pi_phiH (C := C) (c₀ := c₀) hstep M s₀ k

/-- The value of `phiH` on the class of a cycle: it is the class of `phiK`. -/
theorem phiH_pi_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) (x : ↥(hT (C := C) (c₀ := c₀) hstep M s₀ k).K) :
    (phiH (C := C) (c₀ := c₀) hstep M s₀ k)
        ((hT (C := C) (c₀ := c₀) hstep M s₀ k).π x) =
      (hC (C := C) M k).π (phiK (C := C) (c₀ := c₀) hstep M s₀ k x) := by
  have h := congrArg
    (fun (g : (hT (C := C) (c₀ := c₀) hstep M s₀ k).K ⟶ (hC (C := C) M k).H) => g x)
    (pi_phiH (C := C) (c₀ := c₀) hstep M s₀ k)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply] at h

/-- The value of `phiH` on the class of a cycle, with the quotient written explicitly. -/
theorem phiH_mk_apply (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) (x : ↥(hT (C := C) (c₀ := c₀) hstep M s₀ k).K) :
    (phiH (C := C) (c₀ := c₀) hstep M s₀ k) (Submodule.Quotient.mk x) =
      (hC (C := C) M k).π (phiK (C := C) (c₀ := c₀) hstep M s₀ k x) :=
  calc (phiH (C := C) (c₀ := c₀) hstep M s₀ k) (Submodule.Quotient.mk x)
      = (phiH (C := C) (c₀ := c₀) hstep M s₀ k)
          ((hT (C := C) (c₀ := c₀) hstep M s₀ k).π x) := by
        rw [pi_eq_mk (scT (C := C) (c₀ := c₀) hstep M s₀ k) x]
    _ = (hC (C := C) M k).π (phiK (C := C) (c₀ := c₀) hstep M s₀ k x) :=
        phiH_pi_apply (C := C) (c₀ := c₀) hstep M s₀ k x

/-! ## The induced map on homology is an isomorphism -/

/-- `phiH` is surjective: every class of `H^{M-k-1}(C)` is represented by a cycle, and `hσ` of
level `k+1` produces a generator whose image is that cycle up to a boundary. -/
theorem phiH_surjective (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    Function.Surjective (phiH (C := C) (c₀ := c₀) hstep M s₀ k).hom := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (scC (C := C) M k).moduleCatToCycles) q
  have hz : (C.d (mid M k) (levelDeg M (k + 1))).hom z.1 = 0 := LinearMap.mem_ker.mp z.2
  obtain ⟨g, hg⟩ := (tower hstep M s₀ (k + 1)).hσ z.1 hz
  let w : ↥(tower hstep M s₀ (k + 1)).gen × ↥(tower hstep M s₀ (k + 1)).rel := (g, 0)
  have hw : w ∈ LinearMap.ker (scT (C := C) (c₀ := c₀) hstep M s₀ k).g.hom := by
    rw [scT_g_hom]
    exact LinearMap.mem_ker.mpr (cell_dHom_pair_zero (A := A) (s := tower hstep M s₀ (k + 1)) g)
  refine ⟨(hT (C := C) (c₀ := c₀) hstep M s₀ k).π ⟨w, hw⟩, ?_⟩
  have hphi : (phiK (C := C) (c₀ := c₀) hstep M s₀ k ⟨w, hw⟩).1 =
      (C.iCycles (mid M k)).hom ((tower hstep M s₀ (k + 1)).σ.hom g) := by
    rw [phiK_apply, psi_τ₂_apply]
    exact cell_φHom_pair_zero (A := A) (s := tower hstep M s₀ (k + 1)) g
  rw [phiH_pi_apply, pi_eq_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  refine (mem_range_moduleCatToCycles_iff (scC (C := C) M k) _).mpr ?_
  rw [Submodule.coe_sub, hphi]
  exact hg

/-- `phiH` is injective: if the image of a cycle of the tower is a boundary of `C`, then the cycle
lies in the excess kernel `Cell.K`, which is the image of the differential of the next cell
(`tower_range_d`). -/
theorem phiH_injective (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    Function.Injective (phiH (C := C) (c₀ := c₀) hstep M s₀ k).hom := by
  intro a b hab
  obtain ⟨k₁, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (scT (C := C) (c₀ := c₀) hstep M s₀ k).moduleCatToCycles) a
  obtain ⟨k₂, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (scT (C := C) (c₀ := c₀) hstep M s₀ k).moduleCatToCycles) b
  rw [phiH_mk_apply, phiH_mk_apply] at hab
  have hmem : (phiK (C := C) (c₀ := c₀) hstep M s₀ k k₁ -
      phiK (C := C) (c₀ := c₀) hstep M s₀ k k₂) ∈
      LinearMap.range (scC (C := C) M k).moduleCatToCycles := by
    have h := hab
    rw [pi_eq_mk, pi_eq_mk] at h
    exact (Submodule.Quotient.eq _).mp h
  have h1 : (phiK (C := C) (c₀ := c₀) hstep M s₀ k k₁ -
      phiK (C := C) (c₀ := c₀) hstep M s₀ k k₂).1 ∈
      LinearMap.range (C.d (bot M k) (mid M k)).hom :=
    (mem_range_moduleCatToCycles_iff (scC (C := C) M k) _).mp hmem
  have hval : (phiK (C := C) (c₀ := c₀) hstep M s₀ k k₁ -
      phiK (C := C) (c₀ := c₀) hstep M s₀ k k₂).1 =
      (tower hstep M s₀ (k + 1)).φHom A (k₁.1 - k₂.1) :=
    phiK_sub_apply (C := C) (c₀ := c₀) hstep M s₀ k k₁ k₂
  have hK : (k₁ - k₂).1 ∈ (tower hstep M s₀ (k + 1)).K A := by
    rw [cell_K_eq (tower hstep M s₀ (k + 1))]
    refine ⟨?_, ?_⟩
    · have h2 : (scT (C := C) (c₀ := c₀) hstep M s₀ k).g.hom (k₁ - k₂).1 = 0 :=
        LinearMap.mem_ker.mp (k₁ - k₂).2
      exact h2
    · rw [hval] at h1
      exact h1
  have h3 : (k₁ - k₂).1 ∈ LinearMap.range (scT (C := C) (c₀ := c₀) hstep M s₀ k).f.hom := by
    have h := hK
    rw [← tower_range_d hstep M s₀ (k + 1)] at h
    rw [scT_f_hom]
    exact h
  refine (Submodule.Quotient.eq _).mpr ?_
  exact (mem_range_moduleCatToCycles_iff (scT (C := C) (c₀ := c₀) hstep M s₀ k) _).mpr h3

theorem isIso_phiH (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    IsIso (phiH (C := C) (c₀ := c₀) hstep M s₀ k) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨phiH_injective (C := C) (c₀ := c₀) hstep M s₀ k,
    phiH_surjective (C := C) (c₀ := c₀) hstep M s₀ k⟩

/-- **`ψ` is a quasi-isomorphism of short complexes.** -/
theorem quasiIso_psi (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    ShortComplex.QuasiIso (psi (C := C) (c₀ := c₀) hstep M s₀ k) :=
  (ShortComplex.LeftHomologyMapData.quasiIso_iff
    (gammaH (C := C) (c₀ := c₀) hstep M s₀ k)).mpr
    (isIso_phiH (C := C) (c₀ := c₀) hstep M s₀ k)

/-! ## Comparison with the short complexes of the two complexes -/

/-- The short complex `scT` is isomorphic to the degree `k+1` short complex of `towerComplex`. -/
noncomputable def eT (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.down ℕ)
        (k + 2) (k + 1) k).obj (towerComplex hstep M s₀) ≅
      scT (C := C) (c₀ := c₀) hstep M s₀ k :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (towerComplex_d hstep M s₀ (k + 1)).symm (towerComplex_d hstep M s₀ k).symm

/-- The short complex `scC` is isomorphic to the degree `k+1` short complex of `levelComplex`. -/
noncomputable def eC (M : ℤ) (k : ℕ) :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.down ℕ)
        (k + 2) (k + 1) k).obj (levelComplex C M) ≅ scC (C := C) M k :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (levelComplex_d C M (k + 1)).symm (levelComplex_d C M k).symm

/-- The square relating the tower map to `ψ`. -/
theorem sq (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) :
    (eT (C := C) (c₀ := c₀) hstep M s₀ k).hom ≫
        psi (C := C) (c₀ := c₀) hstep M s₀ k =
      (HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.down ℕ)
          (k + 2) (k + 1) k).map (towerMap hstep M s₀) ≫
        (eC (C := C) M k).hom := by
  apply ShortComplex.hom_ext
  · simp only [ShortComplex.comp_τ₁]
    show (𝟙 _) ≫ (tower hstep M s₀ (k + 2)).φ A =
      (tower hstep M s₀ (k + 2)).φ A ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]
  · simp only [ShortComplex.comp_τ₂]
    show (𝟙 _) ≫ (tower hstep M s₀ (k + 1)).φ A =
      (tower hstep M s₀ (k + 1)).φ A ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]
  · simp only [ShortComplex.comp_τ₃]
    show (𝟙 _) ≫ (tower hstep M s₀ k).φ A = (tower hstep M s₀ k).φ A ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]

end TowerMapQI

theorem towerMap_quasiIsoAt_succ {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1)) (k : ℕ) :
    QuasiIsoAt (Work.DSMX0U.towerMap hstep M s₀) (k + 1) := by
  have hprev : (ComplexShape.down ℕ).prev (k + 1) = k + 2 :=
    ComplexShape.prev_eq' (ComplexShape.down ℕ) (ComplexShape.down_mk (k + 2) (k + 1) (by ring))
  have hnext : (ComplexShape.down ℕ).next (k + 1) = k :=
    ComplexShape.next_eq' (ComplexShape.down ℕ) (ComplexShape.down_mk (k + 1) k (by ring))
  rw [quasiIsoAt_iff' (f := towerMap hstep M s₀) (i := k + 2) (j := k + 1) (k := k) hprev hnext]
  exact ShortComplex.quasiIso_of_arrow_mk_iso (TowerMapQI.psi (C := C) (c₀ := c₀) hstep M s₀ k)
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{a} A) (ComplexShape.down ℕ)
        (k + 2) (k + 1) k).map (towerMap hstep M s₀))
    (Arrow.isoMk (TowerMapQI.eT (C := C) (c₀ := c₀) hstep M s₀ k)
      (TowerMapQI.eC (C := C) M k) (TowerMapQI.sq (C := C) (c₀ := c₀) hstep M s₀ k)).symm
    (hφ := TowerMapQI.quasiIso_psi (C := C) (c₀ := c₀) hstep M s₀ k)

end Work.DSMX0U

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (the abstract two-term Laurent operator of the Følner/Lück argument)

# The abstract two-term block-Laurent operator

This module sets up the abstract operator theory of the Følner--Lück approximation step for
[JZLA20, Proposition 3.11] in the group-theoretic model of `Work.ORVonNeumann.Rep`:

for a countable group `G`, a normal subgroup `N ⊴ G` and `t : G` with
`Work.ORP311.IsExtensionByZ G N t` (`H = N ⋊ ⟨t⟩`), and operators `D C` on
`HSum m = ⊕_{i<m} ℓ²(G)` which are **block diagonal over the `N`-cosets** (each preserves the
closed span `ell2Sub m (coset N t j)`), we consider

  `B = D + C · λ(t)`

where `λ(t)` is the blockwise **left** regular operator (`regBlk m t`, the operator which shifts
the coset index `j ↦ j + 1` with a twist).

The two facts about `B` used by the Følner argument are

* `supp (B ξ) ⊆ supp ξ ∪ t · supp ξ`, i.e. `B` maps `ell2Sub m Z` into
  `ell2Sub m (Z ∪ t · Z)` (`regBlk_ell2Sub`), because `D` and `C` are block diagonal and
  `λ(t)` shifts the cosets by one;
* the Toeplitz truncation `P_X B P_X` of `B` to a window `X = ⊔_{|j| ≤ M} N t^j` is
  **injective** when `D` is injective, by the lowest-coefficient induction of
  `Work.ORP311.truncOp_injective_of_ne_zero`.

## Main definitions

* `Work.ORP311.regBlk m g` — the blockwise left regular operator on `HSum m`;
* `Work.ORP311.cosetShift t Z` — the shifted set `t · Z = {t * z | z ∈ Z}`.
-/
import Mathlib
import Submission.Work.ORP311.ell2Sub_mono
import Submission.Work.ORP311.ell2Sub_inf
import Submission.Work.ORP311.FolnerWindow
import Submission.Work.ORVonNeumann.Rep.exists_leftRegular

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The blockwise **left** regular action by `g` on `HSum m = ⊕_{i<m} ℓ²(G)`: the direct sum of
`λ(g)` over the `m` summands, in the same shape as `Rep.diagOp`. -/
noncomputable def regBlk (m : ℕ) (g : G) :
    Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m :=
  ∑ i : Fin m, (Rep.hinclude (G := G) m i).comp
    ((Rep.leftRegOp g).comp (Rep.hcoord (G := G) m i))

/-- The explicit sum formula for `regBlk`. -/
theorem regBlk_apply_sum (m : ℕ) (g : G) (x : Rep.HSum (G := G) m) :
    regBlk (G := G) m g x
      = ∑ i : Fin m,
          Rep.hinclude (G := G) m i (Rep.leftRegOp g (Rep.hcoord (G := G) m i x)) := by
  rw [regBlk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]

/-- `regBlk m g` acts coordinatewise by `λ(g)`. -/
theorem hcoord_regBlk (m : ℕ) (g : G) (i : Fin m) :
    (Rep.hcoord (G := G) m i).comp (regBlk (G := G) m g)
      = (Rep.leftRegOp g).comp (Rep.hcoord (G := G) m i) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, regBlk_apply_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · simp [Rep.hcoord_hinclude]
  · intro j _ hj
    simp [Rep.hcoord_hinclude, Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The coordinate formula for `regBlk`. -/
theorem regBlk_apply (m : ℕ) (g : G) (x : Rep.HSum (G := G) m) (i : Fin m) :
    (regBlk (G := G) m g x).ofLp i = Rep.leftRegOp g (x.ofLp i) := by
  have h := congrArg
    (fun f : Rep.HSum (G := G) m →L[ℂ] Work.ORVonNeumann.l2 G => f x)
    (hcoord_regBlk (G := G) m g i)
  simpa only [ContinuousLinearMap.comp_apply, Rep.hcoord_apply] using h

/-- `regBlk` sends a coordinate inclusion into a coordinate inclusion. -/
theorem regBlk_hinclude (m : ℕ) (t : G) (i : Fin m) (x : Work.ORVonNeumann.l2 G) :
    regBlk (G := G) m t (Rep.hinclude (G := G) m i x)
      = Rep.hinclude (G := G) m i (Rep.leftRegOp t x) := by
  apply Rep.hsum_ext
  intro j
  rw [show Rep.hcoord (G := G) m j (regBlk (G := G) m t (Rep.hinclude (G := G) m i x))
      = Rep.leftRegOp t (Rep.hcoord (G := G) m j (Rep.hinclude (G := G) m i x)) from
        congrArg (fun f => f (Rep.hinclude (G := G) m i x)) (hcoord_regBlk (G := G) m t j)]
  rw [Rep.hcoord_hinclude, Rep.hcoord_hinclude]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- `regBlk` sends a `δ`-generator into a `δ`-generator. -/
theorem regBlk_hdelta (m : ℕ) (t : G) (i : Fin m) (z : G) :
    regBlk (G := G) m t (Rep.hinclude (G := G) m i (Rep.deltaG z))
      = Rep.hinclude (G := G) m i (Rep.deltaG (t * z)) := by
  rw [regBlk_hinclude, Rep.leftRegOp_deltaG]

/-- The shifted set `t · Z = {t * z | z ∈ Z}`. -/
def cosetShift (t : G) (Z : Set G) : Set G := {x | ∃ z ∈ Z, x = t * z}

theorem mem_cosetShift {t : G} {Z : Set G} {x : G} :
    x ∈ cosetShift t Z ↔ ∃ z ∈ Z, x = t * z := Iff.rfl

/-- **`A` is block diagonal over the `N`-cosets**: `A` preserves each of the closed subspaces
`ell2Sub m (coset N t j)`. -/
def IsBlockDiag (N : Subgroup G) (t : G) (m : ℕ)
    (A : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m) : Prop :=
  ∀ j : ℤ, ∀ x ∈ ell2Sub (G := G) m (coset N t j),
    A x ∈ ell2Sub (G := G) m (coset N t j)

/-- **The two-term block-Laurent operator** `B = D + C · λ(t)`: the operator whose injectivity
(when `D` is injective and both are block diagonal over the `N`-cosets) is the analytic core of
[JZLA20, Proposition 3.11]. -/
noncomputable def twoTerm (m : ℕ) (t : G)
    (D C : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m) :
    Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m :=
  D + C.comp (regBlk (G := G) m t)

/-- **The support of `λ(t)`**: the blockwise left regular operator maps the `δ`-span of `Z`
into the `δ`-span of `t · Z`. -/
theorem regBlk_ell2Sub (m : ℕ) (t : G) (Z : Set G) :
    regBlk (G := G) m t '' (ell2Sub (G := G) m Z : Set (Rep.HSum (G := G) m))
      ⊆ ell2Sub (G := G) m (cosetShift t Z) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hgen : ∀ z ∈ Submodule.span ℂ {w | ∃ g ∈ Z, ∃ i : Fin m,
        w = Rep.hinclude (G := G) m i (Rep.deltaG g)},
      regBlk (G := G) m t z ∈ ell2Sub (G := G) m (cosetShift t Z) := by
    intro z hz
    refine Submodule.span_induction
      (p := fun w _ => regBlk (G := G) m t w ∈ ell2Sub (G := G) m (cosetShift t Z))
      ?_ ?_ ?_ ?_ hz
    · rintro w ⟨g, hg, i, rfl⟩
      rw [regBlk_hdelta]
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      exact ⟨t * g, ⟨g, hg, rfl⟩, i, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hTclosed : IsClosed (ell2Sub (G := G) m (cosetShift t Z) :
      Set (Rep.HSum (G := G) m)) :=
    Submodule.isClosed_topologicalClosure (Submodule.span ℂ {w | ∃ g ∈ cosetShift t Z,
      ∃ i : Fin m, w = Rep.hinclude (G := G) m i (Rep.deltaG g)})
  have hle : Submodule.span ℂ {w | ∃ g ∈ Z, ∃ i : Fin m,
      w = Rep.hinclude (G := G) m i (Rep.deltaG g)}
      ≤ Submodule.comap (regBlk (G := G) m t).toLinearMap (ell2Sub (G := G) m (cosetShift t Z)) :=
    fun z hz => hgen z hz
  have hclosed : IsClosed (↑(Submodule.comap (regBlk (G := G) m t).toLinearMap
      (ell2Sub (G := G) m (cosetShift t Z))) : Set (Rep.HSum (G := G) m)) :=
    hTclosed.preimage (regBlk (G := G) m t).continuous
  have hcl := Submodule.topologicalClosure_minimal
    (s := Submodule.span ℂ {w | ∃ g ∈ Z, ∃ i : Fin m,
      w = Rep.hinclude (G := G) m i (Rep.deltaG g)}) hle hclosed
  exact hcl (show x ∈ (Submodule.span ℂ {w | ∃ g ∈ Z, ∃ i : Fin m,
      w = Rep.hinclude (G := G) m i (Rep.deltaG g)}).topologicalClosure from hx)

end Work.ORP311

import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

set_option linter.style.haveILetI false

noncomputable section

/-- The open standard `n`-simplex: the points of `Δ^n` all of whose barycentric coordinates
are positive. -/
def openStdSimplex (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) := {w | ∀ i, 0 < w.weights i}

/-- **A quotient map that is injective is a homeomorphism.**  If `f : α → β` is a quotient map
(surjective with the coinduced topology) and injective, then `α` and `β` are homeomorphic: the
inverse of the bijection `f` is continuous because for an open `U ⊆ α` we have
`(f⁻¹)⁻¹ U = f '' U`, and `f '' U` is open since `f ⁻¹' (f '' U) = U` (injectivity) is open
and `f` is a quotient map. -/
lemma nonempty_homeo_of_isQuotientMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Topology.IsQuotientMap f) (hinj : Function.Injective f) :
    Nonempty (α ≃ₜ β) :=
  ⟨(Equiv.ofBijective f ⟨hinj, hf.surjective⟩).toHomeomorphOfContinuousOpen
    hf.isCoinducing.continuous (hf.isCoinducing.isOpenMap_of_injective hinj)⟩

/-- **The characteristic map of `σ` meets the open cell exactly on the interior of the simplex.**
A point `a` of the standard `n`-simplex is carried by `χ.cls n σ` into the open `n`-cell
`χ.intCell n σ` if and only if all its barycentric coordinates are strictly positive.

If all coordinates are positive then the open simplex `⟨n, σ, a, _⟩` realizes `χ.cls n σ a`, and
since it has dimension exactly `n`, the point cannot lie in any lower skeleton.  Conversely, if
some coordinate vanishes then `a` lies on a face, so `χ.cls n σ a` is in the `(n-1)`-skeleton
(`DeltaRealization.cls_mem_skelSet_of_exists_zero_weight`) and hence is not in the open cell. -/
lemma cls_mem_intCell_iff {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) (a : StdSimplex ℝ (Fin (n + 1))) :
    (R.toDeltaSimplexMap.cls n σ a : X) ∈ R.toDeltaSimplexMap.intCell n σ ↔
      ∀ i, 0 < a.weights i := by
  constructor
  · intro hin i
    rcases n with _ | m
    · have h0 : a.weights 0 = 1 := by
        rw [← Fin.sum_univ_one (fun i => a.weights i), StdSimplex.total_of_fintype]
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi, h0]
      norm_num
    · by_contra hlt
      have hz : a.weights i = 0 := le_antisymm (not_lt.mp hlt) (StdSimplex.weights_nonneg i)
      exact hin.2 m (Nat.lt_succ_self m)
        (R.cls_mem_skelSet_of_exists_zero_weight m σ (y := a) ⟨i, hz⟩)
  · intro hpos
    refine ⟨Set.mem_range_self a, ?_⟩
    intro j hj hmem
    obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R j _).mp hmem
    have hreal : DeltaSimplexMap.real R.toDeltaSimplexMap p
        = DeltaSimplexMap.real R.toDeltaSimplexMap (⟨n, σ, a, hpos⟩ : OpenSimplex K) := by
      rw [hp]; rfl
    have hpn : p.dim = n := congrArg OpenSimplex.dim (R.real_injective hreal)
    omega

/-- **The characteristic map of a simplex restricts to a homeomorphism of the open cells.**
For a realized `Δ`-complex, an `n`-simplex `σ` and its open cell `χ.intCell n σ` (the points of
the closed cell `χ.cell n σ` lying in no lower skeleton), the restriction of the characteristic
map `χ.cls n σ` to `openStdSimplex n` is a homeomorphism onto the open cell.

Route: consider the corestriction `f` of `χ.cls n σ` to its image `χ.cell n σ`, a continuous
surjection from a compact space to a Hausdorff space, hence a quotient map
(`IsQuotientMap.of_surjective_continuous`).  (1) `f` is injective on the open simplex
(`eq_of_cls_eq_of_pos`); (2) for open `U ⊆ openStdSimplex n`, `f ⁻¹' (f '' U) = U` because a
boundary point of the simplex maps into the `(n-1)`-skeleton `χ.skelSet (n-1)`
(`DeltaRealization.cls_mem_skelSet_of_exists_zero_weight`) whereas `f '' U` lies in
`χ.intCell n σ`, which is disjoint from it (`mem_intCell_iff`); hence `f` restricted to the open
simplex is injective and open onto `χ.intCell n σ`, i.e. a homeomorphism onto its image.  The
image is exactly `χ.intCell n σ`: the open simplex of the image of an interior point is
`(n, σ, y)` (`DeltaRealization.openSimplexAt_cls_of_pos`), and conversely a point of the open
cell is realized by an open simplex of dimension `n` (`mem_skelSet_iff`), which must be `σ`
(same dimension and same cell).  Note: if you `open scoped Simplicial`, a set-builder cannot be
written directly in the argument of `TopCat.of`; use the named set `openStdSimplex`. -/
theorem exists_homeo_intCell {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) :
    Nonempty (TopCat.of (R.toDeltaSimplexMap.intCell n σ) ≃ₜ
      TopCat.of (openStdSimplex n)) := by
  haveI : T2Space X := R.t2
  let χ := R.toDeltaSimplexMap
  let f : C(StdSimplex ℝ (Fin (n + 1)), ↥(χ.cell n σ)) :=
    ⟨fun a => ⟨χ.cls n σ a, Set.mem_range_self a⟩,
      (χ.cls n σ).continuous.subtype_mk (fun a => Set.mem_range_self a)⟩
  -- `f` is a continuous surjection from the compact simplex onto the Hausdorff closed cell,
  -- hence a quotient map.
  have hsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    obtain ⟨a, ha⟩ := hc
    exact ⟨a, Subtype.ext ha⟩
  have hquot : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj f.continuous
  -- The open cell, viewed as a subset of the closed cell, is open there: it is the complement
  -- of the (closed) union of the lower skeleta.
  have hT : IsOpen ((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ) := by
    have hUclosed : IsClosed (⋃ (j : {j : ℕ // j < n}), χ.skelSet j) :=
      isClosed_iUnion_of_finite (fun j => isClosed_skelSet R j.1)
    have hTeq : (Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ
        = ((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹'
            (⋃ (j : {j : ℕ // j < n}), χ.skelSet j))ᶜ := by
      ext c
      rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_preimage,
        DeltaSimplexMap.intCell_eq_sdiff]
      simp only [Set.mem_sdiff]
      exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
    rw [hTeq]
    exact (hUclosed.preimage continuous_subtype_val).isOpen_compl
  -- The preimage of the open cell under `f` is the open standard simplex.
  have hpre : f ⁻¹' ((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ)
      = openStdSimplex n := by
    ext a
    rw [Set.mem_preimage, Set.mem_preimage]
    show (χ.cls n σ a : X) ∈ χ.intCell n σ ↔ a ∈ openStdSimplex n
    rw [cls_mem_intCell_iff R n σ a]
    rfl
  -- The restricted quotient map is injective: two interior points with the same image in the
  -- closed cell have the same barycentric coordinates (`eq_of_cls_eq_of_pos`).
  have hginj : Function.Injective
      (((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ).restrictPreimage f) := by
    intro y1 y2 h
    have hf : f y1.1 = f y2.1 :=
      congrArg (Subtype.val : ↥((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ)
        → ↥(χ.cell n σ)) h
    have hcl : χ.cls n σ y1.1 = χ.cls n σ y2.1 :=
      congrArg (Subtype.val : ↥(χ.cell n σ) → X) hf
    have h1 : ∀ i, 0 < y1.1.weights i := (cls_mem_intCell_iff R n σ y1.1).mp y1.2
    have h2 : ∀ i, 0 < y2.1.weights i := (cls_mem_intCell_iff R n σ y2.1).mp y2.2
    exact Subtype.ext (eq_of_cls_eq_of_pos R h1 hcl).2
  have hgq : Topology.IsQuotientMap
      (((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ).restrictPreimage f) :=
    hquot.restrictPreimage_isOpen hT
  obtain ⟨h1⟩ := nonempty_homeo_of_isQuotientMap _ hgq hginj
  -- The open cell, as a set in the closed cell, is homeomorphic to the open cell as a set in `X`.
  have heT : ↥((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ) ≃ₜ ↥(χ.intCell n σ) :=
    { toFun := fun c => ⟨(c.1.1 : X), c.2⟩,
      invFun := fun x => ⟨⟨(x.1 : X), DeltaSimplexMap.intCell_subset_cell χ n σ x.2⟩, x.2⟩,
      left_inv := fun c => by apply Subtype.ext; apply Subtype.ext; rfl,
      right_inv := fun x => by apply Subtype.ext; rfl,
      continuous_toFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) (fun c => c.2),
      continuous_invFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val
          (fun x => DeltaSimplexMap.intCell_subset_cell χ n σ x.2)) (fun x => x.2) }
  have heS : ↥(openStdSimplex n) ≃ₜ
      ↥(f ⁻¹' ((Subtype.val : ↥(χ.cell n σ) → X) ⁻¹' χ.intCell n σ)) :=
    (Homeomorph.setCongr hpre).symm
  exact ⟨heT.symm.trans (h1.symm.trans heS.symm)⟩

end

end Work.DeltaHomology

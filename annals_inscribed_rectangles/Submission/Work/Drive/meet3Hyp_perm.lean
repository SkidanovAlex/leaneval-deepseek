import Mathlib
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.T6GenAtDefs

/-!
# `Meet3Hyp` is invariant under a relabelling of the three chains

`Work.Drive.Meet3Hyp M D` bundles the four hypotheses (smoothness, transversality of the triple, the
face condition, the seam invariance) of the manifold triple-intersection parity engine for a family
`D : Fin 3 → ℝ³ → M` of three `3`-chains in a `4`-manifold.  This file proves that the bundle only
depends on the *set* of the three chains, not on the order in which they are listed:

> `Meet3Hyp M (fun k => D (σ k)) → Meet3Hyp M D`  for every `σ : Equiv.Perm (Fin 3)`.

The only mathematical content is the **permutation invariance of `TripleTransverse`** (the transversality
of three derivatives `f₀ f₁ f₂ : ℝ³ →L ℝ⁴`), which is *not* a tautology: as defined, the difference map
`(v₀,v₁,v₂) ↦ (f₀v₀ - f₁v₁, f₀v₀ - f₂v₂)` singles out the first slot, so the three arguments play
asymmetric roles on the nose.

The proof of that invariance is the standard rank-nullity argument, arranged as follows.  Write
`V = ℝ³`, `E = ℝ⁴` and for a *family* `f : Fin 3 → V →L[ℝ] E` let

* `diffFam f : (Fin 3 → V) →ₗ[ℝ] (E × E)`, `x ↦ (f 0 (x 0) - f 1 (x 1), f 0 (x 0) - f 2 (x 2))` —
  `TripleTransverse (f 0) (f 1) (f 2)` is exactly `(diffFam f).range = ⊤`
  (`tripleTransverse_iff_range_top`);
* `diffFamShift f σ : (Fin 3 → V) →ₗ[ℝ] (E × E)`,
  `x ↦ (f (σ 0) (x (σ 0)) - f (σ 1) (x (σ 1)), f (σ 0) (x (σ 0)) - f (σ 2) (x (σ 2)))` — the
  permutation acts on the *index of the function* **and** on the *slot of the parameter*, so that:

  * `(diffFamShift f σ).range = (diffFam (fun i => f (σ i))).range`
    (`range_diffFamShift`): the two maps differ by the linear equivalence
    `slotPerm σ : x ↦ x ∘ σ` of `Fin 3 → V`, which is surjective;
  * `(diffFamShift f σ).ker = (diffFam f).ker` (`ker_diffFamShift`): both kernels consist of the
    `x` with `f i (x i)` *all equal* over `i ∈ Fin 3` (`mem_ker_diffFam`, `mem_ker_diffFamShift`),
    a condition that is manifestly invariant under a relabelling of the three values.

Rank-nullity (`LinearMap.finrank_range_add_finrank_ker`, the source `Fin 3 → V` being the same for
both maps and finite-dimensional) then gives `finrank (range (diffFam f)) = finrank (range (diffFamShift f σ))`,
so surjectivity transfers.  Applying this to `f i := mfderiv (D i) (x i)` at the point `x ∘ σ` gives
the `trans` field of `Meet3Hyp M D`; the `face` field is transported by the same relabelling of the
common tangent direction (`TripleCommonDir` is invariant *without* any linear algebra, since the
witness `Fin 3 → V` can simply be permuted), and the remaining two fields (`smooth`, `seam`) are
single-variable statements.

With this, any consumer that proves `Meet3Hyp` for a convenient *ordering* of a triple of chains —
for instance the cyclic relabelling `D' i = D (i + k)`, or the orderings used by the concrete
encoded chains — gets it for every ordering.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- The parameter space of one chain: the unit cube of `ℝ³`. -/
abbrev cube3 := EuclideanSpace ℝ (Fin 3)

/-- The model space of the ambient `4`-manifold. -/
abbrev tgt4 := EuclideanSpace ℝ (Fin 4)

/-- The projection of `Fin 3 → ℝ³` onto its `i`-th slot. -/
def slotProj (i : Fin 3) : (Fin 3 → cube3) →ₗ[ℝ] cube3 :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => cube3) i

/-- **The difference map of a family of three derivatives**, indexed by `Fin 3 → ℝ³`. -/
def diffFam (f : Fin 3 → cube3 →L[ℝ] tgt4) : (Fin 3 → cube3) →ₗ[ℝ] (tgt4 × tgt4) :=
  LinearMap.prod
    (((f 0).toLinearMap.comp (slotProj 0)) - ((f 1).toLinearMap.comp (slotProj 1)))
    (((f 0).toLinearMap.comp (slotProj 0)) - ((f 2).toLinearMap.comp (slotProj 2)))

@[simp] lemma diffFam_apply (f : Fin 3 → cube3 →L[ℝ] tgt4) (x : Fin 3 → cube3) :
    diffFam f x = (f 0 (x 0) - f 1 (x 1), f 0 (x 0) - f 2 (x 2)) := by
  simp [diffFam, slotProj, LinearMap.prod_apply]

/-- **The difference map with the permutation applied to the indices of the functions and to the slots
of the parameter simultaneously.** -/
def diffFamShift (f : Fin 3 → cube3 →L[ℝ] tgt4) (σ : Equiv.Perm (Fin 3)) :
    (Fin 3 → cube3) →ₗ[ℝ] (tgt4 × tgt4) :=
  LinearMap.prod
    (((f (σ 0)).toLinearMap.comp (slotProj (σ 0))) - ((f (σ 1)).toLinearMap.comp (slotProj (σ 1))))
    (((f (σ 0)).toLinearMap.comp (slotProj (σ 0))) - ((f (σ 2)).toLinearMap.comp (slotProj (σ 2))))

@[simp] lemma diffFamShift_apply (f : Fin 3 → cube3 →L[ℝ] tgt4) (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → cube3) :
    diffFamShift f σ x = (f (σ 0) (x (σ 0)) - f (σ 1) (x (σ 1)),
      f (σ 0) (x (σ 0)) - f (σ 2) (x (σ 2))) := by
  simp [diffFamShift, slotProj, LinearMap.prod_apply]

/-- The relabelling `x ↦ x ∘ σ` of the parameter space `Fin 3 → ℝ³`. -/
def slotPerm (σ : Equiv.Perm (Fin 3)) : (Fin 3 → cube3) ≃ₗ[ℝ] (Fin 3 → cube3) :=
  LinearEquiv.funCongrLeft ℝ cube3 σ

@[simp] lemma slotPerm_apply (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → cube3) :
    slotPerm σ x = fun i => x (σ i) := by
  funext i
  simp [slotPerm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

lemma range_slotPerm (σ : Equiv.Perm (Fin 3)) :
    ((slotPerm σ : (Fin 3 → cube3) ≃ₗ[ℝ] (Fin 3 → cube3)) :
        (Fin 3 → cube3) →ₗ[ℝ] (Fin 3 → cube3)).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  refine ⟨fun i => y (σ.symm i), ?_⟩
  funext i
  simp [slotPerm_apply]

/-- Three values are all equal as soon as the first two comparisons hold. -/
lemma allEq_iff (g : Fin 3 → tgt4) : (∀ i j, g i = g j) ↔ (g 0 = g 1 ∧ g 0 = g 2) := by
  constructor
  · intro h; exact ⟨h 0 1, h 0 2⟩
  · rintro ⟨h1, h2⟩ i j
    fin_cases i <;> fin_cases j <;> simp_all

/-- The kernel of `diffFam f` is the set of `x` whose three values `f i (x i)` are all equal. -/
lemma mem_ker_diffFam (f : Fin 3 → cube3 →L[ℝ] tgt4) (x : Fin 3 → cube3) :
    x ∈ (diffFam f).ker ↔ ∀ i j : Fin 3, f i (x i) = f j (x j) := by
  rw [LinearMap.mem_ker, diffFam_apply, show (0 : tgt4 × tgt4) = (0, 0) from rfl,
    Prod.ext_iff, sub_eq_zero, sub_eq_zero]
  exact (allEq_iff fun i => f i (x i)).symm

/-- The kernel of `diffFamShift f σ` is the **same** set of `x`: the condition is a condition on the
three values `f i (x i)`, insensitive to the relabelling. -/
lemma mem_ker_diffFamShift (f : Fin 3 → cube3 →L[ℝ] tgt4) (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → cube3) :
    x ∈ (diffFamShift f σ).ker ↔ ∀ i j : Fin 3, f i (x i) = f j (x j) := by
  rw [LinearMap.mem_ker, diffFamShift_apply, show (0 : tgt4 × tgt4) = (0, 0) from rfl,
    Prod.ext_iff, sub_eq_zero, sub_eq_zero]
  rw [show (f (σ 0) (x (σ 0)) = f (σ 1) (x (σ 1)) ∧
      f (σ 0) (x (σ 0)) = f (σ 2) (x (σ 2))) ↔
      ∀ i j : Fin 3, f (σ i) (x (σ i)) = f (σ j) (x (σ j)) from
    (allEq_iff fun i => f (σ i) (x (σ i))).symm]
  constructor
  · intro h i j
    simpa [Equiv.apply_symm_apply] using h (σ.symm i) (σ.symm j)
  · intro h i j
    exact h (σ i) (σ j)

lemma ker_diffFamShift (f : Fin 3 → cube3 →L[ℝ] tgt4) (σ : Equiv.Perm (Fin 3)) :
    (diffFamShift f σ).ker = (diffFam f).ker := by
  ext x
  rw [mem_ker_diffFamShift, mem_ker_diffFam]

/-- Reindexing the family by `σ` does not change the range of the difference map. -/
lemma range_diffFamShift (f : Fin 3 → cube3 →L[ℝ] tgt4) (σ : Equiv.Perm (Fin 3)) :
    (diffFamShift f σ).range = (diffFam (fun i => f (σ i))).range := by
  have hcomp : diffFamShift f σ =
      (diffFam (fun i => f (σ i))).comp (slotPerm σ : (Fin 3 → cube3) →ₗ[ℝ] (Fin 3 → cube3)) := by
    apply LinearMap.ext
    intro x
    simp [slotPerm_apply]
  rw [hcomp, LinearMap.range_comp, range_slotPerm, Submodule.map_top]

/-- `TripleTransverse` is the surjectivity of the difference map on `Fin 3 → ℝ³`. -/
lemma tripleTransverse_iff_range_top (f : Fin 3 → cube3 →L[ℝ] tgt4) :
    TripleTransverse (f 0) (f 1) (f 2) ↔ (diffFam f).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  constructor
  · intro h w
    obtain ⟨v, h1, h2⟩ := h w.1 w.2
    exact ⟨v, by simp [h1, h2]⟩
  · rintro h w₁ w₂
    obtain ⟨v, hv⟩ := h (w₁, w₂)
    exact ⟨v, by simpa using congrArg Prod.fst hv, by simpa using congrArg Prod.snd hv⟩

/-- **The permutation invariance of `TripleTransverse`.**  The transversality of three derivatives is
a property of the *set* of the three derivatives. -/
theorem tripleTransverse_perm (f : Fin 3 → cube3 →L[ℝ] tgt4) (σ : Equiv.Perm (Fin 3))
    (h : TripleTransverse (f (σ 0)) (f (σ 1)) (f (σ 2))) :
    TripleTransverse (f 0) (f 1) (f 2) := by
  have h' : (diffFam fun i => f (σ i)).range = ⊤ :=
    (tripleTransverse_iff_range_top fun i => f (σ i)).mp h
  rw [tripleTransverse_iff_range_top]
  have hshift : (diffFamShift f σ).range = ⊤ := by
    rw [range_diffFamShift]; exact h'
  have hker := ker_diffFamShift f σ
  have h1 := LinearMap.finrank_range_add_finrank_ker (diffFam f)
  have h2 := LinearMap.finrank_range_add_finrank_ker (diffFamShift f σ)
  have hk : Module.finrank ℝ ↥((diffFamShift f σ).ker) =
      Module.finrank ℝ ↥((diffFam f).ker) := by
    rw [hker]
  have heq : Module.finrank ℝ ↥((diffFam f).range) =
      Module.finrank ℝ ↥((diffFamShift f σ).range) := by omega
  rw [hshift, finrank_top] at heq
  exact Submodule.eq_top_iff_finrank_eq.mpr heq

/-- **The permutation invariance of `TripleCommonDir`**: the common tangent direction at a triple
point is carried along by the relabelling of the three chains. -/
lemma tripleCommonDir_perm {g : Fin 3 → cube3 →L[ℝ] tgt4} (σ : Equiv.Perm (Fin 3))
    {v : Fin 3 → cube3}
    (h : TripleCommonDir (g (σ 0)) (g (σ 1)) (g (σ 2)) v) :
    TripleCommonDir (g 0) (g 1) (g 2) (fun i => v (σ.symm i)) := by
  have hall : ∀ j j' : Fin 3, g (σ j) (v j) = g (σ j') (v j') := by
    have h1 := h.1
    have h2 := h.2
    intro j j'
    fin_cases j <;> fin_cases j' <;> simp_all
  constructor
  · have := hall (σ.symm 0) (σ.symm 1)
    simpa [Equiv.apply_symm_apply] using this
  · have := hall (σ.symm 0) (σ.symm 2)
    simpa [Equiv.apply_symm_apply] using this

/-- **`Meet3Hyp` is invariant under a relabelling of the three chains.**  The four hypotheses of the
triple-intersection engine only depend on the three chains, not on the order in which they are
listed. -/
theorem meet3Hyp_perm {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (σ : Equiv.Perm (Fin 3))
    (h : Work.Drive.Meet3Hyp M (fun k => D (σ k))) : Work.Drive.Meet3Hyp M D := by
  -- at a meet of the unpermuted family, the three values `D k (x k)` coincide
  have hval : ∀ (x : Fin 3 → cube3), D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      ∀ k : Fin 3, D k (x k) = D 0 (x 0) := by
    intro x h01 h02 k
    fin_cases k
    · rfl
    · exact h01.symm
    · exact h02.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- smoothness: a single-variable statement
    intro k
    have hh := h.smooth (σ.symm k)
    simpa [Equiv.apply_symm_apply] using hh
  · -- transversality: shift the parameter to `x ∘ σ` and use the permutation invariance
    intro x hx h01 h02
    have hv := hval x h01 h02
    have hx' : ∀ k, x (σ k) ∈ Submission.Drive.unitBox 2 := fun k => hx (σ k)
    have hm1 : (fun k => D (σ k)) 0 (x (σ 0)) = (fun k => D (σ k)) 1 (x (σ 1)) :=
      (hv (σ 0)).trans (hv (σ 1)).symm
    have hm2 : (fun k => D (σ k)) 0 (x (σ 0)) = (fun k => D (σ k)) 2 (x (σ 2)) :=
      (hv (σ 0)).trans (hv (σ 2)).symm
    have htr := h.trans (fun j => x (σ j)) hx' hm1 hm2
    exact tripleTransverse_perm
      (fun i => mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D i) (x i)) σ htr
  · -- the face condition: transport the box combinatorics and relabel the common direction
    intro x hx h01 h02 hbdry
    have hv := hval x h01 h02
    have hx' : ∀ k, x (σ k) ∈ Submission.Drive.unitBox 2 := fun k => hx (σ k)
    have hm1 : (fun k => D (σ k)) 0 (x (σ 0)) = (fun k => D (σ k)) 1 (x (σ 1)) :=
      (hv (σ 0)).trans (hv (σ 1)).symm
    have hm2 : (fun k => D (σ k)) 0 (x (σ 0)) = (fun k => D (σ k)) 2 (x (σ 2)) :=
      (hv (σ 0)).trans (hv (σ 2)).symm
    have hbdry' : ∃ k, x (σ k) ∈ Submission.Drive.unitBoxBdry 2 := by
      obtain ⟨k, hk⟩ := hbdry
      exact ⟨σ.symm k, by simpa [Equiv.apply_symm_apply] using hk⟩
    obtain ⟨k₀, i₀, h1, h2, h3, v', hCD, hv'⟩ :=
      h.face (fun j => x (σ j)) hx' hm1 hm2 hbdry'
    refine ⟨σ k₀, i₀, h1, h2, ?_, ?_⟩
    · intro k' hk' j
      have hne : σ.symm k' ≠ k₀ := by
        intro hh
        exact hk' (by rw [← hh]; simp)
      simpa [Equiv.apply_symm_apply] using h3 (σ.symm k') hne j
    · refine ⟨fun i => v' (σ.symm i), ?_, ?_⟩
      · refine tripleCommonDir_perm (σ := σ)
          (g := fun i => mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D i) (x i)) ?_
        simpa using hCD
      · simpa [Equiv.apply_symm_apply] using hv'
  · -- the seam invariance: again a single-variable statement
    intro k x hx
    have hh := h.seam (σ.symm k) x hx
    simpa [Equiv.apply_symm_apply] using hh

/-- **The cyclic relabelling of the three chains preserves `Meet3Hyp`.**  This is `meet3Hyp_perm`
with `σ = (Equiv.addRight k).symm`, i.e. the case in which the chains are rotated: it is what the
consumers of `Meet3Hyp` use when they need the parity engine for the family `i ↦ D (i + k)` rather than
for `D` itself (cf. the node `Work.Drive.Meet3Hyp_cyclic`). -/
theorem meet3Hyp_reindex_add {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} (h : Work.Drive.Meet3Hyp M D) (k : Fin 3) :
    Work.Drive.Meet3Hyp M (fun i => D (i + k)) := by
  refine meet3Hyp_perm (fun i => D (i + k)) (Equiv.addRight k).symm ?_
  simpa using h

end

end Work.Drive

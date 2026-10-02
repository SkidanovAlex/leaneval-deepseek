import Submission.Work.Tubular.DiscManifold.Charted
import Submission.Work.Tubular.DiscManifold.exists_halfModelReindex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The normal disc bundle is a smooth manifold with boundary

`Charted.lean` makes `D_ε(ν)` a `C¹` manifold modelled on the product `ℝ⁸ × Half (k-1)`.  This file
transports that structure along the linear reindexing `Λ : EuclideanHalfSpace (8+k) ≃ ℝ⁸ × Half (k-1)`
(`Work.Tubular.DiscManifold.HalfModelReindex`), proving directly — via `isManifold_of_contDiffOn` —
that `D_ε(ν)` is a `C¹` manifold with boundary modelled on `EuclideanHalfSpace (8+k)`.

The transition in the half-space model is the conjugate `Λ.op ≫ (chart transition) ≫ Λ.symm.op`, and
the computation `I₂ (Λ.symm (g (Λ (I₂.symm t)))) = join ((I₁ ∘ g ∘ I₁.symm) (split t))` reduces its
smoothness to the smoothness proved in `Transition.lean`.
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter
open OpenPartialHomeomorph

open Work.ThomBordism.PontryaginThom (EmbeddingData CoverIdx coverBaseSet coverIndexAt
  mem_coverBaseSet_indexAt)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-! ## The reindexing and the two models -/

/-- The half-space condition is exactly the fibre condition: `I₁ (Λ x) = split x.val`. -/
theorem map_Iprod_chart (R : DiscManifold.HalfModelReindex k)
    (x : EuclideanHalfSpace (8 + k)) :
    (Iprod k) (R.Λ x) = R.split x.val := by
  refine Prod.ext ?_ ?_
  · show (𝓡 8) (R.Λ x).1 = (R.split x.val).1
    rw [R.Λ_fst]
    rfl
  · show (hModel (k - 1)) (R.Λ x).2 = (R.split x.val).2
    rw [show (hModel (k - 1)) (R.Λ x).2 = ((R.Λ x).2).val from rfl, R.Λ_snd_val]

theorem map_chart_symm (R : DiscManifold.HalfModelReindex k) (y : Euc 8 × Half (k - 1)) :
    (modelWithCornersEuclideanHalfSpace (8 + k)) (R.Λ.symm y) = R.join (Iprod k y) := by
  obtain ⟨a, b⟩ := y
  show (R.Λ.symm (a, b)).val = R.join (Iprod k (a, b))
  rw [R.Λ_symm_val a b]
  rfl

theorem Iprod_symm_Iprod (y : Euc 8 × Half (k - 1)) :
    (Iprod k).symm (Iprod k y) = y := by
  obtain ⟨a, b⟩ := y
  show (Iprod k).symm (Iprod k (a, b)) = (a, b)
  refine Prod.ext ?_ ?_
  · show (𝓡 8).symm ((𝓡 8) a) = a
    rfl
  · show (hModel (k - 1)).symm ((hModel (k - 1)) b) = b
    rw [show (hModel (k - 1)) b = b.val from rfl,
      halfModel_symm_apply_of_le (k - 1) b.property]
    rfl

theorem range_Iprod : Set.range (⇑(Iprod k)) =
    {z : Euc 8 × Euc ((k - 1) + 1) | 0 ≤ z.2 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    show 0 ≤ ((Iprod k) y).2 0
    rw [show ((Iprod k) y).2 = y.2.val from rfl]
    exact y.2.property
  · intro hz
    exact ⟨(z.1, ⟨z.2, hz⟩), rfl⟩

/-- The half-space model, written as `𝓡∂ (8+k)`. -/
abbrev Ihalf (k : ℕ) [NeZero k] :
    ModelWithCorners ℝ (Euc (8 + k)) (EuclideanHalfSpace (8 + k)) :=
  modelWithCornersEuclideanHalfSpace (8 + k)

theorem range_Ihalf : Set.range (⇑(Ihalf k)) = {t : Euc (8 + k) | 0 ≤ t 0} :=
  range_modelWithCornersEuclideanHalfSpace (8 + k)

/-! ## The conjugation of the transition -/

theorem contDiffOn_conj_chart (R : DiscManifold.HalfModelReindex k)
    {g : OpenPartialHomeomorph (Euc 8 × Half (k - 1)) (Euc 8 × Half (k - 1))}
    (h1 : ContDiffOn ℝ 1 (⇑(Iprod k) ∘ ⇑g ∘ ⇑(Iprod k).symm)
      ((⇑(Iprod k).symm) ⁻¹' g.source ∩ Set.range (⇑(Iprod k)))) :
    ContDiffOn ℝ 1
      (⇑(Ihalf k) ∘
        ⇑(R.Λ.toOpenPartialHomeomorph ≫ₕ g ≫ₕ R.Λ.symm.toOpenPartialHomeomorph) ∘
        ⇑(Ihalf k).symm)
      ((⇑(Ihalf k).symm) ⁻¹'
        (R.Λ.toOpenPartialHomeomorph ≫ₕ g ≫ₕ R.Λ.symm.toOpenPartialHomeomorph).source ∩
        Set.range (⇑(Ihalf k))) := by
  set Φ : OpenPartialHomeomorph (EuclideanHalfSpace (8 + k)) (Euc 8 × Half (k - 1)) :=
    R.Λ.toOpenPartialHomeomorph with hΦ
  set Ψ : OpenPartialHomeomorph (Euc 8 × Half (k - 1)) (EuclideanHalfSpace (8 + k)) :=
    R.Λ.symm.toOpenPartialHomeomorph with hΨ
  set S : Set (Euc (8 + k)) :=
    (⇑(Ihalf k).symm) ⁻¹' (Φ ≫ₕ g ≫ₕ Ψ).source ∩ Set.range (⇑(Ihalf k)) with hS
  have hΦsrc : Φ.source = Set.univ := rfl
  have hΨsrc : Ψ.source = Set.univ := rfl
  have ht0 : ∀ t ∈ S, 0 ≤ t 0 := by
    intro t ht
    rw [hS] at ht
    obtain ⟨-, h2⟩ := ht
    rwa [range_Ihalf] at h2
  have hsymm : ∀ (t : Euc (8 + k)) (ht : t ∈ S),
      (⇑(Ihalf k).symm) t = (⟨t, ht0 t ht⟩ : EuclideanHalfSpace (8 + k)) :=
    fun t ht => modelWithCornersEuclideanHalfSpace_symm_apply_of_le (ht0 t ht)
  have hmem : ∀ t ∈ S, R.Λ ((⇑(Ihalf k).symm) t) ∈ g.source := by
    intro t ht
    rw [hS] at ht
    obtain ⟨h, -⟩ := ht
    rw [OpenPartialHomeomorph.trans_source] at h
    obtain ⟨-, h2⟩ := h
    rw [OpenPartialHomeomorph.trans_source] at h2
    exact h2.1
  have hnice : ContDiffOn ℝ 1 (fun t : Euc (8 + k) =>
      R.join (⇑(Iprod k) (g (⇑(Iprod k).symm (R.split t))))) S := by
    have hsp : ContDiffOn ℝ 1 (fun t : Euc (8 + k) => R.split t) S := R.split.contDiff.contDiffOn
    have hmaps : Set.MapsTo (fun t : Euc (8 + k) => R.split t) S
        ((⇑(Iprod k).symm) ⁻¹' g.source ∩ Set.range (⇑(Iprod k))) := by
      intro t ht
      have h2 : (Iprod k) (R.Λ ((⇑(Ihalf k).symm) t)) = R.split t := by
        rw [hsymm t ht]
        exact map_Iprod_chart R ⟨t, ht0 t ht⟩
      have h3 : R.Λ ((⇑(Ihalf k).symm) t) = (Iprod k).symm (R.split t) := by
        rw [← Iprod_symm_Iprod (R.Λ ((⇑(Ihalf k).symm) t)), h2]
      refine ⟨?_, ?_⟩
      · show (⇑(Iprod k).symm) (R.split t) ∈ g.source
        rw [← h3]
        exact hmem t ht
      · show R.split t ∈ Set.range (⇑(Iprod k))
        rw [range_Iprod]
        show 0 ≤ (R.split t).2 0
        rw [R.split_snd_zero]
        exact ht0 t ht
    have hc1 : ContDiffOn ℝ 1 ((⇑(Iprod k) ∘ ⇑g ∘ ⇑(Iprod k).symm) ∘
        (fun t : Euc (8 + k) => R.split t)) S := h1.comp hsp hmaps
    have hc2 : ContDiffOn ℝ 1 (fun t : Euc (8 + k) =>
        R.join ((⇑(Iprod k) ∘ ⇑g ∘ ⇑(Iprod k).symm) (R.split t))) S :=
      R.join.contDiff.comp_contDiffOn hc1
    exact hc2
  refine hnice.congr (fun t ht => ?_)
  have h3 : R.Λ ((⇑(Ihalf k).symm) t) = (Iprod k).symm (R.split t) := by
    have h2 : (Iprod k) (R.Λ ((⇑(Ihalf k).symm) t)) = R.split t := by
      rw [hsymm t ht]
      exact map_Iprod_chart R ⟨t, ht0 t ht⟩
    rw [← Iprod_symm_Iprod (R.Λ ((⇑(Ihalf k).symm) t)), h2]
  show (⇑(Ihalf k) ((Φ ≫ₕ g ≫ₕ Ψ) ((⇑(Ihalf k).symm) t))) =
    R.join (⇑(Iprod k) (g (⇑(Iprod k).symm (R.split t))))
  rw [show (Φ ≫ₕ g ≫ₕ Ψ) ((⇑(Ihalf k).symm) t) = R.Λ.symm (g (R.Λ ((⇑(Ihalf k).symm) t))) from rfl,
    h3, map_chart_symm]

end

end Work.Tubular

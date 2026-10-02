import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.orientedFibreGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre of the normal bundle is homeomorphic to the fibre of the normal total space

For an embedded compact smooth `8`-manifold `E : EmbeddingData V (8 + k)` with normal data `ND`,
`Work.Tubular.eucNormalHomeomorph E ND` identifies the total space of the Euclidean gluing-data
bundle `Work.Tubular.normalBundle E ND` with the concrete normal total space
`Work.Tubular.NormalTotal E`.  This module records that the identification *respects the fibres over
a point `x`* and *respects the punctured fibres*: `eucNormalHomeomorph` carries the fibre over `x`
onto `nfSet E x` and the punctured fibre onto `nfPunct E x`, hence restricts to a homeomorphism of
the fibre pairs.  This is the geometric input that lets the fibre generators `nfGen` of the normal
Thom pair be compared with the fibre generators of the abstract bundle.

The only computation needed is that `bundleToNormal` is `⟨(y.1, insCLM ... y.2), _⟩` (so the
projection is `y.1` and the normal vector is `insCLM` of the fibre coordinate) together with the
norm preservation `Work.Tubular.norm_insCLM`, which says that `insCLM E ND i x` vanishes exactly on
`0`.
-/

set_option autoImplicit false

namespace Work.ThomBordism

/-- The isometric insertion of the fibre of the normal bundle into the ambient space is injective:
it vanishes exactly on `0`. -/
theorem insCLM_ne_zero_iff {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) (v : Work.Tubular.Euc k) :
    Work.Tubular.insCLM E ND i x v ≠ 0 ↔ v ≠ 0 :=
  not_congr (by rw [← norm_eq_zero, Work.Tubular.norm_insCLM E ND i hx v, norm_eq_zero])

theorem exists_fibreHomeomorph_normalBundle {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    ∃ e : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x) ≃ₜ
        ↥(Work.ThomBordism.nfSet E x),
      (∀ p : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
        ((e p : ↥(Work.ThomBordism.nfSet E x)) : Work.Tubular.NormalTotal E)
          = Work.Tubular.eucNormalHomeomorph E ND (p : (Work.Tubular.normalBundle E ND).TotalSpace)) ∧
      (∀ p : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
        p ∈ Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x ↔
          e p ∈ Work.ThomBordism.nfPunct E x) := by
  classical
  -- `eucNormalHomeomorph` maps the fibre over `x` to the fibre over `x`
  have hiff : ∀ y : (Work.Tubular.normalBundle E ND).TotalSpace,
      y ∈ Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x ↔
        (Work.Tubular.eucNormalHomeomorph E ND) y ∈ Work.ThomBordism.nfSet E x := by
    intro y
    simp only [Work.ThomBordism.fibre, Set.mem_ofPred_eq, Work.ThomBordism.nfSet,
      Work.Tubular.NormalTotal.proj, Work.Tubular.eucNormalHomeomorph_apply,
      Work.Tubular.bundleToNormal]
  -- the restriction acts by `eucNormalHomeomorph` on the underlying points
  have hcomm : ∀ p : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
      ((↑(((Work.Tubular.eucNormalHomeomorph E ND).subtype hiff) p)) : Work.Tubular.NormalTotal E)
        = Work.Tubular.eucNormalHomeomorph E ND
            (p : (Work.Tubular.normalBundle E ND).TotalSpace) :=
    fun p => rfl
  refine ⟨(Work.Tubular.eucNormalHomeomorph E ND).subtype hiff, hcomm, ?_⟩
  -- and it preserves the punctured part: the normal vector of the image is `insCLM` of the fibre
  -- coordinate, which vanishes exactly on `0`
  intro p
  have h1 := hcomm p
  have hp : (p : (Work.Tubular.normalBundle E ND).TotalSpace).proj = x := p.2
  simp only [Work.ThomBordism.fibrePunctSub, Set.mem_preimage, Work.ThomBordism.fibrePunct,
    Set.mem_ofPred_eq, Work.ThomBordism.nfPunct, Work.Tubular.NormalTotal.vec]
  rw [h1]
  simp only [Work.Tubular.eucNormalHomeomorph_apply, Work.Tubular.bundleToNormal]
  rw [hp]
  exact ⟨fun h => (insCLM_ne_zero_iff E ND ((Work.Tubular.normalBundle E ND).indexAt x)
      (ND.D.mem_baseSet_at x) _).mpr h.2,
    fun h => ⟨rfl, (insCLM_ne_zero_iff E ND ((Work.Tubular.normalBundle E ND).indexAt x)
      (ND.D.mem_baseSet_at x) _).mp h⟩⟩

end Work.ThomBordism

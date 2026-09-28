import Mathlib
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Serre.simpHomVanishing
import Submission.Work.Serre.simpHomExists
import Submission.Work.Serre.E2dEngine
import Submission.Work.Serre.cubePairDefs

set_option synthInstance.maxHeartbeats 400000


/-!
# Tools for the cell step

Two families of tools, both used by `Work.Serre.cellStep`:

* the two "long exact sequence" consequences of a short exact sequence of chain complexes
  (if the third (resp. first) term is acyclic, the first (resp. second) map is a
  quasi-isomorphism), together with their specialisations to the triple of subsets
  `A ⊆ B ⊆ X` (where the first map enlarges the space and the second shrinks the relative part);
* the criterion "a pair which is compressible in every dimension has vanishing relative
  homology" (`Work.Serre.simpHomVanishing`) and the corresponding statement for the preimage
  under a Serre fibration (`Work.Serre.isZero_relChains_preimage_of_base_compress`).
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The two exactness consequences -/

/-- **If the third term of a short exact sequence of chain complexes is acyclic, the first map is a
quasi-isomorphism.**  (The long exact sequence argument in degree `k`.) -/
theorem isIso_homologyMap_f_of_acyclic_X3 {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (hS : S.ShortExact) (h : ∀ k, IsZero (S.X₃.homology k)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.f k) := by
  haveI hmono : Mono (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₁ (k + 1) k (by simp [ComplexShape.down]))
      (IsZero.eq_zero_of_src (h (k + 1)) _)
  haveI hepi : Epi (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.epi_f (hS.homology_exact₂ k) (IsZero.eq_zero_of_tgt (h k) _)
  exact isIso_of_mono_of_epi _

/-- **If the first term of a short exact sequence of chain complexes is acyclic, the second map is a
quasi-isomorphism.** -/
theorem isIso_homologyMap_g_of_acyclic_X1 {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (hS : S.ShortExact) (h : ∀ k, IsZero (S.X₁.homology k)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.g k) := by
  haveI hmono : Mono (HomologicalComplex.homologyMap S.g k) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₂ k) (IsZero.eq_zero_of_src (h k) _)
  haveI hepi : Epi (HomologicalComplex.homologyMap S.g k) := by
    rcases k with _ | k'
    · haveI hg : Epi S.g := hS.epi_g
      refine HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (fun j hj => ?_)
      simp [ComplexShape.down] at hj
    · have hrel : (ComplexShape.down ℕ).Rel (k' + 1) k' := by simp [ComplexShape.down]
      have hex := hS.homology_exact₃ (k' + 1) k' hrel
      exact ShortComplex.Exact.epi_f hex (IsZero.eq_zero_of_tgt (h k') _)
  exact isIso_of_mono_of_epi _

/-! ## The two triple steps -/

/-- **Shrinking the relative part.**  If the pair `(B, A)` has vanishing relative homology, then the
map `C_*(X,A) ⟶ C_*(X,B)` of relative chain complexes induced by `A ⊆ B` is a quasi-isomorphism. -/
theorem isIso_relCokerMap_of_acyclic (X : TopCat) {A B : Set X} (hAB : A ⊆ B)
    (h : ∀ k, IsZero ((Work.Cohomology.tripleShort X A B hAB).X₁.homology k)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A B hAB) n) := by
  rw [← Work.Cohomology.tripleShort_g X A B hAB]
  exact isIso_homologyMap_g_of_acyclic_X1
    (Work.Cohomology.relChains_triple_shortExact X A B hAB) h n

/-- **Enlarging the space.**  If the pair `(X, B)` has vanishing relative homology, then the map
`C_*(B,A) ⟶ C_*(X,A)` induced by the inclusion of pairs is a quasi-isomorphism. -/
theorem isIso_tripleIncl_of_acyclic (X : TopCat) {A B : Set X} (hAB : A ⊆ B)
    (h : ∀ k, IsZero ((Work.Cohomology.tripleShort X A B hAB).X₃.homology k)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.tripleShort X A B hAB).f n) :=
  isIso_homologyMap_f_of_acyclic_X3 (Work.Cohomology.relChains_triple_shortExact X A B hAB) h n

/-! ## Vanishing of relative homology from compressibility -/

/-- **The compression criterion**: a pair which is compressible in every dimension has vanishing
relative homology in every degree. -/
theorem isZero_relChains_of_compress {X : Type} [TopologicalSpace X] {A : Set X}
    (h : ∀ d, Work.RatHurewicz.CompressRel X A d) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of X) A).homology m) := by
  obtain ⟨H⟩ := Work.Serre.simpHom_of_compress m (fun d _ => h d)
  exact Work.Serre.simpHomVanishing H m le_rfl

/-- A deformation retraction of `Y` onto `A` fixing `A` pointwise gives the compression criterion
for the pair `(Y,A)` in every dimension. -/
theorem isZero_relChains_of_deformation {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (c : C(Y × I, Y)) (hc0 : ∀ y, c (y, 0) = y) (hc1 : ∀ y, c (y, 1) ∈ A)
    (hcA : ∀ y ∈ A, ∀ t : I, c (y, t) = y) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of Y) A).homology m) :=
  isZero_relChains_of_compress (fun d => compressRel_of_deformation c hc0 hc1 hcA d) m

/-- **The compression criterion for the preimage of a fibration**: if the base pair `(W, W₀)` is
compressible in every dimension, then the pair `(q⁻¹W, q⁻¹W₀)` has vanishing relative homology in
every degree. -/
theorem isZero_relChains_preimage_of_compress {X Z : Type} [TopologicalSpace X]
    [TopologicalSpace Z] (q : C(X, Z)) (hq : Work.StemsB.IsSerreFibration q) {W₀ W : Set Z}
    (hW : W₀ ⊆ W) (h : ∀ d, Work.RatHurewicz.CompressRel ↥W {x : ↥W | (x : Z) ∈ W₀} d)
    (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' W))
      {x : ↥(q ⁻¹' W) | (x : X) ∈ q ⁻¹' W₀}).homology m) :=
  isZero_relChains_preimage_of_base_compress q hq W₀ W hW h m

end

end Work.Serre

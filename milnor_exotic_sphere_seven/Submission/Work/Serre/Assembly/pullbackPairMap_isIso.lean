import Mathlib
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Serre.serreK2Int
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.Serre.Assembly.hZeroOfPiZeroInt
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_bijective
import Submission.Work.Serre.rwPiBijectiveOfRelPiVanishing
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv
import Submission.Work.Serre.subsingleton_homotopyFibre_of_piMapN
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_zero_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.Assembly

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-! ## The range form of the five lemma for a map of pairs -/

/-- **The five lemma for a map of pairs, in a range.**  If the map of spaces and the map of
subspaces induce isomorphisms on homology in all degrees `≤ n`, then the induced map of relative
chain complexes does so in degree `n` (in particular in all degrees `≤ n`).

Proof: the morphism of short exact sequences of pairs `hPairShortMap` and
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃`, whose hypotheses are only the degrees
`n` and `n - 1` of the two inputs. -/
theorem relChainsMapOf_isIso_range {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) (n : ℕ)
    (hf : ∀ k, k ≤ n → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ X Y f) k))
    (hg : ∀ k, k ≤ n → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) k)) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf X Y A B f g w) n) := by
  refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (Work.Cohomology.hPairShortMap X Y A B f g w) (Work.Cohomology.hPairShort_shortExact X A)
    (Work.Cohomology.hPairShort_shortExact Y B) n ?_ (hf n le_rfl) ?_ ?_
  · show Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) n)
    haveI := hg n le_rfl
    exact IsIso.epi_of_iso _
  · intro j hj
    have hj' : j ≤ n := by
      rw [ComplexShape.down_Rel] at hj
      omega
    show IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) j)
    exact hg j hj'
  · intro j hj
    have hj' : j ≤ n := by
      rw [ComplexShape.down_Rel] at hj
      omega
    show Mono (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) j)
    haveI := hf j hj'
    exact IsIso.mono_of_iso _

/-! ## Path lifting for Serre fibrations -/

/-- **Path lifting for a Serre fibration.**  For `p : E → B` a Serre fibration with `B` path
connected, if `E` is nonempty then every point of `B` is in the image of `p` (lift a path from
`p e` to `b` through `p`, using the homotopy lifting property with respect to a point). -/
theorem exists_preimage_of_isSerreFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hB : PathConnectedSpace B) (e : E) (b : B) : ∃ e' : E, p e' = b := by
  obtain ⟨γ⟩ := PathConnectedSpace.joined (p e) b
  have hv := hp 0
  let z : Fin 0 → I := fun i => i.elim0
  let f : C(Fin 0 → I, E) := ContinuousMap.const (Fin 0 → I) e
  let b' : C(Fin 0 → I, B) := ContinuousMap.const (Fin 0 → I) b
  have H : (p.comp f).Homotopy b' :=
    { toContinuousMap := ⟨fun q : I × (Fin 0 → I) => γ q.1,
        γ.continuous.comp continuous_fst⟩
      map_zero_left := fun _ => γ.source
      map_one_left := fun _ => γ.target }
  obtain ⟨g, H', hH'⟩ := hv f b' H
  refine ⟨g z, ?_⟩
  have h1 : H'.toContinuousMap (1, z) = g z := H'.map_one_left z
  have h2 : p (H'.toContinuousMap (1, z)) = H.toContinuousMap (1, z) := by
    have := congrFun (congrArg DFunLike.coe hH') (1, z)
    simpa using this
  have h3 : H.toContinuousMap (1, z) = b := H.map_one_left z
  rw [← h1, h2, h3]

/-! ## The pair map of the pullback square -/

variable {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]

/-- **The map on the fibres of the pullback square** `A = q⁻¹{γ₀} → C = p⁻¹{b₀}`, given by the
second projection of the pullback.  It is an isomorphism of topological spaces
(`isIso_fibrePairMap`). -/
def fibrePairMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
      TopCat.of (p ⁻¹' ({b₀} : Set B)) :=
  TopCat.ofHom ⟨
    (fun x : ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) =>
      ⟨Work.StemsB.pullbackSnd g p x.1, by
        have hx : x.1.1.1 = γ₀ := x.2
        calc p (x.1.1.2) = g (x.1.1.1) := x.1.2.symm
          _ = g γ₀ := by rw [hx]
          _ = b₀ := hbase⟩),
    Continuous.subtype_mk
      ((Work.StemsB.pullbackSnd g p).continuous.comp continuous_subtype_val)
      (fun x => by
        have hx : x.1.1.1 = γ₀ := x.2
        calc p (x.1.1.2) = g (x.1.1.1) := x.1.2.symm
          _ = g γ₀ := by rw [hx]
          _ = b₀ := hbase)⟩

/-- The inverse of `fibrePairMap`: `c ↦ (γ₀, c)` on the fibres. -/
def fibrePairMapInv (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    TopCat.of (p ⁻¹' ({b₀} : Set B)) ⟶
      TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) :=
  TopCat.ofHom ⟨
    (fun c : ↥(p ⁻¹' ({b₀} : Set B)) =>
      ⟨⟨(γ₀, c.1), by rw [hbase]; exact (c.2).symm⟩, rfl⟩),
    Continuous.subtype_mk
      (Continuous.subtype_mk
        (continuous_const.prodMk continuous_subtype_val)
        (fun c => by rw [hbase]; exact (c.2).symm))
      (fun c => rfl)⟩

/-- `fibrePairMap` and its inverse compose to the identity on the source. -/
theorem fibrePairMap_hom_inv (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    fibrePairMap g p γ₀ b₀ hbase ≫ fibrePairMapInv g p γ₀ b₀ hbase =
      𝟙 (TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))) := by
  apply TopCat.ext
  intro x
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  exact Prod.ext x.2.symm rfl

/-- `fibrePairMap` and its inverse compose to the identity on the target. -/
theorem fibrePairMap_inv_hom (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    fibrePairMapInv g p γ₀ b₀ hbase ≫ fibrePairMap g p γ₀ b₀ hbase =
      𝟙 (TopCat.of (p ⁻¹' ({b₀} : Set B))) := by
  apply TopCat.ext
  intro c
  refine Subtype.ext ?_
  rfl

/-- **The fibre map is an isomorphism of topological spaces.** -/
theorem isIso_fibrePairMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    IsIso (fibrePairMap g p γ₀ b₀ hbase) :=
  ⟨fibrePairMapInv g p γ₀ b₀ hbase, fibrePairMap_hom_inv g p γ₀ b₀ hbase,
    fibrePairMap_inv_hom g p γ₀ b₀ hbase⟩

/-- **The chain map induced by `fibrePairMap` is an isomorphism** (functoriality on an isomorphism
of spaces). -/
theorem isIso_chainMap_fibrePairMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B)
    (hbase : g γ₀ = b₀) :
    IsIso (Work.Cohomology.chainMap ℤ
      (TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
      (TopCat.of (p ⁻¹' ({b₀} : Set B)))
      (fibrePairMap g p γ₀ b₀ hbase)) := by
  haveI : IsIso (fibrePairMap g p γ₀ b₀ hbase) := isIso_fibrePairMap g p γ₀ b₀ hbase
  exact Functor.map_isIso _ _

/-- The compatibility of `fibrePairMap` with the inclusions of the subspaces: it is the second
component of the map of pairs `(X, A) → (E, C)` induced by `pullbackSnd`.  This is the proof
argument of `Work.Serre.CWModel.pullbackPairMap`. -/
theorem fibrePairMap_comp (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ≫
        TopCat.ofHom (Work.StemsB.pullbackSnd g p) =
      fibrePairMap g p γ₀ b₀ hbase ≫
        Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' ({b₀} : Set B)) := by
  ext x
  rfl

/-- **`pullbackPairMap` is the relative chain map of the map of pairs `(X,A) → (E,C)`.** -/
theorem pullbackPairMap_eq_relChainsMapOf (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B)
    (hbase : g γ₀ = b₀) :
    Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase =
      Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
        (TopCat.ofHom (Work.StemsB.pullbackSnd g p)) (fibrePairMap g p γ₀ b₀ hbase)
        (fibrePairMap_comp g p γ₀ b₀ hbase) := rfl

/-! ## The delegated inputs -/

/-! ## The target -/

theorem pullbackPairMap_isIso {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B)
    (hbase : g γ₀ = b₀) (hp : Work.StemsB.IsSerreFibration p) (N : ℕ)
    (hΓ : PathConnectedSpace Γ) (hB : PathConnectedSpace B)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) :
    ∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) i) := by
  change ∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
      ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
      (TopCat.ofHom (Work.StemsB.pullbackSnd g p)) (fibrePairMap g p γ₀ b₀ hbase)
      (fibrePairMap_comp g p γ₀ b₀ hbase)) i)
  intro i hi
  by_cases hne : Nonempty (Work.StemsB.Pullback g p)
  · haveI : Nonempty (Work.StemsB.Pullback g p) := hne
    have hf : ∀ k : ℕ, k ≤ i → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
          (TopCat.ofHom (Work.StemsB.pullbackSnd g p))) k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact hZeroOfPiZeroInt _ (fun x => pullbackSnd_piMapN_zero_bijective g p hp
          (fun y => hg 1 (by omega) y) hΓ hB x)
      · refine serreK2IntSharp _ N (fun j hj x => ?_) k hkpos (by omega)
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0
          exact pullbackSnd_piMapN_zero_bijective g p hp
            (fun y => hg 1 (by omega) y) hΓ hB x
        · exact pullbackSnd_piMapN_bijective g p hp N hg j hjpos hj x
    have hg' : ∀ k : ℕ, k ≤ i → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ
          (TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of (p ⁻¹' ({b₀} : Set B)))
          (fibrePairMap g p γ₀ b₀ hbase)) k) := by
      intro k _
      haveI : IsIso (Work.Cohomology.chainMap ℤ
          (TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of (p ⁻¹' ({b₀} : Set B)))
          (fibrePairMap g p γ₀ b₀ hbase)) :=
        isIso_chainMap_fibrePairMap g p γ₀ b₀ hbase
      exact Functor.map_isIso
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k)
        (Work.Cohomology.chainMap ℤ
          (TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of (p ⁻¹' ({b₀} : Set B)))
          (fibrePairMap g p γ₀ b₀ hbase))
    exact relChainsMapOf_isIso_range (X := TopCat.of (Work.StemsB.Pullback g p))
      (Y := TopCat.of E)
      ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
      (TopCat.ofHom (Work.StemsB.pullbackSnd g p)) (fibrePairMap g p γ₀ b₀ hbase)
      (fibrePairMap_comp g p γ₀ b₀ hbase) i hf hg'
  · -- `Γ ×_B E` is empty; then so is `E`
    haveI hX : IsEmpty (Work.StemsB.Pullback g p) := not_nonempty_iff.mp hne
    haveI hE : IsEmpty E := by
      rcases isEmpty_or_nonempty E with h | h
      · exact h
      · exact absurd (by
          obtain ⟨e⟩ := h
          obtain ⟨γ⟩ := (inferInstance : Nonempty Γ)
          obtain ⟨e', he'⟩ := exists_preimage_of_isSerreFibration p hp hB e (g γ)
          exact ⟨(γ, e'), he'.symm⟩) hne
    have hA : (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)
        = (∅ : Set (Work.StemsB.Pullback g p)) :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hX.false x)
    have hC : p ⁻¹' ({b₀} : Set B) = (∅ : Set E) :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hE.false x)
    have hz1 : IsZero ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))).homology i) := by
      rw [hA]
      haveI := Work.Cohomology.relChains_empty_homology_iso
        (TopCat.of (Work.StemsB.Pullback g p)) i
      exact IsZero.of_iso
        (Work.Cohomology.isZero_singularChains_homology_of_isEmpty
          (TopCat.of (Work.StemsB.Pullback g p)) i)
        (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p)) ∅)) i)).symm
    have hz2 : IsZero ((Work.Cohomology.relChains (TopCat.of E)
        (p ⁻¹' ({b₀} : Set B))).homology i) := by
      rw [hC]
      haveI := Work.Cohomology.relChains_empty_homology_iso (TopCat.of E) i
      exact IsZero.of_iso
        (Work.Cohomology.isZero_singularChains_homology_of_isEmpty (TopCat.of E) i)
        (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of E) ∅)) i)).symm
    exact IsZero.isIso hz1 hz2 _

end

end Work.Serre.Assembly

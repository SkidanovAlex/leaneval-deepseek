import Mathlib
import Submission.Work.Serre.ratPairInputs
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.SPC.pullbackPairComparison
import Submission.Work.Serre.SPC.pbHelpers
import Submission.Work.Serre.OneCell.RatMap
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_bijective
import Submission.Work.Serre.Assembly.pullbackSnd_piMapN_zero_bijective
import Submission.Work.Serre.Assembly.pullbackPairMap_isIso
import Submission.Work.Cohomology.relChains_empty_homology_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational pullback comparison (base change) of a Serre fibration

`Work.Serre.RatPullbackComparison` is the base-change comparison over `ℚ`: if `g : Γ → B` is
bijective on `π_i` for every `i ≤ N` and `p : E → B` is a Serre fibration, then the map of pairs

  `(Γ ×_B E, q⁻¹{γ₀}) → (E, p⁻¹{b₀})`

induced by the second projection of the fibre product is an isomorphism on rational homology in
degrees `< N`.

Unlike the integral counterpart (`Work.Serre.SPC.pullbackPairComparison`), the statement carries
**no** path-connectedness hypotheses, so the proof cannot use the path-connected special case of
the `π₀`-case of the base change; the two ingredients that replace it are

* `pullbackSnd_piMapN_zero_bijective_of_h0Pi0` — the `π₀`-bijectivity of the base change from the
  `π₀`- and `π₁`-bijectivity of `g` alone (via the `π₀`-injectivity giving the path in `Γ`), and
* the sharp rational `K2` (`Work.Serre.serreK2`) together with the five lemma for a map of pairs
  over `ℚ` (`Work.Serre.OneCell.isIso_homologyMap_relChainsRMapOf_range`).

The empty case (`E = ∅`) is handled separately, where both relative chain complexes have vanishing
homology.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The `π₀`-case of the base change without path-connectedness -/

/-- If `g` is injective on `π₀`, then `γ` and `γ'` are joined as soon as their images under `g`
are. -/
theorem joined_of_joined_map {Γ B : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    (g : C(Γ, B)) (hinj : Function.Injective (Work.Serre.h0Pi0Map g))
    {γ γ' : Γ} (h : Joined (g γ) (g γ')) : Joined γ γ' := by
  obtain ⟨p⟩ := h
  have h2 : Work.Serre.h0Pi0Map g (ZerothHomotopy.mk γ)
      = Work.Serre.h0Pi0Map g (ZerothHomotopy.mk γ') := by
    rw [Work.Serre.h0Pi0Map_mk, Work.Serre.h0Pi0Map_mk]
    exact ZerothHomotopy.sound p
  exact Quotient.exact (hinj h2)

/-- **The `π₀`-case of the base change**, with no path-connectedness hypothesis: if `g` is
bijective on `π₀` and on `π₁` and `p` is a Serre fibration, then `pullbackSnd g p` is bijective on
`π₀`.

Surjectivity: given `e : E`, choose `γ` with `g γ` joined to `p e` (π₀-surjectivity of `g`) and
lift a path from `p e` to `g γ` starting at `e` (path lifting for `p`); the endpoint `e'` then
satisfies `p e' = g γ`, so `(γ, e')` is a point of the fibre product joined to `e`.

Injectivity: if `e` and `e'` are joined in `E`, then `p e = g γ` and `p e' = g γ'` are joined in
`B` (project a path); π₀-injectivity of `g` produces a path `γ ⤳ γ'` in `Γ`, and then
`Work.Serre.Assembly.joined_pullbackSnd` lifts it along `p` using `π₁`-surjectivity. -/
theorem pullbackSnd_piMapN_zero_bijective_of_h0Pi0 {Γ B E : Type} [TopologicalSpace Γ]
    [TopologicalSpace B] [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p)
    (hg0 : Function.Bijective (Work.Serre.h0Pi0Map g))
    (hg1 : ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g 1 x)) :
    ∀ x : Work.StemsB.Pullback g p,
      Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) 0 x) := by
  classical
  have hsurj : ∀ e : E, ∃ y : Work.StemsB.Pullback g p,
      Joined (Work.StemsB.pullbackSnd g p y) e := by
    intro e
    obtain ⟨c, hc⟩ := hg0.2 (ZerothHomotopy.mk (p e))
    obtain ⟨γ, rfl⟩ := ZerothHomotopy.mk_surjective c
    rw [Work.Serre.h0Pi0Map_mk] at hc
    obtain ⟨pp⟩ : Joined (g γ) (p e) := Quotient.exact hc
    obtain ⟨e', he', ⟨α⟩⟩ :=
      Work.Serre.exists_path_lift_of_isSerreFibration p hp (e := e) rfl pp.symm
    exact ⟨⟨(γ, e'), he'.symm⟩, ⟨α.symm⟩⟩
  have hinj : ∀ x x' : Work.StemsB.Pullback g p,
      Joined (Work.StemsB.pullbackSnd g p x) (Work.StemsB.pullbackSnd g p x') →
        Joined x x' := by
    intro x x' hj
    refine Work.Serre.Assembly.joined_pullbackSnd g p hp x.2 x'.2 ?_ (hg1 x.1.1).2 hj
    refine joined_of_joined_map g hg0.1 ?_
    obtain ⟨α⟩ := hj
    exact ⟨(α.map p.continuous).cast x.2 x'.2⟩
  have key : Function.Bijective (Work.Serre.h0Pi0Map (Work.StemsB.pullbackSnd g p)) :=
    ⟨Work.Serre.Assembly.injective_h0Pi0Map_of_joined _ hinj,
      Work.Serre.Assembly.surjective_h0Pi0Map_of_joined _ hsurj⟩
  intro x
  exact (Work.Serre.Assembly.bijective_piMapN_zero_iff_h0Pi0Map _ x).mpr key

/-! ## The vanishing of the relative rational homology of an empty ambient space -/

/-- The singular `n`-simplices of an empty space form an empty type (a singular simplex is a
continuous map from the nonempty standard `n`-simplex into the empty space). -/
theorem isEmpty_singularSimplex_rat_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquivOld Y (Opposite.op (SimplexCategory.mk n))) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop
    (Opposite.op (SimplexCategory.mk n))).len + 1)))) := inferInstance
  exact isEmptyElim (hx (Classical.arbitrary _))

/-- The `n`-th term of the rational singular chain complex of an empty space is a zero object: it
is a coproduct indexed by the (empty) type of singular `n`-simplices. -/
theorem isZero_singularChains_rat_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℚ Y).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) :=
    isEmpty_singularSimplex_rat_of_isEmpty Y n
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) => ModuleCat.of ℚ ℚ)

/-- A chain complex whose `m`-th term is the zero object has vanishing `m`-th homology. -/
theorem isZero_homology_rat_of_isZero_X {K : ChainComplex (ModuleCat ℚ) ℕ} (m : ℕ)
    (h : IsZero (K.X m)) : IsZero (K.homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact CategoryTheory.ShortComplex.exact_of_isZero_X₂ _ h

/-- **The relative rational homology of an empty ambient space vanishes** in every degree: both the
space and the subspace have vanishing rational chains. -/
theorem isZero_relChainsR_rat_homology_of_isEmpty (X : TopCat) [IsEmpty (↥X)] (i : ℕ) :
    IsZero ((Work.StemsB.relChainsR ℚ X (∅ : Set X)).homology i) := by
  have hzero : Work.StemsB.relChainsRIncl ℚ X (∅ : Set X) = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.zero_f]
    exact (isZero_singularChains_rat_of_isEmpty (TopCat.of (∅ : Set X)) n).eq_zero_of_src _
  haveI : IsIso (CategoryTheory.Limits.cokernel.π
      (Work.StemsB.relChainsRIncl ℚ X (∅ : Set X))) :=
    CategoryTheory.Limits.cokernel.π_of_zero hzero
  exact IsZero.of_iso
    (isZero_homology_rat_of_isZero_X i (isZero_singularChains_rat_of_isEmpty X i))
    (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
      (Work.StemsB.relChainsRIncl ℚ X (∅ : Set X))) i)).symm

/-! ## The target -/

theorem ratPullbackComparison : Work.Serre.RatPullbackComparison := by
  intro Γ B E _ _ _ g p γ₀ b₀ hbase hp N hg i hi
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exact absurd hi (by omega)
  have hg0 : Function.Bijective (Work.Serre.h0Pi0Map g) :=
    Work.Serre.h0Pi0Map_bijective g (hg 0 (by omega) γ₀)
  by_cases hne : Nonempty (Work.StemsB.Pullback g p)
  · haveI : Nonempty (Work.StemsB.Pullback g p) := hne
    have hz : ∀ x : Work.StemsB.Pullback g p,
        Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) 0 x) :=
      pullbackSnd_piMapN_zero_bijective_of_h0Pi0 g p hp hg0 (fun x => hg 1 (by omega) x)
    have hf : ∀ k : ℕ, k ≤ i → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
          (TopCat.ofHom (Work.StemsB.pullbackSnd g p))) k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact Work.Serre.hZeroOfPiZero (Work.StemsB.pullbackSnd g p) hz
      · exact Work.Serre.serreK2 (Work.StemsB.Pullback g p) E
          (Work.StemsB.pullbackSnd g p) (k + 1) (fun j hj x => by
            rcases Nat.eq_zero_or_pos j with hj0 | hjpos
            · subst hj0
              exact hz x
            · exact Work.Serre.Assembly.pullbackSnd_piMapN_bijective g p hp N hg
                j hjpos (by omega) x)
          k (by omega)
    have hsub : ∀ k : ℕ, k ≤ i → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℚ
          (TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of (p ⁻¹' ({b₀} : Set B)))
          (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase)) k) := by
      intro k _
      haveI : CategoryTheory.IsIso (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase) :=
        Work.Serre.Assembly.isIso_fibrePairMap g p γ₀ b₀ hbase
      exact Work.Serre.OneCell.isIso_homologyMap_chainMap_of_isIso _ k
    have hmap : Work.Serre.pullbackPairMapRat g p γ₀ b₀ hbase =
        Work.Serre.relChainsRMapOf (R := ℚ) (TopCat.of (Work.StemsB.Pullback g p))
          (TopCat.of E)
          ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
          (TopCat.ofHom (Work.StemsB.pullbackSnd g p))
          (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase)
          (Work.Serre.Assembly.fibrePairMap_comp g p γ₀ b₀ hbase) := rfl
    rw [hmap]
    exact Work.Serre.OneCell.isIso_homologyMap_relChainsRMapOf_range _ _ _ _
      (Work.Serre.Assembly.fibrePairMap_comp g p γ₀ b₀ hbase) i hf hsub
  · haveI hX : IsEmpty (Work.StemsB.Pullback g p) := not_nonempty_iff.mp hne
    -- `E` is empty as well: a path lift along the fibration `p` would produce a point of `Γ ×_B E`
    haveI hE : IsEmpty E := by
      refine ⟨fun e => ?_⟩
      obtain ⟨c, hc⟩ := hg0.2 (ZerothHomotopy.mk (p e))
      obtain ⟨γ, rfl⟩ := ZerothHomotopy.mk_surjective c
      rw [Work.Serre.h0Pi0Map_mk] at hc
      obtain ⟨pp⟩ : Joined (g γ) (p e) := Quotient.exact hc
      obtain ⟨e', he', -⟩ :=
        Work.Serre.exists_path_lift_of_isSerreFibration p hp (e := e) rfl pp.symm
      exact hX.false ⟨(γ, e'), he'.symm⟩
    have hA : (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)
        = (∅ : Set (Work.StemsB.Pullback g p)) :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hX.false x)
    have hC : p ⁻¹' ({b₀} : Set B) = (∅ : Set E) :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hE.false x)
    have hz1 : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))).homology i) := by
      rw [hA]
      exact isZero_relChainsR_rat_homology_of_isEmpty (TopCat.of (Work.StemsB.Pullback g p)) i
    have hz2 : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E)
        (p ⁻¹' ({b₀} : Set B))).homology i) := by
      rw [hC]
      exact isZero_relChainsR_rat_homology_of_isEmpty (TopCat.of E) i
    exact IsZero.isIso hz1 hz2 _

end

end Work.Serre

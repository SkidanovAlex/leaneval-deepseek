import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Serre.Assembly.hZeroOfPiZeroInt
import Submission.Work.Pi6.SRANGE.BaseChange
import Submission.Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap
import Submission.Work.Cohomology.singularChains_free
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMODD

noncomputable section

/-- The integral homology isomorphism in a range, in the `hmap` language. -/
theorem isIso_hmap_int {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (N j : ℕ) (hj : j < N)
    (h : ∀ i : ℕ, i < N → ∀ x : X, Function.Bijective (Work.Serre.piMapN f i x)) :
    IsIso (Work.Pi6.hmap ℤ f j) := by
  rcases Nat.eq_zero_or_pos j with hjz | hjpos
  · subst hjz
    exact Work.Serre.Assembly.hZeroOfPiZeroInt f (h 0 (by omega))
  · exact Work.Serre.Assembly.serreK2IntSharp f N h j hjpos hj

/-- Torsion-freeness of the integral singular chains. -/
theorem isTorsionFree_singularChains (X : Type) [TopologicalSpace X] (i : ℕ) :
    Module.IsTorsionFree ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).X i) := by
  haveI : Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).X i) :=
    Work.Cohomology.singularChains_free (TopCat.of X) i
  infer_instance


/-- **A `π`-isomorphism in a range transfers vanishing of mod-`𝕜` homology.** If `f : X → Y` is a bijection on `π_i` at every base point for all `i < N`, and the mod-`𝕜` homology of `Y` vanishes in degrees `0 < i < N`, then so does that of `X`. (`X` is assumed nonempty, as the integral range Whitehead theorem `Work.Serre.Assembly.serreK2IntSharp` requires.)

(Route: `Work.Serre.Assembly.serreK2IntSharp` gives an isomorphism on *integral* homology in degrees `0 < i < N` (degree `0` from `Work.Serre.Assembly.hZeroOfPiZeroInt`); `Work.Pi6.SRANGE.BaseChange` identifies the base change of the integral singular chain complex with the singular chain complex with coefficients in `𝕜`, naturally, and `Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap` (applied to the chain map, whose complexes are degreewise free, hence torsion free) shows that the base change of an isomorphism on homology below `N` is again an isomorphism below `N`; finally a vanishing integral homology group base-changes to a vanishing one.) -/
theorem piIsoTransfer (𝕜 : Type) [Field 𝕜] (N : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] (f : C(X, Y))
    (h : ∀ i : ℕ, i < N → ∀ x : X, Function.Bijective (Work.Serre.piMapN f i x))
    (hY : ∀ i : ℕ, 0 < i → i < N → Subsingleton (Work.Pi6.HR 𝕜 Y i)) :
    ∀ i : ℕ, 0 < i → i < N → Subsingleton (Work.Pi6.HR 𝕜 X i) := by
  intro i hi0 hiN
  -- the induced map of simplicial sets
  have hBC : IsIso (HomologicalComplex.homologyMap
      (Work.Pi6.SRANGE.baseChangeMap 𝕜 (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) Work.Pi6.SRANGE.ZModZ)) i) :=
    Work.Pi6.SRANGE.isIso_homologyMap_baseChangeMap 𝕜 _ _ _ N
      (fun j => isTorsionFree_singularChains X j)
      (fun j => isTorsionFree_singularChains Y j)
      (fun j hj => isIso_hmap_int f N j hj h) i hiN
  -- naturality of the base change comparison
  obtain ⟨e, he⟩ := Work.Pi6.SRANGE.BaseChange 𝕜
  have hnat := congrArg (fun (g : Work.Pi6.SRANGE.baseChange 𝕜
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex Work.Pi6.SRANGE.ZModZ) ⟶
      (TopCat.toSSet.obj (TopCat.of Y)).chainComplex (Work.Pi6.SRANGE.RMod 𝕜)) =>
      HomologicalComplex.homologyMap g i)
    (he (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSet.map (TopCat.ofHom f)))
  simp only [HomologicalComplex.homologyMap_comp] at hnat
  haveI hXiso : IsIso (HomologicalComplex.homologyMap
      (e (TopCat.toSSet.obj (TopCat.of X))).hom i) :=
    (HomologicalComplex.homologyMapIso (e _) i).isIso_hom
  haveI hYiso : IsIso (HomologicalComplex.homologyMap
      (e (TopCat.toSSet.obj (TopCat.of Y))).hom i) :=
    (HomologicalComplex.homologyMapIso (e _) i).isIso_hom
  have hgoal : IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (Work.Pi6.SRANGE.RMod 𝕜)) i) := by
    have hmain : HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
          (Work.Pi6.SRANGE.RMod 𝕜)) i
        = CategoryTheory.inv (HomologicalComplex.homologyMap
            (e (TopCat.toSSet.obj (TopCat.of X))).hom i)
          ≫ HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap 𝕜
              (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
                Work.Pi6.SRANGE.ZModZ)) i
          ≫ HomologicalComplex.homologyMap
              (e (TopCat.toSSet.obj (TopCat.of Y))).hom i := by
      rw [← hnat]
      rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [hmain]
    infer_instance
  -- transfer the vanishing
  haveI : IsIso (Work.Pi6.hmap 𝕜 f i) := hgoal
  haveI := hY i hi0 hiN
  have hbij := ConcreteCategory.bijective_of_isIso (Work.Pi6.hmap 𝕜 f i)
  exact ⟨fun a b => hbij.1 (Subsingleton.elim _ _)⟩

end

end Work.Pi6.EMODD

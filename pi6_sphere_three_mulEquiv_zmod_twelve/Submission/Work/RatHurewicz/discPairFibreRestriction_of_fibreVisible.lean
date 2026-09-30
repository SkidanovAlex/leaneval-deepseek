import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.StemsB.PairDeltaNaturalR
import Submission.Work.StemsB.RelChainsR
import Submission.Work.RatHurewicz.Dfr.Defs
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.Basic
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.punit
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.DiscPair.fibreConeLine
import Submission.Work.Serre.DiscPair.cellStepPairKernel
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat

/-!
# The fibrewise restriction of the relative Thom class: the visible case

`Work.RatHurewicz.discPairFibreRestriction_of_fibreVisible` is the *fibre-visible* case of the
fibrewise non-vanishing of the relative Thom class of a Serre fibration whose fibres are rationally
`r`-spheres.  If some class `x ∈ H^r(E;ℚ)` restricts non-trivially to the fibre over `b` (`hvis`),
then the restriction of the relative cohomology of the mapping-cylinder pair to the fibre-cone pair,

`H^{r+1}(cyl q, range (cylIncl q); ℚ) ⟶ H^{r+1}((cylRetract q)⁻¹{b}, ·; ℚ)`,

is surjective.

The argument is a single application of the long exact sequence of the pair
`(cyl q, range (cylIncl q))`, together with three observations.

* **The target is a line.**  The preimage of `b` under `cylRetract q` is the cone on the fibre
  `F := q⁻¹{b}` with base the bottom copy of `F` (`Dfr.conePairShift`), so the pair cohomology in
  degree `r + 1` is the reduced homology of the fibre, shifted: `≅ H_r(F;ℚ) ≅ ℚ`
  (`Dfr.fibrePairLine`).  Hence a non-zero map into it is surjective
  (`Dfr.surjective_of_ne_zero_of_line`).
* **The connecting map is injective.**  The cone is contractible, so `H^r` of the cone vanishes and
  the connecting map of the fibre-cone pair embeds `H^r(fibre)` into `H^{r+1}(cone, fibre)`.
* **Kernel classes are pulled back from the base.**  By exactness of the pair sequence, a class in
  the kernel of the connecting map of `(cyl q, range (cylIncl q))` is the restriction of a class on
  `cyl q`, and since `cylRetract q` is a homotopy equivalence (`Dfr.isIso_CohMap_cylRetract`) it is
  the pullback along `cylRetract q`.  Such a class restricts to `0` on every fibre, because `q`
  restricted to a fibre is constant and the pullback along a constant map vanishes in positive
  degrees (`Dfr.CohMap_const_eq_zero`).

So a class with non-zero fibre restriction has non-zero connecting image, whose restriction to the
fibre-cone pair is `δ` of a non-zero class, whence non-zero.

**Note.**  The Thom isomorphism `IH` and the vanishing hypotheses `hvan` are not used: beyond the
fibre being a rational `r`-sphere, the only hypothesis is the visibility of the fibre (`hvis`).
This is the precise sense in which the whole content of the CW-model Thom case lies in the
*invisible* (non-trivial monodromy) case.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.RatHurewicz

open CategoryTheory

noncomputable section

namespace Dfr

/-! ## Elementary auxiliary lemmas -/

/-- The pullback along a homeomorphism is an isomorphism of singular cohomology. -/
theorem isIso_CohMap_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (n : ℕ) : IsIso (Work.Thom.CohMap (φ : C(X, Y)) ℚ n) := by
  refine IsIso.mk ⟨Work.Thom.CohMap (φ.symm : C(Y, X)) ℚ n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp]
    rw [show (φ : C(X, Y)).comp (φ.symm : C(Y, X)) = ContinuousMap.id Y from
      ContinuousMap.ext fun y => φ.apply_symm_apply y]
    exact Work.Thom.CohMap_id (B := Y) ℚ n
  · rw [← Work.Thom.CohMap_comp]
    rw [show (φ.symm : C(Y, X)).comp (φ : C(X, Y)) = ContinuousMap.id X from
      ContinuousMap.ext fun x => φ.symm_apply_apply x]
    exact Work.Thom.CohMap_id (B := X) ℚ n

/-- The push-up homotopy of the mapping cylinder, from `cylInr q ∘ cylRetract q` to the identity. -/
theorem cylInr_comp_cylRetract_homotopic {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (q : C(E, B)) : ((Work.Serre.cylInr q).comp (Work.Serre.cylRetract q)).Homotopic
      (ContinuousMap.id (Work.Serre.cyl q)) :=
  ⟨{ toContinuousMap :=
        ⟨fun p : unitInterval × Work.Serre.cyl q =>
            Work.Serre.cylMove q (p.2, Work.Serre.unitIntervalOneSub p.1),
          (Work.Serre.cylMove q).continuous.comp
            (continuous_snd.prodMk
              (Work.Serre.continuous_unitIntervalOneSub.comp continuous_fst))⟩,
      map_zero_left := fun y => by simp [Work.Serre.cylMove_one],
      map_one_left := fun y => by simp [Work.Serre.cylMove_zero] }⟩

/-- The pullback along the retraction of a mapping cylinder is an isomorphism. -/
theorem isIso_CohMap_cylRetract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (q : C(E, B)) (n : ℕ) : IsIso (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ n) := by
  have hleft := cylInr_comp_cylRetract_homotopic q
  have hcomp : (Work.Serre.cylRetract q).comp (Work.Serre.cylInr q) = ContinuousMap.id B :=
    ContinuousMap.ext fun x => rfl
  refine IsIso.mk ⟨Work.Thom.CohMap (Work.Serre.cylInr q) ℚ n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp, hcomp]
    exact Work.Thom.CohMap_id (B := B) ℚ n
  · rw [← Work.Thom.CohMap_comp, Work.Thom.CohMap_homotopic hleft ℚ n]
    exact Work.Thom.CohMap_id (B := Work.Serre.cyl q) ℚ n

/-- The two inverse identities of an isomorphism in `ModuleCat ℚ`. -/
theorem iso_hom_inv_apply {M N : ModuleCat ℚ} (e : M ≅ N) (y : ↥N) :
    e.hom.hom (e.inv.hom y) = y := by
  have h := congrArg (fun (φ : N ⟶ N) => φ.hom y) (Iso.inv_hom_id e)
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h

theorem iso_inv_hom_apply {M N : ModuleCat ℚ} (e : M ≅ N) (x : ↥M) :
    e.inv.hom (e.hom.hom x) = x := by
  have h := congrArg (fun (φ : M ⟶ M) => φ.hom x) (Iso.hom_inv_id e)
  simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using h

/-- The underlying linear map of an isomorphism of `ModuleCat`s is injective. -/
theorem injective_hom_of_iso {M N : ModuleCat ℚ} (e : M ≅ N) :
    Function.Injective e.hom.hom := by
  intro x y hxy
  rw [← iso_inv_hom_apply e x, ← iso_inv_hom_apply e y, hxy]

/-- A non-zero linear map into `ℚ` is surjective. -/
theorem surjective_rat_of_ne_zero {M : ModuleCat ℚ} (f : M ⟶ ModuleCat.of ℚ ℚ)
    (hf : f.hom ≠ 0) : Function.Surjective f.hom := by
  obtain ⟨m, hm⟩ : ∃ m : ↥M, f.hom m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  intro y
  refine ⟨(y * (f.hom m)⁻¹) • m, ?_⟩
  rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hm, mul_one]

/-- A non-zero linear map into a module isomorphic to `ℚ` is surjective. -/
theorem surjective_of_ne_zero_of_line {M N : ModuleCat ℚ} (f : M ⟶ N) (hf : f.hom ≠ 0)
    (e : N ≅ ModuleCat.of ℚ ℚ) : Function.Surjective f.hom := by
  have hinj : Function.Injective e.hom.hom := injective_hom_of_iso e
  have hg : (f ≫ e.hom).hom ≠ 0 := by
    intro h0
    apply hf
    apply LinearMap.ext
    intro m
    have hm : e.hom.hom (f.hom m) = 0 := by
      have h := LinearMap.congr_fun h0 m
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.zero_apply] using h
    simpa using hinj (by rw [hm, map_zero])
  intro y
  obtain ⟨m, hm⟩ := surjective_rat_of_ne_zero (f ≫ e.hom) hg (e.hom.hom y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hm
  exact ⟨m, hinj hm⟩

/-- The pullback along a constant map vanishes in positive degree. -/
theorem CohMap_const_eq_zero {F B : Type} [TopologicalSpace F] [TopologicalSpace B]
    [Nonempty F] (b : B) (n : ℕ) (hn : 0 < n) :
    Work.Thom.CohMap (⟨fun _ : F => b, continuous_const⟩ : C(F, B)) ℚ n = 0 := by
  have hfac : (⟨fun _ : F => b, continuous_const⟩ : C(F, B))
      = (⟨fun _ : PUnit => b, continuous_const⟩ : C(PUnit, B)).comp
        (⟨fun _ : F => PUnit.unit, continuous_const⟩ : C(F, PUnit)) := rfl
  rw [hfac, Work.Thom.CohMap_comp]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  apply LinearMap.ext
  intro y
  haveI : Subsingleton ↥(Work.Thom.Coh ℚ n PUnit) := by
    refine ModuleCat.isZero_iff_subsingleton.mp ?_
    have h := Work.Cohomology.punit ℚ (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have hy : ((Work.Thom.CohMap (⟨fun _ : PUnit => b, continuous_const⟩ : C(PUnit, B)) ℚ n).hom y)
      = 0 := Subsingleton.elim _ _
  simp only [LinearMap.comp_apply, hy, map_zero, LinearMap.zero_apply]

/-- **The homological cone pair of the fibre of the mapping-cylinder retraction.**

For a continuous map `q : C(E,B)`, a point `b : B` and `k ≥ 1`, the pair

`P := (cylRetract q) ⁻¹' {b}`,   `A := P ∩ range (cylIncl q)`

is the cone on the fibre `F := q ⁻¹'{b}` with base the bottom copy of the fibre, so that

`H_k(P, A; ℚ) ≅ H_{k-1}(F, {b₀}; ℚ)`,

the reduced homology of the fibre shifted by one.  This is
`Work.RatHurewicz.relChainsR_conePair_iso_of_point`, re-proved here so that the present module keeps
a dependency set compatible with the `E3bBridge` import island. -/
theorem conePairShift {B E : Type} [TopologicalSpace B] [TopologicalSpace E]
    (q : C(E, B)) (b : B) (b₀ : Work.StemsB.fibre q b) (k : ℕ) (hk : 1 ≤ k) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {b}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology k
      ≅ (Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.fibre q b)) {b₀}).homology (k - 1)) := by
  classical
  let P : Set (Work.Serre.cyl q) := (Work.Serre.cylRetract q) ⁻¹' {b}
  let A : Set ↥P := {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
  let a : ↥P := ⟨Work.Serre.cylIncl q b₀.1, by
    show (Work.Serre.cylRetract q) (Work.Serre.cylIncl q b₀.1) = b
    exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) b₀.1).trans b₀.2⟩
  have ha : a ∈ A := ⟨b₀.1, rfl⟩
  haveI hcontr : ContractibleSpace ↥P := Work.Serre.DiscPair.cylRetractPreimageContractible q b
  obtain ⟨iso₁⟩ := Work.Serre.DiscPair.conePairIso (TopCat.of ↥P) A a ha k hk
  obtain ⟨e, he⟩ := Work.Serre.DiscPair.baseHomeoFibreGen q b b₀ a ha rfl
  have he' : ∀ x : ↥A, x ∈ ({⟨a, ha⟩} : Set ↥A) ↔
      e x ∈ ({b₀} : Set (Work.StemsB.fibre q b)) := by
    intro x
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => by rw [hx]; exact he, fun hx => e.injective (hx.trans he.symm)⟩
  obtain ⟨iso₂⟩ := Work.Serre.CsrSharp.relChainsRHomeomorphCompat ↥A (Work.StemsB.fibre q b)
    {⟨a, ha⟩} {b₀} e he' (k - 1)
  exact ⟨iso₁ ≪≫ iso₂⟩

/-- **The relative cohomology of the fibre cone pair is a line.**  For `r ≥ 1` and a fibre
`F := q⁻¹{b}` which is path connected with `H_r(F;ℚ) ≅ ℚ`, the relative cohomology of the cone pair
`(P, A)` above is `H^{r+1}(P,A;ℚ) ≅ ℚ`. -/
theorem fibrePairLine {B E : Type} [TopologicalSpace B] [TopologicalSpace E]
    (q : C(E, B)) (b : B) (r : ℕ) (hr : 1 ≤ r)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) ↥((Work.Serre.cylRetract q) ⁻¹' {b})
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      ≅ ModuleCat.of ℚ ℚ) := by
  classical
  let P : Set (Work.Serre.cyl q) := (Work.Serre.cylRetract q) ⁻¹' {b}
  let A : Set ↥P := {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
  obtain ⟨b₀⟩ := hpc.nonempty
  obtain ⟨iso₁⟩ := conePairShift q b b₀ (r + 1) (by omega)
  obtain ⟨iso₃⟩ := Work.Serre.DiscPair.nonempty_abs_iso_rel_singleton
    (Work.StemsB.fibre q b) b₀ r hr
  obtain ⟨iso₄⟩ := hgen
  refine Work.Serre.DiscPair.nonempty_relCoh_iso_of_relH_line A (r + 1) ?_
  exact ⟨iso₁ ≪≫ iso₃.symm ≪≫ iso₄⟩

end Dfr

/-- **The fibrewise restriction of the relative class when the fibre is visible.**

For a continuous map `q : E → B`, a point `b : B` whose fibre is path connected with
`H_r(F;ℚ) ≅ ℚ` (`r ≥ 1`), and a class `x ∈ H^r(E;ℚ)` restricting non-trivially to the fibre
(`hvis`), the restriction

`H^{r+1}(cyl q, range (cylIncl q); ℚ) ⟶ H^{r+1}((cylRetract q)⁻¹{b}, ·)`

is surjective.  The point is that a class in the kernel of `H^r(range (cylIncl q)) → H^{r+1}`
is pulled back from `B`, hence restricts to `0` on the fibre, because `q` restricted to the fibre
is constant. -/
theorem Dfr.surjective_relCohMap_fibre_of_visible {B E : Type} [TopologicalSpace B]
    [TopologicalSpace E]
    (q : C(E, B)) (b : B) (r : ℕ) (hr : 1 ≤ r)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r ≅ ModuleCat.of ℚ ℚ))
    (hvis : (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Work.StemsB.fibre q b, E)) ℚ r).hom ≠ 0) :
    Function.Surjective (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)).hom := by
  classical
  haveI hne : Nonempty (Work.StemsB.fibre q b) := hpc.nonempty
  -- the visible class
  obtain ⟨x, hx⟩ : ∃ x : Work.Thom.Coh ℚ r E,
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Work.StemsB.fibre q b, E)) ℚ r).hom x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hvis (LinearMap.ext h)
  -- the homeomorphism `E ≃ₜ ↥(range (cylIncl q))`
  obtain ⟨e₀, he₀⟩ := Work.Serre.cylHomeoExplicit q
  have hbase : ∀ a : ↥(Set.range (Work.Serre.cylIncl q)),
      (Work.Serre.cylIncl q (e₀.symm a) : Work.Serre.cyl q) = (a : Work.Serre.cyl q) := by
    intro a
    have h := he₀ (e₀.symm a)
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm
  let φ : C(↥(Set.range (Work.Serre.cylIncl q)), E) := ⟨e₀.symm, e₀.symm.continuous⟩
  have hφ_iso : IsIso (Work.Thom.CohMap φ ℚ r) := Dfr.isIso_CohMap_homeo e₀.symm r
  let xA : Work.Thom.Coh ℚ r ↥(Set.range (Work.Serre.cylIncl q)) :=
    (Work.Thom.CohMap φ ℚ r).hom x
  -- the identification of the pullback along the inclusion with `i^*`
  have key1 : ∀ m : Work.Thom.Coh ℚ r (Work.Serre.cyl q),
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(Set.range (Work.Serre.cylIncl q)), Work.Serre.cyl q)) ℚ r).hom m
      = (Work.Thom.CohMap φ ℚ r).hom ((Work.Thom.CohMap (Work.Serre.cylIncl q) ℚ r).hom m) := by
    intro m
    have h := Work.Thom.CohMap_comp φ (Work.Serre.cylIncl q) ℚ r
    have hcomp : (Work.Serre.cylIncl q).comp φ
        = (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(Set.range (Work.Serre.cylIncl q)), Work.Serre.cyl q)) := by
      apply ContinuousMap.ext
      intro a
      exact hbase a
    rw [← hcomp, h, ModuleCat.hom_comp, LinearMap.comp_apply]
  -- `xA` is not in the range of the restriction `H^r(cyl q) → H^r(range (cylIncl q))`
  have key2 : (Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q)) r).hom xA ≠ 0 := by
    intro h0
    have hker := Work.StemsB.pairKer₃R ℚ (A := Set.range (Work.Serre.cylIncl q)) r
    have hmem : xA ∈ LinearMap.range ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Set.range (Work.Serre.cylIncl q)), Work.Serre.cyl q)) ℚ r).hom) := by
      have hmem' : xA ∈ LinearMap.range ((Work.Thom.CohMap
          (Work.Thom.subtypeMap (Set.range (Work.Serre.cylIncl q))) ℚ r).hom) := by
        rw [← hker]
        exact LinearMap.mem_ker.mpr h0
      exact hmem'
    obtain ⟨m, hm⟩ := hmem
    have hφinj : Function.Injective (Work.Thom.CohMap φ ℚ r).hom :=
      Dfr.injective_hom_of_iso (asIso (Work.Thom.CohMap φ ℚ r))
    have hxm : (Work.Thom.CohMap (Work.Serre.cylIncl q) ℚ r).hom m = x := by
      apply hφinj
      rw [← key1 m, hm]
    have hρ_iso : IsIso (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ r) :=
      Dfr.isIso_CohMap_cylRetract q r
    have hρsurj : Function.Surjective
        (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ r).hom := by
      intro z
      refine ⟨((asIso (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ r)).inv).hom z, ?_⟩
      exact Dfr.iso_hom_inv_apply (asIso (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ r)) z
    obtain ⟨y, hy⟩ := hρsurj m
    have hxq : x = (Work.Thom.CohMap q ℚ r).hom y := by
      rw [← hxm, ← hy]
      have h := Work.Thom.CohMap_comp (Work.Serre.cylIncl q) (Work.Serre.cylRetract q) ℚ r
      rw [Work.Serre.cylRetract_cylIncl q] at h
      rw [h, ModuleCat.hom_comp, LinearMap.comp_apply]
    refine hx ?_
    rw [hxq]
    have hqconst : q.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Work.StemsB.fibre q b, E))
        = (⟨fun _ : Work.StemsB.fibre q b => b, continuous_const⟩ :
            C(Work.StemsB.fibre q b, B)) := by
      apply ContinuousMap.ext
      intro z
      exact z.2
    have h2 : (Work.Thom.CohMap (q.comp (⟨Subtype.val, continuous_subtype_val⟩ :
          C(Work.StemsB.fibre q b, E))) ℚ r).hom y
        = (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
            C(Work.StemsB.fibre q b, E)) ℚ r).hom ((Work.Thom.CohMap q ℚ r).hom y) := by
      rw [Work.Thom.CohMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← h2, hqconst, Dfr.CohMap_const_eq_zero b r hr, ModuleCat.hom_zero,
      LinearMap.zero_apply]
  -- the explicit homeomorphism between the fibre pair and the fibre
  have keyfib : ∀ y : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)},
      q (e₀.symm ⟨y.1.1, y.2⟩) = b := by
    intro y
    have h2 : (Work.Serre.cylIncl q (e₀.symm ⟨y.1.1, y.2⟩) : Work.Serre.cyl q) = y.1.1 := by
      rw [← he₀ (e₀.symm ⟨y.1.1, y.2⟩), Homeomorph.apply_symm_apply]
    exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q)
        (e₀.symm ⟨y.1.1, y.2⟩)).symm.trans
      ((congrArg (Work.Serre.cylRetract q) h2).trans (Set.mem_singleton_iff.mp y.1.2))
  let Ψfun : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} → Work.StemsB.fibre q b :=
    fun y => ⟨e₀.symm ⟨y.1.1, y.2⟩, keyfib y⟩
  let Φfun : Work.StemsB.fibre q b → ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
    fun z => ⟨⟨Work.Serre.cylIncl q z.1, by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact (DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) z.1).trans z.2⟩,
      ⟨z.1, rfl⟩⟩
  have hΨΦ : ∀ y, Φfun (Ψfun y) = y := by
    intro y
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    show (Work.Serre.cylIncl q (e₀.symm ⟨y.1.1, y.2⟩) : Work.Serre.cyl q) = y.1.1
    rw [← he₀ (e₀.symm ⟨y.1.1, y.2⟩), Homeomorph.apply_symm_apply]
  have hΦΨ : ∀ z, Ψfun (Φfun z) = z := by
    intro z
    refine Subtype.ext ?_
    show (e₀.symm (⟨(Work.Serre.cylIncl q z.1 : Work.Serre.cyl q), ⟨z.1, rfl⟩⟩ :
      ↥(Set.range (Work.Serre.cylIncl q))) : E) = z.1
    rw [show (⟨(Work.Serre.cylIncl q z.1 : Work.Serre.cyl q), ⟨z.1, rfl⟩⟩ :
          ↥(Set.range (Work.Serre.cylIncl q))) = e₀ z.1 from
        Subtype.ext (he₀ z.1).symm, Homeomorph.symm_apply_apply]
  have hcontΨ : Continuous Ψfun :=
    Continuous.subtype_mk (e₀.symm.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)) _
  have hcontΦ : Continuous Φfun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((Work.Serre.cylIncl q).continuous.comp continuous_subtype_val) _) _
  let Ψ : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≃ₜ Work.StemsB.fibre q b :=
    Homeomorph.mk { toFun := Ψfun, invFun := Φfun, left_inv := hΨΦ, right_inv := hΦΨ }
      hcontΨ hcontΦ
  let Ψc : C(↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)},
      Work.StemsB.fibre q b) := (Ψ : C(↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}, Work.StemsB.fibre q b))
  have hΨcoe : ∀ z : ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)},
      (Ψc z).1 = e₀.symm ⟨z.1.1, z.2⟩ := fun z => rfl
  have hΨ_iso : IsIso (Work.Thom.CohMap Ψc ℚ r) := Dfr.isIso_CohMap_homeo Ψ r
  -- the restriction of `xA` to the fibre pair
  let j' : C(↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)},
      ↥(Set.range (Work.Serre.cylIncl q))) :=
    Dfr.mapsToRestrict (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun x hx => hx)
  let yA : Work.Thom.Coh ℚ r ↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
    (Work.Thom.CohMap j' ℚ r).hom xA
  -- naturality of `pairδ`
  have hnat := Work.StemsB.pairDeltaNaturalR ℚ
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
    {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
      (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
    (Set.range (Work.Serre.cylIncl q)) (fun x hx => hx) r xA
  -- `yA` is the image of `x` under the homeomorphism
  have hyA : yA = (Work.Thom.CohMap Ψc ℚ r).hom
      ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Work.StemsB.fibre q b, E)) ℚ r).hom x) := by
    have h1 : yA = (Work.Thom.CohMap (φ.comp j') ℚ r).hom x := by
      show (Work.Thom.CohMap j' ℚ r).hom ((Work.Thom.CohMap φ ℚ r).hom x) = _
      rw [Work.Thom.CohMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    have h2 : (φ.comp j' : C(↥{x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}, E))
        = (⟨Subtype.val, continuous_subtype_val⟩ :
            C(Work.StemsB.fibre q b, E)).comp Ψc := by
      apply ContinuousMap.ext
      intro z
      show e₀.symm (j' z) = (Ψc z).1
      rw [hΨcoe z]
      rfl
    rw [h1, h2, Work.Thom.CohMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hyA_ne : yA ≠ 0 := by
    rw [hyA]
    intro h0
    refine hx (Dfr.injective_hom_of_iso (asIso (Work.Thom.CohMap Ψc ℚ r)) ?_)
    show (Work.Thom.CohMap Ψc ℚ r).hom
        ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
          C(Work.StemsB.fibre q b, E)) ℚ r).hom x) =
      (Work.Thom.CohMap Ψc ℚ r).hom 0
    rw [h0, map_zero]
  -- the connecting map of the fibre cone pair is injective: its kernel is the range of the
  -- restriction `H^r(cone) → H^r(fibre)`, and the cone is contractible
  haveI hcontrMb : ContractibleSpace ↥((Work.Serre.cylRetract q) ⁻¹' {b}) :=
    Work.Serre.DiscPair.cylRetractPreimageContractible q b
  haveI hsubMb : Subsingleton
      ↥(Work.Thom.Coh ℚ r ↥((Work.Serre.cylRetract q) ⁻¹' {b})) := by
    refine ModuleCat.isZero_iff_subsingleton.mp ?_
    have h := Work.Cohomology.contractible ℚ
      (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {b})) (r - 1)
    rwa [Nat.sub_add_cancel hr] at h
  have hδb : (Work.Cohomology.pairδ ℚ (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {b}))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} r).hom yA ≠ 0 := by
    intro h0
    have hker := Work.StemsB.pairKer₃R ℚ (A := {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) r
    have hmem : yA ∈ LinearMap.range ((Work.Thom.CohMap (Work.Thom.subtypeMap
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) ℚ r).hom) := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr h0
    obtain ⟨z, hz⟩ := hmem
    have hz0 : (Work.Thom.CohMap (Work.Thom.subtypeMap
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) ℚ r).hom z = 0 := by
      rw [Subsingleton.elim z 0, map_zero]
    exact hyA_ne (by rw [← hz, hz0])
  -- the restriction map is non-zero, hence surjective
  have hjnz : (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)).hom ≠ 0 := by
    intro h0
    have h1 : (Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
        (Set.range (Work.Serre.cylIncl q))
        (fun x hx => hx) ℚ (r + 1)).hom
        ((Work.Cohomology.pairδ ℚ (TopCat.of (Work.Serre.cyl q))
          (Set.range (Work.Serre.cylIncl q)) r).hom xA) = 0 := by
      rw [h0]
      rfl
    rw [hnat] at h1
    exact hδb h1
  obtain ⟨eL⟩ := Dfr.fibrePairLine q b r hr hpc hgen
  exact Dfr.surjective_of_ne_zero_of_line _ hjnz eL

end

theorem discPairFibreRestriction_of_fibreVisible (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (q : C(E, B)) (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (IH : Work.Serre.ThomCylAt r N q) (b : B)
    (hvis : (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Work.StemsB.fibre q b, E)) ℚ r).hom ≠ 0) :
    Function.Surjective (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)).hom :=
  Dfr.surjective_relCohMap_fibre_of_visible q b r hr (hpc b) (hgen b) hvis

end Work.RatHurewicz

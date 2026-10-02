import Mathlib
import Submission.Work.RatHurewicz.Cofibre.StableRangeDefs
import Submission.Work.RatHurewicz.Cofibre.AssemblyDefs
import Submission.Work.RatHurewicz.Cofibre.coneMidHomotopyEquiv
import Submission.Work.RatHurewicz.Cofibre.pi_one_E_of_fibration
import Submission.Work.RatHurewicz.trackRelPiVanishing
import Submission.Work.Serre.piMap_fibreIncl_surjective_of_subsingleton
import Submission.Work.Serre.piMap_fibreIncl_surjective_pi1
import Submission.Work.Serre.attachIncl_const_piMapN_bijective
import Submission.Work.Serre.rwPiMapN_bijective_of_homotopyEquiv
import Submission.Work.StemsB.exists_lift_rel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative groups of the collar pair `(U, U∩V)`

This file proves `Work.RatHurewicz.Cofibre.subsingleton_relPi_interInclLeft_wide`, the `hvan`
hypothesis of `Work.RatHurewicz.Cofibre.subsingleton_relPi_cofibreV_of_blakersMassey`.

## The mathematical content

`U := cofibreU ι` is the half-open cone `{h < 1/2}` of the cofibre `C = cofibre ι = E ∪_F CF`
(`ι = setIncl F`, `F = p ⁻¹' {p e₀}`), `V := cofibreV ι` is the punctured cone `{0 < h}`, and
`U ∩ V` is the *collar* `{0 < h < 1/2}`.  The relative group
`RelHomotopyGroup (interInclLeft U V) x₀ J` is the classical `π_{J+1}(U, U∩V)`; since the pair map
`(U, U∩V) → (E, F)` (the retraction `cofibreURetract` on `U` and the "base of a cone point" on the
collar) is a map of pairs whose two components are homotopy equivalences, it is an isomorphism of
pairs and `π_{J+1}(U, U∩V) ≅ π_{J+1}(E, F) ≅ π_{J+1}(B)` — the latter by the long exact sequence of
the fibration `p`, so it vanishes by `hmodel` in the range `J + 1 ≤ 2k-1`, `J + 1 ≠ k`.

## The formal route

1. `cofibreURetract_eq_collarBase` (`AssemblyDefs.lean`) is the commuting square
   `ρ ∘ (U∩V ↪ U) = ι ∘ collarBase` on the collar;
2. `collarBase` is a homotopy equivalence (it is `coneMidProj ∘ collarToMid`, composed of the two
   homotopy equivalences `collarInterHE`/`collarMidHomotopyEquiv` and `coneMidHE`), and so is `ρ`
   (`cofibreUHomotopyEquiv`); `injective_πmap_commSquare` / `surjective_πmap_commSquare` (proved
   here) therefore transfer the injectivity of `π_J(F) → π_J(E)` and the surjectivity of
   `π_{J+1}(F) → π_{J+1}(E)` to the collar inclusion;
3. those two are read off the fibration LES: injectivity from
   `Work.RatHurewicz.injective_piMapN_fibreIncl_of_subsingleton` (exactness at `π_J(F)`, with
   `π_{J+1}(B)` a subsingleton by `hmodel`) and surjectivity from
   `Work.Serre.piMap_fibreIncl_surjective_of_subsingleton` (exactness at `π_{J+1}(E)`); in degree
   `J = 0` the surjectivity is `Work.Serre.piMap_fibreIncl_surjective_pi1` and the injectivity comes
   from the connectedness of `F`;
4. `Work.RatHurewicz.relPiVanishingOfPiInjSurj` converts the injected/surjected pair into the
   vanishing of the relative group of the inclusion, and
   `Work.RatHurewicz.subsingleton_relPi_of_homeo` transports it back from the `collarSet` model of
   the inclusion to `interInclLeft U V`.

Note that `cofibreURetract_eq_collarBase` takes `ι = setIncl F` for a *set* `F`, which is the form
in which the collar is presented in `AssemblyDefs.lean`; the two models of the collar (`↥(U∩V)` and
the subset `collarSet ι` of `↥U`) are exchanged by `interHomeo`/`collarInter`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Cofibre

noncomputable section

/-! ## Triviality of `π_0` and path connectedness -/

/-- **`π₀` of a space whose points are all joined by paths is trivial.** -/
theorem subsingleton_pi_zero_of_paths {X : Type} [TopologicalSpace X]
    (h : ∀ a b : X, Nonempty (Path a b)) (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) := by
  haveI : PathConnectedSpace X := ⟨⟨x⟩, h⟩
  have hZ : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective (hZ.elim _ _)⟩

/-- **Path connectedness transports backwards along a homotopy equivalence.** -/
theorem path_connected_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hY : ∀ a b : Y, Nonempty (Path a b)) :
    ∀ a b : X, Nonempty (Path a b) := by
  intro a b
  obtain ⟨γ⟩ := hY (e.toFun a) (e.toFun b)
  obtain ⟨H⟩ := e.left_inv
  have hA : Path (e.invFun (e.toFun a)) a :=
    ⟨⟨fun t => H (t, a), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left a, H.map_one_left a⟩
  have hB : Path (e.invFun (e.toFun b)) b :=
    ⟨⟨fun t => H (t, b), H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      H.map_zero_left b, H.map_one_left b⟩
  exact ⟨hA.symm.trans ((γ.map (f := ⇑e.invFun) e.invFun.continuous).trans hB)⟩

/-! ## The commuting square of the collar -/

/-- **The square of the collar, in the `collarSet` model**: on the collar the retraction
`cofibreURetract` is `ι` applied to the base of the cone point (`collarBase`). -/
theorem cofibreURetract_comp_setIncl_collarSet {E : Type} [TopologicalSpace E] (F : Set E)
    [Nonempty E] [Nonempty ↥F] (e₀ : E) :
    (cofibreURetract (setIncl F) e₀).comp (setIncl (collarSet (setIncl F)))
      = (setIncl F).comp (collarBase (setIncl F)) := by
  ext z
  exact cofibreURetract_eq_collarBase F e₀ z

/-- **The base of the collar point over `y` is `y`.**  This is the computation rule of the
projection `collarBaseMid = coneMidProj ∘ collarToMid` at the collar point
`collarPt ι y = [y, 1/4]`. -/
theorem collarBaseMid_collarPt {E : Type} [TopologicalSpace E] {F : Set E} [Nonempty ↥F]
    (y : ↥F) :
    collarBaseMid (setIncl F) (collarPt (setIncl F) y) = y := by
  have hstub : collarStub = coneQuarter := Subtype.ext rfl
  have hmemMid : coneMk (F := ↥F) (y, collarStub) ∈ midSet (F := ↥F) := by
    show (0 : unitInterval) < coneHeight (coneMk (F := ↥F) (y, collarStub)) ∧
      coneHeight (coneMk (F := ↥F) (y, collarStub)) < cofibreHalf
    rw [coneHeight_coneMk]
    exact ⟨collarStub_pos, collarStub_lt_half⟩
  have hmem : (Sum.inr (coneMk (F := ↥F) (y, collarStub)) : E ⊕ Work.Stems.Cone ↥F) ∈
      (Quotient.mk'' : E ⊕ Work.Stems.Cone ↥F → cofibre (setIncl F)) ⁻¹'
        (cofibreU (setIncl F) ∩ cofibreV (setIncl F)) := by
    rw [preimage_collar (setIncl F)]
    exact ⟨coneMk (F := ↥F) (y, collarStub), hmemMid, rfl⟩
  have hpt : collarPt (setIncl F) y =
      (⟨Quotient.mk'' (Sum.inr (coneMk (F := ↥F) (y, collarStub))), hmem⟩ :
        ↥(cofibreU (setIncl F) ∩ cofibreV (setIncl F))) := Subtype.ext rfl
  have hmid : collarToMid (setIncl F) (collarPt (setIncl F) y) = coneMidSec (F := ↥F) y := by
    rw [hpt, collarToMid_mk (setIncl F) (Sum.inr (coneMk (F := ↥F) (y, collarStub))) hmem,
      collarToMidRaw_inr (setIncl F) hmem rfl hmemMid]
    apply Subtype.ext
    show coneMk (F := ↥F) (y, collarStub) = coneMk (F := ↥F) (y, coneQuarter)
    rw [hstub]
  change coneMidProj (F := ↥F) (collarToMid (setIncl F) (collarPt (setIncl F) y)) = y
  rw [hmid]
  exact coneMidProj_coneMidMk (F := ↥F) ⟨(y, coneQuarter), coneMid_mem_sec (F := ↥F) y⟩

/-- **A homotopy equivalence induces bijections on homotopy groups**, in the indexing of
`Work.StemsB.πmap` (`πmap f m` acts on `π_{m+1}`).  This is
`Work.RatHurewicz.Cofibre.bijective_pimap_of_homotopyEquiv` (in `collapseAux.lean`), reproved here
through `Work.Serre.piMapN` so as not to depend on that module. -/
theorem bijective_pimap_of_homotopyEquiv' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (m : ℕ) (x : X) :
    Function.Bijective (Work.StemsB.πmap e.toFun m x) := by
  have h1 : Work.StemsB.πmap e.toFun m x = Work.Serre.piMapN e.toFun (m + 1) x := by
    rw [Work.Serre.piMapN_eq_pimap_succ]
  rw [h1, Work.Serre.piMapN_eq_homotopyGroupMap]
  exact Work.Serre.bijective_homotopyGroupMap_of_homotopyEquiv (Q := Fin (m + 1)) e x

/-- **`collarBase` is a homotopy equivalence**, hence induces bijections on all homotopy groups:
it is the composite of the two homotopy equivalences `collarInter` and
`collarBaseMid = coneMidProj ∘ collarToMid`. -/
theorem bijective_pimap_collarBase {E : Type} [TopologicalSpace E] {F : Set E} [Nonempty ↥F]
    (ι : C(↥F, E)) (n : ℕ) (z : ↥(collarSet ι)) :
    Function.Bijective (Work.StemsB.πmap (collarBase ι) n z) := by
  have hcomp : Work.StemsB.πmap (collarBase ι) n z
      = (Work.StemsB.πmap (collarBaseMid ι) n (collarInter ι z)).comp
        (Work.StemsB.πmap (collarInter ι) n z) := by
    ext w
    exact Work.StemsB.πmap_comp_apply (collarInter ι) (collarBaseMid ι) n z w
  rw [hcomp]
  exact (bijective_pimap_of_homotopyEquiv' ((collarMidHomotopyEquiv ι).trans (coneMidHE ↥F)) n
      (collarInter ι z)).comp (bijective_pimap_of_homotopyEquiv' (collarInterHE ι) n z)

/-! ## The transfer of injectivity/surjectivity along a commuting square -/

section square

variable {A₁ X₁ A₂ X₂ : Type*} [TopologicalSpace A₁] [TopologicalSpace X₁]
  [TopologicalSpace A₂] [TopologicalSpace X₂]

/-- The key compatibility of a commuting square with the induced maps on homotopy groups: the two
composites agree up to the base-point transport along the square. -/
theorem πmap_commSquare_cast (g₁ : C(A₁, X₁)) (g₂ : C(A₂, X₂)) (a : C(A₁, A₂)) (x : C(X₁, X₂))
    (hsq : x.comp g₁ = g₂.comp a) (n : ℕ) (α : A₁)
    (w : HomotopyGroup (Fin (n + 1)) A₁ α) :
    Work.StemsB.homotopyGroupCast (congrArg (fun k : C(A₁, X₂) => k α) hsq) n
        (Work.StemsB.πmap x n (g₁ α) (Work.StemsB.πmap g₁ n α w))
      = Work.StemsB.πmap g₂ n (a α) (Work.StemsB.πmap a n α w) := by
  rw [← Work.StemsB.πmap_comp_apply g₁ x n α w,
    ← Work.StemsB.πmap_comp_apply a g₂ n α w]
  exact Work.StemsB.πmap_congr hsq n α w

/-- **Injectivity transfers along a commuting square.** -/
theorem injective_πmap_commSquare (g₁ : C(A₁, X₁)) (g₂ : C(A₂, X₂)) (a : C(A₁, A₂))
    (x : C(X₁, X₂)) (hsq : x.comp g₁ = g₂.comp a) (n : ℕ) (α : A₁)
    (ha : Function.Injective (Work.StemsB.πmap a n α))
    (h : Function.Injective (Work.StemsB.πmap g₂ n (a α))) :
    Function.Injective (Work.StemsB.πmap g₁ n α) := by
  intro u v huv
  have hx : Work.StemsB.homotopyGroupCast (congrArg (fun k : C(A₁, X₂) => k α) hsq) n
        (Work.StemsB.πmap x n (g₁ α) (Work.StemsB.πmap g₁ n α u))
      = Work.StemsB.homotopyGroupCast (congrArg (fun k : C(A₁, X₂) => k α) hsq) n
        (Work.StemsB.πmap x n (g₁ α) (Work.StemsB.πmap g₁ n α v)) := by rw [huv]
  rw [πmap_commSquare_cast g₁ g₂ a x hsq n α u,
    πmap_commSquare_cast g₁ g₂ a x hsq n α v] at hx
  exact ha (h hx)

/-- **Surjectivity transfers along a commuting square.** -/
theorem surjective_πmap_commSquare (g₁ : C(A₁, X₁)) (g₂ : C(A₂, X₂)) (a : C(A₁, A₂))
    (x : C(X₁, X₂)) (hsq : x.comp g₁ = g₂.comp a) (n : ℕ) (α : A₁)
    (ha : Function.Surjective (Work.StemsB.πmap a n α))
    (hx : Function.Injective (Work.StemsB.πmap x n (g₁ α)))
    (h : Function.Surjective (Work.StemsB.πmap g₂ n (a α))) :
    Function.Surjective (Work.StemsB.πmap g₁ n α) := by
  intro y
  set e := congrArg (fun k : C(A₁, X₂) => k α) hsq with he
  obtain ⟨w, hw⟩ := h (Work.StemsB.homotopyGroupCast e n (Work.StemsB.πmap x n (g₁ α) y))
  obtain ⟨u, hu⟩ := ha w
  refine ⟨u, ?_⟩
  have key := πmap_commSquare_cast g₁ g₂ a x hsq n α u
  rw [← hu] at hw
  rw [hw] at key
  exact hx ((Work.StemsB.homotopyGroupCast e n).injective key)

end square

/-! ## The target -/

/-- **The relative groups of `(U, U∩V)` vanish in the wide range `J ≤ 2k-2`, `J ≠ k-1`.**

Setting `ι := setIncl (p ⁻¹' {p e₀}) : C(F, E)` (`F = ↥(p ⁻¹' {p e₀})`), `C = cofibre ι = U ∪ V` the
Blakers–Massey cover of `Submission/Work/RatHurewicz/Cofibre/Cover.lean`
(`U = cofibreU ι`, `V = cofibreV ι`), and `x₀ = collarPt ι ⟨e₀, rfl⟩ ∈ U ∩ V` the collar point (so
that the retraction `ρ : ↥U → E` of `Cofibre.cofibreURetract` sends `x₀` to `e₀` and the collar base
sends `x₀` to `⟨e₀, rfl⟩`).

Mathematically: `RelHomotopyGroup (interInclLeft U V) x₀ J = π_{J+1}(U, U∩V) ≅ π_{J+1}(E, F) ≅
π_{J+1}(B)`, which vanishes by `hmodel` exactly in the stated range.  This is the `hvan` input of
`Work.RatHurewicz.Cofibre.subsingleton_relPi_cofibreV_of_blakersMassey` (with `p = k-2`, `q = k`).

Route, in terms of the *(oriented) square of inclusions*

```
  ↥(collarSet ι) --setIncl--> ↥U         collarSet ι = {u : ↥U | (u : cofibre ι) ∈ V}
        |                          |
   collarBase                     ρ = cofibreURetract
        v                          v
        F ---setIncl F : F → E---> E
```
which commutes on the nose (`Cofibre.cofibreURetract_eq_collarBase` of
`Submission/Work/RatHurewicz/Cofibre/AssemblyDefs.lean`: for `u = [y,t]` with `0 < t < 1/2` both
composites are `ι y`).  The two vertical arrows are homotopy equivalences
(`collarBase = coneMidProj ∘ collarToMid` is `collarInterHE` followed by
`collarMidHomotopyEquiv.trans coneMidHE`, and `ρ` is `cofibreUHomotopyEquiv`), so
`injective_πmap_commSquare` / `surjective_πmap_commSquare` (proved in this file; the same lemmas
are in `Submission/Work/RatHurewicz/Cofibre/collapseAux.lean` under the names
`injective_πmap_of_square` / `surjective_πmap_of_square`) transfer the two ingredients

* `Function.Injective (πmap (setIncl F) (J-1) ⟨e₀,rfl⟩)` — from the exactness of the fibration LES
  at `π_J(F)` (`Work.RatHurewicz.injective_piMapN_fibreIncl_of_subsingleton`, from `les_exact_F`
  with `dMap p (p e₀) hrel (J-1)`, whose source `π_{J+1}(B)` is a subsingleton by `hmodel`), and
* `Function.Surjective (πmap (setIncl F) J ⟨e₀,rfl⟩)` — from
  `Work.Serre.piMap_fibreIncl_surjective_of_subsingleton` (source `π_{J+1}(B)` a subsingleton),

to the corresponding injectivity/surjectivity of `π_J` and `π_{J+1}` of the collar inclusion.
Then `Work.RatHurewicz.relPiVanishingOfPiInjSurj` (applied to the subspace inclusion
`{u : ↥U | (u : cofibre ι) ∈ V} ↪ ↥U`, identified with `interInclLeft U V` by `Cofibre.interHomeo`
and `Cofibre.subsingleton_relPi_of_homeo`) gives the vanishing of
`RelHomotopyGroup (setIncl {u : ↥U | ↑u ∈ V}) ... J`, which is transported back to
`RelHomotopyGroup (interInclLeft U V) x₀ J` (the two inclusions have the same domain up to the shape
of the subtype).

The case `J = 0` is covered by the same criterion `relPiVanishingOfPiInjSurj 0` (injectivity of
`π_0` from the connectedness of the collar, surjectivity of `π_1` from `π_1(↥U) = π_1(E) = 0`, via
`Cofibre.pi_one_E_of_fibration` and `cofibreUHomotopyEquiv`); there the range condition reads
`J + 1 = 1 ≤ 2k-1`, `1 ≠ k`, which holds since `hk : 2 ≤ k`. -/
theorem subsingleton_relPi_interInclLeft_wide {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩)) :
    ∀ J : ℕ, J ≤ 2 * k - 2 → J ≠ k - 1 →
      Subsingleton (RelHomotopyGroup
        (interInclLeft (cofibreU (setIncl (p ⁻¹' {p e₀})))
          (cofibreV (setIncl (p ⁻¹' {p e₀}))))
        (collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩) J) := by
  intro J hJ hJk
  -- ## Notation: the fibre `F`, the inclusion `ι`, the collar point `x₀`, the collar as a subset
  let F : Set E := p ⁻¹' {p e₀}
  let ι : C(↥F, E) := setIncl F
  let x₀ : ↥(cofibreU ι ∩ cofibreV ι) := collarPt ι ⟨e₀, rfl⟩
  let A : Set ↥(cofibreU ι) := collarSet ι
  let α : ↥A := interHomeo (cofibreU ι) (cofibreV ι) x₀
  haveI hEne : Nonempty E := ⟨e₀⟩
  haveI hFne : Nonempty ↥F := ⟨⟨e₀, rfl⟩⟩
  -- ## The two structural facts about the collar
  have hsq : (cofibreURetract ι e₀).comp (setIncl A) = (setIncl F).comp (collarBase ι) :=
    cofibreURetract_comp_setIncl_collarSet F e₀
  have hbase : collarBase ι α = ⟨e₀, rfl⟩ := by
    show collarBaseMid ι (collarInter ι α) = ⟨e₀, rfl⟩
    rw [show collarInter ι α = collarPt ι ⟨e₀, rfl⟩ from rfl]
    exact collarBaseMid_collarPt (F := F) (⟨e₀, rfl⟩ : ↥F)
  -- ## The triviality of `π_1(↥U)` at the base point `setIncl A α`
  have hρa : cofibreURetract ι e₀ (setIncl A α) = e₀ := by
    have h2 := cofibreURetract_eq_collarBase F e₀ α
    rw [show (setIncl A α : ↥(cofibreU ι)) = α.1 from rfl, h2, hbase]
  have hU1 : Subsingleton (HomotopyGroup (Fin 1) ↥(cofibreU ι) (setIncl A α)) := by
    refine (subsingleton_homotopyGroup_of_homotopyEquiv (N := Fin 1)
      (cofibreUHomotopyEquiv ι e₀) (setIncl A α)).mpr ?_
    show Subsingleton (HomotopyGroup (Fin 1) E (cofibreURetract ι e₀ (setIncl A α)))
    rw [hρa]
    exact pi_one_E_of_fibration p hp e₀ k hk hconn hmodel
  -- ## Triviality of `π_0` of the collar (for the case `J = 0`)
  have hcolpc : ∀ a b : ↥(cofibreU ι ∩ cofibreV ι), Nonempty (Path a b) := by
    have hFpc : PathConnectedSpace ↥F :=
      pathConnectedSpace_of_subsingleton_pi_zero (⟨e₀, rfl⟩ : ↥F) (hconn 0 (by omega))
    exact path_connected_of_homotopyEquiv ((collarMidHomotopyEquiv ι).trans (coneMidHE ↥F))
      (fun a b => PathConnectedSpace.joined a b)
  have hinter : Subsingleton (HomotopyGroup (Fin 0) ↥(cofibreU ι ∩ cofibreV ι) x₀) :=
    subsingleton_pi_zero_of_paths hcolpc x₀
  -- ## The fibre side: the long exact sequence of the fibration
  have hfibLES : Work.StemsB.FibrationLES p e₀ :=
    Work.StemsB.fibrationLES_of_isHurewiczFibration p hp e₀
  have hpS : Work.StemsB.IsSerreFibration p := hp.isSerreFibration
  rcases Nat.eq_zero_or_pos J with rfl | hJpos
  · -- ## The case `J = 0`
    have hA0 : Subsingleton (HomotopyGroup (Fin 0) ↥A α) :=
      subsingleton_homotopyGroup_of_homeo (interHomeo (cofibreU ι) (cofibreV ι)) x₀ hinter
    have hset : Subsingleton (RelHomotopyGroup (setIncl A) α 0) :=
      relPiVanishingOfPiInjSurj 0 α (fun x y _ => hA0.elim x y)
        (fun b => ⟨Classical.arbitrary _, hU1.elim _ _⟩)
    have hbridge := subsingleton_relPi_of_homeo (g := setIncl A)
      (interHomeo (cofibreU ι) (cofibreV ι)) x₀ 0 hset
    convert hbridge using 3
    ext x
    rfl
  · -- ## The case `J = n + 1 ≥ 1`
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, J = n + 1 := ⟨J - 1, by omega⟩
    -- `π_{n+2}(B) = 0`
    have hBfib : Subsingleton (HomotopyGroup (Fin (n + 1 + 1)) B (p e₀)) :=
      hmodel (n + 1 + 1) (by omega) (by omega)
    -- injectivity of `π_{n+1}(F) → π_{n+1}(E)`
    have hinjF : Function.Injective (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) n
        (Work.StemsB.fibrePoint p e₀)) := by
      have h := injective_piMapN_fibreIncl_of_subsingleton p e₀ (n + 1) (by omega) hfibLES hBfib
      rw [Work.Serre.piMapN_eq_pimap_succ] at h
      exact h
    -- surjectivity of `π_{n+2}(F) → π_{n+2}(E)`
    have hsurjF : Function.Surjective (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) (n + 1)
        (Work.StemsB.fibrePoint p e₀)) :=
      Work.Serre.piMap_fibreIncl_surjective_of_subsingleton p hpS e₀ (n + 1) (by omega) hBfib
    -- the transfer along the square
    have hInjBottom : Function.Injective
        (Work.StemsB.πmap (setIncl F) n (collarBase ι α)) := by
      rw [hbase]
      exact hinjF
    have hinjSetIncl : Function.Injective (Work.StemsB.πmap (setIncl A) n α) :=
      injective_πmap_commSquare (setIncl A) (setIncl F) (collarBase ι)
        (cofibreURetract ι e₀) hsq n α (bijective_pimap_collarBase ι n α).1 hInjBottom
    have hSurjBottom : Function.Surjective
        (Work.StemsB.πmap (setIncl F) (n + 1) (collarBase ι α)) := by
      rw [hbase]
      exact hsurjF
    have hInjρ : Function.Injective
        (Work.StemsB.πmap (cofibreURetract ι e₀) (n + 1) (setIncl A α)) :=
      (bijective_pimap_of_homotopyEquiv' (cofibreUHomotopyEquiv ι e₀) (n + 1)
        (setIncl A α)).1
    have hsurjSetIncl : Function.Surjective (Work.StemsB.πmap (setIncl A) (n + 1) α) :=
      surjective_πmap_commSquare (setIncl A) (setIncl F) (collarBase ι)
        (cofibreURetract ι e₀) hsq (n + 1) α (bijective_pimap_collarBase ι (n + 1) α).2 hInjρ
        hSurjBottom
    -- the criterion
    have hinj : Function.Injective (Work.Serre.piMapN (setIncl A) (n + 1) α) := by
      rw [Work.Serre.piMapN_eq_pimap_succ]
      exact hinjSetIncl
    have hsurj : Function.Surjective (Work.Serre.piMapN (setIncl A) ((n + 1) + 1) α) := by
      rw [Work.Serre.piMapN_eq_pimap_succ]
      exact hsurjSetIncl
    have hset : Subsingleton (RelHomotopyGroup (setIncl A) α (n + 1)) :=
      relPiVanishingOfPiInjSurj (n + 1) α hinj hsurj
    have hbridge := subsingleton_relPi_of_homeo (g := setIncl A)
      (interHomeo (cofibreU ι) (cofibreV ι)) x₀ (n + 1) hset
    convert hbridge using 3
    ext x
    rfl

end

end Work.RatHurewicz.Cofibre

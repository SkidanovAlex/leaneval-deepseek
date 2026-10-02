import Mathlib
import Submission.Work.RatHurewicz.Cofibre.StableRangeDefs
import Submission.Work.RatHurewicz.Cofibre.RelPiVVU
import Submission.Work.RatHurewicz.Cofibre.pi_one_E_of_fibration
import Submission.Work.Cofibre.pathConnectedSpace_E_of_fibration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz.Cofibre

open scoped Topology unitInterval

noncomputable section

/-! ## Auxiliary lemmas used in the proof -/

/-- **The swap homeomorphism** `↥(B ∩ C) ≃ₜ ↥(C ∩ B)`: the same point of `X`, with the two
membership proofs interchanged. -/
def swapInterHomeo {X : Type} [TopologicalSpace X] (B C : Set X) : ↥(B ∩ C) ≃ₜ ↥(C ∩ B) where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun :=
    Continuous.subtype_mk (by fun_prop : Continuous fun x : ↥(B ∩ C) => (x.1 : X))
      (fun x => ⟨x.2.2, x.2.1⟩)
  continuous_invFun :=
    Continuous.subtype_mk (by fun_prop : Continuous fun x : ↥(C ∩ B) => (x.1 : X))
      (fun x => ⟨x.2.2, x.2.1⟩)

/-- **`π₀` of a space whose points are all joined by paths is trivial.** -/
theorem subsingleton_homotopyGroup_zero_of_paths {X : Type} [TopologicalSpace X]
    (h : ∀ a b : X, Nonempty (Path a b)) (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) := by
  haveI : PathConnectedSpace X := ⟨⟨x⟩, h⟩
  have hZ : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp inferInstance).2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective (hZ.elim _ _)⟩

/-- **Path connectedness transports backwards along a homotopy equivalence.** -/
theorem nonempty_path_of_homotopyEquiv' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- **The criterion `π₁(W,A) = 0` in the `(B,C) = (V,U)` orientation**, the mirror of
`Work.RatHurewicz.subsingleton_relPi_interInclRight` with the two sets of the cover interchanged:
triviality of `π₀` of the intersection and of `π₁` of the second piece give the vanishing of the
relative group `RelHomotopyGroup (interInclRight V U) y₀ 0`. -/
theorem subsingleton_relPi_interInclRight_VU {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (y₀ : ↥(cofibreV ι ∩ cofibreU ι))
    (hinter : Subsingleton (HomotopyGroup (Fin 0) ↥(cofibreV ι ∩ cofibreU ι) y₀))
    (hU : Subsingleton (HomotopyGroup (Fin 1) ↥(cofibreU ι) ⟨y₀.1, y₀.2.2⟩)) :
    Subsingleton (RelHomotopyGroup (interInclRight (cofibreV ι) (cofibreU ι)) y₀ 0) := by
  have hA : Subsingleton (HomotopyGroup (Fin 0)
      ↥{z : ↥(cofibreU ι) | (z : cofibre ι) ∈ cofibreV ι}
      ((interHomeo' (cofibreV ι) (cofibreU ι)) y₀)) :=
    subsingleton_homotopyGroup_of_homeo (interHomeo' (cofibreV ι) (cofibreU ι)) y₀ hinter
  have hset : Subsingleton (RelHomotopyGroup
      (setIncl {z : ↥(cofibreU ι) | (z : cofibre ι) ∈ cofibreV ι})
      ((interHomeo' (cofibreV ι) (cofibreU ι)) y₀) 0) :=
    relPiVanishingOfPiInjSurj 0 ((interHomeo' (cofibreV ι) (cofibreU ι)) y₀)
      (fun x y _ => hA.elim x y)
      (fun b => ⟨Classical.arbitrary _, hU.elim _ _⟩)
  have hbridge := subsingleton_relPi_of_homeo
    (g := setIncl {z : ↥(cofibreU ι) | (z : cofibre ι) ∈ cofibreV ι})
    (interHomeo' (cofibreV ι) (cofibreU ι)) y₀ 0 hset
  convert hbridge using 3
  ext x
  rfl

/-- **The relative groups of `(cofibre ι, U)` vanish up to degree `k`, in degrees `≥ 1`.**

Setting `ι := setIncl (p ⁻¹' {p e₀}) : C(F, E)` (`F = ↥(p ⁻¹' {p e₀})`) and the Blakers–Massey cover
`C = cofibre ι = U ∪ V` of `Submission/Work/RatHurewicz/Cofibre/Cover.lean`
(`U = cofibreU ι = {h < 1/2}`, `V = cofibreV ι = {0 < h}`, `U ∩ V` the collar, `x₀ = collarPt ι
⟨e₀,rfl⟩ ∈ U ∩ V`), the relative homotopy groups of the subspace inclusion `U ↪ cofibre ι` vanish in
degrees `1 ≤ J ≤ k`.

Mathematically `RelHomotopyGroup (setIncl U) x₀ J = π_{J+1}(cofibre ι, U) ≅ π_{J+1}(V, V∩U) ≅
π_J(V∩U) ≅ π_J(F)`, which is trivial for `J ≤ k` by `hconn`.

Route: Blakers–Massey (`Work.RatHurewicz.homotopyExcision`) applied to the *other* orientation of
the cover, `B := cofibreV ι`, `C := cofibreU ι`, with `p := k` and `q := 0`:

* `RelHomotopyGroup (interInclLeft (cofibreV ι) (cofibreU ι)) y₀ J` (`= π_{J+1}(V, V∩U)`) vanishes
  for `J ≤ k` by `Cofibre.subsingleton_relPi_VVU`, whose inputs are
  `Subsingleton (π_J(V∩U, y₀))` (the collar is homotopy equivalent to `F` by
  `Cofibre.collarHomotopyEquiv`, and `π_J(F) = 0` for `J ≤ k` by `hconn` + `subsingleton_pi_collar`
  — for `J = 0` use `hconn 0` and the connectedness of the collar, e.g. via
  `Cofibre.collarHomotopyEquiv` and `Work.RatHurewicz.Cofibre.πmap_eq_map`) and
  `Subsingleton (π_{J+1}(V, y₀))` (`V` is contractible by `exists_contraction_cofibreV`);
* `RelHomotopyGroup (interInclRight (cofibreV ι) (cofibreU ι)) y₀ 0` (`= π_1(U, U∩V)`) vanishes by
  `Work.RatHurewicz.relPiVanishingOfPiInjSurj` at `J = 0`: the source `π_0` is trivial (the collar
  is connected) and the target `π_1(↥U)` is trivial because `π_1(E) = 0`
  (`Cofibre.pi_one_E_of_fibration`, using `hk : 2 ≤ k`) and `↥U ≃ E`
  (`Cofibre.subsingleton_pi_cofibreU` / `cofibreUHomotopyEquiv`).

Blakers–Massey then gives the bijectivity of `excisionMap (cofibreV ι) (cofibreU ι) y₀ n` for
`n + 1 ≤ k + 0`, and since its source is trivial, its target
`RelHomotopyGroup (setIncl (cofibreU ι)) ⟨y₀.1, y₀.2.2⟩ (n+1)` is a subsingleton; the base point of
the conclusion is `⟨(collarPt ι ⟨e₀,rfl⟩).1, (collarPt ι ⟨e₀,rfl⟩).2.1⟩`, so take
`y₀ := ⟨(collarPt ι ⟨e₀,rfl⟩).1, (collarPt ι ⟨e₀,rfl⟩).2.2, (collarPt ι ⟨e₀,rfl⟩).2.1⟩`.

The restriction `1 ≤ J` is deliberate: the case `J = 0` would be the vanishing of `π_1(cofibre ι, U)`
and is *not* covered by this Blakers–Massey application (it is not needed by the caller). -/
theorem subsingleton_relPi_cofibreU_collar {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩)) :
    ∀ J : ℕ, 1 ≤ J → J ≤ k → Subsingleton (RelHomotopyGroup
      (setIncl (cofibreU (setIncl (p ⁻¹' {p e₀}))))
      (⟨(collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩).1,
        (collarPt (setIncl (p ⁻¹' {p e₀})) ⟨e₀, rfl⟩).2.1⟩ : ↥(cofibreU (setIncl (p ⁻¹' {p e₀})))) J) := by
  intro J hJ1 hJk
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, J = n + 1 := ⟨J - 1, by omega⟩
  let ι : C(↥(p ⁻¹' {p e₀}), E) := setIncl (p ⁻¹' {p e₀})
  let x₀ : ↥(cofibreU ι ∩ cofibreV ι) := collarPt ι ⟨e₀, rfl⟩
  let y₀ : ↥(cofibreV ι ∩ cofibreU ι) := ⟨x₀.1, x₀.2.2, x₀.2.1⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  haveI : Nonempty E := ⟨e₀⟩
  -- ### The fibre is path connected, hence its homotopy groups vanish at *every* basepoint
  have hFpc : PathConnectedSpace ↥(p ⁻¹' {p e₀}) :=
    pathConnectedSpace_of_subsingleton_pi_zero ⟨e₀, rfl⟩ (hconn 0 (by omega))
  have hFtriv : ∀ j : ℕ, j ≤ k → ∀ y : ↥(p ⁻¹' {p e₀}),
      Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) y) := by
    intro j hj y
    exact Work.Stems.subsingleton_homotopyGroup_change_basepoint
      (PathConnectedSpace.joined ⟨e₀, rfl⟩ y).some (hconn j hj)
  -- ### The collar `V ∩ U` is homotopy equivalent to the fibre
  obtain ⟨ecol⟩ := collarHomotopyEquiv ι
  have eZ : ContinuousMap.HomotopyEquiv ↥(cofibreV ι ∩ cofibreU ι) ↥(p ⁻¹' {p e₀}) :=
    (swapInterHomeo (cofibreV ι) (cofibreU ι)).toHomotopyEquiv.trans ecol
  have hVUpaths : ∀ a b : ↥(cofibreV ι ∩ cofibreU ι), Nonempty (Path a b) :=
    nonempty_path_of_homotopyEquiv' eZ (fun a b => PathConnectedSpace.joined a b)
  -- ### Triviality of `π_j` of the collar at the collar point
  have hInter : ∀ j : ℕ, j ≤ k →
      Subsingleton (HomotopyGroup (Fin j) ↥(cofibreV ι ∩ cofibreU ι) y₀) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]
      exact subsingleton_homotopyGroup_zero_of_paths hVUpaths y₀
    · haveI : Nonempty (Fin j) := ⟨⟨0, hpos⟩⟩
      exact (subsingleton_homotopyGroup_of_homotopyEquiv (N := Fin j) eZ y₀).mpr
        (hFtriv j hj (eZ.toFun y₀))
  -- ### `V` is contractible, so all its homotopy groups vanish
  obtain ⟨Hv, hHv0, bv, hHv1⟩ := exists_contraction_cofibreV ι
  have hVpi : ∀ j : ℕ, ∀ w : ↥(cofibreV ι),
      Subsingleton (HomotopyGroup (Fin j) ↥(cofibreV ι) w) :=
    fun j w => Work.Stems.subsingleton_of_contraction bv Hv hHv0 hHv1 j w
  -- ### Hypothesis (A) of Blakers–Massey for the cover `(V,U)`
  have hA : ∀ j : ℕ, j ≤ k →
      Subsingleton (RelHomotopyGroup (interInclLeft (cofibreV ι) (cofibreU ι)) y₀ j) :=
    fun j hj => subsingleton_relPi_VVU ι j y₀ (hInter j hj) (hVpi (j + 1) ⟨y₀.1, y₀.2.1⟩)
  -- ### Hypothesis (B) of Blakers–Massey for the cover `(V,U)`: `π_1(↥U) = 0`
  have hE1 : Subsingleton (HomotopyGroup (Fin 1) E e₀) :=
    pi_one_E_of_fibration p hp e₀ k hk hconn hmodel
  have hEpc : PathConnectedSpace E :=
    Work.Cofibre.pathConnectedSpace_E_of_fibration p hp e₀ k hk hconn hmodel
  have hE1all : ∀ y : E, Subsingleton (HomotopyGroup (Fin 1) E y) := fun y =>
    Work.Stems.subsingleton_homotopyGroup_change_basepoint
      (PathConnectedSpace.joined e₀ y).some hE1
  have hU1 : Subsingleton (HomotopyGroup (Fin 1) ↥(cofibreU ι) ⟨y₀.1, y₀.2.2⟩) :=
    (subsingleton_homotopyGroup_of_homotopyEquiv (N := Fin 1) (cofibreUHomotopyEquiv ι e₀) _).mpr
      (hE1all _)
  have hB : ∀ j : ℕ, j ≤ 0 →
      Subsingleton (RelHomotopyGroup (interInclRight (cofibreV ι) (cofibreU ι)) y₀ j) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact subsingleton_relPi_interInclRight_VU ι y₀ (hInter 0 (by omega)) hU1
  -- ### Blakers–Massey
  have hbc : cofibreV ι ∪ cofibreU ι = Set.univ := by
    rw [Set.union_comm]
    exact cofibreU_union_cofibreV ι
  have hbij := Work.RatHurewicz.homotopyExcision (X := cofibre ι) (B := cofibreV ι)
    (C := cofibreU ι) hbc (isOpen_cofibreV ι) (isOpen_cofibreU ι) y₀ k 0 hA hB n (by omega)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hbij.surjective a
  obtain ⟨b', rfl⟩ := hbij.surjective b
  rw [(hA (n + 1) (by omega)).elim a' b']

end

end Work.RatHurewicz.Cofibre

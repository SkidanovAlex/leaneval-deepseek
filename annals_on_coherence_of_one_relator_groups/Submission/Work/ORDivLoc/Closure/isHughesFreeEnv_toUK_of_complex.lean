/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `IsHughesFreeEnv` is insensitive to the coefficient field

The `∗`-regular closure `U_N = U_N(φ, H, N)` of [JZLA20, Theorem 6.1] is the `∗`-regular closure
of the image of `φ(K[N])` inside `U`.  If the coefficient field `K` is embedded in `ℂ` by
`φK : K →+* ℂ`, and if the `K`-algebra structure of `U(G)` factors through that embedding
(`hφK : algebraMap K U k = algebraMap ℂ U (φK k)`), then

* the image of `K[N]` in `U(G)` is contained in the image of `ℂ[N]` (via `k • x = φK k • x`),
  so `U_N(φK, H, N) ⊆ U_N(id, H, N)` for the corresponding structure maps;
* the element `φ(t)` used in the statement of `IsHughesFreeEnv` is the same for both coefficient
  fields, because `toUK E _ H (single h 1) = genU E h` does not depend on the embedding.

Consequently `IsHughesFreeEnv` at the `ℂ`-structure map implies `IsHughesFreeEnv` at the
`K`-structure map.  This is the reduction used by `Work.ORDivLoc` to apply the JZLA20 engine (which
is set over `ℂ`) to an arbitrary coefficient field.

## Main results

* `Work.ORDivLoc.Closure.toUK_mapRingHom` — `toUK` is natural in the coefficient field;
* `Work.ORDivLoc.Closure.range_phiN_toUK_subset` — the `K`-image of `K[N]` lies in the `ℂ`-image;
* `Work.ORDivLoc.Closure.UN_toUK_le` — monotonicity of the `∗`-regular closure `U_N`;
* `Work.ORDivLoc.Closure.isHughesFreeEnv_of_un_le` — `IsHughesFreeEnv` only depends on `U_N` and on
  `φ(t)`;
* `Work.ORDivLoc.Closure.isHughesFreeEnv_toUK_of_complex` — the target.
-/
import Mathlib
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_mono

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ORDivLoc.Closure

open Work

/-! ## `toUK` is natural in the coefficient field -/

/-- **The base change square for `toUK`.**  If the `K`-algebra structure of `E.U` factors through
an embedding `φK : K →+* ℂ` of the coefficient field, then the structure map `K[H] → U` (with
coefficients in `K`) is the composite of the structure map `ℂ[H] → U` with the base change
`MonoidAlgebra K ↥H →+* MonoidAlgebra ℂ ↥H` along `φK`.

Both maps send `single h 1` to `genU E h`; the equality is `MonoidAlgebra.lift_mapRingHom_algebraMap`
applied after registering the `K`-algebra structure `φK.toAlgebra` on `ℂ` and the (equivalent)
`IsScalarTower K ℂ E.U` that `hφK` expresses. -/
theorem toUK_mapRingHom {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k)) (H : Subgroup G)
    (x : MonoidAlgebra K ↥H) :
    (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom
        (MonoidAlgebra.mapRingHom ↥H φK x) =
      (Work.ORBridgeLinnell.toUK E φK H).toRingHom x := by
  letI : Algebra K ℂ := φK.toAlgebra
  haveI : IsScalarTower K ℂ E.U := by
    refine ⟨fun x y z => ?_⟩
    show (x • y) • z = x • (y • z)
    rw [Algebra.smul_def (R := K) (A := ℂ) x y,
        Algebra.smul_def (R := ℂ) (A := E.U),
        Algebra.smul_def (R := K) (A := E.U) x,
        Algebra.smul_def (R := ℂ) (A := E.U) y,
        map_mul, hφK, show (algebraMap K ℂ) x = φK x from rfl, mul_assoc]
  exact MonoidAlgebra.lift_mapRingHom_algebraMap (A := E.U) (R := K) (S := ℂ) (M := ↥H)
    ((Work.ORBridgeLinnell.genU E).comp (Subgroup.subtype H)) x

/-! ## The image of `K[N]` lies in the image of `ℂ[N]` -/

/-- **The range of `phiN` at the `K`-structure map is contained in the range at the `ℂ`-structure
map.**  The point is that `k • genU E g = algebraMap K E.U k * genU E g
= algebraMap ℂ E.U (φK k) * genU E g = φK k • genU E g`. -/
theorem range_phiN_toUK_subset {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    (H : Subgroup G) (H₀ : Subgroup ↥H) (N : Subgroup H₀) :
    Set.range (Work.Section6.phiN (Work.ORBridgeLinnell.toUK E φK H).toRingHom H₀ N)
      ⊆ Set.range (Work.Section6.phiN
          (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom H₀ N) := by
  have hbch : ∀ y : MonoidAlgebra K ↥H,
      (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom
          (MonoidAlgebra.mapRingHom ↥H φK y) =
        (Work.ORBridgeLinnell.toUK E φK H).toRingHom y :=
    fun y => toUK_mapRingHom E φK hφK H y
  have e1 : ∀ z : MonoidAlgebra K ↥N,
      (MonoidAlgebra.mapDomainRingHom ℂ N.subtype) (MonoidAlgebra.mapRingHom ↥N φK z)
        = (MonoidAlgebra.mapRingHom ↥H₀ φK) (MonoidAlgebra.mapDomainRingHom K N.subtype z) :=
    fun z => (RingHom.congr_fun (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (R := K) (S := ℂ) (f := φK) (g := N.subtype)) z).symm
  have e2 : ∀ z : MonoidAlgebra K ↥H₀,
      (MonoidAlgebra.mapDomainRingHom ℂ H₀.subtype) (MonoidAlgebra.mapRingHom ↥H₀ φK z)
        = (MonoidAlgebra.mapRingHom ↥H φK) (MonoidAlgebra.mapDomainRingHom K H₀.subtype z) :=
    fun z => (RingHom.congr_fun (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
      (R := K) (S := ℂ) (f := φK) (g := H₀.subtype)) z).symm
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨MonoidAlgebra.mapRingHom ↥N φK x, ?_⟩
  simp only [Work.Section6.phiN, Work.ORHughesFree.inducedMapRing, RingHom.comp_apply]
  rw [e1 x, e2 (MonoidAlgebra.mapDomainRingHom K N.subtype x), hbch]

/-! ## Monotonicity of the `∗`-regular closure `U_N` -/

/-- **`U_N` is monotone in the structure map.**  If every element in the image of `K[N]` under the
first structure map lies in the `∗`-regular closure computed for the second, then the whole
`∗`-regular closure is contained in the second one. -/
theorem UN_toUK_le {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k))
    (H : Subgroup G) (H₀ : Subgroup ↥H) (N : Subgroup H₀) :
    (Work.Section6.UN (Work.ORBridgeLinnell.toUK E φK H).toRingHom H₀ N : Set E.U)
      ⊆ (Work.Section6.UN
          (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom H₀ N : Set E.U) := by
  refine Work.ORHughesFree.StarRegular.starRegularClosure_mono ?_
  refine Work.ORHughesFree.StarRegular.starSubringClosure_mono ?_
  exact range_phiN_toUK_subset E φK hφK H H₀ N

/-! ## `IsHughesFreeEnv` depends only on `U_N` and on `φ(t)` -/

/-- A matrix over a `∗`-subring `q ⊇ p` with the same entries as a matrix over `p`: the coercion
of the transported matrix to the ambient ring is the coercion of the original one. -/
theorem map_coe_eq {U : Type*} [Ring U] [StarRing U] {n : ℕ}
    {p q : Work.ORHughesFree.StarSubring U} (hle : (p : Set U) ⊆ (q : Set U))
    (A : Matrix (Fin n) (Fin n) ↥p) :
    (Matrix.of (fun i j => (⟨(A i j : U), hle (A i j).2⟩ : ↥q))).map Subtype.val
      = A.map Subtype.val := by
  apply Matrix.ext
  intro i j
  rfl

/-- **`IsHughesFreeEnv` only depends on the `∗`-regular closures `U_N` and on the elements
`φ(t)`.**  If the `U_N` of `φ₁` are contained in those of `φ₂`, and the two maps agree on the
group-like elements `single t 1` of each `K[↥H]`, then `IsHughesFreeEnv φ₂` implies
`IsHughesFreeEnv φ₁`. -/
theorem isHughesFreeEnv_of_un_le {K₁ K₂ : Type} [Field K₁] [Field K₂]
    {G : Type} [Group G] {U : Type} [Ring U] [StarRing U]
    [Work.ORHughesFree.IsStarRegular U]
    {φ₁ : MonoidAlgebra K₁ G →+* U} {φ₂ : MonoidAlgebra K₂ G →+* U}
    (hle : ∀ (H : Subgroup G) (N : Subgroup H),
      (Work.Section6.UN φ₁ H N : Set U) ⊆ (Work.Section6.UN φ₂ H N : Set U))
    (hs : ∀ (H : Subgroup G) (t : H),
      (φ₁.comp (Work.ORHughesFree.inducedMapRing (K := K₁) H)) (MonoidAlgebra.single t 1) =
      (φ₂.comp (Work.ORHughesFree.inducedMapRing (K := K₂) H)) (MonoidAlgebra.single t 1))
    (h : Work.ORHughesFree.IsHughesFreeEnv φ₂) :
    Work.ORHughesFree.IsHughesFreeEnv φ₁ := by
  intro H hfg hne N hNnorm t hdec htinf n A
  have hB := map_coe_eq (n := n) (hle H N) A
  have hunit := h H hfg hne N hNnorm t hdec htinf n
    (Matrix.of (fun i j =>
      (⟨(A i j : U), hle H N (A i j).2⟩ : Work.Section6.UNty φ₂ H N)))
  rw [hB] at hunit
  rwa [← hs H t] at hunit

/-! ## The element `φ(t)` does not depend on the coefficient field -/

/-- The group-like element `φ(single t 1)` of `IsHughesFreeEnv` is `genU E t` for *every*
structure map, since `toUK E _ H (single h 1) = genU E h`. -/
theorem toUK_scalar_eq {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) (H₀ : Subgroup ↥H) (t : H₀) :
    ((Work.ORBridgeLinnell.toUK E φK H).toRingHom.comp
        (Work.ORHughesFree.inducedMapRing (K := K) H₀)) (MonoidAlgebra.single t 1) =
      ((Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom.comp
        (Work.ORHughesFree.inducedMapRing (K := ℂ) H₀)) (MonoidAlgebra.single t 1) := by
  have keyφ : ∀ h : ↥H,
      (Work.ORBridgeLinnell.toUK E φK H).toRingHom (MonoidAlgebra.single h 1) =
        Work.ORBridgeLinnell.genU E (h : G) :=
    fun h => by simpa using Work.ORBridgeLinnell.toUK_single E φK H h (1 : K)
  have keyid : ∀ h : ↥H,
      (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom (MonoidAlgebra.single h 1) =
        Work.ORBridgeLinnell.genU E (h : G) :=
    fun h => by simpa using Work.ORBridgeLinnell.toUK_single E (RingHom.id ℂ) H h (1 : ℂ)
  simp only [Work.ORHughesFree.inducedMapRing, RingHom.comp_apply,
    MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, keyφ, keyid]

/-! ## The target -/

theorem isHughesFreeEnv_toUK_of_complex {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, algebraMap K E.U k = algebraMap ℂ E.U (φK k)) (H : Subgroup G)
    (h : Work.ORHughesFree.IsHughesFreeEnv
      (Work.ORBridgeLinnell.toUK E (RingHom.id ℂ) H).toRingHom) :
    Work.ORHughesFree.IsHughesFreeEnv (Work.ORBridgeLinnell.toUK E φK H).toRingHom :=
  isHughesFreeEnv_of_un_le
    (fun H₀ N => UN_toUK_le E φK hφK H H₀ N)
    (fun H₀ t => toUK_scalar_eq E φK H H₀ t)
    h

end Work.ORDivLoc.Closure

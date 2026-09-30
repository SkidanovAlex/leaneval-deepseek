/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asphericity of the base of a covering with aspherical (e.g. contractible) total space

The main results of this file say that if `p : E → X` is a covering map whose total space `E`
has no higher homotopy groups (e.g. `E` contractible, or `E` a real normed space), then `X` is
aspherical: `π_k(X, x)` is a subsingleton for every `k ≥ 2` and every `x : X`.

* `subsingleton_homotopyGroup_of_covering_of_aspherical` — the general statement, with the
  vanishing of the higher homotopy groups of `E` as a hypothesis;
* `subsingleton_homotopyGroup_of_covering_of_contractible` — `E` contractible;
* `subsingleton_homotopyGroup_of_covering_of_normed` — `E` a real normed space (proved by the
  straight-line homotopy);
* `subsingleton_homotopyGroup_of_covering_euclideanSpace` — `E = EuclideanSpace ℝ (Fin 4)`;
* `subsingleton_homotopyGroup_of_covering_of_homeomorph_normed` and
  `subsingleton_homotopyGroup_of_covering_homeomorph_euclideanSpace` — `E` homeomorphic to a real
  normed space / to `EuclideanSpace ℝ (Fin 4)`;
* the `isAspherical_*` variants package the conclusion as `Work.Aspherical.IsAspherical X`.
-/
import Mathlib
import Submission.Work.Aspherical.Basic
import Submission.Work.Aspherical.Covering
import Submission.Work.Aspherical.cube_joinedIn_boundary
import Submission.Work.Aspherical.cube_homotopicRel_const_of_contractible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology unitInterval

namespace Work.Aspherical

noncomputable section

/-! ### The straight-line homotopy in a real normed space -/

section StraightLine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two maps from the cube `I^k` into a real normed space that agree on the boundary are
homotopic relative to the boundary, by the straight-line homotopy. -/
theorem straightLine_homotopicRel {k : ℕ} {e : E} {F G : C(I^Fin k, E)}
    (hF : ∀ y ∈ Cube.boundary (Fin k), F y = e)
    (hG : ∀ y ∈ Cube.boundary (Fin k), G y = e) :
    F.HomotopicRel G (Cube.boundary (Fin k)) := by
  refine ⟨{ toContinuousMap :=
              { toFun := fun q => (1 - (q.1 : ℝ)) • F q.2 + (q.1 : ℝ) • G q.2
                continuous_toFun := by fun_prop }
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro y
    simp
  · intro y
    simp
  · intro t y hy
    have h1 : F y = e := hF y hy
    have h2 : G y = e := hG y hy
    change (1 - (t : ℝ)) • F y + (t : ℝ) • G y = F y
    rw [h1, h2, ← add_smul, sub_add_cancel, one_smul]

/-- Every higher homotopy group of a real normed space is trivial. -/
theorem subsingleton_homotopyGroup_of_normed {k : ℕ} (_hk : 1 ≤ k) (e : E) :
    Subsingleton (HomotopyGroup (Fin k) E e) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun f g => Quotient.sound ?_
  change f.1.HomotopicRel g.1 (Cube.boundary (Fin k))
  exact straightLine_homotopicRel (fun y hy => f.2 y hy) (fun y hy => g.2 y hy)

/-- Every higher homotopy group of a space homeomorphic to a real normed space is trivial. -/
theorem subsingleton_homotopyGroup_of_normed_homeomorph {k : ℕ} (_hk : 1 ≤ k) {E V : Type*}
    [TopologicalSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : E ≃ₜ V) (e : E) :
    Subsingleton (HomotopyGroup (Fin k) E e) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun f g => Quotient.sound ?_
  change f.1.HomotopicRel g.1 (Cube.boundary (Fin k))
  let φC : C(E, V) := ⟨φ, φ.continuous_toFun⟩
  let φI : C(V, E) := ⟨φ.symm, φ.symm.continuous_toFun⟩
  have hf' : ∀ y ∈ Cube.boundary (Fin k), (φC.comp f.1) y = φ e := by
    intro y hy
    show (⇑φ) (f.1 y) = φ e
    rw [f.2 y hy]
  have hg' : ∀ y ∈ Cube.boundary (Fin k), (φC.comp g.1) y = φ e := by
    intro y hy
    show (⇑φ) (g.1 y) = φ e
    rw [g.2 y hy]
  have h := straightLine_homotopicRel (F := φC.comp f.1) (G := φC.comp g.1) hf' hg'
  have h2 := h.map (fun H => H.compContinuousMap φI)
  have h1 : (φI.comp (φC.comp f.1)) = f.1 := by
    ext y; simp [φC, φI]
  have h3 : (φI.comp (φC.comp g.1)) = g.1 := by
    ext y; simp [φC, φI]
  rwa [h1, h3] at h2

end StraightLine

/-! ### The main theorem -/

section Main

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}

/-- **Asphericity from a covering with aspherical total space** (basepointed form): if `p : E → X`
is a covering map, `E` is aspherical and `e₀` is a lift of `x`, then `π_k(X, x)` is a subsingleton
for `k ≥ 2`. -/
theorem subsingleton_homotopyGroup_of_covering_of_aspherical_at
    (hp : IsCoveringMap p)
    (haspherical : ∀ (k : ℕ), 2 ≤ k → ∀ e : E, Subsingleton (HomotopyGroup (Fin k) E e))
    {x : X} {e₀ : E} (he : p e₀ = x) (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton (HomotopyGroup (Fin k) X x) := by
  have hk0 : NeZero k := ⟨by omega⟩
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun f g => ?_
  obtain ⟨F, hF₀, hF⟩ := IsCoveringMap.exists_lift_genLoop hp f (Cube.zeroPoint_mem_boundary k) he
  obtain ⟨G, hG₀, hG⟩ := IsCoveringMap.exists_lift_genLoop hp g (Cube.zeroPoint_mem_boundary k) he
  have hFb : ∀ y ∈ Cube.boundary (Fin k), F y = e₀ := by
    intro y hy
    obtain ⟨γ, hγ⟩ := cube_joinedIn_boundary k hk (Cube.zeroPoint_mem_boundary k) hy
    exact lift_genLoop_boundary hp hF (Cube.zeroPoint_mem_boundary k) hF₀ hy γ hγ
  have hGb : ∀ y ∈ Cube.boundary (Fin k), G y = e₀ := by
    intro y hy
    obtain ⟨γ, hγ⟩ := cube_joinedIn_boundary k hk (Cube.zeroPoint_mem_boundary k) hy
    exact lift_genLoop_boundary hp hG (Cube.zeroPoint_mem_boundary k) hG₀ hy γ hγ
  have hhom : F.HomotopicRel G (Cube.boundary (Fin k)) := by
    have hsub : Subsingleton (HomotopyGroup (Fin k) E e₀) := haspherical k hk e₀
    have h := hsub.elim (Quotient.mk _ (⟨F, hFb⟩ : GenLoop (Fin k) E e₀))
      (Quotient.mk _ (⟨G, hGb⟩ : GenLoop (Fin k) E e₀))
    exact Quotient.exact h
  refine Quotient.sound ?_
  change f.1.HomotopicRel g.1 (Cube.boundary (Fin k))
  have hcomp1 : (⟨p, hp.continuous⟩ : C(E, X)).comp F = f.1 := by ext y; exact congr_fun hF y
  have hcomp2 : (⟨p, hp.continuous⟩ : C(E, X)).comp G = g.1 := by ext y; exact congr_fun hG y
  have h := hhom.map (fun H => H.compContinuousMap (⟨p, hp.continuous⟩ : C(E, X)))
  rwa [hcomp1, hcomp2] at h

/-- **Asphericity from a covering with aspherical total space.** If `p : E → X` is a surjective
covering map and `E` is aspherical, then `X` is aspherical: `π_k(X, x)` is a subsingleton for
every `k ≥ 2` and every `x : X`. -/
theorem subsingleton_homotopyGroup_of_covering_of_aspherical
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (haspherical : ∀ (k : ℕ), 2 ≤ k → ∀ e : E, Subsingleton (HomotopyGroup (Fin k) E e))
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_aspherical_at hp haspherical (hsurj x).choose_spec k hk

/-- Packaged form of `subsingleton_homotopyGroup_of_covering_of_aspherical`. -/
theorem isAspherical_of_covering_of_aspherical
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (haspherical : ∀ (k : ℕ), 2 ≤ k → ∀ e : E, Subsingleton (HomotopyGroup (Fin k) E e)) :
    IsAspherical X :=
  fun k hk x => subsingleton_homotopyGroup_of_covering_of_aspherical hp hsurj haspherical k hk x

/-- **Asphericity from a contractible cover** (basepointed form): only a lift `e₀` of the
basepoint `x` is required. -/
theorem subsingleton_homotopyGroup_of_covering_of_contractible_at
    (hp : IsCoveringMap p) [ContractibleSpace E]
    {x : X} {e₀ : E} (he : p e₀ = x) (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton (HomotopyGroup (Fin k) X x) := by
  refine subsingleton_homotopyGroup_of_covering_of_aspherical_at hp (fun k hk e => ?_) he k hk
  haveI : NeZero k := ⟨by omega⟩
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun f g => Quotient.sound ?_
  change f.1.HomotopicRel g.1 (Cube.boundary (Fin k))
  have hf := cube_homotopicRel_const_of_contractible (e := e) (F := f.1) (fun y hy => f.2 y hy)
  have hg := cube_homotopicRel_const_of_contractible (e := e) (F := g.1) (fun y hy => g.2 y hy)
  exact hf.trans hg.symm

/-- **Asphericity from a contractible cover.** If `p : E → X` is a surjective covering map with
contractible total space `E`, then `π_k(X, x)` is a subsingleton for every `k ≥ 2` and every
`x : X`. -/
theorem subsingleton_homotopyGroup_of_covering_of_contractible
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) [ContractibleSpace E]
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_contractible_at hp (hsurj x).choose_spec k hk

/-- **Asphericity from a contractible cover** — the area's headline statement, in the
`∀ k, 2 ≤ k → ∀ x` form. -/
theorem subsingleton_homotopyGroup_of_covering
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) [ContractibleSpace E] :
    ∀ k : ℕ, 2 ≤ k → ∀ x : X, Subsingleton (HomotopyGroup (Fin k) X x) :=
  fun k hk x => subsingleton_homotopyGroup_of_covering_of_contractible hp hsurj k hk x

/-- Packaged form of `subsingleton_homotopyGroup_of_covering_of_contractible`. -/
theorem isAspherical_of_covering_of_contractible
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) [ContractibleSpace E] :
    IsAspherical X :=
  fun k hk x => subsingleton_homotopyGroup_of_covering_of_contractible hp hsurj k hk x

/-- **Asphericity from a contractible cover, with path connected base**: surjectivity of `p` is
automatic (`IsCoveringMap.surjective_of_pathConnectedSpace`). -/
theorem subsingleton_homotopyGroup_of_covering_of_contractible_of_pathConnected
    (hp : IsCoveringMap p) [ContractibleSpace E] [Nonempty E] [PathConnectedSpace X]
    (k : ℕ) (hk : 2 ≤ k) (x : X) :
    Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_contractible hp
    (IsCoveringMap.surjective_of_pathConnectedSpace hp) k hk x

/-- **Asphericity from a covering with aspherical total space, with path connected base.** -/
theorem subsingleton_homotopyGroup_of_covering_of_aspherical_of_pathConnected
    (hp : IsCoveringMap p) [Nonempty E] [PathConnectedSpace X]
    (haspherical : ∀ (k : ℕ), 2 ≤ k → ∀ e : E, Subsingleton (HomotopyGroup (Fin k) E e))
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_aspherical hp
    (IsCoveringMap.surjective_of_pathConnectedSpace hp) haspherical k hk x

end Main

/-! ### Coverings by real normed spaces -/

section Normed

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E → X}

/-- **Asphericity from a covering by a real normed space** (basepointed form). -/
theorem subsingleton_homotopyGroup_of_covering_of_normed_at
    (hp : IsCoveringMap p) {x : X} {e₀ : E} (he : p e₀ = x) (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_aspherical_at hp
    (fun k hk e => subsingleton_homotopyGroup_of_normed (k := k) (by omega) e) he k hk

/-- **Asphericity from a covering by a real normed space.** -/
theorem subsingleton_homotopyGroup_of_covering_of_normed
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_aspherical hp hsurj
    (fun k hk e => subsingleton_homotopyGroup_of_normed (k := k) (by omega) e) k hk x

/-- **Asphericity from a covering by a real normed space, with path connected base.** -/
theorem subsingleton_homotopyGroup_of_covering_of_normed_of_pathConnected [PathConnectedSpace X]
    (hp : IsCoveringMap p) (k : ℕ) (hk : 2 ≤ k) (x : X) :
    Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_normed hp
    (IsCoveringMap.surjective_of_pathConnectedSpace hp) k hk x

/-- Packaged form of `subsingleton_homotopyGroup_of_covering_of_normed`. -/
theorem isAspherical_of_covering_of_normed
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) : IsAspherical X :=
  fun k hk x => subsingleton_homotopyGroup_of_covering_of_normed hp hsurj k hk x

/-- **The special case `E = EuclideanSpace ℝ (Fin 4)`.** -/
theorem subsingleton_homotopyGroup_of_covering_euclideanSpace {X : Type*} [TopologicalSpace X]
    {p : EuclideanSpace ℝ (Fin 4) → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_normed hp hsurj k hk x

/-- **The special case `E = EuclideanSpace ℝ (Fin 4)` with a path connected base.** Surjectivity
of `p` is then automatic (`IsCoveringMap.surjective_of_pathConnectedSpace`). -/
theorem subsingleton_homotopyGroup_of_covering_euclideanSpace_of_pathConnected {X : Type*}
    [TopologicalSpace X] [PathConnectedSpace X] {p : EuclideanSpace ℝ (Fin 4) → X}
    (hp : IsCoveringMap p) (k : ℕ) (hk : 2 ≤ k) (x : X) :
    Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_euclideanSpace hp
    (IsCoveringMap.surjective_of_pathConnectedSpace hp) k hk x

/-- **The special case `E = EuclideanSpace ℝ (Fin 4)` with a connected, locally path connected
base.** -/
theorem subsingleton_homotopyGroup_of_covering_euclideanSpace_of_connected {X : Type*}
    [TopologicalSpace X] [ConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : EuclideanSpace ℝ (Fin 4) → X} (hp : IsCoveringMap p) (k : ℕ) (hk : 2 ≤ k) (x : X) :
    Subsingleton (HomotopyGroup (Fin k) X x) := by
  haveI : PathConnectedSpace X := (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
  exact subsingleton_homotopyGroup_of_covering_euclideanSpace_of_pathConnected hp k hk x

/-- **The special case `E = EuclideanSpace ℝ (Fin 4)`, basepointed form**: only a lift of `x` is
required. -/
theorem subsingleton_homotopyGroup_of_covering_euclideanSpace_at {X : Type*} [TopologicalSpace X]
    {p : EuclideanSpace ℝ (Fin 4) → X} (hp : IsCoveringMap p) {x : X}
    {e₀ : EuclideanSpace ℝ (Fin 4)} (he : p e₀ = x) (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_normed_at hp he k hk

/-- **Asphericity from a covering by `EuclideanSpace ℝ (Fin 4)`**, packaged form. -/
theorem isAspherical_of_covering_euclideanSpace {X : Type*} [TopologicalSpace X]
    {p : EuclideanSpace ℝ (Fin 4) → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    IsAspherical X :=
  fun k hk x => subsingleton_homotopyGroup_of_covering_euclideanSpace hp hsurj k hk x

end Normed

/-! ### Coverings by a space homeomorphic to a real normed space -/

section HomeomorphNormed

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] {p : E → X}

/-- **Asphericity from a covering by a space homeomorphic to a real normed space.** -/
theorem subsingleton_homotopyGroup_of_covering_of_homeomorph_normed {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (φ : E ≃ₜ V)
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_aspherical hp hsurj
    (fun k hk e => subsingleton_homotopyGroup_of_normed_homeomorph (k := k) (by omega) φ e)
    k hk x

/-- Packaged form of `subsingleton_homotopyGroup_of_covering_of_homeomorph_normed`. -/
theorem isAspherical_of_covering_of_homeomorph_normed {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (φ : E ≃ₜ V) : IsAspherical X :=
  fun k hk x =>
    subsingleton_homotopyGroup_of_covering_of_homeomorph_normed hp hsurj φ k hk x

/-- **The case `E` homeomorphic to `EuclideanSpace ℝ (Fin 4)`.** -/
theorem subsingleton_homotopyGroup_of_covering_homeomorph_euclideanSpace {X E : Type*}
    [TopologicalSpace X] [TopologicalSpace E] {p : E → X}
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (φ : E ≃ₜ EuclideanSpace ℝ (Fin 4))
    (k : ℕ) (hk : 2 ≤ k) (x : X) : Subsingleton (HomotopyGroup (Fin k) X x) :=
  subsingleton_homotopyGroup_of_covering_of_homeomorph_normed hp hsurj φ k hk x

/-- Packaged form of `subsingleton_homotopyGroup_of_covering_homeomorph_euclideanSpace`. -/
theorem isAspherical_of_covering_homeomorph_euclideanSpace {X E : Type*}
    [TopologicalSpace X] [TopologicalSpace E] {p : E → X}
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (φ : E ≃ₜ EuclideanSpace ℝ (Fin 4)) :
    IsAspherical X :=
  fun k hk x =>
    subsingleton_homotopyGroup_of_covering_homeomorph_euclideanSpace hp hsurj φ k hk x

end HomeomorphNormed

end

end Work.Aspherical

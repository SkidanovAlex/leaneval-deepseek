import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.Serre.AttachCompress.Assemble
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `π₀` of the inclusion of an attachment

Area **SERRE**.  The companion file `Submission/Work/Serre/attachIncl_piMap_bijective_of_compress`
proves that the inclusion `attachIncl n Y ι f : Y → attachCells n Y ι f` induces a bijection on
`π_k` for `1 ≤ k ≤ n`.  The bottom degree `k = 0` is not a group and is not covered by that
statement (nor by `Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel`, whose degree range
starts at `π₁`), and it is needed at the very bottom of the Postnikov tower
(`Work.Serre.serrePostnikovTower`).  This file supplies it.

Note that `π₀` here is the genuinely based object `HomotopyGroup (Fin 0) X x`, which Mathlib
identifies with the *path components* `ZerothHomotopy X` via
`HomotopyGroup.pi0EquivZerothHomotopy`.

## Route

The attached cells are of dimension `n + 2 ≥ 2`, hence simply connected and glued along a connected
boundary, so they change neither the set of path components nor the identifications between them:
`π₀` of the inclusion is a bijection.  Formally this is a consequence of the *compression property*
of the pair `(X, range attachIncl)` in dimensions `0` and `1` (`Work.Serre.AttachCompress.compression`,
available in every dimension `≤ n + 1`):

* compression in dimension `0` says that every point of `X` is joined by a path in `X` to a point of
  `range attachIncl` — so `zmkMap attachIncl` is surjective;
* compression in dimension `1` says that a path in `X` between two points of `range attachIncl` can
  be deformed, relative to its endpoints, into `range attachIncl` — so `zmkMap attachIncl` is
  injective.

`Work.Serre.bijective_zmkMap_setIncl_of_compressRel` records these two implications in general, on
the path components (`ZerothHomotopy`), and the homeomorphism
`Work.RatHurewicz.rangeHomeo : Y ≃ₜ range attachIncl` transports the statement to `attachIncl`
itself.  Finally `Work.Serre.pi0EquivZerothHomotopy_map` (naturality of Mathlib's
`HomotopyGroup.pi0EquivZerothHomotopy`) conjugates the induced map on path components with the
induced map on `HomotopyGroup (Fin 0)`.
-/

open scoped Topology unitInterval Topology.Homotopy

namespace Work.Serre

/-- **The map induced by a continuous map on path components.**  Mathlib has `ZerothHomotopy` and
its `lift` constructor, but no functoriality for it. -/
noncomputable def zmkMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun _x _y p => ZerothHomotopy.sound (p.map f.continuous))

@[simp]
theorem zmkMap_mk {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    zmkMap f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) := rfl

theorem zmkMap_id {X : Type} [TopologicalSpace X] :
    zmkMap (ContinuousMap.id X) = id := by
  funext b
  induction b using ZerothHomotopy.rec with
  | mk x => simp

theorem zmkMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) : zmkMap (g.comp f) = zmkMap g ∘ zmkMap f := by
  funext b
  induction b using ZerothHomotopy.rec with
  | mk x => simp

theorem zmkMap_id_apply {X : Type} [TopologicalSpace X] (b : ZerothHomotopy X) :
    zmkMap (ContinuousMap.id X) b = b := by rw [zmkMap_id]; rfl

theorem zmkMap_comp_apply {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (b : ZerothHomotopy X) :
    zmkMap (g.comp f) b = zmkMap g (zmkMap f b) := by rw [zmkMap_comp]; rfl

/-- **Naturality of Mathlib's `π₀ ≃ ZerothHomotopy`**: the induced map on `HomotopyGroup (Fin 0)`
corresponds to the induced map on path components. -/
theorem pi0EquivZerothHomotopy_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : HomotopyGroup.Pi 0 X x) :
    HomotopyGroup.pi0EquivZerothHomotopy (HomotopyGroup.map (N := Fin 0) f a)
      = zmkMap f (HomotopyGroup.pi0EquivZerothHomotopy a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    show homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) (f x)
        (HomotopyGroup.map f (N := Fin 0) ⟦p⟧)
      = zmkMap f (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x ⟦p⟧)
    rw [HomotopyGroup.map_mk]
    unfold HomotopyGroup ZerothHomotopy
    rw [homotopyGroupEquivZerothHomotopyOfIsEmpty, Quotient.congr_mk]
    rw [homotopyGroupEquivZerothHomotopyOfIsEmpty, Quotient.congr_mk]
    change ZerothHomotopy.mk ((genLoopHomeoOfIsEmpty (Fin 0) (f x)).toEquiv
        (⟨f.comp ↑p, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
          GenLoop (Fin 0) Y (f x)))
      = zmkMap f (ZerothHomotopy.mk ((genLoopHomeoOfIsEmpty (Fin 0) x).toEquiv p))
    simp only [zmkMap, ZerothHomotopy.lift_mk, genLoopHomeoOfIsEmpty]
    rfl

open Work.RatHurewicz

/-- **Compression in dimension `0` makes `π₀` of the inclusion surjective.**  Every point of `X` is
joined by a path to a point of `A`; hence every path component of `X` contains a point of `A`. -/
theorem surjective_zmkMap_setIncl_of_compressRel {X : Type} [TopologicalSpace X] {A : Set X}
    (h0 : CompressRel X A 0) : Function.Surjective (zmkMap (setIncl A)) := by
  intro b
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective b
  obtain ⟨G, hG0, -, hG1⟩ := h0 (ContinuousMap.const (ICube 0) x) (by
    intro c hc
    exact absurd hc (by simp [Cube.boundary]))
  let c₀ : ICube 0 := fun i => i.elim0
  let a : ↥A := ⟨G (c₀, 1), hG1 c₀⟩
  have hpath : Path x (a : X) :=
    ⟨⟨fun t => G (c₀, t), by fun_prop⟩, hG0 c₀, rfl⟩
  exact ⟨ZerothHomotopy.mk a, by rw [zmkMap_mk]; exact (ZerothHomotopy.sound hpath).symm⟩

/-- **Compression in dimension `1` makes `π₀` of the inclusion injective.**  A path in `X` between
two points of `A` can be deformed, relative to its endpoints, into `A`; hence it exhibits a path in
`A` between the two points. -/
theorem injective_zmkMap_setIncl_of_compressRel {X : Type} [TopologicalSpace X] {A : Set X}
    (h1 : CompressRel X A 1) : Function.Injective (zmkMap (setIncl A)) := by
  intro b₁ b₂ h
  obtain ⟨a₁, rfl⟩ := ZerothHomotopy.mk_surjective b₁
  obtain ⟨a₂, rfl⟩ := ZerothHomotopy.mk_surjective b₂
  simp only [zmkMap_mk] at h
  have hjoin : Joined (setIncl A a₁ : X) (setIncl A a₂) := Quotient.exact h
  obtain ⟨γ⟩ := hjoin
  let ofC : ICube 1 → unitInterval := fun c => c 0
  have hof : Continuous ofC := continuous_apply 0
  let γC : C(ICube 1, X) := γ.toContinuousMap.comp ⟨ofC, hof⟩
  have hbdd : ∀ c, c ∈ Cube.boundary (Fin 1) → γC c ∈ A := by
    intro c hc
    obtain ⟨i, hi⟩ := hc
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rcases hi with hi | hi
    · rw [show γC c = γ (c 0) from rfl, hi, γ.source]
      exact a₁.2
    · rw [show γC c = γ (c 0) from rfl, hi, γ.target]
      exact a₂.2
  obtain ⟨G, hG0, hGbd, hG1⟩ := h1 γC hbdd
  let δ : C(ICube 1, ↥A) := ⟨fun c => ⟨G (c, 1), hG1 c⟩, by fun_prop⟩
  have h0 : δ (fun _ => 0) = a₁ := by
    apply Subtype.ext
    show G ((fun _ => 0 : ICube 1), 1) = ↑a₁
    rw [hGbd _ ⟨0, Or.inl rfl⟩ 1]
    show γC (fun _ => 0) = ↑a₁
    rw [show γC (fun _ => 0) = γ 0 from rfl]
    exact γ.source
  have h₂ : δ (fun _ => 1) = a₂ := by
    apply Subtype.ext
    show G ((fun _ => 1 : ICube 1), 1) = ↑a₂
    rw [hGbd _ ⟨0, Or.inr rfl⟩ 1]
    show γC (fun _ => 1) = ↑a₂
    rw [show γC (fun _ => 1) = γ 1 from rfl]
    exact γ.target
  have hpathA : Path a₁ a₂ :=
    ⟨⟨fun t => δ (fun _ => t), by fun_prop⟩, h0, h₂⟩
  exact ZerothHomotopy.sound hpathA

/-- **Compression of `(X, A)` in dimensions `0` and `1` makes `A ↪ X` a bijection on `π₀`.** -/
theorem bijective_zmkMap_setIncl_of_compressRel {X : Type} [TopologicalSpace X] {A : Set X}
    (h0 : CompressRel X A 0) (h1 : CompressRel X A 1) :
    Function.Bijective (zmkMap (setIncl A)) :=
  ⟨injective_zmkMap_setIncl_of_compressRel h1, surjective_zmkMap_setIncl_of_compressRel h0⟩

/-- **Attaching `(n+2)`-cells does not change `π₀`.**  The inclusion
`attachIncl n Y ι f : Y → attachCells n Y ι f` induces a bijection on `π₀`.  (The attached cells
are simply connected and glued along a connected boundary, so they neither create nor merge path
components; formally, the compression property of `(X, range attachIncl)` in dimensions `0` and
`1`.) -/
theorem attachIncl_pi0_bijective (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (y₀ : Y) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) (Work.RatHurewicz.attachIncl n Y ι f)
      (x := y₀)) := by
  have hcomp := Work.Serre.AttachCompress.compression n Y ι f
  have hbijA : Function.Bijective (zmkMap (Work.RatHurewicz.setIncl
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))) :=
    bijective_zmkMap_setIncl_of_compressRel (hcomp 0 (by omega)) (hcomp 1 (by omega))
  let eC : C(Y, ↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f))) :=
    ⟨⇑(Work.RatHurewicz.rangeHomeo n Y ι f), (Work.RatHurewicz.rangeHomeo n Y ι f).continuous⟩
  let eI : C(↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f)), Y) :=
    ⟨⇑(Work.RatHurewicz.rangeHomeo n Y ι f).symm,
      (Work.RatHurewicz.rangeHomeo n Y ι f).symm.continuous⟩
  have h1 : eI.comp eC = ContinuousMap.id Y := by ext y; simp [eC, eI]
  have h2 : eC.comp eI = ContinuousMap.id _ := by ext p; simp [eC, eI]
  have hbijE : Function.Bijective (zmkMap eC) := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨zmkMap eI y, ?_⟩⟩
    · have hh : zmkMap eI (zmkMap eC x) = zmkMap eI (zmkMap eC y) := by rw [hxy]
      rw [← zmkMap_comp_apply eC eI x, h1, zmkMap_id_apply] at hh
      rw [← zmkMap_comp_apply eC eI y, h1, zmkMap_id_apply] at hh
      exact hh
    · rw [← zmkMap_comp_apply eI eC y, h2, zmkMap_id_apply]
  have hbijI : Function.Bijective (zmkMap (Work.RatHurewicz.attachIncl n Y ι f)) := by
    have hfun : zmkMap (Work.RatHurewicz.attachIncl n Y ι f) =
        zmkMap (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
          ∘ zmkMap eC := by
      funext b
      induction b using ZerothHomotopy.rec with
      | mk y => rfl
    rw [hfun]
    exact hbijA.comp hbijE
  have hnat : ∀ a : HomotopyGroup (Fin 0) Y y₀,
      HomotopyGroup.pi0EquivZerothHomotopy
        (HomotopyGroup.map (N := Fin 0) (Work.RatHurewicz.attachIncl n Y ι f) (x := y₀) a)
      = zmkMap (Work.RatHurewicz.attachIncl n Y ι f)
          (HomotopyGroup.pi0EquivZerothHomotopy a) :=
    fun a => pi0EquivZerothHomotopy_map _ _ a
  have hfun : HomotopyGroup.map (N := Fin 0) (Work.RatHurewicz.attachIncl n Y ι f) (x := y₀)
      = fun a => (HomotopyGroup.pi0EquivZerothHomotopy
            (x := Work.RatHurewicz.attachIncl n Y ι f y₀)).symm
          (zmkMap (Work.RatHurewicz.attachIncl n Y ι f)
            (HomotopyGroup.pi0EquivZerothHomotopy (x := y₀) a)) := by
    funext a
    rw [← hnat a]
    exact (Equiv.symm_apply_apply _ _).symm
  rw [hfun]
  exact (Equiv.bijective _).comp (hbijI.comp (Equiv.bijective _))

end Work.Serre

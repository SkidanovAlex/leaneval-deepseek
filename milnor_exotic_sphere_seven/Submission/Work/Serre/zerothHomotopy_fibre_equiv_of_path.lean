import Mathlib
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.Serre.serreFibration_fibre_homology_iso
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.Serre.joinedIn_fibre_of_lifted_path
import Submission.Work.Serre.joinedIn_fibre_of_homotopic_const

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `π₀` of the fibres of a Serre fibration is transported along a path in the base

Let `p : E → B` be a Serre fibration (HLP with respect to all cubes) and `γ : I → B` a path in the
base.  This file proves `Work.Serre.zerothHomotopy_fibre_equiv_of_path`: the path components of the
fibres `p ⁻¹' {γ 0}` and `p ⁻¹' {γ 1}` are in bijection.

The transport is `γ`-lifting: choose for every point `x` of the fibre over `γ 0` a lift
`U x : I → E` of `γ` with `U x 0 = x` (`Work.Serre.exists_liftPath_proj`), and send the class of `x`
to the class of `U x 1`.  The content of the statement is that this is well defined: two points
joined *inside* the fibre over `γ 0` have endpoints joined *inside* the fibre over `γ 1`
(`Work.Serre.joinedIn_fibre_of_lifted_path`, the relative homotopy lifting property on the square),
and that the construction along `γ` and along `γ.symm` are mutually inverse, which uses
`Work.Serre.joinedIn_fibre_of_homotopic_const` for the concatenated loop `γ * γ⁻¹`.

The same argument is carried out for an arbitrary path `lam : Path b₀ b₁` of the base
(`Work.Serre.fibre_zerothHomotopy_equiv_of_path`), so that it applies to `lam.symm` as well.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1000000

/-- Membership in a fibre, unfolded. -/
theorem fibreMem_iff {E B : Type} (p : E → B) (b : B) (x : E) :
    x ∈ p ⁻¹' {b} ↔ p x = b := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff]

/-- **Path lifting with prescribed starting point, keeping the projection.**  A path `γ` in the
base with `p e = γ 0` lifts to a path of `E` starting at `e` and projecting onto `γ`.

This is the degree-`0` case of the relative homotopy lifting property
(`Work.StemsB.exists_lift_rel`) with the projection property exposed, which is what the transport
of `π₀` along `γ` needs. -/
theorem exists_liftPath_proj {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (γ : C(unitInterval, B))
    {e : E} (he : p e = γ 0) :
    ∃ w : C(unitInterval, E), w 0 = e ∧ p.comp w = γ := by
  let H : C((Fin 0 → I) × I, B) := ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  let f : C(Fin 0 → I, E) := ContinuousMap.const (Fin 0 → I) e
  have hf : p.comp f = H.comp (Work.StemsB.zeroIncl 0) := by
    ext z
    show p e = γ 0
    exact he
  let g₀ : C(Work.StemsB.CubeBdry 0 × I, E) := ContinuousMap.const _ e
  have hg : p.comp g₀ = H.comp (Work.StemsB.bdryIncl 0) := by
    ext z
    obtain ⟨i, _⟩ := z.1.2
    exact i.elim0
  have hg0 : ∀ x : Work.StemsB.CubeBdry 0, g₀ (x, 0) = f x.1 := by
    intro x
    obtain ⟨i, _⟩ := x.2
    exact i.elim0
  obtain ⟨G, hGq, hG0, -⟩ := Work.StemsB.exists_lift_rel p hp 0 H f hf g₀ hg hg0
  let z₀ : Fin 0 → I := fun i => i.elim0
  refine ⟨⟨fun t : I => G (z₀, t),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩, ?_, ?_⟩
  · show G (z₀, 0) = e
    rw [hG0 z₀]
    rfl
  · ext t
    exact congrFun (congrArg DFunLike.coe hGq) (z₀, t)

/-- **The projection of a concatenated path.**  If `w₁` and `w₂` are paths of `E` projecting onto
`lam` and onto `lam.symm`, then their concatenation projects onto `lam * lam⁻¹`. -/
theorem comp_trans_pathContinuousMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {a b c : E} (w₁ : Path a b) (w₂ : Path b c)
    {b₀ b₁ : B} (lam : Path b₀ b₁)
    (h₁ : ∀ s : unitInterval, p (w₁ s) = lam s)
    (h₂ : ∀ s : unitInterval, p (w₂ s) = lam.symm s) :
    p.comp (w₁.trans w₂).toContinuousMap = (lam.trans lam.symm).toContinuousMap := by
  ext t
  show p ((w₁.trans w₂) t) = (lam.trans lam.symm) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with hh
  · exact h₁ _
  · exact h₂ _

/-- **Joining in a subtype gives joining in the ambient space.** -/
theorem joinedIn_of_joined_subtype {X : Type} [TopologicalSpace X] {F : Set X} {a b : X}
    (ha : a ∈ F) (hb : b ∈ F) (h : Joined (⟨a, ha⟩ : F) ⟨b, hb⟩) : JoinedIn F a b := by
  obtain ⟨γ⟩ := h
  exact ⟨γ.map continuous_subtype_val, fun t => (γ t).2⟩

/-- **The `π₀` of the fibres of a Serre fibration is transported along a path in the base.**
For an arbitrary path `lam : Path b₀ b₁` of the base, the set of path components of the fibres over
its endpoints are in bijection.

The transport is realised by lifting `lam`: the class of `x ∈ p ⁻¹' {b₀}` is sent to the class of
the endpoint of a lift of `lam` starting at `x`; `joinedIn_fibre_of_lifted_path` says that this is
well defined on path components, and `joinedIn_fibre_of_homotopic_const` applied to `lam * lam⁻¹`
and to `lam⁻¹ * lam` shows that the constructions along `lam` and along `lam⁻¹` are inverse to each
other. -/
theorem fibre_zerothHomotopy_equiv_of_path {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) :
    ∀ {b₀ b₁ : B} (lam : Path b₀ b₁),
      Nonempty (ZerothHomotopy ↥(p ⁻¹' {b₀}) ≃ ZerothHomotopy ↥(p ⁻¹' {b₁})) := by
  intro b₀ b₁ lam
  classical
  -- * lifts along `lam`
  have hU : ∀ e : E, p e = b₀ →
      ∃ w : C(unitInterval, E), w 0 = e ∧ p.comp w = lam.toContinuousMap := fun e he =>
    exists_liftPath_proj p hp lam.toContinuousMap (he.trans lam.source.symm)
  let U : (e : E) → p e = b₀ → C(unitInterval, E) := fun e he => Classical.choose (hU e he)
  have U0 : ∀ (e : E) (he : p e = b₀), U e he 0 = e := fun e he =>
    (Classical.choose_spec (hU e he)).1
  have Up : ∀ (e : E) (he : p e = b₀), p.comp (U e he) = lam.toContinuousMap := fun e he =>
    (Classical.choose_spec (hU e he)).2
  -- * lifts backwards along `lam.symm`
  have hU' : ∀ e : E, p e = b₁ →
      ∃ w : C(unitInterval, E), w 0 = e ∧ p.comp w = lam.symm.toContinuousMap := fun e he =>
    exists_liftPath_proj p hp lam.symm.toContinuousMap (he.trans lam.symm.source.symm)
  let U' : (e : E) → p e = b₁ → C(unitInterval, E) := fun e he => Classical.choose (hU' e he)
  have U'0 : ∀ (e : E) (he : p e = b₁), U' e he 0 = e := fun e he =>
    (Classical.choose_spec (hU' e he)).1
  have U'p : ∀ (e : E) (he : p e = b₁), p.comp (U' e he) = lam.symm.toContinuousMap := fun e he =>
    (Classical.choose_spec (hU' e he)).2
  have mem0 : ∀ x : ↥(p ⁻¹' {b₀}), p x.1 = b₀ := fun x =>
    (fibreMem_iff p b₀ x.1).mp x.2
  have mem1 : ∀ y : ↥(p ⁻¹' {b₁}), p y.1 = b₁ := fun y =>
    (fibreMem_iff p b₁ y.1).mp y.2
  -- * the point maps and their membership
  let φ : ↥(p ⁻¹' {b₀}) → E := fun x => U x.1 (mem0 x) 1
  have φmem : ∀ x : ↥(p ⁻¹' {b₀}), φ x ∈ p ⁻¹' {b₁} := fun x =>
    (fibreMem_iff p b₁ (φ x)).mpr
      ((congrFun (congrArg DFunLike.coe (Up x.1 (mem0 x))) 1).trans lam.target)
  let ψ : ↥(p ⁻¹' {b₁}) → E := fun y => U' y.1 (mem1 y) 1
  have ψmem : ∀ y : ↥(p ⁻¹' {b₁}), ψ y ∈ p ⁻¹' {b₀} := fun y =>
    (fibreMem_iff p b₀ (ψ y)).mpr
      ((congrFun (congrArg DFunLike.coe (U'p y.1 (mem1 y))) 1).trans lam.symm.target)
  let Φfun : ↥(p ⁻¹' {b₀}) → ZerothHomotopy ↥(p ⁻¹' {b₁}) :=
    fun x => ZerothHomotopy.mk ⟨φ x, φmem x⟩
  let Ψfun : ↥(p ⁻¹' {b₁}) → ZerothHomotopy ↥(p ⁻¹' {b₀}) :=
    fun y => ZerothHomotopy.mk ⟨ψ y, ψmem y⟩
  -- * descent of the point maps
  have Φwell : ∀ x y : ↥(p ⁻¹' {b₀}), Joined x y → Φfun x = Φfun y := by
    intro x y hxy
    obtain ⟨α⟩ := hxy
    have hj : JoinedIn (p ⁻¹' {b₀}) x.1 y.1 :=
      joinedIn_of_joined_subtype x.2 y.2 ⟨α⟩
    have hj' : JoinedIn (p ⁻¹' {lam 0}) (U x.1 (mem0 x) 0) (U y.1 (mem0 y) 0) := by
      rw [U0 x.1 (mem0 x), U0 y.1 (mem0 y)]
      exact lam.source.symm ▸ hj
    have h := joinedIn_fibre_of_lifted_path p hp lam.toContinuousMap
      (U x.1 (mem0 x)) (U y.1 (mem0 y)) (Up x.1 (mem0 x)) (Up y.1 (mem0 y)) hj'
    have h' : JoinedIn (p ⁻¹' {b₁}) (φ x) (φ y) := lam.target ▸ h
    obtain ⟨pp⟩ := h'.joined_subtype
    exact ZerothHomotopy.sound pp
  have Ψwell : ∀ x y : ↥(p ⁻¹' {b₁}), Joined x y → Ψfun x = Ψfun y := by
    intro x y hxy
    obtain ⟨α⟩ := hxy
    have hj : JoinedIn (p ⁻¹' {b₁}) x.1 y.1 :=
      joinedIn_of_joined_subtype x.2 y.2 ⟨α⟩
    have hj' : JoinedIn (p ⁻¹' {lam.symm 0}) (U' x.1 (mem1 x) 0) (U' y.1 (mem1 y) 0) := by
      rw [U'0 x.1 (mem1 x), U'0 y.1 (mem1 y)]
      exact lam.symm.source.symm ▸ hj
    have h := joinedIn_fibre_of_lifted_path p hp lam.symm.toContinuousMap
      (U' x.1 (mem1 x)) (U' y.1 (mem1 y)) (U'p x.1 (mem1 x)) (U'p y.1 (mem1 y)) hj'
    have h' : JoinedIn (p ⁻¹' {b₀}) (ψ x) (ψ y) := lam.symm.target ▸ h
    obtain ⟨pp⟩ := h'.joined_subtype
    exact ZerothHomotopy.sound pp
  -- * the two composites are the identity on path components
  have hΨΦ : ∀ z : ZerothHomotopy ↥(p ⁻¹' {b₀}),
      (ZerothHomotopy.lift Ψfun (fun x y h => Ψwell x y ⟨h⟩))
        ((ZerothHomotopy.lift Φfun (fun x y h => Φwell x y ⟨h⟩)) z) = z := by
    intro z
    induction z using ZerothHomotopy.rec with
    | mk x =>
      rw [ZerothHomotopy.lift_mk]
      show (ZerothHomotopy.lift Ψfun (fun x y h => Ψwell x y ⟨h⟩))
        (ZerothHomotopy.mk ⟨φ x, φmem x⟩) = ZerothHomotopy.mk x
      rw [ZerothHomotopy.lift_mk]
      show ZerothHomotopy.mk ⟨ψ ⟨φ x, φmem x⟩, ψmem ⟨φ x, φmem x⟩⟩ = ZerothHomotopy.mk x
      have hpx : p (φ x) = b₁ := (fibreMem_iff p b₁ (φ x)).mp (φmem x)
      let w₁ : Path x.1 (φ x) := Path.mk (U x.1 (mem0 x)) (U0 x.1 (mem0 x)) rfl
      let w₂ : Path (φ x) (ψ ⟨φ x, φmem x⟩) :=
        Path.mk (U' (φ x) hpx) (U'0 (φ x) hpx) rfl
      have hw₁ : ∀ s : unitInterval, p (w₁ s) = lam s := fun s =>
        congrFun (congrArg DFunLike.coe (Up x.1 (mem0 x))) s
      have hw₂ : ∀ s : unitInterval, p (w₂ s) = lam.symm s := fun s => by
        have hh : p ((U' (φ x) hpx) s) = lam.symm s :=
          congrFun (congrArg DFunLike.coe (U'p (φ x) hpx)) s
        show p ((U' (φ x) hpx) s) = lam.symm s
        exact hh
      have hw : p.comp (w₁.trans w₂).toContinuousMap =
          (lam.trans lam.symm).toContinuousMap := comp_trans_pathContinuousMap p w₁ w₂ lam hw₁ hw₂
      have hjoin := joinedIn_fibre_of_homotopic_const p hp (lam.trans lam.symm)
        (w₁.trans w₂).toContinuousMap hw (Path.Homotopic.trans_symm lam)
      have e0 : (w₁.trans w₂).toContinuousMap 0 = x.1 := (w₁.trans w₂).source
      have e1 : (w₁.trans w₂).toContinuousMap 1 = ψ ⟨φ x, φmem x⟩ := (w₁.trans w₂).target
      rw [e0, e1] at hjoin
      obtain ⟨pp⟩ := hjoin.joined_subtype
      exact (ZerothHomotopy.sound pp).symm
  have hΦΨ : ∀ z : ZerothHomotopy ↥(p ⁻¹' {b₁}),
      (ZerothHomotopy.lift Φfun (fun x y h => Φwell x y ⟨h⟩))
        ((ZerothHomotopy.lift Ψfun (fun x y h => Ψwell x y ⟨h⟩)) z) = z := by
    intro z
    induction z using ZerothHomotopy.rec with
    | mk y =>
      rw [ZerothHomotopy.lift_mk]
      show (ZerothHomotopy.lift Φfun (fun x y h => Φwell x y ⟨h⟩))
        (ZerothHomotopy.mk ⟨ψ y, ψmem y⟩) = ZerothHomotopy.mk y
      rw [ZerothHomotopy.lift_mk]
      show ZerothHomotopy.mk ⟨φ ⟨ψ y, ψmem y⟩, φmem ⟨ψ y, ψmem y⟩⟩ = ZerothHomotopy.mk y
      have hpy : p (ψ y) = b₀ := (fibreMem_iff p b₀ (ψ y)).mp (ψmem y)
      let w₁ : Path y.1 (ψ y) := Path.mk (U' y.1 (mem1 y)) (U'0 y.1 (mem1 y)) rfl
      let w₂ : Path (ψ y) (φ ⟨ψ y, ψmem y⟩) :=
        Path.mk (U (ψ y) hpy) (U0 (ψ y) hpy) rfl
      have hw₁ : ∀ s : unitInterval, p (w₁ s) = lam.symm s := fun s =>
        congrFun (congrArg DFunLike.coe (U'p y.1 (mem1 y))) s
      have hw₂ : ∀ s : unitInterval, p (w₂ s) = lam.symm.symm s := fun s => by
        have hh : p ((U (ψ y) hpy) s) = lam s :=
          congrFun (congrArg DFunLike.coe (Up (ψ y) hpy)) s
        show p ((U (ψ y) hpy) s) = lam.symm.symm s
        simpa [Path.symm_symm] using hh
      have hw : p.comp (w₁.trans w₂).toContinuousMap =
          (lam.symm.trans lam).toContinuousMap := by
        simpa [Path.symm_symm] using comp_trans_pathContinuousMap p w₁ w₂ lam.symm hw₁ hw₂
      have hjoin := joinedIn_fibre_of_homotopic_const p hp (lam.symm.trans lam)
        (w₁.trans w₂).toContinuousMap hw (Path.Homotopic.symm_trans lam)
      have e0 : (w₁.trans w₂).toContinuousMap 0 = y.1 := (w₁.trans w₂).source
      have e1 : (w₁.trans w₂).toContinuousMap 1 = φ ⟨ψ y, ψmem y⟩ := (w₁.trans w₂).target
      rw [e0, e1] at hjoin
      obtain ⟨pp⟩ := hjoin.joined_subtype
      exact (ZerothHomotopy.sound pp).symm
  exact ⟨{ toFun := ZerothHomotopy.lift Φfun (fun x y h => Φwell x y ⟨h⟩),
           invFun := ZerothHomotopy.lift Ψfun (fun x y h => Ψwell x y ⟨h⟩),
           left_inv := hΨΦ, right_inv := hΦΨ }⟩

/-- **(t1) The `π₀` of the fibres of a Serre fibration is transported along a path in the base.**
For a Serre fibration `p : E → B` and a path `γ` in the base, the sets of joined classes of the
fibres over `γ 0` and `γ 1` are in bijection.

This is the `π₀` analogue of `Work.Serre.serreFibration_fibre_homology_iso` (and of
`Work.Serre.ratH_fibre_iso_of_path` in `Submission/Work/Serre/ratFibreTransport.lean`, the closest
template: same statement with homology instead of `π₀`).  It is the fibre-class transport needed by
the transfer's order-1 bookkeeping (`PLAN_v2.md` ADDENDUM 23): it is what makes the index set
`L(σ) = π₀ (p ⁻¹' {σ w})` independent of the point `w` and hence comparable across faces.

Route (verified by the reviewers): the path lifting `Work.Serre.exists_path_lift_of_isSerreFibration`
(in `Submission.Work.Serre.exists_path_pullbackFst`) lifts `γ` from a point of either fibre, so the
two fibres are simultaneously empty or nonempty, giving `Nonempty (α ≃ β)` in the empty case via
`Equiv.ofIsEmpty`.  In the nonempty case lift `γ` from a point `e` of `p ⁻¹' {γ 0}` to get a map on
points `F_{γ 0} → F_{γ 1}`, and lift the reverse path for the inverse; descending to `π₀` needs the
observation that two lifts of `γ` starting at points joined *inside* `F_{γ 0}` have endpoints joined
*inside* `F_{γ 1}` — that is the relative HLP on the square, `Work.StemsB.exists_lift_rel` — and
that is the real content (worth extracting as a private lemma).  The two composites then induce the
identity on `π₀` by the same argument with the concatenated path. -/
theorem zerothHomotopy_fibre_equiv_of_path {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (γ : C(unitInterval, B)) :
    Nonempty (ZerothHomotopy ↥(p ⁻¹' {γ 0}) ≃ ZerothHomotopy ↥(p ⁻¹' {γ 1})) :=
  fibre_zerothHomotopy_equiv_of_path p hp (Path.mk (x := γ 0) (y := γ 1) γ rfl rfl)

end

end Work.Serre

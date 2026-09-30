import Mathlib
import Submission.Work.Serre.SPC.piOne_killStep

set_option synthInstance.maxHeartbeats 400000


/-!
# Killing a common `π₁`-kernel of two maps, simultaneously

Given a space `Γ` with two maps `g : Γ → Z`, `h : Γ → P` whose induced maps on `π₁` are both
surjective with the *same* kernel, attach to `Γ` — for every element `α` of the common kernel — a
`2`-cell along the loop `killFamily 0 Γ γ₀ α` representing `α` (the construction of
`Work.Serre.SPC.piOne_killStep`).  The two `π₁`-surjections agree on the kernel, so *both* `g` and
`h` extend over the attached cells, and — exactly as in the one-map case — both extensions induce
`π₁`-bijections.  The common quotient space is the `Y` of the statement.

The whole content is a single observation: the family of attached loops is fixed by the kernel of
`π₁(g)` alone, and `π₁(h)` has the same kernel, so the same cells kill it.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz Work.Serre.CWModel

namespace Work.EMFG

noncomputable section

/-- **A kernel class gives a null-homotopy of its representing loop.**  If `α` lies in the kernel of
`π₁(g)`, then the sphere map `killFamily 0 Γ γ₀ α` representing `α` becomes null-homotopic after
composition with `g`. -/
theorem killFamily_comp_homotopic_const {B : Type} [TopologicalSpace B]
    {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B))
    (α : HomotopyGroup (Fin 1) Γ γ₀) (hα : Work.Serre.piMapN g 1 γ₀ α = 1) :
    (g.comp (killFamily 0 Γ γ₀ α)).Homotopic
      (ContinuousMap.const (cellSphere 0) (g γ₀)) := by
  have hn : 1 ≤ 1 := le_rfl
  have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap g 1 (Quotient.out α))
      (GenLoop.const (N := Fin 1) (X := B) (x := g γ₀)) := by
    have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap g 1 (Quotient.out α)) :
          HomotopyGroup (Fin 1) B (g γ₀))
        = Quotient.mk (GenLoop.Homotopic.setoid (Fin 1) (g γ₀))
            (GenLoop.const (N := Fin 1) (X := B) (x := g γ₀)) := by
      rw [← Work.Serre.piMapN_apply_mk, Quotient.out_eq (α), hα]
      exact HomotopyGroup.one_def (N := Fin 1) (X := B) (x := g γ₀)
    exact Quotient.exact h1
  have h2 := Work.Serre.CWModel.cubeLift_homotopic hn hcube
  rw [Work.RatHurewicz.cubeLift_genLoopMap, Work.Serre.CWModel.cubeLift_const] at h2
  exact h2

/-- **Making one map `π₁`-bijective by attaching cells.**  Let `f : ι → C(S¹, Γ)` be a family of
loops of `Γ` such that `g ∘ f i` is null-homotopic for every `i`, let `π₁(g)` be surjective, and
suppose that every class of `Γ` in the kernel of `π₁(g)` dies in the space obtained by attaching
the cells along `f`.  Then `g` extends over the attached cells and the extension is a
`π₁`-bijection. -/
theorem piOne_bijective_attachG {B : Type} [TopologicalSpace B]
    {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) {ι : Type}
    (f : ι → C(cellSphere 0, Γ)) (g : C(Γ, B))
    (hnull : ∀ i, (g.comp (f i)).Homotopic (ContinuousMap.const (cellSphere 0) (g γ₀)))
    (hsurj : Function.Surjective (Work.Serre.piMapN g 1 γ₀))
    (hkill : ∀ α : HomotopyGroup (Fin 1) Γ γ₀, Work.Serre.piMapN g 1 γ₀ α = 1 →
      Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α = 1) :
    ∃ (G : ι → C(cellDisk 0, B))
      (hG : ∀ (i : ι) (z : cellSphere 0), G i (cellSphereToDisk 0 z) = g (f i z)),
      Function.Bijective (Work.Serre.piMapN (attachG 0 Γ ι f g G hG) 1
        (attachIncl 0 Γ ι f γ₀)) := by
  classical
  let G : ι → C(cellDisk 0, B) := fun k =>
    Classical.choose (sphereExtend (g.comp (f k)) (hnull k).some.toContinuousMap (g γ₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
  have hG : ∀ (k : ι) (z : cellSphere 0), G k (cellSphereToDisk 0 z) = g (f k z) := by
    intro k z
    have hspec := Classical.choose_spec (sphereExtend (g.comp (f k))
      (hnull k).some.toContinuousMap (g γ₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  refine ⟨G, hG, ?_⟩
  let g' : C(attachCells 0 Γ ι f, B) := attachG 0 Γ ι f g G hG
  have hcomp' : ∀ a : HomotopyGroup (Fin 1) Γ γ₀,
      Work.Serre.piMapN g 1 γ₀ a
        = Work.Serre.piMapN g' 1 (attachIncl 0 Γ ι f γ₀)
            (Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ a) :=
    fun a => Work.Serre.piMapN_comp (attachIncl 0 Γ ι f) g' 1 γ₀ a
  have hmul : ∀ {Z : Type} [TopologicalSpace Z] (q : C(Γ, Z))
      (a b : HomotopyGroup (Fin 1) Γ γ₀),
      Work.Serre.piMapN q 1 γ₀ (a * b)
        = Work.Serre.piMapN q 1 γ₀ a * Work.Serre.piMapN q 1 γ₀ b :=
    fun q a b => map_mul (Work.StemsB.πmap q 0 γ₀) a b
  have hinv : ∀ {Z : Type} [TopologicalSpace Z] (q : C(Γ, Z))
      (a : HomotopyGroup (Fin 1) Γ γ₀),
      Work.Serre.piMapN q 1 γ₀ a⁻¹ = (Work.Serre.piMapN q 1 γ₀ a)⁻¹ :=
    fun q a => map_inv (Work.StemsB.πmap q 0 γ₀) a
  have hsf : Function.Surjective (Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀) :=
    surjective_πmap_attachIncl 0 Γ ι f γ₀
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨α, rfl⟩ := hsf a
    obtain ⟨β, rfl⟩ := hsf b
    have hαβ : Work.Serre.piMapN g 1 γ₀ α = Work.Serre.piMapN g 1 γ₀ β := by
      rw [hcomp' α, hcomp' β]; exact hab
    have hkerαβ : Work.Serre.piMapN g 1 γ₀ (α * β⁻¹) = 1 := by
      rw [hmul g α β⁻¹, hinv g β, hαβ, mul_inv_cancel]
    have hk := hkill (α * β⁻¹) hkerαβ
    have hthis : Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α
        = Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ β := by
      refine mul_inv_eq_one.mp ?_
      rw [← hinv (attachIncl 0 Γ ι f) β, ← hmul (attachIncl 0 Γ ι f) α β⁻¹]
      exact hk
    rw [hthis]
  · intro y
    obtain ⟨α, hα⟩ := hsurj y
    exact ⟨Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α, by
      rw [← hcomp' α]; exact hα⟩

theorem commonPiOneKill {Γ Z P : Type} [TopologicalSpace Γ] [TopologicalSpace Z] [TopologicalSpace P]
    (γ₀ : Γ) (g : C(Γ, Z)) (h : C(Γ, P)) (hsurj_g : Function.Surjective (Work.Serre.piMapN g 1 γ₀))
    (hsurj_h : Function.Surjective (Work.Serre.piMapN h 1 γ₀))
    (hker : ∀ a : HomotopyGroup (Fin 1) Γ γ₀,
      Work.Serre.piMapN g 1 γ₀ a = 1 ↔ Work.Serre.piMapN h 1 γ₀ a = 1) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (f : C(Y, Z)) (g' : C(Y, P)),
      Function.Bijective (Work.Serre.piMapN f 1 y₀) ∧ Function.Bijective (Work.Serre.piMapN g' 1 y₀) := by
  classical
  let ι := {α : HomotopyGroup (Fin 1) Γ γ₀ // Work.Serre.piMapN g 1 γ₀ α = 1}
  let f : ι → C(cellSphere 0, Γ) := fun k => killFamily 0 Γ γ₀ k.1
  have hnull_g : ∀ k : ι, (g.comp (f k)).Homotopic (ContinuousMap.const (cellSphere 0) (g γ₀)) :=
    fun k => killFamily_comp_homotopic_const γ₀ g k.1 k.2
  have hnull_h : ∀ k : ι, (h.comp (f k)).Homotopic (ContinuousMap.const (cellSphere 0) (h γ₀)) :=
    fun k => killFamily_comp_homotopic_const γ₀ h k.1 ((hker k.1).mp k.2)
  have hkill_g : ∀ α : HomotopyGroup (Fin 1) Γ γ₀, Work.Serre.piMapN g 1 γ₀ α = 1 →
      Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α = 1 :=
    fun α hα => Work.Serre.CWModel.killSub (n := 0) Γ γ₀ ι (fun k : ι => k.1) ⟨α, hα⟩
  have hkill_h : ∀ α : HomotopyGroup (Fin 1) Γ γ₀, Work.Serre.piMapN h 1 γ₀ α = 1 →
      Work.Serre.piMapN (attachIncl 0 Γ ι f) 1 γ₀ α = 1 :=
    fun α hα => hkill_g α ((hker α).mpr hα)
  obtain ⟨G, hG, hbij_g⟩ := piOne_bijective_attachG γ₀ f g hnull_g hsurj_g hkill_g
  obtain ⟨G', hG', hbij_h⟩ := piOne_bijective_attachG γ₀ f h hnull_h hsurj_h hkill_h
  exact ⟨attachCells 0 Γ ι f, inferInstance, attachIncl 0 Γ ι f γ₀,
    attachG 0 Γ ι f g G hG, attachG 0 Γ ι f h G' hG', hbij_g, hbij_h⟩

end

end Work.EMFG

import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.RelPiPathDefs
import Submission.Work.RatHurewicz.RelPiPathBasepoint
import Submission.Work.StemsB.PiMap

/-!
# The homotopy fibre of `A ↪ Y` is path connected when `π₁(A) → π₁(Y)` is onto

Let `A ⊆ Y`, `i = setIncl A : ↥A → Y`, and let `E_{a₀}` be the homotopy fibre of `i` at `a₀`
(`Work.RatHurewicz.homotopyFibre`), i.e. the space of pairs `(a, γ)` with `γ` a path in `Y` from
`i a₀` to `i a`.  If `↥A` is path connected and `π₁(↥A, a₀) → π₁(Y, i a₀)` is surjective, then
`E_{a₀}` is path connected.  Indeed, `π₀(E_{a₀})` is the relative `π₁(Y, A, a₀)`, which vanishes
exactly when `A` is path connected and the inclusion induces a surjection on `π₁`.

The proof is elementary: given `(a, γ) ∈ E_{a₀}`, pick a path `β` in `A` from `a` to `a₀`; then
`γ ≫ i(β)` is a loop in `Y` at `i a₀`, so by surjectivity it is homotopic rel endpoints to the
image of a loop `λ` in `A`, and cancelling `i(β)` (in the homotopy groupoid) shows that `γ` is
homotopic to the image of the path `λ ≫ β⁻¹` of `A`, which is joined to the base point by
`Work.RatHurewicz.joined_basepoint_fibrePoint`.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Serre

open Work.StemsB

noncomputable section

/-! ## Two elementary lemmas about `genLoopEquivOfUnique` -/

/-- **Naturality of the identification `Ω^{1} X x ≃ Path x x`** with respect to postcomposition.
(This is `genLoopMap` vs. `Path.map`; both act by postcomposition, so the proof is `rfl`.) -/
theorem genLoopEquivOfUnique_genLoopMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : Ω^ (Fin 1) X x) :
    genLoopEquivOfUnique (X := Y) (x := f x) (Fin 1) (genLoopMap f 1 p) =
      (genLoopEquivOfUnique (X := X) (x := x) (Fin 1) p).map f.continuous := by
  ext t; rfl

/-- A homotopy relative to the boundary between generalized loops induces a homotopy of the
corresponding paths.  This is the forward half of the well-definedness of
`genLoopEquivOfUnique`, reproved here for direct use. -/
theorem genLoopEquivOfUnique_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : Ω^ (Fin 1) X x} (H : GenLoop.Homotopic p q) :
    (genLoopEquivOfUnique (X := X) (x := x) (Fin 1) p).Homotopic
      (genLoopEquivOfUnique (X := X) (x := x) (Fin 1) q) := by
  obtain ⟨H⟩ := H
  refine ⟨{ toFun := fun tx => H (tx.1, fun _ => tx.2)
            continuous_toFun := ?_
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }⟩
  · exact H.continuous.comp (by fun_prop)
  · exact H.apply_zero (fun _ => s)
  · exact H.apply_one (fun _ => s)
  · rcases hs with hs | hs
    · rw [hs]
      exact H.eq_fst t (x := fun _ => (0 : I)) ⟨default, Or.inl rfl⟩
    · rw [hs]
      exact H.eq_fst t (x := fun _ => (1 : I)) ⟨default, Or.inr rfl⟩

/-! ## Extracting a path of `A` homotopic to a given path of `Y` -/

/-- If `π₁(↥A, a₀) → π₁(Y, i a₀)` is surjective and `↥A` is path connected then every path of `Y`
from `i a₀` to a point `i a` of `A` is homotopic rel endpoints to the image of a path of `A` from
`a₀` to `a`. -/
theorem exists_path_map_homotopic_of_surj {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (hA : ∀ a : ↥A, Nonempty (Path a a₀))
    (hsurj : Function.Surjective (πmap (Work.RatHurewicz.setIncl A) 0 a₀))
    (a : ↥A) (γ : Path (Work.RatHurewicz.setIncl A a₀) (Work.RatHurewicz.setIncl A a)) :
    ∃ lam : Path a₀ a,
      (lam.map (Work.RatHurewicz.setIncl A).continuous).Homotopic γ := by
  obtain ⟨β⟩ := hA a
  -- the loop `γ ≫ i(β)` in `Y` at `i a₀`
  set s : Path (Work.RatHurewicz.setIncl A a) (Work.RatHurewicz.setIncl A a₀) :=
    Work.RatHurewicz.setInclPath a a₀ β with hs
  have hsmap : s = β.map (Work.RatHurewicz.setIncl A).continuous := rfl
  obtain ⟨μ, hμ⟩ :=
    hsurj ⟦(genLoopEquivOfUnique (X := Y) (x := Work.RatHurewicz.setIncl A a₀) (Fin 1)).symm
      (γ.trans s)⟧
  obtain ⟨lam0, rfl⟩ := Quotient.exists_rep μ
  rw [πmap_apply_mk] at hμ
  have hgen : GenLoop.Homotopic (genLoopMap (Work.RatHurewicz.setIncl A) 1 lam0)
      ((genLoopEquivOfUnique (X := Y) (x := Work.RatHurewicz.setIncl A a₀) (Fin 1)).symm
        (γ.trans s)) := Quotient.exact hμ
  have hpath := genLoopEquivOfUnique_homotopic hgen
  rw [genLoopEquivOfUnique_genLoopMap] at hpath
  rw [Equiv.apply_symm_apply] at hpath
  -- `λA` is the loop of `A` whose image is homotopic to `γ ≫ s`
  refine ⟨(genLoopEquivOfUnique (X := ↥A) (x := a₀) (Fin 1) lam0).trans β.symm, ?_⟩
  have hmap :
      ((genLoopEquivOfUnique (X := ↥A) (x := a₀) (Fin 1) lam0).trans β.symm).map
          (Work.RatHurewicz.setIncl A).continuous =
        ((genLoopEquivOfUnique (X := ↥A) (x := a₀) (Fin 1) lam0).map
            (Work.RatHurewicz.setIncl A).continuous).trans
          (β.symm.map (Work.RatHurewicz.setIncl A).continuous) :=
    Path.map_trans _ _ _
  rw [hmap]
  have hsymm : β.symm.map (Work.RatHurewicz.setIncl A).continuous = s.symm := by
    rw [hsmap, Path.map_symm]
  rw [hsymm]
  exact ((hpath.hcomp (Path.Homotopic.refl s.symm)).trans
    ((Path.Homotopic.trans_assoc γ s s.symm).trans
      (((Path.Homotopic.refl γ).hcomp (Path.Homotopic.trans_symm s)).trans
        (Path.Homotopic.trans_refl γ))))

/-- A point of the homotopy fibre is recovered from its path component. -/
theorem fibrePoint_fibrePath {Y : Type} [TopologicalSpace Y] {A : Set Y} {a₀ : ↥A}
    (p : Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀) :
    Work.RatHurewicz.fibrePoint (Work.RatHurewicz.fibrePath p) = p := rfl

/-- **The homotopy fibre of `A ↪ Y` is path connected** when `↥A` is path connected and the
inclusion induces a surjection on `π₁`. -/
theorem homotopyFibre_pathConnected {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (hA : ∀ a : ↥A, Nonempty (Path a a₀))
    (hsurj : Function.Surjective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀)) :
    PathConnectedSpace (Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀) := by
  have hjoin : ∀ p : Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀,
      Joined (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀) p := by
    intro p
    obtain ⟨lam, hlam⟩ :=
      exists_path_map_homotopic_of_surj a₀ hA hsurj p.1.1 (Work.RatHurewicz.fibrePath p)
    have h1 : Joined
        (Work.RatHurewicz.fibrePoint
          (lam.map (Work.RatHurewicz.setIncl A).continuous))
        (Work.RatHurewicz.fibrePoint (Work.RatHurewicz.fibrePath p)) :=
      Work.RatHurewicz.joined_fibrePoint_of_homotopic hlam
    rw [fibrePoint_fibrePath] at h1
    exact (Work.RatHurewicz.joined_basepoint_fibrePoint a₀ p.1.1 lam).trans h1
  exact ⟨⟨Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀⟩,
    fun p q => (hjoin p).symm.trans (hjoin q)⟩

end

end Work.Serre

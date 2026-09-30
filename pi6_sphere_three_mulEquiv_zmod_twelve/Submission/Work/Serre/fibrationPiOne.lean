import Mathlib
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.RelHomotopy

/-!
# Triviality of `π₁` of the total space of a Serre fibration with trivial `π₁` of base and fibre

For a Serre fibration `p : E → B` with fibre `F = p ⁻¹' {p e₀}`, the long exact homotopy sequence
of `Work.StemsB.FibrationLES` covers exactness at `π_{k+2}` for `k ≥ 0`; the low-degree clause
*exactness at `π₁(E)` of `π₁(F) → π₁(E) → π₁(B)`* is **not** part of that interface (there is no
group `π₀` for the sequence to continue into).  It is proved here directly from the relative
homotopy lifting property `HasHLPRel p 1` (`Work.StemsB.exists_lift_rel`):

given a loop `γ` of `E` based at `e₀` whose projection `p ∘ γ` is null-homotopic relative to the
boundary (which holds as soon as `π₁(B) = 1`), the null-homotopy lifts — with the lateral boundary
prescribed to be the constant `e₀` — to a homotopy from `γ` to a loop of the fibre `F`; hence
`π₁(F) → π₁(E)` is onto, and `π₁(E) = 1` when `π₁(F) = 1` too.

This is the degree-one case of `Work.Serre.piMap_fibreIncl_surjective_of_subsingleton`.  The
homotopy from `γ` to the lifted end loop is the one built in
`Work.Serre.relLoopHom` (for a general map rather than an inclusion).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 800000

/-- **Surjectivity of `π₁(F) → π₁(E)` when `π₁(B)` is trivial.**

A loop `γ` of `E` at `e₀` whose image in `π₁(B)` is trivial admits a null-homotopy relative to the
boundary; lifting it along the Serre fibration with the lateral boundary prescribed to be the
constant `e₀` produces a homotopy from `γ` to a loop of the fibre `F = p ⁻¹' {p e₀}` based at
`fibrePoint p e₀`, i.e. a preimage of the class of `γ` under `πmap (fibreIncl p (p e₀)) 0`. -/
theorem fibrationPiOne_surjective {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E)
    (hB : Subsingleton (HomotopyGroup (Fin 1) B (p e₀))) :
    Function.Surjective (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 0
      (Work.StemsB.fibrePoint p e₀)) := by
  intro y
  -- a representative loop of `y`
  obtain ⟨w, hw⟩ : ∃ w : Ω^ (Fin 1) E e₀, (⟦w⟧ : HomotopyGroup (Fin 1) E e₀) = y :=
    ⟨Quotient.out y, Quotient.out_eq y⟩
  -- its projection to `B` is null-homotopic relative to the boundary
  have hq : GenLoop.Homotopic (Work.StemsB.genLoopMap p 1 w)
      (GenLoop.const : Ω^ (Fin 1) B (p e₀)) := by
    have h1 : (⟦Work.StemsB.genLoopMap p 1 w⟧ : HomotopyGroup (Fin 1) B (p e₀)) =
        ⟦(GenLoop.const : Ω^ (Fin 1) B (p e₀))⟧ := hB.elim _ _
    exact Quotient.exact h1
  obtain ⟨Hq⟩ := hq
  -- the null-homotopy, in the coordinate convention of the relative HLP (cube coordinate first)
  let H : C((Fin 1 → I) × I, B) := ⟨fun q => Hq (q.2, q.1), by fun_prop⟩
  -- the prescribed lift of the lateral boundary, constantly `e₀`
  let g : C(Work.StemsB.CubeBdry 1 × I, E) := ContinuousMap.const _ e₀
  have hf : p.comp w.1 = H.comp (Work.StemsB.zeroIncl 1) := by
    ext x
    show p (w.1 x) = Hq (0, x)
    rw [show Hq (0, x) = (Work.StemsB.genLoopMap p 1 w).1 x from Hq.apply_zero x]
    rfl
  have hg : p.comp g = H.comp (Work.StemsB.bdryIncl 1) := by
    ext y
    show p e₀ = Hq (y.2, y.1.1)
    rw [show Hq (y.2, y.1.1) = (Work.StemsB.genLoopMap p 1 w).1 y.1.1 from Hq.eq_fst y.2 y.1.2]
    rw [show (Work.StemsB.genLoopMap p 1 w).1 y.1.1 = p (w.1 y.1.1) from rfl, w.2 y.1.1 y.1.2]
  have hg0 : ∀ x : Work.StemsB.CubeBdry 1, g (x, 0) = w.1 x.1 := by
    intro x
    show e₀ = w.1 x.1
    exact (w.2 x.1 x.2).symm
  -- lift the null-homotopy, with the lateral boundary fixed at `e₀`
  obtain ⟨G, hGp, hG0, hGbd⟩ := Work.StemsB.exists_lift_rel p hp 1 H w.1 hf g hg hg0
  -- the end loop of the lift
  let ρcm : C(Fin 1 → I, E) :=
    G.comp ((ContinuousMap.id (Fin 1 → I)).prodMk (ContinuousMap.const (Fin 1 → I) (1 : I)))
  have hρapply : ∀ x : Fin 1 → I, ρcm x = G (x, 1) := fun x => rfl
  have hρbdry : ∀ x ∈ Cube.boundary (Fin 1), ρcm x = e₀ := by
    intro x hx
    rw [hρapply]
    exact hGbd ⟨x, hx⟩ 1
  let ρ : Ω^ (Fin 1) E e₀ := ⟨ρcm, hρbdry⟩
  have hρapp : ∀ x : Fin 1 → I, ρ.1 x = G (x, 1) := fun x => rfl
  -- `w` is homotopic to `ρ`, relative to the boundary
  have hhom : ContinuousMap.HomotopyRel w.1 ρ.1 (Cube.boundary (Fin 1)) :=
    { toFun := fun q => G (q.2, q.1)
      continuous_toFun := G.continuous.comp (by fun_prop)
      map_zero_left := fun x => hG0 x
      map_one_left := fun x => hρapp x
      prop' := fun u x hx => (hGbd ⟨x, hx⟩ u).trans (w.2 x hx).symm }
  have hwρ : (⟦w⟧ : HomotopyGroup (Fin 1) E e₀) = ⟦ρ⟧ := Quotient.sound ⟨hhom⟩
  -- the end loop lies in the fibre
  have hmem : ∀ x : Fin 1 → I, p (ρ.1 x) = p e₀ := by
    intro x
    have h1 : p (G (x, 1)) = Hq (1, x) := by
      calc p (G (x, 1)) = H (x, 1) := congrFun (congrArg DFunLike.coe hGp) (x, 1)
        _ = Hq (1, x) := rfl
    calc p (ρ.1 x) = p (G (x, 1)) := by rw [hρapp]
      _ = Hq (1, x) := h1
      _ = (GenLoop.const : Ω^ (Fin 1) B (p e₀)).1 x := Hq.apply_one x
      _ = p e₀ := rfl
  let ρF : Ω^ (Fin 1) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) :=
    ⟨⟨fun x => ⟨ρ.1 x, hmem x⟩, Continuous.subtype_mk ρ.1.continuous hmem⟩,
      fun x hx => Subtype.ext (by
        show ρ.1 x = e₀
        exact hρbdry x hx)⟩
  refine ⟨⟦ρF⟧, ?_⟩
  have hρ_eq : Work.StemsB.genLoopMap (Work.StemsB.fibreIncl p (p e₀)) 1 ρF = ρ := by
    apply GenLoop.ext
    intro x
    rfl
  have key : (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 0
      (Work.StemsB.fibrePoint p e₀)) ⟦ρF⟧ = (⟦ρ⟧ : HomotopyGroup (Fin 1) E e₀) := by
    rw [Work.StemsB.πmap_apply_mk]
    exact congrArg Quotient.mk'' hρ_eq
  exact key.trans (hwρ.symm.trans hw)

end

end Work.Serre

import Mathlib
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.PiMap
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.ConnectingMap
import Submission.Work.StemsB.Fibrations

/-!
# `π₁`-exactness at the total space of a Serre fibration

For a Serre fibration `p : E → B` with fibre `F = p ⁻¹' {p e₀}`, the long exact homotopy sequence
of `Work.StemsB.FibrationLES` covers exactness at `π_{k+2}` for `k ≥ 0`; the low-degree clause
*exactness at `π₁(E)` of `π₁(F) → π₁(E) → π₁(B)`* is **not** part of that interface (there is no
group `π_0` for the sequence to continue into).  It is proved here directly from the relative
homotopy lifting property `HasHLPRel p 1` (`Work.StemsB.exists_lift_rel`):

given a loop `γ` of `E` based at `e₀` whose projection `p ∘ γ` is null-homotopic relative to the
boundary (which holds as soon as `π₁(B) = 1`), the null-homotopy lifts — with the lateral boundary
prescribed to be the constant `e₀` — to a homotopy from `γ` to a loop of the fibre `F`; hence
`π₁(F) → π₁(E)` is onto.

This is the degree-one case of `Work.Serre.piMap_fibreIncl_surjective_of_subsingleton`, needed for
the stable-stems input `Work.StemsB.StableStemsTorsion`.
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
theorem piMap_fibreIncl_surjective_pi1 {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E)
    (hB : Subsingleton (HomotopyGroup (Fin 1) B (p e₀))) :
    Function.Surjective (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) 0
      (Work.StemsB.fibrePoint p e₀)) := by
  intro y
  -- pick a representative loop of `y`
  obtain ⟨w, hw⟩ : ∃ w : Ω^ (Fin 1) E e₀, (⟦w⟧ : HomotopyGroup (Fin 1) E e₀) = y :=
    ⟨Quotient.out y, Quotient.out_eq y⟩
  -- its projection to `B` is null-homotopic relative to the boundary
  have hq : GenLoop.Homotopic (Work.StemsB.genLoopMap p 1 w)
      (GenLoop.const : Ω^ (Fin 1) B (p e₀)) := by
    have h1 : (⟦Work.StemsB.genLoopMap p 1 w⟧ : HomotopyGroup (Fin 1) B (p e₀)) =
        ⟦(GenLoop.const : Ω^ (Fin 1) B (p e₀))⟧ := hB.elim _ _
    exact Quotient.exact h1
  obtain ⟨Hq⟩ := hq
  -- the homotopy, in the coordinate convention of the relative HLP: cube coordinate first
  let H : C((Fin 1 → I) × I, B) :=
    ⟨fun q => Hq (q.2, q.1), Hq.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  -- the prescribed lift of the lateral boundary, constantly `e₀`
  let g : C(Work.StemsB.CubeBdry 1 × I, E) := ContinuousMap.const _ e₀
  have hf : p.comp w.1 = H.comp (Work.StemsB.zeroIncl 1) := by
    ext x
    show p (w.1 x) = Hq (0, x)
    calc p (w.1 x) = (Work.StemsB.genLoopMap p 1 w).1 x := rfl
      _ = Hq (0, x) := (Hq.apply_zero x).symm
  have hg : p.comp g = H.comp (Work.StemsB.bdryIncl 1) := by
    ext y
    show p e₀ = Hq (y.2, y.1.1)
    calc p e₀ = p (w.1 y.1.1) := congrArg p (w.2 y.1.1 y.1.2).symm
      _ = (Work.StemsB.genLoopMap p 1 w).1 y.1.1 := rfl
      _ = Hq (y.2, y.1.1) := (Hq.eq_fst y.2 y.1.2).symm
  have hg0 : ∀ x : Work.StemsB.CubeBdry 1, g (x, 0) = w.1 x.1 := by
    intro x
    show e₀ = w.1 x.1
    exact (w.2 x.1 x.2).symm
  -- lift the null-homotopy, with the lateral boundary fixed at `e₀`
  obtain ⟨G, hGp, hG0, hGbd⟩ := Work.StemsB.exists_lift_rel p hp 1 H w.1 hf g hg hg0
  -- the end loop of the lift lies in the fibre
  have hmem : ∀ v : Fin 1 → I, p (G (v, 1)) = p e₀ := by
    intro v
    have h1 : p (G (v, 1)) = Hq (1, v) := by
      calc p (G (v, 1)) = H (v, 1) := ContinuousMap.congr_fun hGp (v, 1)
        _ = Hq (1, v) := rfl
    calc p (G (v, 1)) = Hq (1, v) := h1
      _ = (GenLoop.const : Ω^ (Fin 1) B (p e₀)).1 v := Hq.apply_one v
      _ = p e₀ := rfl
  have hbd : ∀ v : Fin 1 → I, v ∈ Cube.boundary (Fin 1) →
      (⟨G (v, 1), hmem v⟩ : Work.StemsB.fibre p (p e₀)) = Work.StemsB.fibrePoint p e₀ := by
    intro v hv
    apply Subtype.ext
    show G (v, 1) = e₀
    exact (hGbd ⟨v, hv⟩ 1).trans rfl
  -- the lifted end loop, as an element of `Ω^1 F`
  let w' : Ω^ (Fin 1) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) :=
    ⟨⟨fun v => ⟨G (v, 1), hmem v⟩,
        Continuous.subtype_mk
          (G.continuous.comp (continuous_id.prodMk continuous_const)) hmem⟩,
      hbd⟩
  refine ⟨⟦w'⟧, ?_⟩
  rw [Work.StemsB.πmap_apply_mk, ← hw]
  refine Quotient.sound ?_
  -- the time-reversed lift is a homotopy, relative to the boundary, from the image of `w'` to `w`
  have hcont : Continuous (fun q : I × (Fin 1 → I) => G (q.2, unitInterval.symm q.1)) :=
    G.continuous.comp (continuous_snd.prodMk (unitInterval.continuous_symm.comp continuous_fst))
  have hHomRel : ContinuousMap.HomotopyRel
      ((Work.StemsB.genLoopMap (Work.StemsB.fibreIncl p (p e₀)) 1 w').1) w.1
      (Cube.boundary (Fin 1)) :=
    { toHomotopy :=
        { toContinuousMap :=
            ⟨fun q : I × (Fin 1 → I) => G (q.2, unitInterval.symm q.1), hcont⟩,
          map_zero_left := fun v => by
            show G (v, unitInterval.symm 0) = G (v, 1)
            rw [unitInterval.symm_zero],
          map_one_left := fun v => by
            show G (v, unitInterval.symm 1) = w.1 v
            rw [unitInterval.symm_one]
            exact hG0 v }
      prop' := fun t v hv => by
        show G (v, unitInterval.symm t) = G (v, 1)
        exact (hGbd ⟨v, hv⟩ (unitInterval.symm t)).trans (hGbd ⟨v, hv⟩ 1).symm }
  exact ⟨hHomRel⟩

end

end Work.Serre

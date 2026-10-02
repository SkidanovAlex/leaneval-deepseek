import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.Serre.exists_path_pullbackFst

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre of a Serre fibration over a simply-connected base is path connected

For a Serre fibration `p : E → B` with `E` and `B` path connected and `π₁(B, b₀)` trivial, the
fibre `F = p ⁻¹' {b₀}` is path connected.  This is the `π₀` clause of the long exact homotopy
sequence of a fibration, in the elementary form in which the whole argument is path lifting:

`π₁(B,b₀) → π₀(F) → π₀(E)` is exact at `π₀(F)`, and `π₀(E)` is a point, so `π₀(F)` is a quotient of
`π₁(B,b₀) = *`.  Explicitly, given `x y ∈ F`, take a path `α : Path x y` in `E`; its image
`λ = p ∘ α` is a loop of `B` at `b₀`, hence (trivial `π₁`) homotopic rel endpoints to the constant
loop.  Lifting that homotopy of paths along the fibration with initial condition `α` produces
`G : I × I → E` with `p (G (t,s)) = H (t,s)` and `G (0,s) = α s`.  The three paths
`t ↦ G (t,0)`, `s ↦ G (1,s)`, `t ↦ G (t,1)` all lie in the fibre (their images in `B` are the
lateral boundaries of the square, where the homotopy is constant equal to `b₀`), and they
concatenate to a path in `F` from `x` to `y`.

Nothing here is specific to the stable range: this is the general "`π₀` of the fibre" statement of
a Serre fibration, needed by `Submission/Work/Serre/periodicity_of_serreFibration.lean`.

## Contents

* `Work.Serre.homotopic_refl_of_subsingleton_pi1` — trivial `π₁` means every loop is
  null-homotopic (via the identity `HomotopyGroup (Fin 1) ≃ FundamentalGroup`).
* `Work.Serre.exists_liftPathHomotopy` — homotopy lifting for *paths*: the homotopy lifting
  property of a Serre fibration with respect to the unit interval `I = I¹`
  (equivalently, the `n = 1` case of `IsSerreFibration`, transported along `I ≅ I¹`).
* `Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration` — the target.
-/

open scoped Topology unitInterval

-- `haveI` is used below to pass the vanishing of `π₁` to the instance-implicit argument of
-- `Function.Surjective.subsingleton`; the style linter prefers `have` there, which instance
-- synthesis cannot use.
set_option linter.style.haveILetI false

namespace Work.Serre

noncomputable section

/-- **Trivial `π₁` means every loop is null-homotopic.**  The hypothesis is the vanishing of
`π₁(B,b₀)` in the `HomotopyGroup` model; Mathlib's `HomotopyGroup.pi1EquivFundamentalGroup`
identifies it with the fundamental group `Path.Homotopic.Quotient b₀ b₀`, whose elements are the
homotopy classes of loops, so every loop is homotopic rel endpoints to the constant loop. -/
theorem homotopic_refl_of_subsingleton_pi1 {B : Type*} [TopologicalSpace B] {b₀ : B}
    (hsc : Subsingleton (HomotopyGroup (Fin 1) B b₀)) (lam : Path b₀ b₀) :
    lam.Homotopic (Path.refl b₀) := by
  have hQ : Subsingleton (Path.Homotopic.Quotient b₀ b₀) := by
    haveI : Subsingleton (HomotopyGroup.Pi 1 B b₀) := hsc
    exact (HomotopyGroup.pi1EquivFundamentalGroup (x := b₀)).surjective.subsingleton
  haveI := hQ
  exact Quotient.exact (Subsingleton.elim (Path.Homotopic.Quotient.mk lam)
    (Path.Homotopic.Quotient.mk (Path.refl b₀)))

/-- **Homotopy lifting for paths.**  A Serre fibration has the homotopy lifting property with
respect to the unit interval: a homotopy `H : I × I → B` of paths in the base, together with a
lift `f` of its initial path `H (0, ·)`, lifts to a homotopy `G : I × I → E` over `H` starting at
`f`.

Equivalently, this is the `n = 1` case of `IsSerreFibration` transported along the homeomorphism
`(Fin 1 → I) ≃ₜ I`: the maps that are constant in the (unique) `Fin 1` coordinate are in bijection
with the maps out of `I`, and both directions preserve continuity, so the cube version supplies
the interval version. -/
theorem exists_liftPathHomotopy {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (H : C(I × I, B)) (f : C(I, E)) (hf : ∀ s : I, H (0, s) = p (f s)) :
    ∃ G : C(I × I, E), p.comp G = H ∧ ∀ s : I, G (0, s) = f s := by
  -- re-index the second coordinate by `Fin 1 → I`, using only the constant functions
  let H' : C(I × (Fin 1 → I), B) :=
    ⟨fun q => H (q.1, q.2 default),
      H.continuous.comp (continuous_fst.prodMk ((continuous_apply default).comp continuous_snd))⟩
  let f' : C(Fin 1 → I, E) :=
    ⟨fun v => f (v default), f.continuous.comp (continuous_apply default)⟩
  have hf' : ∀ v : Fin 1 → I, H' (0, v) = p (f' v) := fun v => hf (v default)
  obtain ⟨G', hG', hG'0⟩ := Work.StemsB.hasHLP_rlp (hp 1) H' f' hf'
  refine ⟨⟨fun q : I × I => G' (q.1, fun _ => q.2),
    G'.continuous.comp (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))⟩, ?_, ?_⟩
  · ext q
    have h1 : p (G' (q.1, fun _ => q.2)) = H' (q.1, fun _ => q.2) :=
      congrFun (congrArg DFunLike.coe hG') (q.1, fun _ => q.2)
    simpa [H', ContinuousMap.comp_apply] using h1
  · intro s
    have h1 : G' (0, fun _ => s) = f' (fun _ => s) := hG'0 (fun _ => s)
    simpa [f'] using h1

/-- **The fibre of a Serre fibration is path connected when the base is simply connected.**

Let `p : E → B` be a Serre fibration with `E` and `B` path connected and `π₁(B,b₀)` trivial.  Then
`F = p ⁻¹' {b₀}` is path connected.

Given `x y ∈ F`, choose a path `α : Path x y` in `E` (possible since `E` is path connected); its
image `λ = p ∘ α` is a loop of `B` at `b₀` and therefore null-homotopic rel endpoints.  Lifting
that homotopy along `p` with initial condition `α` gives `G : I × I → E` over the square, and the
three sides of the square through `G` that lie over the boundary of the square are paths of the
fibre; concatenating them gives a path in `F` from `x` to `y`.  Nonemptiness of `F` is path
lifting of a path of `B` from `p e₀` to `b₀`
(`Work.Serre.exists_path_lift_of_isSerreFibration`). -/
theorem pathConnectedSpace_fibre_of_isSerreFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    (hE : PathConnectedSpace E) (hB : PathConnectedSpace B)
    (hsc : Subsingleton (HomotopyGroup (Fin 1) B b₀)) :
    PathConnectedSpace (Work.StemsB.fibre p b₀) := by
  -- the fibre is nonempty: lift a path of `B` from the image of a point of `E` to `b₀`
  have hne : Nonempty (Work.StemsB.fibre p b₀) := by
    obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
    obtain ⟨τ⟩ : Nonempty (Path (p e₀) b₀) := hB.joined (p e₀) b₀
    obtain ⟨e', he', _⟩ := exists_path_lift_of_isSerreFibration p hp rfl τ
    exact ⟨⟨e', he'⟩⟩
  refine ⟨hne, fun x y => ?_⟩
  -- a path of `E` from `x` to `y`, and its image, a loop of `B` at `b₀`
  obtain ⟨α⟩ : Nonempty (Path x.1 y.1) := hE.joined x.1 y.1
  let lam : Path b₀ b₀ := (α.map p.continuous).cast x.2.symm y.2.symm
  have hlam : ∀ s : I, lam.toContinuousMap s = p (α.toContinuousMap s) := fun s => rfl
  -- `λ` is null-homotopic, and the homotopy lifts with initial condition `α`
  obtain ⟨Hp⟩ := homotopic_refl_of_subsingleton_pi1 hsc lam
  have hf : ∀ s : I, Hp.toContinuousMap (0, s) = p (α.toContinuousMap s) := by
    intro s
    have h1 : Hp.toContinuousMap (0, s) = lam.toContinuousMap s := Hp.apply_zero s
    exact h1.trans (hlam s)
  obtain ⟨G, hG, hG0⟩ := exists_liftPathHomotopy p hp Hp.toContinuousMap α.toContinuousMap hf
  -- the fibrewise condition along the three sides of the square
  have hGp : ∀ q : I × I, p (G q) = Hp.toContinuousMap q := by
    intro q
    have h1 := congrFun (congrArg DFunLike.coe hG) q
    simpa [ContinuousMap.comp_apply] using h1
  have hcol0 : ∀ t : I, p (G (t, 0)) = b₀ := by
    intro t
    have h1 : p (G (t, 0)) = Hp.toContinuousMap (t, (0 : I)) := hGp (t, (0 : I))
    have h2 : Hp.toContinuousMap (t, (0 : I)) = (Path.refl b₀).toContinuousMap 0 :=
      Hp.eq_snd t (by simp)
    exact h1.trans (h2.trans (Path.refl_apply b₀ 0))
  have hcol1 : ∀ t : I, p (G (t, 1)) = b₀ := by
    intro t
    have h1 : p (G (t, 1)) = Hp.toContinuousMap (t, (1 : I)) := hGp (t, (1 : I))
    have h2 : Hp.toContinuousMap (t, (1 : I)) = (Path.refl b₀).toContinuousMap 1 :=
      Hp.eq_snd t (by simp)
    exact h1.trans (h2.trans (Path.refl_apply b₀ 1))
  have hrow : ∀ s : I, p (G (1, s)) = b₀ := by
    intro s
    have h1 : p (G (1, s)) = Hp.toContinuousMap ((1 : I), s) := hGp ((1 : I), s)
    have h2 : Hp.toContinuousMap ((1 : I), s) = (Path.refl b₀).toContinuousMap s :=
      Hp.apply_one s
    exact h1.trans (h2.trans (Path.refl_apply b₀ s))
  -- the three paths of the fibre, concatenated
  let xm : Work.StemsB.fibre p b₀ := ⟨G (1, 0), hcol0 1⟩
  let ye : Work.StemsB.fibre p b₀ := ⟨G (1, 1), hcol1 1⟩
  have P₁ : Path x xm :=
    Path.mk ⟨fun t : I => ⟨G (t, 0), hcol0 t⟩,
        Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const)) hcol0⟩
      (Subtype.ext ((hG0 (0 : I)).trans α.source')) (Subtype.ext rfl)
  have P₂ : Path xm ye :=
    Path.mk ⟨fun s : I => ⟨G (1, s), hrow s⟩,
        Continuous.subtype_mk (G.continuous.comp (continuous_const.prodMk continuous_id)) hrow⟩
      (Subtype.ext rfl) (Subtype.ext rfl)
  have P₃ : Path y ye :=
    Path.mk ⟨fun t : I => ⟨G (t, 1), hcol1 t⟩,
        Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const)) hcol1⟩
      (Subtype.ext ((hG0 (1 : I)).trans α.target')) (Subtype.ext rfl)
  exact ⟨P₁.trans (P₂.trans P₃.symm)⟩

end

end Work.Serre

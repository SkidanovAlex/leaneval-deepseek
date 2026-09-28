import Mathlib
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.exists_path_pullbackFst

/-!
# Lifts of a null-homotopic loop are joined inside the fibre

Let `p : E → B` be a Serre fibration, `b : B`, `lam : Path b b` a loop of the base and
`w : C(I, E)` a lift of `lam` (`p ∘ w = lam`).  If `lam` is homotopic to the constant loop at `b`,
then the endpoints `w 0` and `w 1` of the lift are joined by a path lying entirely in the fibre
`p ⁻¹' {b}`.

The proof is the elementary path-lifting argument: a homotopy `H : I × I → B` from `lam` to the
constant loop has all of `∂(I × I) ∖ ({0} × I)` mapped to `b` (because `H (·, 0) = lam` and
`H (·, 1) = refl b` agree on the ends of the second coordinate, and `H (1, ·) = refl b`).  Lifting
`H` along `p` with initial condition `w` gives `G : I × I → E` over `H`, and the three sides
`t ↦ G (t, 0)`, `s ↦ G (1, s)`, `t ↦ G (t, 1)` of the square through `G` lie over points of `B`
that are equal to `b`, hence are paths of the fibre.  Concatenating them gives the required path
from `w 0` to `w 1`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **Lifts of a null-homotopic loop are joined inside the fibre.**  A Serre fibration `p : E → B`,
a loop `lam` of `B` at `b`, a lift `w` of `lam` and a null-homotopy of `lam` produce a path in the
fibre `p ⁻¹' {b}` between the two endpoints of `w`. -/
theorem joinedIn_fibre_of_homotopic_const {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b : B} (lam : Path b b)
    (w : C(unitInterval, E)) (hw : p.comp w = lam.toContinuousMap)
    (h : lam.Homotopic (Path.refl b)) :
    JoinedIn (p ⁻¹' {b}) (w 0) (w 1) := by
  obtain ⟨Hp⟩ := h
  -- `w` is a lift of the initial path `Hp (0, ·) = lam` of the homotopy
  have hf : ∀ s : I, Hp.toContinuousMap (0, s) = p (w s) := fun s => by
    have h1 : Hp.toContinuousMap (0, s) = lam.toContinuousMap s := Hp.apply_zero s
    have h2 : p (w s) = lam.toContinuousMap s := congrFun (congrArg DFunLike.coe hw) s
    exact h1.trans h2.symm
  obtain ⟨G, hG, hG0⟩ := exists_liftPathHomotopy p hp Hp.toContinuousMap w hf
  -- `G` is a lift of `Hp`
  have hGp : ∀ q : I × I, p (G q) = Hp.toContinuousMap q := fun q => by
    have h1 := congrFun (congrArg DFunLike.coe hG) q
    simpa [ContinuousMap.comp_apply] using h1
  -- the three sides of the square (other than the initial one) lie over `b`
  have hcol0 : ∀ t : I, p (G (t, 0)) = b := fun t =>
    (hGp (t, 0)).trans ((Hp.eq_snd t (by simp)).trans (Path.refl_apply b 0))
  have hcol1 : ∀ t : I, p (G (t, 1)) = b := fun t =>
    (hGp (t, 1)).trans ((Hp.eq_snd t (by simp)).trans (Path.refl_apply b 1))
  have hrow : ∀ s : I, p (G (1, s)) = b := fun s =>
    (hGp (1, s)).trans ((Hp.apply_one s).trans (Path.refl_apply b s))
  -- the three paths of the fibre, concatenated
  have J₁ : JoinedIn (p ⁻¹' {b}) (w 0) (G (1, 0)) :=
    ⟨⟨⟨fun t : I => G (t, 0),
        G.continuous.comp (continuous_id.prodMk continuous_const)⟩, hG0 0, rfl⟩,
      fun t => hcol0 t⟩
  have J₂ : JoinedIn (p ⁻¹' {b}) (G (1, 0)) (G (1, 1)) :=
    ⟨⟨⟨fun s : I => G (1, s),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩, rfl, rfl⟩,
      fun s => hrow s⟩
  have J₃ : JoinedIn (p ⁻¹' {b}) (w 1) (G (1, 1)) :=
    ⟨⟨⟨fun t : I => G (t, 1),
        G.continuous.comp (continuous_id.prodMk continuous_const)⟩, hG0 1, rfl⟩,
      fun t => hcol1 t⟩
  exact J₁.trans (J₂.trans J₃.symm)

end

end Work.Serre

import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl

namespace Work.Serre

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

/-- The `0`-cube of `X` at the base point `x₀` whose value is `a`.  (The boundary of the `0`-cube is
empty, so there is no boundary condition.)  Its class in `π₀(X,x₀)` is the path component of `a`,
which is the bridge between the algebraic form of `π₀`-surjectivity and paths in `X`. -/
def zeroCube (X : Type) [TopologicalSpace X] (x₀ a : X) : Ω^ (Fin 0) X x₀ :=
  ⟨ContinuousMap.const (Fin 0 → I) a, fun y hy => by obtain ⟨i, _⟩ := hy; exact i.elim0⟩

/-- **Surjectivity of `π₀(f)` in geometric form**: if `π₀(f) : π₀(X,x₀) → π₀(Y,f x₀)` is
surjective, then every `y : Y` is joined to `f x` for some `x : X`.

The class of `y` in `π₀(Y,f x₀)` is represented by the constant `0`-cube at `y`; a preimage `a` of it
is represented by a `0`-cube `γ` of `X`, and the homotopy `genLoopMap f 0 γ ~` (constant at `y`)
evaluated on the (unique) point of `I^0` is the required path `f (γ 0) → y`. -/
theorem exists_path_of_piMapN_zero_surjective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x₀ : X) (h : Function.Surjective (piMapN f 0 x₀)) (y : Y) :
    ∃ x : X, Nonempty (Path y (f x)) := by
  obtain ⟨a, ha⟩ := h ⟦zeroCube Y (f x₀) y⟧
  set γ : Ω^ (Fin 0) X x₀ := Quotient.out a with hγ
  have hγ' : (⟦γ⟧ : HomotopyGroup (Fin 0) X x₀) = a := by
    rw [hγ]; exact Quotient.out_eq a
  have h1 : (⟦Work.StemsB.genLoopMap f 0 γ⟧ : HomotopyGroup (Fin 0) Y (f x₀))
      = ⟦zeroCube Y (f x₀) y⟧ := by
    rw [← piMapN_apply_mk, hγ']
    exact ha
  have hHom : GenLoop.Homotopic (Work.StemsB.genLoopMap f 0 γ) (zeroCube Y (f x₀) y) :=
    Quotient.exact h1
  obtain ⟨H⟩ := hHom
  let c : Fin 0 → I := fun _ => 0
  refine ⟨γ c, ?_⟩
  have hsrc : H (0, c) = f (γ c) := by
    simp only [ContinuousMap.HomotopyWith.apply_zero]
    exact Work.StemsB.genLoopMap_apply f 0 γ c
  have htgt : H (1, c) = y := by
    simp only [ContinuousMap.HomotopyWith.apply_one]
    rfl
  have hcont : Continuous fun t : I => H (t, c) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have hpath : Path (f (γ c)) y :=
    Path.mk ⟨fun t => H (t, c), hcont⟩ hsrc htgt
  exact ⟨hpath.symm⟩

/-- **`0`-connectivity of the mapping-cylinder pair.**

If `X` is nonempty and `f : X → Y` is surjective on `π₀` (every point of `Y` is joined by a path to a
point of the image of `f`), then every point of the mapping cylinder `cyl f` is joined by a path to
the bottom copy `Set.range (cylIncl f)`.  This is the `hconn0` hypothesis of
`Work.Serre.rangeWhiteheadPair` in the case `i = cylIncl f`, and it removes the
`PathConnectedSpace` hypotheses of the earlier `Work.Serre.cylConnected`.

Route: a point of the cylinder is `⟦inl (p,t)⟧` or `cylInr f y`.  In the first case
`Work.Serre.cylVertPath f p t` is a path from `⟦inl (p,t)⟧` down to `cylIncl f p`.  In the second,
surjectivity of `π₀(f)` at any base point `x₀ : X` gives `x : X` and a path from `y` to `f x` in
`Y`; mapping it by `cylInr f` and using `Work.Serre.cyl_mk_inl_one` (the top copy of the cylinder is
the target) and `Work.Serre.cylVertPath f x 1` (from `⟦inl (x,1)⟧` down to `cylIncl f x`) gives the
required path.  The element of `HomotopyGroup (Fin 0) Y (f x₀)` representing the component of `y` is
`Quotient.mk _` of the constant cube at `y`; an equality of such classes is a path
(`HomotopyGroup.pi0EquivZerothHomotopy` plus the `ZerothHomotopy` API, or the
`GenLoop.Homotopic`-to-`Joined` bridge used elsewhere in `Submission/Work/Serre/`).

The hypothesis `[Nonempty X]` is needed: for `X` empty and `Y = PUnit` the `π₀` condition is vacuous
while `cyl f ≅ Y` is nonempty, so the conclusion, which demands a witness `x : X`, is false. -/
theorem cylJoinedIncl {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (h : ∀ x : X, Function.Surjective (Work.Serre.piMapN f 0 x)) :
    ∀ w : cyl f, ∃ x : X, Nonempty (Path w (cylIncl f x)) := by
  intro w
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  induction w using Quotient.inductionOn with
  | h z =>
      rcases z with ⟨p, t⟩ | y
      · exact ⟨p, ⟨cylVertPath f p t⟩⟩
      · obtain ⟨x, ⟨γY⟩⟩ := exists_path_of_piMapN_zero_surjective f x₀ (h x₀) y
        exact ⟨x, ⟨((γY.map (cylInr f).continuous).cast rfl (cyl_mk_inl_one f x)).trans
          (cylVertPath f x 1)⟩⟩

end

end Work.Serre

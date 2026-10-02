import Mathlib
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.Serre.cylJoinedIncl

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Path lifting, and `π₀`-surjectivity of the base change of a Serre fibration

The main statement `Work.Serre.exists_path_pullbackFst` is the `π₀` clause needed by
`Submission/Work/Serre/pullbackFst_piMapN_bijective.lean`: if `q : E → B` is a Serre fibration and
`g : Γ → B` induces a surjection on `π₀`, then every point of `E` is joined by a path to a point of
the image of `pullbackFst q g`.  The auxiliary `Work.Serre.exists_path_lift_of_isSerreFibration` is
path lifting with prescribed starting point for a Serre fibration, obtained from the relative
homotopy lifting property in degree `0`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **Path lifting with prescribed starting point** for a Serre fibration: a path `γ : Path b b'` in
the base with `q e = b` lifts to a path starting at `e` and ending over `b'`.

This is the degree-`0` case of the relative homotopy lifting property
(`Work.StemsB.HasHLPRel`), whose lateral boundary is empty for `k = 0`. -/
theorem exists_path_lift_of_isSerreFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (q : C(E, B)) (hq : Work.StemsB.IsSerreFibration q) {e : E} {b b' : B}
    (hb : q e = b) (γ : Path b b') : ∃ e' : E, q e' = b' ∧ Nonempty (Path e e') := by
  -- the homotopy to lift: the path `γ`, with the point coordinate first (`HasHLPRel` convention)
  let H : C((Fin 0 → I) × I, B) :=
    ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  -- the prescribed lift at time `0`: the constant map at `e`
  let f : C(Fin 0 → I, E) := ContinuousMap.const (Fin 0 → I) e
  have hf : q.comp f = H.comp (Work.StemsB.zeroIncl 0) := by
    ext z
    show q e = γ (z, 0).2
    rw [hb]
    exact (γ.source').symm
  -- the (empty) lateral boundary
  let g₀ : C(Work.StemsB.CubeBdry 0 × I, E) := ContinuousMap.const _ e
  have hg : q.comp g₀ = H.comp (Work.StemsB.bdryIncl 0) := by
    ext z
    obtain ⟨i, _⟩ := z.1.2
    exact i.elim0
  have hg0 : ∀ x : Work.StemsB.CubeBdry 0, g₀ (x, 0) = f x.1 := by
    intro x
    obtain ⟨i, _⟩ := x.2
    exact i.elim0
  obtain ⟨G, hGq, hG0, -⟩ :=
    Work.StemsB.exists_lift_rel q hq 0 H f hf g₀ hg hg0
  let z₀ : Fin 0 → I := fun i => i.elim0
  refine ⟨G (z₀, 1), ?_, ⟨?_⟩⟩
  · have h : q (G (z₀, 1)) = H (z₀, 1) := by
      simpa using congrFun (congrArg DFunLike.coe hGq) (z₀, 1)
    show q (G (z₀, 1)) = b'
    rw [h]
    exact γ.target'
  · refine Path.mk ⟨fun t : I => G (z₀, t),
      G.continuous.comp (continuous_const.prodMk continuous_id)⟩ ?_ ?_
    · show G (z₀, 0) = e
      rw [hG0 z₀]
      rfl
    · rfl

/-- **`π₀`-surjectivity of the base change of a Serre fibration.**  If `q : E → B` is a Serre
fibration, `g : C(Γ,B)` induces a surjection on `π₀` (at the base point `γ₀`), then every point of
`E` is joined by a path to a point of the image of the projection
`pullbackFst q g : Pullback q g → E`.

The hypothesis is satisfiable only through an actual point `γ₀ : Γ`: if `Γ` is empty then so is the
pullback, which is why the statement takes `γ₀` explicitly rather than a `[Nonempty Γ]` instance. -/
theorem exists_path_pullbackFst {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] (q : C(E, B)) (g : C(Γ, B)) (hq : Work.StemsB.IsSerreFibration q)
    (N : ℕ) (γ₀ : Γ)
    (hg : ∀ i : ℕ, i ≤ N → ∀ γ : Γ, Function.Bijective (Work.Serre.piMapN g i γ)) :
    ∀ w : E, ∃ x : Work.StemsB.Pullback q g,
      Nonempty (Path w (Work.StemsB.pullbackFst q g x)) := by
  intro w
  obtain ⟨γ, ⟨pp⟩⟩ := Work.Serre.exists_path_of_piMapN_zero_surjective g γ₀
    (hg 0 (Nat.zero_le N) γ₀).2 (q w)
  obtain ⟨e', he', ⟨p'⟩⟩ :=
    exists_path_lift_of_isSerreFibration q hq (e := w) rfl pp
  exact ⟨⟨(e', γ), he'⟩, ⟨p'⟩⟩

end

end Work.Serre

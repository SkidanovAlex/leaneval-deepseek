import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.exists_lift_degree

/-!
# Homotopy invariance of the degree of a circle map

`Submission/Work/Drive/WindingNumber.lean` defines the degree `degree f hf` of a continuous circle
map `f : ℝ/ℤ → ℝ/ℤ` as the monodromy of a lift to `ℝ`.  Here we prove the fundamental structural
property: **homotopic maps have equal degree**.

The proof avoids the (false, in general) statement that a free homotopy can be converted into a
basepoint-preserving one.  Instead we lift the *whole* homotopy along the universal covering
`ℝ → ℝ/ℤ` using the homotopy lifting property `IsCoveringMap.liftHomotopy` for maps out of the
connected space `I`: writing `H : I → C(ℝ/ℤ, ℝ/ℤ)` for the homotopy and `f̃` for the chosen lift
of `f`, the lifted homotopy `H̃` satisfies `(H̃ (t,s) : ℝ/ℤ) = H t s`.  The *monodromy*
`D (t, s) = H̃ (t, s + 1) - H̃ (t, s)` is continuous on the connected space `I × ℝ` and takes values
in `ℤ`, hence is constant; at `t = 0` it equals `degree f` and at `t = 1` it is the monodromy of the
lift `s ↦ H̃ (1, s)` of `g`, which therefore also equals `degree g`.
-/

namespace Work.Drive

/-- **Homotopy invariance of the degree.**  Homotopic continuous circle maps have the same degree.

Proof route: lift the *whole* homotopy `H : ℝ/ℤ × I → ℝ/ℤ` through the covering map `ℝ → ℝ/ℤ` to a
continuous `H̃ : ℝ × I → ℝ` with `(H̃ (t,s) : ℝ/ℤ) = H ((t,s))` — for instance by composing `H` with
the identification `ℝ ≃ ℝ/ℤ × I`-charts, or by `IsCoveringMap.exists_path_lifts` along the paths
`s ↦ H (t, s)` with the monodromy proved independent of `t` — and then note that
`s ↦ H̃ (t + 1, s) - H̃ (t, s)` is continuous and integer-valued on the connected space `I`, hence
constant in `s`; comparing `s = 0` and `s = 1` and using `degree_eq_of_lift` (in
`Submission/Work/Drive/WindingNumber.lean`) identifies the two monodromies.  (A direct appeal to
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` needs the two loops to share a basepoint, which
a free homotopy does not provide.) -/
theorem degree_homotopic {f g : C(UnitAddCircle, UnitAddCircle)} (h : f.Homotopic g) :
    degree f f.continuous = degree g g.continuous := by
  obtain ⟨F⟩ := h
  -- The quotient map `ℝ → ℝ/ℤ` is a covering map.
  have hcov : IsCoveringMap ((↑) : ℝ → UnitAddCircle) := AddCircle.isCoveringMap_coe (1 : ℝ)
  let mkC : C(ℝ, UnitAddCircle) := ⟨((↑) : ℝ → UnitAddCircle), by fun_prop⟩
  -- The homotopy `F` reindexed with `A = ℝ` as the source.
  let H : C(unitInterval × ℝ, UnitAddCircle) :=
    F.toContinuousMap.comp ((ContinuousMap.id unitInterval).prodMap mkC)
  -- The chosen lift of `f` as a continuous map `ℝ → ℝ`.
  let f₀' : C(ℝ, ℝ) := ⟨liftOf f f.continuous, liftOf_continuous f f.continuous⟩
  have hH0 : ∀ a : ℝ, H (0, a) = ((↑) : ℝ → UnitAddCircle) (f₀' a) := by
    intro a
    show F (0, (a : UnitAddCircle)) = ((↑) : ℝ → UnitAddCircle) (liftOf f f.continuous a)
    rw [F.apply_zero, liftOf_lifts f f.continuous a]
  -- `G` is the lift of the whole homotopy, by the homotopy lifting property (Hurewicz fibration).
  let G := hcov.liftHomotopy H f₀' hH0
  have hGlift : ∀ ta : unitInterval × ℝ, ((G ta : ℝ) : UnitAddCircle) = H ta :=
    fun ta => congr_fun (hcov.liftHomotopy_lifts H f₀' hH0) ta
  have hG0 : ∀ a : ℝ, G (0, a) = liftOf f f.continuous a := fun a => by
    rw [hcov.liftHomotopy_zero H f₀' hH0 a]; rfl
  -- The lift of `g` obtained at the far end of the homotopy.
  let K : ℝ → ℝ := fun a => G (1, a)
  have hKcont : Continuous K := by
    dsimp only [K]
    exact G.continuous.comp (continuous_const.prodMk continuous_id)
  have hKlift : ∀ a : ℝ, ((K a : ℝ) : UnitAddCircle) = g (a : UnitAddCircle) := by
    intro a
    have h1 : ((G (1, a) : ℝ) : UnitAddCircle) = H (1, a) := hGlift (1, a)
    show ((G (1, a) : ℝ) : UnitAddCircle) = g (a : UnitAddCircle)
    rw [h1]
    show F (1, (a : UnitAddCircle)) = g (a : UnitAddCircle)
    rw [F.apply_one]
  -- The monodromy of the lifted homotopy.
  let D : unitInterval × ℝ → ℝ := fun x => G (x.1, x.2 + 1) - G (x.1, x.2)
  -- `D` is integer-valued: at each time `t`, `s` and `s + 1` have the same image in `ℝ/ℤ`.
  have hDint : ∀ x : unitInterval × ℝ, ∃ k : ℤ, D x = (k : ℝ) := by
    rintro ⟨t, a⟩
    have h1 : ((G (t, a + 1) : ℝ) : UnitAddCircle) = (G (t, a) : UnitAddCircle) := by
      rw [hGlift (t, a + 1), hGlift (t, a)]
      show H (t, a + 1) = H (t, a)
      show F (t, ((a + 1 : ℝ) : UnitAddCircle)) = F (t, (a : UnitAddCircle))
      rw [AddCircle.coe_add_period (1 : ℝ) a]
    have h2 : (G (t, a + 1) - G (t, a) : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      rw [← coe_eq_coe_iff_sub_mem (1 : ℝ)]
      exact h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
    have hk' : G (t, a + 1) - G (t, a) = (k : ℝ) := by simpa using hk.symm
    exact ⟨k, hk'⟩
  have hDcont : Continuous D := by
    dsimp only [D]
    fun_prop
  -- Being continuous and integer-valued, `D` is locally constant...
  have hloc : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨mx, hmx⟩ := hDint x
    refine ⟨{y : unitInterval × ℝ | dist (D y) (D x) < 1/2},
      Metric.isOpen_ball.preimage hDcont, by simp, ?_⟩
    intro y hy
    obtain ⟨my, hmy⟩ := hDint y
    have hx_eq : D x = (mx : ℝ) := hmx
    have hy_eq : D y = (my : ℝ) := hmy
    have hlt : |(my : ℝ) - (mx : ℝ)| < 1 := by
      have hy' : dist (D y) (D x) < 1/2 := hy
      rw [Real.dist_eq, hy_eq, hx_eq] at hy'
      linarith
    rw [hy_eq, hx_eq, Int.cast_inj]
    exact int_eq_of_abs_sub_lt_one hlt
  -- ... hence constant on the connected space `I × ℝ`.
  have hDconst : ∀ x y : unitInterval × ℝ, D x = D y := (IsLocallyConstant.iff_is_const.mp hloc)
  have hkey : ∀ a : ℝ, D (1, a) = (degree f f.continuous : ℝ) := by
    intro a
    have h1 : D (1, a) = D (0, a) := hDconst (1, a) (0, a)
    have h2 : D (0, a) = (degree f f.continuous : ℝ) := by
      show G (0, a + 1) - G (0, a) = (degree f f.continuous : ℝ)
      rw [hG0 (a + 1), hG0 a, liftOf_add_one f f.continuous a]
      ring
    exact h1.trans h2
  have hKmono : ∀ a : ℝ, K (a + 1) = K a + (degree f f.continuous : ℝ) := by
    intro a
    have h1 := hkey a
    show G (1, a + 1) = G (1, a) + (degree f f.continuous : ℝ)
    linarith
  -- The lift `K` of `g` has monodromy `degree f`, so by `degree_eq_of_lift` so does `g`.
  exact degree_eq_of_lift (f := ⇑g) g.continuous hKcont hKlift hKmono

end Work.Drive

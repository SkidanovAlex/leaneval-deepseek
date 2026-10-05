import Mathlib

namespace Work.RPB.Port.Drive

open AddSubgroup

/-- Two reals have the same class in `ℝ/ℤ` (`= AddCircle p`) exactly when they differ by a
multiple of the period `p`.  Companion of `AddCircle.coe_eq_zero_iff`. -/
lemma coe_eq_coe_iff_sub_mem {𝕜 : Type*} [AddCommGroup 𝕜] (p : 𝕜) {x y : 𝕜} :
    (x : AddCircle p) = (y : AddCircle p) ↔ x - y ∈ AddSubgroup.zmultiples p := by
  have key : ((x : AddCircle p) = (y : AddCircle p)) ↔
      ((x : AddCircle p) - (y : AddCircle p) = 0) := sub_eq_zero.symm
  rw [key, ← AddCircle.coe_sub p, AddCircle.coe_eq_zero_iff, AddSubgroup.mem_zmultiples_iff]

/-- Two integers whose difference is `< 1` in absolute value are equal.  Used to see that a
continuous, integer-valued function is locally constant. -/
lemma int_eq_of_abs_sub_lt_one {a b : ℤ} (h : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  have h1 : (a : ℝ) - b < 1 := (abs_lt.mp h).2
  have h2 : -(1 : ℝ) < (a : ℝ) - b := (abs_lt.mp h).1
  have hb1 : ((b + 1 : ℤ) : ℝ) = (b : ℝ) + 1 := by push_cast; ring
  have ha1 : ((a + 1 : ℤ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hab : a ≤ b := by
    have : (a : ℝ) < ((b + 1 : ℤ) : ℝ) := by rw [hb1]; linarith
    exact Int.lt_add_one_iff.mp (Int.cast_lt.mp this)
  have hba : b ≤ a := by
    have : (b : ℝ) < ((a + 1 : ℤ) : ℝ) := by rw [ha1]; linarith
    exact Int.lt_add_one_iff.mp (Int.cast_lt.mp this)
  omega

/-- **The degree of a circle map: existence of a lifted walk.**

For every continuous `f : ℝ/ℤ → ℝ/ℤ` there is a continuous `F : ℝ → ℝ` lifting `f`
(`(F t : ℝ/ℤ) = f t` for all real `t`) whose *monodromy* is a constant integer `n`, i.e.
`F (t + 1) = F t + n` for all `t`.  This `n` is the degree (winding number) of `f`.

Mathlib has no degree/winding theory for circle maps but it does have the ingredients:
`AddCircle.isCoveringMap_coe` (the quotient map `ℝ → ℝ/ℤ` is a covering map, hence a local
homeomorphism), the path-lifting property `IsCoveringMap.exists_path_lifts`,
`IsCoveringMap.liftPath`, the homotopy invariance
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`, and the general lifting theorem
`IsCoveringMap.existsUnique_continuousMap_lifts` for a path-connected, locally path-connected source
(sibling files `Submission/Work/Drive/exists_angle_line.lean`, `exists_angle_tri.lean` already apply
that machinery with source `ℝ`).  The monodromy `F (t+1) - F t` lies in `ℤ` (because `t + 1` and `t`
have the same image in `ℝ/ℤ`, cf. `AddCircle.coe_eq_coe_iff_sub_mem`) and is continuous in `t`, hence
constant on the connected space `ℝ`.

This is the first brick of the winding-number API that the capping step of Hugelmeyer's order theory
needs (the `arg γ` coordinate of `∂M` is such a degree), and that any classical proof of the
inscribed-square input would use. -/
theorem exists_lift_degree (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ t : ℝ, (F t : UnitAddCircle) = f (t : UnitAddCircle)) ∧
      ∃ n : ℤ, ∀ t : ℝ, F (t + 1) = F t + n := by
  -- The quotient map `ℝ → ℝ/ℤ` is a covering map, and `ℝ` is simply connected, so `f` lifts.
  have hcov : IsCoveringMap ((↑) : ℝ → UnitAddCircle) := AddCircle.isCoveringMap_coe (1 : ℝ)
  have hcontmk : Continuous ((↑) : ℝ → UnitAddCircle) := by fun_prop
  let f' : C(ℝ, UnitAddCircle) := ⟨fun t : ℝ => f (t : UnitAddCircle), hf.comp hcontmk⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℝ, (e₀ : UnitAddCircle) = f 0 :=
    ⟨(AddCircle.equivIoc (1 : ℝ) 0 (f 0) : ℝ), by simp [AddCircle.coe_equivIoc]⟩
  obtain ⟨G, ⟨hG0, hGlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts f' 0 e₀ he₀
  have hpt : ∀ t : ℝ, (G t : UnitAddCircle) = f (t : UnitAddCircle) := fun t => by
    have := congr_fun hGlift t
    simpa [f'] using this
  -- The monodromy `t ↦ G (t+1) - G t` takes values in `ℤ`, since `t + 1` and `t` agree in `ℝ/ℤ`.
  have hmono : ∀ t : ℝ, ∃ n : ℤ, G (t + 1) = G t + n := by
    intro t
    have h1 : (G (t + 1) : UnitAddCircle) = (G t : UnitAddCircle) := by
      rw [hpt (t + 1), hpt t, AddCircle.coe_add_period (1 : ℝ) t]
    have h2 : (G (t + 1) - G t : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      rw [← coe_eq_coe_iff_sub_mem (1 : ℝ)]
      exact h1
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
    refine ⟨n, ?_⟩
    have hgn : G (t + 1) - G t = (n : ℝ) := by simpa using hn.symm
    linarith
  -- Being continuous and integer-valued, the monodromy is locally constant...
  have hMcont : Continuous fun t : ℝ => G (t + 1) - G t :=
    (G.continuous.comp (continuous_id.add continuous_const)).sub G.continuous
  have hloc : IsLocallyConstant fun t : ℝ => G (t + 1) - G t := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨mx, hmx⟩ := hmono x
    refine ⟨{y : ℝ | dist (G (y + 1) - G y) (G (x + 1) - G x) < 1/2},
      Metric.isOpen_ball.preimage hMcont, by simp, ?_⟩
    intro y hy
    obtain ⟨my, hmy⟩ := hmono y
    have hx_eq : G (x + 1) - G x = (mx : ℝ) := by linarith
    have hy_eq : G (y + 1) - G y = (my : ℝ) := by linarith
    have hlt : |(my : ℝ) - (mx : ℝ)| < 1 := by
      have hy' : dist (G (y + 1) - G y) (G (x + 1) - G x) < 1/2 := hy
      rw [Real.dist_eq, hy_eq, hx_eq] at hy'
      linarith
    rw [hy_eq, hx_eq, Int.cast_inj]
    exact int_eq_of_abs_sub_lt_one hlt
  -- ... hence constant, by connectedness of `ℝ`.
  have hconst : ∀ t : ℝ, G (t + 1) - G t = G (0 + 1) - G 0 :=
    fun t => (IsLocallyConstant.iff_is_const.mp hloc) t 0
  obtain ⟨n, hn⟩ := hmono 0
  refine ⟨fun t => G t, G.continuous, hpt, n, fun t => ?_⟩
  have h1 : G (t + 1) - G t = (n : ℝ) := by rw [hconst t]; linarith
  linarith

end Work.RPB.Port.Drive

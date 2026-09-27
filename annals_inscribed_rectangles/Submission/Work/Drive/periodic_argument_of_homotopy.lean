import Mathlib

namespace Work.Drive

/-- A continuous real function on a topological space all of whose values are integers is
locally constant. -/
private lemma locallyConstant_of_int_valued {X : Type*} [TopologicalSpace X] {g : X → ℝ}
    (hg : Continuous g) (hint : ∀ x, ∃ m : ℤ, g x = (m : ℝ)) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨mx, hmx⟩ := hint x
  refine ⟨{y | dist (g y) (g x) < 1 / 2}, Metric.isOpen_ball.preimage hg, by simp, ?_⟩
  intro y hy
  obtain ⟨my, hmy⟩ := hint y
  have hlt : |(my : ℝ) - (mx : ℝ)| < 1 := by
    have h : dist (g y) (g x) < 1 / 2 := hy
    rw [Real.dist_eq, hmy, hmx] at h
    linarith
  have h1 : (my : ℝ) - mx < 1 := (abs_lt.mp hlt).2
  have h2 : -(1 : ℝ) < (my : ℝ) - mx := (abs_lt.mp hlt).1
  have hyx : my ≤ mx := by
    have hlt' : (my : ℝ) < ((mx + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (Int.cast_lt.mp hlt')
  have hxy : mx ≤ my := by
    have hlt' : (mx : ℝ) < ((my + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (Int.cast_lt.mp hlt')
  rw [hmy, hmx, Int.cast_inj]
  omega

/-- Two continuous lifts `u`, `v : X → ℝ` of the same `Circle`-valued map on a preconnected space
`X` differ by a constant. -/
private lemma sub_eq_of_continuous_exp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {u v : X → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x, Circle.exp (u x) = Circle.exp (v x)) :
    ∀ x y, u x - v x = u y - v y := by
  have h2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hint : ∀ x, ∃ m : ℤ, (u x - v x) / (2 * Real.pi) = (m : ℝ) := by
    intro x
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (h x)
    refine ⟨m, ?_⟩
    rw [hm, add_sub_cancel_left, mul_div_cancel_right₀ _ h2]
  have hcont : Continuous fun x => (u x - v x) / (2 * Real.pi) :=
    (hu.sub hv).div_const _
  have hlc := locallyConstant_of_int_valued hcont hint
  intro x y
  have hq : (u x - v x) / (2 * Real.pi) = (u y - v y) / (2 * Real.pi) :=
    (IsLocallyConstant.iff_is_const.mp hlc) x y
  have h3 : ((u x - v x) / (2 * Real.pi)) * (2 * Real.pi)
      = ((u y - v y) / (2 * Real.pi)) * (2 * Real.pi) := by rw [hq]
  rw [div_mul_cancel₀ (u x - v x) h2, div_mul_cancel₀ (u y - v y) h2] at h3
  exact h3

/-- **A continuous `2π`-periodic argument survives a non-vanishing homotopy of loops.**

Let `F : ℝ → ℝ → ℂ` be continuous and nowhere zero, with every slice `σ ↦ F s σ` unit-valued and
`2π`-periodic (so each slice is a loop `S¹ → S¹`).  If the loop at `s = 0` has a continuous
`2π`-periodic real argument `θ` — equivalently, the loop at `s = 0` has winding number zero — then the
loop at `s = 1` also has one.  (This is the degree-zero case of homotopy invariance of the winding
number; the conclusion deliberately asks for a *periodic* argument again.)

The proof lifts the *whole* map `(s, σ) ↦ F s σ : ℝ × ℝ → Circle` through the universal covering
`Circle.exp : ℝ → Circle` (`Circle.isCoveringMap_exp` and the lifting theorem
`IsCoveringMap.existsUnique_continuousMap_lifts` for the simply connected, locally path connected
source `ℝ × ℝ`), normalised so that the lift of the slice `s = 0` is the given argument `θ`.  Two
continuous lifts of the same `Circle`-valued map on a preconnected space differ by a constant, so the
monodromy `σ ↦ L (s, σ + 2π) - L (s, σ)` is independent of `(s, σ)`; evaluated at `(0, 0)` it
vanishes because `θ` is `2π`-periodic.  Hence `ψ σ := L (1, σ)` is `2π`-periodic. -/
theorem periodic_argument_of_homotopy (F : ℝ → ℝ → ℂ)
    (hFc : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hFun : ∀ s σ : ℝ, ‖F s σ‖ = 1)
    (hFper : ∀ s : ℝ, Function.Periodic (F s) (2 * Real.pi))
    {θ : ℝ → ℝ} (hθc : Continuous θ) (hθper : Function.Periodic θ (2 * Real.pi))
    (hθ : ∀ σ : ℝ, Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I) = F 0 σ) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ Function.Periodic ψ (2 * Real.pi) ∧
      ∀ σ : ℝ, Complex.exp (((ψ σ : ℝ) : ℂ) * Complex.I) = F 1 σ := by
  have hmem : ∀ s σ : ℝ, F s σ ∈ Metric.sphere (0 : ℂ) 1 := fun s σ => by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hFun s σ
  -- the whole map as a `Circle`-valued continuous map on the contractible space `ℝ × ℝ`
  let f : C(ℝ × ℝ, Circle) :=
    ⟨fun p => ⟨F p.1 p.2, hmem p.1 p.2⟩, hFc.subtype_mk (fun x => hmem x.1 x.2)⟩
  have hfval : ∀ s σ : ℝ, ((f (s, σ) : Circle) : ℂ) = F s σ := fun s σ => rfl
  have hθexp : ∀ σ : ℝ, Circle.exp (θ σ) = f (0, σ) := fun σ => by
    apply Subtype.ext
    rw [Circle.coe_exp, hθ σ]
    exact (hfval 0 σ).symm
  -- periodicity of the slices, as `Circle`-valued maps
  have hfper : ∀ s σ : ℝ, f (s, σ + 2 * Real.pi) = f (s, σ) := fun s σ => by
    apply Subtype.ext
    rw [hfval s (σ + 2 * Real.pi), hfval s σ]
    exact hFper s σ
  -- lift the whole map through the universal covering `ℝ → Circle`
  obtain ⟨L, hL, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f (0, 0) (θ 0) (hθexp 0)
  have hL0 : L (0, 0) = θ 0 := hL.1
  have hLlift : ∀ p : ℝ × ℝ, Circle.exp (L p) = f p := fun p => congr_fun hL.2 p
  -- the lift of the slice `s = 0` agrees with the given argument `θ`
  have hslice : ∀ σ : ℝ, L (0, σ) = θ σ := by
    have h := sub_eq_of_continuous_exp_eq (X := ℝ)
      (u := fun σ : ℝ => L (0, σ)) (v := θ)
      (L.continuous.comp (continuous_const.prodMk continuous_id)) hθc
      (fun σ => by rw [hLlift (0, σ), hθexp σ])
    intro σ
    have h0 : L (0, 0) - θ 0 = 0 := by rw [hL0]; ring
    have hσ : L (0, σ) - θ σ = L (0, 0) - θ 0 := h σ 0
    linarith [h0, hσ]
  -- the monodromy of the lift over the period `2π` is constant and vanishes at `(0, 0)`
  have hper : ∀ s σ : ℝ, L (s, σ + 2 * Real.pi) = L (s, σ) := by
    have hmono := sub_eq_of_continuous_exp_eq (X := ℝ × ℝ)
      (u := fun p : ℝ × ℝ => L (p.1, p.2 + 2 * Real.pi))
      (v := fun p : ℝ × ℝ => L (p.1, p.2))
      (L.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))
      (L.continuous.comp (continuous_fst.prodMk continuous_snd))
      (fun p => by rw [hLlift (p.1, p.2 + 2 * Real.pi), hLlift (p.1, p.2)]; exact hfper p.1 p.2)
    intro s σ
    have hθ2 : θ (2 * Real.pi) = θ 0 := by simpa using hθper 0
    have h0 : L (0, 2 * Real.pi) - L (0, 0) = 0 := by rw [hslice (2 * Real.pi), hL0, hθ2]; ring
    have hσ : L (s, σ + 2 * Real.pi) - L (s, σ) = L (0, 2 * Real.pi) - L (0, 0) := by
      simpa using hmono (s, σ) (0, 0)
    linarith [h0, hσ]
  refine ⟨fun σ => L (1, σ), ?_, ?_, ?_⟩
  · exact L.continuous.comp (continuous_const.prodMk continuous_id)
  · intro σ
    exact hper 1 σ
  · intro σ
    refine (Circle.coe_exp (L (1, σ))).symm.trans ?_
    rw [hLlift (1, σ)]
    exact (hfval 1 σ).symm

end Work.Drive

import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.umlauf
import Submission.Work.Drive.exists_lift_dirC_deriv
import Submission.Work.Drive.exists_continuous_chordDir
import Submission.Work.Drive.exists_lift_degree

namespace Work.Drive

open scoped Topology
open Submission.Collision (dirC)

/-- A continuous real-valued function on a preconnected space whose values are all integers is
locally constant. -/
lemma isLocallyConstant_of_int_valued {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (hint : ∀ x, ∃ m : ℤ, f x = (m : ℝ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨mx, hmx⟩ := hint x
  refine ⟨{y | dist (f y) (f x) < 1 / 2}, Metric.isOpen_ball.preimage hf, by simp, ?_⟩
  intro y hy
  obtain ⟨my, hmy⟩ := hint y
  have hlt : |(my : ℝ) - (mx : ℝ)| < 1 := by
    have h : dist (f y) (f x) < 1 / 2 := hy
    rw [Real.dist_eq, hmy, hmx] at h
    linarith
  rw [hmy, hmx, Int.cast_inj]
  exact int_eq_of_abs_sub_lt_one hlt

/-- **Monodromy transfer along a homotopy of `2π`-periodic loops.**

Let `H : I × ℝ → ℝ/ℤ` be a continuous homotopy which is `2π`-periodic in its second variable, whose
time-`0` slice is the class of a continuous `φ : ℝ → ℝ` (i.e. `H (0,a) = φ a` in `ℝ/ℤ`), and let `k` be
the monodromy of `φ` over a period: `φ (t + 2π) - φ t = k`.  Then the time-`1` slice has a continuous
lift `Φ` to `ℝ` with the same monodromy `k`.

The proof is the standard covering-space argument: lift the whole homotopy through the universal
cover `ℝ → ℝ/ℤ` (`IsCoveringMap.liftHomotopy`), starting from the lift `φ` at time `0`.  The
monodromy `(s, t) ↦ G (s, t + 2π) - G (s, t)` of the lifted homotopy is continuous and integer-valued
on the connected space `I × ℝ`, hence constant, so its value at time `1` equals its value at time `0`,
which is the monodromy `k` of `φ`. -/
lemma exists_lift_of_homotopy {H : C(unitInterval × ℝ, UnitAddCircle)}
    (hHper : ∀ (s : unitInterval) (t : ℝ), H (s, t + 2 * Real.pi) = H (s, t))
    {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hH0 : ∀ a : ℝ, H (0, a) = ((↑) : ℝ → UnitAddCircle) (φ a))
    {k : ℤ} (hφk : ∀ t : ℝ, φ (t + 2 * Real.pi) - φ t = (k : ℝ)) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧
      (∀ a : ℝ, (Φ a : UnitAddCircle) = H (1, a)) ∧
      ∀ t : ℝ, Φ (t + 2 * Real.pi) - Φ t = (k : ℝ) := by
  have hcov : IsCoveringMap ((↑) : ℝ → UnitAddCircle) := AddCircle.isCoveringMap_coe (1 : ℝ)
  let f₀' : C(ℝ, ℝ) := ⟨φ, hφc⟩
  have hH0' : ∀ a : ℝ, H (0, a) = ((↑) : ℝ → UnitAddCircle) (f₀' a) := hH0
  let G := hcov.liftHomotopy H f₀' hH0'
  have hGlift : ∀ ta : unitInterval × ℝ, ((G ta : ℝ) : UnitAddCircle) = H ta :=
    fun ta => congr_fun (hcov.liftHomotopy_lifts H f₀' hH0') ta
  have hG0 : ∀ a : ℝ, G (0, a) = φ a := fun a => by
    rw [hcov.liftHomotopy_zero H f₀' hH0' a]
    rfl
  let Dm : unitInterval × ℝ → ℝ := fun x => G (x.1, x.2 + 2 * Real.pi) - G (x.1, x.2)
  have hDmint : ∀ x : unitInterval × ℝ, ∃ m : ℤ, Dm x = (m : ℝ) := by
    rintro ⟨t, a⟩
    have h1 : ((G (t, a + 2 * Real.pi) : ℝ) : UnitAddCircle) = (G (t, a) : UnitAddCircle) := by
      rw [hGlift (t, a + 2 * Real.pi), hGlift (t, a), hHper t a]
    have h2 : (G (t, a + 2 * Real.pi) - G (t, a) : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      rw [← coe_eq_coe_iff_sub_mem (1 : ℝ)]
      exact h1
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
    refine ⟨m, ?_⟩
    change G (t, a + 2 * Real.pi) - G (t, a) = (m : ℝ)
    simpa using hm.symm
  have hDmcont : Continuous Dm := by
    dsimp only [Dm]
    fun_prop
  have hDmconst : ∀ x y : unitInterval × ℝ, Dm x = Dm y :=
    (IsLocallyConstant.iff_is_const.mp (isLocallyConstant_of_int_valued hDmcont hDmint))
  have hkey : ∀ a : ℝ, Dm (1, a) = (k : ℝ) := by
    intro a
    have h1 : Dm (1, a) = Dm (0, a) := hDmconst (1, a) (0, a)
    have h2 : Dm (0, a) = φ (a + 2 * Real.pi) - φ a := by
      change G (0, a + 2 * Real.pi) - G (0, a) = φ (a + 2 * Real.pi) - φ a
      rw [hG0 (a + 2 * Real.pi), hG0 a]
    rw [h1, h2, hφk a]
  refine ⟨fun a => G (1, a), ?_, ?_, ?_⟩
  · exact G.continuous.comp (continuous_const.prodMk continuous_id)
  · intro a
    exact hGlift (1, a)
  · intro t
    have h := hkey t
    change G (1, t + 2 * Real.pi) - G (1, t) = (k : ℝ) at h
    exact h

/-- **The lift of the chord loop, with the monodromy of the tangent loop.**

Given a continuous lift `φ` of the doubled tangent direction of `γ` whose monodromy over one period is
the integer `k`, the doubled direction of the chord `γ (exp (t + 2πc)) - γ (exp t)` — a non-zero
vector, because `γ` is injective and `0 < c < 1` — has a continuous lift with the same monodromy `k`.

The homotopy is the one suggested by the configuration strip: `s ↦ D (exp t, exp (t + 2π s c))`, where
`D` is the continuous extension of `(x,y) ↦ dirC (γ x - γ y)` to the diagonal of `Circle × Circle`
with diagonal value the doubled tangent direction (`Work.Drive.exists_continuous_chordDir`, proved from
the smoothness of the divided difference near the diagonal).  At `s = 0` this is the tangent loop and at
`s = 1` the chord loop at offset `c`; since the extension is *continuous at the diagonal*, no limiting
argument is needed, and `Work.Drive.exists_lift_of_homotopy` transfers the monodromy. -/
lemma chord_loop_lift (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφlift : ∀ t : ℝ, (φ t : UnitAddCircle) = dirC (deriv (curve γ) t))
    {k : ℤ} (hφk : ∀ t : ℝ, φ (t + 2 * Real.pi) - φ t = (k : ℝ)) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧
      (∀ t : ℝ, (Φ t : UnitAddCircle) =
        dirC (γ (Circle.exp (t + 2 * Real.pi * c)) - γ (Circle.exp t))) ∧
      ∀ t : ℝ, Φ (t + 2 * Real.pi) - Φ t = (k : ℝ) := by
  obtain ⟨D, hDcont, hDoff, hDdiag⟩ := exists_continuous_chordDir γ hγ
  -- the chord at offset `c` never joins a point of the curve to itself
  have hne : ∀ t : ℝ, Circle.exp t ≠ Circle.exp (t + 2 * Real.pi * c) := by
    intro t h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
    have hzero : 2 * Real.pi * c + (m : ℝ) * (2 * Real.pi) = 0 := by linarith
    have hcm : c = -(m : ℝ) := by
      have hfac : 2 * Real.pi * (c + (m : ℝ)) = 0 := by nlinarith [Real.pi_pos]
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact absurd h' (by positivity)
      · linarith
    have h1 : (m : ℝ) < 0 := by linarith
    have h2 : (-1 : ℝ) < (m : ℝ) := by linarith
    have h3 : m < 0 := by exact_mod_cast h1
    have h4 : (-1 : ℤ) < m := by exact_mod_cast h2
    omega
  -- the homotopy on the configuration strip
  have hHcont : Continuous (fun x : unitInterval × ℝ =>
      D (Circle.exp x.2, Circle.exp (x.2 + 2 * Real.pi * (x.1 : ℝ) * c))) := by fun_prop
  let hf : unitInterval × ℝ → UnitAddCircle := fun x =>
    D (Circle.exp x.2, Circle.exp (x.2 + 2 * Real.pi * (x.1 : ℝ) * c))
  let H : C(unitInterval × ℝ, UnitAddCircle) := ⟨hf, hHcont⟩
  have hHper : ∀ (s : unitInterval) (t : ℝ), H (s, t + 2 * Real.pi) = H (s, t) := by
    intro s t
    change D (Circle.exp (t + 2 * Real.pi),
        Circle.exp (t + 2 * Real.pi + 2 * Real.pi * (s : ℝ) * c))
      = D (Circle.exp t, Circle.exp (t + 2 * Real.pi * (s : ℝ) * c))
    rw [Circle.exp_add_two_pi,
      show t + 2 * Real.pi + 2 * Real.pi * (s : ℝ) * c
        = (t + 2 * Real.pi * (s : ℝ) * c) + 2 * Real.pi by ring,
      Circle.exp_add_two_pi]
  have hH0 : ∀ a : ℝ, H (0, a) = ((↑) : ℝ → UnitAddCircle) (φ a) := by
    intro a
    change D (Circle.exp a, Circle.exp (a + 2 * Real.pi * ((0 : unitInterval) : ℝ) * c))
      = ((↑) : ℝ → UnitAddCircle) (φ a)
    rw [show ((0 : unitInterval) : ℝ) = 0 by simp]
    simp only [mul_zero, zero_mul, add_zero]
    rw [hDdiag (Circle.exp a) a rfl]
    show dirC (deriv (curve γ) a) = ((↑) : ℝ → UnitAddCircle) (φ a)
    exact (hφlift a).symm
  obtain ⟨Φ, hΦc, hΦlift, hΦk⟩ := exists_lift_of_homotopy hHper hφc hH0 hφk
  refine ⟨Φ, hΦc, ?_, hΦk⟩
  intro t
  rw [hΦlift t]
  change D (Circle.exp t, Circle.exp (t + 2 * Real.pi * ((1 : unitInterval) : ℝ) * c)) =
    dirC (γ (Circle.exp (t + 2 * Real.pi * c)) - γ (Circle.exp t))
  rw [show ((1 : unitInterval) : ℝ) = 1 by simp, mul_one]
  rw [hDoff (Circle.exp t) (Circle.exp (t + 2 * Real.pi * c)) (hne t)]
  rw [show γ (Circle.exp t) - γ (Circle.exp (t + 2 * Real.pi * c)) =
      -(γ (Circle.exp (t + 2 * Real.pi * c)) - γ (Circle.exp t)) by abel, dirC_neg]

/-- **The fixed-offset chord loop of the configuration strip has direction-winding `±2`.**

For a smooth embedded closed plane curve `γ` and an offset `c ∈ (0,1)`, the loop
`x ↦ γ (x + c) - γ x` in the plane is nowhere zero, so its doubled direction
`dirC` (the class of `arg/π` in `ℝ/ℤ`) has a continuous lift `Φ` to `ℝ`; the lift's monodromy over
one period is `2ε` with `ε = ±1`.  Equivalently: the "fixed offset" chord loop of the configuration
Möbius strip `M` of `γ` has direction-winding `±2`, so (its direction map having non-zero degree) it
is a *homologically essential* loop of `M` — the replacement, in the chain-level route to
`Work.Drive.chainParity`, of the notion "essential loop of the capped plane `P`" that the definition
of `ω_P` and of the order `≺` uses (Hugelmeyer, Lemma 1 and the definition of `≺`).

Proof route (the degree API of `Drive/WindingNumber` + `Drive/degree_homotopic` + the Umlaufsatz):
`t ↦ dirC (γ (exp (t + 2πc')) - γ (exp t))` is a continuous `2π`-periodic loop in `ℝ/ℤ` whose degree
is *locally constant* in `c'` (homotopy invariance of the degree, `c' ↦` the loop being continuous on
the connected interval `(0,1)`); as `c' → 0⁺` the loop converges to the tangent loop
`t ↦ dirC (deriv (curve γ) t)`, whose lift has monodromy `2ε` with `ε = ±1` by
`Work.Drive.doubledTangent_winding` (`Submission.Work.Drive.orderWitness_exists`), so the degree is
`±2` for every `c ∈ (0,1)`. -/
theorem chord_loop_winding (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∃ (Φ : ℝ → ℝ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ Continuous Φ ∧
      (∀ t : ℝ, (Φ t : UnitAddCircle) =
        Submission.Collision.dirC
          (γ (Circle.exp (t + 2 * Real.pi * c)) - γ (Circle.exp t))) ∧
      ∀ t : ℝ, Φ (t + 2 * Real.pi) - Φ t = 2 * ε := by
  obtain ⟨φ, k, hk, hφc, hφlift, hφk⟩ := exists_lift_dirC_deriv umlauf γ hγ
  obtain ⟨Φ, hΦc, hΦlift, hΦk⟩ := chord_loop_lift γ hγ hc hc1 hφc hφlift hφk
  rcases hk with hk | hk
  · exact ⟨Φ, 1, Or.inl rfl, hΦc, hΦlift, fun t => by rw [hΦk t, hk]; norm_num⟩
  · exact ⟨Φ, -1, Or.inr rfl, hΦc, hΦlift, fun t => by rw [hΦk t, hk]; norm_num⟩

end Work.Drive

import Mathlib
import Submission.Work.Drive.weakcase_deps
import Submission.Work.Drive.unit_log_pole_at_every_point
import Submission.Work.Drive.rigidity_at_pole

/-! Guidance from the project lead (the requester):

# Area W — a weak Green function exists ⟹ X ≅ 𝔻 (the hyperbolic case, no decay needed)

Hypotheses: `hP : PeriodsHold X`, i.e. EVERY harmonic function on X∖{z} with a unit log pole at z has
a single-valued holomorphic modulus (`Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods`:
Φ holomorphic on X, `‖Φ x‖ = exp (-E x)` off z, simple zero at z only). Also
`hW : HasWeakGreen X`, a positive harmonic E on X∖{z₀} with a unit log pole. NO decay at infinity is
assumed, and none is needed.
Goal: an injective holomorphic map X → 𝔻 vanishing at a point, i.e. `(Submission.injFamily x₀).Nonempty`,
then `Submission.uniformization_of_injective_into_disc` (Submission/ExtremalInj.lean) concludes.

## The route actually taken here (Ahlfors' rigidity + symmetry, via the ABS endgame)

The route below is the classical one of Ahlfors (*Conformal invariants*, §10-4), assembled from
already-proved, `sorry`-free workspace results: it needs neither the Perron minimality (M1)/(M2) of
the plan sketched above, nor the Behnke–Stein divisor theorem (`exists_holomorphic_single_zero`,
which is `sorry`), because the period hypothesis `hP` supplies the holomorphic modulus at *every*
pole.

1. **The weak Green function gives a modulus.** From `hW` and `hP`,
   `Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods` produces a holomorphic `Φ₀` on
   `X` with a *simple* zero at the pole `z₀` and `‖Φ₀ x‖ = exp (-E x)` off `z₀`.  Hence `Φ₀` is a
   non-zero member of the extremal family `𝔽_{z₀}` whose chart derivative at `z₀` does not vanish.
2. **A weak Green function at every point.** For any `y`, the Möbius conjugate
   `m_{Φ₀ y} ∘ Φ₀` is a non-zero member of `𝔽_y`; feeding it into
   `Work.Drive.unit_log_pole_at_every_point` (sweep of the clamped logarithmic barrier + Bôcher's
   theorem + normalisation) yields a positive harmonic function on `X ∖ {y}` with a *unit*
   logarithmic pole at `y`.
3. **Ahlfors' rigidity at every pole.** `Work.Drive.rigidity_at_pole` (with `hP`) turns that into
   the extremal maximiser `f_y` at `y` together with the Perron envelope `E_y` it attains:
   `E_y` is positive and harmonic off `y`, has a unit log pole at `y`, dominates the whole family
   `𝔽_y`, and `‖f_y z‖ = exp (-(E_y z))` for `z ≠ y`.
4. **Symmetry, for free.** For two poles `x₀ ≠ y` with rigid envelopes `E₀`, `Ey`, the Ahlfors
   symmetry of the extremal value (`Work.SimplyConnected.ABS.envelope_symm`) gives
   `Ey x₀ = E₀ y`.
5. **Injectivity.** `Work.SimplyConnected.ABS.injective_of_maximizer_of_modulus` (Ahlfors'
   univalence: the maximum-principle argument `fibre_eq_singleton` on the Möbius conjugate of the
   maximiser, using the sharpness at the *second* pole supplied by step 4) shows that the maximiser
   at the base point is injective.  Hence `(Submission.injFamily x).Nonempty`, and
   `Submission.uniformization_of_injective_into_disc` concludes.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem weak_case {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hP : Work.Drive.PeriodsHold X) (hW : Work.Drive.HasWeakGreen X) :
    Work.Drive.Conclusion X := by
  classical
  obtain ⟨z₀, E, hEpos, hEharm, hEpole⟩ := hW
  -- ## The holomorphic modulus of the weak Green function
  obtain ⟨Φ₀, hΦ₀hol, hΦ₀zero, hΦ₀mod, hΦ₀pole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods (X := X) (z₀ := z₀) (E := E)
      hEharm hEpole (hP z₀ E hEharm hEpole)
  have hΦ₀mem : Φ₀ ∈ Submission.extremalFamily z₀ :=
    Work.SimplyConnected.ABS.modulus_mem_extremalFamily' (x₀ := z₀) hΦ₀hol hΦ₀pole hEpos hΦ₀mod
  have hΦ₀le : ∀ t : X, ‖Φ₀ t‖ ≤ 1 := fun t => hΦ₀mem.2.1 t
  have hΦ₀lt : ∀ t : X, ‖Φ₀ t‖ < 1 := by
    intro t
    by_cases ht : t = z₀
    · subst ht; rw [hΦ₀zero]; norm_num
    · rw [hΦ₀mod t ht]; exact Real.exp_lt_one_iff.mpr (by linarith [hEpos t ht])
  have hΦ₀ne : ∀ t : X, t ≠ z₀ → Φ₀ t ≠ 0 := by
    intro t ht
    rw [← norm_pos_iff, hΦ₀mod t ht]
    exact Real.exp_pos _
  -- ## A non-zero member of the extremal family at every point (the Möbius trick)
  have hmobius : ∀ t : X, ∃ g : X → ℂ, g ∈ Submission.extremalFamily t ∧ ∃ s : X, g s ≠ 0 := by
    intro t
    refine ⟨fun u => Submission.mobiusA (Φ₀ t) (Φ₀ u), ?_, ?_⟩
    · exact ⟨hΦ₀hol.mobiusA_comp (fun u _ => hΦ₀le u) (hΦ₀lt t),
        fun u => Submission.norm_mobiusA_le (hΦ₀lt t) (hΦ₀le u),
        Submission.mobiusA_self (Φ₀ t)⟩
    · by_cases ht : t = z₀
      · obtain ⟨s, hs⟩ := Submission.exists_ne_of_chartedSpace z₀
        refine ⟨s, ?_⟩
        change Submission.mobiusA (Φ₀ t) (Φ₀ s) ≠ 0
        have h1 : Submission.mobiusA (Φ₀ t) (Φ₀ s) = Φ₀ s := by
          rw [ht, hΦ₀zero]; simp [Submission.mobiusA]
        rw [h1]
        exact hΦ₀ne s hs
      · refine ⟨z₀, ?_⟩
        change Submission.mobiusA (Φ₀ t) (Φ₀ z₀) ≠ 0
        have h1 : Submission.mobiusA (Φ₀ t) (Φ₀ z₀) = -Φ₀ t := by
          rw [hΦ₀zero, Submission.mobiusA_apply_zero]
        rw [h1]
        exact neg_ne_zero.mpr (hΦ₀ne t ht)
  -- ## A weak Green function at the base point `x`
  have hbase : ∃ E₁ : X → ℝ, (∀ t : X, t ≠ x → 0 < E₁ t) ∧
      Submission.HarmonicOnX E₁ (Set.univ \ {x}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x}) x E₁ := by
    by_cases hxz : x = z₀
    · subst hxz; exact ⟨E, hEpos, hEharm, hEpole⟩
    · obtain ⟨g, hg, hne⟩ := hmobius x
      exact unit_log_pole_at_every_point hg hne
  obtain ⟨E₁, hE₁pos, hE₁harm, hE₁pole⟩ := hbase
  -- ## Ahlfors' rigid solution of the extremal problem at the base point
  obtain ⟨E₀, f, hE₀pos, hE₀harm, hE₀pole, hdom₀, hf, hrig, hposf, hmaxf⟩ :=
    rigidity_at_pole (y := x) hP hE₁pos hE₁harm hE₁pole
  -- ## The symmetry of the envelope at a second pole
  have hsymm : ∀ y : X, y ≠ x → ∃ Ey : X → ℝ, Submission.HarmonicOnX Ey (Set.univ \ {y}) ∧
      (∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z))) ∧
      E₀ y ≤ Ey x := by
    intro y hy
    obtain ⟨g, hg, hne⟩ := hmobius y
    obtain ⟨Ey, hEypos, hEyharm, hEypole⟩ := unit_log_pole_at_every_point hg hne
    obtain ⟨Ey', fy, -, hEy'harm, -, hdomy, hfymem, hrigy, -, -⟩ :=
      rigidity_at_pole (y := y) hP hEypos hEyharm hEypole
    refine ⟨Ey', hEy'harm, hdomy, ?_⟩
    have hsym := Work.SimplyConnected.ABS.envelope_symm (x₀ := x) (y := y) (E₀ := E₀) (Ey := Ey')
      (f := f) (f' := fy) hf hdom₀ hrig hfymem hdomy hrigy hy
    exact le_of_eq hsym.symm
  -- ## The modulus of the envelope at the base point
  obtain ⟨Φ, hΦhol, hΦzero, hΦmod, hΦpole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_logPole_of_periods (X := X) (z₀ := x) (E := E₀)
      hE₀harm hE₀pole (hP x E₀ hE₀harm hE₀pole)
  -- ## Ahlfors' univalence and the endgame
  have hinj : Function.Injective f :=
    Work.SimplyConnected.ABS.injective_of_maximizer_of_modulus (x₀ := x) (E := E₀) (f := f)
      hf hmaxf hposf hE₀pos hE₀harm hE₀pole hdom₀ ⟨Φ, hΦhol, hΦpole, hΦmod⟩ hsymm
  exact Submission.uniformization_of_injective_into_disc (x₀ := x) ⟨f, ⟨hf, hinj⟩⟩

end Work.Drive

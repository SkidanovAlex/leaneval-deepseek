/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/smoothOpen_slice_of_epsRHSP.lean` — the `C^∞`-regularity of the
`P₀`-scheme's slices (the "G1-core" of the `StrongEps` area)

**Target.**  For a solution `g` of the projected `ε`-scheme `IsEpsSolP` on `[0,T]`, every
fake-time slice `slice g τ` (`τ ∈ [0,T]`) is `C^k` on the *open* quadrant `Q0` for every `k`,
i.e. `ContDiffOn ℝ k (uncurry (slice g τ)) Q0`.

**Proof shape.**  The scheme `∂_τ g = P₀ J_ε [𝓛 + 𝓡] (P₀ J_ε g)` is an ODE in the fake time
`τ` at every point of `Q0`; its integral form is

  `g z θ τ = g₀ z θ + ∫_{0}^{τ} epsRHSP … s z θ ds`   (`slice_eq_datum_add_primitive` below),

so the slice is a datum plus a *parametric primitive*.  The datum `g₀` is smooth on `Q0` by
hypothesis (`hsm0`), and the primitive of a family `W`

  `(z,θ) ↦ ∫_a^b W s z θ ds`

is smooth on `Q0` of every order as soon as (i) every `W s` is `C^∞` on `Q0`, (ii) for every
`(z,θ) ∈ Q0` the map `s ↦ W s z θ` is continuous, and (iii) the mixed slots
`D_z^kD_θ^l (W s)` are uniformly bounded in `s` on compacts of `Q0`.  That analytic fact is
established in three steps:

* `primitive_mixed_continuous` (`Work.FTS.StrongEps.primitive_mixed_continuous`, a separately
  proved module) — the primitive of `mixed j i (W ·)` is continuous on `Q0`;
* `primitive_mixed_hasDerivAt` (`Work.FTS.StrongEps.primitive_mixed_hasDerivAt`) — the `z`- and
  `θ`-slice derivatives of that primitive are the primitives of `mixed (j+1) i (W ·)` resp.
  `mixed j (i+1) (W ·)`, divided by `z` resp. `sin 2θ`;
* `contDiffOn_primitive_all_of_pieces` (below) — the bootstrap: given the two clauses above for
  *all* `(j,i)`, every primitive of a mixed slot is `C^n` for every `n`, by induction on `n`
  with the criterion `SmoothAux.contDiffOn_succ_of_partials` ("`C^{n+1}` from `C^n` partials":
  for a function on an open set, knowing its two slice derivatives pointwise and knowing that
  these are `C^n` gives `C^{n+1}`).

The domination hypotheses of `primitive_mixed_*` are met by the scheme's uniform slot bound
`hbdd`, and the measurability in `s` by `aemeasurable_mixed_family` (from the pointwise
continuity in `s` of the right-hand side, hypothesis `hcont`).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.aemeasurable_mixed_family
import Submission.Work.FTS.PhiStar.Series.SmoothAux.contDiffOn_of_families_nat
import Submission.Work.FTS.StrongEps.primitive_mixed_continuous
import Submission.Work.FTS.StrongEps.primitive_mixed_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## (1) The scheme in integral form

The pointwise ODE of `IsEpsSolP` on the open quadrant, integrated over `[0,τ]` by the fundamental
theorem of calculus (the integrand is continuous in `s` by `hcont`). -/
private theorem slice_eq_datum_add_primitive {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g : Fam} (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ ε Φs E g s z θ) (Set.Icc 0 T)) :
    ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 T →
      g z θ τ = g₀ z θ + ∫ s in (0 : ℝ)..τ, epsRHSP α ρ ε Φs E g s z θ := by
  intro z θ τ hQ hτ
  obtain ⟨hz, hθ₁, hθ₂⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ₁, hθ₂⟩
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => g z θ s) (epsRHSP α ρ ε Φs E g x z θ) (Set.Icc 0 T) x :=
    fun x hx => hsol.2 z θ x hz hθ hx
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hτ.2
  have hftc : ∫ s in (0 : ℝ)..τ, epsRHSP α ρ ε Φs E g s z θ = g z θ τ - g z θ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1
      ((HasDerivWithinAt.continuousOn hderiv).mono hsub)
      (fun x hx => (hderiv x ⟨hx.1.le, le_trans hx.2.le hτ.2⟩).hasDerivAt
        (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hτ.2)))
      (ContinuousOn.intervalIntegrable_of_Icc hτ.1 ((hcont z θ hQ).mono hsub))
  rw [← hsol.1 z θ]
  linarith

/-! ## (2) The bootstrap: primitives of the mixed slots are `C^n` for every `n`

Given the two clauses (continuity of the primitives, and the two slice derivatives of a
primitive), the induction on `n` is immediate from `contDiffOn_succ_of_partials`: the `z`- and
`θ`-derivatives of the primitive of `mixed j i (W ·)` are the primitives of `mixed (j+1) i (W ·)`
and `mixed j (i+1) (W ·)` divided by `z` resp. `sin 2θ`, and dividing a `C^n` function by the
nowhere-vanishing smooth factors `z` and `sin 2θ` keeps it `C^n` on `Q0`. -/
private theorem contDiffOn_primitive_all_of_pieces {W : ℝ → ℝ → ℝ → ℝ} {a b : ℝ}
    (hcont : ∀ j i : ℕ,
      ContinuousOn (fun q : ℝ × ℝ => ∫ s in a..b, Work.Spaces.mixed j i (W s) q.1 q.2)
        Work.FTS.EllipticEst.Q0)
    (hder : ∀ j i : ℕ,
      (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' => ∫ s in a..b, Work.Spaces.mixed j i (W s) z' θ)
          ((∫ s in a..b, Work.Spaces.mixed (j + 1) i (W s) z θ) / z) z) ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' => ∫ s in a..b, Work.Spaces.mixed j i (W s) z θ')
          ((∫ s in a..b, Work.Spaces.mixed j (i + 1) (W s) z θ) / Real.sin (2 * θ)) θ)) :
    ∀ n : ℕ, ∀ j i : ℕ,
      ContDiffOn ℝ n (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.mixed j i (W s) z θ))
        Work.FTS.EllipticEst.Q0 := by
  have hU : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  intro n
  induction n with
  | zero =>
    intro j i
    exact (contDiffOn_zero (𝕜 := ℝ)).mpr (hcont j i)
  | succ n ih =>
    intro j i
    refine Work.FTS.PhiStar.Series.SmoothAux.contDiffOn_succ_of_partials
      (f := fun z θ => ∫ s in a..b, Work.Spaces.mixed j i (W s) z θ)
      (g := fun z θ => (∫ s in a..b, Work.Spaces.mixed (j + 1) i (W s) z θ) / z)
      (h := fun z θ => (∫ s in a..b, Work.Spaces.mixed j (i + 1) (W s) z θ) / Real.sin (2 * θ))
      hU (fun z θ _ => (hder j i).1 z θ ‹_›) (fun z θ _ => (hder j i).2 z θ ‹_›) ?_ ?_
    · have h1 : ContDiffOn ℝ n
          (fun p : ℝ × ℝ => Function.uncurry (fun z θ => ∫ s in a..b,
            Work.Spaces.mixed (j + 1) i (W s) z θ) p / p.1) Work.FTS.EllipticEst.Q0 :=
        (ih (j + 1) i).div contDiffOn_fst
          (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1.ne')
      exact h1.congr (fun p _ => by rcases p with ⟨z, θ⟩; rfl)
    · have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          Work.FTS.EllipticEst.Q0 := by
        change ContDiffOn ℝ n (Real.sin ∘ fun p : ℝ × ℝ => 2 * p.2) _
        exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.mono
          (Set.subset_univ _)
      have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
        intro p hp
        obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
      have h2 : ContDiffOn ℝ n
          (fun p : ℝ × ℝ => Function.uncurry (fun z θ => ∫ s in a..b,
            Work.Spaces.mixed j (i + 1) (W s) z θ) p / Real.sin (2 * p.2))
          Work.FTS.EllipticEst.Q0 :=
        (ih j (i + 1)).div hsin hne
      exact h2.congr (fun p _ => by rcases p with ⟨z, θ⟩; rfl)

/-! ## (3) The target -/

theorem smoothOpen_slice_of_epsRHSP {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s p.1 p.2)
        (Set.Icc 0 T))
    (hreg : ∀ s ∈ Set.Icc 0 T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
        Work.FTS.EllipticEst.Q0)
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc 0 T, ∀ (k l : ℕ), ∀ q : ℝ × ℝ, q ∈ K →
        |Work.Spaces.mixed k l (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ B)
    (hsm0 : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry g₀) Work.FTS.EllipticEst.Q0) :
    ∀ τ ∈ Set.Icc 0 T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ k
  set W : ℝ → ℝ → ℝ → ℝ := fun s => epsRHSP α ρ ε Φs E g s with hW
  have hT0 : (0 : ℝ) ≤ T := le_trans hτ.1 hτ.2
  have hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (W s) :=
    fun s hs => Work.FTS.EllipticEst.smoothOpen_of_forall (hreg s hs)
  have hcont' : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => W s z θ) (Set.Icc (0 : ℝ) T) :=
    fun z θ h => hcont (z, θ) h
  have hmeas := aemeasurable_mixed_family (T := T) (H := W) hsm hcont'
  have ha : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hbddW : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), ∀ q : ℝ × ℝ, q ∈ K →
        |Work.Spaces.mixed k l (W s) q.1 q.2| ≤ B := hbdd
  have hpiece1 : ∀ j i : ℕ, ContinuousOn
      (fun q : ℝ × ℝ => ∫ s in (0 : ℝ)..τ, Work.Spaces.mixed j i (W s) q.1 q.2)
      Work.FTS.EllipticEst.Q0 :=
    fun j i => primitive_mixed_continuous (W := W) ha hτ hsm hmeas hbddW j i
  have hpiece2 : ∀ j i : ℕ,
      (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' => ∫ s in (0 : ℝ)..τ, Work.Spaces.mixed j i (W s) z' θ)
          ((∫ s in (0 : ℝ)..τ, Work.Spaces.mixed (j + 1) i (W s) z θ) / z) z) ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' => ∫ s in (0 : ℝ)..τ, Work.Spaces.mixed j i (W s) z θ')
          ((∫ s in (0 : ℝ)..τ, Work.Spaces.mixed j (i + 1) (W s) z θ)
            / Real.sin (2 * θ)) θ) :=
    fun j i => primitive_mixed_hasDerivAt (W := W) ha hτ hsm hmeas hbddW j i
  have hall := contDiffOn_primitive_all_of_pieces (W := W) (a := (0 : ℝ)) (b := τ)
    hpiece1 hpiece2
  have hprim : ContDiffOn ℝ k (Function.uncurry (fun z θ => ∫ s in (0 : ℝ)..τ, W s z θ))
      Work.FTS.EllipticEst.Q0 := hall k 0 0
  have hg0 : ContDiffOn ℝ k (Function.uncurry g₀) Work.FTS.EllipticEst.Q0 := hsm0 k
  have hint := slice_eq_datum_add_primitive hsol hcont'
  refine (hg0.add hprim).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  show (slice g τ z θ : ℝ) = g₀ z θ + (∫ s in (0 : ℝ)..τ, W s z θ)
  rw [show slice g τ z θ = g z θ τ from rfl, hint z θ τ hp hτ]

end Work.FTS.StrongEps

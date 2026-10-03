import Mathlib
import Submission.Work.Peluse.Ulower.flatCubeTransform
import Submission.Work.Peluse.Ulower.phaseElimGap_of_flatCube

/-!
# `Work.Peluse.Ulower.lemma75_control`

Target: Peluse's Lemma 7.5 (Forum Math. Pi 8 (2020) e16) in the workspace vocabulary.

The proof is the reduction recorded in `NOTES_lemma75_phase_elimination.md`: writing

* `Ec = (card : ℝ)⁻¹ * (card : ℝ)⁻¹ * ∑ u ∈ Q^s, ∑ v ∈ Q^s, ‖L⁻¹ ∑'_x cubeTerm u v f x · e(θ u v · x)‖²`
  for the **chirped** aggregate of the hypothesis (`card = D^s`, `θ u v = ∑ i, ψ i u v`), and
* `Eu = (card : ℝ)⁻¹ * (card : ℝ)⁻¹ * ∑ u ∈ Q^s, ∑ v ∈ Q^s, ‖L⁻¹ ∑'_x cubeTerm u v f x‖²`
  for the **unchirped** aggregate,

the two ingredients are

* `Work.Peluse.Ulower.phaseElim`: `γ ≤ Ec ⟹ γ^{2^s} ≤ C · Eu`
  (Peluse–Prendiville's "low rank correlation implies lower degree"; Gowers–Cauchy–Schwarz run one
  blind coordinate at a time, which kills the `i`-th phase `ψ i` at the `i`-th step and *randomises*
  the direction pair rather than losing a factor `D`);
* `Work.Peluse.Ulower.windowAggregate`: `C' · Eu ≤ boxNormPow (s+1) (Q^{s+1}) (symIcc L) f`
  (the window-sum/Cauchy–Schwarz step, with `Q = arithIcc 1 D`).

Combining them with `K = 2^s` and `c = C'/C` gives the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **Phase elimination** (Peluse's Lemma 7.5, intermediate step).

A large average of the *chirped* squared Fourier coefficients of the level-`s` cube terms at a
rank-`s` blind phase forces the *unchirped* aggregate to be large:

`γ ≤ σ ⟹ γ^{2^s} ≤ C · Eu`.

This is the step that the paper's proof of Lemma 7.5 leaves to Gowers--Cauchy--Schwarz: expanding
the square and applying GCS in the (blind) `h'`-direction produces, for each `(x,z)`, the flat cube
sum of the two-point family `v ↦ cubeTerm u v f x · conj (cubeTerm u v f z)`; the paper then
*writes down the unweighted version* and the identification of the two is exactly the (nontrivial)
flat-cube inequality.  Here the chain is

* `Work.Peluse.Ulower.flatCubeTransform` — the flat cube sum of the level-`s` cube term of `g` is
  bounded by the flat cube sum of `g` itself (`C = 1`); the mechanism is that each extra factor
  `star^{|α|}(g (cornerShift h v α))`, `α ≠ 0`, is *blind* in a coordinate where `α` is true, and
  `Concat.gowersCS` lets blind factors be dropped from a flat cube sum;
* `Work.Peluse.Ulower.phaseElimGap_of_flatCube` — the assembly: GCS per `(x,z)` + the positivity of
  the flat cube sum + Hölder over the `(u,x,z)`-index set of size `≤ D^s N²` (`N ≤ (3+s)L`).

See `NOTES_lemma75_crux_SESSION.md` and `NOTES_lemma75_GCS_route.md` §7c for the bookkeeping. -/
lemma phaseElimGap :
    ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧
      ∀ (L D : ℕ) (f : ℤ → ℂ) (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ) (γ : ℝ),
        1 ≤ L → 1 ≤ D → (D : ℝ) ≤ (L : ℝ) →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f L →
        (∀ i : Fin s, ∀ u : Fin s → ℤ, ∀ v : Fin s → ℤ, ∀ a b : ℤ,
          ψ i u (Function.update v i a) = ψ i u (Function.update v i b)) →
        0 < γ →
        γ ≤ ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x *
                  Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2 →
        γ ^ (2 ^ s) ≤ C *
          (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2) := by
  intro s hs
  -- `flatCubeTransform` is exactly the hypothesis that `phaseElimGap_of_flatCube` consumes; only
  -- the order of the `γ` binder differs from the statement above, so we rearrange it.
  obtain ⟨C, hCpos, hC⟩ := phaseElimGap_of_flatCube s hs (flatCubeTransform s hs)
  exact ⟨C, hCpos, fun L D f ψ γ hL hD hDL hf hsupp hblind hγ hhyp =>
    hC L D f ψ hL hD hDL hf hsupp hblind γ hγ hhyp⟩

/-- **Peluse's Lemma 7.5** (Forum Math. Pi 8 (2020) e16), in the workspace normalisation: a large
average of the squared Fourier coefficients of the level-`s` cube terms at a rank-`s` phase forces
the level-`(s+1)` box norm of `f` to be large. -/
theorem lemma75_control :
    ∀ s : ℕ, 1 ≤ s → ∃ K : ℕ, 1 ≤ K ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L D : ℕ) (f : ℤ → ℂ) (ψ : Fin s → (Fin s → ℤ) → (Fin s → ℤ) → ℝ),
        1 ≤ L → 1 ≤ D → (D : ℝ) ≤ (L : ℝ) →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f L →
        (∀ i : Fin s, ∀ u : Fin s → ℤ, ∀ v : Fin s → ℤ, ∀ a b : ℤ,
          ψ i u (Function.update v i a) = ψ i u (Function.update v i b)) →
        ∀ γ : ℝ, 0 < γ →
        γ ≤ (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
          * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
          * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
            ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x *
                Complex.exp (2 * Real.pi * Complex.I * (∑ i, ψ i u v) * (x : ℝ))‖ ^ 2 →
        c * γ ^ K ≤ Work.Peluse.boxNormPow (s + 1) (fun _ : Fin (s + 1) => Work.Peluse.arithIcc 1 D)
          (Work.Peluse.symIcc L) f := by
  intro s hs
  obtain ⟨C, hCpos, hC⟩ := phaseElimGap s hs
  obtain ⟨C', hC'pos, hC'⟩ := windowAggregate s hs
  refine ⟨2 ^ s, Nat.one_le_two_pow, C' / C, div_pos hC'pos hCpos, ?_⟩
  intro L D f ψ hL hD hDL hf hsupp hblind γ hγ hhyp
  have h1 : γ ^ (2 ^ s) ≤ C *
      (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹
        * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
        * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
            ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2) :=
    hC L D f ψ γ hL hD hDL hf hsupp hblind hγ hhyp
  have h2 : C' *
      (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹
        * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
        * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
          ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
            ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)
      ≤ Work.Peluse.boxNormPow (s + 1) (fun _ : Fin (s + 1) => Work.Peluse.arithIcc 1 D)
          (Work.Peluse.symIcc L) f := hC' L D f hL hD hDL hf hsupp
  have hCne : C ≠ 0 := ne_of_gt hCpos
  calc (C' / C) * γ ^ (2 ^ s)
      ≤ (C' / C) * (C *
          (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹
            * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
            * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos hC'pos hCpos))
    _ = C' *
          (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹
            * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
            * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
                ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2) := by
        field_simp
    _ ≤ Work.Peluse.boxNormPow (s + 1) (fun _ : Fin (s + 1) => Work.Peluse.arithIcc 1 D)
          (Work.Peluse.symIcc L) f := h2

end

end Work.Peluse.Ulower

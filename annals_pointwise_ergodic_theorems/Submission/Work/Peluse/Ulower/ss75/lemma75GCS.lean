import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Peluse.Ulower.flatCubeTransform
import Submission.Work.Peluse.Ulower.phaseElimGap_of_flatCube

/-!
# `Work.Peluse.Ulower.ss75.lemma75GCS`

Peluse's Lemma 7.5 (Forum Math. Pi 8 (2020) e16, arXiv:1909.00309) in the workspace vocabulary:
a large average of the squared Fourier coefficients of the level-`s` cube terms of `f` at a
rank-`s` *blind* phase forces the level-`(s+1)` box norm of `f` to be large.  This is the same
statement as `Work.Peluse.Ulower.lemma75_control`; the proof here is assembled from the workspace's
components of the GCS route (see `ss75/NOTES.md` for the route and the bookkeeping):

* `Work.Peluse.Ulower.flatCubeTransform` — **the crux**: the flat cube sum of the level-`s` cube
  terms of `g` is bounded by the flat cube sum of the family `v ↦ g (∑ i, v i)`.  The mechanism is
  `Work.Peluse.Ulower.npowBlindProd`: writing
  `cubeTerm h v g 0 = ∏_{α : Fin s → Bool} star^{|α|} (g (cornerShift h v α))`, every factor with
  `α ≠ 0` is `1`-bounded and *blind* in each coordinate where `α` is true, and blind factors may be
  dropped from a flat cube sum (`C = 1`).

* `Work.Peluse.Ulower.phaseElimGap_of_flatCube` — the **parametric phase elimination**
  `FlatCubeTransform s ⟹ (chirped aggregate large ⟹ γ^{2^s} ≤ C · unchirped aggregate)`: one
  application of Gowers–Cauchy–Schwarz (`Concat.gowersCS`) in the `v`-variable — the product over
  the cube of the blind phases is `1`, and the output is the flat cube sum of
  `v ↦ cubeTerm u v f x · conj (cubeTerm u v f z)` — followed by the generalised Hölder over the
  `(u,x,z)`-index set of size `≤ D^s N²` (`N ≤ (3+s)L`) and the arithmetic cancellation.

* `Work.Peluse.Ulower.windowAggregate` — the **window-sum step**
  `C' · (unchirped aggregate) ≤ boxNormPow (s+1) (arithIcc 1 D)^{s+1} (symIcc L) f`.

Combining the last two with `K = 2^s` and `c = C'/C` gives the theorem.
-/

namespace Work.Peluse.Ulower.ss75

theorem lemma75GCS :
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
  obtain ⟨C, hCpos, hC⟩ := Work.Peluse.Ulower.phaseElimGap_of_flatCube s hs
    (Work.Peluse.Ulower.flatCubeTransform s hs)
  obtain ⟨C', hC'pos, hC'⟩ := Work.Peluse.Ulower.windowAggregate s hs
  refine ⟨2 ^ s, Nat.one_le_two_pow, C' / C, div_pos hC'pos hCpos, ?_⟩
  intro L D f ψ hL hD hDL hf hsupp hblind γ hγ hhyp
  set Eu : ℝ := (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
      * (((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ))⁻¹
      * ∑ u ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (1 : ℤ) (D : ℤ)),
          ‖((L : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v f x‖ ^ 2 with hEu
  set B : ℝ := Work.Peluse.boxNormPow (s + 1) (fun _ : Fin (s + 1) => Work.Peluse.arithIcc 1 D)
      (Work.Peluse.symIcc L) f with hB
  have h1 : γ ^ (2 ^ s) ≤ C * Eu := by
    rw [hEu]
    exact hC L D f ψ hL hD hDL hf hsupp hblind γ hγ hhyp
  have h2 : C' * Eu ≤ B := by
    rw [hEu, hB]
    exact hC' L D f hL hD hDL hf hsupp
  have hratio : 0 ≤ C' / C := le_of_lt (div_pos hC'pos hCpos)
  calc (C' / C) * γ ^ (2 ^ s)
      ≤ (C' / C) * (C * Eu) := mul_le_mul_of_nonneg_left h1 hratio
    _ = C' * Eu := by field_simp
    _ ≤ B := h2

end Work.Peluse.Ulower.ss75

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiTrunc_uncurry_smooth` — the truncated mode series is `C^∞` on the open quadrant

`Work.FTS.PhiStar.Series.psiTrunc α F N` is the finite partial sum

  `psiTrunc α F N z θ = ∑_{m ≤ N} acoeff α m F z · eFam m θ`

of the mode series of the solution of `bslOp α Ψ = F` (`Series/Defs.lean`).  Its `z`-dependence
enters only through the radial coefficients `acoeff α m F` and its `θ`-dependence only through
the *fixed* angular eigenfunctions `eFam m` (`Gegenbauer/Defs.lean`); consequently the joint
smoothness of `psiTrunc α F N` on the open quadrant `Q0 = (0,∞) × (0,π/2)` is exactly the
smoothness of the finite list of radial functions `acoeff α m F` (`m ≤ N`) on `(0,∞)`, since
the angular factors are smooth everywhere.

This file records the two ingredients:

* `contDiff_gC_nat` / `contDiff_eFam_nat`: the Gegenbauer polynomials `gC k` (defined by the
  three-term recurrence) and hence the eigenfunctions `eFam m = cos θ · gC (2m+1)(sin θ)` are
  smooth of *every* finite order.  (`contDiff_gC` of `Gegenbauer/gC_ode.lean` only supplies
  order `3`; the recurrence argument gives all orders at once.)
* `contDiffOn_uncurry_fst` / `contDiffOn_uncurry_snd`: the two separable one-variable factors
  `(z,θ) ↦ g z` resp. `(z,θ) ↦ χ θ` are smooth on a product of sets as soon as `g` resp. `χ`
  is smooth on the corresponding factor (composition with `Prod.fst` / `Prod.snd`).

The target `psiTrunc_uncurry_smooth` is then the closure of `ContDiffOn` under the finite sum
`Finset.range (N+1)` of such separable products (`ContDiffOn.sum`, `ContDiffOn.mul`).
-/

namespace Work.FTS.ClassC

/-- The Gegenbauer polynomials `gC k` of `Gegenbauer/Defs.lean` are smooth of every finite
order: the three-term recurrence `(n+2)C_{n+2} = (2n+5)x·C_{n+1} - (n+3)C_n` is built from
products and linear combinations, which preserve `ContDiff ℝ n` at each fixed order `n`. -/
lemma contDiff_gC_nat : ∀ k n : ℕ, ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.gC k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    intro n
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    intro n
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more k ih1 ih2 =>
    intro n
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (k + 2) = (fun x =>
        (2 * ((k : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) x
          - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k x)
            / ((k : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul (ih2 n)).sub
      (contDiff_const.mul (ih1 n))).div_const _

/-- The Dirichlet eigenfunctions `eFam m θ = cos θ · gC (2m+1)(sin θ)` are smooth of every
finite order. -/
lemma contDiff_eFam_nat (m n : ℕ) : ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ => Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        from rfl]
  exact Real.contDiff_cos.mul ((contDiff_gC_nat (2 * m + 1) n).comp Real.contDiff_sin)

/-- The radial factor `(z,θ) ↦ g z` of a separable function is smooth of order `n` on a product
set as soon as `g` is smooth of order `n` on the first factor. -/
lemma contDiffOn_uncurry_fst {g : ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1) (s ×ˢ t) := by
  exact hg.comp (contDiffOn_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := (n : WithTop ℕ∞))
    (s := s ×ˢ t)) (fun p hp => hp.1)

/-- The angular factor `(z,θ) ↦ χ θ` of a separable function is smooth of order `n` on a product
set as soon as `χ` is smooth of order `n` everywhere. -/
lemma contDiffOn_uncurry_snd {χ : ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (hχ : ContDiff ℝ n χ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => χ p.2) (s ×ˢ t) := by
  exact (hχ.contDiffOn (s := Set.univ)).comp
    (contDiffOn_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := (n : WithTop ℕ∞)) (s := s ×ˢ t))
    (fun p hp => Set.mem_univ _)

theorem psiTrunc_uncurry_smooth {α : ℝ} {F : ℝ → ℝ → ℝ} (N : ℕ)
    (hsm : ∀ m ≤ N, ∀ n : ℕ,
      ContDiffOn ℝ n (Work.FTS.PhiStar.Series.acoeff α m F) (Set.Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  have hfe : (Function.uncurry (fun z θ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ))
      = fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.acoeff α m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 := by
    funext p
    rfl
  rw [hfe]
  refine ContDiffOn.sum (fun m hm => ?_)
  have hmN : m ≤ N := by
    have : m < N + 1 := Finset.mem_range.mp hm
    omega
  exact (contDiffOn_uncurry_fst (s := Set.Ioi 0) (t := Set.Ioo 0 (Real.pi / 2))
      (hsm m hmN n)).mul
    (contDiffOn_uncurry_snd (s := Set.Ioi 0) (t := Set.Ioo 0 (Real.pi / 2))
      (contDiff_eFam_nat m n))

end Work.FTS.ClassC

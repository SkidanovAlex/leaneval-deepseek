/-
# `Work.Diff.STE.flat.energy_deriv_local`

The time derivative of the full flat `Hᵏ` matrix energy along a box-supported (Galerkin)
trajectory, in the *coefficient* form used by the a priori estimate
`Work.Diff.STE.flat.energy_apriori`.

Let `c : ℝ → (Fin n → ℤ) → MatC n` be a coefficient family which is supported in the Galerkin box
`box n N` at every time `σ`, let `g : Torus n` be a smooth `1`-periodic function (the right-hand
side of the projected ODE, evaluated at the current state), and suppose that at the time `t` every
box coefficient of `c` has derivative the corresponding Fourier coefficient of `g`:

  `∂_σ (c σ k' i j) = fourierCoeff (g · i j) k'`  for `k' ∈ box n N`.

Then the full energy `σ ↦ ENormSqFull k (seriesFunM (c σ))` is differentiable at `t`, with

  `∂_σ ENormSqFull k (seriesFunM (c σ))`
  `  = 2 Σ_{i,j} ( Σ_{l : Fin k → Fin n} L2re (∂^l g_{ij}) (∂^l u_{ij}) + L2re g_{ij} u_{ij} )`,

where `u = seriesFunM (c t)`.

## Why this is elementary

The box support is the crucial hypothesis: it makes `seriesFunM (c σ)` a *finite* trigonometric
sum, so (i) the energy is the explicit finite sum

  `ENormSqFull k (seriesFunM (c σ))`
  `  = Σ_{i,j} Σ_{l : Fin k → Fin n} Σ_{k' ∈ box} ‖dmulV (List.ofFn l) (c σ · i j) k'‖²`
  `  + Σ_{i,j} Σ_{l : Fin 0 → Fin n} Σ_{k' ∈ box} ‖dmulV (List.ofFn l) (c σ · i j) k'‖²`

(`Work.Diff.STE.flat.ENormSq_seriesFun_eq_sum`, Parseval plus term by term differentiation), (ii)
differentiating this finite sum is a finite dimensional computation
(`Work.Diff.STE.flat.hasDerivAt_sum_normsq_dmulV`), and (iii) each differentiated summand is the
`L²` pairing of the corresponding derivative of `g` with the derivative of the current series
(`Work.Diff.STE.flat.L2re_pdVec_pdVec_seriesFun`, Parseval/Fourier inversion for the smooth
periodic `g`).

In particular no differentiation under the integral sign, no domination hypothesis and no
neighbourhood in `σ` is needed beyond the finiteness of the box: the argument is
finite-dimensional, which is what makes it work at the endpoint `t = 0` as well.

The level `k = 0` and the `Fin 0`-indexed summands are handled by `sum_fin_zero` (`Fin 0 → Fin n`
is a singleton, so its `univ`-sum is a single term).
-/
import Mathlib
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.ENormSq_seriesFun_eq_sum
import Submission.Work.Diff.STE.flat.hasDerivAt_sum_normsq_dmulV
import Submission.Work.Diff.STE.flat.L2re_pdVec_pdVec_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

open Work.Diff.STE.Flat

/-- A sum over the (singleton) index type `Fin 0 → Fin m` is its single term. -/
lemma sum_fin_zero {α : Type*} [AddCommMonoid α] {m : ℕ} (l₀ : Fin 0 → Fin m)
    (F : (Fin 0 → Fin m) → α) : ∑ l : Fin 0 → Fin m, F l = F l₀ := by
  have h1 : ∑ l : Fin 0 → Fin m, F l = ∑ _l : Fin 0 → Fin m, F l₀ :=
    Finset.sum_congr rfl (fun l _ => by rw [show l = l₀ from funext (fun i => i.elim0)])
  rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, pow_zero]
  simp

/-- Every entry of a smooth matrix-valued function is smooth. -/
lemma contDiff_entry {n : ℕ} {g : Torus n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => g x i j) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun (A : Fin n → Fin n → ℂ) => A i j) := by fun_prop
  exact h1.comp hg

/-- Every entry of a `1`-periodic matrix-valued function is `1`-periodic. -/
lemma periodic1_entry {n : ℕ} {g : Torus n} (hgper : Periodic1 g) (i j : Fin n) :
    Periodic1 (fun x => g x i j) := by
  intro a x
  show g (x + Pi.single a 1) i j = g x i j
  rw [hgper a x]

theorem energy_deriv_local {n : ℕ} {k N : ℕ}
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hcbox : ∀ (σ : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c σ k' = 0)
    (g : Work.Diff.STE.Flat.Torus n) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgper : Work.Diff.STE.Periodic1 g) {t : ℝ}
    (hderiv : ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
      HasDerivAt (fun σ => c σ k' i j)
        (Work.Diff.STE.fourierCoeff (fun x => g x i j) k') t) :
    HasDerivAt (fun σ => Work.Diff.STE.Flat.ENormSqFull k
        (Work.Diff.STE.Flat.seriesFunM (c σ)))
      (2 * ∑ i : Fin n, ∑ j : Fin n,
        ((∑ l : Fin k → Fin n,
            Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
              (Work.Diff.STE.pdVec k l
                (fun x => Work.Diff.STE.Flat.seriesFunM (c t) x i j)))
          + Work.Diff.STE.L2re (fun x => g x i j)
              (fun x => Work.Diff.STE.Flat.seriesFunM (c t) x i j))) t := by
  classical
  have hboxm : ∀ (σ : ℝ) (i j : Fin n) (m : Fin n → ℤ), m ∉ box n N →
      (fun m' => c σ m' i j) m = 0 := by
    intro σ i j m hm; show c σ m i j = 0; rw [hcbox σ m hm]; rfl
  -- ## Step 1: the energy is the explicit finite sum
  have hval : ∀ σ : ℝ, ENormSqFull k (seriesFunM (c σ)) =
      ((∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n, ∑ m ∈ box n N,
          ‖dmulV (List.ofFn l) (fun m' => c σ m' i j) m‖ ^ 2)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin 0 → Fin n, ∑ m ∈ box n N,
          ‖dmulV (List.ofFn l) (fun m' => c σ m' i j) m‖ ^ 2)) := by
    intro σ
    rw [ENormSqFull, ENormSqM, ENormSqM]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      simp only [seriesFunM_apply]
      exact ENormSq_seriesFun_eq_sum k (fun m => c σ m i j) (box n N) (hboxm σ i j)
    · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      simp only [seriesFunM_apply]
      exact ENormSq_seriesFun_eq_sum 0 (fun m => c σ m i j) (box n N) (hboxm σ i j)
  -- ## Step 2: differentiate the explicit finite sum
  have hder : HasDerivAt
      (fun σ : ℝ =>
        (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n, ∑ m ∈ box n N,
            ‖dmulV (List.ofFn l) (fun m' => c σ m' i j) m‖ ^ 2)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin 0 → Fin n, ∑ m ∈ box n N,
            ‖dmulV (List.ofFn l) (fun m' => c σ m' i j) m‖ ^ 2))
      ((∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n, ∑ m ∈ box n N,
          2 * (dmulV (List.ofFn l)
                (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin 0 → Fin n, ∑ m ∈ box n N,
          2 * (dmulV (List.ofFn l)
                (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)) t := by
    refine (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ?_))).add
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ?_)))
    · exact hasDerivAt_sum_normsq_dmulV k (fun σ m => c σ m i j)
        (fun m => Work.Diff.STE.fourierCoeff (fun x => g x i j) m) t (box n N)
        (fun m hm => hderiv m hm i j)
    · exact hasDerivAt_sum_normsq_dmulV 0 (fun σ m => c σ m i j)
        (fun m => Work.Diff.STE.fourierCoeff (fun x => g x i j) m) t (box n N)
        (fun m hm => hderiv m hm i j)
  -- ## Step 3: identify the coefficient sums with the `L²` pairings
  have hLk : ∀ (i j : Fin n) (l : Fin k → Fin n),
      (∑ m ∈ box n N, (dmulV (List.ofFn l)
            (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
          * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
        = Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
            (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)) := by
    intro i j l
    simp only [seriesFunM_apply]
    exact (L2re_pdVec_pdVec_seriesFun k l (fun x => g x i j) (contDiff_entry hg i j)
      (periodic1_entry hgper i j) (fun m => c t m i j) (box n N) (hboxm t i j)).symm
  have hL0 : ∀ (i j : Fin n) (l : Fin 0 → Fin n),
      (∑ m ∈ box n N, (dmulV (List.ofFn l)
            (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
          * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
        = Work.Diff.STE.L2re (Work.Diff.STE.pdVec 0 l (fun x => g x i j))
            (Work.Diff.STE.pdVec 0 l (fun x => seriesFunM (c t) x i j)) := by
    intro i j l
    simp only [seriesFunM_apply]
    exact (L2re_pdVec_pdVec_seriesFun 0 l (fun x => g x i j) (contDiff_entry hg i j)
      (periodic1_entry hgper i j) (fun m => c t m i j) (box n N) (hboxm t i j)).symm
  -- ## Step 4: the level-`k` coefficient sum is `2 * ∑∑∑ₗ L2re`
  have hX : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n, ∑ m ∈ box n N,
        2 * (dmulV (List.ofFn l)
              (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
          * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
      = 2 * ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
            (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)) := by
    have hinner : ∀ (i j : Fin n),
        (∑ l : Fin k → Fin n, ∑ m ∈ box n N, 2 * (dmulV (List.ofFn l)
              (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
          = 2 * ∑ l : Fin k → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
                (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)) := by
      intro i j
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [← Finset.mul_sum, hLk i j l]
    calc (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n, ∑ m ∈ box n N,
          2 * (dmulV (List.ofFn l)
                (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
        = ∑ i : Fin n, ∑ j : Fin n, 2 * ∑ l : Fin k → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
                (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hinner i j))
      _ = 2 * ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
                (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)) := by
          rw [Finset.mul_sum]; simp only [Finset.mul_sum]
  -- ## Step 5: the level-`0` coefficient sum is `2 * ∑∑ L2re`
  have hY : (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin 0 → Fin n, ∑ m ∈ box n N,
        2 * (dmulV (List.ofFn l)
              (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
          * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
          Work.Diff.STE.L2re (fun x => g x i j) (fun x => seriesFunM (c t) x i j) := by
    have hinner : ∀ (i j : Fin n),
        (∑ l : Fin 0 → Fin n, ∑ m ∈ box n N, 2 * (dmulV (List.ofFn l)
              (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
          = 2 * Work.Diff.STE.L2re (fun x => g x i j)
              (fun x => seriesFunM (c t) x i j) := by
      intro i j
      rw [sum_fin_zero (fun i : Fin 0 => i.elim0)
        (fun l => ∑ m ∈ box n N, 2 * (dmulV (List.ofFn l)
              (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)]
      rw [← Finset.mul_sum]
      rw [hL0 i j (fun i : Fin 0 => i.elim0)]
      rfl
    calc (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin 0 → Fin n, ∑ m ∈ box n N,
          2 * (dmulV (List.ofFn l)
                (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
        = ∑ i : Fin n, ∑ j : Fin n, 2 * Work.Diff.STE.L2re (fun x => g x i j)
              (fun x => seriesFunM (c t) x i j) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hinner i j))
      _ = 2 * ∑ i : Fin n, ∑ j : Fin n,
              Work.Diff.STE.L2re (fun x => g x i j) (fun x => seriesFunM (c t) x i j) := by
          rw [Finset.mul_sum]; simp only [Finset.mul_sum]
  -- ## Step 6: assemble
  have hXY : ((∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n, ∑ m ∈ box n N,
          2 * (dmulV (List.ofFn l)
                (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin 0 → Fin n, ∑ m ∈ box n N,
          2 * (dmulV (List.ofFn l)
                (fun m' => Work.Diff.STE.fourierCoeff (fun x => g x i j) m') m
            * star (dmulV (List.ofFn l) (fun m' => c t m' i j) m)).re))
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
        ((∑ l : Fin k → Fin n,
            Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
              (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)))
          + Work.Diff.STE.L2re (fun x => g x i j)
              (fun x => seriesFunM (c t) x i j)) := by
    rw [hX, hY]
    have hsplit : (∑ i : Fin n, ∑ j : Fin n,
          ((∑ l : Fin k → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
                (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)))
            + Work.Diff.STE.L2re (fun x => g x i j)
                (fun x => seriesFunM (c t) x i j)))
        = (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin k → Fin n,
            Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (fun x => g x i j))
              (Work.Diff.STE.pdVec k l (fun x => seriesFunM (c t) x i j)))
          + (∑ i : Fin n, ∑ j : Fin n,
              Work.Diff.STE.L2re (fun x => g x i j)
                (fun x => seriesFunM (c t) x i j)) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit]
    ring
  rw [hXY] at hder
  exact hder.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun σ => hval σ))

end

end Work.Diff.STE.flat

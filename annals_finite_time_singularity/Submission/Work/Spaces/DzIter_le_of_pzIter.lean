/-
Copyright: work module for the Elgindi finite-time singularity project.

# `|D_z^b h| ≤ 100 M` from the bounds `|z^j ∂_z^j h| ≤ M`

The operators `D_z = z ∂_z` and `∂_z` satisfy `∂_z D_z = D_z ∂_z + ∂_z`, hence for
every `n`

`D_z^n h = ∑_{k=0}^{n} S(n,k) z^k ∂_z^k h`,

where `S(n,k) = scoef n k` is the Stirling number of the second kind
(`Submission.Work.Spaces.scoef`).  It follows that at a point where the functions
`z^k ∂_z^k h` (`k ≤ n`) are all bounded by `M`, the derivative `D_z^n h` is bounded
by `(∑_k S(n,k)) · M = bell n · M`.  The Bell numbers of the rows `n ≤ 4` are
`1, 1, 2, 5, 15`, so for `b ≤ 4`

`|D_z^b h z θ| ≤ 15 M ≤ 100 M`.

The expansion is proved by induction on `n`, using the smoothness of the `z`-slices
of `h` to differentiate the terms `z'^k ∂_z^k h(z',θ)` (the induction step being
exactly the reindexing identity `scoef_sum_shift`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.scoef
import Submission.Work.Spaces.scoef_sum_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Elementary calculus of the one-dimensional derivative -/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) : deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- `deriv` of the `k`-th iterated `z`-derivative of the `z`-slice: this is the
definition of `pzIter`, so nothing has to be proved. -/
private theorem deriv_pzIter_slice (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => pzIter k h z' θ) z = pzIter (k + 1) h z θ := rfl

/-- The elementary algebra of one term of the induction step: the extra factor `z`
produced by `D_z` from the derivative of `z^k`. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-! ## Smoothness of the `z`-slices of the iterated derivatives -/

/-- If the `z`-slice `z ↦ h z θ` is `C^∞` on the open half-line `(-1,∞)`, then so is
each of its iterated `z`-derivatives.  (`ContDiffOn.deriv_of_isOpen` applied `k`
times; `Ioi (-1)` is open and `⊤ + 1 ≤ ⊤`.) -/
theorem pzIter_slice_contDiff {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ k : ℕ, ContDiffOn ℝ ⊤ (fun z' => pzIter k h z' θ) (Set.Ioi (-1)) := by
  intro k
  induction k with
  | zero => simpa using hsmooth
  | succ n ih =>
    have h := ih.deriv_of_isOpen isOpen_Ioi (le_top : (⊤ : ℕ∞ω) + 1 ≤ ⊤)
    simpa [pzIter_succ, pz] using h

/-- Differentiability at an interior point of the `z`-slices of the iterated
`z`-derivatives of `h`. -/
theorem differentiableAt_pzIter_slice {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsmooth : ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1))) (k : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    DifferentiableAt ℝ (fun z' => pzIter k h z' θ) z :=
  ((pzIter_slice_contDiff hsmooth k).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)

/-! ## The expansion of `D_z^n` in terms of the Stirling numbers -/

/-- **The expansion of the iterated operator `D_z = z ∂_z`.**  For a function whose
`z`-slices are `C^∞` on `(-1,∞)`, for every `n`,
`D_z^n h = ∑_{k≤n} S(n,k) z^k ∂_z^k h` on `(-1,∞) × [0,π/2]`. -/
theorem DzIter_eq_sum_scoef {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1))) :
    ∀ n : ℕ, ∀ z ∈ Set.Ioi (-1), ∀ θ ∈ Iθ,
      DzIter n h z θ = ∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * (z ^ k * pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
    intro z hz θ hθ
    simp [DzIter, scoef]
  | succ n ih =>
    intro z hz θ hθ
    have hdiff : ∀ k : ℕ, DifferentiableAt ℝ (fun z' => pzIter k h z' θ) z := fun k =>
      differentiableAt_pzIter_slice (hsmooth θ hθ) k hz
    have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
      differentiableAt_pow k
    have hd3 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * pzIter k h z' θ) z :=
      fun k => (hd1 k).mul (hdiff k)
    -- the induction hypothesis, as an eventual equality near `z`
    have hev : (fun z' => DzIter n h z' θ)
        =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' hz' θ hθ
    -- the derivative of each summand
    have hterm : ∀ k : ℕ, deriv (fun z' : ℝ => (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) z
        = (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
            + z ^ k * pzIter (k + 1) h z θ) := by
      intro k
      rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * pzIter k h z' θ)
        (scoef n k : ℝ) (hd3 k)]
      congr 1
      have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
        (d := fun z' : ℝ => pzIter k h z' θ) (hd1 k) (hdiff k)
      have hmul' : deriv (fun z' : ℝ => z' ^ k * pzIter k h z' θ) z
          = deriv (fun z' : ℝ => z' ^ k) z * pzIter k h z θ
            + z ^ k * deriv (fun z' : ℝ => pzIter k h z' θ) z := hmul
      rw [hmul', deriv_zpow, deriv_pzIter_slice]
    have hderiv : deriv (fun z' => DzIter n h z' θ) z
        = ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
              + z ^ k * pzIter (k + 1) h z θ) := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ))
          = (∑ k ∈ Finset.range (n + 1),
              fun z' => (scoef n k : ℝ) * (z' ^ k * pzIter k h z' θ)) := by
        funext z'
        simp [Finset.sum_apply]
      rw [hsumfun, deriv_sum (fun k hk => (hd3 k).const_mul (scoef n k : ℝ))]
      exact Finset.sum_congr rfl fun k hk => hterm k
    calc DzIter (n + 1) h z θ
        = z * deriv (fun z' => DzIter n h z' θ) z := by simp [DzIter_succ, Dz, pz]
      _ = z * (∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
              + z ^ k * pzIter (k + 1) h z θ)) := by rw [hderiv]
      _ = ∑ k ∈ Finset.range (n + 1),
            (scoef n k : ℝ) * ((k : ℝ) * z ^ k * pzIter k h z θ
              + z ^ (k + 1) * pzIter (k + 1) h z θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have h1 : z * ((scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
                + z ^ k * pzIter (k + 1) h z θ))
              = (scoef n k : ℝ) * (z * ((k : ℝ) * z ^ (k - 1) * pzIter k h z θ
                + z ^ k * pzIter (k + 1) h z θ)) := by ring
          rw [h1, z_mul_term]
      _ = ∑ j ∈ Finset.range (n + 2), (scoef (n + 1) j : ℝ) * (z ^ j * pzIter j h z θ) :=
          scoef_sum_shift n (fun k => pzIter k h z θ) z

/-! ## The weighted sum bound -/

/-- If `|x k| ≤ M` for `k ≤ n` then the Stirling-weighted sum `∑_k S(n,k) x k` is
bounded by `bell n · M` in absolute value.  (All the coefficients `S(n,k)` are
nonnegative, so the triangle inequality gives the total coefficient mass `bell n`.) -/
theorem abs_sum_scoef_mul_le (n : ℕ) (M : ℝ) (x : ℕ → ℝ) (hx : ∀ k ≤ n, |x k| ≤ M) :
    |∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * x k| ≤ (bell n : ℝ) * M := by
  have h1 : |∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * x k|
      ≤ ∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * |x k| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (scoef n k))]
  have h2 : ∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * |x k|
      ≤ ∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * M := by
    refine Finset.sum_le_sum fun k hk => ?_
    refine mul_le_mul_of_nonneg_left (hx k ?_) (Nat.cast_nonneg (scoef n k))
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have h3 : ∑ k ∈ Finset.range (n + 1), (scoef n k : ℝ) * M = (bell n : ℝ) * M := by
    rw [← Finset.sum_mul, bell, Nat.cast_sum]
  linarith [h1, h2, h3.le, h3.ge]

/-! ## The main estimate -/

/-- **`D_z`-derivatives are bounded by the `z^j ∂_z^j`-bounds.**  If the smooth
function `h` satisfies `|z^j ∂_z^j h| ≤ M` on `[0,∞) × [0,π/2]` for all `j ≤ 4`, then
the first four iterates of `D_z = z ∂_z` satisfy `|D_z^b h| ≤ 100 M` on the whole
domain, for every `b ≤ 4`. -/
theorem DzIter_le_of_pzIter {h : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hsmooth : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    (hbound : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j h z θ| ≤ M)
    (b : ℕ) (hb : b ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter b h z θ| ≤ 100 * M := by
  intro z hz θ hθ
  have hz' : z ∈ Set.Ioi (-1) := by
    simp only [Iz, Set.mem_Ici] at hz
    simp only [Set.mem_Ioi]; linarith
  rw [DzIter_eq_sum_scoef hsmooth b z hz' θ hθ]
  have hsum := abs_sum_scoef_mul_le b M (fun k => z ^ k * pzIter k h z θ)
    (fun k hk => hbound k (le_trans hk hb) z hz θ hθ)
  have hbell : (bell b : ℝ) ≤ 100 := by exact_mod_cast bell_le b hb
  calc |∑ k ∈ Finset.range (b + 1), (scoef b k : ℝ) * (z ^ k * pzIter k h z θ)|
      ≤ (bell b : ℝ) * M := hsum
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right hbell hM

end Work.Spaces

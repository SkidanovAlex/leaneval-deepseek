/-
Copyright: work module for the Elgindi finite-time singularity project.

# Leibniz rule for `∂_z^k D_θ^j (f · g)`

The operators `∂_z` (plain `z`-derivative at fixed angle) and `D_θ = sin(2θ) ∂_θ`
are commuting derivations on functions of the self-similar variables `(z,θ)`, so
for two functions `f g` and every pair `k j` of integers the iterate expands
binomially:

`∂_z^k D_θ^j (f g) = ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{j-a} g`

at every point of the domain `[0,∞) × [0,π/2]`.  This is the *equality* version
of the estimate `Work.Spaces.pz_mixed_mul_le`.

The argument follows `Work.Spaces.pz_mixed_mul_le`: at fixed angle `θ` the
Leibniz rule `DthIter_mul` (from `Submission.Work.Spaces.DthIter_mul`) expands
`D_θ^j (f g)` into a finite sum of products, valid on an open set of `z`; the
expansion therefore agrees with `D_θ^j (f g)` near `z`, and `k`-fold
differentiation in `z` of the resulting sum is Mathlib's `iteratedDeriv_mul`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DthIter_contDiffAt
import Submission.Work.Spaces.DthIter_mul

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

/-! ## Smoothness of the `z`-slices of the iterates of `D_θ` -/

/-- For a `SmoothInt` function and an angle `θ ∈ [0,π/2]`, the `z`-slice of every
iterate of `D_θ` is `C^∞` at every `z ∈ [0,∞)`. -/
lemma contDiffAt_DthIter_zslice (h : ℝ → ℝ → ℝ) (hh : SmoothInt h) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) (a : ℕ) :
    ContDiffAt ℝ ⊤ (fun z' => DthIter a h z' θ) z := by
  have hzIoi : z ∈ Set.Ioi (-1) := by
    simp only [Iz, Set.mem_Ici] at hz
    simp only [Set.mem_Ioi]; linarith
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simpa using hh.contDiffAt_z_slice hz hθ
  · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    by_cases hθi : θ ∈ Ioo 0 (π / 2)
    · exact contDiffAt_slice_left
        (DthIter_contDiffAt h (a' + 1) (hh.contDiffAt_uncurry hzIoi hθi))
    · have hsin := sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      have hzero : (fun z' => DthIter (a' + 1) h z' θ) = fun _ => (0 : ℝ) :=
        funext fun z' => DthIter_succ_eq_zero_of_sin_eq_zero a' h hsin
      rw [hzero]
      exact contDiffAt_const

/-! ## The `θ`-Leibniz identity on `z`-slices -/

/-- At fixed `θ ∈ [0,π/2]`, the `D_θ`-Leibniz expansion of `D_θ^j (f g)` agrees
with `D_θ^j (f g)` on a neighbourhood of every `z ∈ [0,∞)`. -/
lemma DthIter_mul_zslice_eventuallyEq (j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : SmoothInt f) (hg : SmoothInt g) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (fun z' => DthIter j (fun z θ => f z θ * g z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (DthIter a f z' θ * DthIter (j - a) g z' θ)) := by
  have hzIoi : z ∈ Set.Ioi (-1) := by
    simp only [Iz, Set.mem_Ici] at hz
    simp only [Set.mem_Ioi]; linarith
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    filter_upwards with z'
    simp
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
    by_cases hθi : θ ∈ Ioo 0 (π / 2)
    · filter_upwards [isOpen_Ioi.mem_nhds hzIoi] with z' hz'
      exact DthIter_mul (j' + 1) f g z' (Ioo 0 (π / 2)) isOpen_Ioo
        (hf.contDiffOn_theta_slice hz') (hg.contDiffOn_theta_slice hz') θ hθi
    · have hsin := sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      filter_upwards with z'
      rw [DthIter_succ_eq_zero_of_sin_eq_zero j' _ hsin]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        simp [DthIter_succ_eq_zero_of_sin_eq_zero j' g hsin]
      · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hapos.ne'
        simp [DthIter_succ_eq_zero_of_sin_eq_zero a' f hsin]

/-! ## The main Leibniz rule -/

theorem pz_DthIter_mul_eq (k j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothInt f) (hg : Work.Spaces.SmoothInt g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
            ((j.choose a : ℝ) * (k.choose c : ℝ))
              * (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ
                  * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ) := by
  intro z hz θ hθ
  have hslice : ∀ (h : ℝ → ℝ → ℝ), SmoothInt h → ∀ a : ℕ,
      ContDiffAt ℝ ⊤ (fun z' => DthIter a h z' θ) z :=
    fun h hh a => contDiffAt_DthIter_zslice h hh hz hθ a
  have hleib := DthIter_mul_zslice_eventuallyEq j f g hf hg hz hθ
  rw [pzIter_eq_iteratedDeriv k _ z θ, Filter.EventuallyEq.iteratedDeriv_eq k hleib]
  have hsum := iteratedDeriv_sum_const_mul (s := Finset.range (j + 1))
    (c := fun a => (j.choose a : ℝ))
    (F := fun a z' => DthIter a f z' θ * DthIter (j - a) g z' θ) k z
    (fun a _ => ((hslice f hf a).mul (hslice g hg (j - a))).of_le le_top)
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : (fun z' => DthIter a f z' θ * DthIter (j - a) g z' θ)
      = (fun z' => DthIter a f z' θ) * (fun z' => DthIter (j - a) g z' θ) := by
    funext z'; rfl
  rw [hfun]
  have hmul := iteratedDeriv_mul (f := fun z' => DthIter a f z' θ)
    (g := fun z' => DthIter (j - a) g z' θ) (x := z) (n := k)
    ((hslice f hf a).of_le le_top) ((hslice g hg (j - a)).of_le le_top)
  rw [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← pzIter_eq_iteratedDeriv c (DthIter a f) z θ,
    ← pzIter_eq_iteratedDeriv (k - c) (DthIter (j - a) g) z θ]
  ring

end Work.Spaces

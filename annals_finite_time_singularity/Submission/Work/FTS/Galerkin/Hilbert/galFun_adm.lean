import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.Galerkin.Hilbert
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_add
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul
import Submission.Work.FTS.Galerkin.Inhabit
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.CoercivityStep.Step.HkIPStep_core
import Submission.Work.FTS.CoercivityStep.Norm.HkMem_add
import Submission.Work.Coercivity.E2Mixed.E2model_mixed_split
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.Coercivity.L12dens_integrableOn
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin.Hilbert

set_option autoImplicit false

/-! ## Scalar homogeneity of the mixed derivatives

The iterated operators `D_z`, `D_θ` and their mixed iterates commute with multiplication by a
constant **unconditionally**: `deriv` is scalar homogeneous with no differentiability hypothesis
(if `f` is not differentiable at `x` then neither is `c · f` for `c ≠ 0`, and both sides vanish).
This is the same argument as the `private` lemmas of
`Submission/Work/FTS/Galerkin/Hilbert/HkMem_const_mul.lean`, restated here because they are not
exported. -/

private theorem gal_deriv_const_mul (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem gal_pz_const (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [gal_deriv_const_mul]

private theorem gal_pth_const (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [gal_deriv_const_mul]

private theorem gal_Dz_const (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, gal_pz_const]
  ring

private theorem gal_Dth_const (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, gal_pth_const]
  ring

private theorem gal_DzIter_const (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, gal_Dz_const]

private theorem gal_DthIter_const (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, gal_Dth_const]

private theorem gal_mixed_const (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, gal_DthIter_const, gal_DzIter_const]

private theorem gal_mixed_const_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ := by
  rw [gal_mixed_const]

/-! ## Smoothness of finite linear combinations

`SmoothNbhd` is closed under finite linear combinations with arbitrary real coefficients: it is
closed under addition (`Work.FTS.CoercivityStep.Step.SmoothNbhd_add`) and under multiplication by
a constant (`Work.FTS.CoercivityStep.Step.SmoothNbhd_const_mul`). -/

/-- **`SmoothNbhd` is closed under finite linear combinations.** -/
theorem SmoothNbhd_finsetSum {ι : Type*} [DecidableEq ι] (c : ι → ℝ) (F : ι → Fn) :
    ∀ s : Finset ι, (∀ i ∈ s, Work.Spaces.SmoothNbhd (F i)) →
      Work.Spaces.SmoothNbhd (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have h : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ
        simp
      rw [h]
      exact contDiffOn_const
  | insert a s' ha ih =>
      intro hsm
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = (fun z θ => c a * F a z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]
        rfl
      rw [hsum]
      exact Work.FTS.CoercivityStep.Step.SmoothNbhd_add
        (Work.FTS.CoercivityStep.Step.SmoothNbhd_const_mul (c a)
          (hsm a (Finset.mem_insert_self a s')))
        (ih (fun i hi => hsm i (Finset.mem_insert_of_mem hi)))

/-! ## `ℋ^k`-membership of finite linear combinations -/

/-- **`ℋ^k` is closed under finite linear combinations.**  If every `F i` with `i ∈ s` is smooth
on a neighbourhood of the closed quadrant and lies in `ℋ^k`, then so does `∑_{i∈s} c i * F i`.

This is the finite-sum form of `Work.FTS.Galerkin.Hilbert.HkMem_add` (two summands) and
`HkMem_const_mul` (scalars); it is what makes the Galerkin combination
`Work.FTS.Galerkin.galFun φ c` lie in `ℋ⁴`. -/
theorem HkMem_finsetSum {α : ℝ} {k : ℕ} {ι : Type*} [DecidableEq ι] (c : ι → ℝ) (F : ι → Fn) :
    ∀ s : Finset ι, (∀ i ∈ s, Work.Spaces.SmoothNbhd (F i)) →
      (∀ i ∈ s, Work.Spaces.HkMem α k (F i)) →
      Work.Spaces.HkMem α k (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have h : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ
        simp
      rw [h]
      exact Work.FTS.Galerkin.Inhabit.HkMem_zeroF α k
  | insert a s' ha ih =>
      intro hsm hmem
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = (fun z θ => c a * F a z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]
        rfl
      rw [hsum]
      exact Work.FTS.Galerkin.Hilbert.HkMem_add
        (Work.FTS.CoercivityStep.Step.SmoothNbhd_const_mul (c a)
          (hsm a (Finset.mem_insert_self a s')))
        (SmoothNbhd_finsetSum c F s' (fun i hi => hsm i (Finset.mem_insert_of_mem hi)))
        (Work.FTS.Galerkin.Hilbert.HkMem_const_mul (c a)
          (hsm a (Finset.mem_insert_self a s')) (hmem a (Finset.mem_insert_self a s')))
        (ih (fun i hi => hsm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmem i (Finset.mem_insert_of_mem hi)))

/-! ## Linearity of the mixed operator over finite combinations -/

/-- **The mixed operator `D_z^b D_θ^a` is additive over a finite combination of `SmoothNbhd`
functions.**  For functions `F i` (`i ∈ s`) smooth on a neighbourhood of the closed quadrant and
coefficients `c : ι → ℝ`,
`D_z^b D_θ^a (∑_{i∈s} c i * F i) = ∑_{i∈s} c i * (D_z^b D_θ^a F i)`
at every point of the open neighbourhood `Work.Spaces.nbhU` of the closed quadrant — in particular
at every point of the closed quadrant `[0,∞) × [0,π/2]` (`Work.Spaces.mem_nbhU`).

This is the pointwise identity computing the weighted derivatives of a Galerkin combination term
by term.  The additivity of `D_z^b D_θ^a` over a sum of two smooth functions is
`Work.Coercivity.E2Mixed.mixed_add_of_isOpen` on the open set `Work.Spaces.nbhU`, whose
`ContDiffOn` hypotheses are exactly `SmoothNbhd`; the scalar homogeneity is unconditional
(`gal_mixed_const`). -/
theorem mixed_finsetSum {ι : Type*} [DecidableEq ι] (c : ι → ℝ) (F : ι → Fn) (b a : ℕ) :
    ∀ s : Finset ι, (∀ i ∈ s, Work.Spaces.SmoothNbhd (F i)) →
      ∀ z θ, (z, θ) ∈ Work.Spaces.nbhU →
        Work.Spaces.mixed b a (fun z θ => ∑ i ∈ s, c i * F i z θ) z θ
          = ∑ i ∈ s, c i * Work.Spaces.mixed b a (F i) z θ := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ z θ _
      have h : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ
        simp
      rw [h, Work.FTS.Galerkin.mixed_zero_fun b a]
      simp
  | insert p s' hp ih =>
      intro hsm z θ hy
      have hsum : (fun z θ => ∑ i ∈ insert p s', c i * F i z θ)
          = (fun z θ => c p * F p z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert hp]
        rfl
      rw [hsum]
      have hA : Work.Spaces.SmoothNbhd (fun z θ => c p * F p z θ) :=
        Work.FTS.CoercivityStep.Step.SmoothNbhd_const_mul (c p)
          (hsm p (Finset.mem_insert_self p s'))
      have hB : Work.Spaces.SmoothNbhd (fun z θ => ∑ i ∈ s', c i * F i z θ) :=
        SmoothNbhd_finsetSum c F s' (fun i hi => hsm i (Finset.mem_insert_of_mem hi))
      have hadd := Work.Coercivity.E2Mixed.mixed_add_of_isOpen
        (V := Work.Spaces.nbhU) Work.Spaces.isOpen_nbhU hA hB b a
      rw [show Work.Spaces.mixed b a
            ((fun z θ => c p * F p z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ)) z θ
          = Work.Spaces.mixed b a (fun z θ => c p * F p z θ) z θ
            + Work.Spaces.mixed b a (fun z θ => ∑ i ∈ s', c i * F i z θ) z θ from hadd hy]
      rw [Finset.sum_insert hp, gal_mixed_const_apply,
        ih (fun i hi => hsm i (Finset.mem_insert_of_mem hi)) z θ hy]

/-! ## Congruence of the `L₁₂` zero mode -/

/-- **The `L₁₂` zero mode only sees the values on the positive half-line times `Iθ`.**
`Work.Coercivity.L12f f 0 = ∫_{s ∈ (0,∞)} ∫_{θ ∈ Iθ} K θ · f s θ / s dθ ds` is an iterated
integral, so two functions that agree on `(0,∞) × Iθ` have the same zero mode — no integrability
hypothesis is needed, since both the outer and the inner integral are congruent integrals. -/
theorem L12f_congr {u v : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → θ ∈ Work.Spaces.Iθ → u z θ = v z θ) :
    Work.Coercivity.L12f u 0 = Work.Coercivity.L12f v 0 := by
  show Work.FM.L12 Work.Spaces.K u 0 = Work.FM.L12 Work.Spaces.K v 0
  simp only [Work.FM.L12]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  simp only [Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [h s θ hs hθ]

/-! ## Additivity of the `L₁₂` zero mode -/

/-- **Two-term additivity of the `L₁₂` zero mode.**  For `A`, `B` smooth on a neighbourhood of the
closed quadrant whose `L₁₂`-densities are integrable on `(0,∞)`,
`L₁₂(A + B)(0) = L₁₂(A)(0) + L₁₂(B)(0)`.

The integrability hypotheses are not removable (the Bochner integral is not additive without
them).  Note that one must *not* use `Work.FM.L12_add` directly: it asks for the integrability of
the angular slices at *every* real `s`, and `SmoothNbhd` gives no information for `s < -1`.  Since
`L₁₂(·)(0)` integrates over `Ioi 0` only, additivity there is enough, and for `s > 0` the slices
are continuous on the compact `Iθ` by `Work.Elliptic.continuousOn_slice_theta_Iθ`. -/
theorem L12f_add_of_smooth {A B : ℝ → ℝ → ℝ} (hA : Work.Spaces.SmoothNbhd A)
    (hB : Work.Spaces.SmoothNbhd B)
    (hintA : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K A) (Set.Ioi 0))
    (hintB : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K B) (Set.Ioi 0)) :
    Work.Coercivity.L12f (fun z θ => A z θ + B z θ) 0
      = Work.Coercivity.L12f A 0 + Work.Coercivity.L12f B 0 := by
  have hdens : ∀ s ∈ Set.Ioi (0 : ℝ),
      Work.FM.L12dens Work.Spaces.K (fun z θ => A z θ + B z θ) s
        = Work.FM.L12dens Work.Spaces.K A s + Work.FM.L12dens Work.Spaces.K B s := by
    intro s hs
    have hs1 : s ∈ Set.Ioi (-1 : ℝ) := by
      simp only [Set.mem_Ioi] at hs ⊢
      linarith
    have hKA : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * A s θ / s) Work.Spaces.Iθ :=
      (((Work.Elliptic.continuous_ktheta.continuousOn.mul
        (Work.Elliptic.continuousOn_slice_theta_Iθ A hA hs1))).div_const s).integrableOn_compact
        isCompact_Icc
    have hKB : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * B s θ / s) Work.Spaces.Iθ :=
      (((Work.Elliptic.continuous_ktheta.continuousOn.mul
        (Work.Elliptic.continuousOn_slice_theta_Iθ B hB hs1))).div_const s).integrableOn_compact
        isCompact_Icc
    simp only [Work.FM.L12dens]
    have hcongr : (∫ θ in Set.Icc 0 (Real.pi / 2),
          Work.Spaces.K θ * (A s θ + B s θ) / s)
        = ∫ θ in Set.Icc 0 (Real.pi / 2),
            (Work.Spaces.K θ * A s θ / s + Work.Spaces.K θ * B s θ / s) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hcongr]
    exact MeasureTheory.integral_add hKA hKB
  show Work.FM.L12 Work.Spaces.K (fun z θ => A z θ + B z θ) 0
      = Work.FM.L12 Work.Spaces.K A 0 + Work.FM.L12 Work.Spaces.K B 0
  simp only [Work.FM.L12]
  have hkey : (∫ s in Set.Ioi (0 : ℝ),
        Work.FM.L12dens Work.Spaces.K (fun z θ => A z θ + B z θ) s)
      = ∫ s in Set.Ioi (0 : ℝ),
          (Work.FM.L12dens Work.Spaces.K A s + Work.FM.L12dens Work.Spaces.K B s) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hdens
  rw [hkey]
  exact MeasureTheory.integral_add hintA hintB

/-- **The `L₁₂` zero mode vanishes on finite linear combinations of functions with vanishing zero
mode.**  For `F i` (`i ∈ s`) smooth on a neighbourhood of the closed quadrant, in `ℋ⁴` (so that
their `L₁₂`-densities are integrable, `Work.Coercivity.L12dens_integrableOn`) and with
`L₁₂(F i)(0) = 0`, one has `L₁₂(∑_{i∈s} c i * F i)(0) = 0`.

This is the third clause of `Work.Coercivity.HkAdm` for Galerkin combinations: it is what makes
`Work.FTS.Galerkin.galFun φ c` admissible at order `4`. -/
theorem L12f_finsetSum_zero {α : ℝ} {ι : Type*} [DecidableEq ι] (c : ι → ℝ) (F : ι → Fn) :
    ∀ s : Finset ι, (∀ i ∈ s, Work.Spaces.SmoothNbhd (F i)) →
      (∀ i ∈ s, Work.Spaces.HkMem α 4 (F i)) →
      (∀ i ∈ s, Work.Coercivity.L12f (F i) 0 = 0) →
      Work.Coercivity.L12f (fun z θ => ∑ i ∈ s, c i * F i z θ) 0 = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      have h : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ
        simp
      rw [h]
      show Work.FM.L12 Work.Spaces.K (fun _ _ : ℝ => (0 : ℝ)) 0 = 0
      simp [Work.FM.L12, Work.FM.L12dens]
  | insert a s' ha ih =>
      intro hsm hmem h0
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = fun z θ => c a * F a z θ + (∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]
      have hAsm : Work.Spaces.SmoothNbhd (fun z θ => c a * F a z θ) :=
        Work.FTS.CoercivityStep.Step.SmoothNbhd_const_mul (c a)
          (hsm a (Finset.mem_insert_self a s'))
      have hBsm : Work.Spaces.SmoothNbhd (fun z θ => ∑ i ∈ s', c i * F i z θ) :=
        SmoothNbhd_finsetSum c F s' (fun i hi => hsm i (Finset.mem_insert_of_mem hi))
      have hAmem : Work.Spaces.HkMem α 4 (fun z θ => c a * F a z θ) :=
        Work.FTS.Galerkin.Hilbert.HkMem_const_mul (c a)
          (hsm a (Finset.mem_insert_self a s'))
          (hmem a (Finset.mem_insert_self a s'))
      have hBmem : Work.Spaces.HkMem α 4 (fun z θ => ∑ i ∈ s', c i * F i z θ) :=
        HkMem_finsetSum c F s' (fun i hi => hsm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmem i (Finset.mem_insert_of_mem hi))
      have hsplit := L12f_add_of_smooth (A := fun z θ => c a * F a z θ)
        (B := fun z θ => ∑ i ∈ s', c i * F i z θ) hAsm hBsm
        (Work.Coercivity.L12dens_integrableOn α 4 (fun z θ => c a * F a z θ) hAsm hAmem)
        (Work.Coercivity.L12dens_integrableOn α 4 (fun z θ => ∑ i ∈ s', c i * F i z θ) hBsm hBmem)
      rw [hsum, hsplit]
      have hAval : Work.Coercivity.L12f (fun z θ => c a * F a z θ) 0
          = c a * Work.Coercivity.L12f (F a) 0 := by
        show Work.FM.L12 Work.Spaces.K (fun z θ => c a * F a z θ) 0
            = c a * Work.FM.L12 Work.Spaces.K (F a) 0
        exact Work.FM.L12_const_mul
      rw [hAval, h0 a (Finset.mem_insert_self a s'), mul_zero,
        ih (fun i hi => hsm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmem i (Finset.mem_insert_of_mem hi))
          (fun i hi => h0 i (Finset.mem_insert_of_mem hi))]
      ring

/-! ## The main theorem

The proof assembled below follows the route of the docstring, with these local ingredients:

* `SmoothNbhd_finsetSum` — `SmoothNbhd` is closed under finite linear combinations;
* `HkMem_finsetSum` — `ℋ^k` is closed under finite linear combinations (induction on the finset
  from `Work.FTS.Galerkin.Hilbert.HkMem_add` and `HkMem_const_mul`);
* `mixed_finsetSum` — the mixed operator is linear over a finite combination of `SmoothNbhd`
  functions, pointwise on `Work.Spaces.nbhU` (hence on the closed quadrant);
* `L12f_congr` — the `L₁₂` zero mode is a congruent integral, so it only sees `(0,∞) × Iθ`;
* `L12f_add_of_smooth` and `L12f_finsetSum_zero` — the `L₁₂` zero mode is additive over finite
  combinations of functions vanishing individually, the integrability inputs coming from the
  `HkMem` clauses through `Work.Coercivity.L12dens_integrableOn`.

The only transfer that is not purely formal is the passage from the explicit finite combination
`∑ k, c k * mixed b a (φ k)` (about which `HkMem_finsetSum`/`L12f_finsetSum_zero` speak) to the
literal mixed derivative `mixed b a (galFun φ c)` of the Galerkin profile: this uses
`mixed_finsetSum` pointwise on the neighbourhood together with
`Work.Coercivity.HkMem_congr_Ioi` (resp. `L12f_congr`). -/

/-- **Galerkin combinations of admissible test functions are admissible** (in the sense of
`Work.Coercivity.HkAdm`, i.e. smooth on a neighbourhood of the closed quadrant, with all mixed
derivatives up to order `4` in `ℋ⁴` and with vanishing `L₁₂` zero mode).

This is the statement that the finite-dimensional Galerkin space of audit N6 step 2 consists of
admissible functions: it is what lets the coercivity/dominance fields of `Work.Coercivity.IsHkIP`
(`HkAdm α 4 f → c|f|²_{ℋ⁴} ≤ IP (𝓛_Γ^T f) f`, `IP f f ≤ C|f|²_{ℋ⁴}`) be applied to the Galerkin
profiles — and hence what makes the bridge `Work.FTS.Galerkin.coeffBall_of_profileBound` (the
discharge of the bundle's a-priori field `hCoeffBound` from the paper's `ℋ⁴`-bound on the Galerkin
profiles) applicable.

Intended proof: `SmoothNbhd` is closed under finite linear combinations
(`SmoothNbhd_add`, `SmoothNbhd_const_mul`, `Work.Coercivity.HkIPStep_core.SmoothNbhd_add` and
`Work.FTS.CoercivityStep.Norm.HkMem_add.SmoothNbhd_add` are existing instances of this);
`HkMem` of the combination follows from the children `Work.FTS.Galerkin.Hilbert.HkMem_add` and
`Work.FTS.Galerkin.Hilbert.HkMem_const_mul` by induction over `Finset.range n`; the derivative
linearity `mixed b a (galFun φ c) = ∑ k, c k * mixed b a (φ k)` holds pointwise on the open
neighbourhood of the quadrant because each `φ k` is smooth there (from `hφ`), and `L₁₂`
(`= Work.FM.L12 Work.Spaces.K`) is additive over finite sums of functions with integrable angular
densities (`FM.L12_add`-style lemmas; the integrability follows from the `HkMem` clauses). -/
theorem galFun_adm {α : ℝ} {φ : ℕ → Work.FTS.Galerkin.Fn}
    (hφ : ∀ k : ℕ, Work.Coercivity.HkAdm α 4 (φ k)) (n : ℕ) (c : Fin n → ℝ) :
    Work.Coercivity.HkAdm α 4 (Work.FTS.Galerkin.galFun φ c) := by
  have hgal : Work.FTS.Galerkin.galFun φ c
      = fun z θ => ∑ k ∈ (Finset.univ : Finset (Fin n)), c k * φ (k : ℕ) z θ := by
    funext z θ
    rfl
  have hsm : ∀ k ∈ (Finset.univ : Finset (Fin n)), Work.Spaces.SmoothNbhd (φ (k : ℕ)) :=
    fun k _ => (hφ (k : ℕ)).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hgal]
    exact SmoothNbhd_finsetSum c (fun k : Fin n => φ (k : ℕ)) _ hsm
  · intro a b hab
    rw [hgal]
    have hGmem : Work.Spaces.HkMem α 4
        (fun z θ => ∑ k ∈ (Finset.univ : Finset (Fin n)),
          c k * Work.Spaces.mixed b a (φ (k : ℕ)) z θ) :=
      HkMem_finsetSum c (fun k : Fin n => Work.Spaces.mixed b a (φ (k : ℕ))) _
        (fun k _ => Work.Spaces.SmoothNbhd.DzIter
          (Work.Spaces.SmoothNbhd.DthIter (hsm k (Finset.mem_univ k)) a) b)
        (fun k _ => (hφ (k : ℕ)).2.1 a b hab)
    refine Work.Coercivity.HkMem_congr_Ioi α 4 hGmem (fun z hz θ hθ => ?_)
    exact (mixed_finsetSum c (fun k : Fin n => φ (k : ℕ)) b a _ hsm z θ
      (Work.Spaces.mem_nbhU (Work.FTS.CoercivityStep.Step.Iz_of_pos hz) hθ)).symm
  · intro a b hab
    rw [hgal]
    have hcongr := L12f_congr
      (u := Work.Spaces.mixed b a
        (fun z θ => ∑ k ∈ (Finset.univ : Finset (Fin n)), c k * φ (k : ℕ) z θ))
      (v := fun z θ => ∑ k ∈ (Finset.univ : Finset (Fin n)),
        c k * Work.Spaces.mixed b a (φ (k : ℕ)) z θ)
      (fun z θ hz hθ => mixed_finsetSum c (fun k : Fin n => φ (k : ℕ)) b a _ hsm z θ
        (Work.Spaces.mem_nbhU (Work.FTS.CoercivityStep.Step.Iz_of_pos hz) hθ))
    rw [hcongr]
    exact L12f_finsetSum_zero c (fun k : Fin n => Work.Spaces.mixed b a (φ (k : ℕ))) _
      (fun k _ => Work.Spaces.SmoothNbhd.DzIter
        (Work.Spaces.SmoothNbhd.DthIter (hsm k (Finset.mem_univ k)) a) b)
      (fun k _ => (hφ (k : ℕ)).2.1 a b hab)
      (fun k _ => (hφ (k : ℕ)).2.2 a b hab)

end Work.FTS.Galerkin.Hilbert

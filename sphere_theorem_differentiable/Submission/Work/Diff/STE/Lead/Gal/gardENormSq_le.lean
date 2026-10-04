import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.periodicIntegralLeCube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `gardENormSq_le`: the `Hᵏ` energy is controlled by the sup bound on a fundamental cube

`Work.Diff.STE.ENormSq m f` is the sum of the `L²` norms squared of *all* the `m`-th order iterated
partial derivatives `pdVec m l f`, integrated over the unit cube `(0,1]ⁿ`.  The point of this file is
that one only has to bound those derivatives **on the shifted cube** `(-1/2, 1/2]ⁿ` (which is the
cube on which the chart computations of the DeTurck/Gårding assembly produce bounds), provided the
function is `1`-periodic: periodicity transfers the bound to every point of `ℝⁿ`, and then the
integral over any fundamental domain is bounded by the supremum.

The result is the estimate

`ENormSq m f ≤ C * C0²`   for `m ≤ k`,  where `C = ((n:ℝ)+1)^k * (k+1)`,

whenever `‖pdVec m β f z‖ ≤ C0` for every `m ≤ k`, every direction multi-index `β`, and every
`z ∈ (-1/2, 1/2]ⁿ`.

The two ingredients, isolated as lemmas below:

* `periodic1_pd` (and `periodic1_pdVec`): the partial derivative `pd i f = x ↦ fderiv ℝ f x eᵢ` of a
  `1`-periodic function is again `1`-periodic.  Note that no differentiability is assumed: at a point
  where `f` is not differentiable the `fderiv` is the junk value `0`, and the set of
  differentiability points of a periodic function is invariant under translation (this is precisely
  the case distinction in the proof);
* `integral_normSq_le_of_bound`: if `‖g‖ ≤ C0` holds *everywhere*, then
  `∫_{(0,1]ⁿ} ‖g‖² ≤ C0²` (the volume of the unit cube is `1`).  The Bochner integral of a
  non-integrable function is the junk value `0`, which is where the harmless case distinction comes
  from.
-/

noncomputable section

open MeasureTheory

namespace Work.Diff.STE.Lead.Gal

/-- **The partial derivative of a `1`-periodic function is `1`-periodic.**

No differentiability assumption is needed: if `f` is not differentiable at `x` then neither is it at
`x + eⱼ` (the differentiability set of a periodic function is translation invariant), so both
`fderiv`s are the junk value `0`.  When `f` *is* differentiable at `x + eⱼ`, the chain rule applied
to the identity `f ∘ (· + eⱼ) = f` gives `fderiv ℝ f x = fderiv ℝ f (x + eⱼ)`. -/
lemma periodic1_pd {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (i : ι) : Work.Diff.STE.Periodic1 (Work.Diff.STE.pd i f) := by
  intro j x
  set c : ι → ℝ := Pi.single j (1:ℝ) with hc
  have hper : ∀ y : ι → ℝ, f (y + c) = f y := fun y => hf j y
  have hkey : fderiv ℝ f (x + c) = fderiv ℝ f x := by
    by_cases hd : DifferentiableAt ℝ f (x + c)
    · -- `f` is differentiable at `x + c`; differentiate `f ∘ (· + c) = f` at `x`
      have hcomp : (f ∘ (fun y : ι → ℝ => y + c)) = f := by
        funext y; exact hper y
      have h1 := fderiv_comp (𝕜 := ℝ) (x := x) (g := f) (f := fun y : ι → ℝ => y + c)
        hd (differentiableAt_id.add_const c)
      rw [hcomp] at h1
      have h2 : fderiv ℝ (fun y : ι → ℝ => y + c) x = ContinuousLinearMap.id ℝ (ι → ℝ) := by
        simpa using (fderiv_add_const (𝕜 := ℝ) (f := id) (x := x) c)
      rw [h2, ContinuousLinearMap.comp_id] at h1
      exact h1.symm
    · -- `f` is not differentiable at `x + c`: then it is not differentiable at `x` either
      have hper' : ∀ y : ι → ℝ, f (y + (-c)) = f y := by
        intro y
        have h := hper (y + (-c))
        rw [← h]; congr 1; abel
      have hdx : ¬ DifferentiableAt ℝ f x := by
        intro h
        apply hd
        have hcomp2 : (f ∘ (fun y : ι → ℝ => y + (-c))) = f := by
          funext y; exact hper' y
        have hx' : (x + c) + (-c) = x := by abel
        have hd' : DifferentiableAt ℝ f ((x + c) + (-c)) := by rw [hx']; exact h
        have h1 : DifferentiableAt ℝ (f ∘ (fun y : ι → ℝ => y + (-c))) (x + c) :=
          DifferentiableAt.comp (x + c) hd' (differentiableAt_id.add_const (-c))
        rwa [hcomp2] at h1
      rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hdx]
  show Work.Diff.STE.pd i f (x + c) = Work.Diff.STE.pd i f x
  simp only [Work.Diff.STE.pd]
  rw [hkey]

/-- Iterated partial derivatives of a `1`-periodic function are `1`-periodic. -/
lemma periodic1_pdVec {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (m : ℕ) (l : Fin m → ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pdVec m l f) := by
  have haux : ∀ (l' : List ι), Work.Diff.STE.Periodic1 (Work.Diff.STE.pdList l' f) := by
    intro l'
    induction l' with
    | nil => simpa [Work.Diff.STE.pdList] using hf
    | cons i l ih =>
        have hstep : Work.Diff.STE.pdList (i :: l) f
            = Work.Diff.STE.pd i (Work.Diff.STE.pdList l f) := rfl
        rw [hstep]
        exact periodic1_pd ih i
  exact haux (List.ofFn l)

/-- **A bound on the shifted cube is a global bound** for a `1`-periodic function: every point of
`ℝⁿ` is an integer translate of a point of `(-1/2, 1/2]ⁿ`, namely `z = b + m` with
`mᵢ = ⌈zᵢ - 1/2⌉` and `b = z - m`. -/
lemma bound_of_box {n : ℕ} {g : (Fin n → ℝ) → ℂ} (hg : Work.Diff.STE.Periodic1 g) {C0 : ℝ}
    (hb : ∀ z : Fin n → ℝ, (∀ i : Fin n, z i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) → ‖g z‖ ≤ C0) :
    ∀ z : Fin n → ℝ, ‖g z‖ ≤ C0 := by
  intro z
  set m : Fin n → ℤ := fun i => ⌈z i - (1 / 2 : ℝ)⌉ with hm
  have hb' : ∀ i : Fin n, z i - (m i : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro i
    constructor
    · have h1 : (m i : ℝ) < (z i - (1 / 2 : ℝ)) + 1 := Int.ceil_lt_add_one _
      linarith
    · have h1 : z i - (1 / 2 : ℝ) ≤ (m i : ℝ) := Int.le_ceil _
      linarith
  have hzz : z = (fun i => z i - (m i : ℝ)) + Work.Diff.STE.iVec m := by
    funext i; simp [Work.Diff.STE.iVec]
  rw [hzz, Work.Diff.STE.B3.periodic1_add_iVec hg _ m]
  exact hb _ hb'

/-- The `L²` norm squared over the unit cube of a function bounded by `C0` is at most `C0²`
(the unit cube has volume `1`). -/
lemma integral_normSq_le_of_bound {n : ℕ} {g : (Fin n → ℝ) → ℂ} {C0 : ℝ}
    (hb : ∀ z : Fin n → ℝ, ‖g z‖ ≤ C0) :
    ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖g z‖ ^ 2 ≤ C0 ^ 2 := by
  have hfin : volume (Work.Diff.STE.unitCube (ι := Fin n)) < ⊤ := by
    rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]; simp
  haveI : IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hfin⟩
  have hreal : (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))).real Set.univ = 1 := by
    rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
    simp
  by_cases hint : Integrable (fun z : Fin n → ℝ => ‖g z‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n)))
  · have hle : ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖g z‖ ^ 2 ≤
        ∫ _z in Work.Diff.STE.unitCube (ι := Fin n), C0 ^ 2 :=
      integral_mono hint (integrable_const _)
        (fun z => pow_le_pow_left₀ (norm_nonneg _) (hb z) 2)
    rw [integral_const, hreal, one_smul] at hle
    exact hle
  · rw [integral_undef hint]
    exact sq_nonneg C0

theorem gardENormSq_le {n : ℕ} (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : (Fin n → ℝ) → ℂ) (C0 : ℝ), 0 ≤ C0 →
        Work.Diff.STE.Periodic1 f →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ),
          (∀ i : Fin n, z i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) →
          ‖Work.Diff.STE.pdVec m β f z‖ ≤ C0) →
        ∀ m : ℕ, m ≤ k → Work.Diff.STE.ENormSq m f ≤ C * C0 ^ 2 := by
  refine ⟨((n : ℝ) + 1) ^ k * ((k : ℝ) + 1), by positivity, ?_⟩
  intro f C0 hC0 hper hb m hm
  have hstep : Work.Diff.STE.ENormSq m f ≤ ((n : ℝ) ^ m) * C0 ^ 2 := by
    have hterm : ∀ l : Fin m → Fin n,
        ∫ z in Work.Diff.STE.unitCube (ι := Fin n),
          ‖Work.Diff.STE.pdVec m l f z‖ ^ 2 ≤ C0 ^ 2 := by
      intro l
      exact integral_normSq_le_of_bound
        (bound_of_box (periodic1_pdVec hper m l) (fun z hz => hb m hm l z hz))
    rw [Work.Diff.STE.ENormSq]
    calc ∑ l : Fin m → Fin n,
          ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l f z‖ ^ 2
        ≤ ∑ _l : Fin m → Fin n, C0 ^ 2 := Finset.sum_le_sum (fun l _ => hterm l)
      _ = (Fintype.card (Fin m → Fin n) : ℝ) * C0 ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ((n : ℝ) ^ m) * C0 ^ 2 := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  refine le_trans hstep ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg C0)
  calc (n : ℝ) ^ m ≤ ((n : ℝ) + 1) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) m
    _ ≤ ((n : ℝ) + 1) ^ k := pow_le_pow_right₀ (by linarith) hm
    _ ≤ ((n : ℝ) + 1) ^ k * ((k : ℝ) + 1) :=
        le_mul_of_one_le_right (by positivity) (by linarith)

end Work.Diff.STE.Lead.Gal

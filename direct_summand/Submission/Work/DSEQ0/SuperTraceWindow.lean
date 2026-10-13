import Mathlib
import Submission.Work.DSEQ0.SuperTrace
import Submission.Work.DSMap.Mix2
import Submission.Work.DSEQ0.sum_Icc_shift_boundary

/-!
# `Work.DSEQ0`: the supertrace over a `ℤ`-indexed window, and its homotopy invariance

This file sets up the last analytic step of area `EQ0`'s input (4)
(`Work.DSEQ0.exists_modelFunctional`, `Submission/Work/DSEQ0/eq0_inputs.lean`): the functional
`φ₀ = superTrace (μ (ε 1, −))` produced by the trace argument on a *bounded* model `P` of the
Čech complex, and the computation of its value at the coaugmentation.

## Why a windowed supertrace

`Work.DSEQ0.superTrace` (`SuperTrace.lean`) is defined for a family indexed by `Fin (N + 1)`,
i.e. for a complex supported in degrees `0, …, N`.  The model of input (3) is *bounded but its
window need not contain `0`* — and it must not: if `H⁰(Č(U; 𝒪)) = Γ(X, ⊤)` has torsion, then no
model can vanish in negative degrees (`Work.DSEQ0.not_boundedModel_concl`,
`Submission/Work/DSEQ0/boundedModel_of_resolutions.lean`).  So the supertrace has to be summed
over a general window `[a, b] ⊆ ℤ`, with the signs `(-1)^i` given by the *actual* degree `i`.

## The statement, and the indexing convention

The two endomorphism families `α`, `β` of the model differ by a graded commutator
`[d, h] = d ∘ h + h ∘ d` (a homotopy `h`): for a cochain complex this reads, in degree `i + 1`,

  `α (i+1) - β (i+1) = d (i) ∘ h (i) + h (i+1) ∘ d (i+1)`,

with `h j : X (j+1) → X j`.  The relation is stated with `j + 1` as the **outer** index, and every
term is an endomorphism of the *same* type `↥(P.X (j+1))`: writing `P.X (i - 1 + 1)` instead of
`P.X i` does **not** give a definitionally equal type for a `ℤ`-indexed complex (integer
arithmetic is not definitional), so the `j + 1` form is the one that elaborates without transport.
The same convention has to be used when the future proof reindexes the sum `∑ i ∈ Icc a b` into
`∑ j ∈ Icc (a-1) (b-1)` (a `Finset` reindexing, not a `rfl`).

Boundedness enters because the telescoping sum leaves the boundary terms `tr (h b ∘ d b)` (over
`P.X (b+1) = 0`) and `tr (h (a-1) ∘ d (a-1))` (over `P.X (a-1) = 0`), which vanish exactly when
`P` is concentrated in the window `[a, b]` — the hypothesis `hbdd` below. -/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe a

/-- The alternating sign `(-1)^i` of an integer degree, as an element of `A`. -/
noncomputable def degreeSign (A : Type a) [Ring A] (i : ℤ) : A := if Even i then 1 else -1

/-- The supertrace of a family of endomorphisms of a finite free complex, summed over the window
`[a, b]`: `Σ_{i ∈ [a, b]} (-1)^i tr (α i)`. -/
noncomputable def superTraceWindow (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ)
    (α : ∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i)) : A :=
  ∑ i ∈ Finset.Icc a b, degreeSign A i * LinearMap.trace A ↥(P.X i) (α i)

/-- The Euler characteristic of the model over the window `[a, b]`:
`Σ_{i ∈ [a, b]} (-1)^i rk (P.X i)`.  For a bounded model it is independent of the window and
equals the Euler characteristic of the complex. -/
noncomputable def eulerCharWindow (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ) : A :=
  ∑ i ∈ Finset.Icc a b, degreeSign A i * (Module.finrank A ↥(P.X i) : A)

/-- **Homotopy invariance of the supertrace (windowed form).**

If two families of endomorphisms of a complex of finite free modules, concentrated in the window
`[a, b]`, differ by the graded commutator `[d, h]` of a homotopy `h`
(`α (j+1) - β (j+1) = d j ∘ h j + h (j+1) ∘ d (j+1)` for every `j`, with `h j : X (j+1) → X j`),
then their supertraces over the window agree.

This is the statement through which the trace argument of input (4) computes the value of
`φ₀ = superTrace (μ (ε 1, −))` on the coaugmentation: `μ (ε 1, −)` is homotopic to the identity
of the model (the product is unital up to homotopy), so `φ₀ (ε 1) = superTrace (id) =
eulerCharWindow`, which the generic-degree computation identifies with `χ = [K(X):K]`. -/
theorem superTraceWindow_eq_of_homotopy (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ)
    (hbdd : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (α β : ∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i))
    (h : ∀ j : ℤ, ↥(P.X (j + 1)) →ₗ[A] ↥(P.X j))
    (hαβ : ∀ j : ℤ, α (j + 1) - β (j + 1) =
      (P.d j (j + 1)).hom.comp (h j) + (h (j + 1)).comp ((P.d (j + 1) ((j + 1) + 1)).hom)) :
    superTraceWindow A P a b α = superTraceWindow A P a b β := by
  -- the sign relation `(-1)^{i+1} = -(-1)^i`
  have hsign : ∀ i : ℤ, degreeSign A (i + 1) = -degreeSign A i := by
    intro i
    rw [degreeSign, degreeSign]
    by_cases hE : Even i
    · have h2 : ¬ Even (i + 1) :=
        fun hc => (Int.not_even_iff_odd.mpr ((even_add_one).mp hc)) hE
      simp [hE, h2]
    · have h2 : Even (i + 1) := (even_add_one).mpr (Int.not_even_iff_odd.mp hE)
      simp [hE, h2]
  -- the two families: the traces of the differences, and of the homotopy composites
  let T : ℤ → A := fun i => LinearMap.trace A ↥(P.X i) (α i - β i)
  let U : ℤ → A := fun k => LinearMap.trace A ↥(P.X k) ((h k).comp ((P.d k (k + 1)).hom))
  -- the vanishing of the (shifted) supertrace of the differences
  have hmain : (∑ i ∈ Finset.Icc a b, degreeSign A i * T i) = 0 := by
    by_cases hab : a ≤ b
    · -- the homotopy relation, transported to the traces, with the sign change
      have hstep : ∀ j : ℤ, degreeSign A (j + 1) * T (j + 1)
          = -(degreeSign A j * U j) + degreeSign A (j + 1) * U (j + 1) := by
        intro j
        have hTU : T (j + 1) = U j + U (j + 1) := by
          show LinearMap.trace A ↥(P.X (j + 1)) (α (j + 1) - β (j + 1))
            = LinearMap.trace A ↥(P.X j) ((h j).comp ((P.d j (j + 1)).hom))
              + LinearMap.trace A ↥(P.X (j + 1))
                  ((h (j + 1)).comp ((P.d (j + 1) ((j + 1) + 1)).hom))
          rw [hαβ j, map_add]
          simp only [LinearMap.trace_comp_comm' (h j) ((P.d j (j + 1)).hom)]
        rw [hTU, mul_add, hsign j]
        ring
      -- shift the index of the sum
      have h1 := (Work.DSEQ0.sum_Icc_shift_boundary
        (fun i : ℤ => degreeSign A i * T i) (fun i : ℤ => degreeSign A i * U i) a b hab).1
      have h2 := (Work.DSEQ0.sum_Icc_shift_boundary
        (fun i : ℤ => degreeSign A i * T i) (fun i : ℤ => degreeSign A i * U i) a b hab).2
      have h3 := (Work.DSEQ0.sum_Icc_shift_boundary
        (fun i : ℤ => degreeSign A i * U i) (fun i : ℤ => 0) a b hab).1
      rw [h1, Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib,
        Finset.sum_neg_distrib, ← h3]
      -- the two boundary terms die because `P` is concentrated in the window
      have hUb : U b = 0 := by
        haveI : Subsingleton ↥(P.X (b + 1)) :=
          (ModuleCat.isZero_iff_subsingleton).mp (hbdd (b + 1) (Or.inr (by omega)))
        have hz : (h b) = 0 := by
          ext v
          rw [Subsingleton.elim v 0, map_zero, LinearMap.zero_apply]
        show LinearMap.trace A ↥(P.X b) ((h b).comp ((P.d b (b + 1)).hom)) = 0
        rw [hz, LinearMap.zero_comp, map_zero]
      have hUa : U (a - 1) = 0 := by
        haveI : Subsingleton ↥(P.X (a - 1)) :=
          (ModuleCat.isZero_iff_subsingleton).mp (hbdd (a - 1) (Or.inl (by omega)))
        show LinearMap.trace A ↥(P.X (a - 1))
          ((h (a - 1)).comp ((P.d (a - 1) (a - 1 + 1)).hom)) = 0
        have hz : ((h (a - 1)).comp ((P.d (a - 1) (a - 1 + 1)).hom)) = 0 := by
          ext v
          rw [Subsingleton.elim v 0]
          simp
        rw [hz, map_zero]
      have h2' : (∑ k ∈ Finset.Icc a b, degreeSign A k * U k)
          = (∑ k ∈ Finset.Icc (a - 1) (b - 1), degreeSign A k * U k)
            + degreeSign A b * U b - degreeSign A (a - 1) * U (a - 1) := by
        rw [eq_sub_iff_add_eq]
        exact h2
      rw [h2', hUb, mul_zero, hUa, mul_zero]
      ring
    · -- empty window: both sums are empty
      have hlt : b < a := lt_of_not_ge hab
      rw [Finset.Icc_eq_empty_iff.mpr (not_le.mpr hlt)]
      simp
  -- conclude by linearity of the trace
  apply sub_eq_zero.mp
  rw [superTraceWindow, superTraceWindow, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, ← map_sub]
  exact hmain

/-- **The supertrace of the identity family is the Euler characteristic.** -/
theorem superTraceWindow_one (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ) :
    superTraceWindow A P a b (fun _ => 1) = eulerCharWindow A P a b := by
  simp only [superTraceWindow, eulerCharWindow]
  exact Finset.sum_congr rfl fun i _ => by simp only [LinearMap.trace_one]

/-- **The value of the trace functional at the coaugmentation.**

Let `μ` be the family of endomorphisms "multiplication by the coaugmentation", i.e.
`μ = μ_Č (ε 1, −)` on the model `P` (each `μ i` an endomorphism of `P.X i`).  If `μ` is homotopic
to the identity of `P` — with homotopy `h`, `μ (j+1) - 1 = d j ∘ h j + h (j+1) ∘ d (j+1)` — then
the supertrace functional `superTraceWindow A P a b μ` takes at the coaugmentation the value
`eulerCharWindow A P a b`, the Euler characteristic of the model over its window.

This is the computation by which the trace argument of input (4)
(`Work.DSEQ0.exists_modelFunctional`) determines `χ`: the product is unital up to homotopy, so
the functional it produces has value the Euler characteristic; input (4)'s remaining content is
then only `χ ≠ 0`, i.e. the identification of this Euler characteristic with the generic degree. -/
theorem superTraceWindow_eq_eulerChar_of_homotopy (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ)
    (hbdd : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (μ : ∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i))
    (h : ∀ j : ℤ, ↥(P.X (j + 1)) →ₗ[A] ↥(P.X j))
    (hμ : ∀ j : ℤ, μ (j + 1) - 1 =
      (P.d j (j + 1)).hom.comp (h j) + (h (j + 1)).comp ((P.d (j + 1) ((j + 1) + 1)).hom)) :
    superTraceWindow A P a b μ = eulerCharWindow A P a b := by
  have hlemma := superTraceWindow_eq_of_homotopy A P a b hbdd μ (fun _ => 1) h hμ
  rwa [superTraceWindow_one] at hlemma

end Work.DSEQ0

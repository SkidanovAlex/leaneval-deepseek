import Mathlib
import Submission.Work.Diff.GE.frame_family_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gram–Schmidt family `frameFamily G t x s` is `G s`-orthonormal

This file proves `Work.Diff.GE.isONFrame_frameFamily`: if none of the pre-normalisation vectors
`frameU G t x s i` vanishes, then the Gram–Schmidt family `frameFamily G t x s` is orthonormal for
the metric `G s`.

The mathematical content is the classical Gram–Schmidt fact, and it is proved here in the abstract
form in which the recursion `Work.Diff.GE.gs` is set up: for a bilinear form `b` which is

* additive and `ℝ`-homogeneous in its **first** argument,
* symmetric,
* positive definite (`0 < b u u` for `u ≠ 0`),

the family `gs b κ` is `b`-orthonormal as soon as the pre-normalisation vectors `gsU b κ (gs b κ) i`
are all non-zero. (Note that the pre-normalisation vectors must also be assumed to be
`b`-orthogonal to the *earlier* vectors; this is the induction proved here, and it is exactly what
makes the normalisation meaningful — positivity of `b (U i) (U i)` alone would not give
orthogonality.)

The generic statement is `gs_orthonormal`; the three elementary helpers `bform_lin_sub`,
`bform_lin_sum`, `bform_normalize` supply the algebra of `b` used by the induction. The final
theorem `isONFrame_frameFamily` instantiates the generic statement with the bilinear form
`frameB G x s = (G s).inner x`, whose bilinearity, symmetry and positivity come from the
`RiemannianMetric`/`ContMDiffRiemannianMetric` structure on `G s`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.Diff.GE

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Subtraction in the **first** argument of a form which is additive and homogeneous in that
argument. -/
theorem bform_lin_sub (b : V → V → ℝ)
    (hadd : ∀ u v w : V, b (u + v) w = b u w + b v w)
    (hsmul : ∀ (c : ℝ) (u w : V), b (c • u) w = c * b u w)
    (u v w : V) : b (u - v) w = b u w - b v w := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h, hadd, hsmul]
  ring

/-- Linearity in the first argument, for a finite linear combination. -/
theorem bform_lin_sum (b : V → V → ℝ)
    (hadd : ∀ u v w : V, b (u + v) w = b u w + b v w)
    (hsmul : ∀ (c : ℝ) (u w : V), b (c • u) w = c * b u w)
    {ι : Type*} (E : ι → V) (c : ι → ℝ) (s : Finset ι) (w : V) :
    b (∑ j ∈ s, c j • E j) w = ∑ j ∈ s, c j * b (E j) w := by
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun u => b u w
      map_add' := fun u v => hadd u v w
      map_smul' := fun c u => hsmul c u w }
  have h : L (∑ j ∈ s, c j • E j) = ∑ j ∈ s, c j * b (E j) w := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  exact h

/-- **Normalising a non-zero vector.** If `b` is symmetric and positive definite, then the
normalised vector `(√(b u u))⁻¹ • u` has `b`-square `1`. -/
theorem bform_normalize (b : V → V → ℝ)
    (hadd : ∀ u v w : V, b (u + v) w = b u w + b v w)
    (hsmul : ∀ (c : ℝ) (u w : V), b (c • u) w = c * b u w)
    (hsymm : ∀ u v : V, b u v = b v u)
    (hpos : ∀ u : V, u ≠ 0 → 0 < b u u) (u : V) (hu : u ≠ 0) :
    b ((Real.sqrt (b u u))⁻¹ • u) ((Real.sqrt (b u u))⁻¹ • u) = 1 := by
  have ha : 0 < b u u := hpos u hu
  set c := (Real.sqrt (b u u))⁻¹ with hc
  have hcc : c * c * b u u = 1 := by
    have h1 : c * c = (b u u)⁻¹ := by
      rw [hc, ← mul_inv, ← pow_two, Real.sq_sqrt ha.le]
    rw [h1, inv_mul_cancel₀ (ne_of_gt ha)]
  calc b (c • u) (c • u) = c * b u (c • u) := hsmul c u (c • u)
    _ = c * b (c • u) u := by rw [hsymm u (c • u)]
    _ = c * (c * b u u) := by rw [hsmul c u u]
    _ = 1 := by rw [mul_assoc] at hcc; exact hcc

/-- **Gram–Schmidt orthonormality.** If the pre-normalisation vectors `gsU b κ (gs b κ) i` are all
non-zero, then `gs b κ` is `b`-orthonormal.

The proof is the usual Gram–Schmidt induction: writing `E i := gs b κ i` and
`U i := gsU b κ E i`, the (strong) induction hypothesis at `i` is

`(∀ l, l.val < i.val → b (E i) (E l) = 0) ∧ b (E i) (E i) = 1`,

i.e. the vectors of smaller index have already been dealt with. Since `E i = c_i • U i` with
`c_i = (√(b (U i) (U i)))⁻¹` and

`U i = κ i − ∑_{j < i} b (κ i) (E j) • E j`,

the induction hypothesis gives `b (U i) (E l) = b (κ i) (E l) − b (κ i) (E l) = 0` for `l < i`
(this is where the preceding orthonormality is used, in the form `b (E j) (E l) = δ_{jl}`), while
`b (E i) (E i) = c_i² b (U i) (U i) = 1` by `bform_normalize`. -/
theorem gs_orthonormal {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V)
    (hadd : ∀ u v w : V, b (u + v) w = b u w + b v w)
    (hsmul : ∀ (c : ℝ) (u w : V), b (c • u) w = c * b u w)
    (hsymm : ∀ u v : V, b u v = b v u)
    (hpos : ∀ u : V, u ≠ 0 → 0 < b u u)
    (hU : ∀ i : Fin n, gsU b κ (gs b κ) i ≠ 0) :
    ∀ i j : Fin n, b (gs b κ i) (gs b κ j) = if i = j then 1 else 0 := by
  have key' : ∀ m : ℕ, ∀ k : Fin n, k.val = m →
      (∀ l : Fin n, l.val < k.val → b (gs b κ k) (gs b κ l) = 0) ∧
      b (gs b κ k) (gs b κ k) = 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      -- the induction hypothesis in `δ` form, for all indices below `k`
      have hδ : ∀ i j : Fin n, i.val < k.val → j.val < k.val →
          b (gs b κ i) (gs b κ j) = if i = j then 1 else 0 := by
        intro i j hi hj
        rcases eq_or_ne i j with h | h
        · subst h; rw [if_pos rfl]; exact (ih i.val (by omega) i rfl).2
        · rw [if_neg h]
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · rw [hsymm, (ih j.val (by omega) j rfl).1 i hlt]
          · exact absurd (Fin.ext heq) h
          · exact (ih i.val (by omega) i rfl).1 j hgt
      refine ⟨?_, ?_⟩
      · -- orthogonality of `E k` with all earlier vectors
        intro l hl
        rw [gs_apply b κ k, hsmul]
        have hUl : b (gsU b κ (gs b κ) k) (gs b κ l) = 0 := by
          have hUsum : gsU b κ (gs b κ) k
              = κ k - ∑ j : Fin n,
                  (if j.val < k.val then b (κ k) (gs b κ j) • gs b κ j else 0) := rfl
          rw [hUsum, bform_lin_sub b hadd hsmul]
          -- turn the `if`-sum into a linear combination with coefficients `c j`
          have hsum_eq : (∑ j : Fin n,
                (if j.val < k.val then b (κ k) (gs b κ j) • gs b κ j else 0))
              = ∑ j : Fin n,
                  (fun i => if i.val < k.val then b (κ k) (gs b κ i) else 0) j •
                    gs b κ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases h : j.val < k.val <;> simp [h]
          rw [hsum_eq, bform_lin_sum b hadd hsmul]
          -- the sum collapses to the `j = l` term
          have hval : (∑ j : Fin n,
                (if j.val < k.val then b (κ k) (gs b κ j) else 0) *
                  b (gs b κ j) (gs b κ l))
              = b (κ k) (gs b κ l) := by
            rw [Finset.sum_eq_single l]
            · by_cases h : l.val < k.val
              · rw [if_pos h, hδ l l h hl, if_pos rfl, mul_one]
              · exact absurd hl h
            · intro j _ hjne
              by_cases hj : j.val < k.val
              · have hz : b (gs b κ j) (gs b κ l) = 0 := by
                  have hjl := hδ j l hj hl
                  rwa [if_neg hjne] at hjl
                rw [if_pos hj, hz, mul_zero]
              · rw [if_neg hj, zero_mul]
            · intro hmem
              exact absurd (Finset.mem_univ l) hmem
          rw [hval, sub_self]
        rw [hUl, mul_zero]
      · -- the diagonal entry
        rw [gs_apply b κ k]
        exact bform_normalize b hadd hsmul hsymm hpos _ (hU k)
  have key : ∀ i : Fin n,
      (∀ l : Fin n, l.val < i.val → b (gs b κ i) (gs b κ l) = 0) ∧
      b (gs b κ i) (gs b κ i) = 1 := fun i => key' i.val i rfl
  intro i j
  rcases eq_or_ne i j with h | h
  · subst h; rw [if_pos rfl]; exact (key i).2
  · rw [if_neg h]
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · rw [hsymm]; exact (key j).1 i hlt
    · exact absurd (Fin.ext heq) h
    · exact (key i).1 j hgt

end Generic

/-- If none of the pre-normalisation vectors `frameU G t x s i` vanishes, then the Gram–Schmidt
family `frameFamily G t x s` is `G s`-orthonormal. -/
theorem isONFrame_frameFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x : M) {s : ℝ}
    (hu : ∀ i, Work.Diff.GE.frameU G t x s i ≠ 0) :
    Submission.Diff.IsONFrame (G s) x (Work.Diff.GE.frameFamily G t x s) := by
  have hadd : ∀ u v w : TangentSpace I x,
      frameB G x s (u + v) w = frameB G x s u w + frameB G x s v w := by
    intro u v w
    show (G s).inner x (u + v) w = (G s).inner x u w + (G s).inner x v w
    rw [map_add, add_apply]
  have hsmul : ∀ (c : ℝ) (u w : TangentSpace I x),
      frameB G x s (c • u) w = c * frameB G x s u w := by
    intro c u w
    show (G s).inner x (c • u) w = c * (G s).inner x u w
    rw [map_smul, smul_apply, smul_eq_mul]
  have hsymm : ∀ u v : TangentSpace I x, frameB G x s u v = frameB G x s v u := by
    intro u v
    show (G s).inner x u v = (G s).inner x v u
    exact (G s).symm x u v
  have hpos : ∀ u : TangentSpace I x, u ≠ 0 → 0 < frameB G x s u u := by
    intro u hu0
    show 0 < (G s).inner x u u
    exact (G s).pos x u hu0
  exact gs_orthonormal (frameB G x s) (Submission.Diff.onFrame (G t) x)
    hadd hsmul hsymm hpos (fun i => hu i)

end Work.Diff.GE

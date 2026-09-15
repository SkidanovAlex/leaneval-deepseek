import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Conditional expectation of `f` with respect to the partition `part`,
evaluated at `x`: the average of `f` over the atom `part x`. -/
private noncomputable def cE {X : Type*} [Fintype X] (part : X → Finset X) (f : X → ℝ)
    (x : X) : ℝ :=
  ((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, f y

/-- `cE P f` is constant on each `Q`-atom when `Q` refines `P`. -/
private lemma cE_const_on_atom {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : X → Finset X) (hPeq : ∀ x y : X, y ∈ P x → P y = P x)
    (href : ∀ x, Q x ⊆ P x) (f : X → ℝ) {x z : X} (hz : z ∈ Q x) :
    cE P f z = cE P f x := by
  have hPz : P z = P x := hPeq x z (href x hz)
  simp only [cE, hPz]

/-- Over a `Q`-atom, `cE Q f` has the same total mass as `f`. -/
private lemma sum_cE_same {X : Type*} [Fintype X] [DecidableEq X]
    (Q : X → Finset X) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (f : X → ℝ) (y : X) :
    ∑ x ∈ Q y, cE Q f x = ∑ x ∈ Q y, f x := by
  have hconst : ∀ x ∈ Q y, cE Q f x = ((Q y).card : ℝ)⁻¹ * ∑ z ∈ Q y, f z := by
    intro x hx
    have hQx : Q x = Q y := hQeq y x hx
    simp only [cE, hQx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Q y).card ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨y, hQmem y⟩)
  have hne : ((Q y).card : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hcard
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- The residual `cE P f · (cE Q f - f)` sums to zero over any union `s` of `Q`-atoms. -/
private lemma sum_residual_eq_zero {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : X → Finset X) (hPeq : ∀ x y : X, y ∈ P x → P y = P x)
    (hQmem : ∀ x, x ∈ Q x) (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x)
    (href : ∀ x, Q x ⊆ P x) (f : X → ℝ) (s : Finset X) (hs : ∀ x ∈ s, Q x ⊆ s) :
    ∑ x ∈ s, cE P f x * (cE Q f x - f x) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image Q) (g := Q)
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (fun i => cE P f i * (cE Q f i - f i))]
  apply Finset.sum_eq_zero
  intro c hc
  rw [Finset.mem_image] at hc
  obtain ⟨y, hy, rfl⟩ := hc
  have hfilter : (s.filter (fun i => Q i = Q y)) = Q y := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hiQ⟩
      rw [← hiQ]
      exact hQmem i
    · intro hi
      exact ⟨hs y hy hi, hQeq y i hi⟩
  rw [hfilter]
  have hstep : ∑ i ∈ Q y, cE P f i * (cE Q f i - f i)
      = ∑ i ∈ Q y, cE P f y * (cE Q f i - f i) :=
    Finset.sum_congr rfl (fun i hi => by rw [cE_const_on_atom P Q hPeq href f hi])
  rw [hstep, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_cE_same Q hQmem hQeq f y,
    sub_self, mul_zero]

/-- Pulling the constant factor `C` out of the inner sum: the (maximal-parse) form
`c⁻¹ * ∑ y, f y * C` equals `cE P f x * C`. -/
private lemma sum_mul_const_eq {X : Type*} [Fintype X]
    (P : X → Finset X) (f : X → ℝ) (x : X) (C : ℝ) :
    ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y * C = cE P f x * C := by
  rw [← Finset.sum_mul, ← mul_assoc]
  rfl

/-- **Self-adjointness of the annulus weight.**

`P`, `Q` are finite σ-algebras on a finite type `X` presented by their atoms, with `Q` refining
`P`.  `Ω ⊆ Ω'`, `Ω` is a union of `P`-atoms and `Ω'` a union of `Q`-atoms.  Then, summing over
the annulus `Ω' \ Ω`, the pairing of `𝔼(f|P)` with `𝔼(f|Q) - 𝔼(f|P)` can be replaced by the
pairing with `f - 𝔼(f|P)` (self-adjointness of the conditional expectation onto `Q`). -/
theorem cE_annulus_selfadjoint {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : X → Finset X) (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω Ω' : Finset X} (hΩsub : Ω ⊆ Ω') (hΩ : ∀ x ∈ Ω, P x ⊆ Ω)
    (hΩ' : ∀ x ∈ Ω', Q x ⊆ Ω') (f : X → ℝ) :
    ∑ x ∈ Ω' \ Ω, ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y
        * (((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y)
      = ∑ x ∈ Ω' \ Ω, ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y
        * (f x - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y) := by
  -- `Ω' \ Ω` is a union of `Q`-atoms.
  have hs : ∀ x ∈ Ω' \ Ω, Q x ⊆ Ω' \ Ω := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxΩ', hxΩ⟩ := hx
    intro z hz
    rw [Finset.mem_sdiff]
    refine ⟨hΩ' x hxΩ' hz, ?_⟩
    intro hzΩ
    have hPxsub : P x ⊆ Ω := by
      rw [← hPeq x z (href x hz)]
      exact hΩ z hzΩ
    exact hxΩ (hPxsub (hPmem x))
  -- The two residual sums agree.
  have hzero := sum_residual_eq_zero P Q hPeq hQmem hQeq href f (Ω' \ Ω) hs
  have hLR : (∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x))
      = ∑ x ∈ Ω' \ Ω, cE P f x * (f x - cE P f x) := by
    have hdiff : (∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x))
        - (∑ x ∈ Ω' \ Ω, cE P f x * (f x - cE P f x)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      trans ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - f x)
      · apply Finset.sum_congr rfl
        intro x _
        ring
      · exact hzero
    exact sub_eq_zero.mp hdiff
  -- Rewrite each side of the goal into the `cE` form.
  have hL : (∑ x ∈ Ω' \ Ω, ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y
        * (((Q x).card : ℝ)⁻¹ * ∑ y ∈ Q x, f y - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y))
      = ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x) := by
    apply Finset.sum_congr rfl
    intro x _
    exact sum_mul_const_eq P f x (cE Q f x - cE P f x)
  have hR : (∑ x ∈ Ω' \ Ω, ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y
        * (f x - ((P x).card : ℝ)⁻¹ * ∑ y ∈ P x, f y))
      = ∑ x ∈ Ω' \ Ω, cE P f x * (f x - cE P f x) := by
    apply Finset.sum_congr rfl
    intro x _
    exact sum_mul_const_eq P f x (f x - cE P f x)
  exact hL.trans (hLR.trans hR.symm)

end Commons.Combinatorics.Transference
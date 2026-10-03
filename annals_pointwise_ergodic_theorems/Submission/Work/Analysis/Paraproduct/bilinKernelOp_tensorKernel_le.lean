/-
# `ttensor-bil`, upper bound: the tensor product of two bounded bilinear kernel operators

This file proves the upper-bound half of the paper's `ttensor-bil` identity in the concrete
finite-dimensional setting of `Submission.Work.Analysis.Paraproduct.TensorNorm`: if `K₁` is a
bilinear kernel whose associated operator `B₁` is bounded from `L^p × L^q` to `L^r` with constant
`C₁`, and `K₂` gives `B₂` bounded with constant `C₂`, then the tensor-product kernel
`tensorKernel K₁ K₂` gives an operator bounded with constant `C₁ C₂`.

The one structural hypothesis is that `K₁` is the cast of a **non-negative real** kernel
(`hK₁`).  This is exactly what makes the argument work: the sum over the first pair of variables
can be pulled outside the norm by Minkowski's inequality while keeping the numerical factor
`|K₁ z x y| = K₁ z x y` on the right side, so that the resulting expression is recognised as
`B₁` applied to the two vectors of slice norms.

Concretely, writing `Φ x = ‖F (x, ·)‖_{L^p}`, `Ψ y = ‖G (y, ·)‖_{L^q}`, the slicing identity
`bilinKernelOp_tensorKernel_apply` and Minkowski's inequality (`lpNormFin_sum_le`) give the
pointwise (in `z`) estimate

`‖B(F,G)(z,·)‖_{L^r(γ')} ≤ C₂ B₁(Φ,Ψ)(z)`,

and applying `h₁` to `Φ, Ψ` together with the slice identity `lpNormFin_slice` on the two tensor
factors finishes the proof.
-/
import Mathlib
import Submission.Work.Analysis.Paraproduct.lpNormFin_add_le
import Submission.Work.Analysis.Paraproduct.lpNormFin_slice

open scoped BigOperators
open Finset

namespace Work.Analysis.Paraproduct

noncomputable section

/-! ## Elementary facts about the normalised finite `L^p` norm -/

/-- `‖(r : ℂ)‖ = r` for a non-negative real number `r`. -/
private lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr]

/-- The `L^p` norm of the zero function vanishes. -/
private lemma lpNormFin_zero_fun {α : Type*} [Fintype α] {p : ℝ} (hp : p ≠ 0) :
    lpNormFin α p (fun _ : α => (0 : ℂ)) = 0 := by
  rw [lpNormFin]
  have h1 : (∑ a : α, ‖(0 : ℂ)‖ ^ p) = 0 := by simp [Real.zero_rpow hp]
  rw [h1, mul_zero]
  exact Real.zero_rpow (one_div_ne_zero hp)

/-- If the domain is empty then every `L^p` norm vanishes. -/
private lemma lpNormFin_eq_zero_of_isEmpty {α : Type*} [Fintype α] (h : IsEmpty α) {p : ℝ}
    (hp : p ≠ 0) (f : α → ℂ) : lpNormFin α p f = 0 := by
  rw [lpNormFin]
  have h1 : (∑ a : α, ‖f a‖ ^ p) = 0 := by
    rw [Finset.univ_eq_empty_iff.mpr h, Finset.sum_empty]
  rw [h1, mul_zero]
  exact Real.zero_rpow (one_div_ne_zero hp)

/-- The `L^p` norm of the constant function `1` on a nonempty finite type is `1`. -/
private lemma lpNormFin_one {α : Type*} [Fintype α] [Nonempty α] {p : ℝ} :
    lpNormFin α p (fun _ : α => (1 : ℂ)) = 1 := by
  rw [lpNormFin]
  have hsum : (∑ a : α, ‖(1 : ℂ)‖ ^ p) = (Fintype.card α : ℝ) := by
    simp only [norm_one, Real.one_rpow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
  rw [hsum]
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc, Real.one_rpow]

/-- **Minkowski's inequality for a finite family** of functions: for `1 ≤ p`,
`‖∑_i h_i‖_p ≤ ∑_i ‖h_i‖_p`.  Deduced from the two-term inequality `lpNormFin_add_le` by
induction on the finite index set. -/
private lemma lpNormFin_finset_sum_le {α ι : Type*} [Fintype α] [Fintype ι] {p : ℝ}
    (hp : 1 ≤ p) (h : ι → α → ℂ) :
    lpNormFin α p (fun a => ∑ i, h i a) ≤ ∑ i, lpNormFin α p (h i) := by
  classical
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have key : ∀ s : Finset ι,
      lpNormFin α p (fun a => ∑ i ∈ s, h i a) ≤ ∑ i ∈ s, lpNormFin α p (h i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hz : (fun a => ∑ i ∈ (∅ : Finset ι), h i a) = fun _ : α => (0 : ℂ) := by
          funext a; simp
        rw [hz, lpNormFin_zero_fun hp0]
        simp
    | insert i s hi ih =>
        have hsplit : (fun a => ∑ j ∈ insert i s, h j a)
            = (h i) + (fun a => ∑ j ∈ s, h j a) := by
          funext a
          simp only [Pi.add_apply, Finset.sum_insert hi]
        rw [hsplit, Finset.sum_insert hi]
        calc lpNormFin α p ((h i) + (fun a => ∑ j ∈ s, h j a))
            ≤ lpNormFin α p (h i) + lpNormFin α p (fun a => ∑ j ∈ s, h j a) :=
              lpNormFin_add_le hp _ _
          _ ≤ lpNormFin α p (h i) + ∑ j ∈ s, lpNormFin α p (h j) := add_le_add le_rfl ih
  exact key Finset.univ

/-- Monotonicity of the normalised `L^p` norm in the pointwise norm. -/
private lemma lpNormFin_mono {α : Type*} [Fintype α] {p : ℝ} (hp : 0 < p) {f g : α → ℂ}
    (h : ∀ a, ‖f a‖ ≤ ‖g a‖) : lpNormFin α p f ≤ lpNormFin α p g := by
  rw [lpNormFin, lpNormFin]
  refine Real.rpow_le_rpow ?_ ?_ (by positivity)
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _))
  · exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun a _ => Real.rpow_le_rpow (norm_nonneg _) (h a) hp.le))
      (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- When the kernel is the cast of a real-valued kernel, the bilinear kernel operator applied to
cast real-valued functions is the cast of the corresponding real double sum. -/
private lemma bilinKernelOp_ofReal {α β γ : Type*} [Fintype α] [Fintype β]
    {K : γ → α → β → ℂ} {K' : γ → α → β → ℝ}
    (hK : ∀ z x y, K z x y = (K' z x y : ℂ)) (φ : α → ℝ) (ψ : β → ℝ) (z : γ) :
    bilinKernelOp K (fun x => (φ x : ℂ)) (fun y => (ψ y : ℂ)) z
      = ((∑ x, ∑ y, K' z x y * φ x * ψ y : ℝ) : ℂ) := by
  rw [bilinKernelOp]
  have hinner : ∀ x, (∑ y, K z x y * (φ x : ℂ) * (ψ y : ℂ))
      = ((∑ y, K' z x y * φ x * ψ y : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hK z x y, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  exact (Complex.ofReal_sum Finset.univ (fun x => ∑ y, K' z x y * φ x * ψ y)).symm

/-! ## The main result -/

/-- **`ttensor-bil`, upper bound.**  A bilinear kernel operator bounded by `C₁` on the first
factor and one bounded by `C₂` on the second factor have a tensor product bounded by `C₁ C₂`,
provided the first kernel is the cast of a non-negative real kernel. -/
theorem bilinKernelOp_tensorKernel_le {α β γ α' β' γ' : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype γ']
    {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (K₁ : γ → α → β → ℂ) (K₂ : γ' → α' → β' → ℂ)
    (hK₁ : ∃ K₁' : γ → α → β → ℝ, (∀ z x y, 0 ≤ K₁' z x y) ∧
      ∀ z x y, K₁ z x y = (K₁' z x y : ℂ))
    {C₁ C₂ : ℝ}
    (h₁ : ∀ f g, lpNormFin γ r (bilinKernelOp K₁ f g)
      ≤ C₁ * lpNormFin α p f * lpNormFin β q g)
    (h₂ : ∀ f g, lpNormFin γ' r (bilinKernelOp K₂ f g)
      ≤ C₂ * lpNormFin α' p f * lpNormFin β' q g) :
    ∀ F G, lpNormFin (γ × γ') r (bilinKernelOp (tensorKernel K₁ K₂) F G)
      ≤ C₁ * C₂ * lpNormFin (α × α') p F * lpNormFin (β × β') q G := by
  obtain ⟨K₁', hK₁'nn, hK₁'eq⟩ := hK₁
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  intro F G
  rcases isEmpty_or_nonempty α' with hα' | hα'
  · -- degenerate case: `α'` empty
    have hprod : IsEmpty (α × α') := ⟨fun p => hα'.false p.2⟩
    have hL : lpNormFin (γ × γ') r (bilinKernelOp (tensorKernel K₁ K₂) F G) = 0 := by
      have hzero : bilinKernelOp (tensorKernel K₁ K₂) F G = fun _ => (0 : ℂ) := by
        funext z
        simp only [bilinKernelOp]
        rw [Finset.univ_eq_empty_iff.mpr hprod]
        simp
      rw [hzero, lpNormFin_zero_fun (ne_of_gt hr0)]
    have hF : lpNormFin (α × α') p F = 0 :=
      lpNormFin_eq_zero_of_isEmpty hprod (ne_of_gt hp0) F
    rw [hL, hF]
    simp
  rcases isEmpty_or_nonempty β' with hβ' | hβ'
  · -- degenerate case: `β'` empty
    have hprod : IsEmpty (β × β') := ⟨fun p => hβ'.false p.2⟩
    have hL : lpNormFin (γ × γ') r (bilinKernelOp (tensorKernel K₁ K₂) F G) = 0 := by
      have hzero : bilinKernelOp (tensorKernel K₁ K₂) F G = fun _ => (0 : ℂ) := by
        funext z
        simp only [bilinKernelOp]
        rw [Finset.univ_eq_empty_iff.mpr hprod]
        simp
      rw [hzero, lpNormFin_zero_fun (ne_of_gt hr0)]
    have hG : lpNormFin (β × β') q G = 0 :=
      lpNormFin_eq_zero_of_isEmpty hprod (ne_of_gt hq0) G
    rw [hL, hG]
    simp
  · -- main case: `α'` and `β'` are both nonempty
    have hC₂ : 0 ≤ C₂ := by
      have k := h₂ (fun _ : α' => (1 : ℂ)) (fun _ : β' => (1 : ℂ))
      have h1 : lpNormFin α' p (fun _ : α' => (1 : ℂ)) = 1 := lpNormFin_one
      have h2 : lpNormFin β' q (fun _ : β' => (1 : ℂ)) = 1 := lpNormFin_one
      simp only [h1, h2, mul_one] at k
      linarith [lpNormFin_nonneg r (bilinKernelOp K₂ (fun _ : α' => (1 : ℂ))
        (fun _ : β' => (1 : ℂ)))]
    let φ : α → ℝ := fun x => lpNormFin α' p (slice F x)
    let ψ : β → ℝ := fun y => lpNormFin β' q (slice G y)
    -- the pointwise (in `z`) estimate obtained from Minkowski and `h₂`
    have hpoint : ∀ z, lpNormFin γ' r (fun z' => bilinKernelOp (tensorKernel K₁ K₂) F G (z, z'))
        ≤ C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) := by
      intro z
      have hkey : (fun z' => bilinKernelOp (tensorKernel K₁ K₂) F G (z, z'))
          = fun z' => ∑ i : α × β, K₁ z i.1 i.2 *
              bilinKernelOp K₂ (slice F i.1) (slice G i.2) z' := by
        funext z'
        rw [bilinKernelOp_tensorKernel_apply]
        exact (Fintype.sum_prod_type (fun i : α × β => K₁ z i.1 i.2 *
          bilinKernelOp K₂ (slice F i.1) (slice G i.2) z')).symm
      rw [hkey]
      calc lpNormFin γ' r (fun z' => ∑ i : α × β, K₁ z i.1 i.2 *
              bilinKernelOp K₂ (slice F i.1) (slice G i.2) z')
          ≤ ∑ i : α × β, lpNormFin γ' r (fun z' => K₁ z i.1 i.2 *
              bilinKernelOp K₂ (slice F i.1) (slice G i.2) z') :=
            lpNormFin_finset_sum_le hr _
        _ = ∑ i : α × β, K₁' z i.1 i.2 *
              lpNormFin γ' r (bilinKernelOp K₂ (slice F i.1) (slice G i.2)) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [lpNormFin_const_mul hr0, hK₁'eq z i.1 i.2,
              norm_ofReal_of_nonneg (hK₁'nn z i.1 i.2)]
        _ ≤ ∑ i : α × β, K₁' z i.1 i.2 * (C₂ * φ i.1 * ψ i.2) := by
            refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_
              (hK₁'nn z i.1 i.2))
            exact h₂ (slice F i.1) (slice G i.2)
        _ = C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) := by
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            ring
    have hb0 : ∀ z, 0 ≤ C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) := by
      intro z
      refine mul_nonneg hC₂ (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ?_)))
      exact mul_nonneg (mul_nonneg (hK₁'nn z x y) (lpNormFin_nonneg _ _))
        (lpNormFin_nonneg _ _)
    have hmono : lpNormFin γ r (fun z => ((lpNormFin γ' r
          (fun z' => bilinKernelOp (tensorKernel K₁ K₂) F G (z, z')) : ℝ) : ℂ))
        ≤ lpNormFin γ r (fun z => ((C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ)) := by
      refine lpNormFin_mono hr0 (fun z => ?_)
      rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (lpNormFin_nonneg _ _),
        Real.norm_of_nonneg (hb0 z)]
      exact hpoint z
    have hconst : lpNormFin γ r (fun z => ((C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ))
        = C₂ * lpNormFin γ r
            (fun z => (((∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ)) := by
      rw [show (fun z => ((C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ))
          = (fun z => (C₂ : ℂ) *
              (((∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ)) from by
            funext z; rw [Complex.ofReal_mul]]
      rw [lpNormFin_const_mul hr0, Complex.norm_real, Real.norm_of_nonneg hC₂]
    have hbop : (fun z => (((∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ))
        = bilinKernelOp K₁ (fun x => ((φ x : ℝ) : ℂ)) (fun y => ((ψ y : ℝ) : ℂ)) := by
      funext z
      exact (bilinKernelOp_ofReal hK₁'eq φ ψ z).symm
    have h₁app := h₁ (fun x => ((φ x : ℝ) : ℂ)) (fun y => ((ψ y : ℝ) : ℂ))
    have hΦ : lpNormFin α p (fun x => ((φ x : ℝ) : ℂ)) = lpNormFin (α × α') p F :=
      lpNormFin_slice hp0 F
    have hΨ : lpNormFin β q (fun y => ((ψ y : ℝ) : ℂ)) = lpNormFin (β × β') q G :=
      lpNormFin_slice hq0 G
    calc lpNormFin (γ × γ') r (bilinKernelOp (tensorKernel K₁ K₂) F G)
        = lpNormFin γ r (fun z => ((lpNormFin γ' r
            (fun z' => bilinKernelOp (tensorKernel K₁ K₂) F G (z, z')) : ℝ) : ℂ)) :=
          (lpNormFin_slice hr0 (bilinKernelOp (tensorKernel K₁ K₂) F G)).symm
      _ ≤ lpNormFin γ r (fun z => ((C₂ * (∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ)) :=
          hmono
      _ = C₂ * lpNormFin γ r
            (fun z => (((∑ x, ∑ y, K₁' z x y * φ x * ψ y) : ℝ) : ℂ)) := hconst
      _ = C₂ * lpNormFin γ r
            (bilinKernelOp K₁ (fun x => ((φ x : ℝ) : ℂ)) (fun y => ((ψ y : ℝ) : ℂ))) := by
          rw [hbop]
      _ ≤ C₂ * (C₁ * lpNormFin α p (fun x => ((φ x : ℝ) : ℂ))
            * lpNormFin β q (fun y => ((ψ y : ℝ) : ℂ))) :=
          mul_le_mul_of_nonneg_left h₁app hC₂
      _ = C₂ * (C₁ * lpNormFin (α × α') p F * lpNormFin (β × β') q G) := by rw [hΦ, hΨ]
      _ = C₁ * C₂ * lpNormFin (α × α') p F * lpNormFin (β × β') q G := by ring

end

end Work.Analysis.Paraproduct

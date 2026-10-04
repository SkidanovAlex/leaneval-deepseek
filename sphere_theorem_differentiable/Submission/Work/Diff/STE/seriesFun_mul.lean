import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-!
# Multiplicativity of `seriesFun`

`seriesFun c x = ∑' k, c k * fourierExp k x` is the function on the torus whose Fourier
coefficients are `c`, and `conv c d` is the coefficient convolution.  The pointwise product
of `seriesFun c` and `seriesFun d` corresponds to the convolution of the coefficient families:

  `seriesFun c x * seriesFun d x = seriesFun (conv c d) x`.

The proof is the standard one.  Since `∑ ‖c k‖` and `∑ ‖d k‖` are finite and the characters
have modulus one, the product of the two series is the (absolutely convergent) double sum over
`(l, m) ↦ c l · E l x · d m · E m x`; using multiplicativity of the characters this is
`(l, m) ↦ c l · d m · E (l + m) x`, and reindexing by the bijection `(l, m) ↦ (l, l + m)`
turns it into `∑_k (∑_l c l · d (k - l)) · E k x`, which is `seriesFun (conv c d) x`.

We isolate the three elementary facts about the characters that are needed:
`fourierExp_add`, `fourierExp_eq_prod`, `norm_fourierExp`.
-/

private lemma fourierExp_add' {ι : Type*} [Fintype ι]
    (k l : ι → ℤ) (x : ι → ℝ) :
    fourierExp k x * fourierExp l x = fourierExp (k + l) x := by
  simp only [fourierExp]
  rw [← Complex.exp_add]
  congr 1
  have hsum : (∑ i, ((k + l) i : ℂ) * (x i : ℂ))
      = (∑ i, (k i : ℂ) * (x i : ℂ)) + (∑ i, (l i : ℂ) * (x i : ℂ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h : ((k + l) i : ℂ) = (k i : ℂ) + (l i : ℂ) := by simp
    rw [h, add_mul]
  rw [hsum]
  ring

private lemma fourierExp_eq_prod' {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (x : ι → ℝ) :
    fourierExp k x
      = ∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k i : ℂ) * (x i : ℂ))) := by
  simp only [fourierExp]
  rw [Finset.mul_sum, Complex.exp_sum]

private lemma norm_fourierExp' {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (x : ι → ℝ) : ‖fourierExp k x‖ = 1 := by
  have hfac : ∀ i, ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k i : ℂ) * (x i : ℂ)))‖
      = 1 := by
    intro i
    have h : 2 * (Real.pi : ℂ) * Complex.I * ((k i : ℂ) * (x i : ℂ))
        = (↑(2 * Real.pi * (k i : ℝ) * (x i)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  rw [fourierExp_eq_prod', norm_prod]
  simp [hfac]

theorem seriesFun_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => ‖c k‖)) (hd : Summable (fun k : ι → ℤ => ‖d k‖)) :
    ∀ x : ι → ℝ,
      Work.Diff.STE.seriesFun c x * Work.Diff.STE.seriesFun d x
        = Work.Diff.STE.seriesFun (Work.Diff.STE.conv c d) x := by
  intro x
  -- Both series are absolutely summable, because the characters have modulus one.
  have hF : Summable (fun k : ι → ℤ => c k * fourierExp k x) := by
    apply Summable.of_norm
    exact hc.congr (fun k => by rw [norm_mul, norm_fourierExp', mul_one])
  have hG : Summable (fun k : ι → ℤ => d k * fourierExp k x) := by
    apply Summable.of_norm
    exact hd.congr (fun k => by rw [norm_mul, norm_fourierExp', mul_one])
  have hFG : Summable (fun p : (ι → ℤ) × (ι → ℤ) =>
      (c p.1 * fourierExp p.1 x) * (d p.2 * fourierExp p.2 x)) := by
    apply Summable.of_norm
    refine (Summable.mul_of_nonneg hc hd (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
      (fun p => ?_)
    simp only [norm_mul, norm_fourierExp', mul_one]
  -- Multiplicativity of the characters identifies the double sum with the convolution.
  have hkey : ∀ p : (ι → ℤ) × (ι → ℤ),
      (c p.1 * fourierExp p.1 x) * (d p.2 * fourierExp p.2 x)
        = (c p.1 * d p.2) * fourierExp (p.1 + p.2) x := by
    intro p
    rw [show (c p.1 * fourierExp p.1 x) * (d p.2 * fourierExp p.2 x)
        = c p.1 * d p.2 * (fourierExp p.1 x * fourierExp p.2 x) by ring]
    rw [fourierExp_add']
  have step1 : (∑' k : ι → ℤ, c k * fourierExp k x) * (∑' k : ι → ℤ, d k * fourierExp k x)
      = ∑' p : (ι → ℤ) × (ι → ℤ),
          (c p.1 * fourierExp p.1 x) * (d p.2 * fourierExp p.2 x) :=
    Summable.tsum_mul_tsum hF hG hFG
  have step2 : (∑' p : (ι → ℤ) × (ι → ℤ),
          (c p.1 * fourierExp p.1 x) * (d p.2 * fourierExp p.2 x))
      = ∑' p : (ι → ℤ) × (ι → ℤ), (c p.1 * d p.2) * fourierExp (p.1 + p.2) x :=
    tsum_congr hkey
  have hfp : Summable (fun p : (ι → ℤ) × (ι → ℤ) =>
      (c p.1 * d p.2) * fourierExp (p.1 + p.2) x) :=
    hFG.congr hkey
  -- Reindex `(l, m) ↦ (l, l + m)`, i.e. `k = l + m`.
  let e : (ι → ℤ) × (ι → ℤ) ≃ (ι → ℤ) × (ι → ℤ) :=
    { toFun := fun p => (p.1 + p.2, p.1)
      invFun := fun q => (q.2, q.1 - q.2)
      left_inv := by rintro ⟨a, b⟩; simp
      right_inv := by rintro ⟨a, b⟩; simp }
  have hfq : Summable (fun q : (ι → ℤ) × (ι → ℤ) =>
      (c q.2 * d (q.1 - q.2)) * fourierExp q.1 x) :=
    (Equiv.summable_iff e).1 (by simpa [Function.comp_def, e] using hfp)
  have step3 : (∑' p : (ι → ℤ) × (ι → ℤ), (c p.1 * d p.2) * fourierExp (p.1 + p.2) x)
      = ∑' q : (ι → ℤ) × (ι → ℤ), (c q.2 * d (q.1 - q.2)) * fourierExp q.1 x := by
    have h := Equiv.tsum_eq e (fun q : (ι → ℤ) × (ι → ℤ) =>
      (c q.2 * d (q.1 - q.2)) * fourierExp q.1 x)
    simpa [e] using h
  -- Split the (absolutely convergent) double sum and factor out the character.
  have step4 : (∑' q : (ι → ℤ) × (ι → ℤ), (c q.2 * d (q.1 - q.2)) * fourierExp q.1 x)
      = ∑' k : ι → ℤ, ∑' l : ι → ℤ, (c l * d (k - l)) * fourierExp k x :=
    Summable.tsum_prod hfq
  have step5 : (∑' k : ι → ℤ, ∑' l : ι → ℤ, (c l * d (k - l)) * fourierExp k x)
      = ∑' k : ι → ℤ, (∑' l : ι → ℤ, c l * d (k - l)) * fourierExp k x := by
    apply tsum_congr
    intro k
    exact tsum_mul_right
  calc seriesFun c x * seriesFun d x
      = (∑' k : ι → ℤ, c k * fourierExp k x) * (∑' k : ι → ℤ, d k * fourierExp k x) := rfl
    _ = ∑' p : (ι → ℤ) × (ι → ℤ),
          (c p.1 * fourierExp p.1 x) * (d p.2 * fourierExp p.2 x) := step1
    _ = ∑' p : (ι → ℤ) × (ι → ℤ), (c p.1 * d p.2) * fourierExp (p.1 + p.2) x := step2
    _ = ∑' q : (ι → ℤ) × (ι → ℤ), (c q.2 * d (q.1 - q.2)) * fourierExp q.1 x := step3
    _ = ∑' k : ι → ℤ, ∑' l : ι → ℤ, (c l * d (k - l)) * fourierExp k x := step4
    _ = ∑' k : ι → ℤ, (∑' l : ι → ℤ, c l * d (k - l)) * fourierExp k x := step5
    _ = seriesFun (conv c d) x := rfl

end Work.Diff.STE

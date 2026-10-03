/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).
-/
import Submission.Work.OROneRel.CoprodNormalForm
import Submission.Work.OROneRel.coprod_isOfFinOrder_conj

/-!
# Torsion in a free product, after Kurosh

`coprod_isOfFinOrder_conj` (Kurosh's theorem) says that an element of finite order in `M ∗ N` is
conjugate into one of the factors.  Here we draw the corollary used for one-relator groups: a free
product of torsion-free groups has no nontrivial torsion.  Applied to the terminal one-relator group
`⟨α | x ^ m⟩ ≃ F(α \ {x}) ∗ ℤ/|m|`, this is the statement that all torsion lives in the cyclic
factor.
-/

namespace Work.OROneRel

universe u

variable {M N : Type u} [Group M] [Group N]

/-- Conjugation preserves the finiteness of the order. -/
theorem isOfFinOrder_mul_conj_iff (h x : Monoid.Coprod M N) :
    IsOfFinOrder (h * x * h⁻¹) ↔ IsOfFinOrder x := by
  have hconj : ∀ n : ℕ, (h * x * h⁻¹) ^ n = h * x ^ n * h⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, ih]; group
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, hpow⟩
    refine ⟨n, hn, ?_⟩
    have h2 : h * x ^ n * h⁻¹ = 1 := by rw [← hconj n]; exact hpow
    have h3 := congrArg (fun y => h⁻¹ * y * h) h2
    simpa [mul_assoc] using h3
  · rintro ⟨n, hn, hpow⟩
    exact ⟨n, hn, by rw [hconj n, hpow]; group⟩

/-- `IsOfFinOrder` is unchanged by `Monoid.Coprod.inl`. -/
theorem isOfFinOrder_inl_iff (a : M) :
    IsOfFinOrder (Monoid.Coprod.inl a : Monoid.Coprod M N) ↔ IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, hpow⟩
    exact ⟨n, hn, Monoid.Coprod.inl_injective (by simpa [map_pow] using hpow)⟩
  · rintro ⟨n, hn, hpow⟩
    exact ⟨n, hn, by rw [← map_pow, hpow, map_one]⟩

/-- `IsOfFinOrder` is unchanged by `Monoid.Coprod.inr`. -/
theorem isOfFinOrder_inr_iff (b : N) :
    IsOfFinOrder (Monoid.Coprod.inr b : Monoid.Coprod M N) ↔ IsOfFinOrder b := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, hpow⟩
    exact ⟨n, hn, Monoid.Coprod.inr_injective (by simpa [map_pow] using hpow)⟩
  · rintro ⟨n, hn, hpow⟩
    exact ⟨n, hn, by rw [← map_pow, hpow, map_one]⟩

/-- **A free product of torsion-free groups is torsion-free.**  (Kurosh's theorem: a finite-order
element is conjugate into a factor.) -/
theorem coprod_eq_one_of_isOfFinOrder (hM : ∀ m : M, IsOfFinOrder m → m = 1)
    (hN : ∀ n : N, IsOfFinOrder n → n = 1) {g : Monoid.Coprod M N} (hg : IsOfFinOrder g) :
    g = 1 := by
  rcases coprod_isOfFinOrder_conj hg with ⟨h, a, ha⟩ | ⟨h, b, hb⟩
  · have ha' : IsOfFinOrder a := (isOfFinOrder_inl_iff a).mp ((isOfFinOrder_mul_conj_iff h _).mp (ha ▸ hg))
    rw [ha, hM a ha', map_one, mul_one, mul_inv_cancel]
  · have hb' : IsOfFinOrder b := (isOfFinOrder_inr_iff b).mp ((isOfFinOrder_mul_conj_iff h _).mp (hb ▸ hg))
    rw [hb, hN b hb', map_one, mul_one, mul_inv_cancel]

end Work.OROneRel

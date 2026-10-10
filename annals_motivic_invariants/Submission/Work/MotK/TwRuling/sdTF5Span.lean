import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.productSpan_eq
import Submission.Work.MotK.TwRuling.sdTF5SpanDefs
import Submission.Work.MotK.TwRuling.monomial_mem_sdTF5

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fivefold products of `sdBas` span `L(25·O)`

Let `R` be a field, `E` a Weierstrass curve over `R`, `x = genX E`, `y = genY E` in the function
field `Om = E.FunctionField`, and

* `sdBas E = ![1, x, y, x², xy]` — the basis of `L(5·O)`,
* `sdTF5 E` — the 25 monomials `x^i` (`i < 13`) and `x^j y` (`j < 12`) of `L(25·O)`.

The main result `sdTF5Span` says that the `R`-span of the 25 fivefold products `b₁···b₅`
(`bᵢ ∈ sdBas E`) coincides with the `R`-span of `sdTF5 E`.  This is the fivefold analogue of
`Work.MotK.TwRuling.productSpan_eq` (the statement `L(5·O)·L(5·O) = L(10·O)`).

The two inclusions are proved separately.

* `Tsp ≤ Ssp`: every fivefold product is a monomial `x^a y^b` of weight `2a+3b ≤ 25`
  (`prod_sdBas_eq_monomial`), and every monomial of weight `≤ 25` lies in `Ssp`
  (`monomial_mem_sdTF5`, strong induction on `b` via the Weierstrass relation).
* `Ssp ≤ Tsp`: the monomials `x^i` (`i ≤ 12`) and `x^j y` (`j ≤ 11`) are exhibited as products
  of at most five elements of `L(5·O)` (in fact of `L(15·O) · L(10·O)` etc.), using the
  multiplicativity `Q a · Q b ≤ Q (a+b)` of the spans `Q n` of the `n`-fold products.  The four
  "top" monomials `x¹¹`, `x¹²`, `x¹⁰y`, `x¹¹y` use `x⁵ ∈ Q 2`, i.e. the fact `L(5·O)·L(5·O) =
  L(10·O)` (`productSpan_eq`), which supplies `x⁵ = (x²)²y² + a₁x³y + a₃x²y − a₂x⁴ − a₄x³ − a₆x²`.
-/

set_option maxHeartbeats 800000

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling.Five

noncomputable section

variable {R : Type} [Field R]

/-! ## §0 The exponent pair of a basis element -/

/-- The `x`-exponent of the basis element `sdBas E k`. -/
def eX : Fin 5 → ℕ := ![0, 1, 0, 2, 1]

/-- The `y`-exponent of the basis element `sdBas E k`. -/
def eY : Fin 5 → ℕ := ![0, 0, 1, 0, 1]

/-- Each basis element is the monomial `x^{eX k} · y^{eY k}`. -/
theorem sdBas_eq_monomial (E : WeierstrassCurve R) (k : Fin 5) :
    sdBas E k = (Work.MotV.genX E) ^ (eX k) * (Work.MotV.genY E) ^ (eY k) := by
  fin_cases k <;> simp [eX, eY]

/-- The pole weight `2·eX k + 3·eY k` of `sdBas E k` is at most `5`. -/
theorem weight_bound (k : Fin 5) : 2 * eX k + 3 * eY k ≤ 5 := by
  fin_cases k <;> simp [eX, eY]

/-- **Every fivefold product of basis elements is a monomial of weight `≤ 25`.** -/
theorem prod_sdBas_eq_monomial (E : WeierstrassCurve R) (f : Fin 5 → Fin 5) :
    ∃ a b : ℕ, 2 * a + 3 * b ≤ 25 ∧
      (∏ i : Fin 5, sdBas E (f i))
        = (Work.MotV.genX E) ^ a * (Work.MotV.genY E) ^ b := by
  refine ⟨∑ i : Fin 5, eX (f i), ∑ i : Fin 5, eY (f i), ⟨?_, ?_⟩⟩
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc ∑ i : Fin 5, (2 * eX (f i) + 3 * eY (f i)) ≤ ∑ _i : Fin 5, 5 :=
          Finset.sum_le_sum fun i _ => weight_bound (f i)
      _ = 25 := by decide
  · calc (∏ i : Fin 5, sdBas E (f i))
        = ∏ i : Fin 5, ((Work.MotV.genX E) ^ eX (f i) * (Work.MotV.genY E) ^ eY (f i)) :=
          Finset.prod_congr rfl fun i _ => sdBas_eq_monomial E (f i)
      _ = (∏ i : Fin 5, (Work.MotV.genX E) ^ eX (f i))
            * (∏ i : Fin 5, (Work.MotV.genY E) ^ eY (f i)) := by
          rw [Finset.prod_mul_distrib]
      _ = (Work.MotV.genX E) ^ (∑ i : Fin 5, eX (f i))
            * (Work.MotV.genY E) ^ (∑ i : Fin 5, eY (f i)) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

/-! ## §1 The spans `Q n` of the `n`-fold products -/

/-- **Multiplicativity of the spans of `n`-fold products.**  A product of an `a`-fold product and
a `b`-fold product of elements of `sdBas E` is an `(a+b)`-fold product. -/
theorem Q_mul_le (E : WeierstrassCurve R) (a b : ℕ) : Q E a * Q E b ≤ Q E (a + b) := by
  rw [Q, Q, Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro z ⟨u, ⟨q, rfl⟩, v, ⟨q', rfl⟩, rfl⟩
  refine ⟨Fin.append q q', ?_⟩
  show (∏ i : Fin (a + b), sdBas E (Fin.append q q' i))
    = (∏ i, sdBas E (q i)) * ∏ i, sdBas E (q' i)
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- `Q 1` is the span of the basis `sdBas E`. -/
theorem Q_one_eq (E : WeierstrassCurve R) : Q E 1 = Submodule.span R (Set.range (sdBas E)) := by
  unfold Q
  congr 1
  ext z; constructor
  · rintro ⟨q, rfl⟩
    simp only [Fin.prod_univ_one]
    exact ⟨q 0, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨fun _ => k, by simp only [Fin.prod_univ_one]⟩

/-- `Q 2 = span(sdTen E)`, the statement `L(5·O)·L(5·O) = L(10·O)` (`productSpan_eq`). -/
theorem Q_two_eq (E : WeierstrassCurve R) :
    Q E 2 = Submodule.span R (Set.range (sdTen E)) := by
  unfold Q
  have hfun : (fun q : Fin 2 → Fin 5 => ∏ i, sdBas E (q i))
      = (fun q : Fin 2 → Fin 5 => sdBas E (q 0) * sdBas E (q 1)) := by
    funext q; rw [Fin.prod_univ_two]
  rw [hfun]
  have h1 : Set.range (fun q : Fin 2 → Fin 5 => sdBas E (q 0) * sdBas E (q 1))
      = Set.range (fun p : Fin 5 × Fin 5 => sdBas E p.1 * sdBas E p.2) := by
    ext z; constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q 0, q 1), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨![p.1, p.2], by simp⟩
  rw [h1]
  exact productSpan_eq R E

/-- The final reindexing: `Q 5` is the span featuring in the statement of `sdTF5Span`. -/
theorem Q_eq_target (E : WeierstrassCurve R) :
    Q E 5 = Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
      sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2)) := by
  unfold Q
  congr 1
  ext z; constructor
  · rintro ⟨f, rfl⟩
    simp only [Fin.prod_univ_five]
    exact ⟨(f 0, f 1, f 2, f 3, f 4), rfl⟩
  · rintro ⟨q, rfl⟩
    refine ⟨![q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2], ?_⟩
    simp only [Fin.prod_univ_five]
    simp

/-! ## §2 Membership of monomials in the relevant `Q n` -/

/-- `x^k ∈ Q 1` for `k ≤ 2`. -/
theorem x_pow_mem_Q_one (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 2) :
    (Work.MotV.genX E) ^ k ∈ Q E 1 := by
  rw [Q_one_eq]
  interval_cases k
  · exact Submodule.subset_span ⟨0, by simp [sdBas]⟩
  · exact Submodule.subset_span ⟨1, by simp [sdBas]⟩
  · exact Submodule.subset_span ⟨3, by simp [sdBas]⟩

/-- `xy ∈ Q 1`. -/
theorem x_mul_y_mem_Q_one (E : WeierstrassCurve R) :
    (Work.MotV.genX E) * (Work.MotV.genY E) ∈ Q E 1 := by
  rw [Q_one_eq]
  exact Submodule.subset_span ⟨4, by simp⟩

/-- `x^k ∈ Q 2` for `k ≤ 5` (the monomials of `L(10·O)` of the form `x^k`). -/
theorem x_pow_mem_Q_two (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 5) :
    (Work.MotV.genX E) ^ k ∈ Q E 2 := by
  rw [Q_two_eq]
  exact Submodule.subset_span ⟨Sum.inl ⟨k, by omega⟩, by simp⟩

/-- `x^k y ∈ Q 2` for `k ≤ 3` (the monomials of `L(10·O)` of the form `x^k y`). -/
theorem x_pow_mul_y_mem_Q_two (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 3) :
    (Work.MotV.genX E) ^ k * Work.MotV.genY E ∈ Q E 2 := by
  rw [Q_two_eq]
  exact Submodule.subset_span ⟨Sum.inr ⟨k, by omega⟩, by simp⟩

/-- A product of a member of `Q a` and a member of `Q b` lies in `Q (a+b)`. -/
theorem mul_mem_Q (E : WeierstrassCurve R) (a b : ℕ) {u v : Affine.FunctionField E}
    (hu : u ∈ Q E a) (hv : v ∈ Q E b) : u * v ∈ Q E (a + b) :=
  Q_mul_le E a b (Submodule.mul_mem_mul hu hv)

/-- `x^k y ∈ Q 3` for `k ≤ 5`. -/
theorem x_pow_mul_y_mem_Q_three (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 5) :
    (Work.MotV.genX E) ^ k * Work.MotV.genY E ∈ Q E 3 := by
  have ha : k - 3 ≤ 2 := by omega
  have hb : k - (k - 3) ≤ 3 := by omega
  have hsum : k - 3 + (k - (k - 3)) = k := by omega
  have h : (Work.MotV.genX E) ^ k * Work.MotV.genY E
      = (Work.MotV.genX E) ^ (k - 3)
        * ((Work.MotV.genX E) ^ (k - (k - 3)) * Work.MotV.genY E) := by
    rw [← mul_assoc, ← pow_add, hsum]
  rw [h]
  exact mul_mem_Q E 1 2 (x_pow_mem_Q_one E (k - 3) ha) (x_pow_mul_y_mem_Q_two E (k - (k - 3)) hb)

/-! ## §3 The 25 monomials of `sdTF5` lie in `Q 5` -/

/-- `x^k ∈ Q 5` for `k ≤ 12`. -/
theorem x_pow_mem_Q_five (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 12) :
    (Work.MotV.genX E) ^ k ∈ Q E 5 := by
  have ha : min k 5 ≤ 5 := min_le_right _ _
  have hb : min (k - min k 5) 5 ≤ 5 := min_le_right _ _
  have hc : k - min k 5 - min (k - min k 5) 5 ≤ 2 := by omega
  have hsum : min k 5 + min (k - min k 5) 5
      + (k - min k 5 - min (k - min k 5) 5) = k := by omega
  have h : (Work.MotV.genX E) ^ k
      = ((Work.MotV.genX E) ^ (min k 5) * (Work.MotV.genX E) ^ (min (k - min k 5) 5))
        * (Work.MotV.genX E) ^ (k - min k 5 - min (k - min k 5) 5) := by
    rw [← pow_add, ← pow_add, hsum]
  rw [h]
  exact mul_mem_Q E 4 1 (mul_mem_Q E 2 2 (x_pow_mem_Q_two E _ ha) (x_pow_mem_Q_two E _ hb))
    (x_pow_mem_Q_one E _ hc)

/-- `x^k y ∈ Q 5` for `k ≤ 10`. -/
theorem x_pow_mul_y_mem_Q_five (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 10) :
    (Work.MotV.genX E) ^ k * Work.MotV.genY E ∈ Q E 5 := by
  have ha : min k 5 ≤ 5 := min_le_right _ _
  have hb : k - min k 5 ≤ 5 := by omega
  have hsum : min k 5 + (k - min k 5) = k := by omega
  have h : (Work.MotV.genX E) ^ k * Work.MotV.genY E
      = (Work.MotV.genX E) ^ (min k 5)
        * ((Work.MotV.genX E) ^ (k - min k 5) * Work.MotV.genY E) := by
    rw [← mul_assoc, ← pow_add, hsum]
  rw [h]
  exact mul_mem_Q E 2 3 (x_pow_mem_Q_two E _ ha) (x_pow_mul_y_mem_Q_three E _ hb)

/-- `x¹¹ y ∈ Q 5`; here `x⁵ ∈ Q 2` comes from `L(5·O)·L(5·O) = L(10·O)`. -/
theorem x11_y_mem_Q_five (E : WeierstrassCurve R) :
    (Work.MotV.genX E) ^ 11 * Work.MotV.genY E ∈ Q E 5 := by
  have h1 : (Work.MotV.genX E) ^ 11
      = ((Work.MotV.genX E) ^ 5 * (Work.MotV.genX E) ^ 5) * Work.MotV.genX E := by
    rw [show (11 : ℕ) = (5 + 5) + 1 from rfl, pow_add, pow_add, pow_one]
  have h : (Work.MotV.genX E) ^ 11 * Work.MotV.genY E
      = ((Work.MotV.genX E) ^ 5 * (Work.MotV.genX E) ^ 5)
        * ((Work.MotV.genX E) * Work.MotV.genY E) := by
    rw [← mul_assoc, h1]
  rw [h]
  exact mul_mem_Q E 4 1 (mul_mem_Q E 2 2 (x_pow_mem_Q_two E 5 (by norm_num))
    (x_pow_mem_Q_two E 5 (by norm_num))) (x_mul_y_mem_Q_one E)

end

end Work.MotK.TwRuling.Five

namespace Work.MotK.TwRuling

/-- **The fivefold products of the basis `1, x, y, x², xy` span the 25 monomials of `L(25·O)`.**

This is `L(5·O)⁵ = L(25·O)` for an arbitrary Weierstrass curve over an arbitrary field; only the
Weierstrass relation is used (no smoothness, no restriction on the characteristic). -/
theorem sdTF5Span (R : Type) [Field R] (E : WeierstrassCurve R) :
    Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
        Work.MotK.TwRuling.sdBas E q.1 * Work.MotK.TwRuling.sdBas E q.2.1 *
          Work.MotK.TwRuling.sdBas E q.2.2.1 * Work.MotK.TwRuling.sdBas E q.2.2.2.1 *
          Work.MotK.TwRuling.sdBas E q.2.2.2.2))
      = Submodule.span R (Set.range (Work.MotK.TwRuling.sdTF5 E)) := by
  rw [← Five.Q_eq_target E]
  refine le_antisymm ?_ ?_
  · -- every fivefold product is a monomial of weight `≤ 25`, hence lies in `Ssp`
    rw [Five.Q, Submodule.span_le]
    intro z hz
    obtain ⟨f, rfl⟩ := hz
    obtain ⟨a, b, h, heq⟩ := Five.prod_sdBas_eq_monomial E f
    show (∏ i : Fin 5, sdBas E (f i)) ∈ Submodule.span R (Set.range (sdTF5 E))
    rw [heq]
    exact monomial_mem_sdTF5 R E a b h
  · -- every monomial of `sdTF5` is a product of at most five elements of the basis
    rw [Submodule.span_le]
    rintro z ⟨w, rfl⟩
    rcases w with i | j
    · rw [sdTF5_inl]
      exact Five.x_pow_mem_Q_five E (i : ℕ) (by have := i.isLt; omega)
    · rw [sdTF5_inr]
      by_cases hj : (j : ℕ) ≤ 10
      · exact Five.x_pow_mul_y_mem_Q_five E (j : ℕ) hj
      · have hj11 : (j : ℕ) = 11 := by have := j.isLt; omega
        rw [hj11]
        exact Five.x11_y_mem_Q_five E

end Work.MotK.TwRuling

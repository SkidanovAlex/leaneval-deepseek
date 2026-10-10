import Mathlib
import Submission.Work.MotK.TwRuling.KleinKerDefs
import Submission.Work.MotK.TwRuling.sdTF5Span
import Submission.Work.MotK.TwRuling.TF5defs
import Submission.Work.MotK.TwRuling.sdTF5_span
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L(5·O)^n = L(5n·O)` for every `n`

This file proves `Work.MotK.TwRuling.Q_eq_span_sdTFn`: for a field `R`, a Weierstrass curve `E`
over `R` and any `n : ℕ`, the `R`-span of the `n`-fold products of the basis
`sdBas E = ![1, x, y, x², xy]` of `L(5·O)` coincides with the `R`-span of the `5n` monomials
`sdTFn R E n` (`x^i` for `2i ≤ 5n` and `x^j y` for `2j + 3 ≤ 5n`).

The proof has the same two halves as the `n = 5` case (`sdTF5Span`):

* `Q E n ≤ span(sdTFn R E n)`: each `n`-fold product of basis elements is a monomial `x^a y^b`
  of weight `2a + 3b ≤ 5n`; every monomial of weight `≤ 5n` lies in the span by strong induction
  on `b`, lowering the `y`-degree with the Weierstrass relation.
* `span(sdTFn R E n) ≤ Q E n`: writing `i = 5k + s` with `s < 5`, one has
  `x^i = (x^5)^k · x^s ∈ Q E (2k) · Q E ⌈s/2⌉ ⊆ Q E (2k + ⌈s/2⌉) ⊆ Q E n`, and similarly for
  `x^i y` with `Q E (2k) · Q E ⌈(2s+3)/5⌉`; here `x^5 ∈ Q E 2` is `L(5·O)·L(5·O) = L(10·O)`
  (`Five.Q_two_eq`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

noncomputable section

variable {R : Type} [Field R]

/-! ## §0 Monotonicity and basic memberships for the spans `Q n` -/

/-- `1 = sdBas E 0 ∈ Q E j` for every `j` (pad with `1`s). -/
theorem one_mem_Q (E : WeierstrassCurve R) (j : ℕ) :
    (1 : Affine.FunctionField E) ∈ Five.Q E j := by
  refine Submodule.subset_span ⟨fun _ => 0, ?_⟩
  simp

/-- `Q` is monotone in the number of factors. -/
theorem Q_mono (E : WeierstrassCurve R) (m n : ℕ) (h : m ≤ n) : Five.Q E m ≤ Five.Q E n := by
  intro v hv
  have h1 : (1 : Affine.FunctionField E) ∈ Five.Q E (n - m) := one_mem_Q E (n - m)
  have hmul : v * 1 ∈ Five.Q E m * Five.Q E (n - m) := Submodule.mul_mem_mul hv h1
  have hle := Five.Q_mul_le E m (n - m) hmul
  rw [mul_one, Nat.add_sub_of_le h] at hle
  exact hle

/-- Powers of a member of `Q E c` stay in `Q E (c*k)`. -/
theorem pow_mem_Q (E : WeierstrassCurve R) {c : ℕ} {v : Affine.FunctionField E}
    (hv : v ∈ Five.Q E c) (k : ℕ) : v ^ k ∈ Five.Q E (c * k) := by
  induction k with
  | zero => rw [pow_zero, Nat.mul_zero]; exact one_mem_Q E 0
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact Five.mul_mem_Q E (c * k) c ih hv

/-- `x⁵ ∈ Q E 2` (`L(5·O)·L(5·O) = L(10·O)`). -/
theorem x5_mem_Q_two (E : WeierstrassCurve R) : (gx E) ^ 5 ∈ Five.Q E 2 :=
  Five.x_pow_mem_Q_two E 5 (by norm_num)

/-- `x^k ∈ Q E 1` for `k ≤ 2`. -/
theorem x_pow_mem_Q_one (E : WeierstrassCurve R) (k : ℕ) (hk : k ≤ 2) :
    (gx E) ^ k ∈ Five.Q E 1 := by
  interval_cases k
  · rw [pow_zero]; exact one_mem_Q E 1
  · rw [pow_one, Five.Q_one_eq]; exact Submodule.subset_span ⟨1, by simp⟩
  · rw [Five.Q_one_eq]; exact Submodule.subset_span ⟨3, by simp⟩

theorem x3_mem_Q_two (E : WeierstrassCurve R) : (gx E) ^ 3 ∈ Five.Q E 2 := by
  rw [show (gx E) ^ 3 = (gx E) ^ 1 * (gx E) ^ 2 by ring]
  exact Five.mul_mem_Q E 1 1 (x_pow_mem_Q_one E 1 (by norm_num))
    (x_pow_mem_Q_one E 2 (by norm_num))

theorem x4_mem_Q_two (E : WeierstrassCurve R) : (gx E) ^ 4 ∈ Five.Q E 2 := by
  rw [show (gx E) ^ 4 = (gx E) ^ 2 * (gx E) ^ 2 by ring]
  exact Five.mul_mem_Q E 1 1 (x_pow_mem_Q_one E 2 (by norm_num))
    (x_pow_mem_Q_one E 2 (by norm_num))

theorem y_mem_Q_one (E : WeierstrassCurve R) : (gy E) ∈ Five.Q E 1 := by
  rw [Five.Q_one_eq]; exact Submodule.subset_span ⟨2, by simp⟩

theorem xy_mem_Q_one (E : WeierstrassCurve R) : (gx E) * (gy E) ∈ Five.Q E 1 := by
  rw [Five.Q_one_eq]; exact Submodule.subset_span ⟨4, by simp⟩

theorem x2y_mem_Q_two (E : WeierstrassCurve R) : (gx E) ^ 2 * (gy E) ∈ Five.Q E 2 :=
  Five.x_pow_mul_y_mem_Q_two E 2 (by norm_num)

theorem x3y_mem_Q_two (E : WeierstrassCurve R) : (gx E) ^ 3 * (gy E) ∈ Five.Q E 2 :=
  Five.x_pow_mul_y_mem_Q_two E 3 (by norm_num)

theorem x4y_mem_Q_three (E : WeierstrassCurve R) : (gx E) ^ 4 * (gy E) ∈ Five.Q E 3 := by
  rw [show (gx E) ^ 4 * (gy E) = (gx E) ^ 2 * ((gx E) ^ 2 * (gy E)) by ring]
  exact Five.mul_mem_Q E 1 2 (x_pow_mem_Q_one E 2 (by norm_num)) (x2y_mem_Q_two E)

/-! ## §1 The generators of `sdTFn` lie in `Q E n` -/

/-- `x^i ∈ Q E n` whenever `2i ≤ 5n`. -/
theorem x_pow_mem_Q_gen (E : WeierstrassCurve R) (n i : ℕ) (hi : 2 * i ≤ 5 * n) :
    (gx E) ^ i ∈ Five.Q E n := by
  obtain ⟨k, s, hs, rfl⟩ : ∃ k s, s < 5 ∧ i = 5 * k + s :=
    ⟨i / 5, i % 5, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 5).symm⟩
  interval_cases s
  · rw [pow_add, pow_mul, pow_zero, mul_one]
    exact Q_mono E (2 * k) n (by omega)
      (pow_mem_Q E (x5_mem_Q_two E) k)
  · rw [pow_add, pow_mul]
    exact Q_mono E (2 * k + 1) n (by omega)
      (Five.mul_mem_Q E (2 * k) 1 (pow_mem_Q E (x5_mem_Q_two E) k)
        (by rw [Five.Q_one_eq]; exact Submodule.subset_span ⟨1, by simp⟩))
  · rw [pow_add, pow_mul]
    exact Q_mono E (2 * k + 1) n (by omega)
      (Five.mul_mem_Q E (2 * k) 1 (pow_mem_Q E (x5_mem_Q_two E) k)
        (by rw [Five.Q_one_eq]; exact Submodule.subset_span ⟨3, by simp⟩))
  · rw [pow_add, pow_mul]
    exact Q_mono E (2 * k + 2) n (by omega)
      (Five.mul_mem_Q E (2 * k) 2 (pow_mem_Q E (x5_mem_Q_two E) k) (x3_mem_Q_two E))
  · rw [pow_add, pow_mul]
    exact Q_mono E (2 * k + 2) n (by omega)
      (Five.mul_mem_Q E (2 * k) 2 (pow_mem_Q E (x5_mem_Q_two E) k) (x4_mem_Q_two E))

/-- `x^i * y ∈ Q E n` whenever `2i + 3 ≤ 5n`. -/
theorem x_pow_mul_y_mem_Q_gen (E : WeierstrassCurve R) (n i : ℕ) (hi : 2 * i + 3 ≤ 5 * n) :
    (gx E) ^ i * (gy E) ∈ Five.Q E n := by
  obtain ⟨k, s, hs, rfl⟩ : ∃ k s, s < 5 ∧ i = 5 * k + s :=
    ⟨i / 5, i % 5, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 5).symm⟩
  interval_cases s
  · rw [pow_add, pow_mul, pow_zero, mul_one]
    exact Q_mono E (2 * k + 1) n (by omega)
      (Five.mul_mem_Q E (2 * k) 1 (pow_mem_Q E (x5_mem_Q_two E) k) (y_mem_Q_one E))
  · rw [pow_add, pow_mul, pow_one, mul_assoc]
    exact Q_mono E (2 * k + 1) n (by omega)
      (Five.mul_mem_Q E (2 * k) 1 (pow_mem_Q E (x5_mem_Q_two E) k) (xy_mem_Q_one E))
  · rw [pow_add, pow_mul, mul_assoc]
    exact Q_mono E (2 * k + 2) n (by omega)
      (Five.mul_mem_Q E (2 * k) 2 (pow_mem_Q E (x5_mem_Q_two E) k) (x2y_mem_Q_two E))
  · rw [pow_add, pow_mul, mul_assoc]
    exact Q_mono E (2 * k + 2) n (by omega)
      (Five.mul_mem_Q E (2 * k) 2 (pow_mem_Q E (x5_mem_Q_two E) k) (x3y_mem_Q_two E))
  · rw [pow_add, pow_mul, mul_assoc]
    exact Q_mono E (2 * k + 3) n (by omega)
      (Five.mul_mem_Q E (2 * k) 3 (pow_mem_Q E (x5_mem_Q_two E) k) (x4y_mem_Q_three E))

/-! ## §2 The monomial reduction: every monomial of weight `≤ 5n` is in `span(sdTFn)` -/

/-- Multiplication by a scalar preserves `span(sdTFn R E n)`. -/
theorem algebraMap_mul_mem_span_sdTFn (E : WeierstrassCurve R) (n : ℕ) (c : R)
    {v : Affine.FunctionField E} (hv : v ∈ Submodule.span R (Set.range (sdTFn R E n))) :
    algebraMap R (Affine.FunctionField E) c * v ∈ Submodule.span R (Set.range (sdTFn R E n)) := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ c hv

/-- **The monomial reduction.**  Every monomial `x^a y^b` of weight `2a + 3b ≤ 5n` lies in the
span of the `5n` monomials `sdTFn R E n`.  Strong induction on `b`, using the Weierstrass
relation to replace `y²` by a polynomial in `x` and `y`. -/
theorem mono_mem_span_sdTFn (E : WeierstrassCurve R) (n : ℕ) (a b : ℕ)
    (h : 2 * a + 3 * b ≤ 5 * n) :
    (gx E) ^ a * (gy E) ^ b ∈ Submodule.span R (Set.range (sdTFn R E n)) := by
  have hrel := hrel' E
  have key : ∀ b a : ℕ, 2 * a + 3 * b ≤ 5 * n →
      (gx E) ^ a * (gy E) ^ b ∈ Submodule.span R (Set.range (sdTFn R E n)) := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro a h
      rcases lt_or_ge b 2 with hb | hb
      · interval_cases b
        · rw [pow_zero, mul_one]
          have ha : a < 5 * n / 2 + 1 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTFn R E n) (Sum.inl ⟨a, ha⟩))
        · rw [pow_one]
          have ha : a < (5 * n + 1) / 2 - 1 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTFn R E n) (Sum.inr ⟨a, ha⟩))
      · obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
        have hsplit : (gx E) ^ a * (gy E) ^ (c + 2) =
            (gx E) ^ (a + 3) * (gy E) ^ c
            + algebraMap R _ E.a₂ * ((gx E) ^ (a + 2) * (gy E) ^ c)
            + algebraMap R _ E.a₄ * ((gx E) ^ (a + 1) * (gy E) ^ c)
            + algebraMap R _ E.a₆ * ((gx E) ^ a * (gy E) ^ c)
            - algebraMap R _ E.a₁ * ((gx E) ^ (a + 1) * (gy E) ^ (c + 1))
            - algebraMap R _ E.a₃ * ((gx E) ^ a * (gy E) ^ (c + 1)) := by
          rw [show (gy E) ^ (c + 2) = (gy E) ^ c * (gy E) ^ 2 by rw [pow_add]]
          rw [hrel]
          first | refl_ring1 | ring
        rw [hsplit]
        refine Submodule.sub_mem _ (Submodule.sub_mem _
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
        · exact ih c (by omega) (a + 3) (by omega)
        · exact algebraMap_mul_mem_span_sdTFn E n E.a₂ (ih c (by omega) (a + 2) (by omega))
        · exact algebraMap_mul_mem_span_sdTFn E n E.a₄ (ih c (by omega) (a + 1) (by omega))
        · exact algebraMap_mul_mem_span_sdTFn E n E.a₆ (ih c (by omega) a (by omega))
        · exact algebraMap_mul_mem_span_sdTFn E n E.a₁ (ih (c + 1) (by omega) (a + 1) (by omega))
        · exact algebraMap_mul_mem_span_sdTFn E n E.a₃ (ih (c + 1) (by omega) a (by omega))
  exact key b a h

/-- Each `n`-fold product of basis elements is a monomial of weight `≤ 5n`, hence in
`span(sdTFn R E n)`. -/
theorem prod_mem_span_sdTFn (E : WeierstrassCurve R) (n : ℕ) (f : Fin n → Fin 5) :
    (∏ i, sdBas E (f i)) ∈ Submodule.span R (Set.range (sdTFn R E n)) := by
  have hw : 2 * (∑ i, Five.eX (f i)) + 3 * (∑ i, Five.eY (f i)) ≤ 5 * n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc ∑ i : Fin n, (2 * Five.eX (f i) + 3 * Five.eY (f i)) ≤ ∑ _i : Fin n, 5 :=
          Finset.sum_le_sum fun i _ => Five.weight_bound (f i)
      _ = 5 * n := by simp [Finset.sum_const, Nat.mul_comm]
  have heq : (∏ i, sdBas E (f i))
      = (gx E) ^ (∑ i, Five.eX (f i)) * (gy E) ^ (∑ i, Five.eY (f i)) := by
    calc (∏ i, sdBas E (f i))
        = ∏ i, ((gx E) ^ Five.eX (f i) * (gy E) ^ Five.eY (f i)) :=
          Finset.prod_congr rfl fun i _ => Five.sdBas_eq_monomial E (f i)
      _ = (∏ i, (gx E) ^ Five.eX (f i)) * (∏ i, (gy E) ^ Five.eY (f i)) := by
          rw [Finset.prod_mul_distrib]
      _ = (gx E) ^ (∑ i, Five.eX (f i)) * (gy E) ^ (∑ i, Five.eY (f i)) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [heq]
  exact mono_mem_span_sdTFn E n _ _ hw

/-! ## §3 The target -/

/-- **`L(5·O)^n = L(5n·O)`.**  The `R`-span of the `n`-fold products of the basis
`sdBas E = ![1, x, y, x², xy]` equals the `R`-span of the family `sdTFn R E n` of `5n` monomials
`x^i` (`2i ≤ 5n`) and `x^j * y` (`2j + 3 ≤ 5n`).  ROUTE: `≤` by the monomial reduction with the
Weierstrass relation `hrel'` (`Submission.Work.MotK.TwRuling.TF5defs`), strong induction on the
`y`-degree (cf. `mono_mem_Ssp` in `Submission.Work.MotK.TwRuling.sdTF5_span`); `≥` by writing
`A = 5k + s` and using `x^5 ∈ Q E 2` (`Q_two_eq`), `Q_mul_le` and the explicit memberships
`x^s ∈ Q E ⌈s/2⌉`, `x^s * y ∈ Q E ⌈(2s+3)/5⌉` for `s < 5`, together with monotonicity of `Q`
in `n` (pad with `1 = sdBas E 0`).  No hypothesis on `E` beyond `R` a field; `n = 0` included. -/
theorem Q_eq_span_sdTFn (R : Type) [Field R] (E : WeierstrassCurve R) (n : ℕ) :
    Work.MotK.TwRuling.Five.Q E n = Submodule.span R (Set.range (sdTFn R E n)) := by
  refine le_antisymm ?_ ?_
  · rw [Five.Q, Submodule.span_le]
    rintro z ⟨f, rfl⟩
    exact prod_mem_span_sdTFn E n f
  · rw [Submodule.span_le]
    rintro z ⟨w, rfl⟩
    rcases w with i | j
    · rw [sdTFn_inl]
      exact x_pow_mem_Q_gen E n i (by have h := i.isLt; omega)
    · rw [sdTFn_inr]
      exact x_pow_mul_y_mem_Q_gen E n j (by have h := j.isLt; omega)

end

end Work.MotK.TwRuling

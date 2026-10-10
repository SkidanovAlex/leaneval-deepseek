import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.SdWNdeg
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

set_option maxHeartbeats 2000000
set_option linter.unusedTactic false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

noncomputable section

variable {R : Type} [Field R]

/-!
# `L(5·O)⁶ = L(30·O)`: the span of the sixfold products of the basis `1, x, y, x², xy`

For a field `R` and a Weierstrass curve `E` over `R`, the `R`-span of the sixfold
products of the basis `sdBas E = ![1, x, y, x², xy]` (a basis of `L(5·O)`) equals the span of the
30 monomials `sdTF6 E = (x^i)_{i<16} ⊕ (x^j y)_{j<14}` (the standard spanning family of
`L(30·O)`), where `x = genX E`, `y = genY E` in the function field of `E`.

This is the sixfold analogue of `sdTF5_span` (`L(5·O)⁵ = L(25·O)`) and of `productSpan_eq`
(`L(5·O)·L(5·O) = L(10·O)`).

Write `Tsp6` for the span of the sixfold products and `Ssp6` for the span of `sdTF6`.  The two
inclusions are proved independently:

* `Ssp6 ≤ Tsp6`: the fivefold analogue `sdTF5_span` gives `Tsp = Ssp` (`Tsp` the span of the
  fivefold products, `Ssp` the span of `L(25·O)`), and `Tsp ⊆ Tsp6` because a fivefold product is a
  sixfold product (pad with `1 = sdBas 0`).  Hence the 25 monomials of `L(25·O)` lie in `Tsp6`.
  The five remaining monomials `x¹³, x¹⁴, x¹⁵, x¹²y, x¹³y` are obtained by multiplying an element
  of `Tsp` by one basis element (`x¹³ = x¹¹·x²`, `x¹²y = x¹¹y·x`, …), which lands in `Tsp6`; and
  `x¹⁵` additionally uses the Weierstrass relation
  `x¹²y² = x¹⁵ + a₂x¹⁴ + a₄x¹³ + a₆x¹² − a₁x¹³y − a₃x¹²y` with `x¹²y² = x¹¹y·xy`.
* `Tsp6 ≤ Ssp6`: each sixfold product is a monomial `x^A y^B` with `2A + 3B ≤ 30` (each basis
  element has pole order `≤ 5`), and `mono_mem_Ssp6` shows that every such monomial lies in `Ssp6`
  by strong induction on `B`, using the Weierstrass relation to lower the `y`-degree.
-/

/-! ## The two spans -/

/-- The span of the sixfold products of the basis `1, x, y, x², xy`. -/
def Tsp6 (E : WeierstrassCurve R) : Submodule R (Affine.FunctionField E) :=
  Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
    sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2.1 *
      sdBas E q.2.2.2.2.2))

/-- The span of `sdTF6 E`, i.e. of the 30 monomials of `L(30·O)`. -/
def Ssp6 (E : WeierstrassCurve R) : Submodule R (Affine.FunctionField E) :=
  Submodule.span R (Set.range (sdTF6 E))

/-- `Ssp6 E` is closed under multiplication by scalars. -/
theorem hsmS6 (E : WeierstrassCurve R) (c : R) {v : Affine.FunctionField E}
    (hv : v ∈ Ssp6 E) : algebraMap R (Affine.FunctionField E) c * v ∈ Ssp6 E := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ c hv

/-- `Tsp6 E` is closed under multiplication by scalars. -/
theorem hsmT6 (E : WeierstrassCurve R) (c : R) {v : Affine.FunctionField E}
    (hv : v ∈ Tsp6 E) : algebraMap R (Affine.FunctionField E) c * v ∈ Tsp6 E := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ c hv

/-! ## Step 1: every monomial of pole order `≤ 30` lies in `Ssp6` -/

/-- Every monomial `x^a y^b` with pole order `2a + 3b ≤ 30` lies in `Ssp6 E`. -/
theorem mono_mem_Ssp6 (E : WeierstrassCurve R) (a b : ℕ) (h : 2 * a + 3 * b ≤ 30) :
    (gx E) ^ a * (gy E) ^ b ∈ Ssp6 E := by
  have hrel := hrel' E
  have key : ∀ b a : ℕ, 2 * a + 3 * b ≤ 30 → (gx E) ^ a * (gy E) ^ b ∈ Ssp6 E := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro a h
      rcases lt_or_ge b 2 with hb | hb
      · interval_cases b
        · rw [pow_zero, mul_one]
          have ha : a < 16 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTF6 E) (Sum.inl ⟨a, ha⟩))
        · rw [pow_one]
          have ha : a < 14 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTF6 E) (Sum.inr ⟨a, ha⟩))
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
        · exact hsmS6 E E.a₂ (ih c (by omega) (a + 2) (by omega))
        · exact hsmS6 E E.a₄ (ih c (by omega) (a + 1) (by omega))
        · exact hsmS6 E E.a₆ (ih c (by omega) a (by omega))
        · exact hsmS6 E E.a₁ (ih (c + 1) (by omega) (a + 1) (by omega))
        · exact hsmS6 E E.a₃ (ih (c + 1) (by omega) a (by omega))
  exact key b a h

/-! ## Step 2: `Tsp6 ≤ Ssp6` -/

/-- The exponents of the basis elements `sdBas E k = x^(eexp6 k) * y^(fexp6 k)`. -/
private def eexp6 : Fin 5 → ℕ := ![0, 1, 0, 2, 1]

/-- The `y`-exponents of the basis elements `sdBas E k = x^(eexp6 k) * y^(fexp6 k)`. -/
private def fexp6 : Fin 5 → ℕ := ![0, 0, 1, 0, 1]

private theorem sdBas_mono6 (E : WeierstrassCurve R) (k : Fin 5) :
    sdBas E k = (gx E) ^ (eexp6 k) * (gy E) ^ (fexp6 k) := by
  fin_cases k <;> simp [sdBas, eexp6, fexp6]

private theorem wgt_le6 (k : Fin 5) : 2 * eexp6 k + 3 * fexp6 k ≤ 5 := by
  fin_cases k <;> decide

/-- A sixfold product of basis elements is a monomial of pole order `≤ 30`, hence lies in `Ssp6`. -/
private theorem prod_mem_Ssp6 (E : WeierstrassCurve R)
    (q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) :
    sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2.1
      * sdBas E q.2.2.2.2.2 ∈ Ssp6 E := by
  have h1 := sdBas_mono6 E q.1
  have h2 := sdBas_mono6 E q.2.1
  have h3 := sdBas_mono6 E q.2.2.1
  have h4 := sdBas_mono6 E q.2.2.2.1
  have h5 := sdBas_mono6 E q.2.2.2.2.1
  have h6 := sdBas_mono6 E q.2.2.2.2.2
  have hw : 2 * (eexp6 q.1 + eexp6 q.2.1 + eexp6 q.2.2.1 + eexp6 q.2.2.2.1 + eexp6 q.2.2.2.2.1
        + eexp6 q.2.2.2.2.2)
      + 3 * (fexp6 q.1 + fexp6 q.2.1 + fexp6 q.2.2.1 + fexp6 q.2.2.2.1 + fexp6 q.2.2.2.2.1
        + fexp6 q.2.2.2.2.2) ≤ 30 := by
    have w1 := wgt_le6 q.1
    have w2 := wgt_le6 q.2.1
    have w3 := wgt_le6 q.2.2.1
    have w4 := wgt_le6 q.2.2.2.1
    have w5 := wgt_le6 q.2.2.2.2.1
    have w6 := wgt_le6 q.2.2.2.2.2
    omega
  have heq : sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1
        * sdBas E q.2.2.2.2.1 * sdBas E q.2.2.2.2.2
      = (gx E) ^ (eexp6 q.1 + eexp6 q.2.1 + eexp6 q.2.2.1 + eexp6 q.2.2.2.1 + eexp6 q.2.2.2.2.1
          + eexp6 q.2.2.2.2.2)
        * (gy E) ^ (fexp6 q.1 + fexp6 q.2.1 + fexp6 q.2.2.1 + fexp6 q.2.2.2.1 + fexp6 q.2.2.2.2.1
          + fexp6 q.2.2.2.2.2) := by
    rw [h1, h2, h3, h4, h5, h6]
    first | refl_ring1 | ring
  rw [heq]
  exact mono_mem_Ssp6 E _ _ hw

/-- Every sixfold product of basis elements lies in the span of the 30 monomials of `L(30·O)`. -/
theorem Tsp6_le_Ssp6 (E : WeierstrassCurve R) : Tsp6 E ≤ Ssp6 E := by
  change Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
      sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2.1
        * sdBas E q.2.2.2.2.2)) ≤ Ssp6 E
  rw [Submodule.span_le]
  rintro u ⟨q, rfl⟩
  exact prod_mem_Ssp6 E q

/-! ## Step 3: the ingredients of `Ssp6 ≤ Tsp6` -/

/-- A fivefold product of basis elements lies in `Tsp6` (pad with `1 = sdBas E 0`). -/
theorem Tsp_le_Tsp6 (E : WeierstrassCurve R) : Tsp E ≤ Tsp6 E := by
  change Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
      sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2))
      ≤ Tsp6 E
  rw [Submodule.span_le]
  rintro u ⟨q, rfl⟩
  refine Submodule.subset_span ⟨(q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, (0 : Fin 5)), ?_⟩
  simp only [sdBas_apply_zero, mul_one]

/-- The product of a fivefold product of basis elements with one further basis element still lies
in `Tsp6 E`. -/
theorem mul_sdBas_mem_Tsp6 (E : WeierstrassCurve R) (k : Fin 5) {u : Affine.FunctionField E}
    (hu : u ∈ Tsp E) : u * sdBas E k ∈ Tsp6 E := by
  have key : ∀ u ∈ Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
      sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2)),
      u * sdBas E k ∈ Tsp6 E := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨q, rfl⟩ := hu
      exact Submodule.subset_span ⟨(q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, k), rfl⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => rw [add_mul]; exact Submodule.add_mem _ ihx ihy
    | smul a x hx ihx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a ihx
  exact key u hu

/-- `x^m ∈ Tsp E` for `m ≤ 12` (the 13 monomials `x^0, …, x¹²` of `L(25·O)`). -/
theorem xpow_mem_Tsp (E : WeierstrassCurve R) (m : ℕ) (hm : m ≤ 12) :
    (gx E) ^ m ∈ Tsp E := by
  rw [show Tsp E = Ssp E from sdTF5_span R E]
  change (gx E) ^ m ∈ Submodule.span R (Set.range (sdTF5 E))
  exact Submodule.subset_span ⟨Sum.inl ⟨m, by omega⟩, by simp [sdTF5_inl]⟩

/-- `x^m * y ∈ Tsp E` for `m ≤ 11` (the 12 monomials `y, xy, …, x¹¹y` of `L(25·O)`). -/
theorem xpow_mul_mem_Tsp (E : WeierstrassCurve R) (m : ℕ) (hm : m ≤ 11) :
    (gx E) ^ m * gy E ∈ Tsp E := by
  rw [show Tsp E = Ssp E from sdTF5_span R E]
  change (gx E) ^ m * gy E ∈ Submodule.span R (Set.range (sdTF5 E))
  exact Submodule.subset_span ⟨Sum.inr ⟨m, by omega⟩, by simp [sdTF5_inr]⟩

/-! ## Step 4: `Ssp6 ≤ Tsp6` -/

/-- Every monomial of `L(30·O)` lies in the span of the sixfold products. -/
theorem Ssp6_le_Tsp6 (E : WeierstrassCurve R) : Ssp6 E ≤ Tsp6 E := by
  have hx11 : (gx E) ^ 11 ∈ Tsp E := xpow_mem_Tsp E 11 (by norm_num)
  have hx12 : (gx E) ^ 12 ∈ Tsp E := xpow_mem_Tsp E 12 (by norm_num)
  have hx11y : (gx E) ^ 11 * gy E ∈ Tsp E := xpow_mul_mem_Tsp E 11 (by norm_num)
  -- the five "top" monomials
  have hx13 : (gx E) ^ 13 ∈ Tsp6 E := by
    have h := mul_sdBas_mem_Tsp6 E (3 : Fin 5) hx11
    rw [sdBas_apply_three, ← pow_add] at h
    norm_num at h
    exact h
  have hx14 : (gx E) ^ 14 ∈ Tsp6 E := by
    have h := mul_sdBas_mem_Tsp6 E (3 : Fin 5) hx12
    rw [sdBas_apply_three, ← pow_add] at h
    norm_num at h
    exact h
  have hx12y : (gx E) ^ 12 * gy E ∈ Tsp6 E := by
    have h := mul_sdBas_mem_Tsp6 E (1 : Fin 5) hx11y
    rw [sdBas_apply_one] at h
    convert h using 1
    first | refl_ring1 | ring
  have hx13y : (gx E) ^ 13 * gy E ∈ Tsp6 E := by
    have h := mul_sdBas_mem_Tsp6 E (3 : Fin 5) hx11y
    rw [sdBas_apply_three] at h
    convert h using 1
    first | refl_ring1 | ring
  have hx12y2 : (gx E) ^ 12 * (gy E) ^ 2 ∈ Tsp6 E := by
    have h := mul_sdBas_mem_Tsp6 E (4 : Fin 5) hx11y
    rw [sdBas_apply_four] at h
    convert h using 1
    first | refl_ring1 | ring
  have hx15 : (gx E) ^ 15 ∈ Tsp6 E := by
    have hrel := hrel' E
    have hkey : (gx E) ^ 15 = (gx E) ^ 12 * (gy E) ^ 2
        - algebraMap R _ E.a₂ * (gx E) ^ 14 - algebraMap R _ E.a₄ * (gx E) ^ 13
        - algebraMap R _ E.a₆ * (gx E) ^ 12
        + algebraMap R _ E.a₁ * ((gx E) ^ 13 * gy E)
        + algebraMap R _ E.a₃ * ((gx E) ^ 12 * gy E) := by
      linear_combination (norm := first | refl_ring1 | ring1) (-((gx E) ^ 12)) * hrel
    rw [hkey]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx12y2 (hsmT6 E E.a₂ hx14)) (hsmT6 E E.a₄ hx13))
      (hsmT6 E E.a₆ (Tsp_le_Tsp6 E hx12))) (hsmT6 E E.a₁ hx13y)) (hsmT6 E E.a₃ hx12y)
  have hxmem : ∀ m : ℕ, m ≤ 15 → (gx E) ^ m ∈ Tsp6 E := by
    intro m hm
    interval_cases m
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 0 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 1 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 2 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 3 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 4 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 5 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 6 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 7 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 8 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 9 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 10 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 11 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mem_Tsp E 12 (by norm_num))
    · exact hx13
    · exact hx14
    · exact hx15
  have hxymem : ∀ m : ℕ, m ≤ 13 → (gx E) ^ m * gy E ∈ Tsp6 E := by
    intro m hm
    interval_cases m
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 0 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 1 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 2 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 3 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 4 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 5 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 6 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 7 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 8 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 9 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 10 (by norm_num))
    · exact Tsp_le_Tsp6 E (xpow_mul_mem_Tsp E 11 (by norm_num))
    · exact hx12y
    · exact hx13y
  change Submodule.span R (Set.range (sdTF6 E)) ≤ Tsp6 E
  rw [Submodule.span_le]
  rintro u ⟨k, rfl⟩
  rcases k with i | j
  · rw [sdTF6_inl]
    exact hxmem _ (by have := i.isLt; omega)
  · rw [sdTF6_inr]
    exact hxymem _ (by have := j.isLt; omega)

/-! ## The target -/

theorem sdTF6_span (R : Type) [Field R] (E : WeierstrassCurve R) :
    Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
        Work.MotK.TwRuling.sdBas E q.1 * Work.MotK.TwRuling.sdBas E q.2.1 *
          Work.MotK.TwRuling.sdBas E q.2.2.1 * Work.MotK.TwRuling.sdBas E q.2.2.2.1 *
          Work.MotK.TwRuling.sdBas E q.2.2.2.2.1 * Work.MotK.TwRuling.sdBas E q.2.2.2.2.2))
      = Submodule.span R (Set.range (Work.MotK.TwRuling.sdTF6 E)) := by
  change Tsp6 E = Ssp6 E
  exact le_antisymm (Tsp6_le_Ssp6 E) (Ssp6_le_Tsp6 E)

end

end Work.MotK.TwRuling

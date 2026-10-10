import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.MotK.TwRuling.TF5defs
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
# `L(5·O)⁵ = L(25·O)`: the span of the fivefold products of the basis `1, x, y, x², xy`

For a field `R` and a Weierstrass curve `E` over `R`, the `R`-span of the 25 fivefold products of
the basis `sdBas E = ![1, x, y, x², xy]` (the basis of `L(5·O)`) equals the span of the 25 monomials
`sdTF5 E = (x^i)_{i<13} ⊕ (x^j y)_{j<12}` (the standard basis of `L(25·O)`), where `x = genX E`,
`y = genY E` in the function field of `E`.

This is the fivefold analogue of `productSpan_eq` (`L(5·O)·L(5·O) = L(10·O)`), and proves that the
multiplication map `L(5·O)⁵ → L(25·O)` is onto.

The two inclusions are proved independently.

* `⊆` (`Tsp_le_Ssp` below): each fivefold product of basis elements is a monomial `x^a y^b` whose
  *weight* `wt x = 2`, `wt y = 3` is `≤ 25` (each basis element has weight `≤ 5`).  Every monomial
  `x^a y^b` with `2a + 3b ≤ 25` lies in `Ssp` by strong induction on `b`, using the Weierstrass
  relation to lower the `y`-degree (`mono_mem_Ssp` below).
* `⊇`: every monomial `x^a y^b` with `a + b ≤ 10`, `b ≤ 5` is *literally* a fivefold product of
  basis elements (`hp` below), and the four "top" monomials `x¹¹`, `x¹⁰y`, `x¹²`, `x¹¹y`
  (`a + b > 10`) are obtained from the Weierstrass relation: multiplying the relation solved for
  `y²` by a suitable monomial gives each of `x^8y²`, `x^7y³`, `x^6y⁴`, `x^5y^5`, `x^9y²`, `x^8y³`
  as an explicit `R`-linear combination of products, from which `x¹¹`, `x¹⁰y`, `x⁹y²`, `x⁸y³`,
  `x¹²`, `x¹¹y` follow.
-/

/-! ## The monomial reduction `Tsp ≤ Ssp` -/

private theorem mono_mem_Ssp (E : WeierstrassCurve R) (a b : ℕ) (h : 2 * a + 3 * b ≤ 25) :
    (gx E) ^ a * (gy E) ^ b ∈ Ssp E := by
  have hrel := hrel' E
  have key : ∀ b a : ℕ, 2 * a + 3 * b ≤ 25 → (gx E) ^ a * (gy E) ^ b ∈ Ssp E := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro a h
      rcases lt_or_ge b 2 with hb | hb
      · interval_cases b
        · rw [pow_zero, mul_one]
          have ha : a < 13 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTF5 E) (Sum.inl ⟨a, ha⟩))
        · rw [pow_one]
          have ha : a < 12 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTF5 E) (Sum.inr ⟨a, ha⟩))
      · obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
        have hsplit : (gx E) ^ a * (gy E) ^ (c + 2) =
            (gx E) ^ (a + 3) * (gy E) ^ c
            + algebraMap R _ E.a₂ * ((gx E) ^ (a + 2) * (gy E) ^ c)
            + algebraMap R _ E.a₄ * ((gx E) ^ (a + 1) * (gy E) ^ c)
            + algebraMap R _ E.a₆ * ((gx E) ^ a * (gy E) ^ c)
            - algebraMap R _ E.a₁ * ((gx E) ^ (a + 1) * (gy E) ^ (c + 1))
            - algebraMap R _ E.a₃ * ((gx E) ^ a * (gy E) ^ (c + 1)) := by
          rw [show (gy E) ^ (c + 2) = (gy E) ^ c * (gy E) ^(2:ℕ) by rw [pow_add]]
          rw [hrel]
          first | refl_ring1 | ring
        rw [hsplit]
        refine Submodule.sub_mem _ (Submodule.sub_mem _
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
        · exact ih c (by omega) (a + 3) (by omega)
        · exact hsmS E E.a₂ (ih c (by omega) (a + 2) (by omega))
        · exact hsmS E E.a₄ (ih c (by omega) (a + 1) (by omega))
        · exact hsmS E E.a₆ (ih c (by omega) a (by omega))
        · exact hsmS E E.a₁ (ih (c + 1) (by omega) (a + 1) (by omega))
        · exact hsmS E E.a₃ (ih (c + 1) (by omega) a (by omega))
  exact key b a h

/-- The exponents of the basis elements `sdBas E k = x^(eexp k) * y^(fexp k)`. -/
private def eexp : Fin 5 → ℕ := ![0, 1, 0, 2, 1]

/-- The `y`-exponents of the basis elements `sdBas E k = x^(eexp k) * y^(fexp k)`. -/
private def fexp : Fin 5 → ℕ := ![0, 0, 1, 0, 1]

private theorem sdBas_mono (E : WeierstrassCurve R) (k : Fin 5) :
    sdBas E k = (gx E) ^ (eexp k) * (gy E) ^ (fexp k) := by
  fin_cases k <;> simp [sdBas, eexp, fexp]

private theorem wgt_le (k : Fin 5) : 2 * eexp k + 3 * fexp k ≤ 5 := by
  fin_cases k <;> decide

private theorem prod_mem_Ssp (E : WeierstrassCurve R)
    (q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5) :
    sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2
      ∈ Ssp E := by
  have h1 := sdBas_mono E q.1
  have h2 := sdBas_mono E q.2.1
  have h3 := sdBas_mono E q.2.2.1
  have h4 := sdBas_mono E q.2.2.2.1
  have h5 := sdBas_mono E q.2.2.2.2
  have hw : 2 * (eexp q.1 + eexp q.2.1 + eexp q.2.2.1 + eexp q.2.2.2.1 + eexp q.2.2.2.2)
      + 3 * (fexp q.1 + fexp q.2.1 + fexp q.2.2.1 + fexp q.2.2.2.1 + fexp q.2.2.2.2) ≤ 25 := by
    have w1 := wgt_le q.1
    have w2 := wgt_le q.2.1
    have w3 := wgt_le q.2.2.1
    have w4 := wgt_le q.2.2.2.1
    have w5 := wgt_le q.2.2.2.2
    omega
  have heq : sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1
        * sdBas E q.2.2.2.2
      = (gx E) ^ (eexp q.1 + eexp q.2.1 + eexp q.2.2.1 + eexp q.2.2.2.1 + eexp q.2.2.2.2)
        * (gy E) ^ (fexp q.1 + fexp q.2.1 + fexp q.2.2.1 + fexp q.2.2.2.1 + fexp q.2.2.2.2) := by
    rw [h1, h2, h3, h4, h5]
    first | refl_ring1 | ring
  rw [heq]
  exact mono_mem_Ssp E _ _ hw

private theorem Tsp_le_Ssp' (E : WeierstrassCurve R) : Tsp E ≤ Ssp E := by
  change Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
    sdBas E q.1 * sdBas E q.2.1 * sdBas E q.2.2.1 * sdBas E q.2.2.2.1 * sdBas E q.2.2.2.2))
      ≤ Ssp E
  rw [Submodule.span_le]
  rintro u ⟨q, rfl⟩
  exact prod_mem_Ssp E q

/-! ## Fivefold products of basis elements -/

private theorem Tmem (E : WeierstrassCurve R) (i1 i2 i3 i4 i5 : Fin 5)
    {v : Affine.FunctionField E}
    (h : v = sdBas E i1 * sdBas E i2 * sdBas E i3 * sdBas E i4 * sdBas E i5) : v ∈ Tsp E := by
  rw [h]
  exact mem5 E i1 i2 i3 i4 i5

theorem sdTF5_span (R : Type) [Field R] (E : WeierstrassCurve R) :
    Submodule.span R (Set.range (fun q : Fin 5 × Fin 5 × Fin 5 × Fin 5 × Fin 5 =>
        Work.MotK.TwRuling.sdBas E q.1 * Work.MotK.TwRuling.sdBas E q.2.1 *
          Work.MotK.TwRuling.sdBas E q.2.2.1 * Work.MotK.TwRuling.sdBas E q.2.2.2.1 *
          Work.MotK.TwRuling.sdBas E q.2.2.2.2))
      = Submodule.span R (Set.range (Work.MotK.TwRuling.sdTF5 E)) := by
  change Tsp E = Ssp E
  have hrel := hrel' E
  -- ## The six Weierstrass identities (natural direction)
  have hN1 : (gx E)^(8:ℕ) * (gy E)^(2:ℕ) = (gx E)^(11:ℕ) + algebraMap R _ E.a₂ * (gx E)^(10:ℕ)
      + algebraMap R _ E.a₄ * (gx E)^(9:ℕ) + algebraMap R _ E.a₆ * (gx E)^(8:ℕ)
      - algebraMap R _ E.a₁ * ((gx E)^(9:ℕ) * (gy E)) - algebraMap R _ E.a₃ * ((gx E)^(8:ℕ) * (gy E)) := by
    linear_combination (norm := first | refl_ring1 | ring1) ((gx E)^(8:ℕ)) * hrel
  have hN2 : (gx E)^(7:ℕ) * (gy E)^(3:ℕ) = (gx E)^(10:ℕ) * (gy E) + algebraMap R _ E.a₂ * ((gx E)^(9:ℕ) * (gy E))
      + algebraMap R _ E.a₄ * ((gx E)^(8:ℕ) * (gy E)) + algebraMap R _ E.a₆ * ((gx E)^(7:ℕ) * (gy E))
      - algebraMap R _ E.a₁ * ((gx E)^(8:ℕ) * (gy E)^(2:ℕ))
      - algebraMap R _ E.a₃ * ((gx E)^(7:ℕ) * (gy E)^(2:ℕ)) := by
    linear_combination (norm := first | refl_ring1 | ring1) ((gx E)^(7:ℕ) * (gy E)) * hrel
  have hN3 : (gx E)^(6:ℕ) * (gy E)^(4:ℕ) = (gx E)^(9:ℕ) * (gy E)^(2:ℕ) + algebraMap R _ E.a₂ * ((gx E)^(8:ℕ) * (gy E)^(2:ℕ))
      + algebraMap R _ E.a₄ * ((gx E)^(7:ℕ) * (gy E)^(2:ℕ)) + algebraMap R _ E.a₆ * ((gx E)^(6:ℕ) * (gy E)^(2:ℕ))
      - algebraMap R _ E.a₁ * ((gx E)^(7:ℕ) * (gy E)^(3:ℕ))
      - algebraMap R _ E.a₃ * ((gx E)^(6:ℕ) * (gy E)^(3:ℕ)) := by
    linear_combination (norm := first | refl_ring1 | ring1) ((gx E)^(6:ℕ) * (gy E)^(2:ℕ)) * hrel
  have hN4 : (gx E)^(5:ℕ) * (gy E)^(5:ℕ) = (gx E)^(8:ℕ) * (gy E)^(3:ℕ) + algebraMap R _ E.a₂ * ((gx E)^(7:ℕ) * (gy E)^(3:ℕ))
      + algebraMap R _ E.a₄ * ((gx E)^(6:ℕ) * (gy E)^(3:ℕ)) + algebraMap R _ E.a₆ * ((gx E)^(5:ℕ) * (gy E)^(3:ℕ))
      - algebraMap R _ E.a₁ * ((gx E)^(6:ℕ) * (gy E)^(4:ℕ))
      - algebraMap R _ E.a₃ * ((gx E)^(5:ℕ) * (gy E)^(4:ℕ)) := by
    linear_combination (norm := first | refl_ring1 | ring1) ((gx E)^(5:ℕ) * (gy E)^(3:ℕ)) * hrel
  have hN5 : (gx E)^(9:ℕ) * (gy E)^(2:ℕ) = (gx E)^(12:ℕ) + algebraMap R _ E.a₂ * (gx E)^(11:ℕ)
      + algebraMap R _ E.a₄ * (gx E)^(10:ℕ) + algebraMap R _ E.a₆ * (gx E)^(9:ℕ)
      - algebraMap R _ E.a₁ * ((gx E)^(10:ℕ) * (gy E))
      - algebraMap R _ E.a₃ * ((gx E)^(9:ℕ) * (gy E)) := by
    linear_combination (norm := first | refl_ring1 | ring1) ((gx E)^(9:ℕ)) * hrel
  have hN6 : (gx E)^(8:ℕ) * (gy E)^(3:ℕ) = (gx E)^(11:ℕ) * (gy E) + algebraMap R _ E.a₂ * ((gx E)^(10:ℕ) * (gy E))
      + algebraMap R _ E.a₄ * ((gx E)^(9:ℕ) * (gy E)) + algebraMap R _ E.a₆ * ((gx E)^(8:ℕ) * (gy E))
      - algebraMap R _ E.a₁ * ((gx E)^(9:ℕ) * (gy E)^(2:ℕ))
      - algebraMap R _ E.a₃ * ((gx E)^(8:ℕ) * (gy E)^(2:ℕ)) := by
    linear_combination (norm := first | refl_ring1 | ring1) ((gx E)^(8:ℕ) * (gy E)) * hrel
  -- ## The same identities, solved for the top monomial
  have hI1 : (gx E)^(11:ℕ) = (gx E)^(8:ℕ) * (gy E)^(2:ℕ) - algebraMap R _ E.a₂ * (gx E)^(10:ℕ)
      - algebraMap R _ E.a₄ * (gx E)^(9:ℕ) - algebraMap R _ E.a₆ * (gx E)^(8:ℕ)
      + algebraMap R _ E.a₁ * ((gx E)^(9:ℕ) * (gy E)) + algebraMap R _ E.a₃ * ((gx E)^(8:ℕ) * (gy E)) := by
    rw [hN1]; ring
  have hI2 : (gx E)^(10:ℕ) * (gy E) = (gx E)^(7:ℕ) * (gy E)^(3:ℕ) - algebraMap R _ E.a₂ * ((gx E)^(9:ℕ) * (gy E))
      - algebraMap R _ E.a₄ * ((gx E)^(8:ℕ) * (gy E)) - algebraMap R _ E.a₆ * ((gx E)^(7:ℕ) * (gy E))
      + algebraMap R _ E.a₁ * ((gx E)^(8:ℕ) * (gy E)^(2:ℕ))
      + algebraMap R _ E.a₃ * ((gx E)^(7:ℕ) * (gy E)^(2:ℕ)) := by
    rw [hN2]; ring
  have hI3 : (gx E)^(9:ℕ) * (gy E)^(2:ℕ) = (gx E)^(6:ℕ) * (gy E)^(4:ℕ) - algebraMap R _ E.a₂ * ((gx E)^(8:ℕ) * (gy E)^(2:ℕ))
      - algebraMap R _ E.a₄ * ((gx E)^(7:ℕ) * (gy E)^(2:ℕ)) - algebraMap R _ E.a₆ * ((gx E)^(6:ℕ) * (gy E)^(2:ℕ))
      + algebraMap R _ E.a₁ * ((gx E)^(7:ℕ) * (gy E)^(3:ℕ))
      + algebraMap R _ E.a₃ * ((gx E)^(6:ℕ) * (gy E)^(3:ℕ)) := by
    rw [hN3]; ring
  have hI4 : (gx E)^(8:ℕ) * (gy E)^(3:ℕ) = (gx E)^(5:ℕ) * (gy E)^(5:ℕ) - algebraMap R _ E.a₂ * ((gx E)^(7:ℕ) * (gy E)^(3:ℕ))
      - algebraMap R _ E.a₄ * ((gx E)^(6:ℕ) * (gy E)^(3:ℕ)) - algebraMap R _ E.a₆ * ((gx E)^(5:ℕ) * (gy E)^(3:ℕ))
      + algebraMap R _ E.a₁ * ((gx E)^(6:ℕ) * (gy E)^(4:ℕ))
      + algebraMap R _ E.a₃ * ((gx E)^(5:ℕ) * (gy E)^(4:ℕ)) := by
    rw [hN4]; ring
  have hI5 : (gx E)^(12:ℕ) = (gx E)^(9:ℕ) * (gy E)^(2:ℕ) - algebraMap R _ E.a₂ * (gx E)^(11:ℕ)
      - algebraMap R _ E.a₄ * (gx E)^(10:ℕ) - algebraMap R _ E.a₆ * (gx E)^(9:ℕ)
      + algebraMap R _ E.a₁ * ((gx E)^(10:ℕ) * (gy E)) + algebraMap R _ E.a₃ * ((gx E)^(9:ℕ) * (gy E)) := by
    rw [hN5]; ring
  have hI6 : (gx E)^(11:ℕ) * (gy E) = (gx E)^(8:ℕ) * (gy E)^(3:ℕ) - algebraMap R _ E.a₂ * ((gx E)^(10:ℕ) * (gy E))
      - algebraMap R _ E.a₄ * ((gx E)^(9:ℕ) * (gy E)) - algebraMap R _ E.a₆ * ((gx E)^(8:ℕ) * (gy E))
      + algebraMap R _ E.a₁ * ((gx E)^(9:ℕ) * (gy E)^(2:ℕ))
      + algebraMap R _ E.a₃ * ((gx E)^(8:ℕ) * (gy E)^(2:ℕ)) := by
    rw [hN6]; ring
  -- ## Monomials `x^a y^b` with `a + b ≤ 10`, `b ≤ 5`: literal fivefold products
  have hx0 : (gx E)^(0:ℕ) ∈ Tsp E :=
    Tmem E 0 0 0 0 0 (by simp only [sdBas_apply_zero]; ring)
  have hx1 : (gx E)^(1:ℕ) ∈ Tsp E :=
    Tmem E 1 0 0 0 0 (by simp only [sdBas_apply_zero, sdBas_apply_one]; ring)
  have hx2 : (gx E)^(2:ℕ) ∈ Tsp E :=
    Tmem E 3 0 0 0 0 (by simp only [sdBas_apply_zero, sdBas_apply_three]; ring)
  have hx3 : (gx E)^(3:ℕ) ∈ Tsp E :=
    Tmem E 1 3 0 0 0 (by simp only [sdBas_apply_zero, sdBas_apply_one, sdBas_apply_three]; ring)
  have hx4 : (gx E)^(4:ℕ) ∈ Tsp E :=
    Tmem E 3 3 0 0 0 (by simp only [sdBas_apply_zero, sdBas_apply_three]; ring)
  have hx5 : (gx E)^(5:ℕ) ∈ Tsp E :=
    Tmem E 1 3 3 0 0
      (by simp only [sdBas_apply_zero, sdBas_apply_one, sdBas_apply_three]; ring)
  have hx6 : (gx E)^(6:ℕ) ∈ Tsp E :=
    Tmem E 3 3 3 0 0 (by simp only [sdBas_apply_zero, sdBas_apply_three]; ring)
  have hx7 : (gx E)^(7:ℕ) ∈ Tsp E :=
    Tmem E 1 3 3 3 0
      (by simp only [sdBas_apply_zero, sdBas_apply_one, sdBas_apply_three]; ring)
  have hx8 : (gx E)^(8:ℕ) ∈ Tsp E :=
    Tmem E 3 3 3 3 0 (by simp only [sdBas_apply_zero, sdBas_apply_three]; ring)
  have hx9 : (gx E)^(9:ℕ) ∈ Tsp E :=
    Tmem E 1 3 3 3 3 (by simp only [sdBas_apply_one, sdBas_apply_three]; ring)
  have hx10 : (gx E)^(10:ℕ) ∈ Tsp E :=
    Tmem E 3 3 3 3 3 (by simp only [sdBas_apply_three]; ring)
  have hy0 : (gx E)^(0:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 2 0 0 0 0 (by simp only [sdBas_apply_zero, sdBas_apply_two]; ring)
  have hy1 : (gx E)^(1:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 4 0 0 0 0
      (by simp only [sdBas_apply_zero, sdBas_apply_four]; ring)
  have hy2 : (gx E)^(2:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 1 4 0 0 0
      (by simp only [sdBas_apply_zero, sdBas_apply_one, sdBas_apply_four]; ring)
  have hy3 : (gx E)^(3:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 3 4 0 0 0
      (by simp only [sdBas_apply_zero, sdBas_apply_three, sdBas_apply_four]; ring)
  have hy4 : (gx E)^(4:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 1 3 4 0 0
      (by simp only [sdBas_apply_zero, sdBas_apply_one, sdBas_apply_three, sdBas_apply_four]; ring)
  have hy5 : (gx E)^(5:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 3 3 4 0 0
      (by simp only [sdBas_apply_zero, sdBas_apply_three, sdBas_apply_four]; ring)
  have hy6 : (gx E)^(6:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 1 3 3 4 0
      (by simp only [sdBas_apply_zero, sdBas_apply_one, sdBas_apply_three, sdBas_apply_four]; ring)
  have hy7 : (gx E)^(7:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 3 3 3 4 0
      (by simp only [sdBas_apply_zero, sdBas_apply_three, sdBas_apply_four]; ring)
  have hy8 : (gx E)^(8:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 1 3 3 3 4
      (by simp only [sdBas_apply_one, sdBas_apply_three, sdBas_apply_four]; ring)
  have hy9 : (gx E)^(9:ℕ) * (gy E) ∈ Tsp E :=
    Tmem E 3 3 3 3 4 (by simp only [sdBas_apply_three, sdBas_apply_four]; ring)
  have hx8y2 : (gx E)^(8:ℕ) * (gy E)^(2:ℕ) ∈ Tsp E :=
    Tmem E 3 3 3 4 4 (by simp only [sdBas_apply_three, sdBas_apply_four]; ring)
  have hx7y2 : (gx E)^(7:ℕ) * (gy E)^(2:ℕ) ∈ Tsp E :=
    Tmem E 1 3 3 4 4
      (by simp only [sdBas_apply_one, sdBas_apply_three, sdBas_apply_four]; ring)
  have hx6y2 : (gx E)^(6:ℕ) * (gy E)^(2:ℕ) ∈ Tsp E :=
    Tmem E 3 3 4 4 0
      (by simp only [sdBas_apply_zero, sdBas_apply_three, sdBas_apply_four]; ring)
  have hx7y3 : (gx E)^(7:ℕ) * (gy E)^(3:ℕ) ∈ Tsp E :=
    Tmem E 4 4 4 3 3 (by simp only [sdBas_apply_three, sdBas_apply_four]; ring)
  have hx6y3 : (gx E)^(6:ℕ) * (gy E)^(3:ℕ) ∈ Tsp E :=
    Tmem E 3 3 4 4 2
      (by simp only [sdBas_apply_two, sdBas_apply_three, sdBas_apply_four]; ring)
  have hx5y3 : (gx E)^(5:ℕ) * (gy E)^(3:ℕ) ∈ Tsp E :=
    Tmem E 1 3 4 4 2
      (by simp only [sdBas_apply_one, sdBas_apply_two, sdBas_apply_three, sdBas_apply_four]; ring)
  have hx6y4 : (gx E)^(6:ℕ) * (gy E)^(4:ℕ) ∈ Tsp E :=
    Tmem E 3 4 4 4 4 (by simp only [sdBas_apply_three, sdBas_apply_four]; ring)
  have hx5y4 : (gx E)^(5:ℕ) * (gy E)^(4:ℕ) ∈ Tsp E :=
    Tmem E 1 4 4 4 4 (by simp only [sdBas_apply_one, sdBas_apply_four]; ring)
  have hx5y5 : (gx E)^(5:ℕ) * (gy E)^(5:ℕ) ∈ Tsp E :=
    Tmem E 4 4 4 4 4 (by simp only [sdBas_apply_four]; ring)
  -- ## The four top monomials
  have hx11 : (gx E)^(11:ℕ) ∈ Tsp E := by
    rw [hI1]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx8y2 (hsmT E E.a₂ hx10)) (hsmT E E.a₄ hx9)) (hsmT E E.a₆ hx8))
      (hsmT E E.a₁ hy9)) (hsmT E E.a₃ hy8)
  have hx10y : (gx E)^(10:ℕ) * (gy E) ∈ Tsp E := by
    rw [hI2]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx7y3 (hsmT E E.a₂ hy9)) (hsmT E E.a₄ hy8)) (hsmT E E.a₆ hy7))
      (hsmT E E.a₁ hx8y2)) (hsmT E E.a₃ hx7y2)
  have hx9y2 : (gx E)^(9:ℕ) * (gy E)^(2:ℕ) ∈ Tsp E := by
    rw [hI3]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx6y4 (hsmT E E.a₂ hx8y2)) (hsmT E E.a₄ hx7y2)) (hsmT E E.a₆ hx6y2))
      (hsmT E E.a₁ hx7y3)) (hsmT E E.a₃ hx6y3)
  have hx8y3 : (gx E)^(8:ℕ) * (gy E)^(3:ℕ) ∈ Tsp E := by
    rw [hI4]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx5y5 (hsmT E E.a₂ hx7y3)) (hsmT E E.a₄ hx6y3)) (hsmT E E.a₆ hx5y3))
      (hsmT E E.a₁ hx6y4)) (hsmT E E.a₃ hx5y4)
  have hx12 : (gx E)^(12:ℕ) ∈ Tsp E := by
    rw [hI5]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx9y2 (hsmT E E.a₂ hx11)) (hsmT E E.a₄ hx10)) (hsmT E E.a₆ hx9))
      (hsmT E E.a₁ hx10y)) (hsmT E E.a₃ hy9)
  have hx11y : (gx E)^(11:ℕ) * (gy E) ∈ Tsp E := by
    rw [hI6]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ hx8y3 (hsmT E E.a₂ hx10y)) (hsmT E E.a₄ hy9)) (hsmT E E.a₆ hy8))
      (hsmT E E.a₁ hx9y2)) (hsmT E E.a₃ hx8y2)
  -- ## The generators of `Ssp`
  have hxmem : ∀ m : ℕ, m ≤ 12 → (gx E)^m ∈ Tsp E := by
    intro m hm
    interval_cases m
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
    · exact hx4
    · exact hx5
    · exact hx6
    · exact hx7
    · exact hx8
    · exact hx9
    · exact hx10
    · exact hx11
    · exact hx12
  have hxymem : ∀ m : ℕ, m ≤ 11 → (gx E)^m * (gy E) ∈ Tsp E := by
    intro m hm
    interval_cases m
    · exact hy0
    · exact hy1
    · exact hy2
    · exact hy3
    · exact hy4
    · exact hy5
    · exact hy6
    · exact hy7
    · exact hy8
    · exact hy9
    · exact hx10y
    · exact hx11y
  refine le_antisymm (Tsp_le_Ssp' E) ?_
  change Submodule.span R (Set.range (sdTF5 E)) ≤ Tsp E
  rw [Submodule.span_le]
  rintro u ⟨k, rfl⟩
  rcases k with i | j
  · rw [sdTF5_inl]
    exact hxmem _ (by have h := i.isLt; omega)
  · rw [sdTF5_inr]
    exact hxymem _ (by have h := j.isLt; omega)

end

end Work.MotK.TwRuling

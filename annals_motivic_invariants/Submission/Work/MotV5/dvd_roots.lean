import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- If a polynomial `p` over a field vanishes at the pairwise distinct points `f i`
(`hinj`), then the product of the corresponding linear factors divides `p`.
This is the standard "enough roots imply divisibility by the product" statement:
the factors `X - C (f i)` are pairwise coprime (`Polynomial.pairwise_coprime_X_sub_C`)
and each of them divides `p` (`Polynomial.dvd_iff_isRoot`). -/
lemma prod_X_sub_C_dvd_of_eval_zero {R : Type*} [Field R] {ι : Type*} [Fintype ι]
    {f : ι → R} (hinj : Function.Injective f) {p : Polynomial R}
    (hp : ∀ i, p.eval (f i) = 0) :
    (∏ i, (Polynomial.X - Polynomial.C (f i))) ∣ p := by
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · rintro i - j - hij
    exact Polynomial.pairwise_coprime_X_sub_C hinj hij
  · intro i _
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact hp i

/-- A monic polynomial `h` of degree `5` over `F` having five distinct roots
`w, w+1, w+2, w+3, w+4` in `L` divides every polynomial `Q` over `F` that also
vanishes at these five points.  Indeed `h.map` is monic of degree `5` and its five
distinct roots force `h.map = ∏ (X - C (w+i))`; each factor divides `Q.map`, so
`h.map ∣ Q.map`, and injectivity of `algebraMap F L` descends this to `h ∣ Q`. -/
theorem dvd_roots {F L : Type*} [Field F] [Field L] [Algebra F L]
    (h Q : Polynomial F) (w : L) (hh : h.Monic) (hd : h.natDegree = 5)
    (hroot : ∀ i : Fin 5, (h.map (algebraMap F L)).eval (w + ((i:ℕ):L)) = 0)
    (hinj : Function.Injective (fun i : Fin 5 => w + ((i:ℕ):L)))
    (hQ : ∀ i : Fin 5, (Q.map (algebraMap F L)).eval (w + ((i:ℕ):L)) = 0) :
    h ∣ Q := by
  let r : Fin 5 → L := fun i => w + ((i:ℕ):L)
  have hinj' : Function.Injective r := hinj
  have hroot' : ∀ i : Fin 5, (h.map (algebraMap F L)).eval (r i) = 0 := fun i => hroot i
  have hQ' : ∀ i : Fin 5, (Q.map (algebraMap F L)).eval (r i) = 0 := fun i => hQ i
  -- the product of the five linear factors divides both `h.map` and `Q.map`
  have hP_dvd_h : (∏ i : Fin 5, (Polynomial.X - Polynomial.C (r i) : Polynomial L))
      ∣ h.map (algebraMap F L) := prod_X_sub_C_dvd_of_eval_zero hinj' hroot'
  have hP_dvd_Q : (∏ i : Fin 5, (Polynomial.X - Polynomial.C (r i) : Polynomial L))
      ∣ Q.map (algebraMap F L) := prod_X_sub_C_dvd_of_eval_zero hinj' hQ'
  -- monic polynomials of the same degree, one dividing the other, are equal
  have heq : h.map (algebraMap F L)
      = ∏ i : Fin 5, (Polynomial.X - Polynomial.C (r i) : Polynomial L) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (Polynomial.monic_prod_X_sub_C r Finset.univ) (hh.map _) hP_dvd_h (by
        rw [Polynomial.Monic.natDegree_map hh, hd,
          Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
        simp)
  have hmap_dvd : h.map (algebraMap F L) ∣ Q.map (algebraMap F L) := by
    rw [heq]; exact hP_dvd_Q
  exact (Polynomial.map_dvd_map (algebraMap F L) (algebraMap F L).injective hh).mp hmap_dvd

end Work.MotV5

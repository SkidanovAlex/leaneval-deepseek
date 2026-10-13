import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.frobenius_surjective_away
import Submission.Work.DSM5b.frobenius_injective_away
import Submission.Work.DSM5b.sum_pow_p_away
import Submission.Work.DSM5b.phiPC_aux

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

namespace Work.DSM5b

/-- **The Frobenius `p`-th power map on the explicit complex, and its properties.**

`phiPC p t m` (in `PerfComplexDefs`) is the componentwise `p`-th power map
`z ↦ (fun τ => z τ ^ p)` on `PCX p t m`, which stays inside the complex by
`perfChartRing_pow_p_mem_iff`.  It is *not* `R`-linear, but it is additive (the chart rings have
`(p : R) = 0` in their localisations) and `R`-semilinear, and — the content of this statement — it
is a bijection commuting with the differential `PCd`.

Concretely:

* `PCd p t m (phiPC p t m z) = phiPC p t (m+1) (PCd p t m z)`: componentwise this is
  `(Σ i, (-1)^i • rho (z (tupDel i τ)))^p = Σ i, (-1)^i • rho ((z (tupDel i τ))^p)`, i.e. Freshman's
  dream for the sum (`(x+y)^p = x^p + y^p`, available without a `CharP` instance on the chart rings
  since `(p : Localization.Away (tS t S)) = 0`, see `perfChartRing_pow_p_mem_iff`), plus
  `rho (x^p) = (rho x)^p` (`rho` is a ring hom) and `((-1)^i)^p = (-1)^i`;
* `phiPC p t m` is surjective: the ambient localisation `Localization.Away (tS t S)` is perfect
  (`(a/t^n)^{1/p} = a^{1/p}/(t^{1/p})^n` with `a^{1/p}, t^{1/p} ∈ R` since `R` is perfect), so every
  `y ∈ perfChartRing p t S` has a `p`-th root in the ambient ring, which lies in
  `perfChartRing p t S` by the "⇒" half of `perfChartRing_pow_p_mem_iff`;
* `phiPC p t m` is injective: `x^p = y^p` gives `(x − y)^p = 0`, and the localisations of the
  reduced ring `R` are reduced;
* `phiPC p t m (r • z) = r^p • phiPC p t m z` for `r : R`: componentwise multiplicativity of the
  `p`-th power map on the localisation.

The inverse of `phiPC` is the (choice-defined) componentwise `p`-th root map `ψ`, which therefore
satisfies `ψ (r • y) = r^{1/p} • ψ y` with `r^{1/p} = (frobeniusEquiv R p).symm r`.

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`. -/
theorem phiPC_properties (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) :
    (∀ (m : ℕ) (z : PCX p t m), PCd p t m (phiPC p t m z) = phiPC p t (m + 1) (PCd p t m z)) ∧
      (∀ (m : ℕ) (z : PCX p t m), ∃ z' : PCX p t m, phiPC p t m z' = z) ∧
      (∀ (m : ℕ) (z z' : PCX p t m), phiPC p t m z = phiPC p t m z' → z = z') ∧
      (∀ (m : ℕ) (r : R) (z : PCX p t m), phiPC p t m (r • z) = r ^ p • phiPC p t m z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `PCd` commutes with the componentwise `p`-th power map
    intro m z
    funext τ
    apply Subtype.ext
    simp only [PCd_apply, phiPC_apply, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
      Algebra.smul_def, Subalgebra.coe_algebraMap, rho_phiPC_val]
    exact (sum_smul_pow_p_away p (tS t (tupRng τ)) (m + 2)
      (fun i => ↑(rho p t (tupRng_del_subset i τ) (z (tupDel i τ))))).symm
  · -- every element of the perfected chart rings has a `p`-th root
    intro m z
    refine ⟨fun τ => ⟨Classical.choose (frobenius_surjective_away p (tS t (tupRng τ)) (z τ).1),
      ?_⟩, ?_⟩
    · exact (perfChartRing_pow_p_mem_iff p t (tupRng τ) _).1 (by
        rw [Classical.choose_spec (frobenius_surjective_away p (tS t (tupRng τ)) (z τ).1)]
        exact (z τ).2)
    · funext τ
      apply Subtype.ext
      rw [phiPC_apply]
      exact Classical.choose_spec (frobenius_surjective_away p (tS t (tupRng τ)) (z τ).1)
  · -- the componentwise `p`-th power map is injective
    intro m z z' h
    funext τ
    apply Subtype.ext
    refine frobenius_injective_away p (tS t (tupRng τ)) ?_
    simpa only [phiPC_apply] using congrArg Subtype.val (congrFun h τ)
  · -- `R`-semilinearity
    intro m r z
    funext τ
    apply Subtype.ext
    rw [phiPC_apply, Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, mul_pow, ← map_pow,
      Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, phiPC_apply]

end Work.DSM5b

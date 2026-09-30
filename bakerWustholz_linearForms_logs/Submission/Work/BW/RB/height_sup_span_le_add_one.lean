import Mathlib
import Submission.Work.BW.RB.catenary_atPrime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW.RB

open scoped Classical


/-- In the local ring `R = ℂ[σ]_𝔪`, adding one generator to a proper ideal raises the height by at
most one.

Let `K = J ⊔ (a)`.  Pick a minimal prime `P` of `J` of height `ht J` (it exists because `J` has
finitely many minimal primes, and `J ≠ ⊤` so `ht J = c` is a natural number).  If `a ∈ P` then
`K ≤ P` and we are done.  Otherwise `Q`, a minimal prime of `P ⊔ (a)`, satisfies `K ≤ Q` and
`ht(Q / P) ≤ 1` (the image of `a` is a non-zero element of the domain `R / P`, so `Q / P` is a
minimal prime of the principal ideal it generates), and the catenary inequality
`ht Q ≤ ht P + ht(Q/P)` gives the claim. -/
theorem height_sup_span_le_add_one {σ : Type*} [Fintype σ]
    (𝔪 : Ideal (MvPolynomial σ ℂ)) [𝔪.IsMaximal]
    (J : Ideal (Localization.AtPrime 𝔪)) (a : Localization.AtPrime 𝔪)
    (h : J ⊔ Ideal.span {a} ≠ ⊤) :
    (J ⊔ Ideal.span {a}).height ≤ J.height + 1 := by
  classical
  rcases eq_or_ne J ⊤ with rfl | hJ
  · simp
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hJ)
  obtain ⟨P, hPprime, hJP, hPht⟩ := Ideal.exists_isPrime_height_eq hc.symm
  haveI : P.IsPrime := hPprime
  by_cases haP : a ∈ P
  · have hKP : J ⊔ Ideal.span {a} ≤ P :=
      sup_le hJP (Ideal.span_le.mpr (by simpa using haP))
    calc (J ⊔ Ideal.span {a}).height ≤ P.height := Ideal.height_mono hKP
      _ = (c : ℕ∞) := hPht
      _ ≤ J.height + 1 := by rw [hc]; exact le_add_right le_rfl
  · have hKle : J ⊔ Ideal.span {a} ≤ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
      IsLocalRing.le_maximalIdeal h
    have hale : a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
      hKle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
    have hSle : P ⊔ Ideal.span {a} ≤ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
      sup_le (IsLocalRing.le_maximalIdeal_of_isPrime P)
        (Ideal.span_le.mpr (by simpa using hale))
    have hSne : P ⊔ Ideal.span {a} ≠ ⊤ :=
      ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hSle
    obtain ⟨Q, hQmin⟩ := Ideal.nonempty_minimalPrimes hSne
    haveI : Q.IsPrime := hQmin.isPrime
    have hPQ : P ≤ Q := le_trans le_sup_left hQmin.le
    have hKQ : J ⊔ Ideal.span {a} ≤ Q := le_trans (sup_le_sup hJP le_rfl) hQmin.le
    calc (J ⊔ Ideal.span {a}).height ≤ Q.height := Ideal.height_mono hKQ
      _ ≤ P.height + (Q.map (Ideal.Quotient.mk P)).height := catenary_atPrime 𝔪 hPQ
      _ ≤ P.height + 1 := add_le_add le_rfl (Ideal.map_height_le_one_of_mem_minimalPrimes hQmin)
      _ = J.height + 1 := by rw [hPht, hc]

end Work.BW.RB

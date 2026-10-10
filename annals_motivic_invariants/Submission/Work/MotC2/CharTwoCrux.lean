import Mathlib
import Submission.Work.MotC2.CruxSubst
import Submission.Work.MotC2.RatFuncIntegral
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

set_option linter.style.haveILetI false

/-- Auxiliary crux for `CharTwoCrux` (case `q ∉ L[X]`).

Let `L` be a field of characteristic two, `e = C a₁ * (X - C x₀)` with `a₁ ≠ 0`, and
`c ∈ L[X]`.  If `Y, B, N ∈ L[X]` satisfy `Y² + e·B·Y + B²c = e²N` and `e ∤ B`, then there is
`s ∈ L` with `e² ∣ c - s² - s·e`. -/
theorem charTwoCruxAux {L : Type*} [Field L] (h2 : (2 : L) = 0)
    (e c B Y N : Polynomial L) (x₀ a₁ : L) (ha₁ : a₁ ≠ 0)
    (he : e = Polynomial.C a₁ * (Polynomial.X - Polynomial.C x₀))
    (hB : ¬ e ∣ B)
    (heq : Y ^ 2 + e * B * Y + B ^ 2 * c = e ^ 2 * N) :
    ∃ s : L, e ^ 2 ∣ c - Polynomial.C s * Polynomial.C s - Polynomial.C s * e := by
  haveI : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  set p : Polynomial L := Polynomial.X - Polynomial.C x₀ with hpset
  have hp_prime : Prime p := by rw [hpset]; exact Polynomial.prime_X_sub_C x₀
  have hu : IsUnit (Polynomial.C a₁ : Polynomial L) := by
    rw [Polynomial.isUnit_C]; exact isUnit_iff_ne_zero.mpr ha₁
  have hAssoc : Associated p e := ⟨hu.unit, by rw [hu.unit_spec, he]; ring⟩
  have hBp : ¬ p ∣ B := fun h => hB ((hAssoc.dvd_iff_dvd_left).mp h)
  have hdiv1 : p ∣ Y ^ 2 + B ^ 2 * c := by
    have hpdiv : p ∣ e := ⟨Polynomial.C a₁, by rw [he]; ring⟩
    have hfac : Y ^ 2 + B ^ 2 * c = e * (e * N - B * Y) := by
      linear_combination (norm := first | refl_ring1 | ring1) heq
    rw [hfac]
    exact dvd_mul_of_dvd_left hpdiv _
  have hroot : Polynomial.eval x₀ (Y ^ 2 + B ^ 2 * c) = 0 := by
    have hdiv1' := hdiv1
    rw [hpset] at hdiv1'
    have h := Polynomial.dvd_iff_isRoot.mp hdiv1'
    rwa [Polynomial.IsRoot.def] at h
  have ht : Polynomial.eval x₀ B ≠ 0 := by
    intro h
    exact hBp (by rw [hpset, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]; exact h)
  set s : L := Polynomial.eval x₀ Y / Polynomial.eval x₀ B with hsset
  have hsB : s * Polynomial.eval x₀ B = Polynomial.eval x₀ Y := by
    rw [hsset]; exact div_mul_cancel₀ _ ht
  have hdiv2 : p ∣ Y - Polynomial.C s * B := by
    have key : (Polynomial.X - Polynomial.C x₀) ∣ Y - Polynomial.C s * B := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      rw [hsB, sub_self]
    rwa [← hpset] at key
  obtain ⟨Y₁, hY₁⟩ := hdiv2
  have hY : Y = Polynomial.C s * B + p * Y₁ := by rw [← hY₁]; ring
  have hcs : p ^ 2 ∣ B ^ 2 * (Polynomial.C s * Polynomial.C s
      + Polynomial.C s * (Polynomial.C a₁ * p) + c) := by
    refine CruxSubst a₁ B Y Y₁ p c N s hY ?_
    rw [he] at heq
    exact heq
  have hZ : p ^ 2 ∣ Polynomial.C s * Polynomial.C s + Polynomial.C s * e + c := by
    have hBp2 : ¬ p ∣ B ^ 2 := fun h => hBp (hp_prime.dvd_of_dvd_pow h)
    have hZeq : Polynomial.C s * Polynomial.C s + Polynomial.C s * e + c
        = Polynomial.C s * Polynomial.C s + Polynomial.C s * (Polynomial.C a₁ * p) + c := by
      rw [he]
    rw [hZeq]
    exact hp_prime.pow_dvd_of_dvd_mul_left 2 hBp2 hcs
  have hZ' : e ^ 2 ∣ Polynomial.C s * Polynomial.C s + Polynomial.C s * e + c := by
    have hAssoc2 : Associated (p ^ 2) (e ^ 2) :=
      ⟨(hu.pow 2).unit, by rw [(hu.pow 2).unit_spec, he]; ring⟩
    exact (hAssoc2.dvd_iff_dvd_left).mp hZ
  refine ⟨s, ?_⟩
  have hconv : c - Polynomial.C s * Polynomial.C s - Polynomial.C s * e
      = Polynomial.C s * Polynomial.C s + Polynomial.C s * e + c := by
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]; ring
  rw [hconv]
  exact hZ'

/-- **Characteristic-two valuation step.**

Let `L` be a field of characteristic two, `e = a₁X + a₃` (with `a₁ ≠ 0`) and
`c = X³ + a₂X² + a₄X + a₆` in `L[X]`.  Assume the nonsingularity condition
`¬ ∃ s : L, e² ∣ c - s² - s·e`.  If `p, q ∈ L(X) = RatFunc L` satisfy `q·e ∈ L[X]` and
`p² + p·q·e + q²·c ∈ L[X]`, then `p, q ∈ L[X]`.

Route.  Case `q ∈ L[X]`: then `X² + (qe)X + (q²c - N)` is monic over `L[X]` with root `p`, and
`p ∈ Frac(L[X])`, so `p ∈ L[X]` by `IsIntegrallyClosed (Polynomial L)`
(`GCDMonoid.toIsIntegrallyClosed`, since `Polynomial L` is a UFD).

Otherwise `q ∉ L[X]`.  From `q·e = B` with `B ∈ L[X]` we get `q = B/e`; moreover `e ∤ B`
(else `q = B/e ∈ L[X]`).  Put `Y := e·p ∈ RatFunc L`.  Multiplying the norm condition
`p² + p·B + q²c = N` by `e²` and using `q² = B²/e²` gives `Y² + (eB)·Y + B²c = e²N`, a monic
quadratic over `L[X]` with root `Y`; hence `Y ∈ L[X]` (again `IsIntegrallyClosed`).  Modulo
`e` this gives `e ∣ Y² + B²c`.  Writing `e = a₁(X - x₀)` with `x₀ = -a₃/a₁` and
`Y = C r + eY₁`, `B = C t + eB₁` with `r = Y(x₀)`, `t = B(x₀) ≠ 0`, the congruence gives
`r² + t²c(x₀) = 0`, so `s := r/t ∈ L` satisfies `s² + s·e(x₀) = c(x₀)`.  Substituting
`Y = C s·B + eY₁` into `Y² + (eB)Y + B²c = e²N`, all cross terms vanish in characteristic two
and one gets `e² ∣ B²(s² + se + c)`; as `e` is prime and `e ∤ B`, this forces
`e² ∣ c - s² - s·e`, contradicting the hypothesis. -/
theorem CharTwoCrux (L : Type*) [Field L] (h2 : (2 : L) = 0)
    (a₁ a₂ a₃ a₄ a₆ : L) (ha₁ : a₁ ≠ 0)
    (hns : ¬ ∃ s : L, (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃ : Polynomial L) ^ 2 ∣
        (Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₄ * Polynomial.X
            + Polynomial.C a₆) - Polynomial.C s * Polynomial.C s
          - Polynomial.C s * (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃))
    (p q : RatFunc L)
    (hq : ∃ B : Polynomial L,
        q * algebraMap (Polynomial L) (RatFunc L)
              (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃)
          = algebraMap (Polynomial L) (RatFunc L) B)
    (hn : ∃ N : Polynomial L,
        p ^ 2 + p * (q * algebraMap (Polynomial L) (RatFunc L)
              (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃))
          + q ^ 2 * algebraMap (Polynomial L) (RatFunc L)
              (Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2
                + Polynomial.C a₄ * Polynomial.X + Polynomial.C a₆)
          = algebraMap (Polynomial L) (RatFunc L) N) :
    (∃ P : Polynomial L, p = algebraMap (Polynomial L) (RatFunc L) P) ∧
      (∃ Q : Polynomial L, q = algebraMap (Polynomial L) (RatFunc L) Q) := by
  set e : Polynomial L := Polynomial.C a₁ * Polynomial.X + Polynomial.C a₃ with he
  set c : Polynomial L := Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2
      + Polynomial.C a₄ * Polynomial.X + Polynomial.C a₆ with hc
  obtain ⟨B, hB⟩ := hq
  obtain ⟨N, hN⟩ := hn
  by_cases hqmem : ∃ Q : Polynomial L, q = algebraMap (Polynomial L) (RatFunc L) Q
  · obtain ⟨Q, rfl⟩ := hqmem
    have hquad : p ^ 2 + algebraMap (Polynomial L) (RatFunc L) (Q * e) * p
        + algebraMap (Polynomial L) (RatFunc L) (Q ^ 2 * c - N) = 0 := by
      have h1 : algebraMap (Polynomial L) (RatFunc L) (Q * e)
          = algebraMap _ _ Q * algebraMap _ _ e := by rw [map_mul]
      have h2 : algebraMap (Polynomial L) (RatFunc L) (Q ^ 2 * c - N)
          = (algebraMap _ _ Q) ^ 2 * algebraMap _ _ c - algebraMap _ _ N := by
        rw [map_sub, map_mul, map_pow]
      rw [h1, h2]
      linear_combination (norm := first | refl_ring1 | ring1) hN
    obtain ⟨P, hP⟩ := RatFuncIntegral p (Q * e) (Q ^ 2 * c - N) hquad
    exact ⟨⟨P, hP.symm⟩, ⟨Q, rfl⟩⟩
  · exfalso
    have he' : e = Polynomial.C a₁ * (Polynomial.X - Polynomial.C (-a₃ / a₁)) := by
      rw [he]
      have hax : a₁ * (-a₃ / a₁) = -a₃ := by field_simp
      rw [mul_sub, ← Polynomial.C_mul, hax, Polynomial.C_neg, sub_neg_eq_add]
    have he0 : e ≠ 0 := by
      rw [he']
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr ha₁) (Polynomial.monic_X_sub_C _).ne_zero
    have he0' : algebraMap (Polynomial L) (RatFunc L) e ≠ 0 :=
      fun h => he0 (RatFunc.algebraMap_injective L (by rw [h, map_zero]))
    have hB_ne : ¬ e ∣ B := by
      intro hdvd
      obtain ⟨B', hB'⟩ := hdvd
      apply hqmem
      refine ⟨B', ?_⟩
      have h1 : q * algebraMap _ _ e = algebraMap _ _ B' * algebraMap _ _ e := by
        rw [hB, hB', map_mul]; ring
      exact mul_right_cancel₀ he0' h1
    set Y : RatFunc L := algebraMap (Polynomial L) (RatFunc L) e * p with hYset
    have key : Y ^ 2 + algebraMap _ _ (e * B) * Y + algebraMap _ _ (B ^ 2 * c)
        = algebraMap _ _ (e ^ 2 * N) := by
      rw [hYset]
      have hB'' : algebraMap (Polynomial L) (RatFunc L) B = q * algebraMap _ _ e := hB.symm
      simp only [map_mul, map_pow]
      rw [hB'']
      linear_combination (norm := first | refl_ring1 | ring1) (algebraMap (Polynomial L) (RatFunc L) e) ^ 2 * hN
    have hYint : ∃ Yp : Polynomial L, algebraMap (Polynomial L) (RatFunc L) Yp = Y := by
      refine RatFuncIntegral Y (e * B) (B ^ 2 * c - e ^ 2 * N) ?_
      rw [map_sub]
      linear_combination (norm := first | refl_ring1 | ring1) key
    obtain ⟨Yp, hYp⟩ := hYint
    have heq : Yp ^ 2 + (e * B) * Yp + B ^ 2 * c = e ^ 2 * N := by
      have hkey' := key
      simp only [map_mul, map_pow] at hkey'
      rw [← hYp] at hkey'
      have hbig : algebraMap (Polynomial L) (RatFunc L)
          (Yp ^ 2 + (e * B) * Yp + B ^ 2 * c - e ^ 2 * N) = 0 := by
        simp only [map_sub, map_add, map_mul, map_pow]
        linear_combination (norm := first | refl_ring1 | ring1) hkey'
      have hzero : Yp ^ 2 + (e * B) * Yp + B ^ 2 * c - e ^ 2 * N = 0 :=
        RatFunc.algebraMap_injective L (by rw [hbig, map_zero])
      linear_combination (norm := first | refl_ring1 | ring1) hzero
    obtain ⟨s, hs⟩ := charTwoCruxAux h2 e c B Yp N (-a₃ / a₁) a₁ ha₁ he' hB_ne heq
    exact hns ⟨s, hs⟩

end Work.MotC2

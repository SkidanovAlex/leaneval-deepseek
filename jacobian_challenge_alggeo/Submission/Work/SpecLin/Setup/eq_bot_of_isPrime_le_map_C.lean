import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Setup

/-- In a total divisibility (pre)order, a nonempty finite set has an element dividing all of its
elements. -/
lemma Finset.exists_dvd_of_dvd_total {R : Type*} [Monoid R] [PreValuationRing R]
    (s : Finset R) (hs : s.Nonempty) : ∃ c ∈ s, ∀ a ∈ s, c ∣ a := by
  classical
  induction s using Finset.induction with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs'
    · exact ⟨a, Finset.mem_insert_self a ∅, by intro x hx; simp at hx; subst hx; exact dvd_rfl⟩
    · obtain ⟨c, hc, hcd⟩ := ih hs'
      rcases ValuationRing.dvd_total c a with hca | hac
      · refine ⟨c, Finset.mem_insert_of_mem hc, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hca
        · exact hcd x hx
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact dvd_rfl
        · exact dvd_trans hac (hcd x hx)

/-- In a valuation ring `V`, a prime `𝔞 ⊆ V[X]` whose contraction to `V` is `⊥` and which is
contained in `m·V[X]` for a proper ideal `m` must be `⊥`.

Proof: suppose `0 ≠ f ∈ 𝔞`.  All coefficients of `f` lie in `m ⊆ V`.  Since `V` is a valuation
ring, divisibility on `V` is total (`ValuationRing.dvd_total`), so among the (finitely many)
coefficients of `f` there is one, `c`, dividing all of them.  Then `c ≠ 0` and `f = C c * g` for
some `g ∈ V[X]`; moreover `g ∈ 𝔞` because `𝔞` is prime and `c ∉ 𝔞` (`𝔞.under V = ⊥` and `c ≠ 0`
force `C c ∉ 𝔞`), while `g ∉ m·V[X]` because the `X^j`-th coefficient of `g` is `1 ∉ m`.
Contradiction. -/
theorem eq_bot_of_isPrime_le_map_C {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    {m : Ideal V} (hm : m ≠ ⊤) {𝔞 : Ideal (Polynomial V)}
    (h𝔞 : 𝔞.IsPrime) (hunder : 𝔞.under V = ⊥)
    (hle : 𝔞 ≤ Ideal.map (Polynomial.C : V →+* Polynomial V) m) : 𝔞 = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  -- The (nonempty) set of nonzero coefficients of `f` has an element dividing all others.
  have hsp : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hf0 (Polynomial.support_eq_empty.mp h)
  obtain ⟨c, hcS, hmax⟩ :=
    Finset.exists_dvd_of_dvd_total (f.support.image f.coeff) (hsp.image f.coeff)
  obtain ⟨k, hk, hkc⟩ := Finset.mem_image.mp hcS
  have hcne : c ≠ 0 := by
    rw [← hkc]
    exact Polynomial.mem_support_iff.mp hk
  -- `c` divides every coefficient of `f`.
  have hdiv : ∀ j, c ∣ f.coeff j := by
    intro j
    by_cases hj : j ∈ f.support
    · exact hmax (f.coeff j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    · have hj0 : f.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
      rw [hj0]
      exact dvd_zero c
  -- Hence `f = C c * g` for some `g`, with `g.coeff k = 1` since `f.coeff k = c ≠ 0`.
  obtain ⟨g, hg⟩ := (Polynomial.C_dvd_iff_dvd_coeff c f).mpr hdiv
  have hgk : g.coeff k = 1 := by
    have h1 : c * g.coeff k = f.coeff k := by
      rw [← Polynomial.coeff_C_mul, hg]
    rw [hkc] at h1
    exact mul_left_cancel₀ hcne (by rw [mul_one]; exact h1)
  -- `C c ∉ 𝔞` because `𝔞.under V = ⊥` and `c ≠ 0`.
  have hCc_not : Polynomial.C c ∉ 𝔞 := by
    intro hCc
    have hmem : c ∈ 𝔞.under V := by
      rw [Ideal.mem_under, Polynomial.algebraMap_eq]
      exact hCc
    rw [hunder, Ideal.mem_bot] at hmem
    exact hcne hmem
  -- Since `𝔞` is prime and `f = C c * g ∈ 𝔞`, we get `g ∈ 𝔞`.
  have hgf : g ∈ 𝔞 := by
    have : Polynomial.C c * g ∈ 𝔞 := by rw [← hg]; exact hf
    rcases h𝔞.mem_or_mem this with h | h
    · exact absurd h hCc_not
    · exact h
  -- But then `1 = g.coeff k ∈ m`, contradicting that `m` is proper.
  have h1m : (1 : V) ∈ m := by
    have hgm : g ∈ Ideal.map (Polynomial.C : V →+* Polynomial V) m := hle hgf
    have hmk := (Ideal.mem_map_C_iff.mp hgm) k
    rwa [hgk] at hmk
  exact hm (Ideal.eq_top_iff_one m |>.mpr h1m)

end Work.SpecLin.Setup

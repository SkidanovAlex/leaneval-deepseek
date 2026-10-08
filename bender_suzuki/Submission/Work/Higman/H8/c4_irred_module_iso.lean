import Mathlib
import Submission.Work.Higman.H8.Defs
import Submission.Work.Higman.H8.Prelim
import Submission.Work.Higman.RedAux.xi_irreducible_module_scalar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The irreducible `𝔽₂[x]`-module attached to a finite field

Let `S` be a finite elementary abelian `2`-group of order `2 ^ n` (`n ≥ 2`) carrying an
automorphism `x` with no non-trivial invariant subspace, and let `F` be any finite field of
characteristic two with `|F| = 2 ^ n`.  Then `S` is isomorphic, as an additive group, to `F` in
such a way that `x` becomes multiplication by an element `σ ∈ F` which generates `F` over `𝔽₂`;
in particular `σ ≠ 1` and `σ ^ (2 ^ k) ≠ σ` for `1 ≤ k < n`.
-/

namespace Work.Higman.H8

set_option linter.style.haveILetI false

open Polynomial

/-- If `e : V ≃+ F` is an additive isomorphism intertwining an endomorphism `ξ` of the
`𝔽₂`-vector space `V` with multiplication by `σ ∈ F`, then it intertwines the action of every
polynomial in `ξ` with the corresponding polynomial in `σ`. -/
theorem aeval_addEquiv_compat {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {F : Type} [CommRing F] [Algebra (ZMod 2) F]
    (ξ : V →ₗ[ZMod 2] V) (σ : F) (e : V ≃+ F)
    (he : ∀ v : V, e (ξ v) = σ * e v) (p : Polynomial (ZMod 2)) (v : V) :
    e ((Polynomial.aeval ξ) p v) = (Polynomial.aeval σ) p * e v := by
  have hsmul : ∀ (c : ZMod 2) (w : V), e (c • w) = c • e w := by
    intro c w
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with hc | hc <;> subst hc <;> simp
  revert v
  induction p using Polynomial.induction_on with
  | C a =>
      intro v
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        LinearMap.smul_apply, Module.End.one_apply, hsmul a v, Algebra.smul_def]
  | add p q hp hq =>
      intro v
      simp only [map_add, LinearMap.add_apply, hp v, hq v, add_mul]
  | monomial n a ih =>
      intro v
      have hstep : (Polynomial.aeval ξ) (Polynomial.C a * Polynomial.X ^ (n + 1)) v
          = (Polynomial.aeval ξ) (Polynomial.C a * Polynomial.X ^ n) (ξ v) := by
        have hpoly : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (ZMod 2))
            = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by rw [pow_succ]; ring
        rw [hpoly, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      have hstep2 : (Polynomial.aeval (R := ZMod 2) σ)
              (Polynomial.C a * Polynomial.X ^ (n + 1))
          = (Polynomial.aeval (R := ZMod 2) σ) (Polynomial.C a * Polynomial.X ^ n) * σ := by
        have hpoly : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial (ZMod 2))
            = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by rw [pow_succ]; ring
        rw [hpoly, map_mul, Polynomial.aeval_X]
      rw [hstep, ih (ξ v), he v, hstep2, mul_assoc]

/-- The range of `p ↦ p(x) v` is everything when `x` has no non-trivial invariant subspace and
`v ≠ 0`: this is the cyclicity of an irreducible module. -/
theorem range_evalAt_eq_top {S : Type} [AddCommGroup S] [Module (ZMod 2) S]
    (x : S ≃ₗ[ZMod 2] S)
    (hirr : ∀ U : Submodule (ZMod 2) S, (∀ s ∈ U, x s ∈ U) → U = ⊥ ∨ U = ⊤)
    {v : S} (hv : v ≠ 0) :
    LinearMap.range (evalAt (x : S →ₗ[ZMod 2] S) v) = ⊤ := by
  rw [evalAt_range_eq_span]
  rcases hirr (Submodule.span (ZMod 2) (Set.range (fun k : ℕ => (x ^ k) v)))
    (span_orbit_invariant x v) with h | h
  · exfalso
    have hvU : v ∈ Submodule.span (ZMod 2) (Set.range (fun k : ℕ => (x ^ k) v)) :=
      Submodule.subset_span ⟨0, by simp⟩
    rw [h, Submodule.mem_bot] at hvU
    exact hv hvU
  · exact h

/-- `σ` generates `F` over `𝔽₂` as soon as it is the scalar attached to an irreducible module
via an additive isomorphism `e : S ≃+ F`. -/
theorem range_aeval_eq_top {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    {S : Type} [AddCommGroup S] [Module (ZMod 2) S]
    (x : S ≃ₗ[ZMod 2] S)
    (hirr : ∀ U : Submodule (ZMod 2) S, (∀ s ∈ U, x s ∈ U) → U = ⊥ ∨ U = ⊤)
    (σ : F) (e : S ≃+ F) (he : ∀ s : S, e (x s) = σ * e s) :
    (Polynomial.aeval (R := ZMod 2) σ).range = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [AlgHom.mem_range]
  let v₀ : S := e.symm 1
  have hv₀ : v₀ ≠ 0 := by
    intro h0
    have h1 : e v₀ = (0 : F) := by rw [h0, map_zero]
    rw [show e v₀ = 1 from e.apply_symm_apply 1] at h1
    exact one_ne_zero h1
  have hcyc := range_evalAt_eq_top x hirr hv₀
  have hs : e.symm y ∈ LinearMap.range (evalAt (x : S →ₗ[ZMod 2] S) v₀) := by
    rw [hcyc]; exact Submodule.mem_top
  obtain ⟨p, hp⟩ := hs
  refine ⟨p, ?_⟩
  have hc := aeval_addEquiv_compat (x : S →ₗ[ZMod 2] S) σ e he p v₀
  have hξ : (Polynomial.aeval (x : S →ₗ[ZMod 2] S)) p v₀ = e.symm y := hp
  calc (Polynomial.aeval (R := ZMod 2) σ) p
      = (Polynomial.aeval (R := ZMod 2) σ) p * 1 := (mul_one _).symm
    _ = (Polynomial.aeval (R := ZMod 2) σ) p * e v₀ := by rw [e.apply_symm_apply 1]
    _ = e ((Polynomial.aeval (x : S →ₗ[ZMod 2] S)) p v₀) := hc.symm
    _ = e (e.symm y) := by rw [hξ]
    _ = y := e.apply_symm_apply y

/-- If `σ ∈ F` generates the finite field `F` of characteristic two (which has `2 ^ n` elements),
then `σ ≠ 1` and `σ ^ (2 ^ k) ≠ σ` for `1 ≤ k < n`. -/
theorem sigma_pow_frob_ne {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    [CharP F 2] [Algebra (ZMod 2) F] (hcard : Fintype.card F = 2 ^ n) (σ : F)
    (hrange : (Polynomial.aeval (R := ZMod 2) σ).range = ⊤) :
    σ ≠ 1 ∧ ∀ k : ℕ, 1 ≤ k → k < n → σ ^ (2 ^ k) ≠ σ := by
  classical
  have hfin : Module.finrank (ZMod 2) F = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_zmod] at h
    rw [← Fintype.card_eq_nat_card, hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have halg : IsAlgebraic (ZMod 2) σ := IsAlgebraic.of_finite (ZMod 2) σ
  have hS : ∀ x ∈ ({σ} : Set F), IsAlgebraic (ZMod 2) x := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact halg
  have hadj : IntermediateField.adjoin (ZMod 2) ({σ} : Set F) = ⊤ := by
    rw [IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (S := {σ}) hS]
    rw [Algebra.adjoin_singleton_eq_range_aeval (ZMod 2) σ]
    exact hrange
  have hmin : (minpoly (ZMod 2) σ).natDegree = n := by
    have h := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) σ).mp hadj
    rwa [hfin] at h
  have hperp : Irreducible (minpoly (ZMod 2) σ) :=
    minpoly.irreducible (IsIntegral.of_finite (ZMod 2) σ)
  have hpow : ∀ k : ℕ, 1 ≤ k → k < n → σ ^ (2 ^ k) ≠ σ := by
    intro k hk1 hkn hcon
    have hdvd : minpoly (ZMod 2) σ ∣
        (Polynomial.X : Polynomial (ZMod 2)) ^ (Nat.card (ZMod 2)) ^ k - Polynomial.X := by
      rw [minpoly.dvd_iff]
      rw [map_sub, map_pow, Polynomial.aeval_X, Nat.card_zmod]
      rw [hcon, sub_self]
    have hnd := Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hperp hdvd
    rw [hmin] at hnd
    have hk0 : k = 0 := Nat.eq_zero_of_dvd_of_lt hnd hkn
    omega
  refine ⟨?_, hpow⟩
  intro h1
  exact hpow 1 le_rfl (by omega) (by rw [h1]; norm_num)

theorem c4_irred_module_iso {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F]
    [DecidableEq F] [CharP F 2] (hcard : Fintype.card F = 2 ^ n)
    {S : Type} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]
    (hS : Nat.card S = 2 ^ n) (x : S ≃ₗ[ZMod 2] S)
    (hirr : ∀ U : Submodule (ZMod 2) S, (∀ s ∈ U, x s ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (sig : F) (e : S ≃+ F),
      sig ≠ 1 ∧ (∀ k : ℕ, 1 ≤ k → k < n → sig ^ (2 ^ k) ≠ sig) ∧
      (∀ s : S, e (x s) = sig * e s) := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨s0, e0, hs0, he0⟩ := Work.Higman.RedAux.xi_module_scalar hn1 hS x hirr
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hGFcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  let χ : GaloisField 2 n ≃+* F := FiniteField.ringEquivOfCardEq (by rw [hGFcard, hcard])
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let sig : F := χ s0
  let e : S ≃+ F := e0.trans χ.toAddEquiv
  have he : ∀ s : S, e (x s) = sig * e s := by
    intro s
    change χ (e0 (x s)) = χ s0 * χ (e0 s)
    rw [he0 s, map_mul]
  have hgen : (Polynomial.aeval (R := ZMod 2) sig).range = ⊤ :=
    range_aeval_eq_top x hirr sig e he
  obtain ⟨hsig1, hpow⟩ := sigma_pow_frob_ne hn hcard sig hgen
  exact ⟨sig, e, hsig1, hpow, he⟩

end Work.Higman.H8

/-
# The core computation for App. VIII Prop. 3

Let `L = K[α]` be the quadratic extension of the finite field `K` of characteristic two with
`α² = εα + 1` (so that the squaring form `q(a,b) = a² + εab + b²` of Higman's family `B(n,1,ε)`
is the norm `x ↦ x · x^{|K|}` of `L/K`).  If `F : L → L` and `g : K → K` are additive bijections
satisfying `g(N x) = N(F x)` for `x = a + bα` (with `N x = x · x^{|K|}`), then `F` is a
*semilinear* map `F x = λ · x ^ (2^i)`.

This is the computation in the proof of App. VIII Prop. 3 (Peterfalvi I, p. 226): the Frobenius
expansions of `F` and `g` are compared coefficient by coefficient.
-/
import Mathlib
import Submission.Work.Hering.AppVIII.QuadExt
import Submission.Work.Hering.AppVIII.QuadExtNorm
import Submission.Work.Hering.AppVIII.FrobBasis
import Submission.Work.Hering.AppVIII.MonomialCoeff
import Submission.Work.Hering.AppVIII.TwoPowArith

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

noncomputable section

open Polynomial Module

namespace Work.Hering.AppVIII

/-- **The structure of the induced pairs `(F, g)`.**  An additive bijection `F` of the quadratic
extension `L = K[α]` (with `α² = εα + 1`) whose norm relation with an additive bijection `g` of
`K` holds is necessarily of the form `F x = λ · x ^ (2 ^ i)`. -/
theorem semilinear_of_normRepr {K : Type*} [Field K] [CharP K 2] [Finite K] {ε : K}
    [Fact (Irreducible (quadPoly K ε))] (hε : Anisotropic K ε)
    (F : QuadExt K ε ≃+ QuadExt K ε) (g : K ≃+ K)
    (h : ∀ a b : K, algebraMap K (QuadExt K ε) (g (a * a + ε * (a * b) + b * b))
        = (F (algebraMap K (QuadExt K ε) a + algebraMap K (QuadExt K ε) b * qalpha K ε))
          * (F (algebraMap K (QuadExt K ε) a + algebraMap K (QuadExt K ε) b * qalpha K ε))
              ^ (Nat.card K)) :
    ∃ (lam : QuadExt K ε) (i : ℕ), lam ≠ 0 ∧ ∀ x : QuadExt K ε, F x = lam * x ^ (2 ^ i) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (QuadExt K ε) := Fintype.ofFinite (QuadExt K ε)
  obtain ⟨nK, -, hKcard⟩ := FiniteField.card K 2
  have hnK : 0 < (nK : ℕ) := nK.pos
  let dL : ℕ := 2 * (nK : ℕ)
  have hdLval : dL = 2 * (nK : ℕ) := rfl
  have hdLpos : 0 < dL := by omega
  -- ## cardinality of `L`
  have hLcard : Fintype.card (QuadExt K ε) = 2 ^ (2 * (nK : ℕ)) := by
    rw [← Nat.card_eq_fintype_card, quadExt_natCard, Nat.card_eq_fintype_card, hKcard]
    rw [← pow_mul, mul_comm]
  -- ## the Frobenius of `L` is periodic with period `2 ^ (2 nK)`
  have hx_frob : ∀ x : QuadExt K ε, x ^ (2 ^ (2 * (nK : ℕ))) = x := by
    intro x
    rw [show (2 : ℕ) ^ (2 * (nK : ℕ)) = Nat.card (QuadExt K ε) from by
      rw [Nat.card_eq_fintype_card, hLcard]]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hx_frob_mul : ∀ (x : QuadExt K ε) (q : ℕ), x ^ (2 ^ (2 * (nK : ℕ) * q)) = x := by
    intro x q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [show 2 * (nK : ℕ) * (q + 1) = 2 * (nK : ℕ) * q + 2 * (nK : ℕ) by ring, pow_add,
          pow_mul, ih, hx_frob]
  have hx_red : ∀ (x : QuadExt K ε) (a : ℕ), x ^ (2 ^ a) = x ^ (2 ^ (a % (2 * (nK : ℕ)))) := by
    intro x a
    have hdiv : 2 ^ a = 2 ^ (2 * (nK : ℕ) * (a / (2 * (nK : ℕ)))) * 2 ^ (a % (2 * (nK : ℕ))) := by
      conv_lhs => rw [← Nat.div_add_mod a (2 * (nK : ℕ))]
      rw [pow_add]
    calc x ^ (2 ^ a)
        = x ^ (2 ^ (2 * (nK : ℕ) * (a / (2 * (nK : ℕ)))) * 2 ^ (a % (2 * (nK : ℕ)))) := by
          rw [hdiv]
      _ = (x ^ (2 ^ (2 * (nK : ℕ) * (a / (2 * (nK : ℕ)))))) ^ (2 ^ (a % (2 * (nK : ℕ)))) := by
          rw [pow_mul]
      _ = x ^ (2 ^ (a % (2 * (nK : ℕ)))) := by
          rw [hx_frob_mul]
  -- ## the Frobenius expansions of `F` and `g`
  obtain ⟨c, hc, -⟩ := frobExpansion hLcard F.toAddMonoidHom
  obtain ⟨μ, hμ, -⟩ := frobExpansion hKcard g.toAddMonoidHom
  -- ## Frobenius is additive over sums
  have hsum_pow : ∀ (m : ℕ) (s : Finset (Fin (2 * (nK : ℕ)))) (γ : Fin (2 * (nK : ℕ)) → QuadExt K ε),
      (∑ i ∈ s, γ i) ^ (2 ^ m) = ∑ i ∈ s, (γ i) ^ (2 ^ m) := by
    intro m s
    induction s using Finset.induction_on with
    | empty => intro γ; simp
    | insert i s hi ih =>
        intro γ
        rw [Finset.sum_insert hi, Finset.sum_insert hi, add_pow_char_pow, ih]
  -- ## the involution `ψ k = (k + nK) mod (2 nK)`
  let ψ : Fin (2 * (nK : ℕ)) → Fin (2 * (nK : ℕ)) :=
    fun k => ⟨((k : ℕ) + (nK : ℕ)) % (2 * (nK : ℕ)), Nat.mod_lt _ hdLpos⟩
  have hψ_val : ∀ k : Fin (2 * (nK : ℕ)), ((ψ k : ℕ)) = ((k : ℕ) + (nK : ℕ)) % (2 * (nK : ℕ)) :=
    fun k => rfl
  have hψ_invol : ∀ k, ψ (ψ k) = k := by
    intro k
    refine Fin.ext ?_
    rw [hψ_val, hψ_val]
    have h1 : ((k : ℕ) + (nK : ℕ)) % (2 * (nK : ℕ)) + (nK : ℕ)
        ≡ (k : ℕ) + (nK : ℕ) + (nK : ℕ) [MOD 2 * (nK : ℕ)] :=
      (Nat.mod_modEq _ _).add_right _
    have h2 : (k : ℕ) + (nK : ℕ) + (nK : ℕ) ≡ (k : ℕ) [MOD 2 * (nK : ℕ)] := by
      have hzero : 2 * (nK : ℕ) ≡ 0 [MOD 2 * (nK : ℕ)] :=
        Nat.modEq_zero_iff_dvd.mpr dvd_rfl
      have h3 : (k : ℕ) + 2 * (nK : ℕ) ≡ (k : ℕ) [MOD 2 * (nK : ℕ)] := by
        have h := (Nat.ModEq.refl (k : ℕ)).add hzero
        rwa [add_zero] at h
      rwa [show (k : ℕ) + (nK : ℕ) + (nK : ℕ) = (k : ℕ) + 2 * (nK : ℕ) by ring]
    have h3 := h1.trans h2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt k.isLt] at h3
  -- ## the second factor of the norm
  have hFpow : ∀ x : QuadExt K ε, (F x) ^ (2 ^ (nK : ℕ))
      = ∑ k : Fin (2 * (nK : ℕ)), (c (ψ k)) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ (k : ℕ)) := by
    intro x
    have hcx : F x = ∑ i : Fin (2 * (nK : ℕ)), c i * x ^ (2 ^ (i : ℕ)) := hc x
    rw [hcx, hsum_pow]
    rw [Finset.sum_congr rfl (fun i _ => by rw [mul_pow, ← pow_mul, ← pow_add])]
    -- rewrite each term using `hx_red`, then reindex by `ψ`
    have hstep : ∀ i : Fin (2 * (nK : ℕ)),
        (c i) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ ((i : ℕ) + (nK : ℕ)))
          = (c i) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ ((ψ i : ℕ))) := by
      intro i
      rw [hx_red x ((i : ℕ) + (nK : ℕ)), hψ_val]
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    have hcomp : (∑ a, (c (ψ a)) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ (a : ℕ)))
        = ∑ b, (c b) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ ((ψ b : ℕ))) := by
      let ψEquiv : Fin (2 * (nK : ℕ)) ≃ Fin (2 * (nK : ℕ)) :=
        Equiv.ofBijective ψ (Function.Involutive.bijective hψ_invol)
      have hcoe : ⇑ψEquiv = ψ := rfl
      have hsum := Equiv.sum_comp ψEquiv
        (fun i : Fin (2 * (nK : ℕ)) => (c i) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ ((ψ i : ℕ))))
      rw [hcoe] at hsum
      simpa only [hψ_invol] using hsum
    exact hcomp.symm
  -- ## the exponent `2 ^ j + 2 ^ (nK + j)`
  have hLHSterm : ∀ (x : QuadExt K ε) (j : Fin (nK : ℕ)),
      x ^ (2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ))) = (x * x ^ (2 ^ (nK : ℕ))) ^ (2 ^ (j : ℕ)) := by
    intro x j
    calc x ^ (2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ)))
        = x ^ (2 ^ (j : ℕ) + 2 ^ (nK : ℕ) * 2 ^ (j : ℕ)) := by
          rw [pow_add (2 : ℕ) (nK : ℕ) (j : ℕ)]
      _ = x ^ (2 ^ (j : ℕ)) * x ^ (2 ^ (nK : ℕ) * 2 ^ (j : ℕ)) := by rw [pow_add]
      _ = (x * x ^ (2 ^ (nK : ℕ))) ^ (2 ^ (j : ℕ)) := by rw [mul_pow, pow_mul]
  -- ## the identity
  have hident : ∀ x : QuadExt K ε, x ≠ 0 →
      (∑ j : Fin (nK : ℕ), algebraMap K (QuadExt K ε) (μ j)
          * x ^ (2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ))))
        = ∑ p : Fin (2 * (nK : ℕ)) × Fin (2 * (nK : ℕ)),
            c p.1 * (c (ψ p.2)) ^ (2 ^ (nK : ℕ)) * x ^ (2 ^ (p.1 : ℕ) + 2 ^ (p.2 : ℕ)) := by
    intro x hx
    obtain ⟨p, hp⟩ := exists_repr K ε x
    have hKcard' : Nat.card K = 2 ^ (nK : ℕ) := by rw [Nat.card_eq_fintype_card, hKcard]
    set x₀ : QuadExt K ε := algebraMap K (QuadExt K ε) p.1 + algebraMap K (QuadExt K ε) p.2
      * qalpha K ε with hx₀
    -- the hypothesis, in terms of `x₀`
    have hkey := h p.1 p.2
    have hμq : g (p.1 * p.1 + ε * (p.1 * p.2) + p.2 * p.2)
        = ∑ j : Fin (nK : ℕ),
            μ j * (p.1 * p.1 + ε * (p.1 * p.2) + p.2 * p.2) ^ (2 ^ (j : ℕ)) :=
      hμ (p.1 * p.1 + ε * (p.1 * p.2) + p.2 * p.2)
    rw [hμq, map_sum] at hkey
    -- the left hand side, expanded
    have hleft : (∑ j : Fin (nK : ℕ), algebraMap K (QuadExt K ε)
          (μ j * (p.1 * p.1 + ε * (p.1 * p.2) + p.2 * p.2) ^ (2 ^ (j : ℕ))))
        = ∑ j : Fin (nK : ℕ), algebraMap K (QuadExt K ε) (μ j)
            * x₀ ^ (2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, ← normRepr K hε p.1 p.2, hKcard', ← hLHSterm x₀ j]
    rw [← hx₀] at hkey
    rw [hleft] at hkey
    rw [hKcard'] at hkey
    -- the right hand side, expanded
    have hright : (∑ i : Fin (2 * (nK : ℕ)), c i * x₀ ^ (2 ^ (i : ℕ)))
        * (∑ k : Fin (2 * (nK : ℕ)), (c (ψ k)) ^ (2 ^ (nK : ℕ)) * x₀ ^ (2 ^ (k : ℕ)))
        = ∑ p : Fin (2 * (nK : ℕ)) × Fin (2 * (nK : ℕ)),
            c p.1 * (c (ψ p.2)) ^ (2 ^ (nK : ℕ)) * x₀ ^ (2 ^ (p.1 : ℕ) + 2 ^ (p.2 : ℕ)) := by
      rw [Finset.sum_mul]
      conv_rhs => rw [← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
    have hFx : F x₀ = ∑ i : Fin (2 * (nK : ℕ)), c i * x₀ ^ (2 ^ (i : ℕ)) := hc x₀
    rw [hFpow x₀] at hkey
    rw [hFx] at hkey
    rw [hp]
    rw [hkey]
    exact hright
  -- ## the coefficient families and the identity
  let aF : Fin (nK : ℕ) → ℕ := fun j => 2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ))
  let bF : Fin dL × Fin dL → ℕ := fun q => 2 ^ (q.1 : ℕ) + 2 ^ (q.2 : ℕ)
  let cF : Fin (nK : ℕ) → QuadExt K ε := fun j => algebraMap K (QuadExt K ε) (μ j)
  let dF : Fin dL × Fin dL → QuadExt K ε := fun q => c q.1 * (c (ψ q.2)) ^ (2 ^ (nK : ℕ))
  have haF : ∀ j : Fin (nK : ℕ), aF j = 2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ)) := fun j => rfl
  have hbF : ∀ q : Fin dL × Fin dL, bF q = 2 ^ (q.1 : ℕ) + 2 ^ (q.2 : ℕ) := fun q => rfl
  have hdF : ∀ q : Fin dL × Fin dL, dF q = c q.1 * (c (ψ q.2)) ^ (2 ^ (nK : ℕ)) := fun q => rfl
  have hident' : ∀ x : QuadExt K ε, x ≠ 0 →
      (∑ j, cF j * x ^ (aF j)) = ∑ q, dF q * x ^ (bF q) := by
    intro x hx
    have h := hident x hx
    simpa only [aF, bF, cF, dF] using h
  -- ## bounds for the exponents
  have hLcard' : Fintype.card (QuadExt K ε) = 2 ^ dL := by rw [hLcard, hdLval]
  have hMpos : 0 < 2 ^ dL - 1 := by
    have h : 2 ≤ (2 : ℕ) ^ dL := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ dL := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow2 : ∀ k : ℕ, 0 < k → (2 : ℕ) ^ k = 2 ^ (k - 1) * 2 := by
    intro k hk
    rw [← pow_succ]
    congr 1
    omega
  have haf_le : ∀ j : Fin (nK : ℕ), aF j ≤ 2 ^ dL - 1 := by
    intro j
    have hj : (j : ℕ) < (nK : ℕ) := j.isLt
    have h1 : 2 ^ (j : ℕ) ≤ 2 ^ (dL - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ ((nK : ℕ) + (j : ℕ)) ≤ 2 ^ (dL - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ (dL - 1) = 2 ^ (dL - 2) * 2 := hpow2 (dL - 1) (by omega)
    have h4 : (2 : ℕ) ^ dL = 2 ^ (dL - 2) * 4 := by rw [hpow2 dL (by omega), h3]; ring
    have h5 : 1 ≤ 2 ^ (dL - 2) := Nat.one_le_two_pow
    rw [haF]
    omega
  have haf_le2 : ∀ j : Fin (nK : ℕ), aF j ≤ 2 ^ dL := fun j => by have := haf_le j; omega
  have hbf_le : ∀ q : Fin dL × Fin dL, bF q ≤ 2 ^ dL := by
    intro q
    have hq1 : (q.1 : ℕ) < dL := q.1.isLt
    have hq2 : (q.2 : ℕ) < dL := q.2.isLt
    have h1 : 2 ^ (q.1 : ℕ) ≤ 2 ^ (dL - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (q.2 : ℕ) ≤ 2 ^ (dL - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ dL = 2 ^ (dL - 1) * 2 := hpow2 dL (by omega)
    rw [hbF]
    omega
  -- ## a residue class modulo `2 ^ dL - 1` determines a small integer
  have hres : ∀ {m e : ℕ}, e < 2 ^ dL - 1 → 0 < e → m ≤ 2 ^ dL →
      m ≡ e [MOD 2 ^ dL - 1] → m = e ∨ m = e + (2 ^ dL - 1) := by
    intro m e he he0 hm h
    have hmod : m % (2 ^ dL - 1) = e := by
      rw [Nat.ModEq] at h
      rwa [Nat.mod_eq_of_lt he] at h
    have hdiv : m = (2 ^ dL - 1) * (m / (2 ^ dL - 1)) + e := by
      rw [← hmod]
      exact (Nat.div_add_mod m (2 ^ dL - 1)).symm
    have hkey : (2 ^ dL - 1) * (m / (2 ^ dL - 1)) ≤ 2 ^ dL - 1 := by
      have hA : (2 ^ dL - 1) * (m / (2 ^ dL - 1)) + 1 ≤ (2 ^ dL - 1) + 1 := by
        calc (2 ^ dL - 1) * (m / (2 ^ dL - 1)) + 1
            ≤ (2 ^ dL - 1) * (m / (2 ^ dL - 1)) + e := by omega
          _ = m := hdiv.symm
          _ ≤ 2 ^ dL := hm
          _ = (2 ^ dL - 1) + 1 := by omega
      omega
    have hq1 : m / (2 ^ dL - 1) ≤ 1 :=
      le_of_mul_le_mul_left (c := 1) (by simpa using hkey) hMpos
    rcases Nat.eq_zero_or_pos (m / (2 ^ dL - 1)) with hq | hq
    · left; rw [hq, mul_zero, zero_add] at hdiv; exact hdiv
    · right
      have hq1' : m / (2 ^ dL - 1) = 1 := by omega
      rw [hq1', mul_one, add_comm] at hdiv; exact hdiv
  -- ## the class equation
  have hmono' : ∀ e : ℕ, e < 2 ^ dL - 1 → 0 < e →
      (∑ j ∈ Finset.univ.filter (fun j : Fin (nK : ℕ) => aF j ≡ e [MOD 2 ^ dL - 1]), cF j)
        = ∑ q ∈ Finset.univ.filter (fun q : Fin dL × Fin dL => bF q ≡ e [MOD 2 ^ dL - 1]),
            dF q := by
    intro e he he0
    have he' : e < Fintype.card (QuadExt K ε) - 1 := by rw [hLcard']; exact he
    have h := monomialCoeff aF bF cF dF hident' e he'
    rwa [hLcard'] at h
  -- ## (★) : `c p * (c (ψ p)) ^ (2 ^ nK) = 0` for all `p`
  have hstar : ∀ p : Fin dL, c p * (c (ψ p)) ^ (2 ^ (nK : ℕ)) = 0 := by
    intro p
    have hp_lt : (p : ℕ) < dL := p.isLt
    have hp1 : (p : ℕ) + 1 ≤ dL := by omega
    rcases lt_or_eq_of_le hp1 with hlt | heq
    · -- the class of `2 ^ (p + 1)`
      have he_lt : 2 ^ ((p : ℕ) + 1) < 2 ^ dL - 1 := by
        have h1 : 2 ^ ((p : ℕ) + 1) ≤ 2 ^ (dL - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ≤ 2 ^ (dL - 1) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (dL - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : (2 : ℕ) ^ dL = 2 ^ (dL - 1) * 2 := hpow2 dL (by omega)
        omega
      have he_pos : 0 < 2 ^ ((p : ℕ) + 1) := by positivity
      have hstep := hmono' (2 ^ ((p : ℕ) + 1)) he_lt he_pos
      have haf_empty : (Finset.univ.filter (fun j : Fin (nK : ℕ) =>
          aF j ≡ 2 ^ ((p : ℕ) + 1) [MOD 2 ^ dL - 1])) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _ hj
        have hjlt : (j : ℕ) < (nK : ℕ) := j.isLt
        have hbnd : aF j ≤ 2 ^ dL - 1 := haf_le j
        rcases hres (m := aF j) (e := 2 ^ ((p : ℕ) + 1)) he_lt he_pos (haf_le2 j) hj with h | h
        · rw [haF] at h
          obtain ⟨h1, h2⟩ := twoPowAddEq (by omega : (j : ℕ) ≤ (nK : ℕ) + (j : ℕ))
            (le_refl _)
            (by rw [h, pow_succ]; ring : (2 : ℕ) ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ))
              = 2 ^ (p : ℕ) + 2 ^ (p : ℕ))
          omega
        · omega
      have hsing : (Finset.univ.filter (fun q : Fin dL × Fin dL =>
          bF q ≡ 2 ^ ((p : ℕ) + 1) [MOD 2 ^ dL - 1])) = {(p, p)} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hq
          rcases hres (m := bF q) (e := 2 ^ ((p : ℕ) + 1)) he_lt he_pos (hbf_le q) hq with h | h
          · rw [hbF] at h
            rcases twoPowAddEq'
              (h.trans (by rw [pow_succ]; ring :
                (2 : ℕ) ^ ((p : ℕ) + 1) = 2 ^ (p : ℕ) + 2 ^ (p : ℕ))) with h1 | h1
            · exact Prod.ext (Fin.ext h1.1) (Fin.ext h1.2)
            · exact Prod.ext (Fin.ext h1.1) (Fin.ext h1.2)
          · have hb := hbf_le q; omega
        · intro hq
          rw [hq, Nat.ModEq, hbF]
          rw [show (2 : ℕ) ^ (p : ℕ) + 2 ^ (p : ℕ) = 2 ^ ((p : ℕ) + 1) by
            rw [pow_succ]; ring]
      rw [haf_empty, Finset.sum_empty, hsing, Finset.sum_singleton, hdF] at hstep
      exact hstep.symm
    · -- the class of `1` (`p + 1 = dL`)
      have he_lt : 1 < 2 ^ dL - 1 := by
        have h3 : (2 : ℕ) ^ dL = 2 ^ (dL - 1) * 2 := hpow2 dL (by omega)
        have h2 : 2 ≤ 2 ^ (dL - 1) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (dL - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hstep := hmono' 1 he_lt (by norm_num)
      have haf_empty : (Finset.univ.filter (fun j : Fin (nK : ℕ) =>
          aF j ≡ 1 [MOD 2 ^ dL - 1])) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _ hj
        have hbnd : aF j ≤ 2 ^ dL - 1 := haf_le j
        rcases hres (m := aF j) (e := 1) he_lt (by norm_num) (haf_le2 j) hj with h | h
        · rw [haF] at h
          have h2 : 2 ≤ 2 ^ (j : ℕ) + 2 ^ ((nK : ℕ) + (j : ℕ)) := by
            have ha : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
            have hb : 1 ≤ 2 ^ ((nK : ℕ) + (j : ℕ)) := Nat.one_le_two_pow
            omega
          omega
        · omega
      have hsing : (Finset.univ.filter (fun q : Fin dL × Fin dL =>
          bF q ≡ 1 [MOD 2 ^ dL - 1])) = {(p, p)} := by
        have hdL4 : (2 : ℕ) ^ (dL - 1) + 2 ^ (dL - 1) = 2 ^ dL := by
          rw [hpow2 dL (by omega)]; ring
        have hNd : (2 : ℕ) ^ dL % (2 ^ dL - 1) = 1 := by
          have hN1 : 2 ^ dL = (2 ^ dL - 1) + 1 := by omega
          nth_rewrite 1 [hN1]
          rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (Nat.mod_lt 1 hMpos),
            Nat.mod_eq_of_lt (by omega : 1 < 2 ^ dL - 1)]
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hq
          rcases hres (m := bF q) (e := 1) he_lt (by norm_num) (hbf_le q) hq with h | h
          · rw [hbF] at h
            have h2 : 2 ≤ 2 ^ (q.1 : ℕ) + 2 ^ (q.2 : ℕ) := by
              have ha : 1 ≤ 2 ^ (q.1 : ℕ) := Nat.one_le_two_pow
              have hb : 1 ≤ 2 ^ (q.2 : ℕ) := Nat.one_le_two_pow
              omega
            omega
          · rw [hbF] at h
            have h' : 2 ^ (q.1 : ℕ) + 2 ^ (q.2 : ℕ)
                = 2 ^ (dL - 1) + 2 ^ (dL - 1) := by omega
            rcases twoPowAddEq' h' with h1 | h1
            · refine Prod.ext ?_ ?_
              · apply Fin.ext; show (q.1 : ℕ) = (p : ℕ); omega
              · apply Fin.ext; show (q.2 : ℕ) = (p : ℕ); omega
            · refine Prod.ext ?_ ?_
              · apply Fin.ext; show (q.1 : ℕ) = (p : ℕ); omega
              · apply Fin.ext; show (q.2 : ℕ) = (p : ℕ); omega
        · intro hq
          rw [hq, Nat.ModEq, hbF]
          rw [show (2 : ℕ) ^ (p : ℕ) + 2 ^ (p : ℕ) = 2 ^ ((p : ℕ) + 1) by
            rw [pow_succ]; ring, heq]
          rw [hNd, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ dL - 1)]
      rw [haf_empty, Finset.sum_empty, hsing, Finset.sum_singleton, hdF] at hstep
      exact hstep.symm
  -- ## (†) : the cross relations
  have hcross : ∀ p q : Fin dL, p ≠ q → ψ p ≠ q →
      2 ≤ (2 ^ (p : ℕ) + 2 ^ (q : ℕ)) % (2 ^ dL - 1) →
      c p * (c (ψ q)) ^ (2 ^ (nK : ℕ)) + c q * (c (ψ p)) ^ (2 ^ (nK : ℕ)) = 0 := by
    intro p q hpq hpsiq he2
    let e : ℕ := (2 ^ (p : ℕ) + 2 ^ (q : ℕ)) % (2 ^ dL - 1)
    have hp_lt : (p : ℕ) < dL := p.isLt
    have hq_lt : (q : ℕ) < dL := q.isLt
    have he_lt : e < 2 ^ dL - 1 := Nat.mod_lt _ hMpos
    have he_pos : 0 < e := by omega
    have hsum_le : 2 ^ (p : ℕ) + 2 ^ (q : ℕ) ≤ 2 ^ dL := by
      have h1 : 2 ^ (p : ℕ) ≤ 2 ^ (dL - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (q : ℕ) ≤ 2 ^ (dL - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : (2 : ℕ) ^ dL = 2 ^ (dL - 1) * 2 := hpow2 dL (by omega)
      omega
    have hmod : 2 ^ (p : ℕ) + 2 ^ (q : ℕ) ≡ e [MOD 2 ^ dL - 1] := by
      rw [Nat.ModEq, show e = (2 ^ (p : ℕ) + 2 ^ (q : ℕ)) % (2 ^ dL - 1) from rfl,
        Nat.mod_eq_of_lt he_lt]
    have hsum_eq : 2 ^ (p : ℕ) + 2 ^ (q : ℕ) = e := by
      rcases hres he_lt he_pos hsum_le hmod with h | h
      · exact h
      · omega
    have hstep := hmono' e he_lt he_pos
    have hbc_eq : ∀ r : Fin dL × Fin dL, bF r ≡ e [MOD 2 ^ dL - 1] →
        r = (p, q) ∨ r = (q, p) := by
      intro r hr
      have hbr : bF r ≤ 2 ^ dL := hbf_le r
      rcases hres he_lt he_pos hbr hr with h | h
      · rw [hbF] at h
        rcases twoPowAddEq' (h.trans hsum_eq.symm) with h1 | h1
        · exact Or.inl (Prod.ext (Fin.ext h1.1) (Fin.ext h1.2))
        · exact Or.inr (Prod.ext (Fin.ext h1.1) (Fin.ext h1.2))
      · omega
    have hfilter : (Finset.univ.filter (fun r : Fin dL × Fin dL =>
        bF r ≡ e [MOD 2 ^ dL - 1])) = {(p, q), (q, p)} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · exact hbc_eq r
      · rintro (h | h)
        · rw [h, hbF]; exact hmod
        · rw [h, hbF]; simpa only [add_comm] using hmod
    have haf_empty : (Finset.univ.filter (fun j : Fin (nK : ℕ) =>
        aF j ≡ e [MOD 2 ^ dL - 1])) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ hj
      have hjlt : (j : ℕ) < (nK : ℕ) := j.isLt
      have hbnd : aF j ≤ 2 ^ dL - 1 := haf_le j
      rcases hres he_lt he_pos (haf_le2 j) hj with h | h
      · rw [haF] at h
        rcases twoPowAddEq' (h.trans hsum_eq.symm) with h1 | h1
        · have hqval : (q : ℕ) = (p : ℕ) + (nK : ℕ) := by omega
          have hψ : ψ p = q := Fin.ext (by
            rw [hψ_val, Nat.mod_eq_of_lt (by omega)]
            exact hqval.symm)
          exact hpsiq hψ
        · have hpval : (p : ℕ) = (q : ℕ) + (nK : ℕ) := by omega
          have hψq : ψ q = p := Fin.ext (by
            rw [hψ_val, Nat.mod_eq_of_lt (by omega)]
            exact hpval.symm)
          have hψ : ψ p = q := by
            calc ψ p = ψ (ψ q) := by rw [hψq]
              _ = q := hψ_invol q
          exact hpsiq hψ
      · omega
    rw [haf_empty, Finset.sum_empty, hfilter] at hstep
    rw [Finset.sum_insert (by
      simp only [Finset.mem_singleton, Prod.mk.injEq]
      rintro ⟨h1, -⟩
      exact hpq h1), Finset.sum_singleton] at hstep
    simp only [hdF] at hstep
    exact hstep.symm
  -- ## the support of `c` is a single point
  have hstar_psi : ∀ r : Fin dL, c r ≠ 0 → c (ψ r) = 0 := by
    intro r hr
    rcases mul_eq_zero.mp (hstar r) with h | h
    · exact absurd h hr
    · exact pow_eq_zero_iff (by positivity : (2 : ℕ) ^ (nK : ℕ) ≠ 0) |>.mp h
  have hmain : ∀ p q : Fin dL, c p ≠ 0 → c q ≠ 0 → p = q := by
    intro p q hp hq
    by_contra hpq
    have hpp := hstar_psi p hp
    have hqq := hstar_psi q hq
    have h1 : p ≠ ψ p := fun h => hp (h ▸ hpp)
    have h2 : p ≠ ψ q := fun h => hp (h ▸ hqq)
    have h3 : q ≠ ψ p := fun h => hq (h ▸ hpp)
    have h4 : q ≠ ψ q := fun h => hq (h ▸ hqq)
    have hle4 : 4 ≤ dL := by
      have h2a : ({p, ψ p} : Finset (Fin dL)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using h1), Finset.card_singleton]
      have h2b : ({q, ψ q} : Finset (Fin dL)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using h4), Finset.card_singleton]
      have hdisj : Disjoint ({p, ψ p} : Finset (Fin dL)) ({q, ψ q} : Finset (Fin dL)) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with h | h
        · exact hpq h
        · exact h2 h
        · exact h3 h.symm
        · exact hpq (by rw [← hψ_invol p, h, hψ_invol q])
      have hcard := Finset.card_union_of_disjoint hdisj
      have hle : (({p, ψ p} : Finset (Fin dL)) ∪ ({q, ψ q} : Finset (Fin dL))).card ≤ dL := by
        have hcu := Finset.card_le_univ (({p, ψ p} : Finset (Fin dL)) ∪
          ({q, ψ q} : Finset (Fin dL)))
        simpa [Fintype.card_fin] using hcu
      rw [hcard, h2a, h2b] at hle
      omega
    have hp_lt : (p : ℕ) < dL := p.isLt
    have hψq_lt : (ψ q : ℕ) < dL := (ψ q).isLt
    have he2 : 2 ≤ (2 ^ (p : ℕ) + 2 ^ (ψ q : ℕ)) % (2 ^ dL - 1) := by
      have hmax : 2 ^ (p : ℕ) + 2 ^ (ψ q : ℕ) ≤ 2 ^ (dL - 1) + 2 ^ (dL - 2) := by
        rcases (by omega : (p : ℕ) ≤ dL - 2 ∨ (ψ q : ℕ) ≤ dL - 2) with hc | hc
        · have hA := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hc
          have hB := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
            (by omega : (ψ q : ℕ) ≤ dL - 1)
          omega
        · have hA := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
            (by omega : (p : ℕ) ≤ dL - 1)
          have hB := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hc
          omega
      have hlt : 2 ^ (dL - 1) + 2 ^ (dL - 2) < 2 ^ dL - 1 := by
        have h3 : (2 : ℕ) ^ dL = 2 ^ (dL - 1) * 2 := hpow2 dL (by omega)
        have h4 : (2 : ℕ) ^ (dL - 1) = 2 ^ (dL - 2) * 2 := hpow2 (dL - 1) (by omega)
        have h5 : 2 ≤ 2 ^ (dL - 2) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (dL - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hlt' : 2 ^ (p : ℕ) + 2 ^ (ψ q : ℕ) < 2 ^ dL - 1 := lt_of_le_of_lt hmax hlt
      rw [Nat.mod_eq_of_lt hlt']
      have ha : 1 ≤ 2 ^ (p : ℕ) := Nat.one_le_two_pow
      have hb : 1 ≤ 2 ^ (ψ q : ℕ) := Nat.one_le_two_pow
      omega
    have hrel := hcross p (ψ q) h2 (fun h => hpq (by rw [← hψ_invol p, h, hψ_invol q])) he2
    rw [hψ_invol q, hqq, zero_mul, add_zero] at hrel
    rcases mul_eq_zero.mp hrel with h | h
    · exact absurd h hp
    · exact absurd (pow_eq_zero_iff (by positivity : (2 : ℕ) ^ (nK : ℕ) ≠ 0) |>.mp h) hq
  -- ## assemble
  have hex : ∃ p : Fin dL, c p ≠ 0 := by
    by_contra h
    have h0 : ∀ i : Fin dL, c i = 0 := fun i => by
      by_contra hci
      exact h ⟨i, hci⟩
    have h1 : F 1 = 0 := by
      change F.toAddMonoidHom 1 = 0
      rw [hc 1]
      exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_mul]
    have h2 : (1 : QuadExt K ε) = 0 := F.injective (by rw [h1, map_zero])
    exact one_ne_zero h2
  obtain ⟨p, hp⟩ := hex
  exact ⟨c p, p, hp, fun x => by
    change F.toAddMonoidHom x = c p * x ^ (2 ^ (p : ℕ))
    rw [hc x]
    exact Finset.sum_eq_single p
      (fun j _ hj => by
        rcases eq_or_ne (c j) 0 with h0 | h0
        · rw [h0, zero_mul]
        · exact absurd (hmain j p h0 hp) hj)
      (fun hp' => absurd (Finset.mem_univ p) hp')⟩

end Work.Hering.AppVIII

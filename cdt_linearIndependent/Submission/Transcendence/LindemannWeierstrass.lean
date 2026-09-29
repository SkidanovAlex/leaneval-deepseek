import Submission.Transcendence.LindemannC
import Submission.Commons.RingTheory.IsAlgebraic.finset_sum
import Submission.Commons.Data.Rat.finset_int_common_multiple

/-!
# The full Lindemann–Weierstrass theorem (algebraic independence of exponentials)

**Statement (classical).**  If `α₁,…,αₙ : ℂ` are algebraic over `ℚ` and
`ℚ`-linearly independent, then `e^{α₁},…,e^{αₙ}` are algebraically
independent over `ℚ`:

```lean
theorem algebraicIndependent_exp_of_linearIndependent {n : ℕ} (α : Fin n → ℂ)
    (hα : ∀ k : Fin n, IsAlgebraic ℚ (α k)) (hli : LinearIndependent ℚ α) :
    AlgebraicIndependent ℚ (fun k : Fin n => cexp (α k))
```

**Proof structure (classical; Lemma B already proved in `LindemannC.lean`).**
Assume a nonzero `p : MvPolynomial (Fin n) ℚ` with
`aeval (fun k => cexp (α k)) p = 0`.  The monomial expansion over
`p.support` (`aeval_eq_sum_support`, via `MvPolynomial.as_sum` +
`MvPolynomial.eval₂_monomial`) and the exponential identity
`prod_cexp_pow_eq_expVal` (each monomial factor `(e^{αᵢ})^{vᵢ}` is
`e^{(vᵢ:ℂ)·αᵢ}` by `Complex.exp_nat_mul`, and products of exponentials are
exponentials of sums by `Complex.exp_sum`) turn this into the exponential
relation

`Σ_{v ∈ p.support} (coeff v p : ℂ) · cexp (expVal α v) = 0`

over the *distinct* algebraic exponents `expVal α v`
(`expVal_injective` uses the ℚ-linear independence of `α` via
`Fintype.linearIndependent_iff`; `expVal_algebraic` uses
`Commons.RingTheory.IsAlgebraic.finset_sum`).

The rational coefficients `coeff v p : ℚ` are cleared by a common multiple
(`Commons.Data.Rat.finset_int_common_multiple`) into integer coefficients;
reindexing `p.support` to `Fin p.support.card`
(`support_sum_equivFin`, via `Finset.sum_coe_sort` + `Fintype.sum_equiv`)
produces a Fin-indexed relation to which Lemma B (`lemmaB` in
`LindemannC.lean`: *distinct algebraic exponents with integer coefficients,
not all zero, have no exponential relation*) applies — contradiction.
Hence the aeval-kernel is trivial, i.e. `AlgebraicIndependent ℚ (cexp ∘ α)`.

**Corollaries.**  (1) `isAlgebraic_pow_two_of_isAlgebraic_sq`: `x²` algebraic
over ℚ forces `x` algebraic (composition with `X²`);  (2)
`transcendental_riemannZeta_two_complex`: `ζ(2) = π²/6` is transcendental
over ℚ — the first (two-entry) fragment of CDT Theorem A;  (3)
`linearIndependent_pair_one_of_transcendental` and
`linearIndependent_one_riemannZeta_two`: `1, ζ(2)` are ℚ-linearly
independent.

Everything in this module is fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators
open scoped Complex
open Polynomial
set_option maxHeartbeats 800000
noncomputable section
namespace Submission.Transcendence

/-- Exponent value of a monomial exponent vector: the ℂ-sum `Σᵢ ((v i : ℕ) : ℂ) * αᵢ`. -/
def expVal {n : ℕ} (α : Fin n → ℂ) (v : Fin n →₀ ℕ) : ℂ :=
  ∑ i : Fin n, (((v i : ℕ) : ℂ) * α i)

/-- `expVal α v` as the ℚ-linear combination with coefficients `(v i : ℚ)`. -/
lemma expVal_eq_smul_sum {n : ℕ} (α : Fin n → ℂ) (v : Fin n →₀ ℕ) :
    expVal α v = (∑ i : Fin n, (((v i : ℕ) : ℚ) • α i)) := by
  dsimp [expVal]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Algebra.smul_def]

/-- Each monomial factor: `(e^{αᵢ})^{vᵢ} = e^{(vᵢ:ℂ)·αᵢ}`. -/
lemma factor_cexp_pow {x : ℂ} (n : ℕ) : (Complex.exp x) ^ n = Complex.exp ((n : ℂ) * x) := by
  exact (Complex.exp_nat_mul x n).symm

/-- The monomial product equals `cexp` of the exponent value. -/
lemma prod_cexp_pow_eq_expVal {n : ℕ} (α : Fin n → ℂ) (v : Fin n →₀ ℕ) :
    v.prod (fun i e => (Complex.exp (α i)) ^ e)
      = Complex.exp (expVal α v) := by
  classical
  calc
    v.prod (fun i e => (Complex.exp (α i)) ^ e)
        = ∏ i ∈ v.support, Complex.exp (((v i : ℕ) : ℂ) * α i) := by
          calc
            v.prod (fun i e => (Complex.exp (α i)) ^ e)
                = v.prod (fun i e => Complex.exp (((e : ℕ) : ℂ) * α i)) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  dsimp
                  exact (factor_cexp_pow (x := α i) (v i))
            _ = ∏ i ∈ v.support, Complex.exp (((v i : ℕ) : ℂ) * α i) := by
                  rfl
    _ = ∏ i : Fin n, Complex.exp (((v i : ℕ) : ℂ) * α i) := by
          apply Finset.prod_subset (s₁ := v.support) (s₂ := (Finset.univ : Finset (Fin n)))
          · intro i hi
            simp
          · intro i hi hiS
            have hv : v i = 0 := by
              by_contra hvi
              exact hiS ((Finsupp.mem_support_iff).2 hvi)
            simp [hv]
    _ = Complex.exp (∑ i : Fin n, (((v i : ℕ) : ℂ) * α i)) := by
          exact (Complex.exp_sum (Finset.univ : Finset (Fin n)) (fun i => (((v i : ℕ) : ℂ) * α i))).symm
    _ = Complex.exp (expVal α v) := by
          rfl

lemma aeval_eq_sum_support (σ : Type) (x : σ → ℂ) (p : MvPolynomial σ ℚ) :
    (MvPolynomial.aeval x) p
      = ∑ v ∈ p.support, (((p.coeff v : ℚ) : ℂ) * v.prod (fun i e => x i ^ e)) := by
  classical
  have h := MvPolynomial.as_sum p
  calc
    (MvPolynomial.aeval x) p
        = (MvPolynomial.aeval x) (∑ v ∈ p.support, (MvPolynomial.monomial v) (p.coeff v)) := by
          exact congrArg (MvPolynomial.aeval x) h
    _ = ∑ v ∈ p.support, (MvPolynomial.aeval x) ((MvPolynomial.monomial v) (p.coeff v)) := by
          rw [map_sum]
    _ = ∑ v ∈ p.support, (((p.coeff v : ℚ) : ℂ) * v.prod (fun i e => x i ^ e)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial]
          simp

lemma aeval_cexp_eq_expVal_sum {n : ℕ} (α : Fin n → ℂ) (p : MvPolynomial (Fin n) ℚ) :
    (MvPolynomial.aeval (fun k => cexp (α k))) p
      = ∑ v ∈ p.support, (((p.coeff v : ℚ) : ℂ) * cexp (expVal α v)) := by
  classical
  rw [aeval_eq_sum_support]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  exact prod_cexp_pow_eq_expVal α v

/-- `expVal α v` is algebraic over ℚ whenever each `α i` is. -/
lemma expVal_algebraic {n : ℕ} (α : Fin n → ℂ) (hα : ∀ k : Fin n, IsAlgebraic ℚ (α k))
    (v : Fin n →₀ ℕ) : IsAlgebraic ℚ (expVal α v) := by
  classical
  dsimp [expVal]
  refine Commons.RingTheory.IsAlgebraic.finset_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => (((v i : ℕ) : ℂ) * α i)) ?_
  intro i hi
  have hn : IsAlgebraic ℚ (((v i : ℕ) : ℂ)) := by
    have hc : (((v i : ℕ) : ℂ)) = ((((v i : ℕ) : ℚ) : ℂ)) := by norm_num
    rw [hc]
    exact isAlgebraic_ratCast (R := ℚ) (A := ℂ) ((v i : ℕ) : ℚ)
  exact IsAlgebraic.mul hn (hα i)

/-- `expVal α` is injective if the `αᵢ` are ℚ-linearly independent. -/
lemma expVal_injective {n : ℕ} (α : Fin n → ℂ) (hli : LinearIndependent ℚ α) :
    Function.Injective (expVal α) := by
  classical
  intro v w h
  apply Finsupp.ext
  intro i
  let g : Fin n → ℚ := fun j => (v j : ℚ) - (w j : ℚ)
  have hg0 : (∑ j : Fin n, g j • α j) = 0 := by
    calc
      (∑ j : Fin n, g j • α j)
          = (∑ j : Fin n, ((v j : ℚ) • α j)) - (∑ j : Fin n, ((w j : ℚ) • α j)) := by
            simp [g, sub_smul, Finset.sum_sub_distrib]
      _ = expVal α v - expVal α w := by
            rw [expVal_eq_smul_sum, expVal_eq_smul_sum]
      _ = 0 := by
            rw [h]
            ring
  have hall := (Fintype.linearIndependent_iff).mp hli g hg0
  have hg : (v i : ℚ) = (w i : ℚ) := sub_eq_zero.mp (hall i)
  exact_mod_cast hg

lemma support_sum_equivFin {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ v ∈ s, f v) = ∑ j : Fin s.card, f ((Finset.equivFin s).symm j : ι) := by
  classical
  have h1 : (∑ v ∈ s, f v) = (∑ x : {v // v ∈ s}, f x.1) := by
    exact (Finset.sum_coe_sort s f).symm
  rw [h1]
  let e : {v // v ∈ s} ≃ Fin s.card := Finset.equivFin s
  exact Fintype.sum_equiv e (f := fun x : {v // v ∈ s} => f x.1)
      (g := fun j : Fin s.card => f ((e.symm j : {v // v ∈ s}) : ι))
      (by intro x
          exact congrArg f (congrArg Subtype.val (e.symm_apply_apply x)).symm)

/-- A nonzero MvPolynomial has a nonzero coefficient in its support. -/
lemma exists_coeff_ne_zero_of_ne_zero {σ : Type} (p : MvPolynomial σ ℚ) (hp : p ≠ 0) :
    ∃ v ∈ p.support, p.coeff v ≠ 0 := by
  classical
  by_contra h
  have hmem : ∀ v ∈ p.support, p.coeff v = 0 := by
    intro v hv
    by_contra hc
    exact h ⟨v, hv, hc⟩
  have hsum : p = 0 := by
    rw [MvPolynomial.as_sum p]
    apply Finset.sum_eq_zero
    intro v hv
    simp [hmem v hv]
  exact hp hsum

open scoped Complex in
theorem algebraicIndependent_exp_of_linearIndependent {n : ℕ} (α : Fin n → ℂ)
    (hα : ∀ k : Fin n, IsAlgebraic ℚ (α k)) (hli : LinearIndependent ℚ α) :
    AlgebraicIndependent ℚ (fun k : Fin n => cexp (α k)) := by
  classical
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  let S := p.support
  have hrelQ : (∑ v ∈ S, (((p.coeff v : ℚ) : ℂ) * cexp (expVal α v))) = 0 := by
    dsimp [S]
    exact (aeval_cexp_eq_expVal_sum α p).symm.trans hp
  rcases (Commons.Data.Rat.finset_int_common_multiple S (fun v => p.coeff v)) with ⟨D, hD0, hz⟩
  let b : (Fin n →₀ ℕ) → ℤ := fun v => if hv : v ∈ S then Classical.choose (hz v hv) else 0
  have hb_eq : ∀ v ∈ S, (b v : ℂ) = (D : ℂ) * ((p.coeff v : ℚ) : ℂ) := by
    intro v hv
    have hz' : ((Classical.choose (hz v hv) : ℤ) : ℚ) = (D : ℚ) * p.coeff v :=
      Classical.choose_spec (hz v hv)
    have hc : ((Classical.choose (hz v hv) : ℤ) : ℂ) = (D : ℂ) * ((p.coeff v : ℚ) : ℂ) := by
      -- (z : ℂ) = ((D:ℚ)*coeff : ℂ)
      have hcast : ((Classical.choose (hz v hv) : ℤ) : ℂ) = (((Classical.choose (hz v hv) : ℤ) : ℚ) : ℂ) := by
        norm_num
      rw [hcast, hz']
      norm_num
    dsimp [b]
    rw [dif_pos hv]
    exact hc
  have hrelI : (∑ v ∈ S, ((b v : ℤ) : ℂ) * cexp (expVal α v)) = 0 := by
    have hmul : (D : ℂ) * (∑ v ∈ S, (((p.coeff v : ℚ) : ℂ) * cexp (expVal α v))) = 0 := by
      rw [hrelQ]
      ring
    calc
      (∑ v ∈ S, ((b v : ℤ) : ℂ) * cexp (expVal α v))
          = ∑ v ∈ S, ((D : ℂ) * ((p.coeff v : ℚ) : ℂ)) * cexp (expVal α v) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hb_eq v hv]
      _ = (D : ℂ) * (∑ v ∈ S, (((p.coeff v : ℚ) : ℂ) * cexp (expVal α v))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = 0 := hmul
  -- enumerate
  let eS : {v // v ∈ S} ≃ Fin S.card := Finset.equivFin S
  let γ : Fin S.card → ℂ := fun j => expVal α ((eS.symm j : {v // v ∈ S}) : (Fin n →₀ ℕ))
  let bN : Fin S.card → ℤ := fun j => b ((eS.symm j : {v // v ∈ S}) : (Fin n →₀ ℕ))
  have hinjγ : Function.Injective γ := by
    intro j k hjk
    have hE : expVal α (((eS.symm j : {v // v ∈ S}) : (Fin n →₀ ℕ))) =
        expVal α (((eS.symm k : {v // v ∈ S}) : (Fin n →₀ ℕ))) := by
      simpa [γ] using hjk
    have hv : ((eS.symm j : {v // v ∈ S}) : (Fin n →₀ ℕ)) = ((eS.symm k : {v // v ∈ S}) : (Fin n →₀ ℕ)) :=
      expVal_injective α hli hE
    have hs : (eS.symm j : {v // v ∈ S}) = (eS.symm k : {v // v ∈ S}) := Subtype.ext hv
    exact (eS.symm).injective hs
  have halgγ : ∀ j : Fin S.card, IsAlgebraic ℚ (γ j) := by
    intro j
    dsimp [γ]
    exact expVal_algebraic α hα (((eS.symm j : {v // v ∈ S}) : (Fin n →₀ ℕ)))
  have hbnz : ∃ j : Fin S.card, bN j ≠ 0 := by
    obtain ⟨v0, hv0, hc0⟩ := exists_coeff_ne_zero_of_ne_zero p hp0
    have hz0 : (Classical.choose (hz v0 hv0) : ℤ) ≠ 0 := by
      have hz' : ((Classical.choose (hz v0 hv0) : ℤ) : ℚ) = (D : ℚ) * p.coeff v0 :=
        Classical.choose_spec (hz v0 hv0)
      intro hz0
      have hDc : (D : ℚ) * p.coeff v0 = 0 := by
        rw [← hz', hz0]
        ring
      have hDnz : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
      exact hc0 ((mul_eq_zero.mp hDc).resolve_left hDnz)
    refine ⟨eS ⟨v0, hv0⟩, ?_⟩
    dsimp [bN]
    have hs : ((eS.symm (eS ⟨v0, hv0⟩) : {v // v ∈ S}) : (Fin n →₀ ℕ)) = v0 := by
      change ((eS.symm (eS ⟨v0, hv0⟩) : {v // v ∈ S}) : (Fin n →₀ ℕ)) = (⟨v0, hv0⟩ : {v // v ∈ S}).1
      rw [eS.symm_apply_apply]
    rw [hs]
    dsimp [b]
    rw [dif_pos hv0]
    exact hz0
  have hrelN : (∑ j : Fin S.card, ((bN j : ℤ) : ℂ) * cexp (γ j)) = 0 := by
    calc
      (∑ j : Fin S.card, ((bN j : ℤ) : ℂ) * cexp (γ j))
          = (∑ v ∈ S, (((b v : ℤ) : ℂ) * cexp (expVal α v))) := by
            symm
            dsimp [bN, γ]
            exact support_sum_equivFin S (fun v => (((b v : ℤ) : ℂ) * cexp (expVal α v)))
      _ = 0 := hrelI
  exact lemmaB γ bN hinjγ halgγ hbnz hrelN

end Submission.Transcendence

namespace Submission.Transcendence
/-! ### Corollary: ζ(2) = π²/6 is transcendental over ℚ

`riemannZeta 2 = ↑π ^ 2 / 6 : ℂ` (Mathlib `riemannZeta_two`).  If this were
algebraic over ℚ, then `π² = 6·ζ(2)` would be algebraic; with a ℚ-polynomial
`p` vanishing at `π²`, the composition `p(X²)` vanishes at `π`, making `π`
algebraic — contradicting `transcendental_pi_complex`. -/

/-- Square-root-free descent: if `x²` is algebraic over `ℚ` then so is `x`. -/
lemma isAlgebraic_pow_two_of_isAlgebraic_sq {x : ℂ} (h : IsAlgebraic ℚ (x ^ 2)) :
    IsAlgebraic ℚ x := by
  classical
  rcases h with ⟨p, hp0, hpae⟩
  refine ⟨p.comp (X ^ 2), ?_, ?_⟩
  · intro hc
    have hz : p = 0 ∨ (eval ((X ^ 2 : ℚ[X]).coeff 0) p = 0 ∧ (X ^ 2 : ℚ[X]) = C ((X ^ 2 : ℚ[X]).coeff 0)) :=
      (Polynomial.comp_eq_zero_iff.mp hc)
    rcases hz with hp | ⟨_, hq⟩
    · exact hp0 hp
    · -- X^2 ≠ C 0: compare coefficient at 2
      have hc2 := congrArg (fun q : ℚ[X] => q.coeff 2) hq
      simp [Polynomial.coeff_X_pow] at hc2
  · -- aeval x (p.comp (X^2)) = 0
    have hx2 : (Polynomial.aeval (x ^ 2)) p = 0 := hpae
    calc
      (Polynomial.aeval x) (p.comp (X ^ 2)) = (Polynomial.aeval ((Polynomial.aeval x) (X ^ 2))) p := by
        rw [Polynomial.aeval_comp]
      _ = (Polynomial.aeval (x ^ 2)) p := by
        congr 1
        simp
      _ = 0 := hx2

/-- ζ(2) = π²/6 is transcendental over ℚ (hence in particular irrational). -/
theorem transcendental_riemannZeta_two_complex : Transcendental ℚ (riemannZeta 2) := by
  classical
  by_contra htr
  have hζ : IsAlgebraic ℚ (riemannZeta 2) := (not_not.mp htr)
  -- π² = 6·ζ(2): algebraic
  have hpi2 : ((Real.pi : ℝ) : ℂ) ^ 2 = (6 : ℂ) * riemannZeta 2 := by
    rw [riemannZeta_two]
    field_simp
  have h6ζ : IsAlgebraic ℚ (((6 : ℚ) : ℂ) * riemannZeta 2) := by
    exact IsAlgebraic.mul (isAlgebraic_ratCast (R := ℚ) (A := ℂ) (6 : ℚ)) hζ
  have hpi2alg : IsAlgebraic ℚ (((Real.pi : ℝ) : ℂ) ^ 2) := by
    rw [hpi2]
    exact h6ζ
  have hpi : IsAlgebraic ℚ ((Real.pi : ℝ) : ℂ) := isAlgebraic_pow_two_of_isAlgebraic_sq hpi2alg
  exact transcendental_pi_complex hpi
end Submission.Transcendence

namespace Submission.Transcendence

/-- A transcendental element over a field is linearly independent of `1`
(there is no nontrivial `R`-linear relation `a + b·x = 0`). -/
lemma linearIndependent_pair_one_of_transcendental {x : ℂ}
    (hx : Transcendental ℚ x) : LinearIndependent ℚ ![1, x] := by
  classical
  rw [linearIndependent_fin2]
  constructor
  · -- x ≠ 0
    intro hx0
    have hx0' : x = 0 := by simpa using hx0
    exact hx (by
      rw [hx0']
      exact isAlgebraic_zero (R := ℚ) (A := ℂ))
  · -- ∀ a : ℚ, a • x ≠ 1
    intro a ha
    have hxalg : IsAlgebraic ℚ x := by
      by_cases ha0 : a = 0
      · -- a = 0: a•x = 0 ≠ 1: contradiction
        have ha' : a • x = 1 := by simpa using ha
        have hzero : (0 : ℂ) = 1 := by
          simpa [ha0, Algebra.smul_def] using ha'
        exact False.elim (by norm_num at hzero)
      · -- x = 1/a algebraic
        have hxeq : x = ((a⁻¹ : ℚ) : ℂ) := by
          -- a • x = 1 → x = a⁻¹
          calc
            x = (a⁻¹ : ℚ) • (a • x) := by
              rw [← mul_smul, inv_mul_cancel₀ ha0]
              simp
            _ = (a⁻¹ : ℚ) • (1 : ℂ) := by
              have ha' : a • x = 1 := by simpa using ha
              rw [ha']
            _ = ((a⁻¹ : ℚ) : ℂ) := by
              simp [Algebra.smul_def]
        rw [hxeq]
        exact isAlgebraic_ratCast (R := ℚ) (A := ℂ) (a⁻¹ : ℚ)
    exact False.elim (hx hxalg)


/-- `1` and `ζ(2) = π²/6` are linearly independent over `ℚ` (first fragment of
CDT Theorem A; the full theorem needs the third number `L(2,χ₋₃)`). -/
theorem linearIndependent_one_riemannZeta_two : LinearIndependent ℚ ![1, riemannZeta 2] :=
  linearIndependent_pair_one_of_transcendental transcendental_riemannZeta_two_complex

/-- The complex logarithm of an algebraic number `z ∉ {0,1}` is transcendental
over ℚ (`cexp (log z) = z`, and `log z ≠ 0` since `z ≠ 1`). -/
theorem log_complex_transcendental (z : ℂ) (hzalg : IsAlgebraic ℚ z) (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) : Transcendental ℚ (Complex.log z) := by
  by_contra htr
  have hlog : IsAlgebraic ℚ (Complex.log z) := (not_not.mp htr)
  have htrz := cexp_transcendental_of_algebraic_ne_zero (z := Complex.log z) hlog
  have hlog0 : Complex.log z ≠ 0 := by
    intro h
    have hc := congrArg Complex.exp h
    rw [Complex.exp_log hz0] at hc
    have hc' : z = 1 := by simpa using hc
    exact hz1 hc'
  exact htrz hlog0 (by
    rw [Complex.exp_log hz0]
    exact hzalg)

end Submission.Transcendence

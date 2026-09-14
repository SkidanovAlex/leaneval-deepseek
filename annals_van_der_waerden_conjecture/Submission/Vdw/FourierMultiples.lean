import Mathlib
import Submission.Vdw.FourierExpand
import Submission.Vdw.ResidueIndex

open Polynomial Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The Fourier transform of the indicator of the multiples of a monic divisor

Step 1 of the analysis of the paper's Proposition `ftgen2` (Roadmap
Session-145/146).  For monic `P : (ZMod p)[X]` of degree `d ≤ n` the monic
degree-`n` multiples of `P` are exactly `P·(X^{n-d} + ofFn g)`,
`g : Fin (n-d) → ZMod p` (`exists_cofactor`, `multiples_eq_image`,
`cofactor_inj`), so that for any weight

    `Σ_{v : P | m_n v} f v = Σ_{g} f (toFn n (P·m_{n-d} g))`
    (`sum_multiples_eq_sum_cofactor`).

The character argument is *affine* in `g` (`sum_coeff_multiples`):

    `Σ_i a_i (P·m_{n-d} g)_i = c(a) + Σ_j g_j·b(a)_j`,
    `c(a) = Σ_i a_i (P·X^{n-d})_i`,  `b(a)_j = Σ_i a_i (P·X^j)_i`,

and orthogonality (`FourierExpand.sum_stdAddChar_coord`) therefore gives the
exact transform of the multiple-indicator
(`sum_stdAddChar_multiples`):

    `Σ_{v : P | m_n v} χ(a·v) = χ(c(a))·[b(a) = 0]·p^{n-d}`.

The vanishing condition `b(a) = 0` is exactly "`a` annihilates the direction
space `P·V^{≤ n-1-d}`" (`U^0_P` in the paper's notation): this is the
linear-algebra input used to count the pairs `(P, a)` with `a ∈ W_P`, which is
the elementary part (`d < n`) of the `ftgen2` proof.

Axioms: propext / Classical.choice / Quot.sound only.
-/
namespace Submission.Vdw
noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]

local instance decDvdPoly : ∀ (P Q : (ZMod p)[X]), Decidable (P ∣ Q) :=
  fun _ _ => Classical.dec _

/-- Every monic degree-`n` multiple of a monic `P` of degree `d ≤ n` factors as
`P·q` with `q` monic of degree `n - d`. -/
lemma exists_cofactor (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic) (hd : P.natDegree ≤ n)
    {v : Fin n → ZMod p} (hv : P ∣ monicOfTrail n v) :
    ∃ q : (ZMod p)[X], q.Monic ∧ q.natDegree = n - P.natDegree
      ∧ P * q = monicOfTrail n v := by
  obtain ⟨q, hq⟩ := hv
  have hm : (monicOfTrail n v).Monic := monicOfTrail_monic n v
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hm.ne_zero hq
  have hlc : q.Monic := by
    have h1 : (P * q).leadingCoeff = 1 := by rw [← hq]; exact hm.leadingCoeff
    rw [leadingCoeff_mul, hP.leadingCoeff, one_mul] at h1
    exact h1
  have hdeg : q.natDegree = n - P.natDegree := by
    have h2 := natDegree_mul hP.ne_zero hq0
    rw [← hq, monicOfTrail_natDegree] at h2
    omega
  exact ⟨q, hlc, hdeg, hq.symm⟩

/-- The a priori "cofactor vector" of a monic degree-`n` multiple of `P`. -/
noncomputable def cofactorVec (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic)
    (hd : P.natDegree ≤ n) (v : {v : Fin n → ZMod p // P ∣ monicOfTrail n v}) :
    Fin (n - P.natDegree) → ZMod p :=
  Polynomial.toFn (n - P.natDegree) (Classical.choose (exists_cofactor n P hP hd v.2))

lemma cofactorVec_spec (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic) (hd : P.natDegree ≤ n)
    (v : {v : Fin n → ZMod p // P ∣ monicOfTrail n v}) :
    P * monicOfTrail (n - P.natDegree) (cofactorVec n P hP hd v) = monicOfTrail n v.1 := by
  have h := (Classical.choose_spec (exists_cofactor n P hP hd v.2))
  obtain ⟨hqm, hqd, hqe⟩ := h
  rw [cofactorVec, monicOfTrail_toFn (n - P.natDegree) _ hqm hqd]
  exact hqe

/-- The set of monic degree-`n` multiples of a monic `P` of degree `d ≤ n` is
the image of the cofactor parametrisation `g ↦ toFn n (P·(X^{n-d} + ofFn g))`. -/
lemma multiples_eq_image (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic) (hd : P.natDegree ≤ n) :
    (Finset.univ.filter (fun v : Fin n → ZMod p => P ∣ monicOfTrail n v))
      = Finset.univ.image (fun g : Fin (n - P.natDegree) → ZMod p =>
          Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) := by
  classical
  have hdeg : ∀ g : Fin (n - P.natDegree) → ZMod p,
      (P * monicOfTrail (n - P.natDegree) g).natDegree = n := by
    intro g
    rw [natDegree_mul hP.ne_zero (monicOfTrail_monic _ _).ne_zero,
      monicOfTrail_natDegree, Nat.add_sub_cancel' hd]
  have hmon : ∀ g : Fin (n - P.natDegree) → ZMod p,
      (P * monicOfTrail (n - P.natDegree) g).Monic :=
    fun g => hP.mul (monicOfTrail_monic _ _)
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hv
    exact ⟨cofactorVec n P hP hd ⟨v, hv⟩, by
      have h := cofactorVec_spec n P hP hd ⟨v, hv⟩
      rw [h]
      exact toFn_monicOfTrail n v⟩
  · rintro ⟨g, -, rfl⟩
    rw [monicOfTrail_toFn n (P * monicOfTrail (n - P.natDegree) g) (hmon g) (hdeg g)]
    exact dvd_mul_right P _

/-- The injectivity of the cofactor parametrisation. -/
lemma cofactor_inj (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic) (hd : P.natDegree ≤ n) :
    Function.Injective (fun g : Fin (n - P.natDegree) → ZMod p =>
      Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) := by
  intro g₁ g₂ hg
  have hdeg : ∀ g : Fin (n - P.natDegree) → ZMod p,
      (P * monicOfTrail (n - P.natDegree) g).natDegree = n := by
    intro g
    rw [natDegree_mul hP.ne_zero (monicOfTrail_monic _ _).ne_zero,
      monicOfTrail_natDegree, Nat.add_sub_cancel' hd]
  have hmon : ∀ g : Fin (n - P.natDegree) → ZMod p,
      (P * monicOfTrail (n - P.natDegree) g).Monic :=
    fun g => hP.mul (monicOfTrail_monic _ _)
  have heq : P * monicOfTrail (n - P.natDegree) g₁
      = P * monicOfTrail (n - P.natDegree) g₂ := by
    have h := congrArg (fun w : Fin n → ZMod p => monicOfTrail n w) hg
    rwa [monicOfTrail_toFn n _ (hmon g₁) (hdeg g₁),
      monicOfTrail_toFn n _ (hmon g₂) (hdeg g₂)] at h
  have h2 := mul_left_cancel₀ hP.ne_zero heq
  funext j
  have := congrArg (fun q : (ZMod p)[X] => q.coeff (j : ℕ)) h2
  rwa [monicOfTrail_coeff _ _ (j : Fin (n - P.natDegree)).isLt,
    monicOfTrail_coeff _ _ (j : Fin (n - P.natDegree)).isLt] at this

/-- **The reindexing of sums over the multiples of `P`**: summing over the
monic degree-`n` multiples of a monic `P` of degree `d ≤ n` is the same as
summing over the free cofactor vector `g : Fin (n-d) → ZMod p`. -/
theorem sum_multiples_eq_sum_cofactor (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic)
    (hd : P.natDegree ≤ n) (f : (Fin n → ZMod p) → ℂ) :
    (∑ v : Fin n → ZMod p, if P ∣ monicOfTrail n v then f v else 0)
      = ∑ g : Fin (n - P.natDegree) → ZMod p,
          f (Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) := by
  classical
  rw [← Finset.sum_filter, multiples_eq_image n P hP hd]
  rw [Finset.sum_image (fun x _ y _ hxy => cofactor_inj n P hP hd hxy)]

set_option maxHeartbeats 1600000 in
/-- **The character argument is affine in the cofactor vector.** -/
lemma sum_coeff_multiples (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic) (hd : P.natDegree ≤ n)
    (a : Fin n → ZMod p) (g : Fin (n - P.natDegree) → ZMod p) :
    (∑ i : Fin n, a i * (Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) i)
      = (∑ i : Fin n, a i * (P * X ^ (n - P.natDegree)).coeff (i : ℕ))
        + ∑ j : Fin (n - P.natDegree), g j *
            (∑ i : Fin n, a i * (P * X ^ (j : ℕ)).coeff (i : ℕ)) := by
  classical
  have hfac : P * monicOfTrail (n - P.natDegree) g
      = P * X ^ (n - P.natDegree) + ∑ j : Fin (n - P.natDegree), g j • (P * X ^ (j : ℕ)) := by
    rw [monicOfTrail, mul_add]
    congr 1
    rw [Polynomial.ofFn_eq_sum_monomial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul, mul_smul_comm]
  have hto : ∀ i : Fin n, (Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) i
      = (P * monicOfTrail (n - P.natDegree) g).coeff (i : ℕ) := fun i => rfl
  have hcoeff : ∀ i : Fin n, (P * monicOfTrail (n - P.natDegree) g).coeff (i : ℕ)
      = (P * X ^ (n - P.natDegree)).coeff (i : ℕ)
        + ∑ j : Fin (n - P.natDegree), g j * (P * X ^ (j : ℕ)).coeff (i : ℕ) := by
    intro i
    rw [hfac, Polynomial.coeff_add]
    congr 1
    rw [← Polynomial.lcoeff_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, Polynomial.lcoeff_apply, smul_eq_mul]
  have hstep1 : (∑ i : Fin n, a i * (Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) i)
      = ∑ i : Fin n, a i * ((P * X ^ (n - P.natDegree)).coeff (i : ℕ)
          + ∑ j : Fin (n - P.natDegree), g j * (P * X ^ (j : ℕ)).coeff (i : ℕ)) :=
    Finset.sum_congr rfl (fun i _ => by rw [hto i, hcoeff i])
  rw [hstep1]
  have hstep2 : (∑ i : Fin n, a i * ((P * X ^ (n - P.natDegree)).coeff (i : ℕ)
          + ∑ j : Fin (n - P.natDegree), g j * (P * X ^ (j : ℕ)).coeff (i : ℕ)))
      = ∑ i : Fin n, (a i * (P * X ^ (n - P.natDegree)).coeff (i : ℕ)
          + a i * ∑ j : Fin (n - P.natDegree), g j * (P * X ^ (j : ℕ)).coeff (i : ℕ)) :=
    Finset.sum_congr rfl (fun i _ => by rw [mul_add])
  rw [hstep2, Finset.sum_add_distrib]
  congr 1
  · have hstep3 : (∑ i : Fin n, a i * (∑ j : Fin (n - P.natDegree),
          g j * (P * X ^ (j : ℕ)).coeff (i : ℕ)))
        = ∑ j : Fin (n - P.natDegree), g j *
            (∑ i : Fin n, a i * (P * X ^ (j : ℕ)).coeff (i : ℕ)) := by
      have h1 : (∑ i : Fin n, a i * (∑ j : Fin (n - P.natDegree),
            g j * (P * X ^ (j : ℕ)).coeff (i : ℕ)))
          = ∑ i : Fin n, ∑ j : Fin (n - P.natDegree),
              a i * (g j * (P * X ^ (j : ℕ)).coeff (i : ℕ)) :=
        Finset.sum_congr rfl (fun i _ => Finset.mul_sum ..)
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    exact hstep3

set_option maxHeartbeats 4000000 in
/-- **The Fourier transform of the multiple-indicator.**  For monic `P` of
degree `d ≤ n` the character sum over the monic degree-`n` multiples of `P`
equals `p^{n-d}` times a unit phase when the direction functional
`b(a)_j = Σ_i a_i (P·X^j)_i` vanishes, and `0` otherwise. -/
theorem sum_stdAddChar_multiples (n : ℕ) (P : (ZMod p)[X]) (hP : P.Monic)
    (hd : P.natDegree ≤ n) (a : Fin n → ZMod p) :
    (∑ v : Fin n → ZMod p,
        if P ∣ monicOfTrail n v then ZMod.stdAddChar (∑ i : Fin n, a i * v i) else 0)
      = if (fun j : Fin (n - P.natDegree) =>
            ∑ i : Fin n, a i * (P * X ^ (j : ℕ)).coeff i) = 0
        then ((p : ℂ)) ^ (n - P.natDegree) *
          ZMod.stdAddChar (∑ i : Fin n, a i * (P * X ^ (n - P.natDegree)).coeff i)
        else 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let b : Fin (n - P.natDegree) → ZMod p :=
    fun j => ∑ i : Fin n, a i * (P * X ^ (j : ℕ)).coeff (i : ℕ)
  let c : ZMod p := ∑ i : Fin n, a i * (P * X ^ (n - P.natDegree)).coeff (i : ℕ)
  change (∑ v : Fin n → ZMod p,
        if P ∣ monicOfTrail n v then ZMod.stdAddChar (∑ i : Fin n, a i * v i) else 0)
      = if b = 0 then ((p : ℂ)) ^ (n - P.natDegree) * ZMod.stdAddChar c else 0
  rw [sum_multiples_eq_sum_cofactor n P hP hd
    (fun v => ZMod.stdAddChar (∑ i : Fin n, a i * v i))]
  have hstep : (∑ g : Fin (n - P.natDegree) → ZMod p, ZMod.stdAddChar
        (∑ i : Fin n, a i * (Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) i))
      = ∑ g : Fin (n - P.natDegree) → ZMod p, ZMod.stdAddChar (c + ∑ j, g j * b j) :=
    Finset.sum_congr rfl (fun g _ => by
      rw [show (∑ i : Fin n, a i *
            (Polynomial.toFn n (P * monicOfTrail (n - P.natDegree) g)) i)
          = (∑ i : Fin n, a i * (P * X ^ (n - P.natDegree)).coeff (i : ℕ))
            + ∑ j : Fin (n - P.natDegree), g j *
                (∑ i : Fin n, a i * (P * X ^ (j : ℕ)).coeff (i : ℕ)) from
          sum_coeff_multiples n P hP hd a g])
  rw [hstep]
  have hstep2 : (∑ g : Fin (n - P.natDegree) → ZMod p,
        ZMod.stdAddChar (c + ∑ j, g j * b j))
      = ZMod.stdAddChar c * ∑ g : Fin (n - P.natDegree) → ZMod p,
          ZMod.stdAddChar (∑ j, g j * b j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [ZMod.stdAddChar.map_add_eq_mul]
  rw [hstep2]
  have hsum : (∑ g : Fin (n - P.natDegree) → ZMod p,
        ZMod.stdAddChar (∑ j : Fin (n - P.natDegree), g j * b j))
      = if b = 0 then (p : ℂ) ^ (n - P.natDegree) else 0 :=
    sum_stdAddChar_coord p (n - P.natDegree) b
  rw [hsum]
  by_cases hb : b = 0
  · rw [if_pos hb, if_pos hb]; ring
  · rw [if_neg hb, if_neg hb, mul_zero]

end
end Submission.Vdw

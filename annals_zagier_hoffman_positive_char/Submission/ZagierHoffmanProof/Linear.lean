import Submission.ZagierHoffmanProof.PowerSum

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Degree-one power sums

For `d = 1` the only monic polynomial of degree `< 1` is the constant `1`.
Hence every depth-`2` power sum `S_1(s₀,s₁)` collapses to the depth-one
`P_1(s₀)`.  This is the base case `d = 1` of Thakur's product identity
(`thakur_prod_one` in `PowerSum.lean`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The only monic polynomial of natural degree `0` is the constant `1`. -/
lemma monic_deg_zero_eq_one (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = 0) :
    p = 1 := by
  apply Polynomial.ext
  intro i
  by_cases hi : i = 0
  · subst hi
    simpa [hdeg] using hp.coeff_natDegree
  · have hlt : p.natDegree < i := by omega
    have hzero : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    have hone : (1 : F[X]).coeff i = 0 := by
      rw [Polynomial.coeff_one, if_neg hi]
    rw [hzero, hone]

/-- The tail entry of a depth-two tuple whose head has degree `1` is the constant
polynomial `1`. -/
lemma tail_of_deg_one (hr : 0 < 2) (a : monicStrictAntiNatDegree F 2)
    (ha : a ∈ blockSet F 2 hr 1) :
    a.val ⟨1, by omega⟩ = 1 := by
  have hdeg0 : (a.val ⟨0, hr⟩).natDegree = 1 := by simpa [blockSet] using ha
  have h01 : (⟨0, hr⟩ : Fin 2) < ⟨1, by omega⟩ := (Fin.mk_lt_mk).2 (by omega)
  have hlt : (a.val ⟨1, by omega⟩).natDegree < (a.val ⟨0, hr⟩).natDegree := by
    simpa using a.2.1 h01
  exact monic_deg_zero_eq_one F (a.val ⟨1, by omega⟩) (a.2.2 ⟨1, by omega⟩) (by omega)

/-- The function `(p, 1)` on `Fin 2` (head `p`, tail constant `1`). -/
noncomputable def twoTupleFn (p : F[X]) : Fin 2 → F[X] :=
  fun i => if (i : ℕ) = 0 then p else 1

lemma twoTupleFn_zero (p : F[X]) : twoTupleFn F p ⟨0, by omega⟩ = p := by
  simp [twoTupleFn]

lemma twoTupleFn_one (p : F[X]) : twoTupleFn F p ⟨1, by omega⟩ = 1 := by
  simp [twoTupleFn]

lemma twoTupleFn_ofNat_zero (p : F[X]) : twoTupleFn F p (0 : Fin 2) = p := by
  simp [twoTupleFn]

lemma twoTupleFn_ofNat_one (p : F[X]) : twoTupleFn F p (1 : Fin 2) = 1 := by
  simp [twoTupleFn]

/-- `(p, 1)` is strictly degree-decreasing when `p` has degree `1`. -/
lemma strictAnti_twoTupleFn (p : F[X]) (hdeg : p.natDegree = 1) :
    StrictAnti (Polynomial.natDegree ∘ twoTupleFn F p) := by
  intro i j hij
  change Polynomial.natDegree (twoTupleFn F p j) < Polynomial.natDegree (twoTupleFn F p i)
  have hijn : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
  have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
    have hlt : (i : ℕ) < 2 := i.isLt
    omega
  have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by
    have hlt : (j : ℕ) < 2 := j.isLt
    omega
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · -- i = 0, j = 0: impossible
    exfalso
    omega
  · -- i = 0, j = 1: head degree 1 > tail degree 0
    simp [twoTupleFn, hi, hj]
    rw [hdeg]
    simp
  · exfalso
    omega
  · exfalso
    omega

/-- All entries of `(p, 1)` are monic when `p` is monic. -/
lemma monic_twoTupleFn (p : F[X]) (hp : p.Monic) :
    ∀ i : Fin 2, (twoTupleFn F p i).Monic := by
  intro i
  fin_cases i <;> simp [twoTupleFn, hp]

/-- The tuple (`p`, `1`) for a monic degree-one `p`. -/
noncomputable def twoTupleHead (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = 1) :
    monicStrictAntiNatDegree F 2 :=
  ⟨twoTupleFn F p, ⟨strictAnti_twoTupleFn F p hdeg, monic_twoTupleFn F p hp⟩⟩

/-- The tuple (`p`, `1`) belongs to the degree-`1` block of length `2`. -/
lemma twoTupleHead_mem (hr : 0 < 2) (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = 1) :
    twoTupleHead F p hp hdeg ∈ blockSet F 2 hr 1 := by
  change ((twoTupleHead F p hp hdeg).val ⟨0, hr⟩).natDegree = 1
  simp [twoTupleHead, twoTupleFn, hdeg]

/-- `1 : RatFunc F`, embedded in the completion, has all positive powers equal to `1`. -/
lemma coe_one_inv (n : ℕ) :
    (((1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹ =
      (1 : RatFunc.CompletionAtInfty F) := by
  change ((1 : RatFunc.CompletionAtInfty F) ^ n)⁻¹ = (1 : RatFunc.CompletionAtInfty F)
  simp

/-- `1 : F[X]`, pushed through `RatFunc` and into the completion, is the `1` of the
completion, so its positive powers are `1`. -/
lemma coe_poly_one_inv (n : ℕ) :
    ((((1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ n)⁻¹ =
      (1 : RatFunc.CompletionAtInfty F) := by
  rw [show (((1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) =
      (1 : RatFunc.CompletionAtInfty F) by
        rw [show ((1 : F[X]) : RatFunc F) = (1 : RatFunc F) by simp]
        rfl]
  simp

/-- The zeta summand of the tuple (`p`,`1`) is `p ^ (-s₀)`. -/
lemma zetaTerm_pair (𝔰 : Fin 2 → ℕ+) (p : F[X]) (hp : p.Monic) (hdeg : p.natDegree = 1) :
    zetaTerm F 𝔰 (twoTupleHead F p hp hdeg) =
      ((((p : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, by omega⟩ : ℕ))⁻¹) := by
  unfold zetaTerm twoTupleHead
  rw [Fin.prod_univ_two]
  simp [twoTupleFn_ofNat_zero, twoTupleFn_ofNat_one]
  rw [coe_one_inv F (𝔰 (1 : Fin 2) : ℕ)]
  rw [one_mul]

/-- A depth-`2` strictly degree-decreasing monic tuple whose head has degree `1`
is (`p`, `1`) for a unique monic degree-one `p`. -/
noncomputable def twoHeadEquiv (hr : 0 < 2) :
    {a : monicStrictAntiNatDegree F 2 // a ∈ blockSet F 2 hr 1} ≃ HeadD F 1 where
  toFun a := ⟨a.1.val ⟨0, hr⟩, by
    constructor
    · exact a.1.2.2 ⟨0, hr⟩
    · simpa [blockSet] using a.2⟩
  invFun p := ⟨twoTupleHead F p.1 p.2.1 p.2.2, twoTupleHead_mem F hr p.1 p.2.1 p.2.2⟩
  left_inv := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [twoTupleHead, twoTupleFn]
    · have htail : a.1.val ⟨1, by omega⟩ = 1 := tail_of_deg_one F hr a.1 a.2
      simp [twoTupleHead, twoTupleFn]
      exact htail.symm
  right_inv := by
    intro p
    apply Subtype.ext
    simp [twoTupleHead, twoTupleFn]

/-- The zeta summand of the reconstructed tuple (`p`,`1`) is `p ^ (-s₀)`. -/
lemma zetaTerm_two_one (𝔰 : Fin 2 → ℕ+) (hr : 0 < 2) (p : HeadD F 1) :
    zetaTerm F 𝔰 ((twoHeadEquiv F hr).symm p).1 =
      ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr⟩ : ℕ))⁻¹) := by
  change zetaTerm F 𝔰 (twoTupleHead F p.1 p.2.1 p.2.2) =
      ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr⟩ : ℕ))⁻¹)
  exact zetaTerm_pair F 𝔰 p.1 p.2.1 p.2.2

/-- At degree `1`, the depth-two block sum collapses to the depth-one power sum of
the first exponent: the only possible tail is the constant polynomial `1`. -/
lemma S_two_d1_eq_P_head (𝔰 : Fin 2 → ℕ+) (hr : 0 < 2) :
    S F 2 hr 𝔰 1 = P F 1 (𝔰 ⟨0, hr⟩) := by
  classical
  let e := twoHeadEquiv F hr
  unfold S P
  calc
    (∑' a : {a : monicStrictAntiNatDegree F 2 // a ∈ blockSet F 2 hr 1},
        zetaTerm F 𝔰 a.1)
        = ∑' p : HeadD F 1, zetaTerm F 𝔰 (e.symm p).1 := by
          symm
          calc
            (∑' p : HeadD F 1, zetaTerm F 𝔰 (e.symm p).1)
                = ∑' a : {a : monicStrictAntiNatDegree F 2 // a ∈ blockSet F 2 hr 1},
                    zetaTerm F 𝔰 (e.symm (e a)).1 := by
                  exact (Equiv.tsum_eq (e := e)
                    (f := fun p : HeadD F 1 => zetaTerm F 𝔰 (e.symm p).1)).symm
            _ = ∑' a : {a : monicStrictAntiNatDegree F 2 // a ∈ blockSet F 2 hr 1},
                    zetaTerm F 𝔰 a.1 := by
                  apply tsum_congr
                  intro a
                  rw [Equiv.symm_apply_apply e a]
    _ = ∑' p : HeadD F 1,
          ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 ⟨0, hr⟩ : ℕ))⁻¹) := by
          apply tsum_congr
          intro p
          exact zetaTerm_two_one F 𝔰 hr p
    _ = P F 1 (𝔰 ⟨0, hr⟩) := by rfl

end ZagierHoffmanPositiveChar

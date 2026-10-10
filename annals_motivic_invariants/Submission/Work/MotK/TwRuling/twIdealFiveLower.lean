import Mathlib
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.TwRuling.linearIndependent_of_key
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The degree-5 part of the ideal of the twisted Klein Pfaffians has dimension at least 101

For a field `R` and `a b h : R` with `a, b, h ≠ 0`, the span `J` of the 175 products of one of the
five twisted Pfaffians `kleinTwP (C a) (C b) (C h) (fun i => X i)` with a degree-3 monomial has
`R`-dimension at least `101` (in fact exactly `101`).

The route is the one of `GUIDE_twIdealFiveLower.md`: give `101` explicit elements of `J`, each a
Pfaffian times a degree-3 cofactor, with pairwise distinct leading monomials for the weighted
monomial order with weights `(3,4,4,1,1)`.  The five Pfaffians are first expanded in monomial form
(`qk_eq`, `expand`); the table of the `101` rows `(m, k, m')` is `tblK`/`tblMu`; the leading-monomial
bookkeeping (`keyF_le`, `keyF_inj`) and the degree conditions are finite computations (`decide`);
and `Work.MotK.TwRuling.linearIndependent_of_key` turns the distinct leading monomials into linear
independence.  Finally `Submodule.finrank_mono` compares the span of these `101` elements with `J`,
for which `J` is shown to be finite-dimensional via `Module.Finite.span_of_finite` and the finiteness
of the subtype of degree-3 exponent vectors.

The statement itself is unchanged (it is the requirement of the companion file
`twIdeal_five_finrank`).
-/

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.MotK.TwRuling

noncomputable section

variable {R : Type*} [Field R]

/-- The Finsupp with the same coordinates as `v`. -/
def toF (v : Fin 5 → ℕ) : Fin 5 →₀ ℕ := ∑ i, Finsupp.single i (v i)

theorem toF_apply (v : Fin 5 → ℕ) (i : Fin 5) : toF v i = v i := by
  rw [toF, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem toF_injective : Function.Injective (toF : (Fin 5 → ℕ) → (Fin 5 →₀ ℕ)) := by
  intro u v h
  funext i
  rw [← toF_apply u i, h, toF_apply v i]

/-- The monomial with exponent vector `v`. -/
def monF (v : Fin 5 → ℕ) : MvPolynomial (Fin 5) R := ∏ i, MvPolynomial.X i ^ v i

theorem monF_eq_monomial (v : Fin 5 → ℕ) :
    monF (R := R) v = MvPolynomial.monomial (toF v) 1 := by
  simp only [monF, MvPolynomial.X_pow_eq_monomial]
  rw [toF]
  rw [← MvPolynomial.monomial_sum_one Finset.univ (fun i => Finsupp.single i (v i))]

theorem monF_add (u v : Fin 5 → ℕ) : monF (R := R) (u + v) = monF u * monF v := by
  simp only [monF]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.add_apply, pow_add]

theorem coeff_monF (v : Fin 5 → ℕ) (m : Fin 5 →₀ ℕ) :
    (monF (R := R) v).coeff m = if toF v = m then 1 else 0 := by
  rw [monF_eq_monomial, MvPolynomial.coeff_monomial]

theorem coeff_monF_self (v : Fin 5 → ℕ) : (monF (R := R) v).coeff (toF v) = 1 := by
  rw [coeff_monF]; simp

theorem coeff_monF_of_ne {v w : Fin 5 → ℕ} (h : toF v ≠ toF w) :
    (monF (R := R) v).coeff (toF w) = 0 := by
  rw [coeff_monF]; simp [h]

theorem coeff_monF_ne_zero_iff {v : Fin 5 → ℕ} {m : Fin 5 →₀ ℕ} :
    (monF (R := R) v).coeff m ≠ 0 ↔ toF v = m := by
  rw [coeff_monF]; simp

theorem deg_toF (v : Fin 5 → ℕ) :
    (toF v).support.sum (fun x => (toF v) x) = ∑ i, v i := by
  have h1 : (toF v).support.sum (fun x => (toF v) x) = ∑ x : Fin 5, (toF v) x := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa [Finsupp.mem_support_iff] using hx)]
  rw [h1]
  exact Finset.sum_congr rfl (fun i _ => toF_apply v i)

/-- The three exponent vectors of the five twisted Pfaffians; `j = 0` is the leading monomial. -/
def nExp : Fin 5 → Fin 3 → Fin 5 → ℕ :=
  ![![![2,0,0,0,0], ![0,0,1,1,0], ![0,1,0,0,1]],
    ![![0,0,2,0,0], ![1,0,0,0,1], ![0,1,0,1,0]],
    ![![0,1,1,0,0], ![0,0,0,0,2], ![1,0,0,1,0]],
    ![![0,2,0,0,0], ![0,0,0,1,1], ![1,0,1,0,0]],
    ![![1,1,0,0,0], ![0,0,0,2,0], ![0,0,1,0,1]]]

/-- The three coefficients of the five twisted Pfaffians. -/
def nCf (a b h : R) : Fin 5 → Fin 3 → R :=
  ![![-(a*b), a^2*h, -(b^2*h)],
    ![-(a*b), a^2, -(b^2)],
    ![a^2, -(a*b*h), -(b^2)],
    ![-(a*b), a^2*h, -(b^2)],
    ![a^2, -(a*b*h), -(b^2*h)]]

theorem nExp_ne (k : Fin 5) {j j' : Fin 3} (h : j ≠ j') : nExp k j ≠ nExp k j' := by
  fin_cases k <;> fin_cases j <;> fin_cases j' <;> first | exact absurd rfl h | decide

theorem nCf_ne_zero (a b h : R) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (k : Fin 5) (j : Fin 3) :
    nCf a b h k j ≠ 0 := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have ha2h : a ^ 2 * h ≠ 0 := mul_ne_zero ha2 hh
  have hb2h : b ^ 2 * h ≠ 0 := mul_ne_zero hb2 hh
  have habh : a * b * h ≠ 0 := mul_ne_zero hab hh
  fin_cases k <;> fin_cases j <;> simp [nCf, hab, ha2, hb2, ha2h, hb2h, habh]

theorem qk_eq (a b h : R) (k : Fin 5) :
    Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.X i) k
      = ∑ j : Fin 3, MvPolynomial.C (nCf a b h k j) * monF (nExp k j) := by
  fin_cases k <;>
    simp [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2,
      Work.MotK.kleinTwP3, Work.MotK.kleinTwP4, nCf, nExp, monF, Fin.prod_univ_five,
      Fin.sum_univ_three, MvPolynomial.C_mul, MvPolynomial.C_pow] <;>
    refl_ring1

theorem expand (a b h : R) (k : Fin 5) (μ : Fin 5 → ℕ) :
    Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun i => MvPolynomial.X i) k * monF μ
      = ∑ j : Fin 3, MvPolynomial.C (nCf a b h k j) * monF (nExp k j + μ) := by
  rw [qk_eq a b h k, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← monF_add]


/-- The five Pfaffian indices of the 101 rows. -/
def tblK : Fin 101 → Fin 5 :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 2, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The degree-3 cofactors of the 101 rows. -/
def tblMu : Fin 101 → Fin 5 → ℕ :=
  ![![0, 0, 0, 0, 3],
    ![0, 0, 0, 1, 2],
    ![0, 0, 0, 2, 1],
    ![0, 0, 0, 3, 0],
    ![0, 0, 1, 0, 2],
    ![0, 0, 1, 1, 1],
    ![0, 0, 1, 2, 0],
    ![0, 0, 2, 0, 1],
    ![0, 0, 2, 1, 0],
    ![0, 0, 3, 0, 0],
    ![0, 0, 0, 0, 3],
    ![0, 0, 0, 1, 2],
    ![0, 0, 0, 2, 1],
    ![0, 0, 0, 3, 0],
    ![0, 1, 0, 0, 2],
    ![0, 1, 0, 1, 1],
    ![0, 1, 0, 2, 0],
    ![0, 1, 1, 0, 1],
    ![0, 1, 1, 1, 0],
    ![0, 1, 2, 0, 0],
    ![0, 0, 0, 0, 3],
    ![0, 0, 0, 1, 2],
    ![0, 0, 0, 2, 1],
    ![0, 0, 0, 3, 0],
    ![0, 1, 0, 0, 2],
    ![0, 1, 0, 1, 1],
    ![0, 1, 0, 2, 0],
    ![0, 2, 0, 0, 1],
    ![0, 2, 0, 1, 0],
    ![0, 2, 1, 0, 0],
    ![0, 1, 0, 0, 2],
    ![0, 1, 0, 1, 1],
    ![0, 1, 0, 2, 0],
    ![0, 2, 0, 0, 1],
    ![0, 2, 0, 1, 0],
    ![0, 3, 0, 0, 0],
    ![0, 2, 0, 0, 1],
    ![0, 2, 0, 1, 0],
    ![0, 3, 0, 0, 0],
    ![0, 3, 0, 0, 0],
    ![1, 0, 0, 0, 2],
    ![1, 0, 0, 1, 1],
    ![1, 0, 0, 2, 0],
    ![1, 0, 1, 0, 1],
    ![1, 0, 1, 1, 0],
    ![1, 0, 2, 0, 0],
    ![0, 0, 0, 0, 3],
    ![0, 0, 0, 1, 2],
    ![0, 0, 0, 2, 1],
    ![0, 0, 0, 3, 0],
    ![1, 0, 0, 0, 2],
    ![1, 0, 0, 1, 1],
    ![1, 0, 0, 2, 0],
    ![1, 1, 0, 0, 1],
    ![1, 1, 0, 1, 0],
    ![1, 1, 1, 0, 0],
    ![1, 0, 0, 0, 2],
    ![1, 0, 0, 1, 1],
    ![1, 0, 0, 2, 0],
    ![1, 1, 0, 0, 1],
    ![1, 1, 0, 1, 0],
    ![1, 2, 0, 0, 0],
    ![1, 1, 0, 0, 1],
    ![1, 1, 0, 1, 0],
    ![1, 2, 0, 0, 0],
    ![1, 2, 0, 0, 0],
    ![0, 0, 0, 0, 3],
    ![0, 0, 0, 1, 2],
    ![0, 0, 0, 2, 1],
    ![0, 0, 0, 3, 0],
    ![0, 0, 1, 0, 2],
    ![0, 0, 1, 1, 1],
    ![0, 0, 1, 2, 0],
    ![0, 0, 2, 0, 1],
    ![0, 0, 2, 1, 0],
    ![0, 0, 3, 0, 0],
    ![0, 1, 0, 0, 2],
    ![0, 1, 0, 1, 1],
    ![0, 1, 0, 2, 0],
    ![0, 1, 1, 0, 1],
    ![0, 1, 1, 1, 0],
    ![0, 1, 2, 0, 0],
    ![0, 2, 0, 0, 1],
    ![0, 2, 0, 1, 0],
    ![0, 2, 1, 0, 0],
    ![0, 3, 0, 0, 0],
    ![1, 0, 0, 0, 2],
    ![1, 0, 0, 1, 1],
    ![1, 0, 0, 2, 0],
    ![1, 0, 1, 0, 1],
    ![1, 0, 1, 1, 0],
    ![1, 0, 2, 0, 0],
    ![1, 1, 0, 0, 1],
    ![1, 1, 0, 1, 0],
    ![1, 1, 1, 0, 0],
    ![1, 2, 0, 0, 0],
    ![2, 0, 0, 0, 1],
    ![2, 0, 0, 1, 0],
    ![2, 0, 1, 0, 0],
    ![2, 1, 0, 0, 0],
    ![3, 0, 0, 0, 0]]

/-- `tblE i j` is the `j`-th exponent vector of the `i`-th element. -/
def tblE (i : Fin 101) (j : Fin 3) : Fin 5 → ℕ := nExp (tblK i) j + tblMu i

/-- The key used to order monomials: weighted degree first (weights `3,4,4,1,1`), then the
base-`6` lexicographic value. -/
def keyF (v : Fin 5 → ℕ) : ℕ :=
  (3 * v 0 + 4 * v 1 + 4 * v 2 + v 3 + v 4) * 7776 +
    (1296 * v 0 + 216 * v 1 + 36 * v 2 + 6 * v 3 + v 4)

/-- The `i`-th of the 101 explicit elements of the degree-5 part. -/
def F (a b h : R) (i : Fin 101) : MvPolynomial (Fin 5) R :=
  Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun j => MvPolynomial.X j) (tblK i) * MvPolynomial.monomial (toF (tblMu i)) 1

theorem tblMu_deg : ∀ i : Fin 101, (∑ j : Fin 5, tblMu i j) = 3 := by decide

theorem keyF_le : ∀ (i : Fin 101) (j : Fin 3), keyF (tblE i j) ≤ keyF (tblE i 0) := by decide

theorem keyF_inj : Function.Injective (fun i : Fin 101 => keyF (tblE i 0)) := by decide

theorem F_eq_sum (a b h : R) (i : Fin 101) :
    F a b h i = ∑ j : Fin 3, MvPolynomial.C (nCf a b h (tblK i) j) * monF (tblE i j) := by
  rw [F, ← monF_eq_monomial]
  exact expand a b h (tblK i) (tblMu i)

theorem coeff_F_self (a b h : R) (i : Fin 101) :
    (F a b h i).coeff (toF (tblE i 0)) = nCf a b h (tblK i) 0 := by
  rw [F_eq_sum, MvPolynomial.coeff_sum, Finset.sum_eq_single (0 : Fin 3)]
  · rw [MvPolynomial.coeff_C_mul, coeff_monF_self, mul_one]
  · intro j _ hj
    rw [MvPolynomial.coeff_C_mul, coeff_monF_of_ne, mul_zero]
    intro hcontra
    have h1 : tblE i j = tblE i 0 := toF_injective hcontra
    have h2 : nExp (tblK i) j = nExp (tblK i) 0 := by
      funext x
      have := congrFun h1 x
      simp only [tblE, Pi.add_apply] at this
      exact Nat.add_right_cancel this
    exact nExp_ne (tblK i) hj h2
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 3)) h

theorem support_F (a b h : R) (i : Fin 101) (m : Fin 5 →₀ ℕ) (hm : m ∈ (F a b h i).support) :
    ∃ j : Fin 3, m = toF (tblE i j) := by
  rw [MvPolynomial.mem_support_iff] at hm
  rw [F_eq_sum, MvPolynomial.coeff_sum] at hm
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [MvPolynomial.coeff_C_mul] at hj
  have h2 : (monF (R := R) (tblE i j)).coeff m ≠ 0 := fun h => hj (by rw [h, mul_zero])
  exact ⟨j, (coeff_monF_ne_zero_iff.mp h2).symm⟩

theorem deg_tblMu (i : Fin 101) :
    (toF (tblMu i)).support.sum (fun x => (toF (tblMu i)) x) = 3 := by
  rw [deg_toF]
  exact tblMu_deg i

theorem F_mem (a b h : R) (i : Fin 101) :
    F a b h i ∈ Submodule.span R (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 3} =>
        Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1)) :=
  Submodule.subset_span ⟨(tblK i, ⟨toF (tblMu i), deg_tblMu i⟩), rfl⟩

theorem key_mem_le (a b h : R) (i : Fin 101) (m : Fin 5 →₀ ℕ) (hm : m ∈ (F a b h i).support) :
    keyF (fun j => m j) ≤ keyF (tblE i 0) := by
  obtain ⟨j, rfl⟩ := support_F a b h i m hm
  have h1 : (fun x => toF (tblE i j) x) = tblE i j := funext (fun x => toF_apply (tblE i j) x)
  rw [h1]
  exact keyF_le i j

end

/-- The subtype of degree-3 exponent vectors is finite. -/
theorem finite_finsupp_deg3 : Finite {m : Fin 5 →₀ ℕ // m.support.sum m = 3} := by
  have hbound : ∀ (m : {m : Fin 5 →₀ ℕ // m.support.sum m = 3}) (i : Fin 5), m.1 i < 4 := by
    intro m i
    have hle : m.1 i ≤ m.1.support.sum m.1 := by
      by_cases hi : i ∈ m.1.support
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
      · rw [Finsupp.mem_support_iff] at hi
        simp [not_not.mp hi]
    have := m.2
    omega
  refine Finite.of_injective (fun m => fun i => (⟨m.1 i, hbound m i⟩ : Fin 4)) ?_
  intro m m' h
  apply Subtype.ext
  exact Finsupp.ext (fun i => Fin.ext_iff.mp (congrFun h i))

theorem twIdealFiveLower (R : Type) [Field R] (a b h : R) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    101 ≤ Module.finrank R ↥(Submodule.span R (Set.range (fun q : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 3} =>
        Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1))) := by
  classical
  haveI hfinS : Finite {m : Fin 5 →₀ ℕ // m.support.sum m = 3} := finite_finsupp_deg3
  set g : Fin 5 × {m : Fin 5 →₀ ℕ // m.support.sum m = 3} → MvPolynomial (Fin 5) R :=
    fun q => Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun i => MvPolynomial.X i) q.1 * MvPolynomial.monomial q.2.1 1 with hg
  set J : Submodule R (MvPolynomial (Fin 5) R) := Submodule.span R (Set.range g) with hJ
  haveI hfinJ : Module.Finite R ↥J := by
    rw [hJ]
    exact Module.Finite.span_of_finite R (Set.finite_range g)
  set f : Fin 101 → MvPolynomial (Fin 5) R := fun i => F a b h i with hf
  have hcoeff : ∀ i, (f i).coeff (toF (tblE i 0)) ≠ 0 := by
    intro i
    show (F a b h i).coeff (toF (tblE i 0)) ≠ 0
    rw [coeff_F_self]
    exact nCf_ne_zero a b h ha hb hh (tblK i) 0
  have hmem : ∀ i m, m ∈ (f i).support → keyF (fun j => m j) ≤ keyF (tblE i 0) := by
    intro i m hm
    exact key_mem_le a b h i m hm
  have hLI : LinearIndependent R f :=
    linearIndependent_of_key toF keyF f (fun i => tblE i 0) (fun v j => toF_apply v j) hcoeff hmem
      keyF_inj
  have hle : Submodule.span R (Set.range f) ≤ J := by
    rw [hJ]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact F_mem a b h i
  have hcard : Module.finrank R ↥(Submodule.span R (Set.range f)) = 101 := by
    rw [finrank_span_eq_card hLI]; simp
  calc 101 = Module.finrank R ↥(Submodule.span R (Set.range f)) := hcard.symm
    _ ≤ Module.finrank R ↥J := Submodule.finrank_mono hle

end Work.MotK.TwRuling

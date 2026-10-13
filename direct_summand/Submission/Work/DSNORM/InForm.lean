import Submission.Work.DSNORM.Defs
import Submission.Work.DSNORM.PolynomialAux
import Submission.Work.DSNORM.regularSequence_quasiRegular
import Submission.Work.DSNORM.params_regularSequence
import Submission.Work.DSREG.Main

/-!
# DSNORM — the initial form of an element of a regular local ring

For a regular local ring `A`, the associated graded ring of `𝔪` is `k[X₁,…,X_d]`, where
`k = IsLocalRing.ResidueField A` and `d = nParams A = (maximalIdeal A).spanFinrank = ringKrullDim A`.
The informal element of `k[X]` that this file manipulates is the *initial form* `inForm A a` of
`a : A`, and its fundamental property is multiplicativity:

* `Work.DSNORM.inForm_mul` : `inForm (a * b) = inForm a * inForm b`;
* `Work.DSNORM.ord_mul` : `ord (a * b) = ord a + ord b`;
* `Work.DSNORM.inForm_eq_zero_iff` : `inForm a = 0 ↔ a = 0`;
* `Work.DSNORM.inForm_eval_secPoly` : `inForm` of the evaluation of a coefficient-wise lift of a
  homogeneous polynomial over `k` is that polynomial;
* `Work.DSNORM.exists_ord_lt_of_dvd` : if `inForm b ∣ inForm a` (with `a`, `b ≠ 0`) then there is
  `q : A` with `ord a < ord (a - q * b)` — the "successive approximation" step.

The point of the last statement is that it can be iterated: if `a / b` is integral over `A`, then at
every stage the initial form of `b` divides the initial form of the current remainder, so one
approximates `a / b` in `A` modulo arbitrarily high powers of `𝔪`, and Krull's intersection theorem
gives `b ∣ a`.  This is carried out in `Submission/Work/DSNORM/Integral.lean`.

The inputs from other files are the two base facts of the area,
`Work.DSNORM.coeff_mem_of_eval_mem_pow_succ` (a regular sequence is quasi-regular, Stacks 00LN),
`Work.DSNORM.isWeaklyRegular_params` (the parameters form a regular sequence), the polynomial
lemmas in `Submission/Work/DSNORM/PolynomialAux.lean` and `Work.DSREG.isDomain_of_isRegularLocalRing`.
-/

namespace Work.DSNORM

open scoped Pointwise

universe u

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- A regular local ring is a domain (this is the area DSREG). -/
instance instIsDomain : IsDomain A := Work.DSREG.isDomain_of_isRegularLocalRing A

/-- The parameters of a regular local ring satisfy the quasi-regularity condition: a homogeneous
polynomial of degree `n` whose value at the parameters lies in `𝔪 ^ (n + 1)` has all coefficients
in `𝔪`. -/
theorem coeff_mem_of_eval_params {n : ℕ} {F : MvPolynomial (Fin (nParams A)) A}
    (hF : F.IsHomogeneous n)
    (h : MvPolynomial.eval (params A) F ∈ IsLocalRing.maximalIdeal A ^ (n + 1)) :
    ∀ s, F.coeff s ∈ IsLocalRing.maximalIdeal A := by
  have h' : MvPolynomial.eval (params A) F ∈ (Ideal.span (Set.range (params A))) ^ (n + 1) := by
    rwa [params_span A]
  intro s
  have := regularSequence_quasiRegular (params A) (params_regularSequence A) F hF h' s
  rwa [params_span A] at this

/-- If the reduction modulo `𝔪` of a polynomial vanishes, then all its coefficients lie in `𝔪`. -/
theorem coeff_mem_of_map_residue_eq_zero {P : MvPolynomial (Fin (nParams A)) A}
    (h : P.map (IsLocalRing.residue A) = 0) (s : Fin (nParams A) →₀ ℕ) :
    P.coeff s ∈ IsLocalRing.maximalIdeal A := by
  have h1 : (IsLocalRing.residue A) (P.coeff s) = 0 := by
    have := congrArg (fun Q : MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A) =>
      Q.coeff s) h
    rwa [MvPolynomial.coeff_map (IsLocalRing.residue A) P s] at this
  exact (IsLocalRing.residue_eq_zero_iff _).mp h1

/-- If all coefficients of a polynomial lie in `𝔪` then its reduction modulo `𝔪` vanishes. -/
theorem map_residue_eq_zero_of_coeff_mem {P : MvPolynomial (Fin (nParams A)) A}
    (h : ∀ s, P.coeff s ∈ IsLocalRing.maximalIdeal A) : P.map (IsLocalRing.residue A) = 0 := by
  classical
  ext s
  rw [MvPolynomial.coeff_map (IsLocalRing.residue A) P s]
  simp only [MvPolynomial.coeff_zero]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr (h s)

theorem inForm_eq_zero_iff (a : A) : inForm A a = 0 ↔ a = 0 := by
  classical
  constructor
  · intro h
    by_contra ha
    have hmap : (leadPoly A a).map (IsLocalRing.residue A) = 0 := by
      simpa only [inForm] using h
    have hcoeff : ∀ s, (leadPoly A a).coeff s ∈ IsLocalRing.maximalIdeal A :=
      fun s => coeff_mem_of_map_residue_eq_zero A hmap s
    have hmem : MvPolynomial.eval (params A) (leadPoly A a)
        ∈ IsLocalRing.maximalIdeal A ^ (ordNat A a + 1) :=
      eval_mem_pow_succ_of_coeff_mem (IsLocalRing.maximalIdeal A) (params A)
        (fun i => by rw [← params_span A]; exact Submodule.subset_span ⟨i, rfl⟩)
        (leadPoly_isHomogeneous A ha) hcoeff
    rw [eval_leadPoly A ha] at hmem
    exact absurd hmem (ordNat_spec A ha).2
  · rintro rfl
    simp

theorem inForm_ne_zero_iff (a : A) : inForm A a ≠ 0 ↔ a ≠ 0 :=
  (inForm_eq_zero_iff A a).not

theorem inForm_isHomogeneous {a : A} (ha : a ≠ 0) :
    (inForm A a).IsHomogeneous (ordNat A a) := by
  rw [inForm]
  exact (leadPoly_isHomogeneous A ha).map (IsLocalRing.residue A)

/-- Two homogeneous polynomials of the same degree with the same value at the parameters have the
same reduction modulo `𝔪`. -/
theorem map_residue_eq_of_eval_eq {n : ℕ} {P Q : MvPolynomial (Fin (nParams A)) A}
    (hP : P.IsHomogeneous n) (hQ : Q.IsHomogeneous n)
    (h : MvPolynomial.eval (params A) P = MvPolynomial.eval (params A) Q) :
    P.map (IsLocalRing.residue A) = Q.map (IsLocalRing.residue A) := by
  classical
  have hcoeff : ∀ s, (P - Q).coeff s ∈ IsLocalRing.maximalIdeal A :=
    coeff_mem_of_eval_params A (hP.sub hQ) (by rw [map_sub, h, sub_self]; exact Submodule.zero_mem _)
  rw [← sub_eq_zero, ← map_sub]
  exact map_residue_eq_zero_of_coeff_mem A hcoeff

theorem ordNat_one : ordNat A (1 : A) = 0 := by
  by_contra h
  have h1 : 1 ≤ ordNat A (1 : A) := Nat.one_le_iff_ne_zero.mpr h
  have hmem : (1 : A) ∈ IsLocalRing.maximalIdeal A ^ (1 : ℕ) :=
    Ideal.pow_le_pow_right h1 (mem_pow_ordNat A (1 : A))
  have hmem' : (1 : A) ∈ IsLocalRing.maximalIdeal A := by simpa using hmem
  exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one hmem'

theorem inForm_one : inForm A (1 : A) = 1 := by
  have h1 : (1 : A) ≠ 0 := one_ne_zero
  have hpf : (leadPoly A (1 : A)).IsHomogeneous 0 := by
    rw [← ordNat_one A]
    exact leadPoly_isHomogeneous A h1
  have hconst : leadPoly A (1 : A) = MvPolynomial.C ((leadPoly A (1 : A)).coeff 0) := by
    have h := MvPolynomial.homogeneousComponent_eq_self (R := A) hpf
    rw [MvPolynomial.homogeneousComponent_zero] at h
    exact h.symm
  have hcoeff : (leadPoly A (1 : A)).coeff 0 = 1 := by
    have h := eval_leadPoly A h1
    rw [hconst, MvPolynomial.eval_C] at h
    exact h
  rw [inForm, hconst, hcoeff]
  simp

theorem ordNat_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordNat A (a * b) = ordNat A a + ordNat A b := by
  classical
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hge : ordNat A a + ordNat A b ≤ ordNat A (a * b) := by
    refine le_ordNat_of_mem A hab ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul (ordNat_spec A ha).1 (ordNat_spec A hb).1
  refine le_antisymm ?_ hge
  by_contra hcon
  push Not at hcon
  have hnmem : a * b ∉ IsLocalRing.maximalIdeal A ^ (ordNat A a + ordNat A b + 1) := by
    intro hmem
    have hR : (leadPoly A a * leadPoly A b).IsHomogeneous (ordNat A a + ordNat A b) :=
      (leadPoly_isHomogeneous A ha).mul (leadPoly_isHomogeneous A hb)
    have heval : MvPolynomial.eval (params A) (leadPoly A a * leadPoly A b) = a * b := by
      rw [map_mul, eval_leadPoly A ha, eval_leadPoly A hb]
    have hcoeff := coeff_mem_of_eval_params A hR (by rw [heval]; exact hmem)
    have hzero : (leadPoly A a).map (IsLocalRing.residue A)
        * (leadPoly A b).map (IsLocalRing.residue A) = 0 := by
      rw [← map_mul]
      exact map_residue_eq_zero_of_coeff_mem A hcoeff
    have hia : (leadPoly A a).map (IsLocalRing.residue A) ≠ 0 :=
      fun h0 => ha ((inForm_eq_zero_iff A a).mp (by simpa only [inForm] using h0))
    have hib : (leadPoly A b).map (IsLocalRing.residue A) ≠ 0 :=
      fun h0 => hb ((inForm_eq_zero_iff A b).mp (by simpa only [inForm] using h0))
    exact mul_ne_zero hia hib hzero
  exact hnmem (Ideal.pow_le_pow_right (by omega) (mem_pow_ordNat A (a * b)))

theorem inForm_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    inForm A (a * b) = inForm A a * inForm A b := by
  classical
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hP : (leadPoly A (a * b)).IsHomogeneous (ordNat A a + ordNat A b) := by
    rw [← ordNat_mul A ha hb]
    exact leadPoly_isHomogeneous A hab
  have hQ : (leadPoly A a * leadPoly A b).IsHomogeneous (ordNat A a + ordNat A b) :=
    (leadPoly_isHomogeneous A ha).mul (leadPoly_isHomogeneous A hb)
  have key := map_residue_eq_of_eval_eq A hP hQ (by
    rw [map_mul, eval_leadPoly A ha, eval_leadPoly A hb, eval_leadPoly A hab])
  calc inForm A (a * b) = (leadPoly A (a * b)).map (IsLocalRing.residue A) := rfl
    _ = (leadPoly A a * leadPoly A b).map (IsLocalRing.residue A) := key
    _ = inForm A a * inForm A b := by rw [map_mul]; rfl

theorem ord_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ord A (a * b) = ord A a + ord A b := by
  rw [ord_eq_coe_ordNat A (mul_ne_zero ha hb), ord_eq_coe_ordNat A ha, ord_eq_coe_ordNat A hb,
    ordNat_mul A ha hb]
  simp

theorem inForm_pow (a : A) (ha : a ≠ 0) (n : ℕ) :
    inForm A (a ^ n) = (inForm A a) ^ n := by
  induction n with
  | zero => simpa using inForm_one A
  | succ n ih =>
      rw [pow_succ, inForm_mul A (pow_ne_zero n ha) ha, ih, pow_succ]

/-- The initial form of the lift of a homogeneous polynomial over the residue field is that
polynomial. -/
theorem inForm_eval_secPoly {F : MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A)}
    {n : ℕ} (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) :
    inForm A (MvPolynomial.eval (params A) (secPoly A F)) = F := by
  classical
  set P := secPoly A F with hPdef
  have hPhom : P.IsHomogeneous n := secPoly_isHomogeneous A hF
  have hx : ∀ i, params A i ∈ IsLocalRing.maximalIdeal A :=
    fun i => by rw [← params_span A]; exact Submodule.subset_span ⟨i, rfl⟩
  have hmem : MvPolynomial.eval (params A) P ∈ IsLocalRing.maximalIdeal A ^ n :=
    eval_mem_pow_of_isHomogeneous (IsLocalRing.maximalIdeal A) (params A) hx hPhom
  have hnmem : MvPolynomial.eval (params A) P ∉ IsLocalRing.maximalIdeal A ^ (n + 1) := by
    intro hcon
    have hcoeff := coeff_mem_of_eval_params A hPhom hcon
    have hzero : P.map (IsLocalRing.residue A) = 0 := map_residue_eq_zero_of_coeff_mem A hcoeff
    rw [hPdef, secPoly_map A F] at hzero
    exact hF0 hzero
  have hne : MvPolynomial.eval (params A) P ≠ 0 := fun h0 => hnmem (h0 ▸ Submodule.zero_mem _)
  have hord : ordNat A (MvPolynomial.eval (params A) P) = n := by
    refine le_antisymm ?_ (le_ordNat_of_mem A hne hmem)
    by_contra hcon
    push Not at hcon
    exact hnmem (Ideal.pow_le_pow_right (by omega)
      (mem_pow_ordNat A (MvPolynomial.eval (params A) P)))
  have key := map_residue_eq_of_eval_eq A (P := leadPoly A (MvPolynomial.eval (params A) P))
    (Q := P) (by rw [← hord]; exact leadPoly_isHomogeneous A hne) hPhom
    (by rw [eval_leadPoly A hne])
  calc inForm A (MvPolynomial.eval (params A) P)
      = (leadPoly A (MvPolynomial.eval (params A) P)).map (IsLocalRing.residue A) := rfl
    _ = P.map (IsLocalRing.residue A) := key
    _ = F := by rw [hPdef, secPoly_map A F]

/-- If two elements have the same initial form, their difference has larger order. -/
theorem ordNat_lt_of_inForm_eq {u v : A} (huv : u ≠ v) (h : inForm A u = inForm A v) :
    ordNat A u < ordNat A (u - v) := by
  classical
  have hu : u ≠ 0 := fun h0 => huv (by
    have hv0 : inForm A v = 0 := by rw [← h, h0]; simp
    rw [(inForm_eq_zero_iff A v).mp hv0, h0])
  have hv : v ≠ 0 := fun h0 => huv (by
    have hu0 : inForm A u = 0 := by rw [h, h0]; simp
    rw [h0, (inForm_eq_zero_iff A u).mp hu0])
  have hvu : inForm A v ≠ 0 := (inForm_ne_zero_iff A v).mpr hv
  have hdeg : ordNat A v = ordNat A u :=
    (inForm_isHomogeneous A hv).inj_right (by rw [← h]; exact inForm_isHomogeneous A hu) hvu
  have hP : (leadPoly A u - leadPoly A v).IsHomogeneous (ordNat A u) :=
    (leadPoly_isHomogeneous A hu).sub (by rw [← hdeg]; exact leadPoly_isHomogeneous A hv)
  have hmap : (leadPoly A u - leadPoly A v).map (IsLocalRing.residue A) = 0 := by
    rw [map_sub, show (leadPoly A u).map (IsLocalRing.residue A) = inForm A u from rfl,
      show (leadPoly A v).map (IsLocalRing.residue A) = inForm A v from rfl, h, sub_self]
  have hcoeff := coeff_mem_of_map_residue_eq_zero A hmap
  have hmem : u - v ∈ IsLocalRing.maximalIdeal A ^ (ordNat A u + 1) := by
    have hmem' := eval_mem_pow_succ_of_coeff_mem (IsLocalRing.maximalIdeal A) (params A)
      (fun i => by rw [← params_span A]; exact Submodule.subset_span ⟨i, rfl⟩) hP hcoeff
    rwa [map_sub, eval_leadPoly A hu, eval_leadPoly A hv] at hmem'
  have hsub : u - v ≠ 0 := sub_ne_zero.mpr huv
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_ordNat_of_mem A hsub hmem)

/-- If `inForm b` divides `inForm a` (with `a`, `b ≠ 0`), there is `q` with either `a = q * b`, or
`a - q * b ≠ 0` with strictly larger order than `a`. -/
theorem exists_ordNat_lt_of_dvd {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : inForm A b ∣ inForm A a) :
    ∃ q : A, a = q * b ∨ ordNat A a < ordNat A (a - q * b) := by
  classical
  obtain ⟨R, hR, hRdiv⟩ := exists_isHomogeneous_of_dvd (inForm_isHomogeneous A hb)
    (inForm_ne_zero_iff A b |>.mpr hb) (inForm_isHomogeneous A ha) h
  have hR0 : R ≠ 0 := fun h0 => ha ((inForm_eq_zero_iff A a).mp (by rw [hRdiv, h0, mul_zero]))
  have hq : inForm A (MvPolynomial.eval (params A) (secPoly A R)) = R :=
    inForm_eval_secPoly A hR hR0
  have hq0 : MvPolynomial.eval (params A) (secPoly A R) ≠ 0 :=
    fun h0 => hR0 (by rw [← hq, h0]; simp)
  have hqb : inForm A (MvPolynomial.eval (params A) (secPoly A R) * b) = inForm A a := by
    rw [inForm_mul A hq0 hb, hq, mul_comm, hRdiv]
  refine ⟨MvPolynomial.eval (params A) (secPoly A R), ?_⟩
  by_cases hcase : a = MvPolynomial.eval (params A) (secPoly A R) * b
  · exact Or.inl hcase
  · exact Or.inr (ordNat_lt_of_inForm_eq A hcase hqb.symm)

end Work.DSNORM

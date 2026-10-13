import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.of_f
import Submission.Work.DSM1p.Family.stepMap_algebraMap
import Submission.Work.DSM1p.Family.stepMap_root

/-!
# `R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]` is a flat `R`-module

The multi-parameter root closure `FamClosure R p x` is the filtered colimit of the stages

`FamTower R p x n = R[X₁,…,X_d] ⧸ (X_i ^ (p^n) - x_i)`.

Each stage is a *free* `R`-module: the relations `X_i ^ N - C (x_i)` are monic in `X_i`, so the
classes of the monomials whose exponent is `< N` in every variable form an `R`-basis
(`mvPolyQuotFree` below, with the "normal form" map `red`).  Hence each stage is flat
(`flat_stage`), and a filtered colimit of flat modules is flat — the last step is the equational
criterion of flatness (`Module.Flat.of_forall_isTrivialRelation`), exactly as in the
one-parameter case `Work.DSM1p.Root.flat_closure`.

## Main result

* `flat_closure` : `Module.Flat R (FamClosure R p x)` for `p ≠ 0`.
-/

namespace Work.DSM1p.Family

universe u

set_option maxHeartbeats 1000000

variable {R : Type u} [CommRing R] {d : ℕ}

/-! ## Part 1: the quotient `R[X₁,…,X_d] ⧸ (X_i ^ N - c_i)` is a free `R`-module -/

/-- Multi-indices which are reduced: `< N` in every coordinate. -/
abbrev RedIdx (d N : ℕ) : Type := {m : Fin d →₀ ℕ // ∀ i, m i < N}

noncomputable instance instFintypeRedIdx (d N : ℕ) : Fintype (RedIdx d N) :=
  Fintype.ofInjective (fun m : RedIdx d N => fun i : Fin d => (⟨m.1 i, m.2 i⟩ : Fin N))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun i => by
      simpa using congrArg Fin.val (congrFun h i)))

/-- Componentwise `m % N`. -/
noncomputable def idxMod (N : ℕ) (m : Fin d →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.mapRange (fun k => k % N) (Nat.zero_mod N) m

@[simp] lemma idxMod_apply (N : ℕ) (m : Fin d →₀ ℕ) (i : Fin d) : idxMod N m i = m i % N := by
  simp [idxMod]

lemma idxMod_lt {N : ℕ} (hN : N ≠ 0) (m : Fin d →₀ ℕ) (i : Fin d) : idxMod N m i < N := by
  rw [idxMod_apply]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero hN)

lemma idxMod_eq_self {N : ℕ} {m : Fin d →₀ ℕ} (hm : ∀ i, m i < N) : idxMod N m = m := by
  ext i; rw [idxMod_apply, Nat.mod_eq_of_lt (hm i)]

/-- The scalar `∏ i, x i ^ (m i / N)` which multiplies the reduced monomial. -/
noncomputable def scCoeff (N : ℕ) (x : Fin d → R) (m : Fin d →₀ ℕ) : R :=
  ∏ i, x i ^ (m i / N)

lemma scCoeff_of_lt {N : ℕ} {x : Fin d → R} {m : Fin d →₀ ℕ} (hm : ∀ i, m i < N) :
    scCoeff N x m = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Nat.div_eq_of_lt (hm i), pow_zero]

lemma prod_C_x_pow (N : ℕ) (x : Fin d → R) (m : Fin d →₀ ℕ) :
    (∏ j : Fin d, (MvPolynomial.C (x j) : MvPolynomial (Fin d) R) ^ (m j / N))
      = MvPolynomial.C (scCoeff N x m) := by
  rw [scCoeff, map_prod]
  exact Finset.prod_congr rfl fun j _ => (map_pow MvPolynomial.C (x j) (m j / N)).symm

/-- The monomial `X ^ m` rewritten as a product of pure powers of the variables. -/
lemma monomial_eq_prod (m : Fin d →₀ ℕ) (c : R) :
    (MvPolynomial.monomial m c : MvPolynomial (Fin d) R)
      = MvPolynomial.C c * ∏ j : Fin d, MvPolynomial.X j ^ (m j) := by
  rw [MvPolynomial.monomial_eq,
    Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)]

/-- The canonical `R`-linear map from the reduced monomials. -/
noncomputable def phi (N : ℕ) : (RedIdx d N →₀ R) →ₗ[R] MvPolynomial (Fin d) R :=
  Finsupp.linearCombination R fun t : RedIdx d N => MvPolynomial.monomial t.1 (1 : R)

@[simp] lemma phi_single (N : ℕ) (t : RedIdx d N) (c : R) :
    phi N (Finsupp.single t c) = MvPolynomial.monomial t.1 c := by
  rw [phi, Finsupp.linearCombination_single, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

lemma coeff_phi (N : ℕ) (l : RedIdx d N →₀ R) (t : RedIdx d N) :
    (phi N l).coeff t.1 = l t := by
  have hphi : phi N l = ∑ s ∈ l.support, MvPolynomial.monomial s.1 (l s) := by
    rw [show phi N l = ∑ s ∈ l.support,
        l s • (MvPolynomial.monomial s.1 (1 : R) : MvPolynomial (Fin d) R) from rfl]
    exact Finset.sum_congr rfl fun s _ => by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hphi, MvPolynomial.coeff_sum]
  let f : RedIdx d N → R := fun s => (MvPolynomial.monomial s.1 (l s)).coeff t.1
  change (∑ s ∈ l.support, f s) = l t
  have hsum : (∑ s ∈ l.support, f s) = f t :=
    Finset.sum_eq_single (s := l.support) (f := f) t
      (fun b _ hbt => by
        show (MvPolynomial.monomial b.1 (l b)).coeff t.1 = 0
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro hb
        exact hbt (Subtype.ext hb))
      (fun ht => by
        show (MvPolynomial.monomial t.1 (l t)).coeff t.1 = 0
        rw [MvPolynomial.coeff_monomial, if_pos rfl]
        by_contra hc
        exact ht (Finsupp.mem_support_iff.mpr hc))
  rw [hsum]
  show (MvPolynomial.monomial t.1 (l t)).coeff t.1 = l t
  rw [MvPolynomial.coeff_monomial, if_pos rfl]

lemma phi_injective (N : ℕ) : Function.Injective (phi (R := R) (d := d) N) := by
  intro l l' h
  ext t
  rw [← coeff_phi N l t, h, coeff_phi N l' t]

/-- The "reduction of the exponent" linear map `m ↦ c • X ^ (m % N)` with coefficient
`∏ i, x i ^ (m i / N)`. -/
noncomputable def redShift (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) :
    ((Fin d →₀ ℕ) →₀ R) →ₗ[R] (RedIdx d N →₀ R) :=
  Finsupp.linearCombination R fun m : Fin d →₀ ℕ =>
    Finsupp.single (⟨idxMod N m, fun i => idxMod_lt hN m i⟩ : RedIdx d N) (scCoeff N x m)

/-- The `R`-linear normal-form map: `X ^ m ↦ x ^ (m / N) * X ^ (m % N)`, componentwise. -/
noncomputable def red (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) :
    MvPolynomial (Fin d) R →ₗ[R] MvPolynomial (Fin d) R :=
  (phi N).comp ((redShift N x hN).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)

/-- The coefficient linear equivalence at a monomial. -/
lemma coeff_linearEquiv_monomial (m : Fin d →₀ ℕ) (c : R) :
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap (MvPolynomial.monomial m c)
      = Finsupp.single m c := by
  change (AddMonoidAlgebra.coeffLinearEquiv R) (MvPolynomial.monomial m c) = Finsupp.single m c
  rw [AddMonoidAlgebra.coeffLinearEquiv_apply]
  ext n
  rw [MvPolynomial.coeff_monomial, Finsupp.single_apply]

/-- The reduction map on a single monomial (at the level of the `m ↦ m % N` reindexing). -/
lemma redShift_single (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (m : Fin d →₀ ℕ) (c : R) :
    redShift N x hN (Finsupp.single m c)
      = Finsupp.single (⟨idxMod N m, fun i => idxMod_lt hN m i⟩ : RedIdx d N)
          (c * scCoeff N x m) := by
  rw [redShift, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]

lemma red_monomial (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (m : Fin d →₀ ℕ) (c : R) :
    red N x hN (MvPolynomial.monomial m c)
      = MvPolynomial.monomial (idxMod N m) (c * scCoeff N x m) := by
  rw [red, LinearMap.comp_apply, LinearMap.comp_apply, coeff_linearEquiv_monomial,
    redShift_single, phi_single]

lemma red_monomial_of_lt (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) {m : Fin d →₀ ℕ}
    (hm : ∀ i, m i < N) {c : R} :
    red N x hN (MvPolynomial.monomial m c) = MvPolynomial.monomial m c := by
  rw [red_monomial, idxMod_eq_self hm, scCoeff_of_lt hm, mul_one]

@[simp] lemma red_one (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) :
    red N x hN (1 : MvPolynomial (Fin d) R) = 1 := by
  have h : (1 : MvPolynomial (Fin d) R) = MvPolynomial.monomial 0 (1 : R) := by
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
  rw [h, red_monomial_of_lt N x hN (fun _ => Nat.pos_of_ne_zero hN), ← h]

lemma add_single_div (N : ℕ) (hN : N ≠ 0) (m : Fin d →₀ ℕ) (i j : Fin d) :
    ((m + Finsupp.single i N) j) / N = m j / N + (if j = i then 1 else 0) := by
  by_cases h : j = i
  · subst h
    rw [Finsupp.add_apply, Finsupp.single_eq_same, if_pos rfl]
    exact Nat.add_div_right _ (Nat.pos_of_ne_zero hN)
  · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, if_neg h, add_zero, add_zero]

lemma add_single_mod (N : ℕ) (m : Fin d →₀ ℕ) (i j : Fin d) :
    ((m + Finsupp.single i N) j) % N = m j % N := by
  by_cases h : j = i
  · subst h; rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_mod_right]
  · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero]

lemma idxMod_add_single (N : ℕ) (m : Fin d →₀ ℕ) (i : Fin d) :
    idxMod N (m + Finsupp.single i N) = idxMod N m := by
  ext j
  rw [idxMod_apply, idxMod_apply, add_single_mod]

lemma scCoeff_add_single (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (m : Fin d →₀ ℕ) (i : Fin d) :
    scCoeff N x (m + Finsupp.single i N) = scCoeff N x m * x i := by
  rw [scCoeff, scCoeff,
    show (∏ j : Fin d, x j ^ ((m + Finsupp.single i N) j / N))
        = ∏ j : Fin d, x j ^ (m j / N) * x j ^ (if j = i then 1 else 0) from
      Finset.prod_congr rfl fun j _ => by rw [add_single_div N hN m i j, pow_add],
    Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji; rw [if_neg hji, pow_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma red_monomial_X_pow_mul (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (m : Fin d →₀ ℕ) (c : R)
    (i : Fin d) :
    red N x hN (MvPolynomial.X i ^ N * MvPolynomial.monomial m c)
      = MvPolynomial.C (x i) * red N x hN (MvPolynomial.monomial m c) := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul,
    show (Finsupp.single i N + m) = (m + Finsupp.single i N) from add_comm _ _,
    red_monomial, red_monomial, idxMod_add_single, scCoeff_add_single N x hN m i,
    MvPolynomial.C_mul_monomial]
  congr 1
  ring

lemma red_mul_X_pow (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (i : Fin d)
    (p : MvPolynomial (Fin d) R) :
    red N x hN (MvPolynomial.X i ^ N * p)
      = MvPolynomial.C (x i) * red N x hN p := by
  have hp : p = ∑ v ∈ p.support, MvPolynomial.monomial v (p.coeff v) := MvPolynomial.as_sum p
  have hred : red N x hN p
      = ∑ v ∈ p.support, red N x hN (MvPolynomial.monomial v (p.coeff v)) := by
    conv_lhs => rw [hp]
    rw [map_sum]
  calc red N x hN (MvPolynomial.X i ^ N * p)
      = red N x hN (∑ v ∈ p.support, MvPolynomial.X i ^ N *
          MvPolynomial.monomial v (p.coeff v)) := by
        conv_lhs => rw [hp, Finset.mul_sum]
    _ = ∑ v ∈ p.support, red N x hN (MvPolynomial.X i ^ N *
          MvPolynomial.monomial v (p.coeff v)) := by
        rw [map_sum]
    _ = ∑ v ∈ p.support, MvPolynomial.C (x i) *
          red N x hN (MvPolynomial.monomial v (p.coeff v)) :=
        Finset.sum_congr rfl fun v _ => red_monomial_X_pow_mul N x hN v (p.coeff v) i
    _ = MvPolynomial.C (x i) *
          ∑ v ∈ p.support, red N x hN (MvPolynomial.monomial v (p.coeff v)) := by
        rw [Finset.mul_sum]
    _ = MvPolynomial.C (x i) * red N x hN p := by rw [hred]

lemma red_C_mul (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (a : R)
    (p : MvPolynomial (Fin d) R) :
    red N x hN (MvPolynomial.C a * p) = MvPolynomial.C a * red N x hN p := by
  rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul, map_smul]

/-- The defining ideal of the stage `R[X₁,…,X_d] ⧸ (X_i ^ N - c_i)`. -/
noncomputable abbrev stageIdeal (N : ℕ) (x : Fin d → R) : Ideal (MvPolynomial (Fin d) R) :=
  Ideal.span (Set.range fun i : Fin d => MvPolynomial.X i ^ N - MvPolynomial.C (x i))

/-- The quotient map of the stage. -/
noncomputable abbrev stageMk (N : ℕ) (x : Fin d → R) :
    MvPolynomial (Fin d) R →+* (MvPolynomial (Fin d) R ⧸ stageIdeal N x) :=
  Ideal.Quotient.mk (stageIdeal N x)

/-- `red` kills the defining ideal (it is the normal form for the relations `X_i ^ N = x_i`). -/
lemma red_mem_stageIdeal (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) {p : MvPolynomial (Fin d) R}
    (hp : p ∈ stageIdeal N x) : red N x hN p = 0 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  rw [← hc, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show c i * (MvPolynomial.X i ^ N - MvPolynomial.C (x i))
      = MvPolynomial.X i ^ N * c i - MvPolynomial.C (x i) * c i from by ring,
    map_sub, red_mul_X_pow, red_C_mul, sub_self]

/-- Reduction of a power of a variable through the relation `X_i ^ N = x_i`. -/
lemma mk_X_pow (N : ℕ) (x : Fin d → R) (i : Fin d) (k : ℕ) :
    stageMk N x (MvPolynomial.X i ^ k)
      = (stageMk N x (MvPolynomial.C (x i))) ^ (k / N)
        * (stageMk N x (MvPolynomial.X i)) ^ (k % N) := by
  have hrel : stageMk N x (MvPolynomial.X i ^ N) = stageMk N x (MvPolynomial.C (x i)) := by
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))
  conv_lhs => rw [← Nat.div_add_mod k N]
  rw [pow_add, pow_mul, map_mul]
  simp only [map_pow, hrel]

lemma prod_mk_C_x_pow (N : ℕ) (x : Fin d → R) (m : Fin d →₀ ℕ) :
    (∏ j : Fin d, stageMk N x (MvPolynomial.C (x j)) ^ (m j / N))
      = stageMk N x (MvPolynomial.C (scCoeff N x m)) := by
  rw [← prod_C_x_pow N x m]
  have h1 : (∏ j : Fin d, stageMk N x (MvPolynomial.C (x j)) ^ (m j / N))
      = ∏ j : Fin d,
          stageMk N x ((MvPolynomial.C (x j) : MvPolynomial (Fin d) R) ^ (m j / N)) :=
    Finset.prod_congr rfl fun j _ => (map_pow (stageMk N x) _ _).symm
  rw [h1, ← map_prod]

lemma prod_mk_X_pow (N : ℕ) (x : Fin d → R) (m : Fin d →₀ ℕ) :
    (∏ j : Fin d, stageMk N x (MvPolynomial.X j) ^ (m j % N))
      = stageMk N x (∏ j : Fin d, MvPolynomial.X j ^ (idxMod N m j)) := by
  rw [show (∏ j : Fin d, MvPolynomial.X j ^ (idxMod N m j))
      = ∏ j : Fin d, MvPolynomial.X j ^ (m j % N) from
    Finset.prod_congr rfl fun j _ => by rw [idxMod_apply]]
  have h1 : (∏ j : Fin d, stageMk N x (MvPolynomial.X j) ^ (m j % N))
      = ∏ j : Fin d, stageMk N x (MvPolynomial.X j ^ (m j % N)) :=
    Finset.prod_congr rfl fun j _ => (map_pow (stageMk N x) _ _).symm
  rw [h1, ← map_prod]

/-- The normal form computes the class of a monomial in the quotient. -/
lemma mk_monomial (N : ℕ) (x : Fin d → R) (m : Fin d →₀ ℕ) (c : R) :
    stageMk N x (MvPolynomial.monomial m c)
      = stageMk N x (MvPolynomial.monomial (idxMod N m) (c * scCoeff N x m)) := by
  have hL : stageMk N x (MvPolynomial.monomial m c)
      = stageMk N x (MvPolynomial.C c) *
        ∏ j : Fin d, stageMk N x (MvPolynomial.X j ^ (m j)) := by
    rw [monomial_eq_prod, map_mul, map_prod]
  have hR : stageMk N x (MvPolynomial.monomial (idxMod N m) (c * scCoeff N x m))
      = stageMk N x (MvPolynomial.C (c * scCoeff N x m)) *
        stageMk N x (∏ j : Fin d, MvPolynomial.X j ^ (idxMod N m j)) := by
    rw [monomial_eq_prod, map_mul]
  have hstep : (∏ j : Fin d, stageMk N x (MvPolynomial.X j ^ (m j)))
      = ∏ j : Fin d, (stageMk N x (MvPolynomial.C (x j)) ^ (m j / N) *
          stageMk N x (MvPolynomial.X j) ^ (m j % N)) :=
    Finset.prod_congr rfl fun j _ => mk_X_pow N x j (m j)
  have hprod : (∏ j : Fin d, stageMk N x (MvPolynomial.X j ^ (m j)))
      = stageMk N x (MvPolynomial.C (scCoeff N x m)) *
        stageMk N x (∏ j : Fin d, MvPolynomial.X j ^ (idxMod N m j)) := by
    rw [hstep, Finset.prod_mul_distrib, prod_mk_C_x_pow, prod_mk_X_pow]
  rw [hL, hR, hprod, ← mul_assoc, ← map_mul, ← MvPolynomial.C_mul]

/-- Every element of the quotient is the class of its normal form: `red` is a normal form for
the ideal generated by the `X_i ^ N - x_i`. -/
lemma mk_red (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (p : MvPolynomial (Fin d) R) :
    stageMk N x p = stageMk N x (red N x hN p) := by
  have hred : red N x hN p
      = ∑ v ∈ p.support, red N x hN (MvPolynomial.monomial v (p.coeff v)) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum, hred, map_sum]
  exact Finset.sum_congr rfl fun v _ => by
    rw [red_monomial]
    exact mk_monomial N x v (p.coeff v)

/-- `red` is the identity on the span of the reduced monomials. -/
lemma red_phi (N : ℕ) (x : Fin d → R) (hN : N ≠ 0) (l : RedIdx d N →₀ R) :
    red N x hN (phi N l) = phi N l := by
  have hphi : phi N l = ∑ t ∈ l.support, MvPolynomial.monomial t.1 (l t) := by
    rw [show phi N l = ∑ t ∈ l.support,
        l t • (MvPolynomial.monomial t.1 (1 : R) : MvPolynomial (Fin d) R) from rfl]
    exact Finset.sum_congr rfl fun t _ => by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [hphi]
  conv_rhs => rw [hphi]
  rw [map_sum]
  exact Finset.sum_congr rfl fun t _ => red_monomial_of_lt N x hN t.2

/-- The canonical map from the reduced monomials into the quotient. -/
noncomputable def stageMap (N : ℕ) (x : Fin d → R) :
    (RedIdx d N →₀ R) →ₗ[R] (MvPolynomial (Fin d) R ⧸ stageIdeal N x) :=
  (Ideal.Quotient.mkₐ R (stageIdeal N x)).toLinearMap.comp (phi N)

lemma stageMap_apply (N : ℕ) (x : Fin d → R) (l : RedIdx d N →₀ R) :
    stageMap N x l = stageMk N x (phi N l) := rfl

/-- **The quotient `R[X₁,…,X_d] ⧸ (X_i ^ N - c_i)` is a free `R`-module** (for `N ≠ 0`): the
classes of the monomials whose exponents are `< N` in every variable form a basis. -/
theorem mvPolyQuotFree (R : Type u) [CommRing R] (d N : ℕ) (hN : N ≠ 0) (x : Fin d → R) :
    Module.Free R (MvPolynomial (Fin d) R ⧸
      Ideal.span (Set.range fun i => MvPolynomial.X i ^ N - MvPolynomial.C (x i))) := by
  classical
  have hker : ∀ l : RedIdx d N →₀ R, stageMap N x l = 0 → l = 0 := by
    intro l hl
    have h1 : phi N l ∈ stageIdeal N x :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [stageMap_apply] using hl)
    have h2 : red N x hN (phi N l) = 0 := red_mem_stageIdeal N x hN h1
    have h3 : phi N l = 0 := by rw [← red_phi N x hN l, h2]
    exact phi_injective N (by rw [h3, map_zero])
  have hsurj : Function.Surjective (stageMap N x) := by
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨redShift N x hN ((AddMonoidAlgebra.coeffLinearEquiv R) p), ?_⟩
    show stageMk N x (red N x hN p) = stageMk N x p
    exact (mk_red N x hN p).symm
  have hinj : Function.Injective (stageMap N x) := by
    intro l l' hll
    have h : l - l' = 0 := by
      refine hker (l - l') ?_
      rw [map_sub, hll, sub_self]
    rwa [sub_eq_zero] at h
  exact Module.Free.of_equiv (LinearEquiv.ofBijective (stageMap N x) ⟨hinj, hsurj⟩)

/-- Every stage of the multi-parameter root tower is a flat `R`-module. -/
theorem flat_stage (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (hp : p ≠ 0)
    (n : ℕ) : Module.Flat R (Work.DSM1p.FamTower R p x n) := by
  haveI := mvPolyQuotFree R d (p ^ n) (pow_ne_zero n hp) x
  exact Module.Flat.of_free

/-! ## Part 2: the transition maps and the colimit -/

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)

/-- Two ring homomorphisms out of a stage of the family tower agree as soon as they agree on the
images of `R` and of the adjoined roots. -/
lemma famTower_ringHom_ext {S : Type*} [CommRing S] (n : ℕ)
    {f g : Work.DSM1p.FamTower R p x n →+* S}
    (hC : ∀ r : R, f (algebraMap R (Work.DSM1p.FamTower R p x n) r)
      = g (algebraMap R (Work.DSM1p.FamTower R p x n) r))
    (hX : ∀ k : Fin d, f (Work.DSM1p.FamTower.root R p x n k)
      = g (Work.DSM1p.FamTower.root R p x n k)) : f = g := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_))
  · exact hC r
  · exact hX k

/-- The transition maps of the family tower form a directed system. -/
instance stepMap_directedSystem :
    DirectedSystem (Work.DSM1p.FamTower R p x)
      (fun i j h => ⇑(Work.DSM1p.FamTower.stepMap R p x i j h)) where
  map_self := fun {i} y => by
    have h : Work.DSM1p.FamTower.stepMap R p x i i le_rfl = RingHom.id _ := by
      refine famTower_ringHom_ext R p x i (fun r => ?_) (fun k => ?_)
      · show Work.DSM1p.FamTower.stepMap R p x i i le_rfl
            (algebraMap R (Work.DSM1p.FamTower R p x i) r)
          = algebraMap R (Work.DSM1p.FamTower R p x i) r
        rw [stepMap_algebraMap]
      · show Work.DSM1p.FamTower.stepMap R p x i i le_rfl (Work.DSM1p.FamTower.root R p x i k)
          = Work.DSM1p.FamTower.root R p x i k
        rw [stepMap_root, show i - i = 0 from Nat.sub_self i, pow_zero, pow_one]
    rw [h]
    rfl
  map_map := fun {k j i} hij hjk y => by
    have h : (Work.DSM1p.FamTower.stepMap R p x j k hjk).comp
          (Work.DSM1p.FamTower.stepMap R p x i j hij)
        = Work.DSM1p.FamTower.stepMap R p x i k (hij.trans hjk) := by
      refine famTower_ringHom_ext R p x i (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.comp_apply, stepMap_algebraMap]
      · show Work.DSM1p.FamTower.stepMap R p x j k hjk
            (Work.DSM1p.FamTower.stepMap R p x i j hij (Work.DSM1p.FamTower.root R p x i n))
          = Work.DSM1p.FamTower.stepMap R p x i k (hij.trans hjk)
              (Work.DSM1p.FamTower.root R p x i n)
        rw [stepMap_root, map_pow, stepMap_root, stepMap_root, ← pow_mul, ← pow_add,
          show (k - j) + (j - i) = (k - i) from by omega]
    show ((Work.DSM1p.FamTower.stepMap R p x j k hjk).comp
        (Work.DSM1p.FamTower.stepMap R p x i j hij)) y
      = (Work.DSM1p.FamTower.stepMap R p x i k (hij.trans hjk)) y
    rw [h]

/-- The canonical maps from the stages of the tower into the closure are `R`-algebra maps. -/
theorem of_algebraMap (n : ℕ) (r : R) :
    Work.DSM1p.FamClosure.of R p x n (algebraMap R (Work.DSM1p.FamTower R p x n) r)
      = algebraMap R (Work.DSM1p.FamClosure R p x) r := by
  show Work.DSM1p.FamClosure.of R p x n (algebraMap R (Work.DSM1p.FamTower R p x n) r)
      = Work.DSM1p.FamClosure.of R p x 0 (algebraMap R (Work.DSM1p.FamTower R p x 0) r)
  rw [← stepMap_algebraMap R p x 0 n (Nat.zero_le n) r]
  exact Ring.DirectLimit.of_f (Nat.zero_le n) (algebraMap R (Work.DSM1p.FamTower R p x 0) r)

/-- The canonical maps from the stages into the closure are `R`-linear. -/
theorem of_smul (n : ℕ) (r : R) (y : Work.DSM1p.FamTower R p x n) :
    Work.DSM1p.FamClosure.of R p x n (r • y) = r • Work.DSM1p.FamClosure.of R p x n y := by
  rw [show r • y = algebraMap R (Work.DSM1p.FamTower R p x n) r * y from Algebra.smul_def r y,
    map_mul, of_algebraMap]
  exact (Algebra.smul_def r (Work.DSM1p.FamClosure.of R p x n y)).symm

/-- The canonical map from a stage of the tower into the closure, as an `R`-linear map. -/
noncomputable def ofLinearMap (n : ℕ) :
    Work.DSM1p.FamTower R p x n →ₗ[R] Work.DSM1p.FamClosure R p x where
  toFun := Work.DSM1p.FamClosure.of R p x n
  map_add' a b := map_add (Work.DSM1p.FamClosure.of R p x n) a b
  map_smul' r y := of_smul R p x n r y

@[simp] theorem ofLinearMap_apply (n : ℕ) (y : Work.DSM1p.FamTower R p x n) :
    ofLinearMap R p x n y = Work.DSM1p.FamClosure.of R p x n y := rfl

/-- The transition maps of the family tower are `R`-linear. -/
noncomputable def stepMapLinear (m n : ℕ) (h : m ≤ n) :
    Work.DSM1p.FamTower R p x m →ₗ[R] Work.DSM1p.FamTower R p x n where
  toFun := Work.DSM1p.FamTower.stepMap R p x m n h
  map_add' a b := map_add (Work.DSM1p.FamTower.stepMap R p x m n h) a b
  map_smul' r y := by
    rw [show r • y = algebraMap R (Work.DSM1p.FamTower R p x m) r * y from Algebra.smul_def r y,
      map_mul, stepMap_algebraMap]
    exact (Algebra.smul_def r (Work.DSM1p.FamTower.stepMap R p x m n h y)).symm

@[simp] theorem stepMapLinear_apply (m n : ℕ) (h : m ≤ n) (y : Work.DSM1p.FamTower R p x m) :
    stepMapLinear R p x m n h y = Work.DSM1p.FamTower.stepMap R p x m n h y := rfl

end Colimit

/-- **The root closure `R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]` is flat over `R`** (for `p ≠ 0`): it is a
filtered colimit of the free `R`-modules `R[X] ⧸ (X_i ^ p^n - x_i)`, and filtered colimits of flat
modules are flat. -/
theorem flat_closure (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (hp : p ≠ 0) :
    Module.Flat R (Work.DSM1p.FamClosure R p x) := by
  classical
  refine Module.Flat.of_forall_isTrivialRelation (M := Work.DSM1p.FamClosure R p x) ?_
  intro l f y hy
  -- Each `y i` is the image of an element of some stage of the tower.
  have hex : ∀ i : Fin l, ∃ (n : ℕ) (z : Work.DSM1p.FamTower R p x n),
      Work.DSM1p.FamClosure.of R p x n z = y i :=
    fun i => Ring.DirectLimit.exists_of (y i)
  choose m z hz using hex
  -- Move everything to the common stage `N = sup m`.
  let N : ℕ := Finset.univ.sup m
  have hle : ∀ i, m i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  let z' : Fin l → Work.DSM1p.FamTower R p x N :=
    fun i => Work.DSM1p.FamTower.stepMap R p x (m i) N (hle i) (z i)
  have hz' : ∀ i, Work.DSM1p.FamClosure.of R p x N (z' i) = y i := fun i => by
    have h1 : Work.DSM1p.FamClosure.of R p x N (z' i)
        = Work.DSM1p.FamClosure.of R p x (m i) (z i) := by
      simp only [z']
      exact Ring.DirectLimit.of_f (hle i) (z i)
    rw [h1, hz i]
  -- The relation, pushed to the stage `N`.
  let w : Work.DSM1p.FamTower R p x N := ∑ i, f i • z' i
  have hwlin : ofLinearMap R p x N w = 0 := by
    have h1 : ofLinearMap R p x N w = ∑ i, f i • y i := by
      simp only [w, map_sum, map_smul, ofLinearMap_apply]
      exact Finset.sum_congr rfl (fun i _ => by rw [hz' i])
    rw [h1, hy]
  have hw : Work.DSM1p.FamClosure.of R p x N w = 0 := by
    simpa only [ofLinearMap_apply] using hwlin
  -- A vanishing element of the colimit already vanishes in a later stage.
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (G := Work.DSM1p.FamTower R p x)
    (f' := Work.DSM1p.FamTower.stepMap R p x) hw
  let z'' : Fin l → Work.DSM1p.FamTower R p x j :=
    fun i => Work.DSM1p.FamTower.stepMap R p x N j hij (z' i)
  have hz'' : ∀ i, Work.DSM1p.FamClosure.of R p x j (z'' i) = y i := fun i => by
    have h1 : Work.DSM1p.FamClosure.of R p x j (z'' i)
        = Work.DSM1p.FamClosure.of R p x N (z' i) := by
      simp only [z'']
      exact Ring.DirectLimit.of_f hij (z' i)
    rw [h1, hz' i]
  have hwsum : ∑ i, f i • z'' i = 0 := by
    have h1 : stepMapLinear R p x N j hij w = ∑ i, f i • z'' i := by
      simp only [w, z'', map_sum, map_smul, stepMapLinear_apply]
    rw [← h1]
    exact hj
  -- The relation holds in the flat stage `FamTower R p x j`, where it is trivial.
  haveI : Module.Flat R (Work.DSM1p.FamTower R p x j) := flat_stage R p x hp j
  obtain ⟨k, aa, yy, hdec, hrel⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := f) (x := z'') hwsum
  refine ⟨k, aa, fun n => Work.DSM1p.FamClosure.of R p x j (yy n), fun i => ?_, hrel⟩
  have h1 : ofLinearMap R p x j (z'' i)
      = ∑ n, aa i n • Work.DSM1p.FamClosure.of R p x j (yy n) := by
    rw [hdec i, map_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [map_smul, ofLinearMap_apply])
  rw [← hz'' i]
  exact h1

end Work.DSM1p.Family

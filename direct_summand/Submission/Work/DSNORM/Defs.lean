import Mathlib
import Submission.Work.DSREG.Main

/-!
# DSNORM — regular local rings are integrally closed: basic API

This file sets up the vocabulary for the area DSNORM ("regular local rings are integrally closed",
the node `DSMap.Gaps.area_NORM` of the direct summand project).

Fix a Noetherian local ring `A` (`[IsLocalRing A] [IsNoetherianRing A]`), with maximal ideal
`𝔪 = IsLocalRing.maximalIdeal A`.

* `Work.DSNORM.nParams A` and `Work.DSNORM.params A : Fin (nParams A) → A` is a *chosen* family of
  elements generating `𝔪`, of cardinality `(maximalIdeal A).spanFinrank`.
* `Work.DSNORM.exists_homogeneous_eval_eq`: every `a ∈ 𝔪 ^ n` is the value at the parameters of a
  homogeneous polynomial of degree `n` (from `𝔪 ^ n = span ((range params) ^ n)`).
* `Work.DSNORM.ordNat A a` resp. `Work.DSNORM.ord A a : WithTop ℕ` is the `𝔪`-adic order:
  `a ∈ 𝔪 ^ n ↔ (n : WithTop ℕ) ≤ ord A a`.
* `Work.DSNORM.leadPoly A a` is a homogeneous polynomial of degree `ord A a` with value `a`;
  `Work.DSNORM.inForm A a` is its reduction modulo `𝔪`, an element of
  `MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A)`.  For a *regular local* ring this
  is the initial form of `a` in the associated graded ring `k[X₁,…,X_d]`, and the basic fact that
  makes it a useful invariant — its multiplicativity `inForm (a * b) = inForm a * inForm b` — is
  proved in `Submission/Work/DSNORM/InForm.lean` (it needs quasi-regularity of a regular system of
  parameters).

The final theorem of the area is `DSMap.Gaps.area_NORM_proved` in
`Submission/Work/DSNORM/Main.lean`.
-/

namespace Work.DSNORM

open scoped Pointwise

universe u

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The number of generators of the maximal ideal of `A`. -/
noncomputable def nParams : ℕ := (IsLocalRing.maximalIdeal A).spanFinrank

/-- A finite set of generators of the maximal ideal, of cardinality `nParams A`. -/
noncomputable def paramsFinset : Finset A :=
  (Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))).choose

theorem paramsFinset_card : (paramsFinset A).card = nParams A :=
  (Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))).choose_spec.1

theorem paramsFinset_span : Submodule.span A ((paramsFinset A : Finset A) : Set A)
    = IsLocalRing.maximalIdeal A :=
  (Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))).choose_spec.2

/-- A family of `nParams A` elements generating the maximal ideal of `A`. -/
noncomputable def params : Fin (nParams A) → A := fun i =>
  ((Finset.equivFin (paramsFinset A)).symm
    (Fin.cast (paramsFinset_card A).symm i) : A)

theorem params_range : Set.range (params A) = ((paramsFinset A : Finset A) : Set A) := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Finset.equivFin (paramsFinset A)).symm
      (Fin.cast (paramsFinset_card A).symm i)).2
  · intro ha
    refine ⟨Fin.cast (paramsFinset_card A) ((Finset.equivFin (paramsFinset A)) ⟨a, ha⟩), ?_⟩
    have h1 : Fin.cast (paramsFinset_card A).symm
        (Fin.cast (paramsFinset_card A) ((Finset.equivFin (paramsFinset A)) ⟨a, ha⟩))
        = (Finset.equivFin (paramsFinset A)) ⟨a, ha⟩ := by
      ext
      simp
    simp only [params, h1, Equiv.symm_apply_apply]

theorem params_span : Ideal.span (Set.range (params A)) = IsLocalRing.maximalIdeal A := by
  rw [params_range]
  exact paramsFinset_span A

/-- Every element of `𝔪 ^ n` is the value at the parameters of a homogeneous polynomial of
degree `n`. -/
theorem exists_homogeneous_eval_eq {a : A} {n : ℕ}
    (ha : a ∈ IsLocalRing.maximalIdeal A ^ n) :
    ∃ P : MvPolynomial (Fin (nParams A)) A,
      P.IsHomogeneous n ∧ MvPolynomial.eval (params A) P = a := by
  have hspan : IsLocalRing.maximalIdeal A ^ n
      = Submodule.span A (((Set.range (params A)) : Set A) ^ n) := by
    conv_lhs => rw [← params_span A, Ideal.span]
    exact Submodule.span_pow (Set.range (params A)) n
  have key : ∀ a ∈ Submodule.span A (((Set.range (params A)) : Set A) ^ n),
      ∃ P : MvPolynomial (Fin (nParams A)) A,
        P.IsHomogeneous n ∧ MvPolynomial.eval (params A) P = a := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
        rw [Set.mem_pow] at hy
        obtain ⟨f, hf⟩ := hy
        have hg : ∀ i, params A (Classical.choose (f i).2) = (f i : A) :=
          fun i => Classical.choose_spec (f i).2
        refine ⟨∏ i : Fin n, MvPolynomial.X (Classical.choose (f i).2), ?_, ?_⟩
        · have h1 : (∏ i : Fin n, MvPolynomial.X (Classical.choose (f i).2)).IsHomogeneous
              (∑ _i : Fin n, (1 : ℕ)) :=
            MvPolynomial.IsHomogeneous.prod Finset.univ _ _
              fun i _ => MvPolynomial.isHomogeneous_X A _
          simpa using h1
        · rw [map_prod]
          conv_rhs => rw [← hf, List.prod_ofFn]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [MvPolynomial.eval_X]
          exact hg i
    | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero (Fin (nParams A)) A n, by simp⟩
    | add y z hy hz ihy ihz =>
        obtain ⟨P, hP, hPy⟩ := ihy
        obtain ⟨Q, hQ, hQz⟩ := ihz
        exact ⟨P + Q, hP.add hQ, by rw [map_add, hPy, hQz]⟩
    | smul c y hy ihy =>
        obtain ⟨P, hP, hPy⟩ := ihy
        exact ⟨MvPolynomial.C c * P, hP.C_mul c, by
          rw [map_mul, hPy, smul_eq_mul, MvPolynomial.eval_C]⟩
  exact key a (by rw [← hspan]; exact ha)

/-- For `a ≠ 0` there is an `n` with `a ∉ 𝔪 ^ n` (Krull's intersection theorem). -/
theorem exists_notMem_pow (a : A) (ha : a ≠ 0) :
    ∃ n : ℕ, a ∉ IsLocalRing.maximalIdeal A ^ n := by
  by_contra hcon
  push Not at hcon
  refine ha ?_
  have hbot : (⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n) = (⊥ : Ideal A) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have : a ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n) := (Submodule.mem_iInf _).mpr hcon
  rw [hbot] at this
  simpa using this

/-- For `a : A`, the `𝔪`-adic order of `a`: the largest `n` with `a ∈ 𝔪 ^ n`, and `0` when
`a = 0`. -/
noncomputable def ordNat (a : A) : ℕ :=
  sInf {n : ℕ | a ∉ IsLocalRing.maximalIdeal A ^ (n + 1)}

theorem ordNat_set_nonempty {a : A} (ha : a ≠ 0) :
    {n : ℕ | a ∉ IsLocalRing.maximalIdeal A ^ (n + 1)}.Nonempty := by
  obtain ⟨k, hk⟩ := exists_notMem_pow A a ha
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, pow_zero] at hk
    exact absurd (show a ∈ (1 : Ideal A) from by rw [Ideal.one_eq_top]; exact Submodule.mem_top) hk
  · refine ⟨k - 1, ?_⟩
    show a ∉ IsLocalRing.maximalIdeal A ^ (k - 1 + 1)
    rw [Nat.sub_add_cancel h]
    exact hk

theorem mem_pow_succ_of_lt_ordNat {a : A} {n : ℕ} (hn : n < ordNat A a) :
    a ∈ IsLocalRing.maximalIdeal A ^ (n + 1) := by
  by_contra hc
  exact absurd (Nat.sInf_le hc) (not_le.mpr hn)

theorem mem_pow_ordNat (a : A) : a ∈ IsLocalRing.maximalIdeal A ^ ordNat A a := by
  rcases Nat.eq_zero_or_pos (ordNat A a) with h | h
  · rw [h, pow_zero]
    rw [Ideal.one_eq_top]
    exact Submodule.mem_top
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [hk]
    exact mem_pow_succ_of_lt_ordNat (A := A) (a := a) (n := k) (by omega)

theorem notMem_pow_ordNat_succ {a : A} (ha : a ≠ 0) :
    a ∉ IsLocalRing.maximalIdeal A ^ (ordNat A a + 1) :=
  Nat.sInf_mem (ordNat_set_nonempty A ha)

theorem ordNat_zero : ordNat A (0 : A) = 0 := by
  have h : {n : ℕ | (0 : A) ∉ IsLocalRing.maximalIdeal A ^ (n + 1)} = ∅ := by
    ext n
    simp
  rw [ordNat, h, Nat.sInf_empty]

theorem ordNat_spec {a : A} (ha : a ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal A ^ ordNat A a ∧
      a ∉ IsLocalRing.maximalIdeal A ^ (ordNat A a + 1) :=
  ⟨mem_pow_ordNat A a, notMem_pow_ordNat_succ A ha⟩

theorem le_ordNat_of_mem {a : A} (ha : a ≠ 0) {n : ℕ}
    (hn : a ∈ IsLocalRing.maximalIdeal A ^ n) : n ≤ ordNat A a := by
  by_contra hcon
  push Not at hcon
  exact notMem_pow_ordNat_succ A ha (Ideal.pow_le_pow_right (by omega) hn)

/-- The `𝔪`-adic order of an element, as an element of `WithTop ℕ` (`⊤` for `0`). -/
noncomputable def ord (a : A) : WithTop ℕ := by
  classical
  exact if a = 0 then ⊤ else (ordNat A a : WithTop ℕ)

theorem ord_eq_coe_ordNat {a : A} (ha : a ≠ 0) : ord A a = (ordNat A a : WithTop ℕ) := by
  classical
  rw [ord, if_neg ha]

theorem mem_iff_le_ordNat {a : A} (ha : a ≠ 0) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal A ^ n ↔ n ≤ ordNat A a :=
  ⟨fun hn => le_ordNat_of_mem A ha hn, fun hn =>
    Ideal.pow_le_pow_right hn (mem_pow_ordNat A a)⟩

theorem mem_pow_iff_le_ord (a : A) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal A ^ n ↔ (n : WithTop ℕ) ≤ ord A a := by
  classical
  by_cases ha : a = 0
  · subst ha
    simp [ord]
  · rw [ord_eq_coe_ordNat A ha]
    exact (mem_iff_le_ordNat A ha n).trans
      (WithTop.coe_le_coe (a := ordNat A a) (b := n)).symm

theorem ord_eq_top_iff {a : A} : ord A a = ⊤ ↔ a = 0 := by
  classical
  by_cases ha : a = 0
  · simp [ord, ha]
  · constructor
    · intro h
      rw [ord, if_neg ha] at h
      exact absurd h WithTop.coe_ne_top
    · intro h
      exact absurd h ha

theorem ord_ne_top_iff {a : A} : ord A a ≠ ⊤ ↔ a ≠ 0 := by
  rw [ne_eq, ord_eq_top_iff]

/-- A homogeneous polynomial of degree `ord A a` whose value at the parameters is `a`. -/
noncomputable def leadPoly (a : A) : MvPolynomial (Fin (nParams A)) A := by
  classical
  exact if h : a = 0 then 0
    else Classical.choose (exists_homogeneous_eval_eq A ((ordNat_spec A h).1))

theorem leadPoly_eq_choose {a : A} (ha : a ≠ 0) :
    leadPoly A a = Classical.choose (exists_homogeneous_eval_eq A ((ordNat_spec A ha).1)) := by
  classical
  rw [leadPoly, dif_neg ha]

theorem eval_leadPoly {a : A} (ha : a ≠ 0) :
    MvPolynomial.eval (params A) (leadPoly A a) = a := by
  rw [leadPoly_eq_choose A ha]
  exact (Classical.choose_spec (exists_homogeneous_eval_eq A ((ordNat_spec A ha).1))).2

theorem leadPoly_isHomogeneous {a : A} (ha : a ≠ 0) :
    (leadPoly A a).IsHomogeneous (ordNat A a) := by
  rw [leadPoly_eq_choose A ha]
  exact (Classical.choose_spec (exists_homogeneous_eval_eq A ((ordNat_spec A ha).1))).1

/-- The initial form of `a`: the leading polynomial reduced modulo `𝔪`, i.e. an element of the
degree-`ord A a` part of the associated graded ring, transported to `k[X₁,…,X_d]`. -/
noncomputable def inForm (a : A) : MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A) :=
  (leadPoly A a).map (IsLocalRing.residue A)

@[simp]
theorem inForm_zero : inForm A 0 = 0 := by
  simp [inForm, leadPoly]

/-- A section of the residue map `A → k`, used to lift polynomials over `k` to polynomials
over `A`. -/
noncomputable def sec : IsLocalRing.ResidueField A → A := fun c => Quotient.out c

theorem residue_sec (c : IsLocalRing.ResidueField A) : IsLocalRing.residue A (sec A c) = c :=
  Ideal.Quotient.mk_out c

/-- Lift a polynomial over the residue field to a polynomial over `A`, coefficient by
coefficient, using the section `sec`. -/
noncomputable def secPoly
    (F : MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A)) :
    MvPolynomial (Fin (nParams A)) A :=
  F.support.sum fun s => MvPolynomial.monomial s (sec A (F.coeff s))

theorem secPoly_map (F : MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A)) :
    (secPoly A F).map (IsLocalRing.residue A) = F := by
  rw [secPoly, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum F]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.map_monomial, residue_sec]

theorem secPoly_isHomogeneous {F : MvPolynomial (Fin (nParams A)) (IsLocalRing.ResidueField A)}
    {n : ℕ} (hF : F.IsHomogeneous n) : (secPoly A F).IsHomogeneous n := by
  rw [secPoly]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_
  rw [MvPolynomial.mem_support_iff] at hs
  exact MvPolynomial.isHomogeneous_monomial _ (by
    by_contra hdeg
    exact hs (hF.coeff_eq_zero hdeg))

end Work.DSNORM

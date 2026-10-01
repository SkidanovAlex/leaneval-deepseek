import Mathlib
import Submission.Commons.NumberTheory.Stepanov.stepanov_bound_general
import Submission.Commons.NumberTheory.Stepanov.hasseDeriv_pow_factor

/-!
# The general-`e` Stepanov counting lemma (with a witness), `R = ∑_r A_r(X,X^q) g^(r·k)`

This file proves the counting bound

`#{x : g x ^ ((q-1)/e) = 1} · M ≤ A₀ + q·B + (e-1)·(k·deg g)`,  `q = #F`, `k = (q-1)/e`,

for a family `A_r ∈ F[X][Y]`, `r : Fin e`, whose coefficients have `X`-degree `≤ A₀` and whose
`Y`-degree is `≤ B`, subject to the Stepanov conditions

* `∑_r A1lm g 0 (r·k) ℓ (A_r) = 0` for all `ℓ < M`,
* `R := ∑_r A_r(X, X^q) · g^(r·k) ≠ 0`.

This is the *second half* of Stepanov's method (the divisibility/degree count), generalising
`stepanov_count` from `e = 2` to an arbitrary `e`, and it is the "count given a witness" input of
`superelliptic_char_sum_bound`.

The file also contains the *first half*, the dimension count
`stevanov_witness_exists : ∃ (A_r) ≠ 0, (degree bounds) ∧ (conditions)` (and its arithmetic form
`stevanov_witness_exists_of_arith`).  Filling the remaining gap (the injectivity of
`(A_r) ↦ ∑_r A_r(X,X^q) g^(r·k)`, i.e. the non-vanishing input) turns these two into the
unconditional bound `#{x : g x ^ k = 1} ≤ q/e + O_{e,deg g}(√q)`.

Finally, the *monomial case* `g = c·X^D` (for which the conditions are not available) is reduced
to the elementary count `ncard_pow_eq_le_gcd` (a finite field has at most `gcd m (#F-1)` `m`-th
roots of any element) in `ncard_gpow_eq_one_monomial`, giving the sharp bound
`#{x : (c x^D)^k = 1} ≤ k`.

## The method

The single new ingredient is the evaluation formula
`stevanov_eval_hasseDeriv_mul`: for `ℓ ≤ u`, `ℓ < q` and `g x ^ u = 1`,

`(g^ℓ · ∂^ℓ (Q(X,X^q) · g^u)) (x) = A1lm g 0 u ℓ Q (x)`,

which is `hasseDeriv_frobenius_form` with `P = 0`, evaluated at `x`.  Summing it over `r` and
using `∑_r A1lm g 0 (r·k) ℓ (A_r) = 0` (and `(g x)^(r·k) = ((g x)^k)^r = 1` at a good point `x`)
gives `(X - x)^M ∣ R` for every good `x`, whence `#{good x}·M ≤ deg R`, and `deg R` is bounded
by `A₀ + q·B + (e-1)·k·deg g`.

The case `r = 0` needs `A1lm g 0 0 ℓ Q = A0lm g ℓ Q`, i.e. the fact that the cofactor
`wcoef g 0 i` is `δ_{i,0}` (see `A1lm_zero_eq_A0lm`).  That cofactor is `private` in
`Submission.Commons.NumberTheory.Stepanov.stepanov_bound_general`, so this file gives a public
copy `stevanovWcoef` of it, built from the public lemma
`Commons.NumberTheory.Stepanov.hasseDeriv_pow_factor`, together with the definitional equality
`A1lm g hg hd u ℓ = stevanovA1lm g hg hd u ℓ` (`rfl`: the two definitions differ only in the *proof*
component of the `Classical.choose` defining the cofactor, and proofs are definitionally
irrelevant).  Only these two lemmas of the file depend on that trick; every other statement is
about public objects.
-/

namespace Commons.NumberTheory.Stepanov

open Polynomial

noncomputable section

/-! ## A public copy of the cofactor `wcoef` and of `A1lm` -/

/-- The cofactor `wcoef` of `hasseDeriv i (g^u) = g^(u-i) * wcoef`, made public.  (The private
`wcoef` of `stepanov_bound_general.lean` has exactly this definition, so this is *definitionally*
equal to it.) -/
def stevanovWcoef {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u i : ℕ) : Polynomial F :=
  if h : i ≤ u then Classical.choose (hasseDeriv_pow_factor g hg hd u i h) else 0

lemma stevanovWcoef_spec {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u i : ℕ) (hi : i ≤ u) :
    Polynomial.hasseDeriv i (g ^ u) = g ^ (u - i) * stevanovWcoef g hg hd u i ∧
      (stevanovWcoef g hg hd u i).natDegree ≤ i * g.natDegree := by
  rw [stevanovWcoef, dif_pos hi]
  exact Classical.choose_spec (hasseDeriv_pow_factor g hg hd u i hi)

lemma stevanovWcoef_eq_zero {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) {u i : ℕ} (h : u < i) : stevanovWcoef g hg hd u i = 0 := by
  rw [stevanovWcoef, dif_neg (by omega)]

lemma stevanovWcoef_zero_zero {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) : stevanovWcoef g hg hd 0 0 = 1 := by
  have h := (stevanovWcoef_spec g hg hd 0 0 (le_refl 0)).1
  simpa using h.symm

/-- `A1lm` built from the public cofactor `stevanovWcoef`; it is *definitionally* equal to the
`A1lm` of `stepanov_bound_general` (see `stevanovA1lm_eq_A1lm`). -/
def stevanovA1lm {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree)
    (u ℓ : ℕ) : Polynomial (Polynomial F) →ₗ[F] Polynomial F :=
  ∑ i ∈ Finset.range (ℓ+1),
    (mulLM (g^(ℓ-i) * stevanovWcoef g hg hd u i)).comp (evX.comp (Dlm (ℓ-i)))

lemma stevanovA1lm_eq_A1lm {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u ℓ : ℕ) :
    A1lm g hg hd u ℓ = stevanovA1lm g hg hd u ℓ := rfl

lemma stevanovA1lm_apply {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u ℓ : ℕ) (Q : Polynomial (Polynomial F)) :
    stevanovA1lm g hg hd u ℓ Q = ∑ i ∈ Finset.range (ℓ+1),
      (g^(ℓ-i) * stevanovWcoef g hg hd u i) * (D (ℓ-i) Q).eval (Polynomial.X : Polynomial F) := by
  simp only [stevanovA1lm, LinearMap.sum_apply, LinearMap.comp_apply, mulLM_apply, evX_apply,
    Dlm_apply]

/-- At `u = 0` the two operators coincide: `A1lm g hg hd 0 ℓ` is the "`P`-part" `A0lm g ℓ`. -/
theorem A1lm_zero_eq_A0lm {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (ℓ : ℕ) (Q : Polynomial (Polynomial F)) :
    A1lm g hg hd 0 ℓ Q = A0lm g ℓ Q := by
  rw [stevanovA1lm_eq_A1lm, stevanovA1lm_apply, A0lm_apply]
  rw [Finset.sum_eq_single 0]
  · rw [stevanovWcoef_zero_zero]; simp
  · intro i hi hne
    rw [stevanovWcoef_eq_zero g hg hd (u := 0) (i := i) (by omega)]
    simp
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos ℓ)) hmem

/-! ## The key evaluation formula -/

/-- For `ℓ ≤ u`, `ℓ < q`, and a point `x` with `g x ^ u = 1`:
`(g^ℓ · ∂^ℓ (Q(X,X^q)·g^u)) (x) = (A1lm g hg hd u ℓ Q) (x)`.
This is `hasseDeriv_frobenius_form` (with `P = 0`) evaluated at `x`, using `x^q = x`. -/
lemma stevanov_eval_hasseDeriv_mul {F : Type*} [Field F] [Fintype F]
    (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (u ℓ : ℕ)
    (hq : ℓ < Fintype.card F) (hℓu : ℓ ≤ u) (Q : Polynomial (Polynomial F)) (x : F)
    (hx : g.eval x ^ u = 1) :
    Polynomial.eval x (g^ℓ * Polynomial.hasseDeriv ℓ
        (Q.eval (Polynomial.X ^ Fintype.card F) * g^u))
      = Polynomial.eval x (A1lm g hg hd u ℓ Q) := by
  rw [mul_comm (Q.eval (Polynomial.X ^ Fintype.card F)) (g^u)]
  have h := hasseDeriv_frobenius_form g hg hd u ℓ hq hℓu 0 Q
  have h1 := congrArg (Polynomial.eval x) h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_zero, D_zero,
    mul_zero, zero_add] at h1
  rw [eval_eval_Xq_eq, eval_X_C_sum] at h1
  rw [hx, one_mul] at h1
  rw [Polynomial.eval_mul, Polynomial.eval_pow]
  exact h1

/-! ## The counting lemma -/

/-- **Stepanov's count (general `e`, given a witness).**  If the family `A_r`, `r : Fin e`,
satisfies the Stepanov conditions `∑_r A1lm g 0 (r·k) ℓ (A_r) = 0` for `ℓ < M` and the twisted
combination `R = ∑_r A_r(X,X^q) g^(r·k)` is nonzero, then the number of points `x` with
`g x ^ k = 1` is at most `(A₀ + q·B + (e-1)·k·deg g)/M`. -/
theorem stevanov_count_gpow {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (hdiv : e ∣ Fintype.card F - 1) (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree)
    (A₀ B M : ℕ) (hM : 1 ≤ M) (hMk : M ≤ (Fintype.card F - 1) / e)
    (AA : Fin e → Polynomial (Polynomial F))
    (hA : ∀ r (j : ℕ), ((AA r).coeff j).natDegree ≤ A₀) (hB : ∀ r, (AA r).natDegree ≤ B)
    (hcond : ∀ ℓ < M, (Finset.univ.sum fun r : Fin e =>
        Commons.NumberTheory.Stepanov.A1lm g hg hd ((r : ℕ) * ((Fintype.card F - 1) / e)) ℓ (AA r)) = 0)
    (hne : (Finset.univ.sum fun r : Fin e =>
        (AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)
          * g ^ ((r : ℕ) * ((Fintype.card F - 1) / e))) ≠ 0) :
    (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard) * M ≤
      A₀ + Fintype.card F * B + (e - 1) * (((Fintype.card F - 1) / e) * g.natDegree) := by
  classical
  set k := (Fintype.card F - 1) / e with hk
  have hMk' : M ≤ k := by rw [hk]; exact hMk
  have hcond' : ∀ ℓ < M, (Finset.univ.sum fun r : Fin e =>
      A1lm g hg hd ((r : ℕ) * k) ℓ (AA r)) = 0 := by
    intro ℓ hℓ
    simpa [hk] using hcond ℓ hℓ
  set R : Polynomial F := ∑ r : Fin e,
    (AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F) * g ^ ((r:ℕ) * k) with hRdef
  have hRne : R ≠ 0 := by
    rw [hRdef]
    simpa [hk] using hne
  -- **Step 1**: `(X - x)^M ∣ R` for every `x` with `g x ^ k = 1`, hence `#S · M ≤ deg R`.
  have hmain : (({x : F | g.eval x ^ k = 1} : Set F).ncard) * M ≤ R.natDegree := by
    rw [Set.ncard_eq_toFinset_card']
    refine card_mul_le_natDegree_of_pow_dvd hRne ?_
    intro x hxmem
    have hx : g.eval x ^ k = 1 := by simpa using hxmem
    have hx0 : g.eval x ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega : k ≠ 0)] at hx
      exact one_ne_zero hx.symm
    apply X_sub_C_pow_dvd_of_hasseDeriv
    intro ℓ hℓM
    have hℓq : ℓ < Fintype.card F := by
      have h3 : k ≤ Fintype.card F - 1 := by rw [hk]; exact Nat.div_le_self _ _
      omega
    have hgu : ∀ r : Fin e, (g.eval x) ^ ((r:ℕ) * k) = 1 := by
      intro r
      rw [mul_comm, pow_mul, hx, one_pow]
    have key : ∀ r : Fin e,
        Polynomial.eval x (g^ℓ * Polynomial.hasseDeriv ℓ
            ((AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F) * g ^ ((r:ℕ)*k)))
          = Polynomial.eval x (A1lm g hg hd ((r:ℕ)*k) ℓ (AA r)) := by
      intro r
      by_cases hr : (r:ℕ) = 0
      · -- `r = 0`: the `P`-part, via `A1lm_zero_eq_A0lm` and `hasseDeriv_eval_X_pow_card`
        have hu : (r:ℕ) * k = 0 := by rw [hr, zero_mul]
        rw [hu, A1lm_zero_eq_A0lm g hg hd ℓ (AA r), pow_zero, mul_one,
            hasseDeriv_eval_X_pow_card (AA r) ℓ hℓq, A0lm_apply]
        simp only [D, Polynomial.eval_mul, Polynomial.eval_pow]
        rw [eval_eval_Xq_eq]
      · -- `r ≠ 0`: `ℓ ≤ k ≤ r·k`, so the Frobenius-form identity applies
        refine stevanov_eval_hasseDeriv_mul g hg hd ((r:ℕ)*k) ℓ hℓq ?_ (AA r) x (hgu r)
        have hr1 : 1 ≤ (r:ℕ) := Nat.one_le_iff_ne_zero.mpr hr
        calc ℓ ≤ M := le_of_lt hℓM
          _ ≤ k := hMk'
          _ = 1 * k := (one_mul k).symm
          _ ≤ (r:ℕ) * k := Nat.mul_le_mul_right k hr1
    have hstep : Polynomial.hasseDeriv ℓ R = ∑ r : Fin e, Polynomial.hasseDeriv ℓ
        ((AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F) * g ^ ((r:ℕ)*k)) := by
      rw [hRdef]
      exact map_sum (Polynomial.hasseDeriv ℓ) _ _
    have hzero : Polynomial.eval x (g^ℓ * Polynomial.hasseDeriv ℓ R) = 0 := by
      rw [hstep, Finset.mul_sum, Polynomial.eval_finsetSum]
      rw [Finset.sum_congr rfl (fun r _ => key r)]
      rw [← Polynomial.eval_finsetSum, hcond' ℓ hℓM, Polynomial.eval_zero]
    have hmul : (g.eval x)^ℓ * Polynomial.eval x (Polynomial.hasseDeriv ℓ R) = 0 := by
      rw [← hzero, Polynomial.eval_mul, Polynomial.eval_pow]
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hx0)
  -- **Step 2**: degree bound for `R`.
  have hdeg : R.natDegree ≤ A₀ + Fintype.card F * B + (e - 1) * (k * g.natDegree) := by
    rw [hRdef]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, ?_⟩
    intro r _
    have h1 : ((AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)
        * g ^ ((r:ℕ)*k)).natDegree ≤ (A₀ + Fintype.card F * B) + ((r:ℕ)*k) * g.natDegree := by
      calc ((AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F) * g ^ ((r:ℕ)*k)).natDegree
          ≤ ((AA r).eval ((Polynomial.X : Polynomial F) ^ Fintype.card F)).natDegree
              + (g ^ ((r:ℕ)*k)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ (A₀ + Fintype.card F * B) + ((r:ℕ)*k) * g.natDegree := by
            gcongr
            · exact eval_Xq_natDegree_le (AA r) A₀ B (Fintype.card F) (hA r) (hB r)
            · rw [Polynomial.natDegree_pow]
    refine h1.trans ?_
    have hrle : (r:ℕ) ≤ e - 1 := by have := r.isLt; omega
    have h2 : ((r:ℕ)*k) * g.natDegree ≤ (e-1) * (k * g.natDegree) := by
      calc ((r:ℕ)*k) * g.natDegree = (r:ℕ) * (k * g.natDegree) := Nat.mul_assoc _ _ _
        _ ≤ (e-1) * (k * g.natDegree) := Nat.mul_le_mul_right _ hrle
    exact Nat.add_le_add_left h2 _
  exact le_trans hmain hdeg
/-! ## The dimension count: a nonzero family satisfying the Stepanov conditions exists -/

open scoped BigOperators in
/-- **Existence of a witness** (the dimension-count half of Stepanov's method, general `e`).

The `ℓ`-th Stepanov condition `∑_r A1lm g hg hd (r·k) ℓ (A_r) = 0` is a linear condition of
"length" `A₀ + B + ℓ·deg g + 1` on the space of families `(A_r)`, which has dimension
`e·(A₀+1)·(B+1)`; hence if the total number of linear conditions is smaller, a nonzero solution
exists.  The hypothesis `hdim` below is exactly this rank count (`M ≤ k = (q-1)/e` is needed to
know that `ℓ ≤ r·k` for `r ≠ 0`, which makes the `ℓ`-th condition have that length — for `r = 0`
this is `A1lm_zero_eq_A0lm`).  See `stevanov_witness_exists_of_arith` for the purely arithmetic
form of the hypothesis. -/
theorem stevanov_witness_exists {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (A₀ B M : ℕ)
    (hMk : M ≤ (Fintype.card F - 1) / e)
    (hdim : (Finset.univ.sum fun l : Fin M => (A₀ + B + l.val * g.natDegree + 1))
      < e * ((A₀ + 1) * (B + 1))) :
    ∃ AA : Fin e → Polynomial (Polynomial F),
      (∀ r (j : ℕ), ((AA r).coeff j).natDegree ≤ A₀) ∧
      (∀ r, (AA r).natDegree ≤ B) ∧
      (∀ ℓ < M, (Finset.univ.sum fun r : Fin e =>
        A1lm g hg hd ((r : ℕ) * ((Fintype.card F - 1) / e)) ℓ (AA r)) = 0) ∧
      AA ≠ 0 := by
  classical
  set k := (Fintype.card F - 1) / e with hk
  set D := g.natDegree with hD
  let iota := Fin (A₀ + 1) × Fin (B + 1)
  let E := Fin e → (iota → F)
  let Cc := (l : Fin M) → Fin (A₀ + B + l.val * D + 1) → F
  let Psi : E →ₗ[F] Cc := LinearMap.pi (fun l : Fin M => LinearMap.pi
    (fun j : Fin (A₀ + B + l.val * D + 1) =>
      (Polynomial.lcoeff F j).comp
        (∑ r : Fin e, (A1lm g hg hd ((r:ℕ) * k) l.val).comp
          ((toPolyLm (F := F) A₀ B).comp
            (LinearMap.proj (R := F) (φ := fun _ : Fin e => (iota → F)) r)))))
  have hfinE : Module.finrank F E = e * ((A₀ + 1) * (B + 1)) := by
    simp only [E, iota, Module.finrank_pi_fintype, Module.finrank_self,
      Fintype.card_fin, Fintype.card_prod, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
  have hfinCc : Module.finrank F Cc = ∑ l : Fin M, (A₀ + B + l.val * D + 1) := by
    simp only [Cc, Module.finrank_pi_fintype, Module.finrank_self, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  have hlt : Module.finrank F Cc < Module.finrank F E := by
    rw [hfinE, hfinCc]
    exact hdim
  have hker : Psi.ker ≠ ⊥ := by
    intro hbot
    have h1 := Psi.finrank_range_add_finrank_ker
    have h2 : Module.finrank F Psi.range ≤ Module.finrank F Cc := Submodule.finrank_le _
    rw [hbot] at h1
    simp only [finrank_bot, add_zero] at h1
    omega
  obtain ⟨c, hcker, hc0⟩ := (Submodule.ne_bot_iff Psi.ker).mp hker
  rw [LinearMap.mem_ker] at hcker
  refine ⟨fun r => toPolyLm (F := F) A₀ B (fun p : iota => c r p), ?_, ?_, ?_, ?_⟩
  · intro r j
    exact toPolyLm_coeff_natDegree_le A₀ B _ j
  · intro r
    exact toPolyLm_natDegree_le A₀ B _
  · intro l hlM
    set Q : Polynomial F := ∑ r : Fin e,
      A1lm g hg hd ((r:ℕ) * k) l (toPolyLm (F := F) A₀ B (fun p : iota => c r p)) with hQ
    have hcoe : ∀ n < A₀ + B + l * D + 1, Q.coeff n = 0 := by
      intro n hn
      have h1 : Psi c ⟨l, hlM⟩ ⟨n, hn⟩ = 0 := congrFun (congrFun hcker ⟨l, hlM⟩) ⟨n, hn⟩
      have h2 : Psi c ⟨l, hlM⟩ ⟨n, hn⟩ = (∑ r : Fin e, A1lm g hg hd ((r:ℕ) * k) l
          (toPolyLm (F := F) A₀ B (fun p : iota => c r p))).coeff n := by
        simp only [Psi]
        rw [LinearMap.pi_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.sum_apply]
        rfl
      rw [h2] at h1
      rw [hQ]
      exact h1
    have hdeg : Q.natDegree < A₀ + B + l * D + 1 := by
      rw [hQ]
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
      apply Nat.lt_succ_of_le
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, ?_⟩
      intro r _
      simp only [Function.comp_apply]
      by_cases hr : (r:ℕ) = 0
      · rw [hr, zero_mul, A1lm_zero_eq_A0lm]
        have hb := A0lm_natDegree_le g l A₀ B (toPolyLm (F := F) A₀ B (fun p : iota => c r p))
          (toPolyLm_coeff_natDegree_le A₀ B _) (toPolyLm_natDegree_le A₀ B _)
        rw [← hD] at hb
        omega
      · have hr1 : 1 ≤ (r:ℕ) := Nat.one_le_iff_ne_zero.mpr hr
        have hle : l ≤ (r:ℕ) * k := by
          calc l ≤ M := le_of_lt hlM
            _ ≤ k := hMk
            _ = 1 * k := (one_mul k).symm
            _ ≤ (r:ℕ) * k := Nat.mul_le_mul_right k hr1
        have hb := A1lm_natDegree_le g hg hd ((r:ℕ)*k) l A₀ B hle
          (toPolyLm (F := F) A₀ B (fun p : iota => c r p))
          (toPolyLm_coeff_natDegree_le A₀ B _) (toPolyLm_natDegree_le A₀ B _)
        rw [← hD] at hb
        omega
    exact eq_zero_of_coeff_eq_zero hdeg hcoe
  · intro hAA
    apply hc0
    funext x p
    obtain ⟨i, j⟩ := p
    show c x (i, j) = 0
    have h := congrFun hAA x
    have h3 := congrArg (fun q : Polynomial (Polynomial F) =>
      (q.coeff (j:ℕ)).coeff (i:ℕ)) h
    simpa [toPolyLm_coeff] using h3

/-- Arithmetic form of the rank count: `∑_{ℓ<M} (A₀ + B + ℓ·deg g + 1)
= M·(A₀+B+1) + deg g · M(M-1)/2`. -/
lemma sum_stevanov_cond_length (D M A₀ B : ℕ) :
    (Finset.univ.sum fun l : Fin M => (A₀ + B + l.val * D + 1))
      = M * (A₀ + B + 1) + D * (M * (M - 1) / 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (A₀ + B + i * D + 1)) M]
  have h1 : ∀ i : ℕ, (A₀ + B + i * D + 1) = (A₀ + B + 1) + i * D := by
    intro i; ring
  simp only [h1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.sum_mul, Finset.sum_range_id]
  ring

open scoped BigOperators in
/-- **Existence of a witness, arithmetic form**: if `M·(A₀+B+1) + deg g · M(M-1)/2` linear
conditions fit in the `e·(A₀+1)·(B+1)`-dimensional space of families, a nonzero family satisfying
the Stepanov conditions exists. -/
theorem stevanov_witness_exists_of_arith {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (g : Polynomial F) (hg : g ≠ 0) (hd : 1 ≤ g.natDegree) (A₀ B M : ℕ)
    (hMk : M ≤ (Fintype.card F - 1) / e)
    (hdim : M * (A₀ + B + 1) + g.natDegree * (M * (M - 1) / 2)
      < e * ((A₀ + 1) * (B + 1))) :
    ∃ AA : Fin e → Polynomial (Polynomial F),
      (∀ r (j : ℕ), ((AA r).coeff j).natDegree ≤ A₀) ∧
      (∀ r, (AA r).natDegree ≤ B) ∧
      (∀ ℓ < M, (Finset.univ.sum fun r : Fin e =>
        A1lm g hg hd ((r : ℕ) * ((Fintype.card F - 1) / e)) ℓ (AA r)) = 0) ∧
      AA ≠ 0 := by
  refine stevanov_witness_exists e he g hg hd A₀ B M hMk ?_
  rw [sum_stevanov_cond_length]
  exact hdim

/-! ## The monomial case: `#{x : (c x^D)^((q-1)/e) = 1} ≤ (q-1)/e`

For `g = c·X^D` the Stepanov conditions are not available, but the count is elementary: the
solutions of `(c x^D)^k = 1` form a coset of the group of `Dk`-th roots of unity, and (since the
multiplicative group of a finite field is cyclic) that group has at most `gcd(Dk, q-1) = k·gcd(D,e)`
elements.  This is the monomial case of the general-`e` Stepanov method. -/

/-- In a finite field, the number of `m`-th roots of a given element is at most
`gcd m (#F - 1)` (the group `Fˣ` is cyclic of order `#F - 1`). -/
theorem ncard_pow_eq_le_gcd {F : Type*} [Field F] [Fintype F] (m : ℕ) (hm : 0 < m) (a : F) :
    (({x : F | x ^ m = a} : Set F).ncard) ≤ Nat.gcd m (Fintype.card F - 1) := by
  classical
  -- the subgroup of `m`-th roots of unity
  let K : Subgroup Fˣ :=
    { carrier := {u | u ^ m = 1}
      one_mem' := by simp
      mul_mem' := by intro u v hu hv; rw [Set.mem_setOf_eq] at hu hv ⊢; rw [mul_pow, hu, hv, one_mul]
      inv_mem' := by intro u hu; rw [Set.mem_setOf_eq] at hu ⊢; rw [inv_pow, hu, inv_one] }
  have hmem : ∀ u : Fˣ, u ∈ K ↔ u ^ m = 1 := fun u => Iff.rfl
  have hKcyc : IsCyclic ↥K := by
    haveI : Finite ↥K := Finite.of_fintype _
    exact isCyclic_subgroup_units K
  have hKdvd1 : Nat.card ↥K ∣ m := by
    haveI := hKcyc
    obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := ↥K)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hz, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using (hmem (z : Fˣ)).mp z.2)
  have hKdvd2 : Nat.card ↥K ∣ Fintype.card F - 1 := by
    have h : Nat.card ↥K ∣ Nat.card F - 1 := by
      rw [← Nat.card_units F]
      exact Subgroup.card_subgroup_dvd_card K
    simpa [Nat.card_eq_fintype_card] using h
  have hKgcd : Nat.card ↥K ≤ Nat.gcd m (Fintype.card F - 1) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hm) (Nat.dvd_gcd hKdvd1 hKdvd2)
  rcases eq_or_ne a 0 with rfl | ha
  · -- `a = 0`: the only root is `0`
    have hsub : ({x : F | x ^ m = 0} : Set F) ⊆ {0} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_singleton_iff]
      by_contra hx0
      exact pow_ne_zero m hx0 hx
    calc ({x : F | x ^ m = 0} : Set F).ncard ≤ ({0} : Set F).ncard := Set.ncard_le_ncard hsub
      _ = 1 := by simp
      _ ≤ Nat.gcd m (Fintype.card F - 1) := Nat.gcd_pos_of_pos_left _ hm
  · -- `a ≠ 0`: the roots are a coset of `K`
    rcases Set.eq_empty_or_nonempty ({x : F | x ^ m = a} : Set F) with hemp | ⟨x₀, hx₀⟩
    · rw [hemp]; simp
    · have hne : ∀ x ∈ ({x : F | x ^ m = a} : Set F), x ≠ 0 := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        rintro rfl
        rw [zero_pow hm.ne'] at hx
        exact ha hx.symm
      have hx₀ne : x₀ ≠ 0 := hne x₀ hx₀
      let f : F → Fˣ := fun x => if h : x = 0 then 1 else Units.mk0 (x / x₀) (div_ne_zero h hx₀ne)
      have hfval : ∀ x ∈ ({x : F | x ^ m = a} : Set F), (f x : F) = x / x₀ := by
        intro x hx
        simp only [f]
        rw [dif_neg (hne x hx)]
        exact Units.val_mk0 _
      have hmap : ∀ x ∈ ({x : F | x ^ m = a} : Set F), f x ∈ K := by
        intro x hx
        rw [hmem]
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hfval x hx, Units.val_one, div_pow, hx, hx₀, div_self ha]
      have hinj : Set.InjOn f ({x : F | x ^ m = a} : Set F) := by
        intro x hx y hy hxy
        have h1 : x / x₀ = y / x₀ := by rw [← hfval x hx, ← hfval y hy, hxy]
        exact mul_right_cancel₀ hx₀ne ((div_eq_div_iff hx₀ne hx₀ne).mp h1)
      let g : ↥({x : F | x ^ m = a} : Set F) → ↥K := fun x => ⟨f x.1, hmap x.1 x.2⟩
      have hginj : Function.Injective g := by
        intro x y hxy
        have h1 : f x.1 = f y.1 := Subtype.ext_iff.mp hxy
        have h2 : x.1 = y.1 := hinj x.2 y.2 h1
        exact Subtype.ext h2
      have hle : ({x : F | x ^ m = a} : Set F).ncard ≤ Nat.card ↥K := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective g hginj
      exact le_trans hle hKgcd

/-- The monomial case of the general-`e` Stepanov count: if `g = c·X^D` with `c ≠ 0` and no prime
`p ∣ e` divides `D`, then `#{x : g x ^ ((q-1)/e) = 1} ≤ (q-1)/e`. -/
theorem ncard_gpow_eq_one_monomial {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (hdiv : e ∣ Fintype.card F - 1) (c : F) (hc : c ≠ 0) (D : ℕ) (hD : 1 ≤ D)
    (hgcd : ∀ p, p.Prime → p ∣ e → ¬ p ∣ D) :
    (({x : F | (Polynomial.C c * Polynomial.X ^ D).eval x ^ ((Fintype.card F - 1) / e) = 1}
        : Set F).ncard) ≤ (Fintype.card F - 1) / e := by
  classical
  set k := (Fintype.card F - 1) / e with hk
  have hq : 0 < Fintype.card F - 1 := by
    have h := Fintype.one_lt_card (α := F); omega
  have hkpos : 0 < k := by
    rw [hk]
    exact Nat.div_pos (Nat.le_of_dvd hq hdiv) (by omega)
  have hek : e * k = Fintype.card F - 1 := by
    rw [hk]
    exact Nat.mul_div_cancel' hdiv
  have hcop : Nat.Coprime D e := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact hgcd p hp (dvd_trans hpd (Nat.gcd_dvd_right D e))
      (dvd_trans hpd (Nat.gcd_dvd_left D e))
  have hset : ({x : F | (Polynomial.C c * Polynomial.X ^ D).eval x ^ k = 1} : Set F)
      ⊆ {x : F | x ^ (D * k) = (c ^ k)⁻¹} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hx
    have h2 : c ^ k * x ^ (D * k) = 1 := by
      rw [mul_pow, ← pow_mul] at hx
      exact hx
    exact eq_inv_of_mul_eq_one_right h2
  have h1 : ({x : F | (Polynomial.C c * Polynomial.X ^ D).eval x ^ k = 1} : Set F).ncard
      ≤ ({x : F | x ^ (D * k) = (c ^ k)⁻¹} : Set F).ncard := Set.ncard_le_ncard hset
  have h2 : ({x : F | x ^ (D * k) = (c ^ k)⁻¹} : Set F).ncard
      ≤ Nat.gcd (D * k) (Fintype.card F - 1) :=
        ncard_pow_eq_le_gcd (D * k) (Nat.mul_pos hD hkpos) _
  have h3 : Nat.gcd (D * k) (Fintype.card F - 1) = k := by
    rw [← hek, Nat.gcd_mul_right, hcop, one_mul]
  rw [h3] at h2
  exact le_trans h1 h2


end

end Commons.NumberTheory.Stepanov

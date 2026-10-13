/-
Area DSCOH — an independent proof of the finiteness of the chart Čech cohomology of the shifts
`S(-d) = shift d` of the polynomial ring, in the two surviving degrees `0` and `n - 1`.

**Why this file exists.**  The natural home of these two statements is a sibling file; the planned
proof there imports both `Work.DSCOH.resAt_divPow_toLoc` (public) and
`Work.DSCOH.top_cechDiff_eq_laurent_gen`, which declares a *private* lemma of the same user name
`Work.DSCOH.resAt_divPow_toLoc`.  The two modules therefore cannot be imported together, and any
module importing both fails with `environment already contains 'Work.DSCOH.resAt_divPow_toLoc'`.

This file breaks that dependency: the whole `H⁰`-side of the argument — the restriction formula for
explicit fractions and the vanishing `ker (cechDiff … 0) = ⊥` for `d ≥ 1` — is reproduced here under
fresh names inside the namespace `Work.DSCOH.SFI`, so that no module of this file's import graph
mentions the publicly clashing name at all.  The `H^{n-1}`-side then only needs
`Work.DSCOH.top_cechDiff_eq_laurent_gen`, `Work.DSCOH.exists_sum_laurent` and
`Work.DSCOH.finite_beta_set`.

The public output is `Work.DSCOH.SFI.chartCech_shift_finite_indep`.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.ShiftToolkit
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.cechDiff_apply_coe
import Submission.Work.DSCOH.negOne_pow_card_filter_erase
import Submission.Work.DSCOH.mvpoly_X_pow_mul_left_cancel
import Submission.Work.DSCOH.mvpoly_X_pow_mul_eq_dvd
import Submission.Work.DSCOH.isHomogeneous_eq_zero_of_X_pow_dvd
import Submission.Work.DSCOH.degZero_exists_repr
import Submission.Work.DSCOH.top_cechDiff_eq_laurent_gen
import Submission.Work.DSCOH.exists_sum_laurent
import Submission.Work.DSCOH.finite_beta_set
import Submission.Work.DSCOH.ker_cechDiff_zero_finite_dzero
import Submission.Work.DSCOH.chartCech_shift_finite_le_one
import Submission.Work.DSCOH.homology_zero_finite
import Submission.Work.DSCOH.homology_top_finite
import Submission.Work.DSCOH.resAt_eq_of_cechDiff_zero

open MvPolynomial CategoryTheory

namespace Work.DSCOH.SFI

/-! ## The restriction formula for explicit fractions -/

section ResAt

variable {A : Type*} [CommRing A] {n : ℕ}
  {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]

/-- The structure map `resAt h` on the localization sends `toLoc S m` to `toLoc T m`: both are the
class of `m` with denominator `1`. -/
private lemma resAt_toLoc_aux {S T : Finset (Fin n)} (h : S ⊆ T) (m : M) :
    resAt (A := A) (M := M) h (toLoc (A := A) (M := M) S m) = toLoc (A := A) (M := M) T m :=
  IsLocalizedModule.liftOfLE_apply (S₁ := subS (A := A) S) (S₂ := subS (A := A) T)
    (h := subS_mono (A := A) h)
    (f₁ := LocalizedModule.mkLinearMap (subS (A := A) S) M)
    (f₂ := LocalizedModule.mkLinearMap (subS (A := A) T) M) m

/-- `toLoc` is `Poly A n`-linear. -/
private lemma toLoc_smul_aux (S : Finset (Fin n)) (p : Poly A n) (m : M) :
    toLoc (A := A) (M := M) S (p • m) = p • toLoc (A := A) (M := M) S m :=
  LinearMap.map_smul (LocalizedModule.mkLinearMap (subS (A := A) S) M) p m

/-- Multiplying back by `(X_S)^k` recovers the original element. -/
private lemma divPow_mul_smul_aux (S : Finset (Fin n)) (k : ℕ) (x : locAt (A := A) (M := M) S) :
    divPow (A := A) (M := M) S k ((monomial (A := A) S ^ k) • x) = x := by
  rw [divPow]
  exact LocalizedModule.divBy_mul_by
    ⟨monomial (A := A) S ^ k, Submonoid.pow_mem (subS (A := A) S) (monomial_mem S) k⟩ x

private lemma smul_divPow_aux (S : Finset (Fin n)) (k : ℕ) (x : locAt (A := A) (M := M) S) :
    (monomial (A := A) S ^ k) • divPow (A := A) (M := M) S k x = x := by
  rw [divPow]
  exact LocalizedModule.mul_by_divBy
    ⟨monomial (A := A) S ^ k, Submonoid.pow_mem (subS (A := A) S) (monomial_mem S) k⟩ x

/-- The monomial over `T` splits as the product of the monomials over `S` and over `T \ S`. -/
private lemma monomial_sdiff_pow_aux {S T : Finset (Fin n)} (h : S ⊆ T) (k : ℕ) :
    monomial (A := A) T ^ k =
      monomial (A := A) S ^ k * monomial (A := A) (T \ S) ^ k := by
  have hmono : monomial (A := A) T = monomial (A := A) S * monomial (A := A) (T \ S) := by
    simp only [monomial]
    rw [← Finset.prod_sdiff h, mul_comm]
  rw [hmono, mul_pow]

/-- **The structure map on explicit fractions.**  `resAt h` multiplies the numerator by
`X_{T \ S}^k`, the product of the variables inverted when passing from `S` to `T`. -/
private theorem resAt_divPow_toLocI
    {S T : Finset (Fin n)} (h : S ⊆ T) (k : ℕ) (m : M) :
    resAt (A := A) (M := M) h (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      divPow (A := A) (M := M) T k
        (toLoc (A := A) (M := M) T ((monomial (A := A) (T \ S)) ^ k • m)) := by
  have hpow := monomial_sdiff_pow_aux (A := A) h k
  have hL : (monomial (A := A) T ^ k) •
        resAt (A := A) (M := M) h (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      (monomial (A := A) (T \ S) ^ k) • toLoc (A := A) (M := M) T m := by
    rw [hpow, mul_comm (monomial (A := A) S ^ k) (monomial (A := A) (T \ S) ^ k), mul_smul]
    rw [← LinearMap.map_smul, smul_divPow_aux, resAt_toLoc_aux]
  have hR : (monomial (A := A) T ^ k) •
        divPow (A := A) (M := M) T k
          (toLoc (A := A) (M := M) T ((monomial (A := A) (T \ S)) ^ k • m)) =
      (monomial (A := A) (T \ S) ^ k) • toLoc (A := A) (M := M) T m := by
    rw [smul_divPow_aux, toLoc_smul_aux]
  have hkey := hL.trans hR.symm
  have := congrArg (divPow (A := A) (M := M) T k) hkey
  simpa only [divPow_mul_smul_aux] using this

end ResAt

/-! ## Vanishing of `H⁰` of the shift complex -/

section KerZero

variable {A : Type*} [CommRing A] {n : ℕ}

/-- Every element of the submonoid `subS S` is a nonzerodivisor of `A[X₀,…,X_{n-1}]`. -/
private lemma subS_isLeftRegular (S : Finset (Fin n)) :
    ∀ c ∈ subS (A := A) S, IsLeftRegular c := by
  intro c hc
  refine Submonoid.closure_induction (motive := fun c _ => IsLeftRegular c) ?_ ?_ ?_ hc
  · rintro _ ⟨i, -, rfl⟩
    exact (MvPolynomial.isRegular_X (R := A) (n := i)).left
  · intro a b hab
    simpa using hab
  · intro x y _ _ hx hy
    exact hx.mul hy

private lemma monomial_singleton (i : Fin n) :
    monomial (A := A) ({i} : Finset (Fin n)) = (MvPolynomial.X i : Poly A n) := by
  simp [monomial, Var]

private lemma monomial_pair {i j : Fin n} (hij : i ≠ j) :
    monomial (A := A) ({i, j} : Finset (Fin n)) =
      (MvPolynomial.X i : Poly A n) * MvPolynomial.X j := by
  rw [monomial]
  simp only [Var]
  exact Finset.prod_pair hij

private lemma sdiff_singleton_right {i j : Fin n} (hij : i ≠ j) :
    ({i, j} : Finset (Fin n)) \ {j} = {i} := by
  rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne hij]
  simp

private lemma sdiff_singleton_left {i j : Fin n} (hij : i ≠ j) :
    ({i, j} : Finset (Fin n)) \ {i} = {j} := by
  rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert (by simpa using hij)]

/-- **The cross relation.**  If the images of the fractions `pj / X_j^{kj}` and `pi / X_i^{ki}`
agree in the chart `X_i X_j`, then `X_i^{ki} · pj = X_j^{kj} · pi`. -/
private lemma cross_relation {i j : Fin n} (hij : i ≠ j) {ki kj : ℕ} {pi pj : Poly A n}
    (h : resAt (A := A) (M := Poly A n) (S := {j}) (T := {i, j}) (by simp)
          (divPow (A := A) (M := Poly A n) ({j} : Finset (Fin n)) kj
            (toLoc (A := A) (M := Poly A n) ({j} : Finset (Fin n)) pj))
        = resAt (A := A) (M := Poly A n) (S := {i}) (T := {i, j}) (by simp)
          (divPow (A := A) (M := Poly A n) ({i} : Finset (Fin n)) ki
            (toLoc (A := A) (M := Poly A n) ({i} : Finset (Fin n)) pi))) :
    (MvPolynomial.X i : Poly A n) ^ ki * pj = (MvPolynomial.X j : Poly A n) ^ kj * pi := by
  have h1 := resAt_divPow_toLocI (A := A) (S := {j}) (T := {i, j}) (by simp) kj pj
  have h2 := resAt_divPow_toLocI (A := A) (S := {i}) (T := {i, j}) (by simp) ki pi
  rw [h1, h2] at h
  rw [sdiff_singleton_right hij, sdiff_singleton_left hij, monomial_singleton i,
    monomial_singleton j] at h
  simp only [smul_eq_mul] at h
  rw [divPow_toLoc_eq_mk, divPow_toLoc_eq_mk] at h
  rw [LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  simp only [Submonoid.smul_def, smul_eq_mul, den_coe] at hu
  have h3 := (subS_isLeftRegular ({i, j} : Finset (Fin n)) (u : Poly A n) u.2) hu
  rw [monomial_pair hij, mul_pow, mul_pow] at h3
  have hreg : IsLeftRegular
      ((MvPolynomial.X i : Poly A n) ^ kj * (MvPolynomial.X j : Poly A n) ^ ki) :=
    (MvPolynomial.isRegular_X_pow (R := A) (n := i) kj).left.mul
      (MvPolynomial.isRegular_X_pow (R := A) (n := j) ki).left
  refine hreg ?_
  linear_combination (norm := ring_nf) h3

/-- **`H⁰` of the shift complex vanishes for `d ≥ 1`**: the differential `cechDiff … 0` is
injective on the degree-zero part of the Čech complex of `S(-d)`. -/
private theorem ker_cechDiff_zero_eq_zeroI {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] (hn : 2 ≤ n) (hd : 1 ≤ d)
    (c : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0)
    (hc : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0 c = 0)
    (j : Fin n) :
    c ⟨{j}, Finset.card_singleton j⟩ = 0 := by
  obtain ⟨i, hij⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := Fin n) (by rw [Fintype.card_fin]; omega) j
  obtain ⟨kj, pj, hpj, hcj⟩ :=
    degZero_exists_repr (ℳ := shift (A := A) (n := n) d) ({j} : Finset (Fin n))
      (c ⟨{j}, Finset.card_singleton j⟩).2
  obtain ⟨ki, pi, hpi, hci⟩ :=
    degZero_exists_repr (ℳ := shift (A := A) (n := n) d) ({i} : Finset (Fin n))
      (c ⟨{i}, Finset.card_singleton i⟩).2
  rw [Finset.card_singleton, Nat.mul_one] at hpj hpi
  have hrel := resAt_eq_of_cechDiff_zero (A := A) (n := n) d (i := i) (j := j) hij c hc
  rw [hcj, hci] at hrel
  have hstar := cross_relation (i := i) (j := j) hij hrel
  have hdiv : (MvPolynomial.X j : Poly A n) ^ kj ∣ pj := mvpoly_X_pow_mul_eq_dvd hij hstar
  have hpj0 : pj = 0 := by
    by_cases hdk : d ≤ kj
    · refine isHomogeneous_eq_zero_of_X_pow_dvd (i := j) (m := pj) (e := kj - d) (k := kj)
        ?_ (by omega) hdiv
      rwa [shift_of_le hdk] at hpj
    · rwa [shift_of_not_le hdk, Submodule.mem_bot] at hpj
  exact Subtype.ext (by rw [hcj, hpj0]; simp)

end KerZero

/-! ## The chart Čech complex of a shift -/

variable {A : Type*} [CommRing A] {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- The Čech differential of the chart Čech complex is the linear map out of which the complex is
built. -/
lemma chartCech_d (d : ℕ) [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (q : ℕ) :
    (chartCech (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)).d q (q + 1) =
      ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) q) := by
  simp only [chartCech, chartCechOf]
  exact CochainComplex.of_d _ _ _

/-- The chart Čech differential in provably consecutive degrees. -/
lemma chartCech_d_of (d : ℕ) [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    {i j : ℕ} (h : i + 1 = j) :
    (chartCech (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)).d i j =
      ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) i) ≫
        eqToHom (congrArg (fun q => ModuleCat.of A (CechTerm (A := A) (n := n) (M := Poly A n)
          (shift (A := A) (n := n) d) q)) h) := by
  subst h
  simp only [chartCech, chartCechOf]
  rw [CochainComplex.of_d]
  simp

/-- The target of the chart Čech differential in degree `q ≥ n` is the product over an empty index
type. -/
lemma cechTerm_subsingleton {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M] (ℳ : ℕ → Submodule A M) {q : ℕ} (h : n ≤ q) :
    Subsingleton (CechTerm (A := A) (n := n) (M := M) ℳ q) := by
  haveI : IsEmpty {S : Finset (Fin n) // S.card = q + 1} := ⟨fun S => by
    have h1 : S.1.card ≤ n := by simpa using Finset.card_le_univ S.1
    omega⟩
  exact ⟨fun f g => funext fun S => isEmptyElim S⟩

/-- The top-degree differential of the chart Čech complex vanishes. -/
lemma chartCech_d_top_zero (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] :
    (chartCech (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)).d (n - 1)
      ((n - 1) + 1) = 0 := by
  rw [chartCech_d]
  haveI : Subsingleton (CechTerm (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d) ((n - 1) + 1)) := cechTerm_subsingleton _ (by omega)
  have h0 : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (n - 1) = 0 := by
    refine LinearMap.ext fun x => ?_
    exact Subsingleton.elim _ _
  rw [h0]
  exact ModuleCat.ofHom_zero

/-- The kernel finiteness of the chart Čech differential in degree zero, for `n ≥ 2`. -/
lemma ker_cechDiff_zero_finite (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] (hn : 2 ≤ n) :
    Module.Finite A (LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d) 0)) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    letI := shift_gradedSMul (A := A) (n := n) 0
    exact ker_cechDiff_zero_finite_dzero (A := A) (n := n) hn
  · have hbot : LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) 0) = ⊥ := by
      refine Submodule.eq_bot_iff _ |>.mpr fun c hc => ?_
      funext S
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp S.2
      have hS : S = ⟨{j}, Finset.card_singleton j⟩ := Subtype.ext hj
      rw [hS]
      exact ker_cechDiff_zero_eq_zeroI (A := A) (n := n) d hn hd c hc j
    rw [hbot]
    exact Module.Finite.iff_fg.mpr Submodule.fg_bot

/-! ## The "top element" of `CechTerm (q+1)` -/

/-- The "top element" of `CechTerm (q+1)`: the cochain that assigns `v` to every chart (all of
which are `univ`). -/
noncomputable def topEl (d : ℕ) {q : ℕ} (hq : q + 1 + 1 = n)
    (v : degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
      (Finset.univ : Finset (Fin n))) :
    CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1) :=
  fun S => (Finset.eq_univ_of_card S.1 (by rw [S.2, Fintype.card_fin]; omega)).symm ▸ v

lemma eq_transport_self {P : Finset (Fin n) → Type*}
    (h : (Finset.univ : Finset (Fin n)) = Finset.univ) (v : P Finset.univ) :
    (show P Finset.univ from h.symm ▸ v) = v := by
  cases h
  rfl

lemma topEl_univ (d : ℕ) {q : ℕ} (hq : q + 1 + 1 = n)
    (v : degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
      (Finset.univ : Finset (Fin n)))
    (hcard : (Finset.univ : Finset (Fin n)).card = (q + 1) + 1) :
    topEl (A := A) (n := n) d hq v ⟨Finset.univ, hcard⟩ = v := by
  show (show _ from (Finset.eq_univ_of_card (Finset.univ : Finset (Fin n))
    (by rw [Finset.card_univ, Fintype.card_fin])).symm ▸ v) = v
  dsimp only

/-- Two cochains in `CechTerm (q+1)` agree as soon as they agree at the (unique) top chart. -/
lemma cechTerm_ext_univ (d : ℕ) {q : ℕ} (hq : q + 1 + 1 = n)
    {x y : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1)}
    {hcard : (Finset.univ : Finset (Fin n)).card = (q + 1) + 1}
    (h : x ⟨Finset.univ, hcard⟩ = y ⟨Finset.univ, hcard⟩) : x = y := by
  funext S
  have hS : S = ⟨Finset.univ, hcard⟩ := Subtype.ext
    (Finset.eq_univ_of_card S.1 (by rw [S.2, Fintype.card_fin]; omega))
  subst hS
  exact h

/-- **The top quotient is generated by the negative Laurent monomials.** -/
lemma span_range_topEl_laurent (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    {q : ℕ} (hq : q + 1 + 1 = n) (hn : 2 ≤ n) :
    Submodule.span A (Set.range (fun β : Fin n → ℤ =>
      if h : (∀ i, β i ≤ -1) ∧ (∑ i, β i) = -(d : ℤ) then
        Submodule.mkQ (LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n)
          (shift (A := A) (n := n) d) q))
          (topEl (A := A) (n := n) d hq
            ⟨laurent (A := A) (n := n) β, laurent_mem_degZero (A := A) (n := n) h.2⟩)
      else 0)) = ⊤ := by
  classical
  have hcard : (Finset.univ : Finset (Fin n)).card = q + 1 + 1 := by
    rw [Finset.card_univ, Fintype.card_fin, ← hq]
  let ψ : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q →ₗ[A]
      degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
        (Finset.univ : Finset (Fin n)) :=
    (LinearMap.proj (R := A) (φ := fun S : {S : Finset (Fin n) // S.card = q + 1 + 1} =>
        degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) S.1)
      ⟨Finset.univ, hcard⟩).comp
      (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
  let Y : Type _ := CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1)
  let p : Submodule A Y := LinearMap.range
    (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
  let f : (Fin n → ℤ) → Y ⧸ p := fun β =>
    if h : (∀ i, β i ≤ -1) ∧ (∑ i, β i) = -(d : ℤ) then
      Submodule.mkQ p (topEl (A := A) (n := n) d hq
        ⟨laurent (A := A) (n := n) β, laurent_mem_degZero (A := A) (n := n) h.2⟩)
    else 0
  rw [Submodule.eq_top_iff']
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective p y
  rw [← hx, ← Submodule.mkQ_apply]
  obtain ⟨F, c, hFsum, hFx⟩ := exists_sum_laurent (A := A) (n := n) d
    (z := (x ⟨Finset.univ, hcard⟩).1) (x ⟨Finset.univ, hcard⟩).2
  set F₁ : Finset (Fin n → ℤ) := F.filter (fun β => ∀ i, β i ≤ -1) with hF₁
  have hspan : ∀ γ ∈ F₁, (∑ i, γ i) = -(d : ℤ) := fun γ hγ =>
    hFsum γ (Finset.mem_filter.mp hγ).1
  let w : Y := ∑ γ : F₁, c γ.1 • topEl (A := A) (n := n) d hq
    ⟨laurent (A := A) (n := n) γ.1, laurent_mem_degZero (A := A) (n := n) (hspan γ.1 γ.2)⟩
  set F₂ : Finset (Fin n → ℤ) := F.filter (fun β => ¬ ∀ i, β i ≤ -1) with hF₂
  have hw1 : (x - w) ⟨Finset.univ, hcard⟩ =
      ∑ γ : ↥F₂, c γ.1 • (⟨laurent (A := A) (n := n) γ.1,
        laurent_mem_degZero (A := A) (n := n)
          (hFsum γ.1 (Finset.mem_filter.mp γ.2).1)⟩ :
        degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
          (Finset.univ : Finset (Fin n))) := by
    refine Subtype.ext ?_
    have hw2 : (w ⟨Finset.univ, hcard⟩).1 =
        ∑ γ : F₁, c γ.1 • laurent (A := A) (n := n) γ.1 := by
      dsimp only [w]
      rw [Finset.sum_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Pi.smul_apply, Submodule.coe_smul, topEl_univ]
    rw [Pi.sub_apply, Submodule.coe_sub, hFx, hw2, Submodule.coe_sum]
    simp only [Submodule.coe_smul, Subtype.coe_mk]
    rw [← Finset.sum_subtype F₁ (fun x => by simp) (fun γ => c γ • laurent (A := A) (n := n) γ),
      ← Finset.sum_subtype F₂ (fun x => by simp) (fun γ => c γ • laurent (A := A) (n := n) γ)]
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun β => ∀ i, β i ≤ -1)
      (fun γ => c γ • laurent (A := A) (n := n) γ)
    rw [← hF₁, ← hF₂] at hsplit
    rw [← hsplit]
    abel
  have hmem : (x - w) ⟨Finset.univ, hcard⟩ ∈ LinearMap.range ψ := by
    have hsum : (∑ γ : ↥F₂, c γ.1 • (⟨laurent (A := A) (n := n) γ.1,
        laurent_mem_degZero (A := A) (n := n)
          (hFsum γ.1 (Finset.mem_filter.mp γ.2).1)⟩ :
        degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
          (Finset.univ : Finset (Fin n)))) ∈ LinearMap.range ψ := by
      refine Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ (c γ.1) ?_
      have hγF : γ.1 ∈ F := (Finset.mem_filter.mp γ.2).1
      have hnotP : ¬ (∀ i, γ.1 i ≤ -1) := (Finset.mem_filter.mp γ.2).2
      obtain ⟨i, hi⟩ := not_forall.mp hnotP
      obtain ⟨u, hu⟩ := top_cechDiff_eq_laurent_gen (A := A) (n := n) d hn
        (hFsum γ.1 hγF) ⟨i, by omega⟩ hcard
      exact ⟨u, by
        dsimp only [ψ]
        rw [LinearMap.comp_apply, LinearMap.proj_apply]
        exact hu⟩
    rwa [← hw1] at hsum
  have hxp : x - w ∈ p := by
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_⟩
    dsimp only [ψ] at hu
    rw [LinearMap.comp_apply, LinearMap.proj_apply] at hu
    exact cechTerm_ext_univ (A := A) (n := n) d hq hu
  have hxw : Submodule.mkQ p x = Submodule.mkQ p w := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hxp
  rw [hxw]
  have hwit : Submodule.mkQ p w = ∑ γ : F₁, c γ.1 • f γ.1 := by
    dsimp only [w, f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_smul]
    congr 1
    rw [dite_eq_left (⟨(Finset.mem_filter.mp γ.2).2, hspan γ.1 γ.2⟩ :
      (∀ i, γ.1 i ≤ -1) ∧ (∑ i, γ.1 i) = -(d : ℤ))]
  rw [hwit]
  exact Submodule.sum_mem _ fun γ _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ.1, rfl⟩)

/-- **The top quotient of the chart Čech complex is finitely generated.** -/
lemma coker_cechDiff_top_finite (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    {q : ℕ} (hq : q + 1 + 1 = n) (hn : 2 ≤ n) :
    Module.Finite A (CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1) ⧸
      LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) q)) := by
  classical
  let Z := CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1) ⧸
      LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
  let S : Set (Fin n → ℤ) := {β | (∀ i, β i ≤ -1) ∧ (∑ i, β i) = -(d : ℤ)}
  let f : (Fin n → ℤ) → Z := fun β =>
    if h : (∀ i, β i ≤ -1) ∧ (∑ i, β i) = -(d : ℤ) then
      Submodule.mkQ (LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) q))
        (topEl (A := A) (n := n) d hq
          ⟨laurent (A := A) (n := n) β, laurent_mem_degZero (A := A) (n := n) h.2⟩)
    else 0
  have hSfin : S.Finite := finite_beta_set
  have hfin : (Set.range f).Finite := by
    apply Set.Finite.subset (hSfin.image f |>.union (Set.finite_singleton (0 : Z)))
    rintro _ ⟨β, rfl⟩
    by_cases h : β ∈ S
    · exact Or.inl ⟨β, h, rfl⟩
    · refine Or.inr ?_
      have hP : ¬ ((∀ i, β i ≤ -1) ∧ (∑ i, β i) = -(d : ℤ)) := fun hP => h hP
      dsimp only [f]
      rw [dite_eq_right hP]
      simp
  have hspan : Submodule.span A (Set.range f) = ⊤ :=
    span_range_topEl_laurent (A := A) (n := n) d hq hn
  have htop := Module.Finite.span_of_finite A hfin
  rw [hspan] at htop
  haveI : Module.Finite A ↥(⊤ : Submodule A Z) := htop
  exact Module.Finite.equiv (Submodule.topEquiv)

/-! ## Finiteness of the two surviving cohomology groups -/

/-- The quotient of the top term of the chart Čech complex by the image of the top differential is
finitely generated over `A`. -/
lemma top_quotient_finite (d : ℕ) [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (hn : 2 ≤ n) :
    Module.Finite A (↥((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).X (n - 1)) ⧸
      LinearMap.range ((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d)).d ((n - 1) - 1) (n - 1)).hom) := by
  set k := (n - 1) - 1 with hk
  have hm : k + 1 = n - 1 := by omega
  rw [← hm]
  rw [chartCech_d]
  exact coker_cechDiff_top_finite (A := A) (n := n) d (q := k) (by omega) hn

/-- Finiteness of the chart Čech cohomology in degree zero. -/
lemma homology_zero_finite_of (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] (hn : 2 ≤ n) :
    Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology 0) := by
  refine homology_zero_finite _ ?_
  have h1 : (chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).d 0 1 = ModuleCat.ofHom
      (cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) 0) :=
    chartCech_d (A := A) (n := n) d 0
  rw [h1]
  exact ker_cechDiff_zero_finite (A := A) (n := n) d hn

/-- Finiteness of the chart Čech cohomology in the top degree. -/
lemma homology_top_finite_of (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] (hn : 2 ≤ n) :
    Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
      (shift (A := A) (n := n) d)).homology (n - 1)) :=
  homology_top_finite _ (by omega) (chartCech_d_top_zero (A := A) (n := n) d)
    (top_quotient_finite (A := A) (n := n) d hn)

/-- **Finiteness of the chart Čech cohomology of a shift in the two surviving degrees.** -/
theorem chartCech_shift_finite_indep {A : Type*} [CommRing A] {n : ℕ} (d : ℕ)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] :
    Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d)).homology 0) ∧
      Module.Finite A ((chartCech (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d)).homology (n - 1)) := by
  by_cases hn : n ≤ 1
  · exact chartCech_shift_finite_le_one (A := A) (n := n) d hn
  · have hn2 : 2 ≤ n := by omega
    exact ⟨homology_zero_finite_of (A := A) (n := n) d hn2,
      homology_top_finite_of (A := A) (n := n) d hn2⟩

end Work.DSCOH.SFI

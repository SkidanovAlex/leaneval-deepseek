import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Self-contained port of `Submission.Work.BW.taylorC_acf_expand` (`Work.BW.taylorC_acf_expand`).
The auxiliary development of `Submission.Work.BW.taylorC_aux` (together with the two
lemmas `iteratedDeriv_fAt` and `ellM_eq_sum_derVec` it depends on) is inlined below in the
fresh namespace `Work.BW.TC`, so that this module imports `DefsAC` only and can be imported
alongside `Submission.Work.BW.est21_l_vanish_n`. -/

namespace Work.BW.TC

/-- The operator `D_ℓ = ∂/∂Y₀ + Σᵢ ℓᵢ Yᵢ ∂/∂Yᵢ` of the BW §17 chain rule, as a plain function. -/
private noncomputable def idfD {r : ℕ} (ℓ : Fin r → ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ → MvPolynomial (Fin (r + 1)) ℂ :=
  fun Q => MvPolynomial.pderiv 0 Q +
    ∑ i : Fin r, MvPolynomial.C (ℓ i) * MvPolynomial.X i.succ * MvPolynomial.pderiv i.succ Q

/-- The same operator bundled as a `Derivation`, which gives the Leibniz rule for free. -/
private noncomputable def idfDd {r : ℕ} (ℓ : Fin r → ℂ) :
    Derivation ℂ (MvPolynomial (Fin (r + 1)) ℂ) (MvPolynomial (Fin (r + 1)) ℂ) :=
  MvPolynomial.pderiv 0 +
    ∑ i : Fin r, (MvPolynomial.C (ℓ i) * MvPolynomial.X i.succ) • MvPolynomial.pderiv i.succ

private lemma idfDd_apply {r : ℕ} (ℓ : Fin r → ℂ) (Q : MvPolynomial (Fin (r + 1)) ℂ) :
    idfDd ℓ Q = idfD ℓ Q := by
  simp [idfDd, idfD, smul_eq_mul]

/-- The chain rule on the curve: `deriv (z ↦ P(z, e^{zℓ})) = (D_ℓ P)(z, e^{zℓ})`. -/
private lemma hasDerivAt_fAt {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (z : ℂ) :
    HasDerivAt (fAt ℓ P) (fAt ℓ (idfD ℓ P) z) z := by
  have hX : ∀ n : Fin (r + 1),
      HasDerivAt (fAt ℓ (MvPolynomial.X n)) (fAt ℓ (idfD ℓ (MvPolynomial.X n)) z) z := by
    intro n
    refine Fin.cases ?h0 ?hs n
    · have hD : fAt ℓ (idfD ℓ (MvPolynomial.X 0)) z = 1 := by
        simp [idfD, fAt, MvPolynomial.pderiv_X, Fin.succ_ne_zero]
      rw [hD]
      have hfun : fAt ℓ (MvPolynomial.X 0) = fun w => w := by
        funext w; simp [fAt, ptC, Fin.cons_zero]
      rw [hfun]
      exact hasDerivAt_id z
    · intro i
      have hp : idfD ℓ (MvPolynomial.X i.succ) = MvPolynomial.C (ℓ i) * MvPolynomial.X i.succ := by
        simp only [idfD]
        rw [MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero i)]
        rw [zero_add, Finset.sum_eq_single i]
        · rw [MvPolynomial.pderiv_X_self]; simp
        · intro j _ hj
          rw [MvPolynomial.pderiv_X_of_ne (fun h => hj (Fin.succ_inj.mp h).symm)]
          simp
        · intro h; exact absurd (Finset.mem_univ i) h
      have hD : fAt ℓ (idfD ℓ (MvPolynomial.X i.succ)) z = ℓ i * Complex.exp (z * ℓ i) := by
        rw [hp]
        simp [fAt, ptC, MvPolynomial.eval_mul, Fin.cons_succ]
      rw [hD]
      have hfun : fAt ℓ (MvPolynomial.X i.succ) = fun w => Complex.exp (w * ℓ i) := by
        funext w; simp [fAt, ptC, Fin.cons_succ]
      rw [hfun]
      have hg : HasDerivAt (fun w : ℂ => w * ℓ i) (ℓ i) z := by
        simpa using (hasDerivAt_id z).mul_const (ℓ i)
      have hthis : HasDerivAt (fun w : ℂ => Complex.exp (w * ℓ i))
          (Complex.exp (z * ℓ i) * ℓ i) z :=
        (Complex.hasDerivAt_exp (z * ℓ i)).comp z hg
      convert hthis using 1
      ring
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hD : idfD ℓ (MvPolynomial.C a) = 0 := by
      simp only [← idfDd_apply]
      simp [idfDd]
    have hfun : fAt ℓ (MvPolynomial.C a) = fun _ => a := by
      funext w; simp [fAt]
    rw [hfun, hD]
    simpa [fAt] using hasDerivAt_const z a
  | add p q hp hq =>
    have hfun : fAt ℓ (p + q) = fAt ℓ p + fAt ℓ q := by
      funext w; simp [fAt]
    rw [hfun]
    have hD : idfD ℓ (p + q) = idfD ℓ p + idfD ℓ q := by
      simp only [← idfDd_apply, map_add]
    rw [hD]
    have hval : fAt ℓ (idfD ℓ p + idfD ℓ q) z = fAt ℓ (idfD ℓ p) z + fAt ℓ (idfD ℓ q) z := by
      simp [fAt]
    rw [hval]
    exact hp.add hq
  | mul_X p n hp =>
    have hfun : fAt ℓ (p * MvPolynomial.X n) = fAt ℓ p * fAt ℓ (MvPolynomial.X n) := by
      funext w; simp [fAt, MvPolynomial.eval_mul]
    rw [hfun]
    have hpoly : idfD ℓ (p * MvPolynomial.X n) =
        p * idfD ℓ (MvPolynomial.X n) + MvPolynomial.X n * idfD ℓ p := by
      simp only [← idfDd_apply, Derivation.leibniz, smul_eq_mul]
    rw [hpoly]
    have hval : fAt ℓ (p * idfD ℓ (MvPolynomial.X n) + MvPolynomial.X n * idfD ℓ p) z =
        fAt ℓ (idfD ℓ p) z * fAt ℓ (MvPolynomial.X n) z +
          fAt ℓ p z * fAt ℓ (idfD ℓ (MvPolynomial.X n)) z := by
      simp only [fAt, map_add, map_mul]
      ring
    rw [hval]
    exact hp.mul (hX n)


/-- Chain rule on the curve (BW §17 first display): `(d/dz)^m P(z, e^{zℓ}) = (D_ℓ^m P)(z, e^{zℓ})` with `D_ℓ = ∂/∂Y₀ + Σ ℓ_i Y_i ∂/∂Y_i`. -/
theorem iteratedDeriv_fAt {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) (m : ℕ)
    (z : ℂ) :
    iteratedDeriv m (fAt ℓ P) z =
      fAt ℓ ((fun Q => MvPolynomial.pderiv 0 Q + ∑ i : Fin r, MvPolynomial.C (ℓ i) *
          MvPolynomial.X i.succ * MvPolynomial.pderiv i.succ Q)^[m] P) z := by
  have key : ∀ P : MvPolynomial (Fin (r + 1)) ℂ,
      iteratedDeriv m (fAt ℓ P) = fAt ℓ ((idfD ℓ)^[m] P) := by
    intro P
    induction m with
    | zero => simp [iteratedDeriv_zero]
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext w
      rw [Function.iterate_succ_apply']
      exact (hasDerivAt_fAt ℓ ((idfD ℓ)^[m] P) w).deriv
  exact congrFun (key P) z

/-- BW §17: `M_j = Σ_i (2^{-v} log α_i / b_k)·(b_k ∂L_j/∂z_i − b_i ∂L_j/∂z_k)`, i.e. `D_{ellM} = ∂₀ + Σ_i a_i ∂*_i` with `a_i = 2^{-v} log α_i / b_k` (BW's `a(t')`). -/
theorem ellM_eq_sum_derVec {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (v : ℕ) (L : Fin r → Fin n → ℤ) (hbk : b k ≠ 0) (j : Fin r) :
    ellM φ α b k v L j = ∑ i : Fin n, ((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ) *
      ((derVec b k L i j : ℤ) : ℂ) := by
  -- `ellM j = lamP j − (L_{jk}/b_k)·2^{-v}·Λ` and `derVec b k L i j = b_k L_{ji} − b_i L_{jk}`,
  -- so the right-hand side equals `2^{-v}∑_i L_{ji} log α_i − (L_{jk}/b_k)2^{-v}∑_i b_i log α_i`.
  simp only [ellM, lamP, lam, derVec]
  have hB : (b k : ℂ) ≠ 0 := by exact_mod_cast hbk
  have key : ∀ i : Fin n,
      ((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ) * ((b k * L j i - b i * L j k : ℤ) : ℂ)
      = ((2 : ℂ) ^ v)⁻¹ * (((L j i : ℂ) * Complex.log (φ (α i)))
          - ((b i : ℂ) * Complex.log (φ (α i))) * ((L j k : ℂ) / (b k : ℂ))) := by
    intro i; push_cast; field_simp; try ring
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  -- distribute `2^{-v}` over the difference and pull the constants out of the sums
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  field_simp
  try ring

open MvPolynomial

noncomputable section

variable {r : ℕ}

/-- `ℂ[Y₀,…,Y_r]`. -/
abbrev Acy (r : ℕ) := MvPolynomial (Fin (r + 1)) ℂ

/-! ### Multiplication and the elementary operators -/

/-- Multiplication by `p`, as a `ℂ`-linear endomorphism of `ℂ[Y₀,…,Y_r]`. -/
def mulEnd (p : Acy r) : Module.End ℂ (Acy r) := p • 1

@[simp] lemma mulEnd_apply (p Q : Acy r) : mulEnd p Q = p * Q := by
  simp [mulEnd, smul_eq_mul]

lemma mulEnd_add (p q : Acy r) : mulEnd (p + q) = mulEnd p + mulEnd q := by
  apply LinearMap.ext
  intro Q
  rw [mulEnd_apply, LinearMap.add_apply, mulEnd_apply, mulEnd_apply, add_mul]

lemma mulEnd_mul (p q : Acy r) : mulEnd (p * q) = mulEnd p * mulEnd q := by
  apply LinearMap.ext
  intro Q
  rw [mulEnd_apply, Module.End.mul_apply, mulEnd_apply, mulEnd_apply, mul_assoc]

lemma mulEnd_smul (s : ℂ) (p : Acy r) : mulEnd (s • p) = s • mulEnd p := by
  apply LinearMap.ext
  intro Q
  rw [mulEnd_apply, LinearMap.smul_apply, mulEnd_apply, smul_mul_assoc]

lemma mulEnd_sum {ι : Type*} (s : Finset ι) (f : ι → Acy r) :
    mulEnd (∑ i ∈ s, f i) = ∑ i ∈ s, mulEnd (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [mulEnd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mulEnd_add, ih]

/-- `∂/∂Y₀` as an endomorphism. -/
def d0 : Module.End ℂ (Acy r) := (MvPolynomial.pderiv (0 : Fin (r + 1))).toLinearMap

lemma d0_apply (Q : Acy r) : d0 Q = MvPolynomial.pderiv 0 Q := rfl

/-- The Euler derivation `Σ_j c_j Y_{j+1} ∂_{j+1}`. -/
def eulerD (c : Fin r → ℂ) : Derivation ℂ (Acy r) (Acy r) :=
  ∑ j : Fin r, (MvPolynomial.C (c j) * MvPolynomial.X j.succ) • MvPolynomial.pderiv j.succ

/-- `eulerD` as an endomorphism. -/
def eulerEnd (c : Fin r → ℂ) : Module.End ℂ (Acy r) := (eulerD c).toLinearMap

/-! ### Rewriting lemmas for sums of derivations / endomorphisms -/

lemma Derivation_sum_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation ℂ (Acy r) (Acy r)) (Q : Acy r) :
    (∑ i ∈ s, D i) Q = ∑ i ∈ s, D i Q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

lemma End_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ (Acy r)) (Q : Acy r) :
    (∑ i ∈ s, f i) Q = ∑ i ∈ s, f i Q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih]

/-! ### The operators on generators and in expanded form -/

lemma eulerD_X_zero (c : Fin r → ℂ) : eulerD c (MvPolynomial.X (0 : Fin (r + 1))) = 0 := by
  rw [eulerD, Derivation_sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Derivation.smul_apply, MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero j).symm, smul_zero]

lemma eulerD_X_succ (c : Fin r → ℂ) (j : Fin r) :
    eulerD c (MvPolynomial.X j.succ) = MvPolynomial.C (c j) * MvPolynomial.X j.succ := by
  rw [eulerD, Derivation_sum_apply, Finset.sum_eq_single j]
  · simp [Derivation.smul_apply]
  · intro m _ hm
    have hne : j.succ ≠ m.succ := fun h => hm (Fin.succ_inj.mp h).symm
    have hz : (MvPolynomial.pderiv m.succ (MvPolynomial.X j.succ) : Acy r) = 0 :=
      MvPolynomial.pderiv_X_of_ne hne
    rw [Derivation.smul_apply, hz, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma eulerEnd_apply (c : Fin r → ℂ) (Q : Acy r) :
    eulerEnd c Q =
      ∑ j : Fin r, MvPolynomial.C (c j) * MvPolynomial.X j.succ * MvPolynomial.pderiv j.succ Q := by
  show (eulerD c) Q = _
  rw [eulerD, Derivation_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.smul_apply]
  rfl

lemma eulerEnd_expand (c : Fin r → ℂ) :
    eulerEnd c = ∑ j : Fin r,
      mulEnd (MvPolynomial.C (c j) * MvPolynomial.X j.succ) *
        (MvPolynomial.pderiv j.succ).toLinearMap := by
  apply LinearMap.ext
  intro Q
  rw [eulerEnd_apply, End_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.End.mul_apply, mulEnd_apply]
  rfl

/-- The chain-rule operator `D_ℓ = ∂₀ + Σ_j ℓ_j Y_{j+1} ∂_{j+1}` of `iteratedDeriv_fAt`. -/
def idfEnd (ℓ : Fin r → ℂ) : Module.End ℂ (Acy r) := d0 + eulerEnd ℓ

lemma idfEnd_apply (ℓ : Fin r → ℂ) (Q : Acy r) :
    idfEnd ℓ Q = MvPolynomial.pderiv 0 Q +
      ∑ j : Fin r, MvPolynomial.C (ℓ j) * MvPolynomial.X j.succ * MvPolynomial.pderiv j.succ Q := by
  rw [idfEnd, LinearMap.add_apply, d0_apply, eulerEnd_apply]

/-- `fAt` is `ℂ`-linear in the polynomial. -/
lemma fAt_smul (ℓ : Fin r → ℂ) (c : ℂ) (Q : Acy r) (z : ℂ) :
    fAt ℓ (c • Q) z = c * fAt ℓ Q z := by
  show MvPolynomial.eval (ptC ℓ z) (c • Q) = c * MvPolynomial.eval (ptC ℓ z) Q
  rw [show c • Q = MvPolynomial.C c * Q from by
        rw [Algebra.smul_def, ← MvPolynomial.C_eq_algebraMap]]
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]

/-- `fAt` is additive in the polynomial. -/
lemma fAt_add (ℓ : Fin r → ℂ) (Q Q' : Acy r) (z : ℂ) :
    fAt ℓ (Q + Q') z = fAt ℓ Q z + fAt ℓ Q' z :=
  map_add (MvPolynomial.eval (ptC ℓ z)) Q Q'

/-- `fAt` of a sum is the sum of the `fAt`s. -/
lemma fAt_sum {ι : Type*} (ℓ : Fin r → ℂ) (s : Finset ι) (g : ι → Acy r) (z : ℂ) :
    fAt ℓ (∑ i ∈ s, g i) z = ∑ i ∈ s, fAt ℓ (g i) z :=
  map_sum (MvPolynomial.eval (ptC ℓ z)) g s

/-- The chain rule of BW §17: `(d/dz)^m P(z, e^{zℓ}) = (D_ℓ^m P)(z, e^{zℓ})`. -/
lemma iteratedDeriv_acf (ℓ : Fin r → ℂ) (P : Acy r) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (fAt ℓ P) z = fAt ℓ (((idfEnd ℓ) ^ m) P) z := by
  rw [iteratedDeriv_fAt]
  have hfun : (fun Q : Acy r => MvPolynomial.pderiv 0 Q +
        ∑ i : Fin r, MvPolynomial.C (ℓ i) * MvPolynomial.X i.succ * MvPolynomial.pderiv i.succ Q)
      = ⇑(idfEnd ℓ) := by
    funext Q; rw [idfEnd_apply]
  rw [hfun, ← Module.End.coe_pow]

/-! ### Commutation of the operators -/

/-- Derivations that commute on the generators commute everywhere. -/
lemma Derivation.commute_of_commute_X {D E : Derivation ℂ (Acy r) (Acy r)}
    (h : ∀ i : Fin (r + 1), D (E (MvPolynomial.X i)) = E (D (MvPolynomial.X i))) :
    ∀ Q : Acy r, D (E Q) = E (D Q) := by
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      have hD : ∀ a b : Acy r, D (a * b) = a * D b + b * D a := fun a b => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      have hE : ∀ a b : Acy r, E (a * b) = a * E b + b * E a := fun a b => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      simp only [hE, hD, map_add]
      rw [h i, hp]
      ring

lemma commute_deriv {D E : Derivation ℂ (Acy r) (Acy r)}
    (h : ∀ i : Fin (r + 1), D (E (MvPolynomial.X i)) = E (D (MvPolynomial.X i))) :
    Commute (D.toLinearMap) (E.toLinearMap) := by
  rw [Commute]
  apply LinearMap.ext
  intro Q
  rw [Module.End.mul_apply, Module.End.mul_apply]
  exact Derivation.commute_of_commute_X h Q

lemma commute_pderiv (i j : Fin (r + 1)) :
    Commute ((MvPolynomial.pderiv i : Derivation ℂ (Acy r) (Acy r)).toLinearMap)
      ((MvPolynomial.pderiv j : Derivation ℂ (Acy r) (Acy r)).toLinearMap) := by
  refine commute_deriv fun k => ?_
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne k j with rfl | hkj
    · simp
    · rw [MvPolynomial.pderiv_X_of_ne hkj]
      simp
  · rcases eq_or_ne k j with rfl | hkj
    · rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne hki]
      simp
    · rw [MvPolynomial.pderiv_X_of_ne hkj, MvPolynomial.pderiv_X_of_ne hki]
      simp

lemma commute_d0_euler (c : Fin r → ℂ) : Commute d0 (eulerEnd c) := by
  show Commute ((MvPolynomial.pderiv (0 : Fin (r + 1)) : Derivation ℂ (Acy r) (Acy r)).toLinearMap)
    ((eulerD c).toLinearMap)
  refine commute_deriv fun k => ?_
  induction k using Fin.cases with
  | zero => simp [eulerD_X_zero]
  | succ m =>
      rw [eulerD_X_succ, MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero m)]
      simp

/-- `D (C a * f) = C a * D f`. -/
lemma Derivation.map_C_mul {D : Derivation ℂ (Acy r) (Acy r)} (a : ℂ) (f : Acy r) :
    D (MvPolynomial.C a * f) = MvPolynomial.C a * D f := by
  rw [Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero]
  rfl

lemma commute_euler (c c' : Fin r → ℂ) : Commute (eulerEnd c) (eulerEnd c') := by
  show Commute ((eulerD c).toLinearMap) ((eulerD c').toLinearMap)
  refine commute_deriv fun k => ?_
  induction k using Fin.cases with
  | zero => simp [eulerD_X_zero]
  | succ m =>
      rw [eulerD_X_succ, eulerD_X_succ, Derivation.map_C_mul, Derivation.map_C_mul,
        eulerD_X_succ, eulerD_X_succ]
      ring

/-! ### The family `(∂₀, E_1, …, E_n)` -/

/-- The operator family `(∂₀, E_1, …, E_n)`, with `E_i` the Euler operator with coefficients `c i`. -/
def Afam {n : ℕ} (c : Fin n → Fin r → ℚ) : Fin (n + 1) → Module.End ℂ (Acy r) :=
  Fin.cases d0 (fun i : Fin n => eulerEnd (fun j : Fin r => (c i j : ℂ)))

lemma Afam_zero {n : ℕ} (c : Fin n → Fin r → ℚ) : Afam (r := r) c 0 = d0 := by
  rw [Afam, Fin.cases_zero]

lemma Afam_succ {n : ℕ} (c : Fin n → Fin r → ℚ) (i : Fin n) :
    Afam (r := r) c i.succ = eulerEnd (fun j : Fin r => (c i j : ℂ)) := by
  rw [Afam, Fin.cases_succ]

/-- The coefficient family `(1, a_1, …, a_n)`. -/
def bfam {n : ℕ} (a : Fin n → ℂ) : Fin (n + 1) → ℂ := Fin.cases 1 a

lemma bfam_zero {n : ℕ} (a : Fin n → ℂ) : bfam a 0 = 1 := by
  rw [bfam, Fin.cases_zero]

lemma bfam_succ {n : ℕ} (a : Fin n → ℂ) (i : Fin n) : bfam a i.succ = a i := by
  rw [bfam, Fin.cases_succ]

lemma commute_Afam {n : ℕ} (c : Fin n → Fin r → ℚ) :
    ∀ i j : Fin (n + 1), Commute (Afam (r := r) c i) (Afam (r := r) c j) := by
  intro i j
  induction i using Fin.cases with
  | zero =>
      rw [Afam_zero]
      induction j using Fin.cases with
      | zero => exact Commute.refl _
      | succ m => rw [Afam_succ]; exact commute_d0_euler _
  | succ i' =>
      rw [Afam_succ]
      induction j using Fin.cases with
      | zero => rw [Afam_zero]; exact (commute_d0_euler _).symm
      | succ m => rw [Afam_succ]; exact commute_euler _ _

/-! ### Products over `List.finRange` -/

/-- The (ordered) product `f 0 * f 1 * ⋯ * f (q-1)`. -/
def prodEnd {q : ℕ} (f : Fin q → Module.End ℂ (Acy r)) : Module.End ℂ (Acy r) :=
  ((List.finRange q).map f).prod

lemma list_prod_apply {α : Type*} (l : List α) (f : α → Module.End ℂ (Acy r)) (P : Acy r) :
    ((l.map f).prod) P = l.foldr (fun a Q => f a Q) P := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply, ih]

/-- `Finset.noncommProd` over `univ : Finset (Fin q)` is the product over `List.finRange q`. -/
lemma noncommProd_univ_eq {M : Type*} [Monoid M] {q : ℕ} (g : Fin q → M)
    (comm : (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)).Pairwise
      (fun x y => Commute (g x) (g y))) :
    Finset.univ.noncommProd g comm = ((List.finRange q).map g).prod := by
  calc Finset.univ.noncommProd g comm
      = (List.finRange q).toFinset.noncommProd g _ :=
        Finset.noncommProd_congr (List.toFinset_finRange q).symm (fun x _ => rfl) comm
    _ = ((List.finRange q).map g).prod :=
        Finset.noncommProd_toFinset (List.finRange q) g _ (List.nodup_finRange q)

/-- `∏ i, f i` over `Fin q` is the ordered product over `List.finRange q`. -/
lemma prod_finRange_eq {M : Type*} [CommMonoid M] {q : ℕ} (f : Fin q → M) :
    ((List.finRange q).map f).prod = ∏ i, f i := by
  rw [← List.prod_toFinset f (List.nodup_finRange q), List.toFinset_finRange]

/-! ### `applyDer` as a product of the operators -/

lemma eulerEnd_apply_eulerDer {n : ℕ} (c : Fin n → Fin r → ℚ) (i : Fin n) (Q : Acy r) :
    eulerEnd (fun j : Fin r => (c i j : ℂ)) Q = eulerDer (c i) Q := by
  rw [eulerEnd_apply]
  rfl

lemma foldr_Afam {n : ℕ} (c : Fin n → Fin r → ℚ) (k : Fin (n + 1) → ℕ) (l : List (Fin n)) :
    ∀ Q : Acy r,
      l.foldr (fun i Q => ((Afam (r := r) c i.succ) ^ (k i.succ)) Q) Q
        = l.foldr (fun i Q => ((eulerDer (c i)) ^[k i.succ]) Q) Q := by
  induction l with
  | nil => intro Q; rfl
  | cons a l ih =>
      intro Q
      rw [List.foldr_cons, List.foldr_cons, ih]
      have hfun : (⇑(eulerEnd (fun j : Fin r => (c a j : ℂ))) : Acy r → Acy r) = eulerDer (c a) :=
        funext (eulerEnd_apply_eulerDer c a)
      rw [Afam_succ, Module.End.coe_pow, hfun]

lemma prodEnd_Afam_apply {n : ℕ} (c : Fin n → Fin r → ℚ) (k : Fin (n + 1) → ℕ) (P : Acy r) :
    ((List.finRange (n + 1)).map (fun j => (Afam (r := r) c j) ^ (k j))).prod P
      = applyDer (fun i j => c i j) (k 0) (Fin.tail k) P := by
  change prodEnd (fun j : Fin (n + 1) => (Afam (r := r) c j) ^ (k j)) P = _
  have hd0 : ⇑(d0 : Module.End ℂ (Acy r)) = ⇑(MvPolynomial.pderiv (0 : Fin (r + 1))) :=
    funext d0_apply
  simp only [applyDer, Fin.tail]
  rw [prodEnd, List.finRange_succ, List.map_cons, List.prod_cons, Module.End.mul_apply,
    list_prod_apply, List.foldr_map, Afam_zero, foldr_Afam, Module.End.coe_pow, hd0]

/-! ### `D = ∂₀ + Σ_i a_i E_i` -/

lemma sum_smul_C_mul {n : ℕ} (a : Fin n → ℂ) (d : Fin n → ℂ) (j : Fin r) :
    (∑ i : Fin n, a i • (MvPolynomial.C (d i) * MvPolynomial.X j.succ))
      = MvPolynomial.C (∑ i, a i * d i) * MvPolynomial.X j.succ := by
  trans ∑ i : Fin n, (a i • MvPolynomial.C (d i)) * MvPolynomial.X j.succ
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact (smul_mul_assoc (a i) (MvPolynomial.C (d i)) (MvPolynomial.X j.succ)).symm
  · rw [← Finset.sum_mul]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, ← MvPolynomial.C_eq_algebraMap, ← MvPolynomial.C_mul]

lemma idfEnd_eq_sum {n : ℕ} (a : Fin n → ℂ) (c : Fin n → Fin r → ℂ) (ℓ : Fin r → ℂ)
    (h : ∀ j, ℓ j = ∑ i, a i * c i j) :
    idfEnd ℓ = d0 + ∑ i : Fin n, a i • eulerEnd (c i) := by
  have hℓ : ℓ = fun j => ∑ i, a i * c i j := funext h
  rw [hℓ, idfEnd]
  congr 1
  rw [eulerEnd_expand (fun j => ∑ i, a i * c i j)]
  have h2 : ∀ i : Fin n, a i • eulerEnd (c i) =
      ∑ j : Fin r, mulEnd (a i • (MvPolynomial.C (c i j) * MvPolynomial.X j.succ)) *
        (MvPolynomial.pderiv j.succ).toLinearMap := by
    intro i
    rw [eulerEnd_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_mul_assoc, mulEnd_smul]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, ← mulEnd_sum, sum_smul_C_mul]

/-! ### The multinomial expansion (scalar-free form) -/

lemma natCast_eq_smul_one {R M : Type*} [CommSemiring R] [Semiring M] [Algebra R M] (n : ℕ) :
    (n : M) = (n : R) • (1 : M) := by
  rw [Algebra.smul_def, mul_one, map_natCast]

lemma list_prod_smul {R M : Type*} [CommSemiring R] [Semiring M] [Algebra R M] {α : Type*}
    (l : List α) (c : α → R) (g : α → M) :
    (l.map (fun i => c i • g i)).prod = (l.map c).prod • (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
        List.prod_cons, ih, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The multinomial theorem in the shape needed for BW §17. -/
theorem op_multinomial {R M : Type*} [Field R] [CharZero R] [Semiring M] [Algebra R M]
    {q : ℕ} (A : Fin q → M) (m : ℕ) (hcomm : ∀ i j, Commute (A i) (A j)) :
    ((m.factorial : R)⁻¹) • (∑ i : Fin q, A i) ^ m =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin q)) m,
        ((∏ i, ((k i).factorial : R))⁻¹) •
          ((List.finRange q).map (fun i => (A i) ^ (k i))).prod := by
  rw [Finset.sum_pow_eq_sum_piAntidiag_of_commute (Finset.univ : Finset (Fin q)) A
    (fun i _ j _ _ => hcomm i j) m, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hksum, -⟩ := Finset.mem_piAntidiag.mp hk
  rw [show (↑(Nat.multinomial (Finset.univ : Finset (Fin q)) k) : M)
        = (↑(Nat.multinomial (Finset.univ : Finset (Fin q)) k) : R) • (1 : M)
      from natCast_eq_smul_one _]
  rw [smul_mul_assoc, one_mul, noncommProd_univ_eq, smul_smul]
  congr 1
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin q)) k
  rw [hksum] at hspec
  have hM : (∏ i, ((k i).factorial : R)) *
      (Nat.multinomial (Finset.univ : Finset (Fin q)) k : R) = (m.factorial : R) := by
    exact_mod_cast hspec
  have hA : (∏ i : Fin q, ((k i).factorial : R)) ≠ 0 := by
    rw [← Nat.cast_prod]
    exact Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
  have hm : (m.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have h1 : (∏ i : Fin q, ((k i).factorial : R)) *
      ((m.factorial : R)⁻¹ * (Nat.multinomial (Finset.univ : Finset (Fin q)) k : R)) = 1 := by
    rw [← mul_assoc, mul_comm (∏ i : Fin q, ((k i).factorial : R)) ((m.factorial : R)⁻¹),
      mul_assoc, hM, inv_mul_cancel₀ hm]
  exact mul_left_cancel₀ hA (h1.trans (mul_inv_cancel₀ hA).symm)

/-! ### Reindexing the multinomial sum -/

/-- The sum over `piAntidiag (univ : Finset (Fin (n+1))) m` is the same as the sum over
`(a, t) : Fin (m+1) × (Fin n → Fin (m+1))` with `a + Σ_i t_i = m`, via `Fin.cases`. -/
theorem piAntidiag_sum_fin {M : Type*} [AddCommMonoid M] (m n : ℕ)
    (F : (Fin (n + 1) → ℕ) → M) :
    ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) m, F k =
      ∑ at' ∈ (Finset.univ.filter (fun at' : Fin (m + 1) × (Fin n → Fin (m + 1)) =>
          (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) = m)),
        F (fun j => Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) j) := by
  classical
  refine Finset.sum_bij'
    (fun (g : Fin (n + 1) → ℕ) hg =>
      (⟨g 0, Nat.lt_succ_of_le (by
          calc g 0 ≤ ∑ j : Fin (n + 1), g j :=
                Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ 0)
            _ = m := (Finset.mem_piAntidiag.mp hg).1)⟩,
       fun i => ⟨g i.succ, Nat.lt_succ_of_le (by
          calc g i.succ ≤ ∑ j : Fin (n + 1), g j :=
                Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i.succ)
            _ = m := (Finset.mem_piAntidiag.mp hg).1)⟩))
    (fun (at' : Fin (m + 1) × (Fin n → Fin (m + 1))) _ =>
      fun j => Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) j)
    ?_ ?_ ?_ ?_ ?_
  · -- `i` lands in the filtered set
    intro g hg
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show g 0 + ∑ i : Fin n, g i.succ = m
    rw [← Fin.sum_univ_succ]
    exact (Finset.mem_piAntidiag.mp hg).1
  · -- `j` lands in `piAntidiag`
    intro at' hat'
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    exact (Finset.mem_filter.mp hat').2
  · -- `j ∘ i = id`
    intro g hg
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ i => rfl
  · -- `i ∘ j = id`
    intro at' hat'
    apply Prod.ext
    · apply Fin.ext
      show (Fin.cases (↑at'.1) (fun i => ↑(at'.2 i)) 0 : ℕ) = ↑at'.1
      exact Fin.cases_zero
    · funext i
      apply Fin.ext
      show (Fin.cases (↑at'.1) (fun i => ↑(at'.2 i)) i.succ : ℕ) = ↑(at'.2 i)
      exact Fin.cases_succ i
  · -- the two functions agree
    intro g hg
    congr 1
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ i => rfl

end

end Work.BW.TC

namespace Work.BW

open Work.BW.TC

/-- BW (1993) p. 48, first display: the multinomial expansion of the `m`-th Taylor coefficient of
`f` along the curve: `taylorC (acf … t0 t) m z` is the sum over all pairs `(a, t') : ℕ × (Fin n → ℕ)`
with `a + Σᵢ t'_i = m` of `(1/a!)∏ᵢ(a_i^{t'_i}/t'_i!)·fAt (ellM …) (∂₀^a ∏ᵢ (∂*_i)^{t'_i}
Q^{(J)}(·;t0,t)) z`, where `a_i = 2^{-v} log φ(α_i)/b_k` are the coefficients of
`ellM_eq_sum_derVec` and `∂*_i = eulerDer (derVec b k L i ·)`.  Identical statement to
`Submission.Work.BW.taylorC_acf_expand`, restated so that the module does **not** import
`Submission.Work.BW.taylorC_aux`: that module and `Submission.Work.BW.est21_l_vanish_n` both declare
`Work.BW.fAt_sum`, so a module importing both fails to build, and the live `est21_l` assembly needs
the estimate `est21_dpoly_diff_bound`, whose closure contains `est21_l_vanish_n`.  Port
`taylorC_acf_expand.lean` verbatim, inlining under fresh names exactly the `taylorC_aux` results it
uses (`fAt_sum`, `fAt_smul`, `iteratedDeriv_acf`, `idfEnd_eq_sum`, `Afam`, `bfam`,
`prodEnd_Afam_apply`, `op_multinomial`, `piAntdiag_sum_fin`); the module must import `DefsAC` only.

-/
theorem taylorC_acf_expand_clean {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (m : ℕ)
    (z : ℂ) :
    taylorC (acf φ α b k L ι v σ p J μ t0 t) m z =
      ∑ at' ∈ (Finset.univ.filter
          (fun at' : Fin (m + 1) × (Fin n → Fin (m + 1)) =>
            (at'.1 : ℕ) + ∑ i, (at'.2 i : ℕ) = m)),
        ((((at'.1 : ℕ).factorial : ℂ))⁻¹ *
          ∏ i, (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (at'.2 i : ℕ) /
            (((at'.2 i : ℕ).factorial : ℂ))) *
        fAt (ellM φ α b k v L)
          (applyDer (fun i j => (derVec b k L i j : ℚ)) (at'.1 : ℕ) (fun i => (at'.2 i : ℕ))
            (QJ φ b k L ι v σ p J μ t0 t)) z:= by
  classical
  set ℓ : Fin r → ℂ := ellM φ α b k v L with hℓ
  set P : Acy r := QJ φ b k L ι v σ p J μ t0 t with hP
  set a : Fin n → ℂ := fun i => ((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ) with ha
  set cc : Fin n → Fin r → ℚ := fun i j => derVec b k L i j with hcc
  have ha' : ∀ i : Fin n, a i = ((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ) := fun i => rfl
  have hcc' : ∀ (i : Fin n) (j : Fin r), cc i j = (derVec b k L i j : ℚ) := fun i j => rfl
  have hbk : b k ≠ 0 := H.hst.2.2.2.2.1
  have hellM : ∀ j : Fin r, ℓ j = ∑ i : Fin n, a i * (cc i j : ℂ) := by
    intro j
    show (ellM φ α b k v L) j = ∑ i : Fin n,
      ((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ) * ((derVec b k L i j : ℚ) : ℂ)
    rw [ellM_eq_sum_derVec φ α b k v L hbk j]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hD : idfEnd ℓ = ∑ j : Fin (n + 1), bfam a j • Afam cc j := by
    rw [Fin.sum_univ_succ, bfam_zero, Afam_zero, one_smul]
    rw [show (∑ i : Fin n, bfam a i.succ • Afam cc i.succ)
        = ∑ i : Fin n, a i • eulerEnd (fun j : Fin r => (cc i j : ℂ)) from
      Finset.sum_congr rfl fun i _ => by rw [bfam_succ, Afam_succ]]
    exact idfEnd_eq_sum a (fun i j => (cc i j : ℂ)) ℓ hellM
  have hmult := op_multinomial (R := ℂ) (fun j : Fin (n + 1) => bfam a j • Afam cc j) m
    (fun i j => ((commute_Afam cc i j).smul_left (bfam a i : ℂ)).smul_right (bfam a j : ℂ))
  have hprod : ∀ k : Fin (n + 1) → ℕ,
      ((List.finRange (n + 1)).map (fun j => (bfam a j • Afam cc j) ^ (k j))).prod
        = (∏ j : Fin (n + 1), (bfam a j) ^ (k j)) •
          ((List.finRange (n + 1)).map (fun j => (Afam cc j) ^ (k j))).prod := by
    intro k
    have h1 : ∀ j : Fin (n + 1), (bfam a j • Afam cc j) ^ (k j)
        = (bfam a j) ^ (k j) • (Afam cc j) ^ (k j) := by
      intro j
      rw [Algebra.smul_def,
        Commute.mul_pow (Algebra.commute_algebraMap_left (bfam a j) (Afam cc j)),
        ← map_pow, ← Algebra.smul_def]
    have h2 : ((List.finRange (n + 1)).map (fun j => (bfam a j • Afam cc j) ^ (k j))).prod
        = ((List.finRange (n + 1)).map
            (fun j => (bfam a j) ^ (k j) • (Afam cc j) ^ (k j))).prod := by
      simp only [h1]
    rw [h2, list_prod_smul, prod_finRange_eq]
  have hstep1 : taylorC (acf φ α b k L ι v σ p J μ t0 t) m z
      = fAt ℓ ((((m.factorial : ℂ))⁻¹) • (((idfEnd ℓ) ^ m) P)) z := by
    show iteratedDeriv m (fAt ℓ P) z / ((m.factorial : ℂ)) = _
    rw [iteratedDeriv_acf, fAt_smul, div_eq_mul_inv, mul_comm]
  have key : fAt ℓ ((((m.factorial : ℂ))⁻¹) • (((idfEnd ℓ) ^ m) P)) z
      = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) m,
          (((∏ j, ((k j).factorial : ℂ))⁻¹) * ∏ j, (bfam a j) ^ (k j)) *
            fAt ℓ (applyDer (fun i j => cc i j) (k 0) (Fin.tail k) P) z := by
    rw [← LinearMap.smul_apply, hD, hmult, End_sum_apply]
    simp only [LinearMap.smul_apply]
    rw [fAt_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fAt_smul, hprod k, LinearMap.smul_apply, fAt_smul, prodEnd_Afam_apply]
    ring
  rw [hstep1, key]
  rw [piAntidiag_sum_fin m n]
  refine Finset.sum_congr rfl fun at' hat' => ?_
  have hcoef : (∏ j : Fin (n + 1),
        ((((Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) :
            Fin (n + 1) → ℕ) j)).factorial : ℂ))
      = (((at'.1 : ℕ).factorial : ℂ)) * ∏ i : Fin n, (((at'.2 i : ℕ)).factorial : ℂ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
  have hbf : (∏ j : Fin (n + 1),
        (bfam a j) ^ (((Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) :
            Fin (n + 1) → ℕ) j)))
      = ∏ i : Fin n,
          (((2 : ℂ) ^ v)⁻¹ * Complex.log (φ (α i)) / (b k : ℂ)) ^ (at'.2 i : ℕ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, bfam_zero, bfam_succ, one_pow, one_mul, ha']
  have hop : applyDer (fun i j => cc i j)
        ((Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) : Fin (n + 1) → ℕ) 0)
        (Fin.tail (Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) : Fin (n + 1) → ℕ)) P
      = applyDer (fun i j => (derVec b k L i j : ℚ)) (at'.1 : ℕ) (fun i => (at'.2 i : ℕ))
          (QJ φ b k L ι v σ p J μ t0 t) := by
    have htail : Fin.tail (fun i : Fin (n + 1) =>
          (Fin.cases (at'.1 : ℕ) (fun i => (at'.2 i : ℕ)) i : ℕ))
        = fun i : Fin n => (at'.2 i : ℕ) := by
      funext i
      simp only [Fin.tail, Fin.cases_succ]
    simp only [Fin.cases_zero, htail, hcc', hP]
  rw [hcoef, hbf, hop, hℓ]
  rw [Finset.prod_div_distrib, div_eq_mul_inv, mul_inv_rev]
  ring

end Work.BW

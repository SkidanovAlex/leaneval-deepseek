/-
# A linear map killing the odd-weight defect ideal `𝓘_odd` and reading off six coordinates

`𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`, `z = -I`, is the defect ideal of CKMRV at **odd**
weight (`Work.Asymptotics.idealIOdd`).  This file proves that the six classes of
`MpElem i = single (Mp i) 1`, `Mp = (1, T⁻¹, STS, S, ST⁻¹, TS)`, are linearly independent
modulo `𝓘_odd`, in the equivalent form

  `∃ Λ : R →ₗ[ℂ] (Fin 6 → ℂ), Λ (𝓘_odd) = 0 ∧ LinearIndependent ℂ (Λ ∘ MpElem)`,

which is what the odd-weight propagation argument of `exists_extension_of_propagates_odd`
needs.  Since `spMp_all_mem` already shows that the six classes span `R ⧸ 𝓘_odd`, it suffices
to produce a surjection `R ⧸ 𝓘_odd ↠ ℂ⁶`; the map constructed below is in fact an
isomorphism.

## The construction

`R = ℂ[SL(2,ℤ)]` splits as `R = R₊ ⊕ R₋` through the central idempotents
`e_± = 2⁻¹(1 ± z)` (`eMinus`), and `eMinus R` is canonically the algebra in which the
difference operator `T - 1` becomes the **shifted** operator `T - i`; the corresponding
algebra `RR = ℂ[ℤ/2 ∗ ℤ/3]` is related to `eMinus R` by the algebra homomorphism `psiM`
(`Work.Asymptotics.psiM`, injective with `psiM (Tnu i) = i • ((R_T - 1) e₋)`).

The heart of the proof is the six-dimensional representation

* `sigmaOddX = sigmaS`,
* `sigmaOddT = !![0,1,0,0,0,0; 1,2i,0,0,0,0; -2i,0,0,0,0,1; 0,0,0,0,1,0; 0,0,0,1,2i,0;
   0,0,1,-2i,0,0]`

of the free product (the right action of `X`, `T` on the six-dimensional quotient by
`(T-i)²` and `X(T-i)²` in the basis `1, T, TX, X, XT, XTX`), for which

* `row 0` of `(sigmaOddT - i)²` and of `sigmaOddX (sigmaOddT - i)²` vanishes
  (`row0_sq_apply`, `row0_X_sq_apply`), and
* the first rows of `σ (1), σ (T), σ (TX), σ (X), σ (XT), σ (XTX)` are the six standard
  basis vectors (`sigmaOddAlg_W6_zero` … `sigmaOddAlg_W6_five`).

Pulling `(row 0) ∘ σ` back along `psiM⁻¹ ∘ (· e₋)` gives `LamOdd : R →ₗ ℂ⁶`
(`LamOdd_augIdealOdd`, `LamOdd_IdealI` show that it kills the two summands of `𝓘_odd`),
and `LamOdd (M6R i)` is a non-zero multiple of the `i`-th standard basis vector, so the
induced map `LamBar : R ⧸ 𝓘_odd → ℂ⁶` is surjective.  Combined with the spanning statement
(`Phi_surjective` from `exists_sigma_odd`), this gives `finrank ℂ (R ⧸ 𝓘_odd) = 6`; hence
`Phi` and `LamBar` are injective, the six classes of `MpElem` are linearly independent, and
so are their images under `LamOdd`.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.psiOdd
import Submission.Work.Asymptotics.oddDirect_of_shiftedDirect
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.Asymptotics.mem_idealIOdd_exists
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.Modular.GroupAlgebra
import Submission.Work.Residues.Basic

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues (M6)
open Work.FreeProduct (RR X Y TT Tnu)

/-! ## The shifted representation `σ` at `ν = i` -/

/-- `σ(X)` for the shifted (`ν = i`) representation: the permutation matrix `sigmaS`. -/
def sigmaOddX : Matrix (Fin 6) (Fin 6) ℂ := Work.Modular.sigmaS

/-- `σ(T)` for the shifted (`ν = i`) representation. -/
def sigmaOddT : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 1, 0, 0, 0, 0;
     1, 2 * Complex.I, 0, 0, 0, 0;
     -2 * Complex.I, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 2 * Complex.I, 0;
     0, 0, 1, -2 * Complex.I, 0, 0]

lemma sigmaOddX_mul_self : sigmaOddX * sigmaOddX = 1 := by
  rw [sigmaOddX, Work.Modular.sigmaS_mul_self]

lemma sigmaOddXT_cube : (sigmaOddX * sigmaOddT) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, sigmaOddX, sigmaOddT, Work.Modular.sigmaS, Fin.sum_univ_six,
      pow_succ]

lemma sigmaOddT_row0 : sigmaOddT 0 = Pi.single 1 (1 : ℂ) := by
  ext j; fin_cases j <;> simp [sigmaOddT]

lemma sigmaOddT_row1 : sigmaOddT 1 = Pi.single 0 (1 : ℂ) + (2 * Complex.I) • Pi.single 1 1 := by
  ext j; fin_cases j <;> simp [sigmaOddT]

lemma sigmaOddT_row3 : sigmaOddT 3 = Pi.single 4 (1 : ℂ) := by
  ext j; fin_cases j <;> simp [sigmaOddT]

lemma sigmaOddT_row4 : sigmaOddT 4 = Pi.single 3 (1 : ℂ) + (2 * Complex.I) • Pi.single 4 1 := by
  ext j; fin_cases j <;> simp [sigmaOddT]

lemma sigmaOddX_row0 : sigmaOddX 0 = Pi.single 3 (1 : ℂ) := by
  ext j; fin_cases j <;> simp [sigmaOddX, Work.Modular.sigmaS]

lemma sigmaOddX_row1 : sigmaOddX 1 = Pi.single 2 (1 : ℂ) := by
  ext j; fin_cases j <;> simp [sigmaOddX, Work.Modular.sigmaS]

lemma sigmaOddX_row4 : sigmaOddX 4 = Pi.single 5 (1 : ℂ) := by
  ext j; fin_cases j <;> simp [sigmaOddX, Work.Modular.sigmaS]

/-! ## The algebra homomorphism `σ : ℂ[ℤ/2 ∗ ℤ/3] → M₆(ℂ)` -/

/-- The image of the generator of the `ℤ/2` factor. -/
def sigmaOddHomC2 : Work.Modular.PresGroup.C2 →* Matrix (Fin 6) (Fin 6) ℂ where
  toFun x := sigmaOddX ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    show sigmaOddX ^ (x * y).toAdd.val = sigmaOddX ^ x.toAdd.val * sigmaOddX ^ y.toAdd.val
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (show sigmaOddX ^ 2 = 1 from by
      rw [pow_two]; exact sigmaOddX_mul_self), pow_add]

/-- The image of the generator of the `ℤ/3` factor. -/
def sigmaOddHomC3 : Work.Modular.PresGroup.C3 →* Matrix (Fin 6) (Fin 6) ℂ where
  toFun x := (sigmaOddX * sigmaOddT) ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    show (sigmaOddX * sigmaOddT) ^ (x * y).toAdd.val
      = (sigmaOddX * sigmaOddT) ^ x.toAdd.val * (sigmaOddX * sigmaOddT) ^ y.toAdd.val
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ sigmaOddXT_cube, pow_add]

/-- `σ` on the generators of `ℤ/2 ∗ ℤ/3`. -/
def sigmaOddOf : (b : Bool) → Work.Modular.PresGroup.Cyc b →* Matrix (Fin 6) (Fin 6) ℂ
  | false => sigmaOddHomC2
  | true => sigmaOddHomC3

/-- The monoid homomorphism `σ : ℤ/2 ∗ ℤ/3 → M₆(ℂ)`. -/
def sigmaOddFP : Work.Modular.PresGroup.FP →* Matrix (Fin 6) (Fin 6) ℂ :=
  Monoid.CoprodI.lift sigmaOddOf

/-- The linear extension of `σ` to the group algebra `ℂ[ℤ/2 ∗ ℤ/3]`. -/
def sigmaOddAlg : RR →ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  MonoidAlgebra.lift ℂ (Matrix (Fin 6) (Fin 6) ℂ) Work.Modular.PresGroup.FP sigmaOddFP

lemma sigmaOddFP_x : sigmaOddFP Work.FreeProduct.x = sigmaOddX := by
  show sigmaOddFP (Monoid.CoprodI.of (i := false)
    (Multiplicative.ofAdd (1 : ZMod 2))) = sigmaOddX
  rw [sigmaOddFP, Monoid.CoprodI.lift_of]
  show sigmaOddX ^ (ZMod.val (1 : ZMod 2)) = sigmaOddX
  rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]

lemma sigmaOddFP_y : sigmaOddFP Work.FreeProduct.y = sigmaOddX * sigmaOddT := by
  show sigmaOddFP (Monoid.CoprodI.of (i := true)
    (Multiplicative.ofAdd (1 : ZMod 3))) = sigmaOddX * sigmaOddT
  rw [sigmaOddFP, Monoid.CoprodI.lift_of]
  show (sigmaOddX * sigmaOddT) ^ (ZMod.val (1 : ZMod 3)) = sigmaOddX * sigmaOddT
  rw [show ZMod.val (1 : ZMod 3) = 1 from rfl, pow_one]

lemma sigmaOddAlg_X : sigmaOddAlg X = sigmaOddX := by
  show MonoidAlgebra.lift ℂ (Matrix (Fin 6) (Fin 6) ℂ) Work.Modular.PresGroup.FP sigmaOddFP
    (MonoidAlgebra.of ℂ Work.Modular.PresGroup.FP Work.FreeProduct.x) = sigmaOddX
  rw [MonoidAlgebra.lift_of]
  exact sigmaOddFP_x

lemma sigmaOddAlg_Y : sigmaOddAlg Y = sigmaOddX * sigmaOddT := by
  show MonoidAlgebra.lift ℂ (Matrix (Fin 6) (Fin 6) ℂ) Work.Modular.PresGroup.FP sigmaOddFP
    (MonoidAlgebra.of ℂ Work.Modular.PresGroup.FP Work.FreeProduct.y) = sigmaOddX * sigmaOddT
  rw [MonoidAlgebra.lift_of]
  exact sigmaOddFP_y

lemma sigmaOddAlg_TT : sigmaOddAlg TT = sigmaOddT := by
  rw [show TT = X * Y from Work.FreeProduct.X_mul_Y.symm, map_mul, sigmaOddAlg_X,
    sigmaOddAlg_Y, ← mul_assoc, sigmaOddX_mul_self, one_mul]

lemma sigmaOddAlg_TnuI : sigmaOddAlg (Tnu Complex.I) = sigmaOddT - Complex.I • 1 := by
  rw [Work.FreeProduct.Tnu, map_sub, map_smul, map_one, sigmaOddAlg_TT]

lemma sigmaOddAlg_TnuI_sq :
    sigmaOddAlg ((Tnu Complex.I) ^ 2) = (sigmaOddT - Complex.I • 1) ^ 2 := by
  rw [pow_two, map_mul, sigmaOddAlg_TnuI, ← pow_two]

lemma sigmaOddAlg_X_TnuI_sq :
    sigmaOddAlg (X * (Tnu Complex.I) ^ 2)
      = sigmaOddX * (sigmaOddT - Complex.I • 1) ^ 2 := by
  rw [map_mul, sigmaOddAlg_X, sigmaOddAlg_TnuI_sq]

lemma row0_sq_apply (j : Fin 6) :
    ((sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 0 j = 0 := by
  fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, sigmaOddT,
      Fin.sum_univ_six, Complex.I_mul_I] <;> ring

lemma row3_sq_apply (j : Fin 6) :
    ((sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 3 j = 0 := by
  fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, sigmaOddT,
      Fin.sum_univ_six, Complex.I_mul_I] <;> ring

lemma row0_X_sq_apply (j : Fin 6) :
    (sigmaOddX * (sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 0 j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hk : sigmaOddX 0 k = if k = (3 : Fin 6) then 1 else 0 := by
    rw [sigmaOddX_row0, Pi.single_apply]
  rw [hk]
  by_cases h : k = 3
  · subst h; rw [if_pos rfl, one_mul, row3_sq_apply]
  · rw [if_neg h, zero_mul]

/-! ## The right ideal generated by `(T-i)²` and `X (T-i)²` -/

/-- The right ideal `(T-i)² · RR + X (T-i)² · RR` of `RR = ℂ[ℤ/2 ∗ ℤ/3]`, as the set of
elements `(T-i)² * a + X * (T-i)² * b`. -/
def TnuIdeal : Submodule ℂ RR where
  carrier := {r : RR | ∃ a b : RR,
    r = (Tnu Complex.I) ^ 2 * a + X * (Tnu Complex.I) ^ 2 * b}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a₁, b₁, hx⟩ ⟨a₂, b₂, hy⟩
    exact ⟨a₁ + a₂, b₁ + b₂, by rw [hx, hy]; noncomm_ring⟩
  smul_mem' := by
    rintro c x ⟨a, b, hx⟩
    exact ⟨c • a, c • b, by
      rw [hx, smul_add, ← Algebra.mul_smul_comm, ← Algebra.mul_smul_comm]⟩

lemma mem_TnuIdeal {r : RR} :
    r ∈ TnuIdeal ↔ ∃ a b : RR, r = (Tnu Complex.I) ^ 2 * a + X * (Tnu Complex.I) ^ 2 * b :=
  Iff.rfl

lemma row_eq_zero_of_mul {A B : Matrix (Fin 6) (Fin 6) ℂ} (h : A 0 = 0) : (A * B) 0 = 0 := by
  ext j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [congr_fun h k, Pi.zero_apply, zero_mul]

lemma row0_sq : ((sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 0 = 0 :=
  funext row0_sq_apply

lemma row0_X_sq : (sigmaOddX * (sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2) 0 = 0 :=
  funext row0_X_sq_apply

lemma sigmaOddAlg_TnuIdeal_row0 {a : RR} (ha : a ∈ TnuIdeal) : (sigmaOddAlg a) 0 = 0 := by
  obtain ⟨b, c, hbc⟩ := mem_TnuIdeal.mp ha
  rw [hbc, map_add]
  have h1 : (sigmaOddAlg ((Tnu Complex.I) ^ 2 * b)) 0 = 0 := by
    rw [map_mul, sigmaOddAlg_TnuI_sq]
    exact row_eq_zero_of_mul (A := (sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2)
      (B := sigmaOddAlg b) row0_sq
  have h2 : (sigmaOddAlg (X * (Tnu Complex.I) ^ 2 * c)) 0 = 0 := by
    rw [map_mul, map_mul, sigmaOddAlg_X, sigmaOddAlg_TnuI_sq]
    exact row_eq_zero_of_mul
      (A := sigmaOddX * (sigmaOddT - Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) ^ 2)
      (B := sigmaOddAlg c) row0_X_sq
  ext j
  show (sigmaOddAlg ((Tnu Complex.I) ^ 2 * b)) 0 j
    + (sigmaOddAlg (X * (Tnu Complex.I) ^ 2 * c)) 0 j = 0
  rw [congr_fun h1 j, congr_fun h2 j]
  simp

/-! ## The transfer `Λ = (row 0) ∘ σ ∘ psiM⁻¹ ∘ (· e₋)` -/

lemma mul_eMinus_mem_range (x : R) : x * eMinus ∈ psiMLin.range := by
  obtain ⟨a, ha⟩ := psiM_surjective (x * eMinus) (by
    rw [mul_assoc, eMinus_mul_Rneg, mul_neg])
  exact ⟨a, ha⟩

/-- `x ↦ x · e₋` as a linear map into the range of `psiM`. -/
noncomputable def toRange : R →ₗ[ℂ] psiMLin.range where
  toFun x := ⟨x * eMinus, mul_eMinus_mem_range x⟩
  map_add' x y := Subtype.ext (by simp [add_mul])
  map_smul' c x := Subtype.ext (by simp [Algebra.smul_mul_assoc])

/-- The inverse of `psiM` on its range, as a linear equivalence. -/
noncomputable def psiSec : psiMLin.range →ₗ[ℂ] RR :=
  (LinearEquiv.ofInjective psiMLin psiM_injective).symm.toLinearMap

lemma psiM_psiSec (v : psiMLin.range) : psiM (psiSec v) = v := by
  have h1 : (((LinearEquiv.ofInjective psiMLin psiM_injective) (psiSec v) : psiMLin.range) : R)
      = psiM (psiSec v) := LinearEquiv.ofInjective_apply psiMLin (psiSec v)
  have h2 : (LinearEquiv.ofInjective psiMLin psiM_injective) (psiSec v) = v :=
    LinearEquiv.apply_symm_apply _ v
  rw [← h1, h2]

/-- `psiSec` inverts `psiM` on the range. -/
lemma psiSec_eq {a : RR} {x : R} (hx : x ∈ psiMLin.range) (h : psiM a = x) :
    psiSec ⟨x, hx⟩ = a := by
  refine psiM_injective ?_
  rw [psiM_psiSec ⟨x, hx⟩, h]

lemma psiM_neg' (a : RR) : psiM (-a) = -psiM a := by
  rw [show -a = (-1 : ℂ) • a from by rw [neg_smul, one_smul], psiM_smul, neg_smul, one_smul]

/-- The row-`0` functional on matrices. -/
def rowZero : Matrix (Fin 6) (Fin 6) ℂ →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun M := M 0
  map_add' M N := by ext j; simp [Matrix.add_apply]
  map_smul' c M := by ext j; simp [Matrix.smul_apply]

/-- **The linear map of the statement.** It kills `𝓘_odd` and reads off the six coordinates of
the shifted representation. -/
noncomputable def LamOdd : R →ₗ[ℂ] (Fin 6 → ℂ) :=
  rowZero.comp (sigmaOddAlg.toLinearMap.comp (psiSec.comp toRange))

lemma LamOdd_apply (x : R) : LamOdd x = (sigmaOddAlg (psiSec (toRange x))) 0 := rfl

/-! ## `Λ` kills the odd-weight defect ideal -/

lemma LamOdd_augIdealOdd {x : R} (hx : x ∈ augIdealOdd) : LamOdd x = 0 := by
  obtain ⟨C, rfl⟩ := mem_augIdealOdd_exists hx
  have hzero : ((Rneg + 1) * C) * eMinus = 0 := by
    rw [mul_assoc, ← eMinus_comm C, ← mul_assoc, add_mul, one_mul, Rneg_mul_eMinus,
      neg_add_cancel, zero_mul]
  rw [LamOdd_apply, show toRange ((Rneg + 1) * C) = 0 from Subtype.ext hzero, map_zero,
    map_zero]
  rfl

lemma LamOdd_T2 (A : R) : LamOdd ((R_T - 1) ^ 2 * A) = 0 := by
  set b : RR := psiSec (toRange A) with hb
  have hbpsi : psiM b = A * eMinus := by
    rw [hb]; exact psiM_psiSec (toRange A)
  have hmem : ((R_T - 1) ^ 2 * A) * eMinus ∈ psiMLin.range := mul_eMinus_mem_range _
  have hkey : psiM (-((Tnu Complex.I) ^ 2 * b)) = ((R_T - 1) ^ 2 * A) * eMinus := by
    rw [psiM_neg', psiM_mul, psiM_TnuI_sq, hbpsi, neg_smul, one_smul, neg_mul,
      mul_eMinus_mul, neg_neg]
  have hsec : psiSec (toRange ((R_T - 1) ^ 2 * A)) = -((Tnu Complex.I) ^ 2 * b) :=
    psiSec_eq hmem hkey
  have hmemI : (Tnu Complex.I) ^ 2 * b ∈ TnuIdeal :=
    mem_TnuIdeal.mpr ⟨b, 0, by simp⟩
  rw [LamOdd_apply, hsec, map_neg]
  show -(sigmaOddAlg ((Tnu Complex.I) ^ 2 * b)) 0 = 0
  rw [sigmaOddAlg_TnuIdeal_row0 hmemI, neg_zero]

lemma smul_eMinus_mul (c d : ℂ) (x y : R) :
    (c • (x * eMinus)) * (d • (y * eMinus)) = (c * d) • ((x * y) * eMinus) := by
  rw [smul_mul_smul, mul_eMinus_mul]

lemma eMinus_mul_psiM (b : RR) : eMinus * psiM b = psiM b := by
  rw [psiM, ← mul_assoc, eMinus_comm, mul_assoc, eMinus_sq]

/-- The second generator of the shifted ideal, under `psiM`: the `i`-twist turns `X (T-i)²`
into `S (T-1)² e₋`. -/
lemma psiM_smul_X_TnuI_sq (b : RR) :
    psiM (Complex.I • (X * (Tnu Complex.I) ^ 2 * b))
      = R_S * (R_T - 1) ^ 2 * psiM b := by
  have hI : Complex.I * (Complex.I * -1) = 1 := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [psiM_smul, psiM_mul, psiM_mul, psiM_X, psiM_TnuI_sq, smul_eMinus_mul, smul_mul_assoc,
    smul_smul, hI, one_smul, mul_assoc, eMinus_mul_psiM]

lemma LamOdd_S_T2 (B : R) : LamOdd (R_S * (R_T - 1) ^ 2 * B) = 0 := by
  set c : RR := psiSec (toRange B) with hc
  have hcpsi : psiM c = B * eMinus := by
    rw [hc]; exact psiM_psiSec (toRange B)
  have hmem : (R_S * (R_T - 1) ^ 2 * B) * eMinus ∈ psiMLin.range := mul_eMinus_mem_range _
  have hkey : psiM (Complex.I • (X * (Tnu Complex.I) ^ 2 * c))
      = (R_S * (R_T - 1) ^ 2 * B) * eMinus := by
    rw [psiM_smul_X_TnuI_sq, hcpsi]
    noncomm_ring
  have hsec : psiSec (toRange (R_S * (R_T - 1) ^ 2 * B))
      = Complex.I • (X * (Tnu Complex.I) ^ 2 * c) :=
    psiSec_eq hmem hkey
  have hmemI : Complex.I • (X * (Tnu Complex.I) ^ 2 * c) ∈ TnuIdeal :=
    Submodule.smul_mem _ Complex.I (mem_TnuIdeal.mpr ⟨0, c, by simp⟩)
  rw [LamOdd_apply, hsec]
  exact sigmaOddAlg_TnuIdeal_row0 hmemI

lemma LamOdd_IdealI {x : R} (hx : x ∈ IdealI) : LamOdd x = 0 := by
  obtain ⟨A, B, rfl⟩ := Work.Kernels.mem_span2.mp hx
  rw [map_add, LamOdd_T2 A, LamOdd_S_T2 B, add_zero]

lemma LamOdd_idealIOdd {x : R} (hx : x ∈ idealIOdd) : LamOdd x = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, LamOdd_IdealI hy, LamOdd_augIdealOdd hz, add_zero]

/-! ## The images of the six basis elements `1, T, TS, S, ST, STS` -/

/-- The six elements `1, T, TS, S, ST, STS` of `R = ℂ[SL(2,ℤ)]`. -/
def M6R : Fin 6 → R := ![1, R_T, R_T * R_S, R_S, R_S * R_T, R_S * R_T * R_S]

@[simp] lemma M6R_zero : M6R 0 = (1 : R) := rfl
@[simp] lemma M6R_one : M6R 1 = R_T := rfl
@[simp] lemma M6R_two : M6R 2 = R_T * R_S := rfl
@[simp] lemma M6R_three : M6R 3 = R_S := rfl
@[simp] lemma M6R_four : M6R 4 = R_S * R_T := rfl
@[simp] lemma M6R_five : M6R 5 = R_S * R_T * R_S := rfl

/-- The six elements of `RR` whose `psiM`-images are `(1, T, TS, S, ST, STS) e₋`. -/
def W6 : Fin 6 → RR :=
  ![1, (-Complex.I) • TT, (-1 : ℂ) • (TT * X), (-Complex.I) • X, (-1 : ℂ) • (X * TT),
    Complex.I • (X * TT * X)]

lemma psiM_W6_zero : psiM (W6 0) = M6R 0 * eMinus := by
  rw [show W6 0 = 1 from rfl, M6R_zero, psiM_one, one_mul]

lemma psiM_W6_one : psiM (W6 1) = M6R 1 * eMinus := by
  rw [show W6 1 = (-Complex.I) • TT from rfl, M6R_one, psiM_smul, psiM_TT, smul_smul,
    show (-Complex.I) * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I, neg_neg],
    one_smul]

lemma psiM_W6_two : psiM (W6 2) = M6R 2 * eMinus := by
  rw [show W6 2 = (-1 : ℂ) • (TT * X) from rfl, M6R_two, psiM_smul, psiM_mul, psiM_TT,
    psiM_X, smul_eMinus_mul, smul_smul,
    show (-1 : ℂ) * (Complex.I * Complex.I) = 1 from by rw [Complex.I_mul_I]; norm_num,
    one_smul]

lemma psiM_W6_three : psiM (W6 3) = M6R 3 * eMinus := by
  rw [show W6 3 = (-Complex.I) • X from rfl, M6R_three, psiM_smul, psiM_X, smul_smul,
    show (-Complex.I) * Complex.I = 1 from by rw [neg_mul, Complex.I_mul_I, neg_neg],
    one_smul]

lemma psiM_W6_four : psiM (W6 4) = M6R 4 * eMinus := by
  rw [show W6 4 = (-1 : ℂ) • (X * TT) from rfl, M6R_four, psiM_smul, psiM_mul, psiM_X,
    psiM_TT, smul_eMinus_mul, smul_smul,
    show (-1 : ℂ) * (Complex.I * Complex.I) = 1 from by rw [Complex.I_mul_I]; norm_num,
    one_smul]

lemma psiM_W6_five : psiM (W6 5) = M6R 5 * eMinus := by
  rw [show W6 5 = Complex.I • (X * TT * X) from rfl, M6R_five, psiM_smul, psiM_mul,
    psiM_mul, psiM_X, psiM_TT, smul_eMinus_mul, smul_eMinus_mul, smul_smul,
    show Complex.I * (Complex.I * Complex.I * Complex.I) = 1 from by
      rw [show Complex.I * Complex.I * Complex.I = -Complex.I from by
        rw [Complex.I_mul_I]; ring, mul_neg, Complex.I_mul_I, neg_neg],
    one_smul]

lemma psiM_W6 (i : Fin 6) : psiM (W6 i) = M6R i * eMinus := by
  fin_cases i
  · exact psiM_W6_zero
  · exact psiM_W6_one
  · exact psiM_W6_two
  · exact psiM_W6_three
  · exact psiM_W6_four
  · exact psiM_W6_five

lemma LamOdd_M6 (i : Fin 6) : LamOdd (M6R i) = rowZero (sigmaOddAlg (W6 i)) := by
  rw [LamOdd_apply,
    show toRange (M6R i) = ⟨M6R i * eMinus, mul_eMinus_mem_range (M6R i)⟩ from rfl,
    psiSec_eq (mul_eMinus_mem_range (M6R i)) (psiM_W6 i)]
  rfl

/-! ## The six images are multiples of the standard basis vectors -/

lemma rowZero_smul (c : ℂ) (A : Matrix (Fin 6) (Fin 6) ℂ) :
    rowZero (c • A) = c • rowZero A := LinearMap.map_smul rowZero c A

lemma row0_TX : rowZero (sigmaOddT * sigmaOddX) = Pi.single 2 (1 : ℂ) := by
  ext j; fin_cases j <;>
    simp [rowZero, Matrix.mul_apply, sigmaOddT, sigmaOddX, Work.Modular.sigmaS,
      Fin.sum_univ_six]

lemma row0_XT : rowZero (sigmaOddX * sigmaOddT) = Pi.single 4 (1 : ℂ) := by
  ext j; fin_cases j <;>
    simp [rowZero, Matrix.mul_apply, sigmaOddT, sigmaOddX, Work.Modular.sigmaS,
      Fin.sum_univ_six]

lemma row0_XTX : rowZero (sigmaOddX * sigmaOddT * sigmaOddX) = Pi.single 5 (1 : ℂ) := by
  ext j; fin_cases j <;>
    simp [rowZero, Matrix.mul_apply, sigmaOddT, sigmaOddX, Work.Modular.sigmaS,
      Fin.sum_univ_six]

lemma rowZero_one : rowZero (1 : Matrix (Fin 6) (Fin 6) ℂ) = Pi.single 0 (1 : ℂ) := by
  ext j; fin_cases j <;> simp [rowZero, Matrix.one_apply]

lemma sigmaOddAlg_W6_zero : rowZero (sigmaOddAlg (W6 0)) = Pi.single 0 (1 : ℂ) := by
  rw [show W6 0 = 1 from rfl, map_one, rowZero_one]

lemma sigmaOddAlg_W6_one :
    rowZero (sigmaOddAlg (W6 1)) = (-Complex.I) • Pi.single 1 (1 : ℂ) := by
  rw [show W6 1 = (-Complex.I) • TT from rfl, map_smul, sigmaOddAlg_TT, rowZero_smul,
    show rowZero sigmaOddT = Pi.single 1 (1 : ℂ) from sigmaOddT_row0]

lemma sigmaOddAlg_W6_two :
    rowZero (sigmaOddAlg (W6 2)) = (-1 : ℂ) • Pi.single 2 (1 : ℂ) := by
  rw [show W6 2 = (-1 : ℂ) • (TT * X) from rfl, map_smul, map_mul, sigmaOddAlg_TT,
    sigmaOddAlg_X, rowZero_smul, row0_TX]

lemma sigmaOddAlg_W6_three :
    rowZero (sigmaOddAlg (W6 3)) = (-Complex.I) • Pi.single 3 (1 : ℂ) := by
  rw [show W6 3 = (-Complex.I) • X from rfl, map_smul, sigmaOddAlg_X, rowZero_smul,
    show rowZero sigmaOddX = Pi.single 3 (1 : ℂ) from sigmaOddX_row0]

lemma sigmaOddAlg_W6_four :
    rowZero (sigmaOddAlg (W6 4)) = (-1 : ℂ) • Pi.single 4 (1 : ℂ) := by
  rw [show W6 4 = (-1 : ℂ) • (X * TT) from rfl, map_smul, map_mul, sigmaOddAlg_X,
    sigmaOddAlg_TT, rowZero_smul, row0_XT]

lemma sigmaOddAlg_W6_five :
    rowZero (sigmaOddAlg (W6 5)) = Complex.I • Pi.single 5 (1 : ℂ) := by
  simp only [show W6 5 = Complex.I • (X * TT * X) from rfl, map_smul, map_mul,
    sigmaOddAlg_X, sigmaOddAlg_TT, rowZero_smul, row0_XTX]

lemma LamOdd_M6_0 : ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R 0) = μ • Pi.single 0 (1 : ℂ) :=
  ⟨1, one_ne_zero, by rw [LamOdd_M6, sigmaOddAlg_W6_zero, one_smul]⟩

lemma LamOdd_M6_1 : ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R 1) = μ • Pi.single 1 (1 : ℂ) :=
  ⟨-Complex.I, neg_ne_zero.mpr Complex.I_ne_zero,
    by rw [LamOdd_M6, sigmaOddAlg_W6_one]⟩

lemma LamOdd_M6_2 : ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R 2) = μ • Pi.single 2 (1 : ℂ) :=
  ⟨-1, by norm_num, by rw [LamOdd_M6, sigmaOddAlg_W6_two]⟩

lemma LamOdd_M6_3 : ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R 3) = μ • Pi.single 3 (1 : ℂ) :=
  ⟨-Complex.I, neg_ne_zero.mpr Complex.I_ne_zero,
    by rw [LamOdd_M6, sigmaOddAlg_W6_three]⟩

lemma LamOdd_M6_4 : ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R 4) = μ • Pi.single 4 (1 : ℂ) :=
  ⟨-1, by norm_num, by rw [LamOdd_M6, sigmaOddAlg_W6_four]⟩

lemma LamOdd_M6_5 : ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R 5) = μ • Pi.single 5 (1 : ℂ) :=
  ⟨Complex.I, Complex.I_ne_zero, by rw [LamOdd_M6, sigmaOddAlg_W6_five]⟩

lemma LamOdd_M6_eq (i : Fin 6) :
    ∃ μ : ℂ, μ ≠ 0 ∧ LamOdd (M6R i) = μ • Pi.single i (1 : ℂ) := by
  fin_cases i
  · exact LamOdd_M6_0
  · exact LamOdd_M6_1
  · exact LamOdd_M6_2
  · exact LamOdd_M6_3
  · exact LamOdd_M6_4
  · exact LamOdd_M6_5

/-! ## The induced map on the quotient and the dimension count -/

/-- `Λ` as a linear map on `R ⧸ 𝓘_odd`. -/
noncomputable def LamBar : Qodd →ₗ[ℂ] (Fin 6 → ℂ) :=
  Submodule.liftQ idealIOdd LamOdd (fun x hx => LinearMap.mem_ker.mpr (LamOdd_idealIOdd hx))

lemma LamBar_mkQ (x : R) : LamBar (Submodule.mkQ idealIOdd x) = LamOdd x :=
  Submodule.liftQ_apply idealIOdd LamOdd x

lemma LamBar_surjective : Function.Surjective LamBar := by
  have hgen : ∀ i : Fin 6, Pi.single i (1 : ℂ) ∈ LamBar.range := by
    intro i
    obtain ⟨μ, hμ, hval⟩ := LamOdd_M6_eq i
    refine ⟨μ⁻¹ • Submodule.mkQ idealIOdd (M6R i), ?_⟩
    rw [map_smul, LamBar_mkQ, hval, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  intro v
  rw [← LinearMap.mem_range]
  have hv : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
    ext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_apply, if_neg (Ne.symm hb), smul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hv]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgen i)

lemma Qodd_finite : Module.Finite ℂ Qodd :=
  Module.Finite.of_surjective Phi Phi_surjective

lemma finrank_Qodd_le : Module.finrank ℂ Qodd ≤ 6 := by
  haveI := Qodd_finite
  have h := LinearMap.finrank_range_add_finrank_ker Phi
  rw [LinearMap.range_eq_top.mpr Phi_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

lemma finrank_Qodd_ge : 6 ≤ Module.finrank ℂ Qodd := by
  haveI := Qodd_finite
  have h := LinearMap.finrank_range_add_finrank_ker LamBar
  rw [LinearMap.range_eq_top.mpr LamBar_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

lemma finrank_Qodd : Module.finrank ℂ Qodd = 6 :=
  le_antisymm finrank_Qodd_le finrank_Qodd_ge

lemma Phi_injective : Function.Injective Phi := by
  haveI := Qodd_finite
  rw [← LinearMap.ker_eq_bot]
  have h := LinearMap.finrank_range_add_finrank_ker Phi
  rw [LinearMap.range_eq_top.mpr Phi_surjective, finrank_top, finrank_Qodd,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  have hzero : Module.finrank ℂ ↥Phi.ker = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hzero

lemma LamBar_injective : Function.Injective LamBar := by
  haveI := Qodd_finite
  rw [← LinearMap.ker_eq_bot]
  have h := LinearMap.finrank_range_add_finrank_ker LamBar
  rw [LinearMap.range_eq_top.mpr LamBar_surjective, finrank_top, finrank_Qodd,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  have hzero : Module.finrank ℂ ↥LamBar.ker = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hzero

lemma linearIndependent_MpElem_mkQ :
    LinearIndependent ℂ (fun i : Fin 6 => Submodule.mkQ idealIOdd (MpElem i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hmem : Phi g = 0 := by
    rw [Phi]
    exact hg
  have hg0 : g = 0 := Phi_injective (by rw [hmem, map_zero])
  rw [hg0]
  rfl

/-! ## The theorem -/

theorem linearMap_killing_idealIOdd_exists :
    ∃ Λ : Work.Kernels.R →ₗ[ℂ] (Fin 6 → ℂ),
      (∀ x ∈ Work.Asymptotics.idealIOdd, Λ x = 0) ∧
      LinearIndependent ℂ (fun i : Fin 6 => Λ (Work.Asymptotics.MpElem i)) := by
  refine ⟨LamOdd, fun x hx => LamOdd_idealIOdd hx, ?_⟩
  have hLI : LinearIndependent ℂ
      (fun i : Fin 6 => LamBar (Submodule.mkQ idealIOdd (MpElem i))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hg' : LamBar (∑ i, g i • Submodule.mkQ idealIOdd (MpElem i)) = 0 := by
      rw [map_sum]
      simpa only [map_smul] using hg
    have h0 : (∑ i, g i • Submodule.mkQ idealIOdd (MpElem i)) = 0 :=
      LamBar_injective (by rw [hg', map_zero])
    exact (Fintype.linearIndependent_iff.mp linearIndependent_MpElem_mkQ) g h0 j
  have hfun : (fun i : Fin 6 => LamOdd (MpElem i))
      = fun i : Fin 6 => LamBar (Submodule.mkQ idealIOdd (MpElem i)) := by
    funext i
    rw [LamBar_mkQ]
  rw [hfun]
  exact hLI

end Work.Asymptotics

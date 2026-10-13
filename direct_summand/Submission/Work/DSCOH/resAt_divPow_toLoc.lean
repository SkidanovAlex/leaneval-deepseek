import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}
  {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]

/-- The structure map `resAt h` on the localization sends `toLoc S m` to `toLoc T m`: both are the
class of `m` with denominator `1`.  This is the defining property of the localization map
`LocalizedModule.liftOfLE`. -/
private lemma resAt_toLoc_aux {S T : Finset (Fin n)} (h : S ⊆ T) (m : M) :
    resAt (A := A) (M := M) h (toLoc (A := A) (M := M) S m) = toLoc (A := A) (M := M) T m :=
  IsLocalizedModule.liftOfLE_apply (S₁ := subS (A := A) S) (S₂ := subS (A := A) T)
    (h := subS_mono (A := A) h)
    (f₁ := LocalizedModule.mkLinearMap (subS (A := A) S) M)
    (f₂ := LocalizedModule.mkLinearMap (subS (A := A) T) M) m

/-- `toLoc` is `Poly A n`-linear (it is the localization map `M →ₗ[Poly A n] M[1/X_S]`, restricted
along `A → Poly A n`). -/
private lemma toLoc_smul_aux (S : Finset (Fin n)) (p : Poly A n) (m : M) :
    toLoc (A := A) (M := M) S (p • m) = p • toLoc (A := A) (M := M) S m :=
  LinearMap.map_smul (LocalizedModule.mkLinearMap (subS (A := A) S) M) p m

/-- The two inverse properties of `divPow S k` (division by `(X_S)^k`): multiplying back by
`(X_S)^k` recovers the original element. -/
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

/-- The monomial over `T` splits as the product of the monomials over `S` and over `T \ S`, when
`S ⊆ T`. -/
lemma monomial_sdiff_pow_aux {S T : Finset (Fin n)} (h : S ⊆ T) (k : ℕ) :
    monomial (A := A) T ^ k =
      monomial (A := A) S ^ k * monomial (A := A) (T \ S) ^ k := by
  have hmono : monomial (A := A) T = monomial (A := A) S * monomial (A := A) (T \ S) := by
    simp only [monomial]
    rw [← Finset.prod_sdiff h, mul_comm]
  rw [hmono, mul_pow]

theorem resAt_divPow_toLoc {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {S T : Finset (Fin n)} (h : S ⊆ T) (k : ℕ) (m : M) :
    resAt (A := A) (M := M) h (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      divPow (A := A) (M := M) T k
        (toLoc (A := A) (M := M) T ((monomial (A := A) (T \ S)) ^ k • m)) := by
  -- Both sides have the same image after multiplication by `(X_T)^k = (X_S)^k * (X_{T\S})^k`;
  -- since multiplication by `(X_T)^k` is invertible on `M[1/X_T]`, they are equal.
  have hpow := monomial_sdiff_pow_aux (A := A) h k
  -- Left hand side: `(X_T)^k • (m/X_S^k) = (X_{T\S})^k • m`.
  have hL : (monomial (A := A) T ^ k) •
        resAt (A := A) (M := M) h (divPow (A := A) (M := M) S k (toLoc (A := A) (M := M) S m)) =
      (monomial (A := A) (T \ S) ^ k) • toLoc (A := A) (M := M) T m := by
    rw [hpow, mul_comm (monomial (A := A) S ^ k) (monomial (A := A) (T \ S) ^ k), mul_smul]
    rw [← LinearMap.map_smul, smul_divPow_aux, resAt_toLoc_aux]
  -- Right hand side: `(X_T)^k • ((X_{T\S})^k m)/X_T^k = (X_{T\S})^k • m`.
  have hR : (monomial (A := A) T ^ k) •
        divPow (A := A) (M := M) T k
          (toLoc (A := A) (M := M) T ((monomial (A := A) (T \ S)) ^ k • m)) =
      (monomial (A := A) (T \ S) ^ k) • toLoc (A := A) (M := M) T m := by
    rw [smul_divPow_aux, toLoc_smul_aux]
  have hkey := hL.trans hR.symm
  have := congrArg (divPow (A := A) (M := M) T k) hkey
  simpa only [divPow_mul_smul_aux] using this

end Work.DSCOH

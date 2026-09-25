import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormOp
import Submission.NK.LocalReciprocityLubinTate.Unramified.resultant_normOp
import Submission.NK.LocalReciprocityLubinTate.Unramified.resultant_X_pow_sub_C_X
import Submission.NK.LocalReciprocityLubinTate.Unramified.LTGain
import Submission.NK.LocalReciprocityLubinTate.Unramified.Heart.Param
import Submission.NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp_sCoeff
import Submission.NK.LocalReciprocityLubinTate.Unramified.Heart.map_evalRingHom_sub_mem_span

namespace NK.LocalReciprocityLubinTate.Unramified.Heart

universe u

/-- **The gain step of the Lubin–Tate norm operator.**  Let `F` be a nonarchimedean local
field, `P ∈ 𝒪[F]` irreducible, `q = residueCard F` and `𝒩 h = normOp (LTpoly P q) h`, i.e.
`𝒩(h)(Y) = Res_X(f(X) - Y, h(X))` with `f = P·X + X^q`.  Then `𝒩` is a contraction that *gains* a
power of `P`: if `u - v ∈ (P^k)` with `k ≥ 1`, then `𝒩 u - 𝒩 v ∈ (P^{k+1})`.

PROOF ROUTE (all ingredients are available).  Write `u - v = C (P^k) * t` (`Ideal.mem_span_singleton`).
Introduce the base ring `B := A[Z]` (`A = 𝒪[F]`, `Z := Polynomial.X : Polynomial A`, so that
`Polynomial B = A[Z][Y]`) and the `Z`-parametrised norm

`GZ := Res_X (f.map C - C Y) (v.map C + C Z * t.map C) ∈ B[Y]`,

computed in `(B[Y])[X]` with the fixed degree parameters `q` (`f` is monic of degree `q`) and
`N := t.natDegree` (`resultant_map_map` with explicit degrees; the value of the resultant does not
depend on the chosen degree parameter beyond the natDegree because the first argument is monic —
`resultant_add_right_deg` and `leadingCoeff = 1`).

1. *Constant term.*  Use `Polynomial.evalRingHom (0 : A) : Polynomial A →+* A` and
   `Polynomial.map` to substitute `Z ↦ 0`: by `resultant_map_map` the image of `GZ` is
   `Res_X(f - C Y, v) = 𝒩 v`, so the image of `GZ - 𝒩v` is `0`.  By `Polynomial.coeff_map` and
   `Polynomial.X_dvd_iff` (`X ∣ q ↔ q.coeff 0 = 0`, `q.coeff 0 = q.eval 0`) this gives
   `C Z ∣ GZ - 𝒩 v` (`Polynomial.C_dvd_iff_dvd_coeff`).
2. *Modulo `P`.*  Reduce modulo `P` and apply the twisted Frobenius formula
   `resultant_X_pow_sub_C_X'` with the base ring `(A ⧸ (P))[Z]` (a domain of characteristic `p`
   with `q = p ^ k'`), using `f ≡ X^q (mod P)`: in `((A ⧸ (P))[Z])[Y]`,
   `GZ ≡ Σ_j C ((v_j + Z t_j)^q) Y^j = Σ_j C (v_j^q) Y^j + Z^q * (Σ_j C (t_j^q) Y^j)`,
   because the ring has characteristic `p` and `q` is a power of `p`.  Since
   `Σ_j C (v_j^q) Y^j` is the reduction of `𝒩 v` (again `resultant_X_pow_sub_C_X'`, with `t = 0`),
   and `Z^q ∈ (Z^2)` for `q ≥ 2`, this gives `GZ - 𝒩v ∈ (P) + (Z^2)`.
3. *Combination.*  In the domain `B[Y]`: if `Z ∣ Δ` and `Δ ∈ (P) + (Z^2)`, then
   `Δ ∈ (P·Z) + (Z^2)`.  Indeed write `Δ = Z δ` and `Δ = P a + Z^2 b`; then `Z ∣ P a`, and as `Z`
   is prime and `P ∉ (Z)`, `a = Z a'`, whence `Z δ = Z (P a' + Z b)` and `δ = P a' + Z b`.
4. *Substitution.*  Apply the ring hom `Polynomial.map (Polynomial.evalRingHom (P ^ k)) : B[Y] →+* A[Y]`.
   By `resultant_map_map` the image of `GZ` is `𝒩 u` and the image of `𝒩 v` is `𝒩 v`; the image of
   `P` is `P`, of `P·Z` is `P ^ (k+1)`, and of `Z^2` is `P ^ (2k) ⊆ (P ^ (k+1))` since `k ≥ 1`.
   Hence `𝒩 u - 𝒩 v ∈ (P ^ (k+1))`. -/
theorem normOp_sub_mem_span_pow {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (P : ↥(ValuativeRel.valuation F).integer) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (u v : Polynomial ↥(ValuativeRel.valuation F).integer)
    (huv : u - v ∈ Ideal.span {Polynomial.C (P ^ k)}) :
    NK.LocalReciprocityLubinTate.Unramified.normOp
        (NK.LocalReciprocityLubinTate.LTpoly P (NK.LocalReciprocityLubinTate.residueCard F)) u
      - NK.LocalReciprocityLubinTate.Unramified.normOp
        (NK.LocalReciprocityLubinTate.LTpoly P (NK.LocalReciprocityLubinTate.residueCard F)) v
    ∈ Ideal.span {Polynomial.C (P ^ (k + 1))} := by
  -- write `u - v = C (P^k) * t`
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp huv
  have hu : u = v + Polynomial.C (P ^ k) * t := sub_eq_iff_eq_add'.mp ht
  haveI hdom : IsDomain ↥(ValuativeRel.valuation F).integer := inferInstance
  -- the residue ring is a field
  have hI : Ideal.span ({P} : Set ↥(ValuativeRel.valuation F).integer)
      = IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer := hP.maximalIdeal_eq.symm
  haveI hmaxI : (Ideal.span ({P} : Set ↥(ValuativeRel.valuation F).integer)).IsMaximal := by
    rw [hI]; exact IsLocalRing.maximalIdeal.isMaximal _
  haveI hfield : Field (↥(ValuativeRel.valuation F).integer
      ⧸ Ideal.span ({P} : Set ↥(ValuativeRel.valuation F).integer)) := Ideal.Quotient.field _
  -- the three inputs about `q = #𝓀[F]`
  set q : ℕ := NK.LocalReciprocityLubinTate.residueCard F with hqdef
  have hq2 : 2 ≤ q := by rw [hqdef]; exact NK.LocalReciprocityLubinTate.two_le_residueCard F
  have hq0 : 0 < q := by omega
  have hfmon : (NK.LocalReciprocityLubinTate.LTpoly P q).Monic :=
    (NK.LocalReciprocityLubinTate.isMonicOfDegree_LTpoly hq2).monic
  have hfdeg : (NK.LocalReciprocityLubinTate.LTpoly P q).natDegree = q :=
    (NK.LocalReciprocityLubinTate.isMonicOfDegree_LTpoly hq2).natDegree_eq
  have hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower P q := by
    rw [hqdef]
    exact NK.LocalReciprocityLubinTate.LubinTate.isFrobeniusPower_integers F P hP
  -- substituting `s = P ^ k` in the parametrised norm operator gives `𝒩 u`
  have hG : Polynomial.map (Polynomial.evalRingHom (P ^ k))
        (NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t)
      = NK.LocalReciprocityLubinTate.Unramified.normOp
          (NK.LocalReciprocityLubinTate.LTpoly P q) u := by
    rw [NK.LocalReciprocityLubinTate.Unramified.Heart.map_paramNormOp_evalRingHom
      P q (P ^ k) v t hq0 hfmon hfdeg, ← hu]
  -- substituting `s = 0` gives `𝒩 v`
  have hB : Polynomial.map (Polynomial.evalRingHom 0)
        (NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t)
      = NK.LocalReciprocityLubinTate.Unramified.normOp
          (NK.LocalReciprocityLubinTate.LTpoly P q) v :=
    NK.LocalReciprocityLubinTate.Unramified.Heart.map_paramNormOp_evalRingHom_zero
      P q v t hq0 hfmon hfdeg
  -- the `s`-linear coefficients vanish modulo `P`
  have hC : ∀ j, P
      ∣ ((NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t).coeff j).coeff 1 :=
    fun j => Ideal.mem_span_singleton.mp
      (NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp_sCoeff P q hq2 hpow v t j)
  -- the elementary estimate
  have hkey := NK.LocalReciprocityLubinTate.Unramified.Heart.map_evalRingHom_sub_mem_span
    P k hk (NK.LocalReciprocityLubinTate.Unramified.Heart.paramNormOp P q v t)
    (NK.LocalReciprocityLubinTate.Unramified.normOp
      (NK.LocalReciprocityLubinTate.LTpoly P q) v) hB hC
  rw [hG] at hkey
  exact hkey

end NK.LocalReciprocityLubinTate.Unramified.Heart

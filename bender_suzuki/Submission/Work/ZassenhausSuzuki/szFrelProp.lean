import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Suzuki.szW_conj_szU_matrix
import Submission.Work.ZassenhausSuzuki.SzModelCoords
import Submission.Work.ZassenhausSuzuki.SzAux.sz_e_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SzFrelProp`: the `f`-relation of the model `Sz(2^(2n+1))` in coordinates

This file proves `Work.ZassenhausSuzuki.SzFrelProp` (`SzModelCoords.lean`), the last matrix
computation of D2 (`NOTES_SzFrel.md`):

> for every `n ≥ 1` and every `u = (a,b) ≠ 1` in `A(GF(2^(2n+1)), titsTheta n)` there is
> `m ∈ B` with `w · u · w = m · w · τ(u)`,

where `w = szWgM n`, `B = szBorelS n` and `τ = SzA.sigma (titsTheta n)`.

The proof follows `NOTES_SzFrel.md` §1.  With `θ = 2^(n+1)`, `θ₁ = 2^n`, `u = (a,b)`,
`N = a^(2+θ) + a·b + b^θ` and `z` the `(1+θ₁)`-th root of `N`
(`Submission.Sz.sz_exists_root`; `N = z^(1+θ₁)`), let

`c = (a^(1+θ)+b)/z^(1+θ₁)`, `d = a/z^(1+θ₁) + c^(1+θ)`, `e = z^(1+θ₁)·d`, `f = a·z^(θ₁)`.

* `Commons.GroupTheory.Suzuki.szW_conj_szU_matrix` gives
  `w u(a,b) w = u(c,d)·w·u(e,f)·t(z)` in `GL(4,K)`;
* the two scalar identities `e = z·(b/N)` (`SzAux.sz_e_eq`) and
  `f = z^(1+θ)·(a/N)` (`szFrel_f_eq`) say that `u(e,f)·t(z) = t(z)·u(τ(a,b))`;
* `w·t(z) = t(z)⁻¹·w` (the Weyl element inverts the torus, `szWg_conj_szTg`).

Therefore `w u w = (u(c,d)·t(z)⁻¹) · w · u(τ(a,b))` with `u(c,d)·t(z)⁻¹ ∈ B`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

/-- In the coordinates of the Tits endomorphism, `N(a,b) = a^(2+2^(n+1)) + a·b + b^(2^(n+1))`. -/
theorem szAN_eq (n : ℕ) (u : SzA (GaloisField 2 (2 * n + 1)) (titsTheta n)) :
    SzA.N (titsTheta n) u =
      u.a ^ (2 + 2 ^ (n + 1)) + u.a * u.b + u.b ^ (2 ^ (n + 1)) := by
  have h1 : u.a * u.a * titsTheta n u.a = u.a ^ (2 + 2 ^ (n + 1)) := by
    rw [titsTheta_apply, ← pow_two, ← pow_add]
  have h2 : titsTheta n u.b = u.b ^ (2 ^ (n + 1)) := titsTheta_apply n u.b
  change u.a * u.a * titsTheta n u.a + u.a * u.b + titsTheta n u.b =
    u.a ^ (2 + 2 ^ (n + 1)) + u.a * u.b + u.b ^ (2 ^ (n + 1))
  rw [h1, h2]

/-- The second scalar identity of `NOTES_SzFrel.md` §1(iii): `f = z^(1+θ)·(a/N)`. -/
theorem szFrel_f_eq (n : ℕ) (a b z : GaloisField 2 (2 * n + 1)) (hz0 : z ≠ 0)
    (hz : z ^ (1 + 2 ^ n) = a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)))
    (f : GaloisField 2 (2 * n + 1)) (hf : f = a * z ^ (2 ^ n)) :
    f = z ^ (1 + 2 ^ (n + 1)) *
      (a / (a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)))) := by
  have hN0 : a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1)) ≠ 0 := by
    rw [← hz]; exact pow_ne_zero _ hz0
  have hexp : 2 ^ n + (1 + 2 ^ n) = 1 + 2 ^ (n + 1) := by rw [pow_succ]; ring
  rw [hf, ← mul_div_assoc, eq_div_iff hN0, ← hz, mul_assoc, ← pow_add, hexp]
  ring

theorem szFrelProp : Work.ZassenhausSuzuki.SzFrelProp := by
  intro n hn u hu
  have hab : ¬ (u.a = 0 ∧ u.b = 0) := fun h => hu (SzA.ext h.1 h.2)
  obtain ⟨z, hz0, hz⟩ := Submission.Sz.sz_exists_root n u.a u.b hab
  let N : Submission.Sz.SzField n :=
    u.a ^ (2 + 2 ^ (n + 1)) + u.a * u.b + u.b ^ (2 ^ (n + 1))
  let c : Submission.Sz.SzField n := (u.a ^ (1 + 2 ^ (n + 1)) + u.b) / z ^ (1 + 2 ^ n)
  let d : Submission.Sz.SzField n := u.a / z ^ (1 + 2 ^ n) + c ^ (1 + 2 ^ (n + 1))
  let e : Submission.Sz.SzField n := z ^ (1 + 2 ^ n) * d
  let f : Submission.Sz.SzField n := u.a * z ^ (2 ^ n)
  have hcdef : c = (u.a ^ (1 + 2 ^ (n + 1)) + u.b) / z ^ (1 + 2 ^ n) := rfl
  have hddef : d = u.a / z ^ (1 + 2 ^ n) + c ^ (1 + 2 ^ (n + 1)) := rfl
  have hedef : e = z ^ (1 + 2 ^ n) * d := rfl
  have hfdef : f = u.a * z ^ (2 ^ n) := rfl
  -- the matrix identity `w u(a,b) w = u(c,d) w u(e,f) t(z)`
  have hmatrix := Commons.GroupTheory.Suzuki.szW_conj_szU_matrix n u.a u.b z c d e f hz0 hz
    hcdef hddef hedef hfdef
  have hGL : Submission.Sz.szWg n * Submission.Sz.szUg n u.a u.b * Submission.Sz.szWg n =
      Submission.Sz.szUg n c d * Submission.Sz.szWg n * Submission.Sz.szUg n e f *
        Submission.Sz.szTg n (Units.mk0 z hz0) := by
    apply Units.ext
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Submission.Sz.szWg_coe,
      Submission.Sz.szUg_coe, Submission.Sz.szTg_coe, Submission.Sz.szW, Submission.Sz.szU,
      Submission.Sz.szT, Units.val_mk0] using hmatrix
  -- the two scalar identities
  have he_eq : e = z * (u.b / N) :=
    SzAux.sz_e_eq n u.a u.b z hz0 hz c d e hcdef hddef hedef
  have hf_eq : f = z ^ (1 + 2 ^ (n + 1)) * (u.a / N) :=
    szFrel_f_eq n u.a u.b z hz0 hz f hfdef
  -- the torus moves the two root elements
  have hτ' : Submission.Sz.szTg n (Units.mk0 z hz0) * Submission.Sz.szUg n (u.b / N) (u.a / N) =
      Submission.Sz.szUg n e f * Submission.Sz.szTg n (Units.mk0 z hz0) := by
    rw [Submission.Sz.szTg_mul_szUg]
    simp only [Units.val_mk0]
    rw [← he_eq, ← hf_eq]
  -- the Weyl element inverts the torus
  have hcom : Submission.Sz.szWg n * Submission.Sz.szTg n (Units.mk0 z hz0) =
      (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹ * Submission.Sz.szWg n := by
    calc Submission.Sz.szWg n * Submission.Sz.szTg n (Units.mk0 z hz0)
        = Submission.Sz.szWg n * Submission.Sz.szTg n (Units.mk0 z hz0) *
            (Submission.Sz.szWg n * Submission.Sz.szWg n) := by
          rw [Submission.Sz.szWg_mul_self, mul_one]
      _ = (Submission.Sz.szWg n * Submission.Sz.szTg n (Units.mk0 z hz0) *
            Submission.Sz.szWg n) * Submission.Sz.szWg n := by group
      _ = (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹ * Submission.Sz.szWg n := by
          rw [Submission.Sz.szWg_conj_szTg, Submission.Sz.szTg_inv]
  -- the telescoping computation
  have hkey : Submission.Sz.szWg n * Submission.Sz.szUg n u.a u.b * Submission.Sz.szWg n =
      (Submission.Sz.szUg n c d * (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹) *
        Submission.Sz.szWg n * Submission.Sz.szUg n (u.b / N) (u.a / N) := by
    calc Submission.Sz.szWg n * Submission.Sz.szUg n u.a u.b * Submission.Sz.szWg n
        = Submission.Sz.szUg n c d * Submission.Sz.szWg n * Submission.Sz.szUg n e f *
            Submission.Sz.szTg n (Units.mk0 z hz0) := hGL
      _ = Submission.Sz.szUg n c d * Submission.Sz.szWg n *
            (Submission.Sz.szUg n e f * Submission.Sz.szTg n (Units.mk0 z hz0)) := by group
      _ = Submission.Sz.szUg n c d * Submission.Sz.szWg n *
            (Submission.Sz.szTg n (Units.mk0 z hz0) *
              Submission.Sz.szUg n (u.b / N) (u.a / N)) := by
          rw [hτ']
      _ = Submission.Sz.szUg n c d *
            (Submission.Sz.szWg n * Submission.Sz.szTg n (Units.mk0 z hz0)) *
            Submission.Sz.szUg n (u.b / N) (u.a / N) := by group
      _ = Submission.Sz.szUg n c d *
            ((Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹ * Submission.Sz.szWg n) *
            Submission.Sz.szUg n (u.b / N) (u.a / N) := by rw [hcom]
      _ = (Submission.Sz.szUg n c d * (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹) *
            Submission.Sz.szWg n * Submission.Sz.szUg n (u.b / N) (u.a / N) := by group
  -- the element `m` lies in the Borel
  have hmB : Submission.Sz.szUg n c d * (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹ ∈
      Submission.Sz.szBorel n :=
    (Submission.Sz.szBorel n).mul_mem
      (Subgroup.mem_sup_left (show Submission.Sz.szUg n c d ∈ Submission.Sz.szTwoGroup n from
        ⟨c, d, rfl⟩))
      ((Submission.Sz.szBorel n).inv_mem
        (Subgroup.mem_sup_right (show Submission.Sz.szTg n (Units.mk0 z hz0) ∈
          (Submission.Sz.szTgHom n).range from ⟨Units.mk0 z hz0, rfl⟩)))
  refine ⟨⟨Submission.Sz.szUg n c d * (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹,
    Submission.Sz.szBorel_le_szModel n hmB⟩, Subgroup.mem_subgroupOf.mpr hmB, ?_⟩
  apply Subtype.ext
  show Submission.Sz.szWg n * Submission.Sz.szUg n u.a u.b * Submission.Sz.szWg n =
    (Submission.Sz.szUg n c d * (Submission.Sz.szTg n (Units.mk0 z hz0))⁻¹) *
      Submission.Sz.szWg n *
      Submission.Sz.szUg n (u.b / SzA.N (titsTheta n) u) (u.a / SzA.N (titsTheta n) u)
  rw [szAN_eq n u]
  exact hkey

end Work.ZassenhausSuzuki

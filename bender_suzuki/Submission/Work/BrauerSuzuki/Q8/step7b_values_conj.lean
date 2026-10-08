import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.star_Irr
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.Clifford.galoisChar_mem_Irr
import Submission.Work.Clifford.galois_char_apply
import Submission.Work.Clifford.galois_char_apply_of_pow_eq_one
import Submission.Work.Clifford.powChar_mem_Irr
import Submission.Work.BrauerSuzuki.Arith.exists_coprime_mod_four_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman (1974), step (7)(b): `χ (x u) = χ (x u⁻¹)` for `u ∈ H*`

Let `G` be finite, `x ∈ G` of order `4` and `S` a Sylow `2`-subgroup containing `x`, and let
`h : Ctx G x S` be the structural hypotheses of `Q8/Ctx` (`X = ⟨x⟩`, `T = ⟨x²⟩`,
`C* = C_G(X) = X × H*` with `H* = O_{2'}(C*)` of odd order, ...).

Glauberman's step (7)(b) (see `REFS/brauer_suzuki.md` §3, and the transcription
`REFS/vision/glauberman1974/`) says that an irreducible character `χ` of `G` with rational
integer values satisfies

`χ (x * u) = χ (x * u⁻¹)`   for every `u ∈ H*`.

The mathematical argument is the Galois twist `β` of `ℚ (ζ_{|G|})` which fixes the `2`-power
roots of unity and inverts the roots of unity of odd order: since `u ∈ H* ≤ C*` commutes with
`x`, the eigenvalues of `ρ (x * u)` are products `α β` of a `4`-th root of unity `α` (an
eigenvalue of `ρ x`) with an odd-order root of unity `β` (an eigenvalue of `ρ u`), and `β` sends
`α β ↦ α β⁻¹`, i.e. `χ (x * u) ↦ χ (x * u⁻¹)`.  As `χ` is integer valued, `β` fixes `χ (x * u)`
and the claim follows.

Concretely, we let `m = orderOf u` (odd) and use the exponent `k = 2 * m ^ 2 - 1`, which
satisfies `k ≡ 1 (mod 4)`, `k ≡ -1 (mod m)` and is coprime to `4 * m`
(`Work.BrauerSuzuki.Arith.exists_coprime_mod_four_odd`).  A Galois automorphism `σ : ℂ ≃+* ℂ`
with `σ ζ = ζ ^ k` for `ζ` a primitive `4 * m`-th root of unity exists
(`Work.Clifford.exists_aut_of_isPrimitiveRoot_pow`), and the Galois action on character values
(`Work.Clifford.galois_char_apply_of_pow_eq_one`, applied to the element `x * u` whose
`4 * m`-th power is `1`) gives

`σ (χ (x * u)) = χ ((x * u) ^ k) = χ (x ^ k * u ^ k) = χ (x * u⁻¹)`,

where `(x * u) ^ k = x ^ k * u ^ k` because `x` and `u` commute, `x ^ k = x` because
`k ≡ 1 (mod 4) = (mod orderOf x)`, and `u ^ k = u⁻¹` because `k ≡ -1 (mod orderOf u)`.  Finally
`σ (χ (x * u)) = χ (x * u)`, as `χ (x * u)` is a rational integer.
-/

namespace Work.BrauerSuzuki.Q8

open Classical in
theorem step7b_values_conj {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G)
    (hint : ∀ g : G, ∃ n : ℤ, χ g = (n : ℂ)) {u : G}
    (hu : u ∈ Work.BrauerSuzuki.Q8.Hstar x) :
    χ (x * u) = χ (x * u⁻¹) := by
  -- `u ∈ H* ≤ C* = C_G(X)`, so `u` commutes with `x`
  have hcomm : Commute x u :=
    (Subgroup.mem_centralizer_iff.mp (h.Hstar_le_Cstar hu)) x (Subgroup.mem_zpowers x)
  -- `orderOf u` divides `|H*|`, which is odd
  have hmdvd : orderOf u ∣ Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) := by
    have h1 := orderOf_dvd_natCard (⟨u, hu⟩ : ↥(Work.BrauerSuzuki.Q8.Hstar x))
    rwa [Subgroup.orderOf_mk] at h1
  have hmodd : Odd (orderOf u) := Odd.of_dvd_nat h.odd_H hmdvd
  have hHodd : Odd (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x)) := h.odd_H
  have hmpos : 0 < orderOf u := Nat.pos_of_dvd_of_pos hmdvd (by
    rcases Nat.eq_zero_or_pos (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x)) with h0 | hpos
    · rw [h0] at hHodd
      exact absurd hHodd (by rintro ⟨t, ht⟩; omega)
    · exact hpos)
  -- the exponent `k ≡ 1 (mod 4)`, `k ≡ -1 (mod orderOf u)`, coprime to `4 * orderOf u`
  obtain ⟨k, hk4, hkm, hkcp⟩ := Work.BrauerSuzuki.Arith.exists_coprime_mod_four_odd hmodd
  -- the primitive `4 * orderOf u`-th root of unity, and the Galois automorphism `ζ ↦ ζ ^ k`
  have hn0 : 0 < 4 * orderOf u := by omega
  let ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(4 * orderOf u))
  have hζ : IsPrimitiveRoot ζ (4 * orderOf u) := Complex.isPrimitiveRoot_exp _ hn0.ne'
  obtain ⟨σ, hσ⟩ := Work.Clifford.exists_aut_of_isPrimitiveRoot_pow hn0 hζ hkcp
  -- `(x * u) ^ (4 * orderOf u) = 1`
  have hx4 : x ^ 4 = 1 := by rw [← h.hx4]; exact pow_orderOf_eq_one x
  have hu4 : u ^ (4 * orderOf u) = 1 := by
    rw [mul_comm 4 (orderOf u), pow_mul, pow_orderOf_eq_one, one_pow]
  have hgpow : (x * u) ^ (4 * orderOf u) = 1 := by
    rw [hcomm.mul_pow, hu4, mul_one, pow_mul, hx4, one_pow]
  -- the Galois action on `χ (x * u)`
  have hχc : χ ∈ Work.Clifford.Irr G :=
    (Work.Clifford.mem_Irr (G := G) (χ := χ)).mpr
      ((Work.CharCore.mem_Irr_iff_fdrep χ).mp hχ)
  have hgal : σ (χ (x * u)) = χ ((x * u) ^ k) :=
    Work.Clifford.galois_char_apply_of_pow_eq_one hn0 hζ σ hσ hχc hgpow
  -- `(x * u) ^ k = x * u⁻¹`
  have hpow : (x * u) ^ k = x * u⁻¹ := by
    have hxk : x ^ k = x := by rw [← pow_mod_orderOf x k, h.hx4, hk4, pow_one]
    have huk : u ^ k = u⁻¹ := by
      rw [← pow_mod_orderOf u k, hkm]
      have h1 : u * u ^ (orderOf u - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hmpos, pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_right h1
    rw [hcomm.mul_pow, hxk, huk]
  -- `σ` fixes the rational integer `χ (x * u)`
  have hfix : σ (χ (x * u)) = χ (x * u) := by
    obtain ⟨n, hn⟩ := hint (x * u)
    rw [hn]
    simp
  rw [← hfix, hgal, hpow]

end Work.BrauerSuzuki.Q8

import Submission.Work.RouteB.MethodII
import Submission.Work.RouteB.Transport

open OnPropertyT Submission.FreeGroupAut Submission.Helpers
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The final assembly: the two `SAut(F_5)` certificates give `theorem_1`

This file combines the two symmetrisation methods (`MethodI.lean`,
`MethodII.lean`) and the transport (`Transport.lean`) into the complete
reduction of the challenge statement

    `theorem_1 (n : ℕ) (hn : 6 ≤ n) : PropertyT (MulAut (FreeGroup (Fin n)))`

to the paper's computer-assisted input, namely two sum-of-squares certificates
*in the group ring `ℝ SAut(F_5)`* (with `Δ_5 = Laplacian (SAutGen 5)` and
`Adj_5`, `Op_5` the paper's symmetrised sums over adjacent/opposite pairs of
edges of the `4`-simplex):

* `SAut5DeltaCert`  — `Δ_5² − 1.3·Δ_5 ∈ Σ²`  (Kaluba–Kaluba–Ozawa 2017, the
  paper's reference `saut5`: the remainder has `l¹`-norm `< 3·10⁻⁶`, giving the
  certified `λ_5 = 1.29999`);
* `SAut5Adj2OpCert` — `Adj_5 + 2·Op_5 − 0.278·Δ_5 ∈ Σ²` (the paper's
  `Adj5+2Op5`, obtained from an approximate solution with `λ = 0.28` and
  remainder of `l¹`-norm `< 0.0009423`).

Both are stated below in the *existential* form `∃ μ > 0, ...`, which is what the
arguments use and which is implied by the paper's numerical values (`Σ²` is
closed under multiplication by nonnegative scalars and under adding multiples of
`Δ_5 = ½ ∑ star(1-s)(1-s) ∈ Σ²`).  The paper's third computation
(`Adj_5 + 3·Op_5 − 1.37·Δ_5 ∈ Σ²`, its `Adj5+3Op5`) is *not* needed: Method II at
`n = 6` may use any `k ≤ n-3 = 3`, so `k = 2` (the second certificate) suffices,
see `SAut5Adj3OpCert_of_adj2Op` for the (then unnecessary) derivation of the
`k = 3` form.

The two routes:

* `n = 6`: Method II (`methodII_cert`) with the `Δ_5²` certificate and the
  `Adj_5 + 2·Op_5` certificate (`k = 2 ≤ 6-3`);
* `n ≥ 7`: Method I (`propertyT_aut_of_methodI`) with the `Adj_5 + 2·Op_5`
  certificate (`k = 2`, and `k(n-3) = 4 ≤ m-3`).

Both require the certificates transported from `ℝ[Aut(F_5)]` to `ℝ[Aut(F_m)]` by
`extendRingHom`, which is what `isSOS_extend_delta` / `isSOS_extend_adj`
provide.
-/

namespace Submission.RouteB

namespace Edge

variable {r m : ℕ}

/-! ## Transporting a certificate along `Aut(F_r) → Aut(F_m)` -/

lemma extendRingHom_smul (h : r ≤ m) (a : ℝ)
    (x : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r)))) :
    extendRingHom h (a • x) = a • extendRingHom h x := by
  rw [extendRingHom_apply]
  exact Submission.PropertyT.mapDomain_hom_smul (extendAutHom h) a x

/-- The transport of the `Δ`-certificate from level `r` to level `m ≥ r`. -/
theorem isSOS_extend_delta (h : r ≤ m) {lam : ℝ}
    (hcert : IsSOS (deltaSub r r ^ 2 - lam • deltaSub r r)) :
    IsSOS (deltaSub m r ^ 2 - lam • deltaSub m r) := by
  have h1 := IsSOS.map (extendRingHom h) (extendRingHom_star h) hcert
  have h2 : extendRingHom h (deltaSub r r ^ 2 - lam • deltaSub r r)
      = deltaSub m r ^ 2 - lam • deltaSub m r := by
    rw [map_sub, map_pow, extendRingHom_smul, extendRingHom_deltaSub_self]
  rwa [h2] at h1

/-- The transport of the `Adj + k·Op`-certificate from level `r` to level
`m ≥ r`. -/
theorem isSOS_extend_adj (h : r ≤ m) {k mu : ℝ}
    (hcert : IsSOS (AdjPair r r + k • OpPair r r - mu • deltaSub r r)) :
    IsSOS (AdjPair m r + k • OpPair m r - mu • deltaSub m r) := by
  have h1 := IsSOS.map (extendRingHom h) (extendRingHom_star h) hcert
  have h2 : extendRingHom h (AdjPair r r + k • OpPair r r - mu • deltaSub r r)
      = AdjPair m r + k • OpPair m r - mu • deltaSub m r := by
    rw [map_sub, map_add, extendRingHom_smul, extendRingHom_smul, extendRingHom_AdjPair_self,
      extendRingHom_OpPair_self, extendRingHom_deltaSub_self]
  rwa [h2] at h1

/-! ## The paper's equation (1): `Δ_S ∈ Σ²` for a symmetric generating set -/

/-- The paper's equation (1): `Δ_S = ½ ∑_{s∈S} star(1-s)(1-s)`, hence `Δ_S ∈ Σ²`. -/
theorem isSOS_laplacian {G : Type*} [Group G] (S : Finset G) (hsym : (S : Set G)⁻¹ = S) :
    IsSOS (OnPropertyT.Laplacian S) := by
  classical
  have h2 : IsSOS ((2 : ℝ) • OnPropertyT.Laplacian S) := by
    have key : ((2 : ℝ) • OnPropertyT.Laplacian S)
        = ∑ s ∈ S, star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s) := by
      rw [Algebra.smul_def]
      exact two_mul_laplacian_eq_sum_sq S hsym
    rw [key]
    refine IsSOS.finset_sum _ (fun s _ => ⟨{1 - MonoidAlgebra.of ℝ G s}, ?_⟩)
    rw [Finset.sum_singleton]
  have h := IsSOS.smul (r := (1 / 2 : ℝ)) (by norm_num) h2
  rwa [smul_smul, show ((1 : ℝ) / 2 * 2) = 1 by norm_num, one_smul] at h

/-! ## The two certificates for `SAut(F_5)` -/

/-- `Δ_5² − 1.3·Δ_5 ∈ Σ²` (Kaluba–Kaluba–Ozawa). -/
def SAut5DeltaCert : Prop :=
  ∃ Lam : ℝ, 0 < Lam ∧ IsSOS (deltaSub 5 5 ^ 2 - Lam • deltaSub 5 5)

/-- `Adj_5 + 2·Op_5 − 0.278·Δ_5 ∈ Σ²` (the paper's `Adj5+2Op5`). -/
def SAut5Adj2OpCert : Prop :=
  ∃ mu : ℝ, 0 < mu ∧ IsSOS (AdjPair 5 5 + (2 : ℝ) • OpPair 5 5 - mu • deltaSub 5 5)

/-- `Adj_5 + 3·Op_5 − 1.37·Δ_5 ∈ Σ²` (the paper's `Adj5+3Op5`). -/
def SAut5Adj3OpCert : Prop :=
  ∃ mu : ℝ, 0 < mu ∧ IsSOS (AdjPair 5 5 + (3 : ℝ) • OpPair 5 5 - mu • deltaSub 5 5)

/-- The paper's `Adj5+3Op5` follows from its `Adj5+2Op5`: `Op_5 ∈ Σ²` (the
paper's `sq op sos`) and `Δ_5 ∈ Σ²` (equation (1)), and `Σ²` is closed under
addition and nonnegative scaling. -/
theorem SAut5Adj3OpCert_of_adj2Op (h : SAut5Adj2OpCert) : SAut5Adj3OpCert := by
  obtain ⟨mu, hmu, hcert⟩ := h
  refine ⟨mu, hmu, ?_⟩
  have hOp : IsSOS (OpPair 5 5) := isSOS_OpLap 5
  have hDel : IsSOS (deltaSub 5 5) := by
    rw [deltaSub_top]
    exact isSOS_laplacian (SAutGen 5) (sAutGen_symm 5)
  have h0 := hcert.add hOp
  have hid : AdjPair 5 5 + (2 : ℝ) • OpPair 5 5 - mu • deltaSub 5 5 + OpPair 5 5
      = AdjPair 5 5 + (3 : ℝ) • OpPair 5 5 - mu • deltaSub 5 5 := by
    module
  rwa [hid] at h0

/-! ## Interface with the literature's exact constants -/

/-- The literature's certified statement for `SAut(F_5)`: `Δ_5² − 1.2999·Δ_5 ∈ Σ²`. -/
theorem saut5DeltaCert_of (h : IsSOS (deltaSub 5 5 ^ 2 - (12999 / 10000 : ℝ) • deltaSub 5 5)) :
    SAut5DeltaCert :=
  ⟨12999 / 10000, by norm_num, h⟩

/-- The literature's certified statement for `SAut(F_5)`:
`Adj_5 + 2·Op_5 − 0.278·Δ_5 ∈ Σ²` (the paper's `Adj5+2Op5`). -/
theorem saut5Adj2OpCert_of
    (h : IsSOS (AdjPair 5 5 + (2 : ℝ) • OpPair 5 5 - (278 / 1000 : ℝ) • deltaSub 5 5)) :
    SAut5Adj2OpCert :=
  ⟨278 / 1000, by norm_num, h⟩

/-! ## The two routes -/

/-- **`n = 6`**: Method II, from the `Δ_5²` and `Adj_5 + 2·Op_5` certificates. -/
theorem propertyT_aut_of_cert6 (h1 : SAut5DeltaCert) (h2 : SAut5Adj2OpCert) :
    PropertyT (MulAut (FreeGroup (Fin 6))) := by
  obtain ⟨lam, hlam, hcert⟩ := h1
  obtain ⟨mu, hmu, h5⟩ := h2
  have hcert6 : IsSOS (deltaSub 6 (6 - 1) ^ 2 - lam • deltaSub 6 (6 - 1)) :=
    isSOS_extend_delta (by norm_num : 5 ≤ 6) hcert
  have h5' : IsSOS (AdjPair 6 5 + (2 : ℝ) • OpPair 6 5 - mu • deltaSub 6 5) :=
    isSOS_extend_adj (by norm_num : 5 ≤ 6) h5
  have hmain := methodII_cert 6 (by norm_num : 6 ≤ 6) 2 mu lam (by norm_num) (by norm_num)
    hlam (le_of_lt hmu) hcert6 h5'
  obtain ⟨ξ, hξ⟩ := hmain
  have hpos : 0 < (lam + mu / 3) / hCoef 6 :=
    div_pos (by linarith) (hCoef_pos 6 (by norm_num))
  refine Submission.Nielsen.propertyT_aut_of_sAutGen_certificate'' 6 ⟨0, by norm_num⟩ _ hpos ξ ?_
  rw [← deltaSub_top]
  exact hξ

/-- **`n ≥ 7`**: Method I, from the `Adj_5 + 2·Op_5` certificate. -/
theorem propertyT_aut_of_certI (h2 : SAut5Adj2OpCert) (n : ℕ) (hn : 7 ≤ n) :
    PropertyT (MulAut (FreeGroup (Fin n))) := by
  obtain ⟨mu, hmu, h2⟩ := h2
  refine propertyT_aut_of_methodI n 5 (by omega) (by norm_num) (by omega) 2 mu
    (by norm_num) hmu ?_ ?_
  · have : (7 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · exact isSOS_extend_adj (by omega : 5 ≤ n) h2

/-- **The reduction of `theorem_1` to the two `SAut(F_5)` certificates.** -/
theorem theorem_1_of_certificates (h1 : SAut5DeltaCert) (h2 : SAut5Adj2OpCert) :
    ∀ n : ℕ, 6 ≤ n → PropertyT (MulAut (FreeGroup (Fin n))) := by
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h
    exact propertyT_aut_of_cert6 h1 h2
  · exact propertyT_aut_of_certI h2 n (by omega)

/-- **`theorem_1` from the paper's own two computations**, stated with the
constants as they appear in the literature. -/
theorem theorem_1_of_paper_certificates
    (h1 : IsSOS (deltaSub 5 5 ^ 2 - (12999 / 10000 : ℝ) • deltaSub 5 5))
    (h2 : IsSOS (AdjPair 5 5 + (2 : ℝ) • OpPair 5 5 - (278 / 1000 : ℝ) • deltaSub 5 5)) :
    ∀ n : ℕ, 6 ≤ n → PropertyT (MulAut (FreeGroup (Fin n))) :=
  theorem_1_of_certificates (saut5DeltaCert_of h1) (saut5Adj2OpCert_of h2)

end Edge

end Submission.RouteB

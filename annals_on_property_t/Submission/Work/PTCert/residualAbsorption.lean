import Mathlib
import Submission.Work.PTCert.Chain
import Submission.Work.PTCert.orderUnitLemma

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions in `Submission/Work/PTCert/Chain.lean` (also Math.lean, Interfaces.lean).
Prove `ResidualAbsorption r`.  Use the proved `orderUnitLemma` (Submission/Work/PTCert/orderUnitLemma.lean:
`IsSOS ((2·len²) • Δ − (2•1 − of g − of g⁻¹))` for `g = lprod r ks`, all letters `< NB1 r`), with len ≤ 4 so
`32 • Δ − (2 − g − g⁻¹) ∈ Σ²` (add `(32 − 2 len²) • Δ`, and `Δ ∈ Σ²`: `Edge.isSOS_laplacian` + `deltaSub_top`,
see RouteB/Final.lean).  Also `2 − g − g⁻¹ = star(1−g)(1−g) ∈ Σ²`.  Write, using `Σ_t w t = 0`,
`c•Δ + Σ_t (w t/2)(g_t + g_t⁻¹) = (c − 16 Σ|w t|)•Δ + Σ_t [16|w t| • Δ − (w t/2)•(2 − g_t − g_t⁻¹)]`
and each bracket is `(w/2)•(32Δ − (2−g−g⁻¹))` if `w ≥ 0`, or `(|w|/2)•(32Δ + (2−g−g⁻¹))` if `w < 0`.
Close with `IsSOS.add`, `IsSOS.smul` (nonneg scalars), `IsSOS.finset_sum`. ~150 lines.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB Submission.RouteB.Edge
open scoped BigOperators

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-! ## Generic helpers -/

/-- `star x * x` is a sum of hermitian squares. -/
lemma isSOS_star_mul_self {A : Type*} [Ring A] [StarRing A] (x : A) :
    IsSOS (star x * x) :=
  ⟨{x}, by rw [Finset.sum_singleton]⟩

/-- In the group ring `ℝ[G]`, `2·1 - g - g⁻¹` is the hermitian square `star (1-g) * (1-g)`. -/
lemma two_smul_one_sub_of_sub_inv {G : Type*} [Group G] (g : G) :
    (2 : ℝ) • (1 : MonoidAlgebra ℝ G) - MonoidAlgebra.of ℝ G g - MonoidAlgebra.of ℝ G g⁻¹
      = star (1 - MonoidAlgebra.of ℝ G g) * (1 - MonoidAlgebra.of ℝ G g) := by
  have hgg : MonoidAlgebra.of ℝ G g⁻¹ * MonoidAlgebra.of ℝ G g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [two_smul ℝ (1 : MonoidAlgebra ℝ G)]
  rw [Submission.Helpers.star_sub, Submission.Helpers.star_one, Submission.Helpers.star_of,
    sub_mul, one_mul, mul_sub, mul_one, hgg]
  abel

/-- `2·1 - (g + g⁻¹) ∈ Σ²` in the group ring `ℝ[G]`. -/
lemma isSOS_two_smul_one_sub_add_inv {G : Type*} [Group G] (g : G) :
    IsSOS ((2 : ℝ) • (1 : MonoidAlgebra ℝ G)
      - (MonoidAlgebra.of ℝ G g + MonoidAlgebra.of ℝ G g⁻¹)) := by
  have hsq : (2 : ℝ) • (1 : MonoidAlgebra ℝ G)
      - (MonoidAlgebra.of ℝ G g + MonoidAlgebra.of ℝ G g⁻¹)
      = star (1 - MonoidAlgebra.of ℝ G g) * (1 - MonoidAlgebra.of ℝ G g) := by
    rw [← two_smul_one_sub_of_sub_inv g]
    abel
  rw [hsq]
  exact isSOS_star_mul_self (1 - MonoidAlgebra.of ℝ G g)

/-- **The residual absorption identity.**  If `Σ_t w t = 0` then, for any `Y : ι → A`,
`Δ : A`, `c : ℝ` in a real module `A`,
`c • Δ + Σ_t (w t / 2) • Y t = (c - 16 · Σ_t |w t|) • Δ + Σ_t (16·|w t| • Δ - (w t/2) • (2•1 - Y t))`. -/
lemma absorb_identity {A : Type*} [AddCommGroup A] [Module ℝ A] [One A]
    {ι : Type*} (I : Finset ι) (w : ι → ℝ) (Y : ι → A) (Δ : A) (c : ℝ)
    (hsum : ∑ t ∈ I, w t = 0) :
    c • Δ + ∑ t ∈ I, (w t / 2) • Y t
      = (c - 16 * (∑ t ∈ I, |w t|)) • Δ
        + ∑ t ∈ I, ((16 * |w t|) • Δ - (w t / 2) • ((2 : ℝ) • (1 : A) - Y t)) := by
  have h16 : (∑ t ∈ I, (16 * |w t|) • Δ) = (16 * ∑ t ∈ I, |w t|) • Δ := by
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.mul_sum]
  have hsub : (∑ t ∈ I, (w t / 2) • ((2 : ℝ) • (1 : A) - Y t))
      = (∑ t ∈ I, w t) • (1 : A) - ∑ t ∈ I, (w t / 2) • Y t := by
    have h1 : (∑ t ∈ I, (w t / 2) • ((2 : ℝ) • (1 : A) - Y t))
        = ∑ t ∈ I, ((w t / 2) • ((2 : ℝ) • (1 : A)) - (w t / 2) • Y t) :=
      Finset.sum_congr rfl (fun t _ => smul_sub _ _ _)
    rw [h1, Finset.sum_sub_distrib]
    have hfirst : (∑ t ∈ I, (w t / 2) • ((2 : ℝ) • (1 : A))) = (∑ t ∈ I, w t) • (1 : A) := by
      have hpt : ∀ t ∈ I, (w t / 2) • ((2 : ℝ) • (1 : A)) = w t • (1 : A) := by
        intro t _
        rw [smul_smul]
        congr 1
        ring
      rw [Finset.sum_congr rfl hpt, ← Finset.sum_smul]
    rw [hfirst]
  rw [Finset.sum_sub_distrib, h16, hsub, hsum, zero_smul, zero_sub, sub_smul]
  abel

/-- The order-unit lemma in the `g + g⁻¹` form (matching `2•1 - (of g + of g⁻¹)`). -/
lemma orderUnitLemma' (r : ℕ) (ks : List ℕ) (hks : ∀ k ∈ ks, k < NB1 r) :
    IsSOS (((2 * ks.length ^ 2 : ℕ) : ℝ) • Edge.deltaSub r r
      - ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
          - (MonoidAlgebra.of ℝ _ (lprod r ks) + MonoidAlgebra.of ℝ _ (lprod r ks)⁻¹))) := by
  have h := orderUnitLemma r ks hks
  have heq : (((2 * ks.length ^ 2 : ℕ) : ℝ) • Edge.deltaSub r r
      - ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
          - MonoidAlgebra.of ℝ _ (lprod r ks) - MonoidAlgebra.of ℝ _ (lprod r ks)⁻¹))
      = (((2 * ks.length ^ 2 : ℕ) : ℝ) • Edge.deltaSub r r
        - ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
            - (MonoidAlgebra.of ℝ _ (lprod r ks) + MonoidAlgebra.of ℝ _ (lprod r ks)⁻¹))) := by
    rw [sub_add_eq_sub_sub]
  rwa [heq] at h

/-- `Δ = deltaSub r r = Laplacian (SAutGen r) ∈ Σ²`. -/
lemma isSOS_deltaSub (r : ℕ) : IsSOS (Edge.deltaSub r r) := by
  rw [Edge.deltaSub_top]
  exact Edge.isSOS_laplacian (SAutGen r) (sAutGen_symm r)

theorem residualAbsorption (r : ℕ) : ResidualAbsorption r := by
  intro τ I ks w c hks hsum hc
  classical
  have hΔSOS : IsSOS (Edge.deltaSub r r) := isSOS_deltaSub r
  have houter : IsSOS ((c - 16 * ∑ t ∈ I, |w t|) • Edge.deltaSub r r) :=
    IsSOS.smul (by linarith) hΔSOS
  have hstep : ∀ t ∈ I, IsSOS ((16 * |w t|) • Edge.deltaSub r r
      - (w t / 2) • ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
          - (MonoidAlgebra.of ℝ _ (lprod r (ks t)) + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹))) := by
    intro t ht
    obtain ⟨hlen, hlt⟩ := hks t ht
    set X : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))) :=
      (2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
        - (MonoidAlgebra.of ℝ _ (lprod r (ks t)) + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹) with hX
    have hC : (0 : ℝ) ≤ 32 - ((2 * (ks t).length ^ 2 : ℕ) : ℝ) := by
      have h2 : (ks t).length ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hlen 2
      have h5 : (2 * (ks t).length ^ 2 : ℕ) ≤ 32 := by
        calc 2 * (ks t).length ^ 2 ≤ 2 * 4 ^ 2 := Nat.mul_le_mul_left 2 h2
          _ = 32 := by norm_num
      have h6 : ((2 * (ks t).length ^ 2 : ℕ) : ℝ) ≤ 32 := by exact_mod_cast h5
      linarith
    have houl : IsSOS (((2 * (ks t).length ^ 2 : ℕ) : ℝ) • Edge.deltaSub r r - X) :=
      orderUnitLemma' r (ks t) hlt
    have hYsos : IsSOS X := isSOS_two_smul_one_sub_add_inv (lprod r (ks t))
    have h32 : IsSOS ((32 : ℝ) • Edge.deltaSub r r - X) := by
      have h1 : IsSOS (((32 : ℝ) - ((2 * (ks t).length ^ 2 : ℕ) : ℝ)) • Edge.deltaSub r r) :=
        IsSOS.smul hC hΔSOS
      have h3 := h1.add houl
      have heq : ((32 : ℝ) - ((2 * (ks t).length ^ 2 : ℕ) : ℝ)) • Edge.deltaSub r r
          + (((2 * (ks t).length ^ 2 : ℕ) : ℝ) • Edge.deltaSub r r - X)
          = (32 : ℝ) • Edge.deltaSub r r - X := by
        rw [sub_smul]
        abel
      rwa [heq] at h3
    by_cases hw : 0 ≤ w t
    · have hcoef : (0 : ℝ) ≤ w t / 2 := by linarith
      have key : (16 * |w t|) • Edge.deltaSub r r - (w t / 2) • X
          = (w t / 2) • ((32 : ℝ) • Edge.deltaSub r r - X) := by
        conv_lhs => rw [abs_of_nonneg hw, show (16 : ℝ) * w t = w t / 2 * 32 by ring]
        conv_rhs => rw [smul_sub, smul_smul]
      rw [key]
      exact IsSOS.smul hcoef h32
    · have hw' : w t < 0 := lt_of_not_ge hw
      have hcoef : (0 : ℝ) ≤ |w t| / 2 := by positivity
      have h32pos : IsSOS ((32 : ℝ) • Edge.deltaSub r r + X) :=
        (IsSOS.smul (by norm_num : (0 : ℝ) ≤ 32) hΔSOS).add hYsos
      have key : (16 * |w t|) • Edge.deltaSub r r - (w t / 2) • X
          = (|w t| / 2) • ((32 : ℝ) • Edge.deltaSub r r + X) := by
        conv_lhs => rw [show (16 : ℝ) * |w t| = |w t| / 2 * 32 by ring,
          show w t / 2 = -(|w t| / 2) by rw [abs_of_neg hw']; ring,
          neg_smul, sub_neg_eq_add]
        conv_rhs => rw [smul_add, smul_smul]
      rw [key]
      exact IsSOS.smul hcoef h32pos
  have hinner : IsSOS (∑ t ∈ I, ((16 * |w t|) • Edge.deltaSub r r
      - (w t / 2) • ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
          - (MonoidAlgebra.of ℝ _ (lprod r (ks t)) + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹)))) :=
    IsSOS.finset_sum I hstep
  have hgoal : c • Edge.deltaSub r r
      + ∑ t ∈ I, (w t / 2) • (MonoidAlgebra.of ℝ _ (lprod r (ks t))
          + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹)
      = (c - 16 * ∑ t ∈ I, |w t|) • Edge.deltaSub r r
        + ∑ t ∈ I, ((16 * |w t|) • Edge.deltaSub r r - (w t / 2) •
            ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
              - (MonoidAlgebra.of ℝ _ (lprod r (ks t)) + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹))) :=
    absorb_identity I w
      (fun t => MonoidAlgebra.of ℝ _ (lprod r (ks t)) + MonoidAlgebra.of ℝ _ (lprod r (ks t))⁻¹)
      (Edge.deltaSub r r) c hsum
  rw [hgoal]
  exact houter.add hinner

end Work.PTCert

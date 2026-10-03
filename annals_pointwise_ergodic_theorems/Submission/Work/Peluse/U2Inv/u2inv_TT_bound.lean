import Mathlib
import Submission.Work.Peluse.U2Inv.Defs
import Submission.Work.Peluse.U2Inv.u2inv_dft_plancherel

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-!
## Auxiliary Fourier identities for `u2inv_TT_bound`

The point of the file is the `U²`-inverse bound `u2inv_TT_bound`: if all Fourier coefficients of a
function `F` on `ZMod (Gmod L)` are bounded by `η`, then the twisted `U²` quantity `TT` is bounded
by `η² (∑_x ‖F x‖²) / (Gmod L)³`.

The proof has two ingredients:

* the exact Fourier expansion of `TT`, i.e. the quadruple correlation identity
  `TT L k₁ k₂ F = N⁻⁴ ∑_ξ dft F (ξ+k₁+k₂) conj (dft F (ξ+k₁)) conj (dft F (ξ+k₂)) dft F ξ`
  (proved below as `TTB.quadrFourier` by applying the orthogonality of the additive characters
  of `ZMod N` to the three summation variables `x, a, b`);
* Plancherel's identity `∑_ξ ‖dft F ξ‖² = N ∑_x ‖F x‖²` (a colleague's module
  `u2inv_dft_plancherel`) together with the AM–GM inequality, which turns the four Fourier
  coefficients into `η² ∑_ξ ‖dft F ξ‖²`.
-/

/- Auxiliary lemmas: the Fourier toolkit on `ZMod N` and the quadruple correlation identity. -/
namespace TTB

variable {N : ℕ} [NeZero N]

  lemma star_chi (x : ZMod N) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    rw [show star (ZMod.stdAddChar x) = (ZMod.stdAddChar x)⁻¹ from
        (Complex.inv_eq_conj (by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _)).symm,
      ← AddChar.map_neg_eq_inv]

  lemma dft_expand' (Φ : ZMod N → ℂ) (k : ZMod N) :
      ZMod.dft Φ k = ∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) * Φ j := by
    rw [ZMod.dft_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul]

  lemma dft_inversion (Φ : ZMod N → ℂ) (k : ZMod N) :
      Φ k = ((N : ℂ))⁻¹ * ∑ j : ZMod N, ZMod.stdAddChar (j * k) * ZMod.dft Φ j := by
    have h := ZMod.invDFT_apply (N := N) (ZMod.dft Φ) k
    rw [LinearEquiv.symm_apply_apply] at h
    simpa [smul_eq_mul] using h

  lemma star_dft_pairing (Φ : ZMod N → ℂ) (θ : ZMod N) :
      ∑ y : ZMod N, star (Φ y) * ZMod.stdAddChar (y * θ) = star (ZMod.dft Φ θ) := by
    rw [dft_expand', star_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul, star_chi, neg_neg]

  lemma chi_split (u v x θ : ZMod N) :
      ZMod.stdAddChar ((u + v - x) * θ)
        = ZMod.stdAddChar (u * θ) * (ZMod.stdAddChar (v * θ) * ZMod.stdAddChar (-(x * θ))) := by
    rw [show (u + v - x) * θ = u * θ + (v * θ + -(x * θ)) by ring,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

  lemma chi_split_sub (x k₁ k₂ θ : ZMod N) :
      ZMod.stdAddChar (-(x * (θ + k₁ + k₂)))
        = ZMod.stdAddChar (-(x * k₁)) *
            (ZMod.stdAddChar (-(x * k₂)) * ZMod.stdAddChar (-(x * θ))) := by
    rw [show -(x * (θ + k₁ + k₂)) = -(x * k₁) + (-(x * k₂) + -(x * θ)) by ring,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

  /-- Factorisation of a triple sum of a product into a product of sums. -/
  lemma factor3 (P Q R : ZMod N → ℂ) (c : ℂ) :
      (∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, P u * Q v * R x * c)
        = (∑ u : ZMod N, P u) * (∑ v : ZMod N, Q v) * (∑ x : ZMod N, R x) * c := by
    have hA : (∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, P u * Q v * R x * c)
        = ∑ u : ZMod N, ∑ v : ZMod N, (P u * Q v) * (∑ x : ZMod N, R x * c) := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [show (∑ x : ZMod N, P u * Q v * R x * c) = ∑ x : ZMod N, (P u * Q v) * (R x * c) from
        Finset.sum_congr rfl fun x _ => by ring]
      rw [← Finset.mul_sum]
    rw [hA]
    have hB : (∑ u : ZMod N, ∑ v : ZMod N, (P u * Q v) * (∑ x : ZMod N, R x * c))
        = (∑ u : ZMod N, P u) * (∑ v : ZMod N, Q v) * (∑ x : ZMod N, R x * c) := by
      calc ∑ u : ZMod N, ∑ v : ZMod N, (P u * Q v) * (∑ x : ZMod N, R x * c)
          = ∑ u : ZMod N, (∑ v : ZMod N, P u * Q v) * (∑ x : ZMod N, R x * c) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← Finset.sum_mul]
        _ = (∑ u : ZMod N, ∑ v : ZMod N, P u * Q v) * (∑ x : ZMod N, R x * c) := by
              rw [← Finset.sum_mul]
        _ = ((∑ u : ZMod N, P u) * (∑ v : ZMod N, Q v)) * (∑ x : ZMod N, R x * c) := by
              rw [← Finset.sum_mul_sum]
    rw [hB]
    have hC : (∑ x : ZMod N, R x * c) = (∑ x : ZMod N, R x) * c := (Finset.sum_mul ..).symm
    rw [hC]
    ring

  noncomputable section

  /-- The term `T1`, the (reindexed) summand of the left-hand side. -/
  private def T1 (A B C D : ZMod N → ℂ) (k₁ k₂ x u v : ZMod N) : ℂ :=
    (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) * C (u + v - x) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)))

  /-- The term `T2`, the summand of the (expanded) right-hand side. -/
  private def T2 (A B C D : ZMod N → ℂ) (k₁ k₂ θ x u v : ZMod N) : ℂ :=
    (star (A u) * ZMod.stdAddChar (u * k₁) * ZMod.stdAddChar (u * θ)) * (star (B v) * ZMod.stdAddChar (v * k₂) * ZMod.stdAddChar (v * θ)) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)) * ZMod.stdAddChar (-(x * θ))) * ZMod.dft C θ

  theorem quadrFourier (A B C D : ZMod N → ℂ) (k₁ k₂ : ZMod N) :
      (∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N, star (A (x + a)) * star (B (x + b)) * C (x + a + b) * D x * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂))
        = ((N : ℂ))⁻¹ * ∑ ξ : ZMod N, star (ZMod.dft A (ξ + k₁)) * star (ZMod.dft B (ξ + k₂)) * ZMod.dft C ξ * ZMod.dft D (ξ + k₁ + k₂) := by
    have h1 : (∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N, star (A (x + a)) * star (B (x + b)) * C (x + a + b) * D x * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)) = ∑ x : ZMod N, ∑ u : ZMod N, ∑ b : ZMod N, star (A u) * star (B (x + b)) * C (u + b) * D x * ZMod.stdAddChar ((u - x) * k₁) * ZMod.stdAddChar (b * k₂) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun a => ?_)
      rw [Equiv.coe_addLeft, show x + a - x = a by ring]
    have h2 : (∑ x : ZMod N, ∑ u : ZMod N, ∑ b : ZMod N, star (A u) * star (B (x + b)) * C (u + b) * D x * ZMod.stdAddChar ((u - x) * k₁) * ZMod.stdAddChar (b * k₂)) = ∑ x : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, star (A u) * star (B v) * C (u + (v - x)) * D x * ZMod.stdAddChar ((u - x) * k₁) * ZMod.stdAddChar ((v - x) * k₂) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun b => ?_)
      rw [Equiv.coe_addLeft, show x + b - x = b by ring]
    have h3 : (∑ x : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, star (A u) * star (B v) * C (u + (v - x)) * D x * ZMod.stdAddChar ((u - x) * k₁) * ZMod.stdAddChar ((v - x) * k₂)) = ∑ x : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) * C (u + v - x) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂))) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ =>
        Finset.sum_congr rfl fun v _ => ?_
      rw [show C (u + (v - x)) = C (u + v - x) by congr 1; ring,
        show ZMod.stdAddChar ((u - x) * k₁) = ZMod.stdAddChar (u * k₁) * ZMod.stdAddChar (-(x * k₁)) by
          rw [show (u - x) * k₁ = u * k₁ + -(x * k₁) by ring, AddChar.map_add_eq_mul],
        show ZMod.stdAddChar ((v - x) * k₂) = ZMod.stdAddChar (v * k₂) * ZMod.stdAddChar (-(x * k₂)) by
          rw [show (v - x) * k₂ = v * k₂ + -(x * k₂) by ring, AddChar.map_add_eq_mul]]
      ring
    have h4 : (∑ x : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) * C (u + v - x) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)))) = ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, T1 A B C D k₁ k₂ x u v := by
      simp only [T1]
      calc ∑ x : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) * C (u + v - x) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)))
          = ∑ u : ZMod N, ∑ x : ZMod N, ∑ v : ZMod N, (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) * C (u + v - x) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂))) := Finset.sum_comm
        _ = ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) * C (u + v - x) * (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂))) := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
    have h5 : ∀ x u v : ZMod N, T1 A B C D k₁ k₂ x u v
        = (N : ℂ)⁻¹ * ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v := by
      intro x u v
      simp only [T1, T2]
      rw [dft_inversion C (u + v - x)]
      rw [show (star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) *
            ((N : ℂ)⁻¹ * ∑ j : ZMod N, ZMod.stdAddChar (j * (u + v - x)) * ZMod.dft C j) *
            (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)))
          = (N : ℂ)⁻¹ * ((star (A u) * ZMod.stdAddChar (u * k₁)) * (star (B v) * ZMod.stdAddChar (v * k₂)) *
              (∑ j : ZMod N, ZMod.stdAddChar (j * (u + v - x)) * ZMod.dft C j) *
              (D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)))) from by ring]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [show θ * (u + v - x) = (u + v - x) * θ by ring, chi_split u v x θ]
      ring
    have h6 : (∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, T1 A B C D k₁ k₂ x u v) = ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, (N : ℂ)⁻¹ * ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun x _ => h5 x u v
    have h7 : (∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, (N : ℂ)⁻¹ * ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v) = (N : ℂ)⁻¹ * ∑ θ : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, T2 A B C D k₁ k₂ θ x u v := by
      have hA : (∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, (N : ℂ)⁻¹ * ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v)
          = ∑ u : ZMod N, ∑ v : ZMod N, (N : ℂ)⁻¹ * (∑ x : ZMod N, ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum]
      rw [hA]
      have hB : (∑ u : ZMod N, ∑ v : ZMod N, (N : ℂ)⁻¹ * (∑ x : ZMod N, ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v))
          = ∑ u : ZMod N, (N : ℂ)⁻¹ * (∑ v : ZMod N, ∑ x : ZMod N, ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.mul_sum]
      rw [hB]
      have hC : (∑ u : ZMod N, (N : ℂ)⁻¹ * (∑ v : ZMod N, ∑ x : ZMod N, ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v))
          = (N : ℂ)⁻¹ * (∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v) := by
        rw [← Finset.mul_sum]
      rw [hC]
      congr 1
      calc ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, ∑ θ : ZMod N, T2 A B C D k₁ k₂ θ x u v
          = ∑ u : ZMod N, ∑ v : ZMod N, ∑ θ : ZMod N, ∑ x : ZMod N, T2 A B C D k₁ k₂ θ x u v := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_comm
        _ = ∑ u : ZMod N, ∑ θ : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, T2 A B C D k₁ k₂ θ x u v := by
              refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ θ : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, T2 A B C D k₁ k₂ θ x u v := Finset.sum_comm
    have hFA : ∀ θ : ZMod N,
        (∑ u : ZMod N, star (A u) * ZMod.stdAddChar (u * k₁) * ZMod.stdAddChar (u * θ)) = star (ZMod.dft A (θ + k₁)) := by
      intro θ
      rw [← star_dft_pairing A (θ + k₁)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [show ZMod.stdAddChar (u * (θ + k₁)) = ZMod.stdAddChar (u * k₁) * ZMod.stdAddChar (u * θ) by
        rw [show u * (θ + k₁) = u * k₁ + u * θ by ring, AddChar.map_add_eq_mul]]
      ring
    have hFB : ∀ θ : ZMod N,
        (∑ v : ZMod N, star (B v) * ZMod.stdAddChar (v * k₂) * ZMod.stdAddChar (v * θ)) = star (ZMod.dft B (θ + k₂)) := by
      intro θ
      rw [← star_dft_pairing B (θ + k₂)]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [show ZMod.stdAddChar (v * (θ + k₂)) = ZMod.stdAddChar (v * k₂) * ZMod.stdAddChar (v * θ) by
        rw [show v * (θ + k₂) = v * k₂ + v * θ by ring, AddChar.map_add_eq_mul]]
      ring
    have hFD : ∀ θ : ZMod N,
        (∑ x : ZMod N, D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)) * ZMod.stdAddChar (-(x * θ)))
          = ZMod.dft D (θ + k₁ + k₂) := by
      intro θ
      rw [dft_expand' D (θ + k₁ + k₂)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_split_sub x k₁ k₂ θ]
      ring
    have h8 : ((N : ℂ)⁻¹ * ∑ θ : ZMod N, ∑ u : ZMod N, ∑ v : ZMod N, ∑ x : ZMod N, T2 A B C D k₁ k₂ θ x u v) = (N : ℂ)⁻¹ * ∑ θ : ZMod N, star (ZMod.dft A (θ + k₁)) * star (ZMod.dft B (θ + k₂)) * ZMod.dft D (θ + k₁ + k₂) * ZMod.dft C θ := by
      congr 1
      refine Finset.sum_congr rfl fun θ _ => ?_
      simp only [T2]
      rw [factor3 (fun u : ZMod N => star (A u) * ZMod.stdAddChar (u * k₁) * ZMod.stdAddChar (u * θ)) (fun v : ZMod N => star (B v) * ZMod.stdAddChar (v * k₂) * ZMod.stdAddChar (v * θ)) (fun x : ZMod N => D x * ZMod.stdAddChar (-(x * k₁)) * ZMod.stdAddChar (-(x * k₂)) * ZMod.stdAddChar (-(x * θ))) (ZMod.dft C θ)]
      rw [hFA θ, hFB θ, hFD θ]
    have h9 : ((N : ℂ)⁻¹ * ∑ θ : ZMod N, star (ZMod.dft A (θ + k₁)) * star (ZMod.dft B (θ + k₂)) * ZMod.dft D (θ + k₁ + k₂) * ZMod.dft C θ) = ((N : ℂ))⁻¹ * ∑ ξ : ZMod N, star (ZMod.dft A (ξ + k₁)) * star (ZMod.dft B (ξ + k₂)) * ZMod.dft C ξ * ZMod.dft D (ξ + k₁ + k₂) := by
      congr 1
      refine Finset.sum_congr rfl fun θ _ => ?_
      ring
    exact h1.trans (h2.trans (h3.trans (h4.trans (h6.trans (h7.trans (h8.trans h9))))))

  end

end TTB

variable {N : ℕ} [NeZero N]

  /-- Shifting the frequency variable does not change the sum of the squared moduli of the
    discrete Fourier transform. -/
    lemma u2inv_TT_bound_shift (F : ZMod N → ℂ) (k : ZMod N) :
        (∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k)‖ ^ 2) = ∑ ξ : ZMod N, ‖ZMod.dft F ξ‖ ^ 2 :=
      Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun ξ => by rw [Equiv.coe_addLeft, add_comm])

    /-- The Fourier expression of the twisted `U²` quantity `TT`: a single sum over the frequency
    variable of a product of four Fourier coefficients.  (This is the `U²`-inverse identity: the
    `x`-sum and the two shift sums are evaluations of the orthogonality of the additive
    characters of `ZMod (Gmod L)`.) -/
    lemma u2inv_TT_bound_TT_eq_dft (L : ℕ) (k₁ k₂ : ZMod (Gmod L)) (F : ZMod (Gmod L) → ℂ) :
        TT L k₁ k₂ F = (((Gmod L : ℂ)) ^ 4)⁻¹ * ∑ ξ : ZMod (Gmod L),
          star (ZMod.dft F (ξ + k₁)) * star (ZMod.dft F (ξ + k₂)) *
            ZMod.dft F ξ * ZMod.dft F (ξ + k₁ + k₂) := by
      have hmain : (∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
            DeltaG a b F x * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂))
          = ((Gmod L : ℂ))⁻¹ * ∑ ξ : ZMod (Gmod L),
              star (ZMod.dft F (ξ + k₁)) * star (ZMod.dft F (ξ + k₂)) *
                ZMod.dft F ξ * ZMod.dft F (ξ + k₁ + k₂) := by
        simpa only [DeltaG] using TTB.quadrFourier (N := Gmod L) F F F F k₁ k₂
      rw [TT, hmain, ← mul_assoc, ← mul_inv,
        show (Gmod L : ℂ) ^ 3 * (Gmod L : ℂ) = (Gmod L : ℂ) ^ 4 by ring]

    /-- Norm bound for the frequency sum of `u2inv_TT_bound_TT_eq_dft`: the four Fourier
    coefficients are estimated by `η` at the two "free" places and by Cauchy–Schwarz (AM–GM)
    at the two remaining ones, and Plancherel converts the frequency energy into the `ℓ²` mass
    of `F`. -/
    lemma u2inv_TT_bound_sum_le (F : ZMod N → ℂ) (k₁ k₂ : ZMod N) (η : ℝ)
        (hη : ∀ ξ : ZMod N, ‖ZMod.dft F ξ‖ ≤ η) (hη0 : 0 ≤ η) :
        ‖∑ ξ : ZMod N, star (ZMod.dft F (ξ + k₁)) * star (ZMod.dft F (ξ + k₂)) *
            ZMod.dft F ξ * ZMod.dft F (ξ + k₁ + k₂)‖
          ≤ η ^ 2 * ((N : ℝ) * ∑ x : ZMod N, ‖F x‖ ^ 2) := by
      set A : ℝ := ∑ ξ : ZMod N, ‖ZMod.dft F ξ‖ ^ 2 with hA
      have hshift₁ : (∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ ^ 2) = A := u2inv_TT_bound_shift F k₁
      have hshift₂ : (∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₂)‖ ^ 2) = A := u2inv_TT_bound_shift F k₂
      have hplan : A = (N : ℝ) * ∑ x : ZMod N, ‖F x‖ ^ 2 := u2inv_dft_plancherel N F
      calc ‖∑ ξ : ZMod N, star (ZMod.dft F (ξ + k₁)) * star (ZMod.dft F (ξ + k₂)) *
              ZMod.dft F ξ * ZMod.dft F (ξ + k₁ + k₂)‖
          ≤ ∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖ *
              ‖ZMod.dft F ξ‖ * ‖ZMod.dft F (ξ + k₁ + k₂)‖ := by
            refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ξ _ => ?_)
            simp only [norm_mul, norm_star]
            exact le_refl _
        _ ≤ ∑ ξ : ZMod N, η * η *
              (‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖) := by
            refine Finset.sum_le_sum fun ξ _ => ?_
            have h1 : ‖ZMod.dft F ξ‖ ≤ η := hη ξ
            have h2 : ‖ZMod.dft F (ξ + k₁ + k₂)‖ ≤ η := hη (ξ + k₁ + k₂)
            have ha : 0 ≤ ‖ZMod.dft F (ξ + k₁)‖ := norm_nonneg _
            have hb : 0 ≤ ‖ZMod.dft F (ξ + k₂)‖ := norm_nonneg _
            have hcd : ‖ZMod.dft F ξ‖ * ‖ZMod.dft F (ξ + k₁ + k₂)‖ ≤ η * η :=
              mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
            calc ‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖ * ‖ZMod.dft F ξ‖ *
                  ‖ZMod.dft F (ξ + k₁ + k₂)‖
                = (‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖) *
                    (‖ZMod.dft F ξ‖ * ‖ZMod.dft F (ξ + k₁ + k₂)‖) := by ring
              _ ≤ (‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖) * (η * η) :=
                  mul_le_mul_of_nonneg_left hcd (mul_nonneg ha hb)
              _ = η * η * (‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖) := by ring
        _ = η ^ 2 * ∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖ := by
            rw [show η * η = η ^ 2 by ring, Finset.mul_sum]
        _ ≤ η ^ 2 * A := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hη0 2)
            have h1 : ∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖
                ≤ ∑ ξ : ZMod N,
                    (‖ZMod.dft F (ξ + k₁)‖ ^ 2 + ‖ZMod.dft F (ξ + k₂)‖ ^ 2) / 2 := by
              refine Finset.sum_le_sum fun ξ _ => ?_
              nlinarith [sq_nonneg (‖ZMod.dft F (ξ + k₁)‖ - ‖ZMod.dft F (ξ + k₂)‖)]
            have h2 : (∑ ξ : ZMod N,
                  (‖ZMod.dft F (ξ + k₁)‖ ^ 2 + ‖ZMod.dft F (ξ + k₂)‖ ^ 2) / 2)
                = ((∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ ^ 2) +
                    (∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₂)‖ ^ 2)) / 2 := by
              rw [← Finset.sum_div, Finset.sum_add_distrib]
            calc ∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ * ‖ZMod.dft F (ξ + k₂)‖
                ≤ ∑ ξ : ZMod N,
                    (‖ZMod.dft F (ξ + k₁)‖ ^ 2 + ‖ZMod.dft F (ξ + k₂)‖ ^ 2) / 2 := h1
              _ = ((∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₁)‖ ^ 2) +
                    (∑ ξ : ZMod N, ‖ZMod.dft F (ξ + k₂)‖ ^ 2)) / 2 := h2
              _ = A := by rw [hshift₁, hshift₂]; ring
        _ = η ^ 2 * ((N : ℝ) * ∑ x : ZMod N, ‖F x‖ ^ 2) := by rw [hplan]

    /-- The arithmetic of the final step: dividing by the fourth power and multiplying back by the
    group order. -/
    lemma u2inv_TT_bound_arith (L : ℕ) (Z : ℂ) (η S : ℝ)
        (hZ : ‖Z‖ ≤ η ^ 2 * ((Gmod L : ℝ) * S)) :
        ‖(((Gmod L : ℂ)) ^ 4)⁻¹ * Z‖ ≤ η ^ 2 * S / ((Gmod L : ℝ) ^ 3) := by
      have hpos : (0 : ℝ) < (Gmod L : ℝ) := by
        have : (0 : ℕ) < Gmod L := by simp [Gmod]
        exact_mod_cast this
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      calc ((Gmod L : ℝ) ^ 4)⁻¹ * ‖Z‖
          ≤ ((Gmod L : ℝ) ^ 4)⁻¹ * (η ^ 2 * ((Gmod L : ℝ) * S)) :=
            mul_le_mul_of_nonneg_left hZ (by positivity)
        _ = η ^ 2 * S / ((Gmod L : ℝ) ^ 3) := by
            have hN : (Gmod L : ℝ) ≠ 0 := ne_of_gt hpos
            rw [div_eq_mul_inv]
            field_simp

    theorem u2inv_TT_bound (L : ℕ) (k₁ k₂ : ZMod (Work.Peluse.U2Inv.Gmod L))
        (F : ZMod (Work.Peluse.U2Inv.Gmod L) → ℂ) (η : ℝ)
        (hη : ∀ ξ : ZMod (Work.Peluse.U2Inv.Gmod L), ‖ZMod.dft F ξ‖ ≤ η) (hη0 : 0 ≤ η) :
        ‖Work.Peluse.U2Inv.TT L k₁ k₂ F‖ ≤
          η ^ 2 * (∑ x : ZMod (Work.Peluse.U2Inv.Gmod L), ‖F x‖ ^ 2) /
            ((Work.Peluse.U2Inv.Gmod L : ℝ) ^ 3) := by
      rw [u2inv_TT_bound_TT_eq_dft L k₁ k₂ F]
      exact u2inv_TT_bound_arith L _ η _ (u2inv_TT_bound_sum_le F k₁ k₂ η hη hη0)

end

end Work.Peluse.U2Inv

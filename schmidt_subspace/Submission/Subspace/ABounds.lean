import Mathlib
import Submission.Subspace.UBounds
import Submission.Subspace.PderivDivBounds
import Submission.Commons.Algebra.MvPolynomial.pderivIter_aeval_linForm_support_ring
import Submission.Commons.Algebra.MvPolynomial.norm_aeval_lt_one
import Submission.Commons.Algebra.MvPolynomial.isBlockHom_aeval_PhiL
import Submission.Commons.Algebra.MvPolynomial.index_properties_pos_vanishing
import Submission.Commons.Algebra.MvPolynomial.coeff_aeval_linForm_le
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter_norm_le
import Submission.Commons.Algebra.MvPolynomial.card_support_block_le
import Submission.Commons.Algebra.MvPolynomial.blockDiag_aeval_degree_le

/-!
# Step E: the `A`-bounds

This file proves the final step of the maximal-rank part of the subspace theorem: the
contradiction obtained by evaluating a derivative of the auxiliary polynomial once in the
*small* `U`-coordinates `u (h,k) = L_k(x_h)` (using the flatness window coming from Siegel, via
`norm_aeval_lt_one`) and once in the *integral* coordinates `x ∈ ℤ^{mN}` (using integrality).

The main result is `Submission.Subspace.A_bounds_core`.
-/

set_option maxHeartbeats 1600000

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {m N : ℕ}


/-- The block-diagonal matrix of the substitution `PhiL Λ`. -/
noncomputable def blkSub {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R) :
    Fin m × Fin N → Fin m × Fin N → R :=
  fun x y => if x.1 = y.1 then Λ y.2 x.2 else 0

/-- The inverse of `blkSub Λ`. -/
noncomputable def blkInv {R : Type*} [CommSemiring R] (Λi : Matrix (Fin N) (Fin N) R) :
    Fin m × Fin N → Fin m × Fin N → R :=
  fun x y => if x.1 = y.1 then Λi y.2 x.2 else 0

theorem blkSub_apply_eq {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R)
    (h : Fin m) (j k : Fin N) : blkSub Λ (h, j) (h, k) = Λ k j := by
  rw [blkSub]; exact if_pos rfl

theorem blkSub_eq_zero {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R)
    {h h' : Fin m} (hne : h ≠ h') (j k : Fin N) : blkSub Λ (h, j) (h', k) = 0 := by
  rw [blkSub]; exact if_neg hne

theorem blkSub_ne_zero {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R)
    {x y : Fin m × Fin N} (h : blkSub Λ x y ≠ 0) : y.1 = x.1 := by
  by_contra hh
  exact h (by rw [blkSub]; exact if_neg (fun hc => hh hc.symm))

theorem blkInv_apply_eq {R : Type*} [CommSemiring R] (Λi : Matrix (Fin N) (Fin N) R)
    (h : Fin m) (j k : Fin N) : blkInv Λi (h, k) (h, j) = Λi j k := by
  rw [blkInv]; exact if_pos rfl

theorem blkInv_eq_zero {R : Type*} [CommSemiring R] (Λi : Matrix (Fin N) (Fin N) R)
    {h h' : Fin m} (hne : h ≠ h') (j k : Fin N) : blkInv Λi (h, k) (h', j) = 0 := by
  rw [blkInv]; exact if_neg hne

theorem blkSub_eq_PhiL {R : Type*} [CommSemiring R] (Λ : Matrix (Fin N) (Fin N) R) :
    (fun x : Fin m × Fin N => ∑ y, MvPolynomial.C (blkSub Λ x y) * MvPolynomial.X y)
      = (PhiL Λ : Fin m × Fin N → MvPolynomial (Fin m × Fin N) R) := by
  funext x
  obtain ⟨h, j⟩ := x
  rw [PhiL, Fintype.sum_prod_type, Finset.sum_eq_single h]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [blkSub_apply_eq]
  · intro h' _ hne
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [blkSub_eq_zero Λ (Ne.symm hne) j k, MvPolynomial.C_0, zero_mul]
  · intro hnot; exact absurd (Finset.mem_univ h) hnot

theorem blkInv_mul_blkSub {R : Type*} [CommSemiring R] (Λ Λi : Matrix (Fin N) (Fin N) R)
    (hΛi : Λi * Λ = 1) (x x' : Fin m × Fin N) :
    ∑ y, blkInv Λi y x * blkSub Λ x' y = if x = x' then 1 else 0 := by
  obtain ⟨h, j⟩ := x
  obtain ⟨h', j'⟩ := x'
  rw [Fintype.sum_prod_type]
  by_cases hxx : h = h'
  · subst hxx
    rw [Finset.sum_eq_single h]
    · have hstep : ∀ k : Fin N, blkInv Λi (h, k) (h, j) * blkSub Λ (h, j') (h, k)
          = Λi j k * Λ k j' := by
        intro k; rw [blkInv_apply_eq, blkSub_apply_eq]
      rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Matrix.mul_apply, hΛi]
      by_cases hj : j = j'
      · subst hj; rw [Matrix.one_apply, if_pos rfl, if_pos rfl]
      · rw [Matrix.one_apply, if_neg hj,
          if_neg (fun hx => hj (by simpa using congrArg Prod.snd hx))]
    · intro h'' _ hne
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [blkInv_eq_zero Λi hne j k, zero_mul]
    · intro hnot; exact absurd (Finset.mem_univ h) hnot
  · have h0 : ∀ y : Fin m × Fin N, blkInv Λi y (h, j) * blkSub Λ (h', j') y = 0 := by
      intro y
      obtain ⟨g, k⟩ := y
      by_cases hg : g = h
      · subst hg
        rw [blkInv_apply_eq, blkSub_eq_zero Λ (Ne.symm hxx) j' k, mul_zero]
      · rw [blkInv_eq_zero Λi hg j k, zero_mul]
    rw [Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => h0 (x, y))),
      if_neg (fun hx => hxx (by simpa using congrArg Prod.fst hx))]


/-- The block-diagonal substitution written with the block matrix `blkSub`. -/
noncomputable def PhiB (Λ : Matrix (Fin N) (Fin N) ℂ) :
    Fin m × Fin N → MvPolynomial (Fin m × Fin N) ℂ :=
  fun x => ∑ y, MvPolynomial.C (blkSub Λ x y) * MvPolynomial.X y

theorem PhiL_eq_PhiB (Λ : Matrix (Fin N) (Fin N) ℂ) :
    PhiL (m := m) Λ = PhiB (m := m) Λ :=
  (blkSub_eq_PhiL Λ).symm

theorem isBlockHom_aeval_PhiB (Λ : Matrix (Fin N) (Fin N) ℂ)
    {F : MvPolynomial (Fin m × Fin N) ℂ} {d : Fin m → ℕ}
    (hF : ∀ u ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h) :
    ∀ J ∈ (MvPolynomial.aeval (PhiB (m := m) Λ) F).support,
      ∀ h : Fin m, ∑ k : Fin N, J (h, k) = d h := by
  rw [← PhiL_eq_PhiB]
  exact Commons.Algebra.MvPolynomial.isBlockHom_aeval_PhiL Λ hF

theorem aeval_PhiB_eq (Λ : Matrix (Fin N) (Fin N) ℂ) (u x : Fin m × Fin N → ℂ)
    (hx : ∀ q : Fin m × Fin N, x q = ∑ k : Fin N, Λ k q.2 * u (q.1, k))
    (Q : MvPolynomial (Fin m × Fin N) ℂ) :
    MvPolynomial.aeval u (MvPolynomial.aeval (PhiB (m := m) Λ) Q) = MvPolynomial.aeval x Q := by
  rw [← PhiL_eq_PhiB]
  exact aeval_PhiL_eq Λ u x hx Q


theorem A_bounds_core {m N : ℕ} (hN : 2 ≤ N)
    (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h)
    (F : MvPolynomial (Fin m × Fin N) ℤ)
    (hFhom : ∀ u ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h)
    (Λ Λi : Matrix (Fin N) (Fin N) ℂ) (hΛi : Λi * Λ = 1)
    (W : ℝ) (hW : 0 ≤ W)
    (bad : Finset ((Fin m × Fin N) →₀ ℕ))
    (hbad : ∀ J ∈ bad, MvPolynomial.coeff J
      (MvPolynomial.aeval (PhiB (m := m) Λ) (F.map (algebraMap ℤ ℂ))) = 0)
    (hwinF : ∀ J, (∀ h : Fin m, ∑ k : Fin N, J (h, k) = d h) → J ∉ bad →
      ∀ k : Fin N, |(∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|
        ≤ (m : ℝ) * W)
    (x : Fin m × Fin N → ℤ) (u : Fin m × Fin N → ℂ)
    (hxu : ∀ q : Fin m × Fin N, ((x q : ℤ) : ℂ) = ∑ k : Fin N, Λ k q.2 * u (q.1, k))
    (γ : Fin N → ℝ) (ε : ℝ) (hε : 0 < ε) (hγ : ∑ k, γ k ≤ -ε)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (D Θ C0 Bnd : ℝ) (hD : 0 < D) (hΘ : 0 ≤ Θ) (hC0 : 1 ≤ C0) (hBnd : 0 ≤ Bnd)
    (hDlo : ∀ h, D ≤ (d h : ℝ) * Real.log (Q h))
    (hDhi : ∀ h, (d h : ℝ) * Real.log (Q h) ≤ (1 + Θ) * D)
    (hu : ∀ q : Fin m × Fin N, ‖u q‖ ≤ C0 * Q q.1 ^ (γ q.2))
    (e : (Fin m × Fin N) →₀ ℕ)
    (hne : MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ ℂ (x q))
      (pderivIterDiv e (F.map (algebraMap ℤ ℂ))) ≠ 0)
    (hcoeffG : ∀ J ∈ (MvPolynomial.aeval (PhiB (m := m) Λ)
      (pderivIterDiv e (F.map (algebraMap ℤ ℂ)))).support,
      ‖(MvPolynomial.aeval (PhiB (m := m) Λ)
        (pderivIterDiv e (F.map (algebraMap ℤ ℂ)))).coeff J‖ ≤ Bnd)
    (hbig : 2 * (N : ℝ) *
      (Real.log (((MvPolynomial.aeval (PhiB (m := m) Λ)
        (pderivIterDiv e (F.map (algebraMap ℤ ℂ)))).support.card : ℝ) * Bnd)
        + (∑ h : Fin m, d h) * Real.log C0) < D * ε * (m : ℝ))
    (hsmall : ((m : ℝ) * W
        + Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) e
        + Θ * (m : ℝ)) * (∑ k : Fin N, |γ k|) < ε * (m : ℝ) / (2 * (N : ℝ))) :
    False := by
  classical
  set G := MvPolynomial.aeval (PhiB (m := m) Λ)
    (pderivIterDiv e (F.map (algebraMap ℤ ℂ))) with hGdef
  set Qp := MvPolynomial.aeval (PhiB (m := m) Λ) (F.map (algebraMap ℤ ℂ)) with hQpdef
  -- the divided derivative has the same support as the plain one, after substitution
  have hGsupp : G.support = (MvPolynomial.aeval (PhiB (m := m) Λ)
      (Commons.Algebra.MvPolynomial.pderivIter e (F.map (algebraMap ℤ ℂ)))).support := by
    rw [hGdef, pderivIterDiv_eq_inv_mul]
    rw [map_mul, MvPolynomial.aeval_C]
    ext J
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff,
      show ∀ (c : ℂ) (Q : MvPolynomial (Fin m × Fin N) ℂ),
          MvPolynomial.coeff J ((algebraMap ℂ (MvPolynomial (Fin m × Fin N) ℂ)) c * Q)
            = c * MvPolynomial.coeff J Q from fun c Q => by
        rw [show (algebraMap ℂ (MvPolynomial (Fin m × Fin N) ℂ)) c
              = MvPolynomial.C c from rfl, MvPolynomial.coeff_C_mul],
      mul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨inv_ne_zero (Nat.cast_ne_zero.mpr (facOf_pos e).ne'), h⟩⟩
  -- (1) block-homogeneity of the `Λ`-expansion of `F`
  have hFhom' : ∀ u ∈ (F.map (algebraMap ℤ ℂ)).support, ∀ h : Fin m,
      ∑ k : Fin N, u (h, k) = d h := by
    intro u hu h
    refine hFhom u ?_ h
    rw [MvPolynomial.mem_support_iff] at hu ⊢
    intro h0
    exact hu (by rw [MvPolynomial.coeff_map, h0, map_zero])
  have hQhom : ∀ J ∈ Qp.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) = d h := by
    rw [hQpdef]
    exact isBlockHom_aeval_PhiB Λ hFhom'
  -- (2) the support/window transfer
  have hsup : ∀ J ∈ G.support, ∃ ν : (Fin m × Fin N) →₀ ℕ,
      (∀ y, ν y ≤ ∑ x ∈ Finset.univ.filter
        (fun x : Fin m × Fin N => (x.1 : ℕ) = (y.1 : ℕ)), e x) ∧
      J + ν ∈ Qp.support := by
    intro J hJ
    rw [hGsupp] at hJ
    rw [hQpdef]
    rw [show PhiB (m := m) Λ = (fun x : Fin m × Fin N =>
      ∑ y : Fin m × Fin N, MvPolynomial.C (blkSub Λ x y) * MvPolynomial.X y) from rfl] at hJ ⊢
    exact Commons.Algebra.MvPolynomial.pderivIter_aeval_linForm_support_ring
      (blkSub Λ) (blkInv Λi) (blkInv_mul_blkSub Λ Λi hΛi)
      (fun y : Fin m × Fin N => (y.1 : ℕ))
      (fun x y hxy => congrArg (fun z : Fin m => (z : ℕ)) (blkSub_ne_zero Λ hxy))
      e (F.map (algebraMap ℤ ℂ)) J hJ
  -- (3) the window for the derivative
  have hnu_nonneg : 0 ≤ Commons.Algebra.MvPolynomial.indexWt
      (fun hi : Fin m × Fin N => d hi.1) e :=
    Commons.Algebra.MvPolynomial.indexWt_nonneg e
  have hwin : ∀ J ∈ G.support, ∀ k : Fin N,
      |(∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|
        ≤ (m : ℝ) * W + Commons.Algebra.MvPolynomial.indexWt
            (fun hi : Fin m × Fin N => d hi.1) e := by
    intro J hJ k
    obtain ⟨ν, hν, hJν⟩ := hsup J hJ
    have hcomp : ∀ h : Fin m, ∑ k : Fin N, (J + ν) (h, k) = d h := hQhom (J + ν) hJν
    have hnotbad : J + ν ∉ bad := by
      intro hb
      have hzero := hbad (J + ν) hb
      have hmem : (J + ν) ∈ (MvPolynomial.aeval (PhiB (m := m) Λ)
          (F.map (algebraMap ℤ ℂ))).support := hJν
      rw [MvPolynomial.mem_support_iff] at hmem
      exact hmem hzero
    have hwinν := hwinF (J + ν) hcomp hnotbad k
    -- the `ν`-correction
    have hfs : ∀ h : Fin m, (∑ x ∈ Finset.univ.filter
          (fun x : Fin m × Fin N => (x.1 : ℕ) = ((h, k).1 : ℕ)), e x) = ∑ j : Fin N, e (h, j) := by
      intro h
      rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single h]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [if_pos (by simp : ((h, j).1 : ℕ) = ((h, k).1 : ℕ))]
      · intro h' _ hne
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [Prod.fst, if_neg (fun hc : (h' : ℕ) = (h : ℕ) => hne (Fin.val_inj.mp hc)),
          Finset.sum_const_zero]
      · intro hnot; exact absurd (Finset.mem_univ h) hnot
    have h1 : ∀ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ))
        ≤ (((∑ j : Fin N, e (h, j)) : ℕ) : ℝ) / (d h : ℝ) := by
      intro h
      have hd0 : (0 : ℝ) < (d h : ℝ) := by exact_mod_cast hd h
      have hle : (ν (h, k) : ℝ) ≤ (((∑ j : Fin N, e (h, j)) : ℕ) : ℝ) := by
        have hνh := hν (h, k)
        rw [hfs h] at hνh
        exact_mod_cast hνh
      exact div_le_div_of_nonneg_right hle (le_of_lt hd0)
    have hsplit : ∀ h : Fin m, (((∑ j : Fin N, e (h, j)) : ℕ) : ℝ) / (d h : ℝ)
        = ∑ j : Fin N, ((e (h, j) : ℕ) : ℝ) / (d h : ℝ) := by
      intro h
      have hp : (((∑ j : Fin N, e (h, j)) : ℕ) : ℝ) = ∑ j : Fin N, ((e (h, j) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
      rw [hp, Finset.sum_div]
    have hE : (∑ h : Fin m, ∑ j : Fin N, ((e (h, j) : ℕ) : ℝ) / (d h : ℝ))
        = Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) e := by
      rw [Commons.Algebra.MvPolynomial.indexWt]
      exact (Fintype.sum_prod_type (fun p : Fin m × Fin N =>
        ((e p : ℕ) : ℝ) / ((d p.1 : ℕ) : ℝ))).symm
    have hνk : ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ))
        ≤ Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) e :=
      calc ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ))
          ≤ ∑ h : Fin m, (((∑ j : Fin N, e (h, j)) : ℕ) : ℝ) / (d h : ℝ) :=
            Finset.sum_le_sum fun h _ => h1 h
        _ = ∑ h : Fin m, ∑ j : Fin N, ((e (h, j) : ℕ) : ℝ) / (d h : ℝ) :=
            Finset.sum_congr rfl fun h _ => hsplit h
        _ = Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) e := hE
    have hadd : (∑ h : Fin m, ((J + ν) (h, k) : ℝ) / (d h : ℝ))
        = (∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ))
          + ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finsupp.add_apply]; push_cast; ring
    have hsplit : (∑ h : Fin m, ((J + ν) (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)
        = ((∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ))
          + ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ)) := by
      rw [hadd]; ring
    rw [hsplit] at hwinν
    have hV0 : 0 ≤ ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ)) :=
      Finset.sum_nonneg fun h _ => div_nonneg (by positivity) (by positivity)
    have h2 : |(∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|
        ≤ |((∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ))
            + ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ))|
          + ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ)) := by
      have h4 := abs_sub
        (((∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ))
          + ∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ)))
        (∑ h : Fin m, ((ν (h, k) : ℝ) / (d h : ℝ)))
      rw [abs_of_nonneg hV0, add_sub_cancel_right] at h4
      exact h4
    linarith [h2, hνk, hwinν]
  -- (4) the vertical degree bound
  have hdeg : ∀ J ∈ G.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h := by
    intro J hJ h
    obtain ⟨ν, _, hJν⟩ := hsup J hJ
    have := hQhom (J + ν) hJν h
    calc ∑ k : Fin N, J (h, k) ≤ ∑ k : Fin N, (J + ν) (h, k) :=
          Finset.sum_le_sum fun k _ => by
            rw [Finsupp.add_apply]; exact Nat.le_add_right _ _
      _ = d h := this
  -- (5) the numeric bound
  have hlt := Commons.Algebra.MvPolynomial.norm_aeval_lt_one (by omega) d hd γ ε hε hγ Q hQ D Θ W
    (Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) e) Bnd C0
    hD hΘ hW hnu_nonneg hBnd hC0 hDlo hDhi u hu G hcoeffG hdeg hwin hbig hsmall
  -- (6) integrality
  obtain ⟨n, hn⟩ := aeval_pderivIterDiv_int (S := ℂ) F e x
  have hval : MvPolynomial.aeval u G = ((n : ℤ) : ℂ) := by
    rw [hGdef]
    rw [aeval_PhiB_eq Λ u (fun q : Fin m × Fin N => ((x q : ℤ) : ℂ)) hxu
      (pderivIterDiv e (F.map (algebraMap ℤ ℂ)))]
    exact hn
  have hn0 : n ≠ 0 := by
    intro h0
    refine hne ?_
    rw [hn, h0]; simp
  have hone : (1 : ℝ) ≤ ‖MvPolynomial.aeval u G‖ := by
    rw [hval, Complex.norm_intCast]
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  linarith


theorem coeff_aeval_pderivIterDiv_le {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (hΛM : ∀ i j, ‖Λ i j‖ ≤ M)
    (F : MvPolynomial (Fin m × Fin N) ℤ) (d : Fin m → ℕ)
    (hFhom : ∀ u ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h)
    (Bd : ℝ) (hBd0 : 0 ≤ Bd) (hBdF : ∀ J, ‖((F.coeff J : ℤ) : ℂ)‖ ≤ Bd)
    (e : (Fin m × Fin N) →₀ ℕ) :
    ∀ J ∈ (MvPolynomial.aeval (PhiB (m := m) Λ)
        (pderivIterDiv e (F.map (algebraMap ℤ ℂ)))).support,
      ‖(MvPolynomial.aeval (PhiB (m := m) Λ)
        (pderivIterDiv e (F.map (algebraMap ℤ ℂ)))).coeff J‖
        ≤ ((F.support.card : ℝ) * (Bd * 2 ^ (N * ∑ h : Fin m, d h)))
          * (((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h)) := by
  classical
  set Fq := F.map (algebraMap ℤ ℂ) with hFqdef
  set P := pderivIterDiv e Fq with hPdef
  have hFqhom : ∀ u ∈ Fq.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h := by
    intro u hu h
    rw [hFqdef, MvPolynomial.support_map_of_injective _ Int.cast_injective] at hu
    exact hFhom u hu h
  have hmem : ∀ J ∈ P.support, J + e ∈ Fq.support := by
    intro J hJ
    rw [hPdef] at hJ
    rw [MvPolynomial.mem_support_iff] at hJ ⊢
    intro h0
    exact hJ (by rw [coeff_pderivIterDiv, h0, zero_mul])
  have hdegP : ∀ J ∈ P.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h := by
    intro J hJ h
    have := hFqhom (J + e) (hmem J hJ) h
    calc ∑ k : Fin N, J (h, k) ≤ ∑ k : Fin N, (J + e) (h, k) :=
          Finset.sum_le_sum fun k _ => by
            rw [Finsupp.add_apply]; exact Nat.le_add_right _ _
      _ = d h := this
  have hPcoeff : ∀ J, ‖P.coeff J‖ ≤ Bd * 2 ^ (N * ∑ h : Fin m, d h) := by
    intro J
    rw [hPdef]
    refine coeff_pderivIterDiv_norm_le Fq d Bd hBd0 ?_ (fun J hJ h => le_of_eq (hFqhom J hJ h)) e J
    intro J'
    rw [hFqdef, MvPolynomial.coeff_map]
    exact hBdF J'
  have hsum : ∑ J ∈ P.support, ‖P.coeff J‖
      ≤ (F.support.card : ℝ) * (Bd * 2 ^ (N * ∑ h : Fin m, d h)) := by
    have h1 : ∑ J ∈ P.support, ‖P.coeff J‖
        ≤ P.support.card • (Bd * 2 ^ (N * ∑ h : Fin m, d h)) := by
      rw [← Finset.sum_const]
      exact Finset.sum_le_sum fun J _ => hPcoeff J
    rw [nsmul_eq_mul] at h1
    have h2 : (P.support.card : ℝ) ≤ (F.support.card : ℝ) := by
      have h3 : P.support.card ≤ Fq.support.card := by
        refine Finset.card_le_card_of_injOn (fun J => J + e) ?_ ?_
        · intro J hJ
          exact hmem J hJ
        · intro J hJ J' hJ' h
          exact add_right_cancel h
      have h4 : Fq.support.card = F.support.card := by
        rw [hFqdef, MvPolynomial.support_map_of_injective _ Int.cast_injective]
      rw [h4] at h3
      exact_mod_cast h3
    have hB0 : 0 ≤ Bd * 2 ^ (N * ∑ h : Fin m, d h) :=
      mul_nonneg hBd0 (by positivity)
    calc ∑ J ∈ P.support, ‖P.coeff J‖
        ≤ (P.support.card : ℝ) * (Bd * 2 ^ (N * ∑ h : Fin m, d h)) := h1
      _ ≤ (F.support.card : ℝ) * (Bd * 2 ^ (N * ∑ h : Fin m, d h)) :=
          mul_le_mul_of_nonneg_right h2 hB0
  intro J _
  rw [show PhiB (m := m) Λ = (fun x : Fin m × Fin N =>
      ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) from (blkSub_eq_PhiL Λ)]
  exact Commons.Algebra.MvPolynomial.coeff_aeval_linForm_le Λ M hM hΛM P
    ((F.support.card : ℝ) * (Bd * 2 ^ (N * ∑ h : Fin m, d h)))
    hsum d hdegP J


theorem blockDegree_pderivIterDiv {m N : ℕ} (Fq : MvPolynomial (Fin m × Fin N) ℂ)
    (d : Fin m → ℕ)
    (hFqhom : ∀ u ∈ Fq.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h)
    (e : (Fin m × Fin N) →₀ ℕ) {J : (Fin m × Fin N) →₀ ℕ}
    (hJ : J ∈ (pderivIterDiv e Fq).support) :
    ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h := by
  intro h
  have hmem : J + e ∈ Fq.support := by
    rw [MvPolynomial.mem_support_iff] at hJ ⊢
    intro h0
    exact hJ (by rw [coeff_pderivIterDiv, h0, zero_mul])
  have := hFqhom (J + e) hmem h
  calc ∑ k : Fin N, J (h, k) ≤ ∑ k : Fin N, (J + e) (h, k) :=
        Finset.sum_le_sum fun k _ => by
          rw [Finsupp.add_apply]; exact Nat.le_add_right _ _
    _ = d h := this

theorem blockDegree_aeval_PhiB {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ)
    (P : MvPolynomial (Fin m × Fin N) ℂ) (d : Fin m → ℕ)
    (hP : ∀ u ∈ P.support, ∀ h : Fin m, ∑ j : Fin N, u (h, j) ≤ d h)
    {J : (Fin m × Fin N) →₀ ℕ}
    (hJ : J ∈ (MvPolynomial.aeval (PhiB (m := m) Λ) P).support) :
    ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h := by
  rw [show PhiB (m := m) Λ = (fun x : Fin m × Fin N =>
      ∑ y : Fin m × Fin N, MvPolynomial.C (blkSub Λ x y) * MvPolynomial.X y) from rfl] at hJ
  exact Commons.Algebra.MvPolynomial.blockDiag_aeval_degree_le P d hP (blkSub Λ)
    (fun h j h' j' hne => blkSub_ne_zero Λ hne) J hJ

/-- **The `A`-bounds** (Step E, assembled): the coefficient bound and the size estimates are
supplied by the caller, and `A_bounds_core` gives the contradiction. -/
theorem A_bounds {m N : ℕ} (hm : 0 < m) (hN : 2 ≤ N)
    (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h)
    (F : MvPolynomial (Fin m × Fin N) ℤ) (hF0 : F ≠ 0)
    (hFhom : ∀ u ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h)
    (Λ Λi : Matrix (Fin N) (Fin N) ℂ) (hΛi : Λi * Λ = 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hΛM : ∀ i j, ‖Λ i j‖ ≤ M)
    (Bd : ℝ) (hBd0 : 0 < Bd) (hBdF : ∀ J, ‖((F.coeff J : ℤ) : ℂ)‖ ≤ Bd)
    (bad : Finset ((Fin m × Fin N) →₀ ℕ))
    (hbad : ∀ J ∈ bad, MvPolynomial.coeff J
      (MvPolynomial.aeval (PhiB (m := m) Λ) (F.map (algebraMap ℤ ℂ))) = 0)
    (W : ℝ) (hW : 0 ≤ W)
    (hwinF : ∀ J, (∀ h : Fin m, ∑ k : Fin N, J (h, k) = d h) → J ∉ bad →
      ∀ k : Fin N, |(∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)|
        ≤ (m : ℝ) * W)
    (x : Fin m × Fin N → ℤ) (u : Fin m × Fin N → ℂ)
    (hxu : ∀ q : Fin m × Fin N, algebraMap ℤ ℂ (x q) = ∑ k : Fin N, Λ k q.2 * u (q.1, k))
    (γ : Fin N → ℝ) (ε : ℝ) (hε : 0 < ε) (hγ : ∑ k, γ k ≤ -ε)
    (Q : Fin m → ℝ) (hQ : ∀ h, 0 < Q h)
    (D Θ C0 : ℝ) (hD : 0 < D) (hΘ : 0 ≤ Θ) (hC0 : 1 ≤ C0)
    (hDlo : ∀ h, D ≤ (d h : ℝ) * Real.log (Q h))
    (hDhi : ∀ h, (d h : ℝ) * Real.log (Q h) ≤ (1 + Θ) * D)
    (hu : ∀ q : Fin m × Fin N, ‖u q‖ ≤ C0 * Q q.1 ^ (γ q.2))
    (e : (Fin m × Fin N) →₀ ℕ)
    (hne : MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ ℂ (x q))
      (pderivIterDiv e (F.map (algebraMap ℤ ℂ))) ≠ 0)
    (hsmall : ((m : ℝ) * W
        + Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) e
        + Θ * (m : ℝ)) * (∑ k : Fin N, |γ k|) < ε * (m : ℝ) / (2 * (N : ℝ)))
    (hbig : 2 * (N : ℝ) * (Real.log ((F.support.card : ℝ))
        + Real.log Bd
        + (∑ h : Fin m, d h) * ((N : ℝ) * Real.log 2)
        + Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ N)
        + (∑ h : Fin m, d h) * Real.log ((N : ℝ) * M + 1)
        + (∑ h : Fin m, d h) * Real.log C0) < D * ε * (m : ℝ)) :
    False := by
  classical
  set Fq : MvPolynomial (Fin m × Fin N) ℂ := F.map (algebraMap ℤ ℂ) with hFqdef
  set G : MvPolynomial (Fin m × Fin N) ℂ :=
    MvPolynomial.aeval (PhiB (m := m) Λ) (pderivIterDiv e Fq)
    with hGdef
  set Bnd : ℝ := ((F.support.card : ℝ) * (Bd * 2 ^ (N * ∑ h : Fin m, d h)))
      * (((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h)) with hBnddef
  have hFqhom : ∀ u ∈ Fq.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h := by
    intro u hu h
    rw [hFqdef, MvPolynomial.support_map_of_injective _ Int.cast_injective] at hu
    exact hFhom u hu h
  have hcoeffG : ∀ J ∈ G.support, ‖G.coeff J‖ ≤ Bnd := by
    intro J hJ
    rw [hGdef] at hJ
    rw [hGdef, hBnddef]
    exact coeff_aeval_pderivIterDiv_le Λ M hM0 hΛM F d hFhom Bd (le_of_lt hBd0) hBdF e J
      (by rwa [hFqdef] at hJ)
  have hdegG : ∀ J ∈ G.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h := by
    intro J hJ
    rw [hGdef] at hJ
    exact blockDegree_aeval_PhiB Λ (pderivIterDiv e Fq) d
      (fun u hu h => blockDegree_pderivIterDiv Fq d hFqhom e hu h) hJ
  have hcardG : G.support.card ≤ ∏ h : Fin m, (d h + 1) ^ N :=
    Commons.Algebra.MvPolynomial.card_support_block_le G d hdegG
  have hBnd0 : 0 < Bnd := by
    rw [hBnddef]
    have h1 : (0 : ℝ) < (F.support.card : ℝ) := by
      have : 0 < F.support.card := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hF0)
      exact_mod_cast this
    have h2 : 0 < Bd * 2 ^ (N * ∑ h : Fin m, d h) :=
      mul_pos hBd0 (by positivity)
    have h3 : 0 < ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) :=
      pow_pos (by have h : (0:ℝ) ≤ (N:ℝ) * M := mul_nonneg (by positivity) hM0; linarith) _
    exact mul_pos (mul_pos h1 h2) h3
  have hne' : MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ ℂ (x q))
      (pderivIterDiv e Fq) ≠ 0 := by
    rw [hFqdef]; exact hne
  have hGne : G ≠ 0 := by
    intro h0
    refine hne' ?_
    have h1 : MvPolynomial.aeval u G = 0 := by rw [h0, map_zero]
    rw [hGdef] at h1
    rw [aeval_PhiB_eq Λ u (fun q : Fin m × Fin N => algebraMap ℤ ℂ (x q)) hxu
      (pderivIterDiv e Fq)] at h1
    exact h1
  have hGcard0 : 0 < (G.support.card : ℝ) := by
    have : 0 < G.support.card := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hGne)
    exact_mod_cast this
  -- the log estimate
  have hlog : Real.log ((G.support.card : ℝ) * Bnd)
      ≤ Real.log (F.support.card : ℝ) + Real.log Bd
        + (∑ h : Fin m, d h) * ((N : ℝ) * Real.log 2)
        + Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ N)
        + (∑ h : Fin m, d h) * Real.log ((N : ℝ) * M + 1) := by
    have hP1 : (0 : ℝ) < 2 ^ (N * ∑ h : Fin m, d h) := by positivity
    have hP2 : (0 : ℝ) < ∏ h : Fin m, ((d h : ℝ) + 1) ^ N :=
      Finset.prod_pos fun h _ => pow_pos (by linarith [show (0:ℝ) < (d h:ℝ) by exact_mod_cast hd h]) _
    have hNm : (0 : ℝ) < ((N : ℝ) * M + 1) ^ (∑ h : Fin m, d h) :=
      pow_pos (by have h : (0:ℝ) ≤ (N:ℝ) * M := mul_nonneg (by positivity) hM0; linarith) _
    have hcardF0 : (0 : ℝ) < (F.support.card : ℝ) := by
      have : 0 < F.support.card := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hF0)
      exact_mod_cast this
    have hB : (0 : ℝ) < Bd * 2 ^ (N * ∑ h : Fin m, d h) := mul_pos hBd0 hP1
    have hlogB : Real.log Bnd = Real.log (F.support.card : ℝ) + Real.log Bd
        + (∑ h : Fin m, d h) * ((N : ℝ) * Real.log 2)
        + (∑ h : Fin m, d h) * Real.log ((N : ℝ) * M + 1) := by
      rw [hBnddef, Real.log_mul (ne_of_gt (mul_pos hcardF0 hB)) (ne_of_gt hNm),
        Real.log_mul (ne_of_gt hcardF0) (ne_of_gt hB),
        Real.log_mul (ne_of_gt hBd0) (ne_of_gt hP1), Real.log_pow, Nat.cast_mul,
        Real.log_pow]
      ring
    have hle : Real.log (G.support.card : ℝ) ≤ Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ N) := by
      refine Real.log_le_log hGcard0 ?_
      exact_mod_cast hcardG
    rw [Real.log_mul (ne_of_gt hGcard0) (ne_of_gt hBnd0), hlogB]
    linarith
  have hcore_big : 2 * (N : ℝ) * (Real.log ((G.support.card : ℝ) * Bnd)
      + (∑ h : Fin m, d h) * Real.log C0) < D * ε * (m : ℝ) := by
    have h2 : Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ N)
        = (N : ℝ) * ∑ h : Fin m, Real.log ((d h : ℝ) + 1) := by
      rw [Real.log_prod]
      · rw [Finset.sum_congr rfl (fun h _ => Real.log_pow ((d h : ℝ) + 1) N)]
        rw [Finset.mul_sum]
      · intro h _
        exact ne_of_gt (pow_pos (by linarith [show (0:ℝ) < (d h:ℝ) by exact_mod_cast hd h]) _)
    rw [h2] at hbig
    nlinarith [hbig, hlog, hε, hD, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) N]
  -- call the core
  refine A_bounds_core hN d hd F hFhom Λ Λi hΛi W hW bad ?_ hwinF x u hxu γ ε hε hγ Q hQ
    D Θ C0 Bnd hD hΘ hC0 (le_of_lt hBnd0) hDlo hDhi hu e hne ?_ ?_ hsmall
  · intro J hJ
    exact hbad J hJ
  · intro J hJ
    exact hcoeffG J hJ
  · exact hcore_big

end Submission.Subspace

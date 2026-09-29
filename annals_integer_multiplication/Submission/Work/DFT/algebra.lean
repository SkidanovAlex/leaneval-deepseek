import Mathlib
import Submission.Work.DFT.expId

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-! Inversion and the convolution theorem for the multidimensional DFT, conditional on the
character-orthogonality facts `charSumSub` / `charSumConv`. -/

theorem inversion (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t)
    (horth : ∀ j a : Fin ts.prod,
      (∑ k : Fin ts.prod, charExp ts (subN (HvdH.digits ts j) (HvdH.digits ts a)) k)
        = if j = a then (ts.prod : ℂ) else 0)
    (u : Fin ts.prod → ℂ) :
    HvdH.dftMulti ts 1 (HvdH.dftMulti ts (-1) u) = (1 / (ts.prod : ℂ)) • u := by
  have hT : 0 < ts.prod := List.prod_pos hpos
  have hTne : (ts.prod : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  funext j
  rw [Pi.smul_apply]
  have key : ∑ k : Fin ts.prod,
        dftExp ts 1 j k * (∑ a : Fin ts.prod, dftExp ts (-1) k a * u a)
      = (ts.prod : ℂ) * u j := by
    calc ∑ k : Fin ts.prod, dftExp ts 1 j k * (∑ a : Fin ts.prod, dftExp ts (-1) k a * u a)
        = ∑ k : Fin ts.prod, ∑ a : Fin ts.prod,
            (dftExp ts 1 j k * dftExp ts (-1) k a) * u a := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
      _ = ∑ a : Fin ts.prod, ∑ k : Fin ts.prod,
            (dftExp ts 1 j k * dftExp ts (-1) k a) * u a := by
          rw [Finset.sum_comm]
      _ = ∑ a : Fin ts.prod,
            (∑ k : Fin ts.prod, charExp ts (subN (HvdH.digits ts j) (HvdH.digits ts a)) k) * u a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun k _ => by rw [dftExp_mul_charSub ts j a k])
      _ = ∑ a : Fin ts.prod, (if j = a then (ts.prod : ℂ) else 0) * u a := by
          exact Finset.sum_congr rfl (fun a _ => by rw [horth j a])
      _ = (ts.prod : ℂ) * u j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro b _ hb
            have hjb : j ≠ b := fun h => hb h.symm
            simp [hjb]
          · intro hj; exact absurd (Finset.mem_univ j) hj
  have pull : ∑ k : Fin ts.prod,
        dftExp ts 1 j k * ((1 / (ts.prod : ℂ)) * ∑ a : Fin ts.prod, dftExp ts (-1) k a * u a)
      = (1 / (ts.prod : ℂ)) * ∑ k : Fin ts.prod,
        dftExp ts 1 j k * (∑ a : Fin ts.prod, dftExp ts (-1) k a * u a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  simp only [dftMulti_apply]
  rw [pull, key, smul_eq_mul]
  field_simp

/-- Collapsing the `Fin ts.prod`-sum of a Kronecker delta against `vget`. -/
theorem sum_delta_vget (ts : List ℕ) (v : Fin ts.prod → ℂ) (c : ℕ) (hc : c < ts.prod) :
    ∑ b : Fin ts.prod, (if (b : ℕ) = c then (ts.prod : ℂ) else 0) * v b
      = (ts.prod : ℂ) * HvdH.vget v c := by
  have hval : (if ((⟨c, hc⟩ : Fin ts.prod) : ℕ) = c then (ts.prod : ℂ) else 0) * v ⟨c, hc⟩
      = (ts.prod : ℂ) * HvdH.vget v c := by
    simp [HvdH.vget, hc]
  rw [Finset.sum_eq_single (s := Finset.univ) (⟨c, hc⟩ : Fin ts.prod) ?_ ?_]
  · exact hval
  · intro b _ hb
    have hbc : (b : ℕ) ≠ c := fun h => hb (Fin.ext h)
    simp [hbc]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem convolution (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t)
    (horth : ∀ j a b : Fin ts.prod,
      (∑ k : Fin ts.prod, charExp ts (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a))
          (HvdH.digits ts b)) k)
        = if b = HvdH.subIdx ts j a then (ts.prod : ℂ) else 0)
    (u v : Fin ts.prod → ℂ) :
    HvdH.convC ts u v
      = (ts.prod : ℂ) • HvdH.dftMulti ts 1 (HvdH.dftMulti ts (-1) u * HvdH.dftMulti ts (-1) v) := by
  have hT : 0 < ts.prod := List.prod_pos hpos
  have hTne : (ts.prod : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  funext j
  simp only [HvdH.convC, Pi.smul_apply, smul_eq_mul]
  have hR : (ts.prod : ℂ) *
        (HvdH.dftMulti ts 1 (HvdH.dftMulti ts (-1) u * HvdH.dftMulti ts (-1) v) j)
      = (1 / (ts.prod : ℂ)) * ∑ a : Fin ts.prod, u a * HvdH.vget v (HvdH.subIdx ts j a) := by
    have step1 : (ts.prod : ℂ) *
          (HvdH.dftMulti ts 1 (HvdH.dftMulti ts (-1) u * HvdH.dftMulti ts (-1) v) j)
        = ∑ k : Fin ts.prod, dftExp ts 1 j k *
            ((HvdH.dftMulti ts (-1) u k) * (HvdH.dftMulti ts (-1) v k)) := by
      simp only [dftMulti_apply, Pi.mul_apply]
      rw [← mul_assoc, mul_one_div, div_self hTne, one_mul]
    have step2 : ∑ k : Fin ts.prod, dftExp ts 1 j k *
            ((HvdH.dftMulti ts (-1) u k) * (HvdH.dftMulti ts (-1) v k))
        = (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ∑ k : Fin ts.prod, dftExp ts 1 j k *
              ((∑ a : Fin ts.prod, dftExp ts (-1) k a * u a) *
               (∑ b : Fin ts.prod, dftExp ts (-1) k b * v b)) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_congr rfl (fun k _ => ?_)).symm
      rw [dftMulti_apply, dftMulti_apply]
      ring
    have step3 : (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ∑ k : Fin ts.prod, dftExp ts 1 j k *
              ((∑ a : Fin ts.prod, dftExp ts (-1) k a * u a) *
               (∑ b : Fin ts.prod, dftExp ts (-1) k b * v b))
        = (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ∑ k : Fin ts.prod, ∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
              (dftExp ts 1 j k * dftExp ts (-1) k a * dftExp ts (-1) k b) * (u a * v b) := by
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hAB : (∑ a : Fin ts.prod, dftExp ts (-1) k a * u a) *
            (∑ b : Fin ts.prod, dftExp ts (-1) k b * v b)
          = ∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
              (dftExp ts (-1) k a * u a) * (dftExp ts (-1) k b * v b) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum])
      rw [hAB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    have step4 : (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ∑ k : Fin ts.prod, ∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
              (dftExp ts 1 j k * dftExp ts (-1) k a * dftExp ts (-1) k b) * (u a * v b)
        = (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
              (∑ k : Fin ts.prod,
                charExp ts (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a))
                  (HvdH.digits ts b)) k) * (u a * v b) := by
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by rw [dftExp_mul_charConv ts j a b k])
    have step5 : (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ∑ a : Fin ts.prod, ∑ b : Fin ts.prod,
              (∑ k : Fin ts.prod,
                charExp ts (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a))
                  (HvdH.digits ts b)) k) * (u a * v b)
        = (1 / (ts.prod : ℂ)) * (1 / (ts.prod : ℂ)) *
            ((ts.prod : ℂ) * ∑ a : Fin ts.prod, u a * HvdH.vget v (HvdH.subIdx ts j a)) := by
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have hb : ∀ b : Fin ts.prod,
          (∑ k : Fin ts.prod, charExp ts (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a))
              (HvdH.digits ts b)) k)
            = (if b = HvdH.subIdx ts j a then (ts.prod : ℂ) else 0) := fun b => horth j a b
      rw [Finset.sum_congr rfl (fun b _ => by rw [hb b])]
      have hfac : ∑ b : Fin ts.prod,
            (if b = HvdH.subIdx ts j a then (ts.prod : ℂ) else 0) * (u a * v b)
          = u a * ∑ b : Fin ts.prod,
            (if b = HvdH.subIdx ts j a then (ts.prod : ℂ) else 0) * v b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      rw [hfac, sum_delta_vget ts v (HvdH.subIdx ts j a) (subIdx_lt ts hpos j a)]
      ring
    rw [step1, step2, step3, step4, step5]
    field_simp
  exact hR.symm

end Work.DFT

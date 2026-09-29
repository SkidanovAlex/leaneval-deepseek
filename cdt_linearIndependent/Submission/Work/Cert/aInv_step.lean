import Mathlib
import Submission.Work.Cert.aLoop_aux
import Submission.Work.Cert.cx_mul_le
import Submission.Work.Cert.pT_step
import Submission.Work.Cert.dA_step


namespace Work.Cert
open Complex Finset
open scoped BigOperators
noncomputable section

/-! ## my pieces -/

lemma pn_step (qr qi : ℤ) (k : ℕ) (a b : ℤ) (μ : ℝ)
    (hμ : μ ≤ 79 / 100) (hz : ‖qc qr qi‖ ≤ μ)
    (h : ‖cx a b - (qc qr qi) ^ k‖ ≤ 16 / ((S : ℝ))) :
    ‖cx (cmr a b qr qi) (cmi a b qr qi) - (qc qr qi) ^ (k + 1)‖ ≤ 16 / ((S : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := thS_pos
  have h1 : ‖cx (cmr a b qr qi) (cmi a b qr qi) - cx a b * cx qr qi‖ ≤ 3 / ((S : ℝ)) :=
    cx_mul_le a b qr qi
  have h2 : ‖cx a b * cx qr qi - (qc qr qi) ^ (k + 1)‖ ≤ (16 / ((S : ℝ))) * μ := by
    have he : cx a b * cx qr qi - (qc qr qi) ^ (k + 1)
        = (cx a b - (qc qr qi) ^ k) * (qc qr qi) := by
      rw [show cx qr qi = qc qr qi from rfl, pow_succ]
      ring
    rw [he, norm_mul]
    exact mul_le_mul h hz (norm_nonneg _) (by positivity)
  have h3 : ‖cx (cmr a b qr qi) (cmi a b qr qi) - (qc qr qi) ^ (k + 1)‖
      ≤ 3 / ((S : ℝ)) + (16 / ((S : ℝ))) * μ := by
    calc ‖cx (cmr a b qr qi) (cmi a b qr qi) - (qc qr qi) ^ (k + 1)‖
        = ‖(cx (cmr a b qr qi) (cmi a b qr qi) - cx a b * cx qr qi)
            + (cx a b * cx qr qi - (qc qr qi) ^ (k + 1))‖ := by
          rw [show cx (cmr a b qr qi) (cmi a b qr qi) - (qc qr qi) ^ (k + 1)
              = (cx (cmr a b qr qi) (cmi a b qr qi) - cx a b * cx qr qi)
                + (cx a b * cx qr qi - (qc qr qi) ^ (k + 1)) from by ring]
      _ ≤ ‖cx (cmr a b qr qi) (cmi a b qr qi) - cx a b * cx qr qi‖
            + ‖cx a b * cx qr qi - (qc qr qi) ^ (k + 1)‖ := norm_add_le _ _
      _ ≤ 3 / ((S : ℝ)) + (16 / ((S : ℝ))) * μ := add_le_add h1 h2
  have hμ' : (3 : ℝ) + 16 * μ ≤ 16 := by linarith
  have h4 : 3 / ((S : ℝ)) + (16 / ((S : ℝ))) * μ ≤ 16 / ((S : ℝ)) := by
    have hh : (3 + 16 * μ) / (S : ℝ) ≤ 16 / (S : ℝ) :=
      div_le_div_of_nonneg_right hμ' (le_of_lt hS)
    rw [show (3 + 16 * μ) / (S : ℝ) = (3 : ℝ) / (S : ℝ) + (16 / (S : ℝ)) * μ by ring] at hh
    exact hh
  linarith [h3, h4]

lemma T_step (k : ℕ) (t : ℤ) (ht : t = (tri k : ℤ)) :
    t + ((k + 1 : ℕ) : ℤ) = (tri (k + 1) : ℤ) := by
  rw [ht, tri_succ]
  push_cast
  ring

lemma mn_step (m : ℤ) (k : ℕ) (mn : ℤ) (hμ0 : 0 ≤ mub m)
    (hmn : (mub m) ^ k ≤ (mn : ℝ) / ((S : ℝ))) :
    (mub m) ^ (k + 1) ≤ ((mu mn m + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := thS_pos
  have h1 : ((mn : ℝ) * (m : ℝ)) / ((S : ℝ)) ≤ ((mu mn m : ℤ) : ℝ) := mu_ge' mn m
  have h2 : (0 : ℝ) ≤ (mn : ℝ) / ((S : ℝ)) := le_trans (pow_nonneg hμ0 k) hmn
  have h3 : (mub m) ^ (k + 1) ≤ ((mn : ℝ) / ((S : ℝ))) * ((m : ℝ) / ((S : ℝ))) := by
    rw [pow_succ]
    exact mul_le_mul hmn le_rfl hμ0 h2
  have h4 : ((mn : ℝ) / ((S : ℝ))) * ((m : ℝ) / ((S : ℝ)))
      = ((mn : ℝ) * (m : ℝ)) / ((S : ℝ)) / ((S : ℝ)) := by ring
  rw [h4] at h3
  have h5 : ((mn : ℝ) * (m : ℝ)) / ((S : ℝ)) / ((S : ℝ))
      ≤ ((mu mn m : ℤ) : ℝ) / ((S : ℝ)) := div_le_div_of_nonneg_right h1 (le_of_lt hS)
  have h6 : ((mu mn m : ℤ) : ℝ) / ((S : ℝ)) ≤ ((mu mn m + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hS)
    push_cast
    linarith
  linarith [h3, h5, h6]

lemma mT_step (m : ℤ) (k : ℕ) (mn mT : ℤ) (hμ0 : 0 ≤ mub m)
    (hmn : (mub m) ^ (k + 1) ≤ (mn : ℝ) / ((S : ℝ)))
    (hmT : (mub m) ^ (tri k) ≤ (mT : ℝ) / ((S : ℝ))) :
    (mub m) ^ (tri (k + 1)) ≤ ((mu mT mn + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := thS_pos
  have h1 : ((mT : ℝ) * (mn : ℝ)) / ((S : ℝ)) ≤ ((mu mT mn : ℤ) : ℝ) := mu_ge' mT mn
  have h3 : (mub m) ^ (tri k) * (mub m) ^ (k + 1)
      ≤ ((mT : ℝ) / ((S : ℝ))) * ((mn : ℝ) / ((S : ℝ))) :=
    mul_le_mul hmT hmn (pow_nonneg hμ0 (k + 1)) (le_trans (pow_nonneg hμ0 (tri k)) hmT)
  have htk : (mub m) ^ (tri (k + 1)) = (mub m) ^ (tri k) * (mub m) ^ (k + 1) := by
    rw [tri_succ, pow_add]
  rw [htk]
  have h4 : ((mT : ℝ) / ((S : ℝ))) * ((mn : ℝ) / ((S : ℝ)))
      = ((mT : ℝ) * (mn : ℝ)) / ((S : ℝ)) / ((S : ℝ)) := by ring
  rw [h4] at h3
  have h5 : ((mT : ℝ) * (mn : ℝ)) / ((S : ℝ)) / ((S : ℝ))
      ≤ ((mu mT mn : ℤ) : ℝ) / ((S : ℝ)) := div_le_div_of_nonneg_right h1 (le_of_lt hS)
  have h6 : ((mu mT mn : ℤ) : ℝ) / ((S : ℝ)) ≤ ((mu mT mn + 1 : ℤ) : ℝ) / ((S : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hS)
    push_cast
    linarith
  linarith [h3, h5, h6]

lemma hkey_pow (k : ℕ) : 20 * k ≤ 8 * tri (k + 1) + 1 := by
  have hev : 2 ∣ (k + 1) * (k + 2) := by
    have h := Nat.even_mul_succ_self (k + 1)
    exact even_iff_two_dvd.mp (by simpa using h)
  have htri : 2 * tri (k + 1) = (k + 1) * (k + 2) := by
    rw [tri]
    exact (mul_comm 2 _).trans (Nat.div_mul_cancel hev)
  have h4 : 8 * tri (k + 1) = 4 * ((k + 1) * (k + 2)) := by omega
  have h5 : 20 * k ≤ 4 * ((k + 1) * (k + 2)) + 1 := by
    have h : (20 : ℤ) * (k : ℤ) ≤ 4 * (((k : ℤ) + 1) * ((k : ℤ) + 2)) + 1 := by
      nlinarith [sq_nonneg ((k : ℤ) - 1)]
    exact_mod_cast h
  omega

lemma Asum_step (qr qi : ℤ) (k : ℕ) (Ar Ai pTr pTi : ℤ)
    (hbd : ‖cx Ar Ai - Asum (qc qr qi) (k + 1)‖ ≤ (Bd k) / ((S : ℝ)))
    (hpT : ‖cx pTr pTi - (qc qr qi) ^ (tri (k + 1))‖ ≤ (20 * (k : ℝ)) / ((S : ℝ))) :
    ‖cx (Ar + pTr) (Ai + pTi) - Asum (qc qr qi) (k + 2)‖ ≤ (Bd (k + 1)) / ((S : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := thS_pos
  have hsum : Asum (qc qr qi) (k + 2)
      = Asum (qc qr qi) (k + 1) + (qc qr qi) ^ (tri (k + 1)) := by
    simp only [Asum]
    rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ]
  have hadd : cx (Ar + pTr) (Ai + pTi) = cx Ar Ai + cx pTr pTi := cx_add Ar Ai pTr pTi
  have heq : cx (Ar + pTr) (Ai + pTi) - Asum (qc qr qi) (k + 2)
      = (cx Ar Ai - Asum (qc qr qi) (k + 1))
        + (cx pTr pTi - (qc qr qi) ^ (tri (k + 1))) := by
    rw [hadd, hsum]
    ring
  have hkey : (20 * (k : ℝ)) ≤ (((8 * tri (k + 1) + 1 : ℕ)) : ℝ) := by
    have := hkey_pow k
    push_cast
    exact_mod_cast this
  rw [heq]
  calc ‖(cx Ar Ai - Asum (qc qr qi) (k + 1)) + (cx pTr pTi - (qc qr qi) ^ (tri (k + 1)))‖
      ≤ ‖cx Ar Ai - Asum (qc qr qi) (k + 1)‖ + ‖cx pTr pTi - (qc qr qi) ^ (tri (k + 1))‖ :=
        norm_add_le _ _
    _ ≤ (Bd k) / ((S : ℝ)) + (20 * (k : ℝ)) / ((S : ℝ)) := add_le_add hbd hpT
    _ = (Bd k + 20 * (k : ℝ)) / ((S : ℝ)) := by ring
    _ ≤ (Bd (k + 1)) / ((S : ℝ)) := by
        rw [Bd_succ]
        apply div_le_div_of_nonneg_right _ (le_of_lt hS)
        linarith [hkey]

/-! ## assembly -/

/-- One step of the `A`-loop invariant (`Work.Cert.AInv`, `Work.Cert.aStep` in `Submission.Work.Cert.ThetaDefs`).

In *ulp units* (i.e. multiplied by `S = 2^40·10^8`) the bookkeeping is: the `pn` error `e_k` obeys
`e_{k+1} ≤ 3 + μ·e_k ≤ 3 + (79/100)·16 = 15.64 < 16`; the `pT` error `g_k` obeys
`g_{k+1} ≤ 3 + (1 + 20(k-1)/S)·16 + 20(k-1)·μ^{k+1}` (the middle factor uses `‖cx s.pT‖ ≤ μ^{tri k} + g_k/S ≤ 1 + g_k/S`),
which stays below the budget `20k` (use `μ^{k+1} ≤ μ^2` and `320(k-1)/S ≤ k-1`); the `mn`/`mT` lower
bounds and the `dA` budget are the `mu_ge'`/`dvu_ge'` estimates (the new summand
`mu (T * dvu mT m) rq` covers `tri(k+1)·μ^{tri(k+1)-1}·rq`, the mean-value term on the disc of radius
`rq` at `|q| ≤ μ`), and the `Asum` error grows by the `pT` error against the per-step allowance
`8·tri(k+1)+1 ≥ 20k` (`Bd_succ`, `BdM_succ`). -/
theorem aInv_step
    (hcxmul : ∀ a b c d : ℤ, ‖Work.Cert.cx (Work.Cert.cmr a b c d) (Work.Cert.cmi a b c d) - Work.Cert.cx a b * Work.Cert.cx c d‖ ≤ 3 / ((Work.Cert.S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : Work.Cert.mub m ≤ 79 / 100) (hz : ‖Work.Cert.qc qr qi‖ ≤ Work.Cert.mub m)
    (k : ℕ) (hk : 1 ≤ k) (s : Work.Cert.TS) (hs : Work.Cert.AInv qr qi rq m k s) :
    Work.Cert.AInv qr qi rq m (k + 1) (Work.Cert.aStep qr qi rq m (k + 1) s) := by
  obtain ⟨hpn, hpT, hT, hmn, hmT, hdA, hsum⟩ := hs
  have hm0 : (0 : ℤ) ≤ m := le_trans (by norm_num) hm
  have hμ0 : 0 ≤ mub m := mub_nonneg hm0
  have _ : ‖cx (cmr 0 0 0 0) (cmi 0 0 0 0) - cx 0 0 * cx 0 0‖ ≤ 3 / ((S : ℝ)) := hcxmul 0 0 0 0
  have hstep : aStep qr qi rq m (k + 1) s =
      { pnr := cmr s.pnr s.pni qr qi, pni := cmi s.pnr s.pni qr qi,
        pTr := cmr s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi),
        pTi := cmi s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi),
        Ar := s.Ar + cmr s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi),
        Ai := s.Ai + cmi s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi),
        mn := mu s.mn m + 1,
        mT := mu s.mT (mu s.mn m + 1) + 1,
        dA := s.dA + mu ((s.T + ((k + 1 : ℕ) : ℤ)) * dvu (mu s.mT (mu s.mn m + 1) + 1) m) rq
               + 8 * (s.T + ((k + 1 : ℕ) : ℤ)) + 1,
        T := s.T + ((k + 1 : ℕ) : ℤ) } := rfl
  have hpn' : ‖cx (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi) - (qc qr qi) ^ (k + 1)‖
      ≤ 16 / ((S : ℝ)) := pn_step qr qi k s.pnr s.pni (mub m) hμ hz hpn
  have hpT' : ‖cx (cmr s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi))
        (cmi s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi))
        - (qc qr qi) ^ (tri (k + 1))‖ ≤ (20 * (k : ℝ)) / ((S : ℝ)) :=
    pT_step qr qi k hk s.pTr s.pTi (cmr s.pnr s.pni qr qi) (cmi s.pnr s.pni qr qi)
      (mub m) hμ0 hμ hz hpn' hpT
  have hmn' : (mub m) ^ (k + 1) ≤ ((mu s.mn m + 1 : ℤ) : ℝ) / ((S : ℝ)) :=
    mn_step m k s.mn hμ0 hmn
  have hmT' : (mub m) ^ (tri (k + 1)) ≤ ((mu s.mT (mu s.mn m + 1) + 1 : ℤ) : ℝ) / ((S : ℝ)) :=
    mT_step m k (mu s.mn m + 1) s.mT hμ0 hmn' hmT
  have hT' : s.T + ((k + 1 : ℕ) : ℤ) = (tri (k + 1) : ℤ) := T_step k s.T hT
  rw [hstep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpn'
  · simpa only [Nat.add_sub_cancel] using hpT'
  · exact hT'
  · exact hmn'
  · exact hmT'
  · have h := dA_step k hk m rq (s.T + ((k + 1 : ℕ) : ℤ)) (mu s.mT (mu s.mn m + 1) + 1) s.dA
      hT' hdA hmT' hm hrq
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using h
  · exact Asum_step qr qi k s.Ar s.Ai _ _ hsum hpT'

end
end Work.Cert

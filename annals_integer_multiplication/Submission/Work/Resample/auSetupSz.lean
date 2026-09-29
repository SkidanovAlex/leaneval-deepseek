import Mathlib
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auWtSz
import Submission.Work.Resample.auWtErr
import Submission.Work.Resample.auStreamSz
import Submission.Work.Resample.auConvDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auHExpClose
import Submission.Work.Fx.piUBound
import Submission.Work.Fx.piIter

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- Every entry of the extended input array (and the default `(0,0)` used outside its range) lies
in the disc, provided the input array is nonempty and all its entries do. -/
theorem auExtDisc (p α s : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hu : u.length = s)
    (hd : ∀ z ∈ u, HvdH.inDisc p z) :
    ∀ j, HvdH.inDisc p ((Work.Resample.auExt p α s u).getD j (0, 0)) := by
  intro j
  rw [Work.Resample.auExt]
  have hlen : (List.flatten (List.replicate (Work.Resample.auCop p α s) u)).length
      = Work.Resample.auCop p α s * u.length := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate]
    simp
  by_cases h : Work.Resample.auOff p α s + j
      < (List.flatten (List.replicate (Work.Resample.auCop p α s) u)).length
  · have hlt : (Work.Resample.auOff p α s + j) % u.length < u.length :=
      Nat.mod_lt _ (by omega)
    have hgd : (List.drop (Work.Resample.auOff p α s)
        (List.flatten (List.replicate (Work.Resample.auCop p α s) u))).getD j (0, 0)
        = u[(Work.Resample.auOff p α s + j) % u.length]'hlt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
        Work.Resample.auIdx_aux_flattenReplicate u (Work.Resample.auCop p α s)
          (Work.Resample.auOff p α s + j) (by rw [← hlen]; exact h),
        List.getElem?_eq_getElem hlt]
      rfl
    rw [hgd]
    exact hd _ (List.getElem_mem _)
  · have hgd : (List.drop (Work.Resample.auOff p α s)
        (List.flatten (List.replicate (Work.Resample.auCop p α s) u))).getD j (0, 0) = (0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
        List.getElem?_eq_none (not_lt.mp h)]
      rfl
    rw [hgd, HvdH.inDisc]
    positivity

/-- Size of the computed weight, with no accuracy hypothesis: in the guard branch the fixed-point
Horner value `auH p (-auZ) (auNstep p)` is within `2/2^p` of `2^P · exp(-auZ/2^P) ≤ 2^P`
(`auHExpClose`), and division by `2^(P-p)·(2α)` with `α ≥ 2` brings the absolute value below
`2^p`; in the other branch `auWt = 0`. -/
theorem auWtSzNoHt (p α t : ℕ) (N : ℤ) (hN : 0 ≤ N) (ht : 1 ≤ t) (hα : 2 ≤ α) (hp : 100 ≤ p) :
    (Work.Resample.auWt p α t N).natAbs ≤ 2 ^ p ∧
      HvdH.isz (Work.Resample.auWt p α t N) ≤ p + 3 := by
  have hp1 : 1 ≤ p := by omega
  have hmain : (Work.Resample.auWt p α t N).natAbs ≤ 2 ^ p := by
    rw [Work.Resample.auWt]
    split_ifs with hg
    · have hZ0 : 0 ≤ Work.Resample.auZ p α t N := Work.Resample.auZ_nonneg p α t N hN
      have hZle : ((Work.Resample.auZ p α t N : ℤ) : ℝ)
          ≤ ((p : ℝ) + 10) * (2 : ℝ) ^ Work.Resample.auPrec p := by
        calc ((Work.Resample.auZ p α t N : ℤ) : ℝ)
            ≤ ((((p+10 : ℕ) : ℤ) * (2:ℤ)^(Work.Resample.auPrec p) : ℤ) : ℝ) := by
              exact_mod_cast hg
          _ = ((p:ℝ)+10) * (2:ℝ)^(Work.Resample.auPrec p) := by push_cast; ring
      have h2P : (0:ℝ) < (2:ℝ)^(Work.Resample.auPrec p) := by positivity
      have hZp : (0:ℝ) ≤ (Work.Resample.auZ p α t N) := by exact_mod_cast hZ0
      have hy : 0 ≤ (Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p) :=
        div_nonneg hZp (le_of_lt h2P)
      have hexp1 : Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p))) ≤ 1 := by
        rw [Real.exp_le_one_iff]; exact neg_nonpos.mpr hy
      have hexp0 : 0 ≤ Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p))) :=
        le_of_lt (Real.exp_pos _)
      have hclose := Work.Resample.auHExpClose p hp (Work.Resample.auZ p α t N) hZ0 hZle
      have htri : |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)
            / (2:ℝ)^(Work.Resample.auPrec p)|
          ≤ |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)
                / (2:ℝ)^(Work.Resample.auPrec p)
              - Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p)))|
            + |Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p)))| := by
        have h := abs_add_le
          (((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)
              / (2:ℝ)^(Work.Resample.auPrec p)
            - Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p))))
          (Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p))))
        rwa [sub_add_cancel] at h
      have hstep : |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)
            / (2:ℝ)^(Work.Resample.auPrec p)| ≤ 1 + 2/(2:ℝ)^p := by
        have h3 : |Real.exp (-((Work.Resample.auZ p α t N) / (2:ℝ)^(Work.Resample.auPrec p)))| ≤ 1 := by
          rw [abs_of_nonneg hexp0]; exact hexp1
        linarith [le_trans htri (add_le_add hclose h3)]
      have hle2 : 1 + 2/(2:ℝ)^p ≤ 2 := by
        have h2p : (0:ℝ) < (2:ℝ)^p := by positivity
        have hle : (2:ℝ) ≤ (2:ℝ)^p := by
          calc (2:ℝ) = (2:ℝ)^1 := by norm_num
            _ ≤ (2:ℝ)^p := pow_le_pow_right₀ (by norm_num) hp1
        have : 2/(2:ℝ)^p ≤ 1 := (div_le_one h2p).mpr hle
        linarith
      have habs : |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)|
          ≤ (2:ℝ)^(Work.Resample.auPrec p + 1) := by
        have h1 : |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)|
            = |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)
                / (2:ℝ)^(Work.Resample.auPrec p)| * (2:ℝ)^(Work.Resample.auPrec p) := by
          rw [abs_div, abs_of_pos h2P, div_mul_cancel₀ _ (ne_of_gt h2P)]
        rw [h1]
        calc |((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p) : ℤ) : ℝ)
              / (2:ℝ)^(Work.Resample.auPrec p)| * (2:ℝ)^(Work.Resample.auPrec p)
            ≤ (1 + 2/(2:ℝ)^p) * (2:ℝ)^(Work.Resample.auPrec p) :=
              mul_le_mul_of_nonneg_right hstep (le_of_lt h2P)
          _ ≤ 2 * (2:ℝ)^(Work.Resample.auPrec p) :=
              mul_le_mul_of_nonneg_right hle2 (le_of_lt h2P)
          _ = (2:ℝ)^(Work.Resample.auPrec p + 1) := by rw [pow_succ]; ring
      have hnat : (Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p)).natAbs
          ≤ 2 ^ (Work.Resample.auPrec p + 1) := by
        have hnatR : ((Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p)).natAbs : ℝ)
            ≤ ((2:ℕ) ^ (Work.Resample.auPrec p + 1) : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
          push_cast
          exact habs
        exact_mod_cast hnatR
      have hD : ((2:ℤ)^(Work.Resample.auPrec p - p) * (2*(α:ℤ))).natAbs
          = 2 ^ (Work.Resample.auPrec p - p) * (2 * α) := by
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
        norm_num
      have hDge : 2 ^ (Work.Resample.auPrec p - p + 1)
          ≤ ((2:ℤ)^(Work.Resample.auPrec p - p) * (2*(α:ℤ))).natAbs := by
        rw [hD]
        calc 2 ^ (Work.Resample.auPrec p - p + 1) = 2 ^ (Work.Resample.auPrec p - p) * 2 := by
              rw [pow_succ]
          _ ≤ 2 ^ (Work.Resample.auPrec p - p) * (2 * α) := Nat.mul_le_mul_left _ (by omega)
      rw [Int.natAbs_tdiv]
      apply Nat.div_le_of_le_mul
      calc (Work.Resample.auH p (-(Work.Resample.auZ p α t N)) (Work.Resample.auNstep p)).natAbs
          ≤ 2 ^ (Work.Resample.auPrec p + 1) := hnat
        _ = 2 ^ (Work.Resample.auPrec p - p + 1) * 2 ^ p := by
            rw [← Nat.pow_add]; congr 1; simp only [Work.Resample.auPrec]; omega
        _ ≤ ((2:ℤ)^(Work.Resample.auPrec p - p) * (2*(α:ℤ))).natAbs * 2 ^ p :=
            Nat.mul_le_mul_right _ hDge
    · simp only [Int.natAbs_zero]
      exact Nat.zero_le _
  exact ⟨hmain, Work.ConvR.isz_le_of_natAbs_le hmain⟩

theorem auSetupSz (p α s t : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hst : s < t)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hu : u.length = s)
    (hd : ∀ z ∈ u, HvdH.inDisc p z) :
    (∀ k, HvdH.vsz (Work.Resample.auChunk p α s t u k)
      ≤ Work.Resample.auL p α * (3 * p + 16) + 4) ∧
    (HvdH.vsz (Work.Resample.auStreamV p α s t u)
      ≤ t * (Work.Resample.auL p α * (3 * p + 16) + 4) + t + 1) ∧
    (∀ k < t, ∀ v ∈ Work.Resample.auWts p α s t k, HvdH.vsz v ≤ p + 3) ∧
    (∀ v ∈ Work.Resample.auWinV p α s t u 0, HvdH.vsz v ≤ 2 * p + 8) ∧
    (∀ v ∈ Work.Resample.auElems p α s u, HvdH.vsz v ≤ 2 * p + 8) := by
  have ht1 : 1 ≤ t := by omega
  have hExt : ∀ j, HvdH.inDisc p ((Work.Resample.auExt p α s u).getD j (0, 0)) :=
    auExtDisc p α s u hs hu hd
  have hWin : ∀ k, ∀ z ∈ Work.Resample.auWin p α s t u k, HvdH.inDisc p z := by
    intro k z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
    exact hExt _
  have hWt : ∀ N, 0 ≤ N → HvdH.isz (Work.Resample.auWt p α t N) ≤ p + 3 :=
    fun N hN => (auWtSzNoHt p α t N hN ht1 hα hp).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact auChunk_vsz_le p α s t u (hWin k) (fun i _ => hWt _ (auNsq_nonneg p α s t k i))
  · exact (auStreamSz p α s t hs hst hα hp hαp u (fun k _ => hWin k)
      (fun k i _ _ => hWt _ (auNsq_nonneg p α s t k i))).2
  · intro k hk v hv
    rw [Work.Resample.auWts] at hv
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    rw [Work.ConvR.vsz_int]
    exact hWt _ (auNsq_nonneg p α s t k i)
  · intro v hv
    rw [Work.Resample.auWinV] at hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    calc HvdH.vsz (HvdH.cfxVal z) ≤ Work.ConvR.cfxSz p :=
          Work.ConvR.vsz_cfxVal_le (hWin 0 z hz)
      _ = 2 * p + 8 := rfl
  · intro v hv
    rw [Work.Resample.auElems] at hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have hzd : HvdH.inDisc p z := by
      rw [Work.Resample.auExt] at hz
      obtain ⟨a, ha, hza⟩ : ∃ a, a ∈ List.replicate (Work.Resample.auCop p α s) u ∧ z ∈ a :=
        List.mem_flatten.mp (List.mem_of_mem_drop (List.mem_of_mem_drop hz))
      obtain ⟨-, rfl⟩ := List.mem_replicate.mp ha
      exact hd z hza
    calc HvdH.vsz (HvdH.cfxVal z) ≤ Work.ConvR.cfxSz p := Work.ConvR.vsz_cfxVal_le hzd
      _ = 2 * p + 8 := rfl

end Work.Resample

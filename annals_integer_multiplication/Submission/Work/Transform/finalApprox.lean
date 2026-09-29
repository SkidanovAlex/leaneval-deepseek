import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.finalAux
import Submission.Work.Transform.bluestein
import Submission.Work.Transform.eps_mul
import Submission.Work.Transform.phiArrL_norm
import Submission.Work.Transform.psiFlatL_norm
import Submission.Work.Transform.psiFlatL_phiArrL
import Submission.Work.Transform.chirp_norm
import Submission.Work.Transform.convR_norm
import Submission.Work.Transform.convR_sub
import Submission.Work.Transform.final_arith
import Submission.Work.Transform.convC_bridge

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Transform

open HvdH

/-! ## Scalar bookkeeping helpers for the error chain -/

/-- Scalar triangle inequality with non-strict bounds. -/
theorem scaled_triangle_le (p : ℕ) (x y z : ℂ) (b c : ℝ)
    (h1 : (2 : ℝ) ^ p * ‖x - y‖ ≤ b) (h2 : (2 : ℝ) ^ p * ‖y - z‖ ≤ c) :
    (2 : ℝ) ^ p * ‖x - z‖ ≤ b + c := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : x - z = (x - y) + (y - z) := by ring
  calc (2 : ℝ) ^ p * ‖x - z‖ = (2 : ℝ) ^ p * ‖(x - y) + (y - z)‖ := by rw [hdec]
    _ ≤ (2 : ℝ) ^ p * (‖x - y‖ + ‖y - z‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hp0
    _ = (2 : ℝ) ^ p * ‖x - y‖ + (2 : ℝ) ^ p * ‖y - z‖ := by ring
    _ ≤ b + c := by linarith

/-- Scalar product error bound. -/
theorem scaled_mul_bound (p : ℕ) (x y f g : ℂ) (Cg Ch : ℝ)
    (hg : ‖y‖ ≤ Cg) (hh : ‖f‖ ≤ Ch) :
    (2 : ℝ) ^ p * ‖x * y - f * g‖ ≤ Cg * ((2 : ℝ) ^ p * ‖x - f‖) + Ch * ((2 : ℝ) ^ p * ‖y - g‖) := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : x * y - f * g = (x - f) * y + f * (y - g) := by ring
  have h1 : ‖x * y - f * g‖ ≤ ‖x - f‖ * Cg + Ch * ‖y - g‖ := by
    rw [hdec]
    calc ‖(x - f) * y + f * (y - g)‖ ≤ ‖(x - f) * y‖ + ‖f * (y - g)‖ := norm_add_le _ _
      _ = ‖x - f‖ * ‖y‖ + ‖f‖ * ‖y - g‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖x - f‖ * Cg + Ch * ‖y - g‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
                     (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
  calc (2 : ℝ) ^ p * ‖x * y - f * g‖ ≤ (2 : ℝ) ^ p * (‖x - f‖ * Cg + Ch * ‖y - g‖) :=
        mul_le_mul_of_nonneg_left h1 hp0
    _ = Cg * ((2 : ℝ) ^ p * ‖x - f‖) + Ch * ((2 : ℝ) ^ p * ‖y - g‖) := by ring

/-- Shifting a scaled error bound by a common right factor. -/
theorem scaled_shift_left (p : ℕ) (x y f : ℂ) (C : ℝ) (hf : ‖f‖ ≤ C) :
    (2 : ℝ) ^ p * ‖x * f - y * f‖ ≤ C * ((2 : ℝ) ^ p * ‖x - y‖) := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : x * f - y * f = (x - y) * f := by ring
  rw [hdec, norm_mul]
  calc (2 : ℝ) ^ p * (‖x - y‖ * ‖f‖) ≤ (2 : ℝ) ^ p * (‖x - y‖ * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (norm_nonneg _)) hp0
    _ = C * ((2 : ℝ) ^ p * ‖x - y‖) := by ring

/-- Shifting a scaled error bound by a common left factor. -/
theorem scaled_shift_right (p : ℕ) (f x y : ℂ) (C : ℝ) (hf : ‖f‖ ≤ C) :
    (2 : ℝ) ^ p * ‖f * x - f * y‖ ≤ C * ((2 : ℝ) ^ p * ‖x - y‖) := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : f * x - f * y = f * (x - y) := by ring
  rw [hdec, norm_mul]
  calc (2 : ℝ) ^ p * (‖f‖ * ‖x - y‖) ≤ (2 : ℝ) ^ p * (C * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf (norm_nonneg _)) hp0
    _ = C * ((2 : ℝ) ^ p * ‖x - y‖) := by ring

/-- A pointwise scaled error bound gives the same bound for the sup norm (arbitrary values). -/
theorem supScaledLe {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (p : ℕ) (f g : ι → E)
    (b : ℝ) (hb : 0 ≤ b) (h : ∀ i, (2 : ℝ) ^ p * ‖f i - g i‖ ≤ b) :
    (2 : ℝ) ^ p * ‖f - g‖ ≤ b := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h1 : ‖f - g‖ ≤ ((2 : ℝ) ^ p)⁻¹ * b := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
    rw [Pi.sub_apply]
    have h2 := mul_le_mul_of_nonneg_left (h i) (le_of_lt (inv_pos.mpr hp))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hp), one_mul] at h2
  calc (2 : ℝ) ^ p * ‖f - g‖ ≤ (2 : ℝ) ^ p * (((2 : ℝ) ^ p)⁻¹ * b) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
    _ = b := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul]

/-- Sup-norm version of the scaled triangle inequality (non-strict). -/
theorem supScaledTriangle {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (p : ℕ)
    (f g h : ι → E) (b c : ℝ)
    (h1 : (2 : ℝ) ^ p * ‖f - g‖ ≤ b) (h2 : (2 : ℝ) ^ p * ‖g - h‖ ≤ c) :
    (2 : ℝ) ^ p * ‖f - h‖ ≤ b + c := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : f - h = (f - g) + (g - h) := by abel
  calc (2 : ℝ) ^ p * ‖f - h‖ = (2 : ℝ) ^ p * ‖(f - g) + (g - h)‖ := by rw [hdec]
    _ ≤ (2 : ℝ) ^ p * (‖f - g‖ + ‖g - h‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hp0
    _ = (2 : ℝ) ^ p * ‖f - g‖ + (2 : ℝ) ^ p * ‖g - h‖ := by ring
    _ ≤ b + c := by linarith

/-- Evaluation of a difference is bounded by the sup norm of the difference. -/
theorem evalScaledLe {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (p : ℕ)
    (f g : ι → E) (i : ι) :
    (2 : ℝ) ^ p * ‖f i - g i‖ ≤ (2 : ℝ) ^ p * ‖f - g‖ :=
  mul_le_mul_of_nonneg_left (norm_le_pi_norm (f - g) i) (by positivity)

/-- Error bookkeeping of Theorem 3.1: given the pointwise `2^p`-scaled error bounds of the pipeline (zeta tables, chirp tables, pointwise products, the Phi-images ua/ub, the convR output w and the final psi/mul steps), the output approximates the DFT of the input with error below `8 T log2 T`; `hlog : D <= Nat.log 2 T` is the domination hypothesis (`T >= 2^D`) that the ambient `PowTwoParams` provides.  Uses `Work.Transform.eps_mul`, `convR_norm`, `convR_sub`, `phiArrL_norm`, `psiFlatL_norm`, `chirp_norm`, `Work.Transform.bluestein` and the bridge `Work.Transform.convC_bridge` (which is currently only stated -- a prover may have to prove it or wait). -/
theorem finalApprox (p r M T : ℕ) (ts ts' : List ℕ)
    (zs zst zstie a ab b c z : List (ℤ × ℤ))
    (w ua ub : List (List (ℤ × ℤ)))
    (hsplit : ts = ts' ++ [r]) (hT : T = M * r)
    (hlog : HvdH.D ≤ Nat.log 2 T) (hT3 : 3 ≤ T)
    (hpos : ∀ t ∈ ts, 0 < t) (heven : ∀ t ∈ ts, Even t)
    (hzlen : zs.length = T) (hp : 100 ≤ p)
    (hzD1 : HvdH.InDiscVec p T zst) (hzD2 : HvdH.InDiscVec p T zstie)
    (hzE1 : ∀ i < T, (2:ℝ)^p * ‖HvdH.fxC p (zst.getD i (0,0)) - Work.Transform.zeta r (i % r)‖ < 2)
    (hzE2 : ∀ i < T, (2:ℝ)^p * ‖HvdH.fxC p (zstie.getD i (0,0)) -
      Work.Transform.zetaInv r (i % r)‖ < 2)
    (hcaD : HvdH.InDiscVec p T a) (habD : HvdH.InDiscVec p T ab)
    (hcaE : ∀ j < T, (2:ℝ)^p * ‖HvdH.fxC p (a.getD j (0,0)) - Work.Transform.chirp ts j‖ < 4 * HvdH.D)
    (habE : ∀ j < T, (2:ℝ)^p * ‖HvdH.fxC p (ab.getD j (0,0)) -
      star (Work.Transform.chirp ts j)‖ < 4 * HvdH.D)
    (hbD : HvdH.InDiscVec p T b)
    (hbE : ∀ i < T, (2:ℝ)^p * ‖HvdH.fxC p (b.getD i (0,0))
        - HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖ < 2)
    (hubD : HvdH.InDiscArr p M r ub) (hubrow : ∀ α < M, (ub.getD α []).length = r)
    (hubE : ∀ α < M, ∀ γ < r, (2:ℝ)^p * ‖HvdH.fxC p ((ub.getD α []).getD γ (0,0))
        - HvdH.fxC p (zst.getD (α*r+γ) (0,0)) * HvdH.fxC p (b.getD (α*r+γ) (0,0))‖ < 2)
    (huaD : HvdH.InDiscArr p M r ua) (huarow : ∀ α < M, (ua.getD α []).length = r)
    (huaE : ∀ α < M, ∀ γ < r, (2:ℝ)^p * ‖HvdH.fxC p ((ua.getD α []).getD γ (0,0))
        - HvdH.fxC p (zst.getD (α*r+γ) (0,0)) * HvdH.fxC p (a.getD (α*r+γ) (0,0))‖ < 2)
    (hwlen : w.length = M) (hwrow : ∀ α < M, (w.getD α []).length = r)
    (hwD : HvdH.InDiscArr p M r w)
    (hprod : ts.prod = T) (hMts : ts'.prod = M)
    (hwE : HvdH.ApproxR p w (HvdH.convR r ts' (HvdH.fxArr p ts'.prod r ua)
      (HvdH.fxArr p ts'.prod r ub))
      ((3 * (M * r) * Nat.log 2 (M * r) + 2 * (M * r) + 3 : ℕ) : ℝ))
    (hcD : HvdH.InDiscVec p T c)
    (hcE : ∀ i < T, (2:ℝ)^p * ‖HvdH.fxC p (c.getD i (0,0))
        - HvdH.fxC p (zstie.getD i (0,0)) * HvdH.fxC p ((w.getD (i / r) []).getD (i % r) (0,0))‖ < 2)
    (hzD : HvdH.InDiscVec p T z)
    (hzE : ∀ i < T, (2:ℝ)^p * ‖HvdH.fxC p (z.getD i (0,0))
        - HvdH.fxC p (c.getD i (0,0)) * HvdH.fxC p (ab.getD i (0,0))‖ < 2) :
    HvdH.Approx p z (HvdH.dftMulti ts (-1) (HvdH.fxVec p ts.prod zs))
      ((8 * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ) := by
  subst hsplit
  subst hT
  subst hMts
  have hpos' : ∀ t ∈ ts', 0 < t := fun t ht => hpos t (by simp [ht])
  have hr : 0 < r := hpos r (by simp)
  refine ⟨hprod.symm ▸ hzD, ?_⟩
  -- #### the abstract objects of the pipeline
  set U : Fin ((ts' ++ [r]).prod) → ℂ := HvdH.fxVec p ((ts' ++ [r]).prod) zs with hU
  set Wf : Fin ts'.prod → Fin r → ℂ := HvdH.fxArr p ts'.prod r w with hWf
  set Cx : Fin ts'.prod → Fin r → ℂ := HvdH.fxArr p ts'.prod r ua with hCx
  set Ky : Fin ts'.prod → Fin r → ℂ := HvdH.fxArr p ts'.prod r ub with hKy
  set TA : Fin ts'.prod → Fin r → ℂ
    := phiArrL r ts' (fun k : Fin ((ts' ++ [r]).prod) => chirp (ts' ++ [r]) k) with hTA
  set TB : Fin ts'.prod → Fin r → ℂ
    := phiArrL r ts' (fun k : Fin ((ts' ++ [r]).prod) => star (chirp (ts' ++ [r]) k) * U k)
    with hTB
  set tW : Fin ts'.prod → Fin r → ℂ := HvdH.convR r ts' TA TB with htW
  set tC : Fin ((ts' ++ [r]).prod) → ℂ := psiFlatL r ts' tW with htC
  set tZ : Fin ((ts' ++ [r]).prod) → ℂ := fun i => star (chirp (ts' ++ [r]) i) * tC i with htZ
  set eR : ℝ := ((3 * (ts'.prod * r) * Nat.log 2 (ts'.prod * r) + 2 * (ts'.prod * r) + 3 : ℕ) : ℝ)
    with heR
  -- #### step B2: b is close to (conj chirp) * zs
  have hB2 : ∀ j, j < ts'.prod * r → (2:ℝ)^p * ‖HvdH.fxC p (b.getD j (0,0))
      - star (chirp (ts'++[r]) j) * HvdH.fxC p (zs.getD j (0,0))‖ ≤ 12 * (HvdH.D:ℝ) + 2 := by
    intro j hj
    have hb := hbE j hj
    have hab := habE j hj
    have hUj : ‖HvdH.fxC p (zs.getD j (0,0))‖ ≤ 3 :=
      zsNormLeThree p (ts'.prod*r) (ts'++[r]) hp zs ab b hbD habE hbE j hj
    have hstar : ‖star (chirp (ts'++[r]) j)‖ = 1 := by rw [norm_star, chirp_norm]
    have hshift : (2:ℝ)^p * ‖HvdH.fxC p (ab.getD j (0,0)) * HvdH.fxC p (zs.getD j (0,0))
        - star (chirp (ts'++[r]) j) * HvdH.fxC p (zs.getD j (0,0))‖ ≤ 12 * (HvdH.D:ℝ) := by
      have hs := scaled_shift_left p (HvdH.fxC p (ab.getD j (0,0)))
        (star (chirp (ts'++[r]) j)) (HvdH.fxC p (zs.getD j (0,0))) 3 hUj
      have hs' : 3 * ((2:ℝ)^p * ‖HvdH.fxC p (ab.getD j (0,0))
          - star (chirp (ts'++[r]) j)‖) ≤ 3 * (4 * (HvdH.D:ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hab) (by norm_num)
      linarith [hs, hs']
    linarith [scaled_triangle_le p (HvdH.fxC p (b.getD j (0,0)))
      (HvdH.fxC p (ab.getD j (0,0)) * HvdH.fxC p (zs.getD j (0,0)))
      (star (chirp (ts'++[r]) j) * HvdH.fxC p (zs.getD j (0,0)))
      2 (12 * (HvdH.D:ℝ)) (le_of_lt hb) hshift]
  -- #### step UA: Cx is close to TA
  have hUA : ∀ (al : Fin ts'.prod) (gm : Fin r),
      (2:ℝ)^p * ‖Cx al gm - TA al gm‖ ≤ 4 * (HvdH.D:ℝ) + 4 := by
    intro al gm
    have hnc : (gm:ℕ) < r := gm.isLt
    have hflat : (al:ℕ) * r + (gm:ℕ) < ts'.prod * r := by
      calc (al:ℕ) * r + (gm:ℕ) < (al:ℕ) * r + r := Nat.add_lt_add_left hnc _
        _ = ((al:ℕ) + 1) * r := by rw [Nat.succ_mul]
        _ ≤ ts'.prod * r := Nat.mul_le_mul_right r (Nat.succ_le_of_lt al.isLt)
    have h1 : (2:ℝ)^p * ‖Cx al gm - HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        * HvdH.fxC p (a.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))‖ < 2 := by
      rw [hCx]; exact huaE (al:ℕ) al.isLt (gm:ℕ) hnc
    have hAf1 : ‖HvdH.fxC p (a.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))‖ ≤ 1 :=
      Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD hcaD
        ⟨(al:ℕ)*r + (gm:ℕ), hflat⟩)
    have hTAc : TA al gm = zeta r (((al:ℕ)*r + (gm:ℕ)) % r)
        * chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)) := by
      show zeta r (gm:ℕ) * chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ))
        = zeta r (((al:ℕ)*r + (gm:ℕ)) % r) * chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ))
      rw [← zeta_mod_eq r (al:ℕ) (gm:ℕ) hnc]
    have hstep : (2:ℝ)^p * ‖HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        * HvdH.fxC p (a.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        - zeta r (((al:ℕ)*r + (gm:ℕ)) % r) * chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ))‖
        ≤ 4 * (HvdH.D:ℝ) + 2 := by
      have hm := scaled_mul_bound p (HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
        (HvdH.fxC p (a.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
        (zeta r (((al:ℕ)*r + (gm:ℕ)) % r)) (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ))) 1 1 hAf1
        (le_of_eq (norm_zeta r _))
      have hZf := hzE1 _ hflat
      have hAf := hcaE _ hflat
      nlinarith [hm, hZf, hAf]
    rw [hTAc]
    linarith [scaled_triangle_le p (Cx al gm)
      (HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        * HvdH.fxC p (a.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
      (zeta r (((al:ℕ)*r + (gm:ℕ)) % r) * chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
      2 (4 * (HvdH.D:ℝ) + 2) (le_of_lt h1) hstep]
  -- #### step UB: Ky is close to TB
  have hUB : ∀ (al : Fin ts'.prod) (gm : Fin r),
      (2:ℝ)^p * ‖Ky al gm - TB al gm‖ ≤ 12 * (HvdH.D:ℝ) + 6 := by
    intro al gm
    have hnc : (gm:ℕ) < r := gm.isLt
    have hflat : (al:ℕ) * r + (gm:ℕ) < ts'.prod * r := by
      calc (al:ℕ) * r + (gm:ℕ) < (al:ℕ) * r + r := Nat.add_lt_add_left hnc _
        _ = ((al:ℕ) + 1) * r := by rw [Nat.succ_mul]
        _ ≤ ts'.prod * r := Nat.mul_le_mul_right r (Nat.succ_le_of_lt al.isLt)
    have h1 : (2:ℝ)^p * ‖Ky al gm - HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        * HvdH.fxC p (b.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))‖ < 2 := by
      rw [hKy]; exact hubE (al:ℕ) al.isLt (gm:ℕ) hnc
    have hBf1 : ‖HvdH.fxC p (b.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))‖ ≤ 1 :=
      Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD hbD
        ⟨(al:ℕ)*r + (gm:ℕ), hflat⟩)
    have hTBc : TB al gm = zeta r (((al:ℕ)*r + (gm:ℕ)) % r)
        * (star (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
           * HvdH.fxC p (zs.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))) := by
      show zeta r (gm:ℕ) * (star (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
          * HvdH.fxC p (zs.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
        = zeta r (((al:ℕ)*r + (gm:ℕ)) % r) * (star (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
          * HvdH.fxC p (zs.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
      rw [← zeta_mod_eq r (al:ℕ) (gm:ℕ) hnc]
    have hstep : (2:ℝ)^p * ‖HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        * HvdH.fxC p (b.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        - zeta r (((al:ℕ)*r + (gm:ℕ)) % r)
          * (star (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
             * HvdH.fxC p (zs.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))‖
        ≤ 12 * (HvdH.D:ℝ) + 4 := by
      have hm := scaled_mul_bound p (HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
        (HvdH.fxC p (b.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
        (zeta r (((al:ℕ)*r + (gm:ℕ)) % r))
        (star (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
           * HvdH.fxC p (zs.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))) 1 1 hBf1
        (le_of_eq (norm_zeta r _))
      have hZf := hzE1 _ hflat
      have hB := hB2 _ hflat
      nlinarith [hm, hZf, hB]
    rw [hTBc]
    linarith [scaled_triangle_le p (Ky al gm)
      (HvdH.fxC p (zst.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))
        * HvdH.fxC p (b.getD ((al:ℕ)*r + (gm:ℕ)) (0,0)))
      (zeta r (((al:ℕ)*r + (gm:ℕ)) % r)
        * (star (chirp (ts'++[r]) ((al:ℕ)*r + (gm:ℕ)))
           * HvdH.fxC p (zs.getD ((al:ℕ)*r + (gm:ℕ)) (0,0))))
      2 (12 * (HvdH.D:ℝ) + 4) (le_of_lt h1) hstep]
  -- #### sup-norm bounds for the convR arguments
  have hCxTA : (2:ℝ)^p * ‖Cx - TA‖ ≤ 4 * (HvdH.D:ℝ) + 4 := by
    refine supScaledLe p Cx TA _ (by positivity) (fun a => ?_)
    exact supScaledLe p (Cx a) (TA a) _ (by positivity) (fun c => hUA a c)
  have hKyTB : (2:ℝ)^p * ‖Ky - TB‖ ≤ 12 * (HvdH.D:ℝ) + 6 := by
    refine supScaledLe p Ky TB _ (by positivity) (fun a => ?_)
    exact supScaledLe p (Ky a) (TB a) _ (by positivity) (fun c => hUB a c)
  have hTB3 : ‖TB‖ ≤ 3 := by
    rw [hTB]
    refine le_trans (phiArrL_norm r ts' _) ?_
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 (fun k => ?_)
    rw [norm_mul]
    have hk : (k:ℕ) < ts'.prod * r := by rw [← hprod]; exact k.isLt
    have h1 : ‖star (chirp (ts'++[r]) (k:ℕ))‖ = 1 := by rw [norm_star, chirp_norm]
    rw [h1, one_mul, hU]
    exact zsNormLeThree p (ts'.prod*r) (ts'++[r]) hp zs ab b hbD habE hbE (k:ℕ) hk
  have hKy1 : ‖Ky‖ ≤ 1 := by
    rw [hKy]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun a => ?_)
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun c =>
      Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscArr.getD hubD a c))
  have hTA1 : ‖TA‖ ≤ 1 := by
    rw [hTA]
    refine le_trans (phiArrL_norm r ts' _) ?_
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2
      (fun k => le_of_eq (chirp_norm (ts'++[r]) (k:ℕ)))
  -- #### step W: the convR output
  have hWconv : (2:ℝ)^p * ‖Wf - HvdH.convR r ts' Cx Ky‖ ≤ eR := by
    refine supScaledLe p Wf (HvdH.convR r ts' Cx Ky) eR ?_ (fun a => ?_)
    · rw [heR]; exact Nat.cast_nonneg _
    · exact supScaledLe p (Wf a) (HvdH.convR r ts' Cx Ky a) eR
        (by rw [heR]; exact Nat.cast_nonneg _) (fun c => le_of_lt (hwE.2 a c))
  have hWt : (2:ℝ)^p * ‖Wf - tW‖ ≤ eR + 16 * (HvdH.D:ℝ) + 10 := by
    rw [htW]
    have hcr := convRScaledErr p r ts' hpos' Cx TA Ky TB
    have h1 : (0:ℝ) ≤ ‖Ky‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ (2:ℝ)^p * ‖Cx - TA‖ := by positivity
    have h3 : (0:ℝ) ≤ ‖TA‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ (2:ℝ)^p * ‖Ky - TB‖ := by positivity
    have hstep : (2:ℝ)^p * ‖HvdH.convR r ts' Cx Ky - HvdH.convR r ts' TA TB‖
        ≤ 16 * (HvdH.D:ℝ) + 10 := by
      nlinarith [hcr, hKy1, hTA1, hCxTA, hKyTB, h1, h2, h3, h4]
    have hcomb := supScaledTriangle p Wf (HvdH.convR r ts' Cx Ky)
      (HvdH.convR r ts' TA TB) eR (16 * (HvdH.D:ℝ) + 10) hWconv hstep
    linarith [hcomb]
  -- #### step C: the psi step
  have hCT : ∀ i : Fin ((ts'++[r]).prod),
      (2:ℝ)^p * ‖HvdH.fxC p (c.getD (i:ℕ) (0,0)) - tC i‖ ≤ eR + 16 * (HvdH.D:ℝ) + 14 := by
    intro i
    have hii : (i:ℕ) < ts'.prod * r := by rw [← hprod]; exact i.isLt
    have hi1 : (i:ℕ) / r < ts'.prod := (Nat.div_lt_iff_lt_mul hr).2 hii
    have hi2 : (i:ℕ) % r < r := Nat.mod_lt _ hr
    have htCi : tC i = (zeta r ((i:ℕ) % r))⁻¹
        * tW ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩ := by
      rw [htC]; rfl
    have h1 : (2:ℝ)^p * ‖HvdH.fxC p (c.getD (i:ℕ) (0,0))
        - HvdH.fxC p (zstie.getD (i:ℕ) (0,0))
          * Wf ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩‖ < 2 := by
      rw [hWf]; exact hcE (i:ℕ) hii
    have hWnorm : ‖Wf ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩‖ ≤ 1 := by
      rw [hWf]
      exact Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscArr.getD hwD ⟨_, hi1⟩ ⟨_, hi2⟩)
    have hSinorm : ‖(zeta r ((i:ℕ) % r))⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_zeta, inv_one]
    have hwit : (2:ℝ)^p * ‖Wf ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩
        - tW ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩‖ ≤ eR + 16 * (HvdH.D:ℝ) + 10 :=
      le_trans (evalScaledLe p (Wf ⟨(i:ℕ)/r, hi1⟩) (tW ⟨(i:ℕ)/r, hi1⟩) ⟨(i:ℕ)%r, hi2⟩)
        (le_trans (evalScaledLe p Wf tW ⟨(i:ℕ)/r, hi1⟩) hWt)
    have hZf : (2:ℝ)^p * ‖HvdH.fxC p (zstie.getD (i:ℕ) (0,0))
        - (zeta r ((i:ℕ) % r))⁻¹‖ < 2 := hzE2 (i:ℕ) hii
    rw [htCi]
    have hprod : (2:ℝ)^p * ‖HvdH.fxC p (zstie.getD (i:ℕ) (0,0))
          * Wf ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩
          - (zeta r ((i:ℕ) % r))⁻¹ * tW ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩‖
        ≤ 2 + (eR + 16 * (HvdH.D:ℝ) + 10) := by
      have hm := scaled_mul_bound p (HvdH.fxC p (zstie.getD (i:ℕ) (0,0)))
        (Wf ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩) ((zeta r ((i:ℕ) % r))⁻¹)
        (tW ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩) 1 1 hWnorm hSinorm
      nlinarith [hm, hZf, hwit]
    linarith [scaled_triangle_le p (HvdH.fxC p (c.getD (i:ℕ) (0,0)))
      (HvdH.fxC p (zstie.getD (i:ℕ) (0,0)) * Wf ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩)
      ((zeta r ((i:ℕ) % r))⁻¹ * tW ⟨(i:ℕ)/r, hi1⟩ ⟨(i:ℕ)%r, hi2⟩)
      2 (2 + (eR + 16 * (HvdH.D:ℝ) + 10)) (le_of_lt h1) hprod]
  -- #### step Z: the final pointwise product
  have hTI : ∀ i : Fin ((ts'++[r]).prod),
      (2:ℝ)^p * ‖HvdH.fxC p (c.getD (i:ℕ) (0,0)) * HvdH.fxC p (ab.getD (i:ℕ) (0,0))
        - tC i * star (chirp (ts'++[r]) i)‖ ≤ eR + 28 * (HvdH.D:ℝ) + 14 := by
    intro i
    have hii : (i:ℕ) < ts'.prod * r := by rw [← hprod]; exact i.isLt
    have hAbf1 : ‖HvdH.fxC p (ab.getD (i:ℕ) (0,0))‖ ≤ 1 :=
      Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD habD ⟨(i:ℕ), hii⟩)
    have hct3 : ‖tC i‖ ≤ 3 := by
      have h1 : ‖tC i‖ ≤ ‖tW‖ := by
        rw [htC]
        exact le_trans (norm_le_pi_norm (psiFlatL r ts' tW) i) (psiFlatL_norm r ts' tW)
      calc ‖tC i‖ ≤ ‖tW‖ := h1
        _ ≤ ‖TA‖ * ‖TB‖ := convR_norm r ts' hpos' TA TB
        _ ≤ 3 := by nlinarith [hTA1, hTB3, norm_nonneg TA, norm_nonneg TB]
    have ha : (2:ℝ)^p * ‖HvdH.fxC p (c.getD (i:ℕ) (0,0)) * HvdH.fxC p (ab.getD (i:ℕ) (0,0))
        - tC i * HvdH.fxC p (ab.getD (i:ℕ) (0,0))‖ ≤ 1 * (eR + 16 * (HvdH.D:ℝ) + 14) := by
      have hs := scaled_shift_left p (HvdH.fxC p (c.getD (i:ℕ) (0,0))) (tC i)
        (HvdH.fxC p (ab.getD (i:ℕ) (0,0))) 1 hAbf1
      have hc := hCT i
      linarith [hs, hc]
    have hb : (2:ℝ)^p * ‖tC i * HvdH.fxC p (ab.getD (i:ℕ) (0,0))
        - tC i * star (chirp (ts'++[r]) i)‖ ≤ 3 * (4 * (HvdH.D:ℝ)) := by
      have hs := scaled_shift_right p (tC i) (HvdH.fxC p (ab.getD (i:ℕ) (0,0)))
        (star (chirp (ts'++[r]) i)) 3 hct3
      have hab := habE (i:ℕ) hii
      linarith [hs, hab]
    linarith [scaled_triangle_le p
      (HvdH.fxC p (c.getD (i:ℕ) (0,0)) * HvdH.fxC p (ab.getD (i:ℕ) (0,0)))
      (tC i * HvdH.fxC p (ab.getD (i:ℕ) (0,0))) (tC i * star (chirp (ts'++[r]) i))
      (1 * (eR + 16 * (HvdH.D:ℝ) + 14)) (3 * (4 * (HvdH.D:ℝ))) ha hb]
  -- #### the bridge: the DFT is the flattening of the synthetic convolution
  have hbridge : ∀ i : Fin ((ts'++[r]).prod),
      HvdH.dftMulti (ts'++[r]) (-1) U i = tZ i := by
    intro j
    have hb := bluestein (ts'++[r]) hpos heven U
    rw [hb]
    dsimp only
    rw [convC_bridge ts' r hr hpos']
  -- #### assembly
  intro i
  have hii : (i:ℕ) < ts'.prod * r := by rw [← hprod]; exact i.isLt
  have hfin : (2:ℝ)^p * ‖HvdH.fxC p (z.getD (i:ℕ) (0,0)) - tZ i‖
      ≤ eR + 28 * (HvdH.D:ℝ) + 16 := by
    have h1 : (2:ℝ)^p * ‖HvdH.fxC p (z.getD (i:ℕ) (0,0))
        - HvdH.fxC p (c.getD (i:ℕ) (0,0)) * HvdH.fxC p (ab.getD (i:ℕ) (0,0))‖ ≤ 2 :=
      le_of_lt (hzE (i:ℕ) hii)
    have h2 : (2:ℝ)^p * ‖HvdH.fxC p (c.getD (i:ℕ) (0,0)) * HvdH.fxC p (ab.getD (i:ℕ) (0,0))
        - tZ i‖ ≤ eR + 28 * (HvdH.D:ℝ) + 14 := by
      rw [htZ]
      dsimp only
      rw [mul_comm (star (chirp (ts'++[r]) i)) (tC i)]
      exact hTI i
    linarith [scaled_triangle_le p (HvdH.fxC p (z.getD (i:ℕ) (0,0)))
      (HvdH.fxC p (c.getD (i:ℕ) (0,0)) * HvdH.fxC p (ab.getD (i:ℕ) (0,0))) (tZ i)
      2 (eR + 28 * (HvdH.D:ℝ) + 14) h1 h2]
  rw [hbridge i]
  have htarget : ((8 * (ts'++[r]).prod * Nat.log 2 ((ts'++[r]).prod) : ℕ) : ℝ)
      = 8 * ((ts'.prod*r:ℕ):ℝ) * (Nat.log 2 (ts'.prod*r) : ℝ) := by
    rw [hprod]; push_cast; ring
  rw [htarget]
  have harith := finalArith (ts'.prod*r) hlog hT3
  have heR' : eR = 3 * ((ts'.prod*r:ℕ):ℝ) * (Nat.log 2 (ts'.prod*r) : ℝ)
      + 2 * ((ts'.prod*r:ℕ):ℝ) + 3 := by
    rw [heR]; push_cast; ring
  have hDnn : (0:ℝ) ≤ (HvdH.D:ℝ) := Nat.cast_nonneg _
  linarith [hfin, harith, heR', hDnn]

end Work.Transform

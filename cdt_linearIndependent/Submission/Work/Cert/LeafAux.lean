import Mathlib
import Submission.Work.Cert.Spec

/-! # Shared definitions and rounding lemmas for the Theorem-A arc certificate

This file collects, for the soundness proofs of `Work.Cert.leafOK` / `Work.Cert.windLeafOK`:
* the elementary rounding facts for `md` (floor product), `mu` (ceil product), `dvu` (ceil quotient),
* the elementary facts about `cx` (scaled complex numbers),
* the exact arithmetic identities satisfied by the stage constants `s{j}*`,
* named definitions for the ψ_A stage chain inside `leafOK` and for the θ-series data.

Everything here is proved; there are no unfinished proofs. -/

set_option maxRecDepth 100000

namespace Work.Cert
open Complex Submission.CDTPlan

/-! ## The scale -/

lemma S_pos : (0 : ℤ) < S := by norm_num [S]
lemma S_posR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos
lemma S_ne : (S : ℤ) ≠ 0 := ne_of_gt S_pos

/-! ## Integer rounding facts -/

/-- `md a b = ⌊ab/S⌋` is below `ab/S`. -/
lemma md_le (a b : ℤ) : ((md a b : ℤ) : ℝ) ≤ (a : ℝ) * (b : ℝ) / (S : ℝ) := by
  have h : Int.ediv (a * b) S * S ≤ a * b := Int.ediv_mul_le _ (ne_of_gt S_pos)
  have h2 : ((Int.ediv (a * b) S : ℤ) : ℝ) * (S : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    exact_mod_cast h
  rw [md, fdiv, le_div_iff₀ S_posR]
  linarith

/-- `md a b = ⌊ab/S⌋` is above `ab/S - 1`. -/
lemma md_gt (a b : ℤ) : (a : ℝ) * (b : ℝ) / (S : ℝ) - 1 < ((md a b : ℤ) : ℝ) := by
  have h : a * b < (Int.ediv (a * b) S + 1) * S := Int.lt_ediv_add_one_mul_self _ S_pos
  have h2 : (a : ℝ) * (b : ℝ) < (((Int.ediv (a * b) S : ℤ) : ℝ) + 1) * (S : ℝ) := by
    exact_mod_cast h
  rw [md, fdiv, sub_lt_iff_lt_add, div_lt_iff₀ S_posR]
  linarith

/-- `mu a b = ⌈ab/S⌉ ≥ ab/S`. -/
lemma mu_ge (a b : ℤ) : (a : ℝ) * (b : ℝ) / (S : ℝ) ≤ ((mu a b : ℤ) : ℝ) := by
  have h : Int.ediv (-(a * b)) S * S ≤ -(a * b) := Int.ediv_mul_le _ (ne_of_gt S_pos)
  have h2 : ((Int.ediv (-(a * b)) S : ℤ) : ℝ) * (S : ℝ) ≤ -((a : ℝ) * (b : ℝ)) := by
    exact_mod_cast h
  have h3 : ((mu a b : ℤ) : ℝ) = -((Int.ediv (-(a * b)) S : ℤ) : ℝ) := by
    rw [mu, fdiv]; push_cast; ring
  rw [h3, div_le_iff₀ S_posR]
  linarith

/-- `mu a b = ⌈ab/S⌉ < ab/S + 1`. -/
lemma mu_lt (a b : ℤ) : ((mu a b : ℤ) : ℝ) < (a : ℝ) * (b : ℝ) / (S : ℝ) + 1 := by
  have h : -(a * b) < (Int.ediv (-(a * b)) S + 1) * S := Int.lt_ediv_add_one_mul_self _ S_pos
  have h2 : -((a : ℝ) * (b : ℝ)) < (((Int.ediv (-(a * b)) S : ℤ) : ℝ) + 1) * (S : ℝ) := by
    exact_mod_cast h
  have h3 : ((mu a b : ℤ) : ℝ) = -((Int.ediv (-(a * b)) S : ℤ) : ℝ) := by
    rw [mu, fdiv]; push_cast; ring
  rw [h3, ← sub_lt_iff_lt_add, lt_div_iff₀ S_posR]
  linarith

/-- `dvu a b = ⌈aS/b⌉ ≥ aS/b` for `0 < b`. -/
lemma dvu_ge {a b : ℤ} (hb : 0 < b) : (a : ℝ) * (S : ℝ) / (b : ℝ) ≤ ((dvu a b : ℤ) : ℝ) := by
  have h : Int.ediv (-(a * S)) b * b ≤ -(a * S) := Int.ediv_mul_le _ (ne_of_gt hb)
  have h2 : ((Int.ediv (-(a * S)) b : ℤ) : ℝ) * (b : ℝ) ≤ -((a : ℝ) * (S : ℝ)) := by
    exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h3 : ((dvu a b : ℤ) : ℝ) = -((Int.ediv (-(a * S)) b : ℤ) : ℝ) := by
    rw [dvu, fdiv]; push_cast; ring
  rw [h3, div_le_iff₀ hbR]
  linarith

/-- `dvu a b = ⌈aS/b⌉ < aS/b + 1` for `0 < b`. -/
lemma dvu_lt {a b : ℤ} (hb : 0 < b) : ((dvu a b : ℤ) : ℝ) < (a : ℝ) * (S : ℝ) / (b : ℝ) + 1 := by
  have h : -(a * S) < (Int.ediv (-(a * S)) b + 1) * b := Int.lt_ediv_add_one_mul_self _ hb
  have h2 : -((a : ℝ) * (S : ℝ)) < (((Int.ediv (-(a * S)) b : ℤ) : ℝ) + 1) * (b : ℝ) := by
    exact_mod_cast h
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h3 : ((dvu a b : ℤ) : ℝ) = -((Int.ediv (-(a * S)) b : ℤ) : ℝ) := by
    rw [dvu, fdiv]; push_cast; ring
  rw [h3, ← sub_lt_iff_lt_add, lt_div_iff₀ hbR]
  linarith

lemma iabs_nonneg (a : ℤ) : 0 ≤ iabs a := by
  rw [iabs]; split <;> omega

lemma iabs_abs (a : ℤ) : ((iabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  rw [iabs]
  by_cases h : a < 0
  · rw [if_pos h]
    push_cast
    rw [abs_of_neg]
    exact_mod_cast h
  · rw [if_neg h]
    push_cast
    rw [abs_of_nonneg]
    exact_mod_cast (not_lt.mp h)

/-! ## `cx`: scaled complex numbers -/

lemma cx_re (x y : ℤ) : (cx x y).re = (x : ℝ) / (S : ℝ) := by simp [cx]
lemma cx_im (x y : ℤ) : (cx x y).im = (y : ℝ) / (S : ℝ) := by simp [cx]

theorem norm_cx_sq (x y : ℤ) :
    ‖cx x y‖ ^ 2 = ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / (S : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [cx]
  norm_num
  field_simp

lemma norm_cx_le_abs (x y : ℤ) : ‖cx x y‖ ≤ (|(x : ℝ)| + |(y : ℝ)|) / (S : ℝ) := by
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) (le_of_eq ?_)
  rw [cx_re, cx_im, abs_div, abs_div, abs_of_pos S_posR]
  ring

lemma cx_sub (x y x' y' : ℤ) : cx x y - cx x' y' = cx (x - x') (y - y') := by
  simp only [cx]
  push_cast
  ring

lemma norm_cx_le_of_sq_le (x y m : ℤ) (hm : 0 ≤ m) (h : x * x + y * y ≤ m * m) :
    ‖cx x y‖ ≤ (m : ℝ) / (S : ℝ) := by
  have hcast : ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) ≤ (m : ℝ) ^ 2 := by
    have h' : ((x * x + y * y : ℤ) : ℝ) ≤ ((m * m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    simpa [sq] using h'
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2 : ‖cx x y‖ ^ 2 ≤ ((m : ℝ) / (S : ℝ)) ^ 2 := by
    rw [norm_cx_sq, div_pow]
    exact div_le_div_of_nonneg_right hcast (sq_nonneg _)
  calc ‖cx x y‖ = Real.sqrt (‖cx x y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((m : ℝ) / (S : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
    _ = (m : ℝ) / (S : ℝ) := Real.sqrt_sq (div_nonneg hmR S_posR.le)

/-! ## The stage constants -/

lemma K491_eq : ((K491 : ℤ) : ℝ) = (S : ℝ) * (491 / 500) := by norm_num [S, K491]
lemma K45_eq : ((K45 : ℤ) : ℝ) = (S : ℝ) * (4 / 5) := by norm_num [S, K45]

lemma s0A_eq : ((s0A : ℤ) : ℝ) = (S : ℝ) * (1 + (9 / 10 : ℝ)) ^ 2 := by norm_num [S, s0A]
lemma s0B2_eq : ((s0B2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 - 6 * (9 / 10 : ℝ) + (9 / 10 : ℝ) ^ 2)) := by
  norm_num [S, s0B2]
lemma s0E_eq : ((s0E : ℤ) : ℝ) = (S : ℝ) * (2 * ((9 / 10 : ℝ) - 1) ^ 2) := by norm_num [S, s0E]
lemma s0C1_eq : ((s0C1 : ℤ) : ℝ) = (S : ℝ) * (1 + (9 / 10 : ℝ)) := by norm_num [S, s0C1]
lemma s0G8_eq : ((s0G8 : ℤ) : ℝ) = (S : ℝ) * (8 * (9 / 10 : ℝ)) := by norm_num [S, s0G8]
lemma s0A2_eq : ((s0A2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 + (9 / 10 : ℝ)) ^ 2) := by norm_num [S, s0A2]

lemma s1A_eq : ((s1A : ℤ) : ℝ) = (S : ℝ) * (1 + (379 / 625 : ℝ)) ^ 2 := by norm_num [S, s1A]
lemma s1B2_eq :
    ((s1B2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 - 6 * (379 / 625 : ℝ) + (379 / 625 : ℝ) ^ 2)) := by
  norm_num [S, s1B2]
lemma s1E_eq : ((s1E : ℤ) : ℝ) = (S : ℝ) * (2 * ((379 / 625 : ℝ) - 1) ^ 2) := by norm_num [S, s1E]
lemma s1C1_eq : ((s1C1 : ℤ) : ℝ) = (S : ℝ) * (1 + (379 / 625 : ℝ)) := by norm_num [S, s1C1]
lemma s1G8_eq : ((s1G8 : ℤ) : ℝ) = (S : ℝ) * (8 * (379 / 625 : ℝ)) := by norm_num [S, s1G8]
lemma s1A2_eq : ((s1A2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 + (379 / 625 : ℝ)) ^ 2) := by norm_num [S, s1A2]

lemma s2A_eq : ((s2A : ℤ) : ℝ) = (S : ℝ) * (1 + (673 / 1250 : ℝ)) ^ 2 := by norm_num [S, s2A]
lemma s2B2_eq :
    ((s2B2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 - 6 * (673 / 1250 : ℝ) + (673 / 1250 : ℝ) ^ 2)) := by
  norm_num [S, s2B2]
lemma s2E_eq : ((s2E : ℤ) : ℝ) = (S : ℝ) * (2 * ((673 / 1250 : ℝ) - 1) ^ 2) := by norm_num [S, s2E]
lemma s2C1_eq : ((s2C1 : ℤ) : ℝ) = (S : ℝ) * (1 + (673 / 1250 : ℝ)) := by norm_num [S, s2C1]
lemma s2G8_eq : ((s2G8 : ℤ) : ℝ) = (S : ℝ) * (8 * (673 / 1250 : ℝ)) := by norm_num [S, s2G8]
lemma s2A2_eq : ((s2A2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 + (673 / 1250 : ℝ)) ^ 2) := by norm_num [S, s2A2]

lemma s3A_eq : ((s3A : ℤ) : ℝ) = (S : ℝ) * (1 + (7487 / 10000 : ℝ)) ^ 2 := by norm_num [S, s3A]
lemma s3B2_eq :
    ((s3B2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 - 6 * (7487 / 10000 : ℝ) + (7487 / 10000 : ℝ) ^ 2)) := by
  norm_num [S, s3B2]
lemma s3E_eq :
    ((s3E : ℤ) : ℝ) = (S : ℝ) * (2 * ((7487 / 10000 : ℝ) - 1) ^ 2) := by norm_num [S, s3E]
lemma s3C1_eq : ((s3C1 : ℤ) : ℝ) = (S : ℝ) * (1 + (7487 / 10000 : ℝ)) := by norm_num [S, s3C1]
lemma s3G8_eq : ((s3G8 : ℤ) : ℝ) = (S : ℝ) * (8 * (7487 / 10000 : ℝ)) := by norm_num [S, s3G8]
lemma s3A2_eq : ((s3A2 : ℤ) : ℝ) = (S : ℝ) * (2 * (1 + (7487 / 10000 : ℝ)) ^ 2) := by
  norm_num [S, s3A2]

/-! ## The ψ_A stage chain inside `leafOK` -/

/-- input disc of a leaf: centre `(491/500)·(chord midpoint)`, radius `leafRz L`. -/
def stage0 (L : Leaf) : St :=
  ⟨geomOK L, md K491 (leafCx L), md K491 (leafCy L), mu (leafRz L) K491 + 2⟩

def stage1 (L : Leaf) : St :=
  slitStage s0A s0B2 s0E s0C1 s0G8 s0A2 rot0r rot0i (stage0 L) L.w0
def stage2 (L : Leaf) : St :=
  slitStage s1A s1B2 s1E s1C1 s1G8 s1A2 rot1r rot1i (stage1 L) L.w1
def stage3 (L : Leaf) : St :=
  slitStage s2A s2B2 s2E s2C1 s2G8 s2A2 rot2r rot2i (stage2 L) L.w2
def stage4 (L : Leaf) : St :=
  slitStage s3A s3B2 s3E s3C1 s3G8 s3A2 rot3r rot3i (stage3 L) L.w3
def stage5 (L : Leaf) : St := luneStage (stage4 L) L.wl

/-- the disc for `ψ_A(leaf disc)`: `q = -(4/5)·(stage5 value)`. -/
def qrZ (L : Leaf) : ℤ := -(md K45 (stage5 L).cr)
def qiZ (L : Leaf) : ℤ := -(md K45 (stage5 L).ci)
def rqZ (L : Leaf) : ℤ := mu (stage5 L).rho K45 + 2

/-- the truncation index of the θ-series. -/
def mZ (L : Leaf) : ℤ := L.mU + rqZ L + 1

/-! ## θ-series data -/

def Acell (qr qi rq m : ℤ) : TS :=
  aLoop qr qi rq m KTH 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩

def Bcell (qr qi rq m : ℤ) : BS :=
  bLoop (cmr qr qi qr qi) (cmi qr qi qr qi) rq m KTH 1 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩

def tailAZ (qr qi rq m : ℤ) : ℤ :=
  dvu (mu (Acell qr qi rq m).mT (mu (Acell qr qi rq m).mn m + 1)) (S - m) + 1

def tailBZ (qr qi rq m : ℤ) : ℤ :=
  2 * dvu (mu (Bcell qr qi rq m).ms (Bcell qr qi rq m).mo) (S - m) + 1

def AupZ (qr qi rq m aU : ℤ) : ℤ := aU + (Acell qr qi rq m).dA + tailAZ qr qi rq m
def BloZ (qr qi rq m bL : ℤ) : ℤ := bL - (Bcell qr qi rq m).dB - tailBZ qr qi rq m

def ratioZ (Aup Blo : ℤ) : ℤ := dvu (mu Aup Aup) (md Blo Blo)

def r8Z (Aup Blo : ℤ) : ℤ :=
  let r := ratioZ Aup Blo
  let r2 := mu r r
  let r4 := mu r2 r2
  mu r4 r4

def P2Z (Aup Blo m : ℤ) : ℤ := mu (mu (65536 * S) (mu m m)) (r8Z Aup Blo)

/-! ## Destructuring `leafOK` -/

/-- `leafOK L = true` exposes the last stage status, the `q`-disc data, the θ-numerics and the
final `P2 ≤ expLo (2G)` test. -/
theorem leafOK_spec (L : Leaf) (h : leafOK L = true) :
    (stage5 L).ok = true ∧ 0 ≤ L.mU ∧
      qrZ L * qrZ L + qiZ L * qiZ L ≤ L.mU * L.mU ∧
      mZ L ≤ fdiv (79 * S) 100 ∧
      0 ≤ L.aU ∧
      (Acell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Ar * (Acell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Ar
          + (Acell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Ai * (Acell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Ai
        ≤ L.aU * L.aU ∧
      0 ≤ L.bL ∧
      L.bL * L.bL ≤ (Bcell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Br * (Bcell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Br
          + (Bcell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Bi * (Bcell (qrZ L) (qiZ L) (rqZ L) (mZ L)).Bi ∧
      0 < BloZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.bL ∧
      0 < md (BloZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.bL) (BloZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.bL) ∧
      P2Z (AupZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.aU) (BloZ (qrZ L) (qiZ L) (rqZ L) (mZ L) L.bL)
          (mZ L) ≤ expLo (2 * L.G) := by
  simp only [leafOK, stage5, stage4, stage3, stage2, stage1, stage0, qrZ, qiZ, rqZ, mZ, Acell,
    Bcell, tailAZ, tailBZ, AupZ, BloZ, ratioZ, r8Z, P2Z, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  tauto

/-- the `ok` flag of the last slit stage. -/
lemma stage4_ok (L : Leaf) (h : (stage5 L).ok = true) : (stage4 L).ok = true := by
  unfold stage5 luneStage at h
  simp only [Bool.and_eq_true] at h
  tauto

lemma stage3_ok (L : Leaf) (h : (stage4 L).ok = true) : (stage3 L).ok = true := by
  unfold stage4 slitStage at h
  simp only [Bool.and_eq_true] at h
  tauto

lemma stage2_ok (L : Leaf) (h : (stage3 L).ok = true) : (stage2 L).ok = true := by
  unfold stage3 slitStage at h
  simp only [Bool.and_eq_true] at h
  tauto

lemma stage1_ok (L : Leaf) (h : (stage2 L).ok = true) : (stage1 L).ok = true := by
  unfold stage2 slitStage at h
  simp only [Bool.and_eq_true] at h
  tauto

lemma stage0_ok (L : Leaf) (h : (stage1 L).ok = true) : (stage0 L).ok = true := by
  unfold stage1 slitStage at h
  simp only [Bool.and_eq_true] at h
  tauto

end Work.Cert

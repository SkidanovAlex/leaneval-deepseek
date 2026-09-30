import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.ulcm_le_four_pow
import Submission.Work.BW.tijdeman_int
import Submission.Work.BW.norm_Theta_le
import Submission.Work.BW.norm_Delta_le
import Submission.Work.BW.logHeight_intTuple_le
import Submission.Work.BW.logHeight_monomial_le
import Submission.Work.BW.logHeight_one_intermediate
import Submission.Work.BW.gamInt_abs_le
import Submission.Work.BW.sysRow_arith
import Submission.Work.BW.ph_ge_nineteen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex
open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- `1/d ≤ modifiedHeight`. -/
lemma one_div_finrank_le_modifiedHeight (φ : K →+* ℂ) (α : K) :
    (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ α := by
  unfold BakerWustholz.modifiedHeight
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- `1/d ≤ hmod`. -/
lemma one_div_finrank_le_hmod (β : K) (ℓ : ℂ) :
    (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ hmod β ℓ := by
  unfold hmod
  exact le_trans (le_max_right _ _) (le_max_right _ _)

lemma thetaRat_one_zero (x : ℤ) (k : ℕ) : thetaRat x k 1 0 = deltaRat x k := by
  simp [thetaRat, deltaRat, Polynomial.hasseDeriv_zero]

lemma exp_mul_log_two (v : ℕ) : Real.exp ((v : ℝ) * Real.log 2) = (2 : ℝ) ^ v := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- `1 ≤ a * b` for reals. -/
lemma one_le_mul_real {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have h := mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
  simpa using h

/-- `pD` is nonnegative. -/
lemma pD_nonneg {r d : ℕ} (σ : Fin r → ℝ) (hσ : ∀ j, 0 < σ j) : 0 ≤ pD r d σ := by
  rw [pD]
  have hlog : 0 ≤ Real.log ((2:ℝ) * (r:ℝ) * (d:ℝ)) := by
    rw [show (2:ℝ) * (r:ℝ) * (d:ℝ) = (((2 * r * d : ℕ)) : ℝ) by push_cast; ring]
    exact Real.log_natCast_nonneg _
  have hprod : 0 ≤ ∏ j, σ j := Finset.prod_nonneg fun j _ => le_of_lt (hσ j)
  have h2 : (0:ℝ) ≤ (r:ℝ)^r := by positivity
  have h3 : (0:ℝ) ≤ ((32:ℝ) * (d:ℝ))^(r+1) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) h3) hlog) hprod

/-- The `α'`-monomial part of a row of the linear system has height
`≤ [ℚ(α'):ℚ]·|s|·D/d`. -/
lemma mon_height_le {r : ℕ} (α' : Fin r → K) (σ : Fin r → ℝ) (h : ℕ)
    (hσ : ∀ j, Height.logHeight₁ (α' j) ≤ (Module.finrank ℚ K : ℝ) * σ j)
    (hσpos : ∀ j, 0 < σ j) (hr : 2 ≤ r) (s : ℤ) :
    Height.logHeight (fun lm : AuxIdx r h (pD0 r (Module.finrank ℚ K) σ)
        (pDj r (Module.finrank ℚ K) σ) =>
      ∏ j, alphaF α' j ^ (s * ((lm.2.2 j : ℕ) : ℤ)))
      ≤ (Module.finrank ℚ (auxField α'))
        * (|(s : ℝ)| * pD r (Module.finrank ℚ K) σ / (Module.finrank ℚ K : ℝ)) := by
  have hFpos : (0 : ℝ) < (Module.finrank (auxField α') K : ℝ) := by
    have hh : 0 < Module.finrank (auxField α') K := Module.finrank_pos
    exact_mod_cast hh
  have hdFpos : (0 : ℝ) < (Module.finrank ℚ (auxField α') : ℝ) := by
    have hh : 0 < Module.finrank ℚ (auxField α') := Module.finrank_pos
    exact_mod_cast hh
  have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    have hh : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast hh
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hFne : (Module.finrank (auxField α') K : ℝ) ≠ 0 := ne_of_gt hFpos
  have hdFne : (Module.finrank ℚ (auxField α') : ℝ) ≠ 0 := ne_of_gt hdFpos
  have hpD := pD_nonneg (r := r) (d := Module.finrank ℚ K) σ hσpos
  have hrdσ : ∀ j, (0:ℝ) ≤ (r : ℝ) * (Module.finrank ℚ K : ℝ) * σ j :=
    fun j => mul_nonneg (mul_nonneg (le_of_lt hrpos) (le_of_lt hdpos)) (le_of_lt (hσpos j))
  have hdσ : ∀ j, (0:ℝ) ≤ (Module.finrank ℚ K : ℝ) * σ j :=
    fun j => mul_nonneg (le_of_lt hdpos) (le_of_lt (hσpos j))
  have hdσne : ∀ j, (Module.finrank ℚ K : ℝ) * σ j ≠ 0 :=
    fun j => ne_of_gt (mul_pos hdpos (hσpos j))
  have hsF : (0:ℝ) ≤ |(s : ℝ)| / (Module.finrank (auxField α') K : ℝ) :=
    div_nonneg (abs_nonneg _) (le_of_lt hFpos)
  have htower : (Module.finrank ℚ K : ℝ)
      = (Module.finrank (auxField α') K : ℝ) * (Module.finrank ℚ (auxField α') : ℝ) := by
    have hh := (Module.finrank_mul_finrank ℚ (auxField α') K).symm
    have h2 : Module.finrank ℚ K
        = Module.finrank (auxField α') K * Module.finrank ℚ (auxField α') :=
      hh.trans (mul_comm _ _)
    exact_mod_cast h2
  have hheight : ∀ j, Height.logHeight₁ (alphaF α' j)
      ≤ (Module.finrank ℚ K : ℝ) * σ j / (Module.finrank (auxField α') K : ℝ) := by
    intro j
    have hone := logHeight_one_intermediate (auxField α') (alphaF α' j)
    rw [alphaF_coe] at hone
    have h1 : Height.logHeight₁ (α' j) ≤ (Module.finrank ℚ K : ℝ) * σ j := hσ j
    rw [hone] at h1
    rw [le_div_iff₀ hFpos]
    linarith [h1]
  have hDj : ∀ j, (pDj r (Module.finrank ℚ K) σ j : ℝ)
      ≤ pD r (Module.finrank ℚ K) σ / ((r : ℝ) * (Module.finrank ℚ K : ℝ) * σ j) := by
    intro j
    rw [pDj]
    exact Nat.floor_le (div_nonneg hpD (hrdσ j))
  calc Height.logHeight (fun lm : AuxIdx r h (pD0 r (Module.finrank ℚ K) σ)
          (pDj r (Module.finrank ℚ K) σ) =>
        ∏ j, alphaF α' j ^ (s * ((lm.2.2 j : ℕ) : ℤ)))
      = Height.logHeight ((fun lmj : (j : Fin r) → Fin (pDj r (Module.finrank ℚ K) σ j + 1) =>
            ∏ j, alphaF α' j ^ (s * ((lmj j : ℕ) : ℤ)))
          ∘ fun lm : AuxIdx r h (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) => lm.2.2) := rfl
    _ ≤ Height.logHeight (fun lmj : (j : Fin r) → Fin (pDj r (Module.finrank ℚ K) σ j + 1) =>
            ∏ j, alphaF α' j ^ (s * ((lmj j : ℕ) : ℤ))) :=
          Height.logHeight_comp_le (fun lm : AuxIdx r h (pD0 r (Module.finrank ℚ K) σ)
            (pDj r (Module.finrank ℚ K) σ) => lm.2.2) _
    _ ≤ ∑ j, (|(s : ℝ)| * (pDj r (Module.finrank ℚ K) σ j : ℝ)) *
            Height.logHeight₁ (alphaF α' j) :=
          logHeight_monomial_le (alphaF α') s (pDj r (Module.finrank ℚ K) σ)
    _ ≤ ∑ j, (|(s : ℝ)| * (pDj r (Module.finrank ℚ K) σ j : ℝ)) *
            ((Module.finrank ℚ K : ℝ) * σ j / (Module.finrank (auxField α') K : ℝ)) := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hheight j) (by positivity)
    _ = |(s : ℝ)| / (Module.finrank (auxField α') K : ℝ) *
          ∑ j, ((pDj r (Module.finrank ℚ K) σ j : ℝ) * ((Module.finrank ℚ K : ℝ) * σ j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _
          ring
    _ ≤ |(s : ℝ)| / (Module.finrank (auxField α') K : ℝ)
          * ∑ _j : Fin r, pD r (Module.finrank ℚ K) σ / (r : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hsF
          apply Finset.sum_le_sum; intro j _
          calc (pDj r (Module.finrank ℚ K) σ j : ℝ) * ((Module.finrank ℚ K : ℝ) * σ j)
              ≤ (pD r (Module.finrank ℚ K) σ / ((r : ℝ) * (Module.finrank ℚ K : ℝ) * σ j))
                  * ((Module.finrank ℚ K : ℝ) * σ j) := by
                apply mul_le_mul_of_nonneg_right (hDj j); exact hdσ j
            _ = pD r (Module.finrank ℚ K) σ / (r : ℝ) := by
                rw [div_mul_eq_mul_div, show (r : ℝ) * (Module.finrank ℚ K : ℝ) * σ j
                    = (r : ℝ) * ((Module.finrank ℚ K : ℝ) * σ j) by ring]
                exact mul_div_mul_right _ _ (hdσne j)
    _ = |(s : ℝ)| / (Module.finrank (auxField α') K : ℝ) * pD r (Module.finrank ℚ K) σ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_comm (r : ℝ) (pD r (Module.finrank ℚ K) σ / (r : ℝ)),
            div_mul_cancel₀ (pD r (Module.finrank ℚ K) σ) hrne]
    _ = (Module.finrank ℚ (auxField α'))
          * (|(s : ℝ)| * pD r (Module.finrank ℚ K) σ / (Module.finrank ℚ K : ℝ)) := by
          rw [htower]
          field_simp

set_option maxHeartbeats 1000000 in
/-- The rational (integer-valued) part of a row has height `≤ [ℚ(α'):ℚ]·1.7·h·(11.75 r D)`. -/
lemma rat_height_le {n r : ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ)
    (hst : Standing φ α b k c) (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ)
    (α' : Fin r → K) (σ : Fin r → ℝ) (hBH : BH φ α b v c r L α' σ)
    (ι : Fin (r - 1) → Fin n) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (hsum : t0 + ∑ m, t m ≤ pT r (Module.finrank ℚ K) σ) (s : ℤ)
    (hs : |(s : ℝ)| ≤ (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ)) :
    Height.logHeight (fun lm : AuxIdx r (ph (hL b (Module.finrank ℚ K)) v)
        (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) =>
      (coefRat b k L ι (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
        (pDj r (Module.finrank ℚ K) σ) t0 t s lm : auxField α'))
      ≤ (Module.finrank ℚ (auxField α'))
        * (1.7 * (ph (hL b (Module.finrank ℚ K)) v : ℝ)
            * (11.75 * (r : ℝ) * pD r (Module.finrank ℚ K) σ)) := by
  classical
  have hd1 : (1 : ℕ) ≤ Module.finrank ℚ K := Module.finrank_pos
  have hdR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hd1
  set hN : ℕ := ph (hL b (Module.finrank ℚ K)) v with hNdef
  set G0 : ℝ := 2 * Real.exp (hL b (Module.finrank ℚ K)) * (2 : ℝ) ^ v
      * pD r (Module.finrank ℚ K) σ with hG0def
  set M : ℝ := (∏ m : Fin (r - 1), (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m))
      * ((ulcm hN : ℕ) : ℝ) ^ t0
      * (Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
          ^ (hN * (pD0 r (Module.finrank ℚ K) σ + 1)) with hMdef
  set cD : AuxIdx r hN (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) →
      Fin (r - 1) → ℤ :=
    fun lm m => Classical.choose (tijdeman_int (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) 1 0)
    with hcDdef
  set cT : AuxIdx r hN (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) → ℤ :=
    fun lm => Classical.choose (tijdeman_int (s + (lm.1 : ℤ)) hN ((lm.2.1 : ℕ) + 1) t0)
    with hcTdef
  set n : AuxIdx r hN (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) → ℤ :=
    fun lm => (∏ m : Fin (r - 1), cD lm m) * cT lm with hn
  have hσpos : ∀ j, 0 < σ j := fun j => hBH.2.2.2.2.1 j
  have hσ1 : ∀ j, (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * σ j := by
    intro j
    have h1 : (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ hmod (α' j) (lamP φ α v L j) :=
      one_div_finrank_le_hmod _ _
    have h2 : hmod (α' j) (lamP φ α v L j) ≤ σ j := hBH.2.2.2.2.2.1 j
    have h3 : (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ σ j := le_trans h1 h2
    rw [div_le_iff₀ hdR] at h3
    linarith
  have hN19 : 19 ≤ hN := by rw [hNdef]; exact ph_ge_nineteen φ α b k c v hst
  have hpDnn : 0 ≤ pD r (Module.finrank ℚ K) σ := pD_nonneg (r := r) (d := Module.finrank ℚ K) σ hσpos
  have hulcm : 0 < ((ulcm hN : ℕ) : ℝ) := by exact_mod_cast ulcm_pos hN
  have hG0nn : 0 ≤ G0 := by
    rw [hG0def]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hpDnn
  have hG0le : G0 ≤ 2 * Real.exp ((hN : ℝ) + 1) * pD r (Module.finrank ℚ K) σ := by
    rw [hG0def]
    have h2v : (2 : ℝ) ^ v = Real.exp ((v : ℝ) * Real.log 2) := (exp_mul_log_two v).symm
    have hexp : Real.exp (hL b (Module.finrank ℚ K)) * (2 : ℝ) ^ v
        = Real.exp (hL b (Module.finrank ℚ K) + (v : ℝ) * Real.log 2) := by
      rw [h2v, ← Real.exp_add]
    have hle : hL b (Module.finrank ℚ K) + (v : ℝ) * Real.log 2 ≤ (hN : ℝ) + 1 := by
      have hlt := Nat.lt_floor_add_one (hL b (Module.finrank ℚ K) + (v : ℝ) * Real.log 2)
      rw [hNdef]
      simp only [ph]
      linarith [hlt]
    have hone : Real.exp (hL b (Module.finrank ℚ K) + (v : ℝ) * Real.log 2)
        ≤ Real.exp ((hN : ℝ) + 1) := Real.exp_le_exp.mpr hle
    calc 2 * Real.exp (hL b (Module.finrank ℚ K)) * (2 : ℝ) ^ v * pD r (Module.finrank ℚ K) σ
        = 2 * (Real.exp (hL b (Module.finrank ℚ K)) * (2 : ℝ) ^ v)
            * pD r (Module.finrank ℚ K) σ := by ring
      _ = 2 * Real.exp (hL b (Module.finrank ℚ K) + (v : ℝ) * Real.log 2)
            * pD r (Module.finrank ℚ K) σ := by rw [hexp]
      _ ≤ 2 * Real.exp ((hN : ℝ) + 1) * pD r (Module.finrank ℚ K) σ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hone (by norm_num)) hpDnn
  have hcD : ∀ lm m,
      deltaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) = (cD lm m : ℚ) := by
    intro lm m
    have h1 : (ulcm (t m) : ℚ) ^ 0
        * thetaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) 1 0
        = deltaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) := by
      rw [pow_zero, one_mul, thetaRat_one_zero]
    simp only [hcDdef]
    exact h1.symm.trans (Classical.choose_spec (tijdeman_int
      (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) 1 0))
  have hcT : ∀ lm, (ulcm hN : ℚ) ^ t0 * thetaRat (s + (lm.1 : ℤ)) hN ((lm.2.1 : ℕ) + 1) t0
      = (cT lm : ℚ) := by
    intro lm
    simp only [hcTdef]
    exact Classical.choose_spec (tijdeman_int (s + (lm.1 : ℤ)) hN ((lm.2.1 : ℕ) + 1) t0)
  have hncoef : ∀ lm, coefRat b k L ι hN (pD0 r (Module.finrank ℚ K) σ)
      (pDj r (Module.finrank ℚ K) σ) t0 t s lm = (n lm : ℚ) := by
    intro lm
    calc coefRat b k L ι hN (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ)
            t0 t s lm
        = (∏ m : Fin (r - 1), deltaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
            * ((ulcm hN : ℚ) ^ t0 * thetaRat (s + (lm.1 : ℤ)) hN ((lm.2.1 : ℕ) + 1) t0) := by
          rw [coefRat]; ring
      _ = (∏ m : Fin (r - 1), (cD lm m : ℚ)) * (cT lm : ℚ) := by
          rw [Finset.prod_congr rfl (fun m _ => hcD lm m), hcT lm]
      _ = (n lm : ℚ) := by
          rw [hn]; simp only []; push_cast; ring
  have hbound : ∀ lm, |((n lm : ℤ) : ℝ)| ≤ M := by
    intro lm
    have hdlt : ∀ m : Fin (r - 1),
        |((cD lm m : ℤ) : ℝ)| ≤ (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m) := by
      intro m
      have hspecR : (deltaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) : ℝ)
          = ((cD lm m : ℤ) : ℝ) := by
        have hc := congrArg (fun q : ℚ => (q : ℝ)) (hcD lm m)
        push_cast at hc
        exact hc
      have hγ : |(((gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) : ℤ) : ℝ)| ≤ G0 := by
        rw [hG0def]
        exact gamInt_abs_le φ α b k v c L α' σ hBH ι m lm.2.2
      calc |((cD lm m : ℤ) : ℝ)|
          = |(deltaRat (gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) : ℝ)| := by rw [hspecR]
        _ = ‖Delta (((gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) : ℤ) : ℂ) (t m)‖ := by
            rw [Delta_eq_deltaRat, Complex.norm_ratCast]
        _ ≤ (Real.exp 1 * (1 + ‖(((gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) : ℤ) : ℂ)‖
              / (t m : ℝ))) ^ (t m) := norm_Delta_le _ _
        _ = (Real.exp 1 * (1 + |(((gamInt b k L (ι m) (fun i => (lm.2.2 i : ℕ))) : ℤ) : ℝ)|
              / (t m : ℝ))) ^ (t m) := by rw [Complex.norm_intCast]
        _ ≤ (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m) := by
            apply pow_le_pow_left₀
            · exact mul_nonneg (le_of_lt (Real.exp_pos 1))
                (add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
            exact mul_le_mul_of_nonneg_left
              (add_le_add (le_refl 1) (div_le_div_of_nonneg_right hγ (Nat.cast_nonneg _)))
              (le_of_lt (Real.exp_pos 1))
    have hc1 : |((cT lm : ℤ) : ℝ)|
        ≤ ((ulcm hN : ℕ) : ℝ) ^ t0
          * (Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
              ^ (hN * (pD0 r (Module.finrank ℚ K) σ + 1)) := by
      have hspecR : ((ulcm hN : ℕ) : ℝ) ^ t0
            * (thetaRat (s + (lm.1 : ℤ)) hN ((lm.2.1 : ℕ) + 1) t0 : ℝ)
          = ((cT lm : ℤ) : ℝ) := by
        have hc := congrArg (fun q : ℚ => (q : ℝ)) (hcT lm)
        push_cast at hc
        exact hc
      have hNpos : (0 : ℝ) < (hN : ℝ) := by
        have : (0:ℕ) < hN := by omega
        exact_mod_cast this
      have hz1 : |(((s + (lm.1 : ℤ)) : ℤ) : ℝ)| ≤ (hN : ℝ) * (16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) + 1) := by
        have hlm : ((lm.1 : ℕ) : ℝ) ≤ (hN : ℝ) := by
          have : (lm.1 : ℕ) ≤ hN := le_of_lt lm.1.2
          exact_mod_cast this
        have hcast1 : (((lm.1 : ℤ)) : ℝ) = ((lm.1 : ℕ) : ℝ) := by push_cast; ring
        have hcast2 : (((s + (lm.1 : ℤ)) : ℤ) : ℝ) = (s : ℝ) + ((lm.1 : ℕ) : ℝ) := by
          rw [show (((s + (lm.1 : ℤ)) : ℤ) : ℝ) = (s : ℝ) + (((lm.1 : ℤ)) : ℝ) by push_cast; ring,
            hcast1]
        rw [hcast2]
        calc |(s : ℝ) + ((lm.1 : ℕ) : ℝ)|
            ≤ |(s : ℝ)| + |((lm.1 : ℕ) : ℝ)| := abs_add_le _ _
          _ = |(s : ℝ)| + ((lm.1 : ℕ) : ℝ) := by
              rw [abs_of_nonneg (show (0:ℝ) ≤ ((lm.1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
          _ ≤ 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) * (hN : ℝ) + (hN : ℝ) := by
              have hthis : |(s : ℝ)| + ((lm.1 : ℕ) : ℝ)
                  ≤ ((pS r (Module.finrank ℚ K) hN : ℕ) : ℝ) + (hN : ℝ) := add_le_add hs hlm
              have hthis2 : ((pS r (Module.finrank ℚ K) hN : ℕ) : ℝ) + (hN : ℝ)
                  = 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) * (hN : ℝ) + (hN : ℝ) := by
                simp only [pS]; push_cast; ring
              linarith [hthis, hthis2.le, hthis2.ge]
          _ = (hN : ℝ) * (16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) + 1) := by ring
      calc |((cT lm : ℤ) : ℝ)|
          = ((ulcm hN : ℕ) : ℝ) ^ t0
              * |(thetaRat (s + (lm.1 : ℤ)) hN ((lm.2.1 : ℕ) + 1) t0 : ℝ)| := by
            rw [← hspecR, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hulcm) _)]
        _ = ((ulcm hN : ℕ) : ℝ) ^ t0
              * ‖Theta (((s + (lm.1 : ℤ)) : ℤ) : ℂ) hN ((lm.2.1 : ℕ) + 1) t0‖ := by
            rw [Theta_eq_thetaRat, Complex.norm_ratCast]
        _ ≤ ((ulcm hN : ℕ) : ℝ) ^ t0
              * (Real.exp 3 * (1 + ‖(((s + (lm.1 : ℤ)) : ℤ) : ℂ)‖ / (hN : ℝ)))
                  ^ (hN * ((lm.2.1 : ℕ) + 1)) := by
            exact mul_le_mul_of_nonneg_left (norm_Theta_le _ _ _ _) (pow_nonneg (le_of_lt hulcm) _)
        _ = ((ulcm hN : ℕ) : ℝ) ^ t0
              * (Real.exp 3 * (1 + |(((s + (lm.1 : ℤ)) : ℤ) : ℝ)| / (hN : ℝ)))
                  ^ (hN * ((lm.2.1 : ℕ) + 1)) := by rw [Complex.norm_intCast]
        _ ≤ ((ulcm hN : ℕ) : ℝ) ^ t0
              * (Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
                  ^ (hN * ((lm.2.1 : ℕ) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hulcm) _)
            apply pow_le_pow_left₀
            · exact mul_nonneg (le_of_lt (Real.exp_pos 3))
                (add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (le_of_lt hNpos)))
            have hc : 1 + |(((s + (lm.1 : ℤ)) : ℤ) : ℝ)| / (hN : ℝ)
                ≤ 2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) := by
              have hb : 1 + |(((s + (lm.1 : ℤ)) : ℤ) : ℝ)| / (hN : ℝ)
                  ≤ 1 + ((hN : ℝ) * (16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) + 1)) / (hN : ℝ) :=
                add_le_add (le_refl 1) (div_le_div_of_nonneg_right hz1 (le_of_lt hNpos))
              have hb2 : 1 + ((hN : ℝ) * (16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) + 1)) / (hN : ℝ)
                  = 2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) := by
                field_simp
                ring
              linarith [hb, hb2.le, hb2.ge]
            exact mul_le_mul_of_nonneg_left hc (le_of_lt (Real.exp_pos 3))
        _ ≤ ((ulcm hN : ℕ) : ℝ) ^ t0
              * (Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
                  ^ (hN * (pD0 r (Module.finrank ℚ K) σ + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hulcm) _)
            apply pow_le_pow_right₀
            · exact one_le_mul_real (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))
                (by
                  have h2nn : (0:ℝ) ≤ 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) := by positivity
                  linarith)
            have hlm : (lm.2.1 : ℕ) + 1 ≤ pD0 r (Module.finrank ℚ K) σ + 1 := by
              have : (lm.2.1 : ℕ) ≤ pD0 r (Module.finrank ℚ K) σ := by
                have := lm.2.1.2
                omega
              omega
            exact Nat.mul_le_mul_left _ hlm
    have hP : |((((∏ m : Fin (r - 1), cD lm m) : ℤ) : ℝ))|
        ≤ ∏ m : Fin (r - 1), (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m) := by
      have hcast : (((∏ m : Fin (r - 1), cD lm m) : ℤ) : ℝ)
          = ∏ m : Fin (r - 1), ((cD lm m : ℤ) : ℝ) :=
        map_prod (Int.castRingHom ℝ) (fun m : Fin (r - 1) => cD lm m) Finset.univ
      rw [hcast, Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun m _ => abs_nonneg _) (fun m _ => hdlt m)
    have hn_val : n lm = (∏ m : Fin (r - 1), cD lm m) * cT lm := by simp only [hn]
    rw [hn_val, Int.cast_mul, abs_mul]
    calc |((((∏ m : Fin (r - 1), cD lm m) : ℤ) : ℝ))| * |(((cT lm : ℤ)) : ℝ)|
        ≤ (∏ m : Fin (r - 1), (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m))
            * ((((ulcm hN : ℕ) : ℝ) ^ t0)
              * (Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
                  ^ (hN * (pD0 r (Module.finrank ℚ K) σ + 1))) :=
          mul_le_mul hP hc1 (abs_nonneg _) (Finset.prod_nonneg fun m _ => pow_nonneg (by positivity) _)
      _ = M := by rw [hMdef]; ring
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    have hA1 : ∀ m : Fin (r - 1), 1 ≤ (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m) := fun m =>
      one_le_pow₀ (one_le_mul_real
        (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))
        (le_add_of_nonneg_right (div_nonneg hG0nn (Nat.cast_nonneg _))))
    have hAprod : 1 ≤ ∏ m : Fin (r - 1), (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m) :=
      Finset.one_le_prod₀ (fun m _ => hA1 m)
    have hB1 : 1 ≤ ((ulcm hN : ℕ) : ℝ) ^ t0 :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ulcm_ne_zero hN))
    have hC1 : 1 ≤ (Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
        ^ (hN * (pD0 r (Module.finrank ℚ K) σ + 1)) :=
      one_le_pow₀ (one_le_mul_real
        (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))
        (by
          have h2nn : (0:ℝ) ≤ 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ) := by positivity
          linarith))
    exact one_le_mul_real (one_le_mul_real hAprod hB1) hC1
  have hlogM : Real.log M ≤ 1.7 * (hN : ℝ)
      * (11.75 * (r : ℝ) * pD r (Module.finrank ℚ K) σ) := by
    have hexp : Real.log (∏ m : Fin (r - 1), (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m))
        = ∑ m : Fin (r - 1), (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ))) := by
      have hA : (∏ m : Fin (r - 1), (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m))
          = Real.exp (∑ m : Fin (r - 1),
              (t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ)))) := by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl; intro m _
        have hlt : (Real.exp 1 * (1 + G0 / (t m : ℝ))) ^ (t m)
            = Real.exp ((t m : ℝ) * (1 + Real.log (1 + G0 / (t m : ℝ)))) := by
          have hbase : (1 + G0 / (t m : ℝ)) = Real.exp (Real.log (1 + G0 / (t m : ℝ))) := by
            rw [Real.exp_log]
            exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (div_nonneg hG0nn (Nat.cast_nonneg _)))
          nth_rewrite 1 [hbase]
          rw [← Real.exp_add, ← Real.exp_nat_mul]
        rw [hlt]
      rw [hA, Real.log_exp]
    rw [hMdef, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), hexp, Real.log_pow]
    rw [show Real.log ((Real.exp 3 * (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ)))
        ^ (hN * (pD0 r (Module.finrank ℚ K) σ + 1)))
        = (hN : ℝ) * ((pD0 r (Module.finrank ℚ K) σ : ℝ) + 1)
          * (3 + Real.log (2 + 16 * (r : ℝ) * (Module.finrank ℚ K : ℝ))) by
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp]
      push_cast; ring]
    exact sysRow_arith (r := r) (d := Module.finrank ℚ K) (h := hN) hr hd1 hN19 σ hσ1 G0 hG0nn hG0le t0 t hsum
  have hmain : Height.logHeight (fun lm : AuxIdx r hN (pD0 r (Module.finrank ℚ K) σ)
        (pDj r (Module.finrank ℚ K) σ) =>
      (coefRat b k L ι hN (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ)
        t0 t s lm : auxField α'))
      ≤ (Module.finrank ℚ (auxField α') : ℝ) * Real.log M := by
    have hto : (fun lm => ((n lm : ℤ) : auxField α'))
        = (fun lm => (coefRat b k L ι hN (pD0 r (Module.finrank ℚ K) σ)
            (pDj r (Module.finrank ℚ K) σ) t0 t s lm : auxField α')) := by
      funext lm
      rw [← Rat.cast_intCast (n lm)]
      exact (congrArg (fun q : ℚ => (q : auxField α')) (hncoef lm)).symm
    have hh := logHeight_intTuple_le (K := auxField α') n hM1 hbound
    rwa [hto] at hh
  calc Height.logHeight (fun lm : AuxIdx r hN (pD0 r (Module.finrank ℚ K) σ)
          (pDj r (Module.finrank ℚ K) σ) =>
        (coefRat b k L ι hN (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ)
          t0 t s lm : auxField α'))
      ≤ (Module.finrank ℚ (auxField α') : ℝ) * Real.log M := hmain
    _ ≤ (Module.finrank ℚ (auxField α') : ℝ)
          * (1.7 * (hN : ℝ) * (11.75 * (r : ℝ) * pD r (Module.finrank ℚ K) σ)) :=
        mul_le_mul_of_nonneg_left hlogM (by positivity)
    _ = (Module.finrank ℚ (auxField α'))
          * (1.7 * (ph (hL b (Module.finrank ℚ K)) v : ℝ)
              * (11.75 * (r : ℝ) * pD r (Module.finrank ℚ K) σ)) := by rw [hNdef]

/-- Height of a row of the BW §13 linear system, relative to `F = ℚ(α')`.

PROOF SKETCH (the constant 1.7 is attainable and comfortably sufficient, because the number of
equations is `M_e = (2S+1)·binom(T+r,r)` while the number of unknowns is
`M_u = h(D_0+1)∏(D_j+1) ≥ 3.4·M_e`, so `ρ := M_e/(M_u-M_e) ≤ 0.415` and the final check reads
`ρ(0.7344·1.7 + 0.5008) ≤ 0.73 ≤ 0.85`).

Write `F = auxField α'`, `d = [K:ℚ]`, `d_F = [F:ℚ]`, `h = ph (hL b d) v`, `D = pD r d σ`,
`D₀ = pD0 r d σ`, `D_j = pDj r d σ`, `T_0 = 11.75 r D`, and for the equation `e = (s,(t₀,t))` and
unknown `lm : AuxIdx` put `γ = gamInt b k L (ι m) (·) = ∑ᵢ (b_k L_{i,j} - b_j L_{i,k})·lm.2.2 i ∈ ℤ`.

1. `sysRow e lm = (coefRat … lm : F) * ∏_j alphaF α' j ^ (s * lm.2.2 j)`, a pointwise product of
   two tuples, so `Height.logHeight_mul_le` gives `h_F(row) ≤ h_F(rational tuple) + h_F(monomial tuple)`.
2. Rational tuple: each `coefRat` is an integer (use `tijdeman_int` for `u(h)^{t₀}Θ`, and
   `tijdeman_int` with `m = 0, l = 1` for `Δ ∈ ℤ`).  Apply `logHeight_intTuple_le` with the bound
   `M ≤ exp(Σ_m t_m·(1+log(1+G/T_0)) + t₀·log(u(h)) + h(λ₀+1)(3+log(2+16rd)))`,
   where `G := 2·e^{h+1}·D`:  `norm_Delta_le` with `‖γ‖ ≤ G` for each `Δ(γ;t_m)`, then
   `norm_Theta_le` + `Theta_eq_thetaRat` for `Θ`, and `t₀·log(u(h)) ≤ t₀·h·log 4` from
   `ulcm_le_four_pow`.  KEY: bound `t_m(1+log(1+G/t_m)) ≤ t_m(1+log(1+G/T_0))` (the factor
   `t ↦ 1+log(1+G/t)` is antitone) — bounding `G/t_m` by `G` instead would introduce `log D` and
   break the constant.
3. Monomial tuple: `logHeight_monomial_le` (transfer along the projection `lm ↦ lm.2.2` with
   `Height.logHeight_comp_le`) plus `logHeight₁(a) ≤ d_F·σ_j` and `pDj … j ≤ D/(r·d·σ_j)`
   (both from `BH`, whose 6th conjunct bounds `hmod (α'_j) (lamP …)` by `σ_j`, and the fact that
   `logHeight₁_F = (1/[K:F])·logHeight₁_K` from `logHeight_one_intermediate`).
4. The `γ` bound: `BH`'s 7th conjunct `∑ᵢ |L j i|·h'(α_i) ≤ 2^v σ_j` gives `|L i j| ≤ 2^v σ_i/h'(α_j)`,
   and `h'(α_j) ≥ 1/d`, `σ_i ≥ 1/d`, `lm.2.2 i ≤ D/(r d σ_i)`, `|b_i| ≤ e^{hL b d}`; the `σ_i`
   cancels and `d·h'(α_j) ≥ 1`, so `|γ| ≤ 2 e^{hL}2^v D ≤ 2 e^{h+1} D` (no factor `d`).
5. Arithmetic: `t₀ ≤ T₀`, `Σ_m t_m ≤ T₀`, `h ≥ 19`, `‖e.1‖ = |s|`, and
   `(1+log(1+G/T_0)) ≤ h+2`, `(D₀+1)(3+log(2+16rd)) ≤ 0.2137·T₀`. -/
theorem sysRow_height_bound {K : Type*} [Field K] [NumberField K] {n r : ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ)
    (hst : Standing φ α b k c) (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ)
    (α' : Fin r → K) (σ : Fin r → ℝ) (hBH : BH φ α b v c r L α' σ)
    (ι : Fin (r - 1) → Fin n)
    (e : AuxEqnIdx r (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v))
                 (pT r (Module.finrank ℚ K) σ)) :
    Height.logHeight (fun lm : AuxIdx r (ph (hL b (Module.finrank ℚ K)) v)
        (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) =>
      sysRow b k L ι α' (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
        (pDj r (Module.finrank ℚ K) σ) e lm)
      ≤ (Module.finrank ℚ (auxField α'))
        * (1.7 * (ph (hL b (Module.finrank ℚ K)) v : ℝ)
            * (11.75 * r * pD r (Module.finrank ℚ K) σ)
           + |(e.1 : ℤ)| * pD r (Module.finrank ℚ K) σ / (Module.finrank ℚ K : ℝ)) := by
  have hfun : (fun lm : AuxIdx r (ph (hL b (Module.finrank ℚ K)) v)
        (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ) =>
        sysRow b k L ι α' (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
          (pDj r (Module.finrank ℚ K) σ) e lm)
      = (fun lm => (coefRat b k L ι (ph (hL b (Module.finrank ℚ K)) v)
            (pD0 r (Module.finrank ℚ K) σ) (pDj r (Module.finrank ℚ K) σ)
            e.2.1.1 e.2.1.2 (e.1 : ℤ) lm : auxField α'))
        * (fun lm => ∏ j, alphaF α' j ^ ((e.1 : ℤ) * ((lm.2.2 j : ℕ) : ℤ))) := by
    funext lm; rfl
  have hs : |((e.1 : ℤ) : ℝ)| ≤ (pS r (Module.finrank ℚ K)
      (ph (hL b (Module.finrank ℚ K)) v) : ℝ) := by
    have hmem := e.1.2
    rw [Finset.mem_Icc] at hmem
    rw [abs_le]
    exact ⟨by exact_mod_cast hmem.1, by exact_mod_cast hmem.2⟩
  have hsum := e.2.2
  have hrat := rat_height_le φ α b k c hst hr v L α' σ hBH ι e.2.1.1 e.2.1.2 hsum (e.1 : ℤ) hs
  have hmon := mon_height_le α' σ (ph (hL b (Module.finrank ℚ K)) v)
    (fun j => by
      have h2 : hmod (α' j) (lamP φ α v L j) ≤ σ j := hBH.2.2.2.2.2.1 j
      have h1 : Height.logHeight₁ (α' j) / (Module.finrank ℚ K : ℝ)
          ≤ hmod (α' j) (lamP φ α v L j) := by
        unfold hmod
        exact le_max_left _ _
      have h0 : 0 < (Module.finrank ℚ K : ℝ) := by
        have : (0:ℕ) < Module.finrank ℚ K := Module.finrank_pos
        exact_mod_cast this
      rw [div_le_iff₀ h0] at h1
      nlinarith [h1, h2, h0.le])
    (fun j => hBH.2.2.2.2.1 j) hr (e.1 : ℤ)
  rw [hfun]
  refine le_trans (Height.logHeight_mul_le _ _) ?_
  have hcast : ((|(e.1 : ℤ)| : ℤ) : ℝ) = |((e.1 : ℤ) : ℝ)| := Int.cast_abs
  rw [← hcast] at hmon
  have hsum2 : (Module.finrank ℚ (auxField α'))
        * (1.7 * (ph (hL b (Module.finrank ℚ K)) v : ℝ)
            * (11.75 * (r : ℝ) * pD r (Module.finrank ℚ K) σ))
      + (Module.finrank ℚ (auxField α'))
        * (((|(e.1 : ℤ)| : ℤ) : ℝ) * pD r (Module.finrank ℚ K) σ / (Module.finrank ℚ K : ℝ))
      = (Module.finrank ℚ (auxField α'))
        * (1.7 * (ph (hL b (Module.finrank ℚ K)) v : ℝ)
            * (11.75 * r * pD r (Module.finrank ℚ K) σ)
          + |(e.1 : ℤ)| * pD r (Module.finrank ℚ K) σ / (Module.finrank ℚ K : ℝ)) := by
    ring
  linarith [hrat, hmon, hsum2]

end Work.BW

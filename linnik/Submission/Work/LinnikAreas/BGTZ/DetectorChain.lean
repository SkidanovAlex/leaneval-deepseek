import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorLowerAux

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- **The elementary core of the detector chain.**  If
`(1 - 1/N)·(1 + N^{s-δ}) ≤ c·N^s` (the consequence of the two detector upper bounds), if
`c ≤ 1 + δ(1.001/s + 103.001)` (the constant bound coming from `δ ≤ 1/(10 log q)`, `σ ≥ 1/2+1/100`),
if the zero-free region gives `1/s ≤ C`, and if `N ≥ 2`, `Nδ ≥ 1`, `log N ≤ Lmax`, then
`s·log N ≥ log(1/δ) - log(1.01 C + Lmax + 106) - 1`. -/
private lemma chain_core {N : ℕ} {s δ c C Lmax : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hs : 0 < s)
    (hNδ : 1 ≤ (N : ℝ) * δ) (hLmax : Real.log N ≤ Lmax)
    (hC : 1 / s ≤ C)
    (hlc : (1 - 1 / (N : ℝ)) * (1 + (N : ℝ) ^ (s - δ)) ≤ c * (N : ℝ) ^ s)
    (hc : c ≤ 1 + δ * (1.001 / s + 103.001)) :
    s * Real.log N ≥ Real.log (1 / δ) - Real.log (1.01 * C + Lmax + 106) - 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set L : ℝ := Real.log N with hLdef
  have hLpos : 0 < L := hlogN
  set u : ℝ := (N : ℝ) ^ s with hudef
  set w : ℝ := (N : ℝ) ^ δ with hwdef
  have hupos : 0 < u := by rw [hudef]; exact Real.rpow_pos_of_pos hNpos _
  have hwpos : 0 < w := by rw [hwdef]; exact Real.rpow_pos_of_pos hNpos _
  have hw1 : 1 ≤ w := by rw [hwdef]; exact Real.one_le_rpow hN1.le hδ.le
  have hsub : (N : ℝ) ^ (s - δ) = u / w := by
    rw [hudef, hwdef, Real.rpow_sub hNpos]
  rw [hsub] at hlc
  set d : ℝ := 1 - 1 / (N : ℝ) with hddef
  have hdpos : 0 < d := by
    rw [hddef, sub_pos, div_lt_one hNpos]; exact hN1
  have hdge : 1 / 2 ≤ d := by
    rw [hddef]
    have hle : 1 / (N : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
    linarith
  have hinvN : 1 / (N : ℝ) ≤ δ := by
    rw [div_le_iff₀ hNpos]; linarith [hNδ]
  have h1 : (1 + u / w) * w = w + u := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hwpos)]
  have hlcw : d * (w + u) ≤ c * u * w := by
    have h := mul_le_mul_of_nonneg_right hlc hwpos.le
    have hid : d * (1 + u / w) * w = d * (w + u) := by rw [mul_assoc, h1]
    nlinarith [h, hid]
  have hdiv : d * w ≤ u * (c * w - d) := by nlinarith [hlcw]
  have hcw : 0 < c * w - d := by
    have hdw : 0 < d * w := mul_pos hdpos hwpos
    by_contra hle
    rw [not_lt] at hle
    have h0 : u * (c * w - d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hupos.le (by linarith)
    nlinarith
  have hu_ge : d * w / (c * w - d) ≤ u := by
    rw [div_le_iff₀ hcw]
    exact hdiv
  have hwexp : w = Real.exp (δ * L) := by
    rw [hwdef, Real.rpow_def_of_pos hNpos, hLdef]
    congr 1; ring
  have hwsub : w - 1 ≤ δ * L * w := by
    have hxe : 1 - δ * L ≤ Real.exp (-(δ * L)) := Real.one_sub_le_exp_neg _
    have hwe : Real.exp (-(δ * L)) * w = 1 := by
      rw [hwexp, ← Real.exp_add]
      have : -(δ * L) + δ * L = 0 := by ring
      rw [this, Real.exp_zero]
    have h2 : w - 1 = w * (1 - Real.exp (-(δ * L))) := by
      have hwr : w * Real.exp (-(δ * L)) = 1 := by rw [mul_comm]; exact hwe
      nlinarith [hwr]
    rw [h2]
    have := mul_le_mul_of_nonneg_left (by linarith [hxe] : 1 - Real.exp (-(δ*L)) ≤ δ*L) hwpos.le
    linarith
  have hden : c * w - d ≤ δ * w * (1.001 / s + L + 104.001) := by
    have hkey : c * w - d = (c - 1) * w + (w - 1) + 1 / (N : ℝ) := by rw [hddef]; ring
    rw [hkey]
    have hA : (c - 1) * w ≤ δ * (1.001 / s + 103.001) * w := by
      apply mul_le_mul_of_nonneg_right _ hwpos.le
      linarith [hc]
    have hB : 1 / (N : ℝ) ≤ δ * w := by
      have : δ ≤ δ * w := by nlinarith [hδ.le, hw1]
      linarith [hinvN]
    nlinarith [hA, hwsub, hB, hwpos]
  have hKpos : 0 < 1.001 / s + L + 104.001 := by positivity
  have hgoal : d / (δ * (1.001 / s + L + 104.001)) ≤ u := by
    have hEq : d / (δ * (1.001 / s + L + 104.001))
        = d * w / (δ * w * (1.001 / s + L + 104.001)) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [hEq]
    exact le_trans (div_le_div_of_nonneg_left (mul_nonneg hdpos.le hwpos.le) hcw hden) hu_ge
  have hlogd : -Real.log 2 ≤ Real.log d := by
    have h1 : Real.log (1/2) ≤ Real.log d := Real.log_le_log (by norm_num) hdge
    have h2 : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith
  have hlogu : Real.log u = s * Real.log N := by
    rw [hudef, Real.log_rpow hNpos]
  have hloggoal : Real.log (d / (δ * (1.001/s + L + 104.001))) ≤ Real.log u :=
    Real.log_le_log (by positivity) hgoal
  have hlogval : Real.log (d / (δ * (1.001/s+L+104.001)))
      = Real.log d - Real.log δ - Real.log (1.001/s+L+104.001) := by
    rw [Real.log_div (ne_of_gt hdpos) (by positivity),
        Real.log_mul (ne_of_gt hδ) (by positivity)]
    ring
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity : (0:ℝ) < 1/s) hC
  have hK'pos : 0 < 1.01 * C + Lmax + 106 := by
    have : 0 < 1.01 * C := mul_pos (by norm_num) hCpos
    linarith [hLmax, hLpos]
  have hLK : Real.log (1.001/s + L + 104.001) ≤ Real.log (1.01 * C + Lmax + 106) := by
    apply Real.log_le_log hKpos
    have hC' : 1.001 / s ≤ 1.01 * C := by
      have ha : 1.001 / s ≤ 1.01 / s := div_le_div_of_nonneg_right (by norm_num) hs.le
      have hb : 1.01 / s ≤ 1.01 * C := by
        have hC0 : 1.01 * (1/s) ≤ 1.01 * C := mul_le_mul_of_nonneg_left hC (by norm_num)
        have heq : 1.01 * (1/s) = 1.01 / s := by ring
        linarith
      linarith
    linarith [hC', hLmax]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have h1d : Real.log (1/δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [hlogval] at hloggoal
  rw [hlogu] at hloggoal
  linarith [hloggoal, hlogd, hLK, hlog2, h1d]

/-- **The constant bound of the detector chain.**  From `δ = 1 - β₁ ≤ 1/(10 log q) ≤ 1/10000`,
`σ ≥ 1/2 + 1/100` and `σ < 1`, the quantity `δ·A_ρ + δ·A_β` (where `A_ρ`, `A_β` are the two
Proposition-5.1 brackets) is at most `1 + δ(1.001/(1-σ) + 103.001)`. -/
private lemma const_bound {β₁ σ : ℝ} (hσlo : 1 / 2 + 1 / 100 ≤ σ) (hσlt : σ < 1)
    (hδpos : 0 < 1 - β₁) (hδle : 1 - β₁ ≤ 1 / 10000) :
    (1 - β₁) * ((2 - β₁) / (1 - σ) + 1 / (σ - 1 / 2))
      + (1 - β₁) * ((2 - β₁) / (1 - β₁) + 1 / (β₁ - 1 / 2))
      ≤ 1 + (1 - β₁) * (1.001 / (1 - σ) + 103.001) := by
  have hs : 0 < 1 - σ := by linarith
  have hβ1m : 0 < β₁ - 1 / 2 := by linarith
  have hσm : 0 < σ - 1 / 2 := by linarith
  have h2b : 2 - β₁ ≤ 1.001 := by linarith
  have hT1 : (1 - β₁) * ((2 - β₁) / (1 - σ)) ≤ (1 - β₁) * (1.001 / (1 - σ)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2b hs.le) hδpos.le
  have hσinv : 1 / (σ - 1 / 2) ≤ 100 := by
    rw [div_le_iff₀ hσm]; nlinarith
  have hT2 : (1 - β₁) * (1 / (σ - 1 / 2)) ≤ (1 - β₁) * 100 :=
    mul_le_mul_of_nonneg_left hσinv hδpos.le
  have hT3 : (1 - β₁) * ((2 - β₁) / (1 - β₁)) = 1 + (1 - β₁) := by
    field_simp; ring
  have hβinv : 1 / (β₁ - 1 / 2) ≤ 2.001 := by
    rw [div_le_iff₀ hβ1m]; nlinarith
  have hT4 : (1 - β₁) * (1 / (β₁ - 1 / 2)) ≤ (1 - β₁) * 2.001 :=
    mul_le_mul_of_nonneg_left hβinv hδpos.le
  have e1 : (1 - β₁) * ((2 - β₁) / (1 - σ) + 1 / (σ - 1 / 2))
      = (1 - β₁) * ((2 - β₁) / (1 - σ)) + (1 - β₁) * (1 / (σ - 1 / 2)) := by ring
  have e2 : (1 - β₁) * ((2 - β₁) / (1 - β₁) + 1 / (β₁ - 1 / 2))
      = (1 - β₁) * ((2 - β₁) / (1 - β₁)) + (1 - β₁) * (1 / (β₁ - 1 / 2)) := by ring
  have hfin : (1 - β₁) * (1.001 / (1 - σ) + 100) + (1 + (1 - β₁) + (1 - β₁) * 2.001)
      = 1 + (1 - β₁) * (1.001 / (1 - σ) + 103.001) := by ring
  rw [e1, e2]
  linarith [hT1, hT2, hT3, hT4, hfin]

/-- **The BGTZ detector chain, isolated.**  With the two Proposition-5.1 bounds for the detector at
`ρ` (resp. at the exceptional zero `β₁`, with the principal character), the zero-free region
`1 - ρ.re ≥ cZ / log (q max 4 |Im ρ|)`, the Landau--Siegel normalisation `1 - 1/(10 log q) < β₁`
(so `2-β₁ ≤ 1.001` and `1/(β₁-1/2) ≤ 2.001`) and `1/2 + 1/100 ≤ ρ.re` (so `1/(ρ.re-1/2) ≤ 100`),
the detector argument gives

`(1-ρ.re)·log N ≥ log(1/(1-β₁)) - log(1.01·log(q max 4|Im ρ|)/cZ + N' + 106) - 1`,

`N'` any upper bound for `log N`.  This is the (only) place where the zero-free region and the size
of the detection length enter; the theorem `RepulsionFromPiecesC2` performs all remaining
comparisons. -/
theorem DetectorChain {q : ℕ} [NeZero q] {χ₁ χ : DirichletCharacter ℂ q} {θw : ℕ → ℝ} {N : ℕ}
    {β₁ : ℝ} {ρ : ℂ} {cZ Lmax : ℝ} (hcZ : 0 < cZ)
    (hsq : χ₁ ^ 2 = 1) (hθ1 : θw 1 = 1) (hN2 : 2 ≤ N)
    (hβ₁lt : β₁ < 1) (h1β₁ : 0 < 1 - β₁)
    (hβ₁big : 1 - 1 / (10 * Real.log q) < β₁) (hLbig : 1000 ≤ Real.log q)
    (hrele : ρ.re ≤ β₁) (hrege : 1 / 2 + 1 / 100 ≤ ρ.re)
    (hX1 : 1 ≤ Real.log ((q : ℝ) * max 4 |ρ.im|))
    (hZFR : cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re)
    (hNbig : 1 ≤ (N : ℝ) * (1 - β₁)) (hLmax : Real.log N ≤ Lmax)
    (hupρ : ‖Work.LinnikAreas.BGTZ.detector χ₁ χ N θw ρ‖
      ≤ ((2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)))
    (hupβ : (Work.LinnikAreas.BGTZ.detector χ₁ 1 N θw (β₁ : ℂ)).re
      ≤ ((2 - β₁) / (1 - β₁) + 1 / (β₁ - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - β₁))) :
    (1 - ρ.re) * Real.log N
      ≥ Real.log (1 / (1 - β₁))
        - Real.log (1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) + Lmax + 106) - 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hs : 0 < 1 - ρ.re := by linarith
  have hlogq : 0 < Real.log q := by linarith
  have hδsmall : 1 - β₁ < 1 / (10 * Real.log q) := by linarith [hβ₁big]
  have hδle : 1 - β₁ ≤ 1 / 10000 := by
    have hden : (10000 : ℝ) ≤ 10 * Real.log q := by linarith
    have h : 1 / (10 * Real.log q) ≤ 1 / 10000 :=
      one_div_le_one_div_of_le (by norm_num) hden
    linarith [hδsmall.le, h]
  set X : ℝ := Real.log ((q : ℝ) * max 4 |ρ.im|) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; linarith [hX1]
  set C : ℝ := X / cZ with hCdef
  have hC : 1 / (1 - ρ.re) ≤ C := by
    rw [hCdef, div_le_div_iff₀ hs hcZ]
    have h := hZFR
    rw [div_le_iff₀ hXpos] at h
    linarith [h]
  have hlow := detector_lower_bound χ₁ χ N θw ρ β₁ hsq hθ1 hN2 hrele
  set d : ℝ := 1 - 1 / (N : ℝ) with hddef
  set Aρ : ℝ := (2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2) with hAρdef
  set Aβ : ℝ := (2 - β₁) / (1 - β₁) + 1 / (β₁ - 1 / 2) with hAβdef
  set c : ℝ := (1 - β₁) * Aρ + (1 - β₁) * Aβ with hcdef
  set D : ℝ := (detector χ₁ 1 N θw (β₁ : ℂ)).re with hDdef
  have hlow2 : d - (N : ℝ) ^ (β₁ - ρ.re) * (D - d) ≤ Aρ * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) :=
    le_trans hlow hupρ
  have hD : D - d ≤ Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)) - d := by linarith [hupβ]
  have hNexpnn : 0 ≤ (N : ℝ) ^ (β₁ - ρ.re) := Real.rpow_nonneg hNpos.le _
  have hstep : d + (N : ℝ) ^ (β₁ - ρ.re) * d
      ≤ Aρ * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re))
        + (N : ℝ) ^ (β₁ - ρ.re) * (Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - β₁))) := by
    have hm := mul_le_mul_of_nonneg_left hD hNexpnn
    have h3 : (N : ℝ) ^ (β₁ - ρ.re) * (Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)) - d)
        = (N : ℝ) ^ (β₁ - ρ.re) * (Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)))
          - (N : ℝ) ^ (β₁ - ρ.re) * d := by ring
    rw [h3] at hm
    linarith [hlow2, hm]
  have hNM : (N : ℝ) ^ (β₁ - ρ.re) * (N : ℝ) ^ (1 - β₁) = (N : ℝ) ^ (1 - ρ.re) := by
    rw [← Real.rpow_add hNpos]
    congr 1; ring
  have hstar : d * (1 + (N : ℝ) ^ (β₁ - ρ.re)) ≤ c * (N : ℝ) ^ (1 - ρ.re) := by
    have hR : Aρ * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re))
        + (N : ℝ) ^ (β₁ - ρ.re) * (Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)))
        = c * (N : ℝ) ^ (1 - ρ.re) := by
      rw [hcdef]
      have h1 : (N : ℝ) ^ (β₁ - ρ.re) * (Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)))
          = Aβ * (1 - β₁) * ((N : ℝ) ^ (1 - ρ.re)) := by
        rw [← hNM]; ring
      rw [h1]; ring
    nlinarith [hstep, hR]
  have hc : c ≤ 1 + (1 - β₁) * (1.001 / (1 - ρ.re) + 103.001) := by
    rw [hcdef, hAρdef, hAβdef]
    exact const_bound hrege (by linarith) h1β₁ hδle
  have hlc' : (1 - 1 / (N : ℝ)) * (1 + (N : ℝ) ^ ((1 - ρ.re) - (1 - β₁)))
      ≤ c * (N : ℝ) ^ (1 - ρ.re) := by
    have he : (1 - ρ.re) - (1 - β₁) = β₁ - ρ.re := by ring
    rw [hddef] at hstar
    rw [he]
    exact hstar
  have key := chain_core (s := 1 - ρ.re) (δ := 1 - β₁) (c := c) (C := C) (Lmax := Lmax)
    hN2 h1β₁ hs hNbig hLmax hC hlc' hc
  have hCval : C = Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ := by rw [hCdef, hXdef]
  rw [hCval] at key
  exact key

end
end Work.LinnikAreas.BGTZ

import Mathlib
import Submission.Work.FIArea7.UniCut6
import Submission.Work.FIArea4.VcutMod_le_pair_crude

namespace Work.FIArea7

open Finset
open scoped BigOperators

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable section

lemma gnorm_mul' (z1 z2 : GaussianInt) :
    Work.FIPlan.gnorm (z1 * z2) = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma sqrt_gnorm_mul_le {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ (1 + Pa.θ) * Pa.N := by
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h1.2.2.1
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := h2.2.2.1
  have hC0 : (0:ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    have : (0:ℝ) ≤ 1 + Pa.θ := by linarith [Pa.hθ0]
    exact mul_nonneg this (by linarith [Pa.hN1])
  rw [gnorm_mul', Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  have h1' : Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
    Real.sqrt_le_sqrt hg1
  have h2' : Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
    Real.sqrt_le_sqrt hg2
  have hsq : Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N)
      = (1 + Pa.θ) * Pa.N := by
    rw [← pow_two]; exact Real.sq_sqrt hC0
  calc Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
          * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
      ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N) :=
        mul_le_mul h1' h2' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (1 + Pa.θ) * Pa.N := hsq

lemma logFac6_abs_le {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hD : 4 ≤ Work.FIPlan.absDelta z1 z2) :
    |Work.FITop4.logFac6 z1 z2| ≤ Real.log (8 * (1 + Pa.θ) * Pa.N) := by
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hθ0 : (0:ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
  have hDpos : (0:ℝ) < (Work.FIPlan.absDelta z1 z2 : ℝ) := by
    have : (4:ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hD
    linarith
  have hsqrt_le := sqrt_gnorm_mul_le h1 h2
  have hΔS : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) :=
    Work.FIArea4.crude_absDelta_le_sqrt_gnorm z1 z2
  have hD4 : (4:ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hD
  have harg_ge : 1 ≤ 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      / (Work.FIPlan.absDelta z1 z2 : ℝ) := by
    rw [le_div_iff₀ hDpos]
    nlinarith [hΔS, hDpos]
  have harg_le : 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      / (Work.FIPlan.absDelta z1 z2 : ℝ) ≤ 8 * (1 + Pa.θ) * Pa.N := by
    rw [div_le_iff₀ hDpos]
    nlinarith [hsqrt_le, hD4, hDpos, hN0, hθ0]
  have hargpos : 0 < 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
      / (Work.FIPlan.absDelta z1 z2 : ℝ) := by linarith
  have hlf_nonneg : 0 ≤ Work.FITop4.logFac6 z1 z2 := by
    rw [Work.FITop4.logFac6]; exact Real.log_nonneg harg_ge
  have hlf_le : Work.FITop4.logFac6 z1 z2 ≤ Real.log (8 * (1 + Pa.θ) * Pa.N) := by
    rw [Work.FITop4.logFac6]; exact Real.log_le_log hargpos harg_le
  have h8N : 1 ≤ 8 * (1 + Pa.θ) * Pa.N := by nlinarith [hN0, hθ0, Pa.hN1]
  have h8log : 0 ≤ Real.log (8 * (1 + Pa.θ) * Pa.N) := Real.log_nonneg h8N
  rw [abs_le]
  exact ⟨by linarith, hlf_le⟩

lemma ratioSym_abs_le (z1 z2 : GaussianInt) (d : ℕ) :
    |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
  unfold Work.FITop4.ratioSym Work.FIArea7.ratioSym
  rcases jacobiSym.trichotomy _ d with h | h | h <;> rw [h] <;> norm_num

/-- If `X < d` and `d ≤ n/4 + 1` with `1 ≤ X` then `4 ≤ n`. -/
lemma four_le_of_div_le {X d n : ℕ} (hX : 1 ≤ X) (hlt : X < d) (hdle : d ≤ n / 4 + 1) :
    4 ≤ n := by
  have hd2 : 2 ≤ d := Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hX hlt)
  have hle : 2 ≤ n / 4 + 1 := le_trans hd2 hdle
  have h2 : 1 ≤ n / 4 := Nat.succ_le_succ_iff.mp hle
  have h4_1 : 4 ≤ 4 * (n / 4) := by
    calc (4:ℕ) = 4 * 1 := by ring
      _ ≤ 4 * (n / 4) := Nat.mul_le_mul_left 4 h2
  have h4_2 : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  omega

/-- For `d` in `Sset z₁ z₂` with `X < d`, the determinant is at least `4`. -/
lemma four_le_absDelta_of_mem {X d : ℕ} (hX : 1 ≤ X) {z1 z2 : GaussianInt}
    (hd : d ∈ (Work.FITop4.Sset z1 z2).filter
      (fun d => X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X)) :
    4 ≤ Work.FIPlan.absDelta z1 z2 := by
  have hlt : X < d := (Finset.mem_filter.mp hd).2.1
  have hdle : d ≤ Work.FIPlan.absDelta z1 z2 / 4 + 1 := by
    rw [Finset.mem_filter, Work.FITop4.Sset, Finset.mem_filter, Finset.mem_Icc] at hd
    exact hd.1.1.2
  exact four_le_of_div_le hX hlt hdle

/-- The number of `d ∈ Sset z₁ z₂` carrying the `W ∪ B` cut is at most `X`. -/
lemma card_cut_le (X : ℕ) (hX : 1 ≤ X) (z1 z2 : GaussianInt) :
    (((Work.FITop4.Sset z1 z2).filter
        (fun d => X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X)).card) ≤ X := by
  set T := (Work.FITop4.Sset z1 z2).filter
    (fun d => X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X) with hT
  have hmem : ∀ d ∈ T, X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      ∧ d ≤ Work.FIPlan.absDelta z1 z2 / 4 + 1
      ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X ∧ 1 ≤ d := by
    intro d hd
    rw [hT, Finset.mem_filter, Work.FITop4.Sset, Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨hd.2.1, hd.1.2, hd.1.1.2, hd.2.2, hd.1.1.1⟩
  by_cases hne : T.Nonempty
  · obtain ⟨d0, hd0⟩ := hne
    have hD4 : 4 ≤ Work.FIPlan.absDelta z1 z2 :=
      four_le_of_div_le hX (hmem d0 hd0).1 (hmem d0 hd0).2.2.1
    have hDpos : 0 < Work.FIPlan.absDelta z1 z2 := by omega
    have himg : T.image (fun d => Work.FIPlan.absDelta z1 z2 / (4 * d)) ⊆ Finset.Icc 1 X := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨d, hd, rfl⟩ := he
      obtain ⟨hdX, hdvd, hdle, hdM, hd1⟩ := hmem d hd
      rw [Finset.mem_Icc]
      have h4dpos : 0 < 4 * d := by omega
      have h4dle : 4 * d ≤ Work.FIPlan.absDelta z1 z2 :=
        Nat.le_of_dvd hDpos hdvd
      refine ⟨?_, ?_⟩
      · rw [Nat.one_le_div_iff h4dpos]; exact h4dle
      · rw [Nat.div_le_iff_le_mul_add_pred h4dpos]
        calc Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X := hdM
          _ ≤ 4 * d * X + (4 * d - 1) := Nat.le_add_right _ _
    have hinj : Set.InjOn (fun d => Work.FIPlan.absDelta z1 z2 / (4 * d)) ↑T := by
      intro a ha b hb hab
      obtain ⟨_, havd, _, _, ha1⟩ := hmem a ha
      obtain ⟨_, hbvd, _, _, hb1⟩ := hmem b hb
      have h4apos : 0 < 4 * a := by omega
      have h4bpos : 0 < 4 * b := by omega
      have hea : 1 ≤ Work.FIPlan.absDelta z1 z2 / (4 * a) := by
        have h4a : 4 * a ≤ Work.FIPlan.absDelta z1 z2 := Nat.le_of_dvd hDpos havd
        rw [Nat.one_le_div_iff h4apos]; exact h4a
      have h1 : 4 * a * (Work.FIPlan.absDelta z1 z2 / (4 * a)) = Work.FIPlan.absDelta z1 z2 :=
        Nat.mul_div_cancel' havd
      have h2 : 4 * b * (Work.FIPlan.absDelta z1 z2 / (4 * b)) = Work.FIPlan.absDelta z1 z2 :=
        Nat.mul_div_cancel' hbvd
      have heq : Work.FIPlan.absDelta z1 z2 / (4 * b) = Work.FIPlan.absDelta z1 z2 / (4 * a) :=
        hab.symm
      rw [heq] at h2
      have h4 : 4 * a * (Work.FIPlan.absDelta z1 z2 / (4 * a))
          = 4 * b * (Work.FIPlan.absDelta z1 z2 / (4 * a)) := by rw [h1, h2]
      have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < Work.FIPlan.absDelta z1 z2 / (4 * a)) h4
      omega
    have hcard1 : (T.image (fun d => Work.FIPlan.absDelta z1 z2 / (4 * d))).card = T.card :=
      Finset.card_image_of_injOn hinj
    have hcard2 : (T.image (fun d => Work.FIPlan.absDelta z1 z2 / (4 * d))).card ≤ X := by
      have h := Finset.card_le_card himg
      rw [Nat.card_Icc] at h
      omega
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-- **The inner `d`-sum of `Wcut + Bcut` is at most `X log(8(1+θ)N)`.** -/
lemma innerSum_abs_le {Pa : Work.FITop.Params} {φ : ℝ} {X : ℕ} (hX : 1 ≤ X)
    {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    |∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ))
          * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
      ≤ (X : ℝ) * Real.log (8 * (1 + Pa.θ) * Pa.N) := by
  set L := Real.log (8 * (1 + Pa.θ) * Pa.N) with hL
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hθ0 : (0:ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
  have h8N : 1 ≤ 8 * (1 + Pa.θ) * Pa.N := by nlinarith [hN0, hθ0, Pa.hN1]
  have hLnn : 0 ≤ L := by rw [hL]; exact Real.log_nonneg h8N
  set T := (Work.FITop4.Sset z1 z2).filter
    (fun d => X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X) with hT
  have hTcard : T.card ≤ X := card_cut_le X hX z1 z2
  have hsum : (∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ))
          * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2)
      = ∑ d ∈ T, ((Nat.totient d : ℝ) / (d : ℝ))
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hc : X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X <;> simp [hc]
  rw [hsum]
  have hbound : ∀ d ∈ T, |((Nat.totient d : ℝ) / (d : ℝ))
        * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2| ≤ L := by
    intro d hd
    have hd' : d ∈ (Work.FITop4.Sset z1 z2).filter
        (fun d => X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X) := by rw [hT] at hd; exact hd
    have hdS : d ∈ Work.FITop4.Sset z1 z2 := (Finset.mem_filter.mp hd').1
    have hdlt : X < d := (Finset.mem_filter.mp hd').2.1
    rw [Work.FITop4.Sset, Finset.mem_filter, Finset.mem_Icc] at hdS
    obtain ⟨⟨hd1, hdle⟩, _⟩ := hdS
    have hD4 : 4 ≤ Work.FIPlan.absDelta z1 z2 := four_le_of_div_le hX hdlt hdle
    have ht_le : (Nat.totient d : ℝ) / (d : ℝ) ≤ 1 := by
      have h1' : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
      have h2' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd1
      rw [div_le_one h2']; exact h1'
    have htnn : (0:ℝ) ≤ (Nat.totient d : ℝ) / (d : ℝ) := by positivity
    have hlog : |Work.FITop4.logFac6 z1 z2| ≤ L := by
      rw [hL]; exact logFac6_abs_le h1 h2 hD4
    have hrs : |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 := ratioSym_abs_le z1 z2 d
    rw [abs_mul, abs_mul, abs_of_nonneg htnn]
    calc (Nat.totient d : ℝ) / (d : ℝ) * |(Work.FITop4.ratioSym z1 z2 d : ℝ)|
            * |Work.FITop4.logFac6 z1 z2|
        ≤ 1 * 1 * L :=
          mul_le_mul (mul_le_mul ht_le hrs (abs_nonneg _) (by norm_num)) hlog
            (abs_nonneg _) (by norm_num)
      _ = L := by ring
  calc |∑ d ∈ T, ((Nat.totient d : ℝ) / (d : ℝ))
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
      ≤ ∑ d ∈ T, |((Nat.totient d : ℝ) / (d : ℝ))
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ T, L := Finset.sum_le_sum hbound
    _ = (T.card : ℝ) * L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (X : ℝ) * L := by
        have : (T.card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hTcard
        exact mul_le_mul_of_nonneg_right this hLnn
    _ = (X : ℝ) * Real.log (8 * (1 + Pa.θ) * Pa.N) := by rw [hL]
/-- `Tcut6_eq_sum_ofReal` in the `Sset` spelling. -/
theorem Tcut6_eq_sum_ofReal' (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz cut β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                    ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
           else 0) := by
  simpa only [Work.FITop4.Sset] using Tcut6_eq_sum_ofReal Rz cut β

/-- **Norm bound for `Tcut` at the `W ∪ B` cut.** -/
theorem Tcut6_norm_le {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : ∀ z, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z) (hX : 1 ≤ X) :
    ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
        (fun z1 z2 d =>
          if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0) β‖
      ≤ 2 * (X:ℝ) * Real.log (8 * (1 + Pa.θ) * Pa.N)
          * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖)^2 := by
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hθ0 : (0:ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
  have h8N : 1 ≤ 8 * (1 + Pa.θ) * Pa.N := by nlinarith [hN0, hθ0, Pa.hN1]
  have hLnn : 0 ≤ Real.log (8 * (1 + Pa.θ) * Pa.N) := Real.log_nonneg h8N
  rw [Tcut6_eq_sum_ofReal']
  rw [norm_mul, Complex.norm_ofNat]
  set L := Real.log (8 * (1 + Pa.θ) * Pa.N) with hL
  have hpair : ∀ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ∀ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ‖(if Work.FIPlan.GaussCoprime z1 z2 then
          β z1 * star (β z2)
            * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                  ((Nat.totient d : ℝ) / (d : ℝ))
                    * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
                    * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
         else 0)‖ ≤ ‖β z1‖ * ‖β z2‖ * ((X:ℝ) * L) := by
    intro z1 _ z2 _
    by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hcop]
      by_cases hb1 : β z1 = 0
      · rw [hb1]; simp
      by_cases hb2 : β z2 = 0
      · rw [hb2]; simp
      have hbox1 := hβ z1 hb1
      have hbox2 := hβ z2 hb2
      have hinner := innerSum_abs_le hX hbox1 hbox2
      set Ssum : ℝ := ∑ d ∈ Work.FITop4.Sset z1 z2,
            ((Nat.totient d : ℝ) / (d : ℝ))
              * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
              * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 with hS
      have hinner' : |Ssum| ≤ (X:ℝ) * L := by
        rw [hL]; exact hinner
      rw [norm_mul, norm_mul, norm_star]
      rw [show ‖(Ssum : ℂ)‖ = |Ssum| from RCLike.norm_ofReal Ssum]
      exact mul_le_mul_of_nonneg_left hinner' (by positivity)
    · rw [if_neg hcop]; simp only [norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (by positivity) hLnn)
  have hmain : ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                    ((Nat.totient d : ℝ) / (d : ℝ))
                      * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
                      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
           else 0)‖ ≤ ((X:ℝ) * L) * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖)^2 := by
    have h3 : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z1‖ * ‖β z2‖ * ((X:ℝ) * L))
        = ((X:ℝ) * L) * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖)^2 := by
      simp only [← Finset.sum_mul]
      rw [← Finset.sum_mul_sum]
      ring
    calc ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            (if Work.FIPlan.GaussCoprime z1 z2 then
              β z1 * star (β z2)
                * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                      ((Nat.totient d : ℝ) / (d : ℝ))
                        * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
                        * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
             else 0)‖
        ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖(if Work.FIPlan.GaussCoprime z1 z2 then
                β z1 * star (β z2)
                  * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                        ((Nat.totient d : ℝ) / (d : ℝ))
                          * (if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0)
                          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
               else 0)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun z1 _ => norm_sum_le _ _))
      _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z1‖ * ‖β z2‖ * ((X:ℝ) * L) :=
          Finset.sum_le_sum (fun z1 h1 => Finset.sum_le_sum (fun z2 h2 => hpair z1 h1 z2 h2))
      _ = ((X:ℝ) * L) * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖)^2 := h3
  have hgoal : 2 * (X:ℝ) * L * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖)^2
      = 2 * (((X:ℝ) * L) * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖)^2) := by ring
  rw [hgoal]
  exact mul_le_mul_of_nonneg_left hmain (by norm_num)
/-- `t^n e^{-dt} ≤ ((n/d)/e)^n` for `t, d, n > 0`, from `log s ≤ s - 1`. -/
lemma pow_mul_exp_le (n : ℕ) (hn : 1 ≤ n) {d t : ℝ} (hd : 0 < d) (ht : 0 < t) :
    t ^ n * Real.exp (-(d * t)) ≤ Real.exp ((n:ℝ) * (Real.log ((n:ℝ) / d) - 1)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnne : ((n:ℝ)) ≠ 0 := ne_of_gt hnpos
  have hdne : d ≠ 0 := ne_of_gt hd
  have hnd : 0 < (n:ℝ) / d := div_pos hnpos hd
  have hs : 0 < d * t / (n:ℝ) := div_pos (mul_pos hd ht) hnpos
  have hsne : d * t / (n:ℝ) ≠ 0 := ne_of_gt hs
  have hlog := Real.log_le_sub_one_of_pos hs
  have hstep : (n:ℝ) * Real.log (d * t / (n:ℝ)) ≤ d * t - (n:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog hnpos.le
    rw [mul_sub, mul_one] at h
    have hns : (n:ℝ) * (d * t / (n:ℝ)) = d * t := by field_simp
    rw [hns] at h
    linarith
  have hsplit : Real.log t = Real.log (d * t / (n:ℝ)) + Real.log ((n:ℝ) / d) := by
    rw [← Real.log_mul hsne (ne_of_gt hnd)]
    congr 1
    field_simp
  have hkey : (n:ℝ) * Real.log t - d * t ≤ (n:ℝ) * (Real.log ((n:ℝ)/d) - 1) := by
    rw [hsplit]; nlinarith [hstep]
  have htn : t ^ n = Real.exp ((n:ℝ) * Real.log t) := by
    rw [← Real.exp_log (pow_pos ht n), Real.log_pow]
  calc t ^ n * Real.exp (-(d * t))
      = Real.exp ((n:ℝ) * Real.log t) * Real.exp (-(d * t)) := by rw [htn]
    _ = Real.exp ((n:ℝ) * Real.log t + -(d * t)) := (Real.exp_add _ _).symm
    _ = Real.exp ((n:ℝ) * Real.log t - d * t) := by congr 1
    _ ≤ Real.exp ((n:ℝ) * (Real.log ((n:ℝ) / d) - 1)) := Real.exp_le_exp.mpr hkey

theorem area7_numeric_aux :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N X θ : ℝ), 16 ≤ N → 1 ≤ X →
        X ≤ (Real.log N) ^ (2 ^ 20) →
        0 < θ → θ * (Real.log N) ^ (2 ^ 20) ≤ 1 →
        400000 * X * Real.log (8 * (1 + θ) * N)
          * (θ ^ 2 * N + θ * Real.sqrt N + 1)
          * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3
        ≤ C * X⁻¹ * N ^ 2 * Real.log N := by
  set nA : ℕ := 2 ^ 21 + 3 with hnA
  set nB : ℕ := 2 ^ 20 + 3 with hnB
  set EA : ℝ := Real.exp ((nA:ℝ) * (Real.log ((nA:ℝ) / (3/2)) - 1)) with hEA
  set EB : ℝ := Real.exp ((nB:ℝ) * (Real.log ((nB:ℝ) / 1) - 1)) with hEB
  set EC : ℝ := Real.exp ((3:ℝ) * (Real.log ((3:ℝ) / (1/2)) - 1)) with hEC
  have hEApos : 0 < EA := by rw [hEA]; positivity
  have hEBpos : 0 < EB := by rw [hEB]; positivity
  have hECpos : 0 < EC := by rw [hEC]; positivity
  refine ⟨12800000 * EA + 38400000 * EB + 38400000 * EC + 12800000, by positivity, ?_⟩
  intro N X θ hN hX hXb hθpos hθsmall
  have hNpos : (0:ℝ) < N := by linarith
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hXpos : (0:ℝ) < X := by linarith
  have hXnn : (0:ℝ) ≤ X := by linarith
  set t : ℝ := Real.log N with ht
  have htpos : 0 < t := by rw [ht]; exact Real.log_pos (by linarith)
  have ht1 : 1 ≤ t := by
    rw [ht]
    have h1 : (1:ℝ) ≤ Real.log 16 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 16)]
      linarith [Real.exp_one_lt_three]
    exact le_trans h1 (Real.log_le_log (by norm_num) hN)
  have hexpN : Real.exp t = N := by rw [ht]; exact Real.exp_log hNpos
  have hsqhalf : (Real.exp (t/2))^2 = N := by
    rw [pow_two, ← Real.exp_add, show t/2 + t/2 = t from by ring, hexpN]
  have hhalf : Real.exp (t/2) = Real.sqrt N := by
    rw [eq_comm, Real.sqrt_eq_iff_eq_sq hNpos.le (Real.exp_pos _).le]
    exact hsqhalf.symm
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hsNsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hsNnn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN1
  have hK1 : 1 ≤ t ^ (2^20) := one_le_pow₀ ht1
  have htpowpos : 0 < t ^ (2^20) := pow_pos htpos _
  have hθ1 : θ ≤ 1 := by
    calc θ = θ * 1 := by ring
      _ ≤ θ * t ^ (2^20) := mul_le_mul_of_nonneg_left hK1 hθpos.le
      _ ≤ 1 := hθsmall
  have hθle : θ ≤ 1 / t ^ (2^20) := by
    rw [le_div_iff₀ htpowpos]; exact hθsmall
  have hXθ : X * θ ≤ 1 := by
    have h := mul_le_mul hXb hθle hθpos.le htpowpos.le
    rwa [mul_one_div, div_self (ne_of_gt htpowpos)] at h
  -- log bounds
  have hlog1 : Real.log (8 * (1 + θ) * N) ≤ 2 * t := by
    have harg : 8 * (1 + θ) * N ≤ N^2 := by nlinarith [hθ1, hN]
    calc Real.log (8 * (1 + θ) * N) ≤ Real.log (N^2) :=
          Real.log_le_log (by positivity) harg
      _ = 2 * t := by rw [Real.log_pow, ← ht]; push_cast; ring
  have hlog1nn : 0 ≤ Real.log (8 * (1 + θ) * N) := by
    apply Real.log_nonneg; nlinarith [hθ1, hN]
  have hlog2 : Real.log (2 + N) ≤ 2 * t := by
    have harg : 2 + N ≤ N^2 := by nlinarith [hN]
    calc Real.log (2 + N) ≤ Real.log (N^2) := Real.log_le_log (by linarith) harg
      _ = 2 * t := by rw [Real.log_pow, ← ht]; push_cast; ring
  have hlog2nn : 0 ≤ Real.log (2 + N) := by apply Real.log_nonneg; linarith
  -- A, B bounds
  have hθsNnn : 0 ≤ θ * Real.sqrt N := mul_nonneg hθpos.le hsNnn
  have hA_le : θ^2 * N + θ * Real.sqrt N + 1 ≤ (1 + θ * Real.sqrt N)^2 := by
    have hexp : (1 + θ * Real.sqrt N)^2
        = 1 + 2 * (θ * Real.sqrt N) + (θ * Real.sqrt N)^2 := by ring
    rw [hexp]
    have hsq : (θ * Real.sqrt N)^2 = θ^2 * N := by rw [mul_pow, hsNsq]
    rw [hsq]
    linarith [hθsNnn]
  have hB_le : θ * N + Real.sqrt N + 1 ≤ 2 * Real.sqrt N * (1 + θ * Real.sqrt N) := by
    have hterm : 2 * Real.sqrt N * (θ * Real.sqrt N) = 2 * (θ * N) := by
      rw [show 2 * Real.sqrt N * (θ * Real.sqrt N) = 2 * θ * (Real.sqrt N * Real.sqrt N) by ring,
        hsN]
      ring
    have hexp : 2 * Real.sqrt N * (1 + θ * Real.sqrt N) = 2 * Real.sqrt N + 2 * (θ * N) := by
      rw [mul_add, mul_one, hterm]
    rw [hexp]
    have hθNnn : 0 ≤ θ * N := mul_nonneg hθpos.le hNpos.le
    linarith [hθNnn, hsN1]
  -- Step 1: log bounds
  have hstep1 : 400000 * X * Real.log (8 * (1 + θ) * N)
        * (θ ^ 2 * N + θ * Real.sqrt N + 1)
        * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3
      ≤ 400000 * X * (2 * t)
        * (θ ^ 2 * N + θ * Real.sqrt N + 1)
        * (θ * N + Real.sqrt N + 1) * (2 * t) ^ 3 := by
    have h1 : 400000 * X * Real.log (8 * (1 + θ) * N) ≤ 400000 * X * (2 * t) :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have h2 : (400000 * X * Real.log (8 * (1 + θ) * N)) * (θ ^ 2 * N + θ * Real.sqrt N + 1)
        ≤ (400000 * X * (2 * t)) * (θ ^ 2 * N + θ * Real.sqrt N + 1) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ((400000 * X * Real.log (8 * (1 + θ) * N)) * (θ ^ 2 * N + θ * Real.sqrt N + 1))
          * (θ * N + Real.sqrt N + 1)
        ≤ ((400000 * X * (2 * t)) * (θ ^ 2 * N + θ * Real.sqrt N + 1))
            * (θ * N + Real.sqrt N + 1) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : (Real.log (2 + N))^3 ≤ (2 * t)^3 := pow_le_pow_left₀ hlog2nn hlog2 3
    exact mul_le_mul h3 h4 (pow_nonneg hlog2nn 3) (by positivity)
  -- Step 2: A, B bounds and simplification
  have hstep2 : 400000 * X * (2 * t)
        * (θ ^ 2 * N + θ * Real.sqrt N + 1)
        * (θ * N + Real.sqrt N + 1) * (2 * t) ^ 3
      ≤ 12800000 * X * Real.sqrt N * t^4 * (1 + θ * Real.sqrt N)^3 := by
    have hA' : (400000 * X * (2 * t)) * (θ ^ 2 * N + θ * Real.sqrt N + 1)
        ≤ (400000 * X * (2 * t)) * (1 + θ * Real.sqrt N)^2 :=
      mul_le_mul_of_nonneg_left hA_le (by positivity)
    have hAB : ((400000 * X * (2 * t)) * (θ ^ 2 * N + θ * Real.sqrt N + 1))
          * (θ * N + Real.sqrt N + 1)
        ≤ ((400000 * X * (2 * t)) * (1 + θ * Real.sqrt N)^2)
            * (2 * Real.sqrt N * (1 + θ * Real.sqrt N)) :=
      mul_le_mul hA' hB_le (by positivity) (by positivity)
    calc 400000 * X * (2 * t) * (θ ^ 2 * N + θ * Real.sqrt N + 1)
            * (θ * N + Real.sqrt N + 1) * (2 * t) ^ 3
        ≤ ((400000 * X * (2 * t)) * (1 + θ * Real.sqrt N)^2)
            * (2 * Real.sqrt N * (1 + θ * Real.sqrt N)) * (2 * t) ^ 3 :=
          mul_le_mul_of_nonneg_right hAB (pow_nonneg (by linarith) 3)
      _ = 12800000 * X * Real.sqrt N * t^4 * (1 + θ * Real.sqrt N)^3 := by ring
  -- Step 3: expand (1+u)^3
  have hstep3 : 12800000 * X * Real.sqrt N * t^4 * (1 + θ * Real.sqrt N)^3
      = 12800000 * X * Real.sqrt N * t^4
        + 38400000 * X * θ * N * t^4
        + 38400000 * X * θ^2 * N * Real.sqrt N * t^4
        + 12800000 * X * θ^3 * N^2 * t^4 := by
    have hu2 : (θ * Real.sqrt N)^2 = θ^2 * N := by rw [mul_pow, hsNsq]
    have hu3 : (θ * Real.sqrt N)^3 = θ^3 * N * Real.sqrt N := by
      rw [show (θ * Real.sqrt N)^3 = θ^3 * (Real.sqrt N)^3 by rw [mul_pow],
        show (Real.sqrt N)^3 = N * Real.sqrt N by
          rw [show (Real.sqrt N)^3 = (Real.sqrt N)^2 * Real.sqrt N by ring, hsNsq]]
      ring
    rw [show (1 + θ * Real.sqrt N)^3
        = 1 + 3*(θ*Real.sqrt N) + 3*(θ*Real.sqrt N)^2 + (θ*Real.sqrt N)^3 by ring, hu2, hu3]
    ring_nf
    simp only [hsNsq]
    ring
  -- reduction helper
  have reduce : ∀ (A C : ℝ), X * A ≤ C * N^2 * t → A ≤ C * X⁻¹ * N^2 * t := by
    intro A C h
    calc A = X⁻¹ * (X * A) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hXpos), one_mul]
      _ ≤ X⁻¹ * (C * N^2 * t) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hXnn)
      _ = C * X⁻¹ * N^2 * t := by ring
  -- Term 1
  have hT1 : 12800000 * X * Real.sqrt N * t^4 ≤ (12800000 * EA) * X⁻¹ * N^2 * t := by
    have hb := pow_mul_exp_le nA (by rw [hnA]; norm_num) (show (0:ℝ) < 3/2 by norm_num) htpos
    have hb' : t ^ nA * Real.exp (-(3/2 * t)) ≤ EA := by rw [hEA]; exact hb
    have hexp32 : Real.exp (3/2 * t) = N * Real.sqrt N := by
      rw [show (3/2:ℝ) * t = t + t/2 by ring, Real.exp_add, hexpN, hhalf]
    have htnA : t ^ nA ≤ EA * Real.exp (3/2 * t) := by
      have hcancel : t ^ nA = t ^ nA * Real.exp (-(3/2 * t)) * (Real.exp (-(3/2 * t)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
      rw [hcancel]
      calc t ^ nA * Real.exp (-(3/2 * t)) * (Real.exp (-(3/2 * t)))⁻¹
          ≤ EA * (Real.exp (-(3/2 * t)))⁻¹ := mul_le_mul_of_nonneg_right hb' (by positivity)
        _ = EA * Real.exp (3/2 * t) := by congr 1; rw [Real.exp_neg, inv_inv]
    have hb'' : t ^ nA * Real.sqrt N ≤ EA * N^2 := by
      calc t ^ nA * Real.sqrt N ≤ (EA * Real.exp (3/2 * t)) * Real.sqrt N :=
            mul_le_mul_of_nonneg_right htnA hsNnn
        _ = EA * N^2 := by
            rw [hexp32, show EA * (N * Real.sqrt N) * Real.sqrt N
                = EA * (N * (Real.sqrt N * Real.sqrt N)) by ring, hsN]
            ring
    have hX2 : X^2 ≤ t ^ (2^21) := by
      have h := pow_le_pow_left₀ hXnn hXb 2
      rwa [← pow_mul, show 2^20 * 2 = 2^21 from by norm_num] at h
    have hX2sqrt : X^2 * Real.sqrt N * t^3 ≤ t ^ nA * Real.sqrt N := by
      have h1 : X^2 * Real.sqrt N ≤ t^(2^21) * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hX2 hsNnn
      have h2 : X^2 * Real.sqrt N * t^3 ≤ t^(2^21) * Real.sqrt N * t^3 :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg htpos.le 3)
      refine h2.trans (le_of_eq ?_)
      rw [hnA]
      rw [show t ^ (2^21) * Real.sqrt N * t ^ 3 = t ^ (2^21) * t ^ 3 * Real.sqrt N by ring,
        ← pow_add]
    have h1 : X * (12800000 * X * Real.sqrt N * t^4) ≤ (12800000 * EA) * N^2 * t := by
      have hxx : X * (12800000 * X * Real.sqrt N * t^4)
          = 12800000 * (X^2 * Real.sqrt N * t^3) * t := by ring
      rw [hxx]
      calc 12800000 * (X^2 * Real.sqrt N * t^3) * t
          ≤ 12800000 * (EA * N^2) * t :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hX2sqrt.trans hb'') (by norm_num)) htpos.le
        _ = (12800000 * EA) * N^2 * t := by ring
    exact reduce _ _ h1
  -- Term 2
  have hT2 : 38400000 * X * θ * N * t^4 ≤ (38400000 * EB) * X⁻¹ * N^2 * t := by
    have hb := pow_mul_exp_le nB (by rw [hnB]; norm_num) (by norm_num : (0:ℝ) < 1) htpos
    have hb' : t ^ nB * Real.exp (-(1 * t)) ≤ EB := by rw [hEB]; exact hb
    have htnB : t ^ nB ≤ EB * N := by
      have hcancel : t ^ nB = t ^ nB * Real.exp (-(1*t)) * (Real.exp (-(1*t)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
      rw [hcancel]
      calc t ^ nB * Real.exp (-(1*t)) * (Real.exp (-(1*t)))⁻¹
          ≤ EB * (Real.exp (-(1*t)))⁻¹ := mul_le_mul_of_nonneg_right hb' (by positivity)
        _ = EB * Real.exp (1*t) := by congr 1; rw [Real.exp_neg, inv_inv]
        _ = EB * N := by rw [one_mul, hexpN]
    have hX2θ : X^2 * θ ≤ t ^ (2^20) := by
      have h : X^2 * θ = X * (X * θ) := by ring
      rw [h]
      calc X * (X * θ) ≤ X * 1 := mul_le_mul_of_nonneg_left hXθ hXnn
        _ = X := by ring
        _ ≤ t^(2^20) := hXb
    have hkey : X^2 * θ * t^3 ≤ EB * N := by
      refine (mul_le_mul_of_nonneg_right hX2θ (pow_nonneg htpos.le 3)).trans ?_
      have heq : t ^ (2^20) * t^3 = t ^ nB := by rw [hnB, ← pow_add]
      rw [heq]; exact htnB
    have h1 : X * (38400000 * X * θ * N * t^4) ≤ (38400000 * EB) * N^2 * t := by
      have hxx : X * (38400000 * X * θ * N * t^4)
          = 38400000 * (X^2 * θ * t^3) * N * t := by ring
      rw [hxx]
      calc 38400000 * (X^2 * θ * t^3) * N * t ≤ 38400000 * (EB * N) * N * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkey (by norm_num)) hNpos.le) htpos.le
        _ = (38400000 * EB) * N^2 * t := by ring
    exact reduce _ _ h1
  -- Term 3
  have hT3 : 38400000 * X * θ^2 * N * Real.sqrt N * t^4
      ≤ (38400000 * EC) * X⁻¹ * N^2 * t := by
    have hb := pow_mul_exp_le 3 (by norm_num) (show (0:ℝ) < 1/2 by norm_num) htpos
    have hb' : t ^ 3 * Real.exp (-(1/2 * t)) ≤ EC := by rw [hEC]; exact hb
    have ht3 : t ^ 3 ≤ EC * Real.sqrt N := by
      have hcancel : t ^ 3 = t ^ 3 * Real.exp (-(1/2*t)) * (Real.exp (-(1/2*t)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
      rw [hcancel]
      calc t ^ 3 * Real.exp (-(1/2*t)) * (Real.exp (-(1/2*t)))⁻¹
          ≤ EC * (Real.exp (-(1/2*t)))⁻¹ := mul_le_mul_of_nonneg_right hb' (by positivity)
        _ = EC * Real.exp (1/2*t) := by congr 1; rw [Real.exp_neg, inv_inv]
        _ = EC * Real.sqrt N := by rw [show (1/2:ℝ)*t = t/2 by ring, hhalf]
    have hXθ2 : (X * θ)^2 ≤ 1 := by
      have h := mul_le_mul hXθ hXθ (mul_nonneg hXnn hθpos.le) (by norm_num : (0:ℝ) ≤ 1)
      simpa [pow_two] using h
    have hkey : X^2 * θ^2 * t^3 ≤ EC * Real.sqrt N := by
      have hXθ2' : X^2 * θ^2 = (X*θ)^2 := by ring
      rw [hXθ2']
      calc (X*θ)^2 * t^3 ≤ 1 * t^3 := mul_le_mul_of_nonneg_right hXθ2 (pow_nonneg htpos.le 3)
        _ = t^3 := by ring
        _ ≤ EC * Real.sqrt N := ht3
    have h1 : X * (38400000 * X * θ^2 * N * Real.sqrt N * t^4)
        ≤ (38400000 * EC) * N^2 * t := by
      have hxx : X * (38400000 * X * θ^2 * N * Real.sqrt N * t^4)
          = 38400000 * (X^2 * θ^2 * t^3) * (N * Real.sqrt N) * t := by ring
      rw [hxx]
      calc 38400000 * (X^2 * θ^2 * t^3) * (N * Real.sqrt N) * t
          ≤ 38400000 * (EC * Real.sqrt N) * (N * Real.sqrt N) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkey (by norm_num)) (by positivity)) htpos.le
        _ = (38400000 * EC) * N^2 * t := by
            rw [show 38400000 * (EC * Real.sqrt N) * (N * Real.sqrt N) * t
                = 38400000 * EC * (Real.sqrt N * (N * Real.sqrt N)) * t by ring,
              show Real.sqrt N * (N * Real.sqrt N) = N * (Real.sqrt N * Real.sqrt N) by ring,
              hsN]
            ring
    exact reduce _ _ h1
  -- Term 4
  have hT4 : 12800000 * X * θ^3 * N^2 * t^4 ≤ 12800000 * X⁻¹ * N^2 * t := by
    have htpow3 : t^3 ≤ t ^ (2^20) := pow_le_pow_right₀ ht1 (by norm_num : 3 ≤ 2^20)
    have hkey : X^2 * θ^3 * t^3 ≤ 1 := by
      have hXθ2 : X^2 * θ^3 = (X*θ)^2 * θ := by ring
      rw [hXθ2]
      have h2 : (X*θ)^2 ≤ 1 := by
        have h := mul_le_mul hXθ hXθ (mul_nonneg hXnn hθpos.le) (by norm_num : (0:ℝ) ≤ 1)
        simpa [pow_two] using h
      have h3 : θ * t^3 ≤ 1 := by
        have h5 : (1 / t ^ (2^20)) * t ^ (2^20) = 1 := by
          rw [one_div, inv_mul_cancel₀ (ne_of_gt htpowpos)]
        calc θ * t^3 ≤ (1 / t ^ (2^20)) * t ^ (2^20) :=
              (mul_le_mul_of_nonneg_right hθle (pow_nonneg htpos.le 3)).trans
                (mul_le_mul_of_nonneg_left htpow3 (by positivity))
          _ = 1 := h5
      calc (X*θ)^2 * θ * t^3 = (X*θ)^2 * (θ * t^3) := by ring
        _ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) (by norm_num)
        _ = 1 := by ring
    have h1 : X * (12800000 * X * θ^3 * N^2 * t^4) ≤ 12800000 * N^2 * t := by
      have hxx : X * (12800000 * X * θ^3 * N^2 * t^4)
          = 12800000 * (X^2 * θ^3 * t^3) * N^2 * t := by ring
      rw [hxx]
      calc 12800000 * (X^2 * θ^3 * t^3) * N^2 * t ≤ 12800000 * 1 * N^2 * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkey (by norm_num)) (by positivity)) htpos.le
        _ = 12800000 * N^2 * t := by ring
    exact reduce _ _ h1
  have hmain : 400000 * X * Real.log (8 * (1 + θ) * N)
        * (θ ^ 2 * N + θ * Real.sqrt N + 1)
        * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3
      ≤ (12800000 * EA + 38400000 * EB + 38400000 * EC + 12800000) * X⁻¹ * N^2 * t := by
    have h12 := hstep1.trans (hstep2.trans hstep3.le)
    have hsum : 12800000 * X * Real.sqrt N * t^4 + 38400000 * X * θ * N * t^4
          + 38400000 * X * θ^2 * N * Real.sqrt N * t^4
          + 12800000 * X * θ^3 * N^2 * t^4
        ≤ (12800000 * EA) * X⁻¹ * N^2 * t + (38400000 * EB) * X⁻¹ * N^2 * t
          + (38400000 * EC) * X⁻¹ * N^2 * t + 12800000 * X⁻¹ * N^2 * t := by
      linarith [hT1, hT2, hT3, hT4]
    calc 400000 * X * Real.log (8 * (1 + θ) * N) * (θ ^ 2 * N + θ * Real.sqrt N + 1)
            * (θ * N + Real.sqrt N + 1) * (Real.log (2 + N)) ^ 3
        ≤ 12800000 * X * Real.sqrt N * t^4 + 38400000 * X * θ * N * t^4
          + 38400000 * X * θ^2 * N * Real.sqrt N * t^4
          + 12800000 * X * θ^3 * N^2 * t^4 := h12
      _ ≤ (12800000 * EA) * X⁻¹ * N^2 * t + (38400000 * EB) * X⁻¹ * N^2 * t
          + (38400000 * EC) * X⁻¹ * N^2 * t + 12800000 * X⁻¹ * N^2 * t := hsum
      _ = (12800000 * EA + 38400000 * EB + 38400000 * EC + 12800000) * X⁻¹ * N^2 * t := by ring
  simpa only [← ht] using hmain


/-- `Pa.θ * (log N)^{2^20} ≤ 1`, from `θ = (log x)^{-A'}`, `A' ≥ 2^20` and `log x > 2 log N`. -/
lemma theta_mul_log_bound (Pa : Work.FITop.Params) (hN : 16 ≤ Pa.N) :
    Pa.θ * (Real.log (Pa.N : ℝ)) ^ (2^20) ≤ 1 := by
  have hx3 : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hLx1 : 1 ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
      linarith [Real.exp_one_lt_three]
    exact le_trans h3 (Real.log_le_log (by norm_num) hx3)
  have hLx0 : 0 < Real.log (Pa.x : ℝ) := lt_of_lt_of_le one_pos hLx1
  have hrpowB : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 := by
    rw [Real.rpow_neg hLx0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hLx1 Pa.hB.le)
  have hNlt : Pa.N < (Pa.x : ℝ) ^ ((1:ℝ)/2) := by
    have h := Pa.hNhi
    have h2 : Pa.N < (Pa.x : ℝ) ^ ((1:ℝ)/2) * 1 :=
      lt_of_lt_of_le h (mul_le_mul_of_nonneg_left hrpowB (Real.rpow_nonneg (by linarith) _))
    simpa using h2
  have hNpos : (0:ℝ) < Pa.N := by linarith
  have hLn_lt : Real.log (Pa.N : ℝ) < (1/2) * Real.log (Pa.x : ℝ) := by
    have h := Real.log_lt_log hNpos hNlt
    rwa [Real.log_rpow (by linarith : (0:ℝ) < (Pa.x : ℝ))] at h
  have hLn0 : 0 < Real.log (Pa.N : ℝ) := Real.log_pos (by linarith)
  have hratio : Real.log (Pa.N : ℝ) / Real.log (Pa.x : ℝ) ≤ 1 := by
    rw [div_le_one hLx0]; linarith [hLn_lt, hLx0]
  have hA'mem : (2:ℝ)^(20:ℕ) ≤ Pa.A' := by
    have := Pa.hA'; have := Pa.hA; linarith
  calc Pa.θ * (Real.log (Pa.N : ℝ)) ^ (2^20)
      = (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log (Pa.N : ℝ)) ^ (2^20) := by rw [Pa.hθ]
    _ = (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log (Pa.N : ℝ)) ^ ((2:ℝ)^(20:ℕ)) := by
          rw [← Real.rpow_natCast (Real.log (Pa.N : ℝ)) (2^20)]
          congr 1; norm_num
    _ ≤ (Real.log (Pa.x : ℝ)) ^ (-((2:ℝ)^(20:ℕ))) * (Real.log (Pa.N : ℝ)) ^ ((2:ℝ)^(20:ℕ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLn0.le _)
          exact Real.rpow_le_rpow_of_exponent_le hLx1 (by linarith [hA'mem])
    _ = (Real.log (Pa.N : ℝ) / Real.log (Pa.x : ℝ)) ^ ((2:ℝ)^(20:ℕ)) := by
          rw [Real.div_rpow hLn0.le hLx0.le, Real.rpow_neg hLx0.le, div_eq_mul_inv]
          ring
    _ ≤ 1 := Real.rpow_le_one (div_nonneg hLn0.le hLx0.le) hratio (by positivity)

/-- **Elementary bound for area 7 in the polylogarithmic range `X ≤ (log N)^{2^20}`.**

Route (fully elementary, no (17.10), no Proposition 17.2):

1. `Wcut + Bcut = Tcut (1_{X < d ∧ |Δ| ≤ 4dX})` (`Tcut6_add_cut`, `Tcut6_congr_cut`,
   `cutW_add_cutB`), and `Tcut6_eq_sum_ofReal` exposes the inner `d`-sum as a real sum.
2. At a fixed pair, the supporting `d` satisfy `4d ∣ |Δ|` and `e := |Δ|/(4d) ≤ X`, so the map
   `d ↦ e` injects them into `{1, …, X}`: at most `X` divisors, each with `φ(d)/d ≤ 1`,
   `|ratioSym| ≤ 1` and `0 ≤ logFac6 ≤ log(8(1+θ)N)` (the last two need `InPolarBox` for both
   points, from `IsBetaCoeff6.support`).  Hence the inner sum is `≤ X·log(8(1+θ)N)`.
3. Summing over the pairs and factorising the pair sum,
   `‖Wcut + Bcut‖ ≤ 2·X·log(8(1+θ)N)·(Σ_{z ∈ gBox} ‖β z‖)²`, and by Cauchy–Schwarz and the two
   hypotheses `hcard`/`hmass` this is
   `≤ 2·200·1000·X·log(8(1+θ)N)·(θ²N+θ√N+1)(θN+√N+1)(log(2+N))³`.
4. Compare term by term with `C(Pz⁻¹+X⁻¹)N²log N`: the binding conditions are
   `θ³X²(log N)³ ≤ C` (i.e. `X² ≤ C(log x)^{3A'}(log N)^{-3}`) and `θ²X²(log N)³ ≤ CN^{1/2}`,
   both satisfied since `θ = (log x)^{-A'}`, `A' ≥ 2A+2^{20}`, `log x > 2log N` and
   `X ≤ (log N)^{2^20}` (`2·2^20 + 3 ≤ 3A'`). -/
theorem area7_bound_polylog :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 16 ≤ Pa.N → 1 ≤ X →
        (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
          ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) →
        (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
          ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 →
        (X : ℝ) ≤ (Real.log (Pa.N : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) →
        ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
          ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
  obtain ⟨C, hCpos, hnum⟩ := area7_numeric_aux
  refine ⟨C, hCpos, ?_⟩
  intro Pa X φ z0 β hβ hN16 hX1 hcard hmass hXbnd
  set S := Work.FIPlan.gBox (Work.FITop.radN Pa) with hS
  set Sf := S.filter (fun z => β z ≠ 0) with hSf
  have hθpos : 0 < Pa.θ := Pa.hθ0
  have hθsmall : Pa.θ * (Real.log (Pa.N : ℝ)) ^ (2^20) ≤ 1 := theta_mul_log_bound Pa hN16
  have hXb : (X:ℝ) ≤ (Real.log (Pa.N : ℝ)) ^ (2^20) := by
    have h := hXbnd
    rw [show (2:ℝ)^(20:ℕ) = ((2^20 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] at h
    exact h
  have hWB : Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β
      = Work.FITop4.Tcut (Work.FITop.radN Pa)
          (fun z1 z2 d => if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0) β := by
    rw [Work.FITop4.Wcut, Work.FITop4.Bcut, Tcut6_add_cut]
    exact Tcut6_congr_cut _ _ _ _ (fun z1 z2 d => cutW_add_cutB (Work.FIPlan.absDelta z1 z2) X d)
  have hnorm := Tcut6_norm_le (Pa := Pa) (X := X) (φ := φ) (β := β)
    (fun z hz => Work.FITop4.IsBetaCoeff6.support hβ hz) hX1
  have hcs : (∑ z ∈ S, ‖β z‖)^2 ≤ 200 * (Pa.θ^2*Pa.N + Pa.θ*Real.sqrt Pa.N + 1)
      * (1000 * (Pa.θ*Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2+Pa.N))^3) := by
    have hsum_eq : ∑ z ∈ S, ‖β z‖ = ∑ z ∈ Sf, ‖β z‖ := by
      rw [hSf, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro z _
      by_cases hz : β z = 0 <;> simp [hz]
    have h1 : (∑ z ∈ S, ‖β z‖)^2 ≤ (Sf.card : ℝ) * (∑ z ∈ S, ‖β z‖^2) := by
      rw [hsum_eq]
      have hcs0 : (∑ z ∈ Sf, ‖β z‖)^2 ≤ (∑ z ∈ Sf, ‖β z‖^2) * (Sf.card : ℝ) := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq Sf (fun z => ‖β z‖) (fun _ => (1:ℝ))
      refine hcs0.trans ?_
      have hle : (∑ z ∈ Sf, ‖β z‖^2) ≤ ∑ z ∈ S, ‖β z‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · rw [hSf]; exact Finset.filter_subset _ _
        · intro z _ _; positivity
      calc (∑ z ∈ Sf, ‖β z‖^2) * (Sf.card:ℝ) ≤ (∑ z ∈ S, ‖β z‖^2) * (Sf.card:ℝ) :=
            mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
        _ = (Sf.card:ℝ) * (∑ z ∈ S, ‖β z‖^2) := by ring
    have hcard' : (Sf.card : ℝ) ≤ 200 * (Pa.θ^2*Pa.N + Pa.θ*Real.sqrt Pa.N + 1) := hcard
    have hmass' : (∑ z ∈ S, ‖β z‖^2)
        ≤ 1000 * (Pa.θ*Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2+Pa.N))^3 := hmass
    exact h1.trans (mul_le_mul hcard' hmass' (by positivity) (by positivity))
  have hlog1 : 0 ≤ Real.log (8 * (1 + Pa.θ) * Pa.N) := by
    apply Real.log_nonneg; nlinarith [Pa.hθ0, Pa.hN1]
  have hN0 : ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
        (fun z1 z2 d => if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0) β‖
      ≤ 400000 * (X:ℝ) * Real.log (8*(1+Pa.θ)*Pa.N)
          * (Pa.θ^2*Pa.N + Pa.θ*Real.sqrt Pa.N + 1)
          * (Pa.θ*Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2+Pa.N))^3 := by
    calc ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
          (fun z1 z2 d => if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0) β‖
        ≤ 2 * (X:ℝ) * Real.log (8*(1+Pa.θ)*Pa.N) * (∑ z ∈ S, ‖β z‖)^2 := hnorm
      _ ≤ 2 * (X:ℝ) * Real.log (8*(1+Pa.θ)*Pa.N)
            * (200 * (Pa.θ^2*Pa.N + Pa.θ*Real.sqrt Pa.N + 1)
                * (1000 * (Pa.θ*Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2+Pa.N))^3)) := by
            apply mul_le_mul_of_nonneg_left hcs
            exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hlog1
      _ = 400000 * (X:ℝ) * Real.log (8*(1+Pa.θ)*Pa.N)
            * (Pa.θ^2*Pa.N + Pa.θ*Real.sqrt Pa.N + 1)
            * (Pa.θ*Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2+Pa.N))^3 := by ring
  have hnum' := hnum Pa.N (X:ℝ) Pa.θ hN16 (by exact_mod_cast hX1) hXb hθpos hθsmall
  calc ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      = ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
          (fun z1 z2 d => if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0) β‖ := by
        rw [hWB]
    _ ≤ 400000 * (X:ℝ) * Real.log (8*(1+Pa.θ)*Pa.N)
          * (Pa.θ^2*Pa.N + Pa.θ*Real.sqrt Pa.N + 1)
          * (Pa.θ*Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2+Pa.N))^3 := hN0
    _ ≤ C * ((X:ℝ))⁻¹ * (Pa.N)^2 * Real.log Pa.N := hnum'
    _ ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
          have hPzinv : 0 ≤ (Pa.Pz:ℝ)⁻¹ := by
            have hP : (0:ℕ) < Pa.Pz := lt_of_lt_of_le Nat.zero_lt_two Pa.hP2
            positivity
          have h1 : ((X:ℝ))⁻¹ ≤ (Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹ := by linarith
          calc C * ((X:ℝ))⁻¹ * Pa.N^2 * Real.log Pa.N
              = C * (((X:ℝ))⁻¹ * Pa.N^2 * Real.log Pa.N) := by ring
            _ ≤ C * (((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^2 * Real.log Pa.N) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right h1 (sq_nonneg (Pa.N)))
                    (Real.log_nonneg Pa.hN1)) hCpos.le
            _ = C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by ring


end

end Work.FIArea7

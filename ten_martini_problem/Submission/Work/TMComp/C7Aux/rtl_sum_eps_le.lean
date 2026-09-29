import Mathlib
import Submission.Work.TMComp.C7Aux.rtlSchedule

namespace Work.TMComp.C7Aux

open Finset

theorem rtl_run_len_lt (A cκ b : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ)
    (hA : 0 < A) (hcκ : 0 < cκ) (hb : 0 < b)
    (hQ1 : ∀ i ≤ k, 1 ≤ Q i)
    (hmono : ∀ i < k, Q i < Q (i+1))
    (hgrowth : ∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ)))
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ))
    (hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4)
    (hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    {i t1 t2 : ℕ} (hik : i < k)
    (h1 : rtli A cκ Q k N₀ t1 = i) (h2 : rtli A cκ Q k N₀ t2 = i) (h12 : t1 ≤ t2) :
    ((t2 - t1 : ℕ) : ℝ) * (cκ / 4) < b := by
  set M := rtlMM cκ Q i with hM
  set n := t2 - t1 with hn
  have htn : t1 + n = t2 := by omega
  have hQ1i : 1 ≤ Q i := hQ1 i (le_of_lt hik)
  have hQipos : 0 < (Q i : ℝ) := by exact_mod_cast (by omega : 0 < Q i)
  have hMpos1 : 1 ≤ M := by rw [hM]; exact rtlMM_pos cκ Q hQ1i
  have hMge : Real.exp (cκ * (Q i : ℝ) / 2) / 10 ≤ (M : ℝ) := by
    rw [hM]; exact rtlMM_ge cκ Q i (hbig2 i (le_of_lt hik))
  have hMono : Monotone (rtli A cκ Q k N₀) := rtli_mono A cκ Q k N₀ hQ1 hA0
  have hrun : ∀ u, t1 ≤ u → u < t1 + n → rtli A cκ Q k N₀ u = i := by
    intro u hu1 hu2
    have hu2' : u ≤ t2 := by omega
    have hle : rtli A cκ Q k N₀ u ≤ i := by rw [← h2]; exact hMono hu2'
    have hge : i ≤ rtli A cκ Q k N₀ u := by rw [← h1]; exact hMono hu1
    exact le_antisymm hle hge
  have hN2 : rtlN A cκ Q k N₀ t2 = M^n * rtlN A cκ Q k N₀ t1 := by
    rw [← htn]
    have hh := rtlN_eq_pow A cκ Q k N₀ i t1 n hrun
    rw [← hM] at hh
    exact hh
  have hN1ge : A * (Q i : ℝ) ≤ (rtlN A cκ Q k N₀ t1 : ℝ) := by
    have hle : A * (Q 0 : ℝ) ≤ (rtlN A cκ Q k N₀ t1 : ℝ) := by
      have hN := N₀_le_rtlN A cκ Q k N₀ hQ1 t1
      calc A * (Q 0 : ℝ) ≤ (N₀ : ℝ) := hA0
        _ ≤ (rtlN A cκ Q k N₀ t1 : ℝ) := by exact_mod_cast hN
    have hh := rtli_spec (A:=A) (cκ:=cκ) (Q:=Q) (k:=k) (N₀:=N₀) (s:=t1) hle
    rwa [h1] at hh
  have hN2lt : (rtlN A cκ Q k N₀ t2 : ℝ) < A * (Q (i+1) : ℝ) := by
    have hg := rtli_greatest (A:=A) (cκ:=cκ) (Q:=Q) (k:=k) (N₀:=N₀) (s:=t2) (by rw [h2]; exact hik)
    rw [h2] at hg
    exact not_le.mp hg
  have hstep : (M:ℝ)^n * (A * (Q i : ℝ)) < A * (Q (i+1) : ℝ) := by
    calc (M:ℝ)^n * (A * (Q i : ℝ))
        ≤ (M:ℝ)^n * (rtlN A cκ Q k N₀ t1 : ℝ) :=
          mul_le_mul_of_nonneg_left hN1ge (pow_nonneg (by positivity) n)
      _ = ((M^n * rtlN A cκ Q k N₀ t1 : ℕ) : ℝ) := by push_cast; ring
      _ = (rtlN A cκ Q k N₀ t2 : ℝ) := by rw [hN2]
      _ < A * (Q (i+1) : ℝ) := hN2lt
  have hpowlt : (M:ℝ)^n < (Q (i+1) : ℝ) / (Q i : ℝ) := by
    have h' : A * ((M:ℝ)^n * (Q i : ℝ)) < A * (Q (i+1) : ℝ) := by nlinarith [hstep]
    have h'' : (M:ℝ)^n * (Q i : ℝ) < (Q (i+1) : ℝ) := lt_of_mul_lt_mul_left h' (le_of_lt hA)
    exact (lt_div_iff₀ hQipos).mpr h''
  have hexp_le : (Q (i+1) : ℝ) / (Q i : ℝ) ≤ Real.exp (b * (Q i : ℝ)) / (Q i : ℝ) :=
    div_le_div_of_nonneg_right (hgrowth i hik) (le_of_lt hQipos)
  have hMQi : (M:ℝ)^n < Real.exp (b * (Q i : ℝ)) / (Q i : ℝ) := lt_of_lt_of_le hpowlt hexp_le
  have hpowe : (Real.exp (cκ * (Q i : ℝ) / 2) / 10)^n ≤ (M:ℝ)^n :=
    pow_le_pow_left₀ (by positivity) hMge n
  have hmain : (Real.exp (cκ * (Q i : ℝ) / 2) / 10)^n < Real.exp (b * (Q i : ℝ)) / (Q i : ℝ) :=
    lt_of_le_of_lt hpowe hMQi
  have h1p : 0 < Real.exp (cκ * (Q i : ℝ) / 2) / 10 := by positivity
  have hlogle := Real.log_lt_log (pow_pos h1p n) hmain
  have h2l : Real.log ((Real.exp (cκ * (Q i : ℝ) / 2) / 10)^n)
      = (n:ℝ) * (cκ * (Q i : ℝ) / 2 - Real.log 10) := by
    rw [Real.log_pow, Real.log_div (Real.exp_pos _).ne' (by norm_num : (10:ℝ) ≠ 0), Real.log_exp]
  have h3l : Real.log (Real.exp (b * (Q i : ℝ)) / (Q i : ℝ))
      = b * (Q i : ℝ) - Real.log (Q i : ℝ) := by
    rw [Real.log_div (Real.exp_pos _).ne' (ne_of_gt hQipos), Real.log_exp]
  rw [h2l, h3l] at hlogle
  have hlogQi : 0 ≤ Real.log (Q i : ℝ) := Real.log_nonneg (by exact_mod_cast hQ1i : (1:ℝ) ≤ (Q i : ℝ))
  have hbigi : Real.log 10 ≤ cκ * (Q i : ℝ)/4 := hbig i (le_of_lt hik)
  have hfinal1 : (n:ℝ) * (cκ * (Q i : ℝ) / 4) < b * (Q i : ℝ) := by
    have h1' : (n:ℝ) * (cκ * (Q i : ℝ) / 4)
        ≤ (n:ℝ) * (cκ * (Q i : ℝ) / 2 - Real.log 10) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
    linarith [h1', hlogle, hlogQi]
  have hfac : (n:ℝ) * (cκ * (Q i : ℝ) / 4) = ((n:ℝ) * (cκ/4)) * (Q i : ℝ) := by ring
  have hres : (n:ℝ) * (cκ/4) < b := by
    have h2'' : ((n:ℝ)*(cκ/4)) * (Q i : ℝ) < b * (Q i : ℝ) := by rw [← hfac]; exact hfinal1
    exact lt_of_mul_lt_mul_right h2'' (le_of_lt hQipos)
  exact hres


theorem rtl_fiber_card_le (A cκ b : ℝ) (Q : ℕ → ℕ) (k N₀ : ℕ) (Sb : ℕ)
    (hA : 0 < A) (hcκ : 0 < cκ) (hb : 0 < b)
    (hQ1 : ∀ i ≤ k, 1 ≤ Q i)
    (hmono : ∀ i < k, Q i < Q (i+1))
    (hgrowth : ∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ)))
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ))
    (hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4)
    (hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    (hSb : 4 * b / cκ < Sb)
    {i : ℕ} (hik : i < k) (S : ℕ) :
    ((Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i)).card ≤ Sb := by
  classical
  by_cases hne : ((Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i)).Nonempty
  · set t1 := ((Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i)).min' hne with ht1
    have ht1mem : t1 ∈ (Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i) :=
      Finset.min'_mem _ hne
    have ht1val : rtli A cκ Q k N₀ t1 = i := (Finset.mem_filter.mp ht1mem).2
    have hsub : (Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i)
        ⊆ Finset.Ico t1 (t1 + Sb) := by
      intro t ht
      have htval : rtli A cκ Q k N₀ t = i := (Finset.mem_filter.mp ht).2
      have hlt : t1 ≤ t := Finset.min'_le _ t ht
      rw [Finset.mem_Ico]
      refine ⟨hlt, ?_⟩
      have hbnd := rtl_run_len_lt A cκ b Q k N₀ hA hcκ hb hQ1 hmono hgrowth hA0 hbig hbig2
        hik ht1val htval hlt
      have hcκ4 : 0 < cκ/4 := by linarith
      have h1 : ((t - t1 : ℕ) : ℝ) < 4 * b / cκ := by
        have h1' : ((t - t1 : ℕ) : ℝ) < b/(cκ/4) := (lt_div_iff₀ hcκ4).mpr hbnd
        have h1'' : b/(cκ/4) = 4*b/cκ := by field_simp
        rwa [h1''] at h1'
      have h2 : ((t - t1 : ℕ) : ℝ) < (Sb:ℝ) := lt_trans h1 hSb
      have h3 : t - t1 < Sb := Nat.cast_lt.mp h2
      omega
    calc ((Finset.range S).filter (fun t => rtli A cκ Q k N₀ t = i)).card
        ≤ (Finset.Ico t1 (t1 + Sb)).card := Finset.card_le_card hsub
      _ = (t1 + Sb) - t1 := Nat.card_Ico t1 (t1 + Sb)
      _ = Sb := by omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

theorem rtl_term_le (cκ C₀ : ℝ) (Q : ℕ → ℕ) (i : ℕ) (hC₀ : 0 ≤ C₀)
    (hge : Real.exp (cκ * (Q i : ℝ) / 2) / 10 ≤ (rtlMM cκ Q i : ℝ)) :
    (4*C₀+1) * Real.exp (-(cκ * (Q i : ℝ) / 2)) + 4 * C₀ / (rtlMM cκ Q i : ℝ)
      + 4 * (2 * (4*C₀+1) * Real.exp (-(cκ * (Q i : ℝ) / 2)))
      ≤ (76*C₀+9) * Real.exp (-(cκ * (Q i : ℝ) / 2)) := by
  set E := Real.exp (-(cκ * (Q i : ℝ) / 2)) with hE
  have hMpos : 0 < (rtlMM cκ Q i : ℝ) := lt_of_lt_of_le (by positivity) hge
  have hEinv : E = (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ := by
    rw [hE, Real.exp_neg]
  have hMinv : 1 / (rtlMM cκ Q i : ℝ) ≤ 10 * E := by
    rw [hEinv, div_le_iff₀ hMpos]
    have hApos : 0 < Real.exp (cκ * (Q i : ℝ) / 2) := Real.exp_pos _
    have h1 : 10 * (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ * (Real.exp (cκ * (Q i : ℝ) / 2)/10)
        ≤ 10 * (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ * (rtlMM cκ Q i : ℝ) :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    have h2 : 10 * (Real.exp (cκ * (Q i : ℝ) / 2))⁻¹ * (Real.exp (cκ * (Q i : ℝ) / 2)/10) = 1 := by
      field_simp
    linarith [h1, h2]
  have h1 : 4 * C₀ / (rtlMM cκ Q i : ℝ) ≤ 40 * C₀ * E := by
    have h4 : (0:ℝ) ≤ 4*C₀ := by linarith
    calc 4 * C₀ / (rtlMM cκ Q i : ℝ) = 4*C₀ * (1/(rtlMM cκ Q i : ℝ)) := by rw [mul_one_div]
      _ ≤ 4*C₀ * (10*E) := mul_le_mul_of_nonneg_left hMinv h4
      _ = 40*C₀*E := by ring
  nlinarith [h1]


theorem rtl_sum_eps_le (A cκ b C₀ : ℝ) (Q : ℕ → ℕ) (k N₀ Sb S : ℕ)
    (hcκ : 0 < cκ) (hb : 0 < b) (hC₀ : 0 ≤ C₀)
    (hQ1 : ∀ i ≤ k, 1 ≤ Q i)
    (hmono : ∀ i < k, Q i < Q (i+1))
    (hgrowth : ∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ)))
    (hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ))
    (hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4)
    (hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)))
    (hSb : 4 * b / cκ < Sb)
    (hS : ∀ t < S, Work.TMComp.C7Aux.rtli A cκ Q k N₀ t < k) :
    (∑ t ∈ Finset.range S,
        ((4*C₀+1) * Real.exp (-(cκ * (Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ) / 2))
          + 4 * C₀ / (Work.TMComp.C7Aux.rtlMM cκ Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ)
          + 4 * (2 * (4*C₀+1) * Real.exp (-(cκ * (Q (Work.TMComp.C7Aux.rtli A cκ Q k N₀ t) : ℝ) / 2)))))
      ≤ (Sb+1) * (76*C₀+9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) / (1 - Real.exp (-(cκ/2))) := by
  classical
  have hKnn : 0 ≤ 76*C₀+9 := by linarith
  have h1mr_exp : 0 < 1 - Real.exp (-(cκ/2)) := by
    have := Real.exp_lt_one_iff.mpr (show -(cκ/2) < 0 by linarith)
    linarith
  by_cases hA : 0 < A
  · set r := Real.exp (-(cκ/2)) with hr
    have hrpos : 0 < r := Real.exp_pos _
    have hrlt1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
    have h1mr : 0 < 1 - r := by linarith
    set e : ℕ → ℝ := fun i => Real.exp (-(cκ * (Q i : ℝ) / 2)) with hedef
    have hepos : ∀ i, 0 < e i := fun i => Real.exp_pos _
    have henn : ∀ i, 0 ≤ e i := fun i => (hepos i).le
    have hei : ∀ i, e i = r ^ (Q i) := by
      intro i
      simp only [hedef]
      rw [hr]
      rw [show -(cκ * (Q i : ℝ)/2) = (Q i : ℝ) * (-(cκ/2)) by ring]
      rw [Real.exp_nat_mul]
    have hmonoQ : ∀ i ≤ k, Q 0 + i ≤ Q i := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have hik : i < k := by omega
        have hh := ih (by omega)
        have h2 := hmono i hik
        omega
    have hgeob : ∑ i ∈ Finset.range k, e i ≤ e 0 / (1 - r) := by
      have hstep : ∑ i ∈ Finset.range k, e i ≤ ∑ i ∈ Finset.range k, r ^ (Q 0 + i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hei i]
        have hik : i ≤ k := le_of_lt (Finset.mem_range.mp hi)
        exact pow_le_pow_of_le_one hrpos.le hrlt1.le (hmonoQ i hik)
      have hsplit : ∑ i ∈ Finset.range k, r ^ (Q 0 + i)
          = r ^ (Q 0) * ∑ i ∈ Finset.range k, r ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_add]
      have hgeo2 : ∑ i ∈ Finset.range k, r ^ i ≤ (1 - r)⁻¹ := by
        have hs := (summable_geometric_of_lt_one hrpos.le hrlt1).sum_le_tsum (Finset.range k)
          (fun i _ => pow_nonneg hrpos.le i)
        rwa [tsum_geometric_of_lt_one hrpos.le hrlt1] at hs
      calc ∑ i ∈ Finset.range k, e i
          ≤ ∑ i ∈ Finset.range k, r ^ (Q 0 + i) := hstep
        _ = r ^ (Q 0) * ∑ i ∈ Finset.range k, r ^ i := hsplit
        _ ≤ r ^ (Q 0) * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeo2 (pow_nonneg hrpos.le _)
        _ = e 0 / (1 - r) := by rw [hei 0, div_eq_mul_inv]
    have hfiber : ∑ t ∈ Finset.range S, e (rtli A cκ Q k N₀ t)
        ≤ (Sb:ℝ) * ∑ i ∈ Finset.range k, e i := by
      have hcomp := Finset.sum_comp (s := Finset.range S) (f := e)
        (g := fun t => rtli A cκ Q k N₀ t)
      have hcomp' : (∑ t ∈ Finset.range S, e (rtli A cκ Q k N₀ t))
          = ∑ j ∈ Finset.image (fun t => rtli A cκ Q k N₀ t) (Finset.range S),
              (Finset.filter (fun t => rtli A cκ Q k N₀ t = j) (Finset.range S)).card • e j := by
        simpa using hcomp
      rw [hcomp']
      calc ∑ j ∈ Finset.image (fun t => rtli A cκ Q k N₀ t) (Finset.range S),
              (Finset.filter (fun t => rtli A cκ Q k N₀ t = j) (Finset.range S)).card • e j
          ≤ ∑ j ∈ Finset.image (fun t => rtli A cκ Q k N₀ t) (Finset.range S), (Sb:ℝ) * e j := by
            apply Finset.sum_le_sum
            intro j hbmem
            have hbk : j < k := by
              rw [Finset.mem_image] at hbmem
              obtain ⟨t, ht, rfl⟩ := hbmem
              exact hS t (Finset.mem_range.mp ht)
            have hcard : (Finset.filter (fun t => rtli A cκ Q k N₀ t = j) (Finset.range S)).card ≤ Sb :=
              rtl_fiber_card_le A cκ b Q k N₀ Sb hA hcκ hb hQ1 hmono hgrowth hA0 hbig hbig2 hSb hbk S
            have hcard' : ((Finset.filter (fun t => rtli A cκ Q k N₀ t = j) (Finset.range S)).card : ℝ) ≤ (Sb:ℝ) := by
              exact_mod_cast hcard
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right hcard' (henn j)
        _ = (Sb:ℝ) * ∑ j ∈ Finset.image (fun t => rtli A cκ Q k N₀ t) (Finset.range S), e j :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (Sb:ℝ) * ∑ i ∈ Finset.range k, e i := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Sb)
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hbmem
              rw [Finset.mem_range]
              rw [Finset.mem_image] at hbmem
              obtain ⟨t, ht, rfl⟩ := hbmem
              exact hS t (Finset.mem_range.mp ht)
            · intro j _ _; exact henn j
    have hsum1 : (∑ t ∈ Finset.range S,
        ((4*C₀+1) * Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ t) : ℝ) / 2))
          + 4 * C₀ / (rtlMM cκ Q (rtli A cκ Q k N₀ t) : ℝ)
          + 4 * (2 * (4*C₀+1) * Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ t) : ℝ) / 2)))))
        ≤ (76*C₀+9) * ∑ t ∈ Finset.range S, e (rtli A cκ Q k N₀ t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have hik : rtli A cκ Q k N₀ t < k := hS t (Finset.mem_range.mp ht)
      have hge := rtlMM_ge cκ Q (rtli A cκ Q k N₀ t) (hbig2 _ (le_of_lt hik))
      have hpt := rtl_term_le cκ C₀ Q (rtli A cκ Q k N₀ t) hC₀ hge
      simpa [hedef] using hpt
    calc (∑ t ∈ Finset.range S,
        ((4*C₀+1) * Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ t) : ℝ) / 2))
          + 4 * C₀ / (rtlMM cκ Q (rtli A cκ Q k N₀ t) : ℝ)
          + 4 * (2 * (4*C₀+1) * Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ t) : ℝ) / 2)))))
        ≤ (76*C₀+9) * ∑ t ∈ Finset.range S, e (rtli A cκ Q k N₀ t) := hsum1
      _ ≤ (76*C₀+9) * ((Sb:ℝ) * ∑ i ∈ Finset.range k, e i) :=
            mul_le_mul_of_nonneg_left hfiber hKnn
      _ ≤ (76*C₀+9) * ((Sb:ℝ) * (e 0 / (1 - r))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeob (Nat.cast_nonneg Sb)) hKnn
      _ ≤ ((Sb:ℝ)+1) * (76*C₀+9) * (e 0 / (1 - r)) := by
            have hXnn : 0 ≤ e 0 / (1 - r) := div_nonneg (henn 0) (le_of_lt h1mr)
            have h2 := mul_le_mul_of_nonneg_right (show (Sb:ℝ) ≤ (Sb:ℝ)+1 by linarith)
              (mul_nonneg hKnn hXnn)
            rw [div_eq_mul_inv] at h2 ⊢
            nlinarith [h2]
      _ = (Sb+1) * (76*C₀+9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) / (1 - Real.exp (-(cκ/2))) := by
            have he0 : e 0 = Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by simp [hedef]
            rw [he0, hr, div_eq_mul_inv]
            ring
  · have hAle : A ≤ 0 := le_of_not_gt hA
    have hrtli0 : rtli A cκ Q k N₀ 0 = k := by
      rw [rtli_eq_idx]
      unfold rtlIdx
      have hPk : A * (Q k : ℝ) ≤ (N₀ : ℝ) := by
        have h1 : A * (Q k : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAle (Nat.cast_nonneg _)
        have h2 : (0:ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
        linarith
      exact le_antisymm (Nat.findGreatest_le k) (Nat.le_findGreatest (le_refl k) hPk)
    have hS0 : S = 0 := by
      by_contra hSne
      have h0 : 0 < S := Nat.pos_of_ne_zero hSne
      have := hS 0 h0
      rw [hrtli0] at this
      exact lt_irrefl k this
    rw [hS0]
    simp only [Finset.range_zero, Finset.sum_empty]
    apply div_nonneg
    · have h1 : (0:ℝ) ≤ (Sb:ℝ)+1 := by positivity
      exact mul_nonneg (mul_nonneg h1 hKnn) (Real.exp_pos _).le
    · exact le_of_lt h1mr_exp

end Work.TMComp.C7Aux

import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6.TauPieces.ZcontDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse
import Submission.Work.FIArea5.S16Hecke.heckeLam_pow_bound
import Submission.Work.FIArea5.S16Hecke.summable_heckeLam_pow_mul

open scoped BigOperators

namespace Work.FIArea6Road

noncomputable section


lemma summable_primes_rpow_neg {r : ℝ} (hr : 1 < r) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-r)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-r)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact hbase.subtype (fun n : ℕ => n.Prime)

lemma tprod_one_add_le_exp_tsum {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) : ∏' i, (1 + a i) ≤ Real.exp (∑' i, a i) := by
  have hpos : ∀ i, 0 < 1 + a i := fun i => by linarith [ha i]
  have hlog : Summable (fun i => Real.log (1 + a i)) :=
    Summable.of_nonneg_of_le (fun i => Real.log_nonneg (by linarith [ha i]))
      (fun i => by have h := Real.log_le_sub_one_of_pos (hpos i); linarith) hs
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_le_exp.mpr (Summable.tsum_le_tsum (fun i => by
    have h := Real.log_le_sub_one_of_pos (hpos i); linarith) hlog hs)



lemma LocalFactorBound (chi : GaussianInt → ℂ) (m : ℤ) (p : ℕ) (hp : p.Prime)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
        + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
            - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) ≠ 0 ∧
      ‖(1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z)
          / (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
              + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
                  - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) - 1‖
        ≤ 4 * ‖z‖ ^ 2 / (1 - ‖z‖) ^ 2 := by
  have hinv := Work.FIArea5.S16Hecke.heckeLam_localInverse (chi := chi) (k := m) (p := p)
    hp hchimul hchi1 hchibd hz
  have hcbd := (Work.FIArea5.S16Hecke.heckeLam_localRec chi m p hp hchimul hchibd).2
  set S : ℂ := ∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam chi m (p ^ e) * z ^ e with hSdef
  have hSL : S * (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
      + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) = 1 := hinv
  have hLne : (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
      + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hSL; exact one_ne_zero hSL.symm
  have hSin : S = (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
      + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left hSL
  have hSbound : ‖S‖ ≤ 4 / (1 - ‖z‖) ^ 2 := by
    have hsum := Work.FIArea5.S16Hecke.summable_heckeLam_pow_mul (chi := chi) (k := m) (p := p)
      hp hchibd hz
    have hnormsum : Summable (fun e : ℕ => ‖Work.FIArea5.S16Hecke.heckeLam chi m (p ^ e) * z ^ e‖) :=
      hsum.norm
    have hrz : ‖(‖z‖ : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]; exact hz
    have hcmp : Summable (fun e : ℕ => 4 * ((e : ℝ) + 1) * ‖z‖ ^ e) := by
      have h := Work.FIArea5.S16Hecke.summable_nat_succ_mul_geo (r := ‖z‖) hrz
      simpa [mul_assoc] using h.mul_left 4
    have hbound : ∑' e : ℕ, ((e : ℝ) + 1) * ‖z‖ ^ e = 1 / (1 - ‖z‖) ^ 2 := by
      have hr1 : (1 : ℝ) - ‖z‖ ≠ 0 := by have := hz; linarith
      have hA : Summable (fun e : ℕ => (e : ℝ) * ‖z‖ ^ e) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖z‖) hrz
      have hB : Summable (fun e : ℕ => ‖z‖ ^ e) := summable_geometric_of_norm_lt_one hrz
      rw [show (fun e : ℕ => ((e : ℝ) + 1) * ‖z‖ ^ e)
            = (fun e : ℕ => (e : ℝ) * ‖z‖ ^ e + ‖z‖ ^ e) from by funext e; ring]
      rw [Summable.tsum_add hA hB, tsum_coe_mul_geometric_of_norm_lt_one hrz,
        tsum_geometric_of_norm_lt_one hrz]
      field_simp
      ring
    calc ‖S‖ ≤ ∑' e : ℕ, ‖Work.FIArea5.S16Hecke.heckeLam chi m (p ^ e) * z ^ e‖ :=
          norm_tsum_le_tsum_norm hnormsum
      _ ≤ ∑' e : ℕ, 4 * ((e : ℝ) + 1) * ‖z‖ ^ e := by
          refine Summable.tsum_le_tsum (fun e => ?_) hnormsum hcmp
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_right (Work.FIArea5.S16Hecke.heckeLam_pow_bound hp hchibd e)
            (by positivity)
      _ = 4 * ∑' e : ℕ, ((e : ℝ) + 1) * ‖z‖ ^ e := by
          rw [← tsum_mul_left]
          exact tsum_congr (fun e => by ring)
      _ = 4 * (1 / (1 - ‖z‖) ^ 2) := by rw [hbound]
      _ = 4 / (1 - ‖z‖) ^ 2 := by ring
  refine ⟨hLne, ?_⟩
  have hsub : (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z)
      - (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
          + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
              - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2)
      = -(((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
              - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) := by ring
  have hkey : (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z)
      / (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * z
          + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
              - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) - 1
      = -(((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
              - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) * S := by
    rw [div_sub_one hLne, hsub, hSin, div_eq_mul_inv]
  rw [hkey]
  have hfin : ‖-(((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
            - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * z ^ 2) * S‖
      = ‖(Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
            - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)‖ * ‖z‖ ^ 2 * ‖S‖ := by
    simp only [norm_mul, norm_neg, norm_pow]
  rw [hfin]
  have h1 : ‖Work.FIArea5.S16Hecke.heckeLam chi m p ^ 2
        - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)‖ * ‖S‖
      ≤ 1 * (4 / (1 - ‖z‖) ^ 2) :=
    mul_le_mul hcbd hSbound (norm_nonneg S) (by norm_num)
  calc ‖Work.FIArea5.S16Hecke.heckeLam chi m p ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)‖ * ‖z‖ ^ 2 * ‖S‖
      = (‖Work.FIArea5.S16Hecke.heckeLam chi m p ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)‖ * ‖S‖) * ‖z‖ ^ 2 := by ring
    _ ≤ (1 * (4 / (1 - ‖z‖) ^ 2)) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 4 * ‖z‖ ^ 2 / (1 - ‖z‖) ^ 2 := by ring

lemma DiffLocalFactor (chi : GaussianInt → ℂ) (m : ℤ) (p : ℕ) (hp : p.Prime)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    DifferentiableOn ℂ
      (fun s : ℂ => (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * ((p : ℂ) ^ (-s)))
        / Work.FIArea6.TauPieces.localL chi m p s)
      {s : ℂ | 1 / 2 < s.re} := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : DifferentiableOn ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) U := by
    have h1 : DifferentiableOn ℂ (fun s : ℂ => -s) U := by fun_prop
    exact DifferentiableOn.const_cpow h1 (Or.inl hp0)
  have hnum : DifferentiableOn ℂ
      (fun s : ℂ => 1 - Work.FIArea5.S16Hecke.heckeLam chi m p * ((p : ℂ) ^ (-s))) U :=
    (differentiableOn_const (c := (1 : ℂ))).sub
      ((differentiableOn_const (c := Work.FIArea5.S16Hecke.heckeLam chi m p)).mul hpow)
  have hden : DifferentiableOn ℂ (fun s : ℂ => Work.FIArea6.TauPieces.localL chi m p s) U := by
    unfold Work.FIArea6.TauPieces.localL
    exact ((differentiableOn_const (c := (1 : ℂ))).sub
      ((differentiableOn_const (c := Work.FIArea5.S16Hecke.heckeLam chi m p)).mul hpow)).add
      ((differentiableOn_const (c := (Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2))).mul (hpow.pow 2))
  have hne : ∀ s ∈ U, Work.FIArea6.TauPieces.localL chi m p s ≠ 0 := by
    intro s hs
    have hsre : 1 / 2 < s.re := hs
    have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re,
        Real.rpow_neg (by positivity : (0:ℝ) ≤ (p:ℝ))]
      exact inv_lt_one_of_one_lt₀
        (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith))
    exact (LocalFactorBound chi m p hp hchi1 hchimul hchibd hnorm).1
  exact hnum.div hden hne




def ufac (chi : GaussianInt → ℂ) (m : ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  Work.FIArea6.TauPieces.PhiLocal chi m s (p : ℕ) - 1

theorem PhifacAnalyticBound (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    AnalyticOn ℂ (fun s : ℂ => Work.FIArea6.TauPieces.Phifac chi m s) {s : ℂ | 1 / 2 < s.re} ∧
      ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 3 / 4 ≤ s.re →
        ‖Work.FIArea6.TauPieces.Phifac chi m s‖ ≤ K := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hPhifac : ∀ s : ℂ, Work.FIArea6.TauPieces.Phifac chi m s
      = ∏' p : Nat.Primes, (1 + ufac chi m p s) := by
    intro s
    rw [Work.FIArea6.TauPieces.Phifac_eq_tprod_PhiLocal]
    exact tprod_congr (fun p => by simp only [ufac]; ring)
  have hfactor : ∀ p : Nat.Primes, DifferentiableOn ℂ (fun s : ℂ => 1 + ufac chi m p s) U := by
    intro p
    refine (DiffLocalFactor chi m (p : ℕ) p.2 hchi1 hchimul hchibd).congr ?_
    intro s hs
    simp only [ufac, Work.FIArea6.TauPieces.PhiLocal, Work.FIArea6.TauPieces.localL]
    ring
  have hLU : HasProdLocallyUniformlyOn (fun p : Nat.Primes => fun s : ℂ => 1 + ufac chi m p s)
      (fun s : ℂ => ∏' p : Nat.Primes, (1 + ufac chi m p s)) U := by
    apply hasProdLocallyUniformlyOn_of_forall_compact hUopen
    intro K hKU hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact Summable.hasProdUniformlyOn_one_add (f := fun (p : Nat.Primes) (s : ℂ) => ufac chi m p s)
        (K := (∅ : Set ℂ)) isCompact_empty (u := fun _ : Nat.Primes => (0 : ℝ))
        (by simp) (by simp) (fun p => by simp)
    · obtain ⟨x0, hx0K, hx0min⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
      have hx0gt : 1 / 2 < x0.re := hKU hx0K
      have hc : (0:ℝ) < (2:ℝ) ^ (-x0.re) := Real.rpow_pos_of_pos (by norm_num) _
      have hclt : (2:ℝ) ^ (-x0.re) < 1 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
      have hsum0 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * x0.re))) :=
        summable_primes_rpow_neg (by linarith)
      refine Summable.hasProdUniformlyOn_one_add
        (f := fun (p : Nat.Primes) (s : ℂ) => ufac chi m p s)
        (u := fun p : Nat.Primes => (4 / (1 - (2:ℝ)^(-x0.re))^2)
          * (((p : ℕ) : ℝ) ^ (-(2 * x0.re)))) hK (hsum0.mul_left _) ?_ ?_
      · refine Filter.Eventually.of_forall (fun p x hx => ?_)
        have hx0min' : ∀ y ∈ K, x0.re ≤ y.re := by
          rw [IsMinOn, IsMinFilter, Filter.eventually_principal] at hx0min
          exact hx0min
        have hxre : x0.re ≤ x.re := hx0min' x hx
        have hp1 : (1:ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.2).one_le
        have hp2 : (2:ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.2).two_le
        have hppos : (0:ℝ) < (p : ℕ) := by linarith
        have hnorm : ‖((p : ℕ) : ℂ) ^ (-x)‖ = ((p : ℕ) : ℝ) ^ (-x.re) := by
          rw [Complex.norm_natCast_cpow_of_pos (by exact (p.2).pos), Complex.neg_re]
        have hTle0 : ((p : ℕ) : ℝ) ^ (-x.re) ≤ ((p : ℕ) : ℝ) ^ (-x0.re) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        have hTle : ((p : ℕ) : ℝ) ^ (-x.re) ≤ (2:ℝ) ^ (-x0.re) :=
          hTle0.trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith))
        have hz : ‖((p : ℕ) : ℂ) ^ (-x)‖ < 1 := by
          rw [hnorm]; exact lt_of_le_of_lt hTle hclt
        have hLFB := (LocalFactorBound chi m (p : ℕ) p.2 hchi1 hchimul hchibd hz).2
        have hu : ‖ufac chi m p x‖
            ≤ 4 * (((p : ℕ) : ℝ) ^ (-x.re))^2 / (1 - ((p : ℕ) : ℝ) ^ (-x.re))^2 := by
          simpa only [ufac, Work.FIArea6.TauPieces.PhiLocal, Work.FIArea6.TauPieces.localL,
            hnorm] using hLFB
        have hTnn : (0:ℝ) ≤ ((p : ℕ) : ℝ) ^ (-x.re) := Real.rpow_nonneg (by positivity) _
        have hT2 : (((p : ℕ) : ℝ) ^ (-x.re))^2 ≤ ((p : ℕ) : ℝ) ^ (-(2 * x0.re)) := by
          have h1 : (((p : ℕ) : ℝ) ^ (-x.re))^2 ≤ (((p : ℕ) : ℝ) ^ (-x0.re))^2 :=
            pow_le_pow_left₀ hTnn hTle0 2
          have h2 : (((p : ℕ) : ℝ) ^ (-x0.re))^2 = ((p : ℕ) : ℝ) ^ (-(2 * x0.re)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p : ℕ))]
            congr 1
            ring
          rwa [h2] at h1
        have hδpos : 0 < 1 - (2:ℝ)^(-x0.re) := by linarith
        have hden : (1 - (2:ℝ)^(-x0.re))^2 ≤ (1 - ((p : ℕ) : ℝ) ^ (-x.re))^2 :=
          pow_le_pow_left₀ (le_of_lt hδpos) (by linarith) 2
        have hnumc : (0:ℝ) ≤ 4 * ((p : ℕ) : ℝ) ^ (-(2 * x0.re)) := by positivity
        calc ‖ufac chi m p x‖
            ≤ 4 * (((p : ℕ) : ℝ) ^ (-x.re))^2 / (1 - ((p : ℕ) : ℝ) ^ (-x.re))^2 := hu
          _ ≤ 4 * ((p : ℕ) : ℝ) ^ (-(2 * x0.re)) / (1 - (2:ℝ)^(-x0.re))^2 :=
              div_le_div₀ hnumc (by linarith [hT2]) (pow_pos hδpos 2) hden
          _ = (4 / (1 - (2:ℝ)^(-x0.re))^2) * (((p : ℕ) : ℝ) ^ (-(2 * x0.re))) := by ring
      · intro p
        have hd : DifferentiableOn ℂ (fun s : ℂ => 1 + ufac chi m p s) K := (hfactor p).mono hKU
        refine ((hd.sub (differentiableOn_const (c := (1:ℂ)))).congr ?_).continuousOn
        intro s hs
        simp only [ufac, Pi.sub_apply]
        ring
  have hAnal : AnalyticOn ℂ (fun s : ℂ => ∏' p : Nat.Primes, (1 + ufac chi m p s)) U := by
    have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∏' p : Nat.Primes, (1 + ufac chi m p s)) U :=
      (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hLU).differentiableOn
        (Filter.Eventually.of_forall (fun S : Finset Nat.Primes =>
          (DifferentiableOn.finsetProd (u := S)
            (f := fun i : Nat.Primes => fun x : ℂ => 1 + ufac chi m i x)
            (fun i _ => hfactor i)).congr (fun x _ => by
              simp only [Finset.prod_apply]))) hUopen
    exact hdiff.analyticOn hUopen
  set δ : ℝ := 1 - (2:ℝ)^(-(3/4:ℝ)) with hδ
  set S0 : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) with hS0def
  have hδpos : 0 < δ := by
    rw [hδ]
    have h : (2:ℝ)^(-(3/4:ℝ)) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
    linarith
  have hpow34 : (2:ℝ)^(-(3/4:ℝ)) = 1 - δ := by rw [hδ]; ring
  refine ⟨?_, ?_⟩
  · have h := hAnal.congr (fun s hs => hPhifac s)
    rwa [hU] at h
  · refine ⟨Real.exp ((4 / δ^2) * S0), Real.exp_pos _, ?_⟩
    intro s hs
    rw [hPhifac s]
    have hu_bound : ∀ p : Nat.Primes, ‖ufac chi m p s‖
        ≤ (4 / δ^2) * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
      intro p
      have hp1 : (1:ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.2).one_le
      have hp2 : (2:ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.2).two_le
      have hppos : (0:ℝ) < (p : ℕ) := by linarith
      have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
        rw [Complex.norm_natCast_cpow_of_pos (by exact (p.2).pos), Complex.neg_re]
      have hTle : ((p : ℕ) : ℝ) ^ (-s.re) ≤ (2:ℝ)^(-(3/4:ℝ)) :=
        (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)).trans
          (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num))
      have hz : ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
        rw [hnorm]
        rw [hpow34] at hTle
        linarith [hδpos]
      have hLFB := (LocalFactorBound chi m (p : ℕ) p.2 hchi1 hchimul hchibd hz).2
      have hu : ‖ufac chi m p s‖
          ≤ 4 * (((p : ℕ) : ℝ) ^ (-s.re))^2 / (1 - ((p : ℕ) : ℝ) ^ (-s.re))^2 := by
        simpa only [ufac, Work.FIArea6.TauPieces.PhiLocal, Work.FIArea6.TauPieces.localL,
          hnorm] using hLFB
      have hTnn : (0:ℝ) ≤ ((p : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
      have hT2 : (((p : ℕ) : ℝ) ^ (-s.re))^2 ≤ ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
        have h1 : (((p : ℕ) : ℝ) ^ (-s.re))^2 ≤ (((p : ℕ) : ℝ) ^ (-(3/4:ℝ)))^2 :=
          pow_le_pow_left₀ hTnn (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)) 2
        have h2 : (((p : ℕ) : ℝ) ^ (-(3/4:ℝ)))^2 = ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (p : ℕ))]
          congr 1
          ring
        rwa [h2] at h1
      have hden : δ^2 ≤ (1 - ((p : ℕ) : ℝ) ^ (-s.re))^2 := by
        have h1 : δ ≤ 1 - ((p : ℕ) : ℝ) ^ (-s.re) := by
          rw [hpow34] at hTle
          linarith
        exact pow_le_pow_left₀ (le_of_lt hδpos) h1 2
      have hnumc : (0:ℝ) ≤ 4 * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by positivity
      calc ‖ufac chi m p s‖
          ≤ 4 * (((p : ℕ) : ℝ) ^ (-s.re))^2 / (1 - ((p : ℕ) : ℝ) ^ (-s.re))^2 := hu
        _ ≤ 4 * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) / δ^2 :=
            div_le_div₀ hnumc (by linarith [hT2]) (pow_pos hδpos 2) hden
        _ = (4 / δ^2) * ((p : ℕ) : ℝ) ^ (-(3/2:ℝ)) := by ring
    have hsumu : Summable (fun p : Nat.Primes => ‖ufac chi m p s‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _) hu_bound
        ((summable_primes_rpow_neg (show (1:ℝ) < 3/2 by norm_num)).mul_left (4 / δ^2))
    have htsum : (∑' p : Nat.Primes, ‖ufac chi m p s‖) ≤ (4 / δ^2) * S0 := by
      have h := Summable.tsum_le_tsum hu_bound hsumu
        ((summable_primes_rpow_neg (show (1:ℝ) < 3/2 by norm_num)).mul_left (4 / δ^2))
      rw [tsum_mul_left] at h
      rw [hS0def]
      exact h
    have hm : Multipliable (fun p : Nat.Primes => 1 + ufac chi m p s) :=
      multipliable_one_add_of_summable hsumu
    rw [hm.norm_tprod]
    exact hasProd_le_of_prod_le hm.norm.hasProd (fun S => by
      calc ∏ p ∈ S, ‖1 + ufac chi m p s‖
          ≤ ∏ p ∈ S, (1 + ‖ufac chi m p s‖) :=
            Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
              (fun p _ => by simpa using norm_add_le (1:ℂ) (ufac chi m p s))
        _ ≤ Real.exp (∑ p ∈ S, ‖ufac chi m p s‖) :=
            Real.prod_one_add_le_exp_sum S (fun p => norm_nonneg _)
        _ ≤ Real.exp (∑' p : Nat.Primes, ‖ufac chi m p s‖) :=
            Real.exp_le_exp.mpr (Summable.sum_le_tsum S (fun p _ => norm_nonneg _) hsumu)
        _ ≤ Real.exp ((4 / δ^2) * S0) := Real.exp_le_exp.mpr htsum)

end
end Work.FIArea6Road

import Mathlib
import Submission.Commons.Analysis.ExponentialSums.weyl_ineq_two
import Submission.Commons.Analysis.ExponentialSums.intDist_abs_sub_le
import Submission.Commons.Analysis.ExponentialSums.card_small_intDist_residues
import Submission.Commons.Analysis.ExponentialSums.card_filter_mod_eq_le
import Submission.Commons.Analysis.ExponentialSums.min_le_one_add_card_div
import Submission.Commons.Analysis.Series.harmonic_sum_le_rpow

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators Real Topology

set_option maxHeartbeats 1600000

/-! ### Helper lemmas on `intDist` -/

/-- `intDist` is invariant under translation by an integer. -/
private lemma intDist_add_intCast (x : ℝ) (n : ℤ) :
    Submission.VanDerCorput.intDist (x + (n : ℝ)) = Submission.VanDerCorput.intDist x := by
  simp only [Submission.VanDerCorput.intDist, Int.fract_add_intCast]

/-- `intDist` is invariant under adding `2 a j` with `a : ℤ`, `j : ℕ`. -/
private lemma intDist_add_two_mul (x : ℝ) (a : ℤ) (j : ℕ) :
    Submission.VanDerCorput.intDist (x + 2 * (a : ℝ) * (j : ℝ)) =
      Submission.VanDerCorput.intDist x := by
  have hcast : 2 * (a : ℝ) * (j : ℝ) = ((2 * a * (j : ℤ) : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [hcast, intDist_add_intCast]

/-- One-sided Lipschitz bound: `intDist x ≤ intDist y + |x - y|`. -/
private lemma intDist_le_intDist_add_abs (x y : ℝ) :
    Submission.VanDerCorput.intDist x ≤ Submission.VanDerCorput.intDist y + |x - y| := by
  have h := Commons.Analysis.ExponentialSums.intDist_abs_sub_le x y
  have h2 : Submission.VanDerCorput.intDist x - Submission.VanDerCorput.intDist y ≤ |x - y| :=
    le_trans (le_abs_self _) h
  linarith

/-- Transfer of the small-`intDist` condition to the residue class mod `q`. -/
private lemma intDist_mod_le {M : ℕ} (hM : 1 ≤ M) {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (hβ : |β - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (M : ℝ))) {h : ℕ} (hh : h ≤ M) {ε : ℝ}
    (hε : Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ ε) :
    Submission.VanDerCorput.intDist (2 * (a : ℝ) * ((h % q : ℕ) : ℝ) / (q : ℝ))
      ≤ ε + 2 / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hhR : (h : ℝ) ≤ (M : ℝ) := by exact_mod_cast hh
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by positivity
  -- decomposition `h = q * (h / q) + h % q`
  have hdecomp : (h : ℝ) = (q : ℝ) * ((h / q : ℕ) : ℝ) + ((h % q : ℕ) : ℝ) := by
    have h' := Nat.div_add_mod h q
    calc (h : ℝ) = ((q * (h / q) + h % q : ℕ) : ℝ) := by rw [h']
      _ = (q : ℝ) * ((h / q : ℕ) : ℝ) + ((h % q : ℕ) : ℝ) := by push_cast; ring
  have hmm : ((h % q : ℕ) : ℝ) = (h : ℝ) - (q : ℝ) * ((h / q : ℕ) : ℝ) := by linarith
  -- `2 a (h % q) / q + 2 a (h / q) = 2 a h / q`
  have hkey : 2 * (a : ℝ) * ((h % q : ℕ) : ℝ) / (q : ℝ) + 2 * (a : ℝ) * ((h / q : ℕ) : ℝ)
      = 2 * (a : ℝ) * (h : ℝ) / (q : ℝ) := by
    rw [hmm]
    field_simp
    ring
  -- difference bound
  have hdiff : |2 * (a : ℝ) * (h : ℝ) / (q : ℝ) - 2 * β * (h : ℝ)| ≤ 2 / (q : ℝ) := by
    have hrw : 2 * (a : ℝ) * (h : ℝ) / (q : ℝ) - 2 * β * (h : ℝ)
        = (2 * (h : ℝ)) * ((a : ℝ) / (q : ℝ) - β) := by ring
    have hb : |(a : ℝ) / (q : ℝ) - β| ≤ 1 / ((q : ℝ) * (M : ℝ)) := by
      rw [abs_sub_comm]
      exact hβ
    rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (h:ℝ))]
    have hstep : 2 * (h : ℝ) * |(a : ℝ) / (q : ℝ) - β|
        ≤ 2 * (h : ℝ) * (1 / ((q : ℝ) * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    refine le_trans hstep ?_
    rw [show 2 * (h : ℝ) * (1 / ((q : ℝ) * (M : ℝ))) = 2 * (h : ℝ) / ((q : ℝ) * (M : ℝ)) by ring]
    rw [div_le_div_iff₀ (by positivity) hqR]
    nlinarith [hhR, hMR]
  have hstep1 : Submission.VanDerCorput.intDist (2 * (a : ℝ) * (h : ℝ) / (q : ℝ))
      = Submission.VanDerCorput.intDist (2 * (a : ℝ) * ((h % q : ℕ) : ℝ) / (q : ℝ)) := by
    rw [← hkey, intDist_add_two_mul]
  calc Submission.VanDerCorput.intDist (2 * (a : ℝ) * ((h % q : ℕ) : ℝ) / (q : ℝ))
      = Submission.VanDerCorput.intDist (2 * (a : ℝ) * (h : ℝ) / (q : ℝ)) := hstep1.symm
    _ ≤ Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) + |2 * (a : ℝ) * (h : ℝ) / (q : ℝ) - 2 * β * (h : ℝ)| :=
        intDist_le_intDist_add_abs _ _
    _ ≤ ε + 2 / (q : ℝ) := by linarith [hdiff, hε]

/-! ### The counting lemma -/

/-- Count of `h ∈ [1,M]` with `intDist (2βh) ≤ ε`, when `β` is within `1/(qM)` of the
reduced fraction `a/q`. -/
private lemma count_intDist_le {M : ℕ} (hM : 1 ≤ M) {β : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (hgcd : Int.gcd a (q : ℤ) = 1)
    (hβ : ‖β - (a : ℝ) / (q : ℝ)‖ ≤ 1 / ((q : ℝ) * (M : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ((Finset.filter (fun h : ℕ => Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ ε)
        (Finset.Icc 1 M)).card : ℝ)
      ≤ (4 * (q : ℝ) * ε + 14) * ((M : ℝ) / (q : ℝ) + 1) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hβ' : |β - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (M : ℝ)) := by
    rw [← Real.norm_eq_abs]; exact hβ
  set S : Finset ℕ := Finset.filter (fun h : ℕ =>
    Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ ε) (Finset.Icc 1 M) with hSdef
  set R : Finset ℕ := Finset.filter (fun r : ℕ =>
    Submission.VanDerCorput.intDist (2 * (a : ℝ) * (r : ℝ) / (q : ℝ)) ≤ ε + 2 / (q : ℝ))
    (Finset.range q) with hRdef
  set R' : Finset ℕ := Finset.filter (fun r : ℕ =>
    Submission.VanDerCorput.intDist (2 * (r : ℝ) / (q : ℝ)) ≤ ε + 2 / (q : ℝ))
    (Finset.range q) with hR'def
  have memS : ∀ h : ℕ, h ∈ S ↔
      h ∈ Finset.Icc 1 M ∧ Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ ε := by
    intro h; rw [hSdef, Finset.mem_filter]
  have memR : ∀ r : ℕ, r ∈ R ↔
      r < q ∧ Submission.VanDerCorput.intDist (2 * (a : ℝ) * (r : ℝ) / (q : ℝ)) ≤ ε + 2 / (q : ℝ) := by
    intro r; rw [hRdef, Finset.mem_filter, Finset.mem_range]
  have memR' : ∀ r : ℕ, r ∈ R' ↔
      r < q ∧ Submission.VanDerCorput.intDist (2 * (r : ℝ) / (q : ℝ)) ≤ ε + 2 / (q : ℝ) := by
    intro r; rw [hR'def, Finset.mem_filter, Finset.mem_range]
  -- (A) every `h ∈ S` has its residue class in `R`
  have hmapA : ∀ h ∈ S, h % q ∈ R := by
    intro h hh
    rw [memS] at hh
    rw [memR]
    refine ⟨Nat.mod_lt _ hq, ?_⟩
    exact intDist_mod_le hM hq hβ' (Finset.mem_Icc.mp hh.1).2 hh.2
  have hmodlt : ∀ h ∈ S, h % q ∈ Finset.range q := by
    intro h hh
    rw [Finset.mem_range]
    exact Nat.mod_lt _ hq
  -- (B) fiberwise bound
  have hcardSeq : S.card = ∑ r ∈ Finset.range q,
      (S.filter (fun h : ℕ => h % q = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmodlt
  have hfiber : ∀ r ∈ Finset.range q,
      ((S.filter (fun h : ℕ => h % q = r)).card : ℝ) ≤ (M : ℝ) / (q : ℝ) + 1 := by
    intro r _
    have hsub : S.filter (fun h : ℕ => h % q = r)
        ⊆ Finset.filter (fun h : ℕ => h % q = r) (Finset.Icc 1 M) := by
      intro h hh
      rw [Finset.mem_filter] at hh ⊢
      exact ⟨(memS h).mp hh.1 |>.1, hh.2⟩
    calc ((S.filter (fun h : ℕ => h % q = r)).card : ℝ)
        ≤ ((Finset.filter (fun h : ℕ => h % q = r) (Finset.Icc 1 M)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (M : ℝ) / (q : ℝ) + 1 := card_filter_mod_eq_le M q r hq
  have hzero : ∀ r ∈ Finset.range q, r ∉ R →
      ((S.filter (fun h : ℕ => h % q = r)).card : ℝ) = 0 := by
    intro r _ hrR
    have hempty : S.filter (fun h : ℕ => h % q = r) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro h hhS hmod
      have hmem : r ∈ R := by
        have := hmapA h hhS
        rwa [hmod] at this
      exact hrR hmem
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  have hB : (S.card : ℝ) ≤ R.card * ((M : ℝ) / (q : ℝ) + 1) := by
    have h1 : (S.card : ℝ) = ∑ r ∈ R,
        ((S.filter (fun h : ℕ => h % q = r)).card : ℝ) := by
      rw [hcardSeq, Nat.cast_sum]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro r hr
        rw [hRdef, Finset.mem_filter] at hr
        exact hr.1
      · intro r hr hrR
        exact hzero r hr hrR
    have h2 : ∑ r ∈ R, ((S.filter (fun h : ℕ => h % q = r)).card : ℝ)
        ≤ ∑ _r ∈ R, ((M : ℝ) / (q : ℝ) + 1) := by
      refine Finset.sum_le_sum ?_
      intro r hr
      have hr' : r ∈ Finset.range q := Finset.mem_range.mpr ((memR r).mp hr).1
      exact hfiber r hr'
    rw [h1]
    calc ∑ r ∈ R, ((S.filter (fun h : ℕ => h % q = r)).card : ℝ)
        ≤ ∑ _r ∈ R, ((M : ℝ) / (q : ℝ) + 1) := h2
      _ = R.card * ((M : ℝ) / (q : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- (C) `R.card ≤ R'.card`
  set φ : ℕ → ℕ := fun r => ((a * (r : ℤ)) % (q : ℤ)).toNat with hφdef
  have hφnonneg : ∀ r : ℕ, 0 ≤ (a * (r : ℤ)) % (q : ℤ) := fun r =>
    Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  have hφval : ∀ r : ℕ, ((φ r : ℕ) : ℤ) = (a * (r : ℤ)) % (q : ℤ) := by
    intro r
    show ((((a * (r : ℤ)) % (q : ℤ)).toNat : ℕ) : ℤ) = (a * (r : ℤ)) % (q : ℤ)
    exact Int.toNat_of_nonneg (hφnonneg r)
  have hφlt : ∀ r : ℕ, r < q → φ r < q := by
    intro r _hr
    have h1 : (a * (r : ℤ)) % (q : ℤ) < (q : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    have h2 : ((a * (r : ℤ)) % (q : ℤ)).toNat < q ↔
        (a * (r : ℤ)) % (q : ℤ) < (q : ℤ) := Int.toNat_lt (hφnonneg r)
    exact h2.mpr h1
  have hφdist : ∀ r : ℕ,
      Submission.VanDerCorput.intDist (2 * (φ r : ℝ) / (q : ℝ))
        = Submission.VanDerCorput.intDist (2 * (a : ℝ) * (r : ℝ) / (q : ℝ)) := by
    intro r
    set t : ℤ := (a * (r : ℤ)) / (q : ℤ) with ht
    set s : ℤ := (a * (r : ℤ)) % (q : ℤ) with hs
    have hs_nonneg : 0 ≤ s := by rw [hs]; exact hφnonneg r
    have hsval : φ r = s.toNat := by simp only [hφdef, hs]
    have hA : a * (r : ℤ) = (q : ℤ) * t + s := by
      rw [ht, hs]; exact (Int.mul_ediv_add_emod _ _).symm
    have hcastA : (a : ℝ) * (r : ℝ) = (q : ℝ) * (t : ℝ) + (s : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hA
      have e1 : ((a * (r : ℤ) : ℤ) : ℝ) = (a : ℝ) * (r : ℝ) := by
        rw [Int.cast_mul, Int.cast_natCast]
      have e2 : (((q : ℤ) * t + s : ℤ) : ℝ) = (q : ℝ) * (t : ℝ) + (s : ℝ) := by
        rw [Int.cast_add, Int.cast_mul, Int.cast_natCast]
      rw [e1, e2] at h
      exact h
    have hphi : ((φ r : ℕ) : ℝ) = (s : ℝ) := by
      rw [hsval]
      exact_mod_cast (Int.toNat_of_nonneg hs_nonneg)
    have hmain : 2 * (a : ℝ) * (r : ℝ) / (q : ℝ)
        = 2 * (s : ℝ) / (q : ℝ) + 2 * (t : ℝ) := by
      have h2 : 2 * (a : ℝ) * (r : ℝ) = 2 * (s : ℝ) + 2 * (q : ℝ) * (t : ℝ) := by
        have h3 : 2 * ((a : ℝ) * (r : ℝ)) = 2 * ((q : ℝ) * (t : ℝ) + (s : ℝ)) := by rw [hcastA]
        linarith
      rw [h2]
      field_simp
    have h2t : ((2 * t : ℤ) : ℝ) = 2 * (t : ℝ) := by rw [Int.cast_mul, Int.cast_ofNat]
    rw [hmain, hphi, ← h2t, intDist_add_intCast]
  have hC : R.card ≤ R'.card := by
    refine Finset.card_le_card_of_injOn φ ?hmaps ?hinj
    · intro r hr
      obtain ⟨hrq, hrcond⟩ := (memR r).mp hr
      exact (memR' (φ r)).mpr ⟨hφlt r hrq, by rw [hφdist r]; exact hrcond⟩
    · intro r hr r' hr' heq
      obtain ⟨hrq, _⟩ := (memR r).mp hr
      obtain ⟨hr'q, _⟩ := (memR r').mp hr'
      have hEqmod : (a * (r : ℤ)) % (q : ℤ) = (a * (r' : ℤ)) % (q : ℤ) := by
        have h1 : ((φ r : ℕ) : ℤ) = ((φ r' : ℕ) : ℤ) := by exact_mod_cast heq
        rw [hφval r, hφval r'] at h1
        exact h1
      have hdvd : (q : ℤ) ∣ (a * (r : ℤ)) - (a * (r' : ℤ)) := by
        have hmod : ((a * (r : ℤ)) - (a * (r' : ℤ))) % (q : ℤ) = 0 := by
          rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
          exact hEqmod
        exact Int.dvd_of_emod_eq_zero hmod
      have hdvd2 : (q : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) := by
        have hcop : IsCoprime (q : ℤ) a := (Int.isCoprime_iff_gcd_eq_one.mpr hgcd).symm
        refine hcop.dvd_of_dvd_mul_left ?_
        have h : a * ((r : ℤ) - (r' : ℤ)) = (a * (r : ℤ)) - (a * (r' : ℤ)) := by ring
        rw [h]
        exact hdvd
      obtain ⟨k, hk⟩ := hdvd2
      have habs : |((r : ℤ) - (r' : ℤ))| < (q : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      rw [hk, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ))] at habs
      have hk0 : k = 0 := by
        have : |k| < 1 := by
          have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
          nlinarith
        exact Int.abs_lt_one_iff.mp this
      have hsub0 : (r : ℤ) - (r' : ℤ) = 0 := by rw [hk, hk0, mul_zero]
      omega
  -- (D) cardinality of `R'`
  have hD : (R'.card : ℝ) ≤ 4 * (q : ℝ) * (ε + 2 / (q : ℝ)) + 4 := by
    rw [hR'def]
    exact card_small_intDist_residues q hq (ε := ε + 2 / (q : ℝ)) (by positivity)
  have hD2 : (4 * (q : ℝ) * (ε + 2 / (q : ℝ)) + 4) ≤ (4 * (q : ℝ) * ε + 14) := by
    have hq2 : (q : ℝ) * (2 / (q : ℝ)) = 2 := by field_simp
    nlinarith [hq2]
  calc (S.card : ℝ) ≤ R.card * ((M : ℝ) / (q : ℝ) + 1) := hB
    _ ≤ R'.card * ((M : ℝ) / (q : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (by positivity)
    _ ≤ (4 * (q : ℝ) * (ε + 2 / (q : ℝ)) + 4) * ((M : ℝ) / (q : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hD (by positivity)
    _ ≤ (4 * (q : ℝ) * ε + 14) * ((M : ℝ) / (q : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hD2 (by positivity)


/-! ### The main theorem -/

theorem quadratic_differencing_counting {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (a : ℤ) (q : ℕ), 0 < q →
      Int.gcd a (q : ℤ) = 1 →
      ‖β - (a : ℝ) / (q : ℝ)‖ ≤ 1 / ((q : ℝ) * (M : ℝ)) →
      (∑ h ∈ Finset.Icc 1 M,
        (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
         else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ)))))
        ≤ C * (M : ℝ) ^ e * (((M : ℝ) ^ 2) / (q : ℝ) + (M : ℝ) + (q : ℝ)) := by
  obtain ⟨C_H, hC_H_pos, hC_H⟩ := Commons.Analysis.Series.harmonic_sum_le_rpow he
  refine ⟨29 + 4 * C_H, by positivity, ?_⟩
  intro M hM β a q hq hgcd hβ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMe : (1 : ℝ) ≤ (M : ℝ) ^ e := Real.one_le_rpow hM1 (le_of_lt he)
  -- conversion between the pointwise sum of indicators and a cardinality
  have hsum_eq : ∀ F : ℝ,
      ((Finset.filter (fun k : ℕ => F ≤ 1 / (2 * (k : ℝ))) (Finset.Icc 1 M)).card : ℝ)
        = ∑ k ∈ Finset.Icc 1 M, (if F ≤ 1 / (2 * (k : ℝ)) then (1 : ℝ) else 0) := by
    intro F
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    by_cases hk : F ≤ 1 / (2 * (k : ℝ)) <;> simp [hk]
  -- the layer-cake bound, termwise
  have hlayer : ∀ h ∈ Finset.Icc 1 M,
      (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
       else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ))))
      ≤ 1 + ∑ k ∈ Finset.Icc 1 M,
          (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
           then (1 : ℝ) else 0) := by
    intro h _
    set D : ℝ := Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) with hD
    have hD0 : 0 ≤ D := Submission.VanDerCorput.intDist_nonneg _
    by_cases hzero : D = 0
    · have hzero' : Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 := by
        rw [← hD]; exact hzero
      rw [if_pos hzero', hzero]
      have hone : ∀ k ∈ Finset.Icc 1 M,
          (if (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) then (1 : ℝ) else 0) = 1 := by
        intro k hk
        have hk1 : (0 : ℝ) < (k : ℝ) := by
          have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          exact_mod_cast this
        rw [if_pos (by positivity)]
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel, Nat.cast_one, mul_one]
      linarith
    · have hzero' : ¬ Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 := by
        rw [← hD]; exact hzero
      rw [if_neg hzero']
      have hDpos : 0 < D := lt_of_le_of_ne' hD0 hzero
      have hmin := min_le_one_add_card_div M hM hDpos
      rw [← hsum_eq D]
      exact hmin
  -- step 1: sum the termwise bound
  have hstep1 : (∑ h ∈ Finset.Icc 1 M,
        (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
         else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ)))))
      ≤ ∑ h ∈ Finset.Icc 1 M,
          (1 + ∑ k ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
             then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum hlayer
  -- step 2: separate and interchange the double sum
  have hstep2 : ∑ h ∈ Finset.Icc 1 M,
          (1 + ∑ k ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
             then (1 : ℝ) else 0))
      = (M : ℝ) + ∑ k ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
             then (1 : ℝ) else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel, Nat.cast_one, mul_one]
  -- step 3: identify the inner sum with the counting function
  have hstep3 : ∀ k ∈ Finset.Icc 1 M,
      (∑ h ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
             then (1 : ℝ) else 0))
        = ((Finset.filter (fun h : ℕ =>
            Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ)))
            (Finset.Icc 1 M)).card : ℝ) := by
    intro k _
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    by_cases hc : Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
    <;> simp [hc]
  -- step 4: apply the counting lemma
  have hstep4 : ∑ k ∈ Finset.Icc 1 M,
        ((Finset.filter (fun h : ℕ =>
            Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ)))
            (Finset.Icc 1 M)).card : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 M, (4 * (q : ℝ) * (1 / (2 * (k : ℝ))) + 14) * ((M : ℝ) / (q : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    refine count_intDist_le hM hq hgcd hβ ?_
    have hk1 : (0 : ℝ) < (k : ℝ) := by
      have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      exact_mod_cast this
    positivity
  -- step 5: evaluate the resulting sum
  have hstep5 : ∑ k ∈ Finset.Icc 1 M, (4 * (q : ℝ) * (1 / (2 * (k : ℝ))) + 14) * ((M : ℝ) / (q : ℝ) + 1)
      ≤ ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ)) := by
    have hterm : ∀ k ∈ Finset.Icc 1 M,
        (4 * (q : ℝ) * (1 / (2 * (k : ℝ))) + 14) = 2 * (q : ℝ) * (1 / (k : ℝ)) + 14 := by
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (k : ℝ) := by
          have hkk : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          exact_mod_cast hkk
        exact ne_of_gt this
      field_simp
      ring
    calc ∑ k ∈ Finset.Icc 1 M, (4 * (q : ℝ) * (1 / (2 * (k : ℝ))) + 14) * ((M : ℝ) / (q : ℝ) + 1)
        = ((M : ℝ) / (q : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 M, (2 * (q : ℝ) * (1 / (k : ℝ)) + 14) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hterm k hk]
          ring
      _ = ((M : ℝ) / (q : ℝ) + 1)
            * (2 * (q : ℝ) * (∑ k ∈ Finset.Icc 1 M, (1 / (k : ℝ))) + 14 * (M : ℝ)) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp only [Nat.add_sub_cancel]
          ring
      _ ≤ ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 : 2 * (q : ℝ) * (∑ k ∈ Finset.Icc 1 M, (1 / (k : ℝ)))
              ≤ 2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) :=
            mul_le_mul_of_nonneg_left (hC_H M hM) (by positivity)
          linarith [h1]
  -- final algebra
  have hpow : (M : ℝ) ^ (1 + e) = (M : ℝ) ^ e * (M : ℝ) := by
    rw [Real.rpow_add (by positivity : (0 : ℝ) < (M : ℝ)), Real.rpow_one]
    ring
  set P : ℝ := (M : ℝ) ^ e * (((M : ℝ) ^ 2) / (q : ℝ) + (M : ℝ) + (q : ℝ)) with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hMR) e) (by positivity)
  have hMqnn : 0 ≤ (M : ℝ) ^ 2 / (q : ℝ) := by positivity
  have hinner : (M : ℝ) ≤ (M : ℝ) ^ 2 / (q : ℝ) + (M : ℝ) + (q : ℝ) := by
    linarith [hMqnn, hqR.le]
  have hqinner : (q : ℝ) ≤ (M : ℝ) ^ 2 / (q : ℝ) + (M : ℝ) + (q : ℝ) := by
    linarith [hMqnn, hMR.le]
  have hMleP : (M : ℝ) ≤ P := by
    rw [hPdef]
    have h1 : (M : ℝ) ≤ (M : ℝ) ^ e * (M : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hMe (le_of_lt hMR)
      simpa using h
    calc (M : ℝ) ≤ (M : ℝ) ^ e * (M : ℝ) := h1
      _ ≤ (M : ℝ) ^ e * (((M : ℝ) ^ 2) / (q : ℝ) + (M : ℝ) + (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg (le_of_lt hMR) e)
  have hpowleP : (M : ℝ) ^ (1 + e) ≤ P := by
    rw [hPdef, hpow]
    exact mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg (le_of_lt hMR) e)
  have hqleP : (q : ℝ) * (M : ℝ) ^ e ≤ P := by
    rw [hPdef, mul_comm]
    exact mul_le_mul_of_nonneg_left hqinner (Real.rpow_nonneg (le_of_lt hMR) e)
  have hM2qleP : (M : ℝ) ^ 2 / (q : ℝ) ≤ P := by
    rw [hPdef]
    have h2 : (M : ℝ) ^ 2 / (q : ℝ) ≤ (M : ℝ) ^ 2 / (q : ℝ) + (M : ℝ) + (q : ℝ) := by
      linarith [hMqnn, hMR.le, hqR.le]
    calc (M : ℝ) ^ 2 / (q : ℝ) = 1 * ((M : ℝ) ^ 2 / (q : ℝ)) := by ring
      _ ≤ (M : ℝ) ^ e * ((M : ℝ) ^ 2 / (q : ℝ)) :=
          mul_le_mul_of_nonneg_right hMe hMqnn
      _ ≤ (M : ℝ) ^ e * (((M : ℝ) ^ 2) / (q : ℝ) + (M : ℝ) + (q : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (le_of_lt hMR) e)
  have hsplit : (M : ℝ) + ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ))
      = (M : ℝ) + 2 * C_H * (M : ℝ) ^ (1 + e) + 2 * C_H * ((q : ℝ) * (M : ℝ) ^ e)
          + 14 * ((M : ℝ) ^ 2 / (q : ℝ)) + 14 * (M : ℝ) := by
    rw [hpow]
    field_simp
    ring
  have hfinal : (M : ℝ) + ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ))
      ≤ (29 + 4 * C_H) * P := by
    rw [hsplit]
    have h2 : 2 * C_H * (M : ℝ) ^ (1 + e) ≤ 2 * C_H * P :=
      mul_le_mul_of_nonneg_left hpowleP (by linarith [hC_H_pos])
    have h3 : 2 * C_H * ((q : ℝ) * (M : ℝ) ^ e) ≤ 2 * C_H * P :=
      mul_le_mul_of_nonneg_left hqleP (by linarith [hC_H_pos])
    have h4 : 14 * ((M : ℝ) ^ 2 / (q : ℝ)) ≤ 14 * P :=
      mul_le_mul_of_nonneg_left hM2qleP (by norm_num)
    have h5 : 14 * (M : ℝ) ≤ 14 * P := mul_le_mul_of_nonneg_left hMleP (by norm_num)
    have h6 : 2 * C_H * P + 2 * C_H * P + 14 * P + 14 * P = (28 + 4 * C_H) * P := by ring
    nlinarith [h2, h3, h4, h5, h6, hMleP, hPnn]
  have hmain : (∑ h ∈ Finset.Icc 1 M,
        (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
         else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ)))))
      ≤ (M : ℝ) + ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ)) := by
    calc (∑ h ∈ Finset.Icc 1 M,
        (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
         else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ)))))
        ≤ ∑ h ∈ Finset.Icc 1 M,
          (1 + ∑ k ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
             then (1 : ℝ) else 0)) := hstep1
      _ = (M : ℝ) + ∑ k ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 M,
            (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ))
             then (1 : ℝ) else 0) := hstep2
      _ = (M : ℝ) + ∑ k ∈ Finset.Icc 1 M,
            ((Finset.filter (fun h : ℕ =>
              Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) ≤ 1 / (2 * (k : ℝ)))
              (Finset.Icc 1 M)).card : ℝ) := by
          congr 1
          exact Finset.sum_congr rfl (fun k hk => hstep3 k hk)
      _ ≤ (M : ℝ) + ∑ k ∈ Finset.Icc 1 M,
            (4 * (q : ℝ) * (1 / (2 * (k : ℝ))) + 14) * ((M : ℝ) / (q : ℝ) + 1) := by
          linarith [hstep4]
      _ ≤ (M : ℝ) + ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ)) := by
          linarith [hstep5]
  calc (∑ h ∈ Finset.Icc 1 M,
        (if Submission.VanDerCorput.intDist (2 * β * (h : ℝ)) = 0 then (M : ℝ)
         else min (M : ℝ) ((1 / 2) / Submission.VanDerCorput.intDist (2 * β * (h : ℝ)))))
      ≤ (M : ℝ) + ((M : ℝ) / (q : ℝ) + 1) * (2 * (q : ℝ) * (C_H * (M : ℝ) ^ e) + 14 * (M : ℝ)) := hmain
    _ ≤ (29 + 4 * C_H) * P := hfinal
    _ = (29 + 4 * C_H) * (M : ℝ) ^ e * (((M : ℝ) ^ 2) / (q : ℝ) + (M : ℝ) + (q : ℝ)) := by
        rw [hPdef]
        ring

end Commons.Analysis.ExponentialSums

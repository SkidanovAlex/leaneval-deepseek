import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Work.FIArea7.KInner_bound_good
import Submission.Work.FIArea7.jacobiSym_dilation
import Submission.Work.FIArea7.multEps_step
import Submission.Work.FIArea7.sector_diff_le
import Submission.Work.FIArea7.twoChar_pv_dilated
import Submission.Work.FIArea7.TwoCharPV.Basic
import Submission.Work.FIArea7.KStarAP.sum_filter_modEq_eq_sum_class
import Submission.Work.FIArea7.KStarAP.sum_toNat_ediv_le
import Submission.Work.FIArea7.KStarAP.toNat_sub_one_le
import Submission.Work.FIArea7.KStarAP.sqrt_prod_le_gcd_div
import Submission.Work.FIArea7.KStarAP.fibre_arith_chi

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7.KStarAP

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- If `thi < tlo` then every class interval of the `mod κ` splitting of `Icc tlo thi` is empty,
so the sum of the `toNat`-lengths of the class intervals is `0`. -/
private lemma toNat_sum_zero_of_lt (κ : ℤ) (hκ : 0 < κ) (tlo thi : ℤ) (h : thi < tlo) :
    ∑ e ∈ Finset.Ico (0:ℤ) κ, ((thi - e) / κ + (e - tlo) / κ).toNat = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  rw [Int.toNat_eq_zero]
  have h1 : (thi - e) / κ + (e - tlo) / κ ≤ (thi - tlo) / κ := by
    have h2 := Int.ediv_add_ediv_le_add_ediv (x := thi - e) (y := e - tlo) (z := κ) hκ
    rw [show thi - e + (e - tlo) = thi - tlo by ring] at h2
    exact h2
  have h3 : (thi - tlo) / κ ≤ -1 := by
    have h4 : thi - tlo < (0:ℤ) * κ := by omega
    have h5 := Int.ediv_lt_of_lt_mul hκ h4
    omega
  omega

/-- **The fibre bound of *FI* (22.4) for one residue class mod `4M`, with the character `χ` and the
modulus `d` made explicit.**  For primary primitive `w`, odd `r ≠ 0`, `ω` with `ω Re w ≡ -Im w` and
`ω²+1 ≡ 0 (mod q)` (`q = |w|²`), `χ` of modulus `4d` with `‖χ‖ ≤ 1`, a modulus `M ≥ 1` with `M ∣ q`,
and a prime `p ∤ 4dq` dividing `r` to an odd power, the sum of the fibre summand of `K` — the weight
`χ(z)(z/|z|)^k`, the quadrant sign `ε(w,z)` and the two Jacobi characters `(s | |r|)`, `(s - ωr | q)`
— over the residue class `s ≡ c (mod 4M)` inside `Icc S T` satisfies

  `‖Σ …‖ ≤ C·d·(|k|+1)·√(q/M)·(√|r| + (T-S)/√|r|)·log(2 + |r|q)`.

Proof route (mirrors `KInner_bound_good`): set `A := 4 * lcm M (d * gcd r.natAbs q)`, decompose the
filtered sum into the classes `s ≡ c' (mod A)` lying in the class `c (mod 4M)` (there are
`A/(4M)` of them), and apply the proved `Work.FIArea7.class_bound` to each class with the parameter
`G := gcd r.natAbs q`: `G ∣ r.natAbs`, `G ∣ gnorm w`, `G ∣ A`, every common prime of `r.natAbs` and
`q` divides `G ∣ A`, and the good prime `p ∤ 4dq` divides neither `d` nor `q`, so is coprime to `A`.
`class_bound` then gives `C₀(2 + 2N_c·|k|·2A/|r|)·√(r.natAbs·q)/G` per class with `Σ_c N_c·A ≤ T-S`;
summing over the `A/(4M)` classes and using `A = 4·lcm(M,dG) ≤ 4MdG/gcd(M,dG)` gives exactly the
stated bound (the `√(q/M)` factor comes from `M ∣ q` and the `√(r.natAbs·q)/G` type factor). -/
theorem ap_char_chi_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ)
      (r ω M c S T : ℤ),
      Work.FIPlan.IsPrimary w → IsCoprime w.re w.im →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ a b : ℤ, chi (⟨a, b + 4 * (d : ℤ)⟩ : GaussianInt) = chi (⟨a, b⟩ : GaussianInt)) →
      Odd r → r ≠ 0 →
      (ω * w.re ≡ -w.im [ZMOD (((Work.FIPlan.gnorm w : ℕ) : ℤ))]) →
      ((ω ^ 2 + 1) ≡ 0 [ZMOD (((Work.FIPlan.gnorm w : ℕ) : ℤ))]) →
      1 ≤ M → (M : ℤ) ∣ (((Work.FIPlan.gnorm w : ℕ) : ℤ)) →
      (∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (((Work.FIPlan.gnorm w : ℕ) : ℤ))) ∧
        Odd (r.natAbs.factorization p)) →
      ‖∑ s ∈ (Finset.Icc S T).filter (fun s => s ≡ c [ZMOD (4 * M)]),
          chi (⟨r, s⟩ : GaussianInt) * gunitC (⟨r, s⟩ : GaussianInt) ^ k
            * (MultEps w (⟨r, s⟩ : GaussianInt) : ℂ)
            * (jacobiSym s r.natAbs : ℂ)
            * (jacobiSym (s - ω * r) (Work.FIPlan.gnorm w) : ℂ)‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1)
            * Real.sqrt ((((Work.FIPlan.gnorm w : ℕ)) : ℝ) / (M : ℝ))
            * (Real.sqrt |(r : ℝ)|
                + (((T - S).toNat : ℝ)) * (Real.sqrt |(r : ℝ)|)⁻¹)
            * Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) := by
  obtain ⟨C0, hC0pos, h2char⟩ := Work.FIArea7.twoChar_complex_bound
  refine ⟨8 * C0, by positivity, ?_⟩
  intro d hd w k chi r ω M c S T hw hcopw hchi hper hr hrn hω hω2 hM1 hMq hgood
  classical
  set q : ℕ := Work.FIPlan.gnorm w with hqdef
  set τ : ℕ := r.natAbs with hτdef
  set G : ℕ := Nat.gcd τ q with hGdef
  set Mn : ℕ := M.natAbs with hMndef
  set An : ℕ := 4 * Nat.lcm Mn (d * G) with hAndef
  set A : ℤ := (An : ℤ) with hAdef
  set κ : ℕ := An / (4 * Mn) with hκdef
  set W : ℕ := Nat.gcd Mn G with hWdef
  set W2 : ℕ := Nat.gcd Mn (d * G) with hW2def
  set Ln : ℝ := ((T - S).toNat : ℝ) with hLndef
  set DD : ℝ := |(k:ℝ)| * 2 * |(A:ℝ)| / |(r:ℝ)| with hDDdef
  set SQW : ℝ := ((W:ℝ)/(G:ℝ)) * Real.sqrt ((τ:ℝ)*(q:ℝ)/(M:ℝ)) with hSQWdef
  set LG2 : ℝ := Real.log (2 + (τ:ℝ)*(q:ℝ)) with hLG2def
  let F : ℤ → ℂ := fun s => chi (⟨r, s⟩ : GaussianInt) * gunitC (⟨r, s⟩ : GaussianInt) ^ k
      * (MultEps w (⟨r, s⟩ : GaussianInt) : ℂ) * (jacobiSym s τ : ℂ)
      * (jacobiSym (s - ω * r) q : ℂ)
  set Lb : ℤ → ℤ := fun e => -((e + ((c - S) / (4 * M))) / (κ:ℤ)) with hLbdef
  set Ub : ℤ → ℤ := fun e => ((((T - c) / (4 * M)) - e) / (κ:ℤ)) with hUbdef
  have hqodd : Odd q := by rw [hqdef]; exact Work.FIArea7.odd_gnorm_of_isPrimary w hw
  have hqpos : 0 < q := hqodd.pos
  have hτodd : Odd τ := by rw [hτdef]; exact Odd.natAbs hr
  have hτpos : 0 < τ := hτodd.pos
  have hGpos : 0 < G := by rw [hGdef]; exact Nat.gcd_pos_of_pos_left q hτpos
  have hGτ : G ∣ τ := by rw [hGdef]; exact Nat.gcd_dvd_left τ q
  have hGq : G ∣ q := by rw [hGdef]; exact Nat.gcd_dvd_right τ q
  have hMncast : (Mn : ℤ) = M := by rw [hMndef]; exact Int.natAbs_of_nonneg (by omega)
  have hMnpos : 0 < Mn := by rw [hMndef]; exact Int.natAbs_pos.mpr (by omega)
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : (0:ℤ) < M)
  have hτR : (τ:ℝ) = |(r:ℝ)| := by rw [hτdef, Nat.cast_natAbs, Int.cast_abs]
  have hτRpos : (0:ℝ) < (τ:ℝ) := by exact_mod_cast hτpos
  have hMq' : Mn ∣ q := by
    have h : (Mn : ℤ) ∣ (q : ℤ) := by rw [hMncast, hqdef]; exact hMq
    exact_mod_cast h
  have hdGpos : 0 < d * G := Nat.mul_pos (by omega) hGpos
  have hdlcm : d ∣ Nat.lcm Mn (d * G) := (dvd_mul_right d G).trans (Nat.dvd_lcm_right Mn (d * G))
  have hAnpos : 0 < An := by
    rw [hAndef]; exact Nat.mul_pos (by norm_num) (Nat.lcm_pos hMnpos hdGpos)
  have h4Mndvd : 4 * Mn ∣ An := by
    rw [hAndef]; exact mul_dvd_mul_left 4 (Nat.dvd_lcm_left Mn (d * G))
  have hBpos : (0:ℤ) < 4 * M := by omega
  have hκpos : 0 < κ := by
    rw [hκdef]; exact Nat.div_pos (Nat.le_of_dvd hAnpos h4Mndvd) (by positivity)
  have hκzpos : (0:ℤ) < (κ:ℤ) := by exact_mod_cast hκpos
  have hAn_eq : An = 4 * Mn * κ := by
    rw [hκdef]; exact (Nat.mul_div_cancel' h4Mndvd).symm
  have hAeq : A = 4 * M * (κ : ℤ) := by
    rw [hAdef, hAn_eq]; push_cast; rw [hMncast]
  have hApos : (0:ℝ) < (A:ℝ) := by
    have h : (0:ℤ) < A := by rw [hAdef]; exact_mod_cast hAnpos
    exact_mod_cast h
  have hκ_eq : κ = d * G / Nat.gcd Mn (d * G) := by
    rw [hκdef, hAndef, Nat.mul_div_mul_left (Nat.lcm Mn (d * G)) Mn (by norm_num : (0:ℕ) < 4)]
    rw [show Nat.lcm Mn (d * G) = Mn * ((d * G) / Nat.gcd Mn (d * G)) by
          rw [Nat.lcm, Nat.mul_div_assoc Mn (Nat.gcd_dvd_right Mn (d * G))],
        Nat.mul_div_right _ hMnpos]
  have hκW2 : (κ:ℝ) = (d:ℝ) * (G:ℝ) / (W2:ℝ) := by
    rw [hκ_eq, hW2def]
    have hW2pos : 0 < Nat.gcd Mn (d * G) := Nat.gcd_pos_of_pos_left _ hMnpos
    rw [Nat.cast_div (Nat.gcd_dvd_right Mn (d*G)) (by positivity : (Nat.gcd Mn (d*G):ℝ) ≠ 0)]
    push_cast
    ring
  have hW_le : W ≤ W2 := by
    rw [hWdef, hW2def]
    refine Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (d * G) hMnpos) ?_
    refine Nat.dvd_gcd (Nat.gcd_dvd_left Mn G) ?_
    exact (Nat.gcd_dvd_right Mn G).trans ⟨d, by ring⟩
  have hGA : ∀ p : ℕ, p.Prime → (p ∣ Mn ∨ p ∣ G) → (p : ℤ) ∣ A := by
    intro p hp hpcase
    have hAn_dvd : p ∣ An := by
      have hL : p ∣ Nat.lcm Mn (d * G) := by
        rcases hpcase with h | h
        · exact h.trans (Nat.dvd_lcm_left Mn (d * G))
        · exact (h.trans ⟨d, by ring⟩).trans (Nat.dvd_lcm_right Mn (d * G))
      rw [hAndef]; exact hL.trans ⟨4, by ring⟩
    rw [hAdef]; exact_mod_cast hAn_dvd
  obtain ⟨p₀, hp₀prime, hp₀notdvd, hp₀odd⟩ := hgood
  have hp₀odd' : Odd (τ.factorization p₀) := hp₀odd
  have hp₀dvdτ : p₀ ∣ τ := by
    by_contra h
    have hpos : 0 < τ.factorization p₀ := hp₀odd'.pos
    rw [Nat.factorization_eq_zero_of_not_dvd h] at hpos
    omega
  have hp₀A' : ¬ (p₀ : ℤ) ∣ A := by
    intro hcon
    have hnat : p₀ ∣ 4 * Nat.lcm Mn (d * G) := by
      have h : p₀ ∣ An := by rw [hAdef] at hcon; exact_mod_cast hcon
      rwa [hAndef] at h
    have hcontra : (p₀ : ℤ) ∣ 4 * (d : ℤ) * (q : ℤ) := by
      rcases (Nat.Prime.dvd_mul hp₀prime).mp hnat with h4 | hlcm
      · have h4' : p₀ ∣ 2 * 2 := by simpa using h4
        have h2dvd : p₀ ∣ 2 := ((Nat.Prime.dvd_mul hp₀prime).mp h4').elim id id
        have hle2 : p₀ ≤ 2 := Nat.le_of_dvd (by norm_num) h2dvd
        have hp₀2 : p₀ = 2 := by have := hp₀prime.two_le; omega
        have h2τ : 2 ∣ τ := hp₀2 ▸ hp₀dvdτ
        obtain ⟨a, ha⟩ := hτodd
        obtain ⟨b, hb⟩ := even_iff_two_dvd.mpr h2τ
        omega
      · have hMnG : p₀ ∣ Mn * (d * G) := hlcm.trans (Nat.lcm_dvd_mul Mn (d * G))
        rcases (Nat.Prime.dvd_mul hp₀prime).mp hMnG with hMn | hdG
        · have hqq : (p₀ : ℤ) ∣ (q : ℤ) := by exact_mod_cast (hMn.trans hMq')
          exact dvd_mul_of_dvd_right hqq (4 * (d : ℤ))
        · rcases (Nat.Prime.dvd_mul hp₀prime).mp hdG with hd' | hG'
          · have hdZ : (p₀ : ℤ) ∣ (d : ℤ) := by exact_mod_cast hd'
            exact hdZ.trans ⟨4 * (q : ℤ), by ring⟩
          · have hqq : (p₀ : ℤ) ∣ (q : ℤ) := by exact_mod_cast (hG'.trans hGq)
            exact dvd_mul_of_dvd_right hqq (4 * (d : ℤ))
    exact hp₀notdvd (by simpa only [hqdef] using hcontra)
  obtain ⟨V, hV⟩ : ∃ V : ℕ, Nat.lcm Mn (d * G) = d * V :=
    ⟨Nat.lcm Mn (d * G) / d, (Nat.mul_div_cancel' hdlcm).symm⟩
  have hA4d : A = 4 * (d:ℤ) * (V:ℤ) := by
    rw [hAdef, hAndef, hV]; push_cast; ring
  have hchi_c : ∀ (e u : ℤ),
      chi (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) = chi (⟨r, c + 4 * M * e⟩ : GaussianInt) := by
    intro e u
    have harg : c + 4 * M * e + A * u = (c + 4 * M * e) + 4 * (d:ℤ) * ((V:ℤ) * u) := by
      rw [hA4d]; ring
    rw [harg]
    exact Work.FIArea7.chi_period chi d hper r (c + 4 * M * e) ((V:ℤ) * u)
  have hbound : ∀ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
      ‖∑ u ∈ Finset.Icc (Lb e) (Ub e), F (c + 4 * M * e + A * u)‖
        ≤ C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * SQW * (2 * LG2) := by
    intro e he
    obtain ⟨K₁, c₁', m₁', hK₁, hdvd₁, hdil₁, hf₁, hf₁A⟩ :=
      Work.FIArea7.jacobiSym_dilation A (c + 4 * M * e) τ hτodd
    obtain ⟨K₂, c₂', m₂', hK₂, hdvd₂, hdil₂, hf₂, hf₂A⟩ :=
      Work.FIArea7.jacobiSym_dilation A (c + 4 * M * e - ω * r) q hqodd
    have hm₁'odd : Odd m₁' := hτodd.of_dvd_nat hdvd₁
    have hm₂'odd : Odd m₂' := hqodd.of_dvd_nat hdvd₂
    have hm₁'pos : 0 < m₁' := hm₁'odd.pos
    have hm₂'pos : 0 < m₂' := hm₂'odd.pos
    have hcop' : Nat.Coprime m₁' m₂' := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hg
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
      have hp1 : p ∣ m₁' := hpdvd.trans (Nat.gcd_dvd_left _ _)
      have hp2 : p ∣ m₂' := hpdvd.trans (Nat.gcd_dvd_right _ _)
      have hfac1 : m₁'.factorization p ≠ 0 := by
        intro h0
        rw [Nat.factorization_eq_zero_iff] at h0
        rcases h0 with h | h | h
        · exact h hp
        · exact h hp1
        · exact hm₁'pos.ne' h
      have hpA : (p:ℤ) ∣ A := hGA p hp (Or.inr (Nat.dvd_gcd (hp1.trans hdvd₁) (hp2.trans hdvd₂)))
      exact hfac1 (hf₁A p hp hpA)
    have hgood'' : ∃ p : ℕ, p.Prime ∧ Odd (m₁'.factorization p) :=
      ⟨p₀, hp₀prime, by rw [hf₁ p₀ hp₀prime hp₀A']; exact hp₀odd'⟩
    have hsc := Work.FIArea7.single_class_bound C0 hC0pos h2char w k A r (c + 4 * M * e)
        m₁' m₂' c₁' c₂' (Lb e) (Ub e) hrn hm₁'odd hm₂'odd hcop' hgood''
    have hsum_eq : (∑ u ∈ Finset.Icc (Lb e) (Ub e), F (c + 4 * M * e + A * u))
        = chi (⟨r, c + 4 * M * e⟩ : GaussianInt) * (((K₁ * K₂ : ℤ)) : ℂ)
          * (∑ u ∈ Finset.Icc (Lb e) (Ub e),
              gunitC (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) ^ k
                * (MultEps w (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) : ℂ)
                * (jacobiSym (u + c₁') m₁' : ℂ) * (jacobiSym (u + c₂') m₂' : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp only [F]
      have h1 : (jacobiSym (c + 4 * M * e + A * u) τ : ℂ)
          = (((K₁ : ℤ)) : ℂ) * (jacobiSym (u + c₁') m₁' : ℂ) := by
        rw [show c + 4 * M * e + A * u = A * u + (c + 4 * M * e) by ring, hdil₁ u]
        push_cast; ring
      have h2 : (jacobiSym (c + 4 * M * e + A * u - ω * r) q : ℂ)
          = (((K₂ : ℤ)) : ℂ) * (jacobiSym (u + c₂') m₂' : ℂ) := by
        rw [show c + 4 * M * e + A * u - ω * r = A * u + (c + 4 * M * e - ω * r) by ring,
          hdil₂ u]
        push_cast; ring
      rw [hchi_c e u, h1, h2]
      push_cast
      ring
    have hSQ : Real.sqrt ((m₁':ℝ) * (m₂':ℝ)) ≤ SQW := by
      have h := Work.FIArea7.KStarAP.sqrt_prod_le_gcd_div A τ q Mn G m₁' m₂'
        hτpos.ne' hqpos.ne' hMnpos hMq' hGτ hGq hdvd₁ hdvd₂ hf₁A hf₂A hGA
      have hcast : ((Mn : ℕ) : ℝ) = (M : ℝ) := by rw [← hMncast]; push_cast; ring
      rw [hSQWdef, hWdef]
      rw [hcast] at h
      exact h
    have hlog : Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1 ≤ 2 * LG2 := by
      have hm1 : (m₁':ℝ) ≤ (τ:ℝ) := by exact_mod_cast Nat.le_of_dvd hτpos hdvd₁
      have hm2 : (m₂':ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.le_of_dvd hqpos hdvd₂
      have hprod : (m₁':ℝ) * (m₂':ℝ) ≤ (τ:ℝ) * (q:ℝ) :=
        mul_le_mul hm1 hm2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hlog1 : Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) ≤ Real.log (2 + (τ:ℝ) * (q:ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      have hLG1 : (1:ℝ) ≤ LG2 := by
        rw [hLG2def, Real.le_log_iff_exp_le (by positivity)]
        have h1 : (1:ℝ) ≤ (τ:ℝ) := by exact_mod_cast hτpos
        have h2 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqpos
        nlinarith [Real.exp_one_lt_three]
      rw [hLG2def]
      linarith
    have hKK : ‖(((K₁ * K₂ : ℤ)) : ℂ)‖ ≤ 1 := by
      rw [show (((K₁ * K₂ : ℤ)) : ℂ) = ((K₁:ℤ):ℂ) * ((K₂:ℤ):ℂ) by push_cast; ring, norm_mul]
      have h1 : ‖((K₁:ℤ):ℂ)‖ ≤ 1 := by rw [Complex.norm_intCast]; exact_mod_cast hK₁
      have h2 : ‖((K₂:ℤ):ℂ)‖ ≤ 1 := by rw [Complex.norm_intCast]; exact_mod_cast hK₂
      calc ‖((K₁:ℤ):ℂ)‖ * ‖((K₂:ℤ):ℂ)‖ ≤ 1 * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hNnn : (0:ℝ) ≤ ((Ub e - Lb e).toNat : ℝ) := by positivity
    have hDDnn : (0:ℝ) ≤ DD := by rw [hDDdef]; positivity
    have hSQWnn : (0:ℝ) ≤ SQW := by rw [hSQWdef]; positivity
    have hAnn : (0:ℝ) ≤ C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) := by
      refine mul_nonneg hC0pos.le ?_
      refine add_nonneg (by norm_num) ?_
      exact mul_nonneg (mul_nonneg (by norm_num) hNnn) hDDnn
    have hAnn2 : (0:ℝ) ≤ 2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD :=
      add_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hNnn) hDDnn)
    have h2LG : (0:ℝ) ≤ 2 * LG2 := by
      refine mul_nonneg (by norm_num) ?_
      rw [hLG2def]
      refine Real.log_nonneg ?_
      have a : (0:ℝ) ≤ (τ:ℝ) := Nat.cast_nonneg _
      have b : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg a b]
    have hL1nn : (0:ℝ) ≤ Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1 := by
      have h2 : (1:ℝ) ≤ 2 + (m₁':ℝ) * (m₂':ℝ) := by
        have a : (0:ℝ) ≤ (m₁':ℝ) := Nat.cast_nonneg _
        have b : (0:ℝ) ≤ (m₂':ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg a b]
      linarith [Real.log_nonneg h2]
    rw [hsum_eq, norm_mul, norm_mul]
    calc ‖chi (⟨r, c + 4 * M * e⟩ : GaussianInt)‖ * ‖(((K₁ * K₂ : ℤ)) : ℂ)‖
            * ‖∑ u ∈ Finset.Icc (Lb e) (Ub e),
                gunitC (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) ^ k
                  * (MultEps w (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) : ℂ)
                  * (jacobiSym (u + c₁') m₁' : ℂ) * (jacobiSym (u + c₂') m₂' : ℂ)‖
        ≤ 1 * 1 * (C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD)
              * Real.sqrt ((m₁':ℝ) * (m₂':ℝ))
              * (Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1)) := by
          have h3 : (0:ℝ) ≤ ‖∑ u ∈ Finset.Icc (Lb e) (Ub e),
                gunitC (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) ^ k
                  * (MultEps w (⟨r, c + 4 * M * e + A * u⟩ : GaussianInt) : ℂ)
                  * (jacobiSym (u + c₁') m₁' : ℂ) * (jacobiSym (u + c₂') m₂' : ℂ)‖ := norm_nonneg _
          exact mul_le_mul (mul_le_mul (hchi _) hKK (norm_nonneg _) (by norm_num)) hsc h3
            (by norm_num)
      _ = C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * Real.sqrt ((m₁':ℝ) * (m₂':ℝ))
            * (Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1) := by ring
      _ ≤ C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * SQW * (2 * LG2) := by
          have hstep1 : C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD)
                * Real.sqrt ((m₁':ℝ) * (m₂':ℝ))
                * (Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1)
              ≤ C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * SQW
                * (Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSQ hAnn) hL1nn
          have hstep2 : C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * SQW
                * (Real.log (2 + (m₁':ℝ) * (m₂':ℝ)) + 1)
              ≤ C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * SQW * (2 * LG2) :=
            mul_le_mul_of_nonneg_left hlog (mul_nonneg hAnn hSQWnn)
          exact le_trans hstep1 hstep2
  rw [← hτR]
  change ‖∑ s ∈ (Finset.Icc S T).filter (fun s => s ≡ c [ZMOD (4 * M)]), F s‖
      ≤ 8 * C0 * (d:ℝ) * (|(k:ℝ)| + 1) * Real.sqrt ((q:ℝ) / (M:ℝ))
          * (Real.sqrt (τ:ℝ) + Ln * (Real.sqrt (τ:ℝ))⁻¹) * LG2
  have hLnn : (0:ℝ) ≤ Ln := by rw [hLndef]; positivity
  have hSQWnn : (0:ℝ) ≤ SQW := by rw [hSQWdef]; positivity
  have hLG2nn : (0:ℝ) ≤ LG2 := by
    rw [hLG2def]
    apply Real.log_nonneg
    have a : (0:ℝ) ≤ (τ:ℝ) := Nat.cast_nonneg _
    have b : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
    have hab : (0:ℝ) ≤ (τ:ℝ) * (q:ℝ) := mul_nonneg a b
    linarith
  have hqR : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
  have hWnn : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg _
  have hGR : (0:ℝ) < (G:ℝ) := by exact_mod_cast hGpos
  have hW2R : (0:ℝ) < (W2:ℝ) := by
    rw [hW2def]; exact_mod_cast (Nat.gcd_pos_of_pos_left (d * G) hMnpos)
  have hWleR : (W:ℝ) ≤ (W2:ℝ) := by exact_mod_cast hW_le
  have hpt : ∀ e : ℤ, (Ub e - Lb e) =
      ((T - c) / (4*M) - e)/(κ:ℤ) + (e - (-((c - S) / (4 * M))))/(κ:ℤ) := by
    intro e
    rw [hLbdef, hUbdef]
    simp only
    rw [sub_neg_eq_add, sub_neg_eq_add]
  have hsumN : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ)) ≤ Ln / (4 * (M:ℝ)) := by
    by_cases hcase : (-((c - S) / (4 * M))) ≤ ((T - c) / (4 * M))
    · have hR4 := Work.FIArea7.KStarAP.sum_toNat_ediv_le (κ:ℤ) (-((c - S) / (4 * M)))
        ((T - c) / (4 * M)) hκzpos hcase
      have hsub := Work.FIArea7.KStarAP.toNat_sub_one_le M c S T hM1
      have hcast : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ))
          = (((∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
              ((((T - c)/(4*M) - e)/(κ:ℤ) + (e - (-((c - S)/(4*M))))/(κ:ℤ)).toNat)) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [hpt e]
      rw [hcast]
      have hR4R : (((∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
            ((((T - c)/(4*M) - e)/(κ:ℤ) + (e - (-((c - S)/(4*M))))/(κ:ℤ)).toNat)) : ℕ) : ℝ)
          ≤ ((((((T - c) / (4 * M)) + 1 - (-((c - S) / (4 * M)))).toNat - 1 : ℕ)) : ℝ) := by
        exact_mod_cast hR4
      refine le_trans hR4R ?_
      rw [hLndef]
      have hsub' : (((((T - c) / (4 * M)) + 1 - (-((c - S) / (4 * M)))).toNat - 1 : ℕ) : ℝ)
          ≤ ((T - S).toNat : ℝ) / (4 * (M:ℝ)) := by
        rw [sub_neg_eq_add]
        exact hsub
      exact hsub'
    · have hlt : ((T - c) / (4 * M)) < (-((c - S) / (4 * M))) := not_le.mp hcase
      have hz : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
          ((((T - c)/(4*M) - e)/(κ:ℤ) + (e - (-((c - S)/(4*M))))/(κ:ℤ)).toNat)) = 0 :=
        toNat_sum_zero_of_lt (κ:ℤ) hκzpos (-((c - S) / (4 * M))) ((T - c) / (4 * M)) hlt
      have hcast : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ))
          = (((∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
              ((((T - c)/(4*M) - e)/(κ:ℤ) + (e - (-((c - S)/(4*M))))/(κ:ℤ)).toNat)) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [hpt e]
      rw [hcast, hz, Nat.cast_zero, hLndef]
      apply div_nonneg (Nat.cast_nonneg _)
      have : (0:ℝ) < 4 * (M:ℝ) := by linarith [hMR]
      exact this.le
  have hZ : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD))
      ≤ 2 * (κ:ℝ) * (1 + 2 * |(k:ℝ)| * Ln / (τ:ℝ)) := by
    have hconst : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), (2:ℝ)) = 2 * (κ:ℝ) := by
      rw [Finset.sum_const, Int.card_Ico]
      simp only [sub_zero, Int.toNat_natCast, nsmul_eq_mul]
      ring
    have hlin : (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), 2 * ((Ub e - Lb e).toNat : ℝ) * DD)
        = 2 * DD * (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    have hA4MR : (A:ℝ) = 4 * (M:ℝ) * (κ:ℝ) := by rw [hAeq]; push_cast; ring
    have hkey : 2 * DD * (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ))
        ≤ 4 * |(k:ℝ)| * (κ:ℝ) * Ln / (τ:ℝ) := by
      have h1 : 2 * DD * (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ))
          ≤ 2 * DD * (Ln / (4 * (M:ℝ))) :=
        mul_le_mul_of_nonneg_left hsumN (by rw [hDDdef]; positivity)
      have h2 : 2 * DD * (Ln / (4 * (M:ℝ))) = 4 * |(k:ℝ)| * (κ:ℝ) * Ln / (τ:ℝ) := by
        rw [hDDdef, hτR, abs_of_pos hApos, hA4MR, hLndef]
        field_simp
        ring
      exact h1.trans (le_of_eq h2)
    rw [Finset.sum_add_distrib, hconst, hlin]
    calc 2 * (κ:ℝ) + 2 * DD * (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), ((Ub e - Lb e).toNat : ℝ))
        ≤ 2 * (κ:ℝ) + 4 * |(k:ℝ)| * (κ:ℝ) * Ln / (τ:ℝ) := by linarith [hkey]
      _ = 2 * (κ:ℝ) * (1 + 2 * |(k:ℝ)| * Ln / (τ:ℝ)) := by ring
  have hdecomp' : (∑ s ∈ (Finset.Icc S T).filter (fun s => s ≡ c [ZMOD (4 * M)]), F s)
      = ∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
          ∑ u ∈ Finset.Icc (Lb e) (Ub e), F (c + 4 * M * e + A * u) := by
    rw [Work.FIArea7.KStarAP.sum_filter_modEq_eq_sum_class (4*M) A (κ:ℤ) hBpos hκzpos hAeq c S T F]
  have hmain : ‖∑ s ∈ (Finset.Icc S T).filter (fun s => s ≡ c [ZMOD (4 * M)]), F s‖
      ≤ 8 * C0 * (d:ℝ) * (|(k:ℝ)| + 1) * Real.sqrt ((q:ℝ) / (M:ℝ))
          * (Real.sqrt (τ:ℝ) + Ln * (Real.sqrt (τ:ℝ))⁻¹) * LG2 := by
    rw [hdecomp']
    calc ‖∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
            (∑ u ∈ Finset.Icc (Lb e) (Ub e), F (c + 4 * M * e + A * u))‖
        ≤ ∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
            ‖∑ u ∈ Finset.Icc (Lb e) (Ub e), F (c + 4 * M * e + A * u)‖ := norm_sum_le _ _
      _ ≤ ∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ),
            C0 * (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD) * SQW * (2 * LG2) :=
          Finset.sum_le_sum hbound
      _ = C0 * SQW * (2 * LG2)
            * (∑ e ∈ Finset.Ico (0:ℤ) (κ:ℤ), (2 + 2 * ((Ub e - Lb e).toNat : ℝ) * DD)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ ≤ C0 * SQW * (2 * LG2) * (2 * (κ:ℝ) * (1 + 2 * |(k:ℝ)| * Ln / (τ:ℝ))) :=
          mul_le_mul_of_nonneg_left hZ (mul_nonneg (mul_nonneg hC0pos.le hSQWnn)
            (by linarith [hLG2nn]))
      _ = C0 * SQW * (2 * LG2)
            * (2 * ((d:ℝ) * (G:ℝ) / (W2:ℝ)) * (1 + 2 * |(k:ℝ)| * Ln / (τ:ℝ))) := by
          rw [hκW2]
      _ ≤ 8 * C0 * (d:ℝ) * (|(k:ℝ)| + 1) * Real.sqrt ((q:ℝ) / (M:ℝ))
            * (Real.sqrt (τ:ℝ) + Ln * (Real.sqrt (τ:ℝ))⁻¹) * LG2 := by
          rw [hSQWdef, hLG2def]
          have hfib := Work.FIArea7.KStarAP.fibre_arith_chi C0 hC0pos d hd k (τ:ℝ) (q:ℝ) (M:ℝ) Ln
            ((W:ℝ)) ((W2:ℝ)) ((G:ℝ)) hτRpos hqR hMR hLnn hWnn hGR hW2R hWleR
          convert hfib using 1 <;> ring
  exact hmain


end Work.FIArea7.KStarAP

import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.lattice_deriv
import Submission.Work.N8.primesIn_half_card_le_pi0
import Submission.Work.N8.exists_pair_inter_ge
import Submission.Work.N8.deriv_relation_le
import Submission.Work.N8.const_of_lattice_const
import Submission.Work.N8.lattice_inequalities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial Finset

set_option maxHeartbeats 1000000








/-! ### Own helpers -/

lemma Qprod_inter_mul_diff (s t : Finset ℕ) :
    Work.BMF.Qprod s = Work.BMF.Qprod (s ∩ t) * Work.BMF.Qprod (s \ t) := by
  simpa only [Work.BMF.Qprod] using
    (Finset.prod_inter_mul_prod_sdiff s t (fun p : ℕ => (p : ℝ))).symm

lemma IntegralOn_mul_nat {r : ℝ} {γ : Polynomial ℝ} (h : Work.BMF.IntegralOn r γ) (c : ℕ) :
    Work.BMF.IntegralOn (r * (c : ℝ)) γ := by
  intro n
  obtain ⟨m, hm⟩ := h ((c : ℤ) * n)
  refine ⟨m, ?_⟩
  have harg : (r * (c : ℝ)) * (n : ℝ) = r * (((c : ℤ) * n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [harg, hm]

lemma IntegralOn_coarsen {s t : Finset ℕ} {a b : ℕ} {γ : Polynomial ℝ}
    (hs : ∀ p ∈ s, 0 < p) (h : Work.BMF.IntegralOn ((a : ℝ) / Work.BMF.Qprod s) γ) :
    Work.BMF.IntegralOn ((Nat.lcm a b : ℝ) / Work.BMF.Qprod (s ∩ t)) γ := by
  have hQs : ∀ u : Finset ℕ, u ⊆ s → Work.BMF.Qprod u ≠ 0 := by
    intro u hu
    rw [Work.BMF.Qprod]
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    exact_mod_cast ne_of_gt (hs p (hu hp))
  have hQi := hQs (s ∩ t) Finset.inter_subset_left
  have hQt := hQs (s \ t) Finset.sdiff_subset
  have e1 : ((∏ p ∈ s \ t, p : ℕ) : ℝ) = Work.BMF.Qprod (s \ t) := by
    rw [Work.BMF.Qprod, Nat.cast_prod]
  have hP : ((∏ p ∈ s \ t, p : ℕ) : ℝ) ≠ 0 := by rw [e1]; exact hQt
  have key : Work.BMF.Qprod s = Work.BMF.Qprod (s ∩ t) * Work.BMF.Qprod (s \ t) :=
    Qprod_inter_mul_diff s t
  have h1 : Work.BMF.IntegralOn ((Nat.lcm a b : ℝ) / Work.BMF.Qprod s) γ := by
    have hdvd : a ∣ Nat.lcm a b := Nat.dvd_lcm_left a b
    have hlcm : ((Nat.lcm a b : ℕ) : ℝ) = (a : ℝ) * ((Nat.lcm a b / a : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    have h2 := IntegralOn_mul_nat h (Nat.lcm a b / a)
    convert h2 using 1
    rw [hlcm]
    ring
  have h3 : Work.BMF.IntegralOn ((Nat.lcm a b : ℝ) / Work.BMF.Qprod s *
      (∏ p ∈ s \ t, p : ℕ)) γ := IntegralOn_mul_nat h1 (∏ p ∈ s \ t, p)
  have heq : (Nat.lcm a b : ℝ) / Work.BMF.Qprod (s ∩ t) =
      (Nat.lcm a b : ℝ) / Work.BMF.Qprod s * (∏ p ∈ s \ t, p : ℕ) := by
    have key' : Work.BMF.Qprod s = Work.BMF.Qprod (s ∩ t) *
        ((∏ p ∈ s \ t, p : ℕ) : ℝ) := by
      rw [e1, key]
    rw [key']
    field_simp
  rw [heq]
  exact h3

/-- The number `⌈(1-δ¹²)/(δ²-δ¹²)⌉₊ + 2` satisfies the pigeonhole condition. -/
lemma ceil_ratio_ge (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ^ 12 ≤ ((⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2 : ℕ) : ℝ) * (δ ^ 2 - δ ^ 12) := by
  rcases lt_or_eq_of_le hδ1 with h | h
  · have hδ2 : 0 < δ ^ 2 - δ ^ 12 := by
      have h10 : δ ^ 10 < 1 := pow_lt_one₀ (le_of_lt hδ) h (by norm_num)
      nlinarith [sq_pos_of_pos hδ]
    have hceil : (1 - δ ^ 12) / (δ ^ 2 - δ ^ 12) ≤
        ((⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hq : (1 - δ ^ 12) / (δ ^ 2 - δ ^ 12) * (δ ^ 2 - δ ^ 12) = 1 - δ ^ 12 :=
      div_mul_cancel₀ _ (ne_of_gt hδ2)
    have step1 : (1 - δ ^ 12) ≤ ((⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ : ℕ) : ℝ) *
        (δ ^ 2 - δ ^ 12) := by
      conv_lhs => rw [← hq]
      exact mul_le_mul_of_nonneg_right hceil (le_of_lt hδ2)
    have step2 : ((⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ : ℕ) : ℝ) * (δ ^ 2 - δ ^ 12) ≤
        ((⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2 : ℕ) : ℝ) * (δ ^ 2 - δ ^ 12) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hδ2)
      push_cast
      linarith
    linarith
  · subst h
    norm_num

/-- **The heart of Step 3**: two good quadruples at the same point with a large common prime
set have equal minimal modulus, congruent lattice parts and close frequencies. -/
lemma good_quad_pair (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : ℕ → ℂ} {cc C X L P₁ P₂ : ℝ} {ℓ : ℕ} {A : Work.BMF.ADIData k f cc C X L P₁ P₂ ℓ}
    {x T₁ T₂ : ℝ} {q₁ q₂ qf₁ qf₂ : ℕ} {γ₁ γ₂ : Polynomial ℝ} {Ps₁ Ps₂ : Finset ℕ}
    (hX : 0 < X) (hL1 : 1 ≤ L) (hLX : L ≤ X)
    (hQ₁ : Work.BMF.GoodQuad A δ x T₁ q₁ qf₁ γ₁ Ps₁)
    (hQ₂ : Work.BMF.GoodQuad A δ x T₂ q₂ qf₂ γ₂ Ps₂)
    (hinter : δ ^ 12 * Work.BMF.pi0 P₂ ≤ ((Ps₁ ∩ Ps₂).card : ℝ))
    (hbig : Work.BMF.PrimesBig k δ X P₂) :
    q₁ = q₂ ∧ Work.BMF.ModZConst γ₁ γ₂ ∧ |T₁ - T₂| ≤ 40 * Real.pi * δ⁻¹ * (X / L) := by
  have hX1 : 1 ≤ X := by
    have h1 : (1:ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast hQ₁.q_bound
    have h2 : (1:ℝ) ≤ X ^ (1/δ) := le_trans h1 hQ₁.q_le
    have h4 : (0:ℝ) < (1/δ) := by positivity
    have := (Real.rpow_le_rpow_iff (show (0:ℝ) ≤ 1 by norm_num) (le_of_lt hX) h4).mp
      (by simpa using h2)
    exact this
  have hx1 : X / 10 ≤ x := (A.isFam.1 x hQ₁.x_mem).1
  have hx2 : x + L ≤ 10 * X := (A.isFam.1 x hQ₁.x_mem).2
  have hx0 : 0 < x := by linarith
  -- an integer point in `[x, x+L]`
  set n : ℤ := ⌈x⌉ with hn
  have hn_ge : x ≤ (n:ℝ) := by rw [hn]; exact Int.le_ceil x
  have hn_lt : (n:ℝ) < x + 1 := by rw [hn]; exact Int.ceil_lt_add_one x
  have hn_le : (n:ℝ) ≤ x + L := by linarith
  have hn0 : 0 < (n:ℝ) := by linarith
  -- derivative relation at `n`
  have hder := deriv_relation_le (p := A.pol x) (γ₁ := γ₁) (γ₂ := γ₂)
    (c₁ := T₁/(2*Real.pi)) (c₂ := T₂/(2*Real.pi)) (A := δ⁻¹/L) (t := (n:ℝ)) hn0
    (hQ₁.decomp _ ⟨hn_ge, hn_le⟩) (hQ₂.decomp _ ⟨hn_ge, hn_le⟩)
  have hderB : |(γ₁ - γ₂).derivative.eval (n:ℝ) + (T₁ - T₂)/(2*Real.pi*(n:ℝ))| ≤ 2*(δ⁻¹/L) := by
    have hT1 : T₁/(2*Real.pi) - T₂/(2*Real.pi) = (T₁ - T₂)/(2*Real.pi) := by ring
    have hT2 : ((T₁ - T₂)/(2*Real.pi))/(n:ℝ) = (T₁ - T₂)/(2*Real.pi*(n:ℝ)) := by
      rw [div_div]
    rw [hT1, hT2] at hder
    exact hder
  have hBpos : (0:ℝ) < 2*Real.pi*(n:ℝ) := by positivity
  have hBval : |(T₁ - T₂)/(2*Real.pi*(n:ℝ))| = |T₁ - T₂|/(2*Real.pi*(n:ℝ)) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi*(n:ℝ))]
  have hBle : |(T₁ - T₂)/(2*Real.pi*(n:ℝ))| ≤ |T₁ - T₂|/(2*Real.pi*x) := by
    rw [hBval]
    refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    nlinarith [hn_ge, Real.pi_pos]
  have hG'one : |(γ₁ - γ₂).derivative.eval (n:ℝ)| ≤
      2*(δ⁻¹/L) + |(T₁ - T₂)/(2*Real.pi*(n:ℝ))| := by
    rw [abs_le] at hderB ⊢
    constructor <;> linarith [hderB.1, hderB.2,
      neg_abs_le ((T₁ - T₂)/(2*Real.pi*(n:ℝ))), le_abs_self ((T₁ - T₂)/(2*Real.pi*(n:ℝ)))]
  have hG'bound : |(γ₁ - γ₂).derivative.eval (n:ℝ)| ≤ 2*δ⁻¹/L + |T₁ - T₂|/(2*Real.pi*x) := by
    have h2 : 2*(δ⁻¹/L) = 2*δ⁻¹/L := by ring
    linarith [hG'one, hBle, h2]
  -- the lattice
  set Lc : ℕ := Nat.lcm qf₁ qf₂ with hLcdef
  set QQn : ℕ := ∏ p ∈ Ps₁ ∩ Ps₂, p with hQQdef
  have hQQpos : 0 < QQn := by
    rw [hQQdef]
    exact Finset.prod_pos (fun p hp => (hQ₁.primes p (Finset.mem_inter.mp hp).1).1.pos)
  have hLcpos : 0 < Lc := by
    rw [hLcdef]
    exact Nat.lcm_pos (by have := hQ₁.qf_bound; omega) (by have := hQ₂.qf_bound; omega)
  have hQQcast : Work.BMF.Qprod (Ps₁ ∩ Ps₂) = (QQn : ℝ) := by
    rw [hQQdef]
    simp only [Work.BMF.Qprod, Nat.cast_prod]
  have hbigQ : (k.factorial : ℝ) * (X ^ (1/δ)) ^ (2*k) *
      (2 * ((k:ℝ)+1) * δ⁻¹ * ((X ^ (1/δ)) ^ (k+1) + 1)) ≤ (QQn : ℝ) := by
    rw [← hQQcast]
    simpa only [mul_assoc] using
      hbig (Ps₁ ∩ Ps₂) (fun p hp => hQ₁.primes p (Finset.mem_inter.mp hp).1) hinter
  have hlcm_le : (Lc : ℝ) ≤ (X ^ (1/δ)) ^ 2 := by
    have h1 : Lc ≤ qf₁ * qf₂ := by
      rw [hLcdef]
      exact Nat.le_of_dvd (Nat.mul_pos (by have := hQ₁.qf_bound; omega)
        (by have := hQ₂.qf_bound; omega))
        (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
    have h2 : (qf₁:ℝ) ≤ X ^ (1/δ) := hQ₁.qf_le
    have h3 : (qf₂:ℝ) ≤ X ^ (1/δ) := hQ₂.qf_le
    have h4 : (0:ℝ) ≤ X ^ (1/δ) := Real.rpow_nonneg (le_of_lt hX) _
    calc (Lc:ℝ) ≤ ((qf₁ * qf₂ : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (qf₁:ℝ) * (qf₂:ℝ) := by push_cast; ring
      _ ≤ (X ^ (1/δ)) * (X ^ (1/δ)) := mul_le_mul h2 h3 (by positivity) h4
      _ = (X ^ (1/δ)) ^ 2 := by ring
  have hTdiff : |T₁ - T₂| ≤ 2 * δ⁻¹ * (X/L) ^ (k+1) := by
    have h1 := hQ₁.T_bound
    have h2 := hQ₂.T_bound
    calc |T₁ - T₂| ≤ |T₁| + |T₂| := abs_sub _ _
      _ ≤ δ⁻¹ * (X/L) ^ (k+1) + δ⁻¹ * (X/L) ^ (k+1) := add_le_add h1 h2
      _ = 2 * δ⁻¹ * (X/L) ^ (k+1) := by ring
  obtain ⟨hineq1, hineq2, hineq3, hineq4⟩ :=
    lattice_inequalities hk (δ := δ) (X := X) (L := L) (Lc := (Lc:ℝ)) (QQ := (QQn:ℝ))
      (x := x) (T := T₁ - T₂) hδ hδ1 hX1 hL1 hx1 (by exact_mod_cast hQQpos)
      (by exact_mod_cast hLcpos) hbigQ hlcm_le hTdiff
  have hLc1 : 1 ≤ Lc := hLcpos
  have hQQ1 : 1 ≤ QQn := hQQpos
  have hdeg₁ : γ₁.natDegree ≤ k :=
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hQ₁.deg)
  have hdeg₂ : γ₂.natDegree ≤ k :=
    Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hQ₂.deg)
  have hfine₁ : Work.BMF.IntegralOn ((Lc:ℝ)/Work.BMF.Qprod (Ps₁ ∩ Ps₂)) γ₁ := by
    have h' := IntegralOn_coarsen (s := Ps₁) (t := Ps₂) (a := qf₁) (b := qf₂) (γ := γ₁)
      (fun p hp => (hQ₁.primes p hp).1.pos) hQ₁.int_fine
    simpa only [hLcdef] using h'
  have hfine₂ : Work.BMF.IntegralOn ((Lc:ℝ)/Work.BMF.Qprod (Ps₁ ∩ Ps₂)) γ₂ := by
    have h' := IntegralOn_coarsen (s := Ps₂) (t := Ps₁) (a := qf₂) (b := qf₁) (γ := γ₂)
      (fun p hp => (hQ₂.primes p hp).1.pos) hQ₂.int_fine
    rw [Nat.lcm_comm, Finset.inter_comm] at h'
    simpa only [hLcdef] using h'
  have hintq₁ : Work.BMF.IntegralOn ((Lc:ℝ)/(QQn:ℝ)) γ₁ := by
    rw [← hQQcast]; exact hfine₁
  have hintq₂ : Work.BMF.IntegralOn ((Lc:ℝ)/(QQn:ℝ)) γ₂ := by
    rw [← hQQcast]; exact hfine₂
  obtain ⟨m₁, hm₁⟩ := lattice_deriv le_rfl hk (q := Lc) (Q := QQn) hLc1 hQQ1 hdeg₁ hintq₁ n
  obtain ⟨m₂, hm₂⟩ := lattice_deriv le_rfl hk (q := Lc) (Q := QQn) hLc1 hQQ1 hdeg₂ hintq₂ n
  have hfac : ((k.factorial : ℝ) * (Lc:ℝ)^k) ≠ 0 := by positivity
  have hev₁ : γ₁.derivative.eval (n:ℝ) =
      (m₁:ℝ) * ((QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k)) := by
    have h1 : ((k.factorial : ℝ) * (Lc:ℝ)^k / (QQn:ℝ)) * γ₁.derivative.eval (n:ℝ) = (m₁:ℝ) := by
      simpa using hm₁
    have h1b : γ₁.derivative.eval (n:ℝ) * ((k.factorial : ℝ) * (Lc:ℝ)^k) =
        (m₁:ℝ) * (QQn:ℝ) := by
      field_simp at h1
      linarith [h1]
    rw [mul_div_assoc', eq_div_iff hfac]
    exact h1b
  have hev₂ : γ₂.derivative.eval (n:ℝ) =
      (m₂:ℝ) * ((QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k)) := by
    have h1 : ((k.factorial : ℝ) * (Lc:ℝ)^k / (QQn:ℝ)) * γ₂.derivative.eval (n:ℝ) = (m₂:ℝ) := by
      simpa using hm₂
    have h1b : γ₂.derivative.eval (n:ℝ) * ((k.factorial : ℝ) * (Lc:ℝ)^k) =
        (m₂:ℝ) * (QQn:ℝ) := by
      field_simp at h1
      linarith [h1]
    rw [mul_div_assoc', eq_div_iff hfac]
    exact h1b
  have hDzpos : 0 < (QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k) := by positivity
  have hsum : (γ₁ - γ₂).derivative.eval (n:ℝ) =
      ((m₁ - m₂ : ℤ) : ℝ) * ((QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k)) := by
    rw [Polynomial.derivative_sub, Polynomial.eval_sub, hev₁, hev₂, Int.cast_sub]
    ring
  have hG'lt : |(γ₁ - γ₂).derivative.eval (n:ℝ)| <
      (QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k) := lt_of_le_of_lt hG'bound hineq1
  have hG'zero : (γ₁ - γ₂).derivative.eval (n:ℝ) = 0 := by
    by_contra hne
    have hmne : m₁ ≠ m₂ := by
      intro h
      exact hne (by rw [hsum, h, Int.cast_sub, sub_self, zero_mul])
    have hge1 : (1:ℝ) ≤ |↑(m₁ - m₂)| := by
      have h1 : (1:ℤ) ≤ |m₁ - m₂| := Int.one_le_abs (sub_ne_zero.mpr hmne)
      calc (1:ℝ) ≤ ((|m₁ - m₂| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |↑(m₁ - m₂)| := by rw [Int.cast_abs]
    have hge2 : (QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k) ≤
        |(γ₁ - γ₂).derivative.eval (n:ℝ)| := by
      rw [hsum, abs_mul, abs_of_pos hDzpos]
      calc (QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k) =
          1 * ((QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k)) := (one_mul _).symm
        _ ≤ |↑(m₁ - m₂)| * ((QQn:ℝ)/((k.factorial : ℝ) * (Lc:ℝ)^k)) :=
            mul_le_mul_of_nonneg_right hge1 (le_of_lt hDzpos)
    linarith [hG'lt, hge2]
  -- the frequency bound
  have hTfinal : |T₁ - T₂| ≤ 40 * Real.pi * δ⁻¹ * (X/L) := by
    have hBabs : |T₁ - T₂|/(2*Real.pi*(n:ℝ)) ≤ 2*(δ⁻¹/L) := by
      rw [hG'zero, zero_add, abs_div, abs_of_pos hBpos] at hderB
      exact hderB
    have h2 : |T₁ - T₂| ≤ 2*(δ⁻¹/L)*(2*Real.pi*(n:ℝ)) := by
      rw [div_le_iff₀ hBpos] at hBabs
      exact hBabs
    have hnle : (n:ℝ) ≤ 10*X := by linarith
    have hLpos : (0:ℝ) < L := by linarith
    have hLne : L ≠ 0 := ne_of_gt hLpos
    refine le_of_mul_le_mul_right ?_ hLpos
    have hdivL : (δ⁻¹/L) * L = δ⁻¹ := div_mul_cancel₀ _ hLne
    have e1 : 2*(δ⁻¹/L)*(2*Real.pi*(n:ℝ)) * L = 2*δ⁻¹*(2*Real.pi*(n:ℝ)) := by
      calc 2*(δ⁻¹/L)*(2*Real.pi*(n:ℝ)) * L = (δ⁻¹/L) * L * (2*(2*Real.pi*(n:ℝ))) := by ring
        _ = δ⁻¹ * (2*(2*Real.pi*(n:ℝ))) := by rw [hdivL]
        _ = 2*δ⁻¹*(2*Real.pi*(n:ℝ)) := by ring
    have e2 : 40*Real.pi*δ⁻¹*(X/L) * L = 40*Real.pi*δ⁻¹*X := by
      calc 40*Real.pi*δ⁻¹*(X/L) * L = (X/L) * L * (40*Real.pi*δ⁻¹) := by ring
        _ = X * (40*Real.pi*δ⁻¹) := by rw [div_mul_cancel₀ _ hLne]
        _ = 40*Real.pi*δ⁻¹*X := by ring
    calc |T₁ - T₂| * L ≤ (2*(δ⁻¹/L)*(2*Real.pi*(n:ℝ))) * L :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hLpos)
      _ = 2*δ⁻¹*(2*Real.pi*(n:ℝ)) := e1
      _ ≤ 40*Real.pi*δ⁻¹*X := by
          have k1 : 2*δ⁻¹*(2*Real.pi*(n:ℝ)) = (2*δ⁻¹*(2*Real.pi)) * (n:ℝ) := by ring
          have k2 : 40*Real.pi*δ⁻¹*X = (2*δ⁻¹*(2*Real.pi)) * (10*X) := by ring
          rw [k1, k2]
          exact mul_le_mul_of_nonneg_left (by linarith [hnle]) (by positivity)
      _ = (40 * Real.pi * δ⁻¹ * (X/L)) * L := e2.symm

  -- constancy of the lattice part
  have hbound : ∀ t ∈ Set.Icc x (x + L),
      |(γ₁ - γ₂).derivative.eval t| ≤ 2*δ⁻¹/L + |T₁ - T₂|/(2*Real.pi*x) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht0 : 0 < t := by linarith
    have hd := deriv_relation_le (p := A.pol x) (γ₁ := γ₁) (γ₂ := γ₂)
      (c₁ := T₁/(2*Real.pi)) (c₂ := T₂/(2*Real.pi)) (A := δ⁻¹/L) (t := t) ht0
      (hQ₁.decomp t ⟨ht1, ht2⟩) (hQ₂.decomp t ⟨ht1, ht2⟩)
    have hd' : |(γ₁ - γ₂).derivative.eval t + (T₁ - T₂)/(2*Real.pi*t)| ≤ 2*(δ⁻¹/L) := by
      have hT1 : T₁/(2*Real.pi) - T₂/(2*Real.pi) = (T₁ - T₂)/(2*Real.pi) := by ring
      have hT2 : ((T₁ - T₂)/(2*Real.pi))/t = (T₁ - T₂)/(2*Real.pi*t) := by rw [div_div]
      rw [hT1, hT2] at hd
      exact hd
    have hB2 : |(T₁ - T₂)/(2*Real.pi*t)| ≤ |T₁ - T₂|/(2*Real.pi*x) := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi*t)]
      refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
      nlinarith [ht1, Real.pi_pos]
    have hG2 : |(γ₁ - γ₂).derivative.eval t| ≤
        2*(δ⁻¹/L) + |(T₁ - T₂)/(2*Real.pi*t)| := by
      rw [abs_le] at hd' ⊢
      constructor <;> linarith [hd'.1, hd'.2,
        neg_abs_le ((T₁ - T₂)/(2*Real.pi*t)), le_abs_self ((T₁ - T₂)/(2*Real.pi*t))]
    have h2 : 2*(δ⁻¹/L) = 2*δ⁻¹/L := by ring
    calc |(γ₁ - γ₂).derivative.eval t| ≤ 2*(δ⁻¹/L) + |(T₁ - T₂)/(2*Real.pi*t)| := hG2
      _ ≤ 2*δ⁻¹/L + |T₁ - T₂|/(2*Real.pi*x) := by rw [h2]; exact add_le_add le_rfl hB2
  have hint : ∀ m : ℤ, ∃ z : ℤ, (γ₁ - γ₂).eval ((Lc:ℝ)/(QQn:ℝ) * m) = z := by
    intro m
    obtain ⟨z₁, hz₁⟩ := hintq₁ m
    obtain ⟨z₂, hz₂⟩ := hintq₂ m
    refine ⟨z₁ - z₂, ?_⟩
    rw [Polynomial.eval_sub, hz₁, hz₂]
    push_cast
    ring
  have hRpos : (0:ℝ) < (Lc:ℝ)/(QQn:ℝ) := by positivity
  have hdegG : (γ₁ - γ₂).natDegree ≤ k := by
    refine le_trans (Polynomial.natDegree_sub_le γ₁ γ₂) ?_
    exact max_le hdeg₁ hdeg₂
  obtain ⟨cstr, hcstr⟩ := const_of_lattice_const (k := k) (G := γ₁ - γ₂) (x := x) (L := L)
    (R := (Lc:ℝ)/(QQn:ℝ)) (A := 2*δ⁻¹/L + |T₁ - T₂|/(2*Real.pi*x))
    hL1 hRpos (by positivity) hineq3 hdegG hbound hineq4 hint
  have hmod : Work.BMF.ModZConst γ₁ γ₂ := ⟨cstr, sub_eq_iff_eq_add'.mp hcstr⟩
  have hmod' : γ₁ = γ₂ + Polynomial.C (cstr : ℝ) := sub_eq_iff_eq_add'.mp hcstr
  have hmod'' : γ₂ = γ₁ + Polynomial.C ((-cstr : ℤ) : ℝ) := by
    rw [hmod', Int.cast_neg, Polynomial.C_neg]
    ring
  -- the minimal moduli agree
  have hq : q₁ = q₂ := by
    refine le_antisymm ?_ ?_
    · refine hQ₁.minimal q₂ (by exact_mod_cast hQ₂.q_bound) ?_
      intro m
      obtain ⟨z, hz⟩ := hQ₂.int_coarse m
      refine ⟨z + cstr, ?_⟩
      rw [hmod', Polynomial.eval_add, Polynomial.eval_C, hz]
      push_cast
      ring
    · refine hQ₂.minimal q₁ (by exact_mod_cast hQ₁.q_bound) ?_
      intro m
      obtain ⟨z, hz⟩ := hQ₁.int_coarse m
      refine ⟨z - cstr, ?_⟩
      rw [hmod'', Polynomial.eval_add, Polynomial.eval_C, hz]
      push_cast
      ring
  exact ⟨hq, hmod, hTfinal⟩

/-- **Step 3 of MRTTZ §3 (Prop. 3.9)** -/
theorem local_finite (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (f : ℕ → ℂ) (c C X L P₁ P₂ : ℝ) (ℓ : ℕ) (A : Work.BMF.ADIData k f c C X L P₁ P₂ ℓ)
        (x : ℝ) (v : Fin K → (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)),
        0 < X → 1 ≤ L → L ≤ X →
        (∀ j : Fin K, Work.BMF.GoodQuad A δ x (v j).1 (v j).2.1 (v j).2.2.1 (v j).2.2.2.1 (v j).2.2.2.2) →
        Work.BMF.PrimesBig k δ X P₂ →
        ∃ j j' : Fin K, j ≠ j' ∧ (v j).2.1 = (v j').2.1 ∧
          Work.BMF.ModZConst (v j).2.2.2.1 (v j').2.2.2.1 ∧
          |(v j).1 - (v j').1| ≤ C₁ * (X / L) := by
  refine ⟨⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2, by omega, 40 * Real.pi * δ⁻¹,
    by positivity, ?_⟩
  intro f c C X L P₁ P₂ ℓ A x v hX hL1 hLX hquad hbig
  have hK2 : 2 ≤ ⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2 := by omega
  have hKδ := ceil_ratio_ge δ hδ hδ1
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have hconst : ∀ j : Fin (⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2),
        ∃ cj : ℤ, (v j).2.2.2.1 = Polynomial.C (cj : ℝ) := by
      intro j
      obtain ⟨z, hz⟩ := (hquad j).int_coarse (1 : ℤ)
      have hdeg0 : (v j).2.2.2.1.natDegree ≤ 0 :=
        Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp (hquad j).deg)
      have hC : (v j).2.2.2.1 = Polynomial.C ((v j).2.2.2.1.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero hdeg0
      have hz' : (v j).2.2.2.1.coeff 0 = (z : ℝ) := by
        rw [hC, Polynomial.eval_C] at hz
        simpa using hz
      exact ⟨z, hC.trans (by rw [hz'])⟩
    have hqone : ∀ j : Fin (⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2), (v j).2.1 = 1 := by
      intro j
      refine le_antisymm ?_ (hquad j).q_bound
      refine (hquad j).minimal 1 le_rfl ?_
      obtain ⟨z, hz⟩ := hconst j
      intro m
      refine ⟨z, ?_⟩
      rw [hz]
      simp
    have hTb : ∀ j : Fin (⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2),
        |(v j).1| ≤ δ⁻¹ * (X / L) := by
      intro j
      have h1 := (hquad j).T_bound
      rwa [pow_one] at h1
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp, ?_, ?_, ?_⟩
    · rw [hqone ⟨0, by omega⟩, hqone ⟨1, by omega⟩]
    · obtain ⟨z₁, hz₁⟩ := hconst ⟨0, by omega⟩
      obtain ⟨z₂, hz₂⟩ := hconst ⟨1, by omega⟩
      refine ⟨z₁ - z₂, ?_⟩
      rw [hz₁, hz₂, ← Polynomial.C_add]
      congr 1
      push_cast
      ring
    · have h1 := hTb ⟨0, by omega⟩
      have h2 := hTb ⟨1, by omega⟩
      have hXR : 0 ≤ X / L := by positivity
      have hd : 0 < δ⁻¹ := by positivity
      have hp : (2:ℝ) ≤ 40 * Real.pi := by have := Real.pi_gt_three; linarith
      calc |(v ⟨0, by omega⟩).1 - (v ⟨1, by omega⟩).1|
          ≤ |(v ⟨0, by omega⟩).1| + |(v ⟨1, by omega⟩).1| := abs_sub _ _
        _ ≤ δ⁻¹ * (X/L) + δ⁻¹ * (X/L) := add_le_add h1 h2
        _ ≤ 40 * Real.pi * δ⁻¹ * (X/L) := by
            have := mul_nonneg (le_of_lt hd) hXR
            nlinarith [hp, this]
  · obtain ⟨j, j', hne, hinter⟩ :=
      exists_pair_inter_ge δ P₂ hδ hδ1 (⌈(1 - δ ^ 12) / (δ ^ 2 - δ ^ 12)⌉₊ + 2) hK2 hKδ
        (fun P hP => primesIn_half_card_le_pi0 P hP)
        (fun i => (v i).2.2.2.2)
        (fun i p hp => (hquad i).primes p hp)
        (fun i => (hquad i).card)
    obtain ⟨hqeq, hmod, hTle⟩ :=
      good_quad_pair k hk δ hδ hδ1 hX hL1 hLX (hquad j) (hquad j') hinter hbig
    exact ⟨j, j', hne, hqeq, hmod, hTle⟩

end Work.N8

import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg
import Submission.Work.WilC4aP.DescentDefs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators Topology

namespace Work.WilC4aP

open Polynomial

/-- The coefficient of the fibre is the evaluation of the coefficient function. -/
lemma Pz_coeff (P : Polynomial (ℂ → ℂ)) (z : ℂ) (i : ℕ) :
    (Pz P z).coeff i = (P.coeff i) z := by
  simp [Pz]

/-- Precomposition with the ramification `t ↦ t ^ q` of an eventual factorization. -/
lemma eventuallyEq_comp_pow {f g : ℂ → ℂ} {k q : ℕ} (hq : 0 < q)
    (h : f =ᶠ[𝓝 (0:ℂ)] fun z => z ^ k * g z) :
    (fun t : ℂ => f (t ^ q)) =ᶠ[𝓝 (0:ℂ)] fun t => t ^ (q * k) * g (t ^ q) := by
  have hcont : Tendsto (fun t : ℂ => t ^ q) (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by
    simpa [zero_pow hq.ne'] using ((continuous_pow q).continuousAt (x := (0:ℂ))).tendsto
  have h' : (fun t : ℂ => f (t ^ q)) =ᶠ[𝓝 (0:ℂ)] fun t => (t ^ q) ^ k * g (t ^ q) :=
    Filter.EventuallyEq.comp_tendsto h hcont
  filter_upwards [h'] with t ht
  rw [ht, pow_mul]

/-- **The Newton-polygon (rescaling) step of the descent, in fibre form.**

`P` is monic of degree `m ≥ 2` with holomorphic coefficients, `Pz P 0 = X ^ m`, the
`X ^ (m-1)`-coefficient of `P` vanishes and some lower coefficient is not identically zero.
Then there are a ramification `q > 0`, a scaling `a > 0` and a monic `Q` of degree `m` with
holomorphic coefficients, whose fibre at `0` has vanishing `X ^ (m-1)`-coefficient but a
non-vanishing lower coefficient, such that the substitution identity
`P(t ^ q, t ^ a * W) = t ^ (a * m) * Q(t, W)` holds in a neighbourhood of `t = 0`. -/
theorem newton_step {m : ℕ} (hm : 2 ≤ m) {P : Polynomial (ℂ → ℂ)} (hmon : P.Monic)
    (hdeg : P.natDegree = m) (hhol : HolCoeffs P 0) (h0 : Pz P 0 = Polynomial.X ^ m)
    (hsub : P.coeff (m - 1) = 0)
    (hex : ∃ i < m, analyticOrderAt (P.coeff i) 0 ≠ ⊤) :
    ∃ (q a : ℕ) (Q : Polynomial (ℂ → ℂ)) (ρ : ℝ), 0 < q ∧ 0 < a ∧ 0 < ρ ∧
      Q.Monic ∧ Q.natDegree = m ∧ HolCoeffs Q 0 ∧
      (Pz Q 0).coeff (m - 1) = 0 ∧
      (∃ i₀ < m, (Pz Q 0).coeff i₀ ≠ 0) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) ρ,
        (Pz P (t ^ q)).comp (Polynomial.C (t ^ a) * Polynomial.X) =
          Polynomial.C (t ^ (a * m)) * Pz Q t := by
  classical
  -- ## 0. Elementary facts about the coefficients of `P`
  have hcoeff0 : ∀ i, i < m → P.coeff i 0 = 0 := by
    intro i hi
    have h : (P.coeff i) 0 = (Polynomial.X ^ m : Polynomial ℂ).coeff i := by
      rw [← Pz_coeff P 0 i, h0]
    simpa [Polynomial.coeff_X_pow, Nat.ne_of_lt hi] using h
  have hcoeffm : P.coeff m = 1 := by
    rw [← hdeg]; exact hmon.coeff_natDegree
  have hcoeffgt : ∀ j, m < j → P.coeff j = 0 := fun j hj =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hj)
  -- ## 1. The non-trivial lower coefficients and the Newton slope
  set v : Fin m → ℕ := fun i => analyticOrderNatAt (P.coeff (i:ℕ)) 0 with hvdef
  set J : Finset (Fin m) :=
    Finset.univ.filter (fun i => analyticOrderAt (P.coeff (i:ℕ)) 0 ≠ ⊤) with hJdef
  have hJmem : ∀ i : Fin m, i ∈ J ↔ analyticOrderAt (P.coeff (i:ℕ)) 0 ≠ ⊤ := by
    intro i; rw [hJdef]; simp
  have hJne : J.Nonempty := by
    obtain ⟨i, hi, hne⟩ := hex
    exact ⟨⟨i, hi⟩, (hJmem ⟨i, hi⟩).mpr hne⟩
  obtain ⟨i₀, hi₀J, hi₀min⟩ :=
    Finset.exists_min_image J (fun i => ((v i : ℚ) / ((m - (i:ℕ) : ℕ) : ℚ))) hJne
  set a : ℕ := v i₀ with hadef
  set q : ℕ := m - (i₀:ℕ) with hqdef
  have hmsub_pos : ∀ i : Fin m, 0 < m - (i:ℕ) := fun i => by have := i.isLt; omega
  have hqpos : 0 < q := by rw [hqdef]; exact hmsub_pos i₀
  have hmin : ∀ i ∈ J, a * (m - (i:ℕ)) ≤ q * v i := by
    intro i hi
    have hle := hi₀min i hi
    have h1 : (0:ℚ) < ((m - (i₀:ℕ) : ℕ) : ℚ) := by exact_mod_cast hmsub_pos i₀
    have h2 : (0:ℚ) < ((m - (i:ℕ) : ℕ) : ℚ) := by exact_mod_cast hmsub_pos i
    rw [div_le_div_iff₀ h1 h2] at hle
    have hnat : v i₀ * (m - (i:ℕ)) ≤ v i * (m - (i₀:ℕ)) := by exact_mod_cast hle
    rw [hadef, hqdef, Nat.mul_comm (m - (i₀:ℕ)) (v i)]
    exact hnat
  -- ## 2. Non-vanishing factor of every relevant coefficient
  have hfac : ∀ i : Fin m, i ∈ J → ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
      P.coeff (i:ℕ) =ᶠ[𝓝 (0:ℂ)] fun t => t ^ (v i) * g t := by
    intro i hi
    have hne : analyticOrderAt (P.coeff (i:ℕ)) 0 ≠ ⊤ := (hJmem i).mp hi
    obtain ⟨g, hg, hg0, hgf⟩ := (hhol (i:ℕ)).analyticOrderAt_ne_top.mp hne
    refine ⟨g, hg, hg0, ?_⟩
    filter_upwards [hgf] with t ht
    rw [ht]
    simp [hvdef, sub_zero, smul_eq_mul]
  choose Gf hGf_an hGf_0 hGf_fac using hfac
  -- ## 3. The rescaled coefficients `Gm i`
  set Gm : Fin m → ℂ → ℂ := fun i =>
      if hi : i ∈ J then
        (fun t : ℂ => t ^ (q * v i - a * (m - (i:ℕ))) * Gf i hi (t ^ q))
      else 0 with hGmdef
  have hGmval : ∀ (i : Fin m) (hi : i ∈ J),
      Gm i = fun t : ℂ => t ^ (q * v i - a * (m - (i:ℕ))) * Gf i hi (t ^ q) := by
    intro i hi
    rw [hGmdef]
    exact dif_pos hi
  have hGmneg : ∀ (i : Fin m), i ∉ J → Gm i = 0 := by
    intro i hi
    rw [hGmdef]
    exact dif_neg hi
  have hGm_an : ∀ i : Fin m, AnalyticAt ℂ (Gm i) 0 := by
    intro i
    by_cases hi : i ∈ J
    · rw [hGmval i hi]
      exact (analyticAt_id.pow _).mul (AnalyticAt.comp_pow' (hGf_an i hi) hqpos)
    · rw [hGmneg i hi]
      exact analyticAt_const
  -- the key factorization, for `i ∈ J`
  have hGm_fac : ∀ (i : Fin m) (hi : i ∈ J),
      (fun t : ℂ => (P.coeff (i:ℕ)) (t ^ q)) =ᶠ[𝓝 (0:ℂ)]
        fun t => t ^ (a * (m - (i:ℕ))) * Gm i t := by
    intro i hi
    have hcomp := eventuallyEq_comp_pow (f := P.coeff (i:ℕ)) (g := Gf i hi) (k := v i)
      hqpos (hGf_fac i hi)
    have hle : a * (m - (i:ℕ)) ≤ q * v i := hmin i hi
    have hexp : a * (m - (i:ℕ)) + (q * v i - a * (m - (i:ℕ))) = q * v i :=
      Nat.add_sub_of_le hle
    refine hcomp.trans ?_
    filter_upwards with t
    rw [hGmval i hi, ← mul_assoc, ← pow_add, hexp]
  -- ## 4. The rescaled polynomial `Q`
  set Qcf : ℕ → ℂ → ℂ := fun j =>
      if j = m then (1 : ℂ → ℂ) else if hj : j < m then Gm ⟨j, hj⟩ else 0 with hQcfdef
  have hQcfm : Qcf m = 1 := by simp [hQcfdef]
  have hQcflt : ∀ (j : ℕ) (hj : j < m), Qcf j = Gm ⟨j, hj⟩ := by
    intro j hj
    simp [hQcfdef, Nat.ne_of_lt hj, hj]
  have hQcfgt : ∀ j, m < j → Qcf j = 0 := by
    intro j hj
    simp [hQcfdef, show j ≠ m by omega, show ¬ j < m by omega]
  set Q : Polynomial (ℂ → ℂ) :=
      ∑ j ∈ Finset.range (m + 1), Polynomial.C (Qcf j) * Polynomial.X ^ j with hQdef
  have hQcoeff : ∀ j : ℕ, Q.coeff j = if j ≤ m then Qcf j else 0 := by
    intro j
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have hQcoeff_le : ∀ j, j ≤ m → Q.coeff j = Qcf j := by
    intro j hj; rw [hQcoeff j]; simp [hj]
  have hQcoeff_gt : ∀ j, m < j → Q.coeff j = 0 := by
    intro j hj; rw [hQcoeff j]; simp [show ¬ j ≤ m by omega]
  -- ## 5. Basic properties of `Q`
  have hQdeg_le : Q.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hQcoeff_gt N hN]
  have hQdeg : Q.natDegree = m :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hQdeg_le
      (by rw [hQcoeff_le m le_rfl, hQcfm]; exact one_ne_zero)
  have hQmon : Q.Monic := by
    rw [Polynomial.Monic.def, ← Polynomial.coeff_natDegree, hQdeg, hQcoeff_le m le_rfl, hQcfm]
  have hQhol : HolCoeffs Q 0 := by
    unfold HolCoeffs
    intro j
    by_cases hj : j ≤ m
    · have hana : AnalyticAt ℂ (Qcf j) 0 := by
        by_cases hjm : j = m
        · rw [hjm, hQcfm]; exact analyticAt_const
        · have hjlt : j < m := lt_of_le_of_ne hj hjm
          rw [hQcflt j hjlt]
          exact hGm_an ⟨j, hjlt⟩
      rw [hQcoeff_le j hj]
      exact hana
    · simp only [not_le] at hj
      rw [hQcoeff_gt j hj]
      exact analyticAt_const
  -- ## 6. The conditions on the fibre `Pz Q 0`
  have hQsub : (Pz Q 0).coeff (m - 1) = 0 := by
    rw [Pz_coeff, hQcoeff_le (m - 1) (by omega)]
    have hm1 : m - 1 < m := by omega
    have hnotJ : (⟨m - 1, hm1⟩ : Fin m) ∉ J := by
      rw [hJmem]
      have hc : P.coeff ((⟨m - 1, hm1⟩ : Fin m) : ℕ) = 0 := by
        have : ((⟨m - 1, hm1⟩ : Fin m) : ℕ) = m - 1 := rfl
        rw [this]; exact hsub
      rw [hc, analyticOrderAt_zero]
      simp
    rw [hQcflt (m - 1) hm1, hGmneg _ hnotJ]
    simp
  have hQnz : ∃ j < m, (Pz Q 0).coeff j ≠ 0 := by
    refine ⟨(i₀:ℕ), i₀.isLt, ?_⟩
    have hexp : q * v i₀ - a * (m - (i₀:ℕ)) = 0 := by
      rw [hadef, hqdef, Nat.mul_comm (m - (i₀:ℕ)) (v i₀)]
      omega
    rw [Pz_coeff, hQcoeff_le (i₀:ℕ) (le_of_lt i₀.isLt), hQcflt (i₀:ℕ) i₀.isLt,
      hGmval i₀ hi₀J]
    simp only [hexp, pow_zero, one_mul, zero_pow hqpos.ne']
    exact hGf_0 i₀ hi₀J
  -- ## 7. positivity of `a`
  have hne0 : analyticOrderAt (P.coeff (i₀:ℕ)) 0 ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hhol (i₀:ℕ), hcoeff0 (i₀:ℕ) i₀.isLt⟩
  have hapos : 0 < a := by
    rw [hadef, hvdef]
    have hne : analyticOrderAt (P.coeff (i₀:ℕ)) 0 ≠ ⊤ := (hJmem i₀).mp hi₀J
    have hcast : ((analyticOrderNatAt (P.coeff (i₀:ℕ)) 0 : ℕ) : ℕ∞)
        = analyticOrderAt (P.coeff (i₀:ℕ)) 0 := Nat.cast_analyticOrderNatAt hne
    by_contra h
    have hn : analyticOrderNatAt (P.coeff (i₀:ℕ)) 0 = 0 := Nat.eq_zero_of_not_pos h
    rw [hn] at hcast
    simp at hcast
    exact hne0 hcast.symm
  -- ## 8. The substitution identity near `t = 0`
  have hkey_fin : ∀ j, j ≤ m →
      (fun t : ℂ => (P.coeff j) (t ^ q)) =ᶠ[𝓝 (0:ℂ)]
        fun t => t ^ (a * (m - j)) * Qcf j t := by
    intro j hj
    rcases eq_or_lt_of_le hj with hjm | hjlt
    · subst hjm
      filter_upwards with t
      simp [hcoeffm, hQcfm]
    · have hQcfj : Qcf j = Gm ⟨j, hjlt⟩ := hQcflt j hjlt
      by_cases hJ : (⟨j, hjlt⟩ : Fin m) ∈ J
      · have hb := hGm_fac ⟨j, hjlt⟩ hJ
        rw [hQcfj]
        exact hb
      · have htop : analyticOrderAt (P.coeff j) 0 = ⊤ := by
          by_contra h
          exact hJ ((hJmem ⟨j, hjlt⟩).mpr h)
        have hz : P.coeff j =ᶠ[𝓝 (0:ℂ)] fun _ => (0:ℂ) := analyticOrderAt_eq_top.mp htop
        have hGm0 : Gm ⟨j, hjlt⟩ = 0 := hGmneg _ hJ
        have hcontq : Tendsto (fun t : ℂ => t ^ q) (𝓝 (0:ℂ)) (𝓝 (0:ℂ)) := by
          simpa [zero_pow hqpos.ne'] using ((continuous_pow q).continuousAt (x := (0:ℂ))).tendsto
        have hcomp : (fun t : ℂ => (P.coeff j) (t ^ q)) =ᶠ[𝓝 (0:ℂ)] fun _ => (0:ℂ) :=
          Filter.EventuallyEq.comp_tendsto hz hcontq
        rw [hQcfj, hGm0]
        refine hcomp.trans ?_
        filter_upwards with t
        simp
  have hfinal : ∀ᶠ t in 𝓝 (0:ℂ),
      (Pz P (t ^ q)).comp (Polynomial.C (t ^ a) * Polynomial.X) =
        Polynomial.C (t ^ (a * m)) * Pz Q t := by
    have hfin : ∀ᶠ t in 𝓝 (0:ℂ), ∀ j ∈ Finset.range (m + 1),
        (P.coeff j) (t ^ q) = t ^ (a * (m - j)) * Qcf j t := by
      rw [Finset.eventually_all]
      intro j hj
      refine hkey_fin j ?_
      have := hj; simp only [Finset.mem_range] at this; omega
    filter_upwards [hfin] with t ht
    have hti : ∀ i ≤ m, (P.coeff i) (t ^ q) = t ^ (a * (m - i)) * Qcf i t := by
      intro i hi
      exact ht i (by simp only [Finset.mem_range]; omega)
    refine Polynomial.ext fun i => ?_
    by_cases hi : i ≤ m
    · have hti := ht i (by simp only [Finset.mem_range]; omega)
      have h1 : (m - i) + i = m := by omega
      have hL : ((Pz P (t ^ q)).comp (Polynomial.C (t ^ a) * Polynomial.X)).coeff i
          = t ^ (a * (m - i)) * Qcf i t * (t ^ a) ^ i := by
        rw [coeff_comp_C_mul_X, Pz_coeff, hti]
      have hR : (Polynomial.C (t ^ (a * m)) * Pz Q t).coeff i
          = t ^ (a * m) * Qcf i t := by
        rw [Polynomial.coeff_C_mul, Pz_coeff, hQcoeff_le i hi]
      rw [hL, hR, ← pow_mul]
      rw [mul_assoc, mul_comm (Qcf i t), ← mul_assoc, ← pow_add, ← mul_add, h1]
    · simp only [not_le] at hi
      have hL : ((Pz P (t ^ q)).comp (Polynomial.C (t ^ a) * Polynomial.X)).coeff i = 0 := by
        rw [coeff_comp_C_mul_X, Pz_coeff, hcoeffgt i hi]
        simp
      have hR : (Polynomial.C (t ^ (a * m)) * Pz Q t).coeff i = 0 := by
        rw [Polynomial.coeff_C_mul, Pz_coeff, hQcoeff_gt i hi]
        simp
      rw [hL, hR]
  obtain ⟨s, hs_mem, hs⟩ := hfinal.exists_mem
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hs_mem
  exact ⟨q, a, Q, ρ, hqpos, hapos, hρpos, hQmon, hQdeg, hQhol, hQsub, hQnz,
    fun t ht => hs t (hρsub ht)⟩

end Work.WilC4aP

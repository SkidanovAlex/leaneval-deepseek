import Mathlib

/-!
# Lower bound for the Mertens-type sum `Σ_{δ ≤ M} μ(δ)²/φ(δ)`

We prove, elementarily and without any prime number theorem, that there is an absolute
constant `C > 0` with `Real.log M - C ≤ Σ_{δ ≤ M} μ(δ)²/φ(δ)` for every `M ≥ 1`.  In fact the
sharper inequality `Real.log M ≤ Σ_{δ ≤ M} μ(δ)²/φ(δ)` holds, so that `C = 1` works.

The route is the classical one.  Since `μ(δ)²/φ(δ)` equals `1/φ(δ)` for squarefree `δ` and `0`
otherwise,

`Σ_{d ≤ M} 1/d = Σ_{u squarefree ≤ M} Σ_{d ≤ M, rad d = u} 1/d`,

and the *fibre bound* `Σ_{d ≤ M, rad d = u} 1/d ≤ 1/φ(u)` (for squarefree `u`) is the heart of
the argument.  Writing `d = u·m` with `rad m ∣ u`, it follows from

`Tsum u N := Σ_{m ≤ N, rad m ∣ u} 1/m ≤ u/φ(u)`,

proved by strong induction on `u` (with an inner strong induction on `N`): splitting the terms of
`Tsum u N` according to whether `p ∣ m`, where `p` is a prime with `p ∣ u` and `u = p·u'`, gives
`Tsum u N ≤ (1/p)·Tsum u (N/p) + Tsum u' N ≤ (1/p)(u/φ(u)) + u'/φ(u') = u/φ(u)`.
Finally `Real.log M ≤ Σ_{d ≤ M} 1/d` is the harmonic comparison.
-/

open Finset BigOperators
open UniqueFactorizationMonoid

namespace Work.ZeroDensity.Jutila

noncomputable section

private lemma squarefree_ne_zero {n : ℕ} (h : Squarefree n) : n ≠ 0 := by
  rintro rfl
  exact (Nat.squarefree_iff_prime_squarefree.mp h) 2 Nat.prime_two (show 2 * 2 ∣ 0 from ⟨0, rfl⟩)

/-- For a prime `p`, divisibility of `radical (p * b)` by `u` splits into the two conditions
`p ∣ u` and `radical b ∣ u`. -/
private lemma radical_mul_prime_dvd_iff {p b u : ℕ} (hp : p.Prime) (hu0 : u ≠ 0)
    (hb0 : b ≠ 0) : radical (p * b) ∣ u ↔ p ∣ u ∧ radical b ∣ u := by
  have key : (p * b).primeFactors = {p} ∪ b.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hb0, hp.primeFactors]
  rw [Nat.radical_dvd_iff hu0, Nat.radical_dvd_iff hu0, key]
  constructor
  · intro h1
    refine ⟨?_, fun q hq => h1 (Finset.mem_union.mpr (Or.inr hq))⟩
    have h2 : p ∈ u.primeFactors :=
      h1 (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self p)))
    exact (Nat.mem_primeFactors.mp h2).2.1
  · rintro ⟨hpdu, h2⟩ q hq
    rcases Finset.mem_union.mp hq with hq' | hq'
    · rw [Finset.mem_singleton] at hq'
      subst hq'
      exact Nat.mem_primeFactors.mpr ⟨hp, hpdu, hu0⟩
    · exact h2 hq'

/-- `Tsum u N = Σ_{m ≤ N, rad m ∣ u} 1/m`. -/
private noncomputable def Tsum (u N : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m ∣ u), (1 : ℝ) / (m : ℝ)

/-- The part of `Tsum u N` with `p ∣ m`, for a prime `p ∣ u`, equals `(1/p)·Tsum u (N/p)`. -/
private lemma Tsum_pdvd_part (p u N : ℕ) (hp : p.Prime) (hpu : p ∣ u) (hu0 : u ≠ 0) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m ∣ u ∧ p ∣ m), (1 : ℝ) / (m : ℝ))
      = (p : ℝ)⁻¹ * Tsum u (N / p) := by
  rw [Tsum, Finset.mul_sum]
  refine Finset.sum_bij (fun m _ => m / p) ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmIcc, hrad, hpm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmIcc
    have hm0 : m ≠ 0 := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hmN⟩, ?_⟩
    · rw [Nat.one_le_div_iff hp.pos]
      exact Nat.le_of_dvd (by omega) hpm
    · exact (radical_dvd_radical (Nat.div_dvd_of_dvd hpm) hm0).trans hrad
  · intro m₁ hm₁ m₂ hm₂ heq
    have h1 : p ∣ m₁ := (Finset.mem_filter.mp hm₁).2.2
    have h2 : p ∣ m₂ := (Finset.mem_filter.mp hm₂).2.2
    rw [← Nat.mul_div_cancel' h1, heq, Nat.mul_div_cancel' h2]
  · intro b hb
    obtain ⟨hbIcc, hbrad⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbIcc
    have hb0 : b ≠ 0 := by omega
    refine ⟨p * b, ?_, ?_⟩
    · refine Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos (by omega), ?_⟩, ?_, dvd_mul_right p b⟩
      · calc p * b ≤ p * (N / p) := Nat.mul_le_mul_left p hbN
          _ ≤ N := Nat.mul_div_le N p
      · exact (radical_mul_prime_dvd_iff hp hu0 hb0).mpr ⟨hpu, hbrad⟩
    · exact Nat.mul_div_right b hp.pos
  · intro m hm
    have hpm : p ∣ m := (Finset.mem_filter.mp hm).2.2
    have hcast : (m : ℝ) = (p : ℝ) * ((m / p : ℕ) : ℝ) := by
      calc (m : ℝ) = ((p * (m / p) : ℕ) : ℝ) := by rw [Nat.mul_div_cancel' hpm]
        _ = (p : ℝ) * ((m / p : ℕ) : ℝ) := by rw [Nat.cast_mul]
    rw [hcast, one_div, one_div]
    exact mul_inv _ _

/-- The part of `Tsum u N` with `¬ p ∣ m`, where `u = p·u'`, is at most `Tsum u' N`. -/
private lemma Tsum_not_pdvd_part (p u u' N : ℕ) (hp : p.Prime) (hpu : p * u' = u)
    (hu'0 : u' ≠ 0) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m ∣ u ∧ ¬ p ∣ m), (1 : ℝ) / (m : ℝ))
      ≤ Tsum u' N := by
  rw [Tsum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
  intro m hm
  obtain ⟨hmIcc, hrad, hnp⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmIcc
  have hu0 : u ≠ 0 := by rw [← hpu]; exact mul_ne_zero hp.ne_zero hu'0
  have hpnot : p ∉ m.primeFactors := fun h => hnp (Nat.mem_primeFactors.mp h).2.1
  have hsub : m.primeFactors ⊆ u'.primeFactors := by
    have h1 : m.primeFactors ⊆ u.primeFactors := (Nat.radical_dvd_iff hu0).mp hrad
    have h2 : u.primeFactors = {p} ∪ u'.primeFactors := by
      rw [← hpu, Nat.primeFactors_mul hp.ne_zero hu'0, hp.primeFactors]
    intro q hq
    have h3 := h1 hq
    rw [h2, Finset.mem_union, Finset.mem_singleton] at h3
    rcases h3 with h3 | h3
    · exact absurd (h3 ▸ hq) hpnot
    · exact h3
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩, (Nat.radical_dvd_iff hu'0).mpr hsub⟩

/-- **The `Tsum` bound**: `Σ_{m ≤ N, rad m ∣ u} 1/m ≤ u/φ(u)` for squarefree `u`. -/
private lemma Tsum_le : ∀ (u : ℕ), Squarefree u → ∀ N : ℕ,
    Tsum u N ≤ (u : ℝ) / (Nat.totient u : ℝ) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu N
    by_cases hu1 : u = 1
    · subst hu1
      rw [Tsum, Nat.totient_one, Nat.cast_one, div_one]
      have hsub : (Finset.Icc 1 N).filter (fun m => radical m ∣ 1) ⊆ ({1} : Finset ℕ) := by
        intro m hm
        obtain ⟨hmIcc, hrad⟩ := Finset.mem_filter.mp hm
        have hm1 : m ≤ 1 := Nat.radical_le_one_iff.mp (Nat.le_of_dvd one_pos hrad)
        exact Finset.mem_singleton.mpr (le_antisymm hm1 (Finset.mem_Icc.mp hmIcc).1)
      calc (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m ∣ 1), (1 : ℝ) / (m : ℝ))
          ≤ ∑ m ∈ ({1} : Finset ℕ), (1 : ℝ) / (m : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
        _ = 1 := by simp
    · obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd hu1
      have hu0 : u ≠ 0 := squarefree_ne_zero hu
      set u' := u / p with hu'_def
      have hmul : p * u' = u := Nat.mul_div_cancel' hpu
      have hu'0 : u' ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hmul
        exact hu0 hmul.symm
      have hu'lt : u' < u := by
        rw [← hmul]
        calc u' = 1 * u' := (one_mul u').symm
          _ < p * u' := Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hu'0)
      have hsq' : Squarefree u' := Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpu) hu
      have hpndvd : ¬ p ∣ u' := by
        intro hpd
        obtain ⟨k, hk⟩ := hpd
        have hpp : p * p ∣ u := ⟨k, by rw [← hmul, hk]; ring⟩
        exact (Nat.squarefree_iff_prime_squarefree.mp hu) p hp hpp
      have hcop : p.Coprime u' := hp.coprime_iff_not_dvd.mpr hpndvd
      have hphi : (Nat.totient u : ℝ) = ((p : ℝ) - 1) * (Nat.totient u' : ℝ) := by
        have h1 : Nat.totient u = (p - 1) * Nat.totient u' := by
          rw [← hmul, Nat.totient_mul hcop, Nat.totient_prime hp]
        rw [h1, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
      have huc : (u : ℝ) = (p : ℝ) * (u' : ℝ) := by rw [← hmul, Nat.cast_mul]
      have key : Tsum u N ≤ (u : ℝ) / (Nat.totient u : ℝ) := by
        induction N using Nat.strong_induction_on with
        | _ N ihN =>
          rcases Nat.eq_zero_or_pos N with hN0 | hNpos
          · subst hN0
            have hempty : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by simp
            rw [Tsum, hempty, Finset.filter_empty, Finset.sum_empty]
            exact div_nonneg (Nat.cast_nonneg u) (Nat.cast_nonneg _)
          · have hsplit : Tsum u N =
                (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m ∣ u ∧ p ∣ m),
                    (1 : ℝ) / (m : ℝ))
              + (∑ m ∈ (Finset.Icc 1 N).filter (fun m => radical m ∣ u ∧ ¬ p ∣ m),
                    (1 : ℝ) / (m : ℝ)) := by
              simp only [Tsum, Finset.sum_filter]
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun a _ => by
                by_cases hr : radical a ∣ u <;> by_cases hp' : p ∣ a <;> simp [hr, hp'])
            have hA := Tsum_pdvd_part p u N hp hpu hu0
            have hB := Tsum_not_pdvd_part p u u' N hp hmul hu'0
            have hrec : Tsum u (N / p) ≤ (u : ℝ) / (Nat.totient u : ℝ) :=
              ihN (N / p) (Nat.div_lt_self hNpos hp.one_lt)
            have hrec' : Tsum u' N ≤ (u' : ℝ) / (Nat.totient u' : ℝ) := ih u' hu'lt hsq' N
            have hstep1 : Tsum u N ≤ (p : ℝ)⁻¹ * Tsum u (N / p) + Tsum u' N := by
              rw [hsplit, hA]
              linarith [hB]
            have hstep2 : (p : ℝ)⁻¹ * Tsum u (N / p) + Tsum u' N
                ≤ (p : ℝ)⁻¹ * ((u : ℝ) / (Nat.totient u : ℝ))
                  + (u' : ℝ) / (Nat.totient u' : ℝ) :=
              add_le_add (mul_le_mul_of_nonneg_left hrec (by positivity)) hrec'
            have harith : (p : ℝ)⁻¹ * ((u : ℝ) / (Nat.totient u : ℝ))
                  + (u' : ℝ) / (Nat.totient u' : ℝ) = (u : ℝ) / (Nat.totient u : ℝ) := by
              have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
              have hp1 : (p : ℝ) - 1 ≠ 0 := by
                have h2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
                linarith
              have ht0 : (Nat.totient u' : ℝ) ≠ 0 := by
                exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hu'0)).ne'
              rw [huc, hphi]
              field_simp
              ring
            linarith [hstep1, hstep2, harith]
      exact key

/-- **The fibre bound**: `Σ_{d ≤ M, rad d = u} 1/d ≤ 1/φ(u)` for squarefree `u`. -/
private lemma fibre_sum_le (M u : ℕ) (hu : Squarefree u) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d => radical d = u), (1 : ℝ) / (d : ℝ))
      ≤ 1 / (Nat.totient u : ℝ) := by
  have hu0 : u ≠ 0 := squarefree_ne_zero hu
  have hupos : 0 < u := Nat.pos_of_ne_zero hu0
  set s := (Finset.Icc 1 M).filter (fun d => radical d = u) with hs
  have hdiv : ∀ d ∈ s, u ∣ d := by
    intro d hd
    have h1 : radical d = u := (Finset.mem_filter.mp hd).2
    rw [← h1]
    exact radical_dvd_self (a := d)
  have hval : (∑ d ∈ s, (1 : ℝ) / (d : ℝ))
      = (u : ℝ)⁻¹ * ∑ d ∈ s, (1 : ℝ) / ((d / u : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hcast : (d : ℝ) = (u : ℝ) * ((d / u : ℕ) : ℝ) := by
      calc (d : ℝ) = ((u * (d / u) : ℕ) : ℝ) := by rw [Nat.mul_div_cancel' (hdiv d hd)]
        _ = (u : ℝ) * ((d / u : ℕ) : ℝ) := by rw [Nat.cast_mul]
    rw [hcast, one_div, one_div]
    exact mul_inv _ _
  have hsub : s.image (fun d => d / u) ⊆ (Finset.Icc 1 M).filter (fun m => radical m ∣ u) := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hdIcc, hdrad⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hdIcc
    have hd0 : d ≠ 0 := by omega
    have hud : u ∣ d := hdiv d hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, le_trans (Nat.div_le_self d u) hdM⟩, ?_⟩
    · rw [Nat.one_le_div_iff hupos]
      exact Nat.le_of_dvd (by omega) hud
    · have h' : radical (d / u) ∣ radical d :=
        radical_dvd_radical (Nat.div_dvd_of_dvd hud) hd0
      rwa [hdrad] at h'
  have hinj : Set.InjOn (fun d => d / u) ↑s := by
    intro d₁ hd₁ d₂ hd₂ heq
    change d₁ / u = d₂ / u at heq
    rw [← Nat.mul_div_cancel' (hdiv d₁ hd₁), heq, Nat.mul_div_cancel' (hdiv d₂ hd₂)]
  calc (∑ d ∈ s, (1 : ℝ) / (d : ℝ))
      = (u : ℝ)⁻¹ * ∑ d ∈ s, (1 : ℝ) / ((d / u : ℕ) : ℝ) := hval
    _ = (u : ℝ)⁻¹ * ∑ m ∈ s.image (fun d => d / u), (1 : ℝ) / (m : ℝ) := by
        rw [Finset.sum_image hinj]
    _ ≤ (u : ℝ)⁻¹ * Tsum u M := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Tsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    _ ≤ (u : ℝ)⁻¹ * ((u : ℝ) / (Nat.totient u : ℝ)) :=
        mul_le_mul_of_nonneg_left (Tsum_le u hu M) (by positivity)
    _ = 1 / (Nat.totient u : ℝ) := by
        have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu0
        rw [div_eq_mul_inv (u : ℝ) (Nat.totient u : ℝ), one_div, ← mul_assoc,
          inv_mul_cancel₀ huR, one_mul]

/-- For squarefree `δ` the summand `μ(δ)²/φ(δ)` is `1/φ(δ)`, and it vanishes otherwise. -/
private lemma sum_mu_sq_div_totient_eq (M : ℕ) :
    (∑ δ ∈ Finset.Icc 1 M,
        ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ))
      = ∑ n ∈ (Finset.Icc 1 M).filter Squarefree, (1 : ℝ) / (Nat.totient n : ℝ) := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun δ _ => by
    have hsq : ((ArithmeticFunction.moebius δ : ℝ)) ^ 2 = if Squarefree δ then 1 else 0 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
      by_cases h : Squarefree δ <;> simp [h]
    rw [hsq]
    by_cases h : Squarefree δ <;> simp [h])

/-- `Real.log M ≤ Σ_{d ≤ M} 1/d` for `M ≥ 1`. -/
private lemma log_le_sum_inv_Icc (M : ℕ) (hM : 1 ≤ M) :
    Real.log (M : ℝ) ≤ ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ) := by
  have h1 : Real.log (M : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
    refine Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) ?_
    push_cast
    linarith
  have h2 : Real.log ((M + 1 : ℕ) : ℝ) ≤ (harmonic M : ℝ) := log_add_one_le_harmonic M
  have h3 : (harmonic M : ℝ) = ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  linarith

/-- **Lower bound for the Mertens-type sum `Σ_{δ ≤ M} μ(δ)²/φ(δ)`.**  For every `M ≥ 1`,
`Real.log M - C ≤ Σ_{δ ≤ M} μ(δ)²/φ(δ)` with an absolute constant `C > 0`.

This is the lower half of the classical evaluation `Σ_{δ ≤ M} μ(δ)²/φ(δ) = log M + O(1)` (the
sharp upper half, `Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp`, is already proved and
available).  It is needed to turn the Selberg diagonalisation of the two-parameter quadratic form
`Msq` (`Submission/Work/ZeroDensity/Jutila/MsqDiag.lean`) into the SHARP bound
`|Msq w y - log w| ≤ C` (with no `log(y/w)` slack), which is what makes the Selberg sieve form
`Σ_{d,e} bvLam_d·bvLam_e / lcm(d,e)` of the difference weights equal to `log(b/a) + O(1)` — the
"form" half of the sharp Barban–Vehov/Graham difference estimate.

Suggested route (elementary, no PNT): `Σ_{d ≤ M} 1/d = Σ_{u squarefree ≤ M} Σ_{d ≤ M, rad d = u}
1/d ≤ Σ_{u squarefree ≤ M} 1/φ(u) = Σ_{δ ≤ M} μ(δ)²/φ(δ)`, the middle step being the fibre bound
`Σ_{d ≤ M, rad d = u} 1/d ≤ 1/φ(u)` (strong induction on squarefree `u`: for `u = p·u'`,
`Σ_{d ≤ M, rad d = p u'} 1/d ≤ Σ_{m ≤ M, rad m ∣ u'} 1/m + (1/p)·Σ_{m ≤ M/p, rad m ∣ u'} 1/m`),
together with `Σ_{d ≤ M} 1/d ≥ log M`. -/
theorem MuSqDivTotientLower : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
    Real.log (M : ℝ) - C ≤ ∑ δ ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ) := by
  refine ⟨1, one_pos, ?_⟩
  intro M hM
  rw [sum_mu_sq_div_totient_eq M]
  have hmaps : ∀ d ∈ Finset.Icc 1 M, radical d ∈ (Finset.Icc 1 M).filter Squarefree := by
    intro d hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
    have hd0 : d ≠ 0 := by omega
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.radical_pos d, ?_⟩, squarefree_radical (a := d)⟩
    calc radical d ≤ d := Nat.le_of_dvd (by omega) (radical_dvd_self (a := d))
      _ ≤ M := hdM
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun d : ℕ => (1 : ℝ) / (d : ℝ))
  have hchain : (∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ))
      ≤ ∑ n ∈ (Finset.Icc 1 M).filter Squarefree, (1 : ℝ) / (Nat.totient n : ℝ) := by
    rw [← hfib]
    exact Finset.sum_le_sum (fun y hy => fibre_sum_le M y (Finset.mem_filter.mp hy).2)
  have hlog := log_le_sum_inv_Icc M hM
  linarith

end

end Work.ZeroDensity.Jutila

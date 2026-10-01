import Mathlib
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs
import Submission.Work.LinnikAreas.Density4.sum_Icc_one_div_eq_harmonic
import Submission.Work.ZeroDensity.Jutila.MsqDiag
import Submission.Work.ZeroDensity.Jutila.MsqSelErr

namespace Work.ZeroDensity.Jutila

open Finset
open Work.LinnikAreas.Density4 (rad)

noncomputable section

/-! ## Facts about the radical -/

private lemma rad_pos (n : ℕ) : 0 < rad n := by
  rw [rad]
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

private lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

private lemma rad_le {n : ℕ} (hn : n ≠ 0) : rad n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (rad_dvd n)

private lemma squarefree_rad (n : ℕ) : Squarefree (rad n) := by
  rw [rad]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (R := ℕ) (s := n.primeFactors)
    (f := fun p : ℕ => p) ?_ ?_
  · intro a ha b hb hab
    exact (Nat.coprime_iff_isRelPrime).mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
        (Nat.prime_of_mem_primeFactors hb)).mpr hab)
  · intro a ha
    exact (Nat.prime_of_mem_primeFactors ha).squarefree

private lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 := (rad_pos n).ne'

private lemma rad_dvd_rad_of_dvd {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) : rad a ∣ rad b := by
  rw [rad, rad]
  rw [Nat.prod_primeFactors_dvd_iff (show (∏ p ∈ b.primeFactors, p) ≠ 0 from
    ne_of_gt (Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)))]
  rw [Nat.primeFactors_prod_primeFactors]
  exact Nat.primeFactors_mono h hb

private lemma rad_mul_prime_dvd_iff {p m n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn0 : n ≠ 0)
    (hm : m ≠ 0) : rad (p * m) ∣ n ↔ rad m ∣ n := by
  have hpn' : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  rw [rad, rad, Nat.prod_primeFactors_dvd_iff hn0, Nat.prod_primeFactors_dvd_iff hn0]
  have h1 : (p * m).primeFactors = {p} ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hm, hp.primeFactors]
  rw [h1, Finset.union_subset_iff]
  exact ⟨fun h => h.2, fun h => ⟨Finset.singleton_subset_iff.mpr hpn', h⟩⟩

private lemma rad_mul_eq_of_dvd {u m : ℕ} (hu : Squarefree u) (hm : m ≠ 0) (h : rad m ∣ u) :
    rad (u * m) = u := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hsub : m.primeFactors ⊆ u.primeFactors := by
    rw [rad] at h
    exact (Nat.prod_primeFactors_dvd_iff hu0).mp h
  have hpf : (u * m).primeFactors = u.primeFactors := by
    rw [Nat.primeFactors_mul hu0 hm]
    ext q
    simp only [Finset.mem_union]
    constructor
    · rintro (hq | hq)
      · exact hq
      · exact hsub hq
    · intro hq; exact Or.inl hq
  rw [rad, hpf, Nat.prod_primeFactors_of_squarefree hu]

/-! ## The fibre bound `Σ_{m ≤ N, rad m ∣ u} 1/m ≤ u/φ(u)` -/

/-- `T(u, N) = Σ_{m ≤ N, rad m ∣ u} 1/m`. -/
private noncomputable def Tsum (u N : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m ∣ u), (1 : ℝ) / (m : ℝ)

private lemma Tsum_nonneg (u N : ℕ) : 0 ≤ Tsum u N := by
  rw [Tsum]
  exact Finset.sum_nonneg (fun m _ => by positivity)

/-- The part of `T(n, N)` with `p ∣ m` is `T(n, ⌊N/p⌋)/p`, for a prime `p ∣ n`. -/
private lemma sum_filter_pdvd_eq (p n N : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn0 : n ≠ 0) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m ∣ n ∧ p ∣ m), (1 : ℝ) / (m : ℝ))
      = (p : ℝ)⁻¹ * Tsum n (N / p) := by
  rw [Tsum, Finset.mul_sum]
  refine Finset.sum_bij (fun m _ => m / p) ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmIcc, hrad, hpm⟩ : m ∈ Finset.Icc 1 N ∧ rad m ∣ n ∧ p ∣ m :=
      Finset.mem_filter.mp hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmIcc
    have hm0 : m ≠ 0 := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hmN⟩, ?_⟩
    · rw [Nat.one_le_div_iff hp.pos]
      exact Nat.le_of_dvd (by omega) hpm
    · exact (rad_dvd_rad_of_dvd (Nat.div_dvd_of_dvd hpm) hm0).trans hrad
  · intro m₁ hm₁ m₂ hm₂ heq
    have h1 : p ∣ m₁ := (Finset.mem_filter.mp hm₁).2.2
    have h2 : p ∣ m₂ := (Finset.mem_filter.mp hm₂).2.2
    rw [← Nat.mul_div_cancel' h1, heq, Nat.mul_div_cancel' h2]
  · intro b hb
    obtain ⟨hbIcc, hbrad⟩ : b ∈ Finset.Icc 1 (N / p) ∧ rad b ∣ n := Finset.mem_filter.mp hb
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbIcc
    have hb0 : b ≠ 0 := by omega
    refine ⟨p * b, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero hb0)
      · calc p * b ≤ p * (N / p) := Nat.mul_le_mul_left p hbN
          _ ≤ N := Nat.mul_div_le N p
      · rw [rad_mul_prime_dvd_iff hp hpn hn0 hb0]
        exact hbrad
      · exact dvd_mul_right p b
    · exact Nat.mul_div_right b hp.pos
  · intro m hm
    have hpm : p ∣ m := (Finset.mem_filter.mp hm).2.2
    have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hcast : ((m / p : ℕ) : ℝ) = (m : ℝ) / (p : ℝ) := Nat.cast_div hpm hpne
    have key : (p : ℝ)⁻¹ * (((m : ℝ) / (p : ℝ))⁻¹) = (m : ℝ)⁻¹ := by
      rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hpne, one_mul]
    rw [hcast, one_div, one_div, key]

/-- The part of `T(n, N)` with `¬ p ∣ m` is at most `T(n/p, N)`, for a prime `p ∣ n`. -/
private lemma sum_filter_not_pdvd_le (p n n' N : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (hnn' : p * n' = n) (hn'0 : n' ≠ 0) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m ∣ n ∧ ¬ p ∣ m), (1 : ℝ) / (m : ℝ))
      ≤ Tsum n' N := by
  rw [Tsum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
  intro m hm
  obtain ⟨hmIcc, hrad, hnp⟩ : m ∈ Finset.Icc 1 N ∧ rad m ∣ n ∧ ¬ p ∣ m :=
    Finset.mem_filter.mp hm
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmIcc
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by rw [← hnn']; exact mul_ne_zero hp.ne_zero hn'0
  have hsub : m.primeFactors ⊆ n.primeFactors := by
    rw [rad] at hrad
    exact (Nat.prod_primeFactors_dvd_iff hn0).mp hrad
  have hpf : n.primeFactors = {p} ∪ n'.primeFactors := by
    rw [← hnn', Nat.primeFactors_mul hp.ne_zero hn'0, hp.primeFactors]
  have hpnot : p ∉ m.primeFactors := fun hpm => hnp (Nat.mem_primeFactors.mp hpm).2.1
  have hsub' : m.primeFactors ⊆ n'.primeFactors := by
    intro q hq
    have hq' := hsub hq
    rw [hpf, Finset.mem_union, Finset.mem_singleton] at hq'
    rcases hq' with h | h
    · exact absurd (h ▸ hq) hpnot
    · exact h
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩, ?_⟩
  rw [rad]
  exact (Nat.prod_primeFactors_dvd_iff hn'0).mpr hsub'

/-- **Recursion for `T`**: for `u = p·u'`, `T(u,N) ≤ p⁻¹·T(u,⌊N/p⌋) + T(u',N)`. -/
private lemma Tsum_rec (p u u' N : ℕ) (hp : p.Prime) (hpdiv : p ∣ u) (hu0 : u ≠ 0)
    (hu_eq : p * u' = u) (hu'0 : u' ≠ 0) :
    Tsum u N ≤ (p : ℝ)⁻¹ * Tsum u (N / p) + Tsum u' N := by
  have hsplit : Tsum u N =
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m ∣ u ∧ p ∣ m), (1 : ℝ) / (m : ℝ))
      + (∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m ∣ u ∧ ¬ p ∣ m), (1 : ℝ) / (m : ℝ)) := by
    rw [Tsum, ← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.Icc 1 N).filter (fun m => rad m ∣ u)) (p := fun m => p ∣ m)]
    congr 1 <;> rw [Finset.filter_filter]
  rw [hsplit, sum_filter_pdvd_eq p u N hp hpdiv hu0]
  exact add_le_add le_rfl (sum_filter_not_pdvd_le p u u' N hp hpdiv hu_eq hu'0)

/-- The arithmetic core of the induction step of the fibre bound. -/
private lemma Tsum_arith {p u u' : ℕ} (hp : p.Prime) (hu'0 : u' ≠ 0)
    (hphi : (Nat.totient u : ℝ) = ((p : ℝ) - 1) * (Nat.totient u' : ℝ))
    (huc : (u : ℝ) = (p : ℝ) * (u' : ℝ)) :
    (p : ℝ)⁻¹ * ((u : ℝ) / (Nat.totient u : ℝ)) + (u' : ℝ) / (Nat.totient u' : ℝ)
      = (u : ℝ) / (Nat.totient u : ℝ) := by
  rw [huc, hphi]
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have ht : (Nat.totient u' : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hu'0)).ne'
  field_simp
  ring_nf

/-- **Induction step of the fibre bound**, for `u = p·u'`. -/
private lemma Tsum_le_step (p u u' : ℕ) (hp : p.Prime) (hu_eq : p * u' = u) (hu'0 : u' ≠ 0)
    (hphi : (Nat.totient u : ℝ) = ((p : ℝ) - 1) * (Nat.totient u' : ℝ))
    (huc : (u : ℝ) = (p : ℝ) * (u' : ℝ))
    (hTsum' : ∀ N : ℕ, Tsum u' N ≤ (u' : ℝ) / (Nat.totient u' : ℝ))
    (hrec : ∀ N : ℕ, Tsum u N ≤ (p : ℝ)⁻¹ * Tsum u (N / p) + Tsum u' N) :
    ∀ N : ℕ, Tsum u N ≤ (u : ℝ) / (Nat.totient u : ℝ) := by
  intro N0
  refine Nat.strong_induction_on N0 ?_
  intro N ihN
  rcases eq_or_ne N 0 with hN | hN
  · subst hN
    have h : Tsum u 0 = 0 := by simp [Tsum]
    rw [h]
    exact div_nonneg (by positivity) (by positivity)
  · have hlt : N / p < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) hp.one_lt
    calc Tsum u N ≤ (p : ℝ)⁻¹ * Tsum u (N / p) + Tsum u' N := hrec N
      _ ≤ (p : ℝ)⁻¹ * ((u : ℝ) / (Nat.totient u : ℝ)) + (u' : ℝ) / (Nat.totient u' : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left (ihN _ hlt) (by positivity)) (hTsum' N)
      _ = (u : ℝ) / (Nat.totient u : ℝ) := Tsum_arith hp hu'0 hphi huc

/-- The case `u = 1` of the fibre bound: only `m = 1` contributes. -/
private lemma Tsum_one_le (N : ℕ) : Tsum 1 N ≤ (1 : ℝ) := by
  have hsub : (Finset.Icc 1 N).filter (fun m => rad m ∣ 1) ⊆ ({1} : Finset ℕ) := by
    intro m hm
    obtain ⟨hmIcc, hrad⟩ : m ∈ Finset.Icc 1 N ∧ rad m ∣ 1 := Finset.mem_filter.mp hm
    obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hmIcc
    simp only [Finset.mem_singleton]
    have hle : rad m ≤ 1 := Nat.le_of_dvd one_pos hrad
    have hrm : rad m = 1 := le_antisymm hle (rad_pos m)
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqm : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩
    have hqrad : q ∣ rad m := by
      rw [rad]
      exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hqm
    rw [hrm] at hqrad
    exact hq.ne_one (Nat.dvd_one.mp hqrad)
  rw [Tsum]
  have h1 : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => rad m ∣ 1), (1 : ℝ) / (m : ℝ))
      ≤ ∑ m ∈ ({1} : Finset ℕ), (1 : ℝ) / (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
  simpa using h1

/-- **The fibre bound**: `Σ_{m ≤ N, rad m ∣ u} 1/m ≤ u/φ(u)` for squarefree `u`. -/
private lemma Tsum_le : ∀ u : ℕ, Squarefree u → ∀ N : ℕ,
    Tsum u N ≤ (u : ℝ) / (Nat.totient u : ℝ) := by
  intro u0
  refine Nat.strong_induction_on u0 ?_
  intro u ih hu N
  rcases eq_or_ne u 1 with hu1 | hu1
  · subst hu1
    have h1 := Tsum_one_le N
    simpa using h1
  · obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd hu1
    have hu0 : u ≠ 0 := hu.ne_zero
    set u' : ℕ := u / p with hu'def
    have hu_eq : p * u' = u := by rw [hu'def]; exact Nat.mul_div_cancel' hpdiv
    have hu'0 : u' ≠ 0 := by
      intro h
      have hz : u = 0 := by rw [← hu_eq, h, mul_zero]
      exact hu0 hz
    have hlt : u' < u := by
      rw [← hu_eq]
      calc u' = u' * 1 := (mul_one u').symm
        _ < u' * p := Nat.mul_lt_mul_of_pos_left hpprime.one_lt (Nat.pos_of_ne_zero hu'0)
        _ = p * u' := mul_comm _ _
    have hu'dvd : u' ∣ u := ⟨p, by rw [← hu_eq, mul_comm]⟩
    have hsq' : Squarefree u' := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hqq
      exact (Nat.squarefree_iff_prime_squarefree.mp hu) q hq (hqq.trans hu'dvd)
    have hnot : ¬ p ∣ u' := by
      intro h
      obtain ⟨k, hk⟩ := h
      have hpp : p * p ∣ u := ⟨k, by rw [← hu_eq, hk]; ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hu) p hpprime hpp
    have hcop : p.Coprime u' := hpprime.coprime_iff_not_dvd.mpr hnot
    have hphi : (Nat.totient u : ℝ) = ((p : ℝ) - 1) * (Nat.totient u' : ℝ) := by
      rw [← hu_eq, Nat.totient_mul hcop, Nat.totient_prime hpprime, Nat.cast_mul,
        Nat.cast_sub hpprime.one_le, Nat.cast_one]
    have huc : (u : ℝ) = (p : ℝ) * (u' : ℝ) := by
      rw [← hu_eq, Nat.cast_mul]
    exact Tsum_le_step p u u' hpprime hu_eq hu'0 hphi huc (ih u' hlt hsq')
      (fun N => Tsum_rec p u u' N hpprime hpdiv hu0 hu_eq hu'0) N

/-- **The fibre of the radical**: `Σ_{d ≤ M, rad d = u} 1/d ≤ 1/φ(u)` for squarefree `u`. -/
private lemma fiber_sum_le (M u : ℕ) (hu : Squarefree u) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d => rad d = u), (1 : ℝ) / (d : ℝ))
      ≤ 1 / (Nat.totient u : ℝ) := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hupos : 0 < u := Nat.pos_of_ne_zero hu0
  have hset : (Finset.Icc 1 M).filter (fun d => rad d = u)
      = ((Finset.Icc 1 (M / u)).filter (fun m => rad m ∣ u)).image (fun m => u * m) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd1, hdM⟩, hdrad⟩
      have hd0 : d ≠ 0 := by omega
      have hud : u ∣ d := hdrad ▸ rad_dvd d
      refine ⟨d / u, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [Nat.one_le_div_iff hupos]
        exact Nat.le_of_dvd (by omega) hud
      · exact Nat.div_le_div_right hdM
      · have hdu : d / u ∣ d := ⟨u, by rw [mul_comm]; exact (Nat.mul_div_cancel' hud).symm⟩
        have hrad : rad (d / u) ∣ rad d := rad_dvd_rad_of_dvd hdu hd0
        rw [hdrad] at hrad
        exact hrad
      · exact Nat.mul_div_cancel' hud
    · rintro ⟨m, ⟨⟨hm1, hmM⟩, hmrad⟩, hm_eq⟩
      have hm0 : m ≠ 0 := by omega
      rw [← hm_eq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hu0 hm0)
      · calc u * m ≤ u * (M / u) := Nat.mul_le_mul_left u hmM
          _ ≤ M := Nat.mul_div_le M u
      · exact rad_mul_eq_of_dvd hu hm0 hmrad
  rw [hset, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hupos h)]
  have hrew : (∑ m ∈ (Finset.Icc 1 (M / u)).filter (fun m => rad m ∣ u),
        (1 : ℝ) / ((u * m : ℕ) : ℝ)) = (u : ℝ)⁻¹ * Tsum u (M / u) := by
    rw [Tsum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [one_div, Nat.cast_mul, mul_inv]
  rw [hrew]
  have h4 := mul_le_mul_of_nonneg_left (Tsum_le u hu (M / u)) (by positivity : (0:ℝ) ≤ (u:ℝ)⁻¹)
  have h5 : (u : ℝ)⁻¹ * ((u : ℝ) / (Nat.totient u : ℝ)) = 1 / (Nat.totient u : ℝ) := by
    have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu0
    have ht : (Nat.totient u : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hupos).ne'
    field_simp
  linarith [h4, h5]

/-- **The Mertens sum is `≥ log M − 1`.**  The fibre bound together with
`Σ_{d ≤ M} 1/d ≥ log M` (harmonic numbers) shows
`log M ≤ Σ_{d ≤ M} 1/d ≤ Σ_{n ≤ M, squarefree} 1/φ(n) = Σ_{δ ≤ M} μ(δ)²/φ(δ)`. -/
private theorem mu_sq_div_totient_lower_aux : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M →
    Real.log (M : ℝ) - C ≤ ∑ δ ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ) := by
  refine ⟨1, one_pos, ?_⟩
  intro M hM
  have hstep1 : (∑ δ ∈ Finset.Icc 1 M,
        ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ))
      = ∑ n ∈ (Finset.Icc 1 M).filter Squarefree, 1 / (Nat.totient n : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    have hsq : ((ArithmeticFunction.moebius δ : ℝ)) ^ 2 = if Squarefree δ then 1 else 0 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
      split_ifs <;> norm_num
    rw [hsq]
    by_cases h : Squarefree δ <;> simp [h]
  have hmaps : ∀ d ∈ Finset.Icc 1 M, rad d ∈ (Finset.Icc 1 M).filter Squarefree := by
    intro d hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
    have hd0 : d ≠ 0 := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨rad_pos d, (rad_le hd0).trans hdM⟩, squarefree_rad d⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun d : ℕ => (1 : ℝ) / (d : ℝ))
  have hchain : (∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ))
      ≤ ∑ n ∈ (Finset.Icc 1 M).filter Squarefree, 1 / (Nat.totient n : ℝ) := by
    rw [← hfib]
    exact Finset.sum_le_sum (fun y hy => fiber_sum_le M y (Finset.mem_filter.mp hy).2)
  have hlog : Real.log (M : ℝ) ≤ ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / (d : ℝ) := by
    rw [Work.LinnikAreas.Density4.sum_Icc_one_div_eq_harmonic M]
    have h1 : Real.log (M : ℝ) ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast hM) (by linarith)
    have h2 : ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) := by push_cast; ring
    exact le_trans h1 (h2 ▸ log_add_one_le_harmonic M)
  rw [hstep1]
  linarith [hchain, hlog]

/-! ## Assembly -/

/-- Assembly step for `mainTerm`: given the two-parameter Selberg diagonalization `hdiag`, the
error bound `hE` for the diagonalized form against the Mertens sum, the sharp upper bound `hM` and
the sharp lower bound `hL` for `Σ_{δ ≤ M} μ(δ)²/φ(δ)`, the mixed Selberg form has main term
`log w`. -/
private lemma mainTerm_assembly (Ce Cm Cl : ℝ) (hCe : 0 < Ce) (hCm : 0 < Cm) (hCl : 0 < Cl)
    (hdiag : ∀ w y : ℝ, 1 ≤ w → w ≤ y → Msq w y = ∑ δ ∈ Finset.Icc 1 ⌊w⌋₊,
        ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
          Work.LinnikAreas.Density4.selTheta (w / (δ : ℝ)) δ *
          Work.LinnikAreas.Density4.selTheta (y / (δ : ℝ)) δ)
    (hE : ∀ (w y : ℝ) (W : ℕ), 1 ≤ w → w ≤ y → (W : ℝ) ≤ w → 1 ≤ W →
        |(∑ δ ∈ Finset.Icc 1 W,
            ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
              Work.LinnikAreas.Density4.selTheta (w / (δ : ℝ)) δ *
              Work.LinnikAreas.Density4.selTheta (y / (δ : ℝ)) δ)
          - (∑ δ ∈ Finset.Icc 1 W,
              ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ))| ≤ Ce)
    (hM : ∀ M : ℕ, 1 ≤ M → (∑ δ ∈ Finset.Icc 1 M,
              ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ))
            ≤ Real.log (M : ℝ) + Cm)
    (hL : ∀ M : ℕ, 1 ≤ M → Real.log (M : ℝ) - Cl ≤ (∑ δ ∈ Finset.Icc 1 M,
              ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w ≤ y →
      |Msq w y - Real.log w| ≤ C * (1 + Real.log (y / w)) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Ce + (Cm + (Cl + Real.log 2)) + 1, by linarith, ?_⟩
  intro w y h1 h2
  have hw1 : 1 ≤ w := le_of_lt h1
  have hw0 : 0 < w := lt_trans zero_lt_one h1
  have hW1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (show (((1:ℕ):ℝ)) ≤ w from by exact_mod_cast hw1)
  have hWle : ((⌊w⌋₊ : ℕ) : ℝ) ≤ w := Nat.floor_le (le_of_lt hw0)
  set S : ℝ := ∑ δ ∈ Finset.Icc 1 ⌊w⌋₊,
      ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ) with hSdef
  have herr : |Msq w y - S| ≤ Ce := by
    rw [hSdef]
    rw [hdiag w y hw1 h2]
    exact hE w y ⌊w⌋₊ hw1 h2 hWle hW1
  have hSupper : S ≤ Real.log w + Cm := by
    have h := hM ⌊w⌋₊ hW1
    have hle : Real.log ((⌊w⌋₊ : ℕ) : ℝ) ≤ Real.log w :=
      Real.log_le_log (by exact_mod_cast hW1 : (0 : ℝ) < (⌊w⌋₊ : ℝ)) hWle
    rw [hSdef]; linarith
  have hSlower : Real.log w - (Cl + Real.log 2) ≤ S := by
    have h := hL ⌊w⌋₊ hW1
    have hwlt : w < ((⌊w⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one w
    have hW2 : (1 : ℝ) ≤ ((⌊w⌋₊ : ℕ) : ℝ) := by exact_mod_cast hW1
    have hw2W : w ≤ 2 * ((⌊w⌋₊ : ℕ) : ℝ) := by linarith
    have hlogw : Real.log w ≤ Real.log 2 + Real.log ((⌊w⌋₊ : ℕ) : ℝ) := by
      calc Real.log w ≤ Real.log (2 * ((⌊w⌋₊ : ℕ) : ℝ)) := Real.log_le_log hw0 hw2W
        _ = Real.log 2 + Real.log ((⌊w⌋₊ : ℕ) : ℝ) :=
            Real.log_mul (by norm_num) (by positivity)
    rw [hSdef]; linarith
  have hlogS : |S - Real.log w| ≤ Cm + (Cl + Real.log 2) := by
    rw [abs_le]
    constructor <;> linarith
  have hmain : |Msq w y - Real.log w| ≤ Ce + (Cm + (Cl + Real.log 2)) := by
    have hsplit : Msq w y - Real.log w = (Msq w y - S) + (S - Real.log w) := by ring
    calc |Msq w y - Real.log w| = |(Msq w y - S) + (S - Real.log w)| := by rw [hsplit]
      _ ≤ |Msq w y - S| + |S - Real.log w| := abs_add_le _ _
      _ ≤ Ce + (Cm + (Cl + Real.log 2)) := add_le_add herr hlogS
  have hylog : 0 ≤ Real.log (y / w) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hw0]; linarith
  have hXnn : 0 ≤ Ce + (Cm + (Cl + Real.log 2)) := by linarith
  calc |Msq w y - Real.log w| ≤ Ce + (Cm + (Cl + Real.log 2)) := hmain
    _ ≤ (Ce + (Cm + (Cl + Real.log 2)) + 1) * (1 + Real.log (y / w)) := by nlinarith

/-- **The two-parameter Selberg quadratic form has main term `log w`.**  For real cutoffs
`1 < w ≤ y`,

  `Msq w y = log w + O(1 + log(y/w))`,

uniformly in `w, y ≥ w`.  Here `Msq w y = Σ_{d ≤ w, e ≤ y} selW w d·selW y e / lcm(d,e)` with
the Selberg weights `selW w d = μ(d)log(w/d)` (see `mixedSelbergDefs`).

Route: the Selberg diagonalization `Σ_{d,e} a_d a_e/lcm(d,e) = Σ_δ φ(δ)(Σ_{δ|d} a_d/d)²` turns
`Msq w y` into `Σ_δ φ(δ) T_w(δ) T_y(δ)` with
`T_z(δ) = (μ(δ)/δ)·Σ_{m ≤ z/δ, (m,δ)=1} μ(m)log((z/δ)/m)/m = (μ(δ)/δ)·selTheta(z/δ, δ)`
(`selTheta` from `Submission.Work.LinnikAreas.Density4.SelbergDefs`), and the sharp asymptotic
`selTheta(Y,r) = r/φ(r) + O(σ_{1/2}(r)(log(2+Y))^{-3})` (`selTheta_asymptotic`, proved in the
workspace); the leading contribution is `Σ_δ φ(δ)(μ(δ)/φ(δ))² = Σ_δ μ(δ)²/φ(δ) = log w + O(1)`
(`sum_mu_sq_div_totient_sharp` + the dyadic decay estimates `dyadic_decay_sigma_half`,
`dyadic_decay_sigma_half_sq`, all proved in the workspace).  Note the `δ ≥ 2` part of the
error is only `O(1)` because of the coprimality structure: the crude bound
`Σ_{δ≤w} σ_{1/2}(δ)/δ ≍ w` must be improved by expanding the `selTheta` error term in the
`m`-variable and using the decay of the *coprime* Selberg sum `selTheta` (this is exactly how
`selQ_le_log_add_const` in `Submission.Work.LinnikAreas.Density4.selberg_LambdaR_sq_sharp`
handles the one-parameter case). -/
theorem mainTerm :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w ≤ y →
      |Msq w y - Real.log w| ≤ C * (1 + Real.log (y / w)) := by
  obtain ⟨Ce, hCe, hE⟩ := MsqSelErr
  obtain ⟨Cm, hCm, hM⟩ := Work.LinnikAreas.Density4.sum_mu_sq_div_totient_sharp
  obtain ⟨Cl, hCl, hL⟩ := mu_sq_div_totient_lower_aux
  exact mainTerm_assembly Ce Cm Cl hCe hCm hCl MsqDiag hE hM hL

end

end Work.ZeroDensity.Jutila

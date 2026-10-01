import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.capContent_divPoly
import Submission.Work.LinnikBurgess.capContent_fiber_six
import Submission.Work.LinnikBurgess.capContent_fiber_three
import Submission.Work.LinnikBurgess.capContent_fiber_zero
import Submission.Work.LinnikBurgess.capContent_tail
import Submission.Work.LinnikBurgess.critN_tripleVanish_content
import Submission.Work.LinnikBurgess.critN_content_iff

namespace Work.LinnikBurgess

open Polynomial

/-- The capped part of the support of Lemma A, in the `p ∣ contAB` regime, has at most
`7 (e+1) p^(max 0 (m - ⌈A/2⌉))` points, where `m = cubeLevel p e`, `T = capLevel p e`,
`A = e - m - J ≥ 1`, `J = v_p(contAB a b)` (so `p^J` divides every coefficient of `N = critN a b`
but `p^(J+1)` does not).

`capSet p e a b` is the set of support points `y < p^m` with `T ≤ nval y = v_p(N'(y))`; for such `y`,
the transfer hypothesis `hbt` gives `b_y = T` and `p^(m+T) ∣ N(y)`.

Hints: write `N = p^J · Ñ` (all coefficients of `N` are divisible by `p^J`; `Ñ` exists as a
polynomial over `ℤ` and is nonzero with `natDegree Ñ = natDegree N ∈ [2,4]`).  For `y ∈ capSet`,
`p^(J+A) ∣ N(y)` and `p^T ∣ N'(y)`, so `p^A ∣ Ñ(y)` and `p^(T-J) ∣ Ñ'(y)`.  Split the count by
`ν̃ = v_p(Ñ'(y))`: for a *fixed* `ν̃` the `y`'s are confined to at most `natDegree Ñ' ≤ 3` classes
mod `p^min(ν̃,m)` (Hensel on `Ñ'` at `y`, where `v_p(Ñ''(y)) = 0` because `p^(J+1) ∣ N''(y)` would
contradict `critN_tripleVanish_content` at `k = J+1`), and, when `2ν̃+1 ≤ A`, also to at most
`natDegree Ñ ≤ 4` classes mod `p^min(A-ν̃,m)` (Hensel on `Ñ`); `card_hensel_le` gives both counts.
Since `max (min(ν̃,m)) (min(A-ν̃,m)) ≥ ⌈A/2⌉` and `A ≤ 2m`, summing the geometric bounds over
`ν̃` gives the stated `7 (e+1) p^(m - ⌈A/2⌉)` (use `A ≤ e` to absorb the constant `7(A+1) ≤ 7(e+1)`). -/
theorem card_capSet_le_content {p e J : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hdeg2 : 2 ≤ (critN a b).natDegree)
    (hdeg : (critN a b).natDegree ≤ 4)
    (hcontent : ∀ n, ((p ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hprim : ∃ n, ¬ ((p ^ (J + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hbt : SuppTransfer p e a b) (hJ : 1 ≤ J) (hA : J < e - cubeLevel p e) :
    (capSet p e a b).card
      ≤ 7 * (e + 1) * p ^ max 0 (cubeLevel p e - (e - cubeLevel p e - J + 1) / 2) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hpint : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he3 : e ≤ 3 * cubeLevel p e := e_le_three_mul_cubeLevel hp5
  have hmT : cubeLevel p e + capLevel p e = e - cubeLevel p e := cubeLevel_add_capLevel hp5 he
  have hm1 : 1 ≤ cubeLevel p e := one_le_cubeLevel hp5 (by omega)
  have hA1 : 1 ≤ e - cubeLevel p e - J := by omega
  have hA2m : e - cubeLevel p e - J ≤ 2 * cubeLevel p e := by omega
  set K : ℕ := (e - cubeLevel p e - J + 1) / 2 with hK
  set P : ℕ := p ^ (cubeLevel p e - K) with hP
  have hP1 : 1 ≤ P := by
    rw [hP]
    have h := pow_pos (by omega : 0 < p) (cubeLevel p e - K)
    omega
  have hpowJ : ∀ n : ℕ, (((p ^ n : ℕ) : ℤ)) ≠ 0 := fun n => by
    exact_mod_cast (pow_ne_zero n hp.ne_zero)
  have hKmA : K ≤ min (e - cubeLevel p e - J) (cubeLevel p e) := by
    rw [hK]; exact le_min (by omega) (by omega)
  have hcoef : 6 * cubeLevel p e + 6 ≤ 7 * (e + 1) := by omega
  obtain ⟨Ñ, hÑC, hÑcoeff, hÑzero, hÑdeg, hÑmap⟩ := capContent_divPoly p J (critN a b) hcontent
  have hNne : critN a b ≠ 0 := by
    intro h0; rw [h0] at hdeg2; simp at hdeg2
  have hÑne : Ñ ≠ 0 := fun h0 => hNne (hÑzero.mp h0)
  have hÑdeg4 : Ñ.natDegree ≤ 4 := by rw [hÑdeg]; exact hdeg
  have hÑdeg2 : 2 ≤ Ñ.natDegree := by rw [hÑdeg]; exact hdeg2
  have hÑmapne : Ñ.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hprim
    exact hn ((hÑmap.mp h0) n)
  have hNeval : ∀ z : ℤ, (critN a b).eval z = (((p ^ J : ℕ) : ℤ)) * Ñ.eval z := by
    intro z; rw [← hÑC, Polynomial.eval_mul, Polynomial.eval_C]
  have hNder1 : (critN a b).derivative = Polynomial.C (((p ^ J : ℕ) : ℤ)) * Ñ.derivative := by
    rw [← hÑC, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  have hNder2 : ((critN a b).derivative).derivative
      = Polynomial.C (((p ^ J : ℕ) : ℤ)) * (Ñ.derivative).derivative := by
    rw [hNder1, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  have hNdeval : ∀ z : ℤ, (critN a b).derivative.eval z
      = (((p ^ J : ℕ) : ℤ)) * (Ñ.derivative).eval z := by
    intro z; rw [hNder1, Polynomial.eval_mul, Polynomial.eval_C]
  have hNd2eval : ∀ z : ℤ, ((critN a b).derivative).derivative.eval z
      = (((p ^ J : ℕ) : ℤ)) * ((Ñ.derivative).derivative).eval z := by
    intro z; rw [hNder2, Polynomial.eval_mul, Polynomial.eval_C]
  have hpow : (((p ^ (J + 1) : ℕ) : ℤ)) = (((p ^ J : ℕ) : ℤ)) * (p : ℤ) := by
    push_cast
    rw [pow_succ]
  have hmf : ∀ y ∈ capSet p e a b,
      UnitAt p y a b ∧ y < p ^ (cubeLevel p e) ∧
      (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ)) ∣ Ñ.eval (y : ℤ) := by
    intro y hy
    rw [capSet, Finset.mem_filter] at hy
    obtain ⟨hysupp, hylev⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysupp
    obtain ⟨hyrange, hpred⟩ := hysupp
    obtain ⟨hbval, hdvd⟩ := hbt y hpred
    refine ⟨hpred.1, Finset.mem_range.mp hyrange, ?_⟩
    have hT : bval p e a b y = capLevel p e := by
      rw [hbval]; exact min_eq_right hylev
    have hdvdN : (((p ^ (e - cubeLevel p e) : ℕ) : ℤ)) ∣ (critN a b).eval (y : ℤ) := by
      have h1 : cubeLevel p e + bval p e a b y = e - cubeLevel p e := by
        rw [hT]; exact hmT
      rwa [h1] at hdvd
    have hAeq : e - cubeLevel p e = J + (e - cubeLevel p e - J) := by omega
    have h3 : (((p ^ (J + (e - cubeLevel p e - J)) : ℕ) : ℤ)) ∣ (critN a b).eval (y : ℤ) := by
      rw [← hAeq]; exact hdvdN
    have heq : ((p ^ (J + (e - cubeLevel p e - J)) : ℕ) : ℤ)
        = (((p ^ J : ℕ) : ℤ)) * (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ)) := by
      push_cast
      rw [pow_add]
    rw [heq, hNeval (y : ℤ)] at h3
    exact (mul_dvd_mul_iff_left (hpowJ J)).mp h3
  have hnotdvd : ∀ y ∈ capSet p e a b,
      1 ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) →
      ¬ ((p : ℤ) ∣ ((Ñ.derivative).derivative).eval (y : ℤ)) := by
    intro y hy hν hpdiv
    obtain ⟨hunit, hyrange, hdvdÑ⟩ := hmf y hy
    have hpd : (p : ℤ) ∣ Ñ.eval (y : ℤ) := by
      have h1 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ (e - cubeLevel p e - J) :=
        pow_dvd_pow (p : ℤ) hA1
      have h2 : (p : ℤ) ∣ (p : ℤ) ^ (e - cubeLevel p e - J) := by simpa using h1
      have h3 : (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ))
          = (p : ℤ) ^ (e - cubeLevel p e - J) := by rw [Nat.cast_pow]
      rw [h3] at hdvdÑ
      exact h2.trans hdvdÑ
    have hNy : (((p ^ (J + 1) : ℕ) : ℤ)) ∣ (critN a b).eval (y : ℤ) := by
      rw [hNeval (y : ℤ), hpow]
      exact mul_dvd_mul_left _ hpd
    have hpd1 : (p : ℤ) ∣ (Ñ.derivative).eval (y : ℤ) := by
      have hne : ((Ñ.derivative).eval (y : ℤ)).natAbs ≠ 0 := by
        intro h0; rw [h0] at hν; simp at hν
      have h1 : p ^ 1 ∣ ((Ñ.derivative).eval (y : ℤ)).natAbs :=
        (padicValNat_dvd_iff_le hne).mpr hν
      rw [pow_one] at h1
      exact (Int.natAbs_dvd_natAbs).mp (by simpa using h1)
    have hNy1 : (((p ^ (J + 1) : ℕ) : ℤ)) ∣ (critN a b).derivative.eval (y : ℤ) := by
      rw [hNdeval (y : ℤ), hpow]
      exact mul_dvd_mul_left _ hpd1
    have hNy2 : (((p ^ (J + 1) : ℕ) : ℤ))
        ∣ ((critN a b).derivative).derivative.eval (y : ℤ) := by
      rw [hNd2eval (y : ℤ), hpow]
      exact mul_dvd_mul_left _ hpdiv
    have hcont := critN_tripleVanish_content a b y hunit hNy hNy1 hNy2
    have hv6 : padicValNat p 6 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h6
      have h6' : p ∣ 2 * 3 := by simpa using h6
      rcases hp.dvd_mul.mp h6' with h | h
      · have := Nat.le_of_dvd (by norm_num : 0 < 2) h; omega
      · have := Nat.le_of_dvd (by norm_num : 0 < 3) h; omega
    rw [hv6, Nat.sub_zero] at hcont
    obtain ⟨n, hn⟩ := hprim
    exact hn ((critN_content_iff (k := J + 1) hp5 a b).mpr hcont n)
  have hzf_le : ((capSet p e a b).filter
      (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0)).card ≤ 3 := by
    have hddeg : Ñ.derivative.natDegree ≤ 3 := by
      have h1 := Polynomial.natDegree_derivative_le Ñ
      omega
    have hne : Ñ.derivative ≠ 0 := by
      intro h0
      have h1 := Polynomial.derivative_eq_zero.mp h0
      omega
    have hsub : ((capSet p e a b).filter
        (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0)).image (fun y : ℕ => (y : ℤ))
        ⊆ (Ñ.derivative).roots.toFinset := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨hne, ?_⟩
      rw [Polynomial.IsRoot.def]
      exact (Finset.mem_filter.mp hy).2
    calc ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0)).card
        = (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0)).image
            (fun y : ℕ => (y : ℤ))).card :=
          (Finset.card_image_of_injective _ (fun x y h => by exact_mod_cast h)).symm
      _ ≤ ((Ñ.derivative).roots.toFinset).card := Finset.card_le_card hsub
      _ ≤ (Ñ.derivative).roots.card := Multiset.toFinset_card_le _
      _ ≤ Ñ.derivative.natDegree := Polynomial.card_roots' _
      _ ≤ 3 := hddeg
  have hShyp : ∀ (ν : ℕ), ∀ y ∈ (((capSet p e a b).filter
        (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
        (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν)),
      (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ)) ∣ Ñ.eval (y : ℤ)
      ∧ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν
      ∧ (Ñ.derivative).eval (y : ℤ) ≠ 0
      ∧ y ∈ capSet p e a b
      ∧ y < p ^ (cubeLevel p e) := by
    intro ν y hy
    rw [Finset.mem_filter, Finset.mem_filter] at hy
    obtain ⟨⟨hycap, hynz⟩, hyν⟩ := hy
    obtain ⟨_, hyrange, hydvd⟩ := hmf y hycap
    exact ⟨hydvd, hyν, hynz, hycap, hyrange⟩
  have hzero : ∀ y ∈ (((capSet p e a b).filter
        (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
        (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = 0)),
      ¬ ((p : ℤ) ∣ (Ñ.derivative).eval (y : ℤ)) := by
    intro y hy
    obtain ⟨_, hy0, hne, _, _⟩ := hShyp 0 y hy
    have h1 : ¬ p ∣ ((Ñ.derivative).eval (y : ℤ)).natAbs := by
      rcases (padicValNat.eq_zero_iff.mp hy0) with h | h | h
      · omega
      · exact absurd h (by simpa using hne)
      · exact h
    exact fun hd => h1 ((Int.natAbs_dvd_natAbs).mpr hd)
  have hfibb : ∀ ν ∈ Finset.range (cubeLevel p e),
      (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
        (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν)).card
      ≤ 6 * P := by
    intro ν hν
    rcases Nat.eq_zero_or_pos ν with hν0 | hνpos
    · subst hν0
      have hS : ∀ y ∈ (((capSet p e a b).filter
            (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
            (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = 0)),
          (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ)) ∣ Ñ.eval (y : ℤ)
          ∧ ¬ ((p : ℤ) ∣ (Ñ.derivative).eval (y : ℤ))
          ∧ y < p ^ (cubeLevel p e) :=
        fun y hy => ⟨(hShyp 0 y hy).1, hzero y hy, (hShyp 0 y hy).2.2.2.2⟩
      have hcard := capContent_fiber_zero (p := p) Ñ hÑdeg4 hÑmapne
        (A := e - cubeLevel p e - J) (M := cubeLevel p e) hA1 _ hS
      refine hcard.trans ?_
      have hle : cubeLevel p e - min (e - cubeLevel p e - J) (cubeLevel p e)
          ≤ cubeLevel p e - K := Nat.sub_le_sub_left hKmA _
      calc 4 * p ^ (cubeLevel p e - min (e - cubeLevel p e - J) (cubeLevel p e))
          ≤ 4 * p ^ (cubeLevel p e - K) :=
            Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega) hle)
        _ ≤ 6 * p ^ (cubeLevel p e - K) := by omega
        _ = 6 * P := by rw [hP]
    · have hSν : ∀ y ∈ (((capSet p e a b).filter
            (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
            (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν)),
          (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ)) ∣ Ñ.eval (y : ℤ)
          ∧ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν
          ∧ ¬ ((p : ℤ) ∣ ((Ñ.derivative).derivative).eval (y : ℤ))
          ∧ y < p ^ (cubeLevel p e) :=
        fun y hy => ⟨(hShyp ν y hy).1, (hShyp ν y hy).2.1,
          hnotdvd y (hShyp ν y hy).2.2.2.1 (by rw [(hShyp ν y hy).2.1]; exact hνpos),
          (hShyp ν y hy).2.2.2.2⟩
      by_cases h2ν : 2 * ν + 1 ≤ e - cubeLevel p e - J
      · have hcard := capContent_fiber_six (p := p) hp5 Ñ hÑdeg4 hÑmapne hνpos h2ν _ hSν
        refine hcard.trans ?_
        have hle : cubeLevel p e - min (e - cubeLevel p e - J - ν) (cubeLevel p e)
            ≤ cubeLevel p e - K := by
          apply Nat.sub_le_sub_left
          rw [hK]
          omega
        calc 6 * p ^ (cubeLevel p e - min (e - cubeLevel p e - J - ν) (cubeLevel p e))
            ≤ 6 * p ^ (cubeLevel p e - K) :=
              Nat.mul_le_mul_left 6 (Nat.pow_le_pow_right (by omega) hle)
          _ = 6 * P := by rw [hP]
      · have hcard := capContent_fiber_three (p := p) hp5 Ñ hÑdeg4 hÑmapne hνpos _ hSν
        refine hcard.trans ?_
        have hle : cubeLevel p e - min ν (cubeLevel p e) ≤ cubeLevel p e - K := by
          apply Nat.sub_le_sub_left
          rw [hK]
          omega
        calc 3 * p ^ (cubeLevel p e - min ν (cubeLevel p e))
            ≤ 3 * p ^ (cubeLevel p e - K) :=
              Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) hle)
          _ ≤ 6 * P := by rw [hP]; omega
  have htail : (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
      (fun y : ℕ => cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs))).card
      ≤ 3 := by
    have hS : ∀ y ∈ (((capSet p e a b).filter
          (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs))),
        (((p ^ (e - cubeLevel p e - J) : ℕ) : ℤ)) ∣ Ñ.eval (y : ℤ)
        ∧ cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs)
        ∧ ¬ ((p : ℤ) ∣ ((Ñ.derivative).derivative).eval (y : ℤ))
        ∧ y < p ^ (cubeLevel p e) := by
      intro y hy
      rw [Finset.mem_filter, Finset.mem_filter] at hy
      obtain ⟨⟨hycap, _⟩, hylv⟩ := hy
      obtain ⟨_, hyrange, hydvd⟩ := hmf y hycap
      refine ⟨hydvd, hylv, ?_, hyrange⟩
      exact hnotdvd y hycap (by omega)
    exact capContent_tail (p := p) hp5 Ñ hÑdeg4 hÑmapne hA1 hm1 _ hS
  have hsmall : (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
      (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e)).card
      ≤ ∑ ν ∈ Finset.range (cubeLevel p e),
          (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
            (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν)).card := by
    have hsub : (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
        (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e))
        ⊆ ((Finset.range (cubeLevel p e)).biUnion
            (fun ν => ((capSet p e a b).filter
              (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
              (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν))) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hynz, hylt⟩ := hy
      exact Finset.mem_biUnion.mpr ⟨padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs),
        Finset.mem_range.mpr hylt, Finset.mem_filter.mpr ⟨hynz, rfl⟩⟩
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : (∑ ν ∈ Finset.range (cubeLevel p e),
      (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
        (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν)).card)
      ≤ cubeLevel p e * (6 * P) := by
    calc (∑ ν ∈ Finset.range (cubeLevel p e),
        (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) = ν)).card)
        ≤ ∑ ν ∈ Finset.range (cubeLevel p e), 6 * P := Finset.sum_le_sum hfibb
      _ = cubeLevel p e * (6 * P) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp
  have hsplit : (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).card)
      ≤ (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e)).card
        + (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs))).card := by
    have hun : ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0))
        = (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
            (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e))
          ∪ (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
            (fun y : ℕ => cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs))) := by
      ext y
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h
        by_cases hc : padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, by omega⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have h1 : ((((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e))
        ∪ (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs)))).card
        ≤ (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs) < cubeLevel p e)).card
        + (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).filter
          (fun y : ℕ => cubeLevel p e ≤ padicValNat p (((Ñ.derivative).eval (y : ℤ)).natAbs))).card :=
      Finset.card_union_le _ _
    rwa [← hun] at h1
  have hmain : (capSet p e a b).card ≤ 7 * (e + 1) * P := by
    have hpart : (capSet p e a b).card
        ≤ ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0)).card
        + ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).card := by
      have hun : (capSet p e a b)
          = ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0))
            ∪ ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)) := by
        ext y
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro h
          by_cases hc : (Ñ.derivative).eval (y : ℤ) = 0
          · exact Or.inl ⟨h, hc⟩
          · exact Or.inr ⟨h, hc⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have h1 : (((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0))
          ∪ ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0))).card
          ≤ ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) = 0)).card
          + ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).card :=
        Finset.card_union_le _ _
      rwa [← hun] at h1
    have h6 : ((capSet p e a b).filter (fun y : ℕ => (Ñ.derivative).eval (y : ℤ) ≠ 0)).card
        ≤ cubeLevel p e * (6 * P) + 3 := by omega
    have h7 : (capSet p e a b).card ≤ 3 + (cubeLevel p e * (6 * P) + 3) := by omega
    have h8 : 3 + (cubeLevel p e * (6 * P) + 3) ≤ 7 * (e + 1) * P := by
      have h9 : 3 + 3 ≤ 6 * P := by omega
      nlinarith [hcoef, h9]
    linarith [h7, h8]
  rw [max_eq_right (Nat.zero_le _)]
  rw [← hP]
  exact hmain

end Work.LinnikBurgess


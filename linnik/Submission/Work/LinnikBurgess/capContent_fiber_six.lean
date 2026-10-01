import Mathlib
import Submission.Work.LinnikBurgess.capContent_fiber_six_base
import Submission.Work.LinnikBurgess.clusterStep
import Submission.Work.LinnikBurgess.countPsol
import Submission.Work.LinnikBurgess.critRes_card_le_three
import Submission.Work.LinnikBurgess.eval_not_dvd_of_deriv_eq_zero

namespace Work.LinnikBurgess

open Polynomial

/-- `y = p * (y / p) + y % p`, cast to `ℤ`. -/
private lemma cast_decomp (p y : ℕ) :
    (y : ℤ) = (p : ℤ) * (y / p : ℕ) + ((y % p : ℕ) : ℤ) := by
  have h := Nat.div_add_mod y p
  calc (y : ℤ) = ((p * (y / p) + y % p : ℕ) : ℤ) := by rw [h]
    _ = (p : ℤ) * (y / p : ℕ) + ((y % p : ℕ) : ℤ) := by push_cast; ring

theorem capContent_fiber_six {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ 4) (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0)
    {A ν M : ℕ} (hν : 1 ≤ ν) (hA : 2 * ν + 1 ≤ A) (S : Finset ℕ)
    (hS : ∀ y ∈ S, ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ)
        ∧ padicValNat p ((Polynomial.derivative Q).eval (y : ℤ)).natAbs = ν
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ))
        ∧ y < p ^ M) :
    S.card ≤ 6 * p ^ (M - min (A - ν) M) := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpne0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hAy : ∀ y ∈ S, ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ) := fun y hy => (hS y hy).1
  have hval : ∀ y ∈ S, padicValNat p (Q.derivative.eval (y : ℤ)).natAbs = ν :=
    fun y hy => (hS y hy).2.1
  have h3y : ∀ y ∈ S, ¬ ((p : ℤ) ∣ Q.derivative.derivative.eval (y : ℤ)) :=
    fun y hy => (hS y hy).2.2.1
  have hMy : ∀ y ∈ S, y < p ^ M := fun y hy => (hS y hy).2.2.2
  have hpQ : ∀ y ∈ S, (p : ℤ) ∣ Q.eval (y : ℤ) := by
    intro y hy
    have h1 : (p : ℤ) ∣ ((p ^ A : ℕ) : ℤ) := by
      rw [Nat.cast_pow]; exact dvd_pow_self _ (by omega)
    exact h1.trans (hAy y hy)
  have hpQ' : ∀ y ∈ S, (p : ℤ) ∣ Q.derivative.eval (y : ℤ) := by
    intro y hy
    have h1 : (p : ℤ) ∣ ((p ^ ν : ℕ) : ℤ) := by
      rw [Nat.cast_pow]; exact dvd_pow_self _ (by omega)
    exact h1.trans (int_dvd_of_padicValNat_natAbs_eq (hval y hy))
  have hQ'ne : ∀ y ∈ S, Q.derivative.eval (y : ℤ) ≠ 0 :=
    fun y hy => int_ne_zero_of_padicValNat_natAbs_eq hν (hval y hy)
  by_cases hgz : Q.derivative.map (Int.castRingHom (ZMod p)) = 0
  · have hSempty : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      exact eval_not_dvd_of_deriv_eq_zero hp hdeg hQ hgz (y : ℤ) (hpQ y hy)
    rw [hSempty]; simp
  · set N : ℕ := M - ν with hN
    set BB : ℕ := A - 2 * ν with hBB
    have hBB1 : 1 ≤ BB := by omega
    have hhexp : N - BB = M - min (A - ν) M := by rw [hN, hBB]; omega
    set R : Finset ℕ := (Finset.range p).filter (fun r => (p : ℤ) ∣ Q.derivative.eval (r : ℤ)) with hR
    have hRcard : R.card ≤ 3 := by rw [hR]; exact critRes_card_le_three Q hdeg hgz
    have himgsub : S.image (fun y : ℕ => y % p) ⊆ R := by
      intro r hr
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hr
      rw [hR, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt y hp0, ?_⟩
      have hmodp : (p : ℤ) ∣ (y : ℤ) - ((y % p : ℕ) : ℤ) := by
        have he : (y : ℤ) - ((y % p : ℕ) : ℤ) = (p : ℤ) * (y / p : ℕ) := by
          rw [cast_decomp p y]; ring
        rw [he]; exact dvd_mul_right _ _
      obtain ⟨E, hE⟩ := int_dividedDiff Q.derivative (y : ℤ) ((y % p : ℕ) : ℤ)
      have h2 : (p : ℤ) ∣ Q.derivative.eval (y : ℤ) - Q.derivative.eval ((y % p : ℕ) : ℤ) := by
        rw [hE]; exact dvd_mul_of_dvd_left hmodp E
      have h3 := dvd_sub (hpQ' y hyS) h2
      rw [show Q.derivative.eval (y : ℤ) - (Q.derivative.eval (y : ℤ)
          - Q.derivative.eval ((y % p : ℕ) : ℤ)) = Q.derivative.eval ((y % p : ℕ) : ℤ) from
        sub_sub_cancel _ _] at h3
      exact h3
    have himgcard : (S.image (fun y : ℕ => y % p)).card ≤ 3 :=
      le_trans (Finset.card_le_card himgsub) hRcard
    have hfiber : ∀ r ∈ S.image (fun y : ℕ => y % p),
        (S.filter (fun y => y % p = r)).card ≤ 2 * p ^ (N - BB) := by
      intro r hr
      by_cases hne : (S.filter (fun y => y % p = r)).Nonempty
      · set fib : Finset ℕ := S.filter (fun y => y % p = r) with hfib
        have fibmem : ∀ y : ℕ, y ∈ fib ↔ y ∈ S ∧ y % p = r := by
          intro y; rw [hfib, Finset.mem_filter]
        set y0 : ℕ := fib.min' hne with hy0def
        have hy0mem : y0 ∈ fib := by rw [hy0def]; exact Finset.min'_mem fib hne
        have hy0min : ∀ y ∈ fib, y0 ≤ y := by
          intro y hy; rw [hy0def]; exact Finset.min'_le fib y hy
        have hy0S : y0 ∈ S := ((fibmem y0).mp hy0mem).1
        have hy0res : y0 % p = r := ((fibmem y0).mp hy0mem).2
        obtain ⟨H, hHexp, hH2⟩ := taylor2_expansion Q (y0 : ℤ)
        set u : ℤ := Q.derivative.eval (y0 : ℤ) / ((p ^ ν : ℕ) : ℤ) with hu
        have hu_eq : ((p ^ ν : ℕ) : ℤ) * u = Q.derivative.eval (y0 : ℤ) := by
          rw [hu]; exact Int.mul_ediv_cancel' (int_dvd_of_padicValNat_natAbs_eq (hval y0 hy0S))
        have hu_unit : ¬ ((p : ℤ) ∣ u) := by
          intro hpu
          have hdvd : ((p ^ (ν + 1) : ℕ) : ℤ) ∣ Q.derivative.eval (y0 : ℤ) := by
            rw [← hu_eq, Nat.cast_pow, Nat.cast_pow, pow_succ]
            exact mul_dvd_mul_left _ hpu
          exact int_not_dvd_succ_of_padicValNat_natAbs_eq (hQ'ne y0 hy0S) (hval y0 hy0S) hdvd
        have hH_unit : ¬ ((p : ℤ) ∣ H.eval (y0 : ℤ)) := by
          intro hpH
          have hdvd : (p : ℤ) ∣ Q.derivative.derivative.eval (y0 : ℤ) := by
            rw [← hH2]; exact dvd_mul_of_dvd_right hpH 2
          exact h3y y0 hy0S hdvd
        have hpdivZ : ∀ y ∈ fib, (p : ℤ) ∣ (y : ℤ) - (y0 : ℤ) := by
          intro y hy
          have hyres : y % p = r := ((fibmem y).mp hy).2
          have hmod : y % p = y0 % p := by rw [hyres, hy0res]
          have e1 := cast_decomp p y
          have e2 := cast_decomp p y0
          rw [e1, e2, hmod]
          exact ⟨(y / p : ℤ) - (y0 / p : ℤ), by push_cast; ring⟩
        have hdivNat : ∀ y ∈ fib, p ^ ν ∣ (y - y0) := by
          intro y hy
          have hyS : y ∈ S := ((fibmem y).mp hy).1
          have hdivZ : ((p ^ ν : ℕ) : ℤ) ∣ (y : ℤ) - (y0 : ℤ) :=
            clusterStep hν hA (int_dvd_of_padicValNat_natAbs_eq (hval y0 hy0S))
              (int_not_dvd_succ_of_padicValNat_natAbs_eq (hQ'ne y0 hy0S) (hval y0 hy0S))
              (h3y y0 hy0S) (hAy y hyS) (hAy y0 hy0S) (hpdivZ y hy)
          have hnat : (y : ℤ) - (y0 : ℤ) = ((y - y0 : ℕ) : ℤ) := by
            have hle : y0 ≤ y := hy0min y hy; omega
          rw [hnat] at hdivZ
          exact Int.natCast_dvd_natCast.mp hdivZ
        have hmap : Set.MapsTo (fun y : ℕ => (y - y0) / p ^ ν) ↑fib
            ↑((Finset.range (p ^ N)).filter (fun x : ℕ =>
              ((p ^ BB : ℕ) : ℤ) ∣ (x : ℤ) * u
                + (x : ℤ) ^ 2 * H.eval ((y0 : ℤ) + ((p ^ ν : ℕ) : ℤ) * (x : ℤ)))) := by
          intro y hy
          rw [Finset.mem_coe] at hy
          have hyfib : y ∈ fib := hy
          have hyS : y ∈ S := ((fibmem y).mp hyfib).1
          have hle : y0 ≤ y := hy0min y hyfib
          set x : ℕ := (y - y0) / p ^ ν with hx
          have hxmul : p ^ ν * x = y - y0 := by rw [hx]; exact Nat.mul_div_cancel' (hdivNat y hyfib)
          have hxlt : x < p ^ N := by
            have hlt : p ^ ν * x < p ^ M := by
              rw [hxmul]; exact lt_of_le_of_lt (Nat.sub_le y y0) (hMy y hyS)
            by_cases hMν : ν ≤ M
            · have hpM : p ^ ν * p ^ (M - ν) = p ^ M := by
                rw [← pow_add]; congr 1; omega
              rw [← hpM] at hlt
              have := (Nat.mul_lt_mul_left (pow_pos hp0 ν)).mp hlt
              rwa [hN]
            · have hMlt : M < ν := not_le.mp hMν
              have hN0 : N = 0 := by rw [hN]; omega
              rw [hN0, pow_zero]
              have h3 : p ^ ν * x < p ^ ν * 1 := by
                rw [mul_one]
                exact lt_of_lt_of_le hlt (pow_le_pow_right₀ (le_of_lt hp1) (le_of_lt hMlt))
              exact (Nat.mul_lt_mul_left (pow_pos hp0 ν)).mp h3
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          refine ⟨hxlt, ?_⟩
          have hxZ : ((y : ℤ) - (y0 : ℤ)) = ((p ^ ν : ℕ) : ℤ) * (x : ℤ) := by
            have h1 : ((y - y0 : ℕ) : ℤ) = ((p ^ ν * x : ℕ) : ℤ) := by rw [hxmul]
            have hnat : (y : ℤ) - (y0 : ℤ) = ((y - y0 : ℕ) : ℤ) := by omega
            rw [hnat, h1]; push_cast; ring
          have hyZ : (y : ℤ) = (y0 : ℤ) + ((p ^ ν : ℕ) : ℤ) * (x : ℤ) := by rw [← hxZ]; ring
          have hkey : Q.eval (y : ℤ) - Q.eval (y0 : ℤ)
              = (((p ^ ν : ℕ) : ℤ) * ((p ^ ν : ℕ) : ℤ)) * ((x : ℤ) * u
                  + (x : ℤ) ^ 2 * H.eval ((y0 : ℤ) + ((p ^ ν : ℕ) : ℤ) * (x : ℤ))) := by
            have h1 := hHexp (y : ℤ)
            rw [hxZ, ← hu_eq] at h1
            rw [h1]
            rw [hyZ]
            ring
          have hfac : ((p ^ A : ℕ) : ℤ)
              = (((p ^ ν : ℕ) : ℤ) * ((p ^ ν : ℕ) : ℤ)) * ((p ^ BB : ℕ) : ℤ) := by
            have h1 : (p ^ ν * p ^ ν) * p ^ BB = p ^ A := by
              rw [← pow_add, ← pow_add]; congr 1; omega
            rw [← h1]; push_cast; ring
          have hdvdA : (((p ^ ν : ℕ) : ℤ) * ((p ^ ν : ℕ) : ℤ)) * ((p ^ BB : ℕ) : ℤ)
              ∣ (((p ^ ν : ℕ) : ℤ) * ((p ^ ν : ℕ) : ℤ)) * ((x : ℤ) * u
                  + (x : ℤ) ^ 2 * H.eval ((y0 : ℤ) + ((p ^ ν : ℕ) : ℤ) * (x : ℤ))) := by
            have hsub : ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ) - Q.eval (y0 : ℤ) :=
              dvd_sub (hAy y hyS) (hAy y0 hy0S)
            rw [hkey] at hsub
            rwa [hfac] at hsub
          exact (mul_dvd_mul_iff_left (mul_ne_zero
            (by exact_mod_cast pow_ne_zero ν hpne0) (by exact_mod_cast pow_ne_zero ν hpne0))).mp hdvdA
        have hinj : Set.InjOn (fun y : ℕ => (y - y0) / p ^ ν) ↑fib := by
          intro a ha b hb hab
          have hafib : a ∈ fib := ha
          have hbfib : b ∈ fib := hb
          have hae : p ^ ν * ((a - y0) / p ^ ν) = a - y0 :=
            Nat.mul_div_cancel' (hdivNat a hafib)
          have hbe : p ^ ν * ((b - y0) / p ^ ν) = b - y0 :=
            Nat.mul_div_cancel' (hdivNat b hbfib)
          change (a - y0) / p ^ ν = (b - y0) / p ^ ν at hab
          rw [hab] at hae
          have heq : a - y0 = b - y0 := by rw [← hae, hbe]
          have hle1 : y0 ≤ a := hy0min a hafib
          have hle2 : y0 ≤ b := hy0min b hbfib
          omega
        refine le_trans (Finset.card_le_card_of_injOn (fun y : ℕ => (y - y0) / p ^ ν) hmap hinj) ?_
        exact countPsol hν hBB1 (y0 : ℤ) H u hu_unit hH_unit
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
    have hmain := Finset.card_le_mul_card_image_of_maps_to (f := fun y : ℕ => y % p) (s := S)
        (t := S.image (fun y : ℕ => y % p)) (fun a ha => Finset.mem_image_of_mem _ ha)
        (2 * p ^ (N - BB)) hfiber
    calc S.card ≤ (2 * p ^ (N - BB)) * (S.image (fun y : ℕ => y % p)).card := hmain
      _ ≤ (2 * p ^ (N - BB)) * 3 := Nat.mul_le_mul_left _ himgcard
      _ = 6 * p ^ (N - BB) := by ring
      _ = 6 * p ^ (M - min (A - ν) M) := by rw [hhexp]

end Work.LinnikBurgess

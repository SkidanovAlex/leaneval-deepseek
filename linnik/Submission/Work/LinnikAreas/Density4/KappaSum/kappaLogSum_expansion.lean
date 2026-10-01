import Mathlib
import Submission.Work.LinnikAreas.Density4.KappaDefs
import Submission.Work.LinnikAreas.Density4.KappaSum.kappa_divisors_identity
import Submission.Work.LinnikAreas.Density4.KappaSum.kappa_fiber_sum

namespace Work.LinnikAreas.Density4.KappaSum

open Finset
open scoped BigOperators

noncomputable section

/-- The outer index set `{1 ≤ d ≤ M : (d,r)=1}`. -/
abbrev Kset (M r : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r)

/-- The inner index set `{1 ≤ m ≤ ⌊z/d⌋ : (m,d*r)=1}`. -/
abbrev Kam (z : ℝ) (r d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊z / (d : ℝ)⌋₊).filter (fun m => Nat.Coprime m (d * r))

/-- The target index set `{1 ≤ n ≤ ⌊z⌋ : (n,r)=1}`. -/
abbrev Xset (z : ℝ) (r : ℕ) : Finset ℕ := (Finset.Icc 1 ⌊z⌋₊).filter (fun n => Nat.Coprime n r)

/-- The fiber over `n`: the divisors `d | n` with `(d, n/d) = 1`. -/
abbrev Bdset (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The summand of the double sum indexed by pairs `(d,m)`. -/
abbrev Fe (z : ℝ) (d m : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
    (((ArithmeticFunction.moebius m : ℝ)) / (m : ℝ)) * Real.log (z / ((d : ℝ) * (m : ℝ)))

/-- The summand of the double sum indexed by pairs `(n,d)`, `d | n`. -/
abbrev Ge (z : ℝ) (n d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
    (((ArithmeticFunction.moebius (n / d) : ℝ)) / ((n / d : ℕ) : ℝ)) * Real.log (z / (n : ℝ))

lemma floor_mul_le_iff {z : ℝ} {d m : ℕ} (hd : 1 ≤ d) :
    d * m ≤ ⌊z⌋₊ ↔ m ≤ ⌊z / (d : ℝ)⌋₊ := by
  rw [Nat.floor_div_natCast, Nat.le_div_iff_mul_le (by omega : 0 < d), Nat.mul_comm]

theorem kappaLogSum_expansion (z : ℝ) (r : ℕ) (hr : 1 ≤ r) {M : ℕ} (hM : ⌊z⌋₊ ≤ M) :
    kappaLogSum z r =
      ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d r),
        ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
          selTheta (z / (d : ℝ)) (d * r) := by
  rw [kappaLogSum]
  symm
  calc
    (∑ d ∈ Kset M r,
        ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
          selTheta (z / (d : ℝ)) (d * r))
        = ∑ d ∈ Kset M r, ∑ m ∈ Kam z r d, Fe z d m := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [selTheta, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [div_div]
          ring
    _ = ∑ n ∈ Xset z r, ∑ d ∈ Bdset n, Ge z n d := by
          have hsigmaL : (∑ d ∈ Kset M r, ∑ m ∈ Kam z r d, Fe z d m)
              = ∑ p ∈ (Kset M r).sigma (Kam z r), Fe z p.1 p.2 :=
            (Finset.sum_sigma (Kset M r) (Kam z r) (fun p => Fe z p.1 p.2)).symm
          have hsigmaR : (∑ n ∈ Xset z r, ∑ d ∈ Bdset n, Ge z n d)
              = ∑ q ∈ (Xset z r).sigma Bdset, Ge z q.1 q.2 :=
            (Finset.sum_sigma (Xset z r) Bdset (fun q => Ge z q.1 q.2)).symm
          rw [hsigmaL, hsigmaR]
          refine Finset.sum_nbij
            (fun p : Sigma (fun _ : ℕ => ℕ) => (⟨p.1 * p.2, p.1⟩ : Sigma (fun _ : ℕ => ℕ)))
            ?_ ?_ ?_ ?_
          · intro p hp
            obtain ⟨d, m⟩ := p
            rw [Finset.mem_sigma] at hp
            dsimp only at hp
            obtain ⟨hd, hm⟩ := hp
            rw [Kset, Finset.mem_filter, Finset.mem_Icc] at hd
            obtain ⟨⟨hd1, hdM⟩, hdr⟩ := hd
            rw [Kam, Finset.mem_filter, Finset.mem_Icc] at hm
            obtain ⟨⟨hm1, hmd⟩, hmr⟩ := hm
            refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
            · dsimp only
              rw [Xset, Finset.mem_filter, Finset.mem_Icc]
              exact ⟨⟨Nat.mul_pos (by omega : 0 < d) (by omega : 0 < m),
                  (floor_mul_le_iff hd1).mpr hmd⟩,
                Nat.Coprime.mul_left hdr (Nat.Coprime.coprime_dvd_right (dvd_mul_left r d) hmr)⟩
            · dsimp only
              rw [Bdset, Finset.mem_filter]
              refine ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right d m,
                  Nat.mul_ne_zero (by omega : d ≠ 0) (by omega : m ≠ 0)⟩, ?_⟩
              rw [Nat.mul_div_right m (by omega : 0 < d)]
              exact (Nat.Coprime.coprime_dvd_right (dvd_mul_right d r) hmr).symm
          · intro p hp p' hp' hab
            obtain ⟨d, m⟩ := p
            obtain ⟨d', m'⟩ := p'
            simp only [Finset.mem_coe, Finset.mem_sigma] at hp
            obtain ⟨hd, _⟩ := hp
            rw [Kset, Finset.mem_filter, Finset.mem_Icc] at hd
            obtain ⟨⟨hd1, _⟩, _⟩ := hd
            simp only [Sigma.mk.inj_iff, heq_eq_eq] at hab
            obtain ⟨h1, h2⟩ := hab
            subst h2
            have hm : m = m' := Nat.mul_left_cancel (by omega : 0 < d) h1
            subst hm
            rfl
          · intro q hq
            obtain ⟨n, d⟩ := q
            simp only [Finset.mem_coe, Finset.mem_sigma] at hq
            obtain ⟨hn, hd⟩ := hq
            rw [Xset, Finset.mem_filter, Finset.mem_Icc] at hn
            obtain ⟨⟨hn1, hnN⟩, hnr⟩ := hn
            rw [Bdset, Finset.mem_filter, Nat.mem_divisors] at hd
            obtain ⟨⟨hdvd, hn0⟩, hdcop⟩ := hd
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
            refine ⟨⟨d, n / d⟩, ?_, ?_⟩
            · rw [Finset.mem_coe, Finset.mem_sigma]
              refine ⟨?_, ?_⟩
              · dsimp only
                rw [Kset, Finset.mem_filter, Finset.mem_Icc]
                exact ⟨⟨by omega, le_trans (Nat.le_of_dvd (by omega) hdvd) (le_trans hnN hM)⟩,
                  Nat.Coprime.coprime_dvd_left hdvd hnr⟩
              · dsimp only
                rw [Kam, Finset.mem_filter, Finset.mem_Icc]
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · rw [Nat.le_div_iff_mul_le hdpos, one_mul]
                  exact Nat.le_of_dvd (by omega) hdvd
                · rw [← floor_mul_le_iff (by omega : 1 ≤ d), Nat.mul_div_cancel' hdvd]
                  exact hnN
                · rw [Nat.coprime_mul_iff_right]
                  exact ⟨hdcop.symm, Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd) hnr⟩
            · rw [Sigma.mk.inj_iff, heq_eq_eq]
              exact ⟨Nat.mul_div_cancel' hdvd, rfl⟩
          · intro p hp
            obtain ⟨d, m⟩ := p
            rw [Finset.mem_sigma] at hp
            dsimp only at hp
            obtain ⟨hd, _⟩ := hp
            rw [Kset, Finset.mem_filter, Finset.mem_Icc] at hd
            obtain ⟨⟨hd1, _⟩, _⟩ := hd
            show Fe z d m = Ge z (d * m) d
            simp only [Fe, Ge]
            rw [Nat.mul_div_right m (by omega : 0 < d), Nat.cast_mul]
    _ = ∑ n ∈ Xset z r,
            ((ArithmeticFunction.moebius n : ℝ)) / kappaR n * Real.log (z / (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
          rw [← Finset.sum_mul]
          rw [show (∑ d ∈ Bdset n,
                ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
                  (((ArithmeticFunction.moebius (n / d) : ℝ)) / ((n / d : ℕ) : ℝ)))
              = ∑ d ∈ Bdset n,
                ((ArithmeticFunction.moebius d : ℝ))^2 / ((d : ℝ) * kappaR d) *
                  ((ArithmeticFunction.moebius (n / d) : ℝ)) / ((n / d : ℕ) : ℝ) from by
                apply Finset.sum_congr rfl
                intro dd hdd
                ring]
          rw [kappa_fiber_sum n hn1]

end

end Work.LinnikAreas.Density4.KappaSum

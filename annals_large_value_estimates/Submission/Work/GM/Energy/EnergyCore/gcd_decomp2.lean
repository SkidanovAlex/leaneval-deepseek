import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- Splitting the pairs `(n₁,n₂) ∈ [N,2N]²` with `gcd(n₁,n₂) ≥ D₀` according to
`d = gcd(n₁,n₂)` and writing `n₁ = d n₁'`, `n₂ = d n₂'`: the pairs with a given `d` have
`n₁', n₂' ∈ [⌈N/d⌉, 2⌈N/d⌉]`. -/
theorem gcd_decomp (N : ℕ) (hN : 1 ≤ N) (D0 : ℝ) (W : Finset ℝ) :
    (∑ n1 ∈ Finset.Icc N (2 * N),
      ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D0 ≤ (Nat.gcd n1 n2 : ℝ)),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
    ≤ ∑ d ∈ Finset.Icc (⌈D0⌉₊) (2 * N),
        ∑ n1' ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ∑ n2' ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
            ‖Submission.GM.Rfun W ((n1' : ℝ) / (n2' : ℝ))‖ ^ 3 := by
  classical
  set P : Finset (ℕ × ℕ) := (Finset.Icc N (2 * N) ×ˢ Finset.Icc N (2 * N)).filter
      (fun p : ℕ × ℕ => D0 ≤ (Nat.gcd p.1 p.2 : ℝ)) with hP
  -- ### Step 1: the left-hand side is a sum over the filtered square `[N,2N]²`
  have hLHS :
      (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D0 ≤ (Nat.gcd n1 n2 : ℝ)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
      = ∑ p ∈ P, ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3 := by
    rw [hP]
    trans ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
        (if D0 ≤ (Nat.gcd n1 n2 : ℝ) then
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 else 0)
    · exact Finset.sum_congr rfl (fun n1 _ => Finset.sum_filter
        (s := Finset.Icc N (2 * N)) (p := fun n2 => D0 ≤ (Nat.gcd n1 n2 : ℝ))
        (f := fun n2 => ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3))
    · trans ∑ p ∈ Finset.Icc N (2 * N) ×ˢ Finset.Icc N (2 * N),
          (if D0 ≤ (Nat.gcd p.1 p.2 : ℝ) then
            ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3 else 0)
      · exact (Finset.sum_product (Finset.Icc N (2 * N)) (Finset.Icc N (2 * N))
          (fun q : ℕ × ℕ => (if D0 ≤ (Nat.gcd q.1 q.2 : ℝ) then
            ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3 else 0))).symm
      · exact (Finset.sum_filter (s := Finset.Icc N (2 * N) ×ˢ Finset.Icc N (2 * N))
          (p := fun p : ℕ × ℕ => D0 ≤ (Nat.gcd p.1 p.2 : ℝ))
          (f := fun p : ℕ × ℕ => ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3)).symm
  -- ### Step 2: split according to the value of the gcd
  have hmapsto : ∀ p ∈ P, Nat.gcd p.1 p.2 ∈ Finset.Icc (⌈D0⌉₊) (2 * N) := by
    intro p hp
    rw [hP] at hp
    obtain ⟨hpprod, hpcond⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpprod
    rw [Finset.mem_Icc] at ha hb ⊢
    exact ⟨Nat.ceil_le.mpr hpcond, le_trans (Nat.gcd_le_left p.2 (by omega)) ha.2⟩
  have hfib :
      (∑ p ∈ P, ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3)
      = ∑ d ∈ Finset.Icc (⌈D0⌉₊) (2 * N),
          ∑ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
            ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3 :=
    (Finset.sum_fiberwise_of_maps_to hmapsto
      (fun p : ℕ × ℕ => ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3)).symm
  -- ### Step 3: bound the fibre of each `d` by the square of reduced pairs
  have hper : ∀ d ∈ Finset.Icc (⌈D0⌉₊) (2 * N),
      (∑ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
        ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3)
      ≤ ∑ q ∈ (Finset.Icc (Md N d) (2 * Md N d) ×ˢ Finset.Icc (Md N d) (2 * Md N d)),
          ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3 := by
    intro d hd
    rcases (P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)).eq_empty_or_nonempty
      with hemp | ⟨p0, hp0⟩
    · rw [hemp, Finset.sum_empty]
      exact Finset.sum_nonneg fun q _ => by positivity
    · -- `d > 0` because the fibre is nonempty
      have hd1 : 1 ≤ d := by
        obtain ⟨hp0P, hp0d⟩ := Finset.mem_filter.mp hp0
        rw [hP] at hp0P
        obtain ⟨hp0prod, -⟩ := Finset.mem_filter.mp hp0P
        obtain ⟨ha0, -⟩ := Finset.mem_product.mp hp0prod
        rw [Finset.mem_Icc] at ha0
        have hg : 0 < Nat.gcd p0.1 p0.2 := Nat.gcd_pos_of_pos_left p0.2 (by omega)
        omega
      have hdvd_le : ∀ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
          d ∣ p.1 ∧ d ∣ p.2 := by
        intro p hp
        obtain ⟨-, hpd⟩ := Finset.mem_filter.mp hp
        exact ⟨by rw [← hpd]; exact Nat.gcd_dvd_left p.1 p.2,
               by rw [← hpd]; exact Nat.gcd_dvd_right p.1 p.2⟩
      have hInj : Set.InjOn (fun p : ℕ × ℕ => (p.1 / d, p.2 / d))
          ↑(P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)) := by
        intro p hp q hq hpq
        obtain ⟨hp1, hp2⟩ := hdvd_le p hp
        obtain ⟨hq1, hq2⟩ := hdvd_le q hq
        have hf : p.1 / d = q.1 / d := by simpa using congrArg Prod.fst hpq
        have hs : p.2 / d = q.2 / d := by simpa using congrArg Prod.snd hpq
        exact Prod.ext (by rw [← Nat.mul_div_cancel' hp1, hf, Nat.mul_div_cancel' hq1])
          (by rw [← Nat.mul_div_cancel' hp2, hs, Nat.mul_div_cancel' hq2])
      have hterm : ∀ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
          ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3
            = ‖Submission.GM.Rfun W (((p.1 / d : ℕ) : ℝ) / ((p.2 / d : ℕ) : ℝ))‖ ^ 3 := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := hdvd_le p hp
        have hdR : (0 : ℝ) < (d : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
        have e1 : ((p.1 : ℕ) : ℝ) = (d : ℝ) * ((p.1 / d : ℕ) : ℝ) := by
          have h := congrArg (fun m : ℕ => (m : ℝ)) (Nat.mul_div_cancel' hp1)
          push_cast at h
          exact h.symm
        have e2 : ((p.2 : ℕ) : ℝ) = (d : ℝ) * ((p.2 / d : ℕ) : ℝ) := by
          have h := congrArg (fun m : ℕ => (m : ℝ)) (Nat.mul_div_cancel' hp2)
          push_cast at h
          exact h.symm
        rw [e1, e2, mul_div_mul_left _ _ (ne_of_gt hdR)]
      have hsub : (P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)).image
            (fun p : ℕ × ℕ => (p.1 / d, p.2 / d))
          ⊆ Finset.Icc (Md N d) (2 * Md N d) ×ˢ Finset.Icc (Md N d) (2 * Md N d) := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨hpP, hpd⟩ := Finset.mem_filter.mp hp
        rw [hP] at hpP
        obtain ⟨hpprod, -⟩ := Finset.mem_filter.mp hpP
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpprod
        rw [Finset.mem_Icc] at ha hb
        have hdvd1 : d ∣ p.1 := by rw [← hpd]; exact Nat.gcd_dvd_left p.1 p.2
        have hdvd2 : d ∣ p.2 := by rw [← hpd]; exact Nat.gcd_dvd_right p.1 p.2
        have hdne : (d : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd1))
        -- lower bound `⌈N/d⌉ ≤ m/d` for `d ∣ m`, `N ≤ m`
        have hlow : ∀ m : ℕ, N ≤ m → d ∣ m → Md N d ≤ m / d := by
          intro m hm hdm
          refine Nat.ceil_le.mpr ?_
          rw [Nat.cast_div hdm hdne]
          exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)
        -- upper bound `m/d ≤ 2⌈N/d⌉` for `m ≤ 2N`
        have hup : ∀ m : ℕ, m ≤ 2 * N → m / d ≤ 2 * Md N d := by
          intro m hm
          have hmR : ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / (d : ℝ) := Nat.cast_div_le
          have hm2 : (m : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hm
          have h6 : (m : ℝ) / (d : ℝ) ≤ 2 * (Md N d : ℝ) := by
            have h4 : (m : ℝ) / (d : ℝ) ≤ (2 * (N : ℝ)) / (d : ℝ) :=
              div_le_div_of_nonneg_right hm2 (by positivity)
            have h5 : (2 * (N : ℝ)) / (d : ℝ) = 2 * ((N : ℝ) / (d : ℝ)) := by ring
            rw [h5] at h4
            have h7 : 2 * ((N : ℝ) / (d : ℝ)) ≤ 2 * (Md N d : ℝ) := by
              have := le_Md N d
              linarith
            linarith
          have h8 : ((m / d : ℕ) : ℝ) ≤ ((2 * Md N d : ℕ) : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_ofNat]
            exact le_trans hmR h6
          exact_mod_cast h8
        exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hlow p.1 ha.1 hdvd1, hup p.1 ha.2⟩,
           Finset.mem_Icc.mpr ⟨hlow p.2 hb.1 hdvd2, hup p.2 hb.2⟩⟩
      calc (∑ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
              ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3)
          = ∑ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
              ‖Submission.GM.Rfun W (((p.1 / d : ℕ) : ℝ) / ((p.2 / d : ℕ) : ℝ))‖ ^ 3 :=
            Finset.sum_congr rfl hterm
        _ = ∑ q ∈ (P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d)).image
                (fun p : ℕ × ℕ => (p.1 / d, p.2 / d)),
              ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3 :=
            (Finset.sum_image
              (f := fun q : ℕ × ℕ => ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3)
              hInj).symm
        _ ≤ ∑ q ∈ (Finset.Icc (Md N d) (2 * Md N d) ×ˢ Finset.Icc (Md N d) (2 * Md N d)),
              ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
  -- ### Step 4: assemble
  calc (∑ n1 ∈ Finset.Icc N (2 * N),
      ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D0 ≤ (Nat.gcd n1 n2 : ℝ)),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
      = ∑ p ∈ P, ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3 := hLHS
    _ = ∑ d ∈ Finset.Icc (⌈D0⌉₊) (2 * N),
          ∑ p ∈ P.filter (fun p : ℕ × ℕ => Nat.gcd p.1 p.2 = d),
            ‖Submission.GM.Rfun W ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 3 := hfib
    _ ≤ ∑ d ∈ Finset.Icc (⌈D0⌉₊) (2 * N),
          ∑ q ∈ (Finset.Icc (Md N d) (2 * Md N d) ×ˢ Finset.Icc (Md N d) (2 * Md N d)),
            ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3 :=
        Finset.sum_le_sum hper
    _ = ∑ d ∈ Finset.Icc (⌈D0⌉₊) (2 * N),
        ∑ n1' ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d)
            (2 * Work.GM.Energy.EnergyCore.Md N d),
          ∑ n2' ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d)
              (2 * Work.GM.Energy.EnergyCore.Md N d),
            ‖Submission.GM.Rfun W ((n1' : ℝ) / (n2' : ℝ))‖ ^ 3 := by
        exact Finset.sum_congr rfl (fun d _ => Finset.sum_product
          (Finset.Icc (Md N d) (2 * Md N d)) (Finset.Icc (Md N d) (2 * Md N d))
          (fun q : ℕ × ℕ => ‖Submission.GM.Rfun W ((q.1 : ℝ) / (q.2 : ℝ))‖ ^ 3))

end Work.GM.Energy.EnergyCore

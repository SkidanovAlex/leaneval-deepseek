import Mathlib
import Submission.Commons.Measure.Lattice.card_int_lattice_le_volume_ball_three

namespace Commons.NumberTheory.Diophantine

namespace GaussCircleAux

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

def embZ (z : ℤ × ℤ) : Fin 2 → ℝ := ![(z.1 : ℝ), (z.2 : ℝ)]

lemma embZ_zero (z : ℤ × ℤ) : embZ z 0 = (z.1 : ℝ) := by simp [embZ]
lemma embZ_one (z : ℤ × ℤ) : embZ z 1 = (z.2 : ℝ) := by simp [embZ]

def unitCube (z : ℤ × ℤ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi (fun i : Fin 2 => Set.Ico (embZ z i - 1/2) (embZ z i + 1/2))

lemma unitCube_volume (z : ℤ × ℤ) : volume (unitCube z) = 1 := by
  have hpt : ∀ i : Fin 2, volume (Set.Ico (embZ z i - 1/2) (embZ z i + 1/2)) = 1 := by
    intro i; rw [Real.volume_Ico]
    have : (embZ z i + 1/2) - (embZ z i - 1/2) = 1 := by ring
    rw [this, ENNReal.ofReal_one]
  simp only [unitCube]; rw [volume_pi_pi]
  rw [Finset.prod_congr rfl (fun i _ => hpt i)]; simp

lemma unitCube_measurable (z : ℤ × ℤ) : MeasurableSet (unitCube z) := by
  simp only [unitCube]; exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)

lemma unitCube_disjoint {z z' : ℤ × ℤ} (h : z ≠ z') : Disjoint (unitCube z) (unitCube z') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [unitCube, Set.mem_univ_pi] at hx hx'
  have hne : z.1 ≠ z'.1 ∨ z.2 ≠ z'.2 := by
    by_contra hc; push Not at hc
    exact h (Prod.ext hc.1 hc.2)
  rcases hne with h1 | h2
  · exact Commons.Measure.Lattice.Ico_int_disjoint h1 (x 0)
      (by simpa [embZ_zero] using hx 0) (by simpa [embZ_zero] using hx' 0)
  · exact Commons.Measure.Lattice.Ico_int_disjoint h2 (x 1)
      (by simpa [embZ_one] using hx 1) (by simpa [embZ_one] using hx' 1)

def disk2 (s : ℝ) : Set (Fin 2 → ℝ) := {x | Real.sqrt (∑ i : Fin 2, (x i)^2) ≤ s}

lemma volume_disk2 (s : ℝ) (hs : 0 ≤ s) :
    volume (disk2 s) = ENNReal.ofReal (Real.pi * s ^ 2) := by
  have hset : disk2 s = {x : Fin 2 → ℝ | (∑ i : Fin 2, |x i| ^ (2:ℝ)) ^ ((1:ℝ)/2) ≤ s} := by
    ext x; simp only [disk2, Set.mem_ofPred_eq]
    rw [show (∑ i : Fin 2, |x i| ^ (2:ℝ)) = ∑ i : Fin 2, (x i)^2 from by
      apply Finset.sum_congr rfl; intro i _; rw [Real.rpow_two, sq_abs]]
    rw [← Real.sqrt_eq_rpow]
  rw [hset, MeasureTheory.volume_sum_rpow_le (Fin 2) (by norm_num : (1:ℝ) ≤ 2) s]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  have hg : (2 * Real.Gamma (1 / (2:ℝ) + 1)) ^ 2 / Real.Gamma ((2:ℝ) / 2 + 1) = Real.pi := by
    have h1 : Real.Gamma (1/2 + 1 : ℝ) = Real.sqrt Real.pi / 2 := by
      rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
    have h2 : Real.Gamma ((2:ℝ)/2 + 1) = 1 := by norm_num [Real.Gamma_two]
    rw [h2, h1, div_one]
    rw [show 2 * (Real.sqrt Real.pi / 2) = Real.sqrt Real.pi by ring]
    rw [pow_two, Real.mul_self_sqrt Real.pi_nonneg]
  rw [hg, ← ENNReal.ofReal_pow hs, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ s^2)]
  congr 1; ring

lemma union_volume (L : Finset (ℤ × ℤ)) :
    volume (⋃ z ∈ L, unitCube z) = (L.card : ENNReal) := by
  rw [MeasureTheory.measure_biUnion_finset (fun a ha b hb hab => unitCube_disjoint hab)
        (fun b _ => unitCube_measurable b)]
  rw [Finset.sum_congr rfl (fun b _ => unitCube_volume b)]
  simp

lemma half_sq_sum_eq :
    (∑ _i : Fin 2, (1/2:ℝ)^2) = (Real.sqrt 2 / 2)^2 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (Real.sqrt 2 / 2)^2 = (1/2:ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rw [h]; norm_num

lemma card_le_disk (L : Finset (ℤ × ℤ)) (R : ℝ) (hR0 : 0 ≤ R)
    (hL : ∀ z ∈ L, Real.sqrt (∑ i : Fin 2, (embZ z i)^2) ≤ R) :
    (L.card : ℝ) ≤ Real.pi * (R + Real.sqrt 2 / 2)^2 := by
  have hsub : (⋃ z ∈ L, unitCube z) ⊆ disk2 (R + Real.sqrt 2 / 2) := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨z, hz, hxz⟩ := hx
    simp only [unitCube, Set.mem_univ_pi] at hxz
    have hzR : Real.sqrt (∑ i : Fin 2, (embZ z i)^2) ≤ R := hL z hz
    have hstep : ∀ i : Fin 2, (x i - embZ z i)^2 ≤ (1/2:ℝ)^2 := by
      intro i
      have hi := hxz i; rw [Set.mem_Ico] at hi
      exact sq_le_sq' (by linarith [hi.1]) (by linarith [hi.2])
    have hsum : (∑ i : Fin 2, (x i - embZ z i)^2) ≤ (Real.sqrt 2 / 2)^2 := by
      calc (∑ i : Fin 2, (x i - embZ z i)^2) ≤ ∑ _i : Fin 2, (1/2:ℝ)^2 :=
            Finset.sum_le_sum (fun i _ => hstep i)
        _ = (Real.sqrt 2 / 2)^2 := half_sq_sum_eq
    have hd : Real.sqrt (∑ i : Fin 2, (x i - embZ z i)^2) ≤ Real.sqrt 2 / 2 :=
      calc Real.sqrt (∑ i : Fin 2, (x i - embZ z i)^2)
          ≤ Real.sqrt ((Real.sqrt 2/2)^2) := Real.sqrt_le_sqrt hsum
        _ = Real.sqrt 2 / 2 := Real.sqrt_sq (by positivity)
    have hkey := Commons.Measure.Lattice.sqrt_sum_sq_add_le (embZ z) (fun i => x i - embZ z i)
    have hleft : (∑ i : Fin 2, (embZ z i + (x i - embZ z i))^2) = (∑ i : Fin 2, (x i)^2) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hleft] at hkey
    simp only [disk2, Set.mem_ofPred_eq]
    linarith [hkey, hzR, hd]
  have hunionvol := union_volume L
  have hs : (0:ℝ) ≤ R + Real.sqrt 2 / 2 := by
    have h : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    linarith
  have hle : (L.card : ENNReal) ≤ ENNReal.ofReal (Real.pi * (R + Real.sqrt 2 / 2)^2) := by
    rw [← hunionvol, ← volume_disk2 (R + Real.sqrt 2 / 2) hs]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (mul_nonneg Real.pi_nonneg (sq_nonneg _))] at h2
  exact h2

noncomputable def near (x : Fin 2 → ℝ) : ℤ × ℤ := (⌊x 0 + 1/2⌋, ⌊x 1 + 1/2⌋)

lemma embZ_near_apply (x : Fin 2 → ℝ) (i : Fin 2) :
    embZ (near x) i = (⌊x i + 1/2⌋ : ℝ) := by
  fin_cases i <;> simp [embZ, near]

lemma near_spec (x : Fin 2 → ℝ) (i : Fin 2) :
    x i ∈ Set.Ico (embZ (near x) i - 1/2) (embZ (near x) i + 1/2) := by
  rw [Set.mem_Ico, embZ_near_apply]
  constructor
  · have := Int.floor_le (x i + 1/2); linarith
  · have := Int.lt_floor_add_one (x i + 1/2); linarith

lemma len_sub_near (x : Fin 2 → ℝ) :
    Real.sqrt (∑ i : Fin 2, (x i - embZ (near x) i)^2) ≤ Real.sqrt 2 / 2 := by
  have hstep : ∀ i : Fin 2, (x i - embZ (near x) i)^2 ≤ (1/2:ℝ)^2 := by
    intro i; have hi := near_spec x i; rw [Set.mem_Ico] at hi
    exact sq_le_sq' (by linarith [hi.1]) (by linarith [hi.2])
  have hsum : (∑ i : Fin 2, (x i - embZ (near x) i)^2) ≤ (Real.sqrt 2 / 2)^2 := by
    calc (∑ i : Fin 2, (x i - embZ (near x) i)^2) ≤ ∑ _i : Fin 2, (1/2:ℝ)^2 :=
          Finset.sum_le_sum (fun i _ => hstep i)
      _ = (Real.sqrt 2 / 2)^2 := half_sq_sum_eq
  calc Real.sqrt (∑ i : Fin 2, (x i - embZ (near x) i)^2)
      ≤ Real.sqrt ((Real.sqrt 2/2)^2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 / 2 := Real.sqrt_sq (by positivity)

lemma len_gap_near (x : Fin 2 → ℝ) :
    Real.sqrt (∑ i : Fin 2, (embZ (near x) i - x i)^2) ≤ Real.sqrt 2 / 2 := by
  have hstep : ∀ i : Fin 2, (embZ (near x) i - x i)^2 ≤ (1/2:ℝ)^2 := by
    intro i; have hi := near_spec x i; rw [Set.mem_Ico] at hi
    exact sq_le_sq' (by linarith [hi.2]) (by linarith [hi.1])
  have hsum : (∑ i : Fin 2, (embZ (near x) i - x i)^2) ≤ (Real.sqrt 2 / 2)^2 := by
    calc (∑ i : Fin 2, (embZ (near x) i - x i)^2) ≤ ∑ _i : Fin 2, (1/2:ℝ)^2 :=
          Finset.sum_le_sum (fun i _ => hstep i)
      _ = (Real.sqrt 2 / 2)^2 := half_sq_sum_eq
  calc Real.sqrt (∑ i : Fin 2, (embZ (near x) i - x i)^2)
      ≤ Real.sqrt ((Real.sqrt 2/2)^2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 / 2 := Real.sqrt_sq (by positivity)

lemma len_near_le (x : Fin 2 → ℝ) :
    Real.sqrt (∑ i : Fin 2, (embZ (near x) i)^2)
      ≤ Real.sqrt (∑ i : Fin 2, (x i)^2) + Real.sqrt 2 / 2 := by
  have hkey := Commons.Measure.Lattice.sqrt_sum_sq_add_le (fun i : Fin 2 => x i)
    (fun i => embZ (near x) i - x i)
  have hleft : (∑ i : Fin 2, (x i + (embZ (near x) i - x i))^2)
      = (∑ i : Fin 2, (embZ (near x) i)^2) := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hleft] at hkey
  linarith [hkey, len_gap_near x]

lemma disk_le_card (L : Finset (ℤ × ℤ)) (R : ℝ) (hR : Real.sqrt 2 / 2 ≤ R)
    (hL : ∀ z : ℤ × ℤ, Real.sqrt (∑ i : Fin 2, (embZ z i)^2) ≤ R → z ∈ L) :
    Real.pi * (R - Real.sqrt 2 / 2)^2 ≤ (L.card : ℝ) := by
  have hsub : disk2 (R - Real.sqrt 2/2) ⊆ (⋃ z ∈ L, unitCube z) := by
    intro x hx
    simp only [disk2, Set.mem_ofPred_eq] at hx
    refine Set.mem_iUnion.2 ⟨near x, Set.mem_iUnion.2 ⟨hL (near x) ?_, ?_⟩⟩
    · linarith [len_near_le x, hx]
    · simp only [unitCube, Set.mem_univ_pi]
      exact fun i => near_spec x i
  have hunionvol := union_volume L
  have hle : ENNReal.ofReal (Real.pi * (R - Real.sqrt 2 / 2)^2) ≤ (L.card : ENNReal) := by
    rw [← volume_disk2 (R - Real.sqrt 2 / 2) (by linarith), ← hunionvol]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono (ENNReal.natCast_ne_top L.card) hle
  rw [ENNReal.toReal_ofReal (mul_nonneg Real.pi_nonneg (sq_nonneg _)),
      ENNReal.toReal_natCast] at h2
  exact h2


end GaussCircleAux

open GaussCircleAux in
theorem gauss_circle_theorem : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
    |((Finset.filter (fun z : ℤ × ℤ => z.1 ^ 2 + z.2 ^ 2 ≤ (X : ℤ))
        (Finset.Icc (-(X : ℤ)) (X : ℤ) ×ˢ Finset.Icc (-(X : ℤ)) (X : ℤ))).card : ℝ)
      - Real.pi * (X : ℝ)| ≤ C * Real.sqrt (X : ℝ) := by
  refine ⟨Real.pi * (Real.sqrt 2 + 1/2), by positivity, ?_⟩
  intro X hX
  set L : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(X : ℤ)) (X : ℤ) ×ˢ Finset.Icc (-(X : ℤ)) (X : ℤ)).filter
      (fun z => z.1 ^ 2 + z.2 ^ 2 ≤ (X : ℤ)) with hLdef
  set R : ℝ := Real.sqrt (X : ℝ) with hRdef
  have hX1 : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hX0 : (0:ℝ) ≤ (X:ℝ) := by positivity
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (X:ℝ) := Real.sqrt_le_sqrt hX1
  have hR2 : R^2 = (X:ℝ) := by rw [hRdef]; exact Real.sq_sqrt hX0
  have hsqrtX_le : Real.sqrt (X:ℝ) ≤ (X:ℝ) := by
    nlinarith [Real.sq_sqrt hX0, Real.sqrt_nonneg (X:ℝ)]
  have ha2 : (Real.sqrt 2 / 2)^2 = (1/2:ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  -- upper bound
  have hupper : (L.card : ℝ) ≤ Real.pi * (R + Real.sqrt 2 / 2)^2 := by
    apply card_le_disk L R hR0
    intro z hz
    have hz' : z.1^2 + z.2^2 ≤ (X:ℤ) := (Finset.mem_filter.mp hz).2
    have h1 : (z.1:ℝ)^2 + (z.2:ℝ)^2 ≤ R^2 := by
      rw [hR2]; exact_mod_cast hz'
    calc Real.sqrt (∑ i : Fin 2, (embZ z i)^2)
        ≤ Real.sqrt (R^2) := Real.sqrt_le_sqrt (by
              rw [Fin.sum_univ_two]; simpa [embZ_zero, embZ_one] using h1)
      _ = R := Real.sqrt_sq hR0
  -- lower bound
  have hlower : Real.pi * (R - Real.sqrt 2 / 2)^2 ≤ (L.card : ℝ) := by
    apply disk_le_card L R _ _
    · have hsqrt2 : Real.sqrt 2 / 2 ≤ 1 := by
        rw [div_le_one (by norm_num : (0:ℝ) < 2)]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
      linarith [hR1]
    · intro z hz
      rw [Finset.mem_filter, Finset.mem_product]
      have hsum : (∑ i : Fin 2, (embZ z i)^2) ≤ R^2 := (Real.sqrt_le_iff.mp hz).2
      have h1 : (z.1:ℝ)^2 + (z.2:ℝ)^2 ≤ (X:ℝ) := by
        rw [Fin.sum_univ_two, hR2] at hsum
        simpa [embZ_zero, embZ_one] using hsum
      have hz1abs : |(z.1:ℝ)| ≤ (X:ℝ) :=
        calc |(z.1:ℝ)| = Real.sqrt ((z.1:ℝ)^2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (X:ℝ) := Real.sqrt_le_sqrt (by nlinarith [h1, sq_nonneg (z.2:ℝ)])
          _ ≤ (X:ℝ) := hsqrtX_le
      have hz2abs : |(z.2:ℝ)| ≤ (X:ℝ) :=
        calc |(z.2:ℝ)| = Real.sqrt ((z.2:ℝ)^2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (X:ℝ) := Real.sqrt_le_sqrt (by nlinarith [h1, sq_nonneg (z.1:ℝ)])
          _ ≤ (X:ℝ) := hsqrtX_le
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · have hh : (-(X:ℤ) : ℝ) ≤ (z.1:ℝ) := by
            push_cast; linarith [neg_abs_le (z.1:ℝ), hz1abs]
          exact_mod_cast hh
        · have hh : (z.1:ℝ) ≤ (X:ℝ) := by linarith [le_abs_self (z.1:ℝ), hz1abs]
          exact_mod_cast hh
      · rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · have hh : (-(X:ℤ) : ℝ) ≤ (z.2:ℝ) := by
            push_cast; linarith [neg_abs_le (z.2:ℝ), hz2abs]
          exact_mod_cast hh
        · have hh : (z.2:ℝ) ≤ (X:ℝ) := by linarith [le_abs_self (z.2:ℝ), hz2abs]
          exact_mod_cast hh
      · exact_mod_cast h1
  -- combine
  have hmid : |(L.card : ℝ) - Real.pi * (X:ℝ)| ≤ Real.pi * (Real.sqrt 2 * R + 1/2) := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [hlower, ha2, Real.pi_pos, hR2]
    · nlinarith [hupper, ha2, Real.pi_pos, hR2]
  calc |(L.card : ℝ) - Real.pi * (X:ℝ)| ≤ Real.pi * (Real.sqrt 2 * R + 1/2) := hmid
    _ ≤ Real.pi * (Real.sqrt 2 + 1/2) * R := by nlinarith [hR1, Real.pi_pos]

end Commons.NumberTheory.Diophantine

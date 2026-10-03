import Mathlib
import Submission.Commons.NumberTheory.Diophantine.gauss_circle_theorem

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Commons.NumberTheory.Diophantine

namespace LatticeDiskAux

/-- The closed disk of radius `s` centred at `c` in `Fin 2 → ℝ`. -/
def diskC (c : Fin 2 → ℝ) (s : ℝ) : Set (Fin 2 → ℝ) :=
  {x | Real.sqrt (∑ i : Fin 2, (x i - c i)^2) ≤ s}

/-- Volume of a disk in the plane is `π s²`, independently of the centre. -/
lemma volume_diskC (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    volume (diskC c s) = ENNReal.ofReal (Real.pi * s ^ 2) := by
  have hsum : ∀ h : Fin 2 → ℝ,
      (∑ i : Fin 2, ((c + h) i - c i)^2) = (∑ i : Fin 2, (h i)^2) := by
    intro h
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    ring
  have hpre : (fun h : Fin 2 → ℝ => c + h) ⁻¹' diskC c s =
      {x : Fin 2 → ℝ | Real.sqrt (∑ i : Fin 2, (x i)^2) ≤ s} := by
    ext h
    simp only [Set.mem_preimage, diskC, Set.mem_ofPred_eq]
    rw [hsum h]
  have h : volume (diskC c s) =
      volume {x : Fin 2 → ℝ | Real.sqrt (∑ i : Fin 2, (x i)^2) ≤ s} := by
    rw [← measure_preimage_add volume c (diskC c s), hpre]
  rw [h]
  exact GaussCircleAux.volume_disk2 s hs

/-- Upper bound: the number of lattice points in a disk of radius `R` (any centre) is at
most the area of the disk of radius `R + √2/2`. -/
lemma card_le_diskC (c : Fin 2 → ℝ) (L : Finset (ℤ × ℤ)) (R : ℝ) (hR0 : 0 ≤ R)
    (hL : ∀ z ∈ L, Real.sqrt (∑ i : Fin 2, (GaussCircleAux.embZ z i - c i)^2) ≤ R) :
    (L.card : ℝ) ≤ Real.pi * (R + Real.sqrt 2 / 2)^2 := by
  have hsub : (⋃ z ∈ L, GaussCircleAux.unitCube z) ⊆ diskC c (R + Real.sqrt 2 / 2) := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨z, hz, hxz⟩ := hx
    simp only [GaussCircleAux.unitCube, Set.mem_univ_pi] at hxz
    have hzR : Real.sqrt (∑ i : Fin 2, (GaussCircleAux.embZ z i - c i)^2) ≤ R := hL z hz
    have hstep : ∀ i : Fin 2, (x i - GaussCircleAux.embZ z i)^2 ≤ (1/2:ℝ)^2 := by
      intro i
      have hi := hxz i; rw [Set.mem_Ico] at hi
      exact sq_le_sq' (by linarith [hi.1]) (by linarith [hi.2])
    have hsum : (∑ i : Fin 2, (x i - GaussCircleAux.embZ z i)^2) ≤ (Real.sqrt 2 / 2)^2 := by
      calc (∑ i : Fin 2, (x i - GaussCircleAux.embZ z i)^2) ≤ ∑ _i : Fin 2, (1/2:ℝ)^2 :=
            Finset.sum_le_sum (fun i _ => hstep i)
        _ = (Real.sqrt 2 / 2)^2 := GaussCircleAux.half_sq_sum_eq
    have hd : Real.sqrt (∑ i : Fin 2, (x i - GaussCircleAux.embZ z i)^2) ≤ Real.sqrt 2 / 2 :=
      calc Real.sqrt (∑ i : Fin 2, (x i - GaussCircleAux.embZ z i)^2)
          ≤ Real.sqrt ((Real.sqrt 2/2)^2) := Real.sqrt_le_sqrt hsum
        _ = Real.sqrt 2 / 2 := Real.sqrt_sq (by positivity)
    have hkey := Commons.Measure.Lattice.sqrt_sum_sq_add_le
      (fun i => GaussCircleAux.embZ z i - c i) (fun i => x i - GaussCircleAux.embZ z i)
    have hleft : (∑ i : Fin 2, ((GaussCircleAux.embZ z i - c i) + (x i - GaussCircleAux.embZ z i))^2)
        = (∑ i : Fin 2, (x i - c i)^2) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hleft] at hkey
    simp only [diskC, Set.mem_ofPred_eq]
    linarith [hkey, hzR, hd]
  have hunionvol := GaussCircleAux.union_volume L
  have hs : (0:ℝ) ≤ R + Real.sqrt 2 / 2 := by
    have : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    linarith
  have hle : (L.card : ENNReal) ≤ ENNReal.ofReal (Real.pi * (R + Real.sqrt 2 / 2)^2) := by
    rw [← hunionvol, ← volume_diskC c (R + Real.sqrt 2/2) hs]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (mul_nonneg Real.pi_nonneg (sq_nonneg _))] at h2
  exact h2

/-- Lower bound: if `√2/2 ≤ R`, then the number of lattice points in a disk of radius `R`
(any centre) is at least the area of the disk of radius `R - √2/2`. -/
lemma disk_le_cardC (c : Fin 2 → ℝ) (L : Finset (ℤ × ℤ)) (R : ℝ) (hR : Real.sqrt 2 / 2 ≤ R)
    (hL : ∀ z : ℤ × ℤ, Real.sqrt (∑ i : Fin 2, (GaussCircleAux.embZ z i - c i)^2) ≤ R → z ∈ L) :
    Real.pi * (R - Real.sqrt 2 / 2)^2 ≤ (L.card : ℝ) := by
  have hsub : diskC c (R - Real.sqrt 2/2) ⊆ (⋃ z ∈ L, GaussCircleAux.unitCube z) := by
    intro x hx
    simp only [diskC, Set.mem_ofPred_eq] at hx
    refine Set.mem_iUnion.2 ⟨GaussCircleAux.near x, Set.mem_iUnion.2 ⟨hL (GaussCircleAux.near x) ?_, ?_⟩⟩
    · have hkey := Commons.Measure.Lattice.sqrt_sum_sq_add_le
        (fun i => x i - c i) (fun i => GaussCircleAux.embZ (GaussCircleAux.near x) i - x i)
      have hleft : (∑ i : Fin 2, ((x i - c i) + (GaussCircleAux.embZ (GaussCircleAux.near x) i - x i))^2)
          = (∑ i : Fin 2, (GaussCircleAux.embZ (GaussCircleAux.near x) i - c i)^2) := by
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hleft] at hkey
      linarith [hkey, hx, GaussCircleAux.len_gap_near x]
    · simp only [GaussCircleAux.unitCube, Set.mem_univ_pi]
      exact fun i => GaussCircleAux.near_spec x i
  have hunionvol := GaussCircleAux.union_volume L
  have hle : ENNReal.ofReal (Real.pi * (R - Real.sqrt 2 / 2)^2) ≤ (L.card : ENNReal) := by
    rw [← volume_diskC c (R - Real.sqrt 2 / 2) (by linarith), ← hunionvol]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono (ENNReal.natCast_ne_top L.card) hle
  rw [ENNReal.toReal_ofReal (mul_nonneg Real.pi_nonneg (sq_nonneg _)), ENNReal.toReal_natCast] at h2
  exact h2

end LatticeDiskAux

open LatticeDiskAux in
/-- An elementary `O(R)` bound for the Gauss circle problem: the number of integer lattice
points in a disk of radius `R` centred anywhere in the plane differs from the area `π R²`
by at most `C (R + 1)`. -/
theorem lattice_disk_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (c : ℝ × ℝ), 0 ≤ R →
      |(({z : ℤ × ℤ | (z.1 - c.1) ^ 2 + (z.2 - c.2) ^ 2 ≤ R ^ 2}).ncard : ℝ)
          - Real.pi * R ^ 2| ≤ C * (R + 1) := by
  refine ⟨Real.pi * (Real.sqrt 2 + 1), by positivity, ?_⟩
  intro R c hR
  set s : ℝ := Real.sqrt 2 / 2 with hsdef
  set cfun : Fin 2 → ℝ := ![c.1, c.2] with hcfun
  set a1 : ℤ := ⌈c.1 - R⌉ with ha1
  set b1 : ℤ := ⌊c.1 + R⌋ with hb1
  set a2 : ℤ := ⌈c.2 - R⌉ with ha2
  set b2 : ℤ := ⌊c.2 + R⌋ with hb2
  set F : Finset (ℤ × ℤ) := (Finset.Icc a1 b1) ×ˢ (Finset.Icc a2 b2) with hF
  set G : Finset (ℤ × ℤ) :=
    F.filter (fun z : ℤ × ℤ => (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2) with hG
  have hcfun_0 : cfun 0 = c.1 := by simp [hcfun]
  have hcfun_1 : cfun 1 = c.2 := by simp [hcfun]
  have hsumC : ∀ z : ℤ × ℤ,
      (∑ i : Fin 2, (GaussCircleAux.embZ z i - cfun i)^2) =
        (z.1 - c.1)^2 + (z.2 - c.2)^2 := by
    intro z
    rw [Fin.sum_univ_two]
    simp only [GaussCircleAux.embZ_zero, GaussCircleAux.embZ_one, hcfun_0, hcfun_1]
  have hGmem : ∀ z : ℤ × ℤ, z ∈ G ↔
      (z ∈ F ∧ (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2) := by
    intro z; rw [hG]; exact Finset.mem_filter
  have box_mem : ∀ z : ℤ × ℤ, (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2 → z ∈ F := by
    intro z hz
    have hx1 : |(z.1:ℝ) - c.1| ≤ R := by
      have h2 : ((z.1:ℝ) - c.1)^2 ≤ R^2 := by
        nlinarith [sq_nonneg ((z.2:ℝ) - c.2), hz]
      calc |(z.1:ℝ) - c.1| = Real.sqrt (((z.1:ℝ) - c.1)^2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (R^2) := Real.sqrt_le_sqrt h2
        _ = R := Real.sqrt_sq hR
    have hx2 : |(z.2:ℝ) - c.2| ≤ R := by
      have h2 : ((z.2:ℝ) - c.2)^2 ≤ R^2 := by
        nlinarith [sq_nonneg ((z.1:ℝ) - c.1), hz]
      calc |(z.2:ℝ) - c.2| = Real.sqrt (((z.2:ℝ) - c.2)^2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (R^2) := Real.sqrt_le_sqrt h2
        _ = R := Real.sqrt_sq hR
    rw [hF, Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc, ha1, hb1]
      exact ⟨Int.ceil_le.mpr (by linarith [(abs_le.mp hx1).1]),
             Int.le_floor.mpr (by linarith [(abs_le.mp hx1).2])⟩
    · rw [Finset.mem_Icc, ha2, hb2]
      exact ⟨Int.ceil_le.mpr (by linarith [(abs_le.mp hx2).1]),
             Int.le_floor.mpr (by linarith [(abs_le.mp hx2).2])⟩
  have hAG : (G : Set (ℤ × ℤ)) =
      {z : ℤ × ℤ | (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2} := by
    ext z
    simp only [Finset.mem_coe, hG, Finset.mem_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨box_mem z h, h⟩⟩
  have hcard : (({z : ℤ × ℤ | (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2} : Set (ℤ × ℤ)).ncard : ℝ)
      = (G.card : ℝ) := by
    rw [← hAG, Set.ncard_coe_finset]
  have hLu : ∀ z ∈ G, Real.sqrt (∑ i : Fin 2, (GaussCircleAux.embZ z i - cfun i)^2) ≤ R := by
    intro z hz
    have hz' : (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2 := ((hGmem z).mp hz).2
    rw [hsumC z, ← Real.sqrt_sq hR]
    exact Real.sqrt_le_sqrt hz'
  have hupper : (G.card : ℝ) ≤ Real.pi * (R + s)^2 := by
    rw [hsdef]
    exact LatticeDiskAux.card_le_diskC cfun G R hR hLu
  have hlower : s ≤ R → Real.pi * (R - s)^2 ≤ (G.card : ℝ) := by
    intro hsR
    have hsR' : Real.sqrt 2 / 2 ≤ R := by rw [← hsdef]; exact hsR
    rw [hsdef]
    apply LatticeDiskAux.disk_le_cardC cfun G R hsR'
    intro z hz
    have hz' : (z.1 - c.1)^2 + (z.2 - c.2)^2 ≤ R^2 := by
      have hS0 : (0:ℝ) ≤ (∑ i : Fin 2, (GaussCircleAux.embZ z i - cfun i)^2) := by positivity
      have hR2 : (∑ i : Fin 2, (GaussCircleAux.embZ z i - cfun i)^2) ≤ R^2 := by
        have hsq := Real.sq_sqrt hS0
        have hsn := Real.sqrt_nonneg (∑ i : Fin 2, (GaussCircleAux.embZ z i - cfun i)^2)
        nlinarith [hsq, hsn, hz, hR]
      rwa [hsumC z] at hR2
    exact (hGmem z).mpr ⟨box_mem z hz', hz'⟩
  have hub : (G.card : ℝ) - Real.pi * R^2 ≤ Real.pi * (Real.sqrt 2 + 1) * (R + 1) := by
    have hexp : (R + s)^2 = R^2 + (Real.sqrt 2 * R + 1/2) := by
      rw [hsdef]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    have hupper' : (G.card : ℝ) ≤ Real.pi * R^2 + Real.pi * (Real.sqrt 2 * R + 1/2) := by
      have h := hupper
      rw [hexp, mul_add] at h
      exact h
    have h2 : Real.pi * (Real.sqrt 2 * R + 1/2) ≤ Real.pi * (Real.sqrt 2 + 1) * (R + 1) := by
      nlinarith [Real.sqrt_nonneg 2, hR, Real.pi_pos]
    linarith [hupper', h2]
  have hlb : Real.pi * R^2 - (G.card : ℝ) ≤ Real.pi * (Real.sqrt 2 + 1) * (R + 1) := by
    by_cases hsR : s ≤ R
    · have hlw : Real.pi * (R - s)^2 ≤ (G.card : ℝ) := hlower hsR
      have hexp : R^2 - (R - s)^2 = Real.sqrt 2 * R - 1/2 := by
        rw [hsdef]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      have hlw' : Real.pi * R^2 - (G.card : ℝ) ≤ Real.pi * (R^2 - (R - s)^2) := by
        rw [mul_sub]
        linarith [hlw]
      rw [hexp] at hlw'
      have h2 : Real.pi * (Real.sqrt 2 * R - 1/2) ≤ Real.pi * (Real.sqrt 2 + 1) * (R + 1) := by
        nlinarith [Real.sqrt_nonneg 2, hR, Real.pi_pos]
      linarith [hlw', h2]
    · have hRs : R < s := lt_of_not_ge hsR
      have hGnn : (0:ℝ) ≤ (G.card : ℝ) := by positivity
      have hs2 : s^2 = 1/2 := by
        rw [hsdef, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
      have hRs2 : R^2 ≤ (Real.sqrt 2 + 1) * (R + 1) := by
        nlinarith [hRs, hs2, Real.sqrt_nonneg 2, hR]
      nlinarith [hGnn, hRs2, Real.pi_pos]
  rw [hcard, abs_le]
  exact ⟨by linarith, hub⟩

end Commons.NumberTheory.Diophantine

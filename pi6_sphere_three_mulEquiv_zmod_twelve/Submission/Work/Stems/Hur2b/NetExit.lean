import Mathlib
import Submission.Work.Stems.Hur2b.NetGeo

/-!
# The radial exit point of the T-net: the one-dimensional ray computation

The net region `D = ⋃ k, netCell k` is the union of the belt `[1/4,3/4] × [3/8,1/2]` and the
column `[3/8,1/2] × [1/4,5/8]`, and the centre `c = (7/16,7/16)` lies in the interior of both;
hence `D` is star-shaped with respect to `c`, and for every direction `z ≠ 0` the ray
`t ↦ c + t z` meets `D` in a segment `[0, s*]`.

This file proves the *elementary* part of that computation, in offset coordinates (the vector
`z = y - c`): for `t ≥ 0`, `t • z` lies in the belt (resp. the column, resp. their union) exactly
when `t * MBelt z ≤ 1` (resp. `t * MCol z ≤ 1`, resp. `t * Mmin z ≤ 1`); consequently the exit
point `rayOff z = (1/Mmin z) • z` lies in the net region and every point beyond it on the ray
leaves it.  The statements relating this to the actual subsets `netCell k` of the square, and the
continuity of the exit point, are in `NetExitGeom.lean`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-! ## The one-dimensional ray parameter -/

theorem nu_nonneg {l u c z : ℝ} (h1 : l < c) (h2 : c < u) : 0 ≤ nu l u c z := by
  rw [nu]
  split_ifs with h
  · exact div_nonneg h (by linarith)
  · rw [show z / (l - c) = (-z) / (c - l) by
      rw [div_eq_div_iff (by linarith : l - c ≠ 0) (by linarith : c - l ≠ 0)]; ring]
    exact div_nonneg (by linarith) (by linarith)

theorem nu_eq_zero_iff {l u c z : ℝ} (h1 : l < c) (h2 : c < u) :
    nu l u c z = 0 ↔ z = 0 := by
  rw [nu]
  split_ifs with h
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h' | h')
      · exact h'
      · exact absurd h' (ne_of_gt (by linarith : (0:ℝ) < u - c))
    · intro hz; exact Or.inl hz
  · rw [div_eq_zero_iff]
    constructor
    · rintro (h' | h')
      · exact h'
      · exact absurd h' (ne_of_lt (by linarith : l - c < 0))
    · intro hz; exact Or.inl hz

theorem nu_pos_iff {l u c z : ℝ} (h1 : l < c) (h2 : c < u) : 0 < nu l u c z ↔ z ≠ 0 := by
  constructor
  · intro h hz
    rw [hz, nu, if_pos le_rfl, zero_div] at h
    exact lt_irrefl _ h
  · intro hz
    rcases lt_trichotomy z 0 with h | h | h
    · rw [nu, if_neg (not_le.mpr h), show z / (l - c) = (-z) / (c - l) by
        rw [div_eq_div_iff (by linarith : l - c ≠ 0) (by linarith : c - l ≠ 0)]; ring]
      exact div_pos (by linarith) (by linarith)
    · exact absurd h hz
    · rw [nu, if_pos h.le]
      exact div_pos h (by linarith)

theorem ray_mem_Icc {l u c z t : ℝ} (h1 : l < c) (h2 : c < u) (ht : 0 ≤ t) :
    c + t * z ∈ Set.Icc l u ↔ t * nu l u c z ≤ 1 := by
  have hl : l - c < 0 := by linarith
  have hu : 0 < u - c := by linarith
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have htz : t * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hz.le
    have hnu : nu l u c z = z / (l - c) := by rw [nu, if_neg (not_le.mpr hz)]
    rw [hnu, Set.mem_Icc, show t * (z / (l - c)) = (t * z) / (l - c) by ring,
      div_le_one_of_neg hl]
    constructor
    · rintro ⟨hlo, -⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  · subst hz
    rw [show nu l u c 0 = 0 by rw [nu, if_pos le_rfl, zero_div]]
    simp only [mul_zero, add_zero, Set.mem_Icc]
    constructor
    · intro _; norm_num
    · intro _; exact ⟨h1.le, h2.le⟩
  · have htz : 0 ≤ t * z := mul_nonneg ht hz.le
    have hnu : nu l u c z = z / (u - c) := by rw [nu, if_pos hz.le]
    rw [hnu, Set.mem_Icc, show t * (z / (u - c)) = (t * z) / (u - c) by ring, div_le_one hu]
    constructor
    · rintro ⟨-, hhi⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩


theorem nuB0_pos_iff {z : ℝ} : 0 < nuB0 z ↔ z ≠ 0 := nu_pos_iff (by norm_num) (by norm_num)
theorem nuB1_pos_iff {z : ℝ} : 0 < nuB1 z ↔ z ≠ 0 := nu_pos_iff (by norm_num) (by norm_num)
theorem nuC0_pos_iff {z : ℝ} : 0 < nuC0 z ↔ z ≠ 0 := nu_pos_iff (by norm_num) (by norm_num)
theorem nuC1_pos_iff {z : ℝ} : 0 < nuC1 z ↔ z ≠ 0 := nu_pos_iff (by norm_num) (by norm_num)

theorem nuB0_nonneg (z : ℝ) : 0 ≤ nuB0 z := nu_nonneg (by norm_num) (by norm_num)
theorem nuB1_nonneg (z : ℝ) : 0 ≤ nuB1 z := nu_nonneg (by norm_num) (by norm_num)
theorem nuC0_nonneg (z : ℝ) : 0 ≤ nuC0 z := nu_nonneg (by norm_num) (by norm_num)
theorem nuC1_nonneg (z : ℝ) : 0 ≤ nuC1 z := nu_nonneg (by norm_num) (by norm_num)

/-- The first belt coordinate test (offset form). -/
theorem ray_coord_belt0 {z t : ℝ} (ht : 0 ≤ t) :
    (-3/16 ≤ t * z ∧ t * z ≤ 5/16) ↔ t * nuB0 z ≤ 1 := by
  have h := ray_mem_Icc (l := 1/4) (u := 3/4) (c := 7/16) (z := z) (t := t)
    (by norm_num) (by norm_num) ht
  rw [nuB0]
  constructor
  · intro h2; exact h.mp ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro h2
    have := h.mpr h2
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The second belt coordinate test (offset form). -/
theorem ray_coord_belt1 {z t : ℝ} (ht : 0 ≤ t) :
    (-1/16 ≤ t * z ∧ t * z ≤ 1/16) ↔ t * nuB1 z ≤ 1 := by
  have h := ray_mem_Icc (l := 3/8) (u := 1/2) (c := 7/16) (z := z) (t := t)
    (by norm_num) (by norm_num) ht
  rw [nuB1]
  constructor
  · intro h2; exact h.mp ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro h2
    have := h.mpr h2
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The first column coordinate test (offset form). -/
theorem ray_coord_col0 {z t : ℝ} (ht : 0 ≤ t) :
    (-1/16 ≤ t * z ∧ t * z ≤ 1/16) ↔ t * nuC0 z ≤ 1 := by
  have h := ray_mem_Icc (l := 3/8) (u := 1/2) (c := 7/16) (z := z) (t := t)
    (by norm_num) (by norm_num) ht
  rw [nuC0]
  constructor
  · intro h2; exact h.mp ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro h2
    have := h.mpr h2
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The second column coordinate test (offset form). -/
theorem ray_coord_col1 {z t : ℝ} (ht : 0 ≤ t) :
    (-3/16 ≤ t * z ∧ t * z ≤ 3/16) ↔ t * nuC1 z ≤ 1 := by
  have h := ray_mem_Icc (l := 1/4) (u := 5/8) (c := 7/16) (z := z) (t := t)
    (by norm_num) (by norm_num) ht
  rw [nuC1]
  constructor
  · intro h2; exact h.mp ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · intro h2
    have := h.mpr h2
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **The belt test**: for `t ≥ 0` the offset `t • z` lies in the belt exactly when
`t * MBelt z ≤ 1`. -/
theorem ray_mem_beltOff {z : Fin 2 → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    (fun i => t * z i) ∈ beltOff ↔ t * MBelt z ≤ 1 := by
  have h0 := ray_coord_belt0 (z := z 0) ht
  have h1 := ray_coord_belt1 (z := z 1) ht
  have hmul : t * max (nuB0 (z 0)) (nuB1 (z 1)) = max (t * nuB0 (z 0)) (t * nuB1 (z 1)) :=
    mul_max_of_nonneg _ _ ht
  simp only [beltOff, Set.mem_ofPred_eq, MBelt, hmul, max_le_iff]
  exact ⟨fun h => ⟨h0.mp ⟨h.1, h.2.1⟩, h1.mp ⟨h.2.2.1, h.2.2.2⟩⟩,
         fun h => ⟨(h0.mpr h.1).1, (h0.mpr h.1).2, (h1.mpr h.2).1, (h1.mpr h.2).2⟩⟩

/-- **The column test**: for `t ≥ 0` the offset `t • z` lies in the column exactly when
`t * MCol z ≤ 1`. -/
theorem ray_mem_colOff {z : Fin 2 → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    (fun i => t * z i) ∈ colOff ↔ t * MCol z ≤ 1 := by
  have h0 := ray_coord_col0 (z := z 0) ht
  have h1 := ray_coord_col1 (z := z 1) ht
  have hmul : t * max (nuC0 (z 0)) (nuC1 (z 1)) = max (t * nuC0 (z 0)) (t * nuC1 (z 1)) :=
    mul_max_of_nonneg _ _ ht
  simp only [colOff, Set.mem_ofPred_eq, MCol, hmul, max_le_iff]
  exact ⟨fun h => ⟨h0.mp ⟨h.1, h.2.1⟩, h1.mp ⟨h.2.2.1, h.2.2.2⟩⟩,
         fun h => ⟨(h0.mpr h.1).1, (h0.mpr h.1).2, (h1.mpr h.2).1, (h1.mpr h.2).2⟩⟩

/-- **The net region test**: for `t ≥ 0` the offset `t • z` lies in the net region exactly when
`t * Mmin z ≤ 1`. -/
theorem ray_mem_netOff {z : Fin 2 → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    (fun i => t * z i) ∈ netOff ↔ t * Mmin z ≤ 1 := by
  have hmul : t * min (MBelt z) (MCol z) = min (t * MBelt z) (t * MCol z) :=
    mul_min_of_nonneg _ _ ht
  rw [netOff, Set.mem_union, ray_mem_beltOff ht, ray_mem_colOff ht, Mmin, hmul, min_le_iff]

theorem Mmin_pos {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 < Mmin z := by
  have h0 : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  rw [Mmin, lt_min_iff, MBelt, lt_max_iff, MCol, lt_max_iff]
  rcases h0 with h | h
  · exact ⟨Or.inl (nuB0_pos_iff.mpr h), Or.inl (nuC0_pos_iff.mpr h)⟩
  · exact ⟨Or.inr (nuB1_pos_iff.mpr h), Or.inr (nuC1_pos_iff.mpr h)⟩

theorem exitScale_pos {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 < exitScale z :=
  div_pos one_pos (Mmin_pos hz)

/-- **The exit point is in the net region.** -/
theorem rayOff_mem_netOff {z : Fin 2 → ℝ} (hz : z ≠ 0) : rayOff z ∈ netOff := by
  have h1 : (0:ℝ) ≤ exitScale z := (exitScale_pos hz).le
  have h := (ray_mem_netOff (z := z) (t := exitScale z) h1).mpr ?_
  · have heq : (fun i => exitScale z * z i) = rayOff z := by funext i; rw [rayOff]
    rwa [heq] at h
  · rw [exitScale, one_div, inv_mul_cancel₀ (ne_of_gt (Mmin_pos hz))]

/-- **Beyond the exit point the ray has left the net region.** -/
theorem rayOff_exit {z : Fin 2 → ℝ} (hz : z ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    (fun i => rayOff z i + ε * z i) ∉ netOff := by
  intro hmem
  have hpos : 0 < exitScale z := exitScale_pos hz
  have ht : (0:ℝ) ≤ exitScale z + ε := by linarith
  have hmem' : (fun i => (exitScale z + ε) * z i) ∈ netOff := by
    convert hmem using 1
    funext i
    rw [rayOff]
    ring
  have hle := (ray_mem_netOff (z := z) (t := exitScale z + ε) ht).mp hmem'
  have hM := Mmin_pos hz
  have hprod : (exitScale z + ε) * Mmin z = 1 + ε / exitScale z := by
    rw [exitScale, one_div]
    field_simp
  rw [hprod] at hle
  have : ε / exitScale z ≤ 0 := by linarith
  exact absurd this (not_le.mpr (div_pos hε hpos))


end

end Work.Stems.Hur2b

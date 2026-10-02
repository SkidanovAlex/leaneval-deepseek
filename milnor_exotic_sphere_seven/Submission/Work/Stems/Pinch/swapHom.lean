import Mathlib
import Submission.Work.Stems.Cubical.CubeFace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flip-to-transposition homotopy of the cube (the geometric brick of `readingPerm`)

For `i ≠ j` the reversal of the coordinate `i` of `I^n` and the transposition of the coordinates
`i`, `j` are self-maps of the pair `(I^n, ∂I^n)`; the theorem `Work.Stems.swapHom` below exhibits an
explicit homotopy between them through maps preserving `∂I^n`.  (Both act on `∂I^n ≅ S^{n-1}` with
degree `-1`; the witness used is the rotation of the `(i,j)`-square by the angle `-(π/2)t`, radially
renormalised to the square at every time.)

This is the input that `Work.RatHurewicz.GluingPinch.cl_compMap_eq` consumes to compute the *sign*
of a coordinate permutation: with it, `cl (p ∘ swap) = cl (p ∘ flip) = (cl p)⁻¹` (the last step by
the proved `Work.RatHurewicz.revCube_class`), and the multiplicativity of `Equiv.Perm.sign`
(`Equiv.Perm.swap_induction_on`, `Equiv.Perm.sign_swap`) gives
`cl (p ∘ permMap σ) = (cl p) ^ (sign σ)` for every permutation `σ`
(`Work.RatHurewicz.GluingPinch.readingPerm`) — the `sign σ_c` factor of the arrangement computation.
-/

open scoped unitInterval Topology
open Filter
open Work.Stems.Cubical

namespace Work.Stems

noncomputable section

/-! ## The centred coordinates and the planar rotation -/

/-- The centred `k`-th coordinate of a cube point: `u k - 1/2 ∈ [-1/2, 1/2]`. -/
def cen {n : ℕ} (u : IC n) (k : Fin n) : ℝ := (u k : ℝ) - 1/2

theorem abs_cen_le {n : ℕ} (u : IC n) (k : Fin n) : |cen u k| ≤ 1/2 := by
  have h0 : (0:ℝ) ≤ (u k : ℝ) := (u k).2.1
  have h1 : (u k : ℝ) ≤ 1 := (u k).2.2
  rw [cen, abs_le]
  constructor <;> linarith

theorem continuous_cen {n : ℕ} (k : Fin n) : Continuous fun u : IC n => cen u k :=
  (continuous_subtype_val.comp (continuous_apply k)).sub continuous_const

/-- The planar rotation of angle `-(π/2)·t`, first coordinate. -/
def rotP (t X Y : ℝ) : ℝ := X * Real.cos (-(Real.pi/2) * t) - Y * Real.sin (-(Real.pi/2) * t)

/-- The planar rotation of angle `-(π/2)·t`, second coordinate. -/
def rotQ (t X Y : ℝ) : ℝ := X * Real.sin (-(Real.pi/2) * t) + Y * Real.cos (-(Real.pi/2) * t)

theorem rotP_zero (X Y : ℝ) : rotP 0 X Y = X := by simp [rotP, Real.cos_zero, Real.sin_zero]

theorem rotQ_zero (X Y : ℝ) : rotQ 0 X Y = Y := by simp [rotQ, Real.cos_zero, Real.sin_zero]

theorem rotP_one (X Y : ℝ) : rotP 1 X Y = Y := by
  rw [rotP, show (-(Real.pi/2)) * 1 = -(Real.pi/2) from by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem rotQ_one (X Y : ℝ) : rotQ 1 X Y = -X := by
  rw [rotQ, show (-(Real.pi/2)) * 1 = -(Real.pi/2) from by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem rot_identity (t X Y : ℝ) :
    X = Real.cos (-(Real.pi/2)*t) * rotP t X Y + Real.sin (-(Real.pi/2)*t) * rotQ t X Y := by
  rw [rotP, rotQ]
  linear_combination (-X) * Real.cos_sq_add_sin_sq (-(Real.pi/2)*t)

theorem rot_identity' (t X Y : ℝ) :
    Y = -(Real.sin (-(Real.pi/2)*t)) * rotP t X Y + Real.cos (-(Real.pi/2)*t) * rotQ t X Y := by
  rw [rotP, rotQ]
  linear_combination (-Y) * Real.cos_sq_add_sin_sq (-(Real.pi/2)*t)

/-- The rotation is invertible: it has no kernel. -/
theorem rot_eq_zero_iff (t X Y : ℝ) :
    rotP t X Y = 0 ∧ rotQ t X Y = 0 ↔ X = 0 ∧ Y = 0 := by
  constructor
  · intro h
    have hX := rot_identity t X Y
    have hY := rot_identity' t X Y
    rw [h.1, h.2] at hX hY
    exact ⟨by simpa using hX, by simpa using hY⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨by simp [rotP], by simp [rotQ]⟩

/-! ## The two coordinates of the homotopy -/

/-- The denominator of `swapFst`/`swapSnd`. -/
def swapDen (t p q : ℝ) : ℝ := max (|rotP t (-p) q|) (|rotQ t (-p) q|)

/-- The first coordinate of the homotopy, in centred coordinates: rotate `(-p, q)` by the angle
`-(π/2)t` and renormalise the radius `max(|p|,|q|)` to the square. -/
def swapFst (t p q : ℝ) : ℝ := max (|p|) (|q|) * rotP t (-p) q / swapDen t p q

/-- The second coordinate of the homotopy. -/
def swapSnd (t p q : ℝ) : ℝ := max (|p|) (|q|) * rotQ t (-p) q / swapDen t p q

theorem abs_swapFst_le (t p q : ℝ) : |swapFst t p q| ≤ max (|p|) (|q|) := by
  have hm : 0 ≤ max (|p|) (|q|) := le_trans (abs_nonneg p) (le_max_left _ _)
  have hd : 0 ≤ swapDen t p q := le_trans (abs_nonneg _) (le_max_left _ _)
  have hP : |rotP t (-p) q| ≤ swapDen t p q := le_max_left _ _
  have hd' : |swapDen t p q| = swapDen t p q := abs_of_nonneg hd
  rw [swapFst, abs_div, abs_mul, abs_of_nonneg hm, hd']
  rcases eq_or_lt_of_le hd with h | h
  · rw [← h, div_zero]; exact hm
  · rw [div_le_iff₀ h]
    exact mul_le_mul_of_nonneg_left hP hm

theorem abs_swapSnd_le (t p q : ℝ) : |swapSnd t p q| ≤ max (|p|) (|q|) := by
  have hm : 0 ≤ max (|p|) (|q|) := le_trans (abs_nonneg p) (le_max_left _ _)
  have hd : 0 ≤ swapDen t p q := le_trans (abs_nonneg _) (le_max_left _ _)
  have hQ : |rotQ t (-p) q| ≤ swapDen t p q := le_max_right _ _
  have hd' : |swapDen t p q| = swapDen t p q := abs_of_nonneg hd
  rw [swapSnd, abs_div, abs_mul, abs_of_nonneg hm, hd']
  rcases eq_or_lt_of_le hd with h | h
  · rw [← h, div_zero]; exact hm
  · rw [div_le_iff₀ h]
    exact mul_le_mul_of_nonneg_left hQ hm

theorem swapFst_mem (t p q : ℝ) (hp : |p| ≤ 1/2) (hq : |q| ≤ 1/2) :
    0 ≤ 1/2 + swapFst t p q ∧ 1/2 + swapFst t p q ≤ 1 := by
  have h := abs_swapFst_le t p q
  have hm : max (|p|) (|q|) ≤ 1/2 := max_le hp hq
  have hb := abs_le.mp (le_trans h hm)
  constructor <;> linarith [hb.1, hb.2]

theorem swapSnd_mem (t p q : ℝ) (hp : |p| ≤ 1/2) (hq : |q| ≤ 1/2) :
    0 ≤ 1/2 + swapSnd t p q ∧ 1/2 + swapSnd t p q ≤ 1 := by
  have h := abs_swapSnd_le t p q
  have hm : max (|p|) (|q|) ≤ 1/2 := max_le hp hq
  have hb := abs_le.mp (le_trans h hm)
  constructor <;> linarith [hb.1, hb.2]

/-! ## Continuity (the degenerate point handled by a squeeze) -/

theorem continuousAt_swapFst_comp {α : Type} [TopologicalSpace α] {a : α} {t p q : α → ℝ}
    (ht : ContinuousAt t a) (hp : ContinuousAt p a) (hq : ContinuousAt q a) :
    ContinuousAt (fun z => swapFst (t z) (p z) (q z)) a := by
  have hcos : ContinuousAt (fun z => Real.cos (-(Real.pi/2) * t z)) a :=
    Real.continuous_cos.continuousAt.comp (ht.const_mul _)
  have hsin : ContinuousAt (fun z => Real.sin (-(Real.pi/2) * t z)) a :=
    Real.continuous_sin.continuousAt.comp (ht.const_mul _)
  have hn : ContinuousAt (fun z => -(p z)) a := hp.neg
  have hm : ContinuousAt (fun z => max (|p z|) (|q z|)) a :=
    Filter.Tendsto.max (ContinuousAt.abs hp) (ContinuousAt.abs hq)
  have hP : ContinuousAt (fun z => rotP (t z) (-(p z)) (q z)) a := by
    simp only [rotP]
    exact (hn.mul hcos).sub (hq.mul hsin)
  have hQ : ContinuousAt (fun z => rotQ (t z) (-(p z)) (q z)) a := by
    simp only [rotQ]
    exact (hn.mul hsin).add (hq.mul hcos)
  have hden : ContinuousAt (fun z => swapDen (t z) (p z) (q z)) a := by
    simp only [swapDen]
    exact Filter.Tendsto.max (ContinuousAt.abs hP) (ContinuousAt.abs hQ)
  by_cases hd : swapDen (t a) (p a) (q a) = 0
  · have hd' : max (|rotP (t a) (-(p a)) (q a)|) (|rotQ (t a) (-(p a)) (q a)|) = 0 := by
      simpa only [swapDen] using hd
    have hP0 : rotP (t a) (-(p a)) (q a) = 0 := by
      have h := le_max_left (|rotP (t a) (-(p a)) (q a)|) (|rotQ (t a) (-(p a)) (q a)|)
      rw [hd'] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hQ0 : rotQ (t a) (-(p a)) (q a) = 0 := by
      have h := le_max_right (|rotP (t a) (-(p a)) (q a)|) (|rotQ (t a) (-(p a)) (q a)|)
      rw [hd'] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    obtain ⟨hp0, hq0⟩ := (rot_eq_zero_iff (t a) (-(p a)) (q a)).mp ⟨hP0, hQ0⟩
    have hpa : p a = 0 := by simpa using hp0
    have hqa : q a = 0 := hq0
    have hnum : max (|p a|) (|q a|) = 0 := by rw [hpa, hqa]; simp
    have hval : swapFst (t a) (p a) (q a) = 0 := by
      rw [swapFst, swapDen, hnum]; simp
    have hbound : Tendsto (fun z => max (|p z|) (|q z|)) (𝓝 a) (𝓝 0) := by
      have h := hm.tendsto
      rwa [hnum] at h
    have htend : Tendsto (fun z => swapFst (t z) (p z) (q z)) (𝓝 a) (𝓝 0) :=
      squeeze_zero_norm (fun z => abs_swapFst_le (t z) (p z) (q z)) hbound
    rw [ContinuousAt, hval]
    exact htend
  · have h1 : ContinuousAt (fun z => max (|p z|) (|q z|) * rotP (t z) (-(p z)) (q z)) a :=
      hm.mul hP
    have h2 := h1.div hden hd
    show ContinuousAt (fun z => max (|p z|) (|q z|) * rotP (t z) (-(p z)) (q z) /
      max (|rotP (t z) (-(p z)) (q z)|) (|rotQ (t z) (-(p z)) (q z)|)) a
    exact h2

theorem continuousAt_swapSnd_comp {α : Type} [TopologicalSpace α] {a : α} {t p q : α → ℝ}
    (ht : ContinuousAt t a) (hp : ContinuousAt p a) (hq : ContinuousAt q a) :
    ContinuousAt (fun z => swapSnd (t z) (p z) (q z)) a := by
  have hcos : ContinuousAt (fun z => Real.cos (-(Real.pi/2) * t z)) a :=
    Real.continuous_cos.continuousAt.comp (ht.const_mul _)
  have hsin : ContinuousAt (fun z => Real.sin (-(Real.pi/2) * t z)) a :=
    Real.continuous_sin.continuousAt.comp (ht.const_mul _)
  have hn : ContinuousAt (fun z => -(p z)) a := hp.neg
  have hm : ContinuousAt (fun z => max (|p z|) (|q z|)) a :=
    Filter.Tendsto.max (ContinuousAt.abs hp) (ContinuousAt.abs hq)
  have hP : ContinuousAt (fun z => rotP (t z) (-(p z)) (q z)) a := by
    simp only [rotP]
    exact (hn.mul hcos).sub (hq.mul hsin)
  have hQ : ContinuousAt (fun z => rotQ (t z) (-(p z)) (q z)) a := by
    simp only [rotQ]
    exact (hn.mul hsin).add (hq.mul hcos)
  have hden : ContinuousAt (fun z => swapDen (t z) (p z) (q z)) a := by
    simp only [swapDen]
    exact Filter.Tendsto.max (ContinuousAt.abs hP) (ContinuousAt.abs hQ)
  by_cases hd : swapDen (t a) (p a) (q a) = 0
  · have hd' : max (|rotP (t a) (-(p a)) (q a)|) (|rotQ (t a) (-(p a)) (q a)|) = 0 := by
      simpa only [swapDen] using hd
    have hP0 : rotP (t a) (-(p a)) (q a) = 0 := by
      have h := le_max_left (|rotP (t a) (-(p a)) (q a)|) (|rotQ (t a) (-(p a)) (q a)|)
      rw [hd'] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hQ0 : rotQ (t a) (-(p a)) (q a) = 0 := by
      have h := le_max_right (|rotP (t a) (-(p a)) (q a)|) (|rotQ (t a) (-(p a)) (q a)|)
      rw [hd'] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    obtain ⟨hp0, hq0⟩ := (rot_eq_zero_iff (t a) (-(p a)) (q a)).mp ⟨hP0, hQ0⟩
    have hpa : p a = 0 := by simpa using hp0
    have hqa : q a = 0 := hq0
    have hnum : max (|p a|) (|q a|) = 0 := by rw [hpa, hqa]; simp
    have hval : swapSnd (t a) (p a) (q a) = 0 := by
      rw [swapSnd, swapDen, hnum]; simp
    have hbound : Tendsto (fun z => max (|p z|) (|q z|)) (𝓝 a) (𝓝 0) := by
      have h := hm.tendsto
      rwa [hnum] at h
    have htend : Tendsto (fun z => swapSnd (t z) (p z) (q z)) (𝓝 a) (𝓝 0) :=
      squeeze_zero_norm (fun z => abs_swapSnd_le (t z) (p z) (q z)) hbound
    rw [ContinuousAt, hval]
    exact htend
  · have h1 : ContinuousAt (fun z => max (|p z|) (|q z|) * rotQ (t z) (-(p z)) (q z)) a :=
      hm.mul hQ
    have h2 := h1.div hden hd
    show ContinuousAt (fun z => max (|p z|) (|q z|) * rotQ (t z) (-(p z)) (q z) /
      max (|rotP (t z) (-(p z)) (q z)|) (|rotQ (t z) (-(p z)) (q z)|)) a
    exact h2

/-! ## The endpoints -/

theorem swapDen_zero (p q : ℝ) : swapDen 0 p q = max (|p|) (|q|) := by
  have h1 : rotP 0 (-p) q = -p := rotP_zero _ _
  have h2 : rotQ 0 (-p) q = q := rotQ_zero _ _
  rw [swapDen, h1, h2, abs_neg]

theorem swapDen_one (p q : ℝ) : swapDen 1 p q = max (|p|) (|q|) := by
  have h1 : rotP 1 (-p) q = q := rotP_one _ _
  have h2 : rotQ 1 (-p) q = p := by rw [rotQ_one, neg_neg]
  rw [swapDen, h1, h2]
  exact max_comm (|q|) (|p|)

theorem swapFst_zero (p q : ℝ) : swapFst 0 p q = -p := by
  rw [swapFst, swapDen_zero, rotP_zero]
  rcases eq_or_ne (max (|p|) (|q|)) 0 with h | h
  · have hp : p = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_left _ _) (abs_nonneg p))
    have hq : q = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_right _ _) (abs_nonneg q))
    rw [hp, hq]; simp
  · exact mul_div_cancel_left₀ (-p) h

theorem swapSnd_zero (p q : ℝ) : swapSnd 0 p q = q := by
  rw [swapSnd, swapDen_zero, rotQ_zero]
  rcases eq_or_ne (max (|p|) (|q|)) 0 with h | h
  · have hp : p = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_left _ _) (abs_nonneg p))
    have hq : q = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_right _ _) (abs_nonneg q))
    rw [hp, hq]; simp
  · exact mul_div_cancel_left₀ q h

theorem swapFst_one (p q : ℝ) : swapFst 1 p q = q := by
  have h1 : rotP 1 (-p) q = q := rotP_one _ _
  rw [swapFst, swapDen_one, h1]
  rcases eq_or_ne (max (|p|) (|q|)) 0 with h | h
  · have hp : p = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_left _ _) (abs_nonneg p))
    have hq : q = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_right _ _) (abs_nonneg q))
    rw [hp, hq]; simp
  · exact mul_div_cancel_left₀ q h

theorem swapSnd_one (p q : ℝ) : swapSnd 1 p q = p := by
  rw [swapSnd, swapDen_one, rotQ_one, neg_neg]
  rcases eq_or_ne (max (|p|) (|q|)) 0 with h | h
  · have hp : p = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_left _ _) (abs_nonneg p))
    have hq : q = 0 :=
      abs_eq_zero.mp (le_antisymm (by rw [← h]; exact le_max_right _ _) (abs_nonneg q))
    rw [hp, hq]; simp
  · exact mul_div_cancel_left₀ p h

/-- On the boundary of the `(i,j)`-square one of the two coordinates lands on `±1/2`. -/
theorem swapFst_or_swapSnd (t p q : ℝ) (h : max (|p|) (|q|) = 1/2) :
    swapFst t p q = -(1/2) ∨ swapFst t p q = 1/2 ∨
      swapSnd t p q = -(1/2) ∨ swapSnd t p q = 1/2 := by
  rcases eq_or_ne (swapDen t p q) 0 with hz | hz
  · have hz' : max (|rotP t (-p) q|) (|rotQ t (-p) q|) = 0 := by simpa only [swapDen] using hz
    have hP0 : rotP t (-p) q = 0 := by
      have h1 := le_max_left (|rotP t (-p) q|) (|rotQ t (-p) q|)
      rw [hz'] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hQ0 : rotQ t (-p) q = 0 := by
      have h1 := le_max_right (|rotP t (-p) q|) (|rotQ t (-p) q|)
      rw [hz'] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    obtain ⟨hp0, hq0⟩ := (rot_eq_zero_iff t (-p) q).mp ⟨hP0, hQ0⟩
    have hp : p = 0 := by simpa using hp0
    rw [hp, hq0, abs_zero, max_self] at h
    norm_num at h
  · have hm : 0 ≤ max (|p|) (|q|) := le_trans (abs_nonneg p) (le_max_left _ _)
    have hd : 0 ≤ swapDen t p q := le_trans (abs_nonneg _) (le_max_left _ _)
    have hd' : |swapDen t p q| = swapDen t p q := abs_of_nonneg hd
    rcases le_total (|rotP t (-p) q|) (|rotQ t (-p) q|) with hle | hle
    · have hden : swapDen t p q = |rotQ t (-p) q| := max_eq_right hle
      have hzQ : |rotQ t (-p) q| ≠ 0 := by rw [← hden]; exact hz
      have habs : |swapSnd t p q| = max (|p|) (|q|) := by
        rw [swapSnd, abs_div, abs_mul, abs_of_nonneg hm, hd', hden,
          mul_div_assoc, div_self hzQ, mul_one]
      have habs' : |swapSnd t p q| = 1/2 := by rw [habs, h]
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp habs' with h2 | h2
      · exact Or.inr (Or.inr (Or.inr h2))
      · exact Or.inr (Or.inr (Or.inl h2))
    · have hden : swapDen t p q = |rotP t (-p) q| := max_eq_left hle
      have hzP : |rotP t (-p) q| ≠ 0 := by rw [← hden]; exact hz
      have habs : |swapFst t p q| = max (|p|) (|q|) := by
        rw [swapFst, abs_div, abs_mul, abs_of_nonneg hm, hd', hden,
          mul_div_assoc, div_self hzP, mul_one]
      have habs' : |swapFst t p q| = 1/2 := by rw [habs, h]
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp habs' with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inl h2

/-! ## The cube-level coordinates -/

/-- The `k`-th real coordinate of the homotopy at `z`. -/
def swapCoord {n : ℕ} (i j : Fin n) (z : IC n × unitInterval) (k : Fin n) : ℝ :=
  if k = i then 1/2 + swapFst (z.2 : ℝ) (cen z.1 i) (cen z.1 j)
  else if k = j then 1/2 + swapSnd (z.2 : ℝ) (cen z.1 i) (cen z.1 j)
  else (z.1 k : ℝ)

theorem swapCoord_mem {n : ℕ} (i j : Fin n) (z : IC n × unitInterval) (k : Fin n) :
    0 ≤ swapCoord i j z k ∧ swapCoord i j z k ≤ 1 := by
  by_cases hki : k = i
  · rw [swapCoord, if_pos hki]
    exact swapFst_mem _ _ _ (abs_cen_le _ _) (abs_cen_le _ _)
  · by_cases hkj : k = j
    · rw [swapCoord, if_neg hki, if_pos hkj]
      exact swapSnd_mem _ _ _ (abs_cen_le _ _) (abs_cen_le _ _)
    · rw [swapCoord, if_neg hki, if_neg hkj]
      exact ⟨(z.1 k).2.1, (z.1 k).2.2⟩

/-- The homotopy as a self-map of `I^n`. -/
def swapPt {n : ℕ} (i j : Fin n) (z : IC n × unitInterval) : IC n :=
  fun k => ⟨swapCoord i j z k, (swapCoord_mem i j z k).1, (swapCoord_mem i j z k).2⟩

theorem continuous_swapCoord {n : ℕ} (i j : Fin n) (k : Fin n) :
    Continuous fun z : IC n × unitInterval => swapCoord i j z k := by
  have ht : Continuous fun z : IC n × unitInterval => (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hp : Continuous fun z : IC n × unitInterval => cen z.1 i :=
    (continuous_cen i).comp continuous_fst
  have hq : Continuous fun z : IC n × unitInterval => cen z.1 j :=
    (continuous_cen j).comp continuous_fst
  by_cases hki : k = i
  · rw [show (fun z : IC n × unitInterval => swapCoord i j z k)
        = fun z => 1/2 + swapFst (z.2 : ℝ) (cen z.1 i) (cen z.1 j) from by
      funext z; rw [swapCoord, if_pos hki]]
    refine Continuous.add continuous_const ?_
    rw [continuous_iff_continuousAt]
    intro z
    exact continuousAt_swapFst_comp ht.continuousAt hp.continuousAt hq.continuousAt
  · by_cases hkj : k = j
    · rw [show (fun z : IC n × unitInterval => swapCoord i j z k)
          = fun z => 1/2 + swapSnd (z.2 : ℝ) (cen z.1 i) (cen z.1 j) from by
        funext z; rw [swapCoord, if_neg hki, if_pos hkj]]
      refine Continuous.add continuous_const ?_
      rw [continuous_iff_continuousAt]
      intro z
      exact continuousAt_swapSnd_comp ht.continuousAt hp.continuousAt hq.continuousAt
    · rw [show (fun z : IC n × unitInterval => swapCoord i j z k)
          = fun z => (z.1 k : ℝ) from by
        funext z; rw [swapCoord, if_neg hki, if_neg hkj]]
      exact continuous_subtype_val.comp (continuous_apply k |>.comp continuous_fst)

theorem continuous_swapPt {n : ℕ} (i j : Fin n) : Continuous (swapPt i j) := by
  apply continuous_pi
  intro k
  exact Continuous.subtype_mk (continuous_swapCoord i j k)
    (fun z => ⟨(swapCoord_mem i j z k).1, (swapCoord_mem i j z k).2⟩)

/-- A unit-interval equality transferred to `ℝ`. -/
theorem coe_eq_zero_or_one {a : unitInterval} (h : a = 0 ∨ a = 1) :
    (a : ℝ) = 0 ∨ (a : ℝ) = 1 := by
  rcases h with h | h
  · exact Or.inl (congrArg (fun x : unitInterval => (x : ℝ)) h)
  · exact Or.inr (congrArg (fun x : unitInterval => (x : ℝ)) h)

theorem swapCoord_boundary {n : ℕ} (i j : Fin n) (hij : i ≠ j) (z : IC n × unitInterval)
    (hz : z.1 ∈ Cube.boundary (Fin n)) :
    ∃ k : Fin n, swapCoord i j z k = 0 ∨ swapCoord i j z k = 1 := by
  have hcen : ∀ k : Fin n, |cen z.1 k| ≤ 1/2 := fun k => abs_cen_le _ _
  have key : ∀ (k : Fin n) (hk : z.1 k = 0 ∨ z.1 k = 1), |cen z.1 k| = 1/2 := by
    intro k hk
    rcases coe_eq_zero_or_one hk with hcoe | hcoe
    · rw [cen, hcoe]; norm_num
    · rw [cen, hcoe]; norm_num
  obtain ⟨k, hk⟩ := hz
  have hck : |cen z.1 k| = 1/2 := key k hk
  by_cases hki : k = i
  · have hm : max (|cen z.1 i|) (|cen z.1 j|) = 1/2 := by
      rw [← hki, hck]
      exact max_eq_left (abs_cen_le z.1 j)
    rcases swapFst_or_swapSnd (z.2 : ℝ) (cen z.1 i) (cen z.1 j) hm with h | h | h | h
    · exact ⟨i, Or.inl (by rw [swapCoord, if_pos rfl, h]; norm_num)⟩
    · exact ⟨i, Or.inr (by rw [swapCoord, if_pos rfl, h]; norm_num)⟩
    · exact ⟨j, Or.inl (by rw [swapCoord, if_neg hij.symm, if_pos rfl, h]; norm_num)⟩
    · exact ⟨j, Or.inr (by rw [swapCoord, if_neg hij.symm, if_pos rfl, h]; norm_num)⟩
  · by_cases hkj : k = j
    · have hm : max (|cen z.1 i|) (|cen z.1 j|) = 1/2 := by
        rw [← hkj, hck]
        exact max_eq_right (abs_cen_le z.1 i)
      rcases swapFst_or_swapSnd (z.2 : ℝ) (cen z.1 i) (cen z.1 j) hm with h | h | h | h
      · exact ⟨i, Or.inl (by rw [swapCoord, if_pos rfl, h]; norm_num)⟩
      · exact ⟨i, Or.inr (by rw [swapCoord, if_pos rfl, h]; norm_num)⟩
      · exact ⟨j, Or.inl (by rw [swapCoord, if_neg hij.symm, if_pos rfl, h]; norm_num)⟩
      · exact ⟨j, Or.inr (by rw [swapCoord, if_neg hij.symm, if_pos rfl, h]; norm_num)⟩
    · exact ⟨k, by rw [swapCoord, if_neg hki, if_neg hkj]; exact coe_eq_zero_or_one hk⟩

theorem swapPt_boundary {n : ℕ} (i j : Fin n) (hij : i ≠ j) (z : IC n × unitInterval)
    (hz : z.1 ∈ Cube.boundary (Fin n)) : swapPt i j z ∈ Cube.boundary (Fin n) := by
  obtain ⟨k, hk | hk⟩ := swapCoord_boundary i j hij z hz
  · exact ⟨k, Or.inl (Subtype.ext hk)⟩
  · exact ⟨k, Or.inr (Subtype.ext hk)⟩

/-! ## The homotopy -/

/-- **An explicit homotopy, through maps of the pair `(I^n, ∂I^n)`, between the reversal of the
coordinate `i` and the transposition of the coordinates `i`, `j`.** -/
theorem swapHom {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∃ H : C(IC n × unitInterval, IC n),
      (∀ u, H (u, 0) = fun k => if k = i then unitInterval.symm (u k) else u k) ∧
      (∀ u, H (u, 1) = fun k => u (Equiv.swap i j k)) ∧
      (∀ u ∈ Cube.boundary (Fin n), ∀ t, H (u, t) ∈ Cube.boundary (Fin n)) := by
  refine ⟨⟨swapPt i j, continuous_swapPt i j⟩, ?_, ?_, ?_⟩
  · intro u
    funext k
    by_cases hki : k = i
    · rw [if_pos hki]
      apply Subtype.ext
      show swapCoord i j (u, 0) k = ((unitInterval.symm (u k) : unitInterval) : ℝ)
      rw [swapCoord, if_pos hki]
      show 1/2 + swapFst (0 : ℝ) (cen u i) (cen u j) = ((unitInterval.symm (u k) : unitInterval) : ℝ)
      rw [hki]
      show 1/2 + swapFst (0 : ℝ) (cen u i) (cen u j) = 1 - (u i : ℝ)
      rw [swapFst_zero]
      show 1/2 + (-(cen u i)) = 1 - (u i : ℝ)
      rw [cen]
      ring
    · rw [if_neg hki]
      by_cases hkj : k = j
      · apply Subtype.ext
        show swapCoord i j (u, 0) k = (u k : ℝ)
        rw [swapCoord, if_neg hki, if_pos hkj]
        show 1/2 + swapSnd (0 : ℝ) (cen u i) (cen u j) = (u k : ℝ)
        rw [hkj]
        show 1/2 + swapSnd (0 : ℝ) (cen u i) (cen u j) = (u j : ℝ)
        rw [swapSnd_zero]
        show 1/2 + cen u j = (u j : ℝ)
        rw [cen]
        ring
      · apply Subtype.ext
        show swapCoord i j (u, 0) k = (u k : ℝ)
        rw [swapCoord, if_neg hki, if_neg hkj]
  · intro u
    funext k
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left]
      apply Subtype.ext
      show swapCoord i j (u, 1) i = (u j : ℝ)
      rw [swapCoord, if_pos rfl]
      show 1/2 + swapFst (1 : ℝ) (cen u i) (cen u j) = (u j : ℝ)
      rw [swapFst_one]
      show 1/2 + cen u j = (u j : ℝ)
      rw [cen]
      ring
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right]
        apply Subtype.ext
        show swapCoord i j (u, 1) j = (u i : ℝ)
        rw [swapCoord, if_neg hij.symm, if_pos rfl]
        show 1/2 + swapSnd (1 : ℝ) (cen u i) (cen u j) = (u i : ℝ)
        rw [swapSnd_one]
        show 1/2 + cen u i = (u i : ℝ)
        rw [cen]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        apply Subtype.ext
        show swapCoord i j (u, 1) k = (u k : ℝ)
        rw [swapCoord, if_neg hki, if_neg hkj]
  · intro u hu t
    exact swapPt_boundary i j hij (u, t) hu

end

end Work.Stems

import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.screwExists

namespace Work.Mostow

open scoped RealInnerProductSpace

/-!
# `Work.Mostow.screwAtZ`

Assembly of the Dirichlet "screw" (`Work.Mostow.screwExists`) with the block-rotation
displacement estimate, giving the element of `⟨ψ⟩ · Aang` of translation length `≤ δ/W`
whose rotation displaces `Wz` by at most `δ`.

The only geometric input is: if an isometry `c` of `E m` acts on each block
`span {e (i,0), e (i,1)}` of an orthonormal basis `e` as a rotation (with block angle whose
class mod `2π` is `b i`), then for every `v`

`‖c v - v‖² = ∑ i, (2 - 2 cos θ i) · ‖Pᵢ v‖²`,

where `θ i` is any real lift of `b i` and `Pᵢ v` is the `i`-th block projection of `v`; and
`2 - 2 cos θ i = chord (b i)²`, while `‖Pᵢ v‖ ≤ ρ i`.
-/

/-- Projection of `v` onto the `i`-th two-dimensional block of `e`. -/
noncomputable def screwBlkProj {m : ℕ}
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (i : Fin (m / 2)) (v : Submission.Mostow.E m) : Submission.Mostow.E m :=
  (inner ℝ (e (i, (0 : Fin 2))) v) • e (i, (0 : Fin 2)) +
    (inner ℝ (e (i, (1 : Fin 2))) v) • e (i, (1 : Fin 2))

lemma screw_two_sub_two_cos (y : ℝ) : 2 - 2 * Real.cos y = 4 * Real.sin (y / 2) ^ 2 := by
  have h1 : Real.cos y = 2 * Real.cos (y / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring] at this
    linarith
  have h2 := Real.sin_sq_add_cos_sq (y / 2)
  nlinarith [h1, h2]

lemma screw_sin_sq_abs_div (y : ℝ) : Real.sin (|y| / 2) ^ 2 = Real.sin (y / 2) ^ 2 := by
  rcases abs_choice y with h | h
  · rw [h]
  · rw [h, show -y / 2 = -(y / 2) by ring, Real.sin_neg]; ring

/-- For an angle `x` on the circle, `chord x² = 2 - 2 cos x` (with `cos` the well defined
`2π`-periodic cosine on `AddCircle (2π)`). -/
lemma screw_chord_sq_eq_cos (x : AddCircle (2 * Real.pi)) :
    Submission.Mostow.chord x ^ 2 = 2 - 2 * Real.Angle.cos x := by
  have hy : |Real.Angle.toReal x| ≤ |(2 * Real.pi)| / 2 := by
    rw [abs_of_pos (Real.two_pi_pos)]; linarith [Real.Angle.abs_toReal_le_pi x]
  have h2 : ‖(↑(Real.Angle.toReal x) : AddCircle (2 * Real.pi))‖ = |Real.Angle.toReal x| :=
    (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (ne_of_gt Real.two_pi_pos)).mpr hy
  rw [show (↑(Real.Angle.toReal x) : AddCircle (2 * Real.pi)) = x from Real.Angle.coe_toReal x] at h2
  have hcos : Real.Angle.cos x = Real.cos (Real.Angle.toReal x) := (Real.Angle.cos_toReal x).symm
  rw [Submission.Mostow.chord, h2, hcos, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
      screw_two_sub_two_cos, screw_sin_sq_abs_div]

lemma screw_norm_smul_add_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (f g : ℝ) (hxx : inner ℝ x x = 1) (hyy : inner ℝ y y = 1)
    (hxy : inner ℝ x y = 0) (hyx : inner ℝ y x = 0) :
    ‖f • x + g • y‖ ^ 2 = f ^ 2 + g ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hxx, hyy, hxy, hyx]
  ring

/-- **Block-rotation displacement.**  If `c` rotates each block of the orthonormal basis `e`
by the angle `θ i`, then `‖c v - v‖² = ∑ i (2 - 2 cos θ i) ‖Pᵢ v‖²`. -/
lemma screw_blkRotNormSq {m : ℕ}
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (c : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (θ : Fin (m / 2) → ℝ)
    (h0 : ∀ i, c (e (i, Fin.castSucc 0)) =
        Real.cos (θ i) • e (i, Fin.castSucc 0) + Real.sin (θ i) • e (i, 1))
    (h1 : ∀ i, c (e (i, 1)) =
        - Real.sin (θ i) • e (i, Fin.castSucc 0) + Real.cos (θ i) • e (i, 1)) :
    ∀ v : Submission.Mostow.E m,
      ‖c v - v‖ ^ 2 = ∑ i : Fin (m / 2),
        (2 - 2 * Real.cos (θ i)) * ‖screwBlkProj e i v‖ ^ 2 := by
  intro v
  have horth : ∀ k l : Fin (m / 2) × Fin 2, inner ℝ (e k) (e l) = if k = l then 1 else 0 :=
    (orthonormal_iff_ite.mp e.orthonormal)
  have h0' : ∀ i, c (e (i, (0 : Fin 2))) =
      Real.cos (θ i) • e (i, (0 : Fin 2)) + Real.sin (θ i) • e (i, 1) :=
    fun i => by simpa only [Fin.castSucc_zero] using h0 i
  have h1' : ∀ i, c (e (i, 1)) =
      - Real.sin (θ i) • e (i, (0 : Fin 2)) + Real.cos (θ i) • e (i, 1) :=
    fun i => by simpa only [Fin.castSucc_zero] using h1 i
  have hI00 : ∀ i i', inner ℝ (e (i, (0 : Fin 2))) (c (e (i', (0 : Fin 2)))) =
      if i = i' then Real.cos (θ i') else 0 := by
    intro i i'
    rw [h0' i', inner_add_right, real_inner_smul_right, real_inner_smul_right,
        horth (i, (0 : Fin 2)) (i', (0 : Fin 2)), horth (i, (0 : Fin 2)) (i', (1 : Fin 2))]
    by_cases h : i = i'
    · subst h; simp
    · simp [h, Prod.mk.injEq]
  have hI01 : ∀ i i', inner ℝ (e (i, (0 : Fin 2))) (c (e (i', 1))) =
      if i = i' then -Real.sin (θ i') else 0 := by
    intro i i'
    rw [h1' i', inner_add_right, real_inner_smul_right, real_inner_smul_right,
        horth (i, (0 : Fin 2)) (i', (0 : Fin 2)), horth (i, (0 : Fin 2)) (i', (1 : Fin 2))]
    by_cases h : i = i'
    · subst h; simp
    · simp [h, Prod.mk.injEq]
  have hI10 : ∀ i i', inner ℝ (e (i, (1 : Fin 2))) (c (e (i', (0 : Fin 2)))) =
      if i = i' then Real.sin (θ i') else 0 := by
    intro i i'
    rw [h0' i', inner_add_right, real_inner_smul_right, real_inner_smul_right,
        horth (i, (1 : Fin 2)) (i', (0 : Fin 2)), horth (i, (1 : Fin 2)) (i', (1 : Fin 2))]
    by_cases h : i = i'
    · subst h; simp
    · simp [h, Prod.mk.injEq]
  have hI11 : ∀ i i', inner ℝ (e (i, (1 : Fin 2))) (c (e (i', 1))) =
      if i = i' then Real.cos (θ i') else 0 := by
    intro i i'
    rw [h1' i', inner_add_right, real_inner_smul_right, real_inner_smul_right,
        horth (i, (1 : Fin 2)) (i', (0 : Fin 2)), horth (i, (1 : Fin 2)) (i', (1 : Fin 2))]
    by_cases h : i = i'
    · subst h; simp
    · simp [h, Prod.mk.injEq]
  have hv : v = ∑ l, (inner ℝ (e l) v) • e l := by
    simpa [OrthonormalBasis.repr_apply_apply] using (e.sum_repr v).symm
  have hcv : c v = ∑ l, (inner ℝ (e l) v) • c (e l) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [map_smul])
  have H1 : ∀ k : Fin (m / 2) × Fin 2,
      inner ℝ (e k) (c v) =
        ∑ l : Fin (m / 2) × Fin 2, (inner ℝ (e l) v) * inner ℝ (e k) (c (e l)) := by
    intro k
    rw [hcv, inner_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [real_inner_smul_right])
  have key : ∀ (i : Fin (m / 2)) (k' : Fin 2),
      inner ℝ (e (i, k')) (c v)
      = ∑ i' : Fin (m / 2),
          ((inner ℝ (e (i', (0 : Fin 2))) v) * inner ℝ (e (i, k')) (c (e (i', (0 : Fin 2))))
            + (inner ℝ (e (i', (1 : Fin 2))) v) * inner ℝ (e (i, k')) (c (e (i', (1 : Fin 2))))) := by
    intro i k'
    rw [H1 (i, k'), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [Fin.sum_univ_two]
  have hcin0 : ∀ i, inner ℝ (e (i, (0 : Fin 2))) (c v) =
      (inner ℝ (e (i, (0 : Fin 2))) v) * Real.cos (θ i)
        - (inner ℝ (e (i, (1 : Fin 2))) v) * Real.sin (θ i) := by
    intro i
    rw [key i (0 : Fin 2)]
    have hstep : ∀ i' : Fin (m / 2),
        ((inner ℝ (e (i', (0 : Fin 2))) v) * inner ℝ (e (i, (0 : Fin 2))) (c (e (i', (0 : Fin 2))))
          + (inner ℝ (e (i', (1 : Fin 2))) v) * inner ℝ (e (i, (0 : Fin 2))) (c (e (i', (1 : Fin 2)))))
        = (inner ℝ (e (i', (0 : Fin 2))) v) * (if i = i' then Real.cos (θ i') else 0)
          + (inner ℝ (e (i', (1 : Fin 2))) v) * (if i = i' then -Real.sin (θ i') else 0) := by
      intro i'
      rw [hI00 i i', hI01 i i']
    rw [Finset.sum_congr rfl (fun i' _ => hstep i'), Finset.sum_add_distrib,
        Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp only [ite_true]; ring
    · intro b _ hb; rw [if_neg (fun h : i = b => hb h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
    · intro b _ hb; rw [if_neg (fun h : i = b => hb h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hcin1 : ∀ i, inner ℝ (e (i, (1 : Fin 2))) (c v) =
      (inner ℝ (e (i, (0 : Fin 2))) v) * Real.sin (θ i)
        + (inner ℝ (e (i, (1 : Fin 2))) v) * Real.cos (θ i) := by
    intro i
    rw [key i (1 : Fin 2)]
    have hstep : ∀ i' : Fin (m / 2),
        ((inner ℝ (e (i', (0 : Fin 2))) v) * inner ℝ (e (i, (1 : Fin 2))) (c (e (i', (0 : Fin 2))))
          + (inner ℝ (e (i', (1 : Fin 2))) v) * inner ℝ (e (i, (1 : Fin 2))) (c (e (i', (1 : Fin 2)))))
        = (inner ℝ (e (i', (0 : Fin 2))) v) * (if i = i' then Real.sin (θ i') else 0)
          + (inner ℝ (e (i', (1 : Fin 2))) v) * (if i = i' then Real.cos (θ i') else 0) := by
      intro i'
      rw [hI10 i i', hI11 i i']
    rw [Finset.sum_congr rfl (fun i' _ => hstep i'), Finset.sum_add_distrib,
        Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (fun h : i = b => hb h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
    · intro b _ hb; rw [if_neg (fun h : i = b => hb h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hpar : ‖c v - v‖ ^ 2 = ∑ k : Fin (m / 2) × Fin 2, (inner ℝ (e k) (c v - v)) ^ 2 := by
    have h := e.repr.norm_map (c v - v)
    rw [← h, EuclideanSpace.norm_sq_eq]
    simp only [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs]
  rw [hpar, Fintype.sum_prod_type]
  have hblk : ∀ i : Fin (m / 2),
      (∑ j : Fin 2, (inner ℝ (e (i, j)) (c v - v)) ^ 2)
        = (2 - 2 * Real.cos (θ i))
          * ((inner ℝ (e (i, (0 : Fin 2))) v) ^ 2 + (inner ℝ (e (i, (1 : Fin 2))) v) ^ 2) := by
    intro i
    have hd0 : inner ℝ (e (i, (0 : Fin 2))) (c v - v)
        = (inner ℝ (e (i, (0 : Fin 2))) v) * Real.cos (θ i)
          - (inner ℝ (e (i, (1 : Fin 2))) v) * Real.sin (θ i)
          - (inner ℝ (e (i, (0 : Fin 2))) v) := by
      rw [inner_sub_right, hcin0 i]
    have hd1 : inner ℝ (e (i, (1 : Fin 2))) (c v - v)
        = (inner ℝ (e (i, (0 : Fin 2))) v) * Real.sin (θ i)
          + (inner ℝ (e (i, (1 : Fin 2))) v) * Real.cos (θ i)
          - (inner ℝ (e (i, (1 : Fin 2))) v) := by
      rw [inner_sub_right, hcin1 i]
    rw [Fin.sum_univ_two, hd0, hd1]
    nlinarith [Real.sin_sq_add_cos_sq (θ i)]
  rw [Finset.sum_congr rfl (fun i _ => hblk i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [screwBlkProj, screw_norm_smul_add_smul_sq _ _ _ _
      (by rw [horth]; simp) (by rw [horth]; simp)
      (by rw [horth]; simp) (by rw [horth]; simp)]

/-- **Domination transfer.**  The element `b` of the rotation group displaces `Wz` by at most
`δ` whenever the `ρ`-weighted sum of squared chords of `b` is at most `δ²` and each block of
`Wz` is dominated by `ρ`. -/
lemma screw_rotDisp_le (m : ℕ)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (rot : (Fin (m / 2) → AddCircle (2 * Real.pi)) →
      (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (hrot : ∀ (b : Fin (m / 2) → AddCircle (2 * Real.pi)) (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = b i ∧
        rot b (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
          (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
            (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (Wz : Submission.Mostow.E m) (ρ : Fin (m / 2) → ℝ) (hρ : ∀ i, 0 < ρ i)
    (δ : ℝ) (hδ : 0 < δ) (b : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hdom : ∀ i : Fin (m / 2),
      ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖ ≤ ρ i)
    (hdisp : ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (b i)) ^ 2 ≤ δ ^ 2) :
    ‖rot b Wz - Wz‖ ≤ δ := by
  have ht0 : ∀ i : Fin (m / 2), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = b i ∧
        rot b (e (i, Fin.castSucc 0)) =
          Real.cos t • e (i, Fin.castSucc 0) + Real.sin t • e (i, 1) := by
    intro i
    obtain ⟨t, ht, hform⟩ := hrot b i 1 0
    exact ⟨t, ht, by simpa using hform⟩
  choose θ hθ using ht0
  have h1θ : ∀ i : Fin (m / 2), rot b (e (i, 1)) =
      - Real.sin (θ i) • e (i, Fin.castSucc 0) + Real.cos (θ i) • e (i, 1) := by
    intro i
    obtain ⟨t', ht', hform'⟩ := hrot b i 0 1
    have key : (t' : Real.Angle) = (θ i : Real.Angle) := ht'.trans (hθ i).1.symm
    have hcos : Real.cos t' = Real.cos (θ i) := by
      rw [← Real.Angle.cos_coe t', key, Real.Angle.cos_coe]
    have hsin : Real.sin t' = Real.sin (θ i) := by
      rw [← Real.Angle.sin_coe t', key, Real.Angle.sin_coe]
    simpa [hcos, hsin] using hform'
  have hdom' : ∀ i : Fin (m / 2), ‖screwBlkProj e i Wz‖ ≤ ρ i := by
    intro i
    have h := hdom i
    simpa only [screwBlkProj, Fin.castSucc_zero] using h
  have hchord : ∀ i : Fin (m / 2),
      2 - 2 * Real.cos (θ i) = (Submission.Mostow.chord (b i)) ^ 2 := by
    intro i
    have hc := screw_chord_sq_eq_cos (b i)
    have hcx : Real.Angle.cos (b i) = Real.cos (θ i) := by
      rw [← Real.Angle.cos_coe (θ i)]
      exact (congrArg Real.Angle.cos (hθ i).1).symm
    rw [hcx] at hc
    exact hc.symm
  have hfs : ∀ i : Fin (m / 2), 0 ≤ 2 - 2 * Real.cos (θ i) :=
    fun i => by linarith [Real.cos_le_one (θ i)]
  have hsq : ∀ i : Fin (m / 2), ‖screwBlkProj e i Wz‖ ^ 2 ≤ (ρ i) ^ 2 :=
    fun i => pow_le_pow_left₀ (norm_nonneg _) (hdom' i) 2
  have hmain := screw_blkRotNormSq e (rot b) θ (fun i => (hθ i).2) h1θ Wz
  have hle : ‖rot b Wz - Wz‖ ^ 2 ≤ δ ^ 2 := by
    calc ‖rot b Wz - Wz‖ ^ 2
        = ∑ i : Fin (m / 2),
            (2 - 2 * Real.cos (θ i)) * ‖screwBlkProj e i Wz‖ ^ 2 := hmain
      _ ≤ ∑ i : Fin (m / 2), (2 - 2 * Real.cos (θ i)) * (ρ i) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact mul_le_mul_of_nonneg_left (hsq i) (hfs i)
      _ = ∑ i : Fin (m / 2), (ρ i) ^ 2 * (Submission.Mostow.chord (b i)) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hchord i]; ring
      _ ≤ δ ^ 2 := hdisp
  nlinarith [norm_nonneg (rot b Wz - Wz), hδ, hle]

theorem screwAtZ (m : ℕ) (hm : Even m) (hm0 : 0 < m)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (rot : (Fin (m / 2) → AddCircle (2 * Real.pi)) →
      (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (hrot : ∀ (b : Fin (m / 2) → AddCircle (2 * Real.pi)) (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
      (t : AddCircle (2 * Real.pi)) = b i ∧
        rot b (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
          (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
            (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (Aang : AddSubgroup (Fin (m / 2) → AddCircle (2 * Real.pi))) [Finite Aang]
    (T δ W : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hW : 0 < W)
    (ρ : Fin (m / 2) → ℝ) (hρ : ∀ i, 0 < ρ i)
    (ψ : Fin (m / 2) → AddCircle (2 * Real.pi))
    (Wz : Submission.Mostow.E m) (J : ℕ)
    (hJT : (J : ℝ) * T ≤ δ / W)
    (hsm : ∀ i, δ ≤ 2 * Real.pi * (2 * Real.sqrt ((m : ℝ) / 2) * ρ i))
    (hmin : ∀ a ∈ Aang, a ≠ 0 →
      δ ^ 2 ≤ ∑ i, (ρ i) ^ 2 * (Submission.Mostow.chord (a i)) ^ 2)
    (hcount : ∏ i, ⌈2 * Real.pi / (δ / (2 * Real.sqrt ((m : ℝ) / 2) * ρ i))⌉₊ <
      (J + 1) * Nat.card Aang)
    (hdom : ∀ i : Fin (m / 2),
      ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖ ≤ ρ i) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ ∃ b ∈ Aang, (j : ℝ) * T ≤ δ / W ∧
      ‖rot (j • ψ + b) Wz - Wz‖ ≤ δ := by
  have hcast : (m : ℝ) / 2 = ((m / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_div (even_iff_two_dvd.mp hm) (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)]
    norm_num
  have hr : 0 < m / 2 := by
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hm
    omega
  have hsm' : ∀ i, δ ≤ 2 * Real.pi * (2 * Real.sqrt (((m / 2 : ℕ) : ℝ)) * ρ i) := by
    intro i; simpa only [hcast] using hsm i
  have hcount' : ∏ i, ⌈2 * Real.pi / (δ / (2 * Real.sqrt (((m / 2 : ℕ) : ℝ)) * ρ i))⌉₊ <
      (J + 1) * Nat.card Aang := by
    simpa only [hcast] using hcount
  obtain ⟨j, hj1, hjJ, a, haA, hTj, hdisp⟩ :=
    screwExists (m / 2) hr T δ W hT hδ hW ψ Aang ρ hρ J hJT hsm' hmin hcount'
  refine ⟨j, hj1, hjJ, a, haA, hTj, ?_⟩
  exact screw_rotDisp_le m e rot hrot Wz ρ hρ δ hδ (j • ψ + a) hdom hdisp

end Work.Mostow

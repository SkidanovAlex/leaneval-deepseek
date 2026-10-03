import Mathlib

/-!
# `Work.FIArea7.P231.card_rows_le`

A lattice-point count for a thin strip cut out of a disk.  If every point `p = (x,y)` of a
finite set `T ⊆ ℤ × ℤ` lies in the disk `x² + y² ≤ X` and in the strip `|α x - β y| < K`
(with `β ≠ 0`), then

  `#T ≤ (2√X + 1) · (2K/|β| + 1)`.

The proof groups `T` by its first coordinate: there are at most `2√X + 1` admissible
`x`-values, and for a fixed `x` the admissible `y`-values all lie in an interval of real
length `2K/|β|`, whence at most `2K/|β| + 1` of them (one-dimensional interval counting).
-/

namespace Work.FIArea7.P231

/-- **Integers in a real interval.**  A finite set of integers all of whose elements lie in
`[a,b]` has at most `b - a + 1` elements.  (Because the elements are distinct integers with
spacing at least `1`.) -/
lemma card_le_of_subset_Icc_aux {A : Finset ℤ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ A, a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b) :
    (A.card : ℝ) ≤ b - a + 1 := by
  have hsub : A ⊆ Finset.Icc ⌈a⌉ ⌊b⌋ := by
    intro x hx
    obtain ⟨h1, h2⟩ := h x hx
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  have hcard : (A.card : ℝ) ≤ ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hnn : (0 : ℤ) ≤ ⌊b⌋ + 1 - ⌈a⌉ := by
    have hca : ⌈a⌉ ≤ ⌊b⌋ + 1 := by
      apply Int.ceil_le.mpr
      push_cast
      linarith [Int.lt_floor_add_one b, hab]
    omega
  have hbound : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b - a + 1 := by
    rw [Int.card_Icc]
    have hnat : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) = ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
      have hh := Int.toNat_of_nonneg hnn
      exact_mod_cast hh
    rw [hnat]
    push_cast
    linarith [Int.floor_le b, Int.le_ceil a]
  linarith

/-- **A row of the strip.**  For a fixed first coordinate `x`, the points of `T` in the strip
`|α x - β y| < K` have their `y`-coordinate in an interval of real length `2K/|β|`, hence are at
most `2K/|β| + 1` in number. -/
lemma fiber_card_le_aux (α β : ℤ) (hβ : β ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (T : Finset (ℤ × ℤ)) (x : ℤ)
    (hstrip : ∀ p ∈ T, |((α * p.1 - β * p.2 : ℤ) : ℝ)| < K) :
    ((T.filter (fun p => p.1 = x)).card : ℝ) ≤ 2 * K / |(β : ℝ)| + 1 := by
  have hβR : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
  have hβabs : 0 < |(β : ℝ)| := abs_pos.mpr hβR
  set c : ℝ := (α : ℝ) * (x : ℝ) / (β : ℝ) with hc
  set d : ℝ := K / |(β : ℝ)| with hd
  have hdnn : 0 ≤ d := by rw [hd]; exact div_nonneg hK (le_of_lt hβabs)
  have hsub : T.filter (fun p => p.1 = x) ⊆
      ({x} : Finset ℤ) ×ˢ (Finset.Icc ⌈c - d⌉ ⌊c + d⌋) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpT, hp1⟩ := hp
    rw [Finset.mem_product, Finset.mem_singleton]
    refine ⟨hp1, ?_⟩
    rw [Finset.mem_Icc]
    have hs := hstrip p hpT
    rw [hp1] at hs
    have hpush : ((α * x - β * p.2 : ℤ) : ℝ) = (α : ℝ) * (x : ℝ) - (β : ℝ) * (p.2 : ℝ) := by
      push_cast; ring
    rw [hpush] at hs
    have hkey : |(p.2 : ℝ) - c| < d := by
      rw [hc, hd]
      have hstep : (p.2 : ℝ) - (α : ℝ) * (x : ℝ) / (β : ℝ)
          = - (((α : ℝ) * (x : ℝ) - (β : ℝ) * (p.2 : ℝ)) / (β : ℝ)) := by
        field_simp
        ring
      rw [hstep, abs_neg, abs_div]
      exact div_lt_div_of_pos_right hs hβabs
    rw [abs_lt] at hkey
    exact ⟨Int.ceil_le.mpr (by linarith [hkey.1]), Int.le_floor.mpr (by linarith [hkey.2])⟩
  have hcard : ((T.filter (fun p => p.1 = x)).card : ℝ)
      ≤ ((Finset.Icc ⌈c - d⌉ ⌊c + d⌋).card : ℝ) := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_singleton, one_mul] at hh
    exact_mod_cast hh
  have hbound : ((Finset.Icc ⌈c - d⌉ ⌊c + d⌋).card : ℝ) ≤ 2 * K / |(β : ℝ)| + 1 := by
    have h1 := card_le_of_subset_Icc_aux (A := Finset.Icc ⌈c - d⌉ ⌊c + d⌋) (a := c - d) (b := c + d)
      (by linarith) (fun y hy => by
        rw [Finset.mem_Icc] at hy
        obtain ⟨hy1, hy2⟩ := hy
        refine ⟨?_, ?_⟩
        · have h1' := Int.le_ceil (c - d)
          have h2' : ((⌈c - d⌉ : ℤ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
          linarith
        · have h1' := Int.floor_le (c + d)
          have h2' : (y : ℝ) ≤ ((⌊c + d⌋ : ℤ) : ℝ) := by exact_mod_cast hy2
          linarith)
    have h2 : (c + d) - (c - d) + 1 = 2 * K / |(β : ℝ)| + 1 := by
      rw [hd]; ring
    linarith [h1, h2]
  linarith [hcard, hbound]

/-- **Projection of the disk.**  The first coordinates of the points of a finite set `T` lying in
the disk `x² + y² ≤ X` form a set of at most `2√X + 1` integers. -/
lemma image_fst_card_le_aux (X : ℝ) (hX : 0 ≤ X) (T : Finset (ℤ × ℤ))
    (hnorm : ∀ p ∈ T, ((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2 ≤ X) :
    ((T.image Prod.fst).card : ℝ) ≤ 2 * Real.sqrt X + 1 := by
  have hmain : ((T.image Prod.fst).card : ℝ) ≤ Real.sqrt X - (-Real.sqrt X) + 1 := by
    apply card_le_of_subset_Icc_aux
    · linarith [Real.sqrt_nonneg X]
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hpT, rfl⟩
      have hxy := hnorm p hpT
      have hx2 : (p.1 : ℝ) ^ 2 ≤ X := by nlinarith [sq_nonneg (p.2 : ℝ)]
      have hle : |(p.1 : ℝ)| ≤ Real.sqrt X := by
        rw [Real.le_sqrt (abs_nonneg _) hX]
        rwa [sq_abs]
      exact abs_le.mp hle
  linarith [hmain]

theorem card_rows_le (α β : ℤ) (hβ : β ≠ 0) (K X : ℝ) (hK : 0 ≤ K) (hX : 0 ≤ X)
    (T : Finset (ℤ × ℤ))
    (hnorm : ∀ p ∈ T, ((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2 ≤ X)
    (hstrip : ∀ p ∈ T, |((α * p.1 - β * p.2 : ℤ) : ℝ)| < K) :
    (T.card : ℝ) ≤ (2 * Real.sqrt X + 1) * (2 * K / |(β : ℝ)| + 1) := by
  have hCnn : 0 ≤ 2 * K / |(β : ℝ)| + 1 := by
    have hβR : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
    have : 0 ≤ 2 * K / |(β : ℝ)| := by
      apply div_nonneg (by linarith) (abs_nonneg _)
    linarith
  have hsum_eq : (T.card : ℝ)
      = ∑ x ∈ T.image Prod.fst, ((T.filter (fun p => p.1 = x)).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := T) (t := T.image Prod.fst) (f := Prod.fst)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rw [h]
    push_cast
    rfl
  have hsum_le : (∑ x ∈ T.image Prod.fst, ((T.filter (fun p => p.1 = x)).card : ℝ))
      ≤ ∑ x ∈ T.image Prod.fst, (2 * K / |(β : ℝ)| + 1) :=
    Finset.sum_le_sum (fun x _ => fiber_card_le_aux α β hβ K hK T x hstrip)
  have hconst : (∑ x ∈ T.image Prod.fst, (2 * K / |(β : ℝ)| + 1))
      = ((T.image Prod.fst).card : ℝ) * (2 * K / |(β : ℝ)| + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hstep : (T.card : ℝ)
      ≤ ((T.image Prod.fst).card : ℝ) * (2 * K / |(β : ℝ)| + 1) := by
    rw [hsum_eq, ← hconst]
    exact hsum_le
  have hxc : ((T.image Prod.fst).card : ℝ) ≤ 2 * Real.sqrt X + 1 :=
    image_fst_card_le_aux X hX T hnorm
  calc (T.card : ℝ) ≤ ((T.image Prod.fst).card : ℝ) * (2 * K / |(β : ℝ)| + 1) := hstep
    _ ≤ (2 * Real.sqrt X + 1) * (2 * K / |(β : ℝ)| + 1) :=
        mul_le_mul_of_nonneg_right hxc hCnn

end Work.FIArea7.P231

import Mathlib

namespace Work.SimplyConnected.ABS

/-!
# From a weakly escaping direction to a strictly escaping one

Let `n i` be finitely many non-zero vectors of `ℂ` (a real inner product space).
If some non-zero `v` satisfies `⟪v, n i⟫ ≤ 0` for all `i`, and no two of the `n i` are
negative multiples of each other, then some `w` satisfies `⟪w, n i⟫ < 0` for all `i`.

The proof below is elementary and does not use compactness.  Write `⟪v, z⟫ = Re (z * conj v)`,
so `⟪v, z⟫ = v.re * z.re + v.im * z.im` (`inner_complex_re_im`).  Two vectors orthogonal to
`v ≠ 0` are real multiples of `I * v` (`exists_smul_I_of_inner_eq_zero`).  With this,
* if all `⟪v, n i⟫ < 0`, then `w = v` works;
* otherwise, fixing `i₀` with `⟪v, n i₀⟫ = 0`, all the `n i` orthogonal to `v` are positive
  multiples of `n i₀` (this is where the "no negative pair" hypothesis enters,
  `mul_inner_I_mul_pos_of_perp`), and `w = v + ε • (I * v)` for a suitable *small* `ε`
  of the right sign is strictly escaping.
-/

/-- The real inner product on `ℂ` in coordinates: `⟪v, z⟫_ℝ = v.re * z.re + v.im * z.im`. -/
theorem inner_complex_re_im (v z : ℂ) : inner ℝ v z = v.re * z.re + v.im * z.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- A vector `z` orthogonal to a nonzero vector `v` is a real multiple of `I * v`:
the real line `(I * v) • ℝ` is the orthogonal complement of `v`. -/
theorem exists_smul_I_of_inner_eq_zero {v z : ℂ} (hv : v ≠ 0) (h : inner ℝ v z = 0) :
    ∃ t : ℝ, z = t • (Complex.I * v) := by
  have hlin : v.re * z.re + v.im * z.im = 0 := by
    rw [inner_complex_re_im] at h; exact h
  have hden : v.re ^ 2 + v.im ^ 2 ≠ 0 := by
    have hc : v.re ≠ 0 ∨ v.im ≠ 0 := by
      by_contra hc
      rw [not_or] at hc
      simp only [ne_eq, not_not] at hc
      exact hv (by apply Complex.ext <;> simp [hc.1, hc.2])
    rcases hc with h1 | h1
    · have h2 : 0 < v.re ^ 2 := sq_pos_of_ne_zero h1
      nlinarith [sq_nonneg v.im]
    · have h2 : 0 < v.im ^ 2 := sq_pos_of_ne_zero h1
      nlinarith [sq_nonneg v.re]
  refine ⟨(v.re * z.im - v.im * z.re) / (v.re ^ 2 + v.im ^ 2), ?_⟩
  apply Complex.ext
  · simp only [Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hden]
    linear_combination v.re * hlin
  · simp only [Complex.smul_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hden]
    linear_combination v.im * hlin

/-- For `v ≠ 0`, `z ≠ 0` orthogonal to `v`, the pairing `⟪I * v, z⟫` does not vanish:
`z` is a nonzero real multiple of `I * v`. -/
theorem inner_I_mul_ne_zero_of_inner_eq_zero {v z : ℂ} (hv : v ≠ 0) (hz : z ≠ 0)
    (h : inner ℝ v z = 0) : inner ℝ (Complex.I * v) z ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_smul_I_of_inner_eq_zero hv h
  have hIv : Complex.I * v ≠ 0 := mul_ne_zero Complex.I_ne_zero hv
  have htne : t ≠ 0 := by
    intro h0
    exact hz (by rw [ht, h0, zero_smul])
  rw [ht, real_inner_smul_right]
  exact mul_ne_zero htne (inner_self_ne_zero.mpr hIv)

/-- **The sign lemma.**  Let `v ≠ 0` and let `x, y ≠ 0` both be orthogonal to `v`.  If `x` is
not a negative multiple of `y`, then `x` and `y` are *positive* multiples of each other, so the
pairings `⟪I * v, x⟫` and `⟪I * v, y⟫` have the same (strict) sign:
their product is positive. -/
theorem mul_inner_I_mul_pos_of_perp {v x y : ℂ} (hv : v ≠ 0) (hx0 : x ≠ 0) (hy : y ≠ 0)
    (hx : inner ℝ v x = 0) (hyv : inner ℝ v y = 0)
    (hnp : ∀ t : ℝ, 0 < t → x ≠ -t • y) :
    0 < inner ℝ (Complex.I * v) x * inner ℝ (Complex.I * v) y := by
  obtain ⟨tx, htx⟩ := exists_smul_I_of_inner_eq_zero hv hx
  obtain ⟨ty, hty⟩ := exists_smul_I_of_inner_eq_zero hv hyv
  have hIv : Complex.I * v ≠ 0 := mul_ne_zero Complex.I_ne_zero hv
  have htyne : ty ≠ 0 := by
    intro h0
    exact hy (by rw [hty, h0, zero_smul])
  set lam : ℝ := tx / ty with hlamdef
  have hxy : x = lam • y := by
    rw [hlamdef, htx, hty, smul_smul, div_mul_cancel₀ tx htyne]
  have hlampos : 0 < lam := by
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · exact hnp (-lam) (neg_pos.mpr hlt) (by rw [hxy, neg_neg])
    · exact hx0 (by rw [hxy, heq, zero_smul])
  have h1 : tx = lam * ty := by
    rw [hlamdef]; exact (div_mul_cancel₀ tx htyne).symm
  have hprod : 0 < tx * ty := by
    rw [h1, mul_assoc]
    exact mul_pos hlampos (mul_self_pos.mpr htyne)
  have hqne : inner ℝ (Complex.I * v) (Complex.I * v) ≠ 0 := inner_self_ne_zero.mpr hIv
  have hcalc : inner ℝ (Complex.I * v) x * inner ℝ (Complex.I * v) y
      = (tx * ty) * (inner ℝ (Complex.I * v) (Complex.I * v)
          * inner ℝ (Complex.I * v) (Complex.I * v)) := by
    rw [htx, hty, real_inner_smul_right, real_inner_smul_right]
    ring
  rw [hcalc]
  exact mul_pos hprod (mul_self_pos.mpr hqne)

/-- **A strictly escaping direction from a weakly escaping one.**

Let `n i` be finitely many non-zero vectors of `ℂ` (viewed as a real inner product space).  If
* there is a non-zero `v` with `⟪v, n i⟫ ≤ 0` for all `i` (a "weakly escaping" direction), and
* no two of the `n i` are negative multiples of each other (`n j ≠ -t • n i` for `i ≠ j`, `t > 0`;
  in the application this is exactly "two of the round balls are not externally tangent"),

then there is `w` with `⟪w, n i⟫ < 0` for all `i` (a "strictly escaping" direction).

Proof sketch (two routes, both elementary):
* **Minimum-on-the-sphere.**  Let `M v = max_i ⟪v, n i⟫` and take `v₀` minimising `M` on the unit
  sphere (compact; `M` continuous; `M ≤ 0` at the normalisation of the `v` of `ha`).  If `M v₀ < 0`
  then `w = v₀` works.  If `M v₀ = 0`, the indices `Z = {i : ⟪v₀, n i⟫ = 0}` are non-empty, all the
  corresponding `n i` lie in the line `v₀^⊥ = ℝ • (I * v₀)`, and `hb` forces all their scalars to
  have the same sign; then `w = v₀ - ε • (I * v₀)` (or `+`, matching that sign) has `⟪w, n i⟫ < 0`
  for `i ∈ Z`, and for `i ∉ Z` too once `ε > 0` is small enough.
* **Duality.**  Suppose no such `w`; Gordan's theorem (`¬ ∃ w, ∀ i, ⟪w, n i⟫ < 0` gives nonnegative
  `c` with `0 = Σ cᵢ • n i`) applied together with `ha` forces `⟪v, n i⟫ = 0` for every `i` with
  `cᵢ > 0`; there are at least two such `i`, their `n`'s are collinear in `v^⊥`, `hb` forces the
  ratios to be positive, so the nonnegative combination cannot vanish.

Useful API: `Finset.sup'_apply`, `Continuous.finset_sup'`, `IsCompact.exists_isMinOn`,
`isCompact_sphere`, `real_inner_smul_left`, `real_inner_smul_right`, `real_inner_comm`. -/
theorem linear_negative_of_no_opposite_pair {ι : Type*} [Fintype ι] [Nonempty ι] (n : ι → ℂ)
    (hne : ∀ i, n i ≠ 0)
    (ha : ∃ v : ℂ, v ≠ 0 ∧ ∀ i, inner ℝ v (n i) ≤ 0)
    (hb : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → n j ≠ -t • n i) :
    ∃ w : ℂ, ∀ i, inner ℝ w (n i) < 0 := by
  obtain ⟨v, hvne, hv⟩ := ha
  by_cases hz : ∃ i, inner ℝ v (n i) = 0
  · -- some direction is annihilated: perturb `v` inside `v^⊥ ⊗ ℝ`
    obtain ⟨i₀, hi₀⟩ := hz
    set c : ℝ := inner ℝ (Complex.I * v) (n i₀) with hcdef
    have hcne : c ≠ 0 := by
      rw [hcdef]
      exact inner_I_mul_ne_zero_of_inner_eq_zero hvne (hne i₀) hi₀
    -- the sign of the perturbation is the sign opposite to `c`
    set s : ℝ := if 0 < c then -1 else 1 with hsdef
    have hsabs : |s| = 1 := by
      rw [hsdef]; split_ifs <;> simp
    have hsc : s * c < 0 := by
      rw [hsdef]
      split_ifs with h
      · rw [neg_one_mul]; linarith
      · have hc : c < 0 := lt_of_le_of_ne (le_of_not_gt h) hcne
        rw [one_mul]; exact hc
    -- `G > 0` is a lower bound for all the (positive) gaps `-⟪v, n i⟫` at indices with `⟪v,n i⟫ < 0`
    have hgpos : ∀ i, 0 < (if inner ℝ v (n i) < 0 then -inner ℝ v (n i) else 1) := by
      intro i
      by_cases h : inner ℝ v (n i) < 0
      · rw [if_pos h]; linarith
      · rw [if_neg h]; norm_num
    set G : ℝ := Finset.univ.inf' Finset.univ_nonempty
        (fun i => if inner ℝ v (n i) < 0 then -inner ℝ v (n i) else 1) with hGdef
    have hGpos : 0 < G := by
      rw [hGdef, Finset.lt_inf'_iff]
      intro i _
      exact hgpos i
    have hGle : ∀ i, G ≤ (if inner ℝ v (n i) < 0 then -inner ℝ v (n i) else 1) := by
      intro i
      rw [hGdef]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    -- `M` dominates all `|⟪I * v, n i⟫|`
    set M : ℝ := 1 + ∑ i, |inner ℝ (Complex.I * v) (n i)| with hMdef
    have hMpos : 0 < M := by
      rw [hMdef]
      have := Finset.sum_nonneg (s := Finset.univ)
        (f := fun i => |inner ℝ (Complex.I * v) (n i)|) (fun i _ => abs_nonneg _)
      linarith
    have hMle : ∀ i, |inner ℝ (Complex.I * v) (n i)| ≤ M := by
      intro i
      have h1 : |inner ℝ (Complex.I * v) (n i)| ≤ ∑ j, |inner ℝ (Complex.I * v) (n j)| :=
        Finset.single_le_sum (f := fun j => |inner ℝ (Complex.I * v) (n j)|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      rw [hMdef]
      linarith
    set eps : ℝ := s * (G / (2 * M)) with hedef
    have hεabs : |eps| = G / (2 * M) := by
      rw [hedef, abs_mul, hsabs, one_mul, abs_of_nonneg (by positivity)]
    have hεc : eps * c < 0 := by
      have hpos : 0 < G / (2 * M) := by positivity
      have hrw : eps * c = (G / (2 * M)) * (s * c) := by rw [hedef]; ring
      rw [hrw]
      exact mul_neg_of_pos_of_neg hpos hsc
    refine ⟨v + eps • (Complex.I * v), fun i => ?_⟩
    rw [inner_add_left, real_inner_smul_left]
    by_cases hi : inner ℝ v (n i) = 0
    · -- `⟪v, n i⟫ = 0`: use the sign lemma
      by_cases hii : i = i₀
      · rw [hi, zero_add, hii, ← hcdef]
        exact hεc
      · have hprod := mul_inner_I_mul_pos_of_perp hvne (hne i) (hne i₀) hi hi₀
          (fun t ht => hb i₀ i (Ne.symm hii) t ht)
        have hB : inner ℝ (Complex.I * v) (n i) * c > 0 := by
          rw [← hcdef] at hprod; exact hprod
        have hcp : c * inner ℝ (Complex.I * v) (n i) > 0 := by
          simpa [mul_comm] using hB
        rw [hi, zero_add]
        have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hcne
        have hkey : eps * inner ℝ (Complex.I * v) (n i) * c ^ 2 < 0 := by
          have hrw : eps * inner ℝ (Complex.I * v) (n i) * c ^ 2
              = (eps * c) * (c * inner ℝ (Complex.I * v) (n i)) := by ring
          rw [hrw]
          exact mul_neg_of_neg_of_pos hεc hcp
        exact (mul_lt_mul_iff_of_pos_right hc2).mp (by simpa using hkey)
    · -- `⟪v, n i⟫ < 0`: the perturbation is small enough
      have hlt : inner ℝ v (n i) < 0 := lt_of_le_of_ne (hv i) hi
      have hgsmall : G ≤ -inner ℝ v (n i) := by
        have h := hGle i
        rwa [if_pos hlt] at h
      have hεB : eps * inner ℝ (Complex.I * v) (n i) ≤ G / 2 := by
        have h1 : eps * inner ℝ (Complex.I * v) (n i)
            ≤ |eps * inner ℝ (Complex.I * v) (n i)| :=
          le_abs_self _
        have h2 : |eps * inner ℝ (Complex.I * v) (n i)|
            = (G / (2 * M)) * |inner ℝ (Complex.I * v) (n i)| := by
          rw [abs_mul, hεabs]
        have h3 : (G / (2 * M)) * |inner ℝ (Complex.I * v) (n i)| ≤ (G / (2 * M)) * M :=
          mul_le_mul_of_nonneg_left (hMle i) (by positivity)
        have h4 : (G / (2 * M)) * M = G / 2 := by
          field_simp
        linarith
      linarith
  · -- `⟪v, n i⟫ < 0` for every `i`, so `v` itself is strictly escaping
    rw [not_exists] at hz
    exact ⟨v, fun i => lt_of_le_of_ne (hv i) (hz i)⟩

end Work.SimplyConnected.ABS

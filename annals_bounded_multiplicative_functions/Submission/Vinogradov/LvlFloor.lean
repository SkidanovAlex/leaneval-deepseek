/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymJump
import Submission.Vinogradov.AsymExpBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §4: the floor comparisons between the canonical and the refined levels

The §4 exponent `A_l(b)` of GLYZ (arXiv:1912.09798) is defined through the *canonical* level pair
`(⌊a_l(b)·N⌋, ⌊b·N⌋)` where `a_l(b) = ((k−l+1)/l)·b`, while GLYZ Lemma 3.9 (our
`UniformChain.asymDec_of_model_uniform`) consumes and produces the *refined* level
`refLvl l k m = ((k−l+1)·m)/l`.  This module collects the three comparisons between the two.

* `floor_refLvl_le_lvlOf` — `refLvl L k (lvlOf y N) ≤ lvlOf (asymRatio k L * y) N`: the
  refinement is always coarser (the floor identity `⌊c·⌊yN⌋⌋ ≤ ⌊c·y·N⌋`).
* `floor_lvlOf_le_refLvl_add` — `lvlOf (asymRatio k L * y) N ≤ refLvl L k (lvlOf y N) + (k+1)`:
  the canonical level is at most `k+1` levels finer.  Together with `AsymJump.asymDec_coarsen`
  (`D ≤ k+1`) this bridges the two.
* `cast_refLvl_ge`, `exists_lvlOf_le_refLvl` — the *slack* comparison: if
  `c₂ < ((k−L+1)/L)·c₀` then for all large `N` the level `lvlOf (c₂ y) N` lies below
  `refLvl L k (lvlOf (c₀ y) N)`.
* `one_lt_asymRatio_mul_ratio` and `asymRatio_lt_ratio` — the two concrete instances of that
  slack condition which the two factors of the recursion satisfy.

The module is imported by `ROADMAP.lean` only; it is not on the comparator chain.
-/

namespace Submission.Vinogradov

/-- **The refined level is coarser than the canonical level.** -/
lemma floor_refLvl_le_lvlOf {k L N : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) {y : ℝ} (hy : 0 ≤ y) :
    refLvl L k (lvlOf y N) ≤ lvlOf (asymRatio k L * y) N := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLnat : 0 < L := by omega
  have hmle : ((lvlOf y N : ℕ) : ℝ) ≤ y * (N : ℝ) :=
    Nat.floor_le (mul_nonneg hy (Nat.cast_nonneg N))
  have hKgt : asymRatio k L * y * (N : ℝ) < ((lvlOf (asymRatio k L * y) N : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hLc : (L : ℝ) * asymRatio k L = ((k - L + 1 : ℕ) : ℝ) := by
    rw [asymRatio_of_pos hL, Nat.cast_add, Nat.cast_one, Nat.cast_sub hLk]
    field_simp
  have key : ((k - L + 1) * (lvlOf y N) : ℕ) < (lvlOf (asymRatio k L * y) N + 1) * L := by
    have hR : (((k - L + 1) * (lvlOf y N) : ℕ) : ℝ)
        < (((lvlOf (asymRatio k L * y) N + 1) * L : ℕ) : ℝ) := by
      push_cast
      have h1 : ((k - L + 1 : ℕ) : ℝ) * ((lvlOf y N : ℕ) : ℝ)
          ≤ ((k - L + 1 : ℕ) : ℝ) * (y * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hmle (by positivity)
      have h2 : ((k - L + 1 : ℕ) : ℝ) * (y * (N : ℝ))
          = (L : ℝ) * (asymRatio k L * y * (N : ℝ)) := by
        rw [show (L : ℝ) * (asymRatio k L * y * (N : ℝ))
            = ((L : ℝ) * asymRatio k L) * (y * (N : ℝ)) by ring, hLc]
      have h3 : (L : ℝ) * (asymRatio k L * y * (N : ℝ))
          < (L : ℝ) * (((lvlOf (asymRatio k L * y) N : ℕ) : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hKgt hLpos
      have hcast1 : ((k - L + 1 : ℕ) : ℝ) = ((k - L : ℕ) : ℝ) + 1 := by push_cast; ring
      nlinarith [h1, h2, h3, hcast1]
    exact_mod_cast hR
  have hdiv : ((k - L + 1) * (lvlOf y N)) / L ≤ lvlOf (asymRatio k L * y) N := by
    have h := (Nat.div_lt_iff_lt_mul hLnat).mpr key
    exact Nat.lt_succ_iff.mp h
  rw [refLvl]
  exact hdiv

/-- **The canonical level is at most `k+1` levels finer than the refined level.** -/
lemma floor_lvlOf_le_refLvl_add {k L N : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    {y : ℝ} (hy : 0 ≤ y) :
    lvlOf (asymRatio k L * y) N ≤ refLvl L k (lvlOf y N) + (k + 1) := by
  have hc0 : 0 ≤ asymRatio k L := (asymRatio_pos hk hL hLk).le
  have hcle : asymRatio k L ≤ (k : ℝ) := asymRatio_le hk hL hLk
  have hlt : y * (N : ℝ) < ((lvlOf y N : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcm : asymRatio k L * ((lvlOf y N : ℕ) : ℝ)
      = (((k - L + 1 : ℕ) : ℝ) * ((lvlOf y N : ℕ) : ℝ)) / (L : ℝ) := by
    have hcast : ((k - L + 1 : ℕ) : ℝ) = (k : ℝ) - (L : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hLk]
    rw [asymRatio_of_pos hL, div_mul_eq_mul_div, hcast]
  have hstep : ((lvlOf (asymRatio k L * y) N : ℕ) : ℝ)
      ≤ asymRatio k L * ((lvlOf y N : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) := by
    have h1 : ((lvlOf (asymRatio k L * y) N : ℕ) : ℝ) ≤ asymRatio k L * y * (N : ℝ) := by
      rw [lvlOf]; exact Nat.floor_le (mul_nonneg (mul_nonneg hc0 hy) (Nat.cast_nonneg N))
    have h2 : asymRatio k L * y * (N : ℝ) ≤ asymRatio k L * (((lvlOf y N : ℕ) : ℝ) + 1) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hlt.le hc0
    have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    nlinarith [h1, h2, hcle, hk1]
  have hfloor : ⌊asymRatio k L * ((lvlOf y N : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ)⌋₊
      = ((k - L + 1) * (lvlOf y N)) / L + (k + 1) := by
    rw [Nat.floor_add_natCast (by positivity), hcm, Nat.floor_div_natCast]
    simp only [← Nat.cast_mul, Nat.floor_natCast]
  have hfin := le_trans (Nat.le_floor hstep) (le_of_eq hfloor)
  rw [refLvl]
  exact hfin


lemma cast_refLvl_ge {k L : ℕ} (hL : 1 ≤ L) (m : ℕ) :
    (((k - L + 1 : ℕ) : ℝ) / (L : ℝ)) * (m : ℝ) - 1 ≤ ((refLvl L k m : ℕ) : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLnat : 0 < L := by omega
  have hA : ((refLvl L k m : ℕ) : ℝ) = ((((k - L + 1) * m) / L : ℕ) : ℝ) := rfl
  rw [hA]
  have h1 : ((k - L + 1) * m : ℕ) < ((((k - L + 1) * m) / L + 1) * L : ℕ) :=
    (Nat.div_lt_iff_lt_mul hLnat).mp (Nat.lt_succ_self _)
  have h2 : (((k - L + 1) * m : ℕ) : ℝ) < (((((k - L + 1) * m) / L + 1) * L : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  have hcast : ((k - L + 1 : ℕ) : ℝ) = ((k - L : ℕ) : ℝ) + 1 := by push_cast; ring
  have h3 : ((k - L + 1 : ℕ) : ℝ) * (m : ℝ) / (L : ℝ)
      < ((((k - L + 1) * m) / L : ℕ) : ℝ) + 1 := by
    rw [hcast]
    rw [div_lt_iff₀ hLpos]
    linarith [h2]
  have h4 : ((k - L + 1 : ℕ) : ℝ) * (m : ℝ) / (L : ℝ)
      = (((k - L + 1 : ℕ) : ℝ) / (L : ℝ)) * (m : ℝ) := by ring
  linarith [h3, h4]

lemma exists_lvlOf_le_refLvl {k L : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    {c₀ c₂ y : ℝ} (hy : 0 < y) (hc0 : 0 < c₀) (hc2 : 0 < c₂)
    (h : c₂ < (((k - L + 1 : ℕ) : ℝ) / (L : ℝ)) * c₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → lvlOf (c₂ * y) N ≤ refLvl L k (lvlOf (c₀ * y) N) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  set a : ℝ := ((k - L + 1 : ℕ) : ℝ) / (L : ℝ) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  set d : ℝ := a * c₀ - c₂ with hd
  have hdpos : 0 < d := by rw [hd, ha]; linarith
  have hdy : 0 < d * y := mul_pos hdpos hy
  refine ⟨⌈(a + 1) / (d * y)⌉₊ + 1, fun N hN => ?_⟩
  have hNge : (a + 1) / (d * y) ≤ (N : ℝ) := by
    have h1 : (a + 1) / (d * y) ≤ ((⌈(a + 1) / (d * y)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(a + 1) / (d * y)⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hkey : a + 1 ≤ d * y * (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hNge hdy.le
    rw [div_mul_cancel₀ _ (ne_of_gt hdy)] at hh
    linarith
  have hm0 : c₀ * y * (N : ℝ) - 1 ≤ ((lvlOf (c₀ * y) N : ℕ) : ℝ) := by
    have hlt : c₀ * y * (N : ℝ) < ((lvlOf (c₀ * y) N : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have hN2 : ((lvlOf (c₂ * y) N : ℕ) : ℝ) ≤ c₂ * y * (N : ℝ) :=
    Nat.floor_le (mul_nonneg (mul_nonneg hc2.le hy.le) (Nat.cast_nonneg N))
  have hfloor := cast_refLvl_ge (k := k) hL (lvlOf (c₀ * y) N)
  have : ((lvlOf (c₂ * y) N : ℕ) : ℝ) ≤ ((refLvl L k (lvlOf (c₀ * y) N) : ℕ) : ℝ) := by
    have hA : a * ((lvlOf (c₀ * y) N : ℕ) : ℝ) ≥ a * (c₀ * y * (N : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hm0 hapos.le
    have hB : a * (c₀ * y * (N : ℝ) - 1) = (a * c₀) * y * (N : ℝ) - a := by ring
    have hC : d * y * (N : ℝ) = (a * c₀) * y * (N : ℝ) - c₂ * y * (N : ℝ) := by
      rw [hd]; ring
    linarith [hN2, hfloor, hA, hkey, hB, hC]
  exact_mod_cast this

/-! ## The two concrete level comparisons of the §4 recursion -/

/-- **Factor 1 of the recursion.**  For small `b` and large `N`, the `I'`-level `lvlOf b N`
lies below the refinement `refLvl (k−l) k` of the canonical `(k−l)`-level `lvlOf (ρb) N`. -/
lemma one_lt_asymRatio_mul_ratio {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) :
    (1 : ℝ) < (((k - (k - l) + 1 : ℕ) : ℝ) / ((k - l : ℕ) : ℝ)) * asymRatio k l := by
  have hkl : 1 ≤ k - l := by omega
  have hcast : ((k - (k - l) + 1 : ℕ) : ℝ) = (l : ℝ) + 1 := by
    have h1 : k - (k - l) + 1 = l + 1 := by omega
    rw [h1]; push_cast; ring
  have hl0 : (0:ℝ) < (l:ℝ) := by positivity
  have hkl0 : (0:ℝ) < ((k - l : ℕ) : ℝ) := by
    have : 0 < k - l := by omega
    exact_mod_cast this
  have hklR : ((k - l : ℕ) : ℝ) = (k:ℝ) - (l:ℝ) := Nat.cast_sub (by omega : l ≤ k)
  rw [hcast, asymRatio_of_pos hl, div_mul_div_comm, lt_div_iff₀ (mul_pos hkl0 hl0), hklR]
  nlinarith [show (0:ℝ) < (k:ℝ) + 1 from by positivity]

/-- **Factor 2 of the recursion.**  For `l ≥ 2`, small `b` and large `N`, the canonical
`l`-level `lvlOf (ρb) N` lies below the refinement `refLvl (l−1) k` of the `I'`-level
`lvlOf b N`. -/
lemma asymRatio_lt_ratio {k l : ℕ} (hl : 2 ≤ l) (hlk : l ≤ k - 1) :
    asymRatio k l < (((k - (l - 1) + 1 : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ)) * 1 := by
  have hl1 : 1 ≤ l := by omega
  have hlpos : (0:ℝ) < (l:ℝ) := by positivity
  have hl1pos : (0:ℝ) < ((l - 1 : ℕ) : ℝ) := by
    have : 0 < l - 1 := by omega
    exact_mod_cast this
  have hcast1 : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by
    rw [Nat.cast_sub hl1]; norm_num
  have hcast2 : ((k - (l - 1) + 1 : ℕ) : ℝ) = (k:ℝ) - (l:ℝ) + 2 := by
    have h1 : k - (l - 1) + 1 = k - l + 2 := by omega
    rw [h1, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub (by omega : l ≤ k)]
  rw [asymRatio_of_pos hl1, hcast2, mul_one, div_lt_div_iff₀ hlpos hl1pos, hcast1]
  nlinarith [show (0:ℝ) < (k:ℝ) + 1 from by positivity]

end Submission.Vinogradov

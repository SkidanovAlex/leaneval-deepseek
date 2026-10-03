import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.walk_re_mono
import Submission.Work.Pert.Count.exists_int_dist_le_of_iInf_le
import Submission.Work.Pert.Count.count_arith_small
import Submission.Work.Pert.Count.count_arith_big

/-!
# PERT · `Work.Pert.count_gate_walk_close`

A *counting* lemma for the gate walk of Shishikura §4.2 (the "how often is the walk close to the
lattice `ℤ/α`" bound used in the drift estimate for the lifted return map).

Let `w : ℕ → ℂ` be a walk with `w (j+1) ≈ w j + 1` (defect `≤ 1/32`) and let `s ≥ ‖α‖`.  Then the
number of indices `j ≤ n` with `dist (α * w j) ℤ ≤ s` is at most `30 (s/‖α‖)(1 + n‖α‖)`.

**Proof idea (the argument, in one paragraph).**  Write `t j := Re (α * w j)`.  Since
`InF1 α` says `|Im α| < Re α`, we have `‖α‖ < 2 Re α`, and the walk defects give
`t (j+1) - t j = Re α + Re (α (w (j+1) - w j - 1)) ∈ [Re α - ‖α‖/32, Re α + ‖α‖/32]`; in
particular `t` increases by at least `‖α‖/3` per step.  Moreover `dist (α * w j) ℤ ≤ s` forces
`|Im (α * w j)| ≤ s`, i.e. the *real part* `t j` is within `s` of an integer.  Hence the counted
set is contained in `{j ≤ n : dist (t j) ℤ ≤ s}`, and a purely one-dimensional counting argument
(`card_le_of_mono_walk_aux` below: group the good indices by the nearest integer to `t j`; each
group sits in an interval of length `2s`, so has `≤ 2s/δ + 1` elements, and the integers arising
lie in `[t 0 - s, t n + s]`, so there are at most `(t n - t 0) + 2s + 1` groups) gives

`#C ≤ ((t n - t 0) + 2s + 1) (2s/(‖α‖/3) + 1) ≤ ((33/32) n ‖α‖ + 2s + 1) (6 s/‖α‖ + 1)`.

If `2s ≤ 1` the last expression is `≤ 30 (s/‖α‖)(1 + n‖α‖)` (`Work.Pert.Count.count_arith_small`);
if `1 ≤ 2s` then already `#C ≤ n + 1 ≤ 30 (s/‖α‖)(1 + n‖α‖)`
(`Work.Pert.Count.count_arith_big`).

Note that the gate hypothesis `hgate` (and `hΞ`) is *not needed*: the bound follows from the step
condition and the sector condition alone.  -/

namespace Work.Pert

noncomputable section

/-! ## A one-dimensional lattice-counting lemma

`card_le_of_mono_walk_aux` is the combinatorial heart: an increasing sequence `t` with steps
`≥ δ` can be within `s` of an integer only rarely.  It is proved here (self-contained) from the
three small helpers below. -/

/-- A real sequence with steps `≥ δ` grows at least linearly: `t i + (j-i)δ ≤ t j` for `i ≤ j ≤ n`.
(Obtained from `Work.Pert.walk_re_mono` by rescaling with the factor `2δ`.) -/
private lemma gap_of_step {t : ℕ → ℝ} {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hmono : ∀ j < n, t j + δ ≤ t (j + 1)) :
    ∀ i j, i ≤ j → j ≤ n → t i + ((j - i : ℕ) : ℝ) * δ ≤ t j := by
  intro i j hij hjn
  have h2 : (0:ℝ) < 2 * δ := by linarith
  have hx : ∀ k < n, t k / (2 * δ) + 1 / 2 ≤ t (k + 1) / (2 * δ) := by
    intro k hk
    have h4 : t k / (2 * δ) + 1 / 2 = (t k + δ) / (2 * δ) := by field_simp
    rw [h4, div_le_div_iff_of_pos_right h2]
    exact hmono k hk
  have hw := Work.Pert.walk_re_mono (x := fun k => t k / (2 * δ)) (k := n) hx i j hij hjn
  have hm := mul_le_mul_of_nonneg_right hw (le_of_lt h2)
  have e1 : (t i / (2 * δ)) * (2 * δ) = t i := by field_simp
  have e2 : (t j / (2 * δ)) * (2 * δ) = t j := by field_simp
  have e3 : (t i / (2 * δ) + ((j - i : ℕ) : ℝ) / 2) * (2 * δ)
      = t i + ((j - i : ℕ) : ℝ) * δ := by field_simp
  linarith [hm, e1, e2, e3]

/-- `(m.toNat : ℝ) ≤ y` whenever `(m : ℝ) ≤ y` and `0 ≤ y` (for `m : ℤ`). -/
private lemma toNat_cast_le {m : ℤ} {y : ℝ} (h : (m : ℝ) ≤ y) (hy : 0 ≤ y) :
    (m.toNat : ℝ) ≤ y := by
  rcases lt_or_ge (0 : ℤ) m with hm | hm
  · have h1 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
    calc (m.toNat : ℝ) = ((m.toNat : ℤ) : ℝ) := by push_cast; ring
      _ = (m : ℝ) := by rw [h1]
      _ ≤ y := h
  · have h1 : m.toNat = 0 := Int.toNat_of_nonpos hm
    rw [h1]; simpa using hy

/-- **Counting the integers in an interval**: a finite set of integers all lying in a real
interval `[A, B]` (with `A ≤ B`) has at most `B - A + 1` elements. -/
private lemma card_le_of_int_interval {K : Finset ℤ} {A B : ℝ} (hAB : A ≤ B)
    (h : ∀ k ∈ K, A ≤ (k : ℝ) ∧ (k : ℝ) ≤ B) :
    (K.card : ℝ) ≤ B - A + 1 := by
  have hsub : K ⊆ Finset.Icc ⌈A⌉ ⌊B⌋ := by
    intro k hk
    obtain ⟨h1, h2⟩ := h k hk
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  calc (K.card : ℝ) ≤ ((Finset.Icc ⌈A⌉ ⌊B⌋).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((⌊B⌋ + 1 - ⌈A⌉ : ℤ).toNat : ℝ) := by rw [Int.card_Icc]
    _ ≤ B - A + 1 := by
        refine toNat_cast_le ?_ ?_
        · push_cast; linarith [Int.floor_le B, Int.le_ceil A]
        · linarith

/-- **Clusters**: a set of natural numbers with `(a' - a) δ ≤ 2 s` for all `a ≤ a'` in it (i.e. of
diameter `≤ 2s/δ`) has at most `2s/δ + 1` elements. -/
private lemma card_le_of_cluster {F : Finset ℕ} {δ s : ℝ} (hδ : 0 < δ) (hs0 : 0 ≤ s)
    (hF : ∀ a ∈ F, ∀ a' ∈ F, a ≤ a' → ((a' - a : ℕ) : ℝ) * δ ≤ 2 * s) :
    (F.card : ℝ) ≤ 2 * s / δ + 1 := by
  rcases F.eq_empty_or_nonempty with h | h
  · rw [h, Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ 2 * s / δ := div_nonneg (by linarith) (le_of_lt hδ)
    linarith
  · have hA : (F.max' h : ℝ) - 2 * s / δ ≤ (F.max' h : ℝ) := by
      have : 0 ≤ 2 * s / δ := div_nonneg (by linarith) (le_of_lt hδ); linarith
    have hcard : ((F.image (fun a : ℕ => (a : ℤ))).card : ℝ) ≤ 2 * s / δ + 1 := by
      have hkey := card_le_of_int_interval (K := F.image (fun a : ℕ => (a : ℤ))) hA ?_
      · have hthis : (F.max' h : ℝ) - ((F.max' h : ℝ) - 2 * s / δ) + 1
            = 2 * s / δ + 1 := by ring
        linarith [hkey, hthis]
      · intro k hk
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
        have hle : ((F.max' h - a : ℕ) : ℝ) * δ ≤ 2 * s :=
          hF a ha (F.max' h) (Finset.max'_mem F h) (Finset.le_max' F a ha)
        have hle' : ((F.max' h - a : ℕ) : ℝ) ≤ 2 * s / δ := by
          rw [le_div_iff₀ hδ]; linarith
        have hcast : ((F.max' h - a : ℕ) : ℝ) = (F.max' h : ℝ) - (a : ℝ) :=
          Nat.cast_sub (Finset.le_max' F a ha)
        constructor
        · push_cast; linarith
        · push_cast; exact_mod_cast Finset.le_max' F a ha
    have hEq : ((F.image (fun a : ℕ => (a : ℤ))).card : ℝ) = (F.card : ℝ) := by
      rw [Finset.card_image_of_injective _ (fun a b hab => by exact_mod_cast hab)]
    rwa [hEq] at hcard

/-- **The one-dimensional counting bound.**  Let `t : ℕ → ℝ` increase by at least `δ` at every
step below `n`, and let `p` be a predicate on indices such that every `j ≤ n` satisfying `p j` has
`t j` within distance `s` of an integer.  Then

`#{j ≤ n : p j} ≤ ((t n - t 0) + 2 s + 1) * (2 s / δ + 1)`.

(Group the good indices by the nearest integer; each group lies in an interval of length `2s`.) -/
private lemma card_le_of_mono_walk_aux {t : ℕ → ℝ} {n : ℕ} {s δ : ℝ} {p : ℕ → Prop}
    [DecidablePred p]
    (hδ : 0 < δ) (hs0 : 0 ≤ s) (hmono : ∀ j < n, t j + δ ≤ t (j + 1))
    (hp : ∀ j ≤ n, p j → ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s) :
    ((((Finset.range (n + 1)).filter p).card : ℝ))
      ≤ ((t n - t 0) + 2 * s + 1) * (2 * s / δ + 1) := by
  classical
  have hgap : ∀ i j, i ≤ j → j ≤ n → t i + ((j - i : ℕ) : ℝ) * δ ≤ t j :=
    gap_of_step hδ hmono
  set C : Finset ℕ := (Finset.range (n + 1)).filter p with hC
  have hmem : ∀ j ∈ C, j ≤ n := by
    intro j hj; rw [hC] at hj
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have hpk : ∀ j ∈ C, p j := by
    intro j hj; rw [hC] at hj; exact (Finset.mem_filter.mp hj).2
  have hex : ∀ j ∈ C, ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s :=
    fun j hj => hp j (hmem j hj) (hpk j hj)
  -- choose, for each good index, the nearest integer
  let kf : ℕ → ℤ := fun j =>
    if h : ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s then Classical.choose h else 0
  have hkf : ∀ j ∈ C, dist (t j) (kf j : ℝ) ≤ s := by
    intro j hj
    have h := hex j hj
    simp only [kf, dif_pos h]
    exact Classical.choose_spec h
  -- each fibre of `kf` is a cluster of diameter `≤ 2 s / δ`
  have hfiber : ∀ b ∈ C.image kf, ((C.filter (fun a => kf a = b)).card : ℝ) ≤ 2 * s / δ + 1 := by
    intro b hb
    refine card_le_of_cluster hδ hs0 ?_
    intro a ha a' ha' haa'
    rw [Finset.mem_filter] at ha ha'
    have h1 : |t a - (b : ℝ)| ≤ s := by
      have h2 := hkf a ha.1
      rw [ha.2, Real.dist_eq] at h2
      exact h2
    have h2 : |t a' - (b : ℝ)| ≤ s := by
      have h3 := hkf a' ha'.1
      rw [ha'.2, Real.dist_eq] at h3
      exact h3
    have h4 : (b : ℝ) - s ≤ t a := by linarith [(abs_le.mp h1).1]
    have h5 : t a' ≤ (b : ℝ) + s := by linarith [(abs_le.mp h2).2]
    have h6 : t a + ((a' - a : ℕ) : ℝ) * δ ≤ t a' := hgap a a' haa' (hmem a' ha'.1)
    nlinarith [h4, h5, h6]
  -- the integers used all lie in `[t 0 - s, t n + s]`
  have himg : ((C.image kf).card : ℝ) ≤ (t n - t 0) + 2 * s + 1 := by
    have hbdd : ∀ k ∈ C.image kf, t 0 - s ≤ (k : ℝ) ∧ (k : ℝ) ≤ t n + s := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hja := hkf j hj
      rw [Real.dist_eq] at hja
      obtain ⟨hkl, hku⟩ := abs_le.mp hja
      have hjn := hmem j hj
      have h1 : t 0 ≤ t j := by
        have hh := hgap 0 j (Nat.zero_le _) hjn
        have h3 : (0:ℝ) ≤ ((j - 0 : ℕ) : ℝ) * δ := by positivity
        linarith
      have h2 : t j ≤ t n := by
        have hh := hgap j n hjn le_rfl
        have h3 : (0:ℝ) ≤ ((n - j : ℕ) : ℝ) * δ := by positivity
        linarith
      constructor <;> linarith
    have hAB : t 0 - s ≤ t n + s := by
      have hh := hgap 0 n (Nat.zero_le _) le_rfl
      have h3 : (0:ℝ) ≤ ((n - 0 : ℕ) : ℝ) * δ := by positivity
      linarith
    have h := card_le_of_int_interval (K := C.image kf) hAB hbdd
    linarith [h]
  have hsum : (C.card : ℝ)
      = ∑ b ∈ C.image kf, ((C.filter (fun a => kf a = b)).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := kf) (s := C) (t := C.image kf)
      (fun a ha => Finset.mem_image_of_mem kf ha)
    rw [h, Nat.cast_sum]
  calc (C.card : ℝ) = ∑ b ∈ C.image kf, ((C.filter (fun a => kf a = b)).card : ℝ) := hsum
    _ ≤ ∑ b ∈ C.image kf, (2 * s / δ + 1) := Finset.sum_le_sum (fun b hb => hfiber b hb)
    _ = ((C.image kf).card : ℝ) * (2 * s / δ + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((t n - t 0) + 2 * s + 1) * (2 * s / δ + 1) := by
        have hpos : 0 ≤ 2 * s / δ + 1 := by
          have : 0 ≤ 2 * s / δ := div_nonneg (by linarith) (le_of_lt hδ); linarith
        exact mul_le_mul_of_nonneg_right himg hpos

/-! ## The target lemma -/

theorem count_gate_walk_close {α : ℂ} {Ξ : ℝ} {w : ℕ → ℂ} {n : ℕ} {s : ℝ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hs : ‖α‖ ≤ s)
    (hstep : ∀ j < n, ‖w (j+1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    (((Finset.range (n+1)).filter (fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ s)).card : ℝ)
      ≤ 30 * (s / ‖α‖) * (1 + (n : ℝ) * ‖α‖) := by
  have hb : |α.im| < α.re := hInF1
  have hre_pos : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hb
  have hne : α ≠ 0 := by intro h; rw [h] at hre_pos; simp at hre_pos
  have ha_pos : 0 < ‖α‖ := norm_pos_iff.mpr hne
  -- the sector condition: `‖α‖ < 2 Re α`
  have ha2 : ‖α‖ < 2 * α.re := by
    have h1 : ‖α‖ ≤ |α.re| + |α.im| := Complex.norm_le_abs_re_add_abs_im α
    rw [abs_of_pos hre_pos] at h1; linarith
  have hsnneg : 0 ≤ s := le_trans (norm_nonneg α) hs
  -- the real part of the walk step, as `Re α` plus the (small) defect contribution
  have hdiff : ∀ j < n, (α * w (j+1)).re - (α * w j).re
      = (α * (w (j+1) - (w j + 1))).re + α.re := by
    intro j hj
    have h1 : α * w (j+1) - α * w j = α * (w (j+1) - (w j + 1)) + α := by ring
    calc (α * w (j+1)).re - (α * w j).re = (α * w (j+1) - α * w j).re := by
          simp [Complex.sub_re]
      _ = (α * (w (j+1) - (w j + 1)) + α).re := by rw [h1]
      _ = (α * (w (j+1) - (w j + 1))).re + α.re := by simp [Complex.add_re]
  have hsmall : ∀ j < n, |(α * (w (j+1) - (w j + 1))).re| ≤ ‖α‖ * (1/32) := by
    intro j hj
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_mul_le _ _) ?_
    exact mul_le_mul_of_nonneg_left (hstep j hj) (norm_nonneg _)
  -- the two one-sided increment bounds
  have hincr0 : ∀ j < n, (α * w j).re + ‖α‖ / 3 ≤ (α * w (j+1)).re := by
    intro j hj
    have h3 : -(‖α‖ * (1/32)) ≤ (α * (w (j+1) - (w j + 1))).re := by
      have := (abs_le.mp (hsmall j hj)).1
      linarith
    have h6 : ‖α‖ / 3 ≤ α.re - ‖α‖ * (1/32) := by nlinarith [ha2]
    linarith [hdiff j hj]
  have hup0 : ∀ j < n, (α * w (j+1)).re - (α * w j).re ≤ (33/32) * ‖α‖ := by
    intro j hj
    have h3 : (α * (w (j+1) - (w j + 1))).re ≤ ‖α‖ * (1/32) := (abs_le.mp (hsmall j hj)).2
    have h6 : α.re ≤ ‖α‖ := Complex.re_le_norm α
    linarith [hdiff j hj]
  set t : ℕ → ℝ := fun j => (α * w j).re with ht
  have hmono : ∀ j < n, t j + ‖α‖ / 3 ≤ t (j+1) := fun j hj => by
    simpa only [ht] using hincr0 j hj
  have hup : ∀ j < n, t (j+1) - t j ≤ (33/32) * ‖α‖ := fun j hj => by
    simpa only [ht] using hup0 j hj
  set C : Finset ℕ := (Finset.range (n+1)).filter
      (fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ s) with hC
  -- a point of the counted set is (in real part) close to an integer
  have hp : ∀ j ≤ n, ((⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ s) →
      ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s := by
    intro j hj hpj
    obtain ⟨k, hk⟩ :=
      Count.exists_int_dist_le_of_iInf_le (z := α * w j) (s := s) hsnneg hpj
    refine ⟨k, ?_⟩
    show dist ((α * w j).re) (k : ℝ) ≤ s
    have hkey : dist ((α * w j).re) (k : ℝ) ≤ dist (α * w j) (k : ℂ) := by
      rw [Real.dist_eq, Complex.dist_eq]
      have h : ((α * w j) - (k : ℂ)).re = (α * w j).re - (k : ℝ) := by simp
      rw [← h]
      exact Complex.abs_re_le_norm _
    exact le_trans hkey hk
  -- the real part grows at most linearly
  have hgrowth : ∀ j ≤ n, t j - t 0 ≤ (33/32) * (j : ℝ) * ‖α‖ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have h1 : t k - t 0 ≤ (33/32) * (k : ℝ) * ‖α‖ := ih (by omega)
        have h2 : t (k+1) - t k ≤ (33/32) * ‖α‖ := hup k (by omega)
        have h3 : t (k+1) - t 0 = (t (k+1) - t k) + (t k - t 0) := by ring
        have h4 : (33/32) * ((k+1 : ℕ) : ℝ) * ‖α‖
            = (33/32) * (k : ℝ) * ‖α‖ + (33/32) * ‖α‖ := by push_cast; ring
        rw [h3, h4]
        linarith
  by_cases hbig : 1 ≤ 2 * s
  · -- regime `s ≥ 1/2`: the trivial cardinality bound `n + 1` suffices
    have hcard : C.card ≤ n + 1 := by
      rw [hC]
      calc ((Finset.range (n+1)).filter (fun j => (⨅ k : ℤ, dist (α*w j) (k:ℂ)) ≤ s)).card
          ≤ (Finset.range (n+1)).card := Finset.card_filter_le _ _
        _ = n + 1 := Finset.card_range _
    calc (C.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
      _ ≤ 30 * (s / ‖α‖) * (1 + (n:ℝ) * ‖α‖) :=
          Count.count_arith_big ha_pos hs hbig
  · -- regime `2 s ≤ 1`: the one-dimensional lattice count
    have hs2 : 2 * s ≤ 1 := by linarith [not_le.mp hbig]
    have hL2 := card_le_of_mono_walk_aux (t := t) (n := n) (s := s) (δ := ‖α‖/3)
        (p := fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ s)
        (by positivity) hsnneg hmono hp
    have hCbound : (C.card : ℝ) ≤ ((t n - t 0) + 2*s + 1) * (2*s/(‖α‖/3) + 1) := by
      rw [hC]; exact hL2
    have hdiv : 2 * s / (‖α‖/3) = 6 * (s / ‖α‖) := by
      have hne' : ‖α‖ ≠ 0 := ne_of_gt ha_pos
      field_simp
      ring
    have h3 : (t n - t 0) + 2*s + 1 ≤ (33/32)*(n:ℝ)*‖α‖ + 2*s + 1 := by
      have := hgrowth n le_rfl; linarith
    have hpos : 0 ≤ 6 * (s / ‖α‖) + 1 := by
      have := div_nonneg hsnneg (norm_nonneg α); linarith
    calc (C.card : ℝ) ≤ ((t n - t 0) + 2*s + 1) * (2*s/(‖α‖/3) + 1) := hCbound
      _ = ((t n - t 0) + 2*s + 1) * (6 * (s/‖α‖) + 1) := by rw [hdiv]
      _ ≤ ((33/32)*(n:ℝ)*‖α‖ + 2*s + 1) * (6 * (s/‖α‖) + 1) :=
            mul_le_mul_of_nonneg_right h3 hpos
      _ ≤ 30 * (s / ‖α‖) * (1 + (n:ℝ) * ‖α‖) :=
            Count.count_arith_small ha_pos hs hs2

end

end Work.Pert

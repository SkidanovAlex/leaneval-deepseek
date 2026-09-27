import Mathlib
import Submission.Work.Drive.seeleyDefs
import Submission.Work.Drive.trunc_sqrt_contDiff
import Submission.Work.Drive.flat_jets_bound

/-!
# Flat bounds for the Seeley descent `R N = sqrtDesc (S N)`

Let `F : X × ℝ → E` be `C^∞` and even in its second variable, and let
`S N (x,t) = F (x,t) - T N (x,t²)` be the Taylor remainder of `F` in the second variable
(`Work.Drive.seeleyRemainder`), so that `S N` is flat to order `2N+2` along `t = 0`.  Its descent
`R N = Work.Drive.seeleyDescent F N = sqrtDesc (S N)` is `C^N`, and the present file proves the
flat jet bounds

`‖𝔡^k (R N) (x,σ)‖ ≤ C * σ ^ (N + 1 - k)`   (`k ≤ N`, `‖x - x₀‖ < r`, `0 < σ < 1`)

of `Work.Drive.seeleyDescent_bounds`.

The proof has two parts.

* Near the axis `σ = 0`, the flatness hypothesis of `S N` gives the sharp bound with exponent
  `2N+2-2k` for `√σ ^ (2N+2-2k) = σ ^ (N+1-k)` (`Work.Drive.open_jet_bound`); the radius and
  constant obtained for the individual `k ≤ N` are merged with `Finset.range (N+1)` and the
  standard `1/x` trick.
* On the compact piece `σ ∈ [r,1]` the jet function is continuous (`Work.Drive.seeleyDescent_contDiff`
  together with `ContDiff.continuous_iteratedFDeriv`), so a finite subcover of `[r,1]` by
  neighbourhoods on which it is bounded, combined with the elementary lemma
  `Work.Drive.continuous_local_bound` below, bounds it uniformly in `x` near `x₀`; rescaling by
  `r ^ (-(N+1))` gives the required exponent.
-/

namespace Work.Drive

open scoped ContDiff Topology

/-- **Local boundedness of a continuous function on `{x₀} × [a,b]`, uniformly in `x`.**

For a continuous real-valued function `g` on `X × ℝ` and real numbers `a ≤ b`, the function `g` is
bounded on `{x : ‖x - x₀‖ < r} × [a,b]` for some `r > 0`.

The point is that `X` is an arbitrary normed space, so the set `{x₀} × [a,b]` is compact but its
neighbourhoods are not: continuity at each `(x₀,s)`, `s ∈ [a,b]`, gives a neighbourhood of
`(x₀,s)`, and a finite subcover of the compact interval `[a,b]` shrinks these to a common
`x`-radius. -/
theorem continuous_local_bound {X : Type*} [NormedAddCommGroup X] {g : X × ℝ → ℝ}
    (hg : Continuous g) (x₀ : X) {a b : ℝ} (hab : a ≤ b) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : X, ∀ σ : ℝ, ‖x - x₀‖ < r → σ ∈ Set.Icc a b → g (x, σ) ≤ C := by
  classical
  -- A radius and a bound at every centre `s ∈ ℝ`, from continuity.
  have key : ∀ s : ℝ, ∃ δ : ℝ, 0 < δ ∧
      ∀ y : X × ℝ, ‖y - (x₀, s)‖ < δ → g y ≤ |g (x₀, s)| + 1 := by
    intro s
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuous_iff.mp hg) (x₀, s) 1 (by norm_num)
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    have h1 := hδ y (by rwa [dist_eq_norm])
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    linarith [le_abs_self (g (x₀, s))]
  choose δ hδpos hδbound using key
  -- The balls of these radii cover the compact interval `[a,b]`.
  have hcover : Set.Icc a b ⊆ ⋃ s : ℝ, Metric.ball s (δ s) := by
    intro σ hσ
    exact Set.mem_iUnion.mpr ⟨σ, by rw [Metric.mem_ball, dist_self]; exact hδpos σ⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover (fun s : ℝ => Metric.ball s (δ s))
    (fun s => Metric.isOpen_ball) hcover
  have hne : t.Nonempty := by
    obtain ⟨σ, hσ⟩ : (Set.Icc a b).Nonempty := ⟨a, Set.left_mem_Icc.mpr hab⟩
    obtain ⟨s, hst, -⟩ := Set.mem_iUnion₂.mp (ht hσ)
    exact ⟨s, hst⟩
  have hSpos : 0 < ∑ s ∈ t, (δ s / 2)⁻¹ :=
    Finset.sum_pos (s := t) (f := fun s => (δ s / 2)⁻¹)
      (fun s _ => inv_pos.mpr (by linarith [hδpos s])) hne
  -- The `x`-radius is the harmonic mean of the radii of the subcover.
  refine ⟨min 1 (∑ s ∈ t, (δ s / 2)⁻¹)⁻¹, lt_min one_pos (inv_pos.mpr hSpos),
    ∑ s ∈ t, (|g (x₀, s)| + 1),
    Finset.sum_nonneg (s := t) (f := fun s => (|g (x₀, s)| + 1)) (fun s _ => by positivity), ?_⟩
  intro x σ hx hσ
  obtain ⟨s, hst, hsσ⟩ := Set.mem_iUnion₂.mp (ht hσ)
  rw [Metric.mem_ball, Real.dist_eq] at hsσ
  have hsle : (∑ s' ∈ t, (δ s' / 2)⁻¹)⁻¹ ≤ δ s / 2 := by
    have hdpos : 0 < δ s / 2 := by linarith [hδpos s]
    have h1 : (δ s / 2)⁻¹ ≤ ∑ s' ∈ t, (δ s' / 2)⁻¹ :=
      Finset.single_le_sum (f := fun s' => (δ s' / 2)⁻¹)
        (fun s' _ => le_of_lt (inv_pos.mpr (by linarith [hδpos s']))) hst
    rw [inv_le_iff_one_le_mul₀ hSpos]
    calc (1 : ℝ) = (δ s / 2) * (δ s / 2)⁻¹ := (mul_inv_cancel₀ (ne_of_gt hdpos)).symm
      _ ≤ (δ s / 2) * (∑ s' ∈ t, (δ s' / 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hdpos)
  have hrle : min 1 (∑ s ∈ t, (δ s / 2)⁻¹)⁻¹ ≤ δ s / 2 :=
    le_trans (min_le_right 1 _) hsle
  have hnorm : ‖(x, σ) - ((x₀, s) : X × ℝ)‖ < δ s := by
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub]
    refine max_lt ?_ ?_
    · exact lt_of_lt_of_le (lt_of_lt_of_le hx hrle) (by linarith [hδpos s])
    · exact lt_of_lt_of_le hsσ (by linarith [hδpos s])
  calc g (x, σ) ≤ |g (x₀, s)| + 1 := hδbound s (x, σ) hnorm
    _ ≤ ∑ s' ∈ t, (|g (x₀, s')| + 1) :=
        Finset.single_le_sum (f := fun s' => (|g (x₀, s')| + 1)) (fun s' _ => by positivity) hst

/-- Flat bounds for the descent `R N = sqrtDesc (S N)`, where `S N (x,t) = F (x,t) - T N (x,t²)` is the Taylor remainder of a smooth even `F`.  Route: `Work.Drive.seeleyRemainder_flat` and `Work.Drive.seeleyRemainder_bounds` (already available in `seeleyDefs.lean`) give the jet bounds of `S N`; `Work.Drive.open_jet_bound` (with `K = 2N+2`, `m = N`) gives, for `k ≤ N`, a radius `r` and a constant `C` with `‖iteratedFDeriv k (R N) y‖ ≤ C (√y.2)^(2N+2-2k) = C (y.2)^(N+1-k)` for `‖y-(x₀,0)‖ < r`, `y.2 > 0`; the remaining compact piece `σ ∈ [r,1]` is handled by continuity of the jet function (available from `Work.Drive.seeleyDescent_contDiff`) at the points `(x₀,σ)` together with compactness of `[r,1]`, enlarging `C` by the factor `r^(-(N+1))`. -/
theorem seeleyDescent_bounds {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t)) (N : ℕ) :
    ∀ x₀ : X, ∃ C r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x σ, ‖x - x₀‖ < r → 0 < σ → σ < 1 → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Work.Drive.seeleyDescent F N) (x, σ)‖ ≤ C * σ ^ (N + 1 - k) := by
  intro x₀
  classical
  -- Step 1: for each `k ≤ N`, the flat bound of `S N` gives the sharp bound near the axis.
  have hkey : ∀ k : ℕ, ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ (k ≤ N →
      ∀ y : X × ℝ, ‖y - (x₀, 0)‖ < r → 0 < y.2 →
        ‖iteratedFDeriv ℝ k (seeleyDescent F N) y‖ ≤
          C * (Real.sqrt y.2) ^ (2 * N + 2 - 2 * k)) := by
    intro k
    by_cases hk : k ≤ N
    · obtain ⟨r, hr, C, hC, hb⟩ := open_jet_bound (X := X) (E := E) (K := 2 * N + 2) (m := N)
        (by omega) (seeleyRemainder_bounds hF heven N)
        (fun z _ => (seeleyRemainder_contDiff hF N).contDiffAt) hk (x₀, 0) rfl
      exact ⟨r, C, hr, hC, fun _ => hb⟩
    · exact ⟨1, 0, one_pos, le_refl 0, fun hk' => absurd hk' hk⟩
  choose rk Ck hspec using hkey
  have hrk : ∀ k, 0 < rk k := fun k => (hspec k).1
  have hCk : ∀ k, 0 ≤ Ck k := fun k => (hspec k).2.1
  have hbk : ∀ k, k ≤ N → ∀ y : X × ℝ, ‖y - (x₀, 0)‖ < rk k → 0 < y.2 →
      ‖iteratedFDeriv ℝ k (seeleyDescent F N) y‖ ≤
        Ck k * (Real.sqrt y.2) ^ (2 * N + 2 - 2 * k) := fun k => (hspec k).2.2
  -- Step 2: a common radius for all `k ≤ N`.
  have hsumpos : 0 < ∑ k ∈ Finset.range (N + 1), (rk k)⁻¹ :=
    Finset.sum_pos (s := Finset.range (N + 1)) (f := fun k => (rk k)⁻¹)
      (fun k _ => inv_pos.mpr (hrk k)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  let r1 : ℝ := min 1 (∑ k ∈ Finset.range (N + 1), (rk k)⁻¹)⁻¹
  have hr1pos : 0 < r1 := lt_min one_pos (inv_pos.mpr hsumpos)
  have hr1le1 : r1 ≤ 1 := min_le_left 1 _
  have hr1_le_rk : ∀ k ∈ Finset.range (N + 1), r1 ≤ rk k := by
    intro k hk
    have hle : (rk k)⁻¹ ≤ ∑ j ∈ Finset.range (N + 1), (rk j)⁻¹ :=
      Finset.single_le_sum (f := fun j => (rk j)⁻¹)
        (fun j _ => le_of_lt (inv_pos.mpr (hrk j))) hk
    have h2 : (∑ j ∈ Finset.range (N + 1), (rk j)⁻¹)⁻¹ ≤ rk k := by
      rw [inv_le_iff_one_le_mul₀ hsumpos]
      calc (1 : ℝ) = (rk k) * (rk k)⁻¹ := (mul_inv_cancel₀ (ne_of_gt (hrk k))).symm
        _ ≤ (rk k) * (∑ j ∈ Finset.range (N + 1), (rk j)⁻¹) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt (hrk k))
    exact le_trans (min_le_right 1 _) h2
  -- Step 3: a common constant for the axis part.
  let C0 : ℝ := ∑ k ∈ Finset.range (N + 1), Ck k
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg (f := fun k => Ck k) (fun k _ => hCk k)
  have hC0_le : ∀ k ∈ Finset.range (N + 1), Ck k ≤ C0 :=
    fun k hk => Finset.single_le_sum (f := fun k => Ck k) (fun k _ => hCk k) hk
  -- Step 4: the compact piece `σ ∈ [r1, 1]`, via continuity of the jet function.
  let G : X × ℝ → ℝ := fun y => ∑ k ∈ Finset.range (N + 1),
    ‖iteratedFDeriv ℝ k (seeleyDescent F N) y‖
  have hGcont : Continuous G := by
    refine continuous_finsetSum _ ?_
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hm : (↑k : WithTop ℕ∞) ≤ ((N : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hkN
    exact ((seeleyDescent_contDiff hF heven N).continuous_iteratedFDeriv hm).norm
  have hG_le : ∀ (y : X × ℝ) (k : ℕ), k ∈ Finset.range (N + 1) →
      ‖iteratedFDeriv ℝ k (seeleyDescent F N) y‖ ≤ G y := by
    intro y k hk
    exact Finset.single_le_sum
      (f := fun k => ‖iteratedFDeriv ℝ k (seeleyDescent F N) y‖)
      (fun k _ => norm_nonneg _) hk
  obtain ⟨rC, hrC, CC, hCCnn, hCCbound⟩ := continuous_local_bound hGcont x₀ (a := r1) (b := 1) hr1le1
  -- Step 5: assemble.  The factor `r1 ^ (-(N+1))` converts the `σ`-uniform bound into the
  -- required exponent.
  refine ⟨max C0 (CC * (r1 ^ (N + 1))⁻¹), min r1 rC, lt_min hr1pos hrC,
    le_trans (min_le_left _ _) hr1le1, ?_⟩
  intro x σ hx hσpos hσlt k hk
  have hkrange : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  have hσ0 : (0 : ℝ) ≤ σ := le_of_lt hσpos
  have hσ1 : σ ≤ 1 := le_of_lt hσlt
  rcases lt_or_ge σ r1 with hcase | hcase
  · -- near the axis: the sharp flat bound
    have hdist : ‖(x, σ) - ((x₀, 0) : X × ℝ)‖ < rk k := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
      refine max_lt ?_ ?_
      · exact lt_of_lt_of_le (lt_of_lt_of_le hx (min_le_left _ _)) (hr1_le_rk k hkrange)
      · rw [Real.norm_eq_abs, abs_of_pos hσpos]
        exact lt_of_lt_of_le hcase (hr1_le_rk k hkrange)
    have hb := hbk k hk (x, σ) hdist hσpos
    have hexp : (Real.sqrt σ) ^ (2 * N + 2 - 2 * k) = σ ^ (N + 1 - k) := by
      have h : 2 * N + 2 - 2 * k = 2 * (N + 1 - k) := by omega
      rw [h, pow_mul, Real.sq_sqrt hσ0]
    rw [hexp] at hb
    calc ‖iteratedFDeriv ℝ k (seeleyDescent F N) (x, σ)‖
        ≤ Ck k * σ ^ (N + 1 - k) := hb
      _ ≤ C0 * σ ^ (N + 1 - k) :=
          mul_le_mul_of_nonneg_right (hC0_le k hkrange) (pow_nonneg hσ0 _)
      _ ≤ max C0 (CC * (r1 ^ (N + 1))⁻¹) * σ ^ (N + 1 - k) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ0 _)
  · -- bounded away from the axis: the continuity bound, rescaled
    have hmem : σ ∈ Set.Icc r1 1 := ⟨hcase, hσ1⟩
    have hxr : ‖x - x₀‖ < rC := lt_of_lt_of_le hx (min_le_right _ _)
    have h1 : ‖iteratedFDeriv ℝ k (seeleyDescent F N) (x, σ)‖ ≤ CC :=
      le_trans (hG_le (x, σ) k hkrange) (hCCbound x σ hxr hmem)
    have hr1pow : 0 < r1 ^ (N + 1) := pow_pos hr1pos _
    have hpow : r1 ^ (N + 1) ≤ σ ^ (N + 1 - k) := by
      have h2 : r1 ^ (N + 1 - k) ≤ σ ^ (N + 1 - k) :=
        pow_le_pow_left₀ (le_of_lt hr1pos) hcase _
      have h3 : r1 ^ (N + 1) ≤ r1 ^ (N + 1 - k) :=
        pow_le_pow_of_le_one (le_of_lt hr1pos) hr1le1 (Nat.sub_le _ _)
      exact le_trans h3 h2
    have hD : CC ≤ CC * (r1 ^ (N + 1))⁻¹ * σ ^ (N + 1 - k) := by
      have h4 : CC * (r1 ^ (N + 1))⁻¹ * r1 ^ (N + 1) = CC := by
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hr1pow), mul_one]
      calc CC = CC * (r1 ^ (N + 1))⁻¹ * r1 ^ (N + 1) := h4.symm
        _ ≤ CC * (r1 ^ (N + 1))⁻¹ * σ ^ (N + 1 - k) :=
            mul_le_mul_of_nonneg_left hpow
              (mul_nonneg hCCnn (le_of_lt (inv_pos.mpr hr1pow)))
    calc ‖iteratedFDeriv ℝ k (seeleyDescent F N) (x, σ)‖ ≤ CC := h1
      _ ≤ CC * (r1 ^ (N + 1))⁻¹ * σ ^ (N + 1 - k) := hD
      _ ≤ max C0 (CC * (r1 ^ (N + 1))⁻¹) * σ ^ (N + 1 - k) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hσ0 _)

end Work.Drive

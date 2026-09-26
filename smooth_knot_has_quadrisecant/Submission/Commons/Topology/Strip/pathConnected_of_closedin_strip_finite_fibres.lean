import Mathlib
import Submission.Commons.Topology.Circle.locallyPathConnectedSpace_of_finite_meridians

/-!
# A closed periodic continuum in a strip is path connected

Let `d > 0` and let `F ⊆ ℝ × (0,1)` be closed *in the strip*, i.e. `F ∪ {q | q.2 ≤ 0 ∨ 1 ≤ q.2}`
is closed in `ℝ × ℝ`; suppose moreover that `F` is invariant under the translation by `(d, 0)`,
that `F` is connected and that all its vertical fibres are finite.  Then `F` is path connected.

The proof passes to the quotient of the plane by the translation by `(d, 0)`, i.e. to the image of
`F` in the cylinder `Circle × ℝ`.  The closure `K` of that image is compact and connected with
finite meridians, so (by a lemma of the shared commons) it is locally path connected.  The
projection `F → F/ℤ` is a covering map (the sheets near a point are the small balls around the
translates of that point), so `F` inherits local path connectedness, and a connected locally path
connected space is path connected.
-/

open Set Metric Filter
open scoped _root_.Topology

set_option linter.style.haveILetI false

namespace Commons.Topology.Strip

/-- The quotient map from the plane onto the cylinder of circumference `d`, i.e. the orbit map of
the translation by `(d, 0)`. -/
noncomputable def toCyl (d : ℝ) (q : ℝ × ℝ) : Circle × ℝ := (Real.fourierChar (q.1 / d), q.2)

lemma continuous_toCyl (d : ℝ) : Continuous (toCyl d) := by
  unfold toCyl
  exact (Real.continuous_fourierChar.comp (continuous_fst.div_const d)).prodMk continuous_snd

lemma fourierChar_one : Real.fourierChar 1 = 1 := by
  apply Circle.ext
  rw [Real.fourierChar_apply, Circle.coe_one]
  rw [show (↑(2 * Real.pi * (1:ℝ)) : ℂ) * Complex.I = 2 * ↑Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma fourierChar_int (n : ℤ) : Real.fourierChar (n:ℝ) = 1 := by
  apply Circle.ext
  rw [Real.fourierChar_apply, Circle.coe_one]
  rw [show (↑(2 * Real.pi * (n:ℝ)) : ℂ) * Complex.I = (n:ℂ) * (2 * ↑Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma fourierChar_add_int {x : ℝ} (n : ℤ) :
    Real.fourierChar (x + (n:ℝ)) = Real.fourierChar x := by
  rw [AddChar.map_add_eq_mul, fourierChar_int n, mul_one]

lemma toCyl_add_zsmul (d : ℝ) (hd : d ≠ 0) (m : ℤ) (q : ℝ × ℝ) :
    toCyl d (q.1 + (m:ℝ) * d, q.2) = toCyl d q := by
  have harg : (q.1 + (m:ℝ) * d) / d = q.1 / d + (m:ℝ) := by
    rw [add_div, mul_div_cancel_right₀ (m:ℝ) hd]
  unfold toCyl
  rw [harg, fourierChar_add_int m]

lemma toCyl_periodic (d : ℝ) (hd : d ≠ 0) (q : ℝ × ℝ) :
    toCyl d (q.1 + d, q.2) = toCyl d q := by
  have h := toCyl_add_zsmul d hd (1:ℤ) q
  simpa using h

lemma fourierChar_eq_iff {a b : ℝ} :
    Real.fourierChar a = Real.fourierChar b ↔ ∃ n : ℤ, a - b = n := by
  constructor
  · intro h
    have hc : Complex.exp (↑(2 * Real.pi * a) * Complex.I)
        = Complex.exp (↑(2 * Real.pi * b) * Complex.I) := by
      rw [← Real.fourierChar_apply, ← Real.fourierChar_apply]
      exact congrArg Subtype.val h
    have hc' : Complex.exp (↑(2 * Real.pi * a) * Complex.I - ↑(2 * Real.pi * b) * Complex.I) = 1 := by
      rw [Complex.exp_sub, hc, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hc'
    refine ⟨n, ?_⟩
    have h2 : (↑(2 * Real.pi * (a - b)) : ℂ) * Complex.I = (n:ℂ) * (2 * ↑Real.pi * Complex.I) := by
      rw [← hn]; push_cast; ring
    have h3 : (↑(2 * Real.pi * (a - b)) : ℂ) = ↑((n:ℝ) * 2 * Real.pi) := by
      rw [show (n:ℂ) * (2 * ↑Real.pi * Complex.I) = (↑((n:ℝ) * 2 * Real.pi) : ℂ) * Complex.I by
        push_cast; ring] at h2
      exact mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : 2 * Real.pi * (a - b) = (n:ℝ) * 2 * Real.pi := Complex.ofReal_inj.mp h3
    exact mul_left_cancel₀ (ne_of_gt Real.two_pi_pos) (by nlinarith [h4])
  · rintro ⟨n, hn⟩
    rw [show a = b + (n:ℝ) by linarith, fourierChar_add_int n]

lemma toCyl_eq_iff {d : ℝ} (hd : d ≠ 0) (q₁ q₂ : ℝ × ℝ) :
    toCyl d q₁ = toCyl d q₂ ↔ q₁.2 = q₂.2 ∧ ∃ n : ℤ, q₁.1 - q₂.1 = (n:ℝ) * d := by
  constructor
  · intro h
    have h1 : q₁.2 = q₂.2 := by simpa [toCyl] using congrArg Prod.snd h
    have h2 : Real.fourierChar (q₁.1 / d) = Real.fourierChar (q₂.1 / d) := by
      simpa [toCyl] using congrArg Prod.fst h
    obtain ⟨n, hn⟩ := fourierChar_eq_iff.mp h2
    refine ⟨h1, n, ?_⟩
    rw [div_sub_div_same, div_eq_iff hd] at hn
    linarith [hn]
  · rintro ⟨h1, n, hn⟩
    unfold toCyl
    rw [h1]
    congr 1
    rw [show q₁.1 / d = q₂.1 / d + (n:ℝ) by field_simp; linarith [hn]]
    exact fourierChar_add_int n

lemma fourierChar_surj (z : Circle) : ∃ x : ℝ, Real.fourierChar x = z := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  refine ⟨t / (2 * Real.pi), ?_⟩
  have hmain : Real.fourierChar (t / (2 * Real.pi)) = Circle.exp t := by
    apply Circle.ext
    rw [Real.fourierChar_apply, Circle.coe_exp]
    congr 1
    push_cast
    field_simp
  rw [hmain, ht]

/-- An integer translate of `x` lies in the window `[φ - d/2, φ + d/2]`. -/
lemma exists_zsmul_sub_mem_Icc {d φ x : ℝ} (hd : 0 < d) :
    ∃ k : ℤ, x - (k:ℝ)*d ∈ Set.Icc (φ - d/2) (φ + d/2) := by
  refine ⟨⌊(x - φ)/d + 1/2⌋, ?_⟩
  have h1 : (x - φ)/d + 1/2 - 1 < ((⌊(x - φ)/d + 1/2⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h2 : ((⌊(x - φ)/d + 1/2⌋ : ℤ) : ℝ) ≤ (x - φ)/d + 1/2 := Int.floor_le _
  have key1 : -(1/2:ℝ) ≤ (x - φ)/d - (⌊(x - φ)/d + 1/2⌋ : ℝ) := by linarith
  have key2 : (x - φ)/d - (⌊(x - φ)/d + 1/2⌋ : ℝ) ≤ 1/2 := by linarith
  have hkd : (x - φ) - (⌊(x - φ)/d + 1/2⌋ : ℤ) * d
      = ((x - φ)/d - (⌊(x - φ)/d + 1/2⌋ : ℤ)) * d := by field_simp
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right key1 hd.le
    rw [← hkd] at this; linarith
  · have := mul_le_mul_of_nonneg_right key2 hd.le
    rw [← hkd] at this; linarith

/-- Membership in `F` is invariant under integer multiples of the period. -/
lemma mem_F_zsmul {d : ℝ} {F : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + d, q.2) ∈ F) (x y : ℝ) (k : ℤ) :
    ((x + (k:ℝ)*d, y) : ℝ × ℝ) ∈ F ↔ (x, y) ∈ F := by
  have hgper : Function.Periodic (fun t : ℝ => ((t, y) : ℝ × ℝ) ∈ F) d := by
    intro t; exact propext (hper (t,y)).symm
  exact Iff.of_eq (hgper.int_mul k x)

/-- Points of the closure of the image of `F` inside the open cylinder come from `F`. -/
lemma mem_toCyl_image_of_mem_closure {d : ℝ} (hd : 0 < d) {F : Set (ℝ × ℝ)}
    (hF : IsClosed (F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}))
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + d, q.2) ∈ F)
    {z : Circle × ℝ} (hz : z ∈ closure (toCyl d '' F)) (hz2 : 0 < z.2 ∧ z.2 < 1) :
    z ∈ toCyl d '' F := by
  rw [Metric.mem_closure_iff] at hz
  have hex : ∀ n : ℕ, ∃ y : Circle × ℝ, y ∈ toCyl d '' F ∧ dist z y < 1/(n+1) :=
    fun n => hz _ (by positivity)
  choose w hwK hwz using hex
  have hwtend : Tendsto w atTop (𝓝 z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
    refine ⟨N, fun n hn => ?_⟩
    have hle : 1/((n:ℝ)+1) ≤ 1/((N:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : N+1 ≤ n+1))
    have hN' : 1/((N:ℝ)+1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      have h2 : 1/ε < (N:ℝ)+1 := by linarith [hN]
      rw [div_lt_iff₀ hε] at h2; linarith [h2]
    have hwz' : dist (w n) z < 1/((n:ℝ)+1) := by rw [dist_comm]; exact hwz n
    linarith [hwz', hle, hN']
  have hqex : ∀ n : ℕ, ∃ q : ℝ × ℝ, q ∈ F ∧ toCyl d q = w n := fun n => hwK n
  choose q hqF hqw using hqex
  have hkey : ∀ n : ℕ, ∃ k : ℤ, (q n).1 - (k:ℝ)*d ∈ Set.Icc (0:ℝ) d := by
    intro n
    obtain ⟨k, hk⟩ := exists_zsmul_sub_mem_Icc (d := d) (φ := d/2) hd (x := (q n).1)
    refine ⟨k, ?_⟩
    have h1 : (d/2 - d/2 : ℝ) = 0 := by ring
    have h2 : (d/2 + d/2 : ℝ) = d := by ring
    rw [h1, h2] at hk
    exact hk
  choose k hk using hkey
  have hxF : ∀ n, (((q n).1 - (k n:ℝ)*d, (q n).2) : ℝ × ℝ) ∈ F := by
    intro n
    refine (mem_F_zsmul hper ((q n).1 - (k n:ℝ)*d) (q n).2 (k n)).mp ?_
    have h1 : (((q n).1 - (k n:ℝ)*d) + (k n:ℝ)*d, (q n).2) = ((q n).1, (q n).2) := by
      congr 1; ring
    rw [h1]; exact hqF n
  obtain ⟨x0, hx0, ψs, hψmono, hψtend⟩ := isCompact_Icc.tendsto_subseq (fun n => hk n)
  have hseq : Tendsto (fun j => (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2) : ℝ × ℝ))
      atTop (𝓝 (x0, z.2)) := by
    refine hψtend.prodMk_nhds ?_
    have heq : (fun j => (q (ψs j)).2) = fun j => (w (ψs j)).2 := by
      funext j; rw [← hqw (ψs j)]; rfl
    rw [heq]
    exact (continuous_snd.tendsto z).comp (hwtend.comp hψmono.tendsto_atTop)
  have hmemF : ((x0, z.2) : ℝ × ℝ) ∈ F := by
    have h1 : ((x0, z.2) : ℝ × ℝ) ∈ F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2} :=
      hF.mem_of_tendsto hseq (Eventually.of_forall fun j => subset_union_left (hxF (ψs j)))
    rcases h1 with h | h
    · exact h
    · exact absurd h (by
        simp only [Set.mem_ofPred_eq, not_or]
        exact ⟨not_le.mpr hz2.1, not_le.mpr hz2.2⟩)
  have htoCyl : toCyl d (x0, z.2) = z := by
    have h1 : Tendsto (fun j => toCyl d (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2)))
        atTop (𝓝 (toCyl d (x0, z.2))) := ((continuous_toCyl d).tendsto _).comp hseq
    have h2 : (fun j => toCyl d (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2)))
        = fun j => w (ψs j) := by
      funext j
      rw [← hqw (ψs j)]
      symm
      show toCyl d ((q (ψs j)).1, (q (ψs j)).2)
        = toCyl d (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2))
      rw [show ((q (ψs j)).1, (q (ψs j)).2)
        = (((q (ψs j)).1 - (k (ψs j):ℝ)*d) + (k (ψs j):ℝ)*d, (q (ψs j)).2) by congr 1; ring]
      exact toCyl_add_zsmul d hd.ne' (k (ψs j)) ((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hwtend.comp hψmono.tendsto_atTop)
  exact ⟨(x0, z.2), hmemF, htoCyl⟩

/-- On a closed ball of radius `< d/4`, the projection to the cylinder is injective. -/
lemma injOn_toCyl_closedBall {d : ℝ} (hd : 0 < d) (p : ℝ × ℝ) {r : ℝ} (hr : 4 * r < d) :
    Set.InjOn (toCyl d) (Metric.closedBall p (2 * r)) := by
  intro q hq q' hq' heq
  have hq2 : q.2 = q'.2 := ((toCyl_eq_iff hd.ne' q q').mp heq).1
  obtain ⟨n, hn⟩ := ((toCyl_eq_iff hd.ne' q q').mp heq).2
  have hdist : dist q q' ≤ 4 * r := by
    have h1 : dist q p ≤ 2 * r := Metric.mem_closedBall.mp hq
    have h2 : dist p q' ≤ 2 * r := by rw [dist_comm]; exact Metric.mem_closedBall.mp hq'
    linarith [dist_triangle q p q']
  have h1 : |q.1 - q'.1| ≤ dist q q' := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have h2 : |q.1 - q'.1| = ((|n| : ℤ) : ℝ) * d := by
    rw [hn, abs_mul, abs_of_pos hd, ← Int.cast_abs]
  have h3 : ((|n| : ℤ) : ℝ) < 1 := by
    have h4 : ((|n| : ℤ) : ℝ) * d < d := by rw [← h2]; linarith
    nlinarith [h4, hd]
  have h5 : n = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast h3 : |n| < 1)
  rw [h5] at hn
  simp at hn
  exact Prod.ext (by linarith) hq2

/-- **Localization at a point of `F`.**  If `A` is a neighbourhood of `p ∈ F`, then all points of
the closure of the image of `F` in the cylinder that are close enough to `toCyl p` come from
points of `F ∩ A`.  This is the "evenly covered" property of the periodic set `F` over its image
in the cylinder. -/
lemma exists_ball_inter_subset_toCyl_image {d : ℝ} (hd : 0 < d) {F : Set (ℝ × ℝ)}
    (hF : IsClosed (F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}))
    (hsub : F ⊆ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < 1})
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + d, q.2) ∈ F)
    {p : ℝ × ℝ} (hp : p ∈ F) {A : Set (ℝ × ℝ)} (hA : A ∈ 𝓝 p) :
    ∃ δ > 0, closure (toCyl d '' F) ∩ Metric.ball (toCyl d p) δ ⊆ toCyl d '' (F ∩ A) := by
  by_contra hcon
  have hcon' : ∀ n : ℕ, ∃ w : Circle × ℝ,
      w ∈ closure (toCyl d '' F) ∧ w ∈ Metric.ball (toCyl d p) (1/(n+1)) ∧
        w ∉ toCyl d '' (F ∩ A) := by
    intro n
    by_contra h
    refine hcon ⟨1/(n+1), by positivity, ?_⟩
    rintro w ⟨hwK, hwball⟩
    by_contra hwA
    exact h ⟨w, hwK, hwball, hwA⟩
  choose w hwK hwd hwA using hcon'
  have hp2 : 0 < p.2 ∧ p.2 < 1 := hsub hp
  have hwtend : Tendsto w atTop (𝓝 (toCyl d p)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
    refine ⟨N, fun n hn => ?_⟩
    have hle : 1/((n:ℝ)+1) ≤ 1/((N:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : N+1 ≤ n+1))
    have hN' : 1/((N:ℝ)+1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      have h2 : 1/ε < (N:ℝ)+1 := by linarith [hN]
      rw [div_lt_iff₀ hε] at h2; linarith [h2]
    have hw := Metric.mem_ball.mp (hwd n)
    linarith [hw, hle, hN']
  have hev : ∀ᶠ n : ℕ in atTop, (w n).2 ∈ Set.Ioo 0 1 :=
    ((continuous_snd.tendsto (toCyl d p)).comp hwtend).eventually
      (isOpen_Ioo.mem_nhds ⟨hp2.1, hp2.2⟩)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set u : ℕ → Circle × ℝ := fun n => w (n + N) with hu
  have huK : ∀ n, u n ∈ closure (toCyl d '' F) := fun n => hwK (n + N)
  have hu2 : ∀ n, (u n).2 ∈ Set.Ioo 0 1 := fun n => hN (n + N) (by omega)
  have hutend : Tendsto u atTop (𝓝 (toCyl d p)) := hwtend.comp (tendsto_add_atTop_nat N)
  have hqex : ∀ n : ℕ, ∃ q : ℝ × ℝ, q ∈ F ∧ toCyl d q = u n :=
    fun n => mem_toCyl_image_of_mem_closure hd hF hper (huK n) (hu2 n)
  choose q hqF hqu using hqex
  have hkey : ∀ n : ℕ, ∃ k : ℤ, (q n).1 - (k:ℝ)*d ∈ Set.Icc (0:ℝ) d := by
    intro n
    obtain ⟨k, hk⟩ := exists_zsmul_sub_mem_Icc (d := d) (φ := d/2) hd (x := (q n).1)
    refine ⟨k, ?_⟩
    have h1 : (d/2 - d/2 : ℝ) = 0 := by ring
    have h2 : (d/2 + d/2 : ℝ) = d := by ring
    rw [h1, h2] at hk
    exact hk
  choose k hk using hkey
  have hzF : ∀ n, (((q n).1 - (k n:ℝ)*d, (q n).2) : ℝ × ℝ) ∈ F := by
    intro n
    refine (mem_F_zsmul hper ((q n).1 - (k n:ℝ)*d) (q n).2 (k n)).mp ?_
    have h1 : (((q n).1 - (k n:ℝ)*d) + (k n:ℝ)*d, (q n).2) = ((q n).1, (q n).2) := by
      congr 1; ring
    rw [h1]; exact hqF n
  obtain ⟨x0, hx0, ψs, hψmono, hψtend⟩ := isCompact_Icc.tendsto_subseq (fun n => hk n)
  have hq2tend : Tendsto (fun j => (q (ψs j)).2) atTop (𝓝 p.2) := by
    have heq : (fun j => (q (ψs j)).2) = fun j => (u (ψs j)).2 := by
      funext j; rw [← hqu (ψs j)]; rfl
    rw [heq]
    exact (continuous_snd.tendsto (toCyl d p)).comp (hutend.comp hψmono.tendsto_atTop)
  have hseq : Tendsto (fun j => (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2) : ℝ × ℝ))
      atTop (𝓝 (x0, p.2)) := hψtend.prodMk_nhds hq2tend
  have hlimF : ((x0, p.2) : ℝ × ℝ) ∈ F := by
    have h1 : ((x0, p.2) : ℝ × ℝ) ∈ F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2} :=
      hF.mem_of_tendsto hseq (Eventually.of_forall fun j => subset_union_left (hzF (ψs j)))
    rcases h1 with h | h
    · exact h
    · exact absurd h (by
        simp only [Set.mem_ofPred_eq, not_or]
        exact ⟨not_le.mpr hp2.1, not_le.mpr hp2.2⟩)
  have htoCyl : toCyl d (x0, p.2) = toCyl d p := by
    have h1 : Tendsto (fun j => toCyl d (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2)))
        atTop (𝓝 (toCyl d (x0, p.2))) := ((continuous_toCyl d).tendsto _).comp hseq
    have h2 : (fun j => toCyl d (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2)))
        = fun j => u (ψs j) := by
      funext j
      rw [← hqu (ψs j)]
      symm
      show toCyl d ((q (ψs j)).1, (q (ψs j)).2)
        = toCyl d (((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2))
      rw [show ((q (ψs j)).1, (q (ψs j)).2)
        = (((q (ψs j)).1 - (k (ψs j):ℝ)*d) + (k (ψs j):ℝ)*d, (q (ψs j)).2) by congr 1; ring]
      exact toCyl_add_zsmul d hd.ne' (k (ψs j)) ((q (ψs j)).1 - (k (ψs j):ℝ)*d, (q (ψs j)).2)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hutend.comp hψmono.tendsto_atTop)
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, x0 - p.1 = (n0:ℝ)*d :=
    ((toCyl_eq_iff hd.ne' (x0, p.2) p).mp htoCyl).2
  have hshift : Tendsto
      (fun j => (((q (ψs j)).1 - (k (ψs j):ℝ)*d - (n0:ℝ)*d, (q (ψs j)).2) : ℝ × ℝ))
      atTop (𝓝 p) := by
    have h1 : Tendsto (fun j => (q (ψs j)).1 - (k (ψs j):ℝ)*d - (n0:ℝ)*d)
        atTop (𝓝 (x0 - (n0:ℝ)*d)) := hψtend.sub_const _
    have h2 : p = (x0 - (n0:ℝ)*d, p.2) := by
      refine Prod.ext ?_ rfl
      linarith [hn0]
    rw [h2]
    exact h1.prodMk_nhds hq2tend
  have hshiftF : ∀ j,
      (((q (ψs j)).1 - (k (ψs j):ℝ)*d - (n0:ℝ)*d, (q (ψs j)).2) : ℝ × ℝ) ∈ F := by
    intro j
    refine (mem_F_zsmul hper ((q (ψs j)).1 - (k (ψs j):ℝ)*d - (n0:ℝ)*d) (q (ψs j)).2 n0).mp ?_
    have h1 : (((q (ψs j)).1 - (k (ψs j):ℝ)*d - (n0:ℝ)*d) + (n0:ℝ)*d, (q (ψs j)).2)
        = (((q (ψs j)).1 - (k (ψs j):ℝ)*d), (q (ψs j)).2) := by congr 1; ring
    rw [h1]; exact hzF (ψs j)
  obtain ⟨N', hN'⟩ := eventually_atTop.mp (hshift.eventually hA)
  have hAN' : (((q (ψs N')).1 - (k (ψs N'):ℝ)*d - (n0:ℝ)*d, (q (ψs N')).2) : ℝ × ℝ) ∈ A :=
    hN' N' le_rfl
  have hmem : u (ψs N') ∈ toCyl d '' (F ∩ A) := by
    set W : ℝ × ℝ := ((q (ψs N')).1 - (k (ψs N'):ℝ)*d - (n0:ℝ)*d, (q (ψs N')).2) with hW
    have hWF : W ∈ F := by simpa [hW] using hshiftF N'
    have hWA : W ∈ A := by simpa [hW] using hAN'
    refine ⟨W, ⟨hWF, hWA⟩, ?_⟩
    rw [← hqu (ψs N')]
    have hqeq : (q (ψs N')) = (W.1 + ((k (ψs N') + n0):ℤ)*d, W.2) := by
      rw [hW]
      refine Prod.ext ?_ rfl
      push_cast
      ring
    rw [hqeq]
    exact (toCyl_add_zsmul d hd.ne' (k (ψs N') + n0) W).symm
  exact hwA (ψs N' + N) (by simpa [hu] using hmem)

/-- The meridians of the image of `F` in the cylinder are finite. -/
lemma finite_toCyl_image_inter_meridian {d : ℝ} (hd : 0 < d) {F : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + d, q.2) ∈ F)
    (hfin : ∀ x : ℝ, (F ∩ {q : ℝ × ℝ | q.1 = x}).Finite) (z : Circle) :
    (toCyl d '' F ∩ {q : Circle × ℝ | q.1 = z}).Finite := by
  obtain ⟨t, ht⟩ := fourierChar_surj z
  set x₀ : ℝ := d * t with hx₀
  have hx₀' : Real.fourierChar (x₀ / d) = z := by
    rw [hx₀, mul_div_cancel_left₀ t hd.ne']
    exact ht
  refine ((hfin x₀).image (toCyl d)).subset ?_
  rintro w ⟨⟨q, hqF, rfl⟩, hwz⟩
  have h1 : Real.fourierChar (q.1 / d) = Real.fourierChar (x₀ / d) := by
    rw [hx₀']
    simpa [toCyl] using hwz
  obtain ⟨n, hn⟩ := fourierChar_eq_iff.mp h1
  have hq1 : q.1 = x₀ + (n:ℝ)*d := by
    rw [div_sub_div_same, div_eq_iff hd.ne'] at hn
    linarith [hn]
  refine ⟨(x₀, q.2), ⟨?_, rfl⟩, ?_⟩
  · refine (mem_F_zsmul hper x₀ q.2 n).mp ?_
    have hq : (x₀ + (n:ℝ)*d, q.2) = q := Prod.ext hq1.symm rfl
    rw [hq]; exact hqF
  · show toCyl d (x₀, q.2) = toCyl d q
    rw [show q = ((x₀, q.2).1 + (n:ℝ)*d, (x₀, q.2).2) from Prod.ext hq1 rfl]
    exact (toCyl_add_zsmul d hd.ne' n (x₀, q.2)).symm

/-- `toCyl d`, restricted to the points of `F` lying in a closed ball. -/
noncomputable def toCylOn (d : ℝ) (F : Set (ℝ × ℝ)) (p : ℝ × ℝ) (r : ℝ) :
    ↥(F ∩ Metric.closedBall p r) → Circle × ℝ := fun q => toCyl d (q : ℝ × ℝ)

lemma continuous_toCylOn (d : ℝ) (F : Set (ℝ × ℝ)) (p : ℝ × ℝ) (r : ℝ) :
    Continuous (toCylOn d F p r) :=
  (continuous_toCyl d).comp continuous_subtype_val

lemma range_toCylOn (d : ℝ) (F : Set (ℝ × ℝ)) (p : ℝ × ℝ) (r : ℝ) :
    Set.range (toCylOn d F p r) = toCyl d '' (F ∩ Metric.closedBall p r) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩

/-- **Local path connectedness of `F`.**  If `K` is the closure of the image of `F` in the
cylinder and is locally path connected, then every point of `F` has arbitrarily small path
connected neighbourhoods in `F`. -/
lemma exists_pathConnected_nhds_of_mem {d : ℝ} (hd : 0 < d) {F : Set (ℝ × ℝ)}
    (hF : IsClosed (F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}))
    (hsub : F ⊆ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < 1})
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + d, q.2) ∈ F)
    {K : Set (Circle × ℝ)} (hKeq : K = closure (toCyl d '' F))
    [LocallyPathConnectedSpace ↥K] {p : ℝ × ℝ} (hp : p ∈ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set (ℝ × ℝ), IsPathConnected W ∧ p ∈ W ∧ W ⊆ F ∧ W ⊆ Metric.ball p ε ∧
      ∃ δ > 0, F ∩ Metric.ball p δ ⊆ W := by
  classical
  have hp2 : 0 < p.2 ∧ p.2 < 1 := hsub hp
  set r : ℝ := min (min (d/4) (ε/2)) (min (p.2/2) ((1 - p.2)/2)) / 2 with hr
  have hminpos : 0 < min (min (d/4) (ε/2)) (min (p.2/2) ((1 - p.2)/2)) :=
    lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by linarith [hp2.1]) (by linarith [hp2.2]))
  have hrpos : 0 < r := by rw [hr]; linarith
  have hr_d : r ≤ d / 8 := by
    rw [hr]
    have h : min (min (d/4) (ε/2)) (min (p.2/2) ((1 - p.2)/2)) ≤ d/4 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr_e : r ≤ ε / 4 := by
    rw [hr]
    have h : min (min (d/4) (ε/2)) (min (p.2/2) ((1 - p.2)/2)) ≤ ε/2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hr_y : r ≤ p.2 / 4 := by
    rw [hr]
    have h : min (min (d/4) (ε/2)) (min (p.2/2) ((1 - p.2)/2)) ≤ p.2/2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hr_1y : r ≤ (1 - p.2) / 4 := by
    rw [hr]
    have h : min (min (d/4) (ε/2)) (min (p.2/2) ((1 - p.2)/2)) ≤ (1 - p.2)/2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have h4r : 4 * r < d := by linarith
  have h2r_eps : 2 * r < ε := by linarith
  have h2r_y : 2 * r < p.2 := by linarith
  have h2r_1y : 2 * r < 1 - p.2 := by linarith
  have hBstrip : Metric.closedBall p (2*r) ⊆ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < 1} := by
    intro q hq
    have hqd : dist q p ≤ 2*r := Metric.mem_closedBall.mp hq
    have h2 : |q.2 - p.2| ≤ dist q p := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    have h3 : |q.2 - p.2| < p.2 := by linarith
    have h4 : |q.2 - p.2| < 1 - p.2 := by linarith
    obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
    obtain ⟨h4a, h4b⟩ := abs_lt.mp h4
    exact ⟨by linarith, by linarith⟩
  have hDeq : F ∩ Metric.closedBall p (2*r)
      = (F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}) ∩ Metric.closedBall p (2*r) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with h1 | h1
      · exact ⟨h1, h2⟩
      · exfalso
        rcases h1 with h1 | h1
        · exact absurd (hBstrip h2).1 (not_lt.mpr h1)
        · exact absurd (hBstrip h2).2 (not_lt.mpr h1)
  have hDclosed : IsClosed (F ∩ Metric.closedBall p (2*r)) := by
    rw [hDeq]; exact hF.inter Metric.isClosed_closedBall
  have hDc : IsCompact (F ∩ Metric.closedBall p (2*r)) :=
    (isCompact_closedBall p (2*r)).of_isClosed_subset hDclosed inter_subset_right
  haveI : CompactSpace ↥(F ∩ Metric.closedBall p (2*r)) := isCompact_iff_compactSpace.mp hDc
  have hinj : Set.InjOn (toCyl d) (Metric.closedBall p (2*r)) := injOn_toCyl_closedBall hd p h4r
  have hInj : Function.Injective (toCylOn d F p (2*r)) := by
    intro a b hab
    refine Subtype.ext (hinj a.2.2 b.2.2 ?_)
    exact hab
  have hg : Topology.IsClosedEmbedding (toCylOn d F p (2*r)) :=
    Continuous.isClosedEmbedding (continuous_toCylOn d F p (2*r)) hInj
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_ball_inter_subset_toCyl_image hd hF hsub hper hp
    (A := Metric.closedBall p (2*r)) (Metric.closedBall_mem_nhds p (by linarith))
  have hδ₀' : K ∩ Metric.ball (toCyl d p) δ₀ ⊆ toCyl d '' (F ∩ Metric.closedBall p (2*r)) := by
    rw [hKeq]; exact hδ₀
  have hkK : toCyl d p ∈ K := by
    rw [hKeq]; exact subset_closure ⟨p, hp, rfl⟩
  have hnh : Subtype.val ⁻¹' (Metric.ball (toCyl d p) δ₀) ∈ 𝓝 (⟨toCyl d p, hkK⟩ : ↥K) := by
    refine Metric.mem_nhds_iff.mpr ⟨δ₀, hδ₀pos, fun z hz => ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball]
    rwa [Metric.mem_ball, Subtype.dist_eq] at hz
  obtain ⟨s, ⟨hsnh, hspc⟩, hssub⟩ :=
    (LocallyPathConnectedSpace.path_connected_basis (⟨toCyl d p, hkK⟩ : ↥K)).mem_iff.mp hnh
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.mem_nhds_iff.mp hsnh
  have hks : (⟨toCyl d p, hkK⟩ : ↥K) ∈ s := hε₁sub (Metric.mem_ball_self hε₁pos)
  have hCpc : IsPathConnected (Subtype.val '' s) := hspc.image continuous_subtype_val
  have hCball : Subtype.val '' s ⊆ Metric.ball (toCyl d p) δ₀ := by
    rintro w ⟨z, hz, rfl⟩
    simpa using hssub hz
  have hCloc : K ∩ Metric.ball (toCyl d p) ε₁ ⊆ Subtype.val '' s := by
    intro w hw
    refine ⟨⟨w, hw.1⟩, hε₁sub ?_, rfl⟩
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact hw.2
  have hCrange : Subtype.val '' s ⊆ Set.range (toCylOn d F p (2*r)) := by
    rintro w ⟨z, hz, rfl⟩
    rw [range_toCylOn]
    exact hδ₀' ⟨z.2, hCball ⟨z, hz, rfl⟩⟩
  have hpre_pc : IsPathConnected ((toCylOn d F p (2*r)) ⁻¹' (Subtype.val '' s)) := by
    rw [isPathConnected_iff]
    refine ⟨⟨⟨p, hp, Metric.mem_closedBall_self (by linarith)⟩, ?_⟩, ?_⟩
    · show toCyl d p ∈ Subtype.val '' s
      exact ⟨_, hks, rfl⟩
    · intro x hx y hy
      have hxy : JoinedIn (Subtype.val '' s) (toCylOn d F p (2*r) x) (toCylOn d F p (2*r) y) :=
        hCpc.joinedIn _ hx _ hy
      have hiff := hg.isEmbedding.isInducing.joinedIn_image (f := toCylOn d F p (2*r)) hx hy
      rw [Set.image_preimage_eq_of_subset hCrange] at hiff
      exact hiff.mp hxy
  refine ⟨Subtype.val '' ((toCylOn d F p (2*r)) ⁻¹' (Subtype.val '' s)), ?_, ?_, ?_, ?_, ?_⟩
  · exact hpre_pc.image continuous_subtype_val
  · exact ⟨⟨p, hp, Metric.mem_closedBall_self (by linarith)⟩, ⟨_, hks, rfl⟩, rfl⟩
  · rintro w ⟨z, -, rfl⟩; exact z.2.1
  · rintro w ⟨z, -, rfl⟩
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp z.2.2
    linarith
  · obtain ⟨η, hηpos, hη⟩ : ∃ η > 0, ∀ q : ℝ × ℝ,
        dist q p < η → dist (toCyl d q) (toCyl d p) < ε₁ := by
      have hcont := (continuous_toCyl d).continuousAt (x := p)
      rw [Metric.continuousAt_iff] at hcont
      exact hcont ε₁ hε₁pos
    refine ⟨min η (2*r), lt_min hηpos (by linarith), fun q hq => ?_⟩
    have hqF : q ∈ F := hq.1
    have hqd : dist q p < min η (2*r) := Metric.mem_ball.mp hq.2
    refine ⟨⟨q, hqF, Metric.mem_closedBall.mpr (le_trans (le_of_lt hqd) (min_le_right _ _))⟩,
      ?_, rfl⟩
    show toCyl d q ∈ Subtype.val '' s
    refine hCloc ⟨?_, ?_⟩
    · rw [hKeq]; exact subset_closure ⟨q, hqF, rfl⟩
    · exact hη q (lt_of_lt_of_le hqd (min_le_left _ _))

theorem pathConnected_of_closedin_strip_finite_fibres {d : ℝ} (hd : 0 < d) {F : Set (ℝ × ℝ)}
    (hF : IsClosed (F ∪ {q : ℝ × ℝ | q.2 ≤ 0 ∨ 1 ≤ q.2}))
    (hsub : F ⊆ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < 1})
    (hconn : IsConnected F)
    (hper : ∀ q : ℝ × ℝ, q ∈ F ↔ (q.1 + d, q.2) ∈ F)
    (hfin : ∀ x : ℝ, (F ∩ {q : ℝ × ℝ | q.1 = x}).Finite) :
    IsPathConnected F := by
  classical
  set K : Set (Circle × ℝ) := closure (toCyl d '' F) with hKeq
  have hKsub : K ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1 := by
    rw [hKeq]
    refine closure_minimal ?_ ?_
    · rintro w ⟨q, hq, rfl⟩
      exact ⟨trivial, le_of_lt (hsub hq).1, le_of_lt (hsub hq).2⟩
    · exact isClosed_univ.prod isClosed_Icc
  have hKc : IsCompact K :=
    (isCompact_univ.prod isCompact_Icc).of_isClosed_subset isClosed_closure hKsub
  have hKcon : IsConnected K := by
    rw [hKeq]
    exact (hconn.image (toCyl d) (continuous_toCyl d).continuousOn).closure
  have hmer : ∀ z : Circle, (K ∩ {q : Circle × ℝ | q.1 = z}).Finite := by
    intro z
    have hbase : (toCyl d '' F ∩ {q : Circle × ℝ | q.1 = z}).Finite :=
      finite_toCyl_image_inter_meridian hd hper hfin z
    have hsub' : K ∩ {q : Circle × ℝ | q.1 = z} ⊆
        (toCyl d '' F ∩ {q : Circle × ℝ | q.1 = z})
          ∪ ({((z, 0) : Circle × ℝ)} ∪ {((z, 1) : Circle × ℝ)}) := by
      rintro w ⟨hwK, hwz⟩
      have hwz' : w.1 = z := by simpa only [Set.mem_ofPred_eq] using hwz
      have hw2 : w.2 ∈ Set.Icc (0:ℝ) 1 := (hKsub hwK).2
      rcases lt_or_ge w.2 1 with h | h
      · rcases eq_or_lt_of_le hw2.1 with h0 | h0
        · have hw' : w = (z, 0) := Prod.ext hwz' h0.symm
          exact Or.inr (Or.inl (by rw [hw']; simp))
        · exact Or.inl ⟨mem_toCyl_image_of_mem_closure hd hF hper hwK ⟨h0, h⟩, hwz⟩
      · have hw' : w = (z, 1) := Prod.ext hwz' (le_antisymm hw2.2 h)
        exact Or.inr (Or.inr (by rw [hw']; simp))
    exact (hbase.union
      ((Set.finite_singleton ((z, 1) : Circle × ℝ)).insert ((z, 0) : Circle × ℝ))).subset hsub'
  haveI : LocallyPathConnectedSpace ↥K :=
    Commons.Topology.Circle.locallyPathConnectedSpace_of_finite_meridians hKc hKcon hmer
  have hloc : LocallyPathConnectedSpace ↥F := by
    rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
    intro x u hu hxu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds hxu)
    obtain ⟨W, hWpc, hxW, hWF, hWball, δ, hδpos, hδsub⟩ :=
      exists_pathConnected_nhds_of_mem hd hF hsub hper hKeq x.2 hε
    have hpre : Subtype.val ⁻¹' W ∈ 𝓝 x := by
      refine Metric.mem_nhds_iff.mpr ⟨δ, hδpos, fun z hz => ?_⟩
      rw [Set.mem_preimage]
      refine hδsub ⟨z.2, ?_⟩
      rw [Metric.mem_ball]
      exact hz
    refine Filter.mem_of_superset hpre ?_
    intro z hz
    have hsub_pathconn : IsPathConnected (Subtype.val ⁻¹' W : Set ↥F) := hWpc.preimage_coe hWF
    have h1 : Subtype.val ⁻¹' W ⊆ u := by
      intro y hy
      have hyW : (y : ℝ × ℝ) ∈ W := hy
      have hd : dist y x < ε := Metric.mem_ball.mp (hWball hyW)
      exact hεu (Metric.mem_ball.mpr hd)
    have hxW' : x ∈ Subtype.val ⁻¹' W := hxW
    exact (hsub_pathconn.joinedIn x hxW' z hz).mono h1
  haveI : ConnectedSpace ↥F := isConnected_iff_connectedSpace.mp hconn
  haveI : LocallyPathConnectedSpace ↥F := hloc
  exact isPathConnected_iff_pathConnectedSpace.mpr (PathConnectedSpace.of_locallyPathConnectedSpace)

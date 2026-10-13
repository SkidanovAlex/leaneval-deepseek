import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.pm_sqrt_Icc
import Submission.Work.WilC4.pm_geom
import Submission.Work.WilC4.pm_sum_bound

namespace Work.WilC4

/-- Pigeonhole on a monotone/antitone function.

Let `g` be monotone (or antitone) on `[a,b]` with `0 < g t ≤ C` there, and let `m > 0`,
`C / m ≤ δ`.  Then there is a subinterval `[u,v] ⊆ [a,b]` of *multiplicative* width at least
`(b/a)^(1/m)` on which `g` is within `δ` of its value at the geometric mean `√(u v)`.

Proof: cut `[a,b]` into the `m` geometric pieces determined by `x i = a · r^i` with
`r = (b/a)^(1/m)`; the `m` gaps `g (x (i+1)) - g (x i)` telescope to at most `C`
(in either monotonicity direction), so by pigeonhole one of them is `≤ C/m ≤ δ`; that piece is
the required `[u,v]`, and `√(u v)` lies in it. -/
theorem pigeonhole_mono {g : ℝ → ℝ} {a b C δ : ℝ} {m : ℕ}
    (ha : 0 < a) (hab : a < b) (hm : 0 < m) (hC : 0 < C)
    (hmono : MonotoneOn g (Set.Icc a b) ∨ AntitoneOn g (Set.Icc a b))
    (hbd : ∀ t ∈ Set.Icc a b, 0 < g t ∧ g t ≤ C)
    (hδ : C / (m : ℝ) ≤ δ) :
    ∃ u v : ℝ, a ≤ u ∧ u < v ∧ v ≤ b ∧ (b / a) ^ ((1 : ℝ) / (m : ℝ)) ≤ v / u ∧
      ∀ t ∈ Set.Icc u v, |g t - g (Real.sqrt (u * v))| ≤ δ := by
  have hmR : (m : ℝ) ≠ 0 := by positivity
  -- The geometric mesh ratio.
  set r : ℝ := (b / a) ^ ((1 : ℝ) / (m : ℝ)) with hr
  obtain ⟨hr1, haxm, hmem, hstrict⟩ := pm_geom ha hab hm hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  -- The geometric mesh points.
  let x : ℕ → ℝ := fun i => a * r ^ i
  have hx0 : x 0 = a := by show a * r ^ 0 = a; rw [pow_zero, mul_one]
  have hxm : x m = b := haxm
  have hmemx : ∀ i ≤ m, x i ∈ Set.Icc a b := fun i hi => hmem i hi
  have hxinc : ∀ i, i < m → x i ≤ x (i + 1) := fun i _ => le_of_lt (hstrict i)
  -- The telescoping bound on the variation over the mesh.
  have hsum : ∑ i ∈ Finset.range m, |g (x (i + 1)) - g (x i)| ≤ C :=
    pm_sum_bound (le_of_lt hab) hmono hmemx hxinc hxm hx0 hbd
  -- Pigeonhole: some mesh piece has variation at most `C / m`.
  have hne : (Finset.range m).Nonempty := by
    rw [Finset.nonempty_range_iff]; exact hm.ne'
  have hsumconst : (∑ _i ∈ Finset.range m, C / (m : ℝ)) = C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  obtain ⟨i, hi, hile⟩ :=
    Finset.exists_le_of_sum_le (s := Finset.range m)
      (f := fun i => |g (x (i + 1)) - g (x i)|) (g := fun _ => C / (m : ℝ)) hne
      (by rw [hsumconst]; exact hsum)
  have him : i < m := Finset.mem_range.mp hi
  have hδi : |g (x (i + 1)) - g (x i)| ≤ δ := le_trans hile hδ
  have hxipos : 0 < x i := by show 0 < a * r ^ i; exact mul_pos ha (pow_pos hrpos i)
  have heq : x (i + 1) = x i * r := by
    show a * r ^ (i + 1) = a * r ^ i * r; rw [pow_succ]; ring
  have hratio : x (i + 1) / x i = r := by
    rw [heq]; exact mul_div_cancel_left₀ r (ne_of_gt hxipos)
  refine ⟨x i, x (i + 1), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmemx i (le_of_lt him)).1
  · exact hstrict i
  · exact (hmemx (i + 1) (by omega)).2
  · rw [hratio, hr]
  · intro t ht
    have hu : x i ∈ Set.Icc a b := hmemx i (le_of_lt him)
    have hv : x (i + 1) ∈ Set.Icc a b := hmemx (i + 1) (by omega)
    have huv : x i ≤ x (i + 1) := hxinc i him
    -- The geometric mean of the piece lies inside it.
    obtain ⟨huw, hwv⟩ := pm_sqrt_Icc hxipos huv
    have hw : Real.sqrt (x i * x (i + 1)) ∈ Set.Icc a b :=
      ⟨le_trans hu.1 huw, le_trans hwv hv.2⟩
    have ht' : t ∈ Set.Icc a b := ⟨le_trans hu.1 ht.1, le_trans ht.2 hv.2⟩
    rcases hmono with hmono | hanti
    · -- monotone: the oscillation is dominated by the last gap
      have hob : |g t - g (Real.sqrt (x i * x (i + 1)))| ≤ g (x (i + 1)) - g (x i) := by
        have h1 := hmono hu ht' ht.1
        have h2 := hmono ht' hv ht.2
        have h3 := hmono hu hw huw
        have h4 := hmono hw hv hwv
        rw [abs_le]; constructor <;> linarith
      calc |g t - g (Real.sqrt (x i * x (i + 1)))| ≤ g (x (i + 1)) - g (x i) := hob
        _ = |g (x (i + 1)) - g (x i)| := by
              rw [abs_of_nonneg (by linarith [hmono hu hv huv])]
        _ ≤ δ := hδi
    · -- antitone: the oscillation is dominated by the first gap
      have hob : |g t - g (Real.sqrt (x i * x (i + 1)))| ≤ g (x i) - g (x (i + 1)) := by
        have h1 := hanti hu ht' ht.1
        have h2 := hanti ht' hv ht.2
        have h3 := hanti hu hw huw
        have h4 := hanti hw hv hwv
        rw [abs_le]; constructor <;> linarith
      calc |g t - g (Real.sqrt (x i * x (i + 1)))| ≤ g (x i) - g (x (i + 1)) := hob
        _ = |g (x (i + 1)) - g (x i)| := by
              rw [abs_of_nonpos (by linarith [hanti hu hv huv])]; ring
        _ ≤ δ := hδi

end Work.WilC4

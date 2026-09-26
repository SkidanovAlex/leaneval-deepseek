import Mathlib
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le
import Submission.Work.Radial.quad_iteratedFDeriv_bound

/-!
# `x ↦ h (‖x‖ ^ 2)` is Schwartz when `t ↦ h (t ^ 2)` is Schwartz

Let `g : 𝓢(ℝ, ℂ)` be a Schwartz function of one variable and let `h : ℝ → ℂ` be smooth
with `g t = h (t ^ 2)` for all `t`.  Then `h` is rapidly decreasing on `[0, ∞)`
together with all its derivatives -- indeed on `(0, ∞)` the function `h` agrees with
`s ↦ g (√s)`, whose derivatives decay faster than any power of `s` (this is
`Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le`), and on `[0, 1]` they are
bounded by compactness.

Consequently the radial function `x ↦ h (‖x‖ ^ 2) = g (‖x‖)` on `ℝⁿ` is Schwartz:
it is smooth because it is the composition of the smooth function `h` with the
polynomial (hence smooth) function `x ↦ ‖x‖ ^ 2`, and its derivatives decay because
the chain rule bounds them by (a polynomial in `‖x‖`) times the decaying derivatives
of `h` at the point `‖x‖ ^ 2`.

## Main results

* `Work.RadialSpace.exists_halfline_iteratedDeriv_bound`: polynomial decay of the
  iterated derivatives of `h` on `[0, ∞)`.
* `Work.RadialSpace.schwartz_comp_norm_sq`: `x ↦ h (‖x‖ ^ 2)` is a Schwartz function
  on `ℝⁿ`.
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff

namespace Work.RadialSpace

/-- If `g t = h (t ^ 2)` for all `t`, then `g` is even. -/
lemma even_of_eq_comp_sq {g h : ℝ → ℂ} (hgh : ∀ t : ℝ, g t = h (t ^ 2)) :
    Function.Even g := by
  intro t
  rw [hgh (-t), hgh t, neg_sq]

/-- For `s > 0` the iterated derivatives of `h` and of `t ↦ g (√t)` agree, when
`g t = h (t ^ 2)`. -/
lemma iteratedDeriv_eq_iteratedDeriv_comp_sqrt {g h : ℝ → ℂ}
    (hgh : ∀ t : ℝ, g t = h (t ^ 2)) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    iteratedDeriv m h s = iteratedDeriv m (fun t : ℝ => g (Real.sqrt t)) s := by
  have h_eq : (fun t : ℝ => g (Real.sqrt t)) =ᶠ[𝓝 s] h := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
    rw [hgh (Real.sqrt u), Real.sq_sqrt (le_of_lt hu)]
  exact (Filter.EventuallyEq.iteratedDeriv_eq m h_eq).symm

/-- Every natural number, viewed in `ℕ∞ω`, is at most `Smooth`. -/
lemma natCast_le_smooth (m : ℕ) : ((m : ℕ∞ω)) ≤ Smooth := by
  rw [Smooth, show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

/-- **Polynomial decay of the iterated derivatives of `h` on the half-line.**  With
`g` Schwartz and `g t = h (t ^ 2)`, for all `m N` there is `C ≥ 0` with
`(1 + s) ^ N * ‖iteratedDeriv m h s‖ ≤ C` for every `s ≥ 0`. -/
theorem exists_halfline_iteratedDeriv_bound {g : SchwartzMap ℝ ℂ} {h : ℝ → ℂ}
    (hh : ContDiff ℝ Smooth h) (hgh : ∀ t : ℝ, g t = h (t ^ 2)) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ N * ‖iteratedDeriv m h s‖ ≤ C := by
  have he : Function.Even (⇑g) := even_of_eq_comp_sq hgh
  obtain ⟨C₁, hC₁⟩ := iteratedDeriv_comp_sqrt_pow_mul_le g he m N
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedDeriv m hh (natCast_le_smooth m)).continuousOn
  have hT : 0 ≤ max (max C₁ 0) (max B 0) := le_trans (le_max_right C₁ 0) (le_max_left _ _)
  refine ⟨2 ^ N * max (max C₁ 0) (max B 0), ?_, fun s hs => ?_⟩
  · exact mul_nonneg (pow_nonneg (by norm_num) _) hT
  · rcases le_total s 1 with hs1 | hs1
    · -- `0 ≤ s ≤ 1`: bound by compactness on `[0, 1]`
      have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs, hs1⟩
      have h2 : ‖iteratedDeriv m h s‖ ≤ max (max C₁ 0) (max B 0) :=
        le_trans (hB s hsI) (le_trans (le_max_left B 0) (le_max_right (max C₁ 0) (max B 0)))
      calc (1 + s) ^ N * ‖iteratedDeriv m h s‖
          ≤ 2 ^ N * ‖iteratedDeriv m h s‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) N)
              (norm_nonneg _)
        _ ≤ 2 ^ N * max (max C₁ 0) (max B 0) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num) _)
    · -- `s ≥ 1`: use the decay estimate for `s ↦ g (√s)`
      have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
      rw [iteratedDeriv_eq_iteratedDeriv_comp_sqrt hgh hs0 m]
      have h1 : (1 + s) ^ N ≤ 2 ^ N * s ^ N := by
        calc (1 + s) ^ N ≤ (2 * s) ^ N :=
              pow_le_pow_left₀ (by linarith) (by linarith) N
          _ = 2 ^ N * s ^ N := mul_pow 2 s N
      have h2 : s ^ N * ‖iteratedDeriv m (fun t : ℝ => g (Real.sqrt t)) s‖
          ≤ max (max C₁ 0) (max B 0) :=
        le_trans (hC₁ s hs1) (le_trans (le_max_left C₁ 0) (le_max_left _ _))
      calc (1 + s) ^ N * ‖iteratedDeriv m (fun t : ℝ => g (Real.sqrt t)) s‖
          ≤ (2 ^ N * s ^ N) * ‖iteratedDeriv m (fun t : ℝ => g (Real.sqrt t)) s‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = 2 ^ N * (s ^ N * ‖iteratedDeriv m (fun t : ℝ => g (Real.sqrt t)) s‖) := by
            ring
        _ ≤ 2 ^ N * max (max C₁ 0) (max B 0) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num) _)

/-- **The main construction.**  If `g : 𝓢(ℝ, ℂ)` and the smooth `h` satisfy
`g t = h (t ^ 2)`, then `x ↦ h (‖x‖ ^ 2) = g ‖x‖` is a Schwartz function on `ℝⁿ`. -/
theorem schwartz_comp_norm_sq {n : ℕ} [NeZero n] (g : SchwartzMap ℝ ℂ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ Work.RadialSpace.Smooth h) (hgh : ∀ t : ℝ, g t = h (t ^ 2)) :
    ∃ F : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, F x = h (‖x‖ ^ 2) := by
  have hsmooth : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => h (‖x‖ ^ 2)) :=
    hh.comp (contDiff_norm_sq ℝ)
  refine ⟨⟨fun x : EuclideanSpace ℝ (Fin n) => h (‖x‖ ^ 2), hsmooth, ?_⟩, fun x => rfl⟩
  intro k l
  choose C hC using fun i => exists_halfline_iteratedDeriv_bound (g := g) hh hgh i (k + l)
  let S : ℝ := ∑ i ∈ Finset.range (l + 1), C i
  have hS : 0 ≤ S := by
    simp only [S]
    exact Finset.sum_nonneg fun i _ => (hC i).1
  refine ⟨(Nat.factorial l : ℝ) * S * 4 ^ l, fun x => ?_⟩
  set a : ℝ := 1 + ‖x‖ ^ 2 with hadef
  set b : ℝ := 1 + ‖x‖ with hbdef
  have ha : 0 < a := by rw [hadef]; positivity
  have hb : 0 ≤ b := by rw [hbdef]; positivity
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  -- bound on the derivatives of `h` at the point `‖x‖ ^ 2`
  have hCx : ∀ i ≤ l, ‖iteratedFDeriv ℝ i h (‖x‖ ^ 2)‖ ≤ S / a ^ (k + l) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have h3 : a ^ (k + l) * ‖iteratedDeriv i h (‖x‖ ^ 2)‖ ≤ S := by
      have h1 : (1 + ‖x‖ ^ 2) ^ (k + l) * ‖iteratedDeriv i h (‖x‖ ^ 2)‖ ≤ C i :=
        (hC i).2 _ (by positivity)
      have h2 : C i ≤ S := by
        show C i ≤ ∑ j ∈ Finset.range (l + 1), C j
        exact Finset.single_le_sum (fun j _ => (hC j).1)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      rw [hadef]
      exact le_trans h1 h2
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < a ^ (k + l))).mpr (by
      rw [mul_comm]; exact h3)
  -- bound on the derivatives of the polynomial `x ↦ ‖x‖ ^ 2`
  have hDx : ∀ i, 1 ≤ i → i ≤ l →
      ‖iteratedFDeriv ℝ i (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) x‖ ≤ (2 * b ^ 2) ^ i := by
    intro i hi1 _
    refine (Work.Radial.norm_iteratedFDeriv_norm_sq_le i x).trans ?_
    have h2b : 2 * (1 + ‖x‖) ^ 2 = 2 * b ^ 2 := by rw [hbdef]
    rw [h2b]
    calc 2 * b ^ 2 = (2 * b ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ (2 * b ^ 2) ^ i := by
          refine pow_le_pow_right₀ ?_ hi1
          nlinarith [hb, sq_nonneg b]
  have hcomp := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := h)
    (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) hh (contDiff_norm_sq ℝ)
    (natCast_le_smooth l) x
    (C := S / a ^ (k + l)) (D := 2 * b ^ 2) hCx hDx
  simp only [Function.comp_def] at hcomp
  -- the elementary estimate `(2 (1+‖x‖)²)^l ‖x‖^k ≤ 4^l (1+‖x‖²)^(k+l)`
  have key : (2 * b ^ 2) ^ l * ‖x‖ ^ k ≤ 4 ^ l * a ^ (k + l) := by
    have hx_le : ‖x‖ ≤ a := by rw [hadef]; nlinarith [sq_nonneg ‖x‖]
    have h1 : ‖x‖ ^ k ≤ a ^ k := pow_le_pow_left₀ hx hx_le k
    have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * a := by
      rw [hadef]; nlinarith [sq_nonneg (1 - ‖x‖)]
    have h3 : 2 * b ^ 2 ≤ 4 * a := by rw [hbdef]; nlinarith [h2]
    calc (2 * b ^ 2) ^ l * ‖x‖ ^ k ≤ (4 * a) ^ l * a ^ k :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) h3 l) h1 (by positivity) (by positivity)
      _ = 4 ^ l * a ^ (k + l) := by
          rw [mul_pow, mul_assoc, ← pow_add, Nat.add_comm l k]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x : EuclideanSpace ℝ (Fin n) => h (‖x‖ ^ 2)) x‖
      ≤ ‖x‖ ^ k * ((Nat.factorial l : ℝ) * (S / a ^ (k + l)) * (2 * b ^ 2) ^ l) :=
        mul_le_mul_of_nonneg_left hcomp (pow_nonneg hx _)
    _ = (Nat.factorial l : ℝ) * S * ((2 * b ^ 2) ^ l * ‖x‖ ^ k / a ^ (k + l)) := by ring
    _ ≤ (Nat.factorial l : ℝ) * S * (4 ^ l * a ^ (k + l) / a ^ (k + l)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_right key (by positivity)
    _ = (Nat.factorial l : ℝ) * S * 4 ^ l := by
        rw [mul_div_cancel_right₀ _ (by positivity : a ^ (k + l) ≠ 0)]

end Work.RadialSpace

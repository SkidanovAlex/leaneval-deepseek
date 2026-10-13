/-
  WilC4/rexp_deep_window_value_ratio : the fibre's *value* ratio over a deep window.

  ## The statement (proved in this file)

  There are `N ≥ 2` and `Q > 0` such that whenever the window `[z/N, N z']` is free of the
  breakpoint family `B₀` (`Fin.cons t c ∉ B₀` for all `t` in the window), any two fibre values
  `y` at `z` and `y'` at `z'` with `z ≤ z' ≤ 2z` and `y ≠ 0` satisfy `|y'| ≤ Q |y|`.

  ## Why this is *not* a local statement about real functions

  A `2`-multiplicatively periodic continuous `f` with a non-constant profile satisfies
  `GoodFibre`: continuity, nonvanishing, and ratio monotonicity (`w ≡ 1`) — yet its value ratio
  `f (z') / f (z)` over a pair `z ≤ z' ≤ 2z` is unbounded.  Such an `f` is not definable in an
  o-minimal structure, and locally (on a bounded window) no hypothesis in our list separates it from
  a genuine fibre.  What excludes it is the *global* input `Work.WilC4.ulpm_mono_param`: for a
  definable family the fibre is monotone-or-antitone off a definable breakpoint family `Bm` whose
  fibres have at most `N₁` points — a bound on the number of monotonicity pieces of the fibre **on
  every interval**, in particular on the whole window.  The periodic counterexample has a number of
  pieces on the window proportional to the *multiplicative width* of the window, hence violates that
  uniform bound once the window is large.

  ## The argument (the "shift to a monotone slot" trick)

  Write `G x = |valY Y c x|` and `ρ = ratioY Y c`, so that `G (2x) = ρ x · G x` where the fibre is
  nonzero, and `ρ` is monotone-or-antitone on the window `(z/N, N z')` cut at `N z'/2`
  (`ULPMStruct`'s ratio claw).

  * If `ρ` is **nondecreasing**, the telescoping identity shows that the value ratio over the pair
    `(z, z')` is at most the value ratio over the shifted pair `(2^k z, 2^k z')`, for every `k` for
    which the shifted points remain in the window.
  * Among the `N₁ + 2` pairwise disjoint slots `(2^k z, 2^{k+1} z)`, `k = 1, …, N₁ + 2`, at most `N₁`
    meet `Bm`; pick a `Bm`-free one.  The fibre is monotone-or-antitone on that slot, and
    `2^k z' ∈ [2^k z, 2^{k+1} z]`, so the shifted value ratio is bounded by `max (1, ρ (2^k z))`.
  * The deep-ratio bound `Work.WilC4.deep_ratio_scale_bdd` applies at `2^k z` with the scale
    `N z' / (2^{k+1} z) ≥ Γ`, giving `ρ (2^k z) < N/2`.  Hence `|y'| ≤ (N/2) |y|`.
  * If `ρ` is **nonincreasing** the same argument runs with the backward shifts `z / 2^i`, whose
    slots `(z / 2^i, 2 z / 2^i)` are again pairwise disjoint.

  The scale is `N = 2^L` with `(2 + Γ) · 2^{N₁+4} < N`, so that all the shifted points exist inside
  the window and the deep bound `Γ` applies at every slot.  The constant is `Q = N/2`.

  ## Files

  * `Work.WilC4.rexp_deep_window_value_ratio` (this file): the statement, the core `N/2` bound
    `rexp_window_ratio_of_monoOn` (monotone fibre case), and the final assembly.
  * `Work.WilC4.rexp_deep_window_value_ratio_aux`: the real-analysis lemmas (fibre facts on a free
    interval, the ratio claw, the slot bound, the telescoping identities, the slot pigeonhole).
  * `Work.WilC4.window_ratio_case_up` / `Work.WilC4.window_ratio_case_down`: the two cases.
  * Earlier lemmas still exported: `isDeepR_half_of_window`, `ratW_lt_of_window`,
    `rexp_window_ratio_of_monoOn`, `rexp_deep_window_value_ratio_of_mono` (the `hfmono` version);
    the `MonomialDatum` vocabulary (`Work.WilC4.MonomialDatum`) turned out to be unnecessary for
    this statement.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.deep_ratio_scale_bdd
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC4.MonomialDatum
import Submission.Work.WilC4.ulpm_mono_param
import Submission.Work.WilC4.rexp_deep_window_value_ratio_aux
import Submission.Work.WilC4.rexp_deep_window_value_ratio_case_up
import Submission.Work.WilC4.rexp_deep_window_value_ratio_case_down

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr valY ratioY valY_mem InD eq_valY)

variable {k : ℕ}

/-- The standard fact used to compare a value lying between `a` and `c` with their absolute values:
`min a c ≤ b ≤ max a c` implies `|b| ≤ max |a| |c|`. -/
private theorem abs_le_max_abs_of_between {a b c : ℝ} (h1 : min a c ≤ b) (h2 : b ≤ max a c) :
    |b| ≤ max (|a|) (|c|) := by
  rcases le_total a c with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le a, le_max_left (|a|) (|c|)]
    · linarith [le_abs_self c, le_max_right (|a|) (|c|)]
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le c, le_max_right (|a|) (|c|)]
    · linarith [le_abs_self a, le_max_left (|a|) (|c|)]

/-! ## 1. Points of the pair's interval are deep -/

/-- If the window `[z/N, N z']` is free of `B₀` and `z ≤ t ≤ z'`, then `t` is `N/2`-deep: the deep
window `[t/N, N t]` is contained in `[z/N, N z']`.  (Note `2 * (N/2) = N`.) -/
theorem isDeepR_half_of_window {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ}
    {N z z' : ℝ} (hN : 0 < N)
    (hfree : ∀ t : ℝ, z / N ≤ t → t ≤ N * z' → Fin.cons t c ∉ B₀)
    {t : ℝ} (ht1 : z ≤ t) (ht2 : t ≤ z') : Work.WilC4.IsDeepR B₀ c (N / 2) t := by
  intro b hb hcon
  have h2 : 2 * (N / 2) = N := by ring
  rw [h2] at hcon
  obtain ⟨h1, h3⟩ := hcon
  refine hfree b ?_ ?_ hb
  · have : z / N ≤ t / N := div_le_div_of_nonneg_right ht1 (le_of_lt hN)
    linarith
  · have : N * t ≤ N * z' := mul_le_mul_of_nonneg_left ht2 (le_of_lt hN)
    linarith

/-! ## 2. The doubling ratio is bounded at points of the pair's interval -/

/-- The `RatW` value at a point `t ∈ [z, z']` of a configuration with `B₀`-free window
`[z/N, N z']` is bounded by `N/2`, as soon as `N/2` is at least the scale `Γ` supplied by the
proved uniform deep-ratio bound `deep_ratio_scale_bdd`. -/
theorem ratW_lt_of_window {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {c : Fin k → ℝ} {N z z' w Γ : ℝ} (hN : 0 < N) (hΓN : Γ ≤ N / 2)
    (hscale : ∀ β : ℝ, Γ ≤ β → ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      Work.WilC4.IsDeepR B₀ c β x → Work.WilC4.RatW Y c x w → |w| < β)
    (hfree : ∀ t : ℝ, z / N ≤ t → t ≤ N * z' → Fin.cons t c ∉ B₀)
    {t : ℝ} (ht1 : z ≤ t) (ht2 : t ≤ z') (ht0 : 0 < t) (hrat : Work.WilC4.RatW Y c t w) :
    |w| < N / 2 :=
  hscale (N / 2) hΓN c t w ht0 (isDeepR_half_of_window hN hfree ht1 ht2) hrat

/-! ## 3. The core `N/2` bound, and the restated target with the fibre-monotonicity hypothesis -/

/-- **Core of the monotone case (the `N/2` bound).**  If the fibre is monotone-or-antitone on the
`B₀`-free window `(z/N, N z')` and `0 < z ≤ z' ≤ 2z`, then any two fibre values `y` at `z`, `y'`
at `z'` with `y ≠ 0` satisfy `|y'| ≤ (N/2) |y|`.

`y' = f z'` lies between `f z` and `f (2z)` (`2z` is still in the window), and
`|f (2z)| = |ratioY Y c z| · |f z|` with `|ratioY Y c z| < N/2` (`ratW_lt_of_window`), since `z` is
`N/2`-deep. -/
theorem rexp_window_ratio_of_monoOn {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hst : Work.WilC4.ULPMStruct Y B₀) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (c : Fin k → ℝ) (z z' y y' : ℝ), 0 < z → z ≤ z' → z' ≤ 2 * z →
      (∀ t : ℝ, z / (N : ℝ) ≤ t → t ≤ (N : ℝ) * z' → Fin.cons t c ∉ B₀) →
      (MonotoneOn (Work.WilC4.Route.valY Y c) (Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z')) ∨
        AntitoneOn (Work.WilC4.Route.valY Y c) (Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z'))) →
      Work.WilC4.Route.Gr Y c z y → Work.WilC4.Route.Gr Y c z' y' → y ≠ 0 →
      |y'| ≤ ((N : ℝ) / 2) * |y| := by
  classical
  obtain ⟨Γ, hΓ1, hΓ⟩ := deep_ratio_scale_bdd hR hOM hPB Y hY hfun B₀ hB₀ hst
  obtain ⟨N, hN2, hNΓ⟩ : ∃ N : ℕ, 2 ≤ N ∧ Γ ≤ (N : ℝ) / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max (2 * Γ) 2)
    exact ⟨N, by exact_mod_cast le_trans (le_max_right (2 * Γ) 2) hN,
      by linarith [le_max_left (2 * Γ) 2, hN]⟩
  refine ⟨N, hN2, ?_⟩
  intro c z z' y y' hz hle h2 hfree hmono hgz hgz' hy
  have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1r : (1 : ℝ) < (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hz'pos : 0 < z' := lt_of_lt_of_le hz hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- degenerate case `z' = z`: both values are the same
    subst heq
    have hyy : y = y' := hfun c z y y' hgz hgz'
    rw [← hyy]
    nlinarith [abs_nonneg y, hN2r]
  · -- the monotone case
    have hzI : z ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z') :=
      ⟨div_lt_self hz hN1r, by nlinarith [hz'pos, hle, hN2r]⟩
    have hz'I : z' ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z') :=
      ⟨lt_of_lt_of_le (div_lt_self hz hN1r) hle, by nlinarith [hz'pos, hN1r, hN2r]⟩
    have h2zI : 2 * z ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z') := by
      constructor
      · have : z / (N : ℝ) < z := div_lt_self hz hN1r
        linarith
      · nlinarith [hz'pos, hlt, hN2r]
    have hfree' : ∀ x ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z'), Fin.cons x c ∉ B₀ :=
      fun x hx => hfree x (le_of_lt hx.1) (le_of_lt hx.2)
    have hab : z / (N : ℝ) < (N : ℝ) * z' :=
      lt_trans hzI.1 hzI.2
    have hrat : Work.WilC4.RatW Y c z (Work.WilC4.Route.ratioY Y c z) :=
      ratW_ratioY hfun hst.1 hab hfree' hzI h2zI
    have hr : |Work.WilC4.Route.ratioY Y c z| < (N : ℝ) / 2 :=
      ratW_lt_of_window (t := z) hNpos hNΓ hΓ hfree le_rfl hle hz hrat
    have hyz : y = Work.WilC4.Route.valY Y c z := Work.WilC4.Route.eq_valY hfun hgz
    have hyz' : y' = Work.WilC4.Route.valY Y c z' := Work.WilC4.Route.eq_valY hfun hgz'
    -- `f z'` lies between `f z` and `f (2z)`
    have habs : |Work.WilC4.Route.valY Y c z'| ≤
        max (|Work.WilC4.Route.valY Y c z|) (|Work.WilC4.Route.valY Y c (2 * z)|) :=
      abs_le_max_abs_of_between
        (by
          rcases hmono with hm | ha
          · exact le_trans (min_le_left _ _) (hm hzI hz'I (le_of_lt hlt))
          · exact le_trans (min_le_right _ _) (ha hz'I h2zI h2))
        (by
          rcases hmono with hm | ha
          · exact le_trans (hm hz'I h2zI h2) (le_max_right _ _)
          · exact le_trans (ha hzI hz'I (le_of_lt hlt)) (le_max_left _ _))
    have hfzne : Work.WilC4.Route.valY Y c z ≠ 0 := by rw [← hyz]; exact hy
    have h2z_eq : Work.WilC4.Route.valY Y c (2 * z) =
        Work.WilC4.Route.ratioY Y c z * Work.WilC4.Route.valY Y c z := by
      rw [Work.WilC4.Route.ratioY]
      exact (div_mul_cancel₀ _ hfzne).symm
    have h2z_abs : |Work.WilC4.Route.valY Y c (2 * z)| =
        |Work.WilC4.Route.ratioY Y c z| * |Work.WilC4.Route.valY Y c z| := by
      rw [h2z_eq, abs_mul]
    have hmax : max (|Work.WilC4.Route.valY Y c z|) (|Work.WilC4.Route.valY Y c (2 * z)|) ≤
        (N : ℝ) / 2 * |Work.WilC4.Route.valY Y c z| := by
      refine max_le ?_ ?_
      · nlinarith [abs_nonneg (Work.WilC4.Route.valY Y c z), hN2r]
      · rw [h2z_abs]
        nlinarith [abs_nonneg (Work.WilC4.Route.valY Y c z), hr]
    calc |y'| = |Work.WilC4.Route.valY Y c z'| := by rw [hyz']
      _ ≤ max (|Work.WilC4.Route.valY Y c z|) (|Work.WilC4.Route.valY Y c (2 * z)|) := habs
      _ ≤ (N : ℝ) / 2 * |Work.WilC4.Route.valY Y c z| := hmax
      _ = (N : ℝ) / 2 * |y| := by rw [hyz]

/-- **The requested statement, restated with the fibre-monotonicity hypothesis** that `slot_bound`
already takes (`hfmono`).  It is discharged *now* from the proved uniform deep-ratio bound
`deep_ratio_scale_bdd` (via the core `rexp_window_ratio_of_monoOn`), with `Q = N/2`. -/
theorem rexp_deep_window_value_ratio_of_mono {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hst : Work.WilC4.ULPMStruct Y B₀)
    (hfmono : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b →
      (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) →
      MonotoneOn (Work.WilC4.Route.valY Y c) (Set.Ioo a b) ∨
        AntitoneOn (Work.WilC4.Route.valY Y c) (Set.Ioo a b)) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ Q : ℝ, 0 < Q ∧
      ∀ (c : Fin k → ℝ) (z z' y y' : ℝ), 0 < z → z ≤ z' → z' ≤ 2 * z →
      (∀ t : ℝ, z / (N : ℝ) ≤ t → t ≤ (N : ℝ) * z' → Fin.cons t c ∉ B₀) →
      Work.WilC4.Route.Gr Y c z y → Work.WilC4.Route.Gr Y c z' y' → y ≠ 0 →
      |y'| ≤ Q * |y| := by
  obtain ⟨N, hN2, hcore⟩ := rexp_window_ratio_of_monoOn hR hOM hPB Y hY hfun B₀ hB₀ hst
  refine ⟨N, hN2, (N : ℝ) / 2, by positivity, ?_⟩
  intro c z z' y y' hz hle h2 hfree hgz hgz' hy
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    have hyy : y = y' := hfun c z y y' hgz hgz'
    rw [← hyy]
    have h2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    nlinarith [abs_nonneg y, h2r]
  · refine hcore c z z' y y' hz hle h2 hfree ?_ hgz hgz' hy
    have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have hz'pos : 0 < z' := lt_of_lt_of_le hz hle
    have hab : z / (N : ℝ) < (N : ℝ) * z' := by
      have h1 : z / (N : ℝ) ≤ z / 2 :=
        div_le_div_of_nonneg_left (le_of_lt hz) (by norm_num) (by linarith)
      have h2' : z / 2 < z := div_lt_self hz (by norm_num)
      have h3 : z < (N : ℝ) * z' := by nlinarith [hz'pos, hlt, hN2r]
      linarith
    have hfree' : ∀ x ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z'), Fin.cons x c ∉ B₀ :=
      fun x hx => hfree x (le_of_lt hx.1) (le_of_lt hx.2)
    exact hfmono c (z / (N : ℝ)) ((N : ℝ) * z') hab hfree'

/-! ## 5. The requested statement (unchanged; see the header for its status) -/

theorem rexp_deep_window_value_ratio {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hst : Work.WilC4.ULPMStruct Y B₀) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ Q : ℝ, 0 < Q ∧
      ∀ (c : Fin k → ℝ) (z z' y y' : ℝ), 0 < z → z ≤ z' → z' ≤ 2 * z →
      (∀ t : ℝ, z / (N : ℝ) ≤ t → t ≤ (N : ℝ) * z' → Fin.cons t c ∉ B₀) →
      Work.WilC4.Route.Gr Y c z y → Work.WilC4.Route.Gr Y c z' y' → y ≠ 0 →
      |y'| ≤ Q * |y| := by
  classical
  -- ### the two constants of the theory
  obtain ⟨Γ, hΓ1, hΓbd⟩ := deep_ratio_scale_bdd hR hOM hPB Y hY hfun B₀ hB₀ hst
  obtain ⟨N₁, Bm, -, hBmcard, htri⟩ := ulpm_mono_param hOM Y hY hfun
  -- ### the scale: a power of two larger than `(2 + Γ) · 2^{N₁ + 4}`
  obtain ⟨L, hL⟩ :=
    pow_unbounded_of_one_lt ((2 + Γ) * (2 : ℝ) ^ (N₁ + 4)) (show (1 : ℝ) < 2 by norm_num)
  set N : ℕ := 2 ^ L with hNdef
  have hNrbig : (2 + Γ) * (2 : ℝ) ^ (N₁ + 4) < (N : ℝ) := by
    have hcast : (((2 : ℕ) ^ L : ℕ) : ℝ) = (2 : ℝ) ^ L := by push_cast; ring
    rw [hNdef, hcast]
    exact hL
  have hN2 : 2 ≤ N := by
    have hle : (2 : ℝ) ≤ (2 + Γ) * (2 : ℝ) ^ (N₁ + 4) := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (N₁ + 4) := one_le_pow₀ (by norm_num)
      nlinarith [hΓ1, h1]
    exact_mod_cast le_of_lt (lt_of_le_of_lt hle hNrbig)
  refine ⟨N, hN2, (N : ℝ) / 2, by positivity, ?_⟩
  intro c z z' y y' hz hle h2z hfree hgz hgz' hy
  set Nr : ℝ := (N : ℝ) with hNrdef
  have hNrpos : 0 < Nr := by rw [hNrdef]; positivity
  have hNr2 : (2 : ℝ) ≤ Nr := by rw [hNrdef]; exact_mod_cast hN2
  have hNr1 : (1 : ℝ) < Nr := by linarith
  have hNr2Γ : 2 * Γ ≤ Nr := by
    rw [hNrdef]
    have h1 : (16 : ℝ) ≤ (2 : ℝ) ^ (N₁ + 4) := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 4 ≤ N₁ + 4 by omega)
      have h2 : (2 : ℝ) ^ 4 = 16 := by norm_num
      linarith [h, h2]
    nlinarith [le_of_lt hNrbig, h1, hΓ1]
  have hNrΓ : Γ * (2 : ℝ) ^ (N₁ + 3) ≤ Nr := by
    rw [hNrdef]
    have hp : (2 : ℝ) ^ (N₁ + 4) = 2 * (2 : ℝ) ^ (N₁ + 3) := by
      rw [show N₁ + 4 = (N₁ + 3) + 1 by omega, pow_succ]; ring
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (N₁ + 3) := by positivity
    nlinarith [le_of_lt hNrbig, hp, hΓ1, h1]
  have hNrpow : (2 : ℝ) ^ (N₁ + 4) ≤ Nr := by
    rw [hNrdef]
    have h1 : (1 : ℝ) ≤ 2 + Γ := by linarith
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (N₁ + 4) := by positivity
    nlinarith [le_of_lt hNrbig, h1, h2]
  have hz'pos : 0 < z' := lt_of_lt_of_le hz hle
  have hfree' : ∀ t : ℝ, z / Nr ≤ t → t ≤ Nr * z' → Fin.cons t c ∉ B₀ := by
    intro t h1 h2
    rw [hNrdef] at h1 h2
    exact hfree t h1 h2
  -- the window is nondegenerate
  have hab : z / Nr < Nr * z' := by
    have h1 : z / Nr ≤ z / 2 := div_le_div_of_nonneg_left hz.le (by norm_num) hNr2
    have h2 : z / 2 < z := div_lt_self hz (by norm_num)
    have h3 : z < Nr * z' := by nlinarith [hz'pos, hNr2]
    linarith
  have hfreeW : ∀ x ∈ Set.Ioo (z / Nr) (Nr * z'), Fin.cons x c ∉ B₀ :=
    fun x hx => hfree' x (le_of_lt hx.1) (le_of_lt hx.2)
  -- the doubling ratio is monotone-or-antitone on the part of the window whose double fits
  have hab2 : z / Nr < Nr * z' / 2 := by
    have h1 : z / Nr < z := div_lt_self hz hNr1
    have h2 : z ≤ Nr * z' / 2 := by nlinarith [hz'pos, hle, hNr2]
    linarith
  have hsub : Set.Ioo (z / Nr) (Nr * z' / 2) ⊆ Set.Ioo (z / Nr) (Nr * z') :=
    fun x hx => ⟨hx.1, by nlinarith [hx.2, hz'pos, hNrpos]⟩
  have h2W : ∀ x ∈ Set.Ioo (z / Nr) (Nr * z' / 2), 2 * x ∈ Set.Ioo (z / Nr) (Nr * z') := by
    intro x hx
    exact ⟨by nlinarith [hx.1, div_pos hz hNrpos], by nlinarith [hx.2]⟩
  have hρ := ratioY_monoOrAnti hfun hst hab hfreeW hab2 hsub h2W
  rcases hρ with hmono | hanti
  · exact window_ratio_case_up hst hfun hBmcard htri hΓ1 hΓbd hNr2Γ hNrΓ hNrpow hz hle h2z hfree'
      hgz hgz' hy (by simpa only [hNrdef] using hmono)
  · exact window_ratio_case_down hst hfun hBmcard htri hΓ1 hΓbd hNr2Γ hNrΓ hNrpow hz hle h2z
      hfree' hgz hgz' hy (by simpa only [hNrdef] using hanti)

end Work.WilC4

/-
  WilC4/dev_decay_E : the decay of the deviations at deep points (step 5 of the ULPM proof).

  Statement: at every `B`-deep point `(c,x)` of sufficiently large scale `M`, every doubling
  ratio `w = f_c(2x)/f_c(x)` is within `ε` (multiplicatively) of some *positive* element of `E`.
  Equivalently, `BadScale Y B E ε` is bounded above for every `ε > 0`.

  ## Proof strategy (REVISED, 2026-10-11)

  The earlier `limsup`-plan is **dead**: the delegated lemma `Work.WilC4.clusterE_limsup` was
  refuted by its prover (the monotonicity direction is only available *per fibre*, so the limsup
  of the rescaled ratios need not be monotone, and its infimum need not be a cluster value).

  The current plan is a *pigeonhole / flat-piece* argument, with no limsup and no filters.

  0. Setup: `GoodFibre Y B` and `ULPMStruct Y B` from `hst` and `hsub` (`goodFibre_mono`); a
     positive element of `E` from `clusterE_pos` (uses `hR`, `hPB`, `hBcard`, `GoodFibre`) and
     `hsubE`.
  1. Contrapositive: assume `BadScale Y B E ε` is unbounded.  `badScale_all` then produces, for
     every `j`, a bad witness `(c j, x j, w j)` at the scale `M_j = (j:ℝ)+2`, with
     `0 < x j`, `IsDeepR B (c j) M_j (x j)`, `RatW Y (c j) (x j) (w j)` and
     `∀ ρ ∈ E, 0 < ρ → ε < |w j / ρ - 1|`.
  2. `w j = ratioY Y (c j) (x j)` (`ratW_eq_ratioY`); `0 < w j` (`deep_ratW_pos`) and
     `w j ≤ C` (`hbdd`, step 5 of the old plan, `IsDeepR.two_of_window`).
  3. `hband (c j)` applied to the **deep window** `(x j/(2M_j), 2M_j x j)` (B-free by
     `deep_free`) gives the dichotomy:
     • **(B)** the ratio is constantly `mid j ∈ Mid E` on the window.  Then the point `x j` is
       `N`-deep for every `N ≤ 2 M_j` and the ratio is `≡ mid j` on `[x j/N, x j N]`, so `mid j`
       is a cluster value *at those scales*.  Since the scales `M_j` are unbounded and `Mid E` is
       finite, some `mid ∈ Mid E` occurs infinitely often and satisfies `mid ∈ ClusterE Y B ⊆ E`;
       the badness at any of those `j` then gives `ε < |mid/mid - 1| = 0`, a contradiction.
     • **(A)** the ratio *avoids* `Mid E` on the window.  Then, on the inner window
       `Ioo (x j/(2M_j)) (M_j x j)` (where `ratioY` is a genuine `RatW` value,
       `ratW_ratioY_of_deep`), the ratio is continuous (`ratioY_cont_window`) and its image is
       therefore a **connected** subset of `ℝ ∖ Mid E`, i.e. it lies in one component `C` (the
       "band").  `mid_band_unique` gives the unique positive `ρ ∈ E` with the band condition at
       `w j` (`w j ∉ Mid E` by (A), `0 < w j`); since every component of `ℝ ∖ Mid E` contains
       exactly one positive element of `E` (interlacing of `E⁺` with its consecutive geometric
       means), `E ∩ C ∩ (0,∞) = {ρ}`.
  4. **The flat-piece argument.**  `normRatio_mono` makes `s ↦ ratioY Y (c j) (x j s)` monotone
     *or* antitone on `Ioo (1/M_j) M_j`.  Suppose `w j > ρ(1+ε)` (the case `w j < ρ(1-ε)` is
     mirror).  Then, according to the monotonicity direction, one of the two multiplicative
     regions
         `R⁺ := [N, M_j/(2N)]`,      `R⁻ := [2N/M_j, 1/N]`     (in the variable `s`)
     has ratio `≥ w j` throughout (both are the "far side" of `x j`), and every point of `R^±`
     is 2-deep.  On that region the ratio is monotone with values in `(0, C]`, so by the
     pigeonhole lemma `pigeonhole_mono` (delegate) it contains a subinterval of multiplicative
     width `≥ N²` on which the ratio has oscillation `≤ 1/N`.  Its midpoint `y` is `N`-deep
     (the window `[y/(2N), 2Ny]` sits inside the deep window of `x j`) and the ratio is within
     `1/N` of `λ := ratioY Y (c j) y` on `[y/N, yN]`, so **`λ ∈ ClusterE Y B`** at the scale `N`.
     Also `λ ≥ w j` (or `≤`), and `λ` lies in the same band `C` as `w j`.
  5. **Conclusion.**  `λ ∈ ClusterE ⊆ E` (`hsubE`) and `λ ∈ C`, so `λ = ρ` by step 3; but
     `λ ≥ w j > ρ(1+ε) > ρ` (or `λ ≤ w j < ρ(1-ε) < ρ`), contradiction.

  ### The missing ingredient `hzero : 0 ∉ ClusterE Y B`, and how it is discharged

  **Why `hzero` is needed.**  A would-be `0`-cluster witness is a `B`-deep point `x` whose doubling
  ratio is `≤ 1/N` on the whole window `[x/N, Nx]`.  Since `E ⊇ ClusterE Y B` and the conclusion
  only tests the *positive* elements of `E`, the ratio escaping to the cluster value `0` at
  arbitrarily large scales would make every large scale bad and the theorem false.  The
  machine-checked counterexample of the (true, but not `LRc`-definable) family
  `Y = {v | v 1 = Real.exp (-(v 0)^2)}`, `B = ∅`, `E = {0,1}`, `ε = 1/2` shows exactly this: the
  ratio `exp(-3t²)` is `≤ 1/N` on the window of scale `N` at `x` of size `N√(log N)`, so
  `0 ∈ ClusterE Y B`, yet every large scale is bad.  `Real.exp` is not `LRc`-definable, so this is
  not a counterexample to the theorem, but it shows that the case-(A) step — whose output `λ` was
  only known to lie in `ClusterE` — needs `λ ≠ 0`, i.e. `hzero`.

  **Why `hzero` is true.**  The deep ratio is bounded *below* as well as above: applying
  `deep_ratio_scale_bdd` (the *upper* bound `|w| < β` at `β`-deep points) to the **value-inverted**
  family `InvY Y` — whose doubling ratio is the *inverse* of the ratio of `Y` at the same point
  (`ratW_invY_iff`) — gives `2/N < |w|` for any doubling ratio `w` at a point `z` whose window
  `[z/N, Nz']` is `B`-free.  A `0`-witness at the scale `N` is exactly such a point with
  `|w| ≤ 1/N`, a contradiction.  (The inversions needs the halved breakpoint family
  `HalfB B = B ∪ B/2` to keep the sign of the inverted ratio constant on `B`-free intervals, which
  is where `ULPMStruct (InvY Y) (HalfB B)` comes from.)

  This is proved in `Submission/Work/WilC4/zero_cluster.lean`:

  * `Work.WilC4.zero_not_mem_clusterE_aux` : `(0 : ℝ) ∉ Route.ClusterE Y B` from `hR`, `hOM`,
    `hPB`, `hY`, `hfun`, `hB` and `hst : ULPMStruct Y B`;
  * `Work.WilC4.ratW_gt_of_window_aux` : the lower bound `2/N < |w|`;
  * `Work.WilC4.invY_definable_b` : `InvY Y` is `∅`-definable (a self-contained replacement for
    `Submission/Work/WilC4/invY_definable.lean`, which currently does not elaborate).

  The two pieces it rests on live in sibling files: `Work.WilC4.invY_ulpmStruct_b`
  (`ULPMStruct (InvY Y) (HalfB B)` from `ULPMStruct Y B`) and `Work.WilC4.halfB_definable_b`
  (`HalfB B` is `∅`-definable).

  **Status.**  The assembly below is complete and machine-checked; the only input it takes is the
  proved `hzero` (`zero_not_mem_clusterE_aux`) together with the previously proved
  `Work.WilC4.caseA_bad_bounded_zero` (case (A)), `Work.WilC4.pigeonhole_mono`,
  `mid_finite`/`mb_exists_mid_between` (the `Mid` interlacing), `mid_band_unique`,
  `band_label_closed`, `normRatio_mono`, `ratioY_cont_window`, `clusterE_pos`, and the local
  lemmas `badScale_all`, `badScale_mono`, `deep_ratW_pos`, `ratW_ratioY_of_deep`,
  `IsDeepR.two_of_window`, `deep_free`, `deep_val`, `deep_cont`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.ulpm_Bx
import Submission.Work.WilC4.mid_band_unique
import Submission.Work.WilC4.deep_ratio_scale_bdd
import Submission.Work.WilC4.mb_exists_mid_between
import Submission.Work.WilC4.mb_mid_gap_unique
import Submission.Work.WilC4.ratioY_cont_window
import Submission.Work.WilC4.normRatio_mono
import Submission.Work.WilC4.band_label_closed
import Submission.Work.WilC4.band_label_of_interval
import Submission.Work.WilC4.clusterE_pos
import Submission.Work.WilC4.caseA_bad_bounded_zero
import Submission.Work.WilC4.ratio_lower_infty
import Submission.Work.WilC4.ratio_lower_zero
import Submission.Work.WilC4.zero_cluster

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr InD valY valY_mem eq_valY ratioY IsDeep ClusterE)

variable {k : ℕ}

/-! ## 1. Deepness and monotonicity in the breakpoint family -/

/-- Deepness w.r.t. a larger breakpoint family implies deepness w.r.t. a smaller one. -/
theorem IsDeepR.of_subset {B₀ B : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {β x : ℝ}
    (hsub : B₀ ⊆ B) (h : IsDeepR B c β x) : IsDeepR B₀ c β x :=
  fun b hb => h b (hsub hb)

/-- `GoodFibre` transfers to a larger breakpoint family. -/
theorem goodFibre_mono {Y : Set (Fin (k + 2) → ℝ)} {B₀ B : Set (Fin (k + 1) → ℝ)}
    (h : GoodFibre Y B₀) (hsub : B₀ ⊆ B) : GoodFibre Y B :=
  fun c a b hab hB => h c a b hab fun x hx hxB => hB x hx (hsub hxB)

/-- The natural-scale and real-scale deepness conditions agree. -/
theorem isDeep_iff_isDeepR {B : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {N : ℕ} {x : ℝ} :
    IsDeep B c N x ↔ IsDeepR B c (N : ℝ) x := Iff.rfl

/-! ## 2. The doubling ratio at a deep point -/

/-- On the deep window, `ratioY` is a genuine `RatW` value. -/
theorem ratW_ratioY_of_deep {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B₀) {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 < β) (hx : 0 < x)
    (hdeep : IsDeepR B₀ c β x) {z : ℝ} (hz : z ∈ Set.Ioo (x / (2 * β)) (β * x)) :
    RatW Y c z (ratioY Y c z) := by
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := le_of_lt hβ
  have hx2b : 0 < 2 * β := by linarith
  have hzdeep : z ∈ Set.Ioo (x / (2 * β)) (2 * β * x) :=
    ⟨hz.1, by nlinarith [hz.2, hx, hβ0]⟩
  have h2zdeep : 2 * z ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    refine ⟨?_, by nlinarith [hz.2, hx, hβ0]⟩
    have hz1 : x < z * (2 * β) := (div_lt_iff₀ hx2b).mp hz.1
    rw [div_lt_iff₀ hx2b]
    nlinarith [hz1, hz.1, hx2b, hx]
  obtain ⟨hg1, hnz⟩ := deep_val hgf hβ1 hx hdeep hzdeep
  obtain ⟨hg2, -⟩ := deep_val hgf hβ1 hx hdeep h2zdeep
  exact (ratW_iff_valY hfun c z (ratioY Y c z)).mpr ⟨hg1, hg2, hnz, rfl⟩

/-- If `0 < x` is `M`-deep (`M ≥ 2`) then every point of the *inner* window
`[2x/M, M x/2]` is `2`-deep: the scale-`2` forbidden window sits inside the scale-`M` one. -/
theorem IsDeepR.two_of_window {B : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {M x t : ℝ}
    (hM : 2 ≤ M) (hx : 0 < x) (hdeep : IsDeepR B c M x)
    (ht1 : 2 * x / M ≤ t) (ht2 : t ≤ M * x / 2) :
    IsDeepR B c 2 t := by
  intro b hb hb'
  have hMpos : 0 < M := by linarith
  have hden : (0 : ℝ) < 2 * M := by positivity
  exact hdeep b hb ⟨by
      have h1 : x / (2 * M) ≤ t / 4 := by
        rw [div_le_iff₀ hden]
        have h3 : 2 * x ≤ t * M := by
          rw [div_le_iff₀ hMpos] at ht1
          linarith [ht1]
        nlinarith [h3]
      linarith [h1, hb'.1], by
      have h2 : 2 * 2 * t ≤ 2 * M * x := by nlinarith [ht2, hMpos, hx]
      linarith [hb'.2, h2]⟩

/-- **The doubling ratio at a deep point is positive.** -/
theorem deep_ratW_pos {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hst : ULPMStruct Y B₀) {c : Fin k → ℝ} {M x w : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (hdeep : IsDeepR B₀ c M x) (hrat : RatW Y c x w) : 0 < w := by
  have hM1 : 1 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  obtain ⟨-, -, -, hwl⟩ := (ratW_iff_valY hfun c x w).mp hrat
  rw [hwl]
  have h2M : 0 < 2 * M := by linarith
  have h1 : x / (2 * M) < x := by rw [div_lt_iff₀ h2M]; nlinarith [hx, hM]
  have h2 : x < 2 * M * x := by nlinarith [hx, hM]
  have h3 : x / (2 * M) < 2 * x := by rw [div_lt_iff₀ h2M]; nlinarith [hx, hM]
  have h4 : 2 * x < 2 * M * x := by nlinarith [hx, hM]
  exact deep_ratio_pos (Y := Y) (B₀ := B₀) hst (c := c) (β := M) (x := x) (t := x) hM1 hx hdeep
    ⟨h1, h2⟩ ⟨h3, h4⟩

/-! ## 2b. `RatW` values at a deep point are the `ratioY` value -/

/-- At a point where the fibre is a function, the (unique) doubling-ratio value `w` of `RatW`
is literally `ratioY Y c x = f_c(2x)/f_c(x)`. -/
theorem ratW_eq_ratioY {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {c : Fin k → ℝ} {x w : ℝ} (hrat : RatW Y c x w) : w = ratioY Y c x := by
  obtain ⟨y, y', hy, hy', hy0, hwy⟩ := hrat
  have h1 : y = valY Y c x := eq_valY hfun hy
  have h2 : y' = valY Y c (2 * x) := eq_valY hfun hy'
  have hne : valY Y c x ≠ 0 := by rw [← h1]; exact hy0
  have hw : valY Y c (2 * x) = w * valY Y c x := by rw [← h2, ← h1]; exact hwy.symm
  rw [ratioY, hw]
  exact (mul_div_cancel_right₀ w hne).symm

/-! ## 3. `BadScale` is downward closed in the scale -/

/-- A bad scale stays bad at every smaller positive scale. -/
theorem badScale_mono {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)} {E : Set ℝ}
    {ε M M' : ℝ} (hM : M ∈ BadScale Y B E ε) (hM' : 0 < M') (hle : M' ≤ M) :
    M' ∈ BadScale Y B E ε := by
  obtain ⟨hM0, c, x, w, hx, hdeep, hrat, hbad⟩ := hM
  exact ⟨hM', c, x, w, hx, hdeep.mono hM' hle hx, hrat, hbad⟩

/-- If the conclusion of `dev_decay_E` fails, then every scale `j + 2` is bad. -/
theorem badScale_all {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)} {E : Set ℝ}
    {ε : ℝ}
    (hcon : ∀ R : ℝ, ∃ M : ℝ, R ≤ M ∧ M ∈ BadScale Y B E ε) (j : ℕ) :
    ((j : ℝ) + 2) ∈ BadScale Y B E ε := by
  obtain ⟨M, hM, hbad⟩ := hcon ((j : ℝ) + 2)
  exact badScale_mono hbad (by positivity) hM


theorem dev_decay_E {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hst : Work.WilC4.ULPMStruct Y B₀)
    (E : Set ℝ) (hEfin : E.Finite)
    (N₀ : ℕ)
    (B : Set (Fin (k + 1) → ℝ)) (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B)
    (hsub : B₀ ⊆ B) (hsubE : Work.WilC4.Route.ClusterE Y B ⊆ E)
    (hBcard : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N₀)
    (hband : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b →
        (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
        (∀ x ∈ Set.Ioo a b, ∀ w : ℝ, Work.WilC4.RatW Y c x w → w ∉ Work.WilC4.Mid E) ∨
        (∃ mid ∈ Work.WilC4.Mid E, ∀ x ∈ Set.Ioo a b, ∀ w : ℝ,
          Work.WilC4.RatW Y c x w → w = mid))
    (hbdd : ∃ C : ℝ, ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      Work.WilC4.IsDeepR B c 2 x → Work.WilC4.RatW Y c x w → |w| ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ M : ℝ, R ≤ M →
      M ∉ Work.WilC4.BadScale Y B E ε := by
  have hgf : GoodFibre Y B := goodFibre_mono hst.1 hsub
  have hstB : ULPMStruct Y B :=
    ⟨hgf, fun c a b hab hfree => hst.2 c a b hab (fun z hz hzB => hfree z hz (hsub hzB))⟩
  obtain ⟨Cbdd, hCbdd⟩ := hbdd
  obtain ⟨ρ₀, hρ₀E, hρ₀pos⟩ : ∃ ρ ∈ E, 0 < ρ := by
    obtain ⟨ρ, hρ, hpos⟩ := clusterE_pos hR hPB Y hY hfun B N₀ hBcard hgf
    exact ⟨ρ, hsubE hρ, hpos⟩
  intro ε hε
  by_contra hcon
  push_neg at hcon
  -- bad witnesses at every scale `j + 2`
  have hwit : ∀ j : ℕ, ∃ (c : Fin k → ℝ) (x w : ℝ), 0 < x ∧
      IsDeepR B c ((j : ℝ) + 2) x ∧ RatW Y c x w ∧
      ∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1| := by
    intro j
    obtain ⟨-, c, x, w, hx, hdeep, hrat, hbad⟩ := badScale_all hcon j
    exact ⟨c, x, w, hx, hdeep, hrat, hbad⟩
  choose c x w hx hdeep hrat hbad using hwit
  have hM2 : ∀ j : ℕ, (2 : ℝ) ≤ (j : ℝ) + 2 := by
    intro j
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hMpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 2 := fun j => by linarith [hM2 j]
  have hwin : ∀ j : ℕ, x j / (2 * ((j : ℝ) + 2)) < 2 * ((j : ℝ) + 2) * x j := by
    intro j
    have hx0 := hx j
    have h2M : (0 : ℝ) < 2 * ((j : ℝ) + 2) := by linarith [hMpos j]
    have h3 : 1 < (2 * ((j : ℝ) + 2)) * (2 * ((j : ℝ) + 2)) := by
      nlinarith [h2M]
    rw [div_lt_iff₀ h2M]
    nlinarith [hx0, h3]
  have hdich : ∀ j : ℕ,
      (∀ z ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2))) (2 * ((j : ℝ) + 2) * x j), ∀ u : ℝ,
        RatW Y (c j) z u → u ∉ Mid E) ∨
      (∃ mid ∈ Mid E, ∀ z ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2))) (2 * ((j : ℝ) + 2) * x j),
        ∀ u : ℝ, RatW Y (c j) z u → u = mid) :=
    fun j => hband (c j) _ _ (hwin j) (deep_free (hdeep j))
  set Jb : Set ℕ := {j | ∃ mid ∈ Mid E, ∀ z ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2)))
      (2 * ((j : ℝ) + 2) * x j), ∀ u : ℝ, RatW Y (c j) z u → u = mid} with hJbdef
  by_cases hBinf : Jb.Infinite
  · -- ===== CASE (B): the ratio is constantly a midpoint of `E` =====
    have hMidfin : (Mid E).Finite := mid_finite hEfin
    set A : ℝ → Set ℕ := fun m => {j | ∀ z ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2)))
        (2 * ((j : ℝ) + 2) * x j), ∀ u : ℝ, RatW Y (c j) z u → u = m} with hAdef
    have hcov : Jb ⊆ ⋃ m ∈ Mid E, A m := by
      intro j hj
      obtain ⟨m, hm, hmj⟩ := hj
      exact Set.mem_biUnion hm hmj
    obtain ⟨mid, hmid_mem, hmid_inf⟩ : ∃ m ∈ Mid E, (A m).Infinite := by
      by_contra hconB
      push_neg at hconB
      have hfin : (⋃ m ∈ Mid E, A m).Finite :=
        Set.Finite.biUnion hMidfin fun m hm => hconB m hm
      exact hBinf (Set.Finite.subset hfin hcov)
    have hmid_pos : 0 < mid := mid_pos hmid_mem
    -- `mid` is a cluster value
    have hmid_clu : mid ∈ ClusterE Y B := by
      intro N hN
      obtain ⟨j, hjA, hjgt⟩ := hmid_inf.exists_gt (2 * N)
      have hle : (N : ℝ) ≤ (j : ℝ) + 2 := by
        have h1 : (N : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
          have : N ≤ 2 * N := Nat.le_mul_of_pos_left N (by norm_num)
          exact_mod_cast this
        have h2 : ((2 * N : ℕ) : ℝ) ≤ (j : ℝ) := by
          exact_mod_cast (Nat.le_of_lt hjgt)
        push_cast at h1 h2
        linarith
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      refine ⟨c j, x j, hx j, ?_, ?_⟩
      · exact isDeep_iff_isDeepR.mpr (IsDeepR.mono (hdeep j) hNpos hle (hx j))
      · intro t ht1 ht2 y y' hy hy' hy0
        have hMp := hMpos j
        have hx0 := hx j
        have hNM : (N : ℝ) < (j : ℝ) + 2 := by
          have h1 : N < 2 * N := by omega
          have h2 : ((2 * N : ℕ) : ℝ) ≤ (j : ℝ) := by
            exact_mod_cast (Nat.le_of_lt hjgt)
          have h3 : ((N : ℕ) : ℝ) < ((2 * N : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at h2 h3
          linarith
        -- `t` lies in the inner deep window
        have htmem : t ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2))) (((j : ℝ) + 2) * x j) := by
          have hM2pos : (0 : ℝ) < 2 * ((j : ℝ) + 2) := by linarith
          constructor
          · have hN2M : (N : ℝ) < 2 * ((j : ℝ) + 2) := by linarith [hNM]
            have h1 : x j / (2 * ((j : ℝ) + 2)) < x j / (N : ℝ) :=
              div_lt_div_of_pos_left hx0 hNpos hN2M
            linarith [ht1]
          · have h1 : x j * (N : ℝ) < x j * ((j : ℝ) + 2) :=
              mul_lt_mul_of_pos_left hNM hx0
            linarith [ht2]
        have hrat2 : RatW Y (c j) t (ratioY Y (c j) t) :=
          ratW_ratioY_of_deep hfun hgf (by linarith [hM2 j] : 1 < (j : ℝ) + 2) hx0
            (hdeep j) htmem
        have htwin : t ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2))) (2 * ((j : ℝ) + 2) * x j) :=
          ⟨htmem.1, by nlinarith [htmem.2, hx0, hMp]⟩
        have hEq : ratioY Y (c j) t = mid := hjA t htwin (ratioY Y (c j) t) hrat2
        have h1 : y = valY Y (c j) t := eq_valY hfun hy
        have h2 : y' = valY Y (c j) (2 * t) := eq_valY hfun hy'
        have hratio : y' / y = ratioY Y (c j) t := by
          rw [h1, h2]
          rfl
        rw [hratio, hEq, sub_self, abs_zero]
        positivity
    -- so the witness is not bad, contradicting `hbad`
    have hmidE : mid ∈ E := hsubE hmid_clu
    obtain ⟨j, hjA⟩ := hmid_inf.nonempty
    exact absurd (hbad j mid hmidE hmid_pos) (by
      have hEq : w j = mid := by
        have hxwin : x j ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2))) (2 * ((j : ℝ) + 2) * x j) := by
          have hMp := hMpos j
          have hx0 := hx j
          refine ⟨?_, ?_⟩
          · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * ((j : ℝ) + 2))]
            nlinarith [hx0, hMp]
          · nlinarith [hx0, hMp]
        exact hjA (x j) hxwin (w j) (hrat j)
      rw [hEq, div_self (ne_of_gt hmid_pos), sub_self, abs_zero]
      linarith)
  · -- ===== CASE (A): the ratio avoids `Mid E` outside a finite set =====
    have hBfin : Jb.Finite := Set.not_infinite.mp hBinf
    obtain ⟨n, hn⟩ := hBfin.bddAbove
    have havoid : ∀ j : ℕ, n < j → (∀ z ∈ Set.Ioo (x j / (2 * ((j : ℝ) + 2)))
        (2 * ((j : ℝ) + 2) * x j), ∀ u : ℝ, RatW Y (c j) z u → u ∉ Mid E) := by
      intro j hj
      rcases hdich j with h | h
      · exact h
      · exact absurd hj (not_lt.mpr (hn h))
    have hzero : (0 : ℝ) ∉ ClusterE Y B :=
      zero_not_mem_clusterE_aux hR hOM hPB Y hY hfun B hB hstB
    obtain ⟨RA, hRA⟩ := caseA_bad_bounded_zero (k := k) (Y := Y) (B := B) (E := E) hfun hgf
      hEfin ⟨ρ₀, hρ₀E, hρ₀pos⟩ hsubE hzero hCbdd ε hε
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, max RA ((n : ℝ)) ≤ (k' : ℝ) := exists_nat_ge _
    set j : ℕ := max (n + 1) k' with hjdef
    have hjn : n < j := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_left _ _)
    have hjRA : RA ≤ (j : ℝ) + 2 := by
      have h1 : RA ≤ (k' : ℝ) := le_trans (le_max_left _ _) hk'
      have h2 : (k' : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast (le_max_right (n + 1) k')
      linarith
    exact hRA ((j : ℝ) + 2) (c j) (x j) (w j) hjRA (hx j) (hdeep j) (hrat j)
      (havoid j hjn) (normRatio_mono hfun hstB (hM2 j) (hx j) (hdeep j)) (hbad j)

end Work.WilC4

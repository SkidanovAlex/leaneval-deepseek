import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-! ## Two elementary real-analysis tools

The extraction below needs an equicontinuity modulus for a family whose second-order partials are
only **Hölder** of exponent `β > 0` (not Lipschitz).  The two lemmas here supply exactly that:
`x ↦ x ^ β` tends to `0` at `0⁺` for `β > 0`, and consequently `K * δ ^ β` can be made smaller
than any prescribed `ε > 0`. -/

/-- `x ^ β → 0` as `x → 0⁺`, for `β > 0`.  Derived from the negative-exponent limit
`tendsto_rpow_neg_nhdsGT_zero` of Mathlib by taking inverses. -/
theorem tendsto_rpow_nhdsGT_zero_of_pos {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto (fun x : ℝ => x ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-β)) (𝓝[>] (0 : ℝ)) Filter.atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  refine (h1.inv_tendsto_atTop).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (x ^ (-β))⁻¹ = x ^ β
  rw [Real.rpow_neg (le_of_lt (show (0 : ℝ) < x from hx)) β, inv_inv]

/-- For `β > 0` and `ε > 0` the quantity `K * δ ^ β` can be made smaller than `ε` by a suitable
positive `δ`, for *every* real `K`. -/
theorem exists_mul_rpow_lt {K β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ K * δ ^ β < ε := by
  by_cases hK : K ≤ 0
  · exact ⟨1, one_pos, by rw [Real.one_rpow, mul_one]; linarith⟩
  · have hKpos : 0 < K := not_le.mp hK
    have hlim : Filter.Tendsto (fun x : ℝ => K * x ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_rpow_nhdsGT_zero_of_pos hβ)
    have hmem : {x : ℝ | K * x ^ β < ε} ∈ 𝓝[>] (0 : ℝ) :=
      hlim.eventually (Iio_mem_nhds (a := ε) (b := 0) hε)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hmem
    have hr2 : (0 : ℝ) < r / 2 := by linarith
    have hmem2 : r / 2 ∈ Metric.ball (0 : ℝ) r ∩ Set.Ioi 0 := by
      refine ⟨?_, hr2⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
      linarith
    exact ⟨r / 2, hr2, hrsub hmem2⟩

/-! ## Uniform convergence transferred across a pointwise equality on the set -/

/-- If `G n` agrees with `F n` on `s` and `F ·` converges uniformly to `f` on `s`, then so does
`G ·`.  (`G` is the *unclamped* jet family and `F` the clamped one.) -/
theorem wJet_tendstoUniformlyOn_congr {ι α : Type*} [PseudoMetricSpace α]
    {F G : ι → α → ℝ} {f : α → ℝ} {l : Filter ι} {s : Set α}
    (h : TendstoUniformlyOn F f l s) (hFG : ∀ n x, x ∈ s → G n x = F n x) :
    TendstoUniformlyOn G f l s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn x hx
  rw [hFG n x hx]
  exact hn x hx

/-! ## The extraction -/

/-- **Subsequence extraction for the six within-partials of a `C²`-Hölder family on a closed
box.**  Given `Hn := Function.uncurry (H n)`, jointly `C²` on `cbox a b`, with

* the operator norms of `iteratedFDerivWithin ℝ k` (`k ≤ 2`) bounded by `K` on the box,
* the order-`2` within-derivatives Hölder of exponent `β > 0` with constant `K`,
* the first-order within-partials `wPz`, `wPth` Lipschitz with constant `K`,

there is a strictly monotone `φ` and a limit `g` of the six components of
`wJet (cbox a b) (uncurry (H (φ n)))` which is uniform on the box and whose limit is continuous
there.  The proof clamps the angle into `[0,π/2]` (the retraction `clampB` of `WithinVec`), which
turns the family into an equicontinuous family of *continuous* functions on the open
neighbourhood `U ⊃ cbox a b`; Arzelà–Ascoli
(`exists_subseq_tendstoLocallyUniformlyOn_fin`) then gives the subsequence, which is restricted
back to the box (where `clampB` is the identity). -/
theorem wJet_subseq_extract {H : ℕ → ℝ → ℝ → ℝ} {a b K β : ℝ} (hab : a < b) (hβ : 0 < β)
    (hsm : ∀ n, ContDiffOn ℝ 2 (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b))
    (hb : ∀ n k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDerivWithin ℝ k (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b) p‖ ≤ K)
    (hh : ∀ n, ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b) p
        - iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (Work.FTS_EllLimOK.cbox a b) q‖
        ≤ K * ‖p - q‖ ^ β)
    (hlip : ∀ n, ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      |Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) p
          - Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) q|
        ≤ K * ‖p - q‖ ∧
      |Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) p
          - Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) q|
        ≤ K * ‖p - q‖) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ × ℝ → (Fin 6 → ℝ),
      (∀ m : Fin 6, TendstoUniformlyOn
        (fun n p => Work.FTS_EllLimOK.BoxDataH.wJet (Work.FTS_EllLimOK.cbox a b)
          (Function.uncurry (H (φ n))) p m)
        (fun p => g p m) Filter.atTop (Work.FTS_EllLimOK.cbox a b)) ∧
      ContinuousOn g (Work.FTS_EllLimOK.cbox a b) := by
  classical
  have hab' : a ≤ b := le_of_lt hab
  -- ## 0. The box is nonempty, hence `0 ≤ K`
  have hK0 : 0 ≤ K := by
    have hmem : (((a, 0) : ℝ × ℝ)) ∈ Work.FTS_EllLimOK.cbox a b :=
      mem_cbox.mpr ⟨⟨le_rfl, hab'⟩, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩
    exact le_trans (norm_nonneg _) (hb 0 0 (by norm_num : (0 : ℕ) ≤ 2) (a, 0) hmem)
  -- ## 1. An open neighbourhood `U` of the box
  set U : Set (ℝ × ℝ) := Set.Ioo (a - 1) (b + 1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hboxcpt : IsCompact (Work.FTS_EllLimOK.cbox a b) := isCompact_Icc.prod isCompact_Icc
  have hboxU : Work.FTS_EllLimOK.cbox a b ⊆ U := by
    intro p hp
    rw [mem_cbox] at hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  have hmemB : ∀ p : ℝ × ℝ, clampB a b p ∈ Work.FTS_EllLimOK.cbox a b :=
    fun p => clampB_mem_cbox hab'
  -- ## 2. The clamped jet family
  set F : ℕ → ℝ × ℝ → (Fin 6 → ℝ) := fun n p =>
    wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p) with hFdef
  -- boundedness
  have hFbdd : ∀ n : ℕ, ∀ p : ℝ × ℝ, ‖F n p‖ ≤ K := by
    intro n p
    exact norm_wJet_le (s := Work.FTS_EllLimOK.cbox a b)
      (F := Function.uncurry (H n)) (p := clampB a b p) (hmemB p) (hb n)
  -- ## 3. Equicontinuity of the clamped family
  have heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p : ℝ × ℝ, ∀ q : ℝ × ℝ,
      dist p q < δ → ‖F n p - F n q‖ < ε := by
    intro ε hε
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_mul_rpow_lt (K := K) (β := β) (ε := ε / 2) hβ (by linarith)
    refine ⟨min (ε / (2 * (K + 1))) δ₂, lt_min (div_pos hε (by linarith)) hδ₂pos, ?_⟩
    intro n p q hpq
    have hpq1 : dist p q < ε / (2 * (K + 1)) := lt_of_lt_of_le hpq (min_le_left _ _)
    have hpq2 : dist p q < δ₂ := lt_of_lt_of_le hpq (min_le_right _ _)
    have hp' := hmemB p
    have hq' := hmemB q
    have hdist : ‖clampB a b p - clampB a b q‖ ≤ dist p q := by
      rw [← dist_eq_norm]
      exact dist_clampB_le a b p q
    -- the `K`-Lipschitz bound for the two first-order components
    have hKstep : K * (ε / (2 * (K + 1))) ≤ ε / 2 := by
      have hK1 : K / (K + 1) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < K + 1)]
        linarith
      calc K * (ε / (2 * (K + 1))) = (ε / 2) * (K / (K + 1)) := by
            field_simp
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hK1 (by linarith)
        _ = ε / 2 := by ring
    have hcomp : ∀ m : Fin 6, |F n p m - F n q m| ≤ ε / 2 := by
      intro m
      fin_cases m
      · -- `m = 0`: the `z`-partial, Lipschitz
        have h := (hlip n (clampB a b p) hp' (clampB a b q) hq').1
        change |wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
            - wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)| ≤ ε / 2
        calc |wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
              - wPz (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)|
            ≤ K * ‖clampB a b p - clampB a b q‖ := h
          _ ≤ K * dist p q := mul_le_mul_of_nonneg_left hdist hK0
          _ ≤ K * (ε / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left (le_of_lt hpq1) hK0
          _ ≤ ε / 2 := hKstep
      · -- `m = 1`: the `θ`-partial, Lipschitz
        have h := (hlip n (clampB a b p) hp' (clampB a b q) hq').2
        change |wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
            - wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)| ≤ ε / 2
        calc |wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
              - wPth (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b q)|
            ≤ K * ‖clampB a b p - clampB a b q‖ := h
          _ ≤ K * dist p q := mul_le_mul_of_nonneg_left hdist hK0
          _ ≤ K * (ε / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left (le_of_lt hpq1) hK0
          _ ≤ ε / 2 := hKstep
      · -- `m = 2`: `∂_z∂_z`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (2 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
      · -- `m = 3`: `∂_θ∂_z`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (3 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
      · -- `m = 4`: `∂_z∂_θ`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (4 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
      · -- `m = 5`: `∂_θ∂_θ`, Hölder
        have h := abs_wJet_sub_le_hölder (s := Work.FTS_EllLimOK.cbox a b)
          (F := Function.uncurry (H n)) (K := K) (β := β) (hh n) hK0
          (clampB a b p) hp' (clampB a b q) hq' (5 : Fin 6) (by norm_num)
        exact le_trans h (le_trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hβ)) hK0)
          (le_trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (dist_nonneg) (le_of_lt hpq2) (le_of_lt hβ)) hK0)
            (le_of_lt hδ₂)))
    have hnorm : ‖F n p - F n q‖ ≤ ε / 2 := by
      rw [pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2)]
      intro m
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact hcomp m
    linarith
  -- ## 4. Arzelà–Ascoli
  obtain ⟨φ, hφ, G, hGlim⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin (k := 6) hUopen
      (F := F) (fun _ _ _ => ⟨K, fun n p _ => hFbdd n p⟩)
      (fun _ _ _ ε hε => by
        obtain ⟨δ, hδpos, hδ⟩ := heqc ε hε
        exact ⟨δ, hδpos, fun n p _ q _ hpq => hδ n p q hpq⟩)
  -- ## 5. Continuity of the members, hence of the limit
  have hjetcont : ∀ n : ℕ, ContinuousOn
      (fun q : ℝ × ℝ =>
        wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) q)
      (Work.FTS_EllLimOK.cbox a b) :=
    fun n => continuousOn_pi.mpr (continuousOn_wJet hab (hsm n))
  have hFcont : ∀ n : ℕ, ContinuousOn (F n) (Work.FTS_EllLimOK.cbox a b) := by
    intro n
    refine (hjetcont n).congr (fun p hp => ?_)
    change wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) (clampB a b p)
      = wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H n)) p
    rw [clampB_eq_of_mem_cbox hp]
  -- ## 6. Assembly
  have hunif : TendstoUniformlyOn (fun n p => F (φ n) p) G Filter.atTop
      (Work.FTS_EllLimOK.cbox a b) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen).mp hGlim
      (Work.FTS_EllLimOK.cbox a b) hboxU hboxcpt
  have hGcont : ContinuousOn G (Work.FTS_EllLimOK.cbox a b) :=
    hunif.continuousOn (Frequently.of_forall fun n => hFcont (φ n))
  refine ⟨φ, hφ, G, ?_, hGcont⟩
  intro m
  refine wJet_tendstoUniformlyOn_congr
    (F := fun n p => F (φ n) p m) (tendstoUniformlyOn_jetVec_component hunif m) ?_
  intro n p hp
  change wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H (φ n))) p m
    = wJet (Work.FTS_EllLimOK.cbox a b) (Function.uncurry (H (φ n))) (clampB a b p) m
  rw [clampB_eq_of_mem_cbox hp]

end Work.FTS_EllLimOK.BoxDataH

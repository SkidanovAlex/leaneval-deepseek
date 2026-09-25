/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Seeley extension is `C^m` on the slab

This file proves `Work.NN.Seeley.seeleyEV_contDiffOn`: the Seeley extension `seeleyEV a b δ g` of a
function `g` which is smooth on the slab `{-δ < p.2}` is `C^m` on the whole slab, for every `m`.

The strategy is that of `Work.NN.Final.contDiffOn_glue`: away from the hyperplane `{p.2 = 0}` the
extension agrees with a function which is smooth there (`g` above the hyperplane and the locally
finite Seeley sum `seeleySumV` below it), while at a point `p` of the hyperplane one has to check
that the iterated derivatives of the extension have a limit along the punctured neighbourhood of
`p`.  From above this is the continuity of the derivatives of `g`; from below it is the fact that
the iterated derivatives of the Seeley sum tend to the iterated derivatives of `g` at `p`, which is
the jet-matching property of the Seeley extension and follows from the multilinear moment identity
`seeley_moment_tensor`.
-/
import Mathlib
import Submission.Work.NN.Seeley.Setup
import Submission.Work.NN.Seeley.ProdBounds
import Submission.Work.NN.Seeley.gDN_bilinear_le
import Submission.Work.NN.Seeley.iteratedFDeriv_seeleySumV_of_neg
import Submission.Work.NN.Seeley.seeley_moment_tensor
import Submission.Work.NN.Final.contDiffOn_glue

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

namespace Work.NN.Seeley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Evaluation of multilinear maps -/

/-- Evaluation of a continuous multilinear map at a fixed vector, as a continuous linear map. -/
def seeleyEvalCLM {k : ℕ} (v : Fin k → X × ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun Ψ => Ψ v
      map_add' := fun a b => rfl
      map_smul' := fun c a => by simp }
    (∏ i, ‖v i‖)
    (fun Ψ => by
      calc ‖Ψ v‖ ≤ ‖Ψ‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm Ψ v
        _ = (∏ i, ‖v i‖) * ‖Ψ‖ := mul_comm _ _)

@[simp] lemma seeleyEvalCLM_apply {k : ℕ} (v : Fin k → X × ℝ)
    (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) :
    seeleyEvalCLM v Ψ = Ψ v := rfl

/-- Real scalar multiplication viewed as a bilinear map scaled by `k`: `(r, z) ↦ (k * r) • z`. -/
def seeleyScalarBilin' (k : ℝ) : ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (k • ContinuousLinearMap.id ℝ ℝ)

@[simp] lemma seeleyScalarBilin'_apply (k r : ℝ) (z : ℂ) :
    seeleyScalarBilin' k r z = (k * r) • z := by
  simp only [seeleyScalarBilin', ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma norm_seeleyScalarBilin'_le (k : ℝ) : ‖seeleyScalarBilin' k‖ ≤ |k| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg k) fun r => ?_
  show ‖(seeleyScalarBilin' k r : ℂ →L[ℝ] ℂ)‖ ≤ |k| * ‖r‖
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  rw [seeleyScalarBilin'_apply]
  calc ‖(k * r) • z‖ ≤ ‖(k * r : ℝ)‖ * ‖z‖ := norm_smul_le _ _
    _ = (|k| * ‖r‖) * ‖z‖ := by rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]

/-- Norm bound for the pull-back of a multilinear map along the shear `seeleyLam c`. -/
lemma norm_compContinuousLinearMap_seeleyLam_le {k : ℕ}
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) (c : ℝ) :
    ‖Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) c)‖
      ≤ ‖Φ‖ * (max 1 |c|) ^ k :=
  Work.NN.Final.norm_compContinuousLinearMap_const_le Φ c

/-- **The multilinear moment identity at the level of maps.**  The weighted sum of the multilinear
maps obtained from `Φ` by precomposing with all the shears `seeleyLam (-(b m))` is `Φ` itself. -/
theorem tsum_smul_compContinuousLinearMap_seeleyLam_eq {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {k : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) :
    (∑' m, (a m) •
      Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))) = Φ := by
  have hb0 : ∀ m, (0 : ℝ) ≤ b m := fun m => le_trans zero_le_one (hb1 m)
  have habs : ∀ m, max 1 |-(b m)| = b m := by
    intro m
    rw [abs_neg, abs_of_nonneg (hb0 m)]
    exact max_eq_right (hb1 m)
  have hbnd : ∀ m : ℕ,
      ‖(a m) • Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
        ≤ |a m| * (b m) ^ k * ‖Φ‖ := by
    intro m
    rw [norm_smul, Real.norm_eq_abs]
    calc |a m| * ‖Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
        ≤ |a m| * (‖Φ‖ * (max 1 |-(b m)|) ^ k) :=
          mul_le_mul_of_nonneg_left (norm_compContinuousLinearMap_seeleyLam_le Φ (-(b m)))
            (abs_nonneg _)
      _ = |a m| * (b m) ^ k * ‖Φ‖ := by rw [habs]; ring
  have hsumble : Summable fun m : ℕ =>
      (a m) • Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) := by
    refine Summable.of_norm_bounded ((hsum k).mul_right ‖Φ‖) hbnd
  refine ContinuousMultilinearMap.ext fun v => ?_
  change seeleyEvalCLM v
      (∑' m, (a m) •
        Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))) = Φ v
  rw [ContinuousLinearMap.map_tsum (seeleyEvalCLM v) hsumble]
  have hterm : ∀ m : ℕ, seeleyEvalCLM v ((a m) •
      Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))))
      = (a m) • Φ (fun j => ((v j).1, -(b m) * (v j).2)) := by
    intro m
    rw [seeleyEvalCLM_apply, smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl
  rw [tsum_congr hterm]
  exact seeley_moment_tensor ha hsum k Φ v

/-! ## Tails of summable series -/

/-- For a summable nonnegative family `c` and scales `b → ∞`, the tail sums over `{m | R ≤ b m}`
are eventually as small as desired. -/
lemma exists_tsum_indicator_le {b c : ℕ → ℝ} (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hc : Summable c) (hc0 : ∀ m, 0 ≤ c m) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ R' : ℝ, R ≤ R' → (∑' m : ℕ, if R' ≤ b m then c m else 0) ≤ ε := by
  have hsumble_if : ∀ R : ℝ, Summable fun m : ℕ => if R ≤ b m then c m else 0 := by
    intro R
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : R ≤ b m
    · rw [if_pos h, abs_of_nonneg (hc0 m)]
    · rw [if_neg h, abs_zero]
      exact hc0 m
  have hsumble_n : ∀ R : ℝ, Summable fun m : ℕ => if R ≤ (m : ℝ) then c m else 0 := by
    intro R
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : R ≤ (m : ℝ)
    · rw [if_pos h, abs_of_nonneg (hc0 m)]
    · rw [if_neg h, abs_zero]
      exact hc0 m
  have hkey : ∀ N : ℕ, (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then c m else 0)
      = (∑' m, c m) - ∑ m ∈ Finset.range N, c m := by
    intro N
    have h1 : Summable fun m : ℕ => if (N : ℝ) ≤ (m : ℝ) then c m else 0 := hsumble_n N
    have h2 : Summable fun m : ℕ => if (N : ℝ) ≤ (m : ℝ) then (0 : ℝ) else c m := by
      refine Summable.of_norm_bounded hc fun m => ?_
      rw [Real.norm_eq_abs]
      by_cases h : (N : ℝ) ≤ (m : ℝ)
      · rw [if_pos h, abs_zero]
        exact hc0 m
      · rw [if_neg h, abs_of_nonneg (hc0 m)]
    have hadd := h1.tsum_add h2
    have hfun : (fun m : ℕ => (if (N : ℝ) ≤ (m : ℝ) then c m else 0)
        + (if (N : ℝ) ≤ (m : ℝ) then (0 : ℝ) else c m)) = fun m => c m := by
      funext m
      by_cases h : (N : ℝ) ≤ (m : ℝ) <;> simp [h]
    rw [hfun] at hadd
    have h2val : (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then (0 : ℝ) else c m)
        = ∑ m ∈ Finset.range N, c m := by
      rw [tsum_eq_sum (s := Finset.range N)]
      · refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_range] at hm
        rw [if_neg (not_le.mpr (by exact_mod_cast hm))]
      · intro m hm
        rw [Finset.mem_range, not_lt] at hm
        rw [if_pos (by exact_mod_cast hm)]
    rw [h2val] at hadd
    linarith
  have htend : Filter.Tendsto (fun N : ℕ => (∑' m, c m) - ∑ m ∈ Finset.range N, c m)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, c m) Filter.atTop
        (nhds (∑' m, c m)) := hc.hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := (∑' m, c m))).sub h1
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  refine ⟨(∑ m ∈ Finset.range N, |b m|) + 1, fun R' hR' => ?_⟩
  have hle : (∑' m : ℕ, if R' ≤ b m then c m else 0)
      ≤ ∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then c m else 0 := by
    refine Summable.tsum_le_tsum (fun m => ?_) (hsumble_if R') (hsumble_n N)
    by_cases h : R' ≤ b m
    · rw [if_pos h]
      by_cases h2 : (N : ℝ) ≤ (m : ℝ)
      · rw [if_pos h2]
      · rw [if_neg h2]
        exfalso
        have hb_le : b m ≤ |b m| := le_abs_self _
        have hmem : m ∈ Finset.range N := Finset.mem_range.mpr (Nat.cast_lt.mp (not_le.mp h2))
        have hle' : |b m| ≤ ∑ i ∈ Finset.range N, |b i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (b i)) hmem
        have hlt : (∑ i ∈ Finset.range N, |b i|) < R' := by linarith
        linarith
    · rw [if_neg h]
      by_cases h2 : (N : ℝ) ≤ (m : ℝ)
      · rw [if_pos h2]
        exact hc0 m
      · rw [if_neg h2]
  rw [hkey N] at hle
  have hval := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hval
  have hnonneg : 0 ≤ (∑' m, c m) - ∑ m ∈ Finset.range N, c m := by
    rw [← hkey N]
    exact tsum_nonneg fun m => by
      by_cases h : (N : ℝ) ≤ (m : ℝ) <;> simp [h, hc0 m]
  rw [abs_of_nonneg hnonneg] at hval
  linarith

/-! ## A local tube bound -/

/-- A continuous real-valued function on `Y × ℝ` is bounded on a tube `{y | dist y y₀ < η} × K`
for a compact `K ⊆ ℝ` (no compactness assumption on `Y` is needed). -/
lemma exists_tube_bound_le {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Y × ℝ → ℝ} (hf : Continuous f) (y₀ : Y) {K : Set ℝ} (hK : IsCompact K) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, ∀ y : Y, dist y y₀ < η → ∀ t ∈ K, f (y, t) ≤ C := by
  classical
  rcases Set.eq_empty_or_nonempty K with hK0 | hKne
  · exact ⟨1, one_pos, 0, fun y _ t ht => absurd (hK0 ▸ ht : t ∈ (∅ : Set ℝ))
      (Set.notMem_empty t)⟩
  have hmain : ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (t ∈ K → ∀ z : Y × ℝ, dist z (y₀, t) < δ → f z ≤ f (y₀, t) + 1) := by
    intro t
    by_cases ht : t ∈ K
    · obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hf.continuousAt 1 one_pos
      refine ⟨δ, hδ0, fun _ z hz => ?_⟩
      have h1 : dist (f z) (f (y₀, t)) < 1 := hδ hz
      rw [Real.dist_eq] at h1
      linarith [(abs_lt.mp h1).2]
    · exact ⟨1, one_pos, fun h => absurd h ht⟩
  choose δ hδpos hδbd using hmain
  have hcover : K ⊆ ⋃ t, (if t ∈ K then Metric.ball t (δ t / 2) else ∅) := by
    intro t ht
    rw [Set.mem_iUnion]
    refine ⟨t, ?_⟩
    rw [ite_eq_left ht]
    exact Metric.mem_ball_self (by linarith [hδpos t])
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun t : ℝ => if t ∈ K then Metric.ball t (δ t / 2) else ∅)
    (fun t => by by_cases ht : t ∈ K <;> simp [ht, Metric.isOpen_ball]) hcover
  have hFne : F.Nonempty := by
    obtain ⟨t, ht⟩ := hKne
    obtain ⟨i, hiF, _⟩ := Set.mem_iUnion₂.mp (hF ht)
    exact ⟨i, hiF⟩
  refine ⟨F.inf' hFne (fun t => δ t / 4), ?_, F.sup' hFne (fun t => f (y₀, t) + 1), ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro t _
    linarith [hδpos t]
  · intro y hy t ht
    obtain ⟨i, hiF, hti⟩ := Set.mem_iUnion₂.mp (hF ht)
    have hiK : i ∈ K := by
      by_contra hi
      rw [ite_eq_right hi] at hti
      exact hti
    rw [ite_eq_left hiK] at hti
    have hti' : dist t i < δ i / 2 := Metric.mem_ball.mp hti
    have hinf : F.inf' hFne (fun t => δ t / 4) ≤ δ i / 4 := Finset.inf'_le (fun t => δ t / 4) hiF
    have hy' : dist y y₀ < δ i / 4 := lt_of_lt_of_le hy hinf
    have hδi : 0 < δ i := hδpos i
    have hdist : dist (y, t) (y₀, i) < δ i := by
      rw [Prod.dist_eq]
      exact max_lt (by linarith) (by linarith)
    have hbound := hδbd i hiK (y, t) hdist
    calc f (y, t) ≤ f (y₀, i) + 1 := hbound
      _ ≤ F.sup' hFne (fun t => f (y₀, t) + 1) := Finset.le_sup' (fun t => f (y₀, t) + 1) hiF

/-! ## The `gDN` of a singleton -/

lemma gDN_singleton {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (i : ℕ) (f : Y → A) (x : Y) :
    Work.NN.Final.gDN i f {x} = ENNReal.ofReal ‖iteratedFDeriv ℝ i f x‖ := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
  · exact Work.NN.Final.le_gDN i (Set.mem_singleton x)

/-! ## The individual Seeley terms -/

/-- If `b m * |x.2|` is large enough, the `m`-th Seeley term vanishes identically on a neighbourhood
of `x` (so its iterated derivatives at `x` vanish). -/
lemma seeleyTV_eventuallyEq_zero {a b : ℕ → ℝ} {δ : ℝ} {g : X × ℝ → ℂ} {m : ℕ} {x : X × ℝ}
    (hb0 : 0 ≤ b m) (hx : x.2 < 0) (h : 4 ≤ b m * |x.2|) :
    Work.NN.Final.seeleyTV a b δ g m =ᶠ[𝓝 x] 0 := by
  have hxabs : 0 < |x.2| := abs_pos.mpr (ne_of_lt hx)
  have hneigh : {y : X × ℝ | y.2 < x.2 / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const) ?_
    change x.2 < x.2 / 2
    linarith
  filter_upwards [hneigh] with y hy
  have hyabs : |x.2| / 2 ≤ |y.2| := by
    rw [abs_of_neg hx, abs_of_neg (by linarith : y.2 < 0)]
    linarith
  have harg : 2 ≤ |-(b m) * y.2| := by
    rw [Work.NN.Final.abs_neg_mul, abs_of_nonneg hb0]
    nlinarith
  simp only [Work.NN.Final.seeleyTV, Work.NN.Final.seeleyCut_eq_zero harg, zero_smul, smul_zero,
    Pi.zero_apply]

/-- On the open lower half space the iterated derivatives of the Seeley sum reduce to a *finite*
sum of the derivatives of the terms. -/
lemma iteratedFDeriv_seeleySumV_eq_sum {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) (k : ℕ)
    {x : X × ℝ} (hx : x.2 < 0) {N : ℕ} (hN : ∀ m ≥ N, 4 ≤ b m * |x.2|) :
    iteratedFDeriv ℝ k (Work.NN.Final.seeleySumV a b δ g) x
      = ∑ m ∈ Finset.range N, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x := by
  rw [iteratedFDeriv_seeleySumV_of_neg hδ hb hbT hg k hx]
  refine tsum_eq_sum (s := Finset.range N) fun m hm => ?_
  simp only [Finset.mem_range, not_lt] at hm
  rw [iteratedFDeriv_congr_of_eventuallyEq
    (seeleyTV_eventuallyEq_zero (hb0 := by linarith [hb m]) hx (hN m hm)) k]
  simp

/-- When the shear argument `b m * x.2` is smaller than `1` the cutoff equals `1` near `x`, so the
`m`-th term agrees near `x` with `a m • (seeleyV δ g ∘ seeleyLam (-(b m)))`. -/
lemma iteratedFDeriv_seeleyTV_eq_of_mul_abs_snd_lt_one {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ}
    {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    (k : ℕ) {m : ℕ} {x : X × ℝ} (hb0 : 0 ≤ b m) (hx : b m * |x.2| < 1) :
    iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x
      = (a m) • (iteratedFDeriv ℝ k (Work.NN.Final.seeleyV δ g)
            (Work.NN.Final.seeleyLam (X := X) (-(b m)) x)).compContinuousLinearMap
            (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) := by
  have hcx : |(-(b m)) * x.2| < 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hb0]
    exact hx
  have hneigh : {y : X × ℝ | |(-(b m)) * y.2| < 1} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds (isOpen_lt (continuous_const.mul continuous_snd).abs continuous_const) ?_
    change |(-(b m)) * x.2| < 1
    exact hcx
  have h2 : Work.NN.Final.seeleyTV a b δ g m
      =ᶠ[𝓝 x] (fun y => (a m) • Work.NN.Final.seeleyV δ g (y.1, -(b m) * y.2)) := by
    filter_upwards [hneigh] with y hy
    have hcut : Work.NN.Final.seeleyCut (-(b m) * y.2) = 1 :=
      Work.NN.Final.seeleyCut_eq_one_of_abs_lt_one hy
    simp only [Work.NN.Final.seeleyTV, hcut, one_smul]
  rw [iteratedFDeriv_congr_of_eventuallyEq h2 k]
  have hVcd : ContDiff ℝ (k : WithTop ENat) (Work.NN.Final.seeleyV δ g) :=
    Work.NN.Final.seeleyV_contDiff_fin hδ hg k
  have hLcd : ContDiff ℝ (k : WithTop ENat) (Work.NN.Final.seeleyLam (X := X) (-(b m))) :=
    ContinuousLinearMap.contDiff _
  have hccont : ContDiffAt ℝ (k : WithTop ENat)
      (fun y : X × ℝ => Work.NN.Final.seeleyV δ g (y.1, -(b m) * y.2)) x :=
    (hVcd.comp hLcd).contDiffAt
  change iteratedFDeriv ℝ k
        ((a m) • (fun y : X × ℝ => Work.NN.Final.seeleyV δ g (y.1, -(b m) * y.2))) x
      = (a m) • (iteratedFDeriv ℝ k (Work.NN.Final.seeleyV δ g)
          (Work.NN.Final.seeleyLam (X := X) (-(b m)) x)).compContinuousLinearMap
          (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))
  rw [iteratedFDeriv_const_smul_apply hccont]
  rw [show (fun y : X × ℝ => Work.NN.Final.seeleyV δ g (y.1, -(b m) * y.2))
      = Work.NN.Final.seeleyV δ g ∘ (Work.NN.Final.seeleyLam (X := X) (-(b m))) from rfl]
  rw [Work.NN.Final.iteratedFDeriv_comp_seeleyLam hVcd (-(b m)) x]

/-- Pointwise Leibniz-type bound for the iterated derivatives of the `m`-th Seeley term. -/
lemma norm_iteratedFDeriv_seeleyTV_le {δ : ℝ} (hδ : 0 < δ) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m) (k m : ℕ) (x : X × ℝ) :
    ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) x‖
      ≤ |a m| * (b m) ^ k *
          (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j) *
          (∑ j ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ j (Work.NN.Final.seeleyV δ g)
              (Work.NN.Final.seeleyLam (X := X) (-(b m)) x)‖) := by
  set c : ℝ := -(b m) with hc
  have hb0 : 0 < b m := lt_of_lt_of_le zero_lt_one (hb1 m)
  have habsc : |c| = b m := by rw [hc, abs_neg, abs_of_nonneg hb0.le]
  have hmaxc : max 1 |c| = b m := by rw [habsc]; exact max_eq_right (hb1 m)
  have hVcd : ContDiff ℝ (k : WithTop ENat) (Work.NN.Final.seeleyV δ g) :=
    Work.NN.Final.seeleyV_contDiff_fin hδ hg k
  -- the two factors of the term
  set φ : X × ℝ → ℝ := fun y => Work.NN.Final.seeleyCut (c * y.2) with hφdef
  set ψ : X × ℝ → ℂ := fun y => Work.NN.Final.seeleyV δ g (Work.NN.Final.seeleyLam c y) with hψdef
  have hφcd : ContDiff ℝ (k : WithTop ENat) φ := by
    have h1 : ContDiff ℝ (k : WithTop ENat) (fun y : X × ℝ => c * y.2) := by fun_prop
    exact (Work.NN.Final.seeleyCut_contDiff.of_le (by simp)).comp h1
  have hψcd : ContDiff ℝ (k : WithTop ENat) ψ :=
    hVcd.comp (ContinuousLinearMap.contDiff (Work.NN.Final.seeleyLam (X := X) c))
  set B : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := seeleyScalarBilin' (a m) with hBdef
  have hBapp : ∀ (r : ℝ) (z : ℂ), B r z = (a m * r) • z := by
    intro r z
    rw [hBdef]
    exact seeleyScalarBilin'_apply (a m) r z
  have hBnorm : ‖B‖ ≤ |a m| := by
    rw [hBdef]
    exact norm_seeleyScalarBilin'_le (a m)
  have hTV : Work.NN.Final.seeleyTV a b δ g m = fun y : X × ℝ => B (φ y) (ψ y) := by
    funext y
    rw [hBapp]
    simp only [Work.NN.Final.seeleyTV, hφdef, hψdef]
    rw [Work.NN.Final.seeleyLam_apply, hc, smul_smul]
  -- the multilinear Leibniz bound
  have hb := B.norm_iteratedFDeriv_le_of_bilinear hφcd hψcd x le_rfl
  rw [hTV]
  refine hb.trans ?_
  -- bound the sum term by term
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j φ x‖ * ‖iteratedFDeriv ℝ (k - j) ψ x‖
        ≤ (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k *
            ‖iteratedFDeriv ℝ (k - j) (Work.NN.Final.seeleyV δ g) (Work.NN.Final.seeleyLam c x)‖ := by
    intro j hj
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : ‖iteratedFDeriv ℝ j φ x‖ ≤ Work.NN.Final.seeleyCutB j * (b m) ^ j := by
      have hg1 := Work.NN.Final.gDN_cutoff_le (X := X) (c := c) (i := j) (Ω := {x})
      rw [gDN_singleton] at hg1
      have h2' : ‖iteratedFDeriv ℝ j φ x‖ ≤ |c| ^ j * Work.NN.Final.seeleyCutB j :=
        (ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg (pow_nonneg (abs_nonneg c) j) (Work.NN.Final.seeleyCutB_nonneg j))).mp hg1
      calc ‖iteratedFDeriv ℝ j φ x‖ ≤ |c| ^ j * Work.NN.Final.seeleyCutB j := h2'
        _ = Work.NN.Final.seeleyCutB j * (b m) ^ j := by rw [habsc]; ring
    have h2 : ‖iteratedFDeriv ℝ (k - j) ψ x‖
        ≤ ‖iteratedFDeriv ℝ (k - j) (Work.NN.Final.seeleyV δ g) (Work.NN.Final.seeleyLam c x)‖
            * (b m) ^ (k - j) := by
      have hcd : ContDiff ℝ ((k - j : ℕ) : WithTop ENat) (Work.NN.Final.seeleyV δ g) :=
        Work.NN.Final.seeleyV_contDiff_fin hδ hg (k - j)
      rw [show ψ = (Work.NN.Final.seeleyV δ g) ∘ (Work.NN.Final.seeleyLam (X := X) c) from rfl,
        Work.NN.Final.iteratedFDeriv_comp_seeleyLam hcd c x]
      refine le_trans (Work.NN.Final.norm_compContinuousLinearMap_const_le _ c) ?_
      rw [hmaxc]
    have h3 : (0 : ℝ) ≤ (k.choose j : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ Work.NN.Final.seeleyCutB j := Work.NN.Final.seeleyCutB_nonneg j
    have h5 : (0 : ℝ) ≤ (b m) ^ j := pow_nonneg hb0.le j
    have h6 : (0 : ℝ) ≤ (b m) ^ (k - j) := pow_nonneg hb0.le _
    calc (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j φ x‖ * ‖iteratedFDeriv ℝ (k - j) ψ x‖
        ≤ (k.choose j : ℝ) * (Work.NN.Final.seeleyCutB j * (b m) ^ j)
            * (‖iteratedFDeriv ℝ (k - j) (Work.NN.Final.seeleyV δ g)
                (Work.NN.Final.seeleyLam c x)‖ * (b m) ^ (k - j)) := by
          gcongr
      _ = (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k *
            ‖iteratedFDeriv ℝ (k - j) (Work.NN.Final.seeleyV δ g) (Work.NN.Final.seeleyLam c x)‖ := by
          have hp : (b m) ^ j * (b m) ^ (k - j) = (b m) ^ k := by
            rw [← pow_add, Nat.add_sub_cancel' hjle]
          rw [← hp]
          ring
  have hBAD : ∀ j ∈ Finset.range (k + 1),
      (0 : ℝ) ≤ (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j φ x‖ * ‖iteratedFDeriv ℝ (k - j) ψ x‖ :=
    fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg (k.choose j)) (norm_nonneg _)) (norm_nonneg _)
  have hGOOD : ∀ j ∈ Finset.range (k + 1),
      (0 : ℝ) ≤ (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k *
        ‖iteratedFDeriv ℝ (k - j) (Work.NN.Final.seeleyV δ g) (Work.NN.Final.seeleyLam c x)‖ :=
    fun j _ => mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg (k.choose j))
      (Work.NN.Final.seeleyCutB_nonneg j)) (pow_nonneg hb0.le k)) (norm_nonneg _)
  calc ‖B‖ * ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j φ x‖ * ‖iteratedFDeriv ℝ (k - j) ψ x‖
      ≤ |a m| * ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k *
            ‖iteratedFDeriv ℝ (k - j) (Work.NN.Final.seeleyV δ g) (Work.NN.Final.seeleyLam c x)‖ := by
        exact mul_le_mul hBnorm (Finset.sum_le_sum hterm)
          (Finset.sum_nonneg hBAD) (abs_nonneg _)
    _ ≤ |a m| * ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k *
            (∑ i ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyV δ g) (Work.NN.Final.seeleyLam c x)‖) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (abs_nonneg _)
        have h6 : (0 : ℝ) ≤ (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg (k.choose j))
            (Work.NN.Final.seeleyCutB_nonneg j)) (pow_nonneg hb0.le k)
        refine mul_le_mul_of_nonneg_left ?_ h6
        exact Finset.single_le_sum
          (f := fun i => ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyV δ g)
            (Work.NN.Final.seeleyLam c x)‖)
          (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.sub_lt_succ k j))
    _ = |a m| * (b m) ^ k *
          (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j) *
          (∑ j ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ j (Work.NN.Final.seeleyV δ g)
              (Work.NN.Final.seeleyLam (X := X) (-(b m)) x)‖) := by
        rw [← hc]
        rw [show (∑ j ∈ Finset.range (k + 1),
              (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j * (b m) ^ k *
                (∑ i ∈ Finset.range (k + 1),
                  ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyV δ g)
                    (Work.NN.Final.seeleyLam c x)‖))
            = (∑ j ∈ Finset.range (k + 1),
                ((k.choose j : ℝ) * Work.NN.Final.seeleyCutB j)) *
              ((b m) ^ k * (∑ i ∈ Finset.range (k + 1),
                ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyV δ g)
                  (Work.NN.Final.seeleyLam c x)‖)) from by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ => by ring]
        ring

/-! ## Summability of the model family and tail bounds -/

/-- Norm bound for the `m`-th summand of the moment identity. -/
lemma norm_smul_compContinuousLinearMap_seeleyLam_le {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m)
    {k : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) (m : ℕ) :
    ‖(a m) • Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
      ≤ |a m| * (b m) ^ k * ‖Φ‖ := by
  have habs : max 1 |-(b m)| = b m := by
    rw [abs_neg, abs_of_nonneg (le_trans zero_le_one (hb1 m))]
    exact max_eq_right (hb1 m)
  rw [norm_smul, Real.norm_eq_abs]
  calc |a m| * ‖Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
      ≤ |a m| * (‖Φ‖ * (max 1 |-(b m)|) ^ k) :=
        mul_le_mul_of_nonneg_left (Work.NN.Final.norm_compContinuousLinearMap_const_le Φ (-(b m)))
          (abs_nonneg _)
    _ = |a m| * (b m) ^ k * ‖Φ‖ := by rw [habs]; ring

/-- The model family of the moment identity is summable. -/
lemma summable_smul_compContinuousLinearMap_seeleyLam {a b : ℕ → ℝ} (hb1 : ∀ m, 1 ≤ b m)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {k : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) :
    Summable fun m => (a m) •
      Φ.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) :=
  Summable.of_norm_bounded ((hsum k).mul_right ‖Φ‖)
    (fun m => norm_smul_compContinuousLinearMap_seeleyLam_le hb1 Φ m)

/-- Evaluation of a `tsum` of continuous multilinear maps. -/
lemma seeleyEvalCLM_tsum {k : ℕ} (v : Fin k → X × ℝ)
    {f : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ} (hf : Summable f) :
    (∑' m, f m) v = ∑' m, f m v := by
  have h := ContinuousLinearMap.map_tsum (seeleyEvalCLM v) hf
  simpa only [seeleyEvalCLM_apply] using h

/-- The tail sums of a summable nonnegative sequence over `{m | N ≤ m}` are small. -/
lemma exists_tsum_nat_tail_le {c : ℕ → ℝ} (hc : Summable c) (hc0 : ∀ m, 0 ≤ c m) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then c m else 0) ≤ ε := by
  have hsumble_n : ∀ R : ℝ, Summable fun m : ℕ => if R ≤ (m : ℝ) then c m else 0 := by
    intro R
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : R ≤ (m : ℝ)
    · rw [if_pos h, abs_of_nonneg (hc0 m)]
    · rw [if_neg h, abs_zero]
      exact hc0 m
  have hkey : ∀ N : ℕ, (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then c m else 0)
      = (∑' m, c m) - ∑ m ∈ Finset.range N, c m := by
    intro N
    have h1 : Summable fun m : ℕ => if (N : ℝ) ≤ (m : ℝ) then c m else 0 := hsumble_n N
    have h2 : Summable fun m : ℕ => if (N : ℝ) ≤ (m : ℝ) then (0 : ℝ) else c m := by
      refine Summable.of_norm_bounded hc fun m => ?_
      rw [Real.norm_eq_abs]
      by_cases h : (N : ℝ) ≤ (m : ℝ)
      · rw [if_pos h, abs_zero]
        exact hc0 m
      · rw [if_neg h, abs_of_nonneg (hc0 m)]
    have hadd := h1.tsum_add h2
    have hfun : (fun m : ℕ => (if (N : ℝ) ≤ (m : ℝ) then c m else 0)
        + (if (N : ℝ) ≤ (m : ℝ) then (0 : ℝ) else c m)) = fun m => c m := by
      funext m
      by_cases h : (N : ℝ) ≤ (m : ℝ) <;> simp [h]
    rw [hfun] at hadd
    have h2val : (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then (0 : ℝ) else c m)
        = ∑ m ∈ Finset.range N, c m := by
      rw [tsum_eq_sum (s := Finset.range N)]
      · refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_range] at hm
        rw [if_neg (not_le.mpr (by exact_mod_cast hm))]
      · intro m hm
        rw [Finset.mem_range, not_lt] at hm
        rw [if_pos (by exact_mod_cast hm)]
    rw [h2val] at hadd
    linarith
  have htend : Filter.Tendsto (fun N : ℕ => (∑' m, c m) - ∑ m ∈ Finset.range N, c m)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, c m) Filter.atTop
        (nhds (∑' m, c m)) := hc.hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := (∑' m, c m))).sub h1
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  refine ⟨N, ?_⟩
  rw [hkey N]
  have hval := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hval
  have hnonneg : 0 ≤ (∑' m, c m) - ∑ m ∈ Finset.range N, c m := by
    rw [← hkey N]
    exact tsum_nonneg fun m => by
      by_cases h : (N : ℝ) ≤ (m : ℝ) <;> simp [h, hc0 m]
  rw [abs_of_nonneg hnonneg] at hval
  exact le_of_lt hval

/-- Comparison of the tail over `{m | M ≤ m}` with the tail over `{m | N ≤ m}`. -/
lemma tsum_ite_compl_le {c : ℕ → ℝ} (hc : Summable c) (hc0 : ∀ m, 0 ≤ c m) {M N : ℕ}
    (h : N ≤ M) :
    (∑' m : ℕ, if m < M then 0 else c m)
      ≤ (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then c m else 0) := by
  have h1 : Summable fun m : ℕ => if m < M then 0 else c m := by
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases hm : m < M
    · rw [if_pos hm, abs_zero]
      exact hc0 m
    · rw [if_neg hm, abs_of_nonneg (hc0 m)]
  have h2 : Summable fun m : ℕ => if (N : ℝ) ≤ (m : ℝ) then c m else 0 := by
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases hm : (N : ℝ) ≤ (m : ℝ)
    · rw [if_pos hm, abs_of_nonneg (hc0 m)]
    · rw [if_neg hm, abs_zero]
      exact hc0 m
  refine Summable.tsum_le_tsum (fun m => ?_) h1 h2
  by_cases hm : m < M
  · rw [if_pos hm]
    by_cases hN : (N : ℝ) ≤ (m : ℝ)
    · rw [if_pos hN]
      exact hc0 m
    · rw [if_neg hN]
  · rw [if_neg hm]
    have hNm : (N : ℝ) ≤ (m : ℝ) := by
      have hMm : M ≤ m := not_lt.mp hm
      have h1 : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
      have h2 : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hMm
      linarith
    rw [if_pos hNm]

/-- The decomposition of a summable family into its partial sum over `range M` and the tail. -/
lemma tsum_eq_sum_add_tsum_ite_range {E : Type*} [NormedAddCommGroup E] {f : ℕ → E}
    (hf : Summable f) (M : ℕ) :
    ∑' m, f m = ∑ m ∈ Finset.range M, f m + ∑' m, (if m < M then 0 else f m) := by
  have h1 : ∑' m, f m = ∑ m ∈ Finset.range M, f m +
      ∑' (m : ↑(((Finset.range M : Finset ℕ) : Set ℕ)ᶜ)), f ↑m :=
    (Summable.sum_add_tsum_compl hf).symm
  rw [h1, tsum_subtype]
  congr 1
  refine tsum_congr fun m => ?_
  by_cases hm : m ∈ Finset.range M
  · rw [Set.indicator_of_notMem (by simpa using hm), if_pos (Finset.mem_range.mp hm)]
  · rw [Set.indicator_of_mem (by simpa using hm),
      if_neg (by simpa [Finset.mem_range] using hm)]

/-- Norm bound for the tail of the moment identity. -/
lemma norm_sub_sum_range_le {k : ℕ} {Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ}
    {U : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ}
    (hΦ : Φ = ∑' m, U m) (hU : Summable U) {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m)
    (hwsum : Summable w) (hw : ∀ m, ‖U m‖ ≤ w m * ‖Φ‖) (M : ℕ) :
    ‖Φ - ∑ m ∈ Finset.range M, U m‖ ≤ ‖Φ‖ * (∑' m : ℕ, if m < M then 0 else w m) := by
  have hdecomp : Φ - ∑ m ∈ Finset.range M, U m = ∑' m, (if m < M then 0 else U m) := by
    rw [hΦ, tsum_eq_sum_add_tsum_ite_range hU M]
    abel
  rw [hdecomp]
  have hsumm1 : Summable fun m : ℕ => ‖(if m < M then 0 else U m)‖ := by
    refine Summable.of_norm_bounded (hwsum.mul_right ‖Φ‖) fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : m < M
    · rw [if_pos h, norm_zero, abs_zero]
      exact mul_nonneg (hw0 m) (norm_nonneg _)
    · rw [if_neg h, abs_of_nonneg (norm_nonneg _)]
      exact hw m
  have hmid : Summable fun m : ℕ => (if m < M then 0 else ‖U m‖) := by
    refine Summable.of_norm_bounded (hwsum.mul_right ‖Φ‖) fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : m < M
    · rw [if_pos h, abs_zero]
      exact mul_nonneg (hw0 m) (norm_nonneg _)
    · rw [if_neg h, abs_of_nonneg (norm_nonneg _)]
      exact hw m
  have hmid2 : Summable fun m : ℕ => (if m < M then 0 else w m * ‖Φ‖) := by
    refine Summable.of_norm_bounded (hwsum.mul_right ‖Φ‖) fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : m < M
    · rw [if_pos h, abs_zero]
      exact mul_nonneg (hw0 m) (norm_nonneg _)
    · rw [if_neg h, abs_of_nonneg (mul_nonneg (hw0 m) (norm_nonneg _))]
  calc ‖∑' m, (if m < M then 0 else U m)‖
      ≤ ∑' m, ‖(if m < M then 0 else U m)‖ := norm_tsum_le_tsum_norm hsumm1
    _ = ∑' m, (if m < M then 0 else ‖U m‖) :=
        tsum_congr fun m => by by_cases h : m < M <;> simp [h]
    _ ≤ ∑' m, (if m < M then 0 else w m * ‖Φ‖) := by
        refine Summable.tsum_le_tsum ?_ hmid hmid2
        intro m
        by_cases h : m < M
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
          exact hw m
    _ = ‖Φ‖ * (∑' m : ℕ, if m < M then 0 else w m) := by
        rw [show (∑' m : ℕ, (if m < M then 0 else w m * ‖Φ‖))
              = (∑' m : ℕ, (if m < M then 0 else w m) * ‖Φ‖) from
              tsum_congr fun m => by by_cases h : m < M <;> simp [h]]
        rw [tsum_mul_right, mul_comm]

/-! ## The jet matching of the Seeley sum at the hyperplane -/

/-- Pulling back along the shear is additive. -/
lemma compContinuousLinearMap_sub_seeleyLam {k : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) (c : ℝ) :
    (A - B).compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) c)
      = A.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) c)
        - B.compContinuousLinearMap (fun _ => Work.NN.Final.seeleyLam (X := X) c) := by
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.sub_apply]

set_option maxHeartbeats 1200000 in
/-- **The `k`-th iterated derivative of the Seeley sum converges to the `k`-th iterated derivative
of `g` at a point of the hyperplane**, along the open lower half space. -/
theorem tendsto_iteratedFDeriv_seeleySumV_hyperplane {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    (k : ℕ) {p : X × ℝ} (hp : p.2 = 0) (hpδ : -δ < p.2) :
    Filter.Tendsto (fun q : X × ℝ => iteratedFDeriv ℝ k (Work.NN.Final.seeleySumV a b δ g) q)
      (nhdsWithin p {q : X × ℝ | q.2 < 0}) (nhds (iteratedFDeriv ℝ k g p)) := by
  classical
  set V : X × ℝ → ℂ := Work.NN.Final.seeleyV δ g with hVdef
  have hb1 : ∀ m, 1 ≤ b m := fun m => le_trans one_le_two (hb m)
  have hb0 : ∀ m, (0 : ℝ) ≤ b m := fun m => le_trans zero_le_one (hb1 m)
  have hVcd : ContDiff ℝ (k : WithTop ENat) V := Work.NN.Final.seeleyV_contDiff_fin hδ hg k
  have hVinf : ContDiff ℝ ∞ V := Work.NN.Final.seeleyV_contDiff hδ hg
  -- `D^k V p = D^k g p` because `V = g` near `p`
  have hVp : iteratedFDeriv ℝ k V p = iteratedFDeriv ℝ k g p := by
    have hev : V =ᶠ[𝓝 p] g := by
      have hnb : {q : X × ℝ | -(δ / 2) ≤ q.2} ∈ 𝓝 p := by
        have h1 : {q : X × ℝ | -(δ / 2) < q.2} ∈ 𝓝 p := by
          refine IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd) ?_
          change -(δ / 2) < p.2
          rw [hp]; linarith
        exact Filter.mem_of_superset h1 fun q hq => by
          change -(δ / 2) ≤ q.2
          exact le_of_lt (by simpa using hq)
      filter_upwards [hnb] with q hq
      exact Work.NN.Final.seeleyV_eq δ g (hδ := hδ) hq
    exact iteratedFDeriv_congr_of_eventuallyEq hev k
  -- the model family (the summands of the moment identity at `p`)
  have hUinf_summable : Summable fun m => (a m) •
      (iteratedFDeriv ℝ k V p).compContinuousLinearMap
        (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) :=
    summable_smul_compContinuousLinearMap_seeleyLam hb1 hsum _
  have hUinf_tsum : (∑' m, (a m) •
      (iteratedFDeriv ℝ k V p).compContinuousLinearMap
        (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))) = iteratedFDeriv ℝ k V p :=
    tsum_smul_compContinuousLinearMap_seeleyLam_eq hb1 ha hsum _
  have hUinf_bound : ∀ m, ‖(a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
      (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
      ≤ (|a m| * (b m) ^ k) * ‖iteratedFDeriv ℝ k V p‖ :=
    fun m => norm_smul_compContinuousLinearMap_seeleyLam_le hb1 _ m
  -- the weights
  set w : ℕ → ℝ := fun m => |a m| * (b m) ^ k with hwdef
  have hwsum : Summable w := hsum k
  have hw0 : ∀ m, 0 ≤ w m := fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m) k)
  set L : ℝ := ∑' m, w m with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact tsum_nonneg hw0
  have hL1 : 0 < L + 1 := by linarith
  -- a uniform bound for the derivatives of `V` on a tube around `p`
  have hcontV : Continuous fun z : X × ℝ =>
      ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j V z‖ := by
    refine continuous_finset_sum _ fun j _ => ?_
    exact (hVinf.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨ηt, hηt, Ct, hCt⟩ :=
    exists_tube_bound_le (Y := X) (f := fun z : X × ℝ =>
      ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j V z‖) hcontV p.1 isCompact_Icc
  set C₁ : ℝ := max Ct 0 with hC1
  have hC10 : 0 ≤ C₁ := le_max_right _ _
  have htube : ∀ y : X, dist y p.1 < ηt → ∀ s ∈ Set.Icc (0 : ℝ) 4,
      (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j V (y, s)‖) ≤ C₁ :=
    fun y hy s hs => le_trans (hCt y hy s hs) (le_max_left _ _)
  have htube_k : ∀ y : X, dist y p.1 < ηt → ∀ s ∈ Set.Icc (0 : ℝ) 4,
      ‖iteratedFDeriv ℝ k V (y, s)‖ ≤ C₁ := by
    intro y hy s hs
    refine le_trans ?_ (htube y hy s hs)
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedFDeriv ℝ j V (y, s)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have hΦC : ‖iteratedFDeriv ℝ k V p‖ ≤ C₁ := by
    have h := htube_k p.1 (by simpa using hηt) 0 ⟨le_refl 0, by norm_num⟩
    have hp' : (p.1, (0 : ℝ)) = p := by rw [← hp]
    rwa [hp'] at h
  -- the constants of the estimate
  set Kc : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j with hKc
  have hKc0 : 0 ≤ Kc :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (Work.NN.Final.seeleyCutB_nonneg j)
  set Cbad : ℝ := (Kc + 2) * (C₁ + 1) with hCbad
  have hCbadpos : 0 < Cbad := by rw [hCbad]; nlinarith
  -- continuity of `D^k V` at `p` gives a smallness radius
  have hcontk : Filter.Tendsto (fun z : X × ℝ => iteratedFDeriv ℝ k V z) (𝓝 p)
      (𝓝 (iteratedFDeriv ℝ k V p)) :=
    (hVcd.contDiffAt.continuousAt_iteratedFDeriv le_rfl).tendsto
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- the tolerance for the difference of the derivatives of `V` near `p`
  set ε₁ : ℝ := (ε / 4) / (L + 1) with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
  -- a radius on which `D^k V` is `ε₁`-close to its value at `p`
  obtain ⟨η₀, hη₀pos, hη₀b⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z : X × ℝ, dist z p < η →
      ‖iteratedFDeriv ℝ k V z - iteratedFDeriv ℝ k V p‖ ≤ ε₁ := by
    have h := (Metric.tendsto_nhds.mp hcontk) ε₁ hε₁pos
    obtain ⟨η, hη, hηb⟩ := Metric.mem_nhds_iff.mp h
    exact ⟨η, hη, fun z hz => by
      have h2 := hηb hz
      change dist (iteratedFDeriv ℝ k V z) (iteratedFDeriv ℝ k V p) < ε₁ at h2
      rw [dist_eq_norm] at h2
      exact le_of_lt h2⟩
  set η₁ : ℝ := min η₀ 1 with hη₁def
  have hη₁pos : 0 < η₁ := by rw [hη₁def]; exact lt_min hη₀pos one_pos
  have hη₁le_one : η₁ ≤ 1 := by rw [hη₁def]; exact min_le_right _ _
  have hη₁le : η₁ ≤ η₀ := by rw [hη₁def]; exact min_le_left _ _
  have hη₁b : ∀ z : X × ℝ, dist z p < η₁ →
      ‖iteratedFDeriv ℝ k V z - iteratedFDeriv ℝ k V p‖ ≤ ε₁ :=
    fun z hz => hη₀b z (lt_of_lt_of_le hz hη₁le)
  -- the tail of the weights
  obtain ⟨N₁, hN₁⟩ : ∃ N : ℕ, (∑' m : ℕ, if (N : ℝ) ≤ (m : ℝ) then w m else 0)
      ≤ (ε / 4) / (C₁ + 1) :=
    exists_tsum_nat_tail_le hwsum hw0 (by positivity)
  obtain ⟨R₁₀, hR₁₀⟩ : ∃ R : ℝ, ∀ R' : ℝ, R ≤ R' →
      (∑' m : ℕ, if R' ≤ b m then w m else 0) ≤ (ε / 4) / Cbad :=
    exists_tsum_indicator_le hbT hwsum hw0 (by positivity)
  obtain ⟨R₂₀, hR₂₀⟩ : ∃ R : ℝ, ∀ R' : ℝ, R ≤ R' →
      (∑' m : ℕ, if R' ≤ b m then w m else 0) ≤ (ε / 4) / Cbad :=
    exists_tsum_indicator_le hbT hwsum hw0 (by positivity)
  set R₁ : ℝ := max R₁₀ 1 with hR₁def
  set R₂ : ℝ := max R₂₀ 1 with hR₂def
  have hR₁pos : 0 < R₁ := by rw [hR₁def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR₂pos : 0 < R₂ := by rw [hR₂def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR₁b : ∀ R' : ℝ, R₁ ≤ R' → (∑' m : ℕ, if R' ≤ b m then w m else 0) ≤ (ε / 4) / Cbad :=
    fun R' hR' => hR₁₀ R' (le_trans (le_max_left _ _) hR')
  have hR₂b : ∀ R' : ℝ, R₂ ≤ R' → (∑' m : ℕ, if R' ≤ b m then w m else 0) ≤ (ε / 4) / Cbad :=
    fun R' hR' => hR₂₀ R' (le_trans (le_max_left _ _) hR')
  set T₁ : ℝ := 1 / R₁ with hT₁def
  set T₂ : ℝ := η₁ / R₂ with hT₂def
  have hT₁pos : 0 < T₁ := by rw [hT₁def]; positivity
  have hT₂pos : 0 < T₂ := by rw [hT₂def]; positivity
  set δv : ℝ := min (min (η₁ / 4) ηt) (min T₁ T₂) with hδvdef
  have hδvpos : 0 < δv := by
    rw [hδvdef]
    exact lt_min (lt_min (by linarith) hηt) (lt_min hT₁pos hT₂pos)
  refine ⟨δv, hδvpos, fun q hq hdist => ?_⟩
  have hq' : q.2 < 0 := hq
  have htpos : 0 < -q.2 := by linarith
  have hqabs : |q.2| = -q.2 := abs_of_neg hq'
  have hdist_le : dist q p ≤ δv := le_of_lt hdist
  have hδ_ηt : δv ≤ ηt := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_η₁ : δv ≤ η₁ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_T₁ : δv ≤ T₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_T₂ : δv ≤ T₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  have ht_le : -q.2 ≤ δv := by
    have h1 : |q.2 - p.2| ≤ dist q p := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    calc -q.2 = |q.2 - p.2| := by rw [hp, sub_zero, hqabs]
      _ ≤ dist q p := h1
      _ ≤ δv := hdist_le
  have hdist1 : dist q.1 p.1 < ηt := by
    have h1 : dist q.1 p.1 ≤ dist q p := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    linarith
  have hdist1_le : dist q.1 p.1 ≤ dist q p := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hdistη : dist q p < η₁ / 4 := lt_of_lt_of_le hdist hδ_η₁
  -- the truncation
  obtain ⟨M₀, hM₀⟩ := Work.NN.Final.exists_b_ge hbT (4 / (-q.2))
  set M : ℕ := max N₁ M₀ with hMdef
  have hM : ∀ m ≥ M, 4 ≤ b m * |q.2| := by
    intro m hm
    have h1 : 4 / (-q.2) ≤ b m := hM₀ m (le_trans (le_max_right _ _) (by rw [hMdef] at hm; exact hm))
    rw [div_le_iff₀ htpos] at h1
    rw [hqabs]
    linarith
  have hMN : N₁ ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hAM : iteratedFDeriv ℝ k (Work.NN.Final.seeleySumV a b δ g) q
      = ∑ m ∈ Finset.range M, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q :=
    iteratedFDeriv_seeleySumV_eq_sum hδ hb hbT hg k hq' hM
  -- the shear of `q`
  have hτ : ∀ m : ℕ, Work.NN.Final.seeleyLam (X := X) (-(b m)) q = (q.1, b m * (-q.2)) := by
    intro m
    rw [Work.NN.Final.seeleyLam_apply]
    ring
  have hmaxc : ∀ m : ℕ, max 1 |-(b m)| = b m := by
    intro m
    rw [abs_neg, abs_of_nonneg (hb0 m)]
    exact max_eq_right (hb1 m)
  -- the per-summand bound
  have hper : ∀ m : ℕ,
      ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
        - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
            (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
      ≤ w m * (if b m * (-q.2) < η₁ then ε₁ else Cbad) := by
    intro m
    by_cases hsmall : b m * (-q.2) < 1
    · have hgood := iteratedFDeriv_seeleyTV_eq_of_mul_abs_snd_lt_one (a := a) (b := b) hδ hg k
        (hb0 m) (by rw [hqabs]; exact hsmall)
      rw [hgood, ← smul_sub, ← compContinuousLinearMap_sub_seeleyLam, norm_smul, Real.norm_eq_abs]
      have hdiff : ‖iteratedFDeriv ℝ k V (Work.NN.Final.seeleyLam (X := X) (-(b m)) q)
          - iteratedFDeriv ℝ k V p‖ ≤ (if b m * (-q.2) < η₁ then ε₁ else Cbad) := by
        by_cases hc : b m * (-q.2) < η₁
        · rw [if_pos hc]
          refine hη₁b _ ?_
          rw [hτ m, Prod.dist_eq, hp]
          refine max_lt ?_ ?_
          · linarith
          · rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos (by linarith [hb m]) htpos)]
            exact hc
        · rw [if_neg hc]
          have hs4 : b m * (-q.2) ∈ Set.Icc (0 : ℝ) 4 :=
            ⟨mul_nonneg (hb0 m) htpos.le, by linarith⟩
          have h1 : ‖iteratedFDeriv ℝ k V (q.1, b m * (-q.2))‖ ≤ C₁ := htube_k q.1 hdist1 _ hs4
          have h3 : ‖iteratedFDeriv ℝ k V (Work.NN.Final.seeleyLam (X := X) (-(b m)) q)
              - iteratedFDeriv ℝ k V p‖ ≤ C₁ + C₁ := by
            rw [hτ m]
            exact le_trans (norm_sub_le _ _) (add_le_add h1 hΦC)
          refine le_trans h3 ?_
          rw [hCbad]
          nlinarith [hKc0, hC10]
      calc |a m| * ‖(iteratedFDeriv ℝ k V (Work.NN.Final.seeleyLam (X := X) (-(b m)) q)
              - iteratedFDeriv ℝ k V p).compContinuousLinearMap
                (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
          ≤ |a m| * (‖iteratedFDeriv ℝ k V (Work.NN.Final.seeleyLam (X := X) (-(b m)) q)
              - iteratedFDeriv ℝ k V p‖ * (max 1 |-(b m)|) ^ k) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact Work.NN.Final.norm_compContinuousLinearMap_const_le _ _
        _ ≤ |a m| * ((if b m * (-q.2) < η₁ then ε₁ else Cbad) * (b m) ^ k) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [hmaxc m]
            exact mul_le_mul_of_nonneg_right hdiff (pow_nonneg (hb0 m) k)
        _ = w m * (if b m * (-q.2) < η₁ then ε₁ else Cbad) := by
            rw [hwdef]
            ring
    · push Not at hsmall
      have hnot : ¬ (b m * (-q.2) < η₁) := by
        rw [not_lt]
        linarith
      have hTVb : ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q‖ ≤ Kc * C₁ * w m := by
        by_cases hv : 4 ≤ b m * |q.2|
        · have hz : iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q = 0 := by
            rw [iteratedFDeriv_congr_of_eventuallyEq
              (seeleyTV_eventuallyEq_zero (hb0 m) hq' hv) k]
            simp
          rw [hz, norm_zero]
          exact mul_nonneg (mul_nonneg hKc0 hC10) (hw0 m)
        · push Not at hv
          rw [hqabs] at hv
          have hs4 : b m * (-q.2) ∈ Set.Icc (0 : ℝ) 4 :=
            ⟨mul_nonneg (hb0 m) htpos.le, by linarith⟩
          have hbnd := norm_iteratedFDeriv_seeleyTV_le (a := a) hδ hg hb1 k m q
          rw [hτ m] at hbnd
          calc ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q‖
              ≤ |a m| * (b m) ^ k *
                  (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Work.NN.Final.seeleyCutB j) *
                  (∑ j ∈ Finset.range (k + 1),
                    ‖iteratedFDeriv ℝ j V (q.1, b m * (-q.2))‖) := hbnd
            _ ≤ |a m| * (b m) ^ k * Kc * C₁ := by
                rw [hKc]
                refine mul_le_mul_of_nonneg_left (htube q.1 hdist1 (b m * (-q.2)) hs4) ?_
                exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m) k))
                  (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
                    (Work.NN.Final.seeleyCutB_nonneg j))
            _ = Kc * C₁ * w m := by rw [hwdef]; ring
      have hUb : ‖(a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
          (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖ ≤ C₁ * w m := by
        refine le_trans (hUinf_bound m) ?_
        rw [hwdef]
        calc |a m| * (b m) ^ k * ‖iteratedFDeriv ℝ k V p‖ ≤ |a m| * (b m) ^ k * C₁ :=
              mul_le_mul_of_nonneg_left hΦC (mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m) k))
          _ = C₁ * (|a m| * (b m) ^ k) := by ring
      calc ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
            - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
                (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
          ≤ Kc * C₁ * w m + C₁ * w m := le_trans (norm_sub_le _ _) (add_le_add hTVb hUb)
        _ ≤ w m * (if b m * (-q.2) < η₁ then ε₁ else Cbad) := by
            rw [if_neg hnot, hCbad]
            nlinarith [hKc0, hC10, hw0 m]
  -- summability of the eta-indicator
  have hsummableη : Summable fun m : ℕ => if η₁ ≤ b m * (-q.2) then w m else 0 := by
    refine Summable.of_norm_bounded hwsum fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : η₁ ≤ b m * (-q.2)
    · rw [if_pos h, abs_of_nonneg (hw0 m)]
    · rw [if_neg h, abs_zero]
      exact hw0 m
  have hWη : (∑' m : ℕ, if η₁ ≤ b m * (-q.2) then w m else 0) ≤ (ε / 4) / Cbad := by
    have hiff : ∀ m : ℕ, (η₁ / (-q.2) ≤ b m) ↔ (η₁ ≤ b m * (-q.2)) := by
      intro m
      rw [div_le_iff₀ htpos]
    have hge : R₂ ≤ η₁ / (-q.2) := by
      have h1 : -q.2 ≤ η₁ / R₂ := by
        have := ht_le.trans hδ_T₂
        rwa [hT₂def] at this
      rw [le_div_iff₀ hR₂pos] at h1
      rw [le_div_iff₀ htpos]
      linarith
    calc (∑' m : ℕ, if η₁ ≤ b m * (-q.2) then w m else 0)
        = (∑' m : ℕ, if η₁ / (-q.2) ≤ b m then w m else 0) := by
          refine tsum_congr fun m => ?_
          by_cases h : η₁ / (-q.2) ≤ b m
          · rw [if_pos h, if_pos ((hiff m).mp h)]
          · rw [if_neg h, if_neg (fun hc => h ((hiff m).mpr hc))]
      _ ≤ (ε / 4) / Cbad := hR₂b _ hge
  have hWbad : (∑' m : ℕ, if 1 ≤ b m * (-q.2) then w m else 0) ≤ (ε / 4) / Cbad := by
    have hiff : ∀ m : ℕ, (1 / (-q.2) ≤ b m) ↔ (1 ≤ b m * (-q.2)) := by
      intro m
      rw [div_le_iff₀ htpos]
    have hge : R₁ ≤ 1 / (-q.2) := by
      have h1 : -q.2 ≤ 1 / R₁ := by
        have := ht_le.trans hδ_T₁
        rwa [hT₁def] at this
      rw [le_div_iff₀ hR₁pos] at h1
      rw [le_div_iff₀ htpos]
      linarith
    calc (∑' m : ℕ, if 1 ≤ b m * (-q.2) then w m else 0)
        = (∑' m : ℕ, if 1 / (-q.2) ≤ b m then w m else 0) := by
          refine tsum_congr fun m => ?_
          by_cases h : 1 / (-q.2) ≤ b m
          · rw [if_pos h, if_pos ((hiff m).mp h)]
          · rw [if_neg h, if_neg (fun hc => h ((hiff m).mpr hc))]
      _ ≤ (ε / 4) / Cbad := hR₁b _ hge
  -- the finite sum estimate
  have hε₁L : ε₁ * L ≤ ε / 4 := by
    rw [hε₁def, div_mul_eq_mul_div, div_le_iff₀ hL1]
    nlinarith [hε.le, hL0]
  have hsumest : ‖∑ m ∈ Finset.range M,
      (iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
        - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
            (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))))‖ ≤ ε / 2 := by
    calc ‖∑ m ∈ Finset.range M,
          (iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
            - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
                (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))))‖
        ≤ ∑ m ∈ Finset.range M, ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
            - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
                (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range M, w m * (if b m * (-q.2) < η₁ then ε₁ else Cbad) :=
          Finset.sum_le_sum fun m _ => hper m
      _ = ε₁ * (∑ m ∈ (Finset.range M).filter (fun m => b m * (-q.2) < η₁), w m)
          + Cbad * (∑ m ∈ (Finset.range M).filter (fun m => ¬ (b m * (-q.2) < η₁)), w m) := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range M)
            (p := fun m => b m * (-q.2) < η₁)
            (f := fun m => w m * (if b m * (-q.2) < η₁ then ε₁ else Cbad))]
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [Finset.mem_filter] at hm
            rw [if_pos hm.2]
            ring
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [Finset.mem_filter] at hm
            rw [if_neg hm.2]
            ring
      _ ≤ ε₁ * L + Cbad * ((ε / 4) / Cbad) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (le_of_lt hε₁pos))
            (mul_le_mul_of_nonneg_left ?_ (le_of_lt hCbadpos))
          · rw [hLdef]
            exact Summable.sum_le_tsum _ (fun i _ => hw0 i) hwsum
          · calc ∑ m ∈ (Finset.range M).filter (fun m => ¬ (b m * (-q.2) < η₁)), w m
                ≤ ∑ m ∈ (Finset.range M).filter (fun m => ¬ (b m * (-q.2) < η₁)),
                    (if η₁ ≤ b m * (-q.2) then w m else 0) := by
                  refine Finset.sum_le_sum fun m hm => ?_
                  rw [Finset.mem_filter] at hm
                  rw [if_pos (not_lt.mp hm.2)]
              _ ≤ ∑' m : ℕ, (if η₁ ≤ b m * (-q.2) then w m else 0) :=
                  Summable.sum_le_tsum _ (fun i _ => by
                    by_cases h : η₁ ≤ b i * (-q.2)
                    · rw [if_pos h]
                      exact hw0 i
                    · rw [if_neg h]) hsummableη
              _ ≤ (ε / 4) / Cbad := hWη
      _ = ε₁ * L + ε / 4 := by
          rw [mul_comm Cbad ((ε / 4) / Cbad), div_mul_cancel₀ _ (ne_of_gt hCbadpos)]
      _ ≤ ε / 4 + ε / 4 := by linarith
      _ = ε / 2 := by ring
  -- the tail estimate
  have htailest : ‖∑ m ∈ Finset.range M, (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
        (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) - iteratedFDeriv ℝ k g p‖ ≤ ε / 4 := by
    rw [← hVp, norm_sub_rev]
    have h1 : ‖iteratedFDeriv ℝ k V p - ∑ m ∈ Finset.range M,
        (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
          (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
        ≤ ‖iteratedFDeriv ℝ k V p‖ * (∑' m : ℕ, if m < M then 0 else w m) :=
      norm_sub_sum_range_le hUinf_tsum.symm hUinf_summable hw0 hwsum hUinf_bound M
    have h2 : (∑' m : ℕ, if m < M then 0 else w m)
        ≤ (∑' m : ℕ, if (N₁ : ℝ) ≤ (m : ℝ) then w m else 0) :=
      tsum_ite_compl_le hwsum hw0 hMN
    calc ‖iteratedFDeriv ℝ k V p - ∑ m ∈ Finset.range M,
          (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
            (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))‖
        ≤ ‖iteratedFDeriv ℝ k V p‖ * (∑' m : ℕ, if m < M then 0 else w m) := h1
      _ ≤ C₁ * (∑' m : ℕ, if (N₁ : ℝ) ≤ (m : ℝ) then w m else 0) :=
          mul_le_mul hΦC h2
            (tsum_nonneg fun m => by
              by_cases h : m < M
              · rw [if_pos h]
              · rw [if_neg h]; exact hw0 m)
            hC10
      _ ≤ C₁ * ((ε / 4) / (C₁ + 1)) := mul_le_mul_of_nonneg_left hN₁ hC10
      _ ≤ ε / 4 := by
          rw [mul_comm C₁ ((ε / 4) / (C₁ + 1)), div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [hε.le, hC10]
  -- conclusion
  have hfinal : ‖iteratedFDeriv ℝ k (Work.NN.Final.seeleySumV a b δ g) q
      - iteratedFDeriv ℝ k g p‖ < ε := by
    rw [hAM]
    have hsplit : ∑ m ∈ Finset.range M, iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
        - iteratedFDeriv ℝ k g p
        = (∑ m ∈ Finset.range M,
            (iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
              - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
                  (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))))
          + (∑ m ∈ Finset.range M, (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
              (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) - iteratedFDeriv ℝ k g p) := by
      rw [Finset.sum_sub_distrib]
      abel
    rw [hsplit]
    calc ‖(∑ m ∈ Finset.range M,
            (iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
              - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
                  (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m)))))
          + (∑ m ∈ Finset.range M, (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
              (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) - iteratedFDeriv ℝ k g p)‖
        ≤ ‖∑ m ∈ Finset.range M,
            (iteratedFDeriv ℝ k (Work.NN.Final.seeleyTV a b δ g m) q
              - (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
                  (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))))‖
          + ‖∑ m ∈ Finset.range M, (a m) • (iteratedFDeriv ℝ k V p).compContinuousLinearMap
              (fun _ => Work.NN.Final.seeleyLam (X := X) (-(b m))) - iteratedFDeriv ℝ k g p‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + ε / 4 := add_le_add hsumest htailest
      _ < ε := by linarith
  simpa only [dist_eq_norm] using hfinal

/-! ## Smoothness on the open half spaces, continuity on the slab, and the limits -/

/-- Passing from a limit of `iteratedFDeriv ℝ 0` to a limit of the function. -/
lemma tendsto_of_tendsto_iteratedFDeriv_zero {l : Filter (X × ℝ)} {F G : X × ℝ → ℂ} {x : X × ℝ}
    (h : Filter.Tendsto (fun q => iteratedFDeriv ℝ 0 F q) l (nhds (iteratedFDeriv ℝ 0 G x))) :
    Filter.Tendsto F l (nhds (G x)) := by
  have h1 : Filter.Tendsto (fun q => (continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ)
      (iteratedFDeriv ℝ 0 F q)) l
      (nhds ((continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ) (iteratedFDeriv ℝ 0 G x))) :=
    ((continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ).continuous.continuousAt).tendsto.comp h
  have h2 : (fun q => (continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ) (iteratedFDeriv ℝ 0 F q)) = F := by
    funext q
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ).apply_symm_apply (F q)
  have h3 : (continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ) (iteratedFDeriv ℝ 0 G x) = G x := by
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) ℂ).apply_symm_apply (G x)
  rwa [h2, h3] at h1

/-- On the open lower half space the Seeley sum is locally a finite sum of smooth terms, hence
`C^k` at every one of its points. -/
lemma contDiffAt_seeleySumV {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    {x : X × ℝ} (hx : x.2 < 0) (k : ℕ) :
    ContDiffAt ℝ (k : WithTop ENat) (Work.NN.Final.seeleySumV a b δ g) x := by
  obtain ⟨S, hS, _⟩ := exists_finset_seeleySumV_eventuallyEq hb hbT δ g hx
  have hfin : ContDiff ℝ (k : WithTop ENat)
      (fun y => ∑ m ∈ S, Work.NN.Final.seeleyTV a b δ g m y) :=
    ContDiff.sum fun m _ => seeleyTV_contDiff hδ hg a b k m
  exact hfin.contDiffAt.congr_of_eventuallyEq hS

/-- The iterated derivatives of the Seeley extension have a limit along the punctured neighbourhood
of any point of the slab. -/
lemma exists_tendsto_iteratedFDeriv_seeleyEV {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ}
    (hb : ∀ m, 2 ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2})
    (i : ℕ) {p : X × ℝ} (hpδ : -δ < p.2) :
    ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) ℂ,
      Filter.Tendsto (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
        (nhdsWithin p {q : X × ℝ | -δ < q.2 ∧ q.2 ≠ 0}) (nhds L) := by
  rcases lt_trichotomy p.2 0 with hneg | hzero | hpos
  · have hcongr : (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
        =ᶠ[𝓝 p] (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleySumV a b δ g) q) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hneg] with q hq
      exact iteratedFDeriv_congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hq)
          (fun z hz => Work.NN.Final.seeleyEV_of_neg a b δ g hz)) i
    have hcont : ContinuousAt (fun q : X × ℝ =>
        iteratedFDeriv ℝ i (Work.NN.Final.seeleySumV a b δ g) q) p :=
      (contDiffAt_seeleySumV hδ hb hbT hg hneg i).continuousAt_iteratedFDeriv le_rfl
    exact ⟨_, (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hcongr.filter_mono nhdsWithin_le_nhds).symm⟩
  · have hlow : Filter.Tendsto
        (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
        (nhdsWithin p {q : X × ℝ | q.2 < 0}) (nhds (iteratedFDeriv ℝ i g p)) := by
      have hcongr : (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
          =ᶠ[nhdsWithin p {q : X × ℝ | q.2 < 0}]
          (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleySumV a b δ g) q) := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact iteratedFDeriv_congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hq)
            (fun z hz => Work.NN.Final.seeleyEV_of_neg a b δ g hz)) i
      exact (tendsto_iteratedFDeriv_seeleySumV_hyperplane hδ hb hbT ha hsum hg i hzero hpδ).congr'
        hcongr.symm
    have hup : Filter.Tendsto
        (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
        (nhdsWithin p {q : X × ℝ | 0 < q.2}) (nhds (iteratedFDeriv ℝ i g p)) := by
      have hcongr : (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
          =ᶠ[nhdsWithin p {q : X × ℝ | 0 < q.2}]
          (fun q : X × ℝ => iteratedFDeriv ℝ i g q) := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact iteratedFDeriv_congr_of_eventuallyEq
          (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hq)
            (fun z hz => Work.NN.Final.seeleyEV_of_nonneg a b δ g (le_of_lt (by simpa using hz)))) i
      have hcont : ContinuousAt (fun q : X × ℝ => iteratedFDeriv ℝ i g q) p :=
        ((hg i).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hpδ))
          |>.continuousAt_iteratedFDeriv le_rfl
      exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hcongr.symm
    refine ⟨iteratedFDeriv ℝ i g p, ?_⟩
    rw [Metric.tendsto_nhdsWithin_nhds] at hlow hup ⊢
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hlow ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := hup ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hq hqdist => ?_⟩
    rcases lt_or_gt_of_ne hq.2 with h | h
    · exact h₁ h (lt_of_lt_of_le hqdist (min_le_left _ _))
    · exact h₂ h (lt_of_lt_of_le hqdist (min_le_right _ _))
  · have hcongr : (fun q : X × ℝ => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) q)
        =ᶠ[𝓝 p] (fun q : X × ℝ => iteratedFDeriv ℝ i g q) := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hpos] with q hq
      exact iteratedFDeriv_congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hq)
          (fun z hz => Work.NN.Final.seeleyEV_of_nonneg a b δ g
            (le_of_lt (by simpa using hz)))) i
    have hcont : ContinuousAt (fun q : X × ℝ => iteratedFDeriv ℝ i g q) p :=
      ((hg i).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hpδ))
        |>.continuousAt_iteratedFDeriv le_rfl
    exact ⟨_, (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hcongr.filter_mono nhdsWithin_le_nhds).symm⟩

/-- The Seeley extension is continuous on the slab whenever `g` is smooth there. -/
theorem continuousOn_seeleyEV {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j) {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) :
    ContinuousOn (Work.NN.Final.seeleyEV a b δ g) {p : X × ℝ | -δ < p.2} := by
  intro p hp
  rcases lt_trichotomy p.2 0 with hneg | hzero | hpos
  · have hcont : ContinuousAt (Work.NN.Final.seeleySumV a b δ g) p :=
      (contDiffAt_seeleySumV hδ hb hbT hg hneg 0).continuousAt
    refine ((hcont.congr_of_eventuallyEq ?_).continuousWithinAt)
    exact Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hneg)
      (fun z hz => Work.NN.Final.seeleyEV_of_neg a b δ g hz)
  · have hgp : Work.NN.Final.seeleyEV a b δ g p = g p :=
      Work.NN.Final.seeleyEV_of_nonneg a b δ g (le_of_eq hzero.symm)
    have hmain : ContinuousAt (Work.NN.Final.seeleyEV a b δ g) p := by
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hgcont : ContinuousAt g p :=
        (hg 0).continuousOn.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
      have hlow : Filter.Tendsto (Work.NN.Final.seeleySumV a b δ g)
          (nhdsWithin p {q : X × ℝ | q.2 < 0}) (nhds (g p)) :=
        tendsto_of_tendsto_iteratedFDeriv_zero
          (tendsto_iteratedFDeriv_seeleySumV_hyperplane hδ hb hbT ha hsum hg 0 hzero hp)
      obtain ⟨δ₁, hδ₁, h₁⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlow) ε hε
      obtain ⟨δ₂, hδ₂, h₂⟩ := (Metric.continuousAt_iff.mp hgcont) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hqdist => ?_⟩
      rcases lt_trichotomy q.2 0 with hqneg | hqzero | hqpos
      · rw [Work.NN.Final.seeleyEV_of_neg a b δ g hqneg, hgp]
        exact h₁ hqneg (lt_of_lt_of_le hqdist (min_le_left _ _))
      · rw [Work.NN.Final.seeleyEV_of_nonneg a b δ g (le_of_eq hqzero.symm), hgp]
        exact h₂ (lt_of_lt_of_le hqdist (min_le_right _ _))
      · rw [Work.NN.Final.seeleyEV_of_nonneg a b δ g hqpos.le, hgp]
        exact h₂ (lt_of_lt_of_le hqdist (min_le_right _ _))
    exact hmain.continuousWithinAt
  · have hcont : ContinuousAt g p :=
      (hg 0).continuousOn.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
    have hev : Work.NN.Final.seeleyEV a b δ g =ᶠ[𝓝 p] g :=
      Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)
        (fun z hz => Work.NN.Final.seeleyEV_of_nonneg a b δ g (le_of_lt (by simpa using hz)))
    exact (hcont.congr_of_eventuallyEq hev).continuousWithinAt

/-! ## The Seeley extension is `C^m` on the slab -/

/-- The Seeley extension is `C^m` on the slab when `g` is smooth there.  Apply
`Work.NN.Final.contDiffOn_glue` with `F = seeleyEV a b δ g`: on the open upper half space `F = g`
and on the open lower half space `F = seeleySumV a b δ g`, which is `C^∞` there because the sum is
locally finite (`exists_finset_seeleyTV_eq_zero`) and each term is smooth (`seeleyV_contDiff`);
continuity holds because the values agree on the hyperplane (`seeleySumV` at `p.2 = 0` equals
`(∑' m, a m) • g p = g p`); and the limits of the iterated derivatives along the punctured
neighbourhood of a point of the hyperplane agree by `tendsto_iteratedFDeriv_seeleySumV` (from
below) and the continuity of the derivatives of `g` (from above). -/
theorem seeleyEV_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {δ : ℝ} (hδ : 0 < δ) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {g : X × ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) (m : ℕ) :
    ContDiffOn ℝ (m : WithTop ENat) (Work.NN.Final.seeleyEV a b δ g) {p : X × ℝ | -δ < p.2} := by
  refine Work.NN.Final.contDiffOn_glue (m := m) (continuousOn_seeleyEV hδ hb hbT ha hsum hg)
    ?_ ?_ ?_
  · refine ContDiffOn.congr ?_ fun x hx => Work.NN.Final.seeleyEV_of_neg a b δ g hx.2
    intro x hx
    exact (contDiffAt_seeleySumV hδ hb hbT hg hx.2 m).contDiffWithinAt
  · refine ContDiffOn.congr ((hg m).mono ?_) fun x hx =>
      Work.NN.Final.seeleyEV_of_nonneg a b δ g hx.le
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    linarith
  · intro i _ p hp
    exact exists_tendsto_iteratedFDeriv_seeleyEV hδ hb hbT ha hsum hg i hp

end Work.NN.Seeley

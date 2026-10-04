import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.MP.dini_first_exit_lsc_usc
import Submission.Work.Diff.MP.frob_nearest_supporting
import Submission.Work.Diff.MP.isCompact_frobBall
import Submission.Work.Diff.MP.frobDot_nonpos_of_frobDist_min

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.Diff.MP

open Set Filter Submission.Diff.Alg
open scoped Topology
open Work.Diff.MP

/-!
# Chow--Lu maximum principle with semi-continuous data

`Work.Diff.MP.max_principle_lsc` is the variant of `Work.Diff.MP.max_principle` needed by the
pinching-set application: the *joint* continuity of `(s,x) ↦ d s x` is replaced by the weaker
regularity that is actually available there, namely

* `x ↦ d t x` is continuous for each fixed `t` (so that the supremum over the compact `X` is
  attained), and
* the sup function `t ↦ ⨆ x, d t x` is lower semi-continuous on `[a,b]` and upper semi-continuous
  from the right on `[a,b)` (Chow--Lu, Lemma 3.2), in the banded form in which the estimate is
  produced (`t + h ≤ b`).

The proof is that of `max_principle`: the only places where joint continuity was used are the
attainment of the supremum (now `mp_sup_attained`), the continuity of `F` (now the lsc + right-usc
hypotheses, assembled by `mp_continuous_rcont`), and the final Dini lemma (now the banded variant
`mp_dini_lsc_band`, whose `hrusc`/`hD` hypotheses are exactly the shape in which the estimates are
available).
-/

variable {n : ℕ}

/-- If `g → 0` then `d - c * g → d`. -/
private theorem mp_tendsto_const_sub_mul {ι : Type*} {l : Filter ι} {g : ι → ℝ}
    (hg : Tendsto g l (𝓝 (0 : ℝ))) (c d : ℝ) :
    Tendsto (fun i => d - c * g i) l (𝓝 d) := by
  have h1 : Tendsto (fun i => c * g i) l (𝓝 (c * 0)) := hg.const_mul c
  have h2 : Tendsto (fun i => d - c * g i) l (𝓝 (d - c * 0)) := tendsto_const_nhds.sub h1
  have h3 : d - c * 0 = d := by ring
  rwa [h3] at h2

/-- Limit comparison in `ℝ`. -/
private theorem mp_le_of_tendsto_le {ι : Type*} {l : Filter ι} [NeBot l] {u v : ι → ℝ} {a b : ℝ}
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b)) (h : u ≤ᶠ[l] v) : a ≤ b :=
  le_of_tendsto_of_tendsto hu hv h


/-- Composition of a filter limit with a function that is continuous within a set. -/
private theorem mp_tendsto_comp {γ α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {u : γ → α} {F : Filter γ} {p : α} {s : Set α} {g : α → β}
    (hg : ContinuousWithinAt g s p) (hu : Tendsto u F (𝓝 p)) (hs : ∀ᶠ i in F, u i ∈ s) :
    Tendsto (fun i => g (u i)) F (𝓝 (g p)) := by
  have h1 : Tendsto u F (𝓝[s] p) := by
    rw [nhdsWithin, tendsto_inf]
    exact ⟨hu, tendsto_principal.mpr hs⟩
  exact hg.tendsto.comp h1

/-- Every sequence in a compact space converges along any ultrafilter. -/
private theorem mp_ultra_compact {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (𝒰 : Ultrafilter ℕ) (y : ℕ → Y) : ∃ ylim : Y, Tendsto y 𝒰 (𝓝 ylim) := by
  obtain ⟨ylim, -, h⟩ := (isCompact_iff_ultrafilter_le_nhds.mp isCompact_univ) (𝒰.map y)
    (by rw [principal_univ]; exact le_top)
  exact ⟨ylim, tendsto_iff_comap.mpr (by rwa [Ultrafilter.coe_map, map_le_iff_le_comap] at h)⟩

/-- Every sequence that is eventually in a compact set converges along any ultrafilter. -/
private theorem mp_ultra_isCompact {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsCompact C)
    (𝒰 : Ultrafilter ℕ) {y : ℕ → Y} (hy : ∀ᶠ i in 𝒰, y i ∈ C) :
    ∃ ylim ∈ C, Tendsto y 𝒰 (𝓝 ylim) := by
  have hmem : C ∈ (𝒰.map y : Filter Y) := by
    rw [Ultrafilter.coe_map, mem_map]
    exact hy
  obtain ⟨ylim, hylim, h⟩ := hC.ultrafilter_le_nhds (𝒰.map y) (le_principal_iff.mpr hmem)
  exact ⟨ylim, hylim, tendsto_iff_comap.mpr (by rwa [Ultrafilter.coe_map, map_le_iff_le_comap] at h)⟩

/-- Bilinearity of `frobDot` over a fivefold sum. -/
private theorem frobDot_sum5 (R a b c d e : Curv4 n) :
    frobDot R (a + b + c + d + e)
      = frobDot R a + frobDot R b + frobDot R c + frobDot R d + frobDot R e := by
  rw [frobDot_add_right, frobDot_add_right, frobDot_add_right, frobDot_add_right]


/-- Bilinearity of `frobDot` in its second argument over a difference. -/
private theorem frobDot_sub_right (R S T : Curv4 n) :
    frobDot R (S - T) = frobDot R S - frobDot R T := by
  rw [sub_eq_add_neg, frobDot_add_right, frobDot_neg_right]
  ring

/-- Continuity of `u ↦ frobDot u S`. -/
private theorem mp_frobDot_tendsto_const {ι : Type*} {l : Filter ι} {a : ι → Curv4 n} {A : Curv4 n}
    (ha : Tendsto a l (𝓝 A)) (S : Curv4 n) :
    Tendsto (fun i => frobDot (a i) S) l (𝓝 (frobDot A S)) := by
  have hcont : Continuous fun u : Curv4 n => frobDot u S := by
    unfold frobDot
    fun_prop
  exact (hcont.tendsto A).comp ha

/-- `frobDot` of two convergent sequences of curvature arrays. -/
private theorem mp_frobDot_tendsto {ι : Type*} {l : Filter ι} {a b : ι → Curv4 n} {A B : Curv4 n}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    Tendsto (fun i => frobDot (a i) (b i)) l (𝓝 (frobDot A B)) := by
  have h1 : Tendsto (fun i => frobDot A (b i)) l (𝓝 (frobDot A B)) := by
    have hb' : Tendsto (fun i => frobDot (b i) A) l (𝓝 (frobDot B A)) :=
      mp_frobDot_tendsto_const hb A
    have heq : (fun i => frobDot A (b i)) = fun i => frobDot (b i) A :=
      funext fun i => frobDot_comm _ _
    rw [heq]
    simpa [frobDot_comm] using hb'
  have hA : Tendsto (fun i => frobNorm (a i - A)) l (𝓝 0) := by
    have hs : Tendsto (fun i => a i - A) l (𝓝 (A - A)) := ha.sub tendsto_const_nhds
    have h := (continuous_frobNorm.tendsto (A - A)).comp hs
    have h0 : (A - A : Curv4 n) = 0 := sub_self A
    rw [h0, frobNorm_zero] at h
    simpa only [Function.comp_def] using h
  have hB : Tendsto (fun i => frobNorm (b i)) l (𝓝 (frobNorm B)) :=
    (continuous_frobNorm.tendsto B).comp hb
  have h2 : Tendsto (fun i => frobDot (a i - A) (b i)) l (𝓝 0) := by
    have hprod : Tendsto (fun i => frobNorm (a i - A) * frobNorm (b i)) l (𝓝 (0 * frobNorm B)) :=
      hA.mul hB
    have hzero : Tendsto (fun i => frobNorm (a i - A) * frobNorm (b i)) l (𝓝 0) := by
      simpa using hprod
    have habs : Tendsto (fun i => |frobDot (a i - A) (b i)|) l (𝓝 0) :=
      squeeze_zero (fun i => abs_nonneg _) (fun i => frob_cauchy_schwarz _ _) hzero
    have h3 : Tendsto (fun i => ‖frobDot (a i - A) (b i) - 0‖) l (𝓝 0) := by
      simpa [Real.norm_eq_abs] using habs
    exact (tendsto_iff_norm_sub_tendsto_zero).mpr h3
  have h3 : (fun i => frobDot (a i) (b i))
      = fun i => frobDot A (b i) + frobDot (a i - A) (b i) := by
    funext i
    rw [← frobDot_add_left]
    congr 1
    abel
  rw [h3]
  simpa using h1.add h2

/-- `C' * g ^ 2 - g * w → 0` when `g → 0`. -/
private theorem mp_tendsto_sq_sub_mul {ι : Type*} {l : Filter ι} {g w : ι → ℝ} {W C' : ℝ}
    (hg : Tendsto g l (𝓝 0)) (hw : Tendsto w l (𝓝 W)) :
    Tendsto (fun i => C' * g i ^ 2 - g i * w i) l (𝓝 0) := by
  have h1 : Tendsto (fun i => g i ^ 2) l (𝓝 0) := by simpa [pow_two] using hg.mul hg
  have h2 : Tendsto (fun i => g i * w i) l (𝓝 (0 * W)) := hg.mul hw
  have h3 : Tendsto (fun i => C' * g i ^ 2) l (𝓝 (C' * 0)) := h1.const_mul C'
  have h4 : Tendsto (fun i => C' * g i ^ 2 - g i * w i) l (𝓝 (C' * 0 - 0 * W)) := h3.sub h2
  simpa using h4

/-- Limit comparison with `ε / 2 - C' * g` as the lower function. -/
private theorem mp_limit_compare {ι : Type*} {l : Filter ι} [NeBot l] {g D : ι → ℝ} {B C' ε : ℝ}
    (hg : Tendsto g l (𝓝 0)) (hD : Tendsto D l (𝓝 B))
    (hbound : ∀ᶠ i in l, ε / 2 - C' * g i < D i) : ε / 2 ≤ B :=
  mp_le_of_tendsto_le (mp_tendsto_const_sub_mul hg C' (ε / 2)) hD
    (hbound.mono fun _ hm => le_of_lt hm)


/-- For a family of functions `d t` on the compact space `X` that is continuous at each fixed
time, the supremum over `X` is attained.  (This replaces the first half of `mp_sup_props`, which
used *joint* continuity.) -/
private theorem mp_sup_attained {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (d : ℝ → X → ℝ) {a b : ℝ}
    (hdsp : ∀ t ∈ Icc a b, ContinuousOn (d t) univ) :
    ∀ t ∈ Icc a b, ∃ x : X, (∀ y : X, d t y ≤ d t x) ∧
      sSup ((d t) '' univ) = d t x := by
  intro t ht
  have hc : ContinuousOn (d t) univ := hdsp t ht
  have hc' : Continuous (d t) := continuousOn_univ.mp hc
  obtain ⟨x, -, hx⟩ :=
    IsCompact.exists_isMaxOn isCompact_univ ⟨Classical.arbitrary X, trivial⟩ hc
  refine ⟨x, fun y => (isMaxOn_iff.mp hx) y trivial, ?_⟩
  have hbdd : BddAbove ((d t) '' univ) := (isCompact_univ.image hc').bddAbove
  refine le_antisymm ?_ (le_csSup hbdd ⟨x, trivial, rfl⟩)
  exact csSup_le ⟨d t x, x, trivial, rfl⟩ (fun v hv => by
    obtain ⟨y, -, rfl⟩ := hv
    exact (isMaxOn_iff.mp hx) y trivial)

/-- Nearest point of a closed convex nonempty bounded set of curvature arrays to a point `P`,
together with the unit outward normal at the nearest point when `P ∉ K`. -/
private theorem mp_nearest_normal {n : ℕ} (K : Set (Curv4 n)) (hKc : IsClosed K)
    (hKcv : Convex ℝ K) (hKne : K.Nonempty)
    (hKbd : ∃ ρ, ∀ S ∈ K, frobNorm S ≤ ρ) (P : Curv4 n) :
    ∃ v ∈ K, (∀ S ∈ K, frobDist P v ≤ frobDist P S) ∧
      (P ∉ K → ∃ u, frobNorm u = 1 ∧ frobDot u (P - v) = frobDist P v ∧
        ∀ S ∈ K, frobDot u (S - v) ≤ 0) := by
  classical
  obtain ⟨ρ, hρ⟩ := hKbd
  have hbdd : Bornology.IsBounded K :=
    (Metric.isBounded_closedBall (x := (0 : Curv4 n)) (r := max ρ 0)).subset (by
      intro S hS
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (le_trans (norm_le_frobNorm S) (hρ S hS)) (le_max_left ρ 0))
  have hcomp : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKc, hbdd⟩
  have hcont : ContinuousOn (fun S => frobDist P S) K :=
    (continuous_frobNorm.comp (continuous_const.sub continuous_id)).continuousOn
  obtain ⟨v, hvK, hvmin⟩ := hcomp.exists_isMinOn hKne hcont
  refine ⟨v, hvK, fun S hS => (isMinOn_iff.mp hvmin) S hS, ?_⟩
  intro hPnotK
  have hpos : 0 < frobDist P v := by
    rcases lt_or_eq_of_le (frobDist_nonneg P v) with h | h
    · exact h
    · exfalso
      exact hPnotK ((frobDist_eq_zero_iff P v).mp h.symm ▸ hvK)
  refine ⟨(frobDist P v)⁻¹ • (P - v), ?_, ?_, ?_⟩
  · rw [frobNorm_smul, abs_of_pos (inv_pos.mpr hpos)]
    show (frobDist P v)⁻¹ * frobDist P v = 1
    field_simp
  · rw [frobDot_smul_left, ← frobNorm_sq]
    show (frobDist P v)⁻¹ * frobDist P v ^ 2 = frobDist P v
    field_simp
  · intro S hS
    have hmin : ∀ S ∈ K, frobDist P v ≤ frobDist P S := fun S hS => (isMinOn_iff.mp hvmin) S hS
    have hnp := frobDot_nonpos_of_frobDist_min n K hKcv P v hvK hmin S hS
    rw [frobDot_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt hpos)) hnp

end Work.Diff.MP

namespace Work.Diff.MP

open Set Filter Submission.Diff.Alg
open scoped Topology
open Work.Diff.MP

/-- Lower semicontinuity on `[a,b]` together with upper semicontinuity from the right gives
continuity from the right at every `t ∈ [a,b)`. -/
private theorem mp_continuous_rcont {f : ℝ → ℝ} {a b : ℝ}
    (hlsc : LowerSemicontinuousOn f (Icc a b))
    (hrusc : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      f (t + h) ≤ f t + ε) :
    ∀ t ∈ Ico a b, ContinuousWithinAt f (Ici t) t := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have htIcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    exists_delta_of_lsc (hlsc t htIcc) (sub_lt_self (f t) hε2)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hrusc t ht (ε / 2) hε2
  refine ⟨min δ₁ (min δ₂ (b - t)), lt_min hδ₁ (lt_min hδ₂ (by linarith [ht.2])), ?_⟩
  intro y hy hyt
  have hy' : t ≤ y := hy
  rw [Real.dist_eq] at hyt ⊢
  have h1 : |y - t| < δ₁ := lt_of_lt_of_le hyt (min_le_left _ _)
  have h2 : |y - t| < δ₂ :=
    lt_of_lt_of_le hyt (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : |y - t| < b - t :=
    lt_of_lt_of_le hyt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hnn : (0 : ℝ) ≤ y - t := by linarith
  have hyb : y ≤ b := by
    have h4 : y - t < b - t := by rwa [abs_of_nonneg hnn] at h3
    linarith
  have hmem : y ∈ Icc a b := ⟨le_trans ht.1 hy', hyb⟩
  have hlow : f t - ε / 2 < f y := hδ₁' y hmem h1
  have hup : f y ≤ f t + ε / 2 := by
    rcases eq_or_lt_of_le hy' with heq | hlt
    · rw [← heq]; linarith
    · have hh : 0 < y - t := sub_pos.mpr hlt
      have hle : y - t ≤ δ₂ := by rw [abs_of_nonneg hnn] at h2; linarith
      have h5 := hδ₂' (y - t) hh hle (by linarith [hyb])
      rwa [add_sub_cancel] at h5
  exact abs_lt.mpr ⟨by linarith, by linarith⟩


private theorem mp_dini_lsc_band {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t) (ha : f a = 0)
    (hlsc : LowerSemicontinuousOn f (Icc a b))
    (hrusc : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      f (t + h) ≤ f t + ε)
    (hD : ∀ t ∈ Ico a b, 0 < f t → ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      f (t + h) ≤ f t + h * (C * f t + ε)) :
    ∀ t ∈ Icc a b, f t = 0 := by
  have _ := hab
  -- the two consequences of the hypotheses that the Dini machinery needs
  have hL : ∀ t ∈ Ioc a b, ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f t ≤ f (t - s) + ε :=
    lsc_left_of_lsc hlsc
  have hRt : ∀ t ∈ Ico a b, ContinuousWithinAt f (Ici t) t :=
    mp_continuous_rcont hlsc hrusc
  intro t₁ ht₁
  by_contra hne
  have hft₁ : 0 < f t₁ := lt_of_le_of_ne (hnonneg t₁ ht₁) (Ne.symm hne)
  -- the last zero of `f` below `t₁`
  obtain ⟨t₀, ht₀I, hft₀, hpos⟩ := exists_last_zero_of_lsc ha hnonneg hlsc ht₁
  have ht₀lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₀I.2 with h | h
    · exact h
    · exfalso
      rw [h] at hft₀
      linarith
  -- on every `[s,t] ⊆ (t₀,t₁]` the rotated function `g r = f r * exp (-(C*r))` is non-increasing
  have hkey : ∀ s t : ℝ, t₀ < s → s < t → t ≤ t₁ →
      f t * Real.exp (-(C * t)) ≤ f s * Real.exp (-(C * s)) := by
    intro s t hs hst hst₁
    have htb : t ≤ b := le_trans hst₁ ht₁.2
    have has : a < s := lt_of_le_of_lt ht₀I.1 hs
    refine dini_mono_of_lsc (u := fun r => f r * Real.exp (-(C * r))) (α := s) (β := t)
      hst.le ?_ ?_ ?_
    · -- lower semicontinuity of `g` at interior points
      intro z hz η hη
      have hzs : s < z := hz.1
      have hzt : z < t := hz.2
      have hzIoc : z ∈ Ioc a b := ⟨lt_trans has hzs, (lt_of_lt_of_le hzt htb).le⟩
      have hzIco : z ∈ Ico a b := ⟨le_of_lt (lt_trans has hzs), lt_of_lt_of_le hzt htb⟩
      exact lsc_mul_exp (hL z hzIoc) (hRt z hzIco) η hη
    · -- lower semicontinuity of `g` at the right endpoint, from the left
      exact lsc_left_mul_exp (hL t ⟨lt_trans has hst, htb⟩)
    · -- the upper right Dini bound for `g`
      intro z hz ε hε
      have hzs : s ≤ z := hz.1
      have hzt : z < t := hz.2
      have hfz : 0 < f z := hpos z ⟨lt_of_lt_of_le hs hzs, le_of_lt (lt_of_lt_of_le hzt hst₁)⟩
      have hzIco : z ∈ Ico a b :=
        ⟨le_trans has.le hzs, lt_of_lt_of_le hzt htb⟩
      obtain ⟨δ, hδ, hδ'⟩ :=
        local_dini_shift (C := C) (b := b) (t := z) (le_of_lt (lt_of_lt_of_le hzt htb)) hfz
          (fun ε hε => by
            obtain ⟨δ', hδ2, hδ3⟩ := hD z hzIco hfz ε hε
            exact ⟨δ', hδ2, fun h hh hhle hzb => hδ3 h hh hhle hzb⟩) ε hε
      exact ⟨δ, hδ, fun h hh hhle hztb => hδ' h hh hhle (le_trans hztb htb)⟩
  -- let `s ↓ t₀` and use upper semicontinuity from the right at `t₀`
  have hfin : ∀ η > 0, f t₁ ≤ η := by
    intro η hη
    set K : ℝ := Real.exp (max 0 (C * (t₁ - t₀))) with hKdef
    have hKpos : 0 < K := Real.exp_pos _
    have hε : 0 < η / K := div_pos hη hKpos
    obtain ⟨δ, hδ, hδ'⟩ := hrusc t₀ ⟨ht₀I.1, lt_of_lt_of_le ht₀lt ht₁.2⟩ (η / K) hε
    have hgap : 0 < t₁ - t₀ := sub_pos.mpr ht₀lt
    set hh : ℝ := min δ (t₁ - t₀) / 2 with hhdef
    have hhpos : 0 < hh := by rw [hhdef]; exact div_pos (lt_min hδ hgap) two_pos
    have hhδ : hh ≤ δ := by
      rw [hhdef]; have := min_le_left δ (t₁ - t₀); linarith
    have hhgap : hh < t₁ - t₀ := by
      rw [hhdef]; have := min_le_right δ (t₁ - t₀); linarith
    have h2 : t₀ < t₀ + hh := by linarith
    have h3 : t₀ + hh < t₁ := by linarith
    have hfnn : 0 ≤ f (t₀ + hh) := le_of_lt (hpos (t₀ + hh) ⟨h2, h3.le⟩)
    have hfs : f (t₀ + hh) ≤ η / K := by
      have h1 := hδ' hh hhpos hhδ (by linarith [h3, ht₁.2])
      rwa [hft₀, zero_add] at h1
    have h4 : f t₁ ≤ f (t₀ + hh) * Real.exp (C * (t₁ - (t₀ + hh))) := by
      have h4' := hkey (t₀ + hh) t₁ h2 h3 le_rfl
      have hmul := mul_le_mul_of_nonneg_right h4' (Real.exp_pos (C * t₁)).le
      have hleft : f t₁ * Real.exp (-(C * t₁)) * Real.exp (C * t₁) = f t₁ := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have hright : f (t₀ + hh) * Real.exp (-(C * (t₀ + hh))) * Real.exp (C * t₁)
          = f (t₀ + hh) * Real.exp (C * (t₁ - (t₀ + hh))) := by
        rw [mul_assoc, ← Real.exp_add,
          show -(C * (t₀ + hh)) + C * t₁ = C * (t₁ - (t₀ + hh)) by ring]
      rwa [hleft, hright] at hmul
    have h5 : Real.exp (C * (t₁ - (t₀ + hh))) ≤ K := by
      rw [hKdef]
      refine Real.exp_le_exp.mpr ?_
      rcases le_total 0 C with hC | hC
      · have h7 : C * (t₁ - (t₀ + hh)) ≤ C * (t₁ - t₀) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
        exact le_trans h7 (le_max_right _ _)
      · have h7 : C * (t₁ - (t₀ + hh)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC (by linarith)
        exact le_trans h7 (le_max_left _ _)
    have h6 : f (t₀ + hh) * Real.exp (C * (t₁ - (t₀ + hh))) ≤ η / K * K :=
      mul_le_mul hfs h5 (Real.exp_pos _).le (div_pos hη hKpos).le
    have h7 : η / K * K = η := div_mul_cancel₀ η hKpos.ne'
    linarith
  have hle0 : f t₁ ≤ 0 := by
    by_contra hcon
    have hpos₁ : 0 < f t₁ := not_le.mp hcon
    have h9 := hfin (f t₁ / 2) (by linarith)
    linarith
  linarith

theorem max_principle_lsc
    {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (K : ℝ → Set (Submission.Diff.Alg.Curv4 n)) (d : ℝ → X → ℝ)
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hKcl : ∀ t ∈ Set.Icc a b, IsClosed (K t))
    (hKcv : ∀ t ∈ Set.Icc a b, Convex ℝ (K t))
    (hKne : ∀ t ∈ Set.Icc a b, (K t).Nonempty)
    (hKbd : ∀ t ∈ Set.Icc a b, ∃ ρ, ∀ S ∈ K t, Work.Diff.MP.frobNorm S ≤ ρ)
    (hdnn : ∀ t ∈ Set.Icc a b, ∀ x, 0 ≤ d t x)
    (hdsp : ∀ t ∈ Set.Icc a b, ContinuousOn (d t) Set.univ)
    (hlscF : ∀ t ∈ Set.Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Set.Icc a b, |s - t| ≤ δ →
      sSup ((d t) '' Set.univ) ≤ sSup ((d s) '' Set.univ) + ε)
    (hruscF : ∀ t ∈ Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      sSup ((d (t + h)) '' Set.univ) ≤ sSup ((d t) '' Set.univ) + ε)
    (hpush : ∀ t ∈ Set.Ico a b, ∃ δ > 0, ∃ C', ∀ h : ℝ, 0 < h → h ≤ δ →
      ∀ S ∈ K t, ∃ S' ∈ K (t + h),
        Work.Diff.MP.frobDist S' (S + h • Submission.Diff.Alg.Q S) ≤ C' * h ^ 2)
    (hmodel : ∀ t ∈ Set.Ioo a b, ∀ x : X,
      ∃ (δ : ℝ) (_ : 0 < δ) (U : Set X) (_ : U ∈ nhds x)
        (Rl dRl : ℝ → X → Submission.Diff.Alg.Curv4 n),
        (∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U,
          d s y = Work.Diff.MP.frobInfDist (Rl s y) (K s)) ∧
        ContinuousOn (fun p : ℝ × X => (Rl p.1 p.2, dRl p.1 p.2))
          (Set.prod (Set.Icc t (t + δ)) U) ∧
        (∀ ε > 0, ∃ δ' > 0, ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ U,
          Work.Diff.MP.frobDist (Rl (t + h) y)
            (Rl t y + h • (dRl t y + Submission.Diff.Alg.Q (Rl t y))) ≤ ε * h) ∧
        (∀ ℓ : Submission.Diff.Alg.Curv4 n, Work.Diff.MP.frobNorm ℓ ≤ 1 →
          (∀ z ∈ U, Work.Diff.MP.frobDot ℓ (Rl t z) ≤ Work.Diff.MP.frobDot ℓ (Rl t x)) →
          Work.Diff.MP.frobDot ℓ (dRl t x) ≤ 0) ∧
        (∀ y ∈ U, ∀ S ∈ K t,
          Work.Diff.MP.frobDist (Submission.Diff.Alg.Q (Rl t y)) (Submission.Diff.Alg.Q S)
            ≤ C * Work.Diff.MP.frobDist (Rl t y) S))
    (hd0 : ∀ x, d a x = 0) :
    ∀ t ∈ Set.Icc a b, ∀ x, d t x = 0 := by
  classical
  rcases eq_or_lt_of_le hab with habeq | hablt
  · -- the degenerate case `b = a`
    intro t ht x
    have hta : t = a := by
      have ht' : t ≤ a := by rw [habeq]; exact ht.2
      exact le_antisymm ht' ht.1
    rw [hta]
    exact hd0 x
  have hmax_raw := mp_sup_attained d hdsp
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ t : ℝ, F t = sSup ((d t) '' univ) :=
    ⟨fun t => sSup ((d t) '' univ), fun t => rfl⟩
  have hmax : ∀ u ∈ Icc a b, ∃ y : X, (∀ z : X, d u z ≤ d u y) ∧ F u = d u y := by
    intro u hu
    obtain ⟨y, hy, hyeq⟩ := hmax_raw u hu
    exact ⟨y, hy, by rw [hF u]; exact hyeq⟩
  have hFle : ∀ u ∈ Icc a b, ∀ y : X, d u y ≤ F u := by
    intro u hu y
    obtain ⟨z, hz, hzF⟩ := hmax u hu
    rw [hzF]; exact hz y
  have hFnonneg : ∀ u ∈ Icc a b, 0 ≤ F u := by
    intro u hu
    obtain ⟨z, -, hzF⟩ := hmax u hu
    rw [hzF]; exact hdnn u hu z
  have hFa : F a = 0 := by
    obtain ⟨z, -, hzF⟩ := hmax a ⟨le_rfl, hab⟩
    rw [hzF]; exact hd0 z
  -- the sup function is lower semi-continuous ...
  have hlscl : LowerSemicontinuousOn F (Icc a b) := by
    intro t ht
    change LowerSemicontinuousWithinAt F (Icc a b) t
    rw [lowerSemicontinuousWithinAt_iff]
    intro y hy
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    obtain ⟨δ, hδ, hδ'⟩ := hlscF t ht (F t - (y + F t) / 2) (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro s hs
    have hsb : s ∈ Metric.ball t δ := hs.1
    have hsI : s ∈ Icc a b := hs.2
    show y < F s
    have hsδ : |s - t| ≤ δ :=
      le_of_lt (by rwa [Metric.mem_ball, Real.dist_eq] at hsb)
    have h1 : F t ≤ F s + (F t - (y + F t) / 2) := by
      simpa only [hF] using hδ' s hsI hsδ
    linarith
  -- the same regularity hypothesis, written for the sup function `F`
  have hruscF' : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      F (t + h) ≤ F t + ε := by
    intro t ht ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hruscF t ht ε hε
    exact ⟨δ, hδ, fun h hh hhle hb => by simpa only [hF] using hδ' h hh hhle hb⟩
  -- ... and upper semi-continuous from the right, hence right-continuous
  have hcontF : ∀ t ∈ Ico a b, ContinuousWithinAt F (Ici t) t :=
    mp_continuous_rcont hlscl hruscF'
  have hkey : ∀ t ∈ Ico a b, 0 < F t → ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ →
      t + h ≤ b → F (t + h) ≤ F t + h * (C * F t + ε) := by
    intro t ht hFt ε hε
    have htIcc : t ∈ Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    by_contra hcon
    push_neg at hcon
    choose hseq hh using fun m : ℕ => hcon (1 / ((m : ℝ) + 1)) (by positivity)
    have hhpos : ∀ m, 0 < hseq m := fun m => (hh m).1
    have hhle : ∀ m, hseq m ≤ 1 / ((m : ℝ) + 1) := fun m => (hh m).2.1
    have hhtb : ∀ m, t + hseq m ≤ b := fun m => (hh m).2.2.1
    have hhbad : ∀ m, F t + hseq m * (C * F t + ε) < F (t + hseq m) := fun m => (hh m).2.2.2
    have hlim_hat : Tendsto hseq atTop (𝓝 0) := by
      have hone : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (f := hseq) (g := fun _ : ℕ => (0 : ℝ))
        (h := fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) tendsto_const_nhds hone ?_ ?_
      · intro m; exact le_of_lt (hhpos m)
      · intro m; exact hhle m
    obtain ⟨𝒰, h𝒰le⟩ : ∃ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop :=
      ⟨Ultrafilter.of atTop, Ultrafilter.of_le atTop⟩
    have hlim_h : Tendsto hseq 𝒰 (𝓝 0) := hlim_hat.mono_left h𝒰le
    have hTmem : ∀ m, t + hseq m ∈ Icc a b := fun m => ⟨by linarith [ht.1, hhpos m], hhtb m⟩
    choose x hxmax hxeq using fun m => hmax (t + hseq m) (hTmem m)
    obtain ⟨xlim, hxlim⟩ := mp_ultra_compact 𝒰 x
    have hpair : Tendsto (fun m => (t + hseq m, x m)) 𝒰 (𝓝 (t, xlim)) := by
      refine (Prod.tendsto_iff _ _).mpr ⟨?_, hxlim⟩
      simpa using (tendsto_const_nhds.add hlim_h)
    have hta : a ≠ t := by
      intro h
      rw [← h] at hFt
      linarith [hFa]
    have htIoo : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 hta, ht.2⟩
    obtain ⟨δ₀, hδ₀pos, U, hUx, Rl, dRl, hdom, hcontm, hexp, hmp, hlip⟩ :=
      hmodel t htIoo xlim
    obtain ⟨δpush, hδpushpos, C', hpushex⟩ := hpush t ht
    obtain ⟨δexp, hδexppos, hexpex⟩ := hexp (ε / 2) (by linarith)
    have hIcc₁ : t ∈ Icc t (t + δ₀) := ⟨le_rfl, by linarith⟩
    have hxU : ∀ᶠ m in 𝒰, x m ∈ U := Filter.le_def.mp hxlim U hUx
    have hsmall : ∀ᶠ m in 𝒰, hseq m ≤ min δpush (min δ₀ δexp) := by
      have hη : (0 : ℝ) < min δpush (min δ₀ δexp) :=
        lt_min hδpushpos (lt_min hδ₀pos hδexppos)
      exact Filter.Eventually.filter_mono h𝒰le (hlim_hat.eventually (Iic_mem_nhds hη))
    set P : ℕ → Curv4 n := fun m => Rl (t + hseq m) (x m) with hPdef
    have hPlim : Tendsto P 𝒰 (𝓝 (Rl t xlim)) := by
      have hcw : ContinuousWithinAt (fun p : ℝ × X => Rl p.1 p.2)
          (Icc t (t + δ₀) ×ˢ U) (t, xlim) :=
        (hcontm.fst).continuousWithinAt ⟨hIcc₁, mem_of_mem_nhds hUx⟩
      refine mp_tendsto_comp hcw hpair ?_
      filter_upwards [hxU, hsmall] with m hmU hms
      have h1 : hseq m ≤ δ₀ := le_trans hms (le_trans (min_le_right _ _) (min_le_left _ _))
      refine ⟨⟨?_, ?_⟩, hmU⟩
      · change t ≤ t + hseq m
        linarith [hhpos m]
      · change t + hseq m ≤ t + δ₀
        linarith
    -- nearest points and outward normals
    have hv : ∀ m, ∃ v ∈ K (t + hseq m),
        (∀ S ∈ K (t + hseq m), frobDist (P m) v ≤ frobDist (P m) S) ∧
        (P m ∉ K (t + hseq m) → ∃ u, frobNorm u = 1 ∧
          frobDot u (P m - v) = frobDist (P m) v ∧
          ∀ S ∈ K (t + hseq m), frobDot u (S - v) ≤ 0) :=
      fun m => mp_nearest_normal (K (t + hseq m)) (hKcl _ (hTmem m)) (hKcv _ (hTmem m))
        (hKne _ (hTmem m)) (hKbd _ (hTmem m)) (P m)
    choose v hvK hvi using hv
    have hmin : ∀ m, ∀ S ∈ K (t + hseq m), frobDist (P m) (v m) ≤ frobDist (P m) S :=
      fun m => (hvi m).1
    have hnex : ∀ m, P m ∉ K (t + hseq m) → ∃ u, frobNorm u = 1 ∧
        frobDot u (P m - v m) = frobDist (P m) (v m) ∧
        ∀ S ∈ K (t + hseq m), frobDot u (S - v m) ≤ 0 :=
      fun m h => (hvi m).2 h
    set hn : ℕ → Curv4 n :=
      fun m => if h : P m ∉ K (t + hseq m) then Classical.choose (hnex m h) else 0 with hndef
    have hn_norm : ∀ m (h : P m ∉ K (t + hseq m)), frobNorm (hn m) = 1 := by
      intro m h
      simp only [hndef]
      rw [dif_pos h]
      exact (Classical.choose_spec (hnex m h)).1
    have hn_dot : ∀ m (h : P m ∉ K (t + hseq m)),
        frobDot (hn m) (P m - v m) = frobDist (P m) (v m) := by
      intro m h
      simp only [hndef]
      rw [dif_pos h]
      exact (Classical.choose_spec (hnex m h)).2.1
    have hn_supp : ∀ m (h : P m ∉ K (t + hseq m)), ∀ S ∈ K (t + hseq m),
        frobDot (hn m) (S - v m) ≤ 0 := by
      intro m h S hS
      simp only [hndef]
      rw [dif_pos h]
      exact (Classical.choose_spec (hnex m h)).2.2 S hS
    have hvdist : ∀ m, x m ∈ U → hseq m ≤ δ₀ → frobDist (P m) (v m) = F (t + hseq m) := by
      intro m hmU hmδ₀
      have h1 : frobDist (P m) (v m) = frobInfDist (P m) (K (t + hseq m)) := by
        refine le_antisymm (le_frobInfDist (hKne _ (hTmem m)) (fun S hS => hmin m S hS))
          (frobInfDist_le (hvK m))
      have h2 : frobInfDist (P m) (K (t + hseq m)) = F (t + hseq m) := by
        rw [hxeq m]
        exact (hdom (t + hseq m) ⟨by linarith [hhpos m], by linarith⟩ (x m) hmU).symm
      rw [h1, h2]
    have hPnotK : ∀ᶠ m in 𝒰, P m ∉ K (t + hseq m) := by
      filter_upwards [hxU, hsmall] with m hmU hms
      have hmδ₀ : hseq m ≤ δ₀ := le_trans hms (le_trans (min_le_right _ _) (min_le_left _ _))
      intro hPin
      have h1 : frobInfDist (P m) (K (t + hseq m)) = 0 := frobInfDist_eq_zero_of_mem hPin
      have h2 : frobInfDist (P m) (K (t + hseq m)) = F (t + hseq m) := by
        rw [hxeq m]
        exact (hdom (t + hseq m) ⟨by linarith [hhpos m],
          by linarith⟩ (x m) hmU).symm
      have h4 : 0 < F (t + hseq m) := by
        have h5 := hhbad m
        have h6 : 0 < C * F t + ε := by nlinarith [hFt, hC, hε]
        have h7 : 0 < hseq m * (C * F t + ε) := mul_pos (hhpos m) h6
        linarith
      exact (ne_of_gt h4) (by rw [← h2]; exact h1)
    have hlimPn : Tendsto (fun m => frobNorm (P m)) 𝒰 (𝓝 (frobNorm (Rl t xlim))) :=
      continuous_frobNorm.continuousAt.tendsto.comp hPlim
    have hPbound : ∀ᶠ m in 𝒰, frobNorm (P m) ≤ frobNorm (Rl t xlim) + 1 :=
      hlimPn.eventually (Iic_mem_nhds (by linarith))
    have hTlim : Tendsto (fun m => t + hseq m) 𝒰 (𝓝 t) := by
      simpa using (tendsto_const_nhds.add hlim_h)
    have hlimF : Tendsto (fun m => F (t + hseq m)) 𝒰 (𝓝 (F t)) :=
      mp_tendsto_comp (hcontF t ht) hTlim
        (Filter.Eventually.of_forall (fun m => by
          show t ≤ t + hseq m
          linarith [hhpos m]))
    have hFbound : ∀ᶠ m in 𝒰, F (t + hseq m) ≤ F t + 1 :=
      hlimF.eventually (Iic_mem_nhds (by linarith))
    have hvbound : ∀ᶠ m in 𝒰, frobNorm (v m) ≤ frobNorm (Rl t xlim) + (F t + 1) + 1 := by
      filter_upwards [hPbound, hFbound, hxU, hsmall] with m hPm hFm hmU hms
      have hmδ₀ : hseq m ≤ δ₀ := le_trans hms (le_trans (min_le_right _ _) (min_le_left _ _))
      have h1 : frobNorm (v m) ≤ frobNorm (P m) + frobNorm (v m - P m) := by
        have h := frobNorm_add_le (P m) (v m - P m)
        rwa [show P m + (v m - P m) = v m by abel] at h
      have h2 : frobNorm (v m - P m) = frobDist (P m) (v m) := by
        have h : v m - P m = -(P m - v m) := by abel
        rw [h, frobNorm_neg]
        rfl
      have h3 : frobDist (P m) (v m) = F (t + hseq m) := hvdist m hmU hmδ₀
      linarith [h1, h2, h3, hPm, hFm]
    obtain ⟨vlim, hvlimmem, hvlim⟩ :=
      mp_ultra_isCompact (isCompact_frobBall n (frobNorm (Rl t xlim) + (F t + 1) + 1)).1 𝒰 hvbound
    obtain ⟨nlim, hnlimmem, hnlim⟩ := mp_ultra_isCompact (isCompact_frobBall n 1).2 𝒰
      (by filter_upwards [hPnotK] with m hm; exact hn_norm m hm)
    -- the one-step estimate
    have hchain : ∀ᶠ m in 𝒰, ε / 2 - C' * hseq m < frobDot (hn m) (dRl t (x m)) := by
      filter_upwards [hxU, hsmall, hPnotK] with m hmU hms hmPnotK
      have hmδpush : hseq m ≤ δpush := le_trans hms (min_le_left _ _)
      have hmδ₀ : hseq m ≤ δ₀ := le_trans hms (le_trans (min_le_right _ _) (min_le_left _ _))
      have hmδexp : hseq m ≤ δexp := le_trans hms (le_trans (min_le_right _ _) (min_le_right _ _))
      obtain ⟨v0, hv0K, hv0min, -⟩ := mp_nearest_normal (K t) (hKcl t htIcc) (hKcv t htIcc)
        (hKne t htIcc) (hKbd t htIcc) (Rl t (x m))
      have hv0dist : frobDist (Rl t (x m)) v0 = d t (x m) := by
        have h1 : frobDist (Rl t (x m)) v0 = frobInfDist (Rl t (x m)) (K t) := by
          refine le_antisymm (le_frobInfDist (hKne t htIcc) (fun S hS => hv0min S hS))
            (frobInfDist_le hv0K)
        rw [h1]
        exact (hdom t hIcc₁ (x m) hmU).symm
      have hv0dist' : frobNorm (Rl t (x m) - v0) = d t (x m) := hv0dist
      have hv0Ft : d t (x m) ≤ F t := hFle t htIcc (x m)
      obtain ⟨S', hS'K, hS'dist⟩ := hpushex (hseq m) (hhpos m) hmδpush v0 hv0K
      have hE : frobNorm (P m - (Rl t (x m) + hseq m • (dRl t (x m) + Q (Rl t (x m)))))
          ≤ (ε / 2) * hseq m := by
        have h := hexpex (hseq m) (hhpos m) hmδexp (x m) hmU
        rwa [frobDist] at h
      have hsplit : P m - v m
          = (P m - (Rl t (x m) + hseq m • (dRl t (x m) + Q (Rl t (x m)))))
            + (Rl t (x m) - v0) + (v0 + hseq m • Q v0 - v m)
            + hseq m • (dRl t (x m)) + hseq m • (Q (Rl t (x m)) - Q v0) := by
        simp only [hPdef]
        module
      have hdot : frobDot (hn m) (P m - v m)
          = frobDot (hn m) (P m - (Rl t (x m) + hseq m • (dRl t (x m) + Q (Rl t (x m)))))
            + frobDot (hn m) (Rl t (x m) - v0)
            + frobDot (hn m) (v0 + hseq m • Q v0 - v m)
            + hseq m * frobDot (hn m) (dRl t (x m))
            + hseq m * frobDot (hn m) (Q (Rl t (x m)) - Q v0) := by
        rw [hsplit, frobDot_sum5, frobDot_smul_right, frobDot_smul_right]
      have hb1 : frobDot (hn m) (P m - (Rl t (x m) + hseq m • (dRl t (x m) + Q (Rl t (x m)))))
          ≤ (ε / 2) * hseq m := by
        have h := frob_cauchy_schwarz (hn m)
          (P m - (Rl t (x m) + hseq m • (dRl t (x m) + Q (Rl t (x m)))))
        rw [hn_norm m hmPnotK, one_mul] at h
        exact le_trans (le_abs_self _) (le_trans h hE)
      have hb2 : frobDot (hn m) (Rl t (x m) - v0) ≤ F t := by
        have h1 : frobDot (hn m) (Rl t (x m) - v0) ≤ frobNorm (Rl t (x m) - v0) := by
          have h := frob_cauchy_schwarz (hn m) (Rl t (x m) - v0)
          rw [hn_norm m hmPnotK, one_mul] at h
          exact le_trans (le_abs_self _) h
        linarith [h1, hv0dist', hv0Ft]
      have hb3 : frobDot (hn m) (v0 + hseq m • Q v0 - v m) ≤ C' * hseq m ^ 2 := by
        have h1 : frobDot (hn m) (v0 + hseq m • Q v0 - v m)
            = frobDot (hn m) (S' - v m) + frobDot (hn m) (v0 + hseq m • Q v0 - S') := by
          have h : v0 + hseq m • Q v0 - v m
              = (S' - v m) + (v0 + hseq m • Q v0 - S') := by abel
          rw [h, frobDot_add_right]
        rw [h1]
        have h4 : frobDot (hn m) (S' - v m) ≤ 0 := hn_supp m hmPnotK S' hS'K
        have h5 : frobDot (hn m) (v0 + hseq m • Q v0 - S') ≤ C' * hseq m ^ 2 := by
          have h6 : frobDot (hn m) (v0 + hseq m • Q v0 - S')
              ≤ frobNorm (v0 + hseq m • Q v0 - S') := by
            have h := frob_cauchy_schwarz (hn m) (v0 + hseq m • Q v0 - S')
            rw [hn_norm m hmPnotK, one_mul] at h
            exact le_trans (le_abs_self _) h
          have h7 : frobNorm (v0 + hseq m • Q v0 - S') = frobDist S' (v0 + hseq m • Q v0) := by
            have hneg : S' - (v0 + hseq m • Q v0) = -(v0 + hseq m • Q v0 - S') := by abel
            rw [frobDist, hneg, frobNorm_neg]
          linarith [h6, h7, hS'dist]
        linarith [h4, h5]
      have hb4 : frobDot (hn m) (Q (Rl t (x m)) - Q v0) ≤ C * F t := by
        have h1 : frobDot (hn m) (Q (Rl t (x m)) - Q v0)
            ≤ frobNorm (Q (Rl t (x m)) - Q v0) := by
          have h := frob_cauchy_schwarz (hn m) (Q (Rl t (x m)) - Q v0)
          rw [hn_norm m hmPnotK, one_mul] at h
          exact le_trans (le_abs_self _) h
        have h2 : frobNorm (Q (Rl t (x m)) - Q v0) = frobDist (Q (Rl t (x m))) (Q v0) := rfl
        have h3 : frobDist (Q (Rl t (x m))) (Q v0) ≤ C * frobDist (Rl t (x m)) v0 :=
          hlip (x m) hmU v0 hv0K
        have h4 : frobDist (Rl t (x m)) v0 = d t (x m) := hv0dist
        nlinarith [h1, h2, h3, h4, hv0Ft, hC]
      have hmain : F (t + hseq m) ≤ F t + (ε / 2) * hseq m + C' * hseq m ^ 2
          + hseq m * frobDot (hn m) (dRl t (x m)) + hseq m * (C * F t) := by
        have hdveq : F (t + hseq m) = frobDot (hn m) (P m - v m) := by
          rw [hn_dot m hmPnotK]
          exact (hvdist m hmU hmδ₀).symm
        rw [hdveq, hdot]
        linarith [hb1, hb2, hb3,
          mul_le_mul_of_nonneg_left hb4 (le_of_lt (hhpos m))]
      have hA : hseq m * (C * F t + ε) < (ε / 2) * hseq m + C' * hseq m ^ 2
          + hseq m * frobDot (hn m) (dRl t (x m)) + hseq m * (C * F t) := by
        linarith [hmain, hhbad m]
      have e1 : hseq m * (C * F t + ε) = hseq m * (C * F t) + hseq m * ε := by ring
      have e2 : (ε / 2) * hseq m + C' * hseq m ^ 2
            + hseq m * frobDot (hn m) (dRl t (x m)) + hseq m * (C * F t)
          = hseq m * (ε / 2 + C' * hseq m + frobDot (hn m) (dRl t (x m)))
            + hseq m * (C * F t) := by ring
      have hB : hseq m * ε < hseq m * (ε / 2 + C' * hseq m + frobDot (hn m) (dRl t (x m))) := by
        linarith [hA, e1, e2]
      have hC1 : ε < ε / 2 + C' * hseq m + frobDot (hn m) (dRl t (x m)) :=
        lt_of_mul_lt_mul_left hB (le_of_lt (hhpos m))
      linarith [hC1]
    -- limits
    have hlim_dR : Tendsto (fun m => dRl t (x m)) 𝒰 (𝓝 (dRl t xlim)) := by
      have hcw : ContinuousWithinAt (fun p : ℝ × X => dRl p.1 p.2)
          (Icc t (t + δ₀) ×ˢ U) (t, xlim) :=
        (hcontm.snd).continuousWithinAt ⟨hIcc₁, mem_of_mem_nhds hUx⟩
      refine mp_tendsto_comp (u := fun m => (t, x m)) hcw ?_ ?_
      · refine (Prod.tendsto_iff _ _).mpr ⟨?_, hxlim⟩
        simpa using tendsto_const_nhds
      · filter_upwards [hxU] with m hmU
        exact ⟨hIcc₁, hmU⟩
    have hlimkey : Tendsto (fun m => frobDot (hn m) (dRl t (x m))) 𝒰
        (𝓝 (frobDot nlim (dRl t xlim))) := mp_frobDot_tendsto hnlim hlim_dR
    have hε2_le : ε / 2 ≤ frobDot nlim (dRl t xlim) :=
      mp_limit_compare hlim_h hlimkey hchain
    -- the spatial maximum principle
    have hsupp : ∀ S ∈ K t, frobDot nlim (S - vlim) ≤ 0 := by
      intro S hS
      have hev : ∀ᶠ m in 𝒰, frobDot (hn m) (S - v m)
          ≤ C' * hseq m ^ 2 - hseq m * frobDot (hn m) (Q S) := by
        filter_upwards [hsmall, hPnotK] with m hms hmPnotK
        have hmδpush : hseq m ≤ δpush := le_trans hms (min_le_left _ _)
        obtain ⟨S'', hS''K, hS''dist⟩ := hpushex (hseq m) (hhpos m) hmδpush S hS
        have h1 : frobDot (hn m) (S - v m)
            = frobDot (hn m) (S + hseq m • Q S - v m) - hseq m * frobDot (hn m) (Q S) := by
          have h : S - v m = (S + hseq m • Q S - v m) - hseq m • Q S := by module
          rw [h, frobDot_sub_right, frobDot_smul_right]
        have h2 : frobDot (hn m) (S + hseq m • Q S - v m) ≤ C' * hseq m ^ 2 := by
          have h3 : S + hseq m • Q S - v m = (S'' - v m) + (S + hseq m • Q S - S'') := by abel
          rw [h3, frobDot_add_right]
          have h4 : frobDot (hn m) (S'' - v m) ≤ 0 := hn_supp m hmPnotK S'' hS''K
          have h5 : frobDot (hn m) (S + hseq m • Q S - S'')
              ≤ frobNorm (S + hseq m • Q S - S'') := by
            have h := frob_cauchy_schwarz (hn m) (S + hseq m • Q S - S'')
            rw [hn_norm m hmPnotK, one_mul] at h
            exact le_trans (le_abs_self _) h
          have h6 : frobNorm (S + hseq m • Q S - S'') = frobDist S'' (S + hseq m • Q S) := by
            have hneg : S'' - (S + hseq m • Q S) = -(S + hseq m • Q S - S'') := by abel
            rw [frobDist, hneg, frobNorm_neg]
          linarith [h4, h5, h6, hS''dist]
        linarith [h1, h2]
      have hlim1 : Tendsto (fun m => frobDot (hn m) (S - v m)) 𝒰 (𝓝 (frobDot nlim (S - vlim))) :=
        mp_frobDot_tendsto hnlim (tendsto_const_nhds.sub hvlim)
      have hlim2 : Tendsto (fun m => C' * hseq m ^ 2 - hseq m * frobDot (hn m) (Q S)) 𝒰
          (𝓝 0) := mp_tendsto_sq_sub_mul hlim_h (mp_frobDot_tendsto_const hnlim (Q S))
      exact le_of_tendsto_of_tendsto hlim1 hlim2 hev
    have hmaxpt : ∀ z ∈ U, frobDot nlim (Rl t z) ≤ frobDot nlim (Rl t xlim) := by
      intro z hz
      have h7 : frobDot nlim (Rl t xlim - vlim) = F t := by
        have h8 : Tendsto (fun m => frobDot (hn m) (P m - v m)) 𝒰
            (𝓝 (frobDot nlim (Rl t xlim - vlim))) := mp_frobDot_tendsto hnlim (hPlim.sub hvlim)
        have hev : (fun m => frobDot (hn m) (P m - v m)) =ᶠ[𝒰] (fun m => F (t + hseq m)) := by
          filter_upwards [hxU, hsmall, hPnotK] with m hmU hms hmPnotK
          have hmδ₀ : hseq m ≤ δ₀ := le_trans hms (le_trans (min_le_right _ _) (min_le_left _ _))
          rw [hn_dot m hmPnotK, hvdist m hmU hmδ₀]
        exact tendsto_nhds_unique_of_eventuallyEq h8 hlimF hev
      have h1 : frobDot nlim (Rl t z - vlim) ≤ frobInfDist (Rl t z) (K t) := by
        refine le_frobInfDist (hKne t htIcc) (fun S hS => ?_)
        have h2 : frobDot nlim (Rl t z - vlim)
            = frobDot nlim (Rl t z - S) + frobDot nlim (S - vlim) := by
          have h : Rl t z - vlim = (Rl t z - S) + (S - vlim) := by abel
          rw [h, frobDot_add_right]
        rw [h2]
        have h3 : frobDot nlim (S - vlim) ≤ 0 := hsupp S hS
        have h4 : frobDot nlim (Rl t z - S) ≤ frobNorm (Rl t z - S) := by
          have h := frob_cauchy_schwarz nlim (Rl t z - S)
          rw [hnlimmem, one_mul] at h
          exact le_trans (le_abs_self _) h
        have h5 : frobNorm (Rl t z - S) = frobDist (Rl t z) S := rfl
        linarith [h3, h4, h5]
      have h6 : frobInfDist (Rl t z) (K t) = d t z := (hdom t hIcc₁ z hz).symm
      have h9 : d t z ≤ F t := hFle t htIcc z
      have h11 : frobDot nlim (Rl t z) - frobDot nlim vlim = frobDot nlim (Rl t z - vlim) := by
        rw [frobDot_sub_right]
      have h10 : frobDot nlim (Rl t z) - frobDot nlim vlim ≤ F t := by linarith [h1, h6, h9, h11]
      have h12 : frobDot nlim (Rl t xlim) - frobDot nlim vlim
          = frobDot nlim (Rl t xlim - vlim) := by rw [frobDot_sub_right]
      linarith [h7, h10, h11, h12]
    have hmp_final : frobDot nlim (dRl t xlim) ≤ 0 :=
      hmp nlim (le_of_eq hnlimmem) hmaxpt
    linarith [hε2_le, hmp_final, hε]
  have hFzero : ∀ t ∈ Icc a b, F t = 0 :=
    mp_dini_lsc_band hablt hFnonneg hFa hlscl hruscF' hkey
  intro t ht x
  have h1 : d t x ≤ F t := hFle t ht x
  have h2 : 0 ≤ d t x := hdnn t ht x
  rw [hFzero t ht] at h1
  linarith

end Work.Diff.MP

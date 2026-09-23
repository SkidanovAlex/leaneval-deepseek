import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.ODE

open Set Filter Metric
open scoped Topology

/-- **Uniform bound of a continuous field near a compact set.**  If `F` is continuous on an open set
`W` and `K ⊆ W` is compact and nonempty, then there are `η > 0` and `M ≥ 0` such that the
`η`-thickening of `K` is contained in `W` and `‖F‖ ≤ M` on it. -/
private lemma exists_uniform_bound_near_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContinuousOn F W)
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty) (hKW : K ⊆ W) :
    ∃ η : ℝ, 0 < η ∧ ∃ M : ℝ, 0 ≤ M ∧
      Metric.cthickening η K ⊆ W ∧
      (∀ x ∈ Metric.cthickening η K, ‖F x‖ ≤ M) := by
  classical
  have hloc : ∀ x : K, ∃ (rx : ℝ) (Mx : ℝ), 0 < rx ∧
      Metric.ball (x : E) rx ⊆ W ∧ 0 ≤ Mx ∧
      ∀ y ∈ Metric.ball (x : E) rx, ‖F y‖ ≤ Mx := by
    intro x
    have hxW : (x : E) ∈ W := hKW x.2
    have hcont : ContinuousAt F (x : E) := hFW.continuousAt (hW.mem_nhds hxW)
    obtain ⟨b₁, hb₁pos, hb₁sub⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hxW)
    obtain ⟨b₂, hb₂pos, hb₂sub⟩ := Metric.mem_nhds_iff.mp
      (hcont.preimage_mem_nhds (Metric.ball_mem_nhds (F (x : E)) one_pos))
    refine ⟨min b₁ b₂, ‖F (x : E)‖ + 1, lt_min hb₁pos hb₂pos, ?_, by positivity, ?_⟩
    · intro y hy
      exact hb₁sub (Metric.ball_subset_ball (min_le_left _ _) hy)
    · intro y hy
      have hy2 : y ∈ Metric.ball (x : E) b₂ := Metric.ball_subset_ball (min_le_right _ _) hy
      have hd : dist (F y) (F (x : E)) < 1 := hb₂sub hy2
      have hd' : ‖F y - F (x : E)‖ < 1 := by rwa [dist_eq_norm] at hd
      calc ‖F y‖ = ‖(F y - F (x : E)) + F (x : E)‖ := by rw [sub_add_cancel]
        _ ≤ ‖F y - F (x : E)‖ + ‖F (x : E)‖ := norm_add_le _ _
        _ ≤ 1 + ‖F (x : E)‖ := by linarith
        _ = ‖F (x : E)‖ + 1 := by ring
  choose rx Mx hrxpos hballW hMxnn hMxbd using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x : E) (rx x / 2))
      (fun _ => isOpen_ball) (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, by
        simp only [Metric.mem_ball, dist_self]
        exact half_pos (hrxpos ⟨y, hy⟩)⟩)
  set V : Set E := ⋃ x ∈ t, Metric.ball (x : E) (rx x) with hVdef
  have hVopen : IsOpen V := isOpen_biUnion fun _ _ => isOpen_ball
  have hVW : V ⊆ W := by
    intro y hy
    simp only [V, mem_iUnion, exists_prop] at hy
    obtain ⟨x, -, hxy⟩ := hy
    exact hballW x hxy
  have hKV : K ⊆ V := by
    intro y hy
    have hy' := ht hy
    simp only [mem_iUnion, exists_prop] at hy'
    obtain ⟨x, hxt, hxy⟩ := hy'
    exact mem_iUnion₂.mpr ⟨x, hxt, Metric.ball_subset_ball (by linarith [hrxpos x]) hxy⟩
  obtain ⟨η, hηpos, hηV⟩ := hK.exists_cthickening_subset_open hVopen hKV
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := hKne
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hmem := ht hy
    rw [hemp] at hmem
    simp at hmem
  obtain ⟨x₀, hx₀⟩ := htne
  refine ⟨η, hηpos, (t.image Mx).max' (Finset.image_nonempty.mpr ⟨x₀, hx₀⟩),
    le_trans (hMxnn x₀) (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩)),
    hηV.trans hVW, ?_⟩
  intro x hx
  have hxV : x ∈ V := hηV hx
  simp only [V, mem_iUnion, exists_prop] at hxV
  obtain ⟨y, hyt, hxy⟩ := hxV
  exact le_trans (hMxbd y x hxy) (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨y, hyt, rfl⟩))

/-- **A curve with bounded velocity cannot leave a thickening.**  Let `g 0 = p ∈ K` and suppose that
on `[0, s]` the curve `g` solves `g' = F ∘ g`, with `‖F‖ ≤ M` on a set `N ⊇ cthickening r K`.  If
`M * s < r` then `g` maps `[0, s]` into `cthickening r K`. -/
private lemma stays_Icc_of_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {F : E → E} {K N : Set E} {M r s : ℝ}
    (hM : 0 ≤ M) (hMs : M * s < r)
    (hN : Metric.cthickening r K ⊆ N) (hbound : ∀ x ∈ N, ‖F x‖ ≤ M)
    {p : E} (hp : p ∈ K) (h0 : g 0 = p) (hs : 0 ≤ s)
    (hg : ∀ t ∈ Set.Icc 0 s, HasDerivAt g (F (g t)) t) :
    ∀ t ∈ Set.Icc 0 s, g t ∈ Metric.cthickening r K := by
  set C : Set E := Metric.cthickening r K with hC
  set T : Set ℝ := {u | u ∈ Set.Icc 0 s ∧ ∀ v ∈ Set.Icc 0 u, g v ∈ C} with hT
  have hT0 : (0 : ℝ) ∈ T := by
    refine ⟨⟨le_rfl, hs⟩, ?_⟩
    intro v hv
    rw [Set.Icc_self] at hv
    rw [hv, h0]
    exact self_subset_cthickening K hp
  have hTne : T.Nonempty := ⟨0, hT0⟩
  have hTbdd : BddAbove T := ⟨s, fun u hu => hu.1.2⟩
  set t₁ : ℝ := sSup T with ht₁
  have ht₁le : t₁ ≤ s := csSup_le hTne (fun u hu => hu.1.2)
  have ht₁ge : 0 ≤ t₁ := le_csSup hTbdd hT0
  have hsaf : ∀ v ∈ Set.Icc 0 t₁, g v ∈ C := by
    intro v hv
    rcases lt_or_eq_of_le hv.2 with hlt | heq
    · obtain ⟨u, huT, hvu⟩ := exists_lt_of_lt_csSup hTne (by rw [← ht₁]; exact hlt)
      exact huT.2 v ⟨hv.1, le_of_lt hvu⟩
    · rw [heq]
      rcases eq_or_lt_of_le ht₁ge with hz | hpos
      · rw [← hz, h0]
        exact self_subset_cthickening K hp
      · have hcont : ContinuousAt g t₁ := (hg t₁ ⟨ht₁ge, ht₁le⟩).continuousAt
        have hlim : Tendsto g (𝓝[<] t₁) (𝓝 (g t₁)) :=
          hcont.tendsto.mono_left nhdsWithin_le_nhds
        refine IsClosed.mem_of_tendsto (by rw [hC]; exact isClosed_cthickening) hlim ?_
        filter_upwards [Ioo_mem_nhdsLT hpos] with u hu
        obtain ⟨u', hu'T, huu'⟩ := exists_lt_of_lt_csSup hTne (by rw [← ht₁]; exact hu.2)
        exact hu'T.2 u ⟨hu.1.le, le_of_lt huu'⟩
  have ht₁eq : t₁ = s := by
    by_contra hne
    have hlt : t₁ < s := lt_of_le_of_ne ht₁le hne
    have hmvt : ‖g t₁ - g 0‖ ≤ M * (t₁ - 0) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := fun x => F (g x))
        (a := 0) (b := t₁) (C := M) (fun x hx => ?_) (fun x hx => ?_) t₁ ⟨ht₁ge, le_rfl⟩
      · exact (hg x ⟨hx.1, le_trans hx.2 ht₁le⟩).hasDerivWithinAt
      · exact hbound (g x) (hN (hsaf x ⟨hx.1, le_of_lt hx.2⟩))
    have hgt : ‖g t₁ - p‖ < r := by
      have hmvt' : ‖g t₁ - p‖ ≤ M * (t₁ - 0) := by rwa [h0] at hmvt
      have hle : M * (t₁ - 0) ≤ M * s :=
        mul_le_mul_of_nonneg_left (by linarith) hM
      linarith
    have hmem : g t₁ ∈ Metric.thickening r K := by
      rw [Metric.mem_thickening_iff]
      exact ⟨p, hp, by rw [dist_eq_norm]; exact hgt⟩
    have hnhds : Metric.thickening r K ∈ 𝓝 (g t₁) := IsOpen.mem_nhds isOpen_thickening hmem
    obtain ⟨ε, hεpos, hεsub⟩ :=
      Metric.mem_nhds_iff.mp ((hg t₁ ⟨ht₁ge, ht₁le⟩).continuousAt.preimage_mem_nhds hnhds)
    have hεsub' : ∀ u : ℝ, dist u t₁ < ε → g u ∈ C := fun u hu =>
      Metric.thickening_subset_cthickening r K (hεsub (Metric.mem_ball.mpr hu))
    have hst : 0 < s - t₁ := by linarith
    set ε' : ℝ := min ε (s - t₁) with hε'def
    have hε'pos : 0 < ε' := lt_min hεpos hst
    have hε'le : ε' ≤ s - t₁ := min_le_right _ _
    have hε'leε : ε' ≤ ε := min_le_left _ _
    have hstep : t₁ + ε' / 2 ∈ T := by
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      intro v hv
      rcases le_or_gt v t₁ with hle | hlt'
      · exact hsaf v ⟨hv.1, hle⟩
      · apply hεsub'
        rw [Real.dist_eq, abs_lt]
        refine ⟨by linarith [hlt', hεpos], ?_⟩
        have h1 : v - t₁ ≤ ε' / 2 := by linarith [hv.2]
        have h2 : ε' / 2 < ε := by linarith [hε'pos, hε'leε]
        linarith
    have hcontra : t₁ + ε' / 2 ≤ t₁ := by
      have := le_csSup hTbdd hstep
      rwa [← ht₁] at this
    linarith
  intro v hv
  exact hsaf v ⟨hv.1, by rw [ht₁eq]; exact hv.2⟩

theorem exists_confined_time_of_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W) (hFW : ContinuousOn F W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {α : E → ℝ → E}
    (h0 : ∀ p ∈ K, α p 0 = p)
    (hode : ∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ₀ → HasDerivAt (α p) (F (α p t)) t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ p ∈ K, ∀ t : ℝ, |t| ≤ ρ → α p t ∈ W := by
  rcases Set.eq_empty_or_nonempty K with hKemp | hKne
  · refine ⟨ρ₀, hρ₀, le_rfl, ?_⟩
    intro p hp
    rw [hKemp] at hp
    exact absurd hp (Set.notMem_empty p)
  · obtain ⟨η, hηpos, M, hMnn, hηW, hηbd⟩ :=
      exists_uniform_bound_near_compact hW hFW hK hKne hKW
    have hrpos : 0 < η / 2 := by linarith
    have hNr : Metric.cthickening (η / 2) K ⊆ Metric.cthickening η K :=
      cthickening_mono (by linarith) K
    have hN : Metric.cthickening (η / 2) K ⊆ W := hNr.trans hηW
    set ρ : ℝ := min ρ₀ (η / 2 / (2 * (M + 1))) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min hρ₀ (div_pos hrpos (by linarith))
    have hρle : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_left _ _
    have hMs : M * ρ < η / 2 := by
      have hρc : ρ ≤ η / 2 / (2 * (M + 1)) := by rw [hρdef]; exact min_le_right _ _
      have hden : (0 : ℝ) < 2 * (M + 1) := by linarith
      have h1 : M * ρ ≤ M * (η / 2 / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hρc hMnn
      have h2 : M * (η / 2 / (2 * (M + 1))) < η / 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ hden]
        nlinarith [hrpos, hMnn]
      linarith
    refine ⟨ρ, hρpos, hρle, ?_⟩
    intro p hp t ht
    have hful : ∀ u ∈ Set.Icc (0 : ℝ) ρ, α p u ∈ Metric.cthickening (η / 2) K :=
      stays_Icc_of_deriv_bound (F := F) (K := K) (N := Metric.cthickening η K)
        (M := M) (r := η / 2) (s := ρ) (g := α p) (p := p)
        hMnn hMs hNr hηbd hp (h0 p hp) hρpos.le
        (fun u hu => hode p hp u (by rw [abs_of_nonneg hu.1]; exact le_trans hu.2 hρle))
    have hrev : ∀ u ∈ Set.Icc (0 : ℝ) ρ,
        α p (-u) ∈ Metric.cthickening (η / 2) K :=
      stays_Icc_of_deriv_bound (F := fun x => -F x) (K := K) (N := Metric.cthickening η K)
        (M := M) (r := η / 2) (s := ρ) (g := fun u => α p (-u)) (p := p)
        hMnn hMs hNr (fun x hx => by rw [norm_neg]; exact hηbd x hx) hp
        (by show α p (-(0:ℝ)) = p; rw [neg_zero]; exact h0 p hp) hρpos.le
        (fun u hu => by
          have hder := hode p hp (-u)
            (by rw [abs_neg, abs_of_nonneg hu.1]; exact le_trans hu.2 hρle)
          have hcomp := hder.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_neg u)
          simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul]
            using hcomp)
    have hmem : α p t ∈ Metric.cthickening (η / 2) K := by
      rcases le_or_gt 0 t with ht0 | ht0
      · exact hful t ⟨ht0, (abs_le.mp ht).2⟩
      · have hnt : 0 ≤ -t := by linarith
        have hnρ : -t ≤ ρ := by linarith [(abs_le.mp ht).1]
        have := hrev (-t) ⟨hnt, hnρ⟩
        simpa using this
    exact hN hmem

end Commons.Analysis.ODE
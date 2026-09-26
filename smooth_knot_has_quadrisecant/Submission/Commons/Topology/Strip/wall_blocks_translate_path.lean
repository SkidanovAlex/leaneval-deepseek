import Mathlib
import Submission.Commons.Topology.Jordan.crossing_lemma_rect
import Submission.Commons.Topology.Jordan.square_sets_top_bottom_continuum

open Set
open scoped Topology

namespace Commons.Topology.Strip

noncomputable section

/-- `ℝ × ℝ → ℂ`. -/
def toC (q : ℝ × ℝ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

lemma toC_re (q : ℝ × ℝ) : (toC q).re = q.1 := by simp [toC]
lemma toC_im (q : ℝ × ℝ) : (toC q).im = q.2 := by simp [toC]
lemma toC_continuous : Continuous toC := by unfold toC; fun_prop
lemma toC_injective : Function.Injective toC := by
  intro q q' h
  exact Prod.ext (by rw [← toC_re q, ← toC_re q', h]) (by rw [← toC_im q, ← toC_im q', h])

/-- **The staircase lift.**  A path `γ : [0,1] → ℝ × ℝ` from `z = γ 0` to `z + (p,0)`
(`γ 1 = ((γ 0).1 + p, (γ 0).2)`) extends to a continuous `G : ℝ → ℝ × ℝ` which is
`T`-equivariant, `G (t + p) = ((G t).1 + p, (G t).2)`, and whose image is the full
`T`-orbit of `γ '' [0,1]`. -/
theorem exists_staircase (p : ℝ) (hp : p ≠ 0) (γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ))
    (hγ : γ 1 = ((γ 0).1 + p, (γ 0).2)) :
    ∃ G : C(ℝ, ℝ × ℝ), G 0 = γ 0 ∧ (∀ t, G (t + p) = ((G t).1 + p, (G t).2)) ∧
      (∀ t, ∃ s : Set.Icc (0:ℝ) 1, ∃ n : ℤ, G t = ((γ s).1 + p * (n : ℝ), (γ s).2)) := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  set Φ : ℝ → ℝ := fun u => (γ (Set.projIcc 0 1 h01 u)).1 - p * u with hΦ
  set Ψ : ℝ → ℝ := fun u => (γ (Set.projIcc 0 1 h01 u)).2 with hΨ
  have hΦc : ContinuousOn Φ (Set.Icc (0:ℝ) 1) := by rw [hΦ]; fun_prop
  have hΨc : ContinuousOn Ψ (Set.Icc (0:ℝ) 1) := by rw [hΨ]; fun_prop
  have hp0 : Set.projIcc 0 1 h01 (0:ℝ) = (0 : Set.Icc (0:ℝ) 1) := by
    apply Subtype.ext; rw [Set.projIcc_left h01]; rfl
  have hp1 : Set.projIcc 0 1 h01 (1:ℝ) = (1 : Set.Icc (0:ℝ) 1) := by
    apply Subtype.ext; rw [Set.projIcc_right h01]; rfl
  have hΦ0 : Φ 0 = (γ 0).1 := by
    rw [hΦ]; show (γ (Set.projIcc 0 1 h01 (0:ℝ))).1 - p * 0 = (γ 0).1
    rw [hp0]; simp
  have hΦ1 : Φ 1 = (γ 0).1 := by
    rw [hΦ]; show (γ (Set.projIcc 0 1 h01 (1:ℝ))).1 - p * 1 = (γ 0).1
    rw [hp1, hγ]; simp
  have hΨ0 : Ψ 0 = (γ 0).2 := by
    rw [hΨ]; show (γ (Set.projIcc 0 1 h01 (0:ℝ))).2 = (γ 0).2; rw [hp0]
  have hΨ1 : Ψ 1 = (γ 0).2 := by
    rw [hΨ]; show (γ (Set.projIcc 0 1 h01 (1:ℝ))).2 = (γ 0).2; rw [hp1, hγ]
  have hΦf : Continuous (Φ ∘ Int.fract) := ContinuousOn.comp_fract'' hΦc (by rw [hΦ0, hΦ1])
  have hΨf : Continuous (Ψ ∘ Int.fract) := ContinuousOn.comp_fract'' hΨc (by rw [hΨ0, hΨ1])
  have hcont : Continuous fun t : ℝ => (t + (Φ ∘ Int.fract) (t / p), (Ψ ∘ Int.fract) (t / p)) := by
    apply Continuous.prodMk
    · exact continuous_id.add (hΦf.comp (continuous_id.div_const p))
    · exact hΨf.comp (continuous_id.div_const p)
  refine ⟨⟨_, hcont⟩, ?_, ?_, ?_⟩
  · show (0 + (Φ ∘ Int.fract) (0 / p), (Ψ ∘ Int.fract) (0 / p)) = γ 0
    simp only [zero_div, Int.fract_zero, Function.comp_apply, hΦ0, hΨ0]
    exact Prod.ext (by ring) rfl
  · intro t
    show ((t + p) + (Φ ∘ Int.fract) ((t + p) / p), (Ψ ∘ Int.fract) ((t + p) / p))
        = ((t + (Φ ∘ Int.fract) (t / p)) + p, (Ψ ∘ Int.fract) (t / p))
    have hdiv : (t + p) / p = t / p + 1 := by field_simp
    rw [hdiv]; simp only [Function.comp_apply, Int.fract_add_one]
    exact Prod.ext (by ring) rfl
  · intro t
    refine ⟨Set.projIcc 0 1 h01 (Int.fract (t / p)), ⌊t / p⌋, ?_⟩
    show (t + (Φ ∘ Int.fract) (t / p), (Ψ ∘ Int.fract) (t / p))
        = ((γ (Set.projIcc 0 1 h01 (Int.fract (t / p)))).1 + p * (⌊t / p⌋ : ℝ),
           (γ (Set.projIcc 0 1 h01 (Int.fract (t / p)))).2)
    simp only [Function.comp_apply, hΦ, hΨ]
    have hf : Int.fract (t / p) = t / p - (⌊t / p⌋ : ℝ) := (Int.self_sub_floor (t / p)).symm
    rw [hf]
    have hmain : t + ((γ (Set.projIcc 0 1 h01 (t / p - ↑⌊t / p⌋))).1 - p * (t / p - ↑⌊t / p⌋))
        = (γ (Set.projIcc 0 1 h01 (t / p - ↑⌊t / p⌋))).1 + p * ↑⌊t / p⌋ := by
      field_simp; ring
    exact Prod.ext hmain rfl

/-- Integer-period equivariance of the staircase. -/
lemma staircase_zsmul {p : ℝ} {G : ℝ → ℝ × ℝ}
    (hper : ∀ t, G (t + p) = ((G t).1 + p, (G t).2)) (n : ℤ) (t : ℝ) :
    G (t + (n : ℝ) * p) = ((G t).1 + (n : ℝ) * p, (G t).2) := by
  have hF : Function.Periodic (fun t => (G t).1 - t) p := by
    intro x
    show (G (x + p)).1 - (x + p) = (G x).1 - x
    rw [hper x]; ring
  have hS : Function.Periodic (fun t => (G t).2) p := by
    intro x
    show (G (x + p)).2 = (G x).2
    rw [hper x]
  have h1 := (hF.int_mul n) t
  have h2 := (hS.int_mul n) t
  exact Prod.ext (by linarith) h2

/-- **Crossing path.**  A continuous real function taking a value `< u` at `t₀` and a value
`> v` at `t₁ > t₀` has a segment running from level `u` to level `v` while staying in `[u,v]`. -/
theorem exists_crossing_path {X : ℝ → ℝ} (hXc : Continuous X)
    {u v : ℝ} (huv : u < v) {t₀ t₁ : ℝ} (ht : t₀ < t₁) (h₀ : X t₀ < u) (h₁ : v < X t₁) :
    ∃ s₁ s₂ : ℝ, s₁ ≤ s₂ ∧ X s₁ = u ∧ X s₂ = v ∧ ∀ t ∈ Icc s₁ s₂, u ≤ X t ∧ X t ≤ v := by
  have hne_v : ({t : ℝ | X t = v} ∩ Icc t₀ t₁).Nonempty := by
    obtain ⟨t, htI, htval⟩ := intermediate_value_Icc ht.le hXc.continuousOn
      (show v ∈ Icc (X t₀) (X t₁) from ⟨le_of_lt (lt_trans h₀ huv), le_of_lt h₁⟩)
    exact ⟨t, htval, htI⟩
  have hcomp_v : IsCompact ({t : ℝ | X t = v} ∩ Icc t₀ t₁) :=
    isCompact_Icc.of_isClosed_subset ((isClosed_eq hXc continuous_const).inter isClosed_Icc)
      inter_subset_right
  obtain ⟨t₂, ht₂mem, ht₂min⟩ :=
    hcomp_v.exists_isMinOn hne_v (continuous_id.continuousOn (s := {t : ℝ | X t = v} ∩ Icc t₀ t₁))
  have ht₂val : X t₂ = v := ht₂mem.1
  have ht₂I : t₂ ∈ Icc t₀ t₁ := ht₂mem.2
  have hlt : ∀ t ∈ Icc t₀ t₂, X t ≤ v := by
    intro t ht
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le ht.2 with hlt2 | heq
    · have hmem : v ∈ Icc (X t₀) (X t) := ⟨le_of_lt (lt_trans h₀ huv), le_of_lt hcon⟩
      obtain ⟨s, hsI, hsval⟩ := intermediate_value_Icc ht.1 hXc.continuousOn hmem
      have hs_in : s ∈ {t : ℝ | X t = v} ∩ Icc t₀ t₁ :=
        ⟨hsval, ⟨hsI.1, le_trans hsI.2 (le_trans (le_of_lt hlt2) ht₂I.2)⟩⟩
      have hmin := ht₂min hs_in
      have hst : s < t₂ := lt_of_le_of_lt hsI.2 hlt2
      exact absurd hmin (not_le.mpr hst)
    · rw [heq, ht₂val] at hcon; exact lt_irrefl v hcon
  have hne_u : ({t : ℝ | X t = u} ∩ Icc t₀ t₂).Nonempty := by
    obtain ⟨t, htI, htval⟩ := intermediate_value_Icc ht₂I.1 hXc.continuousOn
      (show u ∈ Icc (X t₀) (X t₂) from ⟨le_of_lt h₀, by rw [ht₂val]; exact le_of_lt huv⟩)
    exact ⟨t, htval, htI⟩
  have hcomp_u : IsCompact ({t : ℝ | X t = u} ∩ Icc t₀ t₂) :=
    isCompact_Icc.of_isClosed_subset ((isClosed_eq hXc continuous_const).inter isClosed_Icc)
      inter_subset_right
  obtain ⟨s₁, hs₁mem, hs₁max⟩ :=
    hcomp_u.exists_isMaxOn hne_u (continuous_id.continuousOn (s := {t : ℝ | X t = u} ∩ Icc t₀ t₂))
  have hs₁val : X s₁ = u := hs₁mem.1
  have hs₁I : s₁ ∈ Icc t₀ t₂ := hs₁mem.2
  refine ⟨s₁, t₂, hs₁I.2, hs₁val, ht₂val, ?_⟩
  intro t ht
  refine ⟨?_, hlt t ⟨le_trans hs₁I.1 ht.1, ht.2⟩⟩
  rcases lt_or_eq_of_le ht.1 with hlt1 | heq
  · by_contra hcon
    push Not at hcon
    have hmem : u ∈ Icc (X t) (X t₂) := ⟨le_of_lt hcon, by rw [ht₂val]; exact le_of_lt huv⟩
    obtain ⟨s, hsI, hsval⟩ := intermediate_value_Icc ht.2 hXc.continuousOn hmem
    have hs_in : s ∈ {t : ℝ | X t = u} ∩ Icc t₀ t₂ :=
      ⟨hsval, ⟨le_trans hs₁I.1 (le_of_lt (lt_of_lt_of_le hlt1 hsI.1)), hsI.2⟩⟩
    have hmax := hs₁max hs_in
    have hst : s₁ < s := lt_of_lt_of_le hlt1 hsI.1
    exact absurd hmax (not_le.mpr hst)
  · rw [← heq]; exact le_of_eq hs₁val.symm

set_option maxHeartbeats 1600000 in
/-- **No bottom–top path avoids the staircase.**  If `G` is `T`-equivariant, stays in the
closed strip `a ≤ ·.2 ≤ b`, and `δ` is a path in the strip from the bottom line `·.2 = a` to the
top line `·.2 = b`, then `δ` meets `G`'s image. -/
theorem no_bottom_top_path_of_staircase {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {G : ℝ → ℝ × ℝ} (hGc : Continuous G)
    (hGper : ∀ t, G (t + p) = ((G t).1 + p, (G t).2))
    (hGstrip : ∀ t, a ≤ (G t).2 ∧ (G t).2 ≤ b)
    {δ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ)}
    (hδstrip : ∀ t, a ≤ (δ t).2 ∧ (δ t).2 ≤ b)
    (hδ0 : (δ 0).2 = a) (hδ1 : (δ 1).2 = b)
    (hδavoid : ∀ t, δ t ∉ Set.range G) : False := by
  have hxcomp : IsCompact ((fun q : ℝ × ℝ => q.1) '' Set.range δ) :=
    (isCompact_range δ.continuous).image continuous_fst
  obtain ⟨M, hM⟩ := hxcomp.bddAbove
  obtain ⟨m, hm⟩ := hxcomp.bddBelow
  have hmem0 : (δ 0).1 ∈ (fun q : ℝ × ℝ => q.1) '' Set.range δ := ⟨δ 0, ⟨0, rfl⟩, rfl⟩
  have hmM : m ≤ M := le_trans (hm hmem0) (hM hmem0)
  have hδhi : ∀ t, (δ t).1 ≤ M := fun t => hM ⟨δ t, ⟨t, rfl⟩, rfl⟩
  have hδlo : ∀ t, m ≤ (δ t).1 := fun t => hm ⟨δ t, ⟨t, rfl⟩, rfl⟩
  set X0 : ℝ := m - 1 with hX0
  set X1 : ℝ := M + 1 with hX1
  have hX01 : X0 < X1 := by rw [hX0, hX1]; linarith
  obtain ⟨n₀, hn₀⟩ := exists_int_lt ((X0 - (G 0).1) / p)
  obtain ⟨n₁, hn₁⟩ := exists_int_gt ((X1 - (G 0).1) / p)
  set n₀' : ℤ := min n₀ (-1) with hn₀'
  set n₁' : ℤ := max n₁ 1 with hn₁'
  have hle₀ : (n₀' : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast min_le_left n₀ (-1)
  have hle₁ : (n₁ : ℝ) ≤ (n₁' : ℝ) := by exact_mod_cast le_max_left n₁ 1
  have hlt₀ : (n₀' : ℝ) * p < X0 - (G 0).1 := by
    have h3 : (n₀' : ℝ) * p < ((X0 - (G 0).1) / p) * p :=
      mul_lt_mul_of_pos_right (lt_of_le_of_lt hle₀ hn₀) hp
    rwa [div_mul_cancel₀ _ hp.ne'] at h3
  have hgt₁ : X1 - (G 0).1 < (n₁' : ℝ) * p := by
    have h3 : ((X1 - (G 0).1) / p) * p < (n₁ : ℝ) * p := mul_lt_mul_of_pos_right hn₁ hp
    rw [div_mul_cancel₀ _ hp.ne'] at h3
    have h4 : (n₁ : ℝ) * p ≤ (n₁' : ℝ) * p := mul_le_mul_of_nonneg_right hle₁ hp.le
    linarith
  have hn₀neg : n₀' ≤ -1 := min_le_right n₀ (-1)
  have hn₁pos : 1 ≤ n₁' := le_max_right n₁ 1
  have ht : (n₀' : ℝ) * p < (n₁' : ℝ) * p := by
    have hcast : (n₀' : ℝ) < (n₁' : ℝ) := by
      exact_mod_cast lt_of_le_of_lt hn₀neg (lt_of_lt_of_le (by norm_num) hn₁pos)
    exact mul_lt_mul_of_pos_right hcast hp
  have hXval₀ : (G ((n₀' : ℝ) * p)).1 = (G 0).1 + (n₀' : ℝ) * p := by
    have h := staircase_zsmul hGper n₀' 0
    simpa using congrArg Prod.fst h
  have hXval₁ : (G ((n₁' : ℝ) * p)).1 = (G 0).1 + (n₁' : ℝ) * p := by
    have h := staircase_zsmul hGper n₁' 0
    simpa using congrArg Prod.fst h
  obtain ⟨s₁, s₂, hs12, hs₁, hs₂, hs_in⟩ :=
    exists_crossing_path (X := fun t => (G t).1) (continuous_fst.comp hGc)
      hX01 ht (by rw [hXval₀]; linarith) (by rw [hXval₁]; linarith)
  have h01' : (0:ℝ) ≤ 1 := by norm_num
  set ρ : ℝ → ℝ := fun s => s₁ + ((Set.projIcc (-1) 1 (by norm_num : (-1:ℝ) ≤ 1) s : ℝ) + 1) / 2 * (s₂ - s₁) with hρ
  have hρc : Continuous ρ := by rw [hρ]; fun_prop
  have hρI : ∀ s ∈ Icc (-1:ℝ) 1, ρ s ∈ Icc s₁ s₂ := by
    intro s hs
    have hsq : (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ) ≤ 1) s : ℝ) = s :=
      congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1) hs)
    have hrw : ρ s = s₁ + (s + 1) / 2 * (s₂ - s₁) := by simp only [hρ, hsq]
    rw [hrw]
    have hfac : (s + 1) / 2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    constructor
    · nlinarith [hfac.1, hfac.2, sub_nonneg.mpr hs12]
    · nlinarith [hfac.1, hfac.2, sub_nonneg.mpr hs12]
  let σ : ℝ → Set.Icc (0:ℝ) 1 := fun s => Set.projIcc (0:ℝ) 1 h01' s
  have hσc : Continuous σ := by fun_prop
  let Hf : ℝ → ℂ := fun s => toC (G (ρ s))
  have hHc : Continuous Hf := toC_continuous.comp (hGc.comp hρc)
  let Vf : ℝ → ℂ := fun s => toC (δ (σ s))
  have hVc : Continuous Vf := toC_continuous.comp (δ.continuous.comp hσc)
  have hh : ∀ t ∈ Icc (-1:ℝ) 1, (Hf t).re ∈ Icc X0 X1 ∧ (Hf t).im ∈ Icc a b := by
    intro t ht
    have h1 := hs_in (ρ t) (hρI t ht)
    have h2 := hGstrip (ρ t)
    show (toC (G (ρ t))).re ∈ Icc X0 X1 ∧ (toC (G (ρ t))).im ∈ Icc a b
    rw [toC_re, toC_im]
    exact ⟨h1, h2⟩
  have hv : ∀ t ∈ Icc (-1:ℝ) 1, (Vf t).re ∈ Icc X0 X1 ∧ (Vf t).im ∈ Icc a b := by
    intro t ht
    have h2 := hδstrip (σ t)
    have h3 := hδlo (σ t); have h4 := hδhi (σ t)
    show (toC (δ (σ t))).re ∈ Icc X0 X1 ∧ (toC (δ (σ t))).im ∈ Icc a b
    rw [toC_re, toC_im, hX0, hX1]
    exact ⟨⟨by linarith, by linarith⟩, h2⟩
  have hH0 : (Hf (-1)).re = X0 := by
    show (toC (G (ρ (-1)))).re = X0
    rw [toC_re]
    have hproj : (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ) ≤ 1) (-1:ℝ) : ℝ) = -1 := by
      rw [Set.projIcc_left (by norm_num : (-1:ℝ) ≤ 1)]
    have : ρ (-1) = s₁ := by simp only [hρ, hproj]; ring
    rw [this, hs₁]
  have hH1 : (Hf 1).re = X1 := by
    show (toC (G (ρ 1))).re = X1
    rw [toC_re]
    have hproj : (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ) ≤ 1) (1:ℝ) : ℝ) = 1 := by
      rw [Set.projIcc_right (by norm_num : (-1:ℝ) ≤ 1)]
    have : ρ 1 = s₂ := by simp only [hρ, hproj]; ring
    rw [this, hs₂]
  have hV'0 : (Vf (-1)).im = a := by
    show (toC (δ (σ (-1)))).im = a
    rw [toC_im]
    have hproj : σ (-1) = 0 := by
      apply Subtype.ext
      show (Set.projIcc (0:ℝ) 1 h01' (-1:ℝ) : ℝ) = (0 : ℝ)
      rw [Set.coe_projIcc]; norm_num
    rw [hproj, hδ0]
  have hV'1 : (Vf 1).im = b := by
    show (toC (δ (σ 1))).im = b
    rw [toC_im]
    have hproj : σ 1 = 1 := by
      apply Subtype.ext
      show (Set.projIcc (0:ℝ) 1 h01' (1:ℝ) : ℝ) = (1 : ℝ)
      rw [Set.coe_projIcc]; norm_num
    rw [hproj, hδ1]
  obtain ⟨s, hsI, t, htI, heq⟩ :=
    Commons.Topology.Jordan.crossing_lemma_rect (a := X0) (b := X1) (c := a) (d := b)
      ⟨Hf, hHc⟩ ⟨Vf, hVc⟩ hh hv hH0 hH1 hV'0 hV'1
  have heqq : G (ρ s) = δ (σ t) :=
    toC_injective heq
  exact hδavoid (σ t) ⟨ρ s, heqq⟩


/-- Integer periods of a `p`-periodic set. -/
lemma periodic_shift {p : ℝ} {K : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K) (n : ℤ) (q : ℝ × ℝ) :
    (q.1 + n * p, q.2) ∈ K ↔ q ∈ K := by
  have hp : Function.Periodic (fun x : ℝ => ((q.1 + x, q.2) ∈ K)) p := by
    intro x
    simp only []
    rw [show q.1 + (x + p) = (q.1 + x) + p by ring]
    exact propext (hper (q.1 + x, q.2)).symm
  have := hp.int_mul n 0
  simpa using this

/-- The quotient map `ℝ × ℝ → AddCircle p × ℝ`. -/
def qA (p : ℝ) (w : ℝ × ℝ) : AddCircle p × ℝ := ((w.1 : AddCircle p), w.2)

lemma qA_continuous (p : ℝ) : Continuous (qA p) := by
  unfold qA
  exact Continuous.prodMk
    ((AddCircle.isCoveringMap_coe (𝕜 := ℝ) p).continuous.comp continuous_fst) continuous_snd

lemma qA_eq_iff (p : ℝ) (w w' : ℝ × ℝ) :
    qA p w = qA p w' ↔ ∃ n : ℤ, w'.1 = w.1 + n * p ∧ w'.2 = w.2 := by
  constructor
  · intro h
    have h1 : (w.1 : AddCircle p) = (w'.1 : AddCircle p) :=
      congrArg (Prod.fst : AddCircle p × ℝ → AddCircle p) h
    have h2 : w.2 = w'.2 := congrArg (Prod.snd : AddCircle p × ℝ → ℝ) h
    have h3 : -w.1 + w'.1 ∈ AddSubgroup.zmultiples p := by
      rw [← QuotientAddGroup.eq]; exact h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h3
    rw [zsmul_eq_mul] at hk
    refine ⟨k, ?_, h2.symm⟩
    linarith
  · rintro ⟨n, h1, h2⟩
    have hmk : (w'.1 : AddCircle p) = (w.1 : AddCircle p) := by
      rw [h1, show w.1 + n * p = n * p + w.1 by ring]
      have hnp : ((n * p : ℝ) : AddCircle p) = 0 := by
        have : (n * p : ℝ) = n • p := by rw [zsmul_eq_mul]
        rw [this, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
      rw [AddCircle.coe_add, hnp, zero_add]
    exact Prod.ext (by rw [show (qA p w).1 = (w.1 : AddCircle p) from rfl,
      show (qA p w').1 = (w'.1 : AddCircle p) from rfl, hmk]) (by simp [qA, h2])

lemma qA_preimage_image {p : ℝ} {S : Set (ℝ × ℝ)}
    (hS : ∀ q : ℝ × ℝ, q ∈ S ↔ (q.1 + p, q.2) ∈ S) :
    qA p ⁻¹' (qA p '' S) = S := by
  ext w
  constructor
  · rintro ⟨k, hk, hwk⟩
    obtain ⟨n, hn1, hn2⟩ := (qA_eq_iff p w k).mp hwk.symm
    have hk' : (w.1 + n * p, w.2) ∈ S := by
      rw [← hn1, ← hn2]; exact hk
    exact (periodic_shift hS n w).mp hk'
  · intro hw; exact ⟨w, hw, rfl⟩

lemma isOpenQuotientMap_qA (p : ℝ) : IsOpenQuotientMap (qA p) := by
  have h1 : IsOpenQuotientMap (fun x : ℝ => (x : AddCircle p)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have h3 : IsOpenQuotientMap (Prod.map (fun x : ℝ => (x : AddCircle p)) id) :=
    IsOpenQuotientMap.prodMap h1 (IsOpenQuotientMap.id (X := ℝ))
  rw [show qA p = Prod.map (fun x : ℝ => (x : AddCircle p)) id from rfl]
  exact h3

lemma isClosed_qA_image (p : ℝ) {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (hper : ∀ q : ℝ × ℝ, q ∈ S ↔ (q.1 + p, q.2) ∈ S) :
    IsClosed (qA p '' S) := by
  have hiff : IsClosed ((qA p) ⁻¹' (qA p '' S)) ↔ IsClosed (qA p '' S) :=
    (isOpenQuotientMap_qA p).isQuotientMap.isCoinducing.isClosed_preimage
  rw [← hiff, qA_preimage_image (p := p) hper]
  exact hS

/-- The "strip quotient": `↥(Icc a b)` for the height and the circle for the horizontal
position. -/
abbrev YX (p a b : ℝ) := AddCircle p × ↥(Set.Icc a b)

/-- The closed strip `a ≤ ·.2 ≤ b` as a subspace of `AddCircle p × ℝ`. -/
abbrev Ystrip (p a b : ℝ) := ↥{v : AddCircle p × ℝ | a ≤ v.2 ∧ v.2 ≤ b}

/-- The homeomorphism between the product model and the strip model. -/
def homeoYX (p a b : ℝ) : YX p a b ≃ₜ Ystrip p a b where
  toFun v := ⟨(v.1, v.2.1), v.2.2⟩
  invFun v := (v.1.1, ⟨v.1.2, v.2⟩)
  left_inv v := rfl
  right_inv v := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_snd.comp continuous_subtype_val

lemma locallyPathConnected_Ystrip (p a b : ℝ) : LocallyPathConnectedSpace (Ystrip p a b) := by
  haveI hA : LocallyPathConnectedSpace (AddCircle p) := by
    show LocallyPathConnectedSpace (Quotient (QuotientAddGroup.leftRel (AddSubgroup.zmultiples p)))
    infer_instance
  haveI hI : LocallyPathConnectedSpace ↥(Set.Icc a b) :=
    LocallyPathConnectedSpace.of_convex (convex_Icc a b)
  haveI hX : LocallyPathConnectedSpace (YX p a b) := inferInstance
  exact (homeoYX p a b).isQuotientMap.locallyPathConnectedSpace

lemma isPreconnected_subtype_preimage' {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsPreconnected t) (hts : t ⊆ s) :
    IsPreconnected (Subtype.val ⁻¹' t : Set ↥s) := by
  refine (Topology.IsInducing.subtypeVal (t := s)).isPreconnected_image.mp ?_
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr hts]
  exact ht

lemma qA_shift (p : ℝ) (k : ℤ) (q : ℝ × ℝ) : qA p (q.1 + k * p, q.2) = qA p q := by
  apply Prod.ext
  · show ((q.1 + k * p : ℝ) : AddCircle p) = (q.1 : AddCircle p)
    have hnp : ((k * p : ℝ) : AddCircle p) = 0 := by
      have hk : (k * p : ℝ) = k • p := by rw [zsmul_eq_mul]
      rw [hk, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    rw [AddCircle.coe_add, hnp]; simp
  · rfl
theorem wall_blocks_translate_path {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hsub : K ⊆ {q : ℝ × ℝ | a ≤ q.2 ∧ q.2 ≤ b})
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    {C : Set (ℝ × ℝ)} (hC : C ⊆ K) (hCpre : IsPreconnected C)
    (ha : a ∈ closure ((fun q : ℝ × ℝ => q.2) '' C))
    (hb : b ∈ closure ((fun q : ℝ × ℝ => q.2) '' C)) :
    ∀ z : ℝ × ℝ, a ≤ z.2 → z.2 ≤ b → z ∉ K →
      ¬ ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
        γ 0 = z ∧ γ 1 = (z.1 + p, z.2) ∧
          (∀ t, a ≤ (γ t).2 ∧ (γ t).2 ≤ b) ∧ ∀ t, γ t ∉ K := by
  intro z hz1 hz2 hzK hpath
  obtain ⟨γ, hγ0, hγ1, hγstrip, hγK⟩ := hpath
  haveI : Fact (0 < p) := ⟨hp⟩
  -- staircase
  have hγ : γ 1 = ((γ 0).1 + p, (γ 0).2) := by rw [hγ0, hγ1]
  obtain ⟨G, hG0, hGper, hGform⟩ := exists_staircase p hp.ne' γ hγ
  have hGc : Continuous G := G.continuous
  have hGstrip : ∀ t, a ≤ (G t).2 ∧ (G t).2 ≤ b := by
    intro t; obtain ⟨s, n, hs⟩ := hGform t; rw [hs]; exact hγstrip s
  have hGavoid : ∀ t, G t ∉ K := by
    intro t ht
    obtain ⟨s, n, hs⟩ := hGform t
    rw [hs] at ht
    have hk : ((γ s).1 + (n : ℝ) * p, (γ s).2) ∈ K := by
      have heq : ((γ s).1 + (n : ℝ) * p, (γ s).2)
          = ((γ s).1 + p * (n : ℝ), (γ s).2) := by
        congr 1; ring
      rw [heq]; exact ht
    exact hγK s ((periodic_shift hper n (γ s)).mp hk)
  -- range G is p-periodic
  have hrgper : ∀ q : ℝ × ℝ, q ∈ Set.range G ↔ (q.1 + p, q.2) ∈ Set.range G := by
    intro q
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t + p, by rw [hGper]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t - p, ?_⟩
      have h1 : (G t).1 = (G (t - p)).1 + p := by
        have := congrArg Prod.fst (hGper (t - p))
        rwa [show t - p + p = t by ring] at this
      have h2 : (G t).2 = (G (t - p)).2 := by
        have := congrArg Prod.snd (hGper (t - p))
        rwa [show t - p + p = t by ring] at this
      have h5 : (G t).1 = q.1 + p := by rw [ht]
      have h6 : (G t).2 = q.2 := by rw [ht]
      exact Prod.ext (by linarith) (by linarith)
  -- the quotient sets
  set KA : Set (AddCircle p × ℝ) := qA p '' Set.range G with hKA
  set Z : Set (AddCircle p × ℝ) := closure (qA p '' C) with hZ
  have hKAclosed : IsClosed KA := by
    have heq : qA p '' Set.range G = qA p '' (G '' Set.Icc (0:ℝ) p) := by
      apply Set.Subset.antisymm
      · rintro w ⟨t, ht, hq⟩
        obtain ⟨t₀, rfl⟩ := ht
        set s : ℝ := t₀ - (⌊t₀ / p⌋ : ℤ) * p with hs
        have hfrac : s ∈ Set.Icc (0:ℝ) p := by
          have h1 : s = p * (t₀ / p - (⌊t₀ / p⌋ : ℝ)) := by
            rw [hs]; field_simp
          rw [h1]
          refine ⟨mul_nonneg hp.le (by linarith [Int.floor_le (t₀ / p)]), ?_⟩
          calc p * (t₀ / p - (⌊t₀ / p⌋ : ℝ)) ≤ p * 1 :=
                mul_le_mul_of_nonneg_left (by linarith [Int.lt_floor_add_one (t₀ / p)]) hp.le
            _ = p := mul_one p
        have hGz : G t₀ = ((G s).1 + (⌊t₀ / p⌋ : ℤ) * p, (G s).2) := by
          have hh := staircase_zsmul hGper (⌊t₀ / p⌋ : ℤ) s
          rw [show s + (⌊t₀ / p⌋ : ℤ) * p = t₀ by rw [hs]; ring] at hh
          exact hh
        refine ⟨G s, ⟨s, hfrac, rfl⟩, ?_⟩
        rw [← hq, hGz]
        exact (qA_shift p (⌊t₀ / p⌋ : ℤ) (G s)).symm
      · rintro w ⟨x, ⟨s, hs, hx⟩, hq⟩
        exact ⟨x, ⟨s, hx⟩, hq⟩
    rw [hKA, heq]
    exact ((isCompact_Icc.image hGc).image (qA_continuous p)).isClosed
  have hZK : Z ⊆ qA p '' K := by
    rw [hZ]
    exact closure_minimal (Set.image_mono hC) (isClosed_qA_image p hK hper)
  have hZY : Z ⊆ {v : AddCircle p × ℝ | a ≤ v.2 ∧ v.2 ≤ b} := by
    intro v hv
    obtain ⟨k, hkK, hkq⟩ := hZK hv
    rw [← hkq]
    exact hsub hkK
  -- Z ∩ KA = ∅
  have hZKA : Z ∩ KA = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwZ, hwKA⟩
    obtain ⟨k, hkK, hkq⟩ := hZK hwZ
    obtain ⟨g, hgG, hgq⟩ := hwKA
    obtain ⟨n, hn1, hn2⟩ := (qA_eq_iff p k g).mp (by rw [hkq, hgq])
    have hkg : k ∈ Set.range G := by
      have hkn : k = (g.1 + (-n : ℤ) * p, g.2) := by
        refine Prod.ext ?_ ?_
        · rw [hn1]; push_cast; ring
        · rw [hn2]
      rw [hkn]
      exact (periodic_shift hrgper (-n) g).mpr hgG
    obtain ⟨tk, htk⟩ := hkg
    exact hGavoid tk (htk ▸ hkK)
  -- Z is preconnected and compact
  have hZpre : IsPreconnected Z := by
    rw [hZ]
    exact (hCpre.image _ (qA_continuous p).continuousOn).closure
  have hZcpt : IsCompact Z := by
    have hZc : IsClosed Z := by rw [hZ]; exact isClosed_closure
    refine IsCompact.of_isClosed_subset
      ((isCompact_univ (X := AddCircle p)).prod (isCompact_Icc (a := a) (b := b))) hZc ?_
    intro v hv
    exact ⟨trivial, hZY hv⟩
  -- Z meets the two boundary circles
  have hclZ : IsClosed ((fun v : AddCircle p × ℝ => v.2) '' Z) :=
    (hZcpt.image continuous_snd).isClosed
  have hZbound (y : ℝ) (hyc : y ∈ closure ((fun q : ℝ × ℝ => q.2) '' C)) :
      (Z ∩ {v : AddCircle p × ℝ | v.2 = y}).Nonempty := by
    have hmem : y ∈ ((fun v : AddCircle p × ℝ => v.2) '' Z) := by
      rw [← hclZ.closure_eq]
      refine closure_mono ?_ hyc
      rintro y ⟨c, hc, hcy⟩
      exact ⟨qA p c, subset_closure ⟨c, hc, rfl⟩, by simpa [qA] using hcy⟩
    obtain ⟨v, hvZ, hv2⟩ := hmem
    exact ⟨v, hvZ, hv2⟩
  obtain ⟨wa, hwaZ, hwa2⟩ := hZbound a ha
  obtain ⟨wb, hwbZ, hwb2⟩ := hZbound b hb
  -- separation
  have hsep : ∀ ψ : C(Set.Icc (0:ℝ) 1, AddCircle p × ℝ),
      (∀ t, a ≤ (ψ t).2 ∧ (ψ t).2 ≤ b) →
      (ψ 0).2 = a → (ψ 1).2 = b → (∀ t, ψ t ∉ KA) → False := by
    intro ψ hψstrip hψ0 hψ1 hψavoid
    have hcov : IsCoveringMap (fun x : ℝ => (x : AddCircle p)) :=
      AddCircle.isCoveringMap_coe (𝕜 := ℝ) p
    let θ' : C(Set.Icc (0:ℝ) 1, AddCircle p) :=
      ⟨fun t => (ψ t).1, continuous_fst.comp ψ.continuous⟩
    obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, (x0 : AddCircle p) = θ' 0 :=
      QuotientAddGroup.mk_surjective (θ' 0)
    let θl : C(Set.Icc (0:ℝ) 1, ℝ) := hcov.liftPath θ' x0 hx0.symm
    let δ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) :=
      ⟨fun t => (θl t, (ψ t).2),
        θl.continuous.prodMk (continuous_snd.comp ψ.continuous)⟩
    have hδstrip : ∀ t, a ≤ (δ t).2 ∧ (δ t).2 ≤ b := fun t => hψstrip t
    have hδ0 : (δ 0).2 = a := hψ0
    have hδ1 : (δ 1).2 = b := hψ1
    have hδavoid : ∀ t, δ t ∉ Set.range G := by
      intro t ht
      have hmemKA : qA p (δ t) ∈ KA := by
        rw [hKA]; exact ⟨δ t, ht, rfl⟩
      have hq : qA p (δ t) = ψ t := by
        apply Prod.ext
        · show ((θl t : ℝ) : AddCircle p) = (ψ t).1
          exact congrFun (hcov.liftPath_lifts θ' x0 hx0.symm) t
        · rfl
      exact hψavoid t (hq ▸ hmemKA)
    exact no_bottom_top_path_of_staircase hp hab hGc hGper hGstrip hδstrip hδ0 hδ1 hδavoid
  -- connectedness contradiction
  have hwaY : (⟨wa, hZY hwaZ⟩ : Ystrip p a b) ∈ Subtype.val ⁻¹' Z := hwaZ
  have hwbY : (⟨wb, hZY hwbZ⟩ : Ystrip p a b) ∈ Subtype.val ⁻¹' Z := hwbZ
  haveI : LocallyPathConnectedSpace (Ystrip p a b) := locallyPathConnected_Ystrip p a b
  have hKAsclosed : IsClosed (Subtype.val ⁻¹' KA : Set (Ystrip p a b)) :=
    hKAclosed.preimage continuous_subtype_val
  have hZy_pre : IsPreconnected (Subtype.val ⁻¹' Z : Set (Ystrip p a b)) :=
    isPreconnected_subtype_preimage' hZpre hZY
  have hZyV : (Subtype.val ⁻¹' Z : Set (Ystrip p a b)) ⊆ (Subtype.val ⁻¹' KA)ᶜ := by
    intro v hv hvK
    exact (Set.eq_empty_iff_forall_notMem.mp hZKA) v ⟨hv, hvK⟩
  obtain ⟨γv, hγv⟩ :=
    IsPreconnected.joinedIn_of_isOpen_subset hZy_pre hKAsclosed.isOpen_compl hZyV hwaY hwbY
  have hmap : ∀ t, (γv.map continuous_subtype_val) t = Subtype.val (γv t) := fun t => rfl
  have hψstrip : ∀ t, a ≤ ((γv.map continuous_subtype_val) t).2 ∧
      ((γv.map continuous_subtype_val) t).2 ≤ b := by
    intro t; exact (γv t).2
  have hψavoid : ∀ t, (γv.map continuous_subtype_val) t ∉ KA := by
    intro t; exact hγv t
  have hψ0 : ((γv.map continuous_subtype_val) 0).2 = a := by
    have h0 : (γv.map continuous_subtype_val) 0 = wa := by
      rw [hmap 0, γv.source]
    rw [h0]; exact hwa2
  have hψ1 : ((γv.map continuous_subtype_val) 1).2 = b := by
    have h1 : (γv.map continuous_subtype_val) 1 = wb := by
      rw [hmap 1, γv.target]
    rw [h1]; exact hwb2
  exact hsep (γv.map continuous_subtype_val) hψstrip hψ0 hψ1 hψavoid

end

end Commons.Topology.Strip

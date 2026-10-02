import Mathlib
import Submission.Work.Morse.Basic
import Submission.Work.Morse.isCritPoint_of_isMin
import Submission.Work.Morse.homeomorph_level
import Submission.Work.Morse.exists_le_level_homeomorph
import Submission.Work.Morse.sublevel_ball_range
import Submission.Work.Morse.mfderiv_eq_one
import Submission.Work.Morse.two_balls
import Submission.Work.Morse.continuous_flow

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology
open Metric (sphere)

/-! ## Auxiliary lemmas -/

lemma bilin_smul_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (x : E) : B (c • x) (c • x) = c * c * (B x x) := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

lemma eq_zero_of_eq_smul {E : Type*} [AddCommGroup E] [Module ℝ E] {w : E} {k : ℝ} (hk : k ≠ 1)
    (h : w = k • w) : w = 0 := by
  have h1 : (k - 1) • w = 0 := by rw [sub_smul, one_smul, ← h]; exact sub_self _
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) hk
  · exact h2

theorem isCritPoint_neg {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    IsCritPoint (n := n) (fun x => - f x) p ↔ IsCritPoint (n := n) f p := by
  have h1 : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) f p (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) (fun x => -f x) p
      (-(mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p)) := h1.neg
  simp only [IsCritPoint, h2.mfderiv]
  exact neg_eq_zero

theorem isCritPoint_of_isMax {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {p : M} (hmax : ∀ x, f x ≤ f p) :
    IsCritPoint (n := n) f p := by
  rw [← isCritPoint_neg hf p]
  exact isCritPoint_of_isMin hf.neg (fun x => neg_le_neg (hmax x))

/-- There are two points of `M` different from `p` and from each other. -/
theorem exists_two_ne {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n)
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {p : M}
    (hp : p ∈ e.source) (he0 : e p = 0) :
    ∃ x y : M, x ≠ p ∧ y ≠ p ∧ x ≠ y := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 := exists_ne 0
  have hnorm : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have h0mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.target := he0 ▸ e.map_source hp
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.open_target 0 h0mem
  have hε4 : (0:ℝ) < ε / (4 * ‖u‖) := by positivity
  set w : EuclideanSpace ℝ (Fin n) := (ε / (4 * ‖u‖)) • u with hwdef
  have hwnorm : ‖w‖ = ε / 4 := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos hε4]
    field_simp
  have hwne : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hwnorm; linarith
  have hwle : ‖w‖ < ε := by rw [hwnorm]; linarith
  have hwtgt : w ∈ e.target := hεsub (by rw [Metric.mem_ball, dist_zero_right]; exact hwle)
  have h2wle : ‖(2:ℝ) • w‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2), hwnorm]; linarith
  have h2wtgt : (2:ℝ) • w ∈ e.target :=
    hεsub (by rw [Metric.mem_ball, dist_zero_right]; exact h2wle)
  refine ⟨e.symm w, e.symm ((2:ℝ) • w), ?_, ?_, ?_⟩
  · intro h
    have h' : p = e.symm w := h.symm
    rw [OpenPartialHomeomorph.eq_symm_apply e hp hwtgt, he0] at h'
    exact hwne h'.symm
  · intro h
    have h' : p = e.symm ((2:ℝ) • w) := h.symm
    rw [OpenPartialHomeomorph.eq_symm_apply e hp h2wtgt, he0] at h'
    have h2 : (2:ℝ) • w = 0 := h'.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · exact hwne h3
  · intro h
    have h1 : e (e.symm w) = e (e.symm ((2:ℝ) • w)) := by rw [h]
    rw [e.right_inv hwtgt, e.right_inv h2wtgt] at h1
    have h2 : w + w = w := by rw [← two_smul ℝ w]; exact h1.symm
    exact hwne (add_eq_right.mp h2)

theorem posDef_of_isMin {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {m : M} (hmin : ∀ x, f m ≤ f x)
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hm : m ∈ e.source) (he0 : e m = 0)
    {B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hA : ∀ᶠ x in 𝓝 0, f (e.symm x) - f m = B x x)
    {p q : M} (hpq : p ≠ q)
    (hminsub : ∀ x, (∀ y, f x ≤ f y) → x = p ∨ x = q) :
    ∀ v, v ≠ 0 → 0 < B v v := by
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hA
  have h0tgt : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.target := he0 ▸ e.map_source hm
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.isOpen_iff.mp e.open_target 0 h0tgt
  set ε : ℝ := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hεsub1 : Metric.ball 0 ε ⊆ {y | f (e.symm y) - f m = B y y} :=
    fun y hy => hε₁sub (Metric.ball_subset_ball (min_le_left _ _) hy)
  have hεsub2 : Metric.ball 0 ε ⊆ e.target :=
    fun y hy => hε₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hnonneg : ∀ x, 0 ≤ B x x := by
    intro x
    set t : ℝ := ε / (8 * (‖x‖ + 1)) with htdef
    have htpos : 0 < t := by positivity
    have hmem : t • x ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg x, hε]
    have hB := hεsub1 hmem
    simp only [Set.mem_setOf_eq] at hB
    have hge : 0 ≤ f (e.symm (t • x)) - f m := sub_nonneg.mpr (hmin _)
    rw [bilin_smul_smul B t x] at hB
    rw [hB] at hge
    have htt : 0 < t * t := mul_pos htpos htpos
    nlinarith
  intro v hv
  refine lt_of_le_of_ne (hnonneg v) (Ne.symm ?_)
  intro hBv
  set c : ℝ := ε / (8 * (‖v‖ + 1)) with hcdef
  have hcpos : 0 < c := by positivity
  set w : EuclideanSpace ℝ (Fin n) := c • v with hwdef
  have hcv : c * ‖v‖ < ε / 8 := by
    rw [hcdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v, hε]
  have hwlt4 : ‖w‖ < ε / 4 := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]; linarith
  have hwmem : w ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have h2mem : (2:ℝ) • w ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have h3mem : (3:ℝ) • w ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ)<3)]
    linarith
  have hwtgt := hεsub2 hwmem
  have h2tgt := hεsub2 h2mem
  have h3tgt := hεsub2 h3mem
  have hBw : B w w = 0 := by rw [hwdef, bilin_smul_smul B c v, hBv, mul_zero]
  have hB2 : B ((2:ℝ) • w) ((2:ℝ) • w) = 0 := by rw [bilin_smul_smul B 2 w, hBw, mul_zero]
  have hB3 : B ((3:ℝ) • w) ((3:ℝ) • w) = 0 := by rw [bilin_smul_smul B 3 w, hBw, mul_zero]
  have hfw : f (e.symm w) = f m := by
    have h1 := hεsub1 hwmem; simp only [Set.mem_setOf_eq] at h1; rw [hBw] at h1; linarith
  have hf2 : f (e.symm ((2:ℝ) • w)) = f m := by
    have h1 := hεsub1 h2mem; simp only [Set.mem_setOf_eq] at h1; rw [hB2] at h1; linarith
  have hf3 : f (e.symm ((3:ℝ) • w)) = f m := by
    have h1 := hεsub1 h3mem; simp only [Set.mem_setOf_eq] at h1; rw [hB3] at h1; linarith
  have hH1 : e.symm w = p ∨ e.symm w = q :=
    hminsub _ (fun y => by rw [hfw]; exact hmin y)
  have hH2 : e.symm ((2:ℝ) • w) = p ∨ e.symm ((2:ℝ) • w) = q :=
    hminsub _ (fun y => by rw [hf2]; exact hmin y)
  have hH3 : e.symm ((3:ℝ) • w) = p ∨ e.symm ((3:ℝ) • w) = q :=
    hminsub _ (fun y => by rw [hf3]; exact hmin y)
  have hx12 : e.symm w ≠ e.symm ((2:ℝ) • w) := by
    intro hh
    have hh' : w = (2:ℝ) • w := by
      have := congrArg e hh
      rwa [e.right_inv hwtgt, e.right_inv h2tgt] at this
    have hw0 : w = 0 := eq_zero_of_eq_smul (by norm_num : (2:ℝ) ≠ 1) hh'
    rw [hwdef] at hw0
    rcases smul_eq_zero.mp hw0 with h | h
    · exact absurd h (ne_of_gt hcpos)
    · exact hv h
  have hx13 : e.symm w ≠ e.symm ((3:ℝ) • w) := by
    intro hh
    have hh' : w = (3:ℝ) • w := by
      have := congrArg e hh
      rwa [e.right_inv hwtgt, e.right_inv h3tgt] at this
    have hw0 : w = 0 := eq_zero_of_eq_smul (by norm_num : (3:ℝ) ≠ 1) hh'
    rw [hwdef] at hw0
    rcases smul_eq_zero.mp hw0 with h | h
    · exact absurd h (ne_of_gt hcpos)
    · exact hv h
  have hx23 : e.symm ((2:ℝ) • w) ≠ e.symm ((3:ℝ) • w) := by
    intro hh
    have hh' : (2:ℝ) • w = (3:ℝ) • w := by
      have := congrArg e hh
      rwa [e.right_inv h2tgt, e.right_inv h3tgt] at this
    have hh1 : w = ((2:ℝ)⁻¹ * 3) • w := by
      have h2 : (1/2:ℝ) • ((2:ℝ) • w) = (1/2:ℝ) • ((3:ℝ) • w) := by rw [← hh']
      simpa [smul_smul] using h2
    have hw0 : w = 0 := eq_zero_of_eq_smul (by norm_num : ((2:ℝ)⁻¹ * 3) ≠ 1) hh1
    exact hx12 (by rw [hw0]; simp)
  rcases hH1 with h1 | h1 <;> rcases hH2 with h2 | h2 <;> rcases hH3 with h3 | h3
  · exact hx12 (h1.trans h2.symm)
  · exact hx12 (h1.trans h2.symm)
  · exact hx13 (h1.trans h3.symm)
  · exact hx23 (h2.trans h3.symm)
  · exact hx23 (h2.trans h3.symm)
  · exact hx13 (h1.trans h3.symm)
  · exact hx12 (h1.trans h2.symm)
  · exact hx12 (h1.trans h2.symm)

/-- If `f` attains its minimum at `m` and the nondegenerate points are the two points `p ≠ q`,
then `m` is a *strict* minimum. -/
theorem strict_min_of_isMin_aux {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {p q m mx : M} (hpq : p ≠ q)
    (hcrit : ∀ x, IsCritPoint (n := n) f x → HasMorseThru (n := n) f x)
    (huniq : ∀ x, HasMorseThru (n := n) f x → x = p ∨ x = q)
    (hmM : HasMorseThru (n := n) f m) (hmxM : HasMorseThru (n := n) f mx)
    (hmin : ∀ x, f m ≤ f x) (hmax : ∀ x, f x ≤ f mx) (hltm : f m < f mx) :
    ∀ x, x ≠ m → f m < f x := by
  have hm_mem : m = p ∨ m = q := huniq m hmM
  have hmx_mem : mx = p ∨ mx = q := huniq mx hmxM
  intro x hx
  rcases lt_or_eq_of_le (hmin x) with hh | hh
  · exact hh
  · exfalso
    have hcx : IsCritPoint (n := n) f x := isCritPoint_of_isMin hf (fun y => hh ▸ hmin y)
    have hxmem : x = p ∨ x = q := huniq x (hcrit x hcx)
    have hpm : p = x ∨ p = m := by
      rcases hxmem with h1 | h1 <;> rcases hm_mem with h2 | h2
      · exact absurd (h1.trans h2.symm) hx
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
      · exact absurd (h1.trans h2.symm) hx
    have hqm : q = x ∨ q = m := by
      rcases hxmem with h1 | h1 <;> rcases hm_mem with h2 | h2
      · exact absurd (h1.trans h2.symm) hx
      · exact Or.inr h2.symm
      · exact Or.inl h1.symm
      · exact absurd (h1.trans h2.symm) hx
    have hpmf : f p = f m := by
      rcases hpm with h1 | h1
      · rw [h1]; exact hh.symm
      · rw [h1]
    have hqmf : f q = f m := by
      rcases hqm with h1 | h1
      · rw [h1]; exact hh.symm
      · rw [h1]
    have hmxf : f mx = f m := by
      rcases hmx_mem with h1 | h1
      · rw [h1]; exact hpmf
      · rw [h1]; exact hqmf
    linarith [hltm, hmxf]

/-- If `f` attains its maximum at `mx`, then `mx` is a *strict* maximum. -/
theorem strict_max_of_isMax_aux {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {p q m mx : M} (hpq : p ≠ q)
    (hcrit : ∀ x, IsCritPoint (n := n) f x → HasMorseThru (n := n) f x)
    (huniq : ∀ x, HasMorseThru (n := n) f x → x = p ∨ x = q)
    (hmM : HasMorseThru (n := n) f m) (hmxM : HasMorseThru (n := n) f mx)
    (hmin : ∀ x, f m ≤ f x) (hmax : ∀ x, f x ≤ f mx) (hltm : f m < f mx) :
    ∀ x, x ≠ mx → f x < f mx := by
  have hm_mem : m = p ∨ m = q := huniq m hmM
  have hmx_mem : mx = p ∨ mx = q := huniq mx hmxM
  intro x hx
  rcases lt_or_eq_of_le (hmax x) with hh | hh
  · exact hh
  · exfalso
    have hcx : IsCritPoint (n := n) f x := isCritPoint_of_isMax hf (fun y => hh ▸ hmax y)
    have hxmem : x = p ∨ x = q := huniq x (hcrit x hcx)
    have hpm : p = x ∨ p = mx := by
      rcases hxmem with h1 | h1 <;> rcases hmx_mem with h2 | h2
      · exact absurd (h1.trans h2.symm) hx
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
      · exact absurd (h1.trans h2.symm) hx
    have hqm : q = x ∨ q = mx := by
      rcases hxmem with h1 | h1 <;> rcases hmx_mem with h2 | h2
      · exact absurd (h1.trans h2.symm) hx
      · exact Or.inr h2.symm
      · exact Or.inl h1.symm
      · exact absurd (h1.trans h2.symm) hx
    have hpmf : f p = f mx := by
      rcases hpm with h1 | h1
      · rw [h1]; exact hh
      · rw [h1]
    have hqmf : f q = f mx := by
      rcases hqm with h1 | h1
      · rw [h1]; exact hh
      · rw [h1]
    have hmf : f m = f mx := by
      rcases hm_mem with h1 | h1
      · rw [h1]; exact hpmf
      · rw [h1]; exact hqmf
    linarith [hltm, hmf]

/-! ## The main theorem -/

theorem reeb {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] (hn : 1 ≤ n) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (h : ∃ p q : M, p ≠ q ∧
          (∀ x : M, IsCritPoint (n := n) f x → HasMorseThru (n := n) f x) ∧
          HasMorseThru (n := n) f p ∧ HasMorseThru (n := n) f q ∧
          ∀ x : M, HasMorseThru (n := n) f x → x = p ∨ x = q) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨p0, q0, hpq0, hcrit, hMp0, hMq0, huniq0⟩ := h
  obtain ⟨ep, -, hp0src, hep0, Bp, -, hBp⟩ := hMp0
  -- a point different from `p0` and `q0`
  obtain ⟨x1, x2, hx1, hx2, hx12⟩ := exists_two_ne hn hp0src hep0
  -- `f` is not constant
  have hnonconst : ∃ a b : M, f a ≠ f b := by
    by_contra hc
    push Not at hc
    have hconst : ∀ y, f y = f x1 := fun y => hc y x1
    have hcrit1 : IsCritPoint (n := n) f x1 := by
      rw [IsCritPoint, show f = fun _ => f x1 from funext hconst]
      simp
    have hcrit2 : IsCritPoint (n := n) f x2 := by
      rw [IsCritPoint, show f = fun _ => f x1 from funext hconst]
      simp
    rcases huniq0 x1 (hcrit x1 hcrit1) with h3 | h3 <;>
      rcases huniq0 x2 (hcrit x2 hcrit2) with h4 | h4
    · exact hx1 h3
    · exact hx1 h3
    · exact hx2 h4
    · exact hx12 (h3.trans h4.symm)
  -- minimum and maximum
  obtain ⟨m, -, hminm0⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuous.continuousOn
  obtain ⟨mx, -, hmaxmx0⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuous.continuousOn
  have hminm : ∀ x, f m ≤ f x := fun x => (isMinOn_iff.mp hminm0) x (Set.mem_univ x)
  have hmaxmx : ∀ x, f x ≤ f mx := fun x => (isMaxOn_iff.mp hmaxmx0) x (Set.mem_univ x)
  have hmM : HasMorseThru (n := n) f m := hcrit m (isCritPoint_of_isMin hf hminm)
  have hmxM : HasMorseThru (n := n) f mx := hcrit mx (isCritPoint_of_isMax hf hmaxmx)
  have hm_mem : m = p0 ∨ m = q0 := huniq0 m hmM
  have hmx_mem : mx = p0 ∨ mx = q0 := huniq0 mx hmxM
  have hne : f m ≠ f mx := by
    intro heq
    obtain ⟨a, b, hab⟩ := hnonconst
    refine hab ?_
    have ha : f a = f m := le_antisymm (by rw [heq]; exact hmaxmx a) (hminm a)
    have hb : f b = f m := le_antisymm (by rw [heq]; exact hmaxmx b) (hminm b)
    rw [ha, hb]
  have hlt : f m < f mx := lt_of_le_of_ne (hminm mx) hne
  have hstrictm := strict_min_of_isMin_aux hf hpq0 hcrit huniq0 hmM hmxM hminm hmaxmx hlt
  have hstrictmx := strict_max_of_isMax_aux hf hpq0 hcrit huniq0 hmM hmxM hminm hmaxmx hlt
  -- quadratic models at the minimum and the maximum
  obtain ⟨em, hemem, hmsrc, hem0, Bm, -, hBm⟩ := hmM
  obtain ⟨emx, hemxmem, hmxsrc, hemx0, Bmx, -, hBmx⟩ := hmxM
  have hminsub : ∀ x : M, (∀ y, f x ≤ f y) → x = p0 ∨ x = q0 :=
    fun x hx => huniq0 x (hcrit x (isCritPoint_of_isMin hf hx))
  have hminsubg : ∀ x : M, (∀ y, -f x ≤ -f y) → x = p0 ∨ x = q0 :=
    fun x hx => huniq0 x (hcrit x (isCritPoint_of_isMax hf (fun y => by linarith [hx y])))
  have hBmpos : ∀ v, v ≠ 0 → 0 < Bm v v :=
    posDef_of_isMin hf hminm hmsrc hem0 hBm hpq0 hminsub
  set Bmx' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := -Bmx
    with hBmx'def
  have hgm : ∀ᶠ x in 𝓝 0, (fun y => -f y) (emx.symm x) - (fun y => -f y) mx = Bmx' x x := by
    filter_upwards [hBmx] with x hx
    rw [hBmx'def]
    simp only [Pi.neg_apply, ContinuousLinearMap.neg_apply]
    linarith [hx]
  have hBmx'pos : ∀ v, v ≠ 0 → 0 < Bmx' v v :=
    posDef_of_isMin hf.neg (fun x => neg_le_neg (hmaxmx x)) hmxsrc hemx0 hgm hpq0 hminsubg
  -- disk ranges
  obtain ⟨δm, hδmpos, hδm⟩ :=
    sublevel_ball_range hf hemem hmsrc hem0 hBmpos hBm hstrictm
  have hgstrict : ∀ x, x ≠ mx → (fun y => -f y) mx < (fun y => -f y) x :=
    fun x hx => by simp only [Pi.neg_apply]; linarith [hstrictmx x hx]
  obtain ⟨δx, hδxpos, hδx⟩ :=
    sublevel_ball_range hf.neg hemxmem hmxsrc hemx0 hBmx'pos hgm hgstrict
  -- numerical levels
  have hba : 0 < f mx - f m := sub_pos.mpr hlt
  set δ₁ : ℝ := min δm ((f mx - f m) / 8) / 2 with hδ₁def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; positivity
  have hδ₁δm : δ₁ < δm := by
    rw [hδ₁def]; have h1 := min_le_left δm ((f mx - f m) / 8); linarith [hδmpos, hba]
  have hδ₁lt : δ₁ < (f mx - f m) / 8 := by
    rw [hδ₁def]; have h1 := min_le_right δm ((f mx - f m) / 8); linarith [hba]
  set δ₂ : ℝ := min δx ((f mx - f m) / 8) / 2 with hδ₂def
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hδ₂δx : δ₂ < δx := by
    rw [hδ₂def]; have h1 := min_le_left δx ((f mx - f m) / 8); linarith [hδxpos, hba]
  have hδ₂lt : δ₂ < (f mx - f m) / 8 := by
    rw [hδ₂def]; have h1 := min_le_right δx ((f mx - f m) / 8); linarith [hba]
  obtain ⟨E₁, hE₁⟩ := hδm δ₁ ⟨hδ₁pos, hδ₁δm⟩
  obtain ⟨E₂, hE₂⟩ := hδx δ₂ ⟨hδ₂pos, hδ₂δx⟩
  set a3 : ℝ := f m + δ₁ / 2 with ha3def
  have ha3gt : f m < a3 := by rw [ha3def]; linarith
  have ha3lt : a3 < f m + δ₁ := by rw [ha3def]; linarith
  set c : ℝ := (f m + δ₁ + (f mx - δ₂)) / 2 with hcdef
  have hc_gt : f m + δ₁ < c := by rw [hcdef]; linarith
  have hc_lt : c < f mx - δ₂ := by rw [hcdef]; linarith
  have ha3c : a3 < c := by linarith
  set c₂ : ℝ := (f mx - δ₂ + f mx) / 2 with hc₂def
  have hc₂gt : f mx - δ₂ < c₂ := by rw [hc₂def]; linarith
  have hc₂lt : c₂ < f mx := by rw [hc₂def]; linarith
  have hc₂c : c < c₂ := by linarith
  have ha3c₂ : a3 < c₂ := by linarith
  -- membership transfer between the two pairs of points
  have hmmne : m ≠ mx := fun hh => hne (by rw [hh])
  have hpair : ∀ y, y = p0 ∨ y = q0 → y = m ∨ y = mx := by
    intro y hy
    rcases hy with hy | hy
    · rcases hm_mem with hm | hm
      · exact Or.inl (hy.trans hm.symm)
      · rcases hmx_mem with hmx | hmx
        · exact Or.inr (hy.trans hmx.symm)
        · exact absurd (hm.trans hmx.symm) hmmne
    · rcases hm_mem with hm | hm
      · rcases hmx_mem with hmx | hmx
        · exact absurd (hm.trans hmx.symm) hmmne
        · exact Or.inr (hy.trans hmx.symm)
      · exact Or.inl (hy.trans hm.symm)
  -- regularity on the strip
  have hKreg : ∀ x ∈ f ⁻¹' (Set.Icc a3 c₂), ¬ IsCritPoint (n := n) f x := by
    intro x hx hxc
    have hxp := hpair x (huniq0 x (hcrit x hxc))
    simp only [Set.mem_preimage, Set.mem_Icc] at hx
    rcases hxp with h | h
    · rw [h] at hx; linarith [hx.1, ha3gt]
    · rw [h] at hx; linarith [hx.2, hc₂lt]
  have hKcompact : IsCompact (f ⁻¹' (Set.Icc a3 c₂)) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  obtain ⟨v, hvsm, hv1⟩ := mfderiv_eq_one hf hKcompact hKreg
  obtain ⟨Φ, hΦ0, hΦint, hΦsmul, hΦcont⟩ := continuous_flow v hvsm
  have hv : ∀ x, a3 < f x → f x < c₂ → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (v x) = 1 :=
    fun x h1 h2 => hv1 x (by
      simp only [Set.mem_preimage, Set.mem_Icc]; exact ⟨le_of_lt h1, le_of_lt h2⟩)
  -- the lower half
  obtain ⟨ψ, hψmono, hψp, hψle, hψA, hψB⟩ := exists_le_level_homeomorph ha3lt hc_gt hc₂c
  obtain ⟨H₁, hH₁⟩ := homeomorph_level hf ha3c₂ hv hΦ0 hΦint hΦsmul hΦcont hψle hψA hψB
  have hiff₁ : ∀ x : M, (f x ≤ c) ↔ (f (H₁ x) ≤ f m + δ₁) := by
    intro x
    rw [hH₁ x, ← hψp]
    exact hψmono.le_iff_le.symm
  let hα₁ : {x : M // f x ≤ c} ≃ₜ {x : M // f x ≤ f m + δ₁} :=
    H₁.subtype (p := fun x => f x ≤ c) (q := fun y => f y ≤ f m + δ₁) hiff₁
  have hαbd : ∀ x : {x : M // f x ≤ c},
      (x : M) ∈ {y : M | c ≤ f y} ↔ (hα₁.trans E₁) x ∈ Metric.sphere 0 1 := by
    intro x
    show c ≤ f (x : M) ↔ _
    have hc : (hα₁.trans E₁) x ∈ Metric.sphere 0 1 ↔ f (x : M) = c := by
      rw [Homeomorph.trans_apply, hE₁]
      have h1 : ((hα₁ x : {y : M // f y ≤ f m + δ₁}) : M) = H₁ (x : M) := rfl
      rw [h1, hH₁, ← hψp]
      exact ⟨fun h => hψmono.injective h, fun h => by rw [h]⟩
    exact ⟨fun h => hc.mpr (le_antisymm x.2 h), fun h => (hc.mp h).ge⟩
  -- the upper half
  obtain ⟨ψ', hψ'mono, hψ'p, hψ'le, hψ'A, hψ'B⟩ :=
    exists_le_level_homeomorph ha3c hc_lt hc₂gt
  obtain ⟨H, hH⟩ := homeomorph_level hf ha3c₂ hv hΦ0 hΦint hΦsmul hΦcont hψ'le hψ'A hψ'B
  have hH₂ : ∀ x, f (H.symm x) = ψ'.symm (f x) := by
    intro x
    have h1 : ψ' (f (H.symm x)) = f x := by
      have h2 := hH (H.symm x)
      rw [Homeomorph.apply_symm_apply] at h2
      exact h2.symm
    calc f (H.symm x) = ψ'.symm (ψ' (f (H.symm x))) :=
          (Homeomorph.symm_apply_apply ψ' _).symm
      _ = ψ'.symm (f x) := by rw [h1]
  have hshift : f mx - δ₂ = ψ'.symm c := by
    rw [← hψ'p, Homeomorph.symm_apply_apply]
  have hiff₂ : ∀ x : M, (c ≤ f x) ↔ (-f (H.symm x) ≤ -f mx + δ₂) := by
    intro x
    have h4 : (-f (H.symm x) ≤ -f mx + δ₂) ↔ (f mx - δ₂ ≤ f (H.symm x)) := by
      constructor <;> intro h <;> linarith
    rw [h4, hH₂ x]
    constructor
    · intro hc
      have h5 : ψ' (f mx - δ₂) ≤ ψ' (ψ'.symm (f x)) := by
        rw [hψ'p, Homeomorph.apply_symm_apply]; exact hc
      exact hψ'mono.le_iff_le.mp h5
    · intro hc
      have h5 : ψ' (f mx - δ₂) ≤ ψ' (ψ'.symm (f x)) := hψ'mono.le_iff_le.mpr hc
      rw [hψ'p, Homeomorph.apply_symm_apply] at h5
      exact h5
  let hβ₁ : {x : M // c ≤ f x} ≃ₜ {x : M // -f x ≤ -f mx + δ₂} :=
    H.symm.subtype (p := fun x => c ≤ f x) (q := fun y => -f y ≤ -f mx + δ₂) hiff₂
  have hβbd : ∀ x : {x : M // c ≤ f x},
      (x : M) ∈ {y : M | f y ≤ c} ↔ (hβ₁.trans E₂) x ∈ Metric.sphere 0 1 := by
    intro x
    show f (x : M) ≤ c ↔ _
    have hc : (hβ₁.trans E₂) x ∈ Metric.sphere 0 1 ↔ f (x : M) = c := by
      rw [Homeomorph.trans_apply, hE₂]
      have h1 : ((hβ₁ x : {y : M // -f y ≤ -f mx + δ₂}) : M) = H.symm (x : M) := rfl
      rw [h1, hH₂]
      constructor
      · intro h
        have h5 : ψ'.symm (f (x : M)) = f mx - δ₂ := by linarith
        rw [hshift] at h5
        have h6 := congrArg ψ' h5
        rwa [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h6
      · intro h
        rw [show -f mx + δ₂ = -ψ'.symm c from by rw [← hshift]; ring]
        rw [h]
    exact ⟨fun h => hc.mpr (le_antisymm h x.2), fun h => le_of_eq (hc.mp h)⟩
  refine two_balls hn (isClosed_Iic.preimage hf.continuous) (isClosed_Ici.preimage hf.continuous)
    ?_ hαbd hβbd
  rw [Set.eq_univ_iff_forall]
  intro y
  rcases le_total (f y) c with h | h
  · exact Or.inl h
  · exact Or.inr h

end Work.Morse

import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.Geo.Prism.Push
import Submission.Work.Geo.Prism.Tube.exists_J_thickening
import Submission.Work.Geo.Prism.Tube.exists_tube
import Submission.Work.PL.Defs

namespace Work.Geo.Prism.PushRel

open Set Metric
open scoped Topology
open Classical

/-- The cutoff `χ = if J.Nonempty then max 0 (1 - infDist · J / ρ) else 0`.  It is continuous,
nonnegative, `≤ 1`, equal to `1` on `J`, and `χ z > 0` forces `infDist z J < ρ`.  The `if`
makes it identically `0` when `J = ∅`, so that the "thickened neighbourhood of `J`" input is
never invoked in the empty case. -/
noncomputable def chi {b : ℕ} (J : Set (PL.E b)) (ρ : ℝ) (z : PL.E b) : ℝ :=
  if J.Nonempty then max 0 (1 - Metric.infDist z J / ρ) else 0

theorem chi_continuous {b : ℕ} (J : Set (PL.E b)) (ρ : ℝ) : Continuous (chi J ρ) := by
  by_cases h : J.Nonempty
  · have he : chi J ρ = fun z => max 0 (1 - Metric.infDist z J / ρ) := by
      funext z; simp [chi, h]
    rw [he]
    exact continuous_const.max
      (continuous_const.sub ((Metric.continuous_infDist_pt J).div_const ρ))
  · have he : chi J ρ = fun _ => (0 : ℝ) := by funext z; simp [chi, h]
    rw [he]; exact continuous_const

theorem chi_nonneg {b : ℕ} (J : Set (PL.E b)) (ρ : ℝ) (z : PL.E b) : 0 ≤ chi J ρ z := by
  unfold chi; split_ifs with h
  · exact le_max_left _ _
  · norm_num

theorem chi_le_one {b : ℕ} (J : Set (PL.E b)) {ρ : ℝ} (hρ : 0 < ρ) (z : PL.E b) :
    chi J ρ z ≤ 1 := by
  unfold chi; split_ifs with h
  · refine max_le (by norm_num) ?_
    have : 0 ≤ Metric.infDist z J / ρ := div_nonneg Metric.infDist_nonneg hρ.le
    linarith
  · norm_num

theorem chi_eq_one {b : ℕ} {J : Set (PL.E b)} {ρ : ℝ} {z : PL.E b} (hz : z ∈ J) :
    chi J ρ z = 1 := by
  have hne : J.Nonempty := ⟨z, hz⟩
  have h0 : Metric.infDist z J = 0 :=
    (Metric.mem_closure_iff_infDist_zero hne).mp (subset_closure hz)
  unfold chi
  rw [ite_eq_left hne, h0]
  norm_num

theorem infDist_lt_of_chi_pos {b : ℕ} {J : Set (PL.E b)} {ρ : ℝ} (hρ : 0 < ρ) {z : PL.E b}
    (h : 0 < chi J ρ z) : Metric.infDist z J < ρ := by
  by_cases hne : J.Nonempty
  · have he : chi J ρ z = max 0 (1 - Metric.infDist z J / ρ) := by simp [chi, hne]
    rw [he] at h
    have h2 : 0 < 1 - Metric.infDist z J / ρ := by
      by_contra hle
      rw [max_eq_left (le_of_not_gt hle)] at h
      exact lt_irrefl 0 h
    have h3 : Metric.infDist z J / ρ < 1 := by linarith
    rwa [div_lt_one hρ] at h3
  · simp only [chi, ite_eq_right hne] at h
    exact absurd h (lt_irrefl 0)

/-- Pure topology: if `F` is closed, `ψ`, `γ` are continuous and `ψ > γ` on `frontier F`, then
for `H = F ∩ {z | ψ z ≤ γ z}`: `H` misses the frontier of `F` (so lies in the interior of
`F`), and `ψ = γ` on the frontier of `H`.  This is the input `prism_push` needs when applied
with `F := H`, `φ := ψ`, `γ := γ`. -/
theorem frontier_H_facts {α : Type*} [TopologicalSpace α] {F : Set α} (hF : IsClosed F)
    {ψ γ : α → ℝ} (hψ : Continuous ψ) (hγ : Continuous γ)
    (hgt : ∀ z ∈ frontier F, γ z < ψ z) :
    (F ∩ {z : α | ψ z ≤ γ z} ∩ frontier F = ∅) ∧
    (F ∩ {z : α | ψ z ≤ γ z} ⊆ interior F) ∧
    (∀ z ∈ frontier (F ∩ {z : α | ψ z ≤ γ z}), ψ z = γ z) := by
  have hSclosed : IsClosed {z : α | ψ z ≤ γ z} := isClosed_le hψ hγ
  have hclH : closure (F ∩ {z : α | ψ z ≤ γ z}) ⊆ F :=
    hF.closure_subset_iff.mpr (fun z hz => hz.1)
  have hclS : closure (F ∩ {z : α | ψ z ≤ γ z}) ⊆ {z : α | ψ z ≤ γ z} :=
    hSclosed.closure_subset_iff.mpr (fun z hz => hz.2)
  have hHfr : F ∩ {z : α | ψ z ≤ γ z} ∩ frontier F = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzH, hzF⟩
    have h1 : γ z < ψ z := hgt z hzF
    have h2 : ψ z ≤ γ z := hzH.2
    linarith
  have hdisj : frontier (F ∩ {z : α | ψ z ≤ γ z}) ∩ frontier F = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzH, hzF⟩
    have h1 : γ z < ψ z := hgt z hzF
    have h2 : ψ z ≤ γ z := hclS (frontier_subset_closure hzH)
    linarith
  refine ⟨hHfr, ?_, ?_⟩
  · intro z hz
    have hzmem : z ∈ interior F ∪ frontier F := by
      rw [← closure_eq_interior_union_frontier, hF.closure_eq]; exact hz.1
    rcases hzmem with h | h
    · exact h
    · exact (Set.eq_empty_iff_forall_notMem.mp hHfr z ⟨hz, h⟩).elim
  · intro z hzfr
    have hzcl : z ∈ closure (F ∩ {z : α | ψ z ≤ γ z}) := frontier_subset_closure hzfr
    have hzclc : z ∈ closure (F ∩ {z : α | ψ z ≤ γ z})ᶜ := by
      have h := hzfr; rw [frontier_eq_closure_inter_closure] at h; exact h.2
    have hzF : z ∈ F := hclH hzcl
    have hzS : ψ z ≤ γ z := hclS hzcl
    have hzIntF : z ∈ interior F := by
      have hzmem : z ∈ interior F ∪ frontier F := by
        rw [← closure_eq_interior_union_frontier, hF.closure_eq]; exact hzF
      rcases hzmem with h | h
      · exact h
      · exact (Set.eq_empty_iff_forall_notMem.mp hdisj z ⟨hzfr, h⟩).elim
    refine le_antisymm hzS ?_
    by_contra hcon
    have hcon' : ψ z < γ z := lt_of_not_ge hcon
    have hVopen : IsOpen ({w : α | ψ w < γ w} ∩ interior F) :=
      (isOpen_lt hψ hγ).inter isOpen_interior
    have hzV : z ∈ ({w : α | ψ w < γ w} ∩ interior F) := ⟨hcon', hzIntF⟩
    have hVH : ({w : α | ψ w < γ w} ∩ interior F) ⊆ F ∩ {z : α | ψ z ≤ γ z} := by
      intro w hw
      have hw1 : ψ w < γ w := hw.1
      refine ⟨interior_subset hw.2, ?_⟩
      show ψ w ≤ γ w
      exact le_of_lt hw1
    have hzIntH : z ∈ interior (F ∩ {z : α | ψ z ≤ γ z}) := interior_maximal hVH hVopen hzV
    have hnotcl : z ∉ closure (F ∩ {z : α | ψ z ≤ γ z})ᶜ := by
      intro hmem
      have hsub : closure (F ∩ {z : α | ψ z ≤ γ z})ᶜ ⊆
          (interior (F ∩ {z : α | ψ z ≤ γ z}))ᶜ :=
        closure_minimal (fun w hw => by
          rw [Set.mem_compl_iff] at hw ⊢
          exact fun hwi => hw (interior_subset hwi))
          isOpen_interior.isClosed_compl
      exact (hsub hmem) hzIntH
    exact hnotcl hzclc

/-- **G1' `prism_push_rel`** (blueprint §2, Newman Theorem 2, the form §14 uses): engulf the prism over `F` by `h '' U` with a homeomorphism that is the identity on the closed set `A`, where the only points of the prism that lie in `A` are the floor points and those over `J`. -/
theorem prism_push_rel {a b : ℕ} (F J : Set (PL.E b)) (hF : IsCompact F) (hJ : IsClosed J)
    (hJF : J ⊆ F) (γ₀ γ₁ : PL.E b → ℝ) (h₀ : Continuous γ₀) (h₁ : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z) (hfr : ∀ z ∈ frontier F, γ₀ z = γ₁ z)
    (U W A : Set (Work.Geo.Prism.Pr a b)) (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A)
    (hAU : A ⊆ U)
    (hbase : ∀ z ∈ F, ((0 : PL.E a), z, γ₀ z) ∈ U)
    (hJU : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z), ((0 : PL.E a), z, t) ∈ U)
    (hS : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z), ((0 : PL.E a), z, t) ∈ W)
    (hAS : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      ((0 : PL.E a), z, t) ∈ A → t = γ₀ z ∨ z ∈ J) :
    ∃ h : Work.Geo.Prism.Pr a b ≃ₜ Work.Geo.Prism.Pr a b,
      PL.CSupp h W ∧ (∀ x ∈ A, h x = x) ∧
      ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z), ((0 : PL.E a), z, t) ∈ h '' U := by
  classical
  -- ## Step 1: a slab over the floor graph `{z ↦ γ₀ z}` is inside `U`.
  obtain ⟨δ, hδ, hfloorU⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (γ₀ z + δ), ((0 : PL.E a), z, t) ∈ U := by
    have hKc : IsCompact ((fun z : PL.E b => (z, γ₀ z)) '' F) :=
      hF.image (continuous_id.prodMk h₀)
    have hKsub : ({0} : Set (PL.E a)) ×ˢ ((fun z : PL.E b => (z, γ₀ z)) '' F) ⊆ U := by
      rintro ⟨y, q⟩ ⟨hy, hq⟩
      obtain ⟨z, hz, rfl⟩ := hq
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hbase z hz
    obtain ⟨η, δ, hη, hδ, hsub⟩ :=
      Work.Geo.Prism.Tube.exists_tube (a := a) hKc hU hKsub
    refine ⟨δ, hδ, ?_⟩
    intro z hz t ht
    rw [Set.mem_Icc] at ht
    refine hsub ?_
    refine ⟨by simpa using hη.le, (z, γ₀ z), ⟨z, hz, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_right (abs_nonneg _), Real.dist_eq,
      abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  -- ## Step 2: the thickening of the prism over `J` and the cutoff `χ`.
  have hJthick : J.Nonempty → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : PL.E b, Metric.infDist z J < ρ →
      ∀ t ∈ Set.Icc (γ₀ z - ρ) (γ₁ z + ρ), ((0 : PL.E a), z, t) ∈ U :=
    fun hne => Work.Geo.Prism.Tube.exists_J_thickening hF hJ hJF hne h₀ h₁ hU hJU
  have hex : ∃ ρ : ℝ, 0 < ρ ∧ (J.Nonempty → ∀ z : PL.E b, Metric.infDist z J < ρ →
      ∀ t ∈ Set.Icc (γ₀ z - ρ) (γ₁ z + ρ), ((0 : PL.E a), z, t) ∈ U) := by
    by_cases h : J.Nonempty
    · obtain ⟨ρ, hρ, hρU⟩ := hJthick h
      exact ⟨ρ, hρ, fun _ => hρU⟩
    · exact ⟨1, one_pos, fun hh => absurd hh h⟩
  let ρ : ℝ := Classical.choose hex
  have hρpos : 0 < ρ := (Classical.choose_spec hex).1
  have hρU : J.Nonempty → ∀ z : PL.E b, Metric.infDist z J < ρ →
      ∀ t ∈ Set.Icc (γ₀ z - ρ) (γ₁ z + ρ), ((0 : PL.E a), z, t) ∈ U :=
    (Classical.choose_spec hex).2
  have hχU : ∀ z : PL.E b, 0 < chi J ρ z → Metric.infDist z J < ρ →
      ∀ t ∈ Set.Icc (γ₀ z - ρ) (γ₁ z + ρ), ((0 : PL.E a), z, t) ∈ U := by
    intro z hχ hdist t ht
    by_cases h : J.Nonempty
    · exact hρU h z hdist t ht
    · simp only [chi, ite_eq_right h] at hχ
      exact absurd hχ (lt_irrefl 0)
  -- ## Step 3: `ψ` and `H`.
  let ψ : PL.E b → ℝ := fun z => γ₀ z + δ / 2 + (γ₁ z - γ₀ z + 1) * chi J ρ z
  have hψcont : Continuous ψ := by
    simp only [ψ]
    exact (h₀.add continuous_const).add
      (((h₁.sub h₀).add continuous_const).mul (chi_continuous J ρ))
  have hψ_gt_γ₀ : ∀ z ∈ F, γ₀ z < ψ z := by
    intro z hz
    have hχ0 : 0 ≤ chi J ρ z := chi_nonneg J ρ z
    have hfac : 0 ≤ γ₁ z - γ₀ z + 1 := by linarith [hle z hz]
    have hprod : 0 ≤ (γ₁ z - γ₀ z + 1) * chi J ρ z := mul_nonneg hfac hχ0
    have : 0 < δ / 2 := by linarith
    simp only [ψ]
    linarith
  have hψ_gt_γ₁ : ∀ z ∈ J, γ₁ z < ψ z := by
    intro z hz
    have hχ1 : chi J ρ z = 1 := chi_eq_one hz
    simp only [ψ, hχ1, mul_one]
    linarith
  let H : Set (PL.E b) := F ∩ {z : PL.E b | ψ z ≤ γ₁ z}
  have hHsub : H ⊆ F := fun z hz => hz.1
  have hHclosed : IsClosed H := hF.isClosed.inter (isClosed_le hψcont h₁)
  have hHc : IsCompact H := hF.of_isClosed_subset hHclosed hHsub
  have hHfrontier : ∀ z ∈ frontier H, ψ z = γ₁ z :=
    (frontier_H_facts (F := F) hF.isClosed (ψ := ψ) (γ := γ₁) hψcont h₁
      (fun z hz => by rw [← hfr z hz]; exact hψ_gt_γ₀ z (hF.isClosed.frontier_subset hz))).2.2
  -- ## Step 4: the slab between `γ₀` and `min ψ γ₁` lies in `U`.
  have hgraphU : ∀ z ∈ F, ∀ t ∈ Set.Icc (γ₀ z) (min (ψ z) (γ₁ z)),
      ((0 : PL.E a), z, t) ∈ U := by
    intro z hz t ht
    rw [Set.mem_Icc] at ht
    by_cases hχ : chi J ρ z = 0
    · have hψz : ψ z = γ₀ z + δ / 2 := by simp only [ψ, hχ, mul_zero, add_zero]
      have htle : t ≤ γ₀ z + δ := by
        have h1 : t ≤ ψ z := le_trans ht.2 (min_le_left _ _)
        rw [hψz] at h1; linarith
      exact hfloorU z hz t ⟨ht.1, htle⟩
    · have hχpos : 0 < chi J ρ z := lt_of_le_of_ne (chi_nonneg J ρ z) (Ne.symm hχ)
      have hdist : Metric.infDist z J < ρ := infDist_lt_of_chi_pos hρpos hχpos
      have htle : t ≤ γ₁ z + ρ :=
        le_trans (le_trans ht.2 (min_le_right _ _)) (by linarith [hρpos.le])
      exact hχU z hχpos hdist t ⟨by linarith [ht.1, hρpos.le], htle⟩
  -- ## Step 5: apply G1 with `F := H`, `φ := ψ`, `γ := γ₁`, `W := W \ A`.
  have hW' : IsOpen (W \ A) := hW.sdiff hA
  have hleH : ∀ z ∈ H, ψ z ≤ γ₁ z := fun z hz => hz.2
  have hbaseH : ∀ z ∈ H, ((0 : PL.E a), z, ψ z) ∈ U := by
    intro z hz
    exact hgraphU z hz.1 (ψ z) ⟨le_of_lt (hψ_gt_γ₀ z hz.1), le_min le_rfl hz.2⟩
  have hSH : ∀ z ∈ H, ∀ t, ψ z ≤ t → t ≤ γ₁ z → ((0 : PL.E a), z, t) ∈ W \ A := by
    intro z hz t ht1 ht2
    have hzF : z ∈ F := hz.1
    have hg₀ψ : γ₀ z < ψ z := hψ_gt_γ₀ z hzF
    have htγ₀ : γ₀ z ≤ t := le_trans (le_of_lt hg₀ψ) ht1
    refine ⟨hS z hzF t ⟨htγ₀, ht2⟩, ?_⟩
    intro hA'
    rcases hAS z hzF t ⟨htγ₀, ht2⟩ hA' with h' | h'
    · linarith [ht1, hg₀ψ]
    · linarith [hψ_gt_γ₁ z h', hz.2]
  obtain ⟨h, hsupp, hfix, _hcoord, hengulf⟩ :=
    Work.Geo.Prism.prism_push H hHc ψ γ₁ hψcont h₁ hleH hHfrontier U (W \ A) hU hW'
      hbaseH hSH
  refine ⟨h, ?_, ?_, ?_⟩
  · obtain ⟨C, hC, hCW, hfixC⟩ := hsupp
    exact ⟨C, hC, fun x hx => (hCW hx).1, hfixC⟩
  · intro x hxA
    obtain ⟨C, hC, hCW, hfixC⟩ := hsupp
    exact hfixC x (fun hxC => (hCW hxC).2 hxA)
  · intro z hzF t ht
    rw [Set.mem_Icc] at ht
    by_cases hcase : ψ z ≤ t
    · exact hengulf z ⟨hzF, le_trans hcase ht.2⟩ t hcase ht.2
    · have hlt : t < ψ z := lt_of_not_ge hcase
      have htU : ((0 : PL.E a), z, t) ∈ U :=
        hgraphU z hzF t ⟨ht.1, le_min (le_of_lt hlt) ht.2⟩
      have hfx : h ((0 : PL.E a), z, t) = ((0 : PL.E a), z, t) :=
        hfix (0 : PL.E a) z t (Or.inr (le_of_lt hlt))
      rw [← hfx]
      exact ⟨((0 : PL.E a), z, t), htU, rfl⟩

end Work.Geo.Prism.PushRel

import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.ErgMax.Basic

/-!
# C4c — faces, Bauer's maximum principle, extreme points

* `Mset ρ`: `A`-invariant probability measures carried by `Drho ρ`; `Efun`: the entropy at `a₀`.
* `exists_minimal_closed_face` (Zorn): a nonempty compact family of closed faces has a minimal one.
* `exists_extreme_of_minimal_face` (Bauer): a minimal nonempty closed face of a compact set of
  invariant probability measures is a singleton, hence an extreme point.
-/

open MeasureTheory Topology Filter
open scoped ENNReal BoundedContinuousFunction

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

/-! ## The set `M` and the entropy functional -/

/-- `M ρ`: `A`-invariant probability measures carried by `Drho ρ`. -/
def Mset (ρ : ℝ) : Set (Measure X3) :=
  {μ | IsProbabilityMeasure μ ∧ IsAInvariant μ ∧ μ (Drho ρ) = 1}

/-- The entropy of `μ` for the time-one map `a₀`, as a real number. -/
def Efun (μ : Measure X3) : ℝ := (ent μ (act a0)).toReal

/-! ## Transfer lemmas for `IsClosedProb` / `IsCompactProb` -/

theorem IsCompactProb.of_isClosedProb_subset {S T : Set (Measure X3)} (hS : IsClosedProb S)
    (hST : S ⊆ T) (hT : IsCompactProb T) : IsCompactProb S := by
  have h1 : {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ S}
      = {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ T} ∩
        {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ S} := by
    ext μ
    exact ⟨fun h => ⟨hST h, h⟩, fun h => h.2⟩
  rw [IsCompactProb, h1]
  exact hT.inter_right hS

theorem IsCompactProb.inter [T2Space (ProbabilityMeasure X3)] {S T : Set (Measure X3)}
    (hS : IsCompactProb S) (hT : IsClosedProb T) : IsCompactProb (S ∩ T) := by
  have h1 : {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ S ∩ T}
      = {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ S} ∩
        {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ T} := by
    ext μ
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [IsCompactProb, h1]
  exact hS.inter_right hT

/-! ## Separation of measures by bounded continuous functions -/

theorem exists_integral_ne_of_ne (h2 : P_X3) {μ ν : Measure X3} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : μ ≠ ν) :
    ∃ f : X3 →ᵇ ℝ, ∫ x, f x ∂μ ≠ ∫ x, f x ∂ν := by
  haveI : HasOuterApproxClosed X3 := by
    haveI : PolishSpace X3 := h2.2.1
    infer_instance
  by_contra hc
  simp only [not_exists, not_not] at hc
  exact h (MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure hc)

/-! ## Maximising a bounded continuous functional on a compact set of probability measures -/

theorem exists_maximiser {S : Set (ProbabilityMeasure X3)} (hSne : S.Nonempty)
    (hScomp : IsCompact S) (f : X3 →ᵇ ℝ) :
    ∃ μ₀ ∈ S, ∀ μ ∈ S, ∫ x, f x ∂(μ : Measure X3) ≤ ∫ x, f x ∂(μ₀ : Measure X3) := by
  obtain ⟨μ₀, hμ₀, hμ₀max⟩ := hScomp.exists_isMaxOn hSne
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).continuousOn
  exact ⟨μ₀, hμ₀, fun μ hμ => hμ₀max hμ⟩

theorem isFace_maximiserSet {M F : Set (Measure X3)} (hMprob : ∀ ν ∈ M, IsProbabilityMeasure ν)
    (hFface : IsFace M F) (f : X3 →ᵇ ℝ) {s : ℝ}
    (hmax : ∀ ν ∈ F, ∫ x, f x ∂ν ≤ s) :
    IsFace M {ν | ν ∈ F ∧ ∫ x, f x ∂ν = s} := by
  refine ⟨fun ν hν => hFface.subset hν.1, ?_⟩
  intro μ₁ h₁ μ₂ h₂ a b ha hb hab hcomb
  obtain ⟨hcombF, hcombs⟩ := hcomb
  have h1F : μ₁ ∈ F := hFface.mem_of_smul_add μ₁ h₁ μ₂ h₂ a b ha hb hab hcombF
  have h2F : μ₂ ∈ F := by
    refine hFface.mem_of_smul_add μ₂ h₂ μ₁ h₁ b a hb ha ?_ ?_
    · rw [add_comm]; exact hab
    · rw [add_comm]; exact hcombF
  haveI h1p : IsProbabilityMeasure μ₁ := hMprob μ₁ h₁
  haveI h2p : IsProbabilityMeasure μ₂ := hMprob μ₂ h₂
  have haf : a ≠ ⊤ := by
    intro h; rw [h, top_add] at hab; exact ENNReal.one_ne_top hab.symm
  have hbf : b ≠ ⊤ := by
    intro h; rw [h, add_top] at hab; exact ENNReal.one_ne_top hab.symm
  haveI hfin1 : IsFiniteMeasure (a • μ₁) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact lt_top_iff_ne_top.2 haf⟩
  haveI hfin2 : IsFiniteMeasure (b • μ₂) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact lt_top_iff_ne_top.2 hbf⟩
  have hlin : ∫ x, f x ∂(a • μ₁ + b • μ₂)
      = a.toReal * ∫ x, f x ∂μ₁ + b.toReal * ∫ x, f x ∂μ₂ := by
    rw [integral_add_measure (f.integrable (μ := a • μ₁)) (f.integrable (μ := b • μ₂)),
      integral_smul_measure, integral_smul_measure]
    simp [smul_eq_mul]
  have hsum : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add haf hbf, hab, ENNReal.toReal_one]
  have hle1 : ∫ x, f x ∂μ₁ ≤ s := hmax μ₁ h1F
  have hle2 : ∫ x, f x ∂μ₂ ≤ s := hmax μ₂ h2F
  have ha0 : 0 < a.toReal := ENNReal.toReal_pos ha.ne' haf
  have hb0 : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbf
  have hs : s = a.toReal * ∫ x, f x ∂μ₁ + b.toReal * ∫ x, f x ∂μ₂ := by
    rw [← hcombs, hlin]
  refine ⟨h1F, ?_⟩
  have hx : ∫ x, f x ∂μ₁ = s := by
    by_contra hxs
    have hxlt : ∫ x, f x ∂μ₁ < s := lt_of_le_of_ne hle1 hxs
    have h1 : a.toReal * ∫ x, f x ∂μ₁ < a.toReal * s := by nlinarith
    have h2 : b.toReal * ∫ x, f x ∂μ₂ ≤ b.toReal * s := by nlinarith
    have h3 : a.toReal * ∫ x, f x ∂μ₁ + b.toReal * ∫ x, f x ∂μ₂ <
        a.toReal * s + b.toReal * s := add_lt_add_of_lt_of_le h1 h2
    have h4 : a.toReal * s + b.toReal * s = s := by
      rw [← add_mul, hsum, one_mul]
    linarith [hs, h3, h4]
  exact hx

theorem isClosedProb_maximiserSet {F : Set (Measure X3)} (hFcl : IsClosedProb F)
    (f : X3 →ᵇ ℝ) (s : ℝ) :
    IsClosedProb {ν | ν ∈ F ∧ ∫ x, f x ∂ν = s} := by
  have h1 : {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ {ν | ν ∈ F ∧ ∫ x, f x ∂ν = s}}
      = {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ F} ∩
        {μ : ProbabilityMeasure X3 | ∫ x, f x ∂(μ : Measure X3) = s} := by
    ext μ
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [IsClosedProb, h1]
  exact IsClosed.inter hFcl
    (isClosed_eq (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f)
      continuous_const)

/-! ## The finite-intersection property for a chain of compact sets -/

theorem sInter_nonempty_of_chain [T2Space (ProbabilityMeasure X3)]
    {c : Set (Set (Measure X3))} (hcne : c.Nonempty)
    (hchain : ∀ x ∈ c, ∀ y ∈ c, x ⊆ y ∨ y ⊆ x)
    (hprob : ∀ x ∈ c, x ⊆ {ν : Measure X3 | IsProbabilityMeasure ν})
    (hne : ∀ x ∈ c, x.Nonempty) (hcl : ∀ x ∈ c, IsClosedProb x)
    (hcomp : ∀ x ∈ c, IsCompactProb x) : (⋂₀ c).Nonempty := by
  set T : Set (Set (ProbabilityMeasure X3)) :=
    {A | ∃ x ∈ c, A = {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ x}} with hT
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hcne
    exact ⟨_, x, hx, rfl⟩
  haveI : Nonempty ↥T := hTne.to_subtype
  have hTdir : DirectedOn (· ⊇ ·) T := by
    rintro A ⟨x, hx, rfl⟩ B ⟨y, hy, rfl⟩
    rcases hchain x hx y hy with hxy | hyx
    · exact ⟨_, ⟨x, hx, rfl⟩, fun _ h => h, fun ν hν => hxy hν⟩
    · exact ⟨_, ⟨y, hy, rfl⟩, fun ν hν => hyx hν, fun _ h => h⟩
  have hTnonempty : ∀ U ∈ T, U.Nonempty := by
    rintro A ⟨x, hx, rfl⟩
    obtain ⟨ν, hν⟩ := hne x hx
    exact ⟨(⟨ν, hprob x hx hν⟩ : ProbabilityMeasure X3), hν⟩
  have hTcomp : ∀ U ∈ T, IsCompact U := by
    rintro A ⟨x, hx, rfl⟩
    exact hcomp x hx
  have hTcl : ∀ U ∈ T, IsClosed U := by
    rintro A ⟨x, hx, rfl⟩
    exact hcl x hx
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    hTdir hTnonempty hTcomp hTcl
  exact ⟨(μ : Measure X3), Set.mem_sInter.2 fun x hx => hμ _ ⟨x, hx, rfl⟩⟩

/-! ## Zorn: a minimal nonempty closed face -/

theorem exists_minimal_closed_face [T2Space (ProbabilityMeasure X3)] {M Ms : Set (Measure X3)}
    (hMprob : ∀ ν ∈ M, IsProbabilityMeasure ν) (hMsne : Ms.Nonempty) (hMssub : Ms ⊆ M)
    (hMscl : IsClosedProb Ms) (hMsface : IsFace M Ms) (hMcomp : IsCompactProb M) :
    ∃ F, F.Nonempty ∧ F ⊆ Ms ∧ IsClosedProb F ∧ IsFace M F ∧
      ∀ G, G ⊆ F → G.Nonempty → IsClosedProb G → IsFace M G → G = F := by
  have hbound : ∀ c ⊆ {F : Set (Measure X3) | F.Nonempty ∧ F ⊆ Ms ∧ IsClosedProb F ∧
        IsFace M F}, IsChain (· ⊆ ·) c →
      ∃ lb ∈ {F : Set (Measure X3) | F.Nonempty ∧ F ⊆ Ms ∧ IsClosedProb F ∧ IsFace M F},
        ∀ s ∈ c, lb ⊆ s := by
    intro c hcS hchain
    by_cases hc0 : c = ∅
    · exact ⟨Ms, ⟨hMsne, fun _ h => h, hMscl, hMsface⟩,
        fun s hs => absurd (hc0 ▸ hs) (Set.notMem_empty s)⟩
    have hcne : c.Nonempty := Set.nonempty_iff_ne_empty.2 hc0
    · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hc0
      have hchain' : ∀ x ∈ c, ∀ y ∈ c, x ⊆ y ∨ y ⊆ x := fun x hx y hy => hchain.total hx hy
      have hne' : ∀ x ∈ c, x.Nonempty := fun x hx => (hcS hx).1
      have hsub' : ∀ x ∈ c, x ⊆ Ms := fun x hx => (hcS hx).2.1
      have hcl' : ∀ x ∈ c, IsClosedProb x := fun x hx => (hcS hx).2.2.1
      have hface' : ∀ x ∈ c, IsFace M x := fun x hx => (hcS hx).2.2.2
      have hprob' : ∀ x ∈ c, x ⊆ {ν : Measure X3 | IsProbabilityMeasure ν} :=
        fun x hx => ((hsub' x hx).trans hMssub).trans (fun ν hν => hMprob ν hν)
      have hcomp' : ∀ x ∈ c, IsCompactProb x := fun x hx =>
        IsCompactProb.of_isClosedProb_subset (hcl' x hx) ((hsub' x hx).trans hMssub) hMcomp
      refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_⟩, fun s hs => Set.sInter_subset_of_mem hs⟩
      · exact sInter_nonempty_of_chain hcne hchain' hprob' hne' hcl' hcomp'
      · exact (Set.sInter_subset_of_mem hx₀).trans (hsub' x₀ hx₀)
      · have h1 : {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ ⋂₀ c}
            = ⋂ x : ↥c, {μ : ProbabilityMeasure X3 |
                (μ : Measure X3) ∈ (x.1 : Set (Measure X3))} := by
          rw [Set.sInter_eq_iInter]
          ext μ
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rw [IsClosedProb, h1]
        exact isClosed_iInter fun x => hcl' x.1 x.2
      · exact isFace_sInter hcne hface'
  obtain ⟨F, hFmin⟩ := zorn_superset _ hbound
  exact ⟨F, hFmin.1.1, hFmin.1.2.1, hFmin.1.2.2.1, hFmin.1.2.2.2,
    fun G hGF hGne hGcl hGface =>
      le_antisymm hGF (hFmin.2 ⟨hGne, hGF.trans hFmin.1.2.1, hGcl, hGface⟩ hGF)⟩

/-! ## A minimal nonempty closed face is a singleton, hence an extreme point -/

theorem exists_extreme_of_minimal_face (h2 : P_X3) {M F : Set (Measure X3)}
    (hMprob : ∀ ν ∈ M, IsProbabilityMeasure ν) (hFne : F.Nonempty) (hFsub : F ⊆ M)
    (hFcl : IsClosedProb F) (hFface : IsFace M F) (hMcomp : IsCompactProb M)
    (hFmin : ∀ G, G ⊆ F → G.Nonempty → IsClosedProb G → IsFace M G → G = F) :
    ∃ μ, F = {μ} ∧ ∀ μ₁ ∈ M, ∀ μ₂ ∈ M, ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 →
      a • μ₁ + b • μ₂ = μ → μ₁ = μ := by
  have hsingle : ∀ μ₁ ∈ F, ∀ μ₂ ∈ F, μ₁ = μ₂ := by
    intro μ₁ h₁ μ₂ h₂
    by_contra hne'
    haveI h₁p : IsProbabilityMeasure μ₁ := hMprob μ₁ (hFsub h₁)
    haveI h₂p : IsProbabilityMeasure μ₂ := hMprob μ₂ (hFsub h₂)
    obtain ⟨f, hfne⟩ := exists_integral_ne_of_ne h2 hne'
    have hSne : {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ F}.Nonempty := by
      obtain ⟨ν, hν⟩ := hFne
      exact ⟨(⟨ν, hMprob ν (hFsub hν)⟩ : ProbabilityMeasure X3), hν⟩
    obtain ⟨ν₀, hν₀, hmax⟩ := exists_maximiser hSne
      (IsCompactProb.of_isClosedProb_subset hFcl hFsub hMcomp) f
    have hmax' : ∀ ν ∈ F, ∫ x, f x ∂ν ≤ ∫ x, f x ∂(ν₀ : Measure X3) := by
      intro ν hν
      exact hmax (⟨ν, hMprob ν (hFsub hν)⟩ : ProbabilityMeasure X3) hν
    have hν₀F : (ν₀ : Measure X3) ∈ F := hν₀
    have hface : IsFace M {ν | ν ∈ F ∧ ∫ x, f x ∂ν = ∫ x, f x ∂(ν₀ : Measure X3)} :=
      isFace_maximiserSet hMprob hFface f hmax'
    have hcl : IsClosedProb {ν | ν ∈ F ∧ ∫ x, f x ∂ν = ∫ x, f x ∂(ν₀ : Measure X3)} :=
      isClosedProb_maximiserSet hFcl f _
    have hne'' : {ν | ν ∈ F ∧ ∫ x, f x ∂ν = ∫ x, f x ∂(ν₀ : Measure X3)} ≠ F := by
      intro hEq
      have hA : ∀ ν : Measure X3,
          (ν ∈ {ν : Measure X3 | ν ∈ F ∧ ∫ x, f x ∂ν = ∫ x, f x ∂(ν₀ : Measure X3)} ↔ ν ∈ F) := by
        intro ν
        rw [hEq]
      have h1 : ∫ x, f x ∂μ₁ = ∫ x, f x ∂(ν₀ : Measure X3) := ((hA μ₁).2 h₁).2
      have h2 : ∫ x, f x ∂μ₂ = ∫ x, f x ∂(ν₀ : Measure X3) := ((hA μ₂).2 h₂).2
      exact hfne (by rw [h1, h2])
    exact hne'' (hFmin _ (fun ν hν => hν.1) ⟨(ν₀ : Measure X3), hν₀F, rfl⟩ hcl hface)
  obtain ⟨μ, hμF⟩ := hFne
  have hFsingle : F = {μ} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hμF, fun y hy => hsingle y hy μ hμF⟩
  refine ⟨μ, hFsingle, ?_⟩
  intro μ₁ h₁ μ₂ h₂ a b ha hb hab hcomb
  have hmem : a • μ₁ + b • μ₂ ∈ F := by
    rw [hcomb, hFsingle]
    exact Set.mem_singleton_iff.2 rfl
  have hmem' : μ₁ ∈ F := hFface.mem_of_smul_add μ₁ h₁ μ₂ h₂ a b ha hb hab hmem
  have hmem'' : μ₁ ∈ ({μ} : Set (Measure X3)) := hFsingle ▸ hmem'
  exact Set.mem_singleton_iff.1 hmem''

end

end Work.EKLComp.ErgMax

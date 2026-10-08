import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.CharCore.cfInner_int_vchar
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.FeitSibley.Coherence

theorem exists_lambda_T_rho {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {x₀ : ↥h.H → ℂ}
    (hx₀ : x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSZ h)))
    {y₀ : ↥h.H → ℂ}
    (hy₀ : y₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h))
    {a : ℕ} (hx₀deg : x₀ 1 = (a : ℂ) * (Nat.card h.D : ℂ))
    {ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hρV : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
      Work.Coherence.IsVChar (ρ y))
    (hkey : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
      y ≠ y₀ → Work.Coherence.cfInner
        (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y)
        = Work.Coherence.cfInner
          (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y₀) + (a : ℂ)) :
    ∃ c : ℤ, ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
      Work.Coherence.cfInner (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y)
        = if y = y₀ then ((c : ℂ) - (a : ℂ)) else (c : ℂ) := by
  classical
  -- `x₀` and `y₀` are members of `𝒮` (the latter through `𝒮(Q') ⊆ 𝒮`)
  have hxS : x₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hx₀).1
  have hyS : y₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 :=
    scriptSR_subset_scriptS h (FSQcomm h) hy₀
  -- the shifted element `x₀ - a • y₀` lies in `ℤ[𝒮]`
  have hmem : (x₀ - (a : ℂ) • y₀) ∈
      Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1) := by
    have h1 : x₀ ∈ Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1) :=
      Work.Coherence.self_mem_zSpan hxS
    have h2 : y₀ ∈ Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1) :=
      Work.Coherence.self_mem_zSpan hyS
    have h3 : ((a : ℂ) • y₀ : ↥h.H → ℂ) ∈
        Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1) := by
      have hcast : ((a : ℂ) • y₀ : ↥h.H → ℂ) = (a : ℤ) • y₀ := by
        conv_lhs => rw [← Int.cast_natCast (R := ℂ) a]
        rw [Int.cast_smul_eq_zsmul]
      rw [hcast]
      exact AddSubgroup.zsmul_mem _ h2 (a : ℤ)
    exact AddSubgroup.sub_mem _ h1 h3
  -- hence `Ind_H^G (x₀ - a • y₀)` is a virtual character of `G`
  have hVlin : Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) := by
    have hle : Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1) ≤
        AddSubgroup.comap (Work.FeitSibley.indLin h.H)
          (AddSubgroup.closure (Work.Coherence.Irr G)) := by
      rw [Work.Coherence.zSpan_le_iff]
      intro x hx
      exact isVChar_indLin_scriptS h hx
    exact hle hmem
  -- so its inner product against the virtual character `ρ y₀` is an integer
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Work.Coherence.cfInner
      (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y₀) = (n : ℂ) := by
    obtain ⟨m, hm⟩ := Work.CharCore.cfInner_int_vchar
      ((Work.CharCore.IsVChar_iff_coherence _).mpr hVlin)
      ((Work.CharCore.IsVChar_iff_coherence _).mpr (hρV y₀ hy₀))
    exact ⟨m, by rw [Work.CharCore.cfInner_coherence]; exact hm⟩
  -- `c = ⟨Ind (x₀ - a • y₀), ρ y₀⟩ + a` is the required integer
  refine ⟨n + (a : ℤ), ?_⟩
  intro y hy
  by_cases hyy : y = y₀
  · rw [hyy, hn, ite_eq_left rfl]
    push_cast
    ring
  · rw [ite_eq_right hyy, hkey y hy hyy, hn]
    push_cast
    ring

end Work.FeitSibley.Coherence

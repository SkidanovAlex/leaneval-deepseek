import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm
import Submission.Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.exists_indQH_of_mem_scriptSR_le_Q`

Extraction of the inducing character of `Q` for `χ ∈ 𝒮(R)`, where now only `R ≤ Q` is assumed
(compare `exists_indQH_of_mem_scriptSR`, which asks for `R ≤ S`; the argument does not use the
hypothesis at all, so it applies to any subgroup `R`).

Given `χ ∈ 𝒮(R)` — irreducible on `H`, non-trivial on `Q₁`, trivial on `R` — there is
`φ ∈ Irr Q`, trivial on `R`, with `χ = Ind_Q^H φ` and `χ(1) = |D| · φ(1)`.

The proof is the one of `exists_indQH_of_mem_scriptSR`: `𝒮 = {Ind_Q^H φ | Q₁ ⊄ ker φ}`
(`scriptS_eq_image`), Frobenius reciprocity makes `φ` a constituent of `χ|_Q`, and
`apply_eq_one_of_constituent` propagates the triviality of `χ` at `x ∈ R` to every constituent
of `χ|_Q`.  The degree formula is `[H : Q] · φ(1) = |D| · φ(1)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

/-- **Extraction of the inducing character of `Q`, for `R ≤ Q`.**  A character `χ ∈ 𝒮(R)`
(irreducible on `H`, non-trivial on `Q₁`, trivial on `R`) is induced from a character
`φ ∈ Irr Q` which is itself trivial on `R`, and its degree is `|D| · φ(1)`. -/
theorem exists_indQH_of_mem_scriptSR_le_Q {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {R : Subgroup G} (hR : R ≤ h.Q) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R) :
    ∃ φ ∈ Work.CharCore.Irr ↥h.Q,
      (∀ x : ↥h.Q, (x : G) ∈ R → φ x = φ 1) ∧
      χ = h.indQH φ ∧
      (Work.CharCore.irrDeg χ : ℝ) = (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg φ : ℝ) := by
  classical
  obtain ⟨hscriptS, hRtriv⟩ := (mem_scriptSR_iff h R).mp hχ
  obtain ⟨φ, hφ, -, hχeq⟩ := (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hscriptS
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := by
    have := hscriptS
    rw [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]
      at this
    exact this.1
  have hχC : χ ∈ Work.Clifford.Irr ↥h.H :=
    (Work.Clifford.corr_mem_Irr_charCore).mpr hχIrr
  have hIrr' : h.indQH φ ∈ Work.Clifford.Irr ↥h.H := by rw [← hχeq]; exact hχC
  have hcf : Work.CharCore.IsClassFun (h.indQH φ) := by
    rw [← hχeq]; exact Work.CharCore.isClassFun_of_mem_Irr hχIrr
  have hpull : Work.FeitSibley.CharQ.pull h φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    Work.FeitSibley.CharQ.pull_mem_Irr h hφ
  -- Frobenius reciprocity: `pull h φ` is a constituent of `χ|_Q`
  have hc : Work.Clifford.IsConstituentOf (Work.FeitSibley.CharQ.pull h φ)
      (Work.Clifford.resFun (h.Q.subgroupOf h.H) χ) := by
    rw [hχeq, Work.Clifford.IsConstituentOf]
    have hB : Work.Clifford.cfInner (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ))
        (Work.FeitSibley.CharQ.pull h φ) = 1 := by
      rw [Work.Clifford.cfInner_conj_symm]
      have hA := Work.Clifford.cfInner_indFun (Work.FeitSibley.CharQ.pull h φ) hcf
      rw [← hA, ← Work.FeitSibley.CharQ.indQH_eq_indFun,
        Work.Clifford.cfInner_eq_ite_of_mem_Irr hIrr' hIrr']
      simp
    rw [hB]
    simp
  refine ⟨φ, hφ, ?_, hχeq, ?_⟩
  · intro x hx
    have hxH : χ (((Work.FeitSibley.CharQ.toQ h x : ↥(h.Q.subgroupOf h.H)) : ↥h.H)) = χ 1 :=
      hRtriv _ (by rw [Work.FeitSibley.CharQ.toQ_coe]; exact hx)
    have h1 := Work.FeitSibley.CharQ.apply_eq_one_of_constituent h hχIrr hpull hc hxH
    rwa [Work.FeitSibley.CharQ.pull_toQ, Work.FeitSibley.CharQ.pull_one] at h1
  · have hdeg : Work.Clifford.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
        = (Nat.card h.D : ℂ) * (φ 1) := by
      change Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
        = (Nat.card h.D : ℂ) * (φ 1)
      rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one, index_subgroupOf_Q h]
    have h1 : χ 1 = (Nat.card h.D : ℂ) * (φ 1) := by
      rw [hχeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
      exact hdeg
    have hnat : Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg φ := by
      have hc : ((Work.CharCore.irrDeg χ : ℕ) : ℂ)
          = ((Nat.card h.D * Work.CharCore.irrDeg φ : ℕ) : ℂ) := by
        rw [Nat.cast_mul, ← Work.CharCore.irrDeg_spec hχIrr, h1,
          Work.CharCore.irrDeg_spec hφ]
      exact Nat.cast_inj.mp hc
    rw [hnat]
    push_cast
    ring

end Work.FeitSibley.Coherence

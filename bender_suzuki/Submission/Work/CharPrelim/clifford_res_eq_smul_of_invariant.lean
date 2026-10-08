import Mathlib
import Submission.Work.CharPrelim.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharPrelim

/-- **Clifford's theorem, invariant form.**  Let `N ⊴ G` be a normal subgroup, `θ ∈ Irr N` an
irreducible complex character of `N` whose inertia group is all of `G` (i.e. `θ` is
`G`-invariant), and `lam ∈ Irr G` an irreducible character of `G` lying over `θ`
(`⟪θ, lam|_N⟫ ≠ 0`).  Then the restriction `lam|_N` is a positive multiple of `θ`:
`lam|_N = e • θ` with `0 < e`.

Indeed, by Clifford's theorem (`Work.Clifford.clifford_decomposition`) there are `θ' ∈ Irr N`
and `0 < e` with `lam|_N = e • orbitSum N θ'`.  Since `θ` is a constituent of `lam|_N`, the
hypothesis forces `θ` to lie in the `G`-orbit of `θ'`, hence `charOrbit N θ = charOrbit N θ'`.
But `hinv` says every conjugate of `θ` is `θ`, so `charOrbit N θ = {θ}` and
`orbitSum N θ = θ`.  Therefore `orbitSum N θ' = θ` and `lam|_N = e • θ`. -/
theorem clifford_res_eq_smul_of_invariant {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [N.Normal] [Fintype ↥N] {θ : ↥N → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥N)
    (hinv : Work.Clifford.inertia N θ = ⊤) {lam : G → ℂ} (hlam : lam ∈ Work.CharCore.Irr G)
    (hlamθ : Work.CharCore.cfInner θ (Work.Induction.resFun N lam) ≠ 0) :
    ∃ e : ℕ, 0 < e ∧ Work.Induction.resFun N lam = (e : ℂ) • θ := by
  -- Transfer the irreducibility hypotheses to `Work.Clifford.Irr` (a `Set`).
  have hθC : θ ∈ Work.Clifford.Irr ↥N := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
  have hlamC : lam ∈ Work.Clifford.Irr G := (Work.Clifford.mem_Irr_charCore_iff).mpr hlam
  -- Clifford's theorem: `lam|_N = e • orbitSum N θ'` for some `θ' ∈ Irr N` and `0 < e`.
  obtain ⟨θ', hθ', e, he, hres⟩ := Work.Clifford.clifford_decomposition (N := N) hlamC
  have hθ'C : θ' ∈ Work.CharCore.Irr ↥N := (Work.Clifford.mem_Irr_charCore_iff).mp hθ'
  -- The hypothesis `⟪θ, lam|_N⟫ ≠ 0` shows that `θ` lies in the orbit of `θ'`.
  have hθne : θ ∈ Work.Clifford.charOrbit N θ' := by
    by_contra hc
    apply hlamθ
    rw [show Work.CharCore.cfInner θ (Work.Induction.resFun N lam)
        = Work.Clifford.cfInner θ (Work.Clifford.resFun N lam) from rfl, hres,
      Work.Clifford.cfInner_smul_right, Work.Clifford.cfInner_conj_symm,
      Work.Clifford.cfInner_orbitSum_eq_ite hθ' hθC]
    simp [hc]
  -- Hence `θ` and `θ'` have the same orbit.
  have horbit_eq : Work.Clifford.charOrbit N θ = Work.Clifford.charOrbit N θ' :=
    Work.Clifford.charOrbit_eq_of_mem hθne
  -- `hinv` makes that orbit a singleton.
  have hsing : Work.Clifford.charOrbit N θ = {θ} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Work.Clifford.theta_mem_charOrbit θ, ?_⟩
    intro φ hφ
    rw [Work.Clifford.mem_charOrbit] at hφ
    obtain ⟨g, hg⟩ := hφ
    rw [← hg]
    exact (Work.Clifford.mem_inertia N θ g).mp (by rw [hinv]; exact Subgroup.mem_top g)
  have horb : Work.Clifford.orbitSum N θ' = θ := by
    rw [Work.Clifford.orbitSum_eq_sum, ← horbit_eq, hsing, Finset.sum_singleton]
  exact ⟨e, he, by
    rw [show Work.Induction.resFun N lam = Work.Clifford.resFun N lam from rfl, hres, horb]⟩

end Work.CharPrelim

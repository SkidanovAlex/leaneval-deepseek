import Mathlib
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.caseC_W_semireg

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- **`FpfXi` for the `K`-action `ξ` in case c), without extra hypotheses.**

If `W = C_V(K) ≠ 1` (witnessed by `ζ ∈ W H t`, `ζ ≠ 1`) and `|Q| = |Q₀|³` with
`Q₀ = Q0sub H = ⟨Inv H⟩`, then the conjugation action `caseC_xi` of a generator of
`Ksub H t = Kset H t` on `Q` has the `FpfXi` properties: `|Q| = |Z(Q)|³`, `orderOf ξ = |Z(Q)| - 1`
and every non-trivial power of `ξ` is fixed-point-free on `Q`.

The point of the statement is that neither the case-c non-abelian hypothesis
`¬ IsAbelianSubgroup Q` nor the identification `Q₀ = {x ∈ Q | x² = 1}` is needed as a
hypothesis: `W ≠ ⊥` gives both (`not_abelian_of_W_ne_bot`,
`caseC_Q0sub_subgroupOf_iff_sq`). -/
theorem caseC_fpfXi {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1) :
    Work.Higman.FpfXi (Work.PSU3.StageA.caseC_xi hS hC4
      (Work.PSU3.StageA.caseC_W_ne_bot (Q := Q) hζ hζ1)) := by
  classical
  have hWne : Work.ThmF.W H t ≠ ⊥ := Work.PSU3.StageA.caseC_W_ne_bot (Q := Q) hζ hζ1
  show Work.Higman.FpfXi (Work.PSU3.StageA.caseC_xi hS hC4 hWne)
  -- `W ≠ ⊥` forces `Q` non-abelian and `Q₀` = the elements of `Q` of order `≤ 2`
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q :=
    not_abelian_of_W_ne_bot hS hC4 hWne
  have hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 :=
    caseC_Q0sub_subgroupOf_iff_sq hS hC4
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q := caseC_isSuzuki2Grp hS hC4 hnab hZ hWne
  -- the generator of `K = Ksub H t` exhibited by `caseC_gen`
  set k : G := ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) with hk
  have hkK : k ∈ Work.ThmF.Ksub H t := by
    rw [hk]; exact (caseC_gen hS hC4 hWne).2
  have hgen : Subgroup.zpowers k = Work.ThmF.Ksub H t := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hn]
      exact (Work.ThmF.Ksub H t).zpow_mem hkK n
    · intro hx
      have h1 : (⟨x, hx⟩ : ↥(Work.ThmF.Ksub H t)) ∈
          Subgroup.zpowers (caseC_gen hS hC4 hWne) := by
        rw [caseC_gen_spec hS hC4 hWne]; exact Subgroup.mem_top _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 := congrArg (fun y : ↥(Work.ThmF.Ksub H t) => (y : G)) hn
      simpa [hk] using h2
  -- the `FpfXi` structure for the conjugation action of `k` (public, in `caseC_W_semireg`)
  have hfpf : Work.Higman.FpfXi (cwConj Q k (Ksub_le_normalizer hS hkK)) :=
    fpfXi_conjQ hS hC4 hHig hWne hcard hSuz hkK hgen
  -- `caseC_xi` is exactly that conjugation action
  have hxi : Work.PSU3.StageA.caseC_xi hS hC4 hWne =
      cwConj Q k (Ksub_le_normalizer hS hkK) := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [show (((Work.PSU3.StageA.caseC_xi hS hC4 hWne) y : ↥Q) : G) =
        ((((Work.PSU3.StageA.caseC_xi hS hC4 hWne) ^ 1) y : ↥Q) : G) from by rw [pow_one]]
    rw [caseC_xi_pow_coe hS hC4 hWne 1 y, cwConj_apply, hk]
    simp only [pow_one]
  rwa [hxi]

end Work.PSU3.StageA

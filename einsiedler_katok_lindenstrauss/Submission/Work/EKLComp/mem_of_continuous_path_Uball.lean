import Mathlib
import Submission.Work.EKLComp.LeafDefs

/-!
# A continuous path into `U` that reaches `H` lies in `H`

Contract helper.  Let `U ≤ SL₃(ℝ)` be a subgroup, `H ≤ U` a subgroup, and suppose that the
open ball `Uball U R` of radius `R > 0` around the identity *inside* `U` is contained in `H`.
Then `H` contains a neighbourhood of the identity of `U`; since `U` is a topological group,
`H` is both open and closed in `U`.

Consequently, for any continuous path `σ : ℝ → SL₃(ℝ)` whose image lies in `U`, the preimage
`σ⁻¹(H)` is a clopen subset of the connected space `ℝ`.  As soon as `σ t ∈ H` for a single
`t`, the preimage is all of `ℝ`; in particular `σ s ∈ H` for every `s ≤ t` (indeed for every
`s`).

The statement is exactly the one requested; `hHU` and `hst` are not needed by the argument
(the conclusion holds for all `s : ℝ`).
-/

set_option linter.unusedVariables false

open Filter Topology

namespace Work.EKLComp

theorem mem_of_continuous_path_Uball (U H : Subgroup Work.EKLContract.SL3) (hHU : H ≤ U)
    (R : ℝ) (hR : 0 < R) (hball : Work.EKLComp.Uball U R ⊆ (H : Set Work.EKLContract.SL3))
    (σ : ℝ → Work.EKLContract.SL3) (hσ : Continuous σ)
    (hσU : ∀ lam : ℝ, σ lam ∈ U) {s t : ℝ} (hst : s ≤ t) (ht : σ t ∈ H) : σ s ∈ H := by
  -- View `H ≤ U` as a subgroup `H'` of the topological group `↥U`.
  let H' : Subgroup ↥U := H.subgroupOf U
  -- The entrywise ball `Uball U R`, read inside `↥U`, is an open neighbourhood of `1`.
  let B : Set ↥U := ⋂ (i : Fin 3) (j : Fin 3),
    {g : ↥U | |(((g : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < R}
  have hBopen : IsOpen B := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    have hcont : Continuous (fun g : ↥U =>
        (((g : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by fun_prop
    have hset : {g : ↥U | |(((g : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < R}
        = {g : ↥U | -R < (((g : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j}
          ∩ {g : ↥U | (((g : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j < R} := by
      ext g; simp [abs_lt]
    rw [hset]
    exact (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  -- `B` lies in `H'` because `Uball U R ⊆ H`.
  have hBsub : B ⊆ (H' : Set ↥U) := by
    intro g hg
    have hgmem : ∀ i j : Fin 3,
        |(((g : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < R := by
      simpa only [B, Set.mem_iInter, Set.mem_ofPred_eq] using hg
    exact hball ⟨g.2, hgmem⟩
  have h1B : (1 : ↥U) ∈ B := by
    simp only [B, Set.mem_iInter, Set.mem_ofPred_eq]
    intro i j
    rw [show (((1 : ↥U) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 from by
      rw [show ((1 : ↥U) : Work.EKLContract.SL3) = 1 from rfl,
        Matrix.SpecialLinearGroup.coe_one]]
    simp [hR]
  have hBmem : B ∈ 𝓝 (1 : ↥U) := hBopen.mem_nhds h1B
  -- Hence `H'` is a neighbourhood of `1`, so open — and therefore also closed.
  have hH'open : IsOpen (H' : Set ↥U) :=
    Subgroup.isOpen_of_mem_nhds H' (Filter.mem_of_superset hBmem hBsub)
  have hH'closed : IsClosed (H' : Set ↥U) := Subgroup.isClosed_of_isOpen H' hH'open
  -- The path `σ`, regarded as a path in `↥U`, is continuous.
  let f : ℝ → ↥U := fun lam => ⟨σ lam, hσU lam⟩
  have hf : Continuous f := Continuous.subtype_mk hσ hσU
  -- Its preimage of the clopen `H'` is clopen in the connected space `ℝ`.
  have hcl : IsClopen (f ⁻¹' (H' : Set ↥U)) :=
    ⟨hH'closed.preimage hf, hH'open.preimage hf⟩
  have htmem : t ∈ f ⁻¹' (H' : Set ↥U) := by
    show f t ∈ H'
    rw [Subgroup.mem_subgroupOf]
    exact ht
  have huniv : f ⁻¹' (H' : Set ↥U) = Set.univ := IsClopen.eq_univ hcl ⟨t, htmem⟩
  have hsmem : f s ∈ H' := by
    have : s ∈ f ⁻¹' (H' : Set ↥U) := by rw [huniv]; exact Set.mem_univ s
    exact this
  rw [Subgroup.mem_subgroupOf] at hsmem
  simpa [f] using hsmem

end Work.EKLComp

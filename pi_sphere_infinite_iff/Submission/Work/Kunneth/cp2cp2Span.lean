import Mathlib
import Submission.Work.Kunneth.cp2cp2Pairing
import Submission.Work.Kunneth.span_of_unimodular_pairing
import Submission.Work.Kunneth.kunneth_h4_cp2cp2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `H⁴(ℂP² × ℂP²;ℤ) = ℤ⟨a², ab, b²⟩`

The middle cohomology of `ℂP² × ℂP²` is free of rank `3` (`Work.Kunneth.kunneth_h4_cp2cp2`),
and the three classes `a², ab, b²` (`a = π₁^*h`, `b = π₂^*h`, `h` the hyperplane class of `ℂP²`)
have a *unimodular* matrix of intersection numbers with the fundamental class `c = [ℂP²] × [ℂP²]`
(`Work.Kunneth.cpa2_cpb2_pairing` and the vanishing entries of `Submission/Work/Kunneth/cp2cp2Pairing.lean`):

`⟨a² ⌣ a², c⟩ = 0`, `⟨a² ⌣ ab, c⟩ = 0`, `⟨a² ⌣ b², c⟩ = 1`, `⟨ab ⌣ ab, c⟩ = 1`, and the rest `0`.

By `Work.Kunneth.span_of_unimodular_pairing` this makes them a `ℤ`-basis, i.e. the spanning
statement `Work.Kunneth.cp2cp2_span_middle` — item 4 of the Künneth subproject.

## Main results

* `Work.Kunneth.beta` — the functional `x ↦ ⟨y ⌣ x, c⟩` as a `ℤ`-linear map;
* `Work.Kunneth.cp2cp2_intersectionMatrix` — the matrix of intersection numbers is the permutation
  matrix `!![0,0,1; 0,1,0; 1,0,0]`;
* `Work.Kunneth.cp2cp2_span_middle` — `span {a², ab, b²} = ⊤`;
* `Work.Kunneth.cp2cp2_basis` — the corresponding `Module.Basis (Fin 3) ℤ H⁴(ℂP² × ℂP²;ℤ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-! ## The intersection functional -/

/-- **The intersection functional** `x ↦ ⟨y ⌣ x, c⟩`, as a `ℤ`-linear map. -/
noncomputable def beta (y : ↥((SSetCochainComplex ℤ cpZ).homology 4)) :
    ↥((SSetCochainComplex ℤ cpZ).homology 4) →ₗ[ℤ] ℤ where
  toFun x := kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 y x) cpFund
  map_add' x x' := by
    have h1 : (cupH' ℤ cpZ 4 4 y) (x + x')
        = (cupH' ℤ cpZ 4 4 y) x + (cupH' ℤ cpZ 4 4 y) x' := map_add _ x x'
    rw [h1]
    exact (congrArg (fun f => f cpFund)
      (map_add (kronH ℤ cpZ 8) ((cupH' ℤ cpZ 4 4 y) x) ((cupH' ℤ cpZ 4 4 y) x'))).trans rfl
  map_smul' c x := by
    simp only [RingHom.id_apply]
    have h1 := (cupH' ℤ cpZ 4 4 y).map_smul' c x
    rw [RingHom.id_apply] at h1
    have h2 := (kronH ℤ cpZ 8).map_smul' c ((cupH' ℤ cpZ 4 4 y) x)
    rw [RingHom.id_apply] at h2
    exact (congrArg (fun z => kronH ℤ cpZ 8 z cpFund) h1).trans
      ((congrArg (fun f => f cpFund) h2).trans rfl)

/-- The intersection functional evaluated on a product. -/
lemma beta_apply (y x : ↥((SSetCochainComplex ℤ cpZ).homology 4)) :
    beta y x = kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 y x) cpFund := rfl

/-- **`⟨b² ⌣ a², c⟩ = 1`** (the last off-diagonal entry of the intersection matrix). -/
theorem cpb2_cpa2_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpb2 cpa2) cpFund = 1 := by
  rw [cup_comm_44 cpb2 cpa2]
  exact cpa2_cpb2_pairing

/-! ## The intersection matrix -/

/-- The ordered triple `(a², ab, b²)`. -/
abbrev cpTriple : Fin 3 → ↥((SSetCochainComplex ℤ cpZ).homology 4) := ![cpa2, cpab, cpb2]

/-- **The matrix of intersection numbers of `a², ab, b²`** with the fundamental class of
`ℂP² × ℂP²` is the permutation matrix `!![0,0,1; 0,1,0; 1,0,0]`; in particular it is unimodular. -/
theorem cp2cp2_intersectionMatrix :
    Matrix.of (fun i j : Fin 3 => beta (cpTriple i) (cpTriple j))
      = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cpTriple, beta, cpa2_cpa2_pairing, cpa2_cpab_pairing, cpa2_cpb2_pairing,
      cpab_cpa2_pairing, cpab_cpab_pairing, cpab_cpb2_pairing, cpb2_cpa2_pairing,
      cpb2_cpab_pairing, cpb2_cpb2_pairing]

/-- The intersection matrix is unimodular. -/
theorem cp2cp2_intersectionMatrix_isUnit :
    IsUnit (Matrix.det (Matrix.of (fun i j : Fin 3 => beta (cpTriple i) (cpTriple j)))) := by
  rw [cp2cp2_intersectionMatrix]
  have h : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ).det = -1 := by decide
  rw [h]
  norm_num

/-! ## The spanning statement -/

/-- **`H⁴(ℂP² × ℂP²;ℤ) = ℤ⟨a², ab, b²⟩`** — the three middle classes span the middle cohomology. -/
theorem cp2cp2_span_middle_range :
    Submodule.span ℤ (Set.range cpTriple) = ⊤ := by
  obtain ⟨e⟩ := (kunneth_h4_cp2cp2 :
    Nonempty ((cochainC ℤ cpZ).homology 4 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)))
  exact span_of_unimodular_pairing
    ((Pi.basisFun ℤ (Fin 3)).map e.toLinearEquiv.symm) cpTriple (fun i => beta (cpTriple i))
    cp2cp2_intersectionMatrix_isUnit

/-- **`H⁴(ℂP² × ℂP²;ℤ) = ℤ⟨a², ab, b²⟩`**, in the set spelling used by
`Work.Projective.CP2CP2Model.span_middle`. -/
theorem cp2cp2_span_middle :
    Submodule.span ℤ ({cpa2, cpab, cpb2} : Set ↥((SSetCochainComplex ℤ cpZ).homology 4)) = ⊤ := by
  have hset : ({cpa2, cpab, cpb2} : Set ↥((SSetCochainComplex ℤ cpZ).homology 4))
      = Set.range cpTriple := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h
      · exact ⟨0, by simp [cpTriple, h]⟩
      · exact ⟨1, by simp [cpTriple, h]⟩
      · exact ⟨2, by simp [cpTriple, h]⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [cpTriple]
  rw [hset]
  exact cp2cp2_span_middle_range

/-- **A `ℤ`-basis of `H⁴(ℂP² × ℂP²;ℤ)` on `a², ab, b²`.** -/
theorem cp2cp2_basis_nonempty :
    Nonempty (Module.Basis (Fin 3) ℤ ↥((SSetCochainComplex ℤ cpZ).homology 4)) := by
  obtain ⟨e⟩ := (kunneth_h4_cp2cp2 :
    Nonempty ((cochainC ℤ cpZ).homology 4 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)))
  exact ⟨(Pi.basisFun ℤ (Fin 3)).map e.toLinearEquiv.symm⟩

end

end Work.Kunneth

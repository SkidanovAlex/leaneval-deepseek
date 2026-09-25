import Mathlib
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup

/-!
# Route B, lemma `(L1)`(b): a class killed on `V` is killed on an open subgroup above `V`

This is the *re-homed* copy of `Submission/Work/NUV2/LC/RouteB/res_eq_zero_of_isOpen_le.lean`
whose module does not build (it imported the non-existent `NK.NUV2.LC.surjTwo_of_fc`).  The
statement and the proof are unchanged; only the import list is fixed.

Lemma `(L1)`(b) of the route-B design (`Submission/Work/NUV2/LC/RouteB/decompContainment_B.lean`):
for closed subgroups `V ≤ W ≤ Gal(K'/K)` with `W` **open**, a class `y : H²(W, Z/p)` whose
restriction to `V` vanishes already restricts to `0` on some **open** `V ≤ W' ≤ W`.

The proof is level-wise: write `y = ofLevel L₀ a₀` and read the hypothesis through the computation
rule `res_ofLevel`; by the killing criterion `H2Profinite_ofLevel_eq_zero_iff` there is `L₁ ≥ L₀`
with `H2.map (levelInclHom (V ≤ W) L₁) a₁ = 0`.  Take `W' = V ⊔ (W ⊓ Gal(K'/L₁))`; then
`W' ≤ V ⊔ Gal(K'/L₁)`, so `levelInclHom (V ≤ W') L₁` is surjective hence `H2.map` of it injective,
and the composition identity `levelInclHom (V ≤ W) = levelInclHom (W' ≤ W) ∘ levelInclHom (V ≤ W')`
forces the vanishing of `H2.map (levelInclHom (W' ≤ W) L₁) a₁`.

This is the step which lets Route B pass from an arithmetic statement at an *open* level
(Albert–Brauer–Hasse–Noether) down to the closed subgroup `V` whose `H²(V, Z/p)` is counted.
-/

open CategoryTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The level-group inclusion is surjective as soon as `U ≤ V · Gal(K'/L)`.** -/
lemma levelInclHom_surjective_of_le_sup_v2 {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (hU : U ≤ V ⊔ L.fixingSubgroup) :
    Function.Surjective (NK.BrauerHasse.levelInclHom h L) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨v, hv, n, hn, hvn⟩ := Subgroup.mem_sup_of_normal_right.mp (hU u.2)
    refine ⟨QuotientGroup.mk ⟨v, hv⟩, ?_⟩
    rw [NK.BrauerHasse.levelInclHom, QuotientGroup.map_mk]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    show v⁻¹ * (u : Gal(K'/K)) ∈ L.fixingSubgroup
    rw [← hvn]
    have h2 : v⁻¹ * (v * n) = n := by group
    rw [h2]
    exact hn

/-- **Route-B lemma `(L1)`(b).**  If `W` is an open subgroup of `Gal(K'/K)`, `V ≤ W` and
`y : H²(W, Z/p)` restricts to `0` on `V`, then there is an open `W'` with `V ≤ W' ≤ W` such that
`y` restricts to `0` on `W'`. -/
theorem exists_isOpen_le_res_eq_zero_v2 (p : ℕ) [NeZero p] {V W : Subgroup Gal(K'/K)}
    (hW : IsOpen (W : Set Gal(K'/K))) (hVW : V ≤ W)
    (y : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p W)
    (hy : NK.LocalDecomposition.H2Profinite.res p hVW y = 0) :
    ∃ (W' : Subgroup Gal(K'/K)) (h₁ : V ≤ W') (h₂ : W' ≤ W),
      IsOpen (W' : Set Gal(K'/K)) ∧ NK.LocalDecomposition.H2Profinite.res p h₂ y = 0 := by
  obtain ⟨L₀, a₀, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective y
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel] at hy
  obtain ⟨L₁, hL, hz⟩ :=
    (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p) (U := V)
      ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom hVW L₀)) a₀)).mp hy
  rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p hVW hL a₀] at hz
  set W' : Subgroup Gal(K'/K) := V ⊔ (W ⊓ L₁.fixingSubgroup) with hW'def
  have h₁ : V ≤ W' := le_sup_left
  have h₂ : W' ≤ W := sup_le hVW inf_le_left
  have hW'open : IsOpen (W' : Set Gal(K'/K)) := by
    refine Subgroup.isOpen_of_mem_nhds W' (g := 1) ?_
    exact Filter.mem_of_superset
      ((hW.inter (IntermediateField.fixingSubgroup_isOpen (L₁ : IntermediateField K K'))).mem_nhds
        (by simp : (1 : Gal(K'/K)) ∈ (W ⊓ L₁.fixingSubgroup : Subgroup Gal(K'/K))))
      (fun x hx => (le_sup_right : W ⊓ L₁.fixingSubgroup ≤ W') hx)
  refine ⟨W', h₁, h₂, hW'open, ?_⟩
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel]
  refine (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p) (U := W')
    ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom h₂ L₀)) a₀)).mpr ⟨L₁, hL, ?_⟩
  rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p h₂ hL a₀]
  have hsurj : Function.Surjective (NK.BrauerHasse.levelInclHom h₁ L₁) :=
    levelInclHom_surjective_of_le_sup_v2 h₁ L₁
      (sup_le le_sup_left (le_trans inf_le_right le_sup_right))
  have hbij : Function.Bijective (NK.BrauerHasse.levelInclHom h₁ L₁) :=
    ⟨NK.HassePrinciple.levelInclHom_injective h₁ L₁, hsurj⟩
  have hinj := NK.HassePrinciple.h2Map_injective_of_bijective
    (p := p) (NK.BrauerHasse.levelInclHom h₁ L₁) hbij
  have h1 : NK.BrauerHasse.levelInclHom hVW L₁ =
      NK.BrauerHasse.levelInclHom (h₁.trans h₂ : V ≤ W) L₁ :=
    congrArg (fun hh => NK.BrauerHasse.levelInclHom hh L₁)
      (Subsingleton.elim hVW (h₁.trans h₂ : V ≤ W))
  have h2 : (NK.BrauerHasse.levelInclHom h₂ L₁).comp
        (NK.BrauerHasse.levelInclHom h₁ L₁) =
      NK.BrauerHasse.levelInclHom (h₁.trans h₂ : V ≤ W) L₁ :=
    NK.NUV2.LC.OddTwist.levelInclHom_comp p h₁ h₂ L₁
  have hcomp : (NK.BrauerHasse.H2.map (p := p) (NK.BrauerHasse.levelInclHom hVW L₁)).hom
        (NK.BrauerHasse.levelMap p (U := W) hL a₀) =
      (NK.BrauerHasse.H2.map (p := p) (NK.BrauerHasse.levelInclHom h₁ L₁)).hom
        ((NK.BrauerHasse.H2.map (p := p) (NK.BrauerHasse.levelInclHom h₂ L₁)).hom
          (NK.BrauerHasse.levelMap p (U := W) hL a₀)) := by
    rw [h1, ← h2, NK.BrauerHasse.H2.map_comp]
    rfl
  refine hinj (by simpa using hcomp.symm.trans hz)

end NK.NUV2.LC.RouteB

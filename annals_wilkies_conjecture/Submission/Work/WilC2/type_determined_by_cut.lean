/-
  Area C2 (WilC2): `type_determined_by_cut`.

  In an o-minimal structure the *type* of a point over a parameter set is determined by the
  *cut* the point defines in that set.  Concretely, for a model `M ⊨ TR`, a `dcl`-closed set of
  parameters `A` (`Dcl A ⊆ A`) and points `a, b ∈ M` which define the same cut in `A`
  (`∀ c ∈ A, c < a ↔ c < b` and `a ∈ A ↔ b ∈ A`), every `A`-definable subset of `M` either
  contains both or neither.

  Proof.  We treat the fibre `X = {y | φ.Realize (v, y)}` of the parametric `LRc`-formula `φ`
  over the parameter tuple `v ∈ Aⁿ` (every `A`-definable subset of the line arises this way).
  Suppose `u < w`, `u ∈ X`, `w ∉ X`, `u ∉ A` and `A ∩ (u, w) = ∅`; we derive a contradiction
  ("`Lright`").  Let `s` be a finite cover of `X` by `OrdConnected` sets, given by
  `C2_models_ominimal_proved`.  The `A`-definable sets

  * `maxSet X` — the points of `X` which are the maximum of their component, and
  * `supSet X` — the points outside `X` which are the supremum of a component of `X`,

  are then finite (at most one point per piece of the cover), hence contained in `Dcl A = A`
  (`finite_definable_singleton`).  Now let `J = comp X u` be the component of `u` in `X`
  (`(A ∪ {u})`-definable) and `β = sup J`, which exists in `M` because `M` realises the
  sup-existence schema (`sup_exists_dcl`).  Since `w ∉ X` and `J` is convex below `w`, `u ≤ β ≤ w`.
  If `β > u` then `β ∈ X` (whence `β ∈ maxSet X ⊆ A`) or `β ∉ X` (whence `β ∈ supSet X ⊆ A`);
  either way `β ∈ A ∩ (u, w]`, contradicting the cut.  Otherwise `u` is the maximum of its
  component, `u ∈ maxSet X ⊆ A`, contradicting `u ∉ A`.

  The reverse inclusion is the same argument applied to the complement `Xᶜ` (which is
  `A`-definable as well), and the case `w < u` is the argument applied with the roles of `u`
  and `w` exchanged.

  The four ingredient lemmas are the modules `finite_definable_singleton`,
  `definable_maxSet_supSet`, `finite_maxSet_supSet` and `definable_comp` of this directory.
-/
import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC4.sup_exists_dcl
import Submission.Work.WilC2.CutDefs
import Submission.Work.WilC2.finite_definable_singleton
import Submission.Work.WilC2.definable_maxSet_supSet
import Submission.Work.WilC2.finite_maxSet_supSet
import Submission.Work.WilC2.definable_comp

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

theorem type_determined_by_cut
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] {A : Set M} (hA : Dcl A ⊆ A) {a b : M}
    (hcut : (∀ c ∈ A, (c < a ↔ c < b)) ∧ (a ∈ A ↔ b ∈ A))
    {n : ℕ} (φ : ParamFormula n) (v : Fin n → M) (hv : ∀ i, v i ∈ A) :
    (φ.Realize (Sum.elim v (fun _ => a)) ↔ φ.Realize (Sum.elim v (fun _ => b))) := by
  classical
  -- ## The fibre of `φ` over `v`, an `A`-definable subset of the line
  set X : Set M := {y | φ.Realize (Sum.elim v (fun _ => y))} with hXdef
  have hmemX : ∀ y : M, y ∈ X ↔ φ.Realize (Sum.elim v (fun _ => y)) := fun y => by
    simp only [hXdef, Set.mem_ofPred_eq]
  have hXA : A.Definable₁ LRc X := by
    have h := definable_of_param_formula (L := LRc) (A := A) v hv φ
    have hset : {u : Fin 1 → M | u 0 ∈ X} = {u : Fin 1 → M | φ.Realize (Sum.elim v u)} := by
      ext u
      simp only [Set.mem_setOf_eq]
      rw [hmemX]
      have : (fun _ : Fin 1 => u 0) = u := funext fun i => by rw [Subsingleton.elim i 0]
      rw [this]
    rw [Set.Definable₁, hset]
    exact h
  -- ## O-minimality of `M`
  have hOM : WilkiesDesign.CG.OMinModels := C2_models_ominimal_proved hR hC0 hUF
  -- ## The key step: an `X`-point below a non-`X`-point with no `A`-point in between
  have Lright : ∀ {Y : Set M}, A.Definable₁ LRc Y → ∀ {u w : M}, u < w → u ∉ A → w ∉ A →
      u ∈ Y → w ∉ Y → (∀ c ∈ A, ¬(u < c ∧ c < w)) → False := by
    intro Y hYA u w huw huA hwA huY hwY hgap
    -- a finite cover of `Y` by order-convex pieces
    have hYuniv : (Set.univ : Set M).Definable LRc {v : Fin 1 → M | v 0 ∈ Y} :=
      Set.Definable.mono hYA (Set.subset_univ A)
    obtain ⟨s, hsord, hscov⟩ :=
      hOM M {v : Fin 1 → M | v 0 ∈ Y} hYuniv
    have hYcov : Y = ⋃₀ (s : Set (Set M)) := by
      ext y
      have h := Set.ext_iff.mp hscov (fun _ : Fin 1 => y)
      simpa using h
    -- the endpoint sets are finite and `A`-definable, hence contained in `A`
    have hfin := finite_maxSet_supSet hsord hYcov
    have hdef := definable_maxSet_supSet ‹M ⊨ TR› hYA
    have hmaxA : maxSet Y ⊆ A := fun e he =>
      hA (mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hdef.1 hfin.1 e he))
    have hsupA : supSet Y ⊆ A := fun e he =>
      hA (mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hdef.2 hfin.2 e he))
    -- the component of `u` in `Y` and its supremum
    have hcompdef : (A ∪ {u}).Definable₁ LRc (comp Y u) := definable_comp ‹M ⊨ TR› hYA
    have hJne : (comp Y u).Nonempty := ⟨u, mem_comp_self huY⟩
    have hub : ∀ x ∈ comp Y u, x ≤ w := by
      intro x hx
      by_contra hlt
      rw [not_le] at hlt
      have hwcomp : w ∈ comp Y u :=
        (comp_ordConnected Y u).out (mem_comp_self huY) hx ⟨huw.le, hlt.le⟩
      exact hwY (comp_subset Y u hwcomp)
    obtain ⟨β, hβLUB, _⟩ := Work.WilC4.sup_exists_dcl ‹M ⊨ TR› hcompdef hJne ⟨w, hub⟩
    have hβle : β ≤ w := hβLUB.2 (mem_upperBounds.mpr hub)
    -- case analysis on whether the component of `u` extends strictly above `u`
    by_cases hcase : ∃ x, x ∈ comp Y u ∧ u < x
    · obtain ⟨x, hx, hux⟩ := hcase
      have huβ : u < β := lt_of_lt_of_le hux (mem_upperBounds.mp hβLUB.1 x hx)
      have hβA : β ∈ A := by
        by_cases hβY : β ∈ Y
        · exact hmaxA (mem_maxSet_of_isLUB_comp huY hβLUB hβY)
        · exact hsupA (mem_supSet_of_isLUB_comp huY hβLUB hβY huβ)
      rcases lt_or_eq_of_le hβle with hβlt | hβeq
      · exact hgap β hβA ⟨huβ, hβlt⟩
      · exact hwA (hβeq ▸ hβA)
    · push_neg at hcase
      exact huA (hmaxA (mem_maxSet_of_max_comp huY (fun x hx => hcase x hx)))
  -- ## The type is determined by the cut
  have key : ∀ u w : M, (∀ c ∈ A, (c < u ↔ c < w)) → (u ∈ A ↔ w ∈ A) →
      (u ∈ X ↔ w ∈ X) := by
    intro u w hcw hAmem
    by_cases huw : u = w
    · subst huw; tauto
    -- at most one of `u`, `w` lies in `A`
    have hnotboth : ¬(u ∈ A ∧ w ∈ A) := by
      rintro ⟨huA, hwA⟩
      have h1 : ¬(u < w) := fun h => absurd ((hcw u huA).mpr h) (lt_irrefl u)
      have h2 : ¬(w < u) := fun h => absurd ((hcw w hwA).mp h) (lt_irrefl w)
      exact huw (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
    have huA : u ∉ A := fun h => hnotboth ⟨h, hAmem.mp h⟩
    have hwA : w ∉ A := fun h => hnotboth ⟨hAmem.mpr h, h⟩
    -- the complement is `A`-definable too
    have hXAc : A.Definable₁ LRc (Xᶜ) := by
      have hset : {v : Fin 1 → M | v 0 ∈ Xᶜ} = {v : Fin 1 → M | v 0 ∈ X}ᶜ := by
        ext v
        simp
      rw [Set.Definable₁, hset]
      exact hXA.compl
    -- the gap condition
    have gap_of : ∀ {p q : M}, (∀ c ∈ A, (c < p ↔ c < q)) →
        ∀ c ∈ A, ¬(p < c ∧ c < q) := by
      intro p q hpq c hcA
      rintro ⟨hpc, hcq⟩
      exact absurd hpc (not_lt.mpr ((hpq c hcA).mpr hcq).le)
    have g₁ : ∀ c ∈ A, ¬(u < c ∧ c < w) := gap_of hcw
    have g₂ : ∀ c ∈ A, ¬(w < c ∧ c < u) := gap_of (fun c hcA => (hcw c hcA).symm)
    rcases lt_or_gt_of_ne huw with huw' | hwu'
    · -- `u < w`
      constructor
      · intro huX
        by_contra hwX
        exact Lright hXA huw' huA hwA huX hwX g₁
      · intro hwX
        by_contra huX
        exact Lright hXAc huw' huA hwA (by simpa using huX)
          (by simpa using hwX) g₁
    · -- `w < u`
      constructor
      · intro huX
        by_contra hwX
        exact Lright hXAc hwu' hwA huA (by simpa using hwX)
          (by simpa using huX) g₂
      · intro hwX
        by_contra huX
        exact Lright hXA hwu' hwA huA hwX huX g₂
  exact (hmemX a).symm.trans ((key a b hcut.1 hcut.2).trans (hmemX b))

end Work.WilC2

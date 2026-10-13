/-
  Area C5 (WilC5): `cut_determines_type_of_omin`.

  This is the form of "o-minimality ⇒ the type of a point over a `dcl`-closed parameter set is
  determined by the cut it defines" that C5 uses: the o-minimality input is supplied *directly*
  as the hypothesis `hOM : OMinModels` (rather than being derived from `hR`/`hC0`/`hUF` as in
  `Work.WilC2.type_determined_by_cut`), so that callers who already hold `hOM` — e.g. from
  `Work.WilC4.unifFinite_of_omin` or from a transfer argument — need not reprove the syntax
  bridge.

  The proof is the argument of `Work.WilC2.type_determined_by_cut`, which in fact only ever uses
  the `hOM` component of its hypotheses: reduce to the fibre `X = {y | φ.Realize (v, y)}` of the
  parametric `LRc`-formula `φ`, and rule out a pair `u < w` with `u ∈ X`, `w ∉ X`, both outside
  `A` and with no point of `A` strictly between them ("`Lright`"), using a finite cover of `X` by
  order-convex pieces together with the finiteness of the endpoint sets `maxSet X`, `supSet X`
  and the existence of the supremum of `comp X u`.  The complement and the reversed order give
  the remaining cases.
-/
import Mathlib
import Submission.Work.WilC2.type_determined_by_cut

noncomputable section
open Classical FirstOrder FirstOrder.Language
open Work.WilC2

namespace Work.WilC5

open WilkiesDesign.CG (LR LRc TR rexpL)

theorem cut_determines_type_of_omin (hOM : WilkiesDesign.CG.OMinModels) {M : Type}
    [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] {A : Set M} (hA : Work.WilC2.Dcl A ⊆ A) {a b : M}
    (hcut : (∀ c ∈ A, (c < a ↔ c < b)) ∧ (a ∈ A ↔ b ∈ A))
    {n : ℕ} (φ : Work.WilC2.ParamFormula n) (v : Fin n → M) (hv : ∀ i, v i ∈ A) :
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

end Work.WilC5

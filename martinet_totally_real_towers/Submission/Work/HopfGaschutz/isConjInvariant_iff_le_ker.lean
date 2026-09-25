import Mathlib
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.Setup

/-!
# `Work.HopfGaschutz.isConjInvariant_iff_le_ker`

A `1`-cochain `f` on the relation kernel `K = presKernel gen` of a presentation
`1 → K → FreeGroup α → Q → 1` is invariant under the conjugation action of `FreeGroup α`
precisely when it kills the **relation-Frattini subgroup** `K ^ 2 [K, F]`:

`(∀ g n, f ((presExt gen).conj g n) = f n) ↔ relFrattiniIn 2 K ≤ f.ker`.

Note that the target of `f` is `Multiplicative (ZMod 2)`, an elementary abelian group of
exponent `2`; hence `f` kills every square `k ^ 2` (`k ∈ K`) automatically, and the content of
the equivalence is the commutator part `[K, F] ≤ ker f`:

* `⇐` : `conj g n = n · [n⁻¹, g]`, and `[n⁻¹, g] ∈ K ^ 2 [K, F] ⊆ ker f`;
* `⇒` : `f` being invariant gives `f (n · c) = f n` with `c = [n⁻¹, g]`, hence `f c = 1`, so
  `[K, F] ≤ ker f`; the squares are killed because `x ^ 2 = 1` in `Multiplicative (ZMod 2)`.
-/


namespace Work.HopfGaschutz

open Work.ConCohomology

open scoped commutatorElement

section Prelim

variable {α Q : Type*} [Group Q] (gen : α → Q)

/-- The element `⁅n⁻¹, g⁆` of the presentation kernel `K = presKernel gen`: the "cocycle defect"
of the conjugation by `g` on the element `n`, i.e. the unique `c ∈ K` with `g n g⁻¹ = n · c`.

It lies in `⁅K, ⊤⁆ ≤ K^2[K,F]`, which is the subgroup that separates the conjugation-invariant
`1`-cochains. -/
noncomputable def conjDelta (g : FreeGroup α) (n : ↥(presKernel gen)) : ↥(presKernel gen) :=
  ⟨⁅(n : FreeGroup α)⁻¹, g⁆, by
    have hcommK : ⁅presKernel gen, ⊤⁆ ≤ presKernel gen :=
      (le_sup_right : ⁅presKernel gen, ⊤⁆ ≤
        pPower 2 (presKernel gen) ⊔ ⁅presKernel gen, ⊤⁆).trans
        (relFrattini_le 2 (presKernel gen))
    exact hcommK (Subgroup.subset_closure ⟨(n : FreeGroup α)⁻¹,
      (presKernel gen).inv_mem n.2, g, trivial, rfl⟩)⟩

@[simp]
lemma conjDelta_val (g : FreeGroup α) (n : ↥(presKernel gen)) :
    ((conjDelta gen g n : ↥(presKernel gen)) : FreeGroup α) = ⁅(n : FreeGroup α)⁻¹, g⁆ := rfl

/-- Conjugation on the kernel is multiplication by the element `⁅n⁻¹, g⁆`: `g n g⁻¹ = n · c`. -/
lemma conj_eq_mul_conjDelta (g : FreeGroup α) (n : ↥(presKernel gen)) :
    (presExt gen).conj g n = n * conjDelta gen g n := by
  have h : (((presExt gen).conj g n : ↥(presKernel gen)) : FreeGroup α)
      = g * (n : FreeGroup α) * g⁻¹ :=
    GroupExt.i_conj (presExt gen) g n
  apply Subtype.ext
  rw [h, Subgroup.coe_mul]
  show g * (n : FreeGroup α) * g⁻¹ = (n : FreeGroup α) * ⁅(n : FreeGroup α)⁻¹, g⁆
  rw [commutatorElement_def]
  group

/-- `Multiplicative (ZMod 2)` is an elementary abelian group of exponent `2`. -/
lemma sq_eq_one_zmodTwo (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
  fin_cases x <;> decide

/-- The defect `⁅n⁻¹, g⁆` lies in the relation-Frattini subgroup `K^2[K,F]`. -/
lemma conjDelta_mem_relFrattiniIn (g : FreeGroup α) (n : ↥(presKernel gen)) :
    conjDelta gen g n ∈ relFrattiniIn 2 (presKernel gen) := by
  rw [mem_relFrattiniIn]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨(n : FreeGroup α)⁻¹,
    (presKernel gen).inv_mem n.2, g, trivial, rfl⟩)

/-- A conjugation-invariant `1`-cochain kills the conjugation defect. -/
lemma conjDelta_eq_one_of_conjInvariant
    (f : ↥(presKernel gen) →* Multiplicative (ZMod 2))
    (hinv : ∀ (g : FreeGroup α) (n : ↥(presKernel gen)),
      f ((presExt gen).conj g n) = f n)
    (g : FreeGroup α) (n : ↥(presKernel gen)) : f (conjDelta gen g n) = 1 := by
  have h := hinv g n
  rw [conj_eq_mul_conjDelta gen g n, map_mul] at h
  have h' : f n * f (conjDelta gen g n) = f n * 1 := by rw [h, mul_one]
  exact mul_left_cancel h'

end Prelim

theorem isConjInvariant_iff_le_ker {α Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
    (gen : α → Q) (f : ↥(Work.HopfGaschutz.presKernel gen) →* Multiplicative (ZMod 2)) :
    (∀ g : FreeGroup α, ∀ n : ↥(Work.HopfGaschutz.presKernel gen),
        f ((Work.HopfGaschutz.presExt gen).conj g n) = f n)
      ↔ Work.HopfGaschutz.relFrattiniIn 2 (Work.HopfGaschutz.presKernel gen) ≤ f.ker := by
  constructor
  · intro hinv
    have hmap : Work.HopfGaschutz.relFrattini 2 (Work.HopfGaschutz.presKernel gen) ≤
        (f.ker).map (Work.HopfGaschutz.presKernel gen).subtype := by
      refine sup_le ?_ ?_
      · rw [Work.HopfGaschutz.pPower, Subgroup.closure_le]
        rintro x ⟨k, hk, rfl⟩
        refine Subgroup.mem_map.mpr
          ⟨⟨k ^ 2, (Work.HopfGaschutz.presKernel gen).pow_mem hk 2⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker]
        have heq : (⟨k ^ 2, (Work.HopfGaschutz.presKernel gen).pow_mem hk 2⟩ :
              ↥(Work.HopfGaschutz.presKernel gen))
            = (⟨k, hk⟩ : ↥(Work.HopfGaschutz.presKernel gen)) ^ 2 := Subtype.ext rfl
        rw [heq, map_pow, sq_eq_one_zmodTwo]
      · rw [Subgroup.commutator_le]
        intro a ha b _
        have hmem : ⁅a, b⁆ ∈ Work.HopfGaschutz.presKernel gen := by
          have h2 : b * a⁻¹ * b⁻¹ ∈ Work.HopfGaschutz.presKernel gen :=
            Subgroup.Normal.conj_mem (Work.HopfGaschutz.presKernel_normal gen) a⁻¹
              ((Work.HopfGaschutz.presKernel gen).inv_mem ha) b
          have h3 : a * (b * a⁻¹ * b⁻¹) ∈ Work.HopfGaschutz.presKernel gen :=
            (Work.HopfGaschutz.presKernel gen).mul_mem ha h2
          have heq : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
            rw [commutatorElement_def]; group
          rwa [heq]
        refine Subgroup.mem_map.mpr ⟨⟨⁅a, b⁆, hmem⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker]
        have hkill := conjDelta_eq_one_of_conjInvariant gen f hinv b
          ⟨a⁻¹, (Work.HopfGaschutz.presKernel gen).inv_mem ha⟩
        have heq : (⟨⁅a, b⁆, hmem⟩ : ↥(Work.HopfGaschutz.presKernel gen))
            = conjDelta gen b ⟨a⁻¹, (Work.HopfGaschutz.presKernel gen).inv_mem ha⟩ := by
          apply Subtype.ext
          rw [conjDelta_val]
          show ⁅a, b⁆ = ⁅(a⁻¹)⁻¹, b⁆
          rw [inv_inv]
        rw [heq]
        exact hkill
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hmap hx)
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact MonoidHom.mem_ker.mp hy
  · intro hle g n
    have hone : f (conjDelta gen g n) = 1 :=
      MonoidHom.mem_ker.mp (hle (conjDelta_mem_relFrattiniIn gen g n))
    rw [conj_eq_mul_conjDelta gen g n, map_mul, hone, mul_one]

end Work.HopfGaschutz

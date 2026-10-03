/-
# The algebraic FKS structure theorem for the kernel of `⟨X | u ^ l⟩ →* ⟨X | u⟩`

`Work.ORLocInd.FKSKernelStructure P` states that the kernel of the canonical map
`fksQuotientHom P : G →* ⟨X | u⟩` is the free product of `|⟨X | u⟩|` copies of `ℤ / l`
(Fischer--Karrass--Solitar 1972, Theorem 1; the free-product structure is already implicit in
Cohen--Lyndon 1963; see also Howie 2000, reference [4]).

The proof has three steps, for a root presentation `P` (`G ≅ ⟨X | u ^ l⟩`, `u` not a proper power)
with `F = F(X)` the free group on the generating set of `P`:

1. `ker (fksQuotientHom P) ≃* ⟪u⟫_F ⧸ ⟪u ^ l⟫_F`
   (`Submission.Work.ORLocInd.FKSKernel.kerFksQuotientHomEquiv`): the kernel of the quotient map of
   presented groups, computed by the second isomorphism theorem.
2. `⟪u⟫_F ⧸ ⟪u ^ l⟫_F ≃* FreeGroup (F ⧸ ⟪u⟫_F) ⧸ ⟪{of q ^ l}⟫` (this file, from the
   **Cohen--Lyndon basis theorem**, `Submission.Work.ORLocInd.FKSKernel.cohenLyndonBasis`): by
   Cohen--Lyndon, `⟪u⟫_F` is *freely generated* by the conjugates `s u s⁻¹`, one for each coset `s`
   of `⟪u⟫_F` in `F`; moreover every conjugate of `u` is conjugate *by an element of `⟪u⟫_F`* to one
   of these basis elements, so that `⟪u ^ l⟫_F ∩ ⟪u⟫_F` is generated inside `⟪u⟫_F` by the `l`-th
   powers of the basis elements (`nclPow_subgroupOf_eq`, `quotientEquiv` below).
3. `FreeGroup Q ⧸ ⟪{of q ^ l}⟫ ≃* ∗_{q ∈ Q} ℤ/l`
   (`Submission.Work.ORLocInd.FKSKernel.freeGroupQuotientPowCoprodI`): the free product of cyclic
   groups is the free group on the generators modulo the `l`-th powers.

`l = 1` is the degenerate case: both sides of step 3 are trivial and the statement `ker = ⊥` holds
because `⟨X | u⟩ = ⟨X | u ^ 1⟩`.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSKernelTree
import Submission.Work.ORLocInd.FKSKernel.freeGroupQuotientPowCoprodI
import Submission.Work.ORLocInd.FKSKernel.kerFksQuotientHomEquiv
import Submission.Work.ORLocInd.FKSKernel.cohenLyndonBasisFreeGenerator
import Submission.Work.ORLocInd.FKSKernel.cohenLyndonBasis

universe u

namespace Work.ORLocInd.FKSKernel

open Work.ORLocInd

variable {G : Type u} [Group G]

/-- The normal closure of the root `u` in the free group `F(X)`. -/
abbrev nclU (P : RootPresentation G) : Subgroup (FreeGroup P.α) :=
  Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))

/-- The normal closure of the relator `u ^ l` in the free group `F(X)`. -/
abbrev nclPow (P : RootPresentation G) : Subgroup (FreeGroup P.α) :=
  Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))

theorem nclPow_le_nclU (P : RootPresentation G) : nclPow P ≤ nclU P := by
  rw [nclPow, nclU]
  refine Subgroup.normalClosure_le_normal
    (N := Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton P.u)) P.l

/-- **Cohen--Lyndon, used form.**  Every conjugate of `u ^ l` (`u` not a proper power) is conjugate,
by an element of `⟪u⟫_F`, to the `l`-th power of a basis element `e (of q)` of the Cohen--Lyndon
basis of `⟪u⟫_F`.

Indeed `c u c⁻¹` is conjugate to the basis element lying in the coset of `c` (the conjugating
element being in `⟪u⟫`). -/
theorem conj_pow_mem_map (P : RootPresentation G)
    (e : FreeGroup (FreeGroup P.α ⧸ nclU P) ≃* ↥(nclU P))
    (he : ∀ q : FreeGroup P.α ⧸ nclU P,
      ∃ s : FreeGroup P.α, QuotientGroup.mk s = q ∧
        ((e (FreeGroup.of q) : ↥(nclU P)) : FreeGroup P.α) = s * P.u * s⁻¹)
    (c : FreeGroup P.α) :
    c * P.u ^ P.l * c⁻¹ ∈
      (Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
        e (FreeGroup.of q) ^ P.l)).map (nclU P).subtype := by
  obtain ⟨s, hs, hsq⟩ := he (QuotientGroup.mk c)
  have hm : s⁻¹ * c ∈ nclU P := by
    rw [← QuotientGroup.eq]
    exact hs
  set m : nclU P := ⟨s⁻¹ * c, hm⟩ with hmdef
  have hmcoe : ((m : nclU P) : FreeGroup P.α) = s⁻¹ * c := rfl
  have hminv : (((m⁻¹ : nclU P)) : FreeGroup P.α) = (s⁻¹ * c)⁻¹ := by
    rw [Subgroup.coe_inv, hmcoe]
  set v : nclU P := ⟨c * P.u * c⁻¹,
    Subgroup.Normal.conj_mem (Subgroup.normalClosure_normal) P.u
      (Subgroup.subset_normalClosure (Set.mem_singleton P.u)) c⟩ with hvdef
  have hvcoe : (v : FreeGroup P.α) = c * P.u * c⁻¹ := rfl
  set w : nclU P := ⟨c * ((m⁻¹ : nclU P) : FreeGroup P.α) * c⁻¹,
    Subgroup.Normal.conj_mem (Subgroup.normalClosure_normal) (((m⁻¹ : nclU P)) : FreeGroup P.α)
      (Subgroup.inv_mem _ m.2) c⟩ with hwdef
  have hwcoe : (w : FreeGroup P.α) = c * (((m⁻¹ : nclU P)) : FreeGroup P.α) * c⁻¹ := rfl
  have hg : e (FreeGroup.of (QuotientGroup.mk c)) = w * v * w⁻¹ := by
    apply Subtype.ext
    show ((e (FreeGroup.of (QuotientGroup.mk c)) : ↥(nclU P)) : FreeGroup P.α) =
      (w : FreeGroup P.α) * (v : FreeGroup P.α) * (w : FreeGroup P.α)⁻¹
    rw [hsq, hwcoe, hminv, hvcoe]
    group
  have hmemU : c * P.u ^ P.l * c⁻¹ ∈ nclU P :=
    Subgroup.Normal.conj_mem (Subgroup.normalClosure_normal) (P.u ^ P.l)
      (pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton P.u)) P.l) c
  have hvp : v ^ P.l = (⟨c * P.u ^ P.l * c⁻¹, hmemU⟩ : nclU P) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show (v : FreeGroup P.α) ^ P.l = c * P.u ^ P.l * c⁻¹
    rw [hvcoe, conj_pow]
  have hgen : e (FreeGroup.of (QuotientGroup.mk c)) ^ P.l ∈
      Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
        e (FreeGroup.of q) ^ P.l) :=
    Subgroup.subset_normalClosure ⟨QuotientGroup.mk c, rfl⟩
  have hconj : e (FreeGroup.of (QuotientGroup.mk c)) ^ P.l = w * v ^ P.l * w⁻¹ := by
    rw [hg, conj_pow]
  have hmem : v ^ P.l ∈ Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
        e (FreeGroup.of q) ^ P.l) := by
    have hthis : v ^ P.l = w⁻¹ * e (FreeGroup.of (QuotientGroup.mk c)) ^ P.l * w := by
      rw [hconj]
      group
    rw [hthis]
    simpa using Subgroup.Normal.conj_mem (Subgroup.normalClosure_normal)
      (e (FreeGroup.of (QuotientGroup.mk c)) ^ P.l) hgen w⁻¹
  exact Subgroup.mem_map.mpr ⟨v ^ P.l, hmem, by rw [hvp]; rfl⟩

/-- **The normal closure of `u ^ l` inside `⟪u⟫`.**  If `e : FreeGroup Q ≃* ⟪u⟫_F` is a
Cohen--Lyndon basis, then `⟪u ^ l⟫_F ∩ ⟪u⟫_F` is the subgroup generated inside `⟪u⟫_F` by the
`l`-th powers of the basis elements.

(The two subgroups are *not* equal inside `F`; what makes them equal inside `⟪u⟫_F` is exactly the
"by an element of `⟪u⟫`" part of the Cohen--Lyndon statement, used in `conj_pow_mem_map`.) -/
theorem nclPow_subgroupOf_eq (P : RootPresentation G)
    (e : FreeGroup (FreeGroup P.α ⧸ nclU P) ≃* ↥(nclU P))
    (he : ∀ q : FreeGroup P.α ⧸ nclU P,
      ∃ s : FreeGroup P.α, QuotientGroup.mk s = q ∧
        ((e (FreeGroup.of q) : ↥(nclU P)) : FreeGroup P.α) = s * P.u * s⁻¹) :
    (nclPow P).subgroupOf (nclU P) =
      Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
        e (FreeGroup.of q) ^ P.l) := by
  set L : Subgroup ↥(nclU P) := Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
    e (FreeGroup.of q) ^ P.l) with hL
  refine le_antisymm ?_ ?_
  · -- `⟪u ^ l⟫ ∩ ⟪u⟫ ≤ L`
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hkey : nclPow P ≤ L.map (nclU P).subtype := by
      rw [nclPow, Subgroup.normalClosure]
      refine (Subgroup.closure_le (L.map (nclU P).subtype)).mpr ?_
      intro y hy
      rw [Group.mem_conjugatesOfSet_iff] at hy
      obtain ⟨a, ha, hconj⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      exact conj_pow_mem_map P e he c
    have hx' : (x : FreeGroup P.α) ∈ L.map (nclU P).subtype := hkey hx
    rw [Subgroup.mem_map] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← Subtype.ext hyx]
  · -- `L ≤ ⟪u ^ l⟫ ∩ ⟪u⟫`
    refine Subgroup.normalClosure_le_normal (N := (nclPow P).subgroupOf (nclU P)) ?_
    rintro y ⟨q, rfl⟩
    change (fun q => e (FreeGroup.of q) ^ P.l) q ∈ (nclPow P).subgroupOf (nclU P)
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨s, -, hs⟩ := he q
    have hpow : ((e (FreeGroup.of q) : ↥(nclU P)) : FreeGroup P.α) ^ P.l =
        s * (P.u ^ P.l) * s⁻¹ := by
      rw [hs, conj_pow]
    show (((e (FreeGroup.of q)) ^ P.l : ↥(nclU P)) : FreeGroup P.α) ∈ nclPow P
    rw [Subgroup.coe_pow, hpow]
    exact Subgroup.Normal.conj_mem (Subgroup.normalClosure_normal (s :=
        ({P.u ^ P.l} : Set (FreeGroup P.α)))) (P.u ^ P.l)
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) s

/-- **Step 2 of the reduction.**  `⟪u⟫ ⧸ ⟪u ^ l⟫` is the free group on the cosets of `⟪u⟫` modulo
the normal closure of the `l`-th powers of the free generators. -/
theorem quotientEquiv (P : RootPresentation G)
    (e : FreeGroup (FreeGroup P.α ⧸ nclU P) ≃* ↥(nclU P))
    (he : ∀ q : FreeGroup P.α ⧸ nclU P,
      ∃ s : FreeGroup P.α, QuotientGroup.mk s = q ∧
        ((e (FreeGroup.of q) : ↥(nclU P)) : FreeGroup P.α) = s * P.u * s⁻¹) :
    Nonempty ((↥(nclU P) ⧸ (nclPow P).subgroupOf (nclU P)) ≃*
      (FreeGroup (FreeGroup P.α ⧸ nclU P) ⧸
        Subgroup.normalClosure {x : FreeGroup (FreeGroup P.α ⧸ nclU P) |
          ∃ q : FreeGroup P.α ⧸ nclU P, x = FreeGroup.of q ^ P.l})) := by
  have hmap : Subgroup.map (e.symm : ↥(nclU P) →* FreeGroup (FreeGroup P.α ⧸ nclU P))
      ((nclPow P).subgroupOf (nclU P)) =
      Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
        FreeGroup.of q ^ P.l) := by
    rw [nclPow_subgroupOf_eq P e he]
    rw [Subgroup.map_normalClosure (s := Set.range fun q : FreeGroup P.α ⧸ nclU P =>
      e (FreeGroup.of q) ^ P.l)
      (f := (e.symm : ↥(nclU P) →* FreeGroup (FreeGroup P.α ⧸ nclU P))) e.symm.surjective]
    congr 1
    apply Set.ext
    intro x
    constructor
    · rintro ⟨y, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, by simp⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e (FreeGroup.of q) ^ P.l, ⟨q, rfl⟩, by simp⟩
  have hset : Subgroup.normalClosure (Set.range fun q : FreeGroup P.α ⧸ nclU P =>
      FreeGroup.of q ^ P.l) =
      Subgroup.normalClosure {x : FreeGroup (FreeGroup P.α ⧸ nclU P) |
        ∃ q : FreeGroup P.α ⧸ nclU P, x = FreeGroup.of q ^ P.l} := by
    congr 1
    apply Set.ext
    intro x
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.symm⟩
  exact ⟨QuotientGroup.congr ((nclPow P).subgroupOf (nclU P))
    (Subgroup.normalClosure {x : FreeGroup (FreeGroup P.α ⧸ nclU P) |
      ∃ q : FreeGroup P.α ⧸ nclU P, x = FreeGroup.of q ^ P.l})
    e.symm (by rw [hmap, hset])⟩

/-- **The theorem for a root presentation whose root is a free generator.**

For `u = of a` the Cohen--Lyndon basis of `⟪u⟫_F` is the easy case (`cohenLyndonBasisFreeGenerator`):
the normal closure of a generator `a` in `F(X)` is freely generated by the conjugates
`g a g⁻¹`, one for each coset of the subgroup they generate.  Hence the whole reduction above
applies, and `FKSKernelStructure` holds.  This is a hole-free instance of the general statement
and serves as an end-to-end check of the reduction. -/
theorem fksKernelStructure_rootPresentation_freeGenerator (α : Type u) (a : α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ IsProperPower (FreeGroup.of a)) :
    FKSKernelStructure (rootPresentation (FreeGroup.of a) l hl hpp) := by
  set P : RootPresentation (PresentedGroup ({FreeGroup.of a ^ l} : Set (FreeGroup α))) :=
    rootPresentation (FreeGroup.of a) l hl hpp with hP
  obtain ⟨e, he⟩ := cohenLyndonBasisFreeGenerator a
  obtain ⟨e1⟩ := kerFksQuotientHomEquiv P
  obtain ⟨e2⟩ := quotientEquiv P e he
  obtain ⟨e3⟩ := freeGroupQuotientPowCoprodI (Q := FreeGroup α ⧸ nclU P) l hl
  exact ⟨e1.trans (e2.trans e3)⟩

theorem fksKernelStructure {G : Type u} [Group G] (P : Work.ORLocInd.RootPresentation G) (hu : P.u ≠ 1) : Work.ORLocInd.FKSKernelStructure P := by
  obtain ⟨e, he⟩ := cohenLyndonBasis P.u hu P.not_properPower
  obtain ⟨e1⟩ := kerFksQuotientHomEquiv P
  obtain ⟨e2⟩ := quotientEquiv P e he
  obtain ⟨e3⟩ := freeGroupQuotientPowCoprodI (Q := FreeGroup P.α ⧸ nclU P) P.l P.one_le_l
  exact ⟨e1.trans (e2.trans e3)⟩

end Work.ORLocInd.FKSKernel

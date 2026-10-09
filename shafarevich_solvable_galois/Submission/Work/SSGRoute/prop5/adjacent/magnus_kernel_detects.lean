import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.core.Defs
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.coreLieBar
import Submission.Work.SSGRoute.prop5.gradedCast
import Submission.Work.SSGRoute.prop5.bracketBar_axioms
import Submission.Work.SSGRoute.prop5.gamma_commutator_jacobi_mem
import Submission.Work.SSGRoute.prop5.witt.Assembly
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
import Submission.Work.SSGRoute.prop5.witt.hall_foliage_lt_right
import Submission.Work.SSGRoute.prop5.witt.Swap
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.core.gen_span
import Submission.Work.SSGRoute.prop5.adjacent.lam_span_tree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus kernel detects the next term of the lower central series

For `y` in the `n`-th term of the lower central series of a free group whose Magnus image is
congruent to `1` modulo the degree `n+2` part of the truncated free associative algebra, we show
`y ∈ γ_{n+1}`.

The proof combines

* the identification of the associated graded of the lower central series with the graded Lie ring
  `Λbar` (`coreGraded`, `coreLieBar`, `bracketBar_axioms`),
* the fact that the Hall trees span the free Lie ring (`witt.hall_spanning`),
* the triangularity and independence of the Hall bracket monomials in the free associative
  algebra (`witt.leading_term_coeff`, `witt.hall_foliage_lt_right`),
* the compatibility of the Magnus leading term with bracket monomials (`magLead_monGrp_congr`).
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.adjacent

open Work.SSGRoute.prop5

/-! ## Homogeneity of the bracketed monomial `monBrk` -/

/-- `monBrk X c` is a combination of words of length exactly `Magma.size c`. -/
theorem monBrk_coeff_length (X : Type) (c : Magma X) (v : FreeMonoid X)
    (h : (monBrk X c).coeff v ≠ 0) : v.length = Magma.size c := by
  classical
  have hmain : ∀ (c : Magma X) (v : FreeMonoid X), v ∈ (monBrk X c).coeff.support →
      v.length = Magma.size c := by
    intro c
    induction c with
    | gen x =>
        intro v hv
        rw [monBrk_gen, MonoidAlgebra.coeff_single] at hv
        have hv' : v = FreeMonoid.of x := by
          by_contra hne
          rw [Finsupp.mem_support_iff] at hv
          exact hv (Finsupp.single_eq_of_ne hne)
        rw [hv']
        simp
    | mul a b iha ihb =>
        intro v hv
        rw [monBrk_mul, MonoidAlgebra.coeff_sub] at hv
        rcases Finset.mem_union.mp (Finsupp.support_sub hv) with hv | hv
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X a) (monBrk X b) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, iha u hu, ihb u' hu', Magma.size_mul]
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X b) (monBrk X a) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, ihb u hu, iha u' hu', Magma.size_mul, Nat.add_comm]
  exact hmain c v (by rwa [Finsupp.mem_support_iff])

/-- `monBrk X c` lies in the `size c`-th filtration ideal. -/
theorem monBrk_mem_fil (X : Type) (c : Magma X) : monBrk X c ∈ fil X (Magma.size c) := by
  rw [fil_eq_filI]
  change monBrk X c ∈ filz X (Magma.size c)
  rw [mem_filz_iff]
  intro w hw
  exact le_of_eq (monBrk_coeff_length X c w hw).symm

/-! ## The Magnus leading term of a commutator monomial -/

/-- The Magnus leading term of `monGrp c` lies in the `size c`-th filtration piece. -/
theorem magLead_monGrp_mem (X : Type) (N : ℕ) (c : Magma X) (hN : Magma.size c ≤ N) :
    magLead N (core.monGrp X c) ∈ filq X N (Magma.size c) :=
  magLead_mem_filq (X := X) N (Magma.size c) (Magma.size_pos c) hN
    (core.monGrp_mem_Gam (X := X) c)

/-! ## Reducing the truncation level -/

/-- If the Magnus leading term modulo `fil N` lies in the degree `n+2` part, then it vanishes
modulo `fil (n+2)`. -/
theorem magLead_trunc (X : Type) (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (h : magLead N y ∈ filq X N (n + 2)) : magLead (n + 2) y = 0 := by
  have hle : fil X N ≤ fil X (n + 2) := fil_antitone X hn
  let π : FreeAssoc X ⧸ fil X N →+* FreeAssoc X ⧸ fil X (n + 2) := Ideal.Quotient.factor hle
  have hπmk : ∀ a : FreeAssoc X,
      π (Ideal.Quotient.mk (fil X N) a) = Ideal.Quotient.mk (fil X (n + 2)) a :=
    fun a => Ideal.Quotient.factor_mk hle a
  have hnat : (Units.map π.toMonoidHom).comp (magnus X N) = magnus X (n + 2) := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    apply Units.ext
    simp only [MonoidHom.comp_apply, Units.coe_map]
    rw [magnus_of X N x, magnus_of X (n + 2) x]
    change π (1 + Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) 1)) =
      1 + Ideal.Quotient.mk (fil X (n + 2)) (MonoidAlgebra.single (FreeMonoid.of x) 1)
    rw [map_add, map_one, hπmk]
  have hval : π (↑((magnus X N) y)) = ↑((magnus X (n + 2)) y) := by
    have h2 := congrArg (fun u : (FreeAssoc X ⧸ fil X (n + 2))ˣ =>
      (u : FreeAssoc X ⧸ fil X (n + 2))) (DFunLike.congr_fun hnat y)
    rw [MonoidHom.comp_apply, Units.coe_map] at h2
    exact h2
  have h1 : π (magLead N y) = magLead (n + 2) y := by
    show π (↑((magnus X N) y) - 1) = _
    rw [map_sub, map_one, hval]
    rfl
  obtain ⟨a, ha, haeq⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 h
  rw [← h1, ← haeq, hπmk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-! ## The Magnus leading term of a commutator monomial, in general

We prove `magLead N (monGrp c) ≡ monBrk c` modulo the `(size c + 1)`-st filtration piece by
induction on the tree, using the bracket lemma `magLead_commutator` of `magnusGroupPart`. -/

theorem magLead_monGrp_congr (X : Type) (N : ℕ) (c : Magma X) (hN : Magma.size c + 1 ≤ N) :
    magLead N (core.monGrp X c) - Ideal.Quotient.mk (fil X N) (monBrk X c) ∈
      filq X N (Magma.size c + 1) := by
  induction c with
  | gen x =>
      have h : magLead N (core.monGrp X (Magma.gen x)) =
          Ideal.Quotient.mk (fil X N) (monBrk X (Magma.gen x)) := by
        rw [show core.monGrp X (Magma.gen x) = FreeGroup.of x from rfl, magLead_of, monBrk_gen]
        congr 1
      rw [h, sub_self]
      exact Submodule.zero_mem _
  | mul a b iha ihb =>
      rw [Magma.size_mul] at hN
      have hsa : Magma.size a + 1 ≤ N := by have := Magma.size_pos b; omega
      have hsb : Magma.size b + 1 ≤ N := by have := Magma.size_pos a; omega
      have hda := iha hsa
      have hdb := ihb hsb
      have hα := magLead_monGrp_mem X N a (by omega)
      have hβ := magLead_monGrp_mem X N b (by omega)
      have hma : Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a) :=
        Ideal.mem_map_of_mem _ (monBrk_mem_fil X a)
      have hmb : Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size b) :=
        Ideal.mem_map_of_mem _ (monBrk_mem_fil X b)
      have hcomm := magLead_commutator (X := X) N (Magma.size a) (Magma.size b)
        (Magma.size_pos a) (Magma.size_pos b) (by omega)
        (core.monGrp_mem_Gam (X := X) a) (core.monGrp_mem_Gam (X := X) b)
      have key : magLead N (core.monGrp X (Magma.mul a b)) -
            Ideal.Quotient.mk (fil X N) (monBrk X (Magma.mul a b))
          = ((magLead N (core.monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)) *
                magLead N (core.monGrp X b)
              + Ideal.Quotient.mk (fil X N) (monBrk X a) *
                (magLead N (core.monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b))
              - (magLead N (core.monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b)) *
                magLead N (core.monGrp X a)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) *
                (magLead N (core.monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)))
            + (magLead N (core.monGrp X (Magma.mul a b)) -
                (magLead N (core.monGrp X a) * magLead N (core.monGrp X b) -
                 magLead N (core.monGrp X b) * magLead N (core.monGrp X a))) := by
        rw [show core.monGrp X (Magma.mul a b) = ⁅core.monGrp X a, core.monGrp X b⁆ from rfl,
          monBrk_mul, map_sub, map_mul, map_mul]
        noncomm_ring
      rw [key]
      have ht1 : (magLead N (core.monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)) *
            magLead N (core.monGrp X b) ∈ filq X N (Magma.size (Magma.mul a b) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          mul_mem_filq X N (Magma.size a + 1) (Magma.size b) hda hβ
      have ht2 : Ideal.Quotient.mk (fil X N) (monBrk X a) *
            (magLead N (core.monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b))
            ∈ filq X N (Magma.size (Magma.mul a b) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          mul_mem_filq X N (Magma.size a) (Magma.size b + 1) hma hdb
      have ht3 : (magLead N (core.monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b)) *
            magLead N (core.monGrp X a) ∈ filq X N (Magma.size (Magma.mul a b) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          mul_mem_filq X N (Magma.size b + 1) (Magma.size a) hdb hα
      have ht4 : Ideal.Quotient.mk (fil X N) (monBrk X b) *
            (magLead N (core.monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a))
            ∈ filq X N (Magma.size (Magma.mul a b) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          mul_mem_filq X N (Magma.size b) (Magma.size a + 1) hmb hda
      have ht5 : magLead N (core.monGrp X (Magma.mul a b)) -
            (magLead N (core.monGrp X a) * magLead N (core.monGrp X b) -
             magLead N (core.monGrp X b) * magLead N (core.monGrp X a))
            ∈ filq X N (Magma.size (Magma.mul a b) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcomm
      exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
        (Submodule.add_mem _ ht1 ht2) ht3) ht4) ht5

/-! ## The Lie ring structure on the associated graded of the lower central series -/

/-- The graded bracket makes `Λbar` a Lie ring (the axioms are `bracketBar_axioms`). -/
instance instLieRingLbar (G : Type*) [Group G] : LieRing (graded.Lbar G) where
  bracket := fun x y => graded.bracketBar x y
  add_lie := fun x y z => by
    change graded.bracketBar (x + y) z = graded.bracketBar x z + graded.bracketBar y z
    rw [map_add]; rfl
  lie_add := fun x y z => by
    change graded.bracketBar x (y + z) = graded.bracketBar x y + graded.bracketBar x z
    rw [map_add]
  lie_self := fun x => graded.bracketBar_self (G := G) x
  leibniz_lie := fun x y z => by
    change graded.bracketBar x (graded.bracketBar y z) =
      graded.bracketBar (graded.bracketBar x y) z + graded.bracketBar y (graded.bracketBar x z)
    exact (bracketBar_axioms G).2 x y z

instance instLieAlgebraLbar (G : Type*) [Group G] : LieAlgebra ℤ (graded.Lbar G) where
  lie_smul := fun t x y => by
    change graded.bracketBar x (t • y) = t • graded.bracketBar x y
    exact (graded.bracketBar x).map_zsmul t y

/-- The bracket on `Λbar` is the graded bracket. -/
theorem bracketLbar_eq (G : Type*) [Group G] (x y : graded.Lbar G) :
    ⁅x, y⁆ = graded.bracketBar x y := rfl

/-- The class map `cls` in the `mk'`-form. -/
theorem cls_eq_mk' (X : Type) (q : ℕ) (x : core.Gam X q) :
    core.cls X q x = Additive.ofMul (QuotientGroup.mk'
      ((graded.Gam (G := FreeGroup X) (q + 1)).subgroupOf (graded.Gam (G := FreeGroup X) q)) x) := rfl

/-! ## A grading function on trees for which the bracket is homogeneous on the nose -/

/-- The grading function on trees: `gen ↦ 0`, `mul a b ↦ w a + w b + 1`. -/
def treeW (X : Type) : Magma X → ℕ
  | Magma.gen _ => 0
  | Magma.mul a b => treeW X a + treeW X b + 1

@[simp] theorem treeW_gen (X : Type) (x : X) : treeW X (Magma.gen x) = 0 := rfl
@[simp] theorem treeW_mul (X : Type) (a b : Magma X) :
    treeW X (Magma.mul a b) = treeW X a + treeW X b + 1 := rfl

theorem treeW_eq_size (X : Type) (c : Magma X) : treeW X c = Magma.size c - 1 := by
  induction c with
  | gen x => simp
  | mul a b iha ihb =>
      rw [treeW_mul, Magma.size_mul, iha, ihb]
      have ha := Magma.size_pos a
      have hb := Magma.size_pos b
      omega

theorem monGrp_mem_GamW (X : Type) (c : Magma X) :
    core.monGrp X c ∈ core.Gam X (treeW X c) := by
  induction c with
  | gen x => show FreeGroup.of x ∈ core.Gam X 0; simp [core.Gam]
  | mul a b iha ihb =>
      show ⁅core.monGrp X a, core.monGrp X b⁆ ∈ core.Gam X (treeW X a + treeW X b + 1)
      exact graded.commutator_mem_Gam iha ihb

/-- The class of the commutator monomial of `c`, in the graded piece of degree `treeW c`. -/
noncomputable def clsW (X : Type) (c : Magma X) : graded.LamAdd (G := FreeGroup X) (treeW X c) :=
  core.cls X (treeW X c) ⟨core.monGrp X c, monGrp_mem_GamW X c⟩

theorem clsW_eq_mk' (X : Type) (c : Magma X) :
    clsW X c = Additive.ofMul (QuotientGroup.mk'
      ((graded.Gam (G := FreeGroup X) (treeW X c + 1)).subgroupOf
        (graded.Gam (G := FreeGroup X) (treeW X c)))
      ⟨core.monGrp X c, monGrp_mem_GamW X c⟩) := rfl

/-- The class map on trees, as an element of `Λbar`.  This is defined by recursion so that the
grading indices stay syntactically additive. -/
noncomputable def psiW (X : Type) : Magma X → graded.Lbar (FreeGroup X)
  | Magma.gen x =>
      DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) 0
        (core.cls X 0 ⟨FreeGroup.of x, by simp [core.Gam]⟩)
  | Magma.mul a b =>
      DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a + treeW X b + 1)
        (core.cls X (treeW X a + treeW X b + 1)
          ⟨core.monGrp X (Magma.mul a b),
            by show ⁅core.monGrp X a, core.monGrp X b⁆ ∈ core.Gam X (treeW X a + treeW X b + 1)
               exact graded.commutator_mem_Gam (monGrp_mem_GamW X a) (monGrp_mem_GamW X b)⟩)

theorem psiW_eq_of (X : Type) (c : Magma X) :
    psiW X c = DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X c) (clsW X c) := by
  induction c with
  | gen x =>
      show DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) 0
          (core.cls X 0 ⟨FreeGroup.of x, _⟩) =
        DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) 0
          (core.cls X 0 ⟨core.monGrp X (Magma.gen x), _⟩)
      congr 1
  | mul a b iha ihb =>
      show DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a + treeW X b + 1)
          (core.cls X (treeW X a + treeW X b + 1) ⟨core.monGrp X (Magma.mul a b), _⟩) =
        DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a + treeW X b + 1)
          (core.cls X (treeW X a + treeW X b + 1) ⟨core.monGrp X (Magma.mul a b), _⟩)
      congr 1

theorem psiW_mul_eq (X : Type) (a b : Magma X) :
    psiW X (Magma.mul a b) =
      DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a + treeW X b + 1)
        (core.cls X (treeW X a + treeW X b + 1)
          ⟨core.monGrp X (Magma.mul a b),
            graded.commutator_mem_Gam (monGrp_mem_GamW X a) (monGrp_mem_GamW X b)⟩) := rfl

theorem commClass_eq (X : Type) (a b : Magma X) :
    graded.commClass (G := FreeGroup X) (treeW X a) (treeW X b)
        ⟨core.monGrp X a, monGrp_mem_GamW X a⟩ ⟨core.monGrp X b, monGrp_mem_GamW X b⟩ =
      QuotientGroup.mk' ((graded.Gam (G := FreeGroup X) (treeW X a + treeW X b + 1 + 1)).subgroupOf
        (graded.Gam (G := FreeGroup X) (treeW X a + treeW X b + 1)))
        ⟨core.monGrp X (Magma.mul a b),
          graded.commutator_mem_Gam (monGrp_mem_GamW X a) (monGrp_mem_GamW X b)⟩ :=
  congrArg (QuotientGroup.mk'
      ((graded.Gam (G := FreeGroup X) (treeW X a + treeW X b + 1 + 1)).subgroupOf
        (graded.Gam (G := FreeGroup X) (treeW X a + treeW X b + 1))))
    (Subtype.ext rfl)

theorem clsW_bracket (X : Type) (a b : Magma X) :
    graded.bracketL (G := FreeGroup X) (treeW X a) (treeW X b) (clsW X a) (clsW X b) =
      core.cls X (treeW X a + treeW X b + 1)
        ⟨core.monGrp X (Magma.mul a b),
          by show ⁅core.monGrp X a, core.monGrp X b⁆ ∈ core.Gam X (treeW X a + treeW X b + 1)
             exact graded.commutator_mem_Gam (monGrp_mem_GamW X a) (monGrp_mem_GamW X b)⟩ := by
  rw [clsW_eq_mk', clsW_eq_mk', graded.bracketL_apply_mk, cls_eq_mk']
  exact congrArg Additive.ofMul (commClass_eq X a b)

/-- The composite `FreeLieAlgebra ℤ X → Λbar(FreeGroup X)` sending generators to the classes
of the generators. -/
noncomputable def nuL (X : Type) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ graded.Lbar (FreeGroup X) :=
  FreeLieAlgebra.lift ℤ (fun x => DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) 0
    (core.cls X 0 ⟨FreeGroup.of x, by simp [core.Gam]⟩))

theorem psiW_bracket (X : Type) (a b : Magma X) :
    ⁅psiW X a, psiW X b⁆ = psiW X (Magma.mul a b) := by
  rw [bracketLbar_eq, psiW_eq_of X a, psiW_eq_of X b, psiW_mul_eq X a b]
  rw [show DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a) (clsW X a) =
      graded.lofL (G := FreeGroup X) (treeW X a) (clsW X a) from
    DirectSum.lof_eq_of ℤ ℕ (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a) (clsW X a)]
  rw [show DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X b) (clsW X b) =
      graded.lofL (G := FreeGroup X) (treeW X b) (clsW X b) from
    DirectSum.lof_eq_of ℤ ℕ (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X b) (clsW X b)]
  rw [show DirectSum.of (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a + treeW X b + 1)
        (core.cls X (treeW X a + treeW X b + 1)
          ⟨core.monGrp X (Magma.mul a b),
            by show ⁅core.monGrp X a, core.monGrp X b⁆ ∈ core.Gam X (treeW X a + treeW X b + 1)
               exact graded.commutator_mem_Gam (monGrp_mem_GamW X a) (monGrp_mem_GamW X b)⟩) =
      graded.lofL (G := FreeGroup X) (treeW X a + treeW X b + 1)
        (core.cls X (treeW X a + treeW X b + 1)
          ⟨core.monGrp X (Magma.mul a b),
            by show ⁅core.monGrp X a, core.monGrp X b⁆ ∈ core.Gam X (treeW X a + treeW X b + 1)
               exact graded.commutator_mem_Gam (monGrp_mem_GamW X a) (monGrp_mem_GamW X b)⟩) from
    DirectSum.lof_eq_of ℤ ℕ (fun k => graded.LamAdd (G := FreeGroup X) k) (treeW X a + treeW X b + 1) _]
  rw [graded.bracketBar_lofL, clsW_bracket]

theorem nuL_monLie (X : Type) (c : Magma X) : nuL X (monLie X c) = psiW X c := by
  induction c with
  | gen x =>
      rw [monLie_gen]
      exact FreeLieAlgebra.lift_of_apply _ x
  | mul a b iha ihb =>
      rw [monLie_mul, LieHom.map_lie, iha, ihb, psiW_bracket]

/-! ## Projection onto one graded piece -/

/-- The projection of `Λbar` onto its `p`-th graded piece. -/
noncomputable def projL (G : Type*) [Group G] (p : ℕ) :
    graded.Lbar G →+ graded.LamAdd (G := G) p :=
  (DFinsupp.liftAddHom (β := fun q => graded.LamAdd (G := G) q)
    (γ := graded.LamAdd (G := G) p)
    (fun q => if h : q = p then (graded.GLamCast (G := G) h).toAddMonoidHom else 0) :
    (DirectSum ℕ (fun q => graded.LamAdd (G := G) q) →+ graded.LamAdd (G := G) p))

theorem projL_of_eq (G : Type*) [Group G] (p : ℕ) {q : ℕ} (h : q = p)
    (x : graded.LamAdd (G := G) q) :
    projL G p (DirectSum.of graded.LamAdd q x) = graded.GLamCast (G := G) h x := by
  show (DFinsupp.liftAddHom (β := fun q => graded.LamAdd (G := G) q)
      (γ := graded.LamAdd (G := G) p)
      (fun q => if h : q = p then (graded.GLamCast (G := G) h).toAddMonoidHom else 0))
      (DFinsupp.single q x) = graded.GLamCast (G := G) h x
  rw [DFinsupp.liftAddHom_apply_single, dif_pos h]
  rfl

theorem projL_of_ne (G : Type*) [Group G] (p : ℕ) {q : ℕ} (h : q ≠ p)
    (x : graded.LamAdd (G := G) q) :
    projL G p (DirectSum.of graded.LamAdd q x) = 0 := by
  show (DFinsupp.liftAddHom (β := fun q => graded.LamAdd (G := G) q)
      (γ := graded.LamAdd (G := G) p)
      (fun q => if h : q = p then (graded.GLamCast (G := G) h).toAddMonoidHom else 0))
      (DFinsupp.single q x) = 0
  rw [DFinsupp.liftAddHom_apply_single, dif_neg h]
  rfl

/-- An additive map pushes spans into spans. -/
theorem mem_span_map_of_mem {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    {S : Set M} {x : M} (hx : x ∈ Submodule.span ℤ S) :
    f x ∈ Submodule.span ℤ (f '' S) := by
  refine Submodule.span_induction (p := fun x _ => f x ∈ Submodule.span ℤ (f '' S))
    ?_ ?_ ?_ ?_ hx
  · rintro a ha
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro n a _ ha
    rw [map_zsmul]
    exact Submodule.smul_mem _ n ha

set_option maxHeartbeats 4000000 in
theorem psiW_mem_span (X : Type) [LinearOrder X] (c : Magma X) :
    psiW X c ∈ Submodule.span ℤ (Set.range (fun h : {h : Magma X // IsHall h} => psiW X h.1)) := by
  have h0 : monLie X c ∈ Submodule.span ℤ
      (Set.range (fun h : {h : Magma X // IsHall h} => monLie X h.1)) :=
    witt.hall_spanning (monLie X) (fun _ _ => rfl) c
  have h1 : (nuL X) (monLie X c) ∈ Submodule.span ℤ
      (((nuL X).toLinearMap.toAddMonoidHom) ''
        Set.range (fun h : {h : Magma X // IsHall h} => monLie X h.1)) :=
    mem_span_map_of_mem _ h0
  have hset : ((nuL X).toLinearMap.toAddMonoidHom ''
        Set.range (fun h : {h : Magma X // IsHall h} => monLie X h.1)) =
      Set.range (fun h : {h : Magma X // IsHall h} => psiW X h.1) := by
    ext y
    constructor
    · rintro ⟨x, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, (nuL_monLie X h.1).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨monLie X h.1, ⟨h, rfl⟩, nuL_monLie X h.1⟩
  rw [hset] at h1
  rwa [nuL_monLie] at h1

set_option maxHeartbeats 1000000 in
theorem projL_psiW (X : Type) (c : Magma X) :
    projL (FreeGroup X) (treeW X c) (psiW X c) = clsW X c := by
  rw [psiW_eq_of X c]
  exact projL_of_eq (FreeGroup X) (treeW X c) rfl (clsW X c)

theorem GLamCast_cls (X : Type) {m n : ℕ} (h : m = n) (x : core.Gam X m) :
    graded.GLamCast (G := FreeGroup X) h (core.cls X m x) =
      core.cls X n ⟨(x : FreeGroup X), (congrArg (core.Gam X) h) ▸ x.property⟩ := by
  rw [cls_eq_mk', cls_eq_mk', graded.GLamCast_mk']

theorem hsizeIdx (X : Type) (k : ℕ) (c : core.TreeIdx X k) : treeW X c.1 = k - 1 := by
  rw [treeW_eq_size, c.2]

set_option maxHeartbeats 8000000 in
theorem treeClOf_eq_GLamCast_clsW (X : Type) (k : ℕ) (c : core.TreeIdx X k) :
    core.treeClOf X k c = graded.GLamCast (G := FreeGroup X) (hsizeIdx X k c) (clsW X c.1) := by
  show core.cls X (k - 1) ⟨core.monGrp X c.1, _⟩ =
    graded.GLamCast (G := FreeGroup X) (hsizeIdx X k c)
      (core.cls X (treeW X c.1) ⟨core.monGrp X c.1, monGrp_mem_GamW X c.1⟩)
  rw [cls_eq_mk', cls_eq_mk', graded.GLamCast_mk']

theorem hallClOf_eq_treeClOf (X : Type) [LinearOrder X] (k : ℕ) (h : core.HallIdx X k) :
    core.hallClOf X k h = core.treeClOf X k ⟨h.1, h.2.2⟩ :=
  congrArg (core.cls X (k - 1)) (Subtype.ext rfl)

theorem treeClOf_mem_range_hall (X : Type) [LinearOrder X] (k : ℕ) (c : core.TreeIdx X k)
    (hc : IsHall c.1) : core.treeClOf X k c ∈ LinearMap.range (core.hallToLam X k) := by
  refine LinearMap.mem_range.mpr ⟨Finsupp.single ⟨c.1, hc, c.2⟩ 1, ?_⟩
  rw [core.hallToLam_single, hallClOf_eq_treeClOf]

set_option maxHeartbeats 8000000 in
theorem treeClOf_mem_hall (X : Type) [LinearOrder X] (k : ℕ) (hk : 1 ≤ k)
    (c : core.TreeIdx X k) :
    core.treeClOf X k c ∈ LinearMap.range (core.hallToLam X k) := by
  set S : Set (graded.LamAdd (G := FreeGroup X) (k - 1)) :=
    {x | ∃ h : core.HallIdx X k, core.treeClOf X k ⟨h.1, h.2.2⟩ = x} with hS
  suffices hmain : core.treeClOf X k c ∈ Submodule.span ℤ S by
    refine Submodule.span_le.mpr ?_ hmain
    rintro y ⟨h, rfl⟩
    exact treeClOf_mem_range_hall X k ⟨h.1, h.2.2⟩ h.2.1
  set P : Set (graded.Lbar (FreeGroup X)) :=
    Set.range (fun h : {h : Magma X // IsHall h} => psiW X h.1) with hP
  have hspan : psiW X c.1 ∈ Submodule.span ℤ P := psiW_mem_span X c.1
  set g : graded.Lbar (FreeGroup X) →+ graded.LamAdd (G := FreeGroup X) (treeW X c.1) :=
    projL (FreeGroup X) (treeW X c.1) with hg
  have h1 : g (psiW X c.1) ∈ Submodule.span ℤ (g '' P) := mem_span_map_of_mem g hspan
  rw [hg, projL_psiW] at h1
  set e : graded.LamAdd (G := FreeGroup X) (treeW X c.1) ≃+
      graded.LamAdd (G := FreeGroup X) (k - 1) :=
    graded.GLamCast (G := FreeGroup X) (hsizeIdx X k c) with he
  have hE : e (clsW X c.1) ∈ Submodule.span ℤ (e '' (g '' P)) :=
    mem_span_map_of_mem e.toAddMonoidHom h1
  rw [← treeClOf_eq_GLamCast_clsW X k c] at hE
  have hsub : e '' (g '' P) ⊆ (Submodule.span ℤ S : Set _) := by
    rintro y ⟨z, ⟨w, ⟨h, rfl⟩, rfl⟩, rfl⟩
    simp only []
    rw [psiW_eq_of X h.1]
    by_cases hw : treeW X h.1 = treeW X c.1
    · rw [projL_of_eq (FreeGroup X) (treeW X c.1) hw (clsW X h.1), he, graded.GLamCast_trans]
      have hsize : Magma.size h.1 = k := by
        have h1 := treeW_eq_size X h.1
        have h2 := treeW_eq_size X c.1
        have hp1 := Magma.size_pos h.1
        have hp2 := Magma.size_pos c.1
        omega
      refine Submodule.subset_span ⟨⟨h.1, h.2, hsize⟩, ?_⟩
      rw [treeClOf_eq_GLamCast_clsW X k ⟨h.1, hsize⟩]
    · rw [projL_of_ne (FreeGroup X) (treeW X c.1) hw (clsW X h.1), map_zero]
      exact Submodule.zero_mem _
  simpa using Submodule.span_mono hsub hE

set_option maxHeartbeats 8000000 in
theorem lam_span_hall (X : Type) [LinearOrder X] (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.range (core.treeToLam X k) ≤ LinearMap.range (core.hallToLam X k) := by
  rw [show LinearMap.range (core.treeToLam X k) =
      Submodule.span ℤ (Set.range (core.treeClOf X k)) from
    Finsupp.range_linearCombination (R := ℤ) (v := core.treeClOf X k)]
  rw [Submodule.span_le]
  rintro x ⟨c, rfl⟩
  exact treeClOf_mem_hall X k hk c

/-! ## Independence of the Hall bracket monomials in the free associative algebra -/

theorem hall_foliage_inj (X : Type) [LinearOrder X] :
    ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b :=
  fun a b ha hb h => witt.hall_foliage_injective_aux ha hb h

theorem hlead_hall (X : Type) [LinearOrder X] (c : Magma X) (hc : IsHall c) :
    coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
      ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0 :=
  witt.leading_term_coeff hc
    (fun a b hab => swap_hall_of_crux (fun a b hab => witt.hall_foliage_lt_right hab) hab)

/-- The Hall bracket monomials are linearly independent in `ℤ[FreeMonoid X]` (finset form). -/
theorem independence_monBrk (X : Type) [LinearOrder X]
    (hlead : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0)
    (hinj : ∀ a b : Magma X, IsHall a → IsHall b → Magma.foliage a = Magma.foliage b → a = b)
    (s : Finset {h : Magma X // IsHall h}) (α : {h : Magma X // IsHall h} → ℤ)
    (hzero : (∑ h ∈ s, α h • monBrk X h.1) = 0) :
    ∀ h ∈ s, α h = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁, h₁s, h₁ne⟩ := hcon
  set s' := s.filter (fun h => α h ≠ 0) with hs'
  have hs'ne : s'.Nonempty := ⟨h₁, by simp [hs', h₁s, h₁ne]⟩
  obtain ⟨h₀, h₀s', h₀min⟩ := Finset.exists_min_image s' (fun h => Magma.foliage h.1) hs'ne
  rw [hs', Finset.mem_filter] at h₀s'
  obtain ⟨h₀s, h₀ne⟩ := h₀s'
  have hkey : coeffF (∑ h ∈ s, α h • monBrk X h.1) (Magma.foliage h₀.1) = α h₀ := by
    rw [coeffF_sum, Finset.sum_eq_single h₀]
    · rw [coeffF_smul, (hlead h₀.1 h₀.2).1, mul_one]
    · intro h hs hne
      rw [coeffF_smul]
      by_cases hα : α h = 0
      · rw [hα, zero_mul]
      · have hh : h ∈ s' := by simp [hs', hs, hα]
        have hle := h₀min h hh
        rcases lt_or_eq_of_le hle with hlt | heq
        · rw [(hlead h.1 h.2).2 _ hlt, mul_zero]
        · exact absurd (Subtype.ext (hinj h₀.1 h.1 h₀.2 h.2 heq)).symm hne
    · intro h₀not; exact absurd h₀s h₀not
  rw [hzero, coeffF_zero] at hkey
  exact h₀ne hkey.symm

/-- The Hall bracket monomials are linearly independent (finitely supported form). -/
theorem monBrk_independent_all (X : Type) [LinearOrder X]
    (d : {h : Magma X // IsHall h} →₀ ℤ)
    (hd : d.sum (fun h r => r • monBrk X h.1) = 0) : d = 0 := by
  classical
  rw [Finsupp.ext_iff]
  intro h₀
  have hsum : (∑ h ∈ d.support, d h • monBrk X h.1) = 0 := by
    rw [← Finsupp.sum_of_support_subset d (Finset.Subset.refl _)
      (fun h r => r • monBrk X h.1) (by simp)]
    exact hd
  have := independence_monBrk X (hlead_hall X) (hall_foliage_inj X) d.support
    (fun h => d h) hsum
  by_cases hh : h₀ ∈ d.support
  · simpa using this h₀ hh
  · simpa [Finsupp.mem_support_iff] using hh

/-- The classes of the Hall trees of a fixed size are linearly independent (in the sense that a
combination whose bracketed monomial vanishes has all coefficients zero). -/
theorem hall_independent (X : Type) [LinearOrder X] (k : ℕ) (b : core.HallIdx X k →₀ ℤ)
    (hb : b.sum (fun h r => r • monBrk X h.1) = 0) : b = 0 := by
  classical
  let e : core.HallIdx X k ↪ {h : Magma X // IsHall h} :=
    ⟨fun h => ⟨h.1, h.2.1⟩,
      fun a b hab => Subtype.ext (congrArg (fun x : {h : Magma X // IsHall h} => x.1) hab)⟩
  have hd : (Finsupp.embDomain e b).sum (fun h r => r • monBrk X h.1) = 0 := by
    rw [Finsupp.sum_embDomain]
    exact hb
  exact Finsupp.embDomain_eq_zero.mp (monBrk_independent_all X _ hd)


/-! ## The Magnus leading term as an additive map on the graded piece -/

/-- The Magnus leading term, as an additive map `Λ_{k-1} → A ⧸ fil (k+1)` (`k ≥ 1`). -/
noncomputable def Mbar (X : Type) (k : ℕ) (hk : 1 ≤ k) :
    core.Lam X (k - 1) →+ (FreeAssoc X ⧸ fil X (k + 1)) :=
  MonoidHom.toAdditive
    (QuotientGroup.lift ((core.Gam X (k - 1 + 1)).subgroupOf (core.Gam X (k - 1)))
      { toFun := fun u => Multiplicative.ofAdd (magLead (k + 1) (u : FreeGroup X))
        map_one' := by
          apply Multiplicative.ext
          show magLead (k + 1) ((1 : ↥(core.Gam X (k - 1))) : FreeGroup X) = 0
          rw [show ((1 : ↥(core.Gam X (k - 1))) : FreeGroup X) = 1 from rfl, magLead_one]
        map_mul' := by
          intro a b
          apply Multiplicative.ext
          show magLead (k + 1) (((a * b : ↥(core.Gam X (k - 1)))) : FreeGroup X) =
            magLead (k + 1) (a : FreeGroup X) + magLead (k + 1) (b : FreeGroup X)
          rw [show (((a * b : ↥(core.Gam X (k - 1)))) : FreeGroup X)
            = (a : FreeGroup X) * (b : FreeGroup X) from rfl]
          exact magLead_mul (X := X) (k + 1) k hk (by omega) (by omega) a.property b.property }
      (by
        intro u hu
        apply Multiplicative.ext
        show magLead (k + 1) (u : FreeGroup X) = 0
        have hu2 : (u : FreeGroup X) ∈ core.Gam X k := by
          have h := (Subgroup.mem_subgroupOf (H := core.Gam X (k - 1 + 1))
            (K := core.Gam X (k - 1))).1 hu
          simpa [Nat.sub_add_cancel hk] using h
        exact magLead_eq_zero_of_mem_succ (X := X) k hu2))

theorem Mbar_cls (X : Type) (k : ℕ) (hk : 1 ≤ k) (u : core.Gam X (k - 1)) :
    Mbar X k hk (core.cls X (k - 1) u) = magLead (k + 1) (u : FreeGroup X) := rfl

theorem magLead_monGrp_eq (X : Type) (k : ℕ) (c : core.TreeIdx X k) :
    magLead (k + 1) (core.monGrp X c.1) = Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
  have h1 := magLead_monGrp_congr X (k + 1) c.1 (by rw [c.2])
  rw [show Magma.size c.1 + 1 = k + 1 from by rw [c.2]] at h1
  rw [filq_self_eq_bot' (X := X) (k + 1), Submodule.mem_bot] at h1
  exact sub_eq_zero.mp h1

theorem linearCombination_map {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (g : ι → M) (μ : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ g μ) = Finsupp.linearCombination ℤ (fun i => f (g i)) μ := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset μ (Finset.Subset.refl _) (fun i r => r • g i) (by simp),
    Finsupp.sum_of_support_subset μ (Finset.Subset.refl _) (fun i r => r • f (g i)) (by simp)]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_zsmul f _ _)

theorem linearCombination_congr_left {ι M : Type*} [AddCommGroup M] {g g' : ι → M}
    (h : g = g') (μ : ι →₀ ℤ) :
    Finsupp.linearCombination ℤ g μ = Finsupp.linearCombination ℤ g' μ := by rw [h]

theorem coeff_finset_sum (X : Type) {ι : Type*} (s : Finset ι) (f : ι → FreeAssoc X)
    (w : FreeMonoid X) :
    (∑ i ∈ s, f i).coeff w = ∑ i ∈ s, (f i).coeff w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [MonoidAlgebra.coeff_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]

/-! ## The main theorem -/

/-- **The Magnus kernel detects the next term**:  if `y` lies in the `n`-th term of the lower
central series and the Magnus image of `y` is congruent to `1` modulo the degree-`n+2` part of the
truncated free associative algebra, then `y ∈ γ_{n+1}`. -/
theorem magnus_kernel_detects (X : Type) (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n)
    (h : ((Work.SSGRoute.prop5.magnus X N y : (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N)ˣ) : Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X N) - 1 ∈ Work.SSGRoute.prop5.filq X N (n + 2)) :
    y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (n + 1) := by
  classical
  obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
  letI := instLO
  -- reduce to the sharp truncation
  have hz : magLead (n + 2) y = 0 := magLead_trunc X N n hn y (by simpa [magLead] using h)
  set k := n + 1 with hkdef
  have hk : 1 ≤ k := by omega
  have hyk : y ∈ core.Gam X (k - 1) := by
    show y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)
    rw [hkdef, Nat.add_sub_cancel]
    exact hy
  -- express the class of `y` by Hall commutator monomials
  obtain ⟨μ, hμ⟩ := LinearMap.mem_range.mp (lam_span_tree X k hk y hyk)
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp
    (lam_span_hall X k hk (LinearMap.mem_range.mpr ⟨μ, hμ⟩))
  -- the Magnus leading terms agree
  have hM : Mbar X k hk (core.cls X (k - 1) ⟨y, hyk⟩) = Mbar X k hk (core.hallToLam X k b) := by
    rw [hb]
  rw [Mbar_cls X k hk ⟨y, hyk⟩] at hM
  have hzy : magLead (k + 1) y = 0 := by rw [hkdef]; exact hz
  rw [hzy] at hM
  -- compute the right hand side
  have hP : (Ideal.Quotient.mk (fil X (k + 1))
      (Finsupp.linearCombination ℤ (fun h : core.HallIdx X k => monBrk X h.1) b)) = 0 := by
    rw [hM]
    rw [core.hallToLam, linearCombination_map (Mbar X k hk) (core.hallClOf X k) b]
    rw [show (Finsupp.linearCombination ℤ (fun h : core.HallIdx X k =>
          Mbar X k hk (core.hallClOf X k h)) b)
        = Finsupp.linearCombination ℤ (fun h : core.HallIdx X k =>
            (Ideal.Quotient.mk (fil X (k + 1))).toAddMonoidHom (monBrk X h.1)) b from
      linearCombination_congr_left (funext (fun h : core.HallIdx X k => by
        rw [show core.hallClOf X k h = core.cls X (k - 1) ⟨core.monGrp X h.1, _⟩ from rfl,
          Mbar_cls X k hk]
        exact magLead_monGrp_eq X k ⟨h.1, h.2.2⟩)) b]
    rw [← linearCombination_map ((Ideal.Quotient.mk (fil X (k + 1))).toAddMonoidHom)
      (fun h : core.HallIdx X k => monBrk X h.1) b]
    rfl

  -- homogeneity: the combination vanishes in the free associative algebra
  have hzeroA : Finsupp.linearCombination ℤ (fun h : core.HallIdx X k => monBrk X h.1) b = 0 := by
    have hfil : Finsupp.linearCombination ℤ (fun h : core.HallIdx X k => monBrk X h.1) b
        ∈ fil X (k + 1) := Ideal.Quotient.eq_zero_iff_mem.mp hP
    have hcoeff : ∀ w : FreeMonoid X, w.length ≠ k →
        (Finsupp.linearCombination ℤ (fun h : core.HallIdx X k => monBrk X h.1) b).coeff w = 0 := by
      intro w hw
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset b (Finset.Subset.refl _)
          (fun i r => r • monBrk X i.1) (by simp)]
      rw [coeff_finset_sum X]
      refine Finset.sum_eq_zero (fun h _ => ?_)
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
      have h0 : (monBrk X h.1).coeff w = 0 := by
        by_contra hne
        exact hw (by rw [monBrk_coeff_length X h.1 w hne, h.2.2])
      rw [h0, mul_zero]
    apply MonoidAlgebra.ext
    rw [MonoidAlgebra.coeff_zero]
    ext w
    by_cases hw : w.length = k
    · by_contra hne
      have h2 : Finsupp.linearCombination ℤ (fun h : core.HallIdx X k => monBrk X h.1) b
          ∈ filz X (k + 1) := by
        rw [fil_eq_filI] at hfil
        exact hfil
      have h3 := mem_filz_iff.mp h2 w hne
      omega
    · exact hcoeff w hw
  -- independence of the Hall monomials
  have hb0 : b = 0 := hall_independent X k b (by
    simpa [Finsupp.linearCombination_apply] using hzeroA)
  have hcls0 : core.cls X (k - 1) ⟨y, hyk⟩ = 0 := by
    rw [← hb, hb0]
    rfl
  have hmem : y ∈ core.Gam X k := (core.cls_eq_zero_iff (X := X) (q := k - 1) (x := ⟨y, hyk⟩)).1 hcls0
  show y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (n + 1)
  rw [show n + 1 = k from hkdef.symm]
  exact hmem

end Work.SSGRoute.prop5.adjacent

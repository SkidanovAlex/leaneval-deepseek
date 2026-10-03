import Mathlib
import Submission.Work.ORLinnell.Linnell
import Submission.Work.ORLinnell.FiniteIndex.eq_zero_of_sum_transversal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The finite index decomposition `D H = ⊕_{q ∈ H/G'} D G' · x_q`

Let `L : LinnellDatum K G U` be the Linnell datum attached to a group `G`, a field `K` and the
ring of affiliated operators `U = U(G)`.  For subgroups `G' ⊴ G` (torsion free, of finite index)
and `G' ≤ H ≤ G` we prove that every element of the division closure `L.D H` is uniquely a finite
`L.D G'`-linear combination of the coset representatives `Quotient.out q` of `G'` in `H`.

The two halves of the statement are:

* *existence*: the set `E` of such combinations is a subring of `U` containing `K[H]` and closed
  under inverses in `U`; since `L.D H` is the smallest such subring, `L.D H ≤ E`;
* *uniqueness*: the decomposition is direct by Linnell independence (I1).

Both proofs are self-contained in this file, except for the directness of the decomposition
which is imported from `Submission.Work.ORLinnell.FiniteIndex.eq_zero_of_sum_transversal`.
-/

noncomputable section

namespace Work.ORLinnell.Cosets

open Work.ORLinnell

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-! ## The coset representatives -/

variable {H₀ H : Subgroup G} [hN : (H₀.subgroupOf H).Normal]

/-- The translator `out q * out q' * (out (q * q'))⁻¹` between a product of coset
representatives and the representative of the product coset.  It lies in `H₀`. -/
def repDelta (q q' : H ⧸ H₀.subgroupOf H) : H :=
  Quotient.out q * Quotient.out q' * (Quotient.out (q * q'))⁻¹

lemma repDelta_mem (q q' : H ⧸ H₀.subgroupOf H) : repDelta q q' ∈ H₀.subgroupOf H := by
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk (Quotient.out q * Quotient.out q' * (Quotient.out (q * q'))⁻¹) = 1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq',
      QuotientGroup.out_eq', QuotientGroup.out_eq']
  group

/-- The coset representative `out q` as a unit of `U`. -/
def repXU (L : LinnellDatum K G U) (q : H ⧸ H₀.subgroupOf H) : Uˣ :=
  L.gen ((Quotient.out q : H) : G)

/-- The coset representative `out q` as an element of `U`. -/
def repX (L : LinnellDatum K G U) (q : H ⧸ H₀.subgroupOf H) : U := (repXU L q : U)

/-- The crossed product relation for the representatives. -/
lemma repXU_mul (L : LinnellDatum K G U) (q q' : H ⧸ H₀.subgroupOf H) :
    repXU L q * repXU L q' = L.gen ((repDelta q q' : H) : G) * repXU L (q * q') := by
  have hfac : ((Quotient.out q * Quotient.out q' : H) : G)
      = ((repDelta q q' : H) : G) * ((Quotient.out (q * q') : H) : G) := by
    rw [← Subgroup.coe_mul]
    congr 1
    rw [repDelta]; group
  calc repXU L q * repXU L q' = L.gen (((Quotient.out q * Quotient.out q' : H)) : G) := by
        rw [repXU, repXU, ← map_mul, ← Subgroup.coe_mul]
    _ = L.gen (((repDelta q q' : H) : G) * ((Quotient.out (q * q') : H) : G)) := by rw [hfac]
    _ = L.gen ((repDelta q q' : H) : G) * L.gen ((Quotient.out (q * q') : H) : G) := by
        rw [map_mul]
    _ = L.gen ((repDelta q q' : H) : G) * repXU L (q * q') := rfl

lemma repX_mul (L : LinnellDatum K G U) (q q' : H ⧸ H₀.subgroupOf H) :
    repX L q * repX L q' = (L.gen ((repDelta q q' : H) : G) : U) * repX L (q * q') := by
  rw [show repX L q * repX L q' = (repXU L q : U) * (repXU L q' : U) from rfl, ← Units.val_mul,
    repXU_mul, Units.val_mul]
  rfl

/-! ## The spanning sums -/

/-- The element `∑_q c_q · x_q` of `U`. -/
def xspan (L : LinnellDatum K G U) (c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) : U :=
  c.sum (fun q d => (d : U) * repX L q)

lemma xspan_zero (L : LinnellDatum K G U) :
    xspan L (0 : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) = 0 := by
  rw [xspan, Finsupp.sum_zero_index]

lemma xspan_add (L : LinnellDatum K G U) (c c' : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) :
    xspan L (c + c') = xspan L c + xspan L c' := by
  classical
  simp only [xspan]
  exact Finsupp.sum_add_index (by intro a ha; simp)
    (by intro a ha b₁ b₂; rw [Subring.coe_add, add_mul])

lemma xspan_single (L : LinnellDatum K G U) (q : H ⧸ H₀.subgroupOf H) (d : ↥(L.D H₀)) :
    xspan L (Finsupp.single q d) = (d : U) * repX L q := by
  rw [xspan]
  exact Finsupp.sum_single_index (by simp)

lemma xspan_smul (L : LinnellDatum K G U) (d : ↥(L.D H₀))
    (c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) :
    xspan L (d • c) = (d : U) * xspan L c := by
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [smul_zero, xspan_zero, mul_zero]
  · intro a b f ha hb ih
    rw [smul_add, Finsupp.smul_single, xspan_add, xspan_add, xspan_single, xspan_single, ih,
      mul_add]
    rw [show (d • b : ↥(L.D H₀)) = d * b from rfl]
    simp only [Subring.coe_mul, mul_assoc]

/-! ## The carrier set and its ring structure -/

/-- The set of `D H₀`-linear combinations of the coset representatives. -/
def spanSet (L : LinnellDatum K G U) (H₀ H : Subgroup G) : Set U :=
  {x | ∃ c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀), x = xspan L c}

lemma zero_mem_spanSet (L : LinnellDatum K G U) : (0 : U) ∈ spanSet L H₀ H :=
  ⟨0, (xspan_zero L).symm⟩

lemma add_mem_spanSet (L : LinnellDatum K G U) {x y : U} (hx : x ∈ spanSet L H₀ H)
    (hy : y ∈ spanSet L H₀ H) : x + y ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨c', rfl⟩ := hy
  exact ⟨c + c', (xspan_add L c c').symm⟩

lemma smul_mem_spanSet (L : LinnellDatum K G U) (d : ↥(L.D H₀)) {x : U}
    (hx : x ∈ spanSet L H₀ H) : (d : U) * x ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨d • c, (xspan_smul L d c).symm⟩

lemma neg_mem_spanSet (L : LinnellDatum K G U) {x : U} (hx : x ∈ spanSet L H₀ H) :
    -x ∈ spanSet L H₀ H := by
  have h := smul_mem_spanSet L (-1 : ↥(L.D H₀)) hx
  simpa using h

/-- Conjugation by a coset representative, as an element of `D H₀`. -/
def conjCoeff (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (q : H ⧸ H₀.subgroupOf H)
    (d : ↥(L.D H₀)) : ↥(L.D H₀) :=
  ⟨↑(L.gen ((Quotient.out q : H) : G)) * (d : U) * ↑((L.gen ((Quotient.out q : H) : G))⁻¹),
    L.conj_mem hH₀ hN (Quotient.out q) (d : U) d.2⟩

lemma repX_mul_conjCoeff (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (q : H ⧸ H₀.subgroupOf H)
    (d : ↥(L.D H₀)) :
    repX L q * (d : U) = (conjCoeff L hH₀ q d : U) * repX L q := by
  rw [show repX L q = (repXU L q : U) from rfl,
    show (conjCoeff L hH₀ q d : U) = ↑(repXU L q) * (d : U) * ↑((repXU L q)⁻¹) from rfl]
  rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

lemma out_one_mem : (Quotient.out (1 : H ⧸ H₀.subgroupOf H) : H) ∈ H₀.subgroupOf H := by
  rw [← QuotientGroup.eq_one_iff]
  exact QuotientGroup.out_eq' 1

lemma one_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) : (1 : U) ∈ spanSet L H₀ H := by
  classical
  have hmem : (Quotient.out (1 : H ⧸ H₀.subgroupOf H))⁻¹ ∈ H₀.subgroupOf H :=
    (H₀.subgroupOf H).inv_mem out_one_mem
  have he : (L.gen (((Quotient.out (1 : H ⧸ H₀.subgroupOf H))⁻¹ : H) : G) : U) ∈ L.D H₀ :=
    L.gen_mem H₀ ⟨_, hmem⟩
  have hunit : repXU L (1 : H ⧸ H₀.subgroupOf H)
      * L.gen (((Quotient.out (1 : H ⧸ H₀.subgroupOf H))⁻¹ : H) : G) = 1 := by
    rw [repXU, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one]
  have hone : (1 : U) = (conjCoeff L hH₀ (1 : H ⧸ H₀.subgroupOf H) ⟨_, he⟩ : U)
      * repX L (1 : H ⧸ H₀.subgroupOf H) := by
    rw [← repX_mul_conjCoeff L hH₀ (1 : H ⧸ H₀.subgroupOf H) ⟨_, he⟩]
    show (1 : U) = (repXU L (1 : H ⧸ H₀.subgroupOf H) : U)
        * (L.gen (((Quotient.out (1 : H ⧸ H₀.subgroupOf H))⁻¹ : H) : G) : U)
    rw [← Units.val_mul, hunit, Units.val_one]
  exact ⟨Finsupp.single 1 (conjCoeff L hH₀ (1 : H ⧸ H₀.subgroupOf H) ⟨_, he⟩),
    by rw [xspan_single]; exact hone⟩

lemma gen_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (h : H) :
    (L.gen (h : G) : U) ∈ spanSet L H₀ H := by
  classical
  set q : H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H) h with hq
  have hmem : (Quotient.out q)⁻¹ * h ∈ H₀.subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hq,
      QuotientGroup.mk'_apply]
    group
  have he : (L.gen (((Quotient.out q)⁻¹ * h : H) : G) : U) ∈ L.D H₀ :=
    L.gen_mem H₀ ⟨_, hmem⟩
  have hunit : repXU L q * L.gen (((Quotient.out q)⁻¹ * h : H) : G) = L.gen (h : G) := by
    rw [repXU, ← map_mul, ← Subgroup.coe_mul]
    rw [show (Quotient.out q * ((Quotient.out q)⁻¹ * h) : H) = h from by group]
  have hfac : (L.gen (h : G) : U) = (conjCoeff L hH₀ q ⟨_, he⟩ : U) * repX L q := by
    rw [← repX_mul_conjCoeff L hH₀ q ⟨_, he⟩]
    show (L.gen (h : G) : U)
        = (repXU L q : U) * (L.gen (((Quotient.out q)⁻¹ * h : H) : G) : U)
    rw [← Units.val_mul, hunit]
  exact ⟨Finsupp.single q (conjCoeff L hH₀ q ⟨_, he⟩), by rw [xspan_single]; exact hfac⟩

lemma algebraMap_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (k : K) :
    algebraMap K U k ∈ spanSet L H₀ H := by
  have h := smul_mem_spanSet L (⟨algebraMap K U k, L.algebraMap_mem H₀ k⟩ : ↥(L.D H₀))
    (one_mem_spanSet L hH₀)
  simpa using h

lemma mul_repX_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x : U}
    (hx : x ∈ spanSet L H₀ H) (q : H ⧸ H₀.subgroupOf H) : x * repX L q ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, zero_mul]; exact zero_mem_spanSet L
  · intro a b f ha hb ih
    rw [xspan_add, xspan_single, add_mul, mul_assoc, repX_mul]
    refine add_mem_spanSet L ?_ ih
    refine ⟨Finsupp.single (a * q)
      (b * ⟨(L.gen ((repDelta a q : H) : G) : U), L.gen_mem H₀ ⟨_, repDelta_mem a q⟩⟩), ?_⟩
    simp only [xspan_single, Subring.coe_mul, mul_assoc]

lemma mul_coeff_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x : U}
    (hx : x ∈ spanSet L H₀ H) (d : ↥(L.D H₀)) : x * (d : U) ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, zero_mul]; exact zero_mem_spanSet L
  · intro a b f ha hb ih
    rw [xspan_add, xspan_single, add_mul, mul_assoc, repX_mul_conjCoeff L hH₀ a d]
    refine add_mem_spanSet L ?_ ih
    refine ⟨Finsupp.single a (b * conjCoeff L hH₀ a d), ?_⟩
    simp only [xspan_single, Subring.coe_mul, mul_assoc]

lemma mul_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x y : U}
    (hx : x ∈ spanSet L H₀ H) (hy : y ∈ spanSet L H₀ H) : x * y ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hy
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, mul_zero]; exact zero_mem_spanSet L
  · intro a b f ha hb ih
    rw [xspan_add, xspan_single, mul_add, ← mul_assoc]
    refine add_mem_spanSet L ?_ ih
    exact mul_repX_mem_spanSet L hH₀ (mul_coeff_mem_spanSet L hH₀ hx b) a

/-- The subring of `U` generated by the spanning sums: `∑_q D H₀ · x_q`. -/
def spanSub (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) : Subring U where
  carrier := spanSet L H₀ H
  mul_mem' := fun hx hy => mul_mem_spanSet L hH₀ hx hy
  one_mem' := one_mem_spanSet L hH₀
  add_mem' := fun hx hy => add_mem_spanSet L hx hy
  zero_mem' := zero_mem_spanSet L
  neg_mem' := fun hx => neg_mem_spanSet L hx

lemma mem_spanSub_iff (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x : U} :
    x ∈ spanSub L hH₀ ↔ x ∈ spanSet L H₀ H := Iff.rfl

lemma D_le_spanSub (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) : L.D H₀ ≤ spanSub L hH₀ := by
  intro d hd
  have h1 : (d : U) * (1 : U) ∈ spanSet L H₀ H :=
    smul_mem_spanSet L ⟨d, hd⟩ (one_mem_spanSet L hH₀)
  rw [mul_one] at h1
  exact h1

lemma repX_mem_spanSub (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (q : H ⧸ H₀.subgroupOf H) :
    repX L q ∈ spanSub L hH₀ :=
  ⟨Finsupp.single q 1, by rw [xspan_single, Subring.coe_one, one_mul]⟩

/-- **The span is division closed in `U`.**

The span is a finitely generated module over the division ring `↥(L.D H₀)` (generated by the
finitely many coset representatives), and right multiplication by an element of the span is
`↥(L.D H₀)`-linear and injective, hence surjective: this is the standard argument showing that
`∑_q D H₀ · x_q` is closed under inverses in `U`.

The scalar structure is built by hand from the inclusion `↥(L.D H₀) → ↥(spanSub L hH₀)` rather
than through `moduleOfLe`, because `L.divisionRingOfTorsionFree` and the `Subring` structure of
`L.D H₀` give propositionally (but not definitionally) equal semiring structures; building the
module from a homomorphism elaborated in the presence of that division ring keeps the two
consistent, and all the element level computations below are done inside `U`. -/
theorem isDivisionClosed_spanSub (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H)
    (htf : IsMulTorsionFree H₀) (hfin : (H₀.subgroupOf H).FiniteIndex) :
    IsDivisionClosed (spanSub L hH₀) := by
  classical
  letI : DivisionRing ↥(L.D H₀) := L.divisionRingOfTorsionFree htf
  let incl : ↥(L.D H₀) →+* ↥(spanSub L hH₀) :=
    { toFun := fun d => ⟨(d : U), D_le_spanSub L hH₀ d.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun d d' => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun d d' => Subtype.ext rfl }
  letI : Module ↥(L.D H₀) ↥(spanSub L hH₀) := Module.compHom ↥(spanSub L hH₀) incl
  haveI : (H₀.subgroupOf H).FiniteIndex := hfin
  haveI : Fintype (H ⧸ H₀.subgroupOf H) := Fintype.ofFinite _
  let g : (H ⧸ H₀.subgroupOf H) → ↥(spanSub L hH₀) :=
    fun q => ⟨repX L q, repX_mem_spanSub L hH₀ q⟩
  have hcoe_sum : ∀ v : (H ⧸ H₀.subgroupOf H) → ↥(L.D H₀),
      (↑(∑ q, v q • g q) : U) = ∑ q, (v q : U) * repX L q := fun v => by
    rw [show (↑(∑ q, v q • g q) : U) = ∑ q, ((v q • g q : ↥(spanSub L hH₀)) : U)
        from map_sum (Subring.subtype (spanSub L hH₀)) _ _]
    exact Finset.sum_congr rfl (fun q _ => rfl)
  have hsmul : ∀ (d : ↥(L.D H₀)) (m : ↥(spanSub L hH₀)),
      ((d • m : ↥(spanSub L hH₀)) : U) = (d : U) * (m : U) := fun d m => rfl
  haveI hFD : Module.Finite ↥(L.D H₀) ↥(spanSub L hH₀) := by
    let φ : ((H ⧸ H₀.subgroupOf H) → ↥(L.D H₀)) →ₗ[↥(L.D H₀)] ↥(spanSub L hH₀) :=
      { toFun := fun v => ∑ q, v q • g q
        map_add' := fun a b => by
          apply Subtype.ext
          rw [Subring.coe_add, hcoe_sum (a + b), hcoe_sum a, hcoe_sum b]
          have h1 : (∑ q, (↑((a + b) q) : U) * repX L q)
              = ∑ q, ((↑(a q) : U) * repX L q + (↑(b q) : U) * repX L q) :=
            Finset.sum_congr rfl (fun q _ => by
              show (↑((a + b) q) : U) * repX L q
                = (↑(a q) : U) * repX L q + (↑(b q) : U) * repX L q
              rw [show (↑((a + b) q) : U) = (↑(a q) : U) + (↑(b q) : U) from rfl, add_mul])
          rw [h1, Finset.sum_add_distrib]
        map_smul' := fun d a => by
          apply Subtype.ext
          show (↑(∑ q, (fun q => d • a q) q • g q) : U) = ↑(d • ∑ q, a q • g q)
          rw [hcoe_sum (fun q => d • a q), hsmul d (∑ q, a q • g q), hcoe_sum a, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun q _ => by
            show (d : U) * (a q : U) * repX L q = (d : U) * ((a q : U) * repX L q)
            rw [mul_assoc]) }
    have hsurj : Function.Surjective φ := by
      intro m
      obtain ⟨c, hc⟩ := m.2
      refine ⟨fun q => c q, ?_⟩
      apply Subtype.ext
      show (↑(∑ q, (fun q => c q) q • g q) : U) = ↑m
      rw [hcoe_sum (fun q => c q), hc, xspan, Finsupp.sum_fintype _ _ (by intro q; simp)]
    exact Module.Finite.of_surjective φ hsurj
  intro x hx y hxy
  let θ : ↥(spanSub L hH₀) →ₗ[↥(L.D H₀)] ↥(spanSub L hH₀) :=
    { toFun := fun m => m * ⟨x, hx⟩
      map_add' := fun m n => by
        apply Subtype.ext
        show ((m : U) + (n : U)) * x = (m : U) * x + (n : U) * x
        rw [add_mul]
      map_smul' := fun d m => by
        apply Subtype.ext
        show (d : U) * (m : U) * x = (d : U) * ((m : U) * x)
        rw [mul_assoc] }
  have hinj : Function.Injective θ := by
    intro m n hmn
    have hmn' : m * (⟨x, hx⟩ : ↥(spanSub L hH₀)) = n * ⟨x, hx⟩ := hmn
    have h : (m - n) * ⟨x, hx⟩ = 0 := by rw [sub_mul, hmn', sub_self]
    have hU : ((m : U) - (n : U)) * x = 0 := by
      have h' := congrArg (fun z : ↥(spanSub L hH₀) => (z : U)) h
      rw [Subring.coe_zero] at h'
      exact h'
    have hzero : (m : U) - (n : U) = 0 := by
      have h1 : ((m : U) - (n : U)) * (x * y) = 0 := by rw [← mul_assoc, hU, zero_mul]
      rwa [hxy, mul_one] at h1
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have hsurj : Function.Surjective θ := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨m, hm⟩ := hsurj 1
  have hm' : (m : U) * x = 1 := by
    have h' := congrArg (fun z : ↥(spanSub L hH₀) => (z : U)) hm
    rw [Subring.coe_one] at h'
    exact h'
  have hy : y = (m : U) := by
    calc y = 1 * y := (one_mul y).symm
      _ = ((m : U) * x) * y := by rw [hm']
      _ = (m : U) * (x * y) := by rw [mul_assoc]
      _ = (m : U) * 1 := by rw [hxy]
      _ = m := mul_one _
  rw [hy]
  exact m.2


theorem existsUnique_coset_rep {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) {G' : Subgroup G}
    (hG'n : G'.Normal) (htf : IsMulTorsionFree G') (hfin : G'.FiniteIndex) {H : Subgroup G}
    (hG'H : G' ≤ H) :
    ∀ y ∈ L.D H, ∃! c : (H ⧸ G'.subgroupOf H) →₀ ↥(L.D G'),
      y = c.sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) := by
  intro y hy
  haveI hN' : (G'.subgroupOf H).Normal := hG'n.subgroupOf H
  haveI hDR : DivisionRing ↥(L.D G') := L.divisionRingOfTorsionFree htf
  haveI : G'.FiniteIndex := hfin
  have hfi : (G'.subgroupOf H).FiniteIndex := inferInstance
  -- `D H` is contained in the span
  have hle : L.D H ≤ spanSub L hG'H :=
    L.minimal H (spanSub L hG'H) (fun h => (mem_spanSub_iff L hG'H).mpr (gen_mem_spanSet L hG'H h))
      (fun k => (mem_spanSub_iff L hG'H).mpr (algebraMap_mem_spanSet L hG'H k))
      (isDivisionClosed_spanSub L hG'H htf hfi)
  obtain ⟨c, hc⟩ := (mem_spanSub_iff L hG'H).mp (hle hy)
  refine ⟨c, ?_, ?_⟩
  · -- existence
    simpa only [xspan, repX, repXU] using hc
  · -- uniqueness
    intro c' hc'
    have hcS : y = c.sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) := by
      simpa only [xspan, repX, repXU] using hc
    have hsum : (c' - c).sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) = 0 := by
      rw [Finsupp.sum_sub_index
        (by intro a b₁ b₂
            show ((b₁ - b₂ : ↥(L.D G')) : U) * (L.gen ((Quotient.out a : H) : G) : U)
              = (b₁ : U) * (L.gen ((Quotient.out a : H) : G) : U)
                - (b₂ : U) * (L.gen ((Quotient.out a : H) : G) : U)
            rw [show ((b₁ - b₂ : ↥(L.D G')) : U) = (b₁ : U) - (b₂ : U) from rfl, sub_mul])]
      rw [← hc', ← hcS, sub_self]
    exact sub_eq_zero.mp
      (Work.ORLinnell.FiniteIndex.eq_zero_of_sum_transversal L hG'H hN' (c' - c) hsum)

end Work.ORLinnell.Cosets

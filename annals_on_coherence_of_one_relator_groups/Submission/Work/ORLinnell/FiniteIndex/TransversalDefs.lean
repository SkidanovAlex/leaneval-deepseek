import Mathlib
import Submission.Work.ORLinnell.Linnell

/-!
# The finite index decomposition `D H = ∑_{q ∈ H/H₀} D H₀ · x_q`: ring theoretic part

For a Linnell datum `L : LinnellDatum K G U` and subgroups `H₀ ≤ H` of `G` with `H₀` normal in `H`,
this file builds the ring `spanSub L hH₀ = ∑_{q} (L.D H₀) · x_q` of all finite sums
`∑_q d_q * x_q` (`q` running over the cosets `H/H₀`, `x_q` the image of `Quotient.out q`), and
shows that it contains `L.D H₀`, the image of `K` and all the units `gen h` (`h : H`).

The remaining step of the decomposition `D H = ∑_q D H₀ x_q` is that `spanSub L hH₀` is
*division closed* in `U`, i.e. closed under inverses in `U`.  This is where the hypothesis that
`L.D H₀` is a division ring is used: the argument shows that for `a ∈ spanSub` with `a * y = 1`,
the map `z ↦ z * a` on `spanSub` is an injective `L.D H₀`-linear endomorphism of the
finite dimensional space `spanSub`, hence surjective, which produces the (unique) right inverse
of `a` inside `spanSub`.  Note that this needs the scalar structure on `L.D H₀` to be the one
induced by `U` (left multiplication in `U` is `U`-linear but it is `L.D H₀`-linear only for the
*subring* structure of `L.D H₀`), so the usable form of the hypothesis is
`∀ x ∈ (L.D H₀ : Set U), x ≠ 0 → ∃ u ∈ (L.D H₀ : Set U), u * x = 1 ∧ x * u = 1`
(or `L.divisionOfTorsionFree` when `H₀` is torsion free).
-/

noncomputable section

namespace Work.ORLinnell.FiniteIndex

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-! ## Coset representatives -/

/-- The chosen representative of the coset `q ∈ H ⧸ H₀` as a unit of `U`. -/
def cosetXU (L : LinnellDatum K G U) {H₀ H : Subgroup G} (q : H ⧸ H₀.subgroupOf H) : Uˣ :=
  L.gen ((Quotient.out q : H) : G)

/-- The chosen representative of the coset `q ∈ H ⧸ H₀` as an element of `U`. -/
def cosetX (L : LinnellDatum K G U) {H₀ H : Subgroup G} (q : H ⧸ H₀.subgroupOf H) : U :=
  (cosetXU L q : U)

variable {H₀ H : Subgroup G}

lemma out_coe (q : H ⧸ H₀.subgroupOf H) : (↑(Quotient.out q) : H ⧸ H₀.subgroupOf H) = q :=
  Quotient.out_eq q

section Coset

variable [hN : (H₀.subgroupOf H).Normal]

lemma mk_mul_coe (a b : H) : (↑(a * b) : H ⧸ H₀.subgroupOf H) = ↑a * ↑b := by
  simp

/-- The defining relation of the coset representatives: `out (q * q')` and `out q * out q'`
differ by an element of `H₀`. -/
lemma out_inv_mul_out_mem (q q' : H ⧸ H₀.subgroupOf H) :
    (Quotient.out (q * q'))⁻¹ * (Quotient.out q * Quotient.out q') ∈ H₀.subgroupOf H := by
  rw [← QuotientGroup.eq (a := Quotient.out (q * q')) (b := Quotient.out q * Quotient.out q')]
  show (Quotient.mk'' (Quotient.out (q * q')) : H ⧸ H₀.subgroupOf H) =
    (Quotient.mk'' (Quotient.out q * Quotient.out q') : H ⧸ H₀.subgroupOf H)
  rw [Quotient.out_eq']
  simp

/-- The factorisation of a product of two coset representatives by the representative of the
product coset. -/
lemma cosetXU_mul_eq (L : LinnellDatum K G U) (q q' : H ⧸ H₀.subgroupOf H) :
    cosetXU L q * cosetXU L q' = cosetXU L (q * q') *
      L.gen ((Quotient.out (q * q'))⁻¹ * (Quotient.out q * Quotient.out q') : H) := by
  simp only [cosetXU]
  rw [← map_mul, ← map_mul]
  exact congrArg L.gen (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)

/-- The same factorisation, in `U`. -/
lemma cosetX_mul_eq (L : LinnellDatum K G U) (q q' : H ⧸ H₀.subgroupOf H) :
    cosetX L q * cosetX L q' = cosetX L (q * q') *
      (L.gen ((Quotient.out (q * q'))⁻¹ * (Quotient.out q * Quotient.out q') : H) : U) := by
  simp only [cosetX]
  rw [← Units.val_mul]
  exact congrArg (fun u : Uˣ => (u : U)) (cosetXU_mul_eq L q q')

/-- The twist factor `alpha q q' ∈ D H₀` with `cosetX q * cosetX q' = alpha q q' * cosetX (q*q')`. -/
def alpha (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H)
    (q q' : H ⧸ H₀.subgroupOf H) : ↥(L.D H₀) :=
  ⟨cosetX L q * cosetX L q' * ↑((cosetXU L (q * q'))⁻¹), by
    have hg : (L.gen ((Quotient.out (q * q'))⁻¹ * (Quotient.out q * Quotient.out q') : H) :
        U) ∈ L.D H₀ := L.gen_mem H₀ ⟨_, out_inv_mul_out_mem q q'⟩
    have h1 : cosetX L q * cosetX L q' = cosetX L (q * q') *
        (L.gen ((Quotient.out (q * q'))⁻¹ * (Quotient.out q * Quotient.out q') : H) : U) :=
      cosetX_mul_eq L q q'
    rw [h1]
    exact L.conj_mem (H₀ := H₀) (H := H) hH₀ hN (Quotient.out (q * q')) _ hg⟩

/-- The multiplication rule for the coset representatives. -/
lemma cosetX_mul_alpha (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H)
    (q q' : H ⧸ H₀.subgroupOf H) :
    cosetX L q * cosetX L q' = (alpha L hH₀ q q' : U) * cosetX L (q * q') := by
  have hcoe : (alpha L hH₀ q q' : U) =
      cosetX L q * cosetX L q' * ↑((cosetXU L (q * q'))⁻¹) := rfl
  rw [hcoe]
  simp only [cosetX, ← Units.val_mul]
  congr 1
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Conjugation by the coset representative `cosetX q` preserves `D H₀`. -/
def conjCoeff (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H)
    (q : H ⧸ H₀.subgroupOf H) (d : ↥(L.D H₀)) : ↥(L.D H₀) :=
  ⟨cosetX L q * (d : U) * ↑((cosetXU L q)⁻¹), by
    exact L.conj_mem (H₀ := H₀) (H := H) hH₀ hN (Quotient.out q) (d : U) d.2⟩

lemma conjCoeff_coe (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H)
    (q : H ⧸ H₀.subgroupOf H) (d : ↥(L.D H₀)) :
    (conjCoeff L hH₀ q d : U) = cosetX L q * (d : U) * ↑((cosetXU L q)⁻¹) := rfl

/-- Right multiplication by `d ∈ D H₀` in terms of the coset representative. -/
lemma cosetX_mul_coeff (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H)
    (q : H ⧸ H₀.subgroupOf H) (d : ↥(L.D H₀)) :
    cosetX L q * (d : U) = (conjCoeff L hH₀ q d : U) * cosetX L q := by
  have hcoe : (conjCoeff L hH₀ q d : U) =
      cosetX L q * (d : U) * ↑((cosetXU L q)⁻¹) := rfl
  rw [hcoe, cosetX, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end Coset

/-! ## The spanning sums -/

/-- The element `∑_q c_q * cosetX q` of `U`. -/
def xspan (L : LinnellDatum K G U) (c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) : U :=
  c.sum (fun q d => (d : U) * cosetX L q)

lemma xspan_zero (L : LinnellDatum K G U) :
    xspan L (0 : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) = 0 := by
  rw [xspan, Finsupp.sum_zero_index]

lemma xspan_add (L : LinnellDatum K G U) (c c' : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) :
    xspan L (c + c') = xspan L c + xspan L c' := by
  classical
  rw [xspan, xspan, xspan, Finsupp.sum_add_index]
  · intro a _
    simp
  · intro a _ b₁ b₂
    rw [Subring.coe_add, add_mul]

lemma xspan_single (L : LinnellDatum K G U) (q : H ⧸ H₀.subgroupOf H) (d : ↥(L.D H₀)) :
    xspan L (Finsupp.single q d) = (d : U) * cosetX L q := by
  rw [xspan, Finsupp.sum_single_index]
  simp

lemma xspan_of_fintype (L : LinnellDatum K G U) [Fintype (H ⧸ H₀.subgroupOf H)]
    (c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) :
    xspan L c = ∑ q, (c q : U) * cosetX L q := by
  rw [xspan, Finsupp.sum_fintype]
  intro i
  simp

/-- Scalar multiplication of the spanning sums. -/
lemma xspan_smul (L : LinnellDatum K G U) (d : ↥(L.D H₀))
    (c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀)) :
    xspan L (d • c) = (d : U) * xspan L c := by
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [smul_zero, xspan_zero, mul_zero]
  · intro a b f _ _ ih
    have h1 : xspan L (d • f) = (d : U) * xspan L f := ih
    calc xspan L (d • (Finsupp.single a b + f))
        = xspan L (d • Finsupp.single a b + d • f) := by rw [smul_add]
      _ = xspan L (Finsupp.single a (d * b) + d • f) := by
            rw [Finsupp.smul_single, smul_eq_mul]
      _ = xspan L (Finsupp.single a (d * b)) + xspan L (d • f) := by rw [xspan_add]
      _ = (d : U) * (b : U) * cosetX L a + (d : U) * xspan L f := by
            rw [xspan_single, h1, Subring.coe_mul]
      _ = (d : U) * xspan L (Finsupp.single a b + f) := by
            rw [xspan_add, xspan_single, mul_add, mul_assoc]

/-! ## The carrier set -/

/-- The set of `D H₀`-linear combinations of the coset representatives. -/
def spanSet (L : LinnellDatum K G U) (H₀ H : Subgroup G) : Set U :=
  {x | ∃ c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀), x = xspan L c}

lemma zero_mem_spanSet (L : LinnellDatum K G U) : (0 : U) ∈ spanSet L H₀ H :=
  ⟨0, (xspan_zero (H₀ := H₀) (H := H) L).symm⟩

lemma add_mem_spanSet (L : LinnellDatum K G U) {x y : U} (hx : x ∈ spanSet L H₀ H)
    (hy : y ∈ spanSet L H₀ H) : x + y ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨c', rfl⟩ := hy
  exact ⟨c + c', (xspan_add L c c').symm⟩

lemma smul_mem_spanSet (L : LinnellDatum K G U) (d : ↥(L.D H₀)) {x : U}
    (hx : x ∈ spanSet L H₀ H) : (d : U) * x ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, mul_zero]
    exact zero_mem_spanSet (H₀ := H₀) (H := H) L
  · intro a b f _ _ ih
    rw [xspan_add, xspan_single, mul_add]
    refine add_mem_spanSet L ?_ ih
    exact ⟨Finsupp.single a (d * b), by rw [xspan_single, Subring.coe_mul, mul_assoc]⟩

lemma neg_mem_spanSet (L : LinnellDatum K G U) {x : U} (hx : x ∈ spanSet L H₀ H) :
    -x ∈ spanSet L H₀ H := by
  have h : -x = ((-1 : ↥(L.D H₀)) : U) * x := by
    rw [Subring.coe_neg, Subring.coe_one, neg_one_mul]
  rw [h]
  exact smul_mem_spanSet L (-1) hx

/-- A single coset representative lies in the span. -/
lemma cosetX_mem_spanSet (L : LinnellDatum K G U) (q : H ⧸ H₀.subgroupOf H) :
    cosetX L q ∈ spanSet L H₀ H :=
  ⟨Finsupp.single q 1, by rw [xspan_single, Subring.coe_one, one_mul]⟩

section Normality

variable [hN : (H₀.subgroupOf H).Normal]

/-- Right multiplication by a single coset representative. -/
lemma mul_cosetX_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x : U}
    (hx : x ∈ spanSet L H₀ H) (q : H ⧸ H₀.subgroupOf H) :
    x * cosetX L q ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, zero_mul]
    exact zero_mem_spanSet (H₀ := H₀) (H := H) L
  · intro a b f _ _ ih
    rw [xspan_add, xspan_single, add_mul]
    refine add_mem_spanSet L ?_ ih
    refine ⟨Finsupp.single (a * q) (b * alpha L hH₀ a q), ?_⟩
    rw [xspan_single]
    calc (↑b : U) * cosetX L a * cosetX L q
        = ↑b * (cosetX L a * cosetX L q) := by rw [mul_assoc]
      _ = ↑b * ((alpha L hH₀ a q : U) * cosetX L (a * q)) := by
            rw [cosetX_mul_alpha L hH₀ a q]
      _ = (↑b * (alpha L hH₀ a q : U)) * cosetX L (a * q) := by rw [mul_assoc]
      _ = (↑(b * alpha L hH₀ a q) : U) * cosetX L (a * q) := by rw [Subring.coe_mul]

/-- Right multiplication by an element of `D H₀`. -/
lemma mul_coeff_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x : U}
    (hx : x ∈ spanSet L H₀ H) (d : ↥(L.D H₀)) : x * (d : U) ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hx
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, zero_mul]
    exact zero_mem_spanSet (H₀ := H₀) (H := H) L
  · intro a b f _ _ ih
    rw [xspan_add, xspan_single, add_mul]
    refine add_mem_spanSet L ?_ ih
    refine ⟨Finsupp.single a (b * conjCoeff L hH₀ a d), ?_⟩
    rw [xspan_single, mul_assoc, cosetX_mul_coeff L hH₀ a d, ← mul_assoc, ← Subring.coe_mul]

/-- Multiplication of two elements of the span. -/
lemma mul_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x y : U}
    (hx : x ∈ spanSet L H₀ H) (hy : y ∈ spanSet L H₀ H) : x * y ∈ spanSet L H₀ H := by
  obtain ⟨c, rfl⟩ := hy
  classical
  refine Finsupp.induction c ?_ ?_
  · rw [xspan_zero, mul_zero]
    exact zero_mem_spanSet (H₀ := H₀) (H := H) L
  · intro a b f _ _ ih
    rw [xspan_add, xspan_single, mul_add]
    refine add_mem_spanSet L ?_ ih
    rw [← mul_assoc]
    exact mul_cosetX_mem_spanSet L hH₀ (mul_coeff_mem_spanSet L hH₀ hx b) a

/-- The coset representative of the identity coset lies in `H₀`. -/
lemma out_mk_one_mem : (Quotient.out (QuotientGroup.mk' (H₀.subgroupOf H) (1 : H)) : H)
    ∈ H₀.subgroupOf H := by
  have h : (↑(Quotient.out (QuotientGroup.mk' (H₀.subgroupOf H) (1 : H))) :
      H ⧸ H₀.subgroupOf H) = (↑(1 : H) : H ⧸ H₀.subgroupOf H) := by
    rw [out_coe, QuotientGroup.mk'_apply]
  have hmem : (Quotient.out (QuotientGroup.mk' (H₀.subgroupOf H) (1 : H)))⁻¹ * 1
      ∈ H₀.subgroupOf H := QuotientGroup.eq.mp h
  simpa using (H₀.subgroupOf H).inv_mem hmem

lemma one_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) : (1 : U) ∈ spanSet L H₀ H := by
  classical
  set q : H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H) (1 : H) with hq
  have hmem : (Quotient.out q : H) ∈ H₀.subgroupOf H := out_mk_one_mem (H₀ := H₀) (H := H)
  refine ⟨Finsupp.single q ⟨↑((cosetXU L q)⁻¹), ?_⟩, ?_⟩
  · refine L.isDivisionClosed H₀ (cosetXU L q : U) ?_ ↑((cosetXU L q)⁻¹) ?_
    · exact L.gen_mem H₀ ⟨(Quotient.out q : H), hmem⟩
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [xspan_single, cosetX, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- `D H₀` is contained in the span. -/
lemma D_le_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (d : ↥(L.D H₀)) :
    (d : U) ∈ spanSet L H₀ H := by
  have h : (d : U) = (d : U) * 1 := (mul_one _).symm
  rw [h]
  exact smul_mem_spanSet L d (one_mem_spanSet L hH₀)

/-- The image of `H` is contained in the span. -/
lemma gen_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (h : H) :
    (L.gen (h : G) : U) ∈ spanSet L H₀ H := by
  classical
  set q : H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H) h with hq
  have hcoe : (↑(Quotient.out q) : H ⧸ H₀.subgroupOf H) = ↑h := by
    rw [out_coe, hq, QuotientGroup.mk'_apply]
  have hmem : (Quotient.out q)⁻¹ * h ∈ H₀.subgroupOf H := QuotientGroup.eq.mp hcoe
  have hfac : (L.gen (h : G) : U) = cosetX L q *
      (L.gen (((Quotient.out q)⁻¹ * h : H) : G) : U) := by
    rw [cosetX, cosetXU, ← Units.val_mul, ← map_mul]
    congr 1
    rw [← Subgroup.coe_mul]
    congr 1
    group
  rw [hfac]
  exact mul_coeff_mem_spanSet L hH₀ (cosetX_mem_spanSet L q)
    ⟨(L.gen (((Quotient.out q)⁻¹ * h : H) : G) : U), L.gen_mem H₀ ⟨_, hmem⟩⟩

/-- The image of `K` is contained in the span. -/
lemma algebraMap_mem_spanSet (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) (k : K) :
    algebraMap K U k ∈ spanSet L H₀ H := by
  have h : algebraMap K U k = algebraMap K U k * 1 := (mul_one _).symm
  rw [h]
  exact smul_mem_spanSet L ⟨algebraMap K U k, L.algebraMap_mem H₀ k⟩ (one_mem_spanSet L hH₀)

/-! ## The subring of spanning sums -/

/-- The subring of `U` consisting of the sums `∑_q d_q * x_q`, `d_q ∈ D H₀`. -/
def spanSub (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) : Subring U where
  carrier := spanSet L H₀ H
  mul_mem' := fun hx hy => mul_mem_spanSet L hH₀ hx hy
  one_mem' := one_mem_spanSet L hH₀
  add_mem' := fun hx hy => add_mem_spanSet L hx hy
  zero_mem' := zero_mem_spanSet (H₀ := H₀) (H := H) L
  neg_mem' := fun hx => neg_mem_spanSet L hx

lemma mem_spanSub_iff (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) {x : U} :
    x ∈ spanSub L hH₀ ↔ x ∈ spanSet L H₀ H :=
  Iff.rfl

/-- `D H₀ ≤ spanSub L`. -/
lemma D_le_spanSub (L : LinnellDatum K G U) (hH₀ : H₀ ≤ H) : L.D H₀ ≤ spanSub L hH₀ :=
  fun _ hd => D_le_spanSet L hH₀ ⟨_, hd⟩

end Normality

end Work.ORLinnell.FiniteIndex

import Mathlib
import Submission.Work.ORLinnell.Linnell
import Submission.Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex

/-!
# Semisimplicity of the division closures `D H` (L1 of the torsion case)

If `G' ⊴ G` is torsion free of finite index, then for *every* subgroup `H ≤ G` the division
closure `D H` of `K[H]` in `U(G)` is a semisimple ring.

The proof reduces to the finite index case `H₀ := H ⊓ G'`: this subgroup is normal in `H` of
finite index and torsion free, so `D H₀` is a division ring and a Maschke-type averaging
argument (`isSemisimpleRing_of_groupLike_units` below) applies, using the spanning of `D H`
over `D H₀` by the coset representatives (`span_D_transversal`).
-/

namespace Work.ORLinnell.Cosets

open Work.ORLinnell

/-- **Maschke's theorem for a group-like family of units.**  Let `φ : Da →+* Ra` be a ring
homomorphism from a division ring `Da` into a ring `Ra`, let `u : ι → Raˣ` be a finite family of
units, and let `c : Ra` be a central two-sided inverse of `Fintype.card ι`.  Assume

* every element of `Ra` is a finite `Da`-linear combination of the `u i` (coefficients on the
  left);
* conjugation by each `u i` preserves the image of `Da`;
* right multiplication by each `u j` permutes the family `u` up to `φ`-scalars.

Then `Ra` is a semisimple ring. -/
theorem isSemisimpleRing_of_groupLike_units {Da Ra : Type*} [DivisionRing Da] [Ring Ra]
    (φ : Da →+* Ra) {ι : Type*} [Fintype ι] (u : ι → Raˣ) (c : Ra)
    (hc : c * (Fintype.card ι : Ra) = 1) (hc_central : ∀ x : Ra, c * x = x * c)
    (hspan : ∀ a : Ra, ∃ d : ι →₀ Da, a = ∑ i : ι, φ (d i) * (u i : Ra))
    (hconj : ∀ (i : ι) (a : Da), ∃ a' : Da, φ a' = (u i : Ra) * φ a * ↑((u i)⁻¹))
    (hmul : ∀ j : ι, ∃ (σ : ι ≃ ι) (e : ι → Da),
        ∀ i : ι, (u i : Ra) * (u j : Ra) = φ (e i) * (u (σ i) : Ra)) :
    IsSemisimpleRing Ra := by
  classical
  letI : Module Da Ra := Module.compHom Ra φ
  haveI hST : IsScalarTower Da Ra Ra := ⟨fun d r m => mul_assoc _ _ _⟩
  have hsmul : ∀ (d : Da) (x : Ra), d • x = φ d * x := fun _ _ => rfl
  refine { exists_isCompl := fun I => ?_ }
  let J : Submodule Da Ra := I.restrictScalars Da
  let inc : Ra →ₗ[Da] Ra := (Submodule.subtype J) ∘ₗ (Submodule.subtype J).leftInverse
  have hinc_mem : ∀ x : Ra, inc x ∈ I := fun x => ((Submodule.subtype J).leftInverse x).2
  have hp : ∀ v : Ra, v ∈ I → inc v = v := by
    intro v hv
    have hmem : v ∈ J := hv
    have h1 := LinearMap.leftInverse_apply_of_inj (Submodule.ker_subtype J) (⟨v, hmem⟩ : ↥J)
    simpa [inc] using congrArg (Submodule.subtype J) h1
  let pfA : Ra →+ Ra :=
    { toFun := fun m => c * ∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m)
      map_zero' := by simp
      map_add' := fun a b => by
        have h : (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * (a + b)))
            = (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * a))
              + (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * b)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [mul_add, map_add, mul_add]
        rw [h, mul_add] }
  have hinv_mul : ∀ i : ι, (↑((u i)⁻¹) : Ra) * (u i : Ra) = 1 := fun i => by
    have h : ((u i)⁻¹ * (u i) : Raˣ) = 1 := inv_mul_cancel (u i)
    simpa using congrArg (fun z : Raˣ => (z : Ra)) h
  have hmul_inv : ∀ i : ι, (u i : Ra) * (↑((u i)⁻¹) : Ra) = 1 := fun i => by
    have h : ((u i) * (u i)⁻¹ : Raˣ) = 1 := mul_inv_cancel (u i)
    simpa using congrArg (fun z : Raˣ => (z : Ra)) h
  have hpf_φ : ∀ (d : Da) (m : Ra), pfA (φ d * m) = φ d * pfA m := by
    intro d m
    have hterm : ∀ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * (φ d * m))
        = φ d * ((↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m)) := by
      intro i
      obtain ⟨d', hd'⟩ := hconj i d
      have h2 : (u i : Ra) * φ d = φ d' * (u i : Ra) := by
        rw [hd', mul_assoc, hinv_mul i, mul_one]
      have h1 : (u i : Ra) * (φ d * m) = φ d' * ((u i : Ra) * m) := by
        rw [← mul_assoc, h2, mul_assoc]
      have h3 : (↑((u i)⁻¹) : Ra) * φ d' = φ d * (↑((u i)⁻¹) : Ra) := by
        rw [hd']
        rw [← mul_assoc, ← mul_assoc, hinv_mul i, one_mul]
      rw [h1, ← hsmul d' ((u i : Ra) * m), map_smul, hsmul d' (inc ((u i : Ra) * m)),
        ← mul_assoc, h3, mul_assoc]
    have hsum : (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * (φ d * m)))
        = φ d * ∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    show c * (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * (φ d * m)))
        = φ d * (c * ∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m))
    rw [hsum, ← mul_assoc, hc_central (φ d), mul_assoc]
  have hpf_u : ∀ (j : ι) (m : Ra), pfA ((u j : Ra) * m) = (u j : Ra) * pfA m := by
    intro j m
    obtain ⟨σ, e, he⟩ := hmul j
    have hterm : ∀ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * ((u j : Ra) * m))
        = (u j : Ra) * ((↑((u (σ i))⁻¹) : Ra) * inc ((u (σ i) : Ra) * m)) := by
      intro i
      have h4 : (↑((u i)⁻¹) : Ra) * φ (e i) * (u (σ i) : Ra) = (u j : Ra) := by
        rw [mul_assoc, ← he i, ← mul_assoc, hinv_mul i, one_mul]
      have h3 : (↑((u i)⁻¹) : Ra) * φ (e i) = (u j : Ra) * (↑((u (σ i))⁻¹) : Ra) := by
        have hh := congrArg (fun z : Ra => z * (↑((u (σ i))⁻¹) : Ra)) h4
        simpa [mul_assoc, hmul_inv] using hh
      have h1 : (u i : Ra) * ((u j : Ra) * m) = φ (e i) * ((u (σ i) : Ra) * m) := by
        rw [← mul_assoc, he i, mul_assoc]
      rw [h1, ← hsmul (e i) ((u (σ i) : Ra) * m), map_smul,
        hsmul (e i) (inc ((u (σ i) : Ra) * m)), ← mul_assoc, h3, mul_assoc]
    have hsum : (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * ((u j : Ra) * m)))
        = (u j : Ra) * ∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m) := by
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.mul_sum]
      exact Equiv.sum_comp σ
        (fun k => (u j : Ra) * ((↑((u k)⁻¹) : Ra) * inc ((u k : Ra) * m)))
    show c * (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * ((u j : Ra) * m)))
        = (u j : Ra) * (c * ∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m))
    rw [hsum, ← mul_assoc, hc_central (u j : Ra), mul_assoc]
  have hpf_smul : ∀ a m : Ra, pfA (a * m) = a * pfA m := by
    intro a m
    obtain ⟨d, hd⟩ := hspan a
    rw [hd, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_assoc, mul_assoc, ← hpf_u i m, ← hpf_φ (d i) ((u i : Ra) * m)]
  let pfLin : Ra →ₗ[Ra] Ra :=
    { toFun := pfA, map_add' := fun a b => map_add pfA a b,
      map_smul' := fun a m => hpf_smul a m }
  have hmem : ∀ m : Ra, pfLin m ∈ I := by
    intro m
    show c * (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * m)) ∈ I
    refine I.smul_mem c ?_
    refine I.sum_mem (fun i _ => ?_)
    exact I.smul_mem _ (hinc_mem _)
  have hid : ∀ v : ↥I, pfLin (v : Ra) = (v : Ra) := by
    intro v
    have hv : (v : Ra) ∈ I := v.2
    have hterm : ∀ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * (v : Ra)) = (v : Ra) := by
      intro i
      rw [hp ((u i : Ra) * (v : Ra)) (I.smul_mem (u i : Ra) hv), ← mul_assoc, hinv_mul i,
        one_mul]
    show c * (∑ i : ι, (↑((u i)⁻¹) : Ra) * inc ((u i : Ra) * (v : Ra))) = (v : Ra)
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← mul_assoc, hc, one_mul]
  exact ⟨LinearMap.ker (pfLin.codRestrict I hmem),
    LinearMap.isCompl_of_proj (f := pfLin.codRestrict I hmem) (fun v => Subtype.ext (hid v))⟩

variable {K : Type*} [Field K] [CharZero K] {G : Type*} [Group G] {U : Type*}
  [Ring U] [Nontrivial U] [Algebra K U]

/-- The finite index case of the semisimplicity statement, with the spanning hypothesis
(`span_D_transversal`) supplied as an argument.  The division ring structure on `D H₀` is built
explicitly from `IsMulTorsionFree H₀` so that it is *definitionally* the canonical one coming
from the subring structure. -/
theorem isSemisimpleRing_D_of_finiteIndex (L : LinnellDatum K G U) {H₀ H : Subgroup G}
    (hH₀ : H₀ ≤ H) (hN : (H₀.subgroupOf H).Normal) (hfin : (H₀.subgroupOf H).FiniteIndex)
    (htf : IsMulTorsionFree H₀)
    (hspan : ∀ y ∈ L.D H, ∃ c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀),
      y = c.sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U))) :
    IsSemisimpleRing ↥(L.D H) := by
  classical
  haveI hNinst : (H₀.subgroupOf H).Normal := hN
  haveI hFintype : Fintype (H ⧸ H₀.subgroupOf H) := Fintype.ofFinite _
  letI hDR : DivisionRing ↥(L.D H₀) :=
    DivisionRing.ofIsUnitOrEqZero fun x => by
      rcases eq_or_ne x 0 with h | h
      · exact Or.inr h
      · exact Or.inl (L.division_of_torsionFree H₀ htf x h)
  let u : (H ⧸ H₀.subgroupOf H) → (↥(L.D H))ˣ := fun q =>
    ⟨⟨(L.gen ((Quotient.out q : H) : G) : U), L.gen_mem H (Quotient.out q)⟩,
     ⟨(↑((L.gen ((Quotient.out q : H) : G))⁻¹) : U),
       L.isDivisionClosed H (L.gen ((Quotient.out q : H) : G) : U)
         (L.gen_mem H (Quotient.out q)) (↑((L.gen ((Quotient.out q : H) : G))⁻¹)) (by simp)⟩,
     Subtype.ext (by simp),
     Subtype.ext (by simp)⟩
  let c₀ : ↥(L.D H) :=
    ⟨algebraMap K U ((Fintype.card (H ⧸ H₀.subgroupOf H) : K))⁻¹, L.algebraMap_mem H _⟩
  refine isSemisimpleRing_of_groupLike_units (Da := ↥(L.D H₀)) (Ra := ↥(L.D H))
    (Subring.inclusion (L.D_mono hH₀)) u c₀ ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    have hne : ((Fintype.card (H ⧸ H₀.subgroupOf H) : K)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
    have hcast : ((Fintype.card (H ⧸ H₀.subgroupOf H) : ↥(L.D H)) : U)
        = algebraMap K U ((Fintype.card (H ⧸ H₀.subgroupOf H) : K)) :=
      (map_natCast (Subring.subtype (L.D H)) (Fintype.card (H ⧸ H₀.subgroupOf H))).trans
        (map_natCast (algebraMap K U) (Fintype.card (H ⧸ H₀.subgroupOf H))).symm
    rw [Subring.coe_mul, Subring.coe_one, hcast, ← map_mul, inv_mul_cancel₀ hne, map_one]
  · intro x
    apply Subtype.ext
    show (↑c₀ : U) * ↑x = ↑x * ↑c₀
    exact Algebra.commutes _ _
  · intro a
    obtain ⟨d, hd⟩ := hspan (a : U) a.2
    refine ⟨d, ?_⟩
    apply Subtype.ext
    change Subring.subtype (L.D H) a
      = Subring.subtype (L.D H)
          (∑ i : H ⧸ H₀.subgroupOf H,
            Subring.inclusion (L.D_mono hH₀) (d i) * (u i : ↥(L.D H)))
    have hd' : Subring.subtype (L.D H) a
        = d.sum (fun q e => (e : U) * (L.gen ((Quotient.out q : H) : G) : U)) := hd
    rw [map_sum (Subring.subtype (L.D H)), hd', Finsupp.sum_fintype]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul (Subring.subtype (L.D H))]
      rfl
    · intro i
      simp
  · intro i d
    refine ⟨⟨(L.gen ((Quotient.out i : H) : G) : U) * (d : U)
        * ↑((L.gen ((Quotient.out i : H) : G))⁻¹),
      L.conj_mem hH₀ hN (Quotient.out i) (d : U) d.2⟩, ?_⟩
    apply Subtype.ext
    rfl
  · intro j
    have hmem : ∀ i : (H ⧸ H₀.subgroupOf H),
        ((Quotient.out i * Quotient.out j) * (Quotient.out (i * j))⁻¹ : H)
          ∈ H₀.subgroupOf H := fun i => by
      have h1 : (Quotient.out (i * j))⁻¹ * (Quotient.out i * Quotient.out j)
          ∈ H₀.subgroupOf H := by
        rw [← QuotientGroup.eq (a := Quotient.out (i * j))
          (b := Quotient.out i * Quotient.out j)]
        show (Quotient.mk'' (Quotient.out (i * j)) : H ⧸ H₀.subgroupOf H) =
          (Quotient.mk'' (Quotient.out i * Quotient.out j) : H ⧸ H₀.subgroupOf H)
        rw [Quotient.out_eq']
        simp
      have h2 := hNinst.conj_mem ((Quotient.out (i * j))⁻¹ * (Quotient.out i * Quotient.out j))
        h1 (Quotient.out i * Quotient.out j)
      simpa [mul_assoc] using h2
    refine ⟨(Equiv.mulRight j : (H ⧸ H₀.subgroupOf H) ≃ (H ⧸ H₀.subgroupOf H)),
      fun i => ⟨(L.gen (((Quotient.out i * Quotient.out j) * (Quotient.out (i * j))⁻¹ : H) : G) : U),
        L.gen_mem H₀ ⟨(((Quotient.out i * Quotient.out j) * (Quotient.out (i * j))⁻¹ : H) : G),
          hmem i⟩⟩, fun i => ?_⟩
    show (u i : ↥(L.D H)) * (u j : ↥(L.D H))
      = (Subring.inclusion (L.D_mono hH₀)
          ⟨(L.gen (((Quotient.out i * Quotient.out j) * (Quotient.out (i * j))⁻¹ : H) : G) : U),
            L.gen_mem H₀ ⟨(((Quotient.out i * Quotient.out j) * (Quotient.out (i * j))⁻¹ : H) : G),
              hmem i⟩⟩) * (u ((Equiv.mulRight j : (H ⧸ H₀.subgroupOf H) ≃ (H ⧸ H₀.subgroupOf H)) i) : ↥(L.D H))
    rw [show (Equiv.mulRight j : (H ⧸ H₀.subgroupOf H) ≃ (H ⧸ H₀.subgroupOf H)) i = i * j
      from congrFun (Equiv.coe_mulRight j) i]
    apply Subtype.ext
    show (L.gen ((Quotient.out i : H) : G) : U) * (L.gen ((Quotient.out j : H) : G) : U)
      = (L.gen (((Quotient.out i * Quotient.out j) * (Quotient.out (i * j))⁻¹ : H) : G) : U)
        * (L.gen ((Quotient.out (i * j) : H) : G) : U)
    rw [← Units.val_mul, ← map_mul, ← Units.val_mul, ← map_mul]
    congr 1
    rw [L.gen_injective.eq_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

/-- **L1 corollary.**  If `G' ⊴ G` is torsion free of finite index, then for *every* subgroup
`H ≤ G` the division closure `D H` of `K[H]` in `U(G)` is a semisimple ring. -/
theorem isSemisimpleRing_D {K : Type*} [Field K] [CharZero K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    (G' : Subgroup G) (hG'n : G'.Normal) (htf : IsMulTorsionFree G') (hfin : G'.FiniteIndex)
    (H : Subgroup G) : IsSemisimpleRing ↥(L.D H) := by
  have htf' : IsMulTorsionFree ↥(H ⊓ G') := Work.ORLinnell.isMulTorsionFree_inf htf H
  have hle : H ⊓ G' ≤ H := inf_le_left
  have hN : ((H ⊓ G').subgroupOf H).Normal := by
    rw [Subgroup.inf_subgroupOf_left G' H]
    exact hG'n.subgroupOf H
  have hfi : ((H ⊓ G').subgroupOf H).FiniteIndex := by
    rw [Subgroup.inf_subgroupOf_left G' H]
    infer_instance
  haveI : DivisionRing ↥(L.D (H ⊓ G')) := L.divisionRingOfTorsionFree htf'
  exact Work.ORLinnell.Cosets.isSemisimpleRing_D_of_finiteIndex L hle hN hfi htf'
    (fun y hy => Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex L hle hN hfi
      (fun x hx => L.division_of_torsionFree (H ⊓ G') htf' x hx) y hy)

end Work.ORLinnell.Cosets

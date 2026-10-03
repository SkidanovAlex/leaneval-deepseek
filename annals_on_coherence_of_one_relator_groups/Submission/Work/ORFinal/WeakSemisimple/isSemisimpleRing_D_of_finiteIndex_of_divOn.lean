import Mathlib
import Submission.Work.ORLinnell.Main
import Submission.Work.ORLinnell.Cosets.isSemisimpleRing_D
import Submission.Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex

/-!
# Semisimplicity of `D H` from a finite index division subring

Let `L : LinnellDatum K G U` and let `H₀ ≤ H ≤ G` be such that `H₀` is normal in `H` of finite
index and every nonzero element of the division closure `L.D H₀` is a unit of `L.D H₀`
(i.e. `L.D H₀` is a division ring).  Then `L.D H` is a semisimple ring.

This is the finite index case of L1 in the paper, *without* the torsion freeness hypothesis on
`H₀`: all that the Maschke argument of
`Work.ORLinnell.Cosets.isSemisimpleRing_D_of_finiteIndex` needs from torsion freeness is the
division ring structure on `D H₀`, which we take here directly as the hypothesis `hdiv`.

The spanning hypothesis of the Maschke argument (`span_D_transversal`) is supplied by
`Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex`, the "`D H = ∑_q (D H₀) x_q`" theorem.
-/

namespace Work.ORFinal.WeakSemisimple

open Work.ORLinnell

theorem isSemisimpleRing_D_of_finiteIndex_of_divOn (K : Type*) [Field K] [CharZero K]
    (G : Type*) [Group G] (U : Type*) [Ring U] [Nontrivial U] [Algebra K U]
    (L : Work.ORLinnell.LinnellDatum K G U) {H₀ H : Subgroup G} (hH₀ : H₀ ≤ H)
    (hN : (H₀.subgroupOf H).Normal) (hfin : (H₀.subgroupOf H).FiniteIndex)
    (hdiv : ∀ x : ↥(L.D H₀), x ≠ 0 → IsUnit x) : IsSemisimpleRing ↥(L.D H) := by
  classical
  haveI hNinst : (H₀.subgroupOf H).Normal := hN
  haveI hFintype : Fintype (H ⧸ H₀.subgroupOf H) := Fintype.ofFinite _
  -- `D H₀` is a division ring, since every nonzero element is a unit.
  letI hDR : DivisionRing ↥(L.D H₀) :=
    DivisionRing.ofIsUnitOrEqZero fun x => by
      rcases eq_or_ne x 0 with h | h
      · exact Or.inr h
      · exact Or.inl (hdiv x h)
  -- the spanning of `D H` over `D H₀` along the coset representatives.
  have hspan : ∀ y ∈ L.D H, ∃ c : (H ⧸ H₀.subgroupOf H) →₀ ↥(L.D H₀),
      y = c.sum (fun q d => (d : U) * (L.gen ((Quotient.out q : H) : G) : U)) :=
    fun y hy => Work.ORLinnell.FiniteIndex.span_D_of_finiteIndex L hH₀ hN hfin hdiv y hy
  let u : (H ⧸ H₀.subgroupOf H) → (↥(L.D H))ˣ := fun q =>
    ⟨⟨(L.gen ((Quotient.out q : H) : G) : U), L.gen_mem H (Quotient.out q)⟩,
     ⟨(↑((L.gen ((Quotient.out q : H) : G))⁻¹) : U),
       L.isDivisionClosed H (L.gen ((Quotient.out q : H) : G) : U)
         (L.gen_mem H (Quotient.out q)) (↑((L.gen ((Quotient.out q : H) : G))⁻¹)) (by simp)⟩,
     Subtype.ext (by simp),
     Subtype.ext (by simp)⟩
  let c₀ : ↥(L.D H) :=
    ⟨algebraMap K U ((Fintype.card (H ⧸ H₀.subgroupOf H) : K))⁻¹, L.algebraMap_mem H _⟩
  refine Work.ORLinnell.Cosets.isSemisimpleRing_of_groupLike_units (Da := ↥(L.D H₀))
    (Ra := ↥(L.D H)) (Subring.inclusion (L.D_mono hH₀)) u c₀ ?_ ?_ ?_ ?_ ?_
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

end Work.ORFinal.WeakSemisimple

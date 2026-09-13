import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Module

namespace Commons.LinearAlgebra.Submodule

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]

private noncomputable def prodEquivSupOfDisjoint (S T : Submodule K V) (h : S ⊓ T = ⊥) :
    (↥S × ↥T) ≃ₗ[K] (↥(S ⊔ T)) :=
  LinearEquiv.ofBijective
    ((S.subtype.coprod T.subtype).codRestrict (S ⊔ T)
      (fun c => by rw [Submodule.sup_eq_range]; exact LinearMap.mem_range_self _ c))
    (by
      constructor
      · rw [← LinearMap.ker_eq_bot]
        rw [Submodule.eq_bot_iff]
        rintro ⟨x, y⟩ hxy
        have hxy' : (x : V) + (y : V) = 0 := by
          have := congrArg (fun z : ↥(S ⊔ T) => (z : V)) hxy
          simpa using this
        have hxT : (x : V) ∈ T := by
          have : (x : V) = -(y : V) := eq_neg_of_add_eq_zero_left hxy'
          rw [this]; exact T.neg_mem y.2
        have hx : (x : V) = 0 := by
          have : (x : V) ∈ S ⊓ T := ⟨x.2, hxT⟩
          rw [h] at this; simpa using this
        have hy : (y : V) = 0 := by
          rw [hx, zero_add] at hxy'; exact hxy'
        exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
      · intro z
        obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp z.2
        exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩)

@[simp]
private theorem prodEquivSupOfDisjoint_apply (S T : Submodule K V) (h : S ⊓ T = ⊥)
    (x : ↥S) (y : ↥T) : ((prodEquivSupOfDisjoint S T h (x, y) : ↥(S ⊔ T)) : V) = x + y := rfl

@[simp]
private theorem prodEquivSupOfDisjoint_symm_inclusion_left (S T : Submodule K V) (h : S ⊓ T = ⊥)
    (x : ↥S) : (prodEquivSupOfDisjoint S T h).symm (Submodule.inclusion le_sup_left x) = (x, 0) := by
  apply (prodEquivSupOfDisjoint S T h).symm_apply_eq.mpr
  apply Subtype.ext
  rw [prodEquivSupOfDisjoint_apply]
  simp

@[simp]
private theorem prodEquivSupOfDisjoint_symm_inclusion_right (S T : Submodule K V) (h : S ⊓ T = ⊥)
    (y : ↥T) : (prodEquivSupOfDisjoint S T h).symm (Submodule.inclusion le_sup_right y) = (0, y) := by
  apply (prodEquivSupOfDisjoint S T h).symm_apply_eq.mpr
  apply Subtype.ext
  rw [prodEquivSupOfDisjoint_apply]
  simp

/-- **Classification of pairs of subspaces up to automorphism**: two pairs `(L, L')` and
`(M, M')` of subspaces of a finite `𝔽₂`-space `V` are simultaneously carried to one
another by a linear automorphism of `V` as soon as `dim L = dim M`, `dim L' = dim M'` and
`dim (L ⊓ L') = dim (M ⊓ M')`.

Suggested proof: choose bases of `L ⊓ L'`, `L`, `L + L'`, `V` (extending at each step) and
the corresponding bases for the primed pair; the change-of-basis maps are linear
equivalences; their inverses extend to an automorphism of `V`.  (Use
`Submodule.exists_linearEquiv_restrict_eq`, `LinearEquiv.ofFinrankEq`,
`Submodule.finrank_sup_add_finrank_inf_eq` to see that the intermediate dimensions
coincide.) -/
theorem exists_linearEquiv_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (L L' M M' : Submodule (ZMod 2) V)
    (hL : Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) M)
    (hL' : Module.finrank (ZMod 2) L' = Module.finrank (ZMod 2) M')
    (hinf : Module.finrank (ZMod 2) ↥(L ⊓ L') = Module.finrank (ZMod 2) ↥(M ⊓ M')) :
    ∃ e : V ≃ₗ[ZMod 2] V, L.map (e : V →ₗ[ZMod 2] V) = M ∧ L'.map (e : V →ₗ[ZMod 2] V) = M' := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (L ⊓ L')
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl (M ⊓ M')
  have hAD : (L ⊓ L') ⊓ (Q ⊓ L) = ⊥ := by rw [← inf_assoc, hQ.inf_eq_bot, bot_inf_eq]
  have hsupL : (L ⊓ L') ⊔ (Q ⊓ L) = L := by
    rw [← sup_inf_assoc_of_le (z := L) Q (show L ⊓ L' ≤ L from inf_le_left),
      hQ.sup_eq_top, top_inf_eq]
  have hAE : (L ⊓ L') ⊓ (Q ⊓ L') = ⊥ := by rw [← inf_assoc, hQ.inf_eq_bot, bot_inf_eq]
  have hsupL' : (L ⊓ L') ⊔ (Q ⊓ L') = L' := by
    rw [← sup_inf_assoc_of_le (z := L') Q (show L ⊓ L' ≤ L' from inf_le_right),
      hQ.sup_eq_top, top_inf_eq]
  have hLE : L ⊓ (Q ⊓ L') = ⊥ := by
    rw [show L ⊓ (Q ⊓ L') = (L ⊓ L') ⊓ Q from by ac_rfl, hQ.inf_eq_bot]
  have hL'le : L' ≤ L ⊔ (Q ⊓ L') := by
    calc L' = (L ⊓ L') ⊔ (Q ⊓ L') := hsupL'.symm
      _ ≤ L ⊔ (Q ⊓ L') := sup_le (le_trans inf_le_left le_sup_left) le_sup_right
  have hBD : (M ⊓ M') ⊓ (Q' ⊓ M) = ⊥ := by rw [← inf_assoc, hQ'.inf_eq_bot, bot_inf_eq]
  have hsupM : (M ⊓ M') ⊔ (Q' ⊓ M) = M := by
    rw [← sup_inf_assoc_of_le (z := M) Q' (show M ⊓ M' ≤ M from inf_le_left),
      hQ'.sup_eq_top, top_inf_eq]
  have hBE : (M ⊓ M') ⊓ (Q' ⊓ M') = ⊥ := by rw [← inf_assoc, hQ'.inf_eq_bot, bot_inf_eq]
  have hsupM' : (M ⊓ M') ⊔ (Q' ⊓ M') = M' := by
    rw [← sup_inf_assoc_of_le (z := M') Q' (show M ⊓ M' ≤ M' from inf_le_right),
      hQ'.sup_eq_top, top_inf_eq]
  have hME : M ⊓ (Q' ⊓ M') = ⊥ := by
    rw [show M ⊓ (Q' ⊓ M') = (M ⊓ M') ⊓ Q' from by ac_rfl, hQ'.inf_eq_bot]
  have hM'le : M' ≤ M ⊔ (Q' ⊓ M') := by
    calc M' = (M ⊓ M') ⊔ (Q' ⊓ M') := hsupM'.symm
      _ ≤ M ⊔ (Q' ⊓ M') := sup_le (le_trans inf_le_left le_sup_left) le_sup_right
  have hfinL : Module.finrank (ZMod 2) L
      = Module.finrank (ZMod 2) ↥(L ⊓ L') + Module.finrank (ZMod 2) ↥(Q ⊓ L) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ L') (Q ⊓ L)
    rw [hsupL, hAD, finrank_bot, add_zero] at this
    exact this
  have hfinL' : Module.finrank (ZMod 2) L'
      = Module.finrank (ZMod 2) ↥(L ⊓ L') + Module.finrank (ZMod 2) ↥(Q ⊓ L') := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ L') (Q ⊓ L')
    rw [hsupL', hAE, finrank_bot, add_zero] at this
    exact this
  have hfinM : Module.finrank (ZMod 2) M
      = Module.finrank (ZMod 2) ↥(M ⊓ M') + Module.finrank (ZMod 2) ↥(Q' ⊓ M) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (M ⊓ M') (Q' ⊓ M)
    rw [hsupM, hBD, finrank_bot, add_zero] at this
    exact this
  have hfinM' : Module.finrank (ZMod 2) M'
      = Module.finrank (ZMod 2) ↥(M ⊓ M') + Module.finrank (ZMod 2) ↥(Q' ⊓ M') := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (M ⊓ M') (Q' ⊓ M')
    rw [hsupM', hBE, finrank_bot, add_zero] at this
    exact this
  have hdimDL : Module.finrank (ZMod 2) ↥(Q ⊓ L) = Module.finrank (ZMod 2) ↥(Q' ⊓ M) := by
    omega
  have hdimE : Module.finrank (ZMod 2) ↥(Q ⊓ L') = Module.finrank (ZMod 2) ↥(Q' ⊓ M') := by
    omega
  let φ : ↥(L ⊓ L') ≃ₗ[ZMod 2] ↥(M ⊓ M') := LinearEquiv.ofFinrankEq _ _ hinf
  let ψ : ↥(Q ⊓ L) ≃ₗ[ZMod 2] ↥(Q' ⊓ M) := LinearEquiv.ofFinrankEq _ _ hdimDL
  let ψ' : ↥(Q ⊓ L') ≃ₗ[ZMod 2] ↥(Q' ⊓ M') := LinearEquiv.ofFinrankEq _ _ hdimE
  let f : ↥L ≃ₗ[ZMod 2] ↥M :=
    (LinearEquiv.ofEq L ((L ⊓ L') ⊔ (Q ⊓ L)) hsupL.symm).trans
      ((prodEquivSupOfDisjoint (L ⊓ L') (Q ⊓ L) hAD).symm.trans
        ((φ.prodCongr ψ).trans
          ((prodEquivSupOfDisjoint (M ⊓ M') (Q' ⊓ M) hBD).trans
            (LinearEquiv.ofEq ((M ⊓ M') ⊔ (Q' ⊓ M)) M hsupM))))
  have hfA : ∀ a : ↥(L ⊓ L'), (f ⟨(a : V), (inf_le_left : L ⊓ L' ≤ L) a.2⟩ : V) = (φ a : V) := by
    intro a
    have e1 : LinearEquiv.ofEq L ((L ⊓ L') ⊔ (Q ⊓ L)) hsupL.symm ⟨(a : V), (inf_le_left : L ⊓ L' ≤ L) a.2⟩
        = Submodule.inclusion le_sup_left a := Subtype.ext rfl
    simp only [f, LinearEquiv.trans_apply, e1, LinearEquiv.prodCongr_apply,
      prodEquivSupOfDisjoint_symm_inclusion_left, prodEquivSupOfDisjoint_apply, map_zero,
      LinearEquiv.coe_ofEq_apply, Submodule.coe_zero, add_zero]
  let h : ↥(L ⊔ (Q ⊓ L')) ≃ₗ[ZMod 2] ↥(M ⊔ (Q' ⊓ M')) :=
    (prodEquivSupOfDisjoint L (Q ⊓ L') hLE).symm.trans
      ((f.prodCongr ψ').trans (prodEquivSupOfDisjoint M (Q' ⊓ M') hME))
  have keyL : ∀ x : ↥L, (h (Submodule.inclusion le_sup_left x) : V) = (f x : V) := by
    intro x
    simp only [h, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      prodEquivSupOfDisjoint_symm_inclusion_left, prodEquivSupOfDisjoint_apply, map_zero, Submodule.coe_zero, add_zero]
  have keyE : ∀ y : ↥(Q ⊓ L'), (h (Submodule.inclusion le_sup_right y) : V) = (ψ' y : V) := by
    intro y
    simp only [h, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      prodEquivSupOfDisjoint_symm_inclusion_right, prodEquivSupOfDisjoint_apply, map_zero, Submodule.coe_zero,
      zero_add]
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq h
  refine ⟨e, ?_, ?_⟩
  · apply Submodule.eq_of_le_of_finrank_eq
    · rintro y ⟨x, hx, rfl⟩
      have hmem : (h (Submodule.inclusion le_sup_left (⟨x, hx⟩ : ↥L)) : V) ∈ M := by
        rw [keyL ⟨x, hx⟩]
        exact (f ⟨x, hx⟩).2
      have hx' : (e : V →ₗ[ZMod 2] V) x
          = (h (Submodule.inclusion le_sup_left (⟨x, hx⟩ : ↥L)) : V) := by
        have hh := he (Submodule.inclusion le_sup_left (⟨x, hx⟩ : ↥L))
        simp only [Submodule.coe_inclusion] at hh
        exact hh.symm
      rw [hx']; exact hmem
    · rw [← LinearEquiv.finrank_eq (e.submoduleMap L), hL]
  · apply Submodule.eq_of_le_of_finrank_eq
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hsupL' ▸ hx)
      have hdec : (⟨x, hL'le hx⟩ : ↥(L ⊔ (Q ⊓ L')))
          = Submodule.inclusion le_sup_left (⟨a, (inf_le_left : L ⊓ L' ≤ L) ha⟩ : ↥L)
            + Submodule.inclusion le_sup_right (⟨c, hc⟩ : ↥(Q ⊓ L')) := by
        apply Subtype.ext
        simp only [Submodule.coe_add, Submodule.coe_inclusion, hac]
      have key : (h ⟨x, hL'le hx⟩ : V) = (φ ⟨a, ha⟩ : V) + (ψ' ⟨c, hc⟩ : V) := by
        rw [hdec, map_add, Submodule.coe_add, keyL ⟨a, (inf_le_left : L ⊓ L' ≤ L) ha⟩, keyE ⟨c, hc⟩, hfA ⟨a, ha⟩]
      have hx' : (e : V →ₗ[ZMod 2] V) x = (h ⟨x, hL'le hx⟩ : V) := by
        exact (he ⟨x, hL'le hx⟩).symm
      rw [hx', key]
      exact M'.add_mem ((inf_le_right : (M ⊓ M') ≤ M') (φ ⟨a, ha⟩).2)
        ((inf_le_right : (Q' ⊓ M') ≤ M') (ψ' ⟨c, hc⟩).2)
    · rw [← LinearEquiv.finrank_eq (e.submoduleMap L'), hL']

end Commons.LinearAlgebra.Submodule
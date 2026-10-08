import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.chISixCor1Prop
import Submission.Work.NormalComplement.Sec5Fix.NF.three_le_fixedPts_centH
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5Fix.NF

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- Any subgroup of `G` fixing at least two distinct points of `Ω = G ⧸ H` is conjugate into
`D = H ⊓ H^t`.  Indeed the ordered pairs of distinct points form a single `G`-orbit (`ThmAProp`
supplies the `2`-transitivity of `G` on `Ω`), so every pointwise stabiliser of two distinct points
is conjugate to the pointwise stabiliser of `{H, tH}`, namely `D`. -/
theorem exists_conj_le_twoPoint_of_two_fixed
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G}
    (hTT : Submission.Blueprint.IsTwoTransitiveOn H) (htH : t ∉ H)
    (X : Subgroup G) (h2 : 2 ≤ (Submission.Blueprint.fixedPts H X).ncard) :
    ∃ g : G, X.map (MulAut.conj g).toMonoidHom ≤ Submission.Blueprint.twoPoint H t := by
  classical
  have h2' : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := hTT
  rw [MulAction.is_two_pretransitive_iff] at h2'
  have h1lt : 1 < (Submission.Blueprint.fixedPts H X).ncard := by omega
  obtain ⟨ω₁, hω₁, ω₂, hω₂, hne⟩ :=
    (Set.one_lt_ncard (s := Submission.Blueprint.fixedPts H X) (Set.toFinite _)).mp h1lt
  -- the points `pt H` and `t • pt H` are distinct, since `t ∉ H`
  have ht_ne : Work.DoubleTransitivity.pt H ≠ (t • Work.DoubleTransitivity.pt H) := by
    intro hc
    rw [Work.DoubleTransitivity.smul_pt] at hc
    have h1 : t ∈ H := by
      have := QuotientGroup.eq.mp hc
      simpa [Work.DoubleTransitivity.pt] using this
    exact htH h1
  obtain ⟨g, hg1, hg2⟩ := h2' hne ht_ne
  refine ⟨g, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hx1 : x • ω₁ = ω₁ := (Work.ThreePoints.mem_fixedPts.mp hω₁) x hx
  have hx2 : x • ω₂ = ω₂ := (Work.ThreePoints.mem_fixedPts.mp hω₂) x hx
  have hconj : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hyfix1 : (MulAut.conj g).toMonoidHom x • Work.DoubleTransitivity.pt H
      = Work.DoubleTransitivity.pt H := by
    rw [hconj, ← hg1]
    calc (g * x * g⁻¹) • (g • ω₁)
        = ((g * x * g⁻¹) * g) • ω₁ := (mul_smul _ _ _).symm
      _ = (g * x) • ω₁ := by rw [show (g * x * g⁻¹) * g = g * x from by group]
      _ = g • (x • ω₁) := mul_smul g x ω₁
      _ = g • ω₁ := by rw [hx1]
  have hyfix2 : (MulAut.conj g).toMonoidHom x • (t • Work.DoubleTransitivity.pt H)
      = t • Work.DoubleTransitivity.pt H := by
    rw [hconj, ← hg2]
    calc (g * x * g⁻¹) • (g • ω₂)
        = ((g * x * g⁻¹) * g) • ω₂ := (mul_smul _ _ _).symm
      _ = (g * x) • ω₂ := by rw [show (g * x * g⁻¹) * g = g * x from by group]
      _ = g • (x • ω₂) := mul_smul g x ω₂
      _ = g • ω₂ := by rw [hx2]
  rw [Work.ThreePoints.mem_twoPoint]
  constructor
  · rw [← Work.DoubleTransitivity.Sec4.stabilizer_pt_eq H, MulAction.mem_stabilizer_iff]
    exact hyfix1
  · have hstab : (MulAut.conj g).toMonoidHom x
        ∈ MulAction.stabilizer G (t • Work.DoubleTransitivity.pt H) :=
      MulAction.mem_stabilizer_iff.mpr hyfix2
    rw [Work.DoubleTransitivity.smul_pt] at hstab
    rw [Work.ThreePoints.stabilizer_mk] at hstab
    exact Work.ThreePoints.mem_conj_iff.mp hstab

/-- **§5 Proposition 3, conjugacy step.**  With `N = O_{f'}(M)`, the subgroup `C_H(N)` fixes at
least three points of `Ω` (`three_le_fixedPts_centH`), hence is conjugate into `V = C_D(t)`:
`Ch. II §4 Prop. 2 (b)` (`prop2b_conj_into_centD`) does this for a subgroup of `D`, and any subgroup
fixing two distinct points is conjugate into `D` by the `2`-transitivity of `G` on `Ω`
(`exists_conj_le_twoPoint_of_two_fixed`). -/
theorem centH_conj_into_centD
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (hB : (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))))
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t)
    (hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hMc : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hMd : Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
      Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G)) :
    ∃ g : G, ((Subgroup.centralizer
        ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G)) ⊓ H).map
          (MulAut.conj g).toMonoidHom ≤ Submission.Blueprint.centD H t := by
  classical
  set X : Subgroup G := Subgroup.centralizer
      ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G) ⊓ H
    with hXdef
  -- `X = C_H(N)` has at least three fixed points
  have hCor1 : Work.NormalComplement.Design.ChISixCor1Prop :=
    Work.NormalComplement.chISixCor1Prop hA hBP
  have h3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard := by
    have := three_le_fixedPts_centH hFT hCor1 h u hu hf hB M hM hMd.1
    simpa only [hXdef] using this
  -- `G` is `2`-transitive on `Ω = G ⧸ H`
  have hTT : Submission.Blueprint.IsTwoTransitiveOn H := hA G h.sit.1.1 H h.se
  -- conjugate `X` into `D`
  obtain ⟨g, hgD⟩ := exists_conj_le_twoPoint_of_two_fixed hTT h.notMem X (by omega)
  have h3' : 3 ≤ (Submission.Blueprint.fixedPts H (X.map (MulAut.conj g).toMonoidHom)).ncard := by
    rw [Work.DoubleTransitivity.Sec4.ncard_fixedPts_conj H g X]
    exact h3
  -- Ch. II §4 Prop. 2 (b)
  obtain ⟨d, _hdD, hdX⟩ :=
    Work.NormalComplement.prop2b_conj_into_centD G h.sit hBP hC4 h.se h.invol h.notMem hgD h3'
  refine ⟨d * g, ?_⟩
  have hhom : (MulAut.conj d).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = (MulAut.conj (d * g)).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hmap : (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj d).toMonoidHom
      = X.map (MulAut.conj (d * g)).toMonoidHom := by
    rw [Subgroup.map_map, hhom]
  rw [hmap] at hdX
  exact hdX

end Work.NormalComplement.Sec5Fix.NF

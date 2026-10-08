import Mathlib
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The orbit count of case (10-1): `|𝒜| = |C_Q(P)|`

`Step11Out.reg` says that `C_Q(P)` acts on `AT R T P` sharply transitively (for `A, B` in `AT`
there is a *unique* `y ∈ C_Q(P)` with `y A y⁻¹ = B`).  Consequently, as soon as `AT R T P` is
nonempty, the map `y ↦ y A₀ y⁻¹` (`A₀` a fixed member of `AT`) is a bijection
`C_Q(P) ≃ AT R T P`, and the two sets have the same cardinality.

The well-definedness of that map is where the two normalizer hypotheses enter: `C_Q(P) ≤ C_G(P)`
and `C_G(P) ≤ N_G(R)` (that is `hRn`) keep `A ≤ R` under conjugation, while `Step11Out.Tn` keeps
`¬ A ≤ T`; `A ≠ P` is preserved because `C_Q(P)` centralizes `P`.
-/

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

theorem AT_ncard_eq_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {P R T : Subgroup G}
    (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T)
    (hne : (Work.ThmF.ChV3.Prove.AT R T P).Nonempty) :
    (Work.ThmF.ChV3.Prove.AT R T P).ncard = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) := by
  classical
  -- a fixed element of `AT`, from the nonemptiness hypothesis
  obtain ⟨A0, hA0⟩ := hne
  have hA0R : A0 ≤ R := hA0.1
  have hA0c : Nat.card A0 = Nat.card P := hA0.2.1
  have hA0T : ¬ A0 ≤ T := hA0.2.2.1
  have hA0P : A0 ≠ P := hA0.2.2.2
  -- `C_Q(P) = Q ⊓ C_G(P)` normalizes `R` (via `hRn`) and `T` (via `Step11Out.Tn`)
  have hCQCG : CQ Q P ≤ CG P := inf_le_right
  have hCQR : CQ Q P ≤ NG R := le_trans hCQCG hRn
  have hCQT : CQ Q P ≤ NG T := le_trans le_sup_left h11.Tn
  -- the conjugation map lands in `AT`
  have hmem : ∀ y : ↥(CQ Q P), cj (y : G) A0 ∈ AT R T P := by
    intro y
    have hyR : (y : G) ∈ NG R := hCQR y.2
    have hyT : (y : G) ∈ NG T := hCQT y.2
    have hyP : (y : G) ∈ CG P := hCQCG y.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc cj (y : G) A0 ≤ cj (y : G) R := cj_mono hA0R _
        _ = R := (cj_eq_self_iff _ R).mpr hyR
    · rw [card_cj, hA0c]
    · intro hle
      have h : cj (y : G)⁻¹ (cj (y : G) A0) ≤ cj (y : G)⁻¹ T := cj_mono hle _
      rw [cj_inv_cj] at h
      have hT : cj (y : G)⁻¹ T = T := (cj_eq_self_iff _ T).mpr (hCQT (Subgroup.inv_mem _ y.2))
      rw [hT] at h
      exact hA0T h
    · intro heq
      apply hA0P
      have h : cj (y : G)⁻¹ (cj (y : G) A0) = cj (y : G)⁻¹ P := by rw [heq]
      rw [cj_inv_cj] at h
      have hP : cj (y : G)⁻¹ P = P :=
        (cj_eq_self_iff _ P).mpr (Subgroup.centralizer_le_normalizer (P : Set G)
          (hCQCG (Subgroup.inv_mem _ y.2)))
      rwa [hP] at h
  -- sharp transitivity, read off `Step11Out.reg`
  have key : ∀ B ∈ AT R T P, ∃! y : ↥(CQ Q P), cj (y : G) A0 = B := by
    intro B hB
    have h := h11.reg A0 B hA0R hB.1 hA0c hB.2.1 hA0T hB.2.2.1 hA0P hB.2.2.2
    simpa only [cj] using h
  let f : ↥(CQ Q P) → ↥(AT R T P) := fun y => ⟨cj (y : G) A0, hmem y⟩
  have hinj : Function.Injective f := by
    intro y1 y2 heq
    have hval : cj (y1 : G) A0 = cj (y2 : G) A0 := congrArg Subtype.val heq
    obtain ⟨w, -, huniq⟩ := key (cj (y1 : G) A0) (hmem y1)
    exact (huniq y1 rfl).trans (huniq y2 hval.symm).symm
  have hsurj : Function.Surjective f := by
    intro B
    obtain ⟨y, hy, -⟩ := key (B : Subgroup G) B.2
    exact ⟨y, Subtype.ext hy⟩
  have hcard : Nat.card ↥(AT R T P) = Nat.card ↥(CQ Q P) :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
  exact hcard

end Work.ThmF.ChV3.Prove

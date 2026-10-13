/-
  WilC5 — a partial elementary map into `M` *extends to a surjective* one, and hence carries an
  elementary embedding `M ⪯ N`.

  Given a partial elementary map `τ : B → M` (`B ⊆ N`) and a `κ`-saturated `N` with `κ > |M|`, the
  classical Zorn argument on the poset of partial elementary maps extending `τ` (`PEM`,
  `Work.WilC5.elemOn_extend`, `Work.WilC5.PEM.iUnion_valid`) produces a *maximal* one;
  maximality together with the one-point extension step (`elemOn_extend`) forces it to be onto `M`.
  The inverse of a surjective partial elementary map is then an elementary embedding `M ⪯ N`
  (`Work.WilC5.emb_of_surj_elemOn`), and `τ'` exhibits it as a section.
-/
import Mathlib
import Submission.Work.WilC5.ExtSatAux
import Submission.Work.WilC5.ExtSatChain
import Submission.Work.WilC5.elemOn_extend
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.emb_of_surj_elemOn

set_option autoImplicit false

noncomputable section
open Classical

namespace Work.WilC5

open FirstOrder Language

/-- **A partial elementary map extends to a surjective partial elementary map.**

Let `τ : B → M` be an elementary map defined on `B ⊆ N`, let `N` be `κ`-saturated with
`κ > |M|`.  Then `τ` extends to an elementary map `τ' : B' → M` on a superset `B' ⊇ B` whose range
is *all* of `M`.

The proof is the Zorn argument: the union of a chain of partial elementary maps extending `τ` is
again one (`PEM.iUnion_valid`), so the poset of such maps has a maximal element `pstar`;
if `m ∈ M` were not in the range of `pstar`, the type of `m` over `pstar.1` would be realised at a
point `n ∉ pstar.1` of the `κ`-saturated `N` (`elemOn_extend`, applicable because
`|pstar.1| ≤ |M| < κ`), contradicting maximality. -/
theorem exists_surj_extension_elemOn {L : FirstOrder.Language.{0, 0}} {M N : Type}
    [L.Structure M] [L.Structure N] {B : Set N} {τ : B → M}
    (hτ : @ElemOn L M N _ _ B τ) (κ : Cardinal.{0}) (hκ : Cardinal.mk M < κ)
    (hsat : @IsSaturated L N _ κ) :
    ∃ (B' : Set N) (hB : B ⊆ B') (τ' : B' → M),
      @ElemOn L M N _ _ B' τ' ∧
      (∀ b : B, τ' ⟨(b : N), hB b.2⟩ = τ b) ∧
      ∀ m : M, ∃ b : B', τ' b = m := by
  -- the partial elementary maps agreeing with `τ` on `B`
  let s : Set (PEM L M N) :=
    {p | p.Valid ∧ B ⊆ p.1 ∧ ∀ b : B, ∀ hh : (b : N) ∈ p.1, p.2 ⟨(b : N), hh⟩ = τ b}
  have hbase : (⟨B, τ⟩ : PEM L M N) ∈ s := by
    refine ⟨hτ, subset_rfl, fun b _ => ?_⟩
    exact congrArg τ (Subtype.ext rfl)
  -- Zorn: the union of a chain of such maps is again such a map
  obtain ⟨pstar, -, hp_max⟩ :=
    zorn_le_nonempty₀ s (fun c hc_sub hchain y hy => by
      obtain ⟨ub, hubvalid, hubdom, huble⟩ :=
        PEM.iUnion_valid hchain ⟨y, hy⟩ (fun p hp => (hc_sub hp).1)
      refine ⟨ub, ⟨hubvalid, ?_, ?_⟩, huble⟩
      · intro b hb
        rw [hubdom]
        exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, (hc_sub hy).2.1 hb⟩⟩
      · intro b hh
        have hy1 : (b : N) ∈ y.1 := (hc_sub hy).2.1 b.2
        have key := (huble y hy).2 ⟨(b : N), hy1⟩
        rw [show (⟨(b : N), hh⟩ : ub.1) = ⟨(b : N), (huble y hy).1 hy1⟩ from Subtype.ext rfl]
          at key
        rw [key]
        exact (hc_sub hy).2.2 b hy1)
      (⟨B, τ⟩ : PEM L M N) hbase
  have hvalid : @ElemOn L M N _ _ pstar.1 pstar.2 := hp_max.1.1
  -- a maximal such map is onto `M`
  have hsurj : ∀ m : M, ∃ b : pstar.1, pstar.2 b = m := by
    intro m
    by_contra hcon
    have hm : m ∉ Set.range pstar.2 := by
      rintro ⟨b, hb⟩
      exact hcon ⟨b, hb⟩
    have hκstar : Cardinal.mk pstar.1 < κ :=
      lt_of_le_of_lt (mk_le_of_elemOn hvalid) hκ
    obtain ⟨n, hnB, hext⟩ := elemOn_extend hvalid κ hκstar hsat m hm
    set y' : PEM L M N := ⟨insert n pstar.1, PEM.extendFun pstar.2 n m⟩ with hy'_def
    have hy'_s : y' ∈ s := by
      rw [hy'_def]
      refine ⟨hext, ?_, ?_⟩
      · exact Set.Subset.trans hp_max.1.2.1 (Set.subset_insert n pstar.1)
      · intro b hh
        have hb_mem : (b : N) ∈ pstar.1 := hp_max.1.2.1 b.2
        exact (PEM.extendFun_apply_of_mem pstar.2 ⟨(b : N), hh⟩ hb_mem).trans
          (hp_max.1.2.2 b hb_mem)
    have hle' : pstar ≤ y' := by
      rw [hy'_def]
      refine ⟨Set.subset_insert n pstar.1, fun x => ?_⟩
      exact PEM.extendFun_apply_of_mem pstar.2 ⟨x.1, Set.mem_insert_of_mem n x.2⟩ x.2
    have hnle : ¬ y' ≤ pstar := by
      intro hle
      rw [hy'_def] at hle
      exact hnB (hle.1 (by simp))
    exact hnle (hp_max.2 hy'_s hle')
  exact ⟨pstar.1, hp_max.1.2.1, pstar.2, hvalid, fun b => hp_max.1.2.2 b (hp_max.1.2.1 b.2),
    hsurj⟩

theorem extends_elemOn_sat {L : FirstOrder.Language.{0, 0}}
    {M N : Type} [L.Structure M] [L.Structure N] {B : Set N} {τ : B → M}
    (hτ : Work.WilC5.ElemOn (L := L) B τ)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk M < κ) (hsat : @Work.WilC5.IsSaturated L N _ κ) :
    ∃ (B' : Set N) (hB : B ⊆ B') (τ' : B' → M),
      Work.WilC5.ElemOn (L := L) B' τ' ∧
      (∀ b : B, τ' ⟨(b : N), hB b.2⟩ = τ b) ∧
      ∃ (g : FirstOrder.Language.ElementaryEmbedding L M N),
        ∀ m : M, ∃ h : ((g m : N) ∈ B'), τ' ⟨(g m : N), h⟩ = m := by
  obtain ⟨B', hB, τ', hτ', hagree, hsurj⟩ := exists_surj_extension_elemOn hτ κ hκ hsat
  exact ⟨B', hB, τ', hτ', hagree, emb_of_surj_elemOn hτ' hsurj⟩

end Work.WilC5

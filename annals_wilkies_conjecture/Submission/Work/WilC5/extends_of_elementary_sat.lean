import Mathlib
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.ExtSatAux
import Submission.Work.WilC5.ExtSatChain
import Submission.Work.WilC5.elemOn_extend
import Submission.Work.WilC5.elemOn_range_of_helem
import Submission.Work.WilC5.embedding_of_surjective_elemOn

namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

/-- **An elementary embedding of a substructure into a saturated structure extends to all of `M`.**
If `σ : A → N` is an elementary embedding of an `L`-substructure `A` of `M` into a `κ`-saturated
`N` with `|M| < κ`, then `σ` extends to an `L`-embedding of all of `M` into `N`.

The proof is the classical Zorn argument on the poset `PEM L M N` of *partial elementary maps*: the
inverse `τ₀` of `σ` is such a map on `Set.range σ`, chains have upper bounds (`PEM.iUnion_valid`),
and a maximal partial map `τ : B → M` must be surjective, since otherwise realising the type of a
missing element `m` over `B` (`elemOn_extend`) would enlarge it.  The set `s` below carries the
partial maps that are elementary and extend `σ`. -/
theorem extends_of_elementary_sat {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    {M N : Type} [L.Structure M] [L.Structure N] (hM : M ⊨ T) (hN : N ⊨ T)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk M < κ) (hsat : @Work.WilC5.IsSaturated L N _ κ)
    (A : L.Substructure M) (σ : L.Embedding A N)
    (helem : ∀ (φ : L.Formula (A ⊕ Fin 0)),
      (φ.Realize (Sum.elim Subtype.val (fun i : Fin 0 => i.elim0)) ↔
        φ.Realize (Sum.elim (fun a : A => (σ a : N)) (fun i : Fin 0 => i.elim0)))) :
    ∃ g : L.Embedding M N, ∀ a : A, g a = σ a := by
  classical
  -- the inverse of `σ`, a partial elementary map on `Set.range σ`
  let τ₀ : Set.range σ → M :=
    fun y => (Classical.choose (show ∃ a : A, σ a = (y : N) from y.2) : A)
  have hτ₀ : ∀ a : A, τ₀ ⟨σ a, Set.mem_range_self a⟩ = a := by
    intro a
    dsimp only [τ₀]
    exact congrArg (fun x : A => (x : M))
      (σ.injective (Classical.choose_spec (show ∃ a' : A, σ a' = (σ a : N) from
        Set.mem_range_self a)))
  have hbase : @ElemOn L M N _ _ (Set.range σ) τ₀ := elemOn_range_of_helem helem
  -- the partial elementary maps extending `σ`
  let s : Set (PEM L M N) :=
    {p | p.Valid ∧ Set.range σ ⊆ p.1 ∧ ∀ a : A, ∀ hh : (σ a : N) ∈ p.1, p.2 ⟨σ a, hh⟩ = a}
  have hbase_s : (⟨Set.range σ, τ₀⟩ : PEM L M N) ∈ s := by
    refine ⟨hbase, subset_rfl, fun a hh => ?_⟩
    rw [show (⟨σ a, hh⟩ : Set.range σ) = ⟨σ a, Set.mem_range_self a⟩ from Subtype.ext rfl]
    exact hτ₀ a
  -- Zorn: chains of partial elementary maps have upper bounds
  obtain ⟨pstar, hpstar_le, hpstar_max⟩ :=
    zorn_le_nonempty₀ s (fun c hc_sub hchain y hy => by
      obtain ⟨ub, hubvalid, hubdom, huble⟩ :=
        PEM.iUnion_valid hchain ⟨y, hy⟩ (fun p hp => (hc_sub hp).1)
      refine ⟨ub, ⟨hubvalid, ?_, ?_⟩, huble⟩
      · intro a ha
        rw [hubdom]
        exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, (hc_sub hy).2.1 ha⟩⟩
      · intro a hh
        have hy1 : (σ a : N) ∈ y.1 := (hc_sub hy).2.1 (Set.mem_range_self a)
        have key := (huble y hy).2 ⟨σ a, hy1⟩
        rw [show (⟨σ a, hh⟩ : ub.1) = ⟨σ a, (huble y hy).1 hy1⟩ from Subtype.ext rfl] at key
        rw [key]
        exact (hc_sub hy).2.2 a hy1)
      (⟨Set.range σ, τ₀⟩ : PEM L M N) hbase_s
  have hpstar_valid : @ElemOn L M N _ _ pstar.1 pstar.2 := hpstar_max.1.1
  -- a maximal partial elementary map is surjective
  have hsurj : ∀ m : M, ∃ b : pstar.1, pstar.2 b = m := by
    by_contra hcon
    have hcon' : ∃ m : M, ∀ b : pstar.1, pstar.2 b ≠ m := by
      simpa only [not_forall, not_exists] using hcon
    obtain ⟨m, hm⟩ := hcon'
    have hm' : m ∉ Set.range pstar.2 := by
      rintro ⟨b, hb⟩
      exact hm b hb
    have hκstar : Cardinal.mk pstar.1 < κ :=
      lt_of_le_of_lt (mk_le_of_elemOn hpstar_valid) hκ
    obtain ⟨n, hnB, hext⟩ := elemOn_extend hpstar_valid κ hκstar hsat m hm'
    set y' : PEM L M N := ⟨insert n pstar.1, PEM.extendFun pstar.2 n m⟩ with hy'_def
    have hy'_s : y' ∈ s := by
      rw [hy'_def]
      refine ⟨hext, ?_, ?_⟩
      · exact Set.Subset.trans hpstar_max.1.2.1 (Set.subset_insert n pstar.1)
      · intro a hh
        have ha_mem : (σ a : N) ∈ pstar.1 :=
          hpstar_max.1.2.1 (Set.mem_range_self (f := (σ : ↥A → N)) a)
        exact (PEM.extendFun_apply_of_mem pstar.2 ⟨σ a, hh⟩ ha_mem).trans
          (hpstar_max.1.2.2 a ha_mem)
    have hle' : pstar ≤ y' := by
      rw [hy'_def]
      refine ⟨Set.subset_insert n pstar.1, fun x => ?_⟩
      exact PEM.extendFun_apply_of_mem pstar.2 ⟨x.1, Set.mem_insert_of_mem n x.2⟩ x.2
    have hnle : ¬ y' ≤ pstar := by
      intro hle
      rw [hy'_def] at hle
      exact hnB (hle.1 (by simp))
    exact hnle (hpstar_max.2 hy'_s hle')
  -- the inverse of the (surjective) maximal map is the required embedding
  exact embedding_of_surjective_elemOn hpstar_valid hsurj hpstar_max.1.2.1 hpstar_max.1.2.2

end Work.WilC5

import Mathlib
import Submission.Work.ORHughesFree.Rat.Source.Setup

/-!
# The source subgroup of an element of `Rat(U)`: the induction

We assemble [DHS04, Theorem 5.7] for the term model `RatU U` from the four case lemmas about the
behaviour of the family `Rat.F x = {V ≤ U | x ∈ Rat(V)·U}` and its mirror `Rat.FL x` under the
four-way decomposition `RatU.exists_decomp` of a non-zero element:

* `Rat.Source.F_left_translate` : `F (φa·x) = {V | V.map (MulAut.conj a⁻¹) ∈ F x}`;
* `Rat.Source.F_add`, `Rat.Source.FL_add` : the sum case;
* `Rat.Source.F_mul`, `Rat.Source.FL_mul` : the product case for two words.

Here the four lemmas are taken as *hypotheses*, so that this file can be checked independently of
them; `Rat/Source/Main.lean` applies them.

The induction is on the complexity `Rat.treeOfRat U x` and proves, for every `x`, both
`∃ S, IsLeastF x S` and `∃ S, IsLeastL x S`.  The `⋄`-case uses the duality
`Rat.F_ratOp_eq_FL` (`isLeastF_ratOp`, `isLeastL_ratOp` in `Rat/Source/Setup.lean`), and the base
cases are `isLeastF_zero`, `isLeastL_zero`, `isLeastF_ofGroup`, `isLeastL_ofGroup`.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-- **The induction.**  Assuming the four case lemmas, every element of `Rat(U)` has a least
element in `Rat.F` and in `Rat.FL`. -/
theorem exists_least_of_cases
    (hleft : ∀ (a : U) (x : RatU U),
      F (RatU.ofGroup a * x) = { V : Subgroup U | V.map (MulAut.conj a⁻¹) ∈ F x })
    (hadd : ∀ {y z : RatU U} {Sy Sz : Subgroup U} {uy uz : U}, y ≠ 0 → z ≠ 0 →
      IsLeastF y Sy → IsLeastF z Sz → y * RatU.ofGroup uy ∈ A Sy →
      z * RatU.ofGroup uz ∈ A Sz →
      ∀ V : Subgroup U, V ∈ F (y + z) ↔ Sy ≤ V ∧ Sz ≤ V ∧ uy⁻¹ * uz ∈ V)
    (hladd : ∀ {y z : RatU U} {Sy Sz : Subgroup U} {uy uz : U}, y ≠ 0 → z ≠ 0 →
      IsLeastL y Sy → IsLeastL z Sz → RatU.ofGroup uy * y ∈ A Sy →
      RatU.ofGroup uz * z ∈ A Sz →
      ∀ V : Subgroup U, V ∈ FL (y + z) ↔ Sy ≤ V ∧ Sz ≤ V ∧ uy * uz⁻¹ ∈ V)
    (hmul : ∀ {y z : RatU U} {Sy Sz : Subgroup U} {uy : U}, RatU.IsWord y → RatU.IsWord z →
      IsLeastF y Sy → IsLeastF z Sz → y * RatU.ofGroup uy ∈ A Sy →
      ∀ V : Subgroup U, V ∈ F (y * z) ↔ Sy ≤ V ∧ Sz.map (MulAut.conj uy⁻¹) ≤ V)
    (hlmul : ∀ {y z : RatU U} {Sy Sz : Subgroup U} {uz : U}, RatU.IsWord y → RatU.IsWord z →
      IsLeastL y Sy → IsLeastL z Sz → RatU.ofGroup uz * z ∈ A Sz →
      ∀ V : Subgroup U, V ∈ FL (y * z) ↔ Sz ≤ V ∧ Sy.map (MulAut.conj uz) ≤ V) :
    ∀ x : RatU U, (∃ S : Subgroup U, IsLeastF x S) ∧ (∃ S : Subgroup U, IsLeastL x S) := by
  have key : ∀ t : Tree, ∀ x : RatU U, Rat.treeOfRat U x = t →
      (∃ S : Subgroup U, IsLeastF x S) ∧ (∃ S : Subgroup U, IsLeastL x S) := by
    intro t
    induction t using Tree.lt_wf.induction with
    | _ t ih =>
      intro x hxt
      rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨⟨⊥, isLeastF_zero⟩, ⟨⊥, isLeastL_zero⟩⟩
      rcases RatU.exists_decomp x hx0 with
        ⟨u, rfl⟩ | ⟨y, z, rfl, hyw, hzw, hlt1, hlt2⟩ |
          ⟨y, z, rfl, hy0, hz0, hlt1, hlt2⟩ | ⟨y, rfl, hlt⟩
      · -- `x = φu`
        exact ⟨⟨⊥, isLeastF_ofGroup u⟩, ⟨⊥, isLeastL_ofGroup u⟩⟩
      · -- `x = y·z`, both words
        have hy1 : Tree.lt (Rat.treeOfRat U y) t := by rwa [hxt] at hlt1
        have hz1 : Tree.lt (Rat.treeOfRat U z) t := by rwa [hxt] at hlt2
        obtain ⟨⟨Sy, hSy⟩, ⟨SLy, hSLy⟩⟩ := ih (Rat.treeOfRat U y) hy1 y rfl
        obtain ⟨⟨Sz, hSz⟩, ⟨SLz, hSLz⟩⟩ := ih (Rat.treeOfRat U z) hz1 z rfl
        obtain ⟨uy, huy⟩ := (nonempty_T_iff y Sy).mpr hSy.1
        have huyA : y * RatU.ofGroup uy ∈ A Sy := (mem_T_iff y Sy uy).mp huy
        obtain ⟨uz, huz⟩ := (nonempty_TL_iff z SLz).mpr hSLz.1
        refine ⟨⟨Sy ⊔ Sz.map (MulAut.conj uy⁻¹), ?_⟩,
          ⟨SLz ⊔ SLy.map (MulAut.conj uz), ?_⟩⟩
        · refine ⟨?_, ?_⟩
          · rw [hmul hyw hzw hSy hSz huyA]
            exact ⟨le_sup_left, le_sup_right⟩
          · intro V hV
            rw [hmul hyw hzw hSy hSz huyA] at hV
            exact sup_le hV.1 hV.2
        · refine ⟨?_, ?_⟩
          · rw [hlmul hyw hzw hSLy hSLz huz]
            exact ⟨le_sup_left, le_sup_right⟩
          · intro V hV
            rw [hlmul hyw hzw hSLy hSLz huz] at hV
            exact sup_le hV.1 hV.2
      · -- `x = y + z`
        have hy1 : Tree.lt (Rat.treeOfRat U y) t := by rwa [hxt] at hlt1
        have hz1 : Tree.lt (Rat.treeOfRat U z) t := by rwa [hxt] at hlt2
        obtain ⟨⟨Sy, hSy⟩, ⟨SLy, hSLy⟩⟩ := ih (Rat.treeOfRat U y) hy1 y rfl
        obtain ⟨⟨Sz, hSz⟩, ⟨SLz, hSLz⟩⟩ := ih (Rat.treeOfRat U z) hz1 z rfl
        obtain ⟨uy, huy⟩ := (nonempty_T_iff y Sy).mpr hSy.1
        obtain ⟨uz, huz⟩ := (nonempty_T_iff z Sz).mpr hSz.1
        obtain ⟨uy', huy'⟩ := (nonempty_TL_iff y SLy).mpr hSLy.1
        obtain ⟨uz', huz'⟩ := (nonempty_TL_iff z SLz).mpr hSLz.1
        have huyA : y * RatU.ofGroup uy ∈ A Sy := (mem_T_iff y Sy uy).mp huy
        have huzA : z * RatU.ofGroup uz ∈ A Sz := (mem_T_iff z Sz uz).mp huz
        refine ⟨⟨Sy ⊔ Sz ⊔ Subgroup.zpowers (uy⁻¹ * uz), ?_⟩,
          ⟨SLy ⊔ SLz ⊔ Subgroup.zpowers (uy' * uz'⁻¹), ?_⟩⟩
        · refine ⟨?_, ?_⟩
          · rw [hadd hy0 hz0 hSy hSz huyA huzA]
            have hg : Subgroup.zpowers (uy⁻¹ * uz) ≤ Sy ⊔ Sz ⊔ Subgroup.zpowers (uy⁻¹ * uz) :=
              le_sup_right
            exact ⟨le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left,
              hg (Subgroup.mem_zpowers _)⟩
          · intro V hV
            rw [hadd hy0 hz0 hSy hSz huyA huzA] at hV
            exact sup_le (sup_le hV.1 hV.2.1)
              (Subgroup.zpowers_le.mpr hV.2.2)
        · refine ⟨?_, ?_⟩
          · rw [hladd hy0 hz0 hSLy hSLz huy' huz']
            have hg : Subgroup.zpowers (uy' * uz'⁻¹) ≤
                SLy ⊔ SLz ⊔ Subgroup.zpowers (uy' * uz'⁻¹) := le_sup_right
            exact ⟨le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left,
              hg (Subgroup.mem_zpowers _)⟩
          · intro V hV
            rw [hladd hy0 hz0 hSLy hSLz huy' huz'] at hV
            exact sup_le (sup_le hV.1 hV.2.1)
              (Subgroup.zpowers_le.mpr hV.2.2)
      · -- `x = y⋄`
        have hy1 : Tree.lt (Rat.treeOfRat U y) t := by rwa [hxt] at hlt
        obtain ⟨hF, hL⟩ := ih (Rat.treeOfRat U y) hy1 y rfl
        exact ⟨hL.imp (fun _ h => isLeastF_ratOp h), hF.imp (fun _ h => isLeastL_ratOp h)⟩
  exact fun x => key (Rat.treeOfRat U x) x rfl

end Work.ORHughesFree.Rat

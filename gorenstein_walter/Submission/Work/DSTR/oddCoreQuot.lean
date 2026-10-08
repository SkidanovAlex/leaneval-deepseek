import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.ASM.oddCore_odd

/-!
# DS2: `O(X/O(X)) = 1`

`Work.GW2.oddCore X = (sSup {N | N.Normal ∧ Odd (Nat.card N)}).normalCore` is the largest normal
subgroup of odd order (`Work.ASM.oddCore_odd` supplies that it really is odd).  The statement

`oddCore (X ⧸ oddCore X) = ⊥`

is proved here by the argument described in the docstring of the target: pull a normal odd subgroup
`M` of the quotient back to `X`.

* `N := M.comap π` is normal in `X` (`Subgroup.Normal.comap`), where `π = QuotientGroup.mk' (oddCore X)`;
* `Nat.card N = Nat.card (oddCore X) * Nat.card M`; indeed `π` restricts to a surjection
  `N ↠ M` with kernel `(oddCore X).subgroupOf N`, and the quotient of `N` by it has the same
  cardinality as `M` (`card_comap_of_surjective` below).  Both factors are odd, so `Odd (Nat.card N)`;
* hence `N ≤ oddCore X` (`le_oddCore_of_odd_normal`, the universal property of the odd core), and
  since conversely `oddCore X = π.ker ≤ N`, we get `N = oddCore X`, so `M = π(N) = 1`.

Consequently the `sSup` defining `oddCore (X ⧸ oddCore X)` is `⊥`, and its `normalCore` is `⊥` too.

The two lemmas below are private: they are pieces of this proof, not part of the area interface.
-/

namespace Work.DSTR

open scoped MatrixGroups

/-- For a surjective homomorphism `f : A →* B` and a subgroup `M ≤ B`, the pullback `M.comap f`
has order `|ker f| * |M|`: `f` restricts to a surjection `M.comap f ↠ M` with kernel
`f.ker.subgroupOf (M.comap f)`, and `Nat.card` is multiplicative over this quotient. -/
private theorem card_comap_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (M : Subgroup B) :
    Nat.card (M.comap f) = Nat.card f.ker * Nat.card M := by
  have hker : f.ker ≤ M.comap f := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact M.one_mem
  let φ : (M.comap f) →* M :=
    { toFun := fun x => ⟨f x, x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφ : Function.Surjective φ := by
    intro m
    obtain ⟨x, hx⟩ := hf ↑m
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap]; rw [hx]; exact m.2
    · ext; simp [φ, hx]
  have hker_eq : φ.ker = f.ker.subgroupOf (M.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  calc Nat.card (M.comap f)
      = Nat.card ((M.comap f) ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    _ = Nat.card M * Nat.card (f.ker.subgroupOf (M.comap f)) := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
            ← hker_eq]
    _ = Nat.card M * Nat.card f.ker := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv]
    _ = Nat.card f.ker * Nat.card M := Nat.mul_comm _ _

/-- **Universal property of the odd core.**  A normal subgroup of odd order lies in `O(G)`. -/
private theorem le_oddCore_of_odd_normal {G : Type*} [Group G] {N : Subgroup G} (hNn : N.Normal)
    (hNo : Odd (Nat.card N)) : N ≤ Work.GW2.oddCore G := by
  have : N.Normal := hNn
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNn, hNo⟩)

/-- **DS2** (`Work.GW2.OddCoreQuotProp`): `O(X/O(X)) = 1`.  A normal odd subgroup of `X/O(X)` pulls back to a normal odd subgroup of `X`, hence lies in the kernel. -/
theorem oddCoreQuot : Work.GW2.OddCoreQuotProp := by
  intro X _ _
  have hKodd : Odd (Nat.card (Work.GW2.oddCore X)) := Work.ASM.oddCore_odd X
  -- every normal odd subgroup `M` of `X ⧸ O(X)` is trivial; hence the defining `sSup` is `⊥`
  have hsup : sSup {M : Subgroup (X ⧸ Work.GW2.oddCore X) |
      M.Normal ∧ Odd (Nat.card M)} = ⊥ := by
    rw [← le_bot_iff]
    apply sSup_le
    rintro M ⟨hMn, hMo⟩
    intro m hm
    rw [Subgroup.mem_bot]
    -- `m` is the image of some `x ∈ X`
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Work.GW2.oddCore X) m
    -- the pullback `N = M.comap π` is normal ...
    have hNnorm : (M.comap (QuotientGroup.mk' (Work.GW2.oddCore X))).Normal :=
      hMn.comap _
    -- ... and odd, since `|N| = |O(X)| * |M|`
    have hcard : Nat.card (M.comap (QuotientGroup.mk' (Work.GW2.oddCore X)))
        = Nat.card (Work.GW2.oddCore X) * Nat.card M := by
      rw [card_comap_of_surjective _ (QuotientGroup.mk'_surjective (Work.GW2.oddCore X)) M,
        QuotientGroup.ker_mk']
    have hNodd : Odd (Nat.card (M.comap (QuotientGroup.mk' (Work.GW2.oddCore X)))) := by
      rw [hcard]; exact hKodd.mul hMo
    -- so `N ≤ O(X)`, and `x` lies in `N` because `π x = m ∈ M`
    exact (QuotientGroup.eq_one_iff x).mpr (le_oddCore_of_odd_normal hNnorm hNodd hm)
  show (sSup {M : Subgroup (X ⧸ Work.GW2.oddCore X) |
    M.Normal ∧ Odd (Nat.card M)}).normalCore = ⊥
  rw [hsup]
  exact Subgroup.normalCore_eq_self ⊥

end Work.DSTR

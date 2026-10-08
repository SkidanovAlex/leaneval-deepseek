import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centralizer of a maximal abelian normal subgroup of a `p`-group

Let `P` be a finite `p`-subgroup of a group `G` and let `A ≤ P` be abelian and normal in `P`,
maximal with these properties among subgroups of `P`.  Then

`P ⊓ C_G(A) = A`,

i.e. `A` is self-centralizing in `P`.

This is the standard fact that a maximal abelian normal subgroup of a nilpotent group is
self-centralizing (see Gorenstein, *Finite Groups*, §5.3), applied to the `p`-group `P` and
transported back to the ambient group `G`.  The proof runs the usual upper central series
argument inside the nilpotent group `↥P`: if `C = C_P(A)` and `Z₀ ≤ Z₁ ≤ ⋯` is the upper central
series of `P`, one shows `C ⊓ Zᵢ ≤ A` by induction, whence `C = C ⊓ P = C ⊓ Z_n ≤ A`.

## Main results

* `Work.PGroup.centralizer_inf_eq_of_maximal_normal_abelian`
* `Work.PGroup.centralizer_eq_of_maximal_normal_abelian_of_nilpotent` (the nilpotent-group form)

## References

* D. Gorenstein, *Finite Groups*, Harper & Row, 1968, §5.3.
* W. Feit, J. G. Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13** (1963).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise
open Subgroup
open scoped commutatorElement

noncomputable section

namespace Work.PGroup

variable {G : Type*} [Group G]

/-- Conjugation by `g` sends `x` into `H` whenever `H` is invariant under conjugation by `g`. -/
theorem conjBy_mul_mem {H : Subgroup G} {g x : G} (h : conjBy g H = H) (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H := by
  have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) H hx
  rw [show MulAut.conj g • H = H from h, MulAut.smul_def, MulAut.conj_apply] at this
  exact this

/-- The centralizer of `A ≤ H`, taken inside `H`, agrees with the subgroup of `↥H` obtained from
the centralizer of `A` in `G`. -/
theorem centralizer_subgroupOf (H A : Subgroup G) (hA : A ≤ H) :
    (Subgroup.centralizer (A : Set G)).subgroupOf H
      = Subgroup.centralizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    apply Subtype.ext
    exact h (y : G) (Subgroup.mem_subgroupOf.mp hy)
  · intro h a ha
    have hmem : (⟨a, hA ha⟩ : ↥H) ∈ A.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact ha
    exact congrArg Subtype.val (h ⟨a, hA ha⟩ hmem)

/-- `B.map H.subtype` is invariant under conjugation by `g ∈ H` whenever `B ≤ ↥H` is. -/
theorem map_subtype_conj_eq_self (H : Subgroup G) (B : Subgroup ↥H)
    (hBnorm : ∀ g : ↥H, MulAut.conj g • B = B) (g : G) (hg : g ∈ H) :
    MulAut.conj g • (B.map H.subtype) = B.map H.subtype := by
  have hle : ∀ g ∈ H, MulAut.conj g • (B.map H.subtype) ≤ B.map H.subtype := by
    intro g hg x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map] at hx
    obtain ⟨b, hb, hbeq⟩ := hx
    have hbeq' : (b : G) = g⁻¹ * x * g := by simpa using hbeq
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hg⟩ * b * ⟨g, hg⟩⁻¹, conjBy_mul_mem (hBnorm ⟨g, hg⟩) hb, ?_⟩
    have hgoal : g * (b : G) * g⁻¹ = x := by rw [hbeq']; group
    simpa using hgoal
  refine le_antisymm (hle g hg) ?_
  calc B.map H.subtype = MulAut.conj g • (MulAut.conj g⁻¹ • (B.map H.subtype)) := by simp
    _ ≤ MulAut.conj g • (B.map H.subtype) := Subgroup.map_mono (hle g⁻¹ (H.inv_mem hg))

/-- Commutativity is preserved by `B ↦ B.map H.subtype`. -/
theorem map_subtype_isMulCommutative (H : Subgroup G) (B : Subgroup ↥H)
    (hBcomm : IsMulCommutative B) : IsMulCommutative (B.map H.subtype) := by
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp y.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hbx, ← hcy, ← map_mul, ← map_mul]
  have hbc : b * c = c * b :=
    congrArg Subtype.val (isMulCommutative_iff.mp hBcomm ⟨b, hb⟩ ⟨c, hc⟩)
  rw [hbc]

/-- **A maximal abelian normal subgroup of a nilpotent group is self-centralizing.**

Let `G` be nilpotent and `A ≤ G` abelian and normal, maximal among abelian normal subgroups.
Then `C_G(A) = A`.

The proof uses the upper central series `Zᵢ` of `G`: one shows `C_G(A) ⊓ Zᵢ ≤ A` by induction on
`i`.  Indeed, if `h ∈ C_G(A) ⊓ Z_{i+1}` then `⁅h, g⁆ ∈ C_G(A) ⊓ Zᵢ ≤ A` for every `g`, so that
`A⟨h⟩` is a normal abelian subgroup of `G`; maximality of `A` forces `h ∈ A`.  Since `Z_n = ⊤`
for some `n`, the claim follows. -/
theorem centralizer_eq_of_maximal_normal_abelian_of_nilpotent {G : Type*} [Group G]
    [Group.IsNilpotent G] {A : Subgroup G}
    (hAn : ∀ g : G, MulAut.conj g • A = A) (hA : IsMulCommutative A)
    (hmax : ∀ B : Subgroup G, (∀ g : G, MulAut.conj g • B = B) →
      IsMulCommutative B → A ≤ B → B = A) :
    Subgroup.centralizer (A : Set G) = A := by
  haveI : A.Normal := Subgroup.Normal.of_conjugate_fixed hAn
  have hCnorm : (Subgroup.centralizer (A : Set G)).Normal := Subgroup.normal_centralizer
  have hAleC : A ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer A
  obtain ⟨s, hs⟩ := Group.IsNilpotent.nilpotent G
  have key : ∀ i : ℕ,
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.upperCentralSeries G i ≤ A := by
    intro i
    induction i with
    | zero => simp [Subgroup.upperCentralSeries_zero]
    | succ i ih =>
      intro h hh
      rw [Subgroup.mem_inf] at hh
      obtain ⟨hhC, hhZ⟩ := hh
      have hcomm : ∀ g : G, ⁅h, g⁆ ∈ A := by
        intro g
        have h1 : ⁅h, g⁆ ∈ Subgroup.upperCentralSeries G i :=
          (Subgroup.mem_upperCentralSeries_succ_iff.mp hhZ) g
        have h2 : ⁅h, g⁆ ∈ Subgroup.centralizer (A : Set G) := by
          have h2a : g * h⁻¹ * g⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
            hCnorm.conj_mem h⁻¹ ((Subgroup.centralizer (A : Set G)).inv_mem hhC) g
          have h2b : h * (g * h⁻¹ * g⁻¹) ∈ Subgroup.centralizer (A : Set G) :=
            (Subgroup.centralizer (A : Set G)).mul_mem hhC h2a
          rw [commutatorElement_def]
          simpa only [mul_assoc] using h2b
        exact ih (Subgroup.mem_inf.mpr ⟨h2, h1⟩)
      set B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {h}) with hB
      have hAB : A ≤ B := by
        rw [hB]
        calc A = Subgroup.closure (A : Set G) := (Subgroup.closure_eq A).symm
          _ ≤ Subgroup.closure ((A : Set G) ∪ {h}) := Subgroup.closure_mono Set.subset_union_left
      have hhB : h ∈ B := by
        rw [hB]
        exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
      have hBcomm : IsMulCommutative B := by
        rw [hB]
        apply Subgroup.isMulCommutative_closure
        rintro x hx y hy hne
        rw [Set.mem_union, Set.mem_singleton_iff] at hx hy
        rcases hx with hxA | hxh
        · rcases hy with hyA | hyh
          · exact (commute_iff_eq x y).mpr
              (congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨x, hxA⟩ ⟨y, hyA⟩))
          · rw [hyh]
            exact (commute_iff_eq x h).mpr (Subgroup.mem_centralizer_iff.mp hhC x hxA)
        · rw [hxh]
          rcases hy with hyA | hyh
          · exact (commute_iff_eq h y).mpr (Subgroup.mem_centralizer_iff.mp hhC y hyA).symm
          · exact absurd (hxh.trans hyh.symm) hne
      have hgh : ∀ g : G, g * h * g⁻¹ ∈ B := by
        intro g
        have h1 : g * h * g⁻¹ * h⁻¹ ∈ A := by
          have h2 : (h * g * h⁻¹ * g⁻¹)⁻¹ = g * h * g⁻¹ * h⁻¹ := by group
          rw [← h2]
          exact A.inv_mem (by simpa [commutatorElement_def] using hcomm g)
        rw [show g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h by group]
        exact B.mul_mem (hAB h1) hhB
      have hle_aux : ∀ g : G, MulAut.conj g • B ≤ B := by
        intro g
        rw [hB, Subgroup.smul_closure, Set.smul_set_union, Set.smul_set_singleton,
          ← Subgroup.coe_pointwise_smul (MulAut.conj g) A, hAn g]
        refine (Subgroup.closure_le _).mpr ?_
        rintro x (hx | hx)
        · exact hAB hx
        · rw [Set.mem_singleton_iff] at hx
          rw [hx, MulAut.smul_def, MulAut.conj_apply]
          exact hgh g
      have hBnorm : ∀ g : G, MulAut.conj g • B = B := by
        intro g
        refine le_antisymm (hle_aux g) ?_
        calc B = MulAut.conj g • (MulAut.conj g⁻¹ • B) := by simp
          _ ≤ MulAut.conj g • B := Subgroup.map_mono (hle_aux g⁻¹)
      have := hmax B hBnorm hBcomm hAB
      rw [this] at hhB
      exact hhB
  refine le_antisymm ?_ hAleC
  have := key s
  rw [hs, inf_top_eq] at this
  exact this

theorem centralizer_inf_eq_of_maximal_normal_abelian {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) (P A : Subgroup G)
    [Finite P] (hP : IsPGroup p P) (hA : A ≤ P)
    (hAnorm : ∀ g : G, g ∈ P → Work.PGroup.conjBy g A = A) (hab : IsMulCommutative A)
    (hmax : ∀ B : Subgroup G, B ≤ P → (∀ g : G, g ∈ P → Work.PGroup.conjBy g B = B) →
      IsMulCommutative B → A ≤ B → B = A) :
    P ⊓ Subgroup.centralizer (A : Set G) = A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hA'norm : (A.subgroupOf P).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conjBy_mul_mem (hAnorm (g : G) g.2) hn
    simpa using this
  have hA'conj : ∀ g : ↥P, MulAut.conj g • (A.subgroupOf P) = A.subgroupOf P :=
    fun g => Subgroup.Normal.conj_smul_eq_self g (A.subgroupOf P)
  have hA'comm : IsMulCommutative (A.subgroupOf P) :=
    @Subgroup.comap_injective_isMulCommutative _ _ _ _ A P.subtype Subtype.coe_injective hab
  have hmax' : ∀ B : Subgroup ↥P, (∀ g : ↥P, MulAut.conj g • B = B) →
      IsMulCommutative B → A.subgroupOf P ≤ B → B = A.subgroupOf P := by
    intro B hBnorm hBcomm hAB
    have hBnorm' : ∀ g : G, g ∈ P → MulAut.conj g • (B.map P.subtype) = B.map P.subtype :=
      fun g hg => map_subtype_conj_eq_self P B hBnorm g hg
    have hBcomm' : IsMulCommutative (B.map P.subtype) :=
      map_subtype_isMulCommutative P B hBcomm
    have hBmap : (B.map P.subtype).subgroupOf P = B := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨b, hb, hbeq⟩
        have : b = x := Subtype.ext hbeq
        rwa [← this]
      · exact fun hx => ⟨x, hx, rfl⟩
    have hAB' : A ≤ B.map P.subtype := by
      intro a ha
      exact Subgroup.mem_map.mpr
        ⟨⟨a, hA ha⟩, hAB (by rw [Subgroup.mem_subgroupOf]; exact ha), rfl⟩
    have hthis := hmax (B.map P.subtype) (Subgroup.map_subtype_le B) hBnorm' hBcomm' hAB'
    rw [← hBmap, hthis]
  have hmain := centralizer_eq_of_maximal_normal_abelian_of_nilpotent hA'conj hA'comm hmax'
  have h1 : (Subgroup.centralizer (A : Set G)).subgroupOf P = A.subgroupOf P := by
    rw [centralizer_subgroupOf P A hA, hmain]
  have h2 : (A.subgroupOf P).map P.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA
  have h3 : Subgroup.centralizer (A : Set G) ⊓ P = A := by
    rw [← Subgroup.subgroupOf_map_subtype (Subgroup.centralizer (A : Set G)) P, h1, h2]
  rw [inf_comm]
  exact h3

end Work.PGroup

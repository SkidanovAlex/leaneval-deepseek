import Mathlib
import Submission.Work.ORHughesFree.Section6.SubgroupComplexity
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Rat.source_subgroup_exists
import Submission.Work.ORHughesFree.Rat.Restrict
import Submission.Work.ORHughesFree.Section6.treeG_Phi_mul_ofGroup
import Submission.Work.ORHughesFree.Section6.UnitsTimesEquiv
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.Rat.MapHom
import Submission.Work.ORHughesFree.Rat.treeOfRat_mapHom
import Submission.Work.ORHughesFree.Rat.mapHom_ofSubgroup
import Submission.Work.ORHughesFree.Section6.ofSubgroup_ratUnitsTimesEquiv
import Submission.Work.ORHughesFree.Section6.map_map_snd_insertion

namespace Work.ORHughesFree.Section6

/-- **The source-based finitely generated reduction of [JZLA20, Theorem 6.1].**  For every
`a ∈ D_{K[G],U}` there is a finitely generated subgroup `H ≤ G`, an element `α ∈ Rat(Kˣ × H)` and a
group unit `u ∈ Kˣ × G` such that, writing `a' = Φ (ofSubgroup (ratUnitsTimesEquiv H α))` (an
element of the division closure with the same complexity as `a`):

* `a' = a * φ (unitOf u)`, i.e. `a'` is `a` multiplied by the unit `φ (unitOf u)` of `D`;
* `Tree_G a' = Tree_G a`;
* `Tree α = Tree_G a'` — α realises the complexity of `a'`;
* `α` is *minimal*: every `β` with the same image satisfies `Tree α ≤ Tree β`;
* `H` is contained in the image in `G` of the source of `α`, in the strong form: for every subgroup
  `V ≤ Kˣ × H`, every `v ∈ Kˣ × H` and `e : Rat ↥V` with `ofSubgroup V e * ofGroup v = α`, the
  image of `V` in `H` under `snd`, viewed in `G`, contains `H`.

Construct it from [DHS04, Theorem 5.7] (`Rat.source_subgroup_exists`): take a minimal realiser
`α₀ ∈ Rat(Kˣ × G)` of the `G`-complexity of `a`, write `α₀ = β * ofGroup w` with `β ∈ Rat(S)`,
`S := source(α₀)` finitely generated, and set `H := S.map snd`, `u := w`.  Since `S ≤ Kˣ × H`, the
element `β` is the image of an element `α ∈ Rat(Kˣ × H)` under `ofSubgroup S` composed with the
transport `ratUnitsTimesEquiv H` (`UnitsTimesEquiv.lean`), and `Tree α = Tree β`
(`Rat.treeOfRat_ofSubgroup` and `treeOfRat_ratUnitsTimesEquiv`).  The first clause is
`Phi φ α₀ = a` together with `Phi_ofGroup`; the second is `treeG_Phi_mul_ofGroup`; the third gives
minimality, using `Tree β = Tree α₀`.  The last clause is the leastness of the source:
`S ∈ F(α₀)` and `F(β) = F(α₀)` (the two differ by the unit `ofGroup w`), so `S ≤ V` for every
`V ∈ F(β)`, whence `H ≤ snd '' V`. -/
theorem exists_source_reduction {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (a : ↥(divisionClosure (Set.range φ))) :
    ∃ (H : Subgroup G) (α : RatU (Kˣ × H)) (u : Kˣ × G),
      H.FG ∧
      ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H α)) : U) = (a : U) * φ (unitOf u) ∧
      treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
          (ratUnitsTimesEquiv (K := K) H α))) = treeG φ a ∧
      Rat.treeOfRat (Kˣ × H) α
        = treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H α))) ∧
      (∀ β : RatU (Kˣ × H),
        (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
            (ratUnitsTimesEquiv (K := K) H β))
          = (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H)
              (ratUnitsTimesEquiv (K := K) H α)) →
        Tree.le (Rat.treeOfRat (Kˣ × H) α) (Rat.treeOfRat (Kˣ × H) β)) ∧
      (∀ (V : Subgroup (Kˣ × H)) (v : Kˣ × H) (e : RatU ↥V),
        RatU.ofSubgroup V e * RatU.ofGroup v = α →
        H ≤ (V.map (MonoidHom.snd Kˣ H)).map (Subgroup.subtype H)) := by
  classical
  -- a minimal `G`-realiser of `a`
  obtain ⟨α₀, hα₀, htree₀⟩ := (treeG_spec φ a).1
  -- the (finitely generated) source of `α₀`
  obtain ⟨S, hSfg, ⟨w, β, hβ⟩, hleast⟩ := Rat.source_subgroup_exists α₀
  -- `H := snd '' S`, and `T = Kˣ × H` viewed inside `Kˣ × G`
  let H : Subgroup G := S.map (MonoidHom.snd Kˣ G)
  have hHfg : H.FG := Subgroup.fg_map S (MonoidHom.snd Kˣ G) hSfg
  let T : Subgroup (Kˣ × G) := unitsTimesSubgroup (K := K) H
  have hST : S ≤ T := fun x hx => mem_unitsTimesSubgroup.mpr ⟨x, hx, rfl⟩
  let j : ↥S →* ↥T := Subgroup.inclusion hST
  -- the element of `Rat(Kˣ × H)` corresponding to `β ∈ Rat(S)`
  let A : RatU (Kˣ × H) := (ratUnitsTimesEquiv (K := K) H).symm (RatU.mapHom j β)
  have hA : ratUnitsTimesEquiv (K := K) H A = RatU.mapHom j β :=
    (ratUnitsTimesEquiv (K := K) H).apply_symm_apply _
  have hAT : RatU.ofSubgroup T (ratUnitsTimesEquiv (K := K) H A) = RatU.ofSubgroup S β := by
    rw [hA]
    exact RatU.ofSubgroup_mapHom_inclusion hST β
  -- the image of `A` under `Φ` is `Φ β`, hence has `G`-complexity `Tree_G a`
  have hgtree : treeG φ ((Phi φ) (RatU.ofSubgroup T (ratUnitsTimesEquiv (K := K) H A)))
      = treeG φ a := by
    rw [hAT, ← hα₀, ← hβ, treeG_Phi_mul_ofGroup]
  -- `Tree A = Tree α₀`
  have htreeA : Rat.treeOfRat (Kˣ × H) A = Rat.treeOfRat (Kˣ × G) α₀ := by
    rw [← treeOfRat_ratUnitsTimesEquiv (K := K) H A, hA, Rat.treeOfRat_mapHom j β,
      ← Rat.treeOfRat_ofSubgroup S β, ← hβ, RatU.treeOfRat_mul_ofGroup]
  -- clause 1: `Φ A = a * φ (unitOf w⁻¹)`
  have hw : ((Phi φ) (RatU.ofGroup w) : U) = φ (unitOf w) := by
    rw [Phi_ofGroup]; rfl
  have hco : (a : U) = ((Phi φ) (RatU.ofSubgroup S β) : U) * φ (unitOf w) := by
    rw [← hα₀, ← hβ, map_mul, Subring.coe_mul, hw]
  have hmunit : φ (unitOf w) * φ (unitOf w⁻¹) = 1 := by
    rw [← map_mul, ← unitOf_mul, mul_inv_cancel, unitOf_one, map_one]
  have hgoal1 : ((Phi φ) (RatU.ofSubgroup T (ratUnitsTimesEquiv (K := K) H A)) : U)
      = (a : U) * φ (unitOf w⁻¹) := by
    rw [hAT, hco, mul_assoc, hmunit, mul_one]
  refine ⟨H, A, w⁻¹, hHfg, hgoal1, hgtree, ?_, ?_, ?_⟩
  · -- clause 3: `Tree A = Tree_G a'`
    rw [htreeA, htree₀]
    exact hgtree.symm
  · -- clause 4: minimality of `α` among the realisers of `a'`
    intro β' hβ'
    have hγ : (Phi φ) (RatU.ofSubgroup T (ratUnitsTimesEquiv (K := K) H β'))
        = (Phi φ) (RatU.ofSubgroup S β) := by
      rw [hβ', hAT]
    have hP : (Phi φ) (RatU.ofSubgroup T (ratUnitsTimesEquiv (K := K) H β')
        * RatU.ofGroup w) = a := by
      rw [map_mul, hγ, ← map_mul, hβ, hα₀]
    have hmin := (treeG_spec φ a).2 _ hP
    rw [RatU.treeOfRat_mul_ofGroup,
      Rat.treeOfRat_ofSubgroup T (ratUnitsTimesEquiv (K := K) H β'),
      treeOfRat_ratUnitsTimesEquiv (K := K) H β'] at hmin
    rw [htreeA, htree₀]
    exact hmin
  · -- clause 5: leastness of the source
    intro V v e he
    set ins : Kˣ × H →* Kˣ × G :=
      MonoidHom.prodMap (MonoidHom.id Kˣ) (Subgroup.subtype H) with hins
    have hmap : RatU.mapHom ins A = RatU.ofSubgroup S β := by
      rw [hins, ← hAT, ofSubgroup_ratUnitsTimesEquiv (K := K) H A]
    have hnat : RatU.mapHom ins (RatU.ofSubgroup V e)
        = RatU.ofSubgroup (V.map ins) (RatU.mapHom (ins.subgroupMap V) e) :=
      Rat.mapHom_ofSubgroup ins V e
    have h1 : RatU.ofSubgroup (V.map ins) (RatU.mapHom (ins.subgroupMap V) e)
        * RatU.ofGroup (ins v) = RatU.ofSubgroup S β := by
      rw [← hnat, ← RatU.mapHom_ofGroup ins v, ← map_mul, he, hmap]
    have heq : RatU.ofSubgroup (V.map ins) (RatU.mapHom (ins.subgroupMap V) e)
        * RatU.ofGroup (ins v * w) = α₀ := by
      rw [RatU.ofGroup_mul, ← mul_assoc, h1, hβ]
    have hSle : S ≤ V.map ins :=
      hleast (V.map ins) (ins v * w) (RatU.mapHom (ins.subgroupMap V) e) heq
    have h2 : H ≤ (V.map ins).map (MonoidHom.snd Kˣ G) := Subgroup.map_mono hSle
    rw [hins] at h2
    rw [map_map_snd_insertion (K := K) H V] at h2
    exact h2

end Work.ORHughesFree.Section6

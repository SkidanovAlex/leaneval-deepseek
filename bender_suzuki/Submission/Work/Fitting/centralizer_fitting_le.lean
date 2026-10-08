import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Fitting subgroup is self-centralizing in a solvable group

`Work.Fitting.fitting G`, the Fitting subgroup `F(G)`, is the supremum of the normal
nilpotent subgroups of `G`.  The main result here is

`Work.Fitting.centralizer_fitting_le` : if `G` is finite and solvable, then every element
centralizing `F(G)` already lies in `F(G)`, i.e. `C_G(F(G)) ≤ F(G)`.

The proof: set `F = F(G)`, `C = C_G(F)` and `Z = C ⊓ F`.  We show `C ≤ F`, i.e. that
the image `C̄` of `C` in `G/(C ⊓ F)` is trivial.  If not, `C̄` is a nontrivial normal subgroup
of the solvable group `G/(C ⊓ F)`, so it contains a nontrivial abelian normal subgroup `M̄`
(a suitable term of its derived series).  Its preimage `M` is a normal subgroup of `G`,
contained in `C`, with `M/(C ⊓ F) = M̄`.  Since `M ≤ C` centralizes `F ⊇ Z` and `Z ≤ Z(M)`,
the group `M` is an extension of an abelian group by a central subgroup, hence nilpotent;
being normal it then lies in `F(G) = F`.  But then `M ≤ C ⊓ F = Z`, contradicting `M/Z = M̄ ≠ 1`.
-/

noncomputable section

open Classical
open scoped commutatorElement

namespace Work.Fitting

/-- **Key descent lemma.** In a finite solvable group `Q`, every nontrivial normal subgroup
`Cb` contains a nontrivial abelian subgroup `Mb` which is still normal in `Q`.

Such an `Mb` is obtained as a suitable nontrivial term of the derived series of `Cb`
(which is characteristic in `Cb`, hence normal in `Q`); the strict decrease
`⁅N, N⁆ < N` for nontrivial `N` in a solvable group supplies the induction. -/
theorem exists_abelian_normal_le (Q : Type*) [Group Q] [Finite Q] [Group.IsSolvable Q] :
    ∀ Cb : Subgroup Q, Cb.Normal → Cb ≠ ⊥ →
      ∃ Mb : Subgroup Q, Mb.Normal ∧ Mb ≤ Cb ∧ Mb ≠ ⊥ ∧ IsMulCommutative ↥Mb := by
  intro Cb
  induction Cb using WellFoundedLT.induction with
  | ind Cb ih =>
    intro hCb hne
    haveI : Cb.Normal := hCb
    by_cases hcomm : ⁅Cb, Cb⁆ = ⊥
    · exact ⟨Cb, hCb, le_rfl, hne, (Subgroup.commutator_self_eq_bot_iff).mp hcomm⟩
    · have hlt : ⁅Cb, Cb⁆ < Cb := Group.IsSolvable.commutator_lt_of_ne_bot hne
      have hnorm : (⁅Cb, Cb⁆).Normal := Subgroup.commutator_normal Cb Cb
      obtain ⟨Mb, h1, h2, h3, h4⟩ := ih ⁅Cb, Cb⁆ hlt hnorm hcomm
      exact ⟨Mb, h1, h2.trans (le_of_lt hlt), h3, h4⟩

/-- **The Fitting subgroup of a finite solvable group is self-centralizing.** -/
theorem centralizer_fitting_le (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    Subgroup.centralizer (Work.Fitting.fitting G : Set G) ≤ Work.Fitting.fitting G := by
  classical
  let F : Subgroup G := Work.Fitting.fitting G
  let C : Subgroup G := Subgroup.centralizer (F : Set G)
  let Z : Subgroup G := C ⊓ F
  change C ≤ F
  have hCnormal : C.Normal := Subgroup.normal_centralizer
  haveI : Z.Normal := inferInstance
  let π : G →* G ⧸ Z := QuotientGroup.mk' Z
  let Cb : Subgroup (G ⧸ Z) := Subgroup.map π C
  by_contra hle
  -- `C ≤ F` would follow from `Cb = ⊥`
  have hCbne : Cb ≠ ⊥ := by
    intro hbot
    apply hle
    have hCZ : C ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff C (f := π)).mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    exact hCZ.trans inf_le_right
  have hCbnorm : Cb.Normal := Subgroup.Normal.map hCnormal π (QuotientGroup.mk'_surjective Z)
  obtain ⟨Mb, hMbnorm, hMb_le, hMbne, hMbcomm⟩ :=
    exists_abelian_normal_le (G ⧸ Z) Cb hCbnorm hCbne
  haveI : IsMulCommutative ↥Mb := hMbcomm
  -- preimage of `Mb`
  let M : Subgroup G := Subgroup.comap π Mb
  have hπM : Subgroup.map π M = Mb :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) Mb
  have hMnorm : M.Normal := hMbnorm.comap π
  -- `M ≤ C`
  have hMleC : M ≤ C := by
    have h1 : M ≤ Subgroup.comap π (Subgroup.map π C) := Subgroup.comap_mono hMb_le
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr inf_le_left] at h1
    exact h1
  -- `M` is nilpotent, being a central extension of the abelian group `Mb`
  have hMnil : Group.IsNilpotent ↥M := by
    haveI : Group.IsNilpotent ↥Mb := inferInstance
    let f : ↥M →* ↥Mb := (π.comp M.subtype).codRestrict Mb (fun x => Subgroup.mem_comap.mp x.2)
    refine Subgroup.isNilpotent_of_ker_le_center f ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxZ : (x : G) ∈ Z := by
      have h1 : π (x : G) = 1 := by
        have := congrArg Subtype.val hx
        simpa [f] using this
      exact (QuotientGroup.eq_one_iff (x : G)).mp h1
    have hxF : (x : G) ∈ F := hxZ.2
    have hyC : (y : G) ∈ C := hMleC y.2
    have hcomm : (x : G) * (y : G) = (y : G) * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp hyC) (x : G) hxF
    exact Subtype.ext hcomm.symm
  have hMleF : M ≤ F := le_fitting hMnorm hMnil
  have hMleZ : M ≤ Z := le_inf hMleC hMleF
  have hmapZ : Subgroup.map π Z = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hMb_le_bot : Mb ≤ ⊥ := by
    rw [← hπM, ← hmapZ]
    exact Subgroup.map_mono hMleZ
  exact hMbne (le_bot_iff.mp hMb_le_bot)

end Work.Fitting

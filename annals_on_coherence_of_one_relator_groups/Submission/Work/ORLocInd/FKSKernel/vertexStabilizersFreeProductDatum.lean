import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.TreeDatum
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSReduction
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection
import Submission.Work.ORLocInd.FKSKernel.Kurosh.reducedSpan_vert_subset_repSet
import Submission.Work.ORLocInd.FKSKernel.Kurosh.nearestRep_projection
import Submission.Work.ORLocInd.FKSKernel.Kurosh.eq_of_smul_eq_self
import Submission.Work.ORLocInd.FKSKernel.Kurosh.nearestRep_smul_eq_vert
import Submission.Work.ORLocInd.FKSKernel.Kurosh.list_prod_ne_one
import Submission.Work.ORLocInd.FKSKernel.Kurosh.closure_vgroup_eq_top

namespace Work.ORLocInd.FKSKernel

universe u

open Work.ORLocInd.FKSKernel.Kurosh

theorem vertexStabilizersFreeProductDatum {Γ : Type u} {V : Type u} [Group Γ]
    [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction Γ V]
    [Work.ORBassSerre.GraphAction Γ V]
    (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions Γ V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer Γ e = ⊥)
    (hgen : Subgroup.closure (⋃ v : V, (MulAction.stabilizer Γ v : Set Γ)) = ⊤)
    (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum Γ V) :
    ∃ e : Monoid.CoprodI (fun A : Work.ORBassSerre.orbitV Γ V => ↥(d.vgroup A)) ≃* Γ,
      ∀ (A : Work.ORBassSerre.orbitV Γ V) (z : ↥(d.vgroup A)),
        e (Monoid.CoprodI.of z) = (z : Γ) := by
  classical
  -- the geometric input: the representatives span a subtree, so the nearest representative is
  -- a projection, and the vertex stabilisers act as a "trap"
  have hbetween : ∀ A B : Work.ORBassSerre.orbitV Γ V,
      Work.ORBassSerre.reducedSpan (d.vert A) (d.vert B) ⊆ repSet d :=
    fun A B => reducedSpan_vert_subset_repSet hT d A B
  obtain ⟨hmem, hproj, hfix, huniq⟩ := nearestRep_projection hT d hbetween
  have hfixpt : ∀ g : Γ, g ≠ 1 → ∀ x y : V, g • x = x → g • y = y → x = y :=
    fun g hg x y hx hy => eq_of_smul_eq_self hT hedge hg hx hy
  have hG : ∀ (A : Work.ORBassSerre.orbitV Γ V) (h : ↥(d.vgroup A)), (h : Γ) ≠ 1 → ∀ v : V,
      nearestRep hT d v ≠ d.vert A → nearestRep hT d ((h : Γ) • v) = d.vert A :=
    fun A h hne v hv => nearestRep_smul_eq_vert hT d hbetween hproj huniq hfix hfixpt A h hne v hv
  -- the reduced word lemma
  have hlist : ∀ (l : List (Σ A : Work.ORBassSerre.orbitV Γ V, ↥(d.vgroup A))),
      (∀ x ∈ l, (x.2 : Γ) ≠ 1) →
      List.IsChain (fun x y : Σ A : Work.ORBassSerre.orbitV Γ V, ↥(d.vgroup A) =>
        x.1 ≠ y.1) l →
      (l.map (fun x => (x.2 : Γ))).prod = 1 → l = [] :=
    fun l => list_prod_ne_one hT d hG l
  -- the vertex stabilisers of the representatives generate
  have htop : Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV Γ V, (d.vgroup A : Set Γ)) = ⊤ :=
    closure_vgroup_eq_top hT hninv hedge hgen d
  -- the assembly
  let M : Work.ORBassSerre.orbitV Γ V → Type u := fun A => ↥(d.vgroup A)
  let φ : Monoid.CoprodI M →* Γ := Monoid.CoprodI.lift fun A => (d.vgroup A).subtype
  have hφ_of : ∀ (A : Work.ORBassSerre.orbitV Γ V) (z : M A),
      φ (Monoid.CoprodI.of z) = (z : Γ) := fun A z => Monoid.CoprodI.lift_of _ z
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    let w : Monoid.CoprodI.Word M := Monoid.CoprodI.Word.equiv x
    have hprod : w.prod = x := by
      have h2 : Monoid.CoprodI.Word.equiv.symm (Monoid.CoprodI.Word.equiv x) = x :=
        Equiv.symm_apply_apply _ _
      have h3 : Monoid.CoprodI.Word.equiv.symm (Monoid.CoprodI.Word.equiv x)
          = (Monoid.CoprodI.Word.equiv x).prod := rfl
      rw [h3] at h2
      exact h2
    have hlistprod : (w.toList.map (fun l => (l.2 : Γ))).prod = 1 := by
      have h1 : (w.toList.map (fun l => (l.2 : Γ))).prod = φ w.prod := by
        rw [Monoid.CoprodI.Word.prod, map_list_prod]
        congr 1
        rw [List.map_map]
        rfl
      rw [h1, hprod, hx]
    have hne : ∀ y ∈ w.toList, (y.2 : Γ) ≠ 1 := by
      intro y hy h
      exact (w.ne_one y hy) (Subtype.ext h)
    have hempty : w.toList = [] := hlist w.toList hne w.chain_ne hlistprod
    rw [← hprod, Monoid.CoprodI.Word.prod, hempty]
    simp
  have hsurj : Function.Surjective φ := by
    have hle : Subgroup.closure (⋃ A : Work.ORBassSerre.orbitV Γ V, (d.vgroup A : Set Γ))
        ≤ φ.range := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨A, hxA⟩ := hx
      exact ⟨Monoid.CoprodI.of ⟨x, hxA⟩, hφ_of A ⟨x, hxA⟩⟩
    have htop' : (⊤ : Subgroup Γ) ≤ φ.range := by
      rw [← htop]
      exact hle
    exact MonoidHom.range_eq_top.mp (le_antisymm le_top htop')
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun A z => hφ_of A z⟩

end Work.ORLocInd.FKSKernel

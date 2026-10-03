import Mathlib

set_option linter.style.haveILetI false

namespace Work.ORBassSerre.FP

open Monoid

/-- The map on free products induced by a family of homomorphisms. -/
def freeProductMap {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]
    (f : ∀ i, M i →* N i) : Monoid.CoprodI M →* Monoid.CoprodI N :=
  Monoid.CoprodI.lift fun i => (Monoid.CoprodI.of : N i →* Monoid.CoprodI N).comp (f i)

@[simp]
lemma freeProductMap_of {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]
    (f : ∀ i, M i →* N i) (i : ι) (x : M i) :
    freeProductMap f (Monoid.CoprodI.of x) = Monoid.CoprodI.of (f i x) := by
  simp [freeProductMap]

lemma freeProductMap_surjective {ι : Type*} {M N : ι → Type*} [∀ i, Group (M i)]
    [∀ i, Group (N i)] (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (freeProductMap f) := by
  intro y
  induction y using Monoid.CoprodI.induction_on with
  | one => exact ⟨1, map_one _⟩
  | of i m => obtain ⟨x, hx⟩ := hf i m; exact ⟨Monoid.CoprodI.of x, by rw [freeProductMap_of, hx]⟩
  | mul a b ha hb => obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb
                     exact ⟨x * y, by rw [map_mul, hx, hy]⟩

/-- The kernel of the map induced by a family of surjective homomorphisms between free products
is the normal closure of the images of the kernels in the factors. -/
lemma freeProductMap_ker {ι : Type*} {M N : ι → Type*} [∀ i, Group (M i)] [∀ i, Group (N i)]
    (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Surjective (f i)) :
    (freeProductMap f).ker
      = Subgroup.normalClosure (⋃ i, (Monoid.CoprodI.of : M i →* Monoid.CoprodI M) '' (f i).ker) := by
  set S : Set (Monoid.CoprodI M) := ⋃ i, (Monoid.CoprodI.of : M i →* Monoid.CoprodI M) '' (f i).ker
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    let Q := Monoid.CoprodI M ⧸ Subgroup.normalClosure S
    have hle : ∀ i, (f i).ker ≤ ((QuotientGroup.mk' (Subgroup.normalClosure S)).comp
        (Monoid.CoprodI.of : M i →* Monoid.CoprodI M)).ker := by
      intro i y hy
      show (QuotientGroup.mk' (Subgroup.normalClosure S)) (Monoid.CoprodI.of y) = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact Subgroup.subset_normalClosure (Set.mem_iUnion.mpr ⟨i, ⟨y, hy, rfl⟩⟩)
    let g : ∀ i, N i →* Q := fun i =>
      (MonoidHom.liftOfSurjective (f i) (hf i)) ⟨_, hle i⟩
    have hg : ∀ i, (g i).comp (f i) = (QuotientGroup.mk' (Subgroup.normalClosure S)).comp
        (Monoid.CoprodI.of : M i →* Monoid.CoprodI M) := by
      intro i
      ext y
      exact MonoidHom.liftOfRightInverse_comp_apply (f i) (Function.surjInv (hf i))
        (Function.rightInverse_surjInv (hf i)) ⟨_, hle i⟩ y
    have hcomp : (Monoid.CoprodI.lift g).comp (freeProductMap f) =
        QuotientGroup.mk' (Subgroup.normalClosure S) := by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext y
      simp only [MonoidHom.comp_apply, freeProductMap_of, Monoid.CoprodI.lift_of]
      exact DFunLike.congr_fun (hg i) y
    have h1 : QuotientGroup.mk' (Subgroup.normalClosure S) x = 1 := by
      conv_lhs => rw [← hcomp, MonoidHom.comp_apply, hx, map_one]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    exact h1
  · apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨i, x, hx, rfl⟩ := hy
    show freeProductMap f (Monoid.CoprodI.of x) = 1
    rw [freeProductMap_of, MonoidHom.mem_ker.mp hx, map_one]

/-- The kernel of the map induced by a family of surjective homomorphisms between free products
is the normal closure of the images of any finite normally generating sets of the kernels. -/
lemma freeProductMap_ker_of_normalClosure {ι : Type*} {M N : ι → Type*} [∀ i, Group (M i)]
    [∀ i, Group (N i)] (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Surjective (f i))
    (S : ∀ i, Set (M i)) (hS : ∀ i, Subgroup.normalClosure (S i) = (f i).ker) :
    (freeProductMap f).ker
      = Subgroup.normalClosure (⋃ i, (Monoid.CoprodI.of : M i →* Monoid.CoprodI M) '' S i) := by
  rw [freeProductMap_ker f hf]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, y, hy, rfl⟩ := hz
    rw [← hS i] at hy
    exact Subgroup.normalClosure_mono
      (Set.subset_iUnion (fun j => (Monoid.CoprodI.of : M j →* Monoid.CoprodI M) '' S j) i)
      (Subgroup.map_normalClosure_le (S i) (Monoid.CoprodI.of : M i →* Monoid.CoprodI M)
        ⟨y, hy, rfl⟩)
  · apply Subgroup.normalClosure_mono
    intro z hz
    rw [Set.mem_iUnion] at hz ⊢
    obtain ⟨i, y, hy, rfl⟩ := hz
    exact ⟨i, y, by rw [← hS i]; exact Subgroup.subset_normalClosure hy, rfl⟩

/-- A free product of free groups on finite generating types is finitely presented. -/
theorem coprodI_freeGroup_isFinitelyPresented {ι : Type*} [Finite ι] (X : ι → Type*)
    [∀ i, Finite (X i)] :
    Group.IsFinitelyPresented (Monoid.CoprodI fun i => FreeGroup (X i)) :=
  Group.IsFinitelyPresented.equiv
    (Monoid.CoprodI.FreeGroupBasis.coprodI (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm

/-- A free product of finitely many finitely presented groups is finitely presented. -/
theorem isFinitelyPresented_coprodI {ι : Type*} [Finite ι] (G : ι → Type*) [∀ i, Group (G i)]
    [∀ i, Group.IsFinitelyPresented (G i)] :
    Group.IsFinitelyPresented (Monoid.CoprodI G) := by
  classical
  have hdata : ∀ i, ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G i),
      Function.Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated := fun i =>
    (inferInstance : Group.IsFinitelyPresented (G i)).out
  choose n π hπ using hdata
  have hS : ∀ i, ∃ S : Set (FreeGroup (Fin (n i))),
      S.Finite ∧ Subgroup.normalClosure S = (π i).ker := fun i => (hπ i).2
  choose S hSfin hSkern using hS
  haveI : Group.IsFinitelyPresented (Monoid.CoprodI fun i => FreeGroup (Fin (n i))) :=
    coprodI_freeGroup_isFinitelyPresented _
  refine Group.IsFinitelyPresented.of_surjective (freeProductMap π)
    (freeProductMap_surjective π fun i => (hπ i).1) ?_
  refine ⟨⋃ j, (Monoid.CoprodI.of (M := fun i => FreeGroup (Fin (n i))) (i := j)) '' S j,
    Set.finite_iUnion fun i => (hSfin i).image _, ?_⟩
  exact (freeProductMap_ker_of_normalClosure π (fun i => (hπ i).1) S hSkern).symm

/-- The wide pushout (amalgamated free product) of finitely many finitely presented groups
over a finitely generated group is finitely presented. -/
theorem pushoutI_isFinitelyPresented {ι : Type*} [Finite ι] [Nonempty ι] (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, Group.IsFinitelyPresented (G i)]
    (H : Type*) [Group H] [Group.FG H] (φ : ∀ i, H →* G i) :
    Group.IsFinitelyPresented (Monoid.PushoutI φ) := by
  classical
  haveI : Group.IsFinitelyPresented (Monoid.CoprodI G) := isFinitelyPresented_coprodI G
  let i0 : ι := Classical.arbitrary ι
  have hsurj : Function.Surjective (Monoid.PushoutI.ofCoprodI (φ := φ)) := by
    intro x
    induction x using Monoid.PushoutI.induction_on with
    | of i g => exact ⟨Monoid.CoprodI.of g, Monoid.PushoutI.ofCoprodI_of i g⟩
    | base h => exact ⟨Monoid.CoprodI.of (φ i0 h),
        by rw [Monoid.PushoutI.ofCoprodI_of, Monoid.PushoutI.of_apply_eq_base]⟩
    | mul x y hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a * b, by rw [map_mul, ha, hb]⟩
  obtain ⟨k, ⟨T⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp (inferInstance : Group.FG H)
  set Sset : Set (Monoid.CoprodI G) :=
    Set.range fun p : ι × Fin k =>
      Monoid.CoprodI.of (φ p.1 (T.val p.2)) *
        (Monoid.CoprodI.of (φ i0 (T.val p.2)))⁻¹ with hSset
  refine Group.IsFinitelyPresented.of_surjective (Monoid.PushoutI.ofCoprodI (φ := φ)) hsurj ?_
  refine ⟨Sset, ?_, ?_⟩
  · rw [hSset]; exact Set.finite_range _
  · apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rintro z ⟨p, rfl⟩
      exact MonoidHom.mem_ker.mpr (by
        simp [map_mul, map_inv, Monoid.PushoutI.ofCoprodI_of, Monoid.PushoutI.of_apply_eq_base])
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      let q := QuotientGroup.mk' (Subgroup.normalClosure Sset)
      let f : ∀ i, G i →* (Monoid.CoprodI G ⧸ Subgroup.normalClosure Sset) :=
        fun i => q.comp Monoid.CoprodI.of
      let kk : H →* (Monoid.CoprodI G ⧸ Subgroup.normalClosure Sset) := (f i0).comp (φ i0)
      have hf : ∀ i, (f i).comp (φ i) = kk := by
        intro i
        apply T.hom_ext
        intro j
        show q (Monoid.CoprodI.of (φ i (T.val j))) = q (Monoid.CoprodI.of (φ i0 (T.val j)))
        have hq : q (Monoid.CoprodI.of (φ i (T.val j)) *
            (Monoid.CoprodI.of (φ i0 (T.val j)))⁻¹) = 1 := by
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          exact Subgroup.subset_normalClosure ⟨(i, j), rfl⟩
        exact eq_of_mul_inv_eq_one (by simpa [map_mul, map_inv] using hq)
      have hcomp : (Monoid.PushoutI.lift f kk hf).comp
          (Monoid.PushoutI.ofCoprodI (φ := φ)) = q := by
        apply Monoid.CoprodI.ext_hom
        intro i
        ext y
        simp only [MonoidHom.comp_apply, Monoid.PushoutI.ofCoprodI_of, Monoid.PushoutI.lift_of]
        rfl
      have h1 : q x = 1 := by
        conv_lhs => rw [← hcomp, MonoidHom.comp_apply, hx, map_one]
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
      exact h1

end Work.ORBassSerre.FP

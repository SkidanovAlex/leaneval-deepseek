import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

/-- **A finite spanning family contains a linearly independent subfamily of full size.**
If `v : ι → M` is a finite family of vectors spanning a finite-dimensional vector space `M`,
then some subfamily indexed by a `Finset` `S ⊆ ι` is linearly independent and has
`S.card = finrank 𝕜 M`. -/
theorem exists_finset_linearIndependent_card_eq_finrank
    {𝕜 M ι : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M] [FiniteDimensional 𝕜 M]
    [Fintype ι] (v : ι → M) (hsp : Submodule.span 𝕜 (Set.range v) = ⊤) :
    ∃ S : Finset ι, S.card = Module.finrank 𝕜 M ∧
      LinearIndependent 𝕜 (fun i : S => v i) := by
  classical
  set P : Finset ι → Prop := fun S => LinearIndepOn 𝕜 v ((S : Finset ι) : Set ι) with hP
  have hne : (Finset.univ.filter P).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hP]; simp⟩
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card hne
  have hSgood : P S := (Finset.mem_filter.mp hSmem).2
  have hSmax' : ∀ T, P T → T.card ≤ S.card := fun T hT =>
    hSmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩)
  have hSli : LinearIndependent 𝕜 (fun i : S => v i) := by
    rw [hP] at hSgood
    simpa using hSgood.linearIndependent
  have hspanS : Submodule.span 𝕜 (Set.range (fun i : S => v i)) = ⊤ := by
    by_contra hne_top
    have hex : ∃ i : ι, v i ∉ Submodule.span 𝕜 (Set.range fun j : S => v j) := by
      by_contra h
      push Not at h
      have htop : Submodule.span 𝕜 (Set.range fun j : S => v j) = ⊤ := by
        rw [eq_top_iff, ← hsp]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        exact h i
      exact hne_top htop
    obtain ⟨i, hi⟩ := hex
    have hiS : i ∉ S :=
      fun hiS => hi (Submodule.subset_span (show v i ∈ Set.range (fun j : S => v j) from
        ⟨⟨i, hiS⟩, rfl⟩))
    have hgood' : P (insert i S) := by
      rw [hP] at hSgood ⊢
      have hmem : v i ∉ Submodule.span 𝕜 (v '' ((S : Finset ι) : Set ι)) := by
        rw [Set.image_eq_range]
        exact hi
      simpa using hSgood.insert hmem
    have hcard' : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hiS
    have := hSmax' (insert i S) hgood'
    omega
  have hcard : S.card = Module.finrank 𝕜 M := by
    have h1 := finrank_span_eq_card hSli
    rw [hspanS, finrank_top, Fintype.card_coe] at h1
    exact h1.symm
  exact ⟨S, hcard, hSli⟩

/-- **Coordinate restriction of a surjection.** Let `φ : V →ₗ[𝕜] W` be a surjective linear map between finite-dimensional vector spaces and let `b : Module.Basis ι 𝕜 V` be a basis of `V`. Then there is a subset `S` of the basis with `S.card = finrank 𝕜 W` such that `φ` is injective on the span of `{b i : i ∈ S}`. Such an `S` exists because the coordinate functionals indexed by the complement of `S` separate points of `ker φ`; equivalently, a matrix of rank `finrank 𝕜 W` has a non-vanishing minor of that size. -/
theorem exists_finset_injective_on_span {ι : Type*} [Fintype ι] {𝕜 V W : Type*} [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (b : Module.Basis ι 𝕜 V) (φ : V →ₗ[𝕜] W) (hφ : ∀ w : W, ∃ v : V, φ v = w) :
    ∃ S : Finset ι, S.card = Module.finrank 𝕜 W ∧
      ∀ x ∈ Submodule.span 𝕜 (b '' (S : Set ι)), φ x = 0 → x = 0 := by
  classical
  have hrange_top : φ.range = ⊤ := LinearMap.range_eq_top.mpr hφ
  have hspanw : Submodule.span 𝕜 (Set.range (φ ∘ b)) = ⊤ := by
    have h := Submodule.map_span φ (Set.range b)
    rw [b.span_eq, Submodule.map_top, hrange_top] at h
    rw [Set.range_comp φ b]
    exact h.symm
  obtain ⟨S, hScard, hSli⟩ :=
    exists_finset_linearIndependent_card_eq_finrank (φ ∘ b) hspanw
  refine ⟨S, hScard, ?_⟩
  intro x hx hxφ
  set C : Submodule 𝕜 V := Submodule.span 𝕜 (b '' (S : Set ι)) with hCdef
  have hxC : x ∈ C := by rw [hCdef]; exact hx
  have hCrange : C = Submodule.span 𝕜 (Set.range (fun i : S => b i)) := by
    rw [hCdef]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨↑i, i.2, rfl⟩
  have hspanW : Submodule.span 𝕜 (Set.range (fun i : S => (φ ∘ b) i)) = ⊤ :=
    hSli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_coe, hScard])
  have hbli : LinearIndependent 𝕜 (fun i : S => b i) := by
    simpa only [Function.comp_def] using
      b.linearIndependent.comp (Subtype.val) (Subtype.val_injective)
  have hfinC : Module.finrank 𝕜 C = S.card := by
    rw [hCrange, finrank_span_eq_card hbli, Fintype.card_coe]
  have hker : Module.finrank 𝕜 (LinearMap.ker φ) + Module.finrank 𝕜 W = Module.finrank 𝕜 V := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange_top, finrank_top] at h
    omega
  have hmapC : Submodule.map φ C = ⊤ := by
    rw [hCdef, Submodule.map_span]
    have himg : φ '' (b '' (S : Set ι)) = Set.range (fun i : S => (φ ∘ b) i) := by
      rw [Set.image_image]
      ext y
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨↑i, i.2, rfl⟩
    rw [himg, hspanW]
  have hsup : C ⊔ LinearMap.ker φ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy' : φ y ∈ Submodule.map φ C := by rw [hmapC]; exact Submodule.mem_top
    rw [Submodule.mem_map] at hy'
    obtain ⟨z, hzC, hzy⟩ := hy'
    rw [Submodule.mem_sup]
    exact ⟨z, hzC, y - z, by rw [LinearMap.mem_ker, map_sub, hzy, sub_self],
      by rw [add_comm, sub_add_cancel]⟩
  have hhdim := Submodule.finrank_sup_add_finrank_inf_eq C (LinearMap.ker φ)
  have hz : Module.finrank 𝕜 ↥(C ⊓ LinearMap.ker φ) = 0 := by
    rw [hsup, finrank_top] at hhdim
    rw [hfinC, hScard] at hhdim
    omega
  have hbot : C ⊓ LinearMap.ker φ = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hxker : x ∈ LinearMap.ker φ := LinearMap.mem_ker.mpr hxφ
  have hxinf : x ∈ C ⊓ LinearMap.ker φ := ⟨hxC, hxker⟩
  rw [hbot] at hxinf
  simpa using hxinf

end Commons.LinearAlgebra.Submodule
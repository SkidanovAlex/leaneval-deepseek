import Mathlib
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.SubgroupAlg.subgroupAlgMap_injective
import Submission.Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff
import Submission.Work.ORReductions.SubgroupAlg.cosetComponent_normalized_mem_range

set_option autoImplicit false

namespace Work.ORReductions.Coherent

open MonoidAlgebra

variable {G : Type*} [Group G]

namespace Aux

variable {K : Type*} [Semiring K]

/-- The coefficient of a left multiple of `z` by the monomial `single g c`. -/
theorem coeff_single_mul (g : G) (c : K) (z : MonoidAlgebra K G) (x : G) :
    (MonoidAlgebra.single g c * z).coeff x = c * z.coeff (g⁻¹ * x) := by
  classical
  refine MonoidAlgebra.coeff_single_mul_eq_mul_coeff (x := z) (r := c) (m := g) (m₁ := x)
    (g⁻¹ * x) fun m₀ _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, inv_mul_cancel_left]
  · rw [h, mul_inv_cancel_left]

/-- The support of a monomial `single g c` is contained in the singleton of `g`. -/
theorem support_single_subset (g : G) (c : K) :
    ↑(MonoidAlgebra.single g c).coeff.support ⊆ ({g} : Set G) := by
  intro x hx
  rw [Finset.mem_coe, MonoidAlgebra.coeff_single, Finsupp.mem_support_single] at hx
  simpa using hx.1

end Aux

/-- The projection of `x : K[G]` onto the summand `K[H]` in the decomposition of `K[G]` into
left cosets of `H`: it keeps the coefficients of `x` at elements of `H`. -/
noncomputable def hPart (H : Subgroup G) (K : Type*) [Semiring K]
    (x : MonoidAlgebra K G) : MonoidAlgebra K G :=
  letI : DecidablePred (fun g : G => g ∈ H) := Classical.decPred _
  MonoidAlgebra.ofCoeff (Finsupp.filter (fun g : G => g ∈ H) x.coeff)

variable (H : Subgroup G) (K : Type*) [Semiring K]

theorem hPart_coeff_of_mem (x : MonoidAlgebra K G) {g : G} (hg : g ∈ H) :
    (hPart H K x).coeff g = x.coeff g := by
  classical
  rw [hPart, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply, if_pos hg]

theorem hPart_coeff_of_notMem (x : MonoidAlgebra K G) {g : G} (hg : g ∉ H) :
    (hPart H K x).coeff g = 0 := by
  classical
  rw [hPart, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply, if_neg hg]

theorem hPart_zero : hPart H K (0 : MonoidAlgebra K G) = 0 := by
  classical
  rw [hPart, MonoidAlgebra.coeff_zero, Finsupp.filter_zero, MonoidAlgebra.ofCoeff_zero]

theorem hPart_add (x y : MonoidAlgebra K G) :
    hPart H K (x + y) = hPart H K x + hPart H K y := by
  classical
  rw [hPart, hPart, hPart, ← MonoidAlgebra.ofCoeff_add, MonoidAlgebra.ofCoeff_inj,
    MonoidAlgebra.coeff_add, Finsupp.filter_add]

theorem hPart_support_subset (x : MonoidAlgebra K G) :
    ↑(hPart H K x).coeff.support ⊆ (H : Set G) := by
  classical
  intro g hg
  rw [Finset.mem_coe] at hg
  by_contra hgH
  exact (Finsupp.mem_support_iff.mp hg) (hPart_coeff_of_notMem H K x hgH)

theorem hPart_eq_self_of_support_subset (x : MonoidAlgebra K G)
    (hx : ↑x.coeff.support ⊆ (H : Set G)) : hPart H K x = x := by
  classical
  apply MonoidAlgebra.ext
  ext g
  by_cases hg : g ∈ H
  · rw [hPart_coeff_of_mem H K x hg]
  · rw [hPart_coeff_of_notMem H K x hg]
    exact (Finsupp.notMem_support_iff.mp fun hm => hg (hx (Finset.mem_coe.mpr hm))).symm

theorem hPart_eq_zero_of_notMem (x : MonoidAlgebra K G)
    (hx : ∀ g ∈ x.coeff.support, g ∉ H) : hPart H K x = 0 := by
  classical
  apply MonoidAlgebra.ext
  ext g
  by_cases hg : g ∈ H
  · rw [hPart_coeff_of_mem H K x hg, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact Finsupp.notMem_support_iff.mp fun hm => hx g hm hg
  · rw [hPart_coeff_of_notMem H K x hg, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem hPart_single_of_mem (g : G) (c : K) (hg : g ∈ H) :
    hPart H K (MonoidAlgebra.single g c) = MonoidAlgebra.single g c := by
  have hsub : ↑(MonoidAlgebra.single g c).coeff.support ⊆ ({g} : Set G) :=
    Aux.support_single_subset g c
  refine hPart_eq_self_of_support_subset H K _ fun x hx => ?_
  have hxg : x = g := by simpa using hsub hx
  simpa [hxg] using hg

theorem hPart_single_of_notMem (g : G) (c : K) (hg : g ∉ H) :
    hPart H K (MonoidAlgebra.single g c) = 0 := by
  have hsub : ↑(MonoidAlgebra.single g c).coeff.support ⊆ ({g} : Set G) :=
    Aux.support_single_subset g c
  refine hPart_eq_zero_of_notMem H K _ fun x hx hxH => ?_
  have hxg : x = g := by simpa using hsub hx
  exact hg (hxg ▸ hxH)

theorem hPart_single_mul (g : G) (c : K) (z : MonoidAlgebra K G)
    (hz : ↑z.coeff.support ⊆ (H : Set G)) :
    hPart H K (MonoidAlgebra.single g c * z) = hPart H K (MonoidAlgebra.single g c) * z := by
  classical
  have hcoeff : ∀ x : G, (MonoidAlgebra.single g c * z).coeff x ≠ 0 → z.coeff (g⁻¹ * x) ≠ 0 := by
    intro x hx h0
    exact hx (by rw [Aux.coeff_single_mul, h0, mul_zero])
  by_cases hg : g ∈ H
  · rw [hPart_single_of_mem H K g c hg]
    refine hPart_eq_self_of_support_subset H K _ fun x hx => ?_
    by_contra hxH
    have hnotmem : g⁻¹ * x ∉ z.coeff.support := by
      intro hm
      have hgim : g⁻¹ * x ∈ H := hz (Finset.mem_coe.mpr hm)
      exact hxH (by rw [← mul_inv_cancel_left g x]; exact H.mul_mem hg hgim)
    have hx0 : (MonoidAlgebra.single g c * z).coeff x = 0 := by
      rw [Aux.coeff_single_mul, Finsupp.notMem_support_iff.mp hnotmem, mul_zero]
    rw [Finset.mem_coe] at hx
    exact (Finsupp.mem_support_iff.mp hx) hx0
  · rw [hPart_single_of_notMem H K g c hg, zero_mul]
    refine hPart_eq_zero_of_notMem H K _ fun x hx hxH => ?_
    have hxc : z.coeff (g⁻¹ * x) ≠ 0 := hcoeff x (Finsupp.mem_support_iff.mp hx)
    have hmem : g⁻¹ * x ∈ H := hz (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hxc))
    have heq : x * (g⁻¹ * x)⁻¹ = g := by group
    exact hg (heq ▸ H.mul_mem hxH (H.inv_mem hmem))

/-- **Key lemma.** For `z : K[G]` supported on `H` and any `a : K[G]`, the projection onto the
`H`-component is right `K[H]`-linear: `hPart (a * z) = hPart a * z`. -/
theorem hPart_mul_of_support_subset (a z : MonoidAlgebra K G)
    (hz : ↑z.coeff.support ⊆ (H : Set G)) :
    hPart H K (a * z) = hPart H K a * z := by
  classical
  refine Finsupp.induction (motive := fun c => hPart H K (MonoidAlgebra.ofCoeff c * z)
    = hPart H K (MonoidAlgebra.ofCoeff c) * z) a.coeff ?_ ?_
  · rw [MonoidAlgebra.ofCoeff_zero, zero_mul, hPart_zero, zero_mul]
  · intro g c f _ _ ih
    have h1 : MonoidAlgebra.ofCoeff (Finsupp.single g c + f)
        = MonoidAlgebra.single g c + MonoidAlgebra.ofCoeff f := by
      rw [MonoidAlgebra.ofCoeff_add]; rfl
    rw [h1, add_mul, hPart_add]
    have hmul : hPart H K (MonoidAlgebra.single g c * z)
        = hPart H K (MonoidAlgebra.single g c) * z := hPart_single_mul H K g c z hz
    rw [hmul, ih, ← add_mul, ← hPart_add]

end Work.ORReductions.Coherent

namespace Work.ORReductions.Coherent


theorem mem_span_of_subgroupAlgMap_mem_span {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] {ι : Type*} (y : ι → MonoidAlgebra K H) (x : MonoidAlgebra K H)
    (hx : Work.ORReductions.subgroupAlgMap H K x ∈
      Submodule.span (MonoidAlgebra K G)
        (Set.range fun i => Work.ORReductions.subgroupAlgMap H K (y i))) :
    x ∈ Submodule.span (MonoidAlgebra K H) (Set.range y) := by
  classical
  let S : Submodule (MonoidAlgebra K H) (MonoidAlgebra K H) :=
    Submodule.span (MonoidAlgebra K H) (Set.range y)
  have key : ∀ z ∈ (Submodule.span (MonoidAlgebra K G)
        (Set.range fun i => Work.ORReductions.subgroupAlgMap H K (y i)) :
          Set (MonoidAlgebra K G)),
      ∀ a : MonoidAlgebra K G,
        ∃ s ∈ S, hPart H K (a * z) = Work.ORReductions.subgroupAlgMap H K s := by
    intro z hz
    refine Submodule.span_induction
      (s := Set.range fun i => Work.ORReductions.subgroupAlgMap H K (y i))
      (p := fun z _ => ∀ a : MonoidAlgebra K G,
        ∃ s ∈ S, hPart H K (a * z) = Work.ORReductions.subgroupAlgMap H K s) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨i, rfl⟩ a
      have hsupp : ↑(Work.ORReductions.subgroupAlgMap H K (y i)).coeff.support ⊆ (H : Set G) :=
        (Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff H K _).mp ⟨y i, rfl⟩
      have hmul : hPart H K (a * Work.ORReductions.subgroupAlgMap H K (y i))
          = hPart H K a * Work.ORReductions.subgroupAlgMap H K (y i) :=
        hPart_mul_of_support_subset H K a _ hsupp
      obtain ⟨u, hu⟩ := Work.ORReductions.SubgroupAlg.mem_range_subgroupAlgMap_of_support_subset
        H K (hPart H K a) (hPart_support_subset H K a)
      refine ⟨u • y i, ?_, ?_⟩
      · have hmem : u • y i ∈ S :=
          S.smul_mem u (Submodule.subset_span (Set.mem_range_self i))
        rwa [smul_eq_mul] at hmem
      · rw [hmul, smul_eq_mul, map_mul, ← hu]
    · intro a
      exact ⟨0, S.zero_mem, by rw [mul_zero, hPart_zero, map_zero]⟩
    · intro z₁ z₂ _ _ ih₁ ih₂ a
      obtain ⟨s₁, hs₁, h₁⟩ := ih₁ a
      obtain ⟨s₂, hs₂, h₂⟩ := ih₂ a
      refine ⟨s₁ + s₂, S.add_mem hs₁ hs₂, ?_⟩
      rw [mul_add, hPart_add, h₁, h₂, map_add]
    · intro a₀ z _ ih a
      rw [smul_eq_mul, ← mul_assoc]
      exact ih (a * a₀)
  obtain ⟨s, hsS, hs⟩ := key (Work.ORReductions.subgroupAlgMap H K x) hx 1
  have hsupp : ↑(Work.ORReductions.subgroupAlgMap H K x).coeff.support ⊆ (H : Set G) :=
    (Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff H K _).mp ⟨x, rfl⟩
  have hfx : hPart H K (Work.ORReductions.subgroupAlgMap H K x)
      = Work.ORReductions.subgroupAlgMap H K x :=
    hPart_eq_self_of_support_subset H K _ hsupp
  rw [one_mul, hfx] at hs
  have hxs : x = s := Work.ORReductions.SubgroupAlg.subgroupAlgMap_injective H K hs
  rw [hxs]
  exact hsS

end Work.ORReductions.Coherent

import Mathlib
import Submission.Work.ORReductions.Coherent.FiniteIndexSetup
import Submission.Work.ORReductions.SubgroupAlg

set_option autoImplicit false

namespace Work.ORReductions.Coherent

open MonoidAlgebra

variable {G : Type*} [Group G] {K : Type*}

/-- The coefficient at `g ∈ H` of `subgroupAlgMap H K a`, for `a : K[H]`. -/
lemma coeff_subgroupAlgMap_of_mem (H : Subgroup G) (K : Type*) [Semiring K]
    (a : MonoidAlgebra K H) {g : G} (hg : g ∈ H) :
    (Work.ORReductions.subgroupAlgMap H K a).coeff g = a.coeff ⟨g, hg⟩ := by
  rw [Work.ORReductions.subgroupAlgMap, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.coeff_mapDomain]
  simpa using Finsupp.mapDomain_apply_of_injective H.subtype_injective a.coeff ⟨g, hg⟩

/-- The coefficient at `g ∉ H` of `subgroupAlgMap H K a`, for `a : K[H]`. -/
lemma coeff_subgroupAlgMap_of_notMem (H : Subgroup G) (K : Type*) [Semiring K]
    (a : MonoidAlgebra K H) {g : G} (hg : g ∉ H) :
    (Work.ORReductions.subgroupAlgMap H K a).coeff g = 0 := by
  rw [Work.ORReductions.subgroupAlgMap, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_of_notMem_range a.coeff g (by
    rintro ⟨x, hx⟩
    exact hg (hx ▸ x.2))

/-- The coefficient at `g` of `subgroupAlgMap H K a * single r 1`, when `g * r⁻¹ ∈ H`. -/
lemma coeff_subgroupAlgMap_mul_single_of_mem (H : Subgroup G) (K : Type*) [Semiring K]
    (a : MonoidAlgebra K H) (r : G) {g : G} (hg : g * r⁻¹ ∈ H) :
    (Work.ORReductions.subgroupAlgMap H K a * MonoidAlgebra.single r 1).coeff g =
      a.coeff ⟨g * r⁻¹, hg⟩ := by
  rw [MonoidAlgebra.coeff_mul_single_apply, mul_one]
  exact coeff_subgroupAlgMap_of_mem H K a hg

/-- The coefficient at `g` of `subgroupAlgMap H K a * single r 1`, when `g * r⁻¹ ∉ H`. -/
lemma coeff_subgroupAlgMap_mul_single_of_notMem (H : Subgroup G) (K : Type*) [Semiring K]
    (a : MonoidAlgebra K H) (r : G) {g : G} (hg : g * r⁻¹ ∉ H) :
    (Work.ORReductions.subgroupAlgMap H K a * MonoidAlgebra.single r 1).coeff g = 0 := by
  rw [MonoidAlgebra.coeff_mul_single_apply, mul_one]
  exact coeff_subgroupAlgMap_of_notMem H K a hg

/-- The coefficient at `g` of the `q`-th summand is `x.coeff g` when `g` lies in the right
coset `H * cosetRep H q`. -/
lemma coeff_summand_of_mem (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) {g : G} (hg : g * (cosetRep H q)⁻¹ ∈ H) :
    (Work.ORReductions.subgroupAlgMap H K (coord H K q x)
        * MonoidAlgebra.single (cosetRep H q) 1).coeff g = x.coeff g := by
  rw [coeff_subgroupAlgMap_mul_single_of_mem H K (coord H K q x) (cosetRep H q) hg,
    coeff_coord]
  have hg' : ((⟨g * (cosetRep H q)⁻¹, hg⟩ : H) : G) * cosetRep H q = g := by
    group
  rw [hg']

/-- The coefficient at `g` of the `q`-th summand vanishes when `g` does not lie in the right
coset `H * cosetRep H q`. -/
lemma coeff_summand_of_notMem (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) {g : G} (hg : g * (cosetRep H q)⁻¹ ∉ H) :
    (Work.ORReductions.subgroupAlgMap H K (coord H K q x)
        * MonoidAlgebra.single (cosetRep H q) 1).coeff g = 0 := by
  rw [coeff_subgroupAlgMap_mul_single_of_notMem H K (coord H K q x) (cosetRep H q) hg]

theorem sum_coord_mul_repr (G : Type*) [Group G] (K : Type*) [Field K] (H : Subgroup G)
    [Fintype (G ⧸ H)] (x : MonoidAlgebra K G) :
    ∑ q : G ⧸ H, Work.ORReductions.subgroupAlgMap H K (Work.ORReductions.Coherent.coord H K q x)
        * MonoidAlgebra.single (Work.ORReductions.Coherent.cosetRep H q) 1 = x := by
  classical
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply]
  obtain ⟨q0, hq0⟩ := cosetRep_spec H g
  have hsingle : ∀ b ∈ (Finset.univ : Finset (G ⧸ H)), b ≠ q0 →
      (Work.ORReductions.subgroupAlgMap H K (Work.ORReductions.Coherent.coord H K b x)
        * MonoidAlgebra.single (Work.ORReductions.Coherent.cosetRep H b) 1).coeff g = 0 := by
    intro b _ hb
    refine coeff_summand_of_notMem H K b x ?_
    intro hbH
    refine hb (cosetRep_eq_of_mul_inv_mem H ?_)
    have h1 : cosetRep H b * g⁻¹ ∈ H := by
      simpa using H.inv_mem hbH
    have h2 : (cosetRep H b * g⁻¹) * (g * (cosetRep H q0)⁻¹) ∈ H := H.mul_mem h1 hq0
    simpa [mul_assoc] using h2
  rw [Finset.sum_eq_single q0 hsingle (fun h => absurd (Finset.mem_univ q0) h)]
  exact coeff_summand_of_mem H K q0 x hq0

end Work.ORReductions.Coherent

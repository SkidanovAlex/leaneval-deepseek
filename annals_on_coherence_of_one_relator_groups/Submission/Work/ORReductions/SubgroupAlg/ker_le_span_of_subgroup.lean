import Mathlib
import Submission.Work.ORReductions.SubgroupAlg

/-!
# The kernel of a relation matrix over a subgroup algebra

Let `H ≤ G` be a subgroup and `K` a commutative semiring.  The group algebra `K[G]` splits, as a
`K`-vector space, into the direct sum of the coset components `K[qH]` over the left cosets
`q ∈ G ⧸ H`; each of these components is a copy of `K[H]`, the copy of `r : K[H]` in the component
of `q` being `single (Quotient.out q) 1 * subgroupAlgMap H K r`.

`assemble` is the resulting identification `((G ⧸ H) →₀ K[H]) ≃ₗ[K] K[G]`.  Its basic properties
are that it is a bijection (`exists_assemble_eq` and `sum_coset_eq_zero`) and that multiplication on
the right by an element of `K[H] ⊆ K[G]` acts on each coset component separately, i.e.
`assemble (c · y) = assemble c * subgroupAlgMap H K y`.

The main theorem then transfers a presentation of `ker (linearCombination K[H] y)` to
`ker (linearCombination K[G] (subgroupAlgMap H K ∘ y))`: this is the algebraic core of the fact
that `K[G]` is a free (hence flat) left `K[H]`-module.
-/

set_option maxHeartbeats 800000

namespace Work.ORReductions.SubgroupAlg

open MonoidAlgebra

variable {G : Type*} [Group G]

/-! ### Left cosets and their chosen representatives -/

/-- The left coset `gH` of `g`, as an element of `G ⧸ H`. -/
def cosetOf (H : Subgroup G) (g : G) : G ⧸ H := Quotient.mk (QuotientGroup.leftRel H) g

lemma cosetOf_out (H : Subgroup G) (q : G ⧸ H) : cosetOf H (Quotient.out q) = q :=
  Quotient.out_eq q

lemma cosetOf_out_mul (H : Subgroup G) (q : G ⧸ H) (h : H) :
    cosetOf H (Quotient.out q * (h : G)) = q := by
  have h1 : QuotientGroup.leftRel H (Quotient.out q) (Quotient.out q * (h : G)) := by
    rw [QuotientGroup.leftRel_apply]
    simp [h.2]
  have h2 : cosetOf H (Quotient.out q) = cosetOf H (Quotient.out q * (h : G)) :=
    Quotient.sound h1
  rw [← h2]
  exact cosetOf_out H q

/-- `cosetLog H q g` is the element `x ∈ H` with `g = Quotient.out q * x` when `g` lies in the
coset `q`, and `1` otherwise. -/
noncomputable def cosetLog (H : Subgroup G) (q : G ⧸ H) (g : G) : H := by
  classical
  exact if h : cosetOf H g = q then
    ⟨(Quotient.out q)⁻¹ * g, by
      rw [← QuotientGroup.leftRel_apply]
      exact Quotient.exact ((Quotient.out_eq q).trans h.symm)⟩
  else 1

lemma cosetLog_spec (H : Subgroup G) {q : G ⧸ H} {g : G} (h : cosetOf H g = q) :
    ((cosetLog H q g : H) : G) = (Quotient.out q)⁻¹ * g := by
  classical
  rw [cosetLog, dif_pos h]

lemma out_mul_cosetLog (H : Subgroup G) {q : G ⧸ H} {g : G} (h : cosetOf H g = q) :
    Quotient.out q * ((cosetLog H q g : H) : G) = g := by
  rw [cosetLog_spec H h, mul_inv_cancel_left]

/-! ### Coefficient computations for `subgroupAlgMap` -/

lemma coeff_subgroupAlgMap (H : Subgroup G) (K : Type*) [Semiring K]
    (r : MonoidAlgebra K H) (h : H) :
    (Work.ORReductions.subgroupAlgMap H K r).coeff (h : G) = r.coeff h := by
  simp [Work.ORReductions.subgroupAlgMap, MonoidAlgebra.coeff_mapDomain]

lemma coeff_subgroupAlgMap_eq_zero (H : Subgroup G) (K : Type*) [Semiring K]
    (r : MonoidAlgebra K H) {g : G} (hg : g ∉ H) :
    (Work.ORReductions.subgroupAlgMap H K r).coeff g = 0 := by
  have h : (Work.ORReductions.subgroupAlgMap H K r).coeff g =
      (Finsupp.mapDomain (H.subtype : H → G) r.coeff) g := by
    simp [Work.ORReductions.subgroupAlgMap, MonoidAlgebra.coeff_mapDomain]
  rw [h]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨h', rfl⟩; exact hg h'.2)

lemma subgroupAlgMap_single (H : Subgroup G) (K : Type*) [Semiring K] (h : H) (c : K) :
    Work.ORReductions.subgroupAlgMap H K (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (h : G) c := by
  show MonoidAlgebra.mapDomain (H.subtype : H → G) (MonoidAlgebra.single h c) = _
  exact MonoidAlgebra.mapDomain_single

lemma subgroupAlgMap_finset_sum (H : Subgroup G) (K : Type*) [Semiring K] {ι : Type*}
    (s : Finset ι) (F : ι → MonoidAlgebra K H) :
    Work.ORReductions.subgroupAlgMap H K (∑ i ∈ s, F i) =
      ∑ i ∈ s, Work.ORReductions.subgroupAlgMap H K (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, ih]

lemma coeff_single_mul_subgroupAlgMap_same (H : Subgroup G) (K : Type*) [Semiring K]
    (q : G ⧸ H) (r : MonoidAlgebra K H) (h : H) :
    (MonoidAlgebra.single (Quotient.out q) (1 : K) *
      Work.ORReductions.subgroupAlgMap H K r).coeff (Quotient.out q * (h : G)) = r.coeff h := by
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, inv_mul_cancel_left]
  exact coeff_subgroupAlgMap H K r h

lemma coeff_single_mul_subgroupAlgMap_ne (H : Subgroup G) (K : Type*) [Semiring K]
    (q q' : G ⧸ H) (h : H) (r : MonoidAlgebra K H) (hq : q' ≠ q) :
    (MonoidAlgebra.single (Quotient.out q) (1 : K) *
      Work.ORReductions.subgroupAlgMap H K r).coeff (Quotient.out q' * (h : G)) = 0 := by
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
  refine coeff_subgroupAlgMap_eq_zero H K r ?_
  intro hmem
  refine hq ?_
  have hmem' : (Quotient.out q)⁻¹ * Quotient.out q' ∈ H := by
    have h2 : ((Quotient.out q)⁻¹ * (Quotient.out q' * (h : G))) * (h : G)⁻¹ ∈ H :=
      H.mul_mem hmem (H.inv_mem h.2)
    rwa [show ((Quotient.out q)⁻¹ * (Quotient.out q' * (h : G))) * (h : G)⁻¹ =
      (Quotient.out q)⁻¹ * Quotient.out q' by group] at h2
  have key : cosetOf H (Quotient.out q) = cosetOf H (Quotient.out q') :=
    Quotient.sound (QuotientGroup.leftRel_apply.mpr hmem')
  rw [cosetOf_out H q, cosetOf_out H q'] at key
  exact key.symm

/-! ### The decomposition map `assemble` -/

/-- The `K`-algebra homomorphism `K[H] → K[G]`. -/
noncomputable def subgroupAlgHom (H : Subgroup G) (K : Type*) [CommSemiring K] :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainAlgHom K K H.subtype

/-- Assembly of an element of `(G ⧸ H) →₀ K[H]` into an element of `K[G]`: the component at the
coset `q` is placed on the coset `q` using the representative `Quotient.out q`. -/
noncomputable def assemble (H : Subgroup G) (K : Type*) [CommSemiring K] :
    ((G ⧸ H) →₀ MonoidAlgebra K H) →ₗ[K] MonoidAlgebra K G :=
  Finsupp.lsum K fun q =>
    (LinearMap.mulLeft K (MonoidAlgebra.single (Quotient.out q) (1 : K))).comp
      (subgroupAlgHom H K).toLinearMap

lemma assemble_apply (H : Subgroup G) (K : Type*) [CommSemiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H) :
    assemble H K c = c.sum fun q r =>
      MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K r := by
  rw [assemble, Finsupp.lsum_apply]
  rfl

lemma assemble_single (H : Subgroup G) (K : Type*) [CommSemiring K]
    (q : G ⧸ H) (r : MonoidAlgebra K H) :
    assemble H K (Finsupp.single q r) = MonoidAlgebra.single (Quotient.out q) (1 : K) *
      Work.ORReductions.subgroupAlgMap H K r := by
  rw [assemble_apply, Finsupp.sum_single_index]
  simp

lemma assemble_add (H : Subgroup G) (K : Type*) [CommSemiring K]
    (c c' : (G ⧸ H) →₀ MonoidAlgebra K H) :
    assemble H K (c + c') = assemble H K c + assemble H K c' := by
  classical
  rw [assemble_apply, assemble_apply, assemble_apply]
  rw [Finsupp.sum_add_index (by intro q _; simp) (by intro q _ a b; rw [map_add, mul_add])]

lemma assemble_finset_sum (H : Subgroup G) (K : Type*) [CommSemiring K] {ι : Type*}
    (s : Finset ι) (F : ι → (G ⧸ H) →₀ MonoidAlgebra K H) :
    assemble H K (∑ i ∈ s, F i) = ∑ i ∈ s, assemble H K (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, assemble_add, ih]

lemma assemble_mapRange_mul (H : Subgroup G) (K : Type*) [CommSemiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H) (y : MonoidAlgebra K H) :
    assemble H K (c.mapRange (fun r => r * y) (by simp)) =
      assemble H K c * Work.ORReductions.subgroupAlgMap H K y := by
  rw [assemble_apply, assemble_apply, Finsupp.sum_mapRange_index]
  · rw [Finsupp.sum_mul]
    exact Finsupp.sum_congr fun x _ => by rw [map_mul, mul_assoc]
  · intro q
    simp

/-! ### The two round trips -/

/-- The coefficient of `assemble c` on the coset `q`, in the coordinates given by `Quotient.out q`,
is the coefficient of `c` at `q`. -/
lemma coeff_sum_coset (H : Subgroup G) (K : Type*) [CommSemiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H) (q : G ⧸ H) (h : H) :
    (c.sum fun q' r => MonoidAlgebra.single (Quotient.out q') (1 : K) *
      Work.ORReductions.subgroupAlgMap H K r).coeff (Quotient.out q * (h : G)) =
        (c q).coeff h := by
  classical
  rw [show c.sum (fun q' r => MonoidAlgebra.single (Quotient.out q') (1 : K) *
        Work.ORReductions.subgroupAlgMap H K r) =
      ∑ q' ∈ c.support, MonoidAlgebra.single (Quotient.out q') (1 : K) *
        Work.ORReductions.subgroupAlgMap H K (c q') from rfl]
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  trans ∑ q' ∈ c.support, (if q' = q then (c q').coeff h else 0)
  · refine Finset.sum_congr rfl fun q' _ => ?_
    by_cases hqq : q' = q
    · rw [if_pos hqq, hqq]
      exact coeff_single_mul_subgroupAlgMap_same H K q (c q) h
    · rw [if_neg hqq]
      exact coeff_single_mul_subgroupAlgMap_ne H K q' q h (c q') (fun hq => hqq hq.symm)
  · rw [Finset.sum_ite_eq']
    by_cases hq : q ∈ c.support
    · rw [if_pos hq]
    · rw [if_neg hq, Finsupp.notMem_support_iff.mp hq]
      rfl

lemma sum_coset_eq_zero (H : Subgroup G) (K : Type*) [CommSemiring K]
    (c : (G ⧸ H) →₀ MonoidAlgebra K H)
    (hc : c.sum (fun q r => MonoidAlgebra.single (Quotient.out q) (1 : K) *
      Work.ORReductions.subgroupAlgMap H K r) = 0) : c = 0 := by
  classical
  refine Finsupp.ext fun q => MonoidAlgebra.coeff_injective ?_
  refine Finsupp.ext fun h => ?_
  have hh := coeff_sum_coset H K c q h
  rw [hc] at hh
  simpa using hh.symm

/-- Every element of `K[G]` is the assembly of an element of `(G ⧸ H) →₀ K[H]`, i.e. `assemble`
is surjective. -/
lemma exists_assemble_eq (H : Subgroup G) (K : Type*) [CommSemiring K]
    (x : MonoidAlgebra K G) :
    ∃ c : (G ⧸ H) →₀ MonoidAlgebra K H, assemble H K c = x := by
  classical
  refine ⟨∑ g ∈ x.coeff.support, Finsupp.single (cosetOf H g)
    (MonoidAlgebra.single (cosetLog H (cosetOf H g) g) (x.coeff g)), ?_⟩
  rw [assemble_finset_sum]
  rw [show (∑ g ∈ x.coeff.support, assemble H K (Finsupp.single (cosetOf H g)
      (MonoidAlgebra.single (cosetLog H (cosetOf H g) g) (x.coeff g)))) =
      ∑ g ∈ x.coeff.support, MonoidAlgebra.single g (x.coeff g) from
    Finset.sum_congr rfl fun g _ => by
      rw [assemble_single, subgroupAlgMap_single, MonoidAlgebra.single_mul_single, one_mul,
        out_mul_cosetLog H rfl]]
  exact MonoidAlgebra.sum_coeff_single x

/-! ### The main transfer theorem -/

theorem ker_le_span_of_subgroup {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Field K]
    {m t : ℕ} (y : Fin m → MonoidAlgebra K H)
    (k : Fin t → (Fin m →₀ MonoidAlgebra K H))
    (hk : Submodule.span (MonoidAlgebra K H) (Set.range k) =
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y)) :
    LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G)
        (fun j => Work.ORReductions.subgroupAlgMap H K (y j))) ≤
      Submodule.span (MonoidAlgebra K G)
        (Set.range (fun l : Fin t =>
          Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K) (map_zero _) (k l))) := by
  classical
  intro e he
  rw [LinearMap.mem_ker] at he
  choose r hr using fun j : Fin m => exists_assemble_eq H K (e j)
  set w : (G ⧸ H) →₀ MonoidAlgebra K H :=
    ∑ j : Fin m, (r j).mapRange (fun a => a * y j) (by simp) with hwdef
  have hw_apply : ∀ q : G ⧸ H, w q = ∑ j : Fin m, (r j) q * y j := by
    intro q
    rw [hwdef, Finsupp.finsetSum_apply]
    simp [Finsupp.mapRange_apply]
  have hw_zero : assemble H K w = 0 := by
    have h1 : assemble H K w =
        ∑ j : Fin m, e j * Work.ORReductions.subgroupAlgMap H K (y j) := by
      rw [hwdef, assemble_finset_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [assemble_mapRange_mul, hr j]
    rw [h1, ← he, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_of_support_subset e (Finset.subset_univ _)
      (fun j a => a • Work.ORReductions.subgroupAlgMap H K (y j)) (by intro j _; simp)]
    simp
  have hw0 : w = 0 := by
    refine sum_coset_eq_zero H K w ?_
    rw [← assemble_apply]
    exact hw_zero
  have hker : ∀ q : G ⧸ H,
      (Finsupp.onFinset Finset.univ (fun j : Fin m => (r j) q) (fun _ _ => Finset.mem_univ _))
        ∈ LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y) := by
    intro q
    rw [LinearMap.mem_ker, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _
      (by intro j _; simp)]
    simp only [Finsupp.onFinset_apply, smul_eq_mul]
    rw [← hw_apply q, hw0]
    simp
  have hcoeff : ∀ q : G ⧸ H, ∃ a : Fin t → MonoidAlgebra K H,
      ∀ j : Fin m, (∑ l : Fin t, a l * (k l) j) = (r j) q := by
    intro q
    have hmem : (Finsupp.onFinset Finset.univ (fun j : Fin m => (r j) q)
        (fun _ _ => Finset.mem_univ _)) ∈
          Submodule.span (MonoidAlgebra K H) (Set.range k) := by
      rw [hk]
      exact hker q
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, fun j => ?_⟩
    have h1 : (∑ i : Fin t, a i • k i) j = ∑ i : Fin t, a i * (k i) j := by
      rw [Finsupp.finsetSum_apply]
      simp [Finsupp.smul_apply]
    rw [← h1, ha, Finsupp.onFinset_apply]
  choose a ha using hcoeff
  set Q : Finset (G ⧸ H) := Finset.univ.biUnion fun j : Fin m => (r j).support with hQ
  set s : Fin t → MonoidAlgebra K G := fun l =>
    ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : K) *
      Work.ORReductions.subgroupAlgMap H K (a q l) with hs
  have hmain : e = ∑ l : Fin t, s l •
      Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K) (map_zero _) (k l) := by
    refine Finsupp.ext fun j => ?_
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    have h1 : e j = ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : K) *
        Work.ORReductions.subgroupAlgMap H K ((r j) q) := by
      rw [← hr j, assemble_apply]
      rw [show (r j).sum (fun q r' => MonoidAlgebra.single (Quotient.out q) (1 : K) *
            Work.ORReductions.subgroupAlgMap H K r') =
          ∑ q ∈ (r j).support, MonoidAlgebra.single (Quotient.out q) (1 : K) *
            Work.ORReductions.subgroupAlgMap H K ((r j) q) from rfl]
      exact Finset.sum_subset
        (Finset.subset_biUnion_of_mem (fun j : Fin m => (r j).support) (Finset.mem_univ j))
        (fun q _ hq => by rw [Finsupp.notMem_support_iff.mp hq]; simp)
    have h2 : (∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : K) *
          Work.ORReductions.subgroupAlgMap H K ((r j) q)) =
        ∑ q ∈ Q, ∑ l : Fin t,
          (MonoidAlgebra.single (Quotient.out q) (1 : K) *
            Work.ORReductions.subgroupAlgMap H K (a q l)) *
          Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← ha q j, subgroupAlgMap_finset_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, mul_assoc]
    have h3 : (∑ q ∈ Q, ∑ l : Fin t,
          (MonoidAlgebra.single (Quotient.out q) (1 : K) *
            Work.ORReductions.subgroupAlgMap H K (a q l)) *
          Work.ORReductions.subgroupAlgMap H K ((k l) j)) =
        ∑ l : Fin t, s l * Work.ORReductions.subgroupAlgMap H K ((k l) j) := by
      rw [hs, Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => (Finset.sum_mul Q _ _).symm
    exact h1.trans (h2.trans h3)
  rw [hmain]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self l))

end Work.ORReductions.SubgroupAlg

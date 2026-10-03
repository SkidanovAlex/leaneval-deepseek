/-
# The coordinate maps of the Laurent datum (node N7, "Laurent/Ore decomposition")

For a `LinnellDatum L`, subgroups `N ≤ H ≤ G` with `N` normal in `H`, and `s : H` whose powers
`s ^ j` (`j : ℤ`) exhaust `H/N` (so `H/N ≅ ℤ`), the subalgebra

`R = TorsionRsub L N H = ⟨D N ∪ gen H⟩ ⊆ U`

is the twisted Laurent polynomial ring `⊕_j D(N) · gen(s)^j`.  Concretely:

* every element of `Subring.closure (D N ∪ gen H)` is `laurentSum L s c = Σ_j (c j : U) * gen(s)^j`
  for a finitely supported family `c : ℤ →₀ D(N)`
  (`Work.ORLinnell.Laurent.laurentSum_exists`), and that family is unique
  (`Work.ORLinnell.Laurent.laurentSum_unique`, uniqueness being Linnell independence (I1) applied
  to the powers of `s`, which are pairwise distinct modulo `N`);

hence the assignment `y ↦ c` is a `K`-linear map `decomp : R → (ℤ →₀ D(N))`, and the coordinate
maps `coordMap i y = (decomp y) i` satisfy the three structural properties requested by
`Work.ORTorsion.LaurentBase`: the shift rule, the base rule on `D(N)·s^k`, and the
reconstruction of `y` from its coordinates.  This file constructs those maps.
-/
import Mathlib
import Submission.Work.ORFinal.TorsionData.Defs
import Submission.Work.ORLinnell.Laurent.Defs
import Submission.Work.ORLinnell.Laurent.existsUnique_laurent_rep

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

noncomputable section

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-! ## Right multiplication by a power of `gen s` -/

/-- Right multiplication by `genZPow L s j` in the ambient ring `U`, as a `K`-linear map. -/
def mulRightZ (L : LinnellDatum K G U) {H : Subgroup G} (s : H) (j : ℤ) : U →ₗ[K] U where
  toFun x := x * genZPow L (s : G) j
  map_add' a b := by rw [add_mul]
  map_smul' k a := Algebra.smul_mul_assoc k a _

@[simp] theorem mulRightZ_apply (L : LinnellDatum K G U) {H : Subgroup G} (s : H) (j : ℤ)
    (x : U) : mulRightZ L s j x = x * genZPow L (s : G) j := rfl

/-! ## The Laurent expansion map -/

/-- The `K`-linear map `(ℤ →₀ D N) → U`, `Σ_j d_j s^j ↦ Σ_j (d_j : U) * gen s ^ j`. -/
def laurentLM (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) :
    (ℤ →₀ ↥(Dsub L N)) →ₗ[K] U :=
  Finsupp.lsum K (fun j => (mulRightZ L s j).comp (Dsub L N).val.toLinearMap)

theorem laurentLM_apply (L : LinnellDatum K G U) (N H : Subgroup G) (s : H)
    (c : ℤ →₀ ↥(Dsub L N)) :
    laurentLM L N H s c = c.sum (fun j d => (d : U) * genZPow L (s : G) j) :=
  Finsupp.lsum_apply K _ c

theorem laurentLM_single (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (j : ℤ)
    (d : ↥(Dsub L N)) :
    laurentLM L N H s (Finsupp.single j d) = (d : U) * genZPow L (s : G) j := by
  rw [laurentLM, Finsupp.lsum_single]
  rfl

/-- `laurentLM` agrees with the Laurent expansion `laurentSum` of `Work.ORLinnell.Laurent`. -/
theorem laurentLM_eq_laurentSum (L : LinnellDatum K G U) (N H : Subgroup G) (s : H)
    (c : ℤ →₀ ↥(Dsub L N)) :
    laurentLM L N H s c = Work.ORLinnell.Laurent.laurentSum L s c := by
  rw [laurentLM_apply]
  show c.sum (fun j d => (d : U) * genZPow L (s : G) j)
      = c.sum (fun j d => (d : U) * Work.ORLinnell.Laurent.laurentBasis L s j)
  exact Finsupp.sum_congr fun j _ => by
    rw [genZPow_eq_gen L H s j]
    rfl

/-- **Injectivity.**  `laurentLM` is injective, since the powers of `s` are pairwise distinct
modulo `N` (Linnell independence). -/
theorem laurentLM_injective (L : LinnellDatum K G U) (N H : Subgroup G) (s : H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    Function.Injective (laurentLM L N H s) := by
  intro c c' h
  exact Work.ORLinnell.Laurent.laurentSum_unique L s hs0 c c'
    (by rw [← laurentLM_eq_laurentSum L N H s c, ← laurentLM_eq_laurentSum L N H s c', h])

/-- The image of `laurentLM` contains `R = TorsionRsub L N H`. -/
theorem TorsionRsub_le_range (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H) :
    (TorsionRsub L N H : Set U) ⊆ ((laurentLM L N H s).range : Set U) := by
  intro y hy
  have hy' : y ∈ TorsionR L N H := (mem_TorsionRsub_iff L N H y).mp (by simpa using hy)
  obtain ⟨c, hc⟩ := Work.ORLinnell.Laurent.laurentSum_exists L hNH hNn s hs y hy'
  exact ⟨c, (laurentLM_eq_laurentSum L N H s c).trans hc⟩

/-! ## The coefficient map -/

/-- The `K`-linear coefficient extraction `R → (ℤ →₀ D N)`. -/
def decomp (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ↥(TorsionRsub L N H) →ₗ[K] (ℤ →₀ ↥(Dsub L N)) :=
  (LinearEquiv.ofInjective (laurentLM L N H s) (laurentLM_injective L N H s hs0)).symm.toLinearMap.comp
    (LinearMap.codRestrict ((laurentLM L N H s).range) ((TorsionRsub L N H).val.toLinearMap)
      (fun y => TorsionRsub_le_range L N H hNH hNn s hs y.2))

theorem laurentLM_decomp (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (y : ↥(TorsionRsub L N H)) :
    laurentLM L N H s (decomp L N H hNH hNn s hs hs0 y) = (y : U) := by
  rw [decomp, LinearMap.comp_apply]
  exact LinearEquiv.ofInjective_symm_apply _ _

/-- The `i`-th coordinate map `R → D N`. -/
def coordMap (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (i : ℤ) :
    ↥(TorsionRsub L N H) →ₗ[K] ↥(Dsub L N) :=
  (Finsupp.lapply i).comp (decomp L N H hNH hNn s hs hs0)

theorem coordMap_apply (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (i : ℤ) (y : ↥(TorsionRsub L N H)) :
    coordMap L N H hNH hNn s hs hs0 i y = decomp L N H hNH hNn s hs hs0 y i := rfl

/-! ## The base rule -/

theorem coordMap_rightMulU (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (i k : ℤ) (d : ↥(Dsub L N)) :
    coordMap L N H hNH hNn s hs hs0 i
        (rightMulU L N H s k ⟨(d : U), Dsub_le_TorsionRsub L N H d.2⟩)
      = if i = k then d else 0 := by
  have hdec : decomp L N H hNH hNn s hs hs0
      (rightMulU L N H s k ⟨(d : U), Dsub_le_TorsionRsub L N H d.2⟩)
      = Finsupp.single k d := by
    refine laurentLM_injective L N H s hs0 ?_
    rw [laurentLM_decomp, laurentLM_single, rightMulU_coe]
  rw [coordMap, LinearMap.comp_apply, hdec, Finsupp.lapply_apply, Finsupp.single_apply]
  by_cases h : i = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-! ## The reconstruction from the coordinates -/

theorem coordMap_expand (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (y : ↥(TorsionRsub L N H)) :
    ∃ S : Finset ℤ, ∑ i ∈ S, rightMulU L N H s i
        ⟨((coordMap L N H hNH hNn s hs hs0 i y : ↥(Dsub L N)) : U),
          Dsub_le_TorsionRsub L N H (coordMap L N H hNH hNn s hs hs0 i y).2⟩ = y := by
  refine ⟨(decomp L N H hNH hNn s hs hs0 y).support, ?_⟩
  apply Subtype.ext
  push_cast
  simp only [rightMulU_coe, coordMap_apply]
  rw [← Finsupp.sum_of_support_subset (decomp L N H hNH hNn s hs hs0 y) (Finset.Subset.refl _)
      (fun j d => (d : U) * genZPow L (s : G) j) (by intro i _; simp),
    ← laurentLM_apply L N H s, laurentLM_decomp]

/-! ## The shift rule -/

theorem laurentLM_mapDomain_shift (L : LinnellDatum K G U) (N H : Subgroup G) (s : H) (k : ℤ)
    (c : ℤ →₀ ↥(Dsub L N)) :
    laurentLM L N H s (Finsupp.mapDomain (fun j : ℤ => j + k) c)
      = laurentLM L N H s c * genZPow L (s : G) k := by
  refine Finsupp.induction (motive := fun c => laurentLM L N H s
      (Finsupp.mapDomain (fun j : ℤ => j + k) c)
      = laurentLM L N H s c * genZPow L (s : G) k) c ?_ ?_
  · simp
  · intro a b c' hnot hb ih
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, ih, map_add,
      laurentLM_single, laurentLM_single, add_mul, genZPow_add, mul_assoc]

theorem decomp_rightMulU (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (k : ℤ) (y : ↥(TorsionRsub L N H)) :
    decomp L N H hNH hNn s hs hs0 (rightMulU L N H s k y)
      = Finsupp.mapDomain (fun j : ℤ => j + k) (decomp L N H hNH hNn s hs hs0 y) := by
  refine laurentLM_injective L N H s hs0 ?_
  rw [laurentLM_decomp, laurentLM_mapDomain_shift, laurentLM_decomp, rightMulU_coe]

theorem coordMap_shift (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) (i k : ℤ) (y : ↥(TorsionRsub L N H)) :
    coordMap L N H hNH hNn s hs hs0 i (rightMulU L N H s k y)
      = coordMap L N H hNH hNn s hs hs0 (i - k) y := by
  have hmaps : Finsupp.mapDomain (fun j : ℤ => j + k) (decomp L N H hNH hNn s hs hs0 y) i
      = decomp L N H hNH hNn s hs hs0 y (i - k) := by
    have h := Finsupp.mapDomain_apply_of_injective (f := fun j : ℤ => j + k)
      (fun a b hab => add_right_cancel hab) (decomp L N H hNH hNn s hs hs0 y) (i - k)
    simpa [show (i - k) + k = i by omega] using h
  rw [coordMap, coordMap, LinearMap.comp_apply, LinearMap.comp_apply, decomp_rightMulU,
    Finsupp.lapply_apply, Finsupp.lapply_apply, hmaps]

end

theorem coordExists {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U) (N H : Subgroup G)
    (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ∃ coord : ℤ → (↥(Work.ORFinal.TorsionData.TorsionRsub L N H) →ₗ[K]
        ↥(Work.ORFinal.TorsionData.Dsub L N)),
      (∀ (i k : ℤ) (y : ↥(Work.ORFinal.TorsionData.TorsionRsub L N H)),
        coord i (Work.ORFinal.TorsionData.rightMulU L N H s k y) = coord (i - k) y) ∧
      (∀ (i k : ℤ) (d : ↥(Work.ORFinal.TorsionData.Dsub L N)),
        coord i (Work.ORFinal.TorsionData.rightMulU L N H s k
            ⟨(d : U), Work.ORFinal.TorsionData.Dsub_le_TorsionRsub L N H d.2⟩)
          = if i = k then d else 0) ∧
      (∀ y : ↥(Work.ORFinal.TorsionData.TorsionRsub L N H), ∃ S : Finset ℤ,
        ∑ i ∈ S, Work.ORFinal.TorsionData.rightMulU L N H s i
            ⟨((coord i y : ↥(Work.ORFinal.TorsionData.Dsub L N)) : U),
              Work.ORFinal.TorsionData.Dsub_le_TorsionRsub L N H (coord i y).2⟩ = y) := by
  refine ⟨coordMap L N H hNH hNn s hs hs0, ?_, ?_, ?_⟩
  · intro i k y
    exact coordMap_shift L N H hNH hNn s hs hs0 i k y
  · intro i k d
    exact coordMap_rightMulU L N H hNH hNn s hs hs0 i k d
  · intro y
    exact coordMap_expand L N H hNH hNn s hs hs0 y

end Work.ORFinal.TorsionData

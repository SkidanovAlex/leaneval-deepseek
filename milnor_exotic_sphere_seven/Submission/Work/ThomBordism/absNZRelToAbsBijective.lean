import Mathlib
import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.Tubular.onePoint_pairing_transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- **The forgetful map `H^{m+1}(X,A;ℤ) → H^{m+1}(X;ℤ)` is bijective for a contractible `A`,
in degrees `m + 1 ≥ 2`.**  A contractible space has vanishing cohomology in every positive degree
(`Work.Cohomology.contractible`), so in the long exact sequence of the pair `(X,A)`

`H^m(A) → H^{m+1}(X,A) → H^{m+1}(X) → H^{m+1}(A)`

both outer terms vanish for `m ≥ 1`: the first gives injectivity (a mono is injective) and the
second surjectivity (an epi is surjective). -/
theorem relToAbs_bijective_of_contractible {X : Type} [TopologicalSpace X] {A : Set X}
    (hcon : ContractibleSpace ↥A) {m : ℕ} (hm : 1 ≤ m) :
    Function.Bijective ((Work.Thom.relToAbs ℤ A (m + 1)).hom) := by
  haveI := hcon
  have H1 : CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ m (TopCat.of ↥A)) := by
    rw [← Nat.sub_add_cancel hm]
    exact Work.Cohomology.contractible ℤ (TopCat.of ↥A) (m - 1)
  have H2 : CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ (m + 1) (TopCat.of ↥A)) :=
    Work.Cohomology.contractible ℤ (TopCat.of ↥A) m
  have hrel : Work.Thom.relToAbs ℤ A (m + 1)
      = HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℤ (TopCat.of X) A) (m + 1) := rfl
  rw [hrel]
  have hmono : Mono (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of X) A) (m + 1)) := by
    have hδ : Work.Cohomology.pairδ ℤ (TopCat.of X) A m = 0 := H1.eq_of_src _ 0
    exact (ShortComplex.exact_iff_mono _ hδ).mp
      (Work.Cohomology.pair_exact₁ ℤ (TopCat.of X) A m)
  have hepi : Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of X) A) (m + 1)) := by
    have hrestr : HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℤ (TopCat.of X) A) (m + 1) = 0 := H2.eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hrestr).mp
      (Work.Cohomology.pair_exact₂ ℤ (TopCat.of X) A (m + 1))
  exact ⟨(ModuleCat.mono_iff_injective _).mp hmono,
    (ModuleCat.epi_iff_surjective _).mp hepi⟩

theorem absNZRelToAbsBijective {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι)
    (hcon : ContractibleSpace ↥(Work.ThomBordism.absNZ Z)) {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective ((Work.Thom.relToAbs ℤ (Work.ThomBordism.absNZ Z) n).hom) := by
  have hm : 1 ≤ n - 1 := by omega
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [← hn']
  exact relToAbs_bijective_of_contractible hcon hm

end

end Work.ThomBordism

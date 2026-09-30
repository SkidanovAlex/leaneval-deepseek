import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_aux
import Submission.Work.SymQuot.Chart.chartRes_isOpen_range
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding
import Submission.Work.SymQuot.Chart.chartMap_fiber_orbit
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.Chart

variable {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}

/-! ## Auxiliary lemmas -/

/-- The basic open of the conjugate of a section by `g` is the preimage of the basic open of the
section under the action of `g`. -/
lemma basicOpen_sectionHom (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hUi : A.IsInvariantOpen U) (g : G) (f : Γ(X, U)) :
    X.basicOpen (Work.SymQuot.GAction.sectionHom A U hUi g f)
      = (A.hom g) ⁻¹ᵁ (X.basicOpen f) := by
  rw [Work.SymQuot.GAction.sectionHom_apply, Scheme.basicOpen_appLE, inf_eq_right]
  exact ((A.hom g).preimage_mono (X.basicOpen_le f)).trans (le_of_eq (hUi g))

/-- The basic open of a finite product of sections over `U`. -/
lemma basicOpen_prod {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, U)) :
    X.basicOpen (∏ i ∈ s, f i) = U ⊓ ⨅ i ∈ s, X.basicOpen (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.iInf_insert,
        inf_left_comm]

/-- A finite product of sections vanishes only where one of its factors vanishes. -/
lemma basicOpen_prod_le {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, U)) {j : ι}
    (hj : j ∈ s) : X.basicOpen (∏ i ∈ s, f i) ≤ X.basicOpen (f j) := by
  classical
  induction s using Finset.induction with
  | empty => exact absurd hj (Finset.notMem_empty j)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact inf_le_left
      · exact inf_le_right.trans (ih hj')

/-- Membership in the basic open of a finite product of sections over `U`. -/
lemma mem_basicOpen_prod_of_mem {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, U))
    {x : X} (hx : x ∈ U) : x ∈ X.basicOpen (∏ i ∈ s, f i) ↔ ∀ i ∈ s, x ∈ X.basicOpen (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hx]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
      simp only [TopologicalSpace.Opens.mem_inf, ih]
      constructor
      · rintro ⟨h₁, h₂⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h₁
        · exact h₂ i hi
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
          fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- The dictionary between the points of an affine open `U` and the primes of `Γ(X,U)`. -/
lemma mem_basicOpen_iff_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) (u : U)
    (f : Γ(X, U)) : U.ι u ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf u).asIdeal := by
  have h1 : (hU.fromSpec (hU.primeIdealOf u)) ∈ X.basicOpen f ↔ U.ι u ∈ X.basicOpen f := by
    rw [hU.fromSpec_primeIdealOf]
    exact Iff.rfl
  rw [← h1]
  have h2 : (hU.fromSpec (hU.primeIdealOf u)) ∈ X.basicOpen f ↔
      hU.primeIdealOf u ∈
        (PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum Γ(X, U))) := by
    rw [← hU.fromSpec_preimage_basicOpen]
    exact Iff.rfl
  rw [h2]
  exact PrimeSpectrum.mem_basicOpen f _

/-- **Prime avoidance for basic opens.**  For an affine open `U`, an open `V ≤ U` and finitely
many points of `V`, there is a section of `Γ(X,U)` whose basic open is contained in `V` and
contains all these points. -/
theorem sections_basicOpen_finset {U V : X.Opens} (hU : IsAffineOpen U) (hVU : V ≤ U)
    (S : Finset X) (hS : ∀ s ∈ S, s ∈ V) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ ∀ s ∈ S, s ∈ X.basicOpen f := by
  classical
  -- the ideal of sections whose basic open lies inside `V`
  let I : Ideal Γ(X, U) :=
    { carrier := {f | X.basicOpen f ≤ V}
      add_mem' := fun {f g} hf hg => by
        change X.basicOpen (f + g) ≤ V
        exact (Scheme.basicOpen_add_le X f g).trans (sup_le hf hg)
      zero_mem' := by simp
      smul_mem' := fun c f hf => by
        rw [smul_eq_mul]
        change X.basicOpen (c * f) ≤ V
        rw [Scheme.basicOpen_mul]
        exact inf_le_right.trans hf }
  have hmemI : ∀ f : Γ(X, U), f ∈ I ↔ X.basicOpen f ≤ V := fun f => Iff.rfl
  -- for every point of `S` some element of `I` does not vanish there
  set pr : {t // t ∈ S} → Ideal Γ(X, U) :=
    fun s => (hU.primeIdealOf ⟨s.1, hVU (hS s.1 s.2)⟩).asIdeal with hpr
  have hprime : ∀ i ∈ (S.attach.image pr : Finset (Ideal Γ(X, U))), i.IsPrime := by
    intro i hi
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hi
    rw [← hs]
    exact PrimeSpectrum.isPrime _
  have hnot : ∀ s : {t // t ∈ S}, ¬ I ≤ pr s := by
    intro s
    obtain ⟨f, hf₁, hf₂⟩ :=
      hU.exists_basicOpen_le (V := V) ⟨s.1, hS s.1 s.2⟩ (hVU (hS s.1 s.2))
    intro hle
    exact (mem_basicOpen_iff_primeIdealOf hU ⟨s.1, hVU (hS s.1 s.2)⟩ f).mp hf₂
      (hle ((hmemI f).mpr hf₁))
  -- prime avoidance: some element of `I` avoids all the primes
  have hex : ¬ ((I : Set Γ(X, U)) ⊆
      ⋃ i ∈ ((S.attach.image pr : Finset (Ideal Γ(X, U))) : Set (Ideal Γ(X, U))), i) := by
    intro hsub
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime_finite (f := id)
      (S.attach.image pr).finite_toSet (⊤ : Ideal Γ(X, U)) ⊤
      (fun i hi _ _ => hprime i hi)).mp hsub
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hi
    exact hnot s (hs ▸ hle)
  obtain ⟨f, hfI, hfT⟩ := Set.not_subset.mp hex
  simp only [Set.mem_iUnion, not_exists] at hfT
  have hnotmem : ∀ s : {t // t ∈ S}, f ∉ pr s := fun s hfs =>
    hfT (pr s) (Finset.mem_image.mpr ⟨s, Finset.mem_attach _ _, rfl⟩) hfs
  exact ⟨f, (hmemI f).mp hfI, fun s hs =>
    (mem_basicOpen_iff_primeIdealOf hU ⟨s, hVU (hS s hs)⟩ f).mpr (hnotmem ⟨s, hs⟩)⟩

/-- **The norm of a section is fixed.**  If a section `f` over a `G`-invariant open `U` does not
vanish on the orbit of a point `u ∈ U`, then the norm `∏ g • f` of `f` is a `G`-fixed section
which does not vanish at `u` and vanishes at least where `f` does. -/
theorem invariantSection_orbit (A : Work.SymQuot.GAction G X) {U : X.Opens}
    (hUi : A.IsInvariantOpen U) (u : U) (f : Γ(X, U))
    (hx : ∀ g : G, A.hom g (U.ι u) ∈ X.basicOpen f) :
    ∃ h : Γ(X, U), (∀ g : G, Work.SymQuot.GAction.sectionHom A U hUi g h = h) ∧
      X.basicOpen h ≤ X.basicOpen f ∧ U.ι u ∈ X.basicOpen h := by
  classical
  cases nonempty_fintype G
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hUi
  have hsmul : ∀ (g : G) (x : Γ(X, U)),
      g • x = Work.SymQuot.GAction.sectionHom A U hUi g⁻¹ x := fun g x => rfl
  refine ⟨∏ g : G, g • f, ?_, ?_, ?_⟩
  · intro g
    simpa only [inv_inv] using
      (hsmul g⁻¹ (∏ g' : G, g' • f)).symm.trans (Finset.smul_prod_perm f g⁻¹)
  · refine (basicOpen_prod_le Finset.univ (fun g : G => g • f) (Finset.mem_univ (1 : G))).trans ?_
    rw [one_smul]
  · refine (mem_basicOpen_prod_of_mem Finset.univ (fun g : G => g • f) (hx := u.2)).mpr ?_
    intro g _
    rw [hsmul g f, basicOpen_sectionHom A hUi g⁻¹ f]
    simpa only [Scheme.Hom.mem_preimage, Scheme.Opens.ι_apply] using hx g⁻¹

theorem chartRes_cover {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {V U : X.Opens} (hVU : V ≤ U)
    (hU : AlgebraicGeometry.IsAffineOpen U) (hV : AlgebraicGeometry.IsAffineOpen V)
    (hUi : A.IsInvariantOpen U) (hVi : A.IsInvariantOpen V)
    (y : Work.SymQuot.GAction.chart A V hVi) :
    ∃ (h : X.presheaf.obj (Opposite.op U))
      (hh : ∀ g : G, Work.SymQuot.GAction.sectionHom A U hUi g h = h)
      (hle : X.basicOpen h ≤ V),
      y ∈ Set.range ⇑(Work.SymQuot.GAction.chartRes A (X.basicOpen h) V hle hVi
        (Work.SymQuot.Chart.isInvariantOpen_basicOpen A hUi h hh)) := by
  classical
  cases nonempty_fintype G
  -- 1. a point of `V` above `y`
  obtain ⟨x, hx⟩ := chartMap_surjective A hV hVi y
  -- 2. the corresponding point of `U`
  let u : U := X.homOfLE hVU x
  have hux : U.ι u = V.ι x := by
    have h := congrFun (congrArg (fun φ : V.toScheme ⟶ X => ⇑φ) (Scheme.homOfLE_ι X hVU)) x
    simpa only [Scheme.Hom.comp_apply] using h
  have huV : U.ι u ∈ V := by
    rw [hux]
    exact x.2
  -- 3. a section over `U`, with basic open inside `V`, avoiding the orbit of `u`
  let S : Finset X := Finset.univ.image (fun g : G => A.hom g (U.ι u))
  have hS : ∀ s ∈ S, s ∈ V := by
    intro s hs
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hs
    exact hVi.smul_mem huV g
  obtain ⟨f, hfV, hfS⟩ := sections_basicOpen_finset hU hVU S hS
  -- 4. the norm of `f`, a fixed section
  obtain ⟨h, hh, hhf, humem⟩ := invariantSection_orbit A hUi u f (fun g => hfS _
    (Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩))
  have hle : X.basicOpen h ≤ V := hhf.trans hfV
  refine ⟨h, hh, hle, ?_⟩
  rw [range_chartRes_eq_image_homOfLE A hle hVi (hU.basicOpen h)
    (Work.SymQuot.Chart.isInvariantOpen_basicOpen A hUi h hh)]
  exact ⟨x, (mem_range_homOfLE hle).mpr (by rw [← hux]; exact humem), hx⟩

end Work.SymQuot.Chart

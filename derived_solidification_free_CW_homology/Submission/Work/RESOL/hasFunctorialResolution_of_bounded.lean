import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Telescope
import Submission.Work.RESOL.telD_natural
import Submission.Work.RESOL.telDesc_natural
import Submission.Work.RESOL.exists_windowTower
import Submission.Work.RESOL.quasiIso_telDesc

/-!
# AREA RESOL — functorial solid-cofibrant resolutions of unbounded complexes

Given a functorial resolution `R` of *bounded* complexes (the hypothesis `hR`), we build a
functorial solid-cofibrant resolution of an *arbitrary* complex `K` by the classical telescope
construction: telescope the bounded two-sided truncations `σ_n K` of `K`, resolved by `R`.

The construction is the following.  Let `(W n, wtr n, wto n)` be a functorial tower of bounded
complexes with `K = colim_n W n K` (see `exists_windowTower`).  Set

* `seqP R W K n := R (W n K)` (cofibrant, since `W n K` is bounded above),
* `seqT R W K n := R (wtr n K) : seqP K n ⟶ seqP K (n+1)`,
* `ρ K := mappingCone (1 - shift : ∐ n, seqP K n ⟶ ∐ n, seqP K n)`,
* `ε K := telDesc : ρ K ⟶ K`, induced by the compatible cocone
  `seqP K n ⟶ K` given by `ε_{W n K} ≫ wto n`.

Then `ρ` is a functor, `ε` is natural, `ρ K` is solid-cofibrant (coproducts and mapping cones of
cofibrant complexes are cofibrant, `hC`), and `ε K` is a quasi-isomorphism (it is the telescope
comparison map, `quasiIso_telDesc`).
-/

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local instance 2000] HomologicalComplex.instHasColimitsOfShape

/-- The distinguished triangle of a mapping cone, stated for the rotation used to transfer
cofibrancy. -/
lemma mappingCone_triangleh_mem {K L : Cpx} (f : K ⟶ L) :
    CochainComplex.mappingCone.triangleh f ∈ Pretriangulated.distinguishedTriangles :=
  ⟨K, L, f, ⟨Iso.refl _⟩⟩

/-! ### The resolved telescope functor -/

/-- The `n`-th piece of the tower applied to `K`, then resolved by `R`. -/
abbrev seqP (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (K : Cpx) : ℕ → Cpx :=
  fun n => R.obj ((W n).obj K)

/-- The transition maps of the resolved tower. -/
abbrev seqT (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wtr : ∀ n : ℕ, W n ⟶ W (n+1)) (K : Cpx) :
    ∀ n : ℕ, seqP R W K n ⟶ seqP R W K (n+1) :=
  fun n => R.map ((wtr n).app K)

@[simp]
lemma seqP_apply (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (K : Cpx) (n : ℕ) :
    seqP R W K n = R.obj ((W n).obj K) := rfl

@[simp]
lemma seqT_apply (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    (K : Cpx) (n : ℕ) : seqT R W wtr K n = R.map ((wtr n).app K) := rfl

lemma seqT_natural (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    (K L : Cpx) (φ : K ⟶ L) (n : ℕ) :
    seqT R W wtr K n ≫ R.map ((W (n+1)).map φ) =
      R.map ((W n).map φ) ≫ seqT R W wtr L n := by
  simp only [seqT, ← R.map_comp, (wtr n).naturality]

/-- The map `∐ n, R (W n K) ⟶ ∐ n, R (W n L)` induced by `φ : K ⟶ L`. -/
abbrev sigmaMap (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) {K L : Cpx} (φ : K ⟶ L) :
    (∐ seqP R W K) ⟶ (∐ seqP R W L) :=
  Sigma.desc (fun n : ℕ => R.map ((W n).map φ) ≫ Sigma.ι (seqP R W L) n)

lemma Sigma_ι_sigmaMap (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) {K L : Cpx} (φ : K ⟶ L) (n : ℕ) :
    Sigma.ι (seqP R W K) n ≫ sigmaMap R W φ =
      R.map ((W n).map φ) ≫ Sigma.ι (seqP R W L) n :=
  Sigma.ι_comp_desc _ n

@[simp]
lemma sigmaMap_id (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (K : Cpx) :
    sigmaMap R W (𝟙 K) = 𝟙 (∐ seqP R W K) := by
  apply Sigma.hom_ext
  intro n
  rw [Sigma_ι_sigmaMap, (W n).map_id, R.map_id]
  simp

lemma sigmaMap_comp (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) {K L M : Cpx} (φ : K ⟶ L)
    (ψ : L ⟶ M) : sigmaMap R W (φ ≫ ψ) = sigmaMap R W φ ≫ sigmaMap R W ψ := by
  apply Sigma.hom_ext
  intro n
  rw [Sigma_ι_sigmaMap, (W n).map_comp, R.map_comp, Category.assoc,
    ← Category.assoc (Sigma.ι (seqP R W K) n) (sigmaMap R W φ) (sigmaMap R W ψ),
    Sigma_ι_sigmaMap, Category.assoc, Sigma_ι_sigmaMap]

/-- Naturality of `telD` along `sigmaMap`. -/
lemma telD_sigmaMap (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    {K L : Cpx} (φ : K ⟶ L) :
    telD (seqP R W K) (seqT R W wtr K) ≫ sigmaMap R W φ =
      sigmaMap R W φ ≫ telD (seqP R W L) (seqT R W wtr L) :=
  telD_natural (seqP R W K) (seqP R W L) (seqT R W wtr K) (seqT R W wtr L)
    (fun n => R.map ((W n).map φ)) (fun n => seqT_natural R W wtr K L φ n)

/-- The compatibility of `telD` with `sigmaMap`, phrased for the functoriality of `telFunctor`. -/
lemma telFunctor_map_comm (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx))
    (wtr : ∀ n : ℕ, W n ⟶ W (n+1)) {K L : Cpx} (φ : K ⟶ L) :
    telD (seqP R W K) (seqT R W wtr K) ≫ sigmaMap R W φ =
      sigmaMap R W φ ≫ telD (seqP R W L) (seqT R W wtr L) :=
  telD_sigmaMap R W wtr φ

/-- The resolved telescope of `K`. -/
abbrev telObj (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wtr : ∀ n : ℕ, W n ⟶ W (n+1)) (K : Cpx) :
    Cpx := tel (seqP R W K) (seqT R W wtr K)

/-- The functor `K ↦ tel (∐ n, R (W n K))`. -/
def telFunctor (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    [∀ K : Cpx, HasCoproduct (seqP R W K)] : Cpx ⥤ Cpx where
  obj K := telObj R W wtr K
  map {K L} φ :=
    CochainComplex.mappingCone.map (telD (seqP R W K) (seqT R W wtr K))
      (telD (seqP R W L) (seqT R W wtr L)) (sigmaMap R W φ) (sigmaMap R W φ)
      (telD_sigmaMap R W wtr φ)
  map_id K := by
    have h := CochainComplex.mappingCone.map_id (telD (seqP R W K) (seqT R W wtr K))
    simpa only [telObj, tel, sigmaMap_id] using h
  map_comp {K L M} φ ψ := by
    have h := CochainComplex.mappingCone.map_comp (telD (seqP R W K) (seqT R W wtr K))
      (telD (seqP R W L) (seqT R W wtr L)) (telD (seqP R W M) (seqT R W wtr M))
      (sigmaMap R W φ) (sigmaMap R W φ) (telD_sigmaMap R W wtr φ)
      (sigmaMap R W ψ) (sigmaMap R W ψ) (telD_sigmaMap R W wtr ψ)
    simpa only [telObj, tel, sigmaMap_comp] using h

/-! ### The counit of the telescope -/

/-- The compatible cocone `R (W n K) ⟶ K` induced by `ε : R ⟶ 𝟭` and `wto`. -/
abbrev epsF (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (ε : R ⟶ 𝟭 Cpx)
    (wto : ∀ n : ℕ, W n ⟶ 𝟭 Cpx) (K : Cpx) : ∀ n : ℕ, seqP R W K n ⟶ K :=
  fun n => ε.app ((W n).obj K) ≫ (wto n).app K

lemma epsF_compat (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wto : ∀ n : ℕ, W n ⟶ 𝟭 Cpx)
    (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    (hcompat : ∀ (n : ℕ) (K : Cpx), (wtr n).app K ≫ (wto (n+1)).app K = (wto n).app K)
    (ε : R ⟶ 𝟭 Cpx) (K : Cpx) (n : ℕ) :
    seqT R W wtr K n ≫ epsF R W ε wto K (n+1) = epsF R W ε wto K n := by
  simp only [seqT, epsF]
  rw [← Category.assoc, ε.naturality]
  simp [hcompat n K]

/-- The natural transformation `telFunctor R W wtr ⟶ 𝟭 Cpx`. -/
def telEps (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wto : ∀ n : ℕ, W n ⟶ 𝟭 Cpx)
    (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    (hcompat : ∀ (n : ℕ) (K : Cpx), (wtr n).app K ≫ (wto (n+1)).app K = (wto n).app K)
    (ε : R ⟶ 𝟭 Cpx)
    [∀ K : Cpx, HasCoproduct (seqP R W K)] : telFunctor R W wtr ⟶ 𝟭 Cpx where
  app K := telDesc (seqP R W K) (seqT R W wtr K) K (epsF R W ε wto K)
    (epsF_compat R W wto wtr hcompat ε K)
  naturality {K L} φ := by
    have hgu : ∀ n : ℕ, R.map ((W n).map φ) ≫ epsF R W ε wto L n = epsF R W ε wto K n ≫ φ := by
      intro n
      simp only [epsF]
      rw [← Category.assoc, ε.naturality]
      simp [(wto n).naturality]
    have h := telDesc_natural (seqP R W K) (seqP R W L) (seqT R W wtr K) (seqT R W wtr L)
      K L (epsF R W ε wto K) (epsF R W ε wto L)
      (epsF_compat R W wto wtr hcompat ε K) (epsF_compat R W wto wtr hcompat ε L)
      (fun n => R.map ((W n).map φ)) (telD_sigmaMap R W wtr φ) φ hgu
    exact h.symm

/-! ### Cofibrancy -/

theorem solidCofibrant_telObj (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx))
    (wtr : ∀ n : ℕ, W n ⟶ W (n+1)) (hC : CofibrantClosure)
    (hcof : ∀ (B : Cpx), IsBoundedAbove B → Submission.Blueprint.SolidCofibrant (R.obj B))
    (hbdd : ∀ (n : ℕ) (K : Cpx), IsBoundedAbove ((W n).obj K))
    (K : Cpx) : Submission.Blueprint.SolidCofibrant (telObj R W wtr K) := by
  have hP : Submission.Blueprint.SolidCofibrant (∐ seqP R W K) :=
    hC.sigma ℕ (seqP R W K) (fun n => hcof _ (hbdd n K))
  have hPH : SolidCofibrantH (Submission.Blueprint.hq (∐ seqP R W K)) :=
    (solidCofibrant_iff _).mp hP
  have hT : CochainComplex.mappingCone.triangleh (telD (seqP R W K) (seqT R W wtr K)) ∈
      Pretriangulated.distinguishedTriangles := mappingCone_triangleh_mem _
  have h := hC.cone (CochainComplex.mappingCone.triangleh (telD (seqP R W K) (seqT R W wtr K)))
    hT (fun n => hC.shift n _ hPH) (fun n => hC.shift n _ hPH)
  have hobj : (CochainComplex.mappingCone.triangleh (telD (seqP R W K) (seqT R W wtr K))).obj₃ =
      Submission.Blueprint.hq
        (CochainComplex.mappingCone (telD (seqP R W K) (seqT R W wtr K))) := by
    first
      | simp [CochainComplex.mappingCone.triangleh, CochainComplex.mappingCone.triangle]
      | simp [CochainComplex.mappingCone.triangleh]
      | rfl
  rw [hobj] at h
  exact (solidCofibrant_iff _).mpr (by simpa only [telObj, tel] using h)

/-! ### The quasi-isomorphism -/

theorem quasiIso_telEps (R : Cpx ⥤ Cpx) (W : ℕ → (Cpx ⥤ Cpx)) (wto : ∀ n : ℕ, W n ⟶ 𝟭 Cpx)
    (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
    (hcompat : ∀ (n : ℕ) (K : Cpx), (wtr n).app K ≫ (wto (n+1)).app K = (wto n).app K)
    (ε : R ⟶ 𝟭 Cpx)
    (hQI : ∀ B : Cpx, IsBoundedAbove B → IsBoundedBelow B → QuasiIso (ε.app B))
    (hbdd : ∀ (n : ℕ) (K : Cpx), IsBoundedAbove ((W n).obj K) ∧ IsBoundedBelow ((W n).obj K))
    (hev : ∀ k : ℤ, ∃ N : ℕ, ∀ n ≥ N, ∀ K : Cpx, QuasiIsoAt ((wto n).app K) k)
    (K : Cpx) : QuasiIso ((telEps R W wto wtr hcompat ε).app K) := by
  refine quasiIso_telDesc (seqP R W K) (seqT R W wtr K) K (epsF R W ε wto K)
    (epsF_compat R W wto wtr hcompat ε K) ?_
  intro k
  obtain ⟨N, hN⟩ := hev k
  refine ⟨N, fun n hn => ?_⟩
  haveI h1 : QuasiIso (ε.app ((W n).obj K)) := hQI _ (hbdd n K).1 (hbdd n K).2
  haveI h2 : QuasiIsoAt ((wto n).app K) k := hN n hn K
  simpa only [epsF] using (inferInstance : QuasiIsoAt (ε.app ((W n).obj K) ≫ (wto n).app K) k)

/-! ### Assembly -/

theorem hasFunctorialResolution_of_bounded (hC : Work.RESOL.CofibrantClosure)
    (hR : ∃ (R : CategoryTheory.Functor Work.RESOL.Cpx Work.RESOL.Cpx)
        (ε : R ⟶ CategoryTheory.Functor.id Work.RESOL.Cpx),
      (∀ B : Work.RESOL.Cpx, Work.RESOL.HasAtomicTerms (R.obj B)) ∧
      (∀ B : Work.RESOL.Cpx, Work.RESOL.IsBoundedAbove B → Work.RESOL.IsBoundedBelow B →
        QuasiIso (ε.app B)) ∧
      (∀ B : Work.RESOL.Cpx, Work.RESOL.IsBoundedAbove B →
        Submission.Blueprint.SolidCofibrant (R.obj B))) :
    Work.RESOL.HasFunctorialResolution := by
  obtain ⟨R, ε, _hAt, hQI, hCof⟩ := hR
  obtain ⟨W, wtr, wto, hbdd, hcompat, hev⟩ := exists_windowTower
  haveI : ∀ K : Cpx, HasCoproduct (seqP R W K) := fun K => inferInstance
  refine ⟨telFunctor R W wtr, telEps R W wto wtr hcompat ε, fun K => ?_, fun K => ?_⟩
  · exact solidCofibrant_telObj R W wtr hC hCof (fun n K => (hbdd n K).1) K
  · exact quasiIso_telEps R W wto wtr hcompat ε hQI hbdd hev K

end Work.RESOL

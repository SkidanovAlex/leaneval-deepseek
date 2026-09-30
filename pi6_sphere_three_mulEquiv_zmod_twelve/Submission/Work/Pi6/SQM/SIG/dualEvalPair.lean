import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.Cohomology.relCupH
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.SQM.SIG.DualEvalPairDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Pi6.SQM.SIG

noncomputable section

/-! ## Elementary computation rules for (co)cycles of a complex of `F`-modules

The five lemmas below are stated for an arbitrary `HomologicalComplex` of `F`-modules (chain or
cochain); they are the only place where the underlying sets of the `cycles` are used. -/

/-- The inclusion of the cycles, evaluated on a boundary: `iCycles (toCycles y) = d y`. -/
lemma iCycles_toCycles_apply (F : Type) [Field F] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{0} F) c) (i j : ι) [K.HasHomology j] (y : ↥(K.X i)) :
    (K.iCycles j).hom ((K.toCycles i j).hom y) = (K.d i j).hom y := by
  have h := congrArg (fun (g : K.X i ⟶ K.X j) => g.hom y) (HomologicalComplex.toCycles_i K i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- A cycle of a complex of `F`-modules is killed by the differential. -/
lemma iCycles_d_apply (F : Type) [Field F] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{0} F) c) (i j : ι) (w : K.cycles i) :
    (K.d i j).hom ((K.iCycles i).hom w) = 0 := by
  have h := congrArg (fun (g : K.cycles i ⟶ K.X j) => g.hom w) (HomologicalComplex.iCycles_d K i j)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] using h

/-- Boundaries have zero homology class. -/
lemma homologyπ_toCycles_apply (F : Type) [Field F] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{0} F) c) (i j : ι) [K.HasHomology j] (y : ↥(K.X i)) :
    (K.homologyπ j).hom ((K.toCycles i j).hom y) = 0 := by
  have h := congrArg (fun (g : K.X i ⟶ K.homology j) => g.hom y)
    (HomologicalComplex.toCycles_comp_homologyπ K i j)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] using h

/-- The inclusion of the cycles is injective. -/
lemma iCycles_injective (F : Type) [Field F] {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{0} F) c) (i : ι) :
    Function.Injective (K.iCycles i).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- A morphism of complexes sends the class of a cycle to the class of the image cycle. -/
lemma cyclesMap_i_apply (F : Type) [Field F] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{0} F) c} (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := congrArg (fun (g : K.cycles i ⟶ L.X i) => g.hom z)
    (HomologicalComplex.cyclesMap_i φ i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- `fdVal` is the identity, made into a rewrite rule. -/
@[simp] lemma fdVal_id (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (φ : ↥((Work.Cohomology.dualComplex F E).X n)) : Work.StemsB.fdVal F E n φ = φ := rfl

/-- The defining formula of the transposed chain map, in the form needed below. -/
lemma dualComplexMapComp_fdVal (F : Type) [Field F]
    {C D : ChainComplex (ModuleCat.{0} F) ℕ} (g : C ⟶ D) (n : ℕ)
    (X : ↥((Work.Cohomology.dualComplex F D).X n)) (y : ↥(C.X n)) :
    (Work.Cohomology.dualComplexMapComp F C D g n).hom X y =
      Work.StemsB.fdVal F D n X ((g.f n).hom y) := by
  rw [Work.Cohomology.dualComplexMapComp_apply]
  simp only [fdVal_id]

/-- The dual differential, evaluated through `fdVal`: the value of the coboundary of `y` at `x` is
the value of `y` at the boundary of `x`. -/
lemma fdVal_dual_d_apply (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (m : ℕ)
    (y : ↥((Work.Cohomology.dualComplex F E).X m)) (x : ↥(E.X (m + 1))) :
    Work.StemsB.fdVal F E (m + 1) ((Work.Cohomology.dualComplex F E).d m (m + 1) y) x
      = Work.StemsB.fdVal F E m y ((E.d (m + 1) m).hom x) := by
  have h : Work.StemsB.fdVal F E (m + 1)
        ((Work.Cohomology.dualComplex F E).d m (m + 1) y)
      = (Work.StemsB.fdVal F E m y).comp (E.d (m + 1) m).hom := by
    simp only [fdVal_id]
    exact Work.StemsB.fd_d_apply F E m y
  have h2 := LinearMap.congr_fun h x
  rw [LinearMap.comp_apply] at h2
  exact h2

/-! ## Evaluation of an element of the dual complex against the cycles -/

/-- Evaluation of a degree-`n` element of the dual complex against the `n`-cycles, as a linear
map in the element of the dual complex. -/
def sigEval (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    ↥((Work.Cohomology.dualComplex F E).X n) →ₗ[F] (↥(E.cycles n) →ₗ[F] F) where
  toFun φ := (Work.StemsB.fdVal F E n φ).comp (E.iCycles n).hom
  map_add' a b := by
    ext z
    rfl
  map_smul' r a := by
    ext z
    simp

/-! ## The functional on the homology determined by a cocycle -/

/-- A cocycle of the dual complex pairs trivially with a boundary: this is what makes the
descent to the homology of the chain complex possible. -/
lemma toCycles_sigEval (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) :
    E.toCycles (n + 1) n ≫
      ModuleCat.ofHom (sigEval F E n ((Work.Cohomology.dualComplex F E).iCycles n w)) = 0 := by
  have hcoc : (Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w)).comp
      (E.d (n + 1) n).hom = 0 := by
    rw [← Work.StemsB.fd_d_apply F E n]
    exact iCycles_d_apply F (Work.Cohomology.dualComplex F E) n (n + 1) w
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  show (Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w))
      ((E.iCycles n).hom ((E.toCycles (n + 1) n).hom y)) = 0
  rw [iCycles_toCycles_apply F E (n + 1) n y]
  exact LinearMap.congr_fun hcoc y

/-- The functional on the `n`-th homology determined by an `n`-cocycle of the dual complex. -/
def sigFun (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) : ↥(E.homology n) →ₗ[F] F :=
  (Cofork.IsColimit.desc (E.homologyIsCokernel (n + 1) n (Work.Cohomology.down_prev n))
    (ModuleCat.ofHom (sigEval F E n ((Work.Cohomology.dualComplex F E).iCycles n w)))
    (by simpa using toCycles_sigEval F E n w)).hom

/-- The value of `sigFun` on the class of a cycle. -/
lemma sigFun_apply (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) (z : E.cycles n) :
    sigFun F E n w ((E.homologyπ n) z)
      = (Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w))
          ((E.iCycles n).hom z) := by
  have h := Cofork.IsColimit.π_desc'
    (E.homologyIsCokernel (n + 1) n (Work.Cohomology.down_prev n))
    (ModuleCat.ofHom (sigEval F E n ((Work.Cohomology.dualComplex F E).iCycles n w)))
    (by simpa using toCycles_sigEval F E n w)
  have h2 := congrArg (fun (g : E.cycles n ⟶ ModuleCat.of F F) => g.hom z) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    CokernelCofork.π_ofπ] at h2
  show (Cofork.IsColimit.desc (E.homologyIsCokernel (n + 1) n (Work.Cohomology.down_prev n))
      (ModuleCat.ofHom (sigEval F E n ((Work.Cohomology.dualComplex F E).iCycles n w)))
      (by simpa using toCycles_sigEval F E n w)).hom ((E.homologyπ n) z)
    = (Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w))
        ((E.iCycles n).hom z)
  exact h2

lemma sigFun_add (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w w' : (Work.Cohomology.dualComplex F E).cycles n) :
    sigFun F E n (w + w') = sigFun F E n w + sigFun F E n w' := by
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (E.homologyπ n)).mp inferInstance y
  rw [LinearMap.add_apply, sigFun_apply F E n (w + w') z, sigFun_apply F E n w z,
    sigFun_apply F E n w' z]
  simp only [fdVal_id, map_add]
  rfl

lemma sigFun_smul (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) (r : F)
    (w : (Work.Cohomology.dualComplex F E).cycles n) :
    sigFun F E n (r • w) = r • sigFun F E n w := by
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (E.homologyπ n)).mp inferInstance y
  rw [LinearMap.smul_apply, sigFun_apply F E n (r • w) z, sigFun_apply F E n w z]
  simp only [fdVal_id, map_smul]
  try rfl

/-- The evaluation pairing, at the level of cycles: `w ↦ (z ↦ w z)`. -/
def sigLin (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    (Work.Cohomology.dualComplex F E).cycles n →ₗ[F] (↥(E.homology n) →ₗ[F] F) where
  toFun := sigFun F E n
  map_add' := sigFun_add F E n
  map_smul' := sigFun_smul F E n

@[simp] lemma sigLin_apply (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) :
    sigLin F E n w = sigFun F E n w := rfl

/-! ## Descent to the cohomology of the dual complex -/

/-- A coboundary of the dual complex pairs trivially with every cycle: this is what makes the
descent to the cohomology of the dual complex possible. -/
lemma toCycles_sigLin (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    (Work.Cohomology.dualComplex F E).toCycles ((ComplexShape.up ℕ).prev n) n ≫
      ModuleCat.ofHom (sigLin F E n) = 0 := by
  generalize hpn : (ComplexShape.up ℕ).prev n = pn
  rcases n with _ | m
  · have hpn' : pn = 0 := by rw [← hpn]; simp
    rw [hpn']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpn' : pn = m := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show sigLin F E (m + 1) ((Work.Cohomology.dualComplex F E).toCycles m (m + 1) y) = 0
    apply LinearMap.ext
    intro c
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (E.homologyπ (m + 1))).mp inferInstance c
    rw [sigLin_apply, sigFun_apply F E (m + 1) _ z,
      iCycles_toCycles_apply F (Work.Cohomology.dualComplex F E) m (m + 1) y,
      fdVal_dual_d_apply F E m y ((E.iCycles (m + 1)).hom z),
      iCycles_d_apply F E (m + 1) m z]
    simp

/-- **The evaluation pairing of a chain complex of `F`-vector spaces with its dual**, as a
morphism of `F`-modules: `Hⁿ(Hom_F(E,F)) ⟶ Hom_F(Hₙ(E),F)`, `⟨[w],[z]⟩ = w(z)`. -/
def sigKronHom (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    (Work.Cohomology.dualComplex F E).homology n ⟶
      ModuleCat.of F (↥(E.homology n) →ₗ[F] F) :=
  Cofork.IsColimit.desc
    ((Work.Cohomology.dualComplex F E).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl)
    (ModuleCat.ofHom (sigLin F E n))
    (by simpa using toCycles_sigLin F E n)

/-- The linear map underlying `sigKronHom`. -/
def sigKron (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    (Work.Cohomology.dualComplex F E).homology n →ₗ[F] (↥(E.homology n) →ₗ[F] F) :=
  (sigKronHom F E n).hom

lemma sigKronHom_apply (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) :
    (sigKronHom F E n).hom ((Work.Cohomology.dualComplex F E).homologyπ n w) =
      sigLin F E n w := by
  have h := Cofork.IsColimit.π_desc'
    ((Work.Cohomology.dualComplex F E).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl)
    (ModuleCat.ofHom (sigLin F E n)) (by simpa using toCycles_sigLin F E n)
  have h2 := congrArg (fun (m : (Work.Cohomology.dualComplex F E).cycles n ⟶
      ModuleCat.of F (↥(E.homology n) →ₗ[F] F)) => m.hom w) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    CokernelCofork.π_ofπ] at h2
  show (Cofork.IsColimit.desc
      ((Work.Cohomology.dualComplex F E).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl)
      (ModuleCat.ofHom (sigLin F E n)) (by simpa using toCycles_sigLin F E n)).hom
        ((Work.Cohomology.dualComplex F E).homologyπ n w) = sigLin F E n w
  exact h2

lemma sigKron_apply (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) :
    sigKron F E n ((Work.Cohomology.dualComplex F E).homologyπ n w) = sigLin F E n w := by
  simpa only [sigKron] using sigKronHom_apply F E n w

/-- **The computation rule of the evaluation pairing** on classes of cycles. -/
lemma sigKron_spec (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) (z : E.cycles n) :
    sigKron F E n ((Work.Cohomology.dualComplex F E).homologyπ n w) (E.homologyπ n z)
      = Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w)
          ((E.iCycles n).hom z) := by
  rw [sigKron_apply F E n w, sigLin_apply, sigFun_apply F E n w z]

/-! ## Bijectivity over a field -/

lemma sigKron_bijective (F : Type) [Field F] (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ) :
    Function.Bijective (sigKron F E n) := by
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro a b hab
    have key : ∀ (n : ℕ) (a : ↑((Work.Cohomology.dualComplex F E).homology n)),
        sigKron F E n a = 0 → a = 0 := by
      intro n a ha
      obtain ⟨w, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((Work.Cohomology.dualComplex F E).homologyπ n)).mp
          inferInstance a
      have hval : ∀ z : E.cycles n,
          (Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w))
            ((E.iCycles n).hom z) = 0 := by
        intro z
        rw [← sigKron_spec F E n w z, ha, LinearMap.zero_apply]
      clear ha
      rcases n with _ | m
      · -- degree zero
        have hshape : E.d 0 (0 - 1) = 0 :=
          HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down])
        have hφ : (Work.StemsB.fdVal F E 0 ((Work.Cohomology.dualComplex F E).iCycles 0 w)) = 0 := by
          apply LinearMap.ext
          intro x
          have hx : (E.d 0 (0 - 1)).hom x = 0 := by
            rw [hshape]
            rfl
          obtain ⟨z, hz⟩ := Work.Cohomology.exists_iCycles_eq_of_d_eq_zero F E 0 (0 - 1)
            (Work.Cohomology.down_next 0) x hx
          rw [← hz]
          exact hval z
        have hw0 : w = 0 := by
          apply iCycles_injective F (Work.Cohomology.dualComplex F E) 0
          rw [map_zero]
          exact hφ
        rw [hw0, map_zero]
      · -- positive degree
        have hker : ∀ x : ↥(E.X (m + 1)), (E.d (m + 1) m).hom x = 0 →
            (Work.StemsB.fdVal F E (m + 1) ((Work.Cohomology.dualComplex F E).iCycles (m + 1) w))
              x = 0 := by
          intro x hx
          obtain ⟨z, hz⟩ := Work.Cohomology.exists_iCycles_eq_of_d_eq_zero F E (m + 1) m
            (Work.Cohomology.down_next (m + 1)) x hx
          rw [← hz]
          exact hval z
        obtain ⟨β, hβ⟩ := Work.Cohomology.exists_comp_d_eq_of_eq_zero_on_ker F E m
          (Work.StemsB.fdVal F E (m + 1) ((Work.Cohomology.dualComplex F E).iCycles (m + 1) w))
          hker
        have hw : w = (Work.Cohomology.dualComplex F E).toCycles m (m + 1) β := by
          apply iCycles_injective F (Work.Cohomology.dualComplex F E) (m + 1)
          rw [iCycles_toCycles_apply F (Work.Cohomology.dualComplex F E) m (m + 1) β,
            Work.StemsB.fd_d_apply F E m]
          exact hβ.symm
        rw [hw, homologyπ_toCycles_apply F (Work.Cohomology.dualComplex F E) m (m + 1) β]
    have hsub : a - b = 0 := key n (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp hsub
  · -- surjectivity
    intro g
    obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (E.iCycles n).hom
      (LinearMap.ker_eq_bot.mpr (iCycles_injective F E n))
    have hρz : ∀ z : E.cycles n, ρ ((E.iCycles n).hom z) = z := by
      intro z
      exact LinearMap.congr_fun hρ z
    let gbar : ↥(E.cycles n) →ₗ[F] F := g.comp (E.homologyπ n).hom
    let φ : ↥(E.X n) →ₗ[F] F := gbar.comp ρ
    have hφ : ((Work.Cohomology.dualComplex F E).d n (n + 1)).hom
        (show ↥((Work.Cohomology.dualComplex F E).X n) from φ) = 0 := by
      rw [Work.StemsB.fd_d_apply F E n]
      apply LinearMap.ext
      intro y
      change φ ((E.d (n + 1) n).hom y) = 0
      have h1 : ρ ((E.d (n + 1) n).hom y) = (E.toCycles (n + 1) n) y := by
        have hz := hρz ((E.toCycles (n + 1) n) y)
        rwa [iCycles_toCycles_apply F E (n + 1) n y] at hz
      change gbar (ρ ((E.d (n + 1) n).hom y)) = 0
      rw [h1]
      change g ((E.homologyπ n).hom ((E.toCycles (n + 1) n) y)) = 0
      rw [homologyπ_toCycles_apply F E (n + 1) n y]
      exact map_zero g
    refine ⟨(Work.Cohomology.dualComplex F E).homologyπ n
      (Work.Cohomology.cocycleOfK (Work.Cohomology.dualComplex F E)
        (show ↥((Work.Cohomology.dualComplex F E).X n) from φ) hφ), ?_⟩
    apply LinearMap.ext
    intro c
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (E.homologyπ n)).mp inferInstance c
    rw [sigKron_spec F E n _ z, Work.Cohomology.iCycles_cocycleOfK]
    change gbar (ρ ((E.iCycles n).hom z)) = g ((E.homologyπ n).hom z)
    rw [hρz z]
    rfl

/-! ## Naturality -/

lemma sigKron_natural (F : Type) [Field F] :
    IsNaturalKron F (sigKron F) := by
  intro C D g n a b
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((Work.Cohomology.dualComplex F D).homologyπ n)).mp
      inferInstance a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance b
  have hA : (HomologicalComplex.homologyMap g n) ((C.homologyπ n) z)
      = (D.homologyπ n) ((HomologicalComplex.cyclesMap g n) z) :=
    Work.Cohomology.homologyMap_homologyπ_apply g n z
  have hB : (HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F C D g) n)
        ((Work.Cohomology.dualComplex F D).homologyπ n w)
      = ((Work.Cohomology.dualComplex F C).homologyπ n)
          ((HomologicalComplex.cyclesMap (Work.Cohomology.dualComplexMap F C D g) n) w) :=
    Work.Cohomology.homologyMap_homologyπ_apply (Work.Cohomology.dualComplexMap F C D g) n w
  rw [hA, hB, sigKron_spec F D n w (HomologicalComplex.cyclesMap g n z),
    sigKron_spec F C n (HomologicalComplex.cyclesMap (Work.Cohomology.dualComplexMap F C D g) n w) z,
    cyclesMap_i_apply F g n z,
    cyclesMap_i_apply F (Work.Cohomology.dualComplexMap F C D g) n w]
  change Work.StemsB.fdVal F D n ((Work.Cohomology.dualComplex F D).iCycles n w)
      ((g.f n).hom ((C.iCycles n).hom z))
    = (Work.Cohomology.dualComplexMapComp F C D g n).hom
        ((Work.Cohomology.dualComplex F D).iCycles n w) ((C.iCycles n).hom z)
  exact dualComplexMapComp_fdVal F g n ((Work.Cohomology.dualComplex F D).iCycles n w)
    ((C.iCycles n).hom z)

/-! ## The main theorem -/

/-- **The evaluation pairing of a chain complex with its dual over a field**: for a field `F` and
a chain complex `E` of `F`-vector spaces there is a pairing
`H^n(Hom_F(E,F)) ⟶ Hom_F(H_n(E), F)`, `⟨[w],[z]⟩ = w(z)`, it is bijective, and it is natural in
`E` (`⟨a, g_* b⟩ = ⟨g^* a, b⟩`).

Models to copy: `Work.Cohomology.kronecker_descent`/`kronH` (the descent construction),
`Work.Cohomology.kronH_bijective_field` (bijectivity over a field, whose proof only uses the chain
complex), `Work.Cohomology.kronH_natural` (naturality), and `Work.StemsB.fdVal`. -/
theorem dualEvalPair (F : Type) [Field F] :
    ∃ kron : ∀ (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ),
        (Work.Cohomology.dualComplex F E).homology n →ₗ[F] ((E.homology n) →ₗ[F] F),
      (∀ (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
        (w : (Work.Cohomology.dualComplex F E).cycles n) (z : E.cycles n),
        kron E n ((Work.Cohomology.dualComplex F E).homologyπ n w) (E.homologyπ n z)
          = Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w)
              ((E.iCycles n).hom z)) ∧
      (∀ (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ), Function.Bijective (kron E n)) ∧
      (∀ {C D : ChainComplex (ModuleCat.{0} F) ℕ} (g : C ⟶ D) (n : ℕ)
        (a : (Work.Cohomology.dualComplex F D).homology n) (b : C.homology n),
        kron D n a ((HomologicalComplex.homologyMap g n) b)
          = kron C n ((HomologicalComplex.homologyMap
              (Work.Cohomology.dualComplexMap F C D g) n) a) b) := by
  refine ⟨sigKron F, ?_, ?_, ?_⟩
  · intro E n w z
    exact sigKron_spec F E n w z
  · intro E n
    exact sigKron_bijective F E n
  · exact sigKron_natural F

end

end Work.Pi6.SQM.SIG

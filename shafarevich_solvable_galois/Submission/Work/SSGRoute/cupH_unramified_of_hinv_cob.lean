import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.cupInvariantPerPlace
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
import Submission.Work.SSGRoute.inertiaStructureOfFinPlace_zhat
import Submission.Work.SSGRoute.evCupFun_isCocycle2On
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
import Submission.Work.SSGRoute.HSTwoRow.extFunAux
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.exists_frobenius_complement
import Submission.Work.SSGRoute.PT.isCoboundary2On_of_proCyclic_growth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified clause of the cup pairing, from the coboundary clause of `inv`

The target `Work.SSGRoute.cupH_unramified_of_hinv_cob` derives the "unramified place" clause of the
per-place pairing `Work.SSGRoute.pairOfInvH` from the hypothesis `hinv_cob` that the invariant
functional `inv H` kills the `2`-coboundaries on `H`.

The mathematical content is the vanishing of the second cohomology of a decomposition group at a
finite place `A` which is unramified in `K` and whose residue characteristic is prime to `p`, for
cochains that vanish on the inertia: such a cochain descends to the unramified quotient
`D_A/I_A ≅ Ẑ`, which is a pro-cyclic group growing `p`-adically, where
`Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth` provides a primitive.

The argument is the following.

1. `Work.SSGRoute.exists_frobenius_complement` gives `σ` with `D_A = I_A · C`,
   `I_A ⊓ C = ⊥`, `C = closure (zpowers σ)`; `Work.SSGRoute.HSTwoRow.isProCyclicGrp_zpowersClosure`
   and `Work.SSGRoute.PT.hbig_zpowersClosure` give the pro-cyclicity and the growth hypotheses for
   `C`, the surjections `C ↠ ZMod n` being `Work.SSGRoute.zhat_surjection_of_level`.
2. Writing `c = evCupFun a b`, the cup product of the two `1`-cocycles `a`, `b` is a `2`-cocycle
   (`Work.SSGRoute.evCupFun_isCocycle2On`), locally constant, and vanishes on pairs with an inertia
   coordinate (`Work.SSGRoute.E7Fin.evCupFun_eq_zero_of_inertia`); it is invariant under left
   multiplication by inertia elements in both variables, because `res k K` kills `I_A` (the place is
   unramified in `K`) and `a`, `b` vanish there.  Hence `c g h = c (proj g) (proj h)`.
3. The growth lemma, applied to `Γ = C` with the `C`-coordinate `proj`, produces a locally constant
   `βc` with `c (proj g) (proj h) = act (proj g) • βc (proj h) - βc (proj g · proj h) + βc (proj g)`
   on `C`.
4. `β := fun x => βc (proj x)` (and `0` off `D_A`) is locally constant on `D_A`, since `proj` is
   continuous (`Work.SSGRoute.HSTwoRow.continuous_ip_proj`, via the product homeomorphism
   `D_A ≅ I_A × C`), and satisfies the coboundary identity on `D_A`.  Note that `proj` is a group
   homomorphism (`Work.SSGRoute.HS.proj_mul`).
5. Finally `res k K g = res k K (proj g)`, since `g = ip g · proj g` and `res k K` kills `I_A`.
-/

open scoped TensorProduct Pointwise Topology
open Filter

namespace Work.SSGRoute

noncomputable section

/-- A finite `𝔽_p`-module of `𝔽_p`-dimension `1` has a nonzero element. -/
theorem cupH_exists_ne_zero_of_finrank_eq_one (p : ℕ) [Fact p.Prime] {T : Type}
    [AddCommGroup T] [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) :
    ∃ v : T, v ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hsub : Subsingleton T := ⟨fun a b => by rw [hcon a, hcon b]⟩
  have h0 : Module.finrank (ZMod p) T = 0 := Module.finrank_zero_iff.mpr hsub
  omega

/-- A finite `𝔽_p`-module of `𝔽_p`-dimension `1` is finite. -/
theorem cupH_finite_of_finrank_eq_one (p : ℕ) [Fact p.Prime] {T : Type}
    [AddCommGroup T] [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  obtain ⟨v, hv⟩ := cupH_exists_ne_zero_of_finrank_eq_one p h
  refine Finite.of_surjective (fun c : ZMod p => c • v) ?_
  intro w
  exact (finrank_eq_one_iff_of_nonzero' v hv).mp h w

/-- For a finite module `M` and an `𝔽_p`-line `T`, the tensor product `M ⊗ T` is finite. -/
theorem cupH_finite_tensorProduct_of_finrank_eq_one (p : ℕ) [Fact p.Prime] {M T : Type}
    [AddCommGroup M] [Module (ZMod p) M] [AddCommGroup T] [Module (ZMod p) T] [Finite M]
    (h : Module.finrank (ZMod p) T = 1) : Finite (TensorProduct (ZMod p) M T) := by
  obtain ⟨v, hv⟩ := cupH_exists_ne_zero_of_finrank_eq_one p h
  have hgen : ∀ t : T, ∃ c : ZMod p, c • v = t :=
    fun t => (finrank_eq_one_iff_of_nonzero' v hv).mp h t
  have hsurj : Function.Surjective (fun m : M => TensorProduct.tmul (ZMod p) m v) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m t =>
        obtain ⟨c, hc⟩ := hgen t
        refine ⟨c • m, ?_⟩
        calc (c • m) ⊗ₜ[ZMod p] v = m ⊗ₜ[ZMod p] (c • v) := TensorProduct.smul_tmul _ _ _
          _ = m ⊗ₜ[ZMod p] t := by rw [hc]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        refine ⟨a + b, ?_⟩
        show (a + b) ⊗ₜ[ZMod p] v = x + y
        have ha' : a ⊗ₜ[ZMod p] v = x := ha
        have hb' : b ⊗ₜ[ZMod p] v = y := hb
        rw [TensorProduct.add_tmul, ha', hb']
  exact Finite.of_surjective _ hsurj

/-- The `𝔽_p`-dual of an `𝔽_p`-line is finite. -/
theorem cupH_finite_dualMod_of_finrank_eq_one (p : ℕ) [Fact p.Prime] {T : Type}
    [AddCommGroup T] [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) :
    Finite (Work.SSGRoute.DualMod p T) := by
  haveI : Finite T := cupH_finite_of_finrank_eq_one p h
  haveI : Finite (T → ZMod p) := inferInstance
  exact Finite.of_injective
    (fun f : Work.SSGRoute.DualMod p T => (f : T → ZMod p))
    (fun a b hh => LinearMap.ext (congrFun hh))

end

theorem cupH_unramified_of_hinv_cob (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p)
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) :
    Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0 := by
  classical
  haveI hgal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- ## 0. Notation
  -- the coefficient module
  have hfinT : Finite T := cupH_finite_of_finrank_eq_one p hT.1
  haveI : Finite T := hfinT
  have hfinN : Finite (Work.SSGRoute.DualMod p T) := cupH_finite_dualMod_of_finrank_eq_one p hT.1
  haveI : Finite (Work.SSGRoute.DualMod p T) := hfinN
  -- ## 1. The Frobenius complement and the procyclic hypotheses
  obtain ⟨σ, hσD, hsup, hinf⟩ := Work.SSGRoute.exists_frobenius_complement k Ω A hA
  have hCD : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A :=
    Work.SSGRoute.HS.CC_le_DD A σ hσD
  haveI : CompactSpace ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact
  have hZ : ∀ n : ℕ, 0 < n →
      ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →* Multiplicative (ZMod n),
        Function.Surjective f :=
    fun n hn => Work.SSGRoute.zhat_surjection_of_level p k Ω A hA σ hσD hsup n hn
  have hcyc : Work.SSGRoute.IsProCyclicGrp
      ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
    Work.SSGRoute.HSTwoRow.isProCyclicGrp_zpowersClosure k Ω σ
  have hgrowth : ∀ U : Subgroup ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
      IsOpen (U : Set ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) → U.Normal →
      ∃ V : Subgroup ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)), V ≤ U ∧
        IsOpen (V : Set ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) ∧ V.Normal ∧
        p ∣ (V.subgroupOf U).index :=
    Work.SSGRoute.PT.hbig_zpowersClosure k Ω p σ hZ
  -- the `C`-coordinate `D_A →* C ≅ D_A/I_A`
  let prj : ↥(SSGRoute.decomp k A) →* ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
    Work.SSGRoute.HSTwoRow.DprojHom A (Work.SSGRoute.inertiaSub k Ω A) σ
      (Work.SSGRoute.inertiaSub_le_decomp k Ω A) (Work.SSGRoute.inertiaSub_normal k Ω A) hσD
      hsup hinf
  -- ## 2. `res k K` kills the inertia (the place is unramified in `K`)
  have hres_inertia : ∀ u : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A u → SSGRoute.res k K u = 1 := by
    intro u hu
    have hfix : u ∈ K.fixingSubgroup := by
      by_contra h
      exact hramA ⟨u, hu, h⟩
    have hker : u ∈ (SSGRoute.res k K).ker := by
      rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
        IntermediateField.restrictNormalHom_ker]
      exact hfix
    exact MonoidHom.mem_ker.mp hker
  -- ## 3. The `2`-cocycle `c = evCupFun a b` and its invariance under the inertia
  have hc2On : Work.SSGRoute.IsCocycle2On p k Ω K (Work.SSGRoute.DualMod p T)
      (SSGRoute.decomp k A) (fun g h => Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h) :=
    evCupFun_isCocycle2On p k Ω K T M (SSGRoute.decomp k A) a b ha.1 hb.1
  -- left multiplication by an inertia element in the first variable
  have hbiL : ∀ (x y i : Ω ≃ₐ[k] Ω), x ∈ SSGRoute.decomp k A → y ∈ SSGRoute.decomp k A →
      SSGRoute.IsInertia k A i →
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b (i * x) y =
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b x y := by
    intro x y i hx hy hi
    have hai : a (i * x) = a x := by
      rw [ha.1 i hi.1 x hx, (hiner i hi).1, hres_inertia i hi, one_smul, zero_add]
    have hbi : SSGRoute.res k K (i * x) • b y = SSGRoute.res k K x • b y := by
      rw [map_mul, hres_inertia i hi, one_mul]
    show Work.SSGRoute.E7Fin.evLin p M T
        (TensorProduct.tmul (ZMod p) (a (i * x)) (SSGRoute.res k K (i * x) • b y)) =
      Work.SSGRoute.E7Fin.evLin p M T
        (TensorProduct.tmul (ZMod p) (a x) (SSGRoute.res k K x • b y))
    rw [hai, hbi]
  -- left multiplication by an inertia element in the second variable
  have hbiR : ∀ (x y j : Ω ≃ₐ[k] Ω), x ∈ SSGRoute.decomp k A → y ∈ SSGRoute.decomp k A →
      SSGRoute.IsInertia k A j →
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b x (j * y) =
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b x y := by
    intro x y j hx hy hj
    have hbj : b (j * y) = b y := by
      rw [hb.1 j hj.1 y hy, (hiner j hj).2, hres_inertia j hj, one_smul, zero_add]
    show Work.SSGRoute.E7Fin.evLin p M T
        (TensorProduct.tmul (ZMod p) (a x) (SSGRoute.res k K x • b (j * y))) =
      Work.SSGRoute.E7Fin.evLin p M T
        (TensorProduct.tmul (ZMod p) (a x) (SSGRoute.res k K x • b y))
    rw [hbj]
  -- `c` depends only on the `C`-coordinates
  have hcomp : ∀ g h : ↥(SSGRoute.decomp k A),
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
          ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)
          ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) := by
    intro g h
    have hgf : (g : Ω ≃ₐ[k] Ω) =
        (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup g) : Ω ≃ₐ[k] Ω) *
        ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) :=
      (Work.SSGRoute.HS.ip_mul_proj A (Work.SSGRoute.inertiaSub k Ω A) σ
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
        (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup g).symm
    have hhf : (h : Ω ≃ₐ[k] Ω) =
        (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h) : Ω ≃ₐ[k] Ω) *
        ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) :=
      (Work.SSGRoute.HS.ip_mul_proj A (Work.SSGRoute.inertiaSub k Ω A) σ
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
        (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h).symm
    have higI : SSGRoute.IsInertia k A
        (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup g) : Ω ≃ₐ[k] Ω) :=
      (Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
        (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup g).2
    have hihI : SSGRoute.IsInertia k A
        (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h) : Ω ≃ₐ[k] Ω) :=
      (Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
        (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h).2
    have hpgD : ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) :
        Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := hCD (prj g).2
    have hphD : ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) :
        Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := hCD (prj h).2
    have hmixD : (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h) : Ω ≃ₐ[k] Ω) *
        ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) ∈
          SSGRoute.decomp k A :=
      (SSGRoute.decomp k A).mul_mem
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A
          (Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
            (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
            (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h).2) hphD
    rw [hgf, hhf]
    have h1 : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
          ((↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
            (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
            (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup g) : Ω ≃ₐ[k] Ω) *
            ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω))
          ((↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
            (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
            (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h) : Ω ≃ₐ[k] Ω) *
            ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)) =
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
          ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)
          ((↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
            (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
            (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h) : Ω ≃ₐ[k] Ω) *
            ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)) :=
      hbiL _ _ _ hpgD hmixD higI
    have h2 : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
          ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)
          ((↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
            (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
            (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup h) : Ω ≃ₐ[k] Ω) *
            ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)) =
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
          ((prj g : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)
          ((prj h : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) :=
      hbiR _ _ _ hpgD hphD hihI
    rw [h1, h2]

  -- ## 4. The growth lemma on `C`
  have hcC : SSGRoute.IsCocycle2
      ((SSGRoute.res k K).comp (Subgroup.subtype (Subgroup.topologicalClosure
        (Subgroup.zpowers σ))))
      (fun x y : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) =>
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b (x : Ω ≃ₐ[k] Ω) (y : Ω ≃ₐ[k] Ω)) := by
    intro x y z
    have h1 := hc2On (x : Ω ≃ₐ[k] Ω) (hCD x.2) (y : Ω ≃ₐ[k] Ω) (hCD y.2)
      (z : Ω ≃ₐ[k] Ω) (hCD z.2)
    simpa only [Subgroup.coe_mul, MonoidHom.comp_apply, Subgroup.coe_subtype] using h1
  have hlcC : SSGRoute.IsLocConst2
      (fun x y : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) =>
        Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b (x : Ω ≃ₐ[k] Ω) (y : Ω ≃ₐ[k] Ω)) := by
    obtain ⟨Ua, hUaopen, hUainv⟩ := ha.2
    obtain ⟨Ub, hUbopen, hUbinv⟩ := hb.2
    refine ⟨Subgroup.comap (Subgroup.subtype (Subgroup.topologicalClosure
        (Subgroup.zpowers σ))) (Ua ⊓ Ub ⊓ K.fixingSubgroup), ?_, ?_⟩
    · exact ((hUaopen.inter hUbopen).inter
        (K.fixingSubgroup_isOpen)).preimage continuous_subtype_val
    · intro g h u v hu hv
      have hug : (u : Ω ≃ₐ[k] Ω) ∈ Ua ⊓ Ub ⊓ K.fixingSubgroup := hu
      have hvg : (v : Ω ≃ₐ[k] Ω) ∈ Ua ⊓ Ub ⊓ K.fixingSubgroup := hv
      have hua : (u : Ω ≃ₐ[k] Ω) ∈ Ua := hug.1.1
      have hub : (u : Ω ≃ₐ[k] Ω) ∈ Ub := hug.1.2
      have hva : (v : Ω ≃ₐ[k] Ω) ∈ Ua := hvg.1.1
      have hvb : (v : Ω ≃ₐ[k] Ω) ∈ Ub := hvg.1.2
      have huk : (u : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := hug.2
      have hvk : (v : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := hvg.2
      have hukres : SSGRoute.res k K (u : Ω ≃ₐ[k] Ω) = 1 := by
        have : (u : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
          rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
            IntermediateField.restrictNormalHom_ker]
          exact huk
        exact MonoidHom.mem_ker.mp this
      have hvhres : SSGRoute.res k K (v : Ω ≃ₐ[k] Ω) = 1 := by
        have : (v : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
          rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
            IntermediateField.restrictNormalHom_ker]
          exact hvk
        exact MonoidHom.mem_ker.mp this
      have ha' : a ((g : Ω ≃ₐ[k] Ω) * (u : Ω ≃ₐ[k] Ω)) = a (g : Ω ≃ₐ[k] Ω) :=
        hUainv (g : Ω ≃ₐ[k] Ω) (hCD g.2) (u : Ω ≃ₐ[k] Ω) hua (hCD u.2)
      have hb' : b ((h : Ω ≃ₐ[k] Ω) * (v : Ω ≃ₐ[k] Ω)) = b (h : Ω ≃ₐ[k] Ω) :=
        hUbinv (h : Ω ≃ₐ[k] Ω) (hCD h.2) (v : Ω ≃ₐ[k] Ω) hvb (hCD v.2)
      have hres' : SSGRoute.res k K ((g : Ω ≃ₐ[k] Ω) * (u : Ω ≃ₐ[k] Ω)) •
          b ((h : Ω ≃ₐ[k] Ω) * (v : Ω ≃ₐ[k] Ω)) =
          SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • b (h : Ω ≃ₐ[k] Ω) := by
        rw [hb', map_mul, hukres, mul_one]
      show Work.SSGRoute.E7Fin.evLin p M T
          (TensorProduct.tmul (ZMod p) (a ((g : Ω ≃ₐ[k] Ω) * (u : Ω ≃ₐ[k] Ω)))
            (SSGRoute.res k K ((g : Ω ≃ₐ[k] Ω) * (u : Ω ≃ₐ[k] Ω)) •
              b ((h : Ω ≃ₐ[k] Ω) * (v : Ω ≃ₐ[k] Ω)))) =
        Work.SSGRoute.E7Fin.evLin p M T
          (TensorProduct.tmul (ZMod p) (a (g : Ω ≃ₐ[k] Ω))
            (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • b (h : Ω ≃ₐ[k] Ω)))
      rw [ha', hres']
  have hker : ∃ U₀ : Subgroup ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
      IsOpen (U₀ : Set ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) ∧
      ∀ g ∈ U₀, ∀ n : Work.SSGRoute.DualMod p T,
        ((SSGRoute.res k K).comp (Subgroup.subtype (Subgroup.topologicalClosure
          (Subgroup.zpowers σ)))) g • n = n := by
    refine ⟨Subgroup.comap (Subgroup.subtype (Subgroup.topologicalClosure
      (Subgroup.zpowers σ))) K.fixingSubgroup, ?_, ?_⟩
    · exact K.fixingSubgroup_isOpen.preimage continuous_subtype_val
    · intro g hg n
      have hg1 : SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) = 1 := by
        have : (g : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
          rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
            IntermediateField.restrictNormalHom_ker]
          exact hg
        exact MonoidHom.mem_ker.mp this
      show SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • n = n
      rw [hg1, one_smul]
  obtain ⟨βc, hβcloc, hβceq⟩ := Work.SSGRoute.PT.isCoboundary2On_of_proCyclic_growth (p := p)
    (Γ := ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) (G := K ≃ₐ[k] K)
    (N := Work.SSGRoute.DualMod p T)
    ((SSGRoute.res k K).comp (Subgroup.subtype (Subgroup.topologicalClosure
      (Subgroup.zpowers σ)))) hker hcyc hgrowth
    (fun x y : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) =>
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b (x : Ω ≃ₐ[k] Ω) (y : Ω ≃ₐ[k] Ω)) hcC hlcC
  -- ## 5. Lifting `βc` to `D_A` along `proj`
  have hcontprj : Continuous (fun d : ↥(SSGRoute.decomp k A) => prj d) := by
    have hmain := (Work.SSGRoute.HSTwoRow.continuous_ip_proj k Ω A
      (Work.SSGRoute.inertiaSub k Ω A) σ (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
      (Work.SSGRoute.inertiaSub_isClosed_zhat k Ω A)
      (Work.SSGRoute.inertiaSub_normal k Ω A) hσD hsup hinf).1
    refine Continuous.subtype_mk ?_ (fun d => (prj d).2)
    dsimp only [prj, Work.SSGRoute.HSTwoRow.DprojHom]
    exact hmain
  let β : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
    fun x => if hx : x ∈ SSGRoute.decomp k A then βc (prj ⟨x, hx⟩) else 0
  have hβloc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) β := by
    obtain ⟨V, hVopen, hVinv⟩ := hβcloc
    have hpre : IsOpen (prj ⁻¹' (V : Set ↥(Subgroup.topologicalClosure
        (Subgroup.zpowers σ)))) := hVopen.preimage hcontprj
    obtain ⟨U', hU'open, hU'eq⟩ := (isOpen_induced_iff
      (f := (Subtype.val : ↥(SSGRoute.decomp k A) → Ω ≃ₐ[k] Ω))).mp hpre
    have h1U' : (1 : Ω ≃ₐ[k] Ω) ∈ U' := by
      have h1 : (1 : ↥(SSGRoute.decomp k A)) ∈ (Subtype.val :
          ↥(SSGRoute.decomp k A) → Ω ≃ₐ[k] Ω) ⁻¹' U' := by
        rw [hU'eq]
        show prj 1 ∈ V
        rw [map_one]
        exact V.one_mem
      exact h1
    have hmem : U' ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) := hU'open.mem_nhds h1U'
    rw [krullTopology_mem_nhds_one_iff_of_normal k Ω] at hmem
    obtain ⟨E, hEfin, hEnorm, hEsub⟩ := hmem
    haveI := hEfin
    refine ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, ?_⟩
    intro g hg u hu huH
    have huD : u ∈ SSGRoute.decomp k A := huH
    have huU' : u ∈ U' := hEsub hu
    have hguD : g * u ∈ SSGRoute.decomp k A := (SSGRoute.decomp k A).mul_mem hg huH
    show β (g * u) = β g
    rw [show β (g * u) = βc (prj ⟨g * u, hguD⟩) from dif_pos hguD,
      show β g = βc (prj ⟨g, hg⟩) from dif_pos hg]
    have hprju : prj ⟨u, huH⟩ ∈ V := by
      have hmem' : (⟨u, huH⟩ : ↥(SSGRoute.decomp k A)) ∈ prj ⁻¹' (V : Set ↥(Subgroup.topologicalClosure
          (Subgroup.zpowers σ))) := by
        rw [← hU'eq]
        exact huU'
      exact hmem'
    have hmul : prj ⟨g * u, hguD⟩ = prj ⟨g, hg⟩ * prj ⟨u, huH⟩ := by
      have h1 := map_mul prj ⟨g, hg⟩ ⟨u, huH⟩
      have h2 : (⟨g, hg⟩ * ⟨u, huH⟩ : ↥(SSGRoute.decomp k A)) = ⟨g * u, hguD⟩ :=
        Subtype.ext rfl
      rw [h2] at h1
      exact h1
    rw [hmul]
    exact hVinv (prj ⟨g, hg⟩) (Subgroup.mem_top _) (prj ⟨u, huH⟩) hprju (Subgroup.mem_top _)
  -- ## 6. The coboundary identity on `D_A`
  have hβeq : ∀ g ∈ SSGRoute.decomp k A, ∀ h ∈ SSGRoute.decomp k A,
      Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h =
        SSGRoute.res k K g • β h - β (g * h) + β g := by
    intro g hg h hh
    have hgh : g * h ∈ SSGRoute.decomp k A := (SSGRoute.decomp k A).mul_mem hg hh
    have hprojD : ∀ x : ↥(SSGRoute.decomp k A),
        ((prj x : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) ∈
          SSGRoute.decomp k A := fun x => hCD (prj x).2
    have hipg : ((↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A) (Work.SSGRoute.inertiaSub_normal k Ω A) hCD
        hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω)) ∈ SSGRoute.decomp k A :=
      Work.SSGRoute.inertiaSub_le_decomp k Ω A
        (Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩).2
    have hipgI : SSGRoute.IsInertia k A
        (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω) :=
      (Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
        (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩).2
    have hresg : SSGRoute.res k K ((prj ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure
        (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) = SSGRoute.res k K g := by
      have hfac : (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω) *
          ((prj ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) :
            Ω ≃ₐ[k] Ω) = g :=
        Work.SSGRoute.HS.ip_mul_proj A (Work.SSGRoute.inertiaSub k Ω A) σ
          (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
          (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩
      have hkey : ((prj ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) :
          Ω ≃ₐ[k] Ω) =
          (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
            (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
            (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω)⁻¹ * g := by
        calc ((prj ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)
            = (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
                (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
                (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω)⁻¹ *
                ((↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
                  (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
                  (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω) *
                  ((prj ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) :
                    Ω ≃ₐ[k] Ω)) := by group
          _ = (↑(Work.SSGRoute.HS.ip A (Work.SSGRoute.inertiaSub k Ω A) σ
                (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
                (Work.SSGRoute.inertiaSub_normal k Ω A) hCD hsup ⟨g, hg⟩) : Ω ≃ₐ[k] Ω)⁻¹ * g := by
              rw [hfac]
      rw [hkey, map_mul, map_inv, hres_inertia _ hipgI, inv_one, one_mul]
    have hprojmul : prj ⟨g * h, hgh⟩ = prj ⟨g, hg⟩ * prj ⟨h, hh⟩ := by
      have h1 := map_mul prj ⟨g, hg⟩ ⟨h, hh⟩
      have h2 : (⟨g, hg⟩ * ⟨h, hh⟩ : ↥(SSGRoute.decomp k A)) = ⟨g * h, hgh⟩ :=
        Subtype.ext rfl
      rw [h2] at h1
      exact h1
    have hstep : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h =
        SSGRoute.res k K g • βc (prj ⟨h, hh⟩) -
          βc (prj ⟨g, hg⟩ * prj ⟨h, hh⟩) + βc (prj ⟨g, hg⟩) := by
      have h3 := hβceq (prj ⟨g, hg⟩) (Subgroup.mem_top _) (prj ⟨h, hh⟩) (Subgroup.mem_top _)
      have h4 : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b
            ((prj ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)
            ((prj ⟨h, hh⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) =
          SSGRoute.res k K g • βc (prj ⟨h, hh⟩) -
            βc (prj ⟨g, hg⟩ * prj ⟨h, hh⟩) + βc (prj ⟨g, hg⟩) := by
        simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, hresg] using h3
      rw [hcomp ⟨g, hg⟩ ⟨h, hh⟩, h4]
    rw [show β h = βc (prj ⟨h, hh⟩) from dif_pos hh,
      show β (g * h) = βc (prj ⟨g * h, hgh⟩) from dif_pos hgh,
      show β g = βc (prj ⟨g, hg⟩) from dif_pos hg]
    rw [hstep, hprojmul]

  -- ## 7. Conclusion
  have hcob : SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
      (fun g h => Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b g h) :=
    ⟨β, hβloc, hβeq⟩
  rw [Work.SSGRoute.pairOfInvH_eq p k Ω K T inv M (SSGRoute.decomp k A) a b,
    Work.SSGRoute.E7Fin.pairOfInv_of_cocycle p k Ω K T (inv (SSGRoute.decomp k A)) M
      (SSGRoute.decomp k A) a b ⟨ha.1, hb.1⟩]
  exact hinv_cob (SSGRoute.decomp k A) _ hcob

end Work.SSGRoute

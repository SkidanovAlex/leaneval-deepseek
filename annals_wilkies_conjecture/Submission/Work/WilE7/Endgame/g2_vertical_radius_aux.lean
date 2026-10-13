import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical
import Submission.Work.WilE7.DimAPI.coordProj_fderiv_ker_eventually
import Submission.Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt
import Submission.Work.WilE7.Endgame.g2_injOn_of_kjac_inj
import Submission.Work.WilE7.Endgame.eq_zero_of_mem_ker_jac_of_projTop_eq_zero
import Submission.Work.WilE7.DimAPI.image_mem_nhds_of_hasStrictFDerivAt_bijective
import Submission.Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.Endgame.g2_ker_basePrLin_eq
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E

/-! ## The auxiliary map `θ = (eqMap T, e ∘ basePrLin, verT)`

`g2_vertical_radius` is proved by regarding the stratum `T` near `z` as the graph of the map
`θ = (eqMap T, e ∘ basePrLin, verT)`: the first block `eqMap T` is the defining-equation map of
`T` (so `T.X.set` is locally its zero set, `Good`), and the second block is the "restricted
vertical coordinate" `(e ∘ π_n, vert)`.

At every point `w ∈ T.X.set` where the rank hypotheses of `hvert`/`hpers` hold, the differential
of `θ` is injective (`thetaDeriv_injective`): a tangent vector killed by `e ∘ π_n` is killed by
`π_n` (kernel equality `g2_ker_basePrLin_eq`, from `hvert` + `hpers`), and then `verT = 0` forces
the vector to vanish by `HImm`.  Hence `θ` is a local diffeomorphism at every such point;
around `z` it is even a homeomorphism onto a ball, and on the `(e ∘ π_n)`-fibres of that ball
`π_n` is locally constant (`alpha_fiber_local_const`, the local-analytic "critical level set"
lemma `criticalLevelSetLocallyConstAt` applied to `(eqMap T, e ∘ π_n - c)`).

Since the ball is convex, the fibre of `e ∘ π_n` inside it is a single interval of vertical
values; a locally constant function on an interval is constant, so `π_n` is constant on the
whole fibre.  That is precisely the claim: two points of `T.X.set` near `z` whose
`e`-coordinates of `π_n` agree and whose vertical coordinates are close have the same `π_n`. -/

/-- The map `θ = (eqMap T, e ∘ basePrLin, verT)`, in the coordinates of an absolute stratum. -/
def thetaMap {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) :
    (Fin (0 + (n + (m + 1))) → ℝ) →
      ((Fin T.j → ℝ) × (Fin (n + (m + 1) - T.j - 1) → ℝ) × ℝ) :=
  fun w => (Work.WilE7.DimAPI.eqMap T w,
    (fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) w (e i)),
    Work.WilE7.CoreStep.verT w)

/-- The differential of `thetaMap T e` at `w`. -/
def thetaDeriv {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ]
      ((Fin T.j → ℝ) × (Fin (n + (m + 1) - T.j - 1) → ℝ) × ℝ) :=
  (Work.WilE7.MainDesign.jac T w).toContinuousLinearMap.prod
    (((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
      (Work.WilE7.MainDesign.basePrLin n (m + 1))).toContinuousLinearMap.prod
      (ContinuousLinearMap.proj (Fin.natAdd 0 (Fin.natAdd n (Fin.last m)))))

@[simp] lemma thetaMap_fst {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    (thetaMap T e w).1 = Work.WilE7.DimAPI.eqMap T w := rfl

@[simp] lemma thetaMap_snd_fst {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    (thetaMap T e w).2.1
      = fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) w (e i) := rfl

@[simp] lemma thetaMap_snd_snd {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    (thetaMap T e w).2.2 = Work.WilE7.CoreStep.verT w := rfl

@[simp] lemma thetaDeriv_fst {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w ξ : Fin (0 + (n + (m + 1))) → ℝ) :
    (thetaDeriv T e w ξ).1 = Work.WilE7.MainDesign.jac T w ξ := rfl

@[simp] lemma thetaDeriv_snd_fst {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w ξ : Fin (0 + (n + (m + 1))) → ℝ) :
    (thetaDeriv T e w ξ).2.1
      = fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) ξ (e i) := rfl

@[simp] lemma thetaDeriv_snd_snd {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w ξ : Fin (0 + (n + (m + 1))) → ℝ) :
    (thetaDeriv T e w ξ).2.2 = Work.WilE7.CoreStep.verT ξ := rfl

/-- `θ` is analytic (its components are: the defining equations, which are EA functions, and two
linear maps). -/
lemma theta_analyticAt {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    AnalyticAt ℝ (thetaMap T e) w := by
  have hG : AnalyticAt ℝ (Work.WilE7.DimAPI.eqMap T) w := Work.WilE7.DimAPI.analyticAt_eqMap T w
  have hα : AnalyticAt ℝ (fun y : Fin (0 + (n + (m + 1))) → ℝ =>
      fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i)) w :=
    (((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
      (Work.WilE7.MainDesign.basePrLin n (m + 1))).toContinuousLinearMap).analyticAt w
  have hv : AnalyticAt ℝ (Work.WilE7.CoreStep.verT) w := by
    have h : AnalyticAt ℝ (fun z : Fin (0 + (n + (m + 1))) → ℝ =>
        z (Fin.natAdd 0 (Fin.natAdd n (Fin.last m)))) w :=
      (ContinuousLinearMap.proj (Fin.natAdd 0 (Fin.natAdd n (Fin.last m))) :
        (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] ℝ).analyticAt w
    exact h
  exact hG.prod (hα.prod hv)

/-- `θ` is strictly differentiable at every point, with differential `thetaDeriv T e w`. -/
lemma theta_hasStrictFDerivAt {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n) (w : Fin (0 + (n + (m + 1))) → ℝ) :
    HasStrictFDerivAt (thetaMap T e) (thetaDeriv T e w) w := by
  have hG : HasStrictFDerivAt (Work.WilE7.DimAPI.eqMap T)
      ((Work.WilE7.MainDesign.jac T w).toContinuousLinearMap) w := by
    have h := (Work.WilE7.DimAPI.analyticAt_eqMap T w).hasStrictFDerivAt
    have hf : fderiv ℝ (Work.WilE7.DimAPI.eqMap T) w
        = (Work.WilE7.MainDesign.jac T w).toContinuousLinearMap := by
      rw [Work.WilE7.DimAPI.jac_eq_fderiv T w]
      rfl
    rwa [hf] at h
  have hcl : HasStrictFDerivAt
      (fun y : Fin (0 + (n + (m + 1))) → ℝ =>
        fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i))
      ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
        (Work.WilE7.MainDesign.basePrLin n (m + 1))).toContinuousLinearMap w :=
    ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
      (Work.WilE7.MainDesign.basePrLin n (m + 1))).toContinuousLinearMap.hasStrictFDerivAt
  have hv : HasStrictFDerivAt (Work.WilE7.CoreStep.verT)
      (ContinuousLinearMap.proj (Fin.natAdd 0 (Fin.natAdd n (Fin.last m))) :
        (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] ℝ) w := by
    have h : HasStrictFDerivAt (fun z : Fin (0 + (n + (m + 1))) → ℝ =>
        z (Fin.natAdd 0 (Fin.natAdd n (Fin.last m))))
      (ContinuousLinearMap.proj (Fin.natAdd 0 (Fin.natAdd n (Fin.last m))) :
        (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] ℝ) w :=
      (ContinuousLinearMap.proj (Fin.natAdd 0 (Fin.natAdd n (Fin.last m))) :
        (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] ℝ).hasStrictFDerivAt (x := w)
    exact h
  exact hG.prodMk (hcl.prodMk hv)

/-! ## Injectivity of the differential of `θ` -/

/-- **Step B.**  If the kernel equality of Step A holds at `w ∈ T.X.set`, then the differential of
`θ` at `w` is injective: a tangent vector of `T` at `w` whose `(e ∘ π_n)`-coordinates of `π_n`
and whose vertical coordinate both vanish is zero. -/
lemma thetaDeriv_injective {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (himm : Work.WilE7.CoreLTSuccPlan.HImm T)
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n)
    (w : Fin (0 + (n + (m + 1))) → ℝ) (hw : w ∈ T.X.set)
    (hker : LinearMap.ker (Work.WilE7.MainDesign.jac T w) ⊓
        (Work.WilE7.MainDesign.basePrLin n (m + 1)).ker
      = LinearMap.ker (Work.WilE7.MainDesign.jac T w) ⊓
        ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
          (Work.WilE7.MainDesign.basePrLin n (m + 1))).ker) :
    Function.Injective (thetaDeriv T e w) := by
  intro ξ η hξη
  have h0 : thetaDeriv T e w (ξ - η) = 0 := by rw [map_sub, hξη, sub_self]
  have h1 : Work.WilE7.MainDesign.jac T w (ξ - η) = 0 := by
    have h := congrArg Prod.fst h0
    simpa only [thetaDeriv_fst, Prod.fst_zero] using h
  have h2 : (fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) (ξ - η) (e i)) = 0 := by
    have h := congrArg (fun z => z.2.1) h0
    simpa only [thetaDeriv_snd_fst, Prod.snd_zero, Prod.fst_zero] using h
  have h3 : Work.WilE7.CoreStep.verT (ξ - η) = 0 := by
    have h := congrArg (fun z => z.2.2) h0
    simpa only [thetaDeriv_snd_snd, Prod.snd_zero] using h
  have hb : Work.WilE7.MainDesign.basePrLin n (m + 1) (ξ - η) = 0 := by
    have hmem : (ξ - η) ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T w) ⊓
        ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
          (Work.WilE7.MainDesign.basePrLin n (m + 1))).ker := by
      refine ⟨LinearMap.mem_ker.mpr h1, LinearMap.mem_ker.mpr ?_⟩
      change (Work.WilE7.DimAPI.coordProjCLM e)
        ((Work.WilE7.MainDesign.basePrLin n (m + 1)) (ξ - η)) = 0
      rw [Work.WilE7.DimAPI.coordProjCLM_apply]
      exact h2
    rw [← hker] at hmem
    exact hmem.2
  have hinit : Fin.init (Work.WilE7.CoreStep.projTopLin n m
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) (ξ - η))) = 0 := by
    rw [Work.WilE7.CoreStep.projTopLin_absPtLin_init]
    exact hb
  have hlast : Work.WilE7.CoreStep.projTopLin n m
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) (ξ - η)) (Fin.last n) = 0 := by
    rw [Work.WilE7.CoreStep.projTopLin_absPtLin_last]
    exact h3
  have htop : Work.WilE7.CoreStep.projTopLin n m
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) (ξ - η)) = 0 := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · exact hlast
    · intro j
      have h := congrFun hinit j
      simpa [Fin.init] using h
  have hzero : ξ - η = 0 :=
    Work.WilE7.Endgame.eq_zero_of_mem_ker_jac_of_projTop_eq_zero T hT himm hw
      (LinearMap.mem_ker.mpr h1) htop
  exact sub_eq_zero.mp hzero

/-- The differential of `θ` at a point of the stratum is bijective (injective by the kernel
equality, and the dimensions agree). -/
lemma thetaDeriv_bijective {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (himm : Work.WilE7.CoreLTSuccPlan.HImm T)
    (hvert : ∀ w ∈ T.X.set, Work.WilE7.MainDesign.projRank T w + 1 = n + (m + 1) - T.j)
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n)
    (w : Fin (0 + (n + (m + 1))) → ℝ) (hw : w ∈ T.X.set)
    (hpersw : (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).map
      ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
        (Work.WilE7.MainDesign.basePrLin n (m + 1))) = ⊤) :
    Function.Bijective (thetaDeriv T e w) := by
  have hinj : Function.Injective (thetaDeriv T e w) :=
    thetaDeriv_injective T hT himm e w hw (g2_ker_basePrLin_eq T hT hvert e w hw hpersw)
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank ℝ (Fin (0 + (n + (m + 1))) → ℝ)
      = Module.finrank ℝ ((Fin T.j → ℝ) × (Fin (n + (m + 1) - T.j - 1) → ℝ) × ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun, Module.finrank_self]
    have h1 : 1 ≤ n + (m + 1) - T.j := by
      have h := hvert w hw
      simp only [Work.WilE7.MainDesign.projRank] at h
      omega
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

/-! ## The local constancy of `π_n` along `(e ∘ π_n)`-fibres -/

/-- Packing lemma: the composite `appendCLM ∘ (J × A)` is the appended pair. -/
lemma appendCLM_comp_prod_apply {N j k : ℕ} (J : (Fin N → ℝ) →L[ℝ] (Fin j → ℝ))
    (A : (Fin N → ℝ) →L[ℝ] (Fin k → ℝ)) (v : Fin N → ℝ) :
    ((Work.WilE9.Ift.appendCLM j k).comp (J.prod A)) v = Fin.append (J v) (A v) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Work.WilE9.Ift.appendCLM_apply]

/-- **Step C.**  Along the fibres of
`e ∘ π_n` inside `T.X.set`, the base projection `π_n` is locally constant near `w`.

This is the local-analytic "critical level set" lemma
`Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt` applied to the submersion
`g = (eqMap T, e ∘ π_n - cw)`: its differential is `(jac, e ∘ basePrLin)`, surjective at `w`
(`Good` and `hpersw`), and vanishes on `ker (jac T y) ⊓ ker (e ∘ basePrLin) = ker (jac T y) ⊓
ker (basePrLin)` (`hker`), where `π_n` has zero derivative. -/
lemma alpha_fiber_local_const {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n)
    (w : Fin (0 + (n + (m + 1))) → ℝ) (hw : w ∈ T.X.set)
    (hpersw : (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).map
      ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
        (Work.WilE7.MainDesign.basePrLin n (m + 1))) = ⊤)
    (hker : ∀ᶠ y in nhds w, y ∈ T.X.set →
      LinearMap.ker (Work.WilE7.MainDesign.jac T y) ⊓
          (Work.WilE7.MainDesign.basePrLin n (m + 1)).ker
        = LinearMap.ker (Work.WilE7.MainDesign.jac T y) ⊓
          ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
            (Work.WilE7.MainDesign.basePrLin n (m + 1))).ker) :
    ∀ᶠ y in nhds w, Work.WilE7.DimAPI.eqMap T y = 0 →
      (∀ i, Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i)
        = Work.WilE7.MainDesign.basePrLin n (m + 1) w (e i)) →
      Work.WilE7.MainDesign.basePrLin n (m + 1) y
        = Work.WilE7.MainDesign.basePrLin n (m + 1) w := by
  classical
  -- the composed coordinate projection `e ∘ π_n`
  set Ae : (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin (n + (m + 1) - T.j - 1) → ℝ) :=
    (Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
      (Work.WilE7.MainDesign.basePrLin n (m + 1)) with hAedef
  have hAeapply : ∀ v : Fin (0 + (n + (m + 1))) → ℝ,
      Ae v = fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) v (e i) := by
    intro v
    rw [hAedef, LinearMap.comp_apply]
    exact Work.WilE7.DimAPI.coordProjCLM_apply e _
  -- the value of `e ∘ π_n` at `w`
  set cw : Fin (n + (m + 1) - T.j - 1) → ℝ :=
    fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) w (e i) with hcwdef
  -- the submersion whose level sets are the `(e ∘ π_n)`-fibres
  set g : (Fin (0 + (n + (m + 1))) → ℝ) → (Fin (T.j + (n + (m + 1) - T.j - 1)) → ℝ) :=
    fun z => Work.WilE9.Ift.appendCLM T.j (n + (m + 1) - T.j - 1)
      (Work.WilE7.DimAPI.eqMap T z, fun i => Ae z i - cw i) with hgdef
  have hg_apply : ∀ z, g z = Fin.append (Work.WilE7.DimAPI.eqMap T z)
      (fun i => Ae z i - cw i) := by
    intro z
    simp only [hgdef, Work.WilE9.Ift.appendCLM_apply]
  -- `Good`'s locality clause at `w`
  have hgood_ev : ∀ᶠ y in nhds w, Work.WilE7.DimAPI.eqMap T y = 0 → y ∈ T.X.set := by
    filter_upwards [Work.WilE5.Stratum.good_local hT hw] with y hy hG
    exact hy (Subsingleton.elim _ _) (fun a => congrFun hG a)
  -- ## the differential of `g`
  have hfderiv : ∀ z : Fin (0 + (n + (m + 1))) → ℝ, fderiv ℝ g z =
      (Work.WilE9.Ift.appendCLM T.j (n + (m + 1) - T.j - 1)).comp
        (((Work.WilE7.MainDesign.jac T z).toContinuousLinearMap).prod
          Ae.toContinuousLinearMap) := by
    intro z
    have h1 : HasFDerivAt (fun z : Fin (0 + (n + (m + 1))) → ℝ =>
        (Work.WilE7.DimAPI.eqMap T z, fun i => Ae z i - cw i))
        (((Work.WilE7.MainDesign.jac T z).toContinuousLinearMap).prod
          Ae.toContinuousLinearMap) z := by
      refine HasFDerivAt.prodMk ?_ ?_
      · have h := (Work.WilE7.DimAPI.analyticAt_eqMap T z).hasStrictFDerivAt.hasFDerivAt
        have hf : fderiv ℝ (Work.WilE7.DimAPI.eqMap T) z
            = (Work.WilE7.MainDesign.jac T z).toContinuousLinearMap := by
          rw [Work.WilE7.DimAPI.jac_eq_fderiv T z]
          rfl
        rwa [hf] at h
      · have hα : HasFDerivAt (fun z : Fin (0 + (n + (m + 1))) → ℝ => Ae z)
            Ae.toContinuousLinearMap z := Ae.toContinuousLinearMap.hasFDerivAt
        have hc : HasFDerivAt (fun _ : Fin (0 + (n + (m + 1))) → ℝ => cw)
            (0 : (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ]
              (Fin (n + (m + 1) - T.j - 1) → ℝ)) z :=
          hasFDerivAt_const _ _
        simpa using hα.sub hc
    have h2 :=
      (Work.WilE9.Ift.appendCLM T.j (n + (m + 1) - T.j - 1)).hasFDerivAt.comp z h1
    rw [hgdef]
    exact h2.fderiv
  -- ## surjectivity of `dg` at `w`
  have hsurjCLM : Function.Surjective
      ((Work.WilE9.Ift.appendCLM T.j (n + (m + 1) - T.j - 1)).comp
        (((Work.WilE7.MainDesign.jac T w).toContinuousLinearMap).prod
          Ae.toContinuousLinearMap)) := by
    intro u
    set u₁ : Fin T.j → ℝ := fun a => u (Fin.castAdd (n + (m + 1) - T.j - 1) a) with hu₁def
    set u₂ : Fin (n + (m + 1) - T.j - 1) → ℝ := fun i => u (Fin.natAdd T.j i) with hu₂def
    have hu : Fin.append u₁ u₂ = u := by
      funext a
      refine Fin.addCases ?_ ?_ a
      · intro a'; rw [Fin.append_left]
      · intro b; rw [Fin.append_right]
    have hξ₁ : ∃ ξ : Fin (0 + (n + (m + 1))) → ℝ,
        Work.WilE7.MainDesign.jac T w ξ = u₁ := by
      have htop := Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hw
      have : u₁ ∈ (Work.WilE7.MainDesign.jac T w).range := by
        rw [htop]; exact Submodule.mem_top
      exact LinearMap.mem_range.mp this
    obtain ⟨ξ₁, hξ₁⟩ := hξ₁
    obtain ⟨ξ₂, hξ₂ker, hξ₂val⟩ : ∃ ξ : Fin (0 + (n + (m + 1))) → ℝ,
        ξ ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T w) ∧ Ae ξ = u₂ - Ae ξ₁ := by
      have hmem : u₂ - Ae ξ₁ ∈ (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).map Ae := by
        rw [hAedef, hpersw]
        exact Submodule.mem_top
      obtain ⟨ξ, hξker, hξval⟩ := Submodule.mem_map.mp hmem
      exact ⟨ξ, hξker, hξval⟩
    refine ⟨ξ₁ + ξ₂, ?_⟩
    have hfirst : Work.WilE7.MainDesign.jac T w (ξ₁ + ξ₂) = u₁ := by
      rw [map_add, hξ₁, LinearMap.mem_ker.mp hξ₂ker, add_zero]
    have hsecond : Ae (ξ₁ + ξ₂) = u₂ := by
      rw [map_add, hξ₂val]
      abel
    change (Work.WilE9.Ift.appendCLM T.j (n + (m + 1) - T.j - 1))
      ((Work.WilE7.MainDesign.jac T w) (ξ₁ + ξ₂), Ae (ξ₁ + ξ₂)) = u
    rw [hfirst, hsecond, Work.WilE9.Ift.appendCLM_apply, hu]
  -- ## the criticality condition, coordinate by coordinate
  have hcrit : ∀ i : Fin n, ∀ᶠ y in nhds w, g y = 0 →
      ∀ v : Fin (0 + (n + (m + 1))) → ℝ,
      (fderiv ℝ g y) v = 0 →
      (fderiv ℝ (fun z => Work.WilE7.MainDesign.basePrLin n (m + 1) z i) y) v = 0 := by
    intro i
    filter_upwards [hgood_ev, hker] with y hygood hkery hgy v hv
    have hGy : Work.WilE7.DimAPI.eqMap T y = 0 := by
      have h := hgy
      rw [hg_apply] at h
      funext a
      have h2 := congrFun h (Fin.castAdd (n + (m + 1) - T.j - 1) a)
      rw [Fin.append_left, Pi.zero_apply] at h2
      exact h2
    have hyX : y ∈ T.X.set := hygood hGy
    have hv' := hv
    rw [hfderiv y, appendCLM_comp_prod_apply] at hv'
    have hvy : Work.WilE7.MainDesign.jac T y v = 0 := by
      funext a
      have h2 := congrFun hv' (Fin.castAdd (n + (m + 1) - T.j - 1) a)
      rw [Fin.append_left, Pi.zero_apply] at h2
      exact h2
    have hAev : Ae v = 0 := by
      funext i'
      have h2 := congrFun hv' (Fin.natAdd T.j i')
      rw [Fin.append_right, Pi.zero_apply] at h2
      exact h2
    have hmem : v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T y) ⊓ Ae.ker :=
      ⟨LinearMap.mem_ker.mpr hvy, LinearMap.mem_ker.mpr hAev⟩
    have hkey := hkery hyX
    rw [hAedef] at hkey hmem
    rw [← hkey] at hmem
    have hbv : Work.WilE7.MainDesign.basePrLin n (m + 1) v = 0 :=
      LinearMap.mem_ker.mp hmem.2
    have hFd : fderiv ℝ (fun z => Work.WilE7.MainDesign.basePrLin n (m + 1) z i) y
        = ((ContinuousLinearMap.proj i).comp
            (Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap) :=
      (((ContinuousLinearMap.proj i).comp
        (Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap).hasFDerivAt
          (x := y)).fderiv
    rw [hFd, ContinuousLinearMap.comp_apply]
    have hbv' : (LinearMap.toContinuousLinearMap
        (Work.WilE7.MainDesign.basePrLin n (m + 1))) v = 0 := hbv
    rw [hbv']
    exact map_zero _
  -- ## analyticity of `g` and of the coordinates of `π_n`
  have hg_an : AnalyticAt ℝ g w := by
    rw [hgdef]
    refine AnalyticAt.comp (f := fun z => (Work.WilE7.DimAPI.eqMap T z,
      fun i => Ae z i - cw i)) (x := w) ?_ ?_
    · exact (Work.WilE9.Ift.appendCLM T.j (n + (m + 1) - T.j - 1)).analyticAt _
    · exact (Work.WilE7.DimAPI.analyticAt_eqMap T w).prod
        ((Ae.toContinuousLinearMap.analyticAt w).sub (analyticAt_const (v := cw) (x := w)))
  -- ## apply the critical-level-set lemma coordinatewise
  have hcoord : ∀ i : Fin n, ∀ᶠ y in nhds w, g y = 0 →
      Work.WilE7.MainDesign.basePrLin n (m + 1) y i
        = Work.WilE7.MainDesign.basePrLin n (m + 1) w i := by
    intro i
    refine Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt g
      (fun z => Work.WilE7.MainDesign.basePrLin n (m + 1) z i) w hg_an ?_ ?_ ?_
    · exact ((ContinuousLinearMap.proj i).comp
        (Work.WilE7.MainDesign.basePrLin n (m + 1)).toContinuousLinearMap).analyticAt w
    · rw [hfderiv w]
      exact LinearMap.range_eq_top.mpr hsurjCLM
    · exact hcrit i
  have hall : ∀ᶠ y in nhds w, ∀ i, (g y = 0 →
      Work.WilE7.MainDesign.basePrLin n (m + 1) y i
        = Work.WilE7.MainDesign.basePrLin n (m + 1) w i) :=
    (Filter.eventually_all).mpr hcoord
  -- ## rephrase in terms of `eqMap` and the `e`-coordinates
  filter_upwards [hall] with y hy hGy heq
  refine funext fun i => hy i ?_
  rw [hg_apply]
  have hc : (fun i => Ae y i - cw i) = 0 := by
    funext i
    have h1 : Ae y i = Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i) := by
      rw [hAeapply y]
    have h2 : cw i = Work.WilE7.MainDesign.basePrLin n (m + 1) w (e i) := by
      rw [hcwdef]
    rw [h1, h2, heq i, sub_self]
    rfl
  rw [hGy, hc]
  funext a
  refine Fin.addCases ?_ ?_ a <;> simp

end Work.WilE7.Endgame

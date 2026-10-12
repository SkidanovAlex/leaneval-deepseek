import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.Analysis.BoseBand.MomWordOffdiag.continuous_kFT_boxState_fibre
import Submission.Work.Analysis.BoseBand.MomWordOffdiag.kFT_indU_fibre_update_integral_zero
import Submission.Work.Analysis.BoseBand.MomWordOffdiag.momWord_fibre_integrable
import Submission.Work.BoseFixB2.DvApriori.momForm_polar_diff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.momWord_fibre_offdiag`

The **off-diagonal fibre integral of FS `eq:DefT`'s third kinetic piece** `momWord`:
for a slot `j` belonging to two *different* joint sector sets `S ≠ T`, the polarised
combination

    ∫_{abox n ℓ} θ₀(x_j)·[ momWord(fibre_j(E_SΦ + E_TΦ)(x)) − momWord(fibre_j(E_SΦ − E_TΦ)(x)) ] d x

vanishes.

## The argument

Write `A = E_SΦ`, `B = E_TΦ` (`E_S = jointProj ℓ S Φ = ∏_{i∈S}Q_i ∏_{i∉S}P_i`).  Since
`momWord ℓ d εT b 0 = b·εT·(dℓ)⁻²·momForm ℓ d 0` and `momForm` is a quadratic form with
polarisation `momBil` (`momForm_polar_diff`), and since the slot-`j` means of `A` and `B`
vanish (`j ∈ S`, `j ∈ T`), so that `boxState ℓ 0 (fibre_j A x) = 1_{Λ(0)}·fibre_j A x`
(`boxState_fibre_eq_of_mean_zero`), the target reduces to

    ∫_{abox n ℓ} θ₀(x_j)·momBil ℓ d (fibre_j A x) (fibre_j B x) d x = 0.

Because `S ≠ T` with `j ∈ S ∩ T`, there is a slot `i ≠ j` (`exists_diff_slot`) lying in
exactly one of the two sets; say `i ∈ S`, `i ∉ T`.  Then

* the slot-`i` mean of `A` vanishes (`jointProj_aP_eq_zero`), while
* `B` does not depend on the slot-`i` coordinate (`constIn_jointProj`).

For fixed `p` the `x`-integrand
`x ↦ θ₀(x_j)·⟨kFT(boxState(fibre_j A x))p, kFT(boxState(fibre_j B x))p⟩` therefore has zero
slot-`i` fibre integral: the `B`-factor is constant along the fibre, the `A`-factor's fibre
integral is the `kFT` of a slot-`i`-mean-free state
(`kFT_indU_fibre_update_integral_zero`).  Peeling the slot `i`
(`setIntegral_eq_zero_of_fibre_eq_zero`) gives the vanishing of the whole `x`-integral.
Fubini in `(x,p)` — legitimate by `momWord_fibre_integrable` — then finishes.
-/

noncomputable section

namespace Work.Analysis.BoseBand

open MeasureTheory
open scoped Real Topology BigOperators ComplexConjugate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary slot algebra -/

lemma fibre_add {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (fun y => A y + B y) x
      = fun z => Work.BoseKinLoc.fibre N j A x z + Work.BoseKinLoc.fibre N j B x z := rfl

lemma fibre_sub {N : ℕ} (j : Fin N) (A B : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.fibre N j (fun y => A y - B y) x
      = fun z => Work.BoseKinLoc.fibre N j A x z - Work.BoseKinLoc.fibre N j B x z := rfl

lemma contDiff_fibre {N : ℕ} (j : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (x : Submission.BoseGases.X N) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre N j Ψ x) :=
  hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)

lemma continuous_update_const {N : ℕ} (j : Fin N) (x : Submission.BoseGases.X N) :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) => Function.update x j z := by
  have h2 : Continuous fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
      Function.update p.1 j p.2 := continuous_update j
  exact h2.comp (continuous_const.prodMk continuous_id)

lemma lamBox_zero_eq_acube (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext z
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

lemma indU_eq_one_of_mem_abox {n : ℕ} {ℓ : ℝ} (j : Fin n) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) : Work.BoseKinLoc.indU ℓ 0 (x j) = 1 := by
  have hmem : x j ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
    rw [lamBox_zero_eq_acube]
    exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j
  rw [Work.BoseKinLoc.indU, Set.indicator_of_mem hmem]

/-- `aP ℓ i Ψ = 0` unwound: the slot-`i` cube integral of `Ψ` vanishes at every point. -/
lemma integral_update_eq_zero_of_aP_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (h : Submission.BoseGases.aP ℓ i Ψ = 0)
    (x : Submission.BoseGases.X n) :
    ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y) = 0 := by
  have hx := congrFun h x
  simp only [Submission.BoseGases.aP] at hx
  exact (mul_eq_zero.mp hx).resolve_left (by positivity : (1 / ℓ ^ 3 : ℝ) ≠ 0)

/-- If two subsets `S`, `T` of `range n` both contain the index `j` and are distinct,
then they differ at some index `i ≠ j`. -/
lemma exists_diff_slot {n : ℕ} (j : Fin n) {S T : Finset ℕ} (hS : S ⊆ Finset.range n)
    (hT : T ⊆ Finset.range n) (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) :
    ∃ i : Fin n, i ≠ j ∧ (((i : ℕ) ∈ S ∧ (i : ℕ) ∉ T) ∨ ((i : ℕ) ∈ T ∧ (i : ℕ) ∉ S)) := by
  have keyS : ∀ {x : ℕ}, x ∈ S → x ∉ T → x < n ∧ x ≠ (j : ℕ) := by
    intro x hxS hxT
    exact ⟨Finset.mem_range.mp (hS hxS), fun h => hxT (h ▸ hjT)⟩
  have keyT : ∀ {x : ℕ}, x ∈ T → x ∉ S → x < n ∧ x ≠ (j : ℕ) := by
    intro x hxT hxS
    exact ⟨Finset.mem_range.mp (hT hxT), fun h => hxS (h ▸ hjS)⟩
  by_cases hsub : S ⊆ T
  · have hnot : ¬ T ⊆ S := fun h' => hST (Finset.Subset.antisymm hsub h')
    rw [Finset.not_subset] at hnot
    obtain ⟨x, hxT, hxS⟩ := hnot
    obtain ⟨hxlt, hxj⟩ := keyT hxT hxS
    exact ⟨⟨x, hxlt⟩, fun hi => hxj (congrArg Fin.val hi), Or.inr ⟨hxT, hxS⟩⟩
  · rw [Finset.not_subset] at hsub
    obtain ⟨x, hxS, hxT⟩ := hsub
    obtain ⟨hxlt, hxj⟩ := keyS hxS hxT
    exact ⟨⟨x, hxlt⟩, fun hi => hxj (congrArg Fin.val hi), Or.inl ⟨hxS, hxT⟩⟩

/-! ## 2. The anchored box state of a slot fibre -/

/-- The anchored mean-free projection commutes with taking the slot-`j` fibre. -/
lemma Qfree_fibre_eq {ℓ : ℝ} {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
      = Work.BoseKinLoc.fibre n j (Submission.BoseGases.aQ ℓ j Ψ) x := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BoseKinLoc.fibre, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean, Submission.BoseGases.aQ, Submission.BoseGases.aP,
    Function.update_idem, smul_zero, zero_add, one_div]

/-- If the slot-`j` mean of `Ψ` vanishes, the anchored box state of the slot-`j` fibre of `Ψ`
is just the indicator of the box times the fibre (no mean subtracted). -/
lemma boxState_fibre_eq_of_mean_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hmean : ∀ x : Submission.BoseGases.X n,
      ∫ z in Submission.BoseGases.acube ℓ, Ψ (Function.update x j z) = 0)
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
      = fun z => ((Work.BoseKinLoc.indU ℓ 0 z : ℝ) : ℂ) *
          ((Work.BoseKinLoc.fibre n j Ψ x z : ℝ) : ℂ) := by
  have hQ : Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
      = Work.BoseKinLoc.fibre n j Ψ x := by
    rw [Qfree_fibre_eq j x]
    funext y
    simp only [Work.BoseKinLoc.fibre, Submission.BoseGases.aQ, Submission.BoseGases.aP,
      Function.update_idem]
    rw [hmean x]
    ring
  funext z
  simp only [Work.BoseKinLoc.Kinetic.boxState, hQ]

/-- The anchored box state of the slot-`j` fibre is invariant under an update in a *different*
slot on which the state does not depend. -/
lemma boxState_fibre_indep_slot {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {j i : Fin n} (hij : i ≠ j)
    {A : Submission.BoseGases.X n → ℝ}
    (hind : ∀ (x : Submission.BoseGases.X n) (y : EuclideanSpace ℝ (Fin 3)),
      A (Function.update x i y) = A x) (x : Submission.BoseGases.X n)
    (y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A (Function.update x i y))
      = Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A x) := by
  have hψ : Work.BoseKinLoc.fibre n j A (Function.update x i y)
      = Work.BoseKinLoc.fibre n j A x := by
    funext z
    simp only [Work.BoseKinLoc.fibre]
    rw [Function.update_comm hij y z x]
    exact hind (Function.update x j z) y
  rw [hψ]

/-! ## 3. Peeling a slot whose fibre integral vanishes -/

/-- **The peel of a slot-`i`-mean-zero function.**  If the slot-`i` fibre integral of `Φ`
vanishes pointwise, then the box integral of `Φ` vanishes. -/
theorem setIntegral_eq_zero_of_fibre_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i : Fin n}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hfib : ∀ x : Submission.BoseGases.X n,
      ∫ z in Submission.BoseGases.acube ℓ, Φ (Function.update x i z) = 0) :
    ∫ x in Submission.BoseGases.abox n ℓ, Φ x = 0 := by
  by_cases hInt : IntegrableOn Φ (Submission.BoseGases.abox n ℓ) volume
  · cases n with
    | zero => exact Fin.elim0 i
    | succ m =>
      rw [Submission.BoseGases.abox_integral_peel (n := m) (ℓ := ℓ) i Φ hInt]
      have hzero : (fun r : Submission.BoseGases.X m =>
          ∫ y in Submission.BoseGases.acube ℓ,
            Φ ((Submission.BoseGases.kcInsN m i) (y, r))) = fun _ => (0 : ℝ) := by
        funext r
        rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
              Φ ((Submission.BoseGases.kcInsN m i) (y, r)))
            = fun y => Φ (Function.update ((Submission.BoseGases.kcInsN m i) (0, r)) i y) from by
          funext y
          rw [Submission.BoseGases.kcInsN_update_zero]]
        exact hfib _
      rw [hzero, MeasureTheory.integral_zero]
  · exact MeasureTheory.integral_undef hInt

/-! ## 4. Pulling an integral out of an inner product with a constant -/

/-- For `u` integrable on the cube and `c : ℂ` a constant,
`∫_y ⟪u y, c⟫_ℝ = ⟪∫_y u y, c⟫_ℝ`. -/
theorem setIntegral_inner_const {ℓ : ℝ} {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : IntegrableOn u (Submission.BoseGases.acube ℓ) volume) (c : ℂ) :
    (∫ y in Submission.BoseGases.acube ℓ, inner ℝ (u y) c)
      = inner ℝ (∫ y in Submission.BoseGases.acube ℓ, u y) c := by
  have hL : ∀ a : ℂ, inner ℝ a c
      = Complex.reCLM (((ContinuousLinearMap.mul ℝ ℂ) (conj c)) a) := by
    intro a
    simp only [Complex.inner, Complex.reCLM_apply, ContinuousLinearMap.mul_apply']
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hInt : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      ((ContinuousLinearMap.mul ℝ ℂ) (conj c)) (u y))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    (((ContinuousLinearMap.mul ℝ ℂ) (conj c))).integrable_comp hu
  calc (∫ y in Submission.BoseGases.acube ℓ, inner ℝ (u y) c)
      = ∫ y in Submission.BoseGases.acube ℓ,
          Complex.reCLM (((ContinuousLinearMap.mul ℝ ℂ) (conj c)) (u y)) := by
        apply setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        intro y hy
        exact hL (u y)
    _ = Complex.reCLM (∫ y in Submission.BoseGases.acube ℓ,
          ((ContinuousLinearMap.mul ℝ ℂ) (conj c)) (u y)) := by
        rw [Complex.reCLM.integral_comp_comm hInt]
    _ = Complex.reCLM (((ContinuousLinearMap.mul ℝ ℂ) (conj c))
          (∫ y in Submission.BoseGases.acube ℓ, u y)) := by
        exact congrArg Complex.reCLM (ContinuousLinearMap.integral_comp_comm
          (L := (ContinuousLinearMap.mul ℝ ℂ) (conj c)) hu)
    _ = inner ℝ (∫ y in Submission.BoseGases.acube ℓ, u y) c := (hL _).symm

/-! ## 5. The off-diagonal fibre integral vanishes, pointwise in `p` -/

theorem fibre_kFT_pair_integral_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {S T : Finset ℕ} (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {i : Fin n} (hij : i ≠ j) (hiS : (i : ℕ) ∈ S) (hiT : (i : ℕ) ∉ T)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
        (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))) = 0 := by
  have hAc : Continuous (Work.BoseFixB2.jointProj ℓ S Φ) :=
    Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ.continuous
  have hAd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ S Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hAz : ∀ x : Submission.BoseGases.X n,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x j z) = 0 :=
    fun x => integral_update_eq_zero_of_aP_eq_zero hℓ j
      (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjS j.isLt hΦ) x
  have hBz : ∀ x : Submission.BoseGases.X n,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update x j z) = 0 :=
    fun x => integral_update_eq_zero_of_aP_eq_zero hℓ j
      (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjT j.isLt hΦ) x
  have hmeaniS : ∀ x : Submission.BoseGases.X n,
      ∫ y in Submission.BoseGases.acube ℓ,
        (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update x i y) = 0 :=
    fun x => integral_update_eq_zero_of_aP_eq_zero hℓ i
      (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hiS i.isLt hΦ) x
  have hBind : ∀ (x : Submission.BoseGases.X n) (y : EuclideanSpace ℝ (Fin 3)),
      Work.BoseFixB2.jointProj ℓ T Φ (Function.update x i y)
        = Work.BoseFixB2.jointProj ℓ T Φ x :=
    fun x y => Work.BoseFixB2.Sector.constIn_jointProj hℓ i.isLt hiT hΦ.continuous x y
  -- the slot-`i` fibre integral of the `x`-integrand vanishes
  have hfib : ∀ x : Submission.BoseGases.X n,
      ∫ y in Submission.BoseGases.acube ℓ,
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
              (Function.update x i y))) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ)
              (Function.update x i y))) p) = 0 := by
    intro x
    have hTconst : ∀ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ)
            (Function.update x i y))) p
        = Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p := by
      intro y
      rw [boxState_fibre_indep_slot hℓ hij hBind x y]
    have hcontS : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
            (Function.update x i y))) p) :=
      (MomWordOffdiag.continuous_kFT_boxState_fibre hℓ j hAc p).comp
        (continuous_update_const i x)
    have hintS : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
            (Function.update x i y))) p)
        (Submission.BoseGases.acube ℓ) volume :=
      ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
        hcontS.continuousOn
    have hpull : (∫ y in Submission.BoseGases.acube ℓ,
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update x i y))) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))
        = inner ℝ (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update x i y))) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p) :=
      setIntegral_inner_const hintS _
    have hSzero : (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
            (Function.update x i y))) p) = 0 := by
      simp only [boxState_fibre_eq_of_mean_zero hℓ j hAd hAz]
      exact MomWordOffdiag.kFT_indU_fibre_update_integral_zero hℓ hij hAc hmeaniS x p
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update x i y))) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ)
                (Function.update x i y))) p))
        = (∫ y in Submission.BoseGases.acube ℓ,
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ)
                (Function.update x i y))) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p)) from by
      apply setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      intro y hy
      beta_reduce
      rw [hTconst y]]
    rw [hpull, hSzero, inner_zero_left]
  -- drop the indicator and peel the slot `i`
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))
      = ∫ x in Submission.BoseGases.abox n ℓ,
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p) from by
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    beta_reduce
    rw [indU_eq_one_of_mem_abox j hx, one_mul]]
  exact setIntegral_eq_zero_of_fibre_eq_zero hℓ (i := i) hfib

/-! ## 6. The target -/

theorem momWord_fibre_offdiag {ℓ d εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n) (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) * (Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x) - Work.BoseKinLoc.momWord ℓ d εT b 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  classical
  set c : ℝ := b * εT * (d * ℓ) ^ (-2 : ℤ) with hc
  have hAd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ S Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hBd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ T Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ
  have hAc : Continuous (Work.BoseFixB2.jointProj ℓ S Φ) :=
    Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ.continuous
  have hBc : Continuous (Work.BoseFixB2.jointProj ℓ T Φ) :=
    Work.BoseFixB2.Sector.jointProj_continuous hℓ T hΦ.continuous
  -- ## the pointwise polarisation
  have hpt : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0
            (Work.BoseKinLoc.fibre n j
              (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0
            (Work.BoseKinLoc.fibre n j
              (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))
      = (c * 4) * (Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) := by
    intro x
    have hsum : Work.BoseKinLoc.fibre n j
          (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x
        = fun z => Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z
            + Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x z := rfl
    have hsub : Work.BoseKinLoc.fibre n j
          (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x
        = fun z => Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z
            - Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x z := rfl
    have hmw : Work.BoseKinLoc.momWord ℓ d εT b 0
            (Work.BoseKinLoc.fibre n j
              (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
          - Work.BoseKinLoc.momWord ℓ d εT b 0
            (Work.BoseKinLoc.fibre n j
              (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)
        = c * (Work.BoseKinLoc.momForm ℓ d 0
              (Work.BoseKinLoc.fibre n j
                (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
            - Work.BoseKinLoc.momForm ℓ d 0
              (Work.BoseKinLoc.fibre n j
                (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)) := by
      simp only [Work.BoseKinLoc.momWord, hc]
      ring
    rw [hmw, hsum, hsub,
      Work.BoseFixB2.DvApriori.momForm_polar_diff hℓ
        (contDiff_fibre j hAd x) (contDiff_fibre j hBd x)]
    ring
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.momWord ℓ d εT b 0
            (Work.BoseKinLoc.fibre n j
              (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
         - Work.BoseKinLoc.momWord ℓ d εT b 0
            (Work.BoseKinLoc.fibre n j
              (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)))
      = (c * 4) * (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) := by
    rw [setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => hpt x)]
    rw [MeasureTheory.integral_const_mul]
  -- ## the `(x,p)`-integrand
  set K : Submission.BoseGases.X n → EuclideanSpace ℝ (Fin 3) → ℝ := fun x p =>
      Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
        (Work.BoseKinLoc.momProj ℓ d p *
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))) with hK
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseFixB2.DvApriori.momBil ℓ d
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)
            (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x))
      = ∫ x in Submission.BoseGases.abox n ℓ, ∫ p : EuclideanSpace ℝ (Fin 3), K x p := by
    apply setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    intro x hx
    beta_reduce
    have hKx : (∫ p : EuclideanSpace ℝ (Fin 3), K x p)
        = Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p)) := by
      rw [hK, MeasureTheory.integral_const_mul]
      congr 1
      exact MeasureTheory.integral_const_mul ((2 * Real.pi) ^ 3)⁻¹
        (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.momProj ℓ d p *
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))
    rw [hKx]
    simp only [Work.BoseFixB2.DvApriori.momBil]
  have hIntK : MeasureTheory.Integrable (Function.uncurry K)
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h := MomWordOffdiag.momWord_fibre_integrable (ℓ := ℓ) (d := d) hℓ (n := n) j hAd hBd
    refine h.congr (Filter.Eventually.of_forall (fun q => ?_))
    simp only [Function.uncurry_def, hK]
    ring
  have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ, ∫ p : EuclideanSpace ℝ (Fin 3), K x p)
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          ∫ x in Submission.BoseGases.abox n ℓ, K x p :=
    MeasureTheory.integral_integral_swap hIntK
  -- ## the inner `x`-integral vanishes for every `p`
  obtain ⟨i, hij, hmem⟩ := exists_diff_slot j hS hT hjS hjT hST
  have hJall : ∀ p : EuclideanSpace ℝ (Fin 3),
      (∫ x in Submission.BoseGases.abox n ℓ, K x p) = 0 := by
    intro p
    have hKp : (fun x : Submission.BoseGases.X n => K x p)
        = fun x => Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
            (Work.BoseKinLoc.momProj ℓ d p *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))) := by
      funext x
      rw [hK]
    have hfac : (fun x : Submission.BoseGases.X n =>
          Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
            (Work.BoseKinLoc.momProj ℓ d p *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p))))
        = fun x => (((2 * Real.pi) ^ 3)⁻¹ * Work.BoseKinLoc.momProj ℓ d p) *
            (Work.BoseKinLoc.indU ℓ 0 (x j) *
              inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
                (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                  (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p)) := by
      funext x
      ring
    have hzero : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x)) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x)) p)) = 0 := by
      rcases hmem with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
      · exact fibre_kFT_pair_integral_zero hℓ j hjS hjT hΦ hij hiS hiT p
      · have hkey := fibre_kFT_pair_integral_zero (S := T) (T := S) hℓ j hjT hjS hΦ hij hiT hiS p
        refine (setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
          (fun x hx => by rw [real_inner_comm])).trans hkey
    rw [hKp, hfac, MeasureTheory.integral_const_mul, hzero, mul_zero]
  have hz : (∫ p : EuclideanSpace ℝ (Fin 3),
      ∫ x in Submission.BoseGases.abox n ℓ, K x p) = 0 := by
    simp only [hJall, MeasureTheory.integral_zero]
  rw [hstep1, hstep2, hstep3, hz, mul_zero]

end Work.Analysis.BoseBand

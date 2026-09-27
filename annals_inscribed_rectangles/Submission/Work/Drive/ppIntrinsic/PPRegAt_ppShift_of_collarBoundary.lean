import Mathlib
import Submission.Work.Drive.ppIntrinsic.Defs
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.PPRegAt_chart_indep
import Submission.Work.Drive.ppIntrinsic.Smooth
import Submission.Work.Drive.ppParity.contDiffAt_ppDiff_family2

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive.ppIntrinsic
open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) M]
local notation "C∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma top_ne_zero' : C∞ ≠ (0 : WithTop ℕ∞) := by
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

def pC (E : ℝ → EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 9)) : M :=
  E (ftS x) (ftU x)

def pC' (E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (x : EuclideanSpace ℝ (Fin 9)) : M :=
  E' (ftS x) (ftU x)

/-- The perturbed weight vanishes on the closed collar. -/
lemma weight_eq_zero_of_closedCollar {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    {x : EuclideanSpace ℝ (Fin 9)} (hc : ftS x = δ ∨ ftS x = 1 - δ) :
    w (ftS x) = 0 := by
  rcases hc with h | h
  · exact hwleft _ (le_of_eq h)
  · exact hwright _ (le_of_eq h.symm)

/-- **The perturbed pair meet at a collar-boundary point is the base pair meet.** -/
lemma ppMeet_ppShift_iff_of_closedCollar {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) {x : EuclideanSpace ℝ (Fin 9)}
    (hc : ftS x = δ ∨ ftS x = 1 - δ) :
    ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x ↔
      ppMeet E E' V W x := by
  have hw := weight_eq_zero_of_closedCollar hwleft hwright hc
  have h1 : ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x) = E (ftS x) (ftU x) :=
    ppShift_eq_of_eq_zero hΞ0 hw (ftU x)
  have h2 : ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x) = E' (ftS x) (ftU x) :=
    ppShift_eq_of_eq_zero hΞ0 hw (ftU x)
  constructor
  · intro h
    obtain ⟨hbox, hA, hB⟩ := h
    exact ⟨hbox, by rw [← h1]; exact hA, by rw [← h2]; exact hB⟩
  · intro h
    obtain ⟨hbox, hA, hB⟩ := h
    exact ⟨hbox, by rw [h1]; exact hA, by rw [h2]; exact hB⟩

/-- **The `τ = 0` chain is the base chain.** -/
lemma ppShift_zero_left (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (w : ℝ → ℝ) (E : ℝ → EuclideanSpace ℝ (Fin 2) → M) :
    ppShift Ξ w (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E = E := by
  funext s u
  simp [ppShift, hΞ0]

lemma ppShift_zero_right (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (w : ℝ → ℝ) (E : ℝ → EuclideanSpace ℝ (Fin 2) → M) :
    ppShift Ξ w (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E = E := by
  funext s u
  simp [ppShift, hΞ0]

lemma continuous_cofactorVec_apply {m : ℕ} (i : Fin (m + 1)) :
    Continuous fun T : Amb m →L[ℝ] Tgt m => cofactorVec T i := by
  have hdet : Continuous fun T : Amb m →L[ℝ] Tgt m =>
      ((cofactorMatrix T).submatrix (Fin.succAbove i) id).det := by
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (by fun_prop : Continuous fun T : Amb m →L[ℝ] Tgt m =>
      T (EuclideanSpace.single (Fin.succAbove i a) 1) b)
  have h : Continuous fun T : Amb m →L[ℝ] Tgt m =>
      (-1 : ℝ) ^ (i : ℕ) * ((cofactorMatrix T).submatrix (Fin.succAbove i) id).det :=
    continuous_const.mul hdet
  simpa only [cofactorVec] using h

lemma isOpen_setOf_surjective_clm_pp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L₀ hL₀
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective (L₀ : E →ₗ[ℝ] F)
    (LinearMap.range_eq_top.mpr hL₀)
  have hRcont : Continuous R := LinearMap.continuous_of_finiteDimensional R
  let R' : F →L[ℝ] E := ⟨R, hRcont⟩
  have hR'coe : (R' : F → E) = R := rfl
  have hR' : L₀.comp R' = ContinuousLinearMap.id ℝ F := by
    ext x
    rw [ContinuousLinearMap.comp_apply, hR'coe, ContinuousLinearMap.id_apply]
    exact DFunLike.congr_fun hR x
  have hcont : Continuous fun L : E →L[ℝ] F => L.comp R' := by
    have h1 : Continuous fun L : E →L[ℝ] F =>
        ((ContinuousLinearMap.compL ℝ F E F) L) R' :=
      (ContinuousLinearMap.compL ℝ F E F).continuous.clm_apply continuous_const
    simpa [ContinuousLinearMap.compL_apply] using h1
  have hnbhd : {L : E →L[ℝ] F | ‖L.comp R' - ContinuousLinearMap.id ℝ F‖ < 1} ∈ 𝓝 L₀ := by
    have hc : Continuous fun L : E →L[ℝ] F => ‖L.comp R' - ContinuousLinearMap.id ℝ F‖ :=
      (hcont.sub continuous_const).norm
    refine (isOpen_lt hc (continuous_const : Continuous fun _ : E →L[ℝ] F => (1 : ℝ))).mem_nhds ?_
    show ‖L₀.comp R' - ContinuousLinearMap.id ℝ F‖ < 1
    rw [hR', sub_self, norm_zero]
    norm_num
  refine Filter.mem_of_superset hnbhd ?_
  intro L hL
  have hunit : IsUnit (L.comp R') := by
    have hsplit : L.comp R' = ContinuousLinearMap.id ℝ F -
        (ContinuousLinearMap.id ℝ F - L.comp R') := by abel
    rw [hsplit]
    exact isUnit_one_sub_of_norm_lt_one (by simpa [norm_sub_rev] using hL)
  have hbij : Function.Bijective (L.comp R') :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  intro y
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨R' x, hx⟩

lemma isOpen_setOf_surjective_domRestrict {m : ℕ} (i : Fin (m + 1)) :
    IsOpen {T : Amb m →L[ℝ] Tgt m |
      Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1)} := by
  let S1 : Set (Amb m →L[ℝ] Tgt m) := {T | Function.Surjective T}
  let S2 : Set (Amb m →L[ℝ] Tgt m) := {T | cofactorVec T i ≠ 0}
  have hset : ({T : Amb m →L[ℝ] Tgt m |
      Function.Surjective (fun v : {v : Amb m // v i = 0} => T v.1)}) = S1 ∩ S2 := by
    ext T
    constructor
    · intro h
      exact ⟨fun w => by obtain ⟨v, hv⟩ := h w; exact ⟨v.1, hv⟩,
        cofactorVec_apply_ne_zero T i h⟩
    · rintro ⟨hT, hc⟩
      exact (surjective_domRestrict_iff_cofactorVec_ne_zero T hT i).mpr hc
  rw [hset]
  exact (isOpen_setOf_surjective_clm_pp (E := Amb m) (F := Tgt m)).inter
    (isOpen_ne.preimage (continuous_cofactorVec_apply i))

theorem contMDiff_V_ftY (V : EuclideanSpace ℝ (Fin 3) → M)
    (hV : ContMDiff (𝓡 3) (𝓡 4) C∞ V) :
    ContMDiff (𝓡 9) (𝓡 4) C∞ (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) := by
  refine hV.comp ?_
  refine (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
    (E' := EuclideanSpace ℝ (Fin 3))).mpr ?_
  show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 3 => z ⟨3 + i.val, by omega⟩))
  fun_prop

theorem contMDiff_W_ftZ (W : EuclideanSpace ℝ (Fin 3) → M)
    (hW : ContMDiff (𝓡 3) (𝓡 4) C∞ W) :
    ContMDiff (𝓡 9) (𝓡 4) C∞ (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) := by
  refine hW.comp ?_
  refine (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
    (E' := EuclideanSpace ℝ (Fin 3))).mpr ?_
  show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 3 => z ⟨6 + i.val, by omega⟩))
  fun_prop

lemma continuous_V_ftY (V : EuclideanSpace ℝ (Fin 3) → M)
    (hV : ContMDiff (𝓡 3) (𝓡 4) C∞ V) :
    Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => V (ftY q.2) := by
  refine hV.continuous.comp ?_
  show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 3 => q.2 ⟨3 + i.val, by omega⟩)
  fun_prop

lemma continuous_W_ftZ (W : EuclideanSpace ℝ (Fin 3) → M)
    (hW : ContMDiff (𝓡 3) (𝓡 4) C∞ W) :
    Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => W (ftZ q.2) := by
  refine hW.continuous.comp ?_
  show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 3 => q.2 ⟨6 + i.val, by omega⟩)
  fun_prop

theorem contMDiff_chain_shift (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    {w : ℝ → ℝ} (hw : ContDiff ℝ C∞ w) (v : EuclideanSpace ℝ (Fin 4))
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w v E (ftS z) (ftU z)) := by
  have hsmul : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => w (ftS z) • v) := by
    refine (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
      (E' := EuclideanSpace ℝ (Fin 4))).mpr ?_
    exact (hw.comp (by
      show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
      fun_prop)).smul contDiff_const
  have hSU : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => (ftS z, ftU z)) := by
    refine (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
      (E' := ℝ × EuclideanSpace ℝ (Fin 2))).mpr ?_
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
      fun_prop
    · show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 2 => z ⟨1 + i.val, by omega⟩))
      fun_prop
  have hchain : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)) := by
    simpa [Function.comp_def, Function.uncurry] using hE.comp hSU
  exact hΞsm.comp (hsmul.prodMk hchain)

theorem continuous_ppShift_chain_apply (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    {w : ℝ → ℝ} (hw : ContDiff ℝ C∞ w)
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E)) :
    Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      w (ftS q.2) • unpackFst q.1 := by
    refine (hw.continuous.comp ?_).smul ?_
    · show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => q.2 0
      fun_prop
    · exact unpackFst.continuous.comp (by fun_prop : Continuous fun q :
        EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => q.1)
  have hpair : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      (ftS q.2, ftU q.2) := by
    refine Continuous.prodMk ?_ ?_
    · show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => q.2 0
      fun_prop
    · show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 2 => q.2 ⟨1 + i.val, by omega⟩)
      fun_prop
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      E (ftS q.2) (ftU q.2) := by
    simpa [Function.comp_def, Function.uncurry] using hE.continuous.comp hpair
  exact hΞsm.continuous.comp (h1.prodMk h2)

theorem continuous_ppShift_chain_apply' (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    {w : ℝ → ℝ} (hw : ContDiff ℝ C∞ w)
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E)) :
    Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E (ftS q.2) (ftU q.2) := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      w (ftS q.2) • unpackSnd q.1 := by
    refine (hw.continuous.comp ?_).smul ?_
    · show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => q.2 0
      fun_prop
    · exact unpackSnd.continuous.comp (by fun_prop : Continuous fun q :
        EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => q.1)
  have hpair : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      (ftS q.2, ftU q.2) := by
    refine Continuous.prodMk ?_ ?_
    · show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => q.2 0
      fun_prop
    · show Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 2 => q.2 ⟨1 + i.val, by omega⟩)
      fun_prop
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      E (ftS q.2) (ftU q.2) := by
    simpa [Function.comp_def, Function.uncurry] using hE.continuous.comp hpair
  exact hΞsm.continuous.comp (h1.prodMk h2)



/-! ## The local propagation lemma

Given a base meet `x₀` at which the (self-centred charted) pair map is regular, and a finite set `I`
of face indices over which the base derivative is surjective when restricted, the same conditions
hold — in the *same* chart pair, that of `x₀` — for the perturbed family, at every point in a
neighbourhood of `x₀` and for all small enough perturbation parameters; the neighbourhood is contained
in a prescribed ball, on which the geometry of the box boundary is controlled by `hforce`. -/

theorem ppRegAt_local
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ W)
    {w : ℝ → ℝ} (hw : ContDiff ℝ C∞ w)
    {x₀ : EuclideanSpace ℝ (Fin 9)} (hx₀ : x₀ ∈ ppMeet E E' V W)
    (hfull : Function.Surjective
      (fderiv ℝ (ppDiff (pC E x₀) (pC' E' x₀) E E' V W) x₀))
    (I : Finset (Fin 9))
    (hres : ∀ i ∈ I, Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
      fderiv ℝ (ppDiff (pC E x₀) (pC' E' x₀) E E' V W) x₀ v.1))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hforce : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Metric.ball x₀ ρ →
      y ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ i ∈ I, (y i = 0 ∨ y i = 1) ∧ ∀ j : Fin 9, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set (EuclideanSpace ℝ (Fin 9)), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ Metric.ball x₀ ρ ∧
      ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε → ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ U →
        y ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W →
        PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y := by
  classical
  let G : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
      EuclideanSpace ℝ (Fin 8) := fun q =>
    ppDiff (pC E x₀) (pC' E' x₀) (ppShift Ξ w (unpackFst q.1) E)
      (ppShift Ξ w (unpackSnd q.1) E') V W q.2
  have hsrc : ppShift Ξ w (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E
        (ftS x₀) (ftU x₀) ∈ (chr (pC E x₀)).source ∧
      V (ftY x₀) ∈ (chr (pC E x₀)).source ∧
      ppShift Ξ w (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E'
        (ftS x₀) (ftU x₀) ∈ (chr (pC' E' x₀)).source ∧
      W (ftZ x₀) ∈ (chr (pC' E' x₀)).source := by
    rw [ppShift_zero_left Ξ hΞ0 w E, ppShift_zero_right Ξ hΞ0 w E']
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [pC, chr] using mem_chart_source (EuclideanSpace ℝ (Fin 4)) (E (ftS x₀) (ftU x₀))
    · rw [← hx₀.2.1]
      simpa only [pC, chr] using mem_chart_source (EuclideanSpace ℝ (Fin 4)) (E (ftS x₀) (ftU x₀))
    · simpa only [pC', chr] using mem_chart_source (EuclideanSpace ℝ (Fin 4)) (E' (ftS x₀) (ftU x₀))
    · rw [← hx₀.2.2]
      simpa only [pC', chr] using mem_chart_source (EuclideanSpace ℝ (Fin 4)) (E' (ftS x₀) (ftU x₀))
  have hG : ContDiffAt ℝ C∞ G (0, x₀) :=
    ppParity.contDiffAt_ppDiff_family2 Ξ hΞsm w hw hE hE' hV hW (pC E x₀) (pC' E' x₀) 0 hsrc
  -- differentiability of `G` on a ball around the base point
  obtain ⟨uloc, huloc, hulocdiff⟩ := hG.contDiffOn (m := 1) (by norm_num)
    (by intro h; exact absurd h (by norm_num))
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.mem_nhds_iff.mp huloc
  have hdiffball : DifferentiableOn ℝ G
      (Metric.ball ((0 : EuclideanSpace ℝ (Fin 8)), x₀) ρ₀) :=
    (hulocdiff.differentiableOn (by norm_num)).mono hρ₀sub
  have hcurry : (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        fderiv ℝ (fun y => G (q.1, y)) q.2)
      =ᶠ[𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀)]
      fun q => (fderiv ℝ G q).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin 9))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ₀)] with q hq
    have hd : DifferentiableAt ℝ G q :=
      hdiffball.differentiableAt (Metric.isOpen_ball.mem_nhds hq)
    exact (hd.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
  have hcomp_cont : Continuous fun L :
        (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)) →L[ℝ] EuclideanSpace ℝ (Fin 8) =>
      L.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin 9))) := by
    have h1 : Continuous fun L :
          (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)) →L[ℝ] EuclideanSpace ℝ (Fin 8) =>
        ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 9))
            (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9))
            (EuclideanSpace ℝ (Fin 8))) L)
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 8)) (EuclideanSpace ℝ (Fin 9))) :=
      (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 9))
        (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9))
        (EuclideanSpace ℝ (Fin 8))).continuous.clm_apply continuous_const
    simpa [ContinuousLinearMap.compL_apply] using h1
  have hpart : ContinuousAt (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      fderiv ℝ (fun y => G (q.1, y)) q.2) ((0 : EuclideanSpace ℝ (Fin 8)), x₀) :=
    (hcomp_cont.continuousAt.comp (hG.continuousAt_fderiv top_ne_zero')).congr hcurry.symm
  -- the base facts at `τ = 0`
  have hG0 : (fun y : EuclideanSpace ℝ (Fin 9) => G ((0 : EuclideanSpace ℝ (Fin 8)), y))
      = ppDiff (pC E x₀) (pC' E' x₀) E E' V W := by
    funext y
    simp only [G]
    rw [ppShift_zero_left Ξ hΞ0 w E, ppShift_zero_right Ξ hΞ0 w E']
  have h0full : Function.Surjective
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) => G ((0 : EuclideanSpace ℝ (Fin 8)), y)) x₀) := by
    rw [hG0]; exact hfull
  -- the neighbourhoods
  have hSres : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      ppRegion (pC E x₀) (pC' E' x₀) (ppShift Ξ w (unpackFst q.1) E)
        (ppShift Ξ w (unpackSnd q.1) E') V W q.2} ∈
      𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) := by
    have h1 : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) ∈ (chr (pC E x₀)).source} ∈
        𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) :=
      (continuous_ppShift_chain_apply Ξ hΞsm hw E hE).continuousAt.preimage_mem_nhds
        ((chr (pC E x₀)).open_source.mem_nhds hsrc.1)
    have h2 : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        V (ftY q.2) ∈ (chr (pC E x₀)).source} ∈
        𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) :=
      (continuous_V_ftY V hV).continuousAt.preimage_mem_nhds
        ((chr (pC E x₀)).open_source.mem_nhds hsrc.2.1)
    have h3 : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2) ∈ (chr (pC' E' x₀)).source} ∈
        𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) :=
      (continuous_ppShift_chain_apply' Ξ hΞsm hw E' hE').continuousAt.preimage_mem_nhds
        ((chr (pC' E' x₀)).open_source.mem_nhds hsrc.2.2.1)
    have h4 : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        W (ftZ q.2) ∈ (chr (pC' E' x₀)).source} ∈
        𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) :=
      (continuous_W_ftZ W hW).continuousAt.preimage_mem_nhds
        ((chr (pC' E' x₀)).open_source.mem_nhds hsrc.2.2.2)
    refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem h1 h2) h3) h4) ?_
    intro q hq
    exact ⟨hq.1.1.1, hq.1.1.2, hq.1.2, hq.2⟩
  have hSfull : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      Function.Surjective (fderiv ℝ (fun y => G (q.1, y)) q.2)} ∈
      𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) := by
    have hpre : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        Function.Surjective (fderiv ℝ (fun y => G (q.1, y)) q.2)}
        = (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            fderiv ℝ (fun y => G (q.1, y)) q.2) ⁻¹'
          {L : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8) |
            Function.Surjective L} := rfl
    rw [hpre]
    exact hpart.preimage_mem_nhds
      ((isOpen_setOf_surjective_clm_pp (E := EuclideanSpace ℝ (Fin 9))
        (F := EuclideanSpace ℝ (Fin 8))).mem_nhds h0full)
  have hSres_i : ∀ i ∈ I, {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
        (fderiv ℝ (fun y => G (q.1, y)) q.2) v.1)} ∈
      𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) := by
    intro i hi
    have h0res : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 9) =>
          G ((0 : EuclideanSpace ℝ (Fin 8)), y)) x₀) v.1) := by
      rw [hG0]; exact hres i hi
    have hpre : {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          (fderiv ℝ (fun y => G (q.1, y)) q.2) v.1)}
        = (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            fderiv ℝ (fun y => G (q.1, y)) q.2) ⁻¹'
          {L : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8) |
            Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} => L v.1)} := rfl
    rw [hpre]
    exact hpart.preimage_mem_nhds
      ((isOpen_setOf_surjective_domRestrict (m := 8) i).mem_nhds h0res)
  have hVnbhd : ({q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppRegion (pC E x₀) (pC' E' x₀) (ppShift Ξ w (unpackFst q.1) E)
          (ppShift Ξ w (unpackSnd q.1) E') V W q.2} ∩
      {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        Function.Surjective (fderiv ℝ (fun y => G (q.1, y)) q.2)} ∩
      (⋂ i ∈ I, {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          (fderiv ℝ (fun y => G (q.1, y)) q.2) v.1)})) ∈
      𝓝 ((0 : EuclideanSpace ℝ (Fin 8)), x₀) :=
    Filter.inter_mem (Filter.inter_mem hSres hSfull)
      ((Filter.biInter_finset_mem I).mpr hSres_i)
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ :=
    Filter.mem_prod_iff.mp (by rwa [nhds_prod_eq] at hVnbhd)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp ht₁
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.mem_nhds_iff.mp ht₂
  have hUsub : Metric.ball x₀ ε₂ ∩ Metric.ball x₀ ρ ⊆ Metric.ball x₀ ρ := Set.inter_subset_right
  refine ⟨ε, hε, Metric.ball x₀ ε₂ ∩ Metric.ball x₀ ρ, Metric.isOpen_ball.inter Metric.isOpen_ball,
    ⟨Metric.mem_ball_self hε₂, Metric.mem_ball_self hρ⟩, hUsub, ?_⟩
  intro τ hτ y hyU hymeet
  obtain ⟨hy1, hy2⟩ := hyU
  have hτmem : τ ∈ t₁ := hεsub (by rw [Metric.mem_ball, dist_eq_norm]; simpa using hτ)
  have hymem : y ∈ t₂ := hε₂sub hy1
  have hq := hsub (show (τ, y) ∈ t₁ ×ˢ t₂ from ⟨hτmem, hymem⟩)
  simp only [Set.mem_inter_iff, Set.mem_iInter] at hq
  have hresidQ : ppRegion (pC E x₀) (pC' E' x₀) (ppShift Ξ w (unpackFst τ) E)
      (ppShift Ξ w (unpackSnd τ) E') V W y := hq.1.1
  have hfullQ : Function.Surjective (fderiv ℝ (fun y' => G (τ, y')) y) := hq.1.2
  have hresQ : ∀ i ∈ I, Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
      (fderiv ℝ (fun y' => G (τ, y')) y) v.1) := fun i hi => hq.2 i hi
  have hEs : ContMDiff (𝓡 9) (𝓡 4) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w (unpackFst τ) E (ftS z) (ftU z)) :=
    contMDiff_chain_shift Ξ hΞsm hw (unpackFst τ) E hE
  have hEs' : ContMDiff (𝓡 9) (𝓡 4) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w (unpackSnd τ) E' (ftS z) (ftU z)) :=
    contMDiff_chain_shift Ξ hΞsm hw (unpackSnd τ) E' hE'
  have hVs : ContMDiff (𝓡 9) (𝓡 4) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) := contMDiff_V_ftY V hV
  have hWs : ContMDiff (𝓡 9) (𝓡 4) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) := contMDiff_W_ftZ W hW
  have hresidSelf : y ∈ ppRegion (pC (ppShift Ξ w (unpackFst τ) E) y)
      (pC' (ppShift Ξ w (unpackSnd τ) E') y) (ppShift Ξ w (unpackFst τ) E)
      (ppShift Ξ w (unpackSnd τ) E') V W := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mem_chart_source _ _
    · rw [← hymeet.2.1]
      exact mem_chart_source _ _
    · exact mem_chart_source _ _
    · rw [← hymeet.2.2]
      exact mem_chart_source _ _
  have hci := PPRegAt_chart_indep hEs hEs' hVs hWs hymeet hresidQ hresidSelf
  refine ⟨hci.1.mp hfullQ, ?_⟩
  intro hybdry
  obtain ⟨i, hiI, hgi, hgj⟩ := hforce y hy2 hybdry
  exact ⟨i, hgi, hgj, (hci.2 i hgi).mp (hresQ i hiI)⟩


/-! ## The target: the collar-boundary transfer -/

def Scollar (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (δ : ℝ) : Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | x ∈ ppMeet E E' V W ∧ (ftS x = δ ∨ ftS x = 1 - δ)}

lemma mem_Scollar {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {δ : ℝ} {x : EuclideanSpace ℝ (Fin 9)} :
    x ∈ Scollar E E' V W δ ↔ x ∈ ppMeet E E' V W ∧ (ftS x = δ ∨ ftS x = 1 - δ) :=
  Iff.rfl

theorem PPRegAt_ppShift_of_collarBoundary
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞsm : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {δ : ℝ}
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Work.Drive.ppMeet E E' V W,
      (Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x) →
      Work.Drive.PPRegAt E E' V W x) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < η →
      ∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
        (Work.Drive.ftS x = δ ∨ Work.Drive.ftS x = 1 - δ) →
        Work.Drive.PPRegAt (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W x := by
  classical
  -- every collar-boundary perturbed meet is a base meet
  have mem_S : ∀ (τ : EuclideanSpace ℝ (Fin 8)) (x : EuclideanSpace ℝ (Fin 9)),
      x ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W →
      (ftS x = δ ∨ ftS x = 1 - δ) → x ∈ Scollar E E' V W δ := fun τ x hx hc =>
    ⟨(ppMeet_ppShift_iff_of_closedCollar hΞ0 hwleft hwright τ E E' V W hc).mp hx, hc⟩
  -- the collar-boundary base meet set is compact
  have hScomp : IsCompact (Scollar E E' V W δ) := by
    refine (isCompact_unitBox 8).of_isClosed_subset ?_ ?_
    · have hZ : IsClosed (ppMeet E E' V W) := by
        rw [ppMeet_eq_Zpp_inter]
        exact (isClosed_Zpp E E' V W hE.continuous hE'.continuous hV.continuous
          hW.continuous).inter (isClosed_unitBox 8)
      have hftS : Continuous fun x : EuclideanSpace ℝ (Fin 9) => ftS x := by
        show Continuous fun x : EuclideanSpace ℝ (Fin 9) => x 0
        fun_prop
      have hcl : IsClosed {x : EuclideanSpace ℝ (Fin 9) | ftS x = δ ∨ ftS x = 1 - δ} := by
        rw [show {x : EuclideanSpace ℝ (Fin 9) | ftS x = δ ∨ ftS x = 1 - δ}
            = {x : EuclideanSpace ℝ (Fin 9) | ftS x = δ} ∪
              {x : EuclideanSpace ℝ (Fin 9) | ftS x = 1 - δ} from by
          ext x; simp]
        exact (isClosed_eq hftS continuous_const).union (isClosed_eq hftS continuous_const)
      exact hZ.inter hcl
    · intro x hx
      exact (mem_ppMeet.mp hx.1).1
  -- the local pieces
  have piece : ∀ x₀ : Scollar E E' V W δ, ∃ ε : ℝ, ∃ U : Set (EuclideanSpace ℝ (Fin 9)),
      0 < ε ∧ IsOpen U ∧ (x₀ : EuclideanSpace ℝ (Fin 9)) ∈ U ∧
      ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε → ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ U →
        y ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W →
        PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y := by
    intro x₀
    obtain ⟨hm, hc₀⟩ := mem_Scollar.mp x₀.2
    have hcollar : ftS (x₀ : EuclideanSpace ℝ (Fin 9)) ≤ δ ∨
        1 - δ ≤ ftS (x₀ : EuclideanSpace ℝ (Fin 9)) := by
      rcases hc₀ with h | h
      · exact Or.inl (le_of_eq h)
      · exact Or.inr (le_of_eq h.symm)
    have hbase : PPRegAt E E' V W (x₀ : EuclideanSpace ℝ (Fin 9)) := hregBase _ hm hcollar
    have hbasefull : Function.Surjective (fderiv ℝ (ppDiff (pC E (x₀ : EuclideanSpace ℝ (Fin 9)))
        (pC' E' (x₀ : EuclideanSpace ℝ (Fin 9))) E E' V W) (x₀ : EuclideanSpace ℝ (Fin 9))) :=
      hbase.1
    by_cases hb : ∃ i : Fin 9,
      ((x₀ : EuclideanSpace ℝ (Fin 9)) i = 0 ∨ (x₀ : EuclideanSpace ℝ (Fin 9)) i = 1)
    · -- the base point lies on the boundary of the box
      have hxbdry : (x₀ : EuclideanSpace ℝ (Fin 9)) ∈ Submission.Drive.unitBoxBdry 8 :=
        ⟨(mem_ppMeet.mp hm).1, hb⟩
      obtain ⟨i₀, hi₀, hoth₀, hres₀⟩ := hbase.2 hxbdry
      have hopen_i : IsOpen {y : EuclideanSpace ℝ (Fin 9) |
          ∀ j : Fin 9, j ≠ i₀ → y j ∈ Set.Ioo (0 : ℝ) 1} := by
        rw [show {y : EuclideanSpace ℝ (Fin 9) | ∀ j : Fin 9, j ≠ i₀ → y j ∈ Set.Ioo (0 : ℝ) 1}
            = ⋂ j ∈ (Finset.univ.erase i₀),
              {y : EuclideanSpace ℝ (Fin 9) | y j ∈ Set.Ioo (0 : ℝ) 1} from by
          ext y; simp [Finset.mem_erase]]
        exact isOpen_biInter_finset fun j _ =>
          isOpen_Ioo.preimage (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 9) => y j)
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hopen_i.mem_nhds hoth₀)
      have hresI : ∀ i ∈ ({i₀} : Finset (Fin 9)), Function.Surjective (fun v :
          {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (ppDiff (pC E (x₀ : EuclideanSpace ℝ (Fin 9)))
            (pC' E' (x₀ : EuclideanSpace ℝ (Fin 9))) E E' V W)
            (x₀ : EuclideanSpace ℝ (Fin 9)) v.1) := by
        intro i hi
        rw [Finset.mem_singleton] at hi
        subst hi
        exact hres₀
      have hforce : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Metric.ball (x₀ : EuclideanSpace ℝ (Fin 9)) ρ →
          y ∈ Submission.Drive.unitBoxBdry 8 →
          ∃ i ∈ ({i₀} : Finset (Fin 9)), (y i = 0 ∨ y i = 1) ∧
            ∀ j : Fin 9, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1 := by
        intro y hy hybdry
        obtain ⟨i, hi⟩ := hybdry.2
        by_cases hii : i = i₀
        · subst hii
          exact ⟨i, Finset.mem_singleton_self i, hi, fun j hj => hρsub hy j hj⟩
        · obtain ⟨h1, h2⟩ := hρsub hy i hii
          rcases hi with h | h
          · rw [h] at h1; exact absurd h1 (lt_irrefl 0)
          · rw [h] at h2; exact absurd h2 (lt_irrefl 1)
      obtain ⟨ε, hε, U, hUopen, hxU, hUsub, hprop⟩ :=
        ppRegAt_local Ξ hΞ0 hΞsm hE hE' hV hW hw hm hbasefull {i₀} hresI hρ hforce
      exact ⟨ε, U, hε, hUopen, hxU, hprop⟩
    · -- the base point is in the interior of the box
      have hall : ∀ j : Fin 9,
          (x₀ : EuclideanSpace ℝ (Fin 9)) j ∈ Set.Ioo (0 : ℝ) 1 := by
        intro j
        have h1 := (mem_ppMeet.mp hm).1 j
        exact ⟨lt_of_le_of_ne h1.1 (fun h => hb ⟨j, Or.inl h.symm⟩),
          lt_of_le_of_ne h1.2 (fun h => hb ⟨j, Or.inr h⟩)⟩
      have hopen_all : IsOpen {y : EuclideanSpace ℝ (Fin 9) |
          ∀ j : Fin 9, y j ∈ Set.Ioo (0 : ℝ) 1} := by
        rw [show {y : EuclideanSpace ℝ (Fin 9) | ∀ j : Fin 9, y j ∈ Set.Ioo (0 : ℝ) 1}
            = ⋂ j ∈ (Finset.univ : Finset (Fin 9)),
              {y : EuclideanSpace ℝ (Fin 9) | y j ∈ Set.Ioo (0 : ℝ) 1} from by
          ext y; simp]
        exact isOpen_biInter_finset fun j _ =>
          isOpen_Ioo.preimage (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 9) => y j)
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hopen_all.mem_nhds hall)
      have hforce : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Metric.ball (x₀ : EuclideanSpace ℝ (Fin 9)) ρ →
          y ∈ Submission.Drive.unitBoxBdry 8 →
          ∃ i ∈ (∅ : Finset (Fin 9)), (y i = 0 ∨ y i = 1) ∧
            ∀ j : Fin 9, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1 := by
        intro y hy hybdry
        exfalso
        obtain ⟨i, hi⟩ := hybdry.2
        obtain ⟨h1, h2⟩ := hρsub hy i
        rcases hi with h | h
        · rw [h] at h1; exact lt_irrefl 0 h1
        · rw [h] at h2; exact lt_irrefl 1 h2
      obtain ⟨ε, hε, U, hUopen, hxU, hUsub, hprop⟩ :=
        ppRegAt_local Ξ hΞ0 hΞsm hE hE' hV hW hw hm hbasefull ∅
          (fun i hi => absurd hi (Finset.notMem_empty i)) hρ hforce
      exact ⟨ε, U, hε, hUopen, hxU, hprop⟩
  choose ε₀ U₀ hrest using piece
  obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover U₀ (fun x₀ => (hrest x₀).2.1) fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hrest ⟨y, hy⟩).2.2.1⟩
  by_cases hSne : (Scollar E E' V W δ).Nonempty
  · obtain ⟨x₁, hx₁⟩ := hSne
    set t' : Finset (Scollar E E' V W δ) := insert ⟨x₁, hx₁⟩ t with ht'
    have ht'ne : t'.Nonempty := ⟨⟨x₁, hx₁⟩, Finset.mem_insert_self _ _⟩
    set η : ℝ := t'.inf' ht'ne (fun x₀ => ε₀ x₀) with hη
    have hηpos : 0 < η := by
      rw [hη]
      exact Finset.lt_inf'_iff ht'ne |>.mpr fun x₀ _ => (hrest x₀).1
    refine ⟨η, hηpos, fun τ hτ x hxmeet hcd => ?_⟩
    have hxS : x ∈ Scollar E E' V W δ := mem_S τ x hxmeet hcd
    have hcover' : Scollar E E' V W δ ⊆ ⋃ x₀ ∈ t', U₀ x₀ := fun y hy' => by
      obtain ⟨x₀, hx₀t, hxU⟩ := Set.mem_iUnion₂.mp (ht hy')
      exact Set.mem_iUnion₂.mpr ⟨x₀, Finset.mem_insert_of_mem hx₀t, hxU⟩
    obtain ⟨x₀, hx₀t', hxU⟩ := Set.mem_iUnion₂.mp (hcover' hxS)
    have hηε : η ≤ ε₀ x₀ := by
      rw [hη]
      exact Finset.inf'_le (fun x₀ => ε₀ x₀) hx₀t'
    exact (hrest x₀).2.2.2 τ (lt_of_lt_of_le hτ hηε) x hxU hxmeet
  · refine ⟨1, one_pos, fun τ hτ x hxmeet hcd => ?_⟩
    exact absurd (mem_S τ x hxmeet hcd) fun hmem => hSne ⟨x, hmem⟩

end

end Work.Drive.ppIntrinsic

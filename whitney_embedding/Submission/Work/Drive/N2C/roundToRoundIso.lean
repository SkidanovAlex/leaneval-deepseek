import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2C.isLevelIsotopy_blend
import Submission.Work.Drive.N2.roundConfigPath
import Submission.Work.Drive.N2.pictureOfConfig
import Submission.Work.Drive.N2Lead.levelCurvesReparamCinf

/-!
# `roundToRoundIso`: from one round picture of a level to another

This file proves `Work.Drive.N2C.roundToRoundIso`.  The statement is an assembly statement: given
two parametrisations `L`, `L'` of the same regular level `f = b` of a compact surface, related by
`L'.γ i x = L.γ (σ i) (h i x)` with `σ` a permutation of the labels and `h i` a monotone
reparametrisation with `h i (x + 1) = h i x + ε i`, `ε i = ± 1`, and two disjoint labelled round
configurations `D`, `D'`, there is a level isotopy (`IsLevelIsotopy f b`, i.e. a smooth family of
pictures of `f = b`) carrying the picture `D ∘ L` to the picture `D' ∘ L'`.

Two inputs come from the caller, exactly as in the statement: `hc` settles the *orientation
preserving* reparametrisation at a fixed round configuration, and `hfl` is Whitney's shell flip (a
family of ambient isotopies reversing a round circle about its centre and fixing a neighbourhood of
infinity); `hfl` is the statement of the proved `Work.Drive.N2C.shellFlip`.

The proof is a chain of four level isotopies (with `τ = σ⁻¹`, `θ i = ε (τ i) : ℝ`):

* `P₁` — moving the configuration `D` to the *stacked* configuration `stkCfg n` (coaxial circles of
  radius `1` at the heights `10 i`) along `L`: the placement isotopy
  `rtr_sameParam` (proved here, since the equally proved
  `rtr_sameParam` sits in a module carrying an unrelated stub);
* `P₂` — flipping the individual circles of the relabelled stacked configuration `labCfg τ` along
  the components on which `θ` is `-1`, with the ambient families produced by `hfl`; the circles of
  the relabelled stacked configuration are mutually at distance at least `9 > 3`, so each flip
  fixes all the other circles;
* `P₃` — the reparametrisation `hc`, instantiated on the flipped parametrisation
  `γ i x ↦ L.γ i (θ i * x)` and the relabelled `L'`;
* `P₄` — moving the stacked configuration to `D'` along `L'`, again by
  `rtr_sameParam`.

The pieces are glued with `glueLevelIsotopy` (a two-into-one concatenation built from
`isLevelIsotopy_blend` and the smooth step `rtr_smoothStep`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

noncomputable section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-! ## Smooth steps, time reversal and the single-configuration placement isotopy

These three tools are proved here so that the file rests only on complete modules: the equally
proved `roundToRound_sameParam` of `N2C/gapEngine.lean` sits in a module which carries an unrelated
development stub, and is therefore not imported. -/

/-- The smooth step `0` below `u` and `1` above `v` (for `u < v`). -/
noncomputable def rtr_smoothStep (u v : ℝ) : ℝ → ℝ :=
  fun s => Real.smoothTransition ((s - u) / (v - u))

lemma rtr_smoothStep_contDiff (u v : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rtr_smoothStep u v) := by
  unfold rtr_smoothStep
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma rtr_smoothStep_zero (u v : ℝ) (h : u < v) {s : ℝ} (hs : s ≤ u) :
    rtr_smoothStep u v s = 0 := by
  unfold rtr_smoothStep
  exact Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma rtr_smoothStep_one (u v : ℝ) (h : u < v) {s : ℝ} (hs : v ≤ s) :
    rtr_smoothStep u v s = 1 := by
  unfold rtr_smoothStep
  refine Real.smoothTransition.one_of_one_le ?_
  rw [one_le_div (by linarith)]
  linarith

/-- Reversing a level isotopy in time. -/
theorem rtr_rev {f : M → ℝ} {b : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : IsLevelIsotopy f b e) : IsLevelIsotopy f b (fun s y => e (1 - s) y) :=
  isLevelIsotopy_comp_time he (ρ := fun s : ℝ => 1 - s) (by fun_prop)

/-- **The placement isotopy at a fixed parametrisation.**  Two disjoint round configurations read
through the same parametrisation of a regular level are joined by a level isotopy: `roundConfigPath`
supplies the path of configurations and `roundConfigPictureGlobal` the jointly smooth picture
family. -/
theorem rtr_sameParam {f : M → ℝ}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n : ℕ} (L : LevelCurves f b n) {D D' : Work.Drive.N2.RoundConfig n}
    (hD : D.Disjoint) (hD' : D'.Disjoint) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
      (∀ (i : Fin n) (x : ℝ), e 0 (L.γ i x) = D.circle i x) ∧
      (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x) = D'.circle i x) := by
  obtain ⟨Dp, hDp0, hDp1, -, -, hDpd, hDppos, hDprad, hDpph⟩ :=
    Work.Drive.N2.roundConfigPath D D' hD hD'
  obtain ⟨P, hPc, hPinj, hPimm, hPsm⟩ :=
    Work.Drive.N2.roundConfigPictureGlobal (f := f) (b := b) (n := n) L.γ hf hreg L.sm L.val
      L.per L.injIco L.cover L.disj L.ker hDpd hDppos hDprad hDpph
  refine ⟨P, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s y _
    exact hPsm.contMDiffAt
  · intro s x y hx hy hxy
    obtain ⟨i, t, rfl⟩ := L.cover x hx
    obtain ⟨j, u, rfl⟩ := L.cover y hy
    exact hPinj s _ _ ⟨i, t, rfl⟩ ⟨j, u, rfl⟩ hxy
  · intro s y hy v hv hv'
    obtain ⟨i, t, rfl⟩ := L.cover y hy
    exact hPimm s _ ⟨i, t, rfl⟩ v hv hv'
  · intro i x
    rw [hPc 0 i x, hDp0]
  · intro i x
    rw [hPc 1 i x, hDp1]


/-! ## Two round configurations with coaxial circles at the heights `10 i` -/

/-- The stacked configuration: `n` coaxial circles of radius `1` at the heights `10 i`. -/
def stkCfg (n : ℕ) : Work.Drive.N2.RoundConfig n where
  pos := fun i => Work.Drive.N2.rcMk 0 0 (10 * ((i : ℕ) : ℝ))
  rad := fun _ => 1
  hrad := fun _ => one_pos
  phase := fun _ => 0

/-- The stacked configuration relabelled by `τ`: the `i`-th circle is the `τ i`-th one. -/
def labCfg {n : ℕ} (τ : Fin n → Fin n) : Work.Drive.N2.RoundConfig n where
  pos := fun i => Work.Drive.N2.rcMk 0 0 (10 * ((τ i : ℕ) : ℝ))
  rad := fun _ => 1
  hrad := fun _ => one_pos
  phase := fun _ => 0

@[simp] lemma stkCfg_pos (n : ℕ) (i : Fin n) :
    (stkCfg n).pos i = Work.Drive.N2.rcMk 0 0 (10 * ((i : ℕ) : ℝ)) := rfl
@[simp] lemma stkCfg_rad (n : ℕ) (i : Fin n) : (stkCfg n).rad i = 1 := rfl
@[simp] lemma stkCfg_phase (n : ℕ) (i : Fin n) : (stkCfg n).phase i = 0 := rfl
@[simp] lemma labCfg_pos {n : ℕ} (τ : Fin n → Fin n) (i : Fin n) :
    (labCfg τ).pos i = Work.Drive.N2.rcMk 0 0 (10 * ((τ i : ℕ) : ℝ)) := rfl
@[simp] lemma labCfg_rad {n : ℕ} (τ : Fin n → Fin n) (i : Fin n) : (labCfg τ).rad i = 1 := rfl
@[simp] lemma labCfg_phase {n : ℕ} (τ : Fin n → Fin n) (i : Fin n) : (labCfg τ).phase i = 0 := rfl

/-- `rcZ` is additive for the difference. -/
lemma rtr_rcZ_sub (a b : EuclideanSpace ℝ (Fin 3)) :
    Work.Drive.N2.rcZ (a - b) = Work.Drive.N2.rcZ a - Work.Drive.N2.rcZ b :=
  map_sub _ _ _

/-- The stacked configuration is disjoint. -/
lemma stkCfg_disjoint (n : ℕ) : (stkCfg n).Disjoint := by
  intro i j hij s t hEq
  have h1 : Work.Drive.N2.rcZ ((stkCfg n).circle i s) = 10 * ((i : ℕ) : ℝ) := by
    rw [Work.Drive.N2.rcZ_circle]
    simp only [stkCfg_pos]
    rw [Work.Drive.N2.rcZ_mk]
  have h2 : Work.Drive.N2.rcZ ((stkCfg n).circle j t) = 10 * ((j : ℕ) : ℝ) := by
    rw [Work.Drive.N2.rcZ_circle]
    simp only [stkCfg_pos]
    rw [Work.Drive.N2.rcZ_mk]
  rw [hEq] at h1
  have hcast : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
  exact hij (Fin.ext (Nat.cast_injective hcast))

/-- The relabelled stacked configuration is disjoint along an injective relabelling. -/
lemma labCfg_disjoint {n : ℕ} {τ : Fin n → Fin n} (hτ : Function.Injective τ) :
    (labCfg τ).Disjoint := by
  intro i j hij s t hEq
  have h1 : Work.Drive.N2.rcZ ((labCfg τ).circle i s) = 10 * ((τ i : ℕ) : ℝ) := by
    rw [Work.Drive.N2.rcZ_circle]
    simp only [labCfg_pos]
    rw [Work.Drive.N2.rcZ_mk]
  have h2 : Work.Drive.N2.rcZ ((labCfg τ).circle j t) = 10 * ((τ j : ℕ) : ℝ) := by
    rw [Work.Drive.N2.rcZ_circle]
    simp only [labCfg_pos]
    rw [Work.Drive.N2.rcZ_mk]
  rw [hEq] at h1
  have hcast : ((τ i : ℕ) : ℝ) = ((τ j : ℕ) : ℝ) := by linarith
  exact hij (hτ (Fin.ext (Nat.cast_injective hcast)))

/-- Circles of the relabelled stacked configuration are at distance at least `9`, hence every other
circle stays outside the ball of radius `3` about a given centre. -/
lemma labCfg_sep {n : ℕ} {τ : Fin n → Fin n} (hτ : Function.Injective τ)
    {i j : Fin n} (hij : i ≠ j) (x : ℝ) : 3 < ‖(labCfg τ).circle i x - (labCfg τ).pos j‖ := by
  have hZle : |Work.Drive.N2.rcZ ((labCfg τ).pos i - (labCfg τ).pos j)|
      ≤ ‖(labCfg τ).pos i - (labCfg τ).pos j‖ := by
    have h := PiLp.norm_apply_le (p := 2) (x := (labCfg τ).pos i - (labCfg τ).pos j)
      (i := (2 : Fin 3))
    simpa [Work.Drive.N2.rcZ, Real.norm_eq_abs] using h
  have hZval : Work.Drive.N2.rcZ ((labCfg τ).pos i - (labCfg τ).pos j)
      = 10 * ((τ i : ℕ) : ℝ) - 10 * ((τ j : ℕ) : ℝ) := by
    rw [rtr_rcZ_sub]
    simp only [labCfg_pos, Work.Drive.N2.rcZ_mk]
  have hne : ((τ i : ℕ) : ℝ) ≠ ((τ j : ℕ) : ℝ) := by
    intro hc
    exact hij (hτ (Fin.ext (Nat.cast_injective hc)))
  have h1 : (1 : ℝ) ≤ |((τ i : ℕ) : ℝ) - ((τ j : ℕ) : ℝ)| := by
    rcases Nat.lt_or_gt_of_ne (fun hc => hne (by exact_mod_cast hc)) with hh | hh
    · have h2 : (((τ i : ℕ) + 1 : ℕ) : ℝ) ≤ ((τ j : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hh
      push_cast at h2
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h2 : (((τ j : ℕ) + 1 : ℕ) : ℝ) ≤ ((τ i : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hh
      push_cast at h2
      rw [abs_of_nonneg (by linarith)]
      linarith
  have h10 : (10 : ℝ) ≤ |Work.Drive.N2.rcZ ((labCfg τ).pos i - (labCfg τ).pos j)| := by
    rw [hZval, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
    linarith
  have hnorm : ‖(labCfg τ).circle i x - (labCfg τ).pos i‖ = 1 := by
    rw [Work.Drive.N2.norm_circle_sub]
    rfl
  have htri : ‖(labCfg τ).pos i - (labCfg τ).pos j‖
      ≤ ‖(labCfg τ).pos i - (labCfg τ).circle i x‖
        + ‖(labCfg τ).circle i x - (labCfg τ).pos j‖ := by
    have hsum : (labCfg τ).pos i - (labCfg τ).pos j
        = ((labCfg τ).pos i - (labCfg τ).circle i x)
          + ((labCfg τ).circle i x - (labCfg τ).pos j) := by abel
    rw [hsum]
    exact norm_add_le _ _
  have habs : ‖(labCfg τ).pos i - (labCfg τ).circle i x‖ = 1 := by
    rw [norm_sub_rev]; exact hnorm
  linarith

/-- The derivative of `x ↦ c * u x`. -/
lemma rtr_deriv_constMul (c : ℝ) {u : ℝ → ℝ} {x : ℝ} (hu : DifferentiableAt ℝ u x) :
    deriv (fun y : ℝ => c * u y) x = c * deriv u x :=
  (hu.hasDerivAt.const_mul c).deriv

/-! ## Reindexing and flipping a level parametrisation -/

/-- Reindexing the components of a parametrisation of a level by a bijection. -/
def LevelCurves.reindexBy {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n)
    (τ : Fin n → Fin n) (hτ : Function.Bijective τ) : LevelCurves f b n where
  γ := fun i => L.γ (τ i)
  sm := fun i => L.sm (τ i)
  val := fun i x => L.val (τ i) x
  per := fun i x => L.per (τ i) x
  injIco := fun i => L.injIco (τ i)
  modOne := fun i x y hxy => L.modOne (τ i) x y hxy
  cover := fun x hx => by
    obtain ⟨i, t, ht⟩ := L.cover x hx
    obtain ⟨j, hj⟩ := hτ.2 i
    exact ⟨j, t, by rw [hj]; exact ht⟩
  disj := fun i j hij => L.disj (τ i) (τ j) (fun h => hij (hτ.1 h))
  ker := fun i x v hv => L.ker (τ i) x v hv

/-- Flipping the parametrisation of each component (`x ↦ ε i * x`) keeps a level parametrisation. -/
theorem rtr_flipParam {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n)
    (ε' : Fin n → ℤ) (hε' : ∀ i : Fin n, ε' i = 1 ∨ ε' i = -1) :
    ∃ L' : LevelCurves f b n, ∀ (i : Fin n) (x : ℝ), L'.γ i x = L.γ i ((ε' i : ℝ) * x) := by
  obtain ⟨L', hL'⟩ := Work.Drive.N2Lead.levelCurvesReparamCinf (u := b) L
    (h := fun i x => (ε' i : ℝ) * x) (δ := fun i => (ε' i : ℝ))
    (fun i => by rcases hε' i with hh | hh <;> simp [hh])
    (fun i => by fun_prop)
    (fun i x y hxy => by
      have hc : (ε' i : ℝ) ≠ 0 := by rcases hε' i with hh | hh <;> simp [hh]
      exact mul_left_cancel₀ hc hxy)
    (fun i y => ⟨y / (ε' i : ℝ), by
      have hc : (ε' i : ℝ) ≠ 0 := by rcases hε' i with hh | hh <;> simp [hh]
      field_simp⟩)
    (fun i x => by
      have hc : (ε' i : ℝ) ≠ 0 := by rcases hε' i with hh | hh <;> simp [hh]
      have hder : HasDerivAt (fun y : ℝ => (ε' i : ℝ) * y) (ε' i : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (ε' i : ℝ)
      rw [hder.deriv]
      exact hc)
    (fun i x => by ring)
  exact ⟨L', hL'⟩

/-! ## Gluing two level isotopies -/

/-- **Concatenation of two level isotopies.**  If `e₁` and `e₂` are level isotopies whose middle
pictures agree on the level, they can be concatenated into a single level isotopy with the ends of
`e₁` and `e₂`. -/
theorem rtr_glue {f : M → ℝ} {b : ℝ} {e₁ e₂ : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    (h₁ : IsLevelIsotopy f b e₁) (h₂ : IsLevelIsotopy f b e₂)
    (hmid : ∀ y : M, f y = b → e₁ 1 y = e₂ 0 y) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
      (∀ y : M, e 0 y = e₁ 0 y) ∧ (∀ y : M, e 1 y = e₂ 1 y) := by
  have h413 : (1:ℝ)/4 < 1/3 := by norm_num
  have h1254 : (1:ℝ)/2 < 3/4 := by norm_num
  have h13 : (1:ℝ)/3 < 1/2 := by norm_num
  have hê₁ : IsLevelIsotopy f b (fun s => e₁ (rtr_smoothStep (1/4) (1/3) s)) :=
    isLevelIsotopy_comp_time h₁ (rtr_smoothStep_contDiff _ _)
  have hê₂ : IsLevelIsotopy f b (fun s => e₂ (rtr_smoothStep (1/2) (3/4) s)) :=
    isLevelIsotopy_comp_time h₂ (rtr_smoothStep_contDiff _ _)
  obtain ⟨e, heiso, hel, her⟩ := isLevelIsotopy_blend (f := f) hf hreg hê₁ hê₂ h13
    (by
      intro s hs y hy
      rw [rtr_smoothStep_one (1/4) (1/3) h413 hs.1,
        rtr_smoothStep_zero (1/2) (3/4) h1254 hs.2, hmid y hy])
  refine ⟨e, heiso, ?_, ?_⟩
  · intro y
    rw [hel 0 (by norm_num), rtr_smoothStep_zero (1/4) (1/3) h413 (by norm_num)]
  · intro y
    rw [her 1 (by norm_num), rtr_smoothStep_one (1/2) (3/4) h1254 (by norm_num)]

/-! ## The flip piece -/

/-- **The flip piece.**  Starting from any picture `A` of the level read through `L` from the
configuration `C` (whose circles are at pairwise distance more than `3 * C.rad`), applying the
ambient family `F i` of Whitney flips in the components on which `θ` is `-1` gives a level isotopy
carrying the picture `A` to the picture in which those circles are traversed backwards. -/
theorem rtr_flipPiece {f : M → ℝ} {b : ℝ} {n : ℕ} (L : LevelCurves f b n)
    (C : Work.Drive.N2.RoundConfig n)
    (A : M → EuclideanSpace ℝ (Fin 3))
    (hAval : ∀ (i : Fin n) (x : ℝ), A (L.γ i x) = C.circle i x)
    (hAiso : IsLevelIsotopy f b (fun _ : ℝ => A))
    (F : Fin n → ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hFsm : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (F i)))
    (hFinj : ∀ (i : Fin n) (s : ℝ), Function.Injective (F i s))
    (hFimm : ∀ (i : Fin n) (s : ℝ) (w : EuclideanSpace ℝ (Fin 3)),
      Function.Injective (fderiv ℝ (F i s) w))
    (hF0 : ∀ (i : Fin n) (v : EuclideanSpace ℝ (Fin 3)), F i 0 v = v)
    (hF1 : ∀ (i : Fin n) (t : ℝ),
      F i 1 (C.pos i + C.rad i • Work.Drive.N2.roundPic t)
        = C.pos i + C.rad i • Work.Drive.N2.roundPic (-t))
    (hFfix : ∀ (i : Fin n) (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)),
      3 * C.rad i < ‖v - C.pos i‖ → F i s v = v)
    (hsep : ∀ (i j : Fin n), i ≠ j → ∀ x : ℝ, 3 * C.rad j < ‖C.circle i x - C.pos j‖)
    (hphase : ∀ i : Fin n, C.phase i = 0)
    (θ : Fin n → ℝ) (hθ : ∀ i : Fin n, θ i = 1 ∨ θ i = -1) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
      (∀ y : M, f y = b → e 0 y = A y) ∧
      (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x) = C.circle i (θ i * x)) := by
  classical
  have key : ∀ S : Finset (Fin n), (∀ i ∈ S, θ i = -1) →
      ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
        (∀ y : M, f y = b → e 0 y = A y) ∧
        (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x)
          = C.circle i ((if i ∈ S then (-1 : ℝ) else 1) * x)) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro _
      refine ⟨fun _ => A, hAiso, fun y _ => rfl, ?_⟩
      intro i x
      rw [if_neg (Finset.notMem_empty i), one_mul]
      exact hAval i x
    | insert i₀ S hi₀ ih =>
      intro hS
      have hS' : ∀ i ∈ S, θ i = -1 := fun i hi => hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨e, heiso, he0, he1⟩ := ih hS'
      refine ⟨fun s y => F i₀ s (e s y), ?_, ?_, ?_⟩
      · exact isLevelIsotopy_ambient_contDiff heiso (hFsm i₀) (hFinj i₀) (hFimm i₀)
      · intro y hy
        show F i₀ 0 (e 0 y) = A y
        rw [he0 y hy, hF0 i₀]
      · intro j x
        change F i₀ 1 (e 1 (L.γ j x))
          = C.circle j ((if j ∈ insert i₀ S then (-1 : ℝ) else 1) * x)
        rw [he1 j x]
        by_cases hji : j = i₀
        · rw [hji]
          have hχS : (if i₀ ∈ S then (-1 : ℝ) else 1) = 1 := by rw [if_neg hi₀]
          have hχI : (if i₀ ∈ insert i₀ S then (-1 : ℝ) else 1) = -1 := by
            rw [if_pos (Finset.mem_insert_self i₀ S)]
          rw [hχS, one_mul, hχI, neg_one_mul]
          have hc1 : C.circle i₀ x
              = C.pos i₀ + C.rad i₀ • Work.Drive.N2.roundPic (2 * Real.pi * x) := by
            rw [Work.Drive.N2.RoundConfig.circle, hphase i₀, zero_add]
          have hc2 : C.circle i₀ (-x)
              = C.pos i₀ + C.rad i₀ • Work.Drive.N2.roundPic (-(2 * Real.pi * x)) := by
            rw [Work.Drive.N2.RoundConfig.circle, hphase i₀, zero_add, mul_neg]
          rw [hc1, hF1 i₀ (2 * Real.pi * x), hc2]
        · have hχ : (if j ∈ insert i₀ S then (-1 : ℝ) else 1)
              = (if j ∈ S then (-1 : ℝ) else 1) := by
            simp only [Finset.mem_insert, hji, false_or]
          rw [hχ]
          have hfix := hFfix i₀ 1 (C.circle j ((if j ∈ S then (-1 : ℝ) else 1) * x))
            (hsep j i₀ hji ((if j ∈ S then (-1 : ℝ) else 1) * x))
          rw [hfix]
  have hS₀ : ∀ i ∈ (Finset.univ.filter (fun i : Fin n => θ i = -1)), θ i = -1 := by
    intro i hi
    simpa using hi
  obtain ⟨e, heiso, he0, he1⟩ := key (Finset.univ.filter (fun i : Fin n => θ i = -1)) hS₀
  refine ⟨e, heiso, he0, ?_⟩
  intro i x
  rw [he1 i x]
  congr 1
  by_cases h : i ∈ Finset.univ.filter (fun i : Fin n => θ i = -1)
  · have hti : θ i = -1 := by simpa using h
    rw [if_pos h, hti]
  · have hti : θ i = 1 := by
      rcases hθ i with h1 | h1
      · exact h1
      · exact absurd (by simpa using h1) h
    rw [if_neg h, hti]


/-! ## The main theorem -/

theorem roundToRoundIso {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n : ℕ} (L L' : Work.Drive.N2C.LevelCurves f b n)
    {D D' : Work.Drive.N2.RoundConfig n} (hD : D.Disjoint) (hD' : D'.Disjoint)
    (σ : Fin n → Fin n) (hσ : Function.Bijective σ) (h : Fin n → ℝ → ℝ) (ε : Fin n → ℤ)
    (hε : ∀ i : Fin n, ε i = 1 ∨ ε i = -1)
    (hcd : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i))
    (hper : ∀ (i : Fin n) (x : ℝ), h i (x + 1) = h i x + (ε i : ℝ))
    (hmono : ∀ (i : Fin n) (x : ℝ), 0 < (ε i : ℝ) * deriv (h i) x)
    (hrel : ∀ (i : Fin n) (x : ℝ), L'.γ i x = L.γ (σ i) (h i x))
    (hc : ∀ (L₁ L₂ : Work.Drive.N2C.LevelCurves f b n) (Dc : Work.Drive.N2.RoundConfig n),
      Dc.Disjoint → ∀ (h' : Fin n → ℝ → ℝ),
      (∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h' i)) →
      (∀ (i : Fin n) (x : ℝ), h' i (x + 1) = h' i x + 1) →
      (∀ (i : Fin n) (x : ℝ), 0 < deriv (h' i) x) →
      (∀ (i : Fin n) (x : ℝ), L₂.γ i x = L₁.γ i (h' i x)) →
      ∃ e₁ : ℝ → M → EuclideanSpace ℝ (Fin 3), Work.Drive.N2C.IsLevelIsotopy f b e₁ ∧
        (∀ (i : Fin n) (x : ℝ), e₁ 0 (L₂.γ i x) = Dc.circle i x) ∧
        (∀ (i : Fin n) (x : ℝ), e₁ 1 (L₁.γ i x) = Dc.circle i x))
    (hfl : ∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
      ∃ F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) ∧
        (∀ s : ℝ, Function.Injective (F s)) ∧
        (∀ (s : ℝ) (w : EuclideanSpace ℝ (Fin 3)), Function.Injective (fderiv ℝ (F s) w)) ∧
        (∀ v : EuclideanSpace ℝ (Fin 3), F 0 v = v) ∧
        (∀ t : ℝ, F 1 (c + r • Work.Drive.N2.roundPic t) = c + r • Work.Drive.N2.roundPic (-t)) ∧
        (∀ (s : ℝ) (v : EuclideanSpace ℝ (Fin 3)), 3 * r < ‖v - c‖ → F s v = v)) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), Work.Drive.N2C.IsLevelIsotopy f b e ∧
      (∀ (i : Fin n) (x : ℝ), e 0 (L.γ i x) = D.circle i x) ∧
      (∀ (i : Fin n) (x : ℝ), e 1 (L'.γ i x) = D'.circle i x) := by
  classical
  -- the inverse relabelling
  obtain ⟨τ, hτσ, hστ⟩ : ∃ τ : Fin n → Fin n, (∀ j, τ (σ j) = j) ∧ (∀ i, σ (τ i) = i) := by
    choose τ hτ using hσ.2
    exact ⟨τ, fun j => hσ.1 (hτ (σ j)), hτ⟩
  have hτinj : Function.Injective τ := fun a b hab => by rw [← hστ a, hab, hστ b]
  have hτsurj : Function.Surjective τ := fun j => ⟨σ j, hτσ j⟩
  have hτbij : Function.Bijective τ := ⟨hτinj, hτsurj⟩
  -- the sign attached to the label `i` of `L`
  set θ : Fin n → ℝ := fun i => (ε (τ i) : ℝ) with hθdef
  have hθ : ∀ i : Fin n, θ i = 1 ∨ θ i = -1 := fun i => by
    simp only [hθdef]
    rcases hε (τ i) with hh | hh <;> simp [hh]
  have hθsq : ∀ i : Fin n, θ i * θ i = 1 := fun i => by rcases hθ i with hh | hh <;> simp [hh]
  have hθeq : ∀ i : Fin n, ((((fun i' => ε (τ i')) i : ℤ)) : ℝ) = θ i := fun i => rfl
  -- the parametrisation with the flipped components
  obtain ⟨Lflip, hLflip⟩ := rtr_flipParam L (fun i => ε (τ i)) (fun i => hε (τ i))
  -- the relabelled `L'`
  set Lr : Work.Drive.N2C.LevelCurves f b n := L'.reindexBy τ hτbij with hLrdef
  have hLrγ : ∀ i x, Lr.γ i x = L'.γ (τ i) x := fun i x => rfl
  have hLrγ2 : ∀ i x, Lr.γ i x = L.γ i (h (τ i) x) := by
    intro i x
    rw [hLrγ i x, hrel (τ i) x, hστ i]
  -- the picture of the stacked configuration along `L`
  obtain ⟨A, hAsm, hAval, hAinj, hAimm⟩ :=
    Work.Drive.N2.exists_picture_of_config (b := b) (n := n) L.γ hf hreg L.sm L.val L.per
      L.injIco L.cover L.disj L.ker (labCfg τ) (labCfg_disjoint hτinj)
  have hAiso : Work.Drive.N2C.IsLevelIsotopy f b (fun _ : ℝ => A) :=
    isLevelIsotopy_const
      (fun y _ => hAsm.contMDiffAt)
      (fun x y hx hy hxy => hAinj x y (L.cover x hx) (L.cover y hy) hxy)
      (fun y hy v hv hw => hAimm y (L.cover y hy) v hv hw)
  -- the flip families supplied by `hfl`
  choose F hF using fun i : Fin n =>
    hfl ((labCfg τ).pos i) ((labCfg τ).rad i) ((labCfg τ).hrad i)
  -- `P₁`: the placement isotopy along `L`, `D ↦ labCfg τ`
  obtain ⟨e₁, he₁iso, he₁0, he₁1⟩ :=
    rtr_sameParam (f := f) hf hreg L (D := D) (D' := labCfg τ) hD
      (labCfg_disjoint hτinj)
  -- `P₂`: the flips
  obtain ⟨e₂, he₂iso, he₂0, he₂1⟩ :=
    rtr_flipPiece L (labCfg τ) A hAval hAiso F
      (fun i => (hF i).1) (fun i s => (hF i).2.1 s) (fun i s w => (hF i).2.2.1 s w)
      (fun i v => (hF i).2.2.2.1 v) (fun i t => (hF i).2.2.2.2.1 t)
      (fun i s v hv => (hF i).2.2.2.2.2 s v hv)
      (fun i j hij x => by
        have hle := labCfg_sep hτinj hij x
        simpa using hle)
      (fun i => rfl) θ hθ
  -- `P₃`: the reparametrisation supplied by `hc`
  obtain ⟨e₃, he₃iso, he₃0, he₃1⟩ :=
    hc Lflip Lr (labCfg τ) (labCfg_disjoint hτinj) (fun i x => θ i * h (τ i) x)
      (fun i => by
        have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h (τ i)) := hcd (τ i)
        simpa [smul_eq_mul] using h1.const_smul (θ i))
      (fun i x => by
        have h1 : h (τ i) (x + 1) = h (τ i) x + θ i := hper (τ i) x
        calc θ i * h (τ i) (x + 1) = θ i * (h (τ i) x + θ i) := by rw [h1]
          _ = θ i * h (τ i) x + 1 := by rw [mul_add, hθsq i])
      (fun i x => by
        have hder : deriv (fun y : ℝ => θ i * h (τ i) y) x = θ i * deriv (h (τ i)) x :=
          rtr_deriv_constMul (θ i) (((hcd (τ i)).differentiable (by simp)).differentiableAt)
        rw [hder]
        exact hmono (τ i) x)
      (fun i x => by
        rw [hLrγ2 i x, hLflip i (θ i * h (τ i) x), hθeq i]
        congr 1
        rw [← mul_assoc, hθsq i, one_mul])
  -- `P₄`: the placement isotopy along `L'`, `stkCfg n ↦ D'`
  obtain ⟨e₄, he₄iso, he₄0, he₄1⟩ :=
    rtr_sameParam (f := f) hf hreg L' (D := stkCfg n) (D' := D')
      (stkCfg_disjoint n) hD'
  -- the interfaces
  have h12 : ∀ y : M, f y = b → e₁ 1 y = e₂ 0 y := by
    intro y hy
    obtain ⟨i, x, rfl⟩ := L.cover y hy
    rw [he₁1 i x, he₂0 (L.γ i x) (L.val i x), hAval i x]
  have h23 : ∀ y : M, f y = b → e₂ 1 y = e₃ 1 y := by
    intro y hy
    obtain ⟨i, x, rfl⟩ := Lflip.cover y hy
    rw [he₃1 i x, hLflip i x, hθeq i, he₂1 i (θ i * x)]
    congr 1
    rw [← mul_assoc, hθsq i, one_mul]
  have h34 : ∀ y : M, f y = b → e₃ 0 y = e₄ 0 y := by
    intro y hy
    obtain ⟨i, x, rfl⟩ := Lr.cover y hy
    rw [he₃0 i x]
    have hpt : Lr.γ i x = L'.γ (τ i) x := rfl
    rw [hpt, he₄0 (τ i) x]
    simp only [Work.Drive.N2.RoundConfig.circle, labCfg, stkCfg]
  -- the concatenation
  obtain ⟨e₁₂, h₁₂iso, h₁₂l, h₁₂r⟩ := rtr_glue (f := f) hf hreg he₁iso he₂iso h12
  have h₂₃ : ∀ y : M, f y = b → e₁₂ 1 y = (fun s y => e₃ (1 - s) y) 0 y := by
    intro y hy
    rw [h₁₂r y]
    simpa using h23 y hy
  obtain ⟨e₁₂₃, h₁₂₃iso, h₁₂₃l, h₁₂₃r⟩ :=
    rtr_glue (f := f) hf hreg h₁₂iso (rtr_rev he₃iso) h₂₃
  have h₃₄ : ∀ y : M, f y = b → e₁₂₃ 1 y = e₄ 0 y := by
    intro y hy
    rw [h₁₂₃r y]
    simpa using h34 y hy
  obtain ⟨e, heiso, hel, her⟩ := rtr_glue (f := f) hf hreg h₁₂₃iso he₄iso h₃₄
  refine ⟨e, heiso, ?_, ?_⟩
  · intro i x
    rw [hel (L.γ i x), h₁₂₃l (L.γ i x), h₁₂l (L.γ i x)]
    exact he₁0 i x
  · intro i x
    rw [her (L'.γ i x), he₄1 i x]

end

end Work.Drive.N2C

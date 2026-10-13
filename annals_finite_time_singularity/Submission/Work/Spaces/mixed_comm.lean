import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-! ## The open set on which `SmoothNbhd` is stated

`SmoothNbhd f` says that the uncurried `f` is smooth on an open neighbourhood of the
closed quadrant.  For the commutation of the operators `D_z = z ∂_z` and
`D_θ = sin(2θ) ∂_θ` we only ever need smoothness on that open set, so it is convenient
to give it a name. -/

/-- The open set `(-1,∞) × (-1, π/2+1)` on which `SmoothNbhd` is formulated. -/
def nbhU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)

lemma isOpen_nbhU : IsOpen nbhU := isOpen_Ioi.prod isOpen_Ioo

lemma mem_nbhU {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) : (z, θ) ∈ nbhU := by
  rw [Iz, Set.mem_Ici] at hz
  rw [Iθ, Set.mem_Icc] at hθ
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · rw [Set.mem_Ioi]; linarith
  · rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith [Real.pi_pos]⟩

/-! ## Slice derivatives and the derivative of the uncurried function

The partial derivative in `z` (at fixed `θ`) of `f : ℝ → ℝ → ℝ` is the derivative of
the slice of `Function.uncurry f`, and it is the first derivative of the uncurried
function in the direction `(1,0)`.  Similarly in `θ`. -/

lemma deriv_slice_fst (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : DifferentiableAt ℝ F (z,θ)) :
    deriv (fun z' => F (z',θ)) z = fderiv ℝ F (z,θ) (1,0) := by
  have h2 : HasFDerivAt (fun t : ℝ => (t, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  have h3 : HasDerivAt (fun t : ℝ => F (t, θ))
      ((fderiv ℝ F (z,θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) z :=
    (h.hasFDerivAt.comp z h2).hasDerivAt
  rw [h3.deriv]; simp

lemma deriv_slice_snd (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : DifferentiableAt ℝ F (z,θ)) :
    deriv (fun θ' => F (z,θ')) θ = fderiv ℝ F (z,θ) (0,1) := by
  have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun t : ℝ => F (z, t))
      ((fderiv ℝ F (z,θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
    (h.hasFDerivAt.comp θ h2).hasDerivAt
  rw [h3.deriv]; simp

/-- The second mixed slice derivative `∂_z ∂_θ` is the second differential of the
uncurried function evaluated on `((1,0),(0,1))`. -/
lemma deriv_deriv_fst_snd (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : ContDiffAt ℝ 2 F (z,θ)) :
    deriv (fun z' => deriv (fun θ' => F (z',θ')) θ) z
      = (fderiv ℝ (fderiv ℝ F) (z,θ) (1,0)) (0,1) := by
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ F) (z,θ) :=
    (ContDiffAt.fderiv_right h (by norm_num : (1:WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hnd : ∀ᶠ y in 𝓝 (z,θ), DifferentiableAt ℝ F y :=
    (ContDiffAt.eventually h (by decide : (2:WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hslice : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ F (z',θ) :=
    (Continuous.prodMk_left θ).continuousAt.eventually hnd
  have hcongr : (fun z' => deriv (fun θ' => F (z',θ')) θ) =ᶠ[𝓝 z]
      (fun z' => fderiv ℝ F (z',θ) (0,1)) := by
    filter_upwards [hslice] with z' hz'
    have h2 : HasFDerivAt (fun t : ℝ => (z', t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
      hasFDerivAt_prodMk_right z' θ
    have h3 : HasDerivAt (fun t : ℝ => F (z', t))
        ((fderiv ℝ F (z',θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
      (hz'.hasFDerivAt.comp θ h2).hasDerivAt
    rw [h3.deriv]; simp
  rw [hcongr.deriv_eq]
  let Φ : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (0,1)
  have hΦ : Φ = (ContinuousLinearMap.apply ℝ ℝ (0,1)) ∘ (fderiv ℝ F) := by
    funext y; simp only [Φ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hΦdiff : DifferentiableAt ℝ Φ (z,θ) := by
    rw [hΦ]; exact (ContinuousLinearMap.differentiableAt _).comp _ hfd_diff
  have stepA : deriv (fun z' => Φ (z',θ)) z = fderiv ℝ Φ (z,θ) (1,0) := by
    have h2 : HasFDerivAt (fun t : ℝ => (t, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
      hasFDerivAt_prodMk_left z θ
    have h3 : HasDerivAt (fun t : ℝ => Φ (t, θ))
        ((fderiv ℝ Φ (z,θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) z := by
      convert (hΦdiff.hasFDerivAt.comp z h2).hasDerivAt using 1
      · ext t; rfl
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    rw [h3.deriv]; simp
  have hΦderiv : fderiv ℝ Φ (z,θ) =
      (ContinuousLinearMap.apply ℝ ℝ (0,1)) ∘SL fderiv ℝ (fderiv ℝ F) (z,θ) := by
    conv_lhs => rw [hΦ]
    rw [fderiv_comp (z,θ) (ContinuousLinearMap.differentiableAt _) hfd_diff]
    rw [ContinuousLinearMap.fderiv]
  rw [stepA, hΦderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-- The second mixed slice derivative `∂_θ ∂_z` is the second differential of the
uncurried function evaluated on `((0,1),(1,0))`. -/
lemma deriv_deriv_snd_fst (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : ContDiffAt ℝ 2 F (z,θ)) :
    deriv (fun θ' => deriv (fun z' => F (z',θ')) z) θ
      = (fderiv ℝ (fderiv ℝ F) (z,θ) (0,1)) (1,0) := by
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ F) (z,θ) :=
    (ContDiffAt.fderiv_right h (by norm_num : (1:WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hnd : ∀ᶠ y in 𝓝 (z,θ), DifferentiableAt ℝ F y :=
    (ContDiffAt.eventually h (by decide : (2:WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hslice : ∀ᶠ θ' in 𝓝 θ, DifferentiableAt ℝ F (z,θ') :=
    (Continuous.prodMk_right z).continuousAt.eventually hnd
  have hcongr : (fun θ' => deriv (fun z' => F (z',θ')) z) =ᶠ[𝓝 θ]
      (fun θ' => fderiv ℝ F (z,θ') (1,0)) := by
    filter_upwards [hslice] with θ' hθ'
    have h2 : HasFDerivAt (fun t : ℝ => (t, θ')) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
      hasFDerivAt_prodMk_left z θ'
    have h3 : HasDerivAt (fun t : ℝ => F (t, θ'))
        ((fderiv ℝ F (z,θ')) (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) z :=
      (hθ'.hasFDerivAt.comp z h2).hasDerivAt
    rw [h3.deriv]; simp
  rw [hcongr.deriv_eq]
  let Φ : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (1,0)
  have hΦ : Φ = (ContinuousLinearMap.apply ℝ ℝ (1,0)) ∘ (fderiv ℝ F) := by
    funext y; simp only [Φ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hΦdiff : DifferentiableAt ℝ Φ (z,θ) := by
    rw [hΦ]; exact (ContinuousLinearMap.differentiableAt _).comp _ hfd_diff
  have stepA : deriv (fun θ' => Φ (z,θ')) θ = fderiv ℝ Φ (z,θ) (0,1) := by
    have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
      hasFDerivAt_prodMk_right z θ
    have h3 : HasDerivAt (fun t : ℝ => Φ (z, t))
        ((fderiv ℝ Φ (z,θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ := by
      convert (hΦdiff.hasFDerivAt.comp θ h2).hasDerivAt using 1
      · ext t; rfl
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [h3.deriv]; simp
  have hΦderiv : fderiv ℝ Φ (z,θ) =
      (ContinuousLinearMap.apply ℝ ℝ (1,0)) ∘SL fderiv ℝ (fderiv ℝ F) (z,θ) := by
    conv_lhs => rw [hΦ]
    rw [fderiv_comp (z,θ) (ContinuousLinearMap.differentiableAt _) hfd_diff]
    rw [ContinuousLinearMap.fderiv]
  rw [stepA, hΦderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-! ## Clairaut's theorem for the curvilinear derivatives -/

/-- The two iterated slice derivatives of a `C²` function agree (Clairaut/Schwarz). -/
lemma pz_pth_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z,θ)) :
    pz (pth f) z θ = pth (pz f) z θ := by
  have h1 := deriv_deriv_fst_snd (Function.uncurry f) z θ h
  have h2 := deriv_deriv_snd_fst (Function.uncurry f) z θ h
  have hsym := (ContDiffAt.isSymmSndFDerivAt h (by simp : minSmoothness ℝ 2 ≤ 2)).eq (1,0) (0,1)
  change deriv (fun z' => deriv (fun θ' => (Function.uncurry f) (z',θ')) θ) z
      = deriv (fun θ' => deriv (fun z' => (Function.uncurry f) (z',θ')) z) θ
  rw [h1, h2]
  exact hsym

/-- The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` commute at any point where the
function is `C²`. -/
lemma Dz_Dth_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z,θ)) :
    Dz (Dth f) z θ = Dth (Dz f) z θ := by
  show z * pz (Dth f) z θ = Real.sin (2*θ) * pth (Dz f) z θ
  have h1 : pz (Dth f) z θ = Real.sin (2*θ) * pz (pth f) z θ := by
    show deriv (fun z' => Real.sin (2*θ) * pth f z' θ) z = Real.sin (2*θ) * pz (pth f) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : pth (Dz f) z θ = z * pth (pz f) z θ := by
    show deriv (fun θ' => z * pz f z θ') θ = z * pth (pz f) z θ
    rw [deriv_const_mul_field]
    rfl
  rw [h1, h2, pz_pth_comm h]
  ring

/-! ## `SmoothNbhd` is preserved by `D_z`, `D_θ` and their iterates -/

lemma SmoothNbhd.Dz {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (Dz f) := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) nbhU :=
    ContDiffOn.fderiv_of_isOpen h isOpen_nbhU (by simp)
  have hev : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (1,0)) nbhU :=
    hfd.clm_apply contDiffOn_const
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      y.1 * (fderiv ℝ (Function.uncurry f) y) (1,0)) nbhU :=
    (contDiff_fst.contDiffOn).mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = (fderiv ℝ (Function.uncurry f) y) (1,0) := deriv_slice_fst _ _ _ hdiff
  show y.1 * deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = y.1 * (fderiv ℝ (Function.uncurry f) y) (1,0)
  rw [hderiv]

lemma SmoothNbhd.Dth {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (Dth f) := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) nbhU :=
    ContDiffOn.fderiv_of_isOpen h isOpen_nbhU (by simp)
  have hev : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (0,1)) nbhU :=
    hfd.clm_apply contDiffOn_const
  have hsin : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => Real.sin (2 * y.2)) nbhU :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      Real.sin (2*y.2) * (fderiv ℝ (Function.uncurry f) y) (0,1)) nbhU := hsin.mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = (fderiv ℝ (Function.uncurry f) y) (0,1) := deriv_slice_snd _ _ _ hdiff
  show Real.sin (2*y.2) * deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = Real.sin (2*y.2) * (fderiv ℝ (Function.uncurry f) y) (0,1)
  rw [hderiv]

lemma SmoothNbhd.DzIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ n : ℕ, SmoothNbhd (DzIter n f)
  | 0 => h
  | n+1 => SmoothNbhd.Dz (SmoothNbhd.DzIter h n)

lemma SmoothNbhd.DthIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ n : ℕ, SmoothNbhd (DthIter n f)
  | 0 => h
  | n+1 => SmoothNbhd.Dth (SmoothNbhd.DthIter h n)

/-! ## Congruence of `pz`, `pth`, `Dz`, `Dth` under equality on `nbhU` -/

lemma pz_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) {z θ : ℝ}
    (hz : (z,θ) ∈ nbhU) : pz g z θ = pz g' z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ nbhU :=
    (Continuous.prodMk_left θ).continuousAt.eventually (isOpen_nbhU.mem_nhds hz)
  have hslice : (fun z' => Function.uncurry g (z',θ)) =ᶠ[𝓝 z]
      (fun z' => Function.uncurry g' (z',θ)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [pz, Function.uncurry] using this

lemma pth_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) {z θ : ℝ}
    (hz : (z,θ) ∈ nbhU) : pth g z θ = pth g' z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ nbhU :=
    (Continuous.prodMk_right z).continuousAt.eventually (isOpen_nbhU.mem_nhds hz)
  have hslice : (fun θ' => Function.uncurry g (z,θ')) =ᶠ[𝓝 θ]
      (fun θ' => Function.uncurry g' (z,θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have := hslice.deriv_eq
  simpa only [pth, Function.uncurry] using this

lemma Dz_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) :
    EqOn (Function.uncurry (Dz g)) (Function.uncurry (Dz g')) nbhU := by
  intro y hy
  have hp := pz_congr h hy
  show y.1 * pz g y.1 y.2 = y.1 * pz g' y.1 y.2
  rw [hp]

lemma Dth_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) :
    EqOn (Function.uncurry (Dth g)) (Function.uncurry (Dth g')) nbhU := by
  intro y hy
  have hp := pth_congr h hy
  show Real.sin (2*y.2) * pth g y.1 y.2 = Real.sin (2*y.2) * pth g' y.1 y.2
  rw [hp]

lemma DzIter_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) (j : ℕ) :
    EqOn (Function.uncurry (DzIter j g)) (Function.uncurry (DzIter j g')) nbhU := by
  induction j with
  | zero => exact h
  | succ j ih => exact Dz_congr ih

/-! ## The commutation identities on `nbhU` -/

lemma Dz_Dth_comm_eqOn {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    EqOn (Function.uncurry (Dz (Dth f))) (Function.uncurry (Dth (Dz f))) nbhU := by
  intro y hy
  exact Dz_Dth_comm ((ContDiffOn.contDiffAt h (isOpen_nbhU.mem_nhds hy)).of_le (by norm_num))

/-- A single `D_θ` can be moved across any iterate of `D_z`. -/
lemma Dth_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (b : ℕ) :
    EqOn (Function.uncurry (Dth (DzIter b f))) (Function.uncurry (DzIter b (Dth f))) nbhU := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Dz (Dth (DzIter b f)) y.1 y.2 = Dth (Dz (DzIter b f)) y.1 y.2 :=
        Dz_Dth_comm_eqOn (SmoothNbhd.DzIter h b) hy
      have hpz := pz_congr ih hy
      show Dth (Dz (DzIter b f)) y.1 y.2 = Dz (DzIter b (Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * pz (Dth (DzIter b f)) y.1 y.2 = y.1 * pz (DzIter b (Dth f)) y.1 y.2
      rw [hpz]

/-- The iterates of `D_θ` can be moved across any iterate of `D_z`. -/
lemma DthIter_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (b i : ℕ) :
    EqOn (Function.uncurry (DthIter i (DzIter b f))) (Function.uncurry (DzIter b (DthIter i f))) nbhU := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Dth (DthIter i (DzIter b f)) y.1 y.2 = Dth (DzIter b (DthIter i f)) y.1 y.2 :=
        Dth_congr ih hy
      have hstep : Dth (DzIter b (DthIter i f)) y.1 y.2 = DzIter b (Dth (DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn (SmoothNbhd.DthIter h i) b hy
      show Dth (DthIter i (DzIter b f)) y.1 y.2 = DzIter b (Dth (DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-! ## Composition of the iterates -/

lemma DthIter_add_right (i a : ℕ) (f : ℝ → ℝ → ℝ) :
    DthIter i (DthIter a f) = DthIter (i + a) f := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [show (i + 1) + a = (i + a) + 1 from Nat.succ_add i a]
      show Dth (DthIter i (DthIter a f)) = Dth (DthIter (i + a) f)
      rw [ih]

lemma DzIter_add_right (j b : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter (j + b) f = DzIter j (DzIter b f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show (j + 1) + b = (j + b) + 1 from Nat.succ_add j b]
      show Dz (DzIter (j + b) f) = Dz (DzIter j (DzIter b f))
      rw [ih]

theorem mixed_comm (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (j i b a : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed j i (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (j + b) (i + a) g z θ := by
  have hy : (z, θ) ∈ nbhU := mem_nbhU hz hθ
  have hga : SmoothNbhd (DthIter a g) := SmoothNbhd.DthIter hg a
  have e1 : DzIter j (DthIter i (DzIter b (DthIter a g))) z θ
      = DzIter j (DzIter b (DthIter i (DthIter a g))) z θ :=
    (DzIter_congr (DthIter_DzIter_comm_eqOn hga b i) j) hy
  have e3 : DzIter j (DzIter b (DthIter (i + a) g)) = DzIter (j + b) (DthIter (i + a) g) :=
    (DzIter_add_right j b (DthIter (i + a) g)).symm
  show DzIter j (DthIter i (DzIter b (DthIter a g))) z θ
      = DzIter (j + b) (DthIter (i + a) g) z θ
  rw [e1]
  rw [DthIter_add_right]
  rw [e3]

end Work.Spaces

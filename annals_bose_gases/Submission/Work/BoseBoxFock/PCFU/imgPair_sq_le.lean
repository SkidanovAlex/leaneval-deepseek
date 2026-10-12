import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.chiScale_mul_boxRestrictR_kcInsN
import Submission.Work.BoseBoxFock.PCFU.imgDualShift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.imgPair_sq_le`

The **`χ`-localised, lattice-image, one-slot pairing bound**: for a `W₁`-kernel whose argument is
shifted by the image `ℓ • latVec mm` and reflected, paired against the `χ_ℓ`-windowed `i`-th slot
of the box state

    Φ_i(y) := χ_ℓ(y) · boxRestrictR ℓ Φ (kcInsN m i (y, r)) ,

the squared modulus of the pairing is dominated by the `64 π (a v)`-multiple of the Dirichlet
energy of the *windowed slot* `y ↦ χ_ℓ(y)·Φ(kcInsN m i (y,r))`:

    ‖∫_y χ_ℓ(y)·W₁(r_{j'} − y + ℓ•latVec mm)·Φ_i(y) dy‖²  ≤  64π(a v)·∑_k ∫_u ‖∂_k(χ_ℓ·Φ_i)‖² .

## Proof

1. **The shift is a reflection.**  With `c := r j' + ℓ • latVec mm` the identity
   `r j' − y + ℓ•latVec mm = c − y` (`abel`) puts the kernel in the reflected form `W₁(c − y)`.

2. **The box restriction is invisible under the window.**  `chiScale_mul_boxRestrictR_kcInsN`
   (a sibling module) gives the *pointwise* identity
   `χ_ℓ(u)·boxRestrictR ℓ Φ (kcInsN m i (u,r)) = χ_ℓ(u)·Φ(kcInsN m i (u,r))`:
   either the inserted configuration is in the box (so the indicator is `1`), or else the offending
   coordinate is the inserted one, hence `u ∉ acube ℓ` and the window `χ_ℓ` vanishes (it is
   supported in `acube ℓ`, by `chiScale_mem_acube`).

3. **Duality at a shifted kernel.**  `imgDualShift` (sibling module: the reflection substitution
   `y ↦ c − y`, the `W₁`-instance `coulombDual_W1_le` of the Coulomb duality, and the invariance
   `dirichlet_comp_const_sub` of the Dirichlet energy under reflection) bounds the pairing by
   `64π(a v)·∑_k ∫ ‖∂_k Ψ‖²` for the complexified windowed slot
   `Ψ = (· : ℂ) ∘ (u ↦ χ_ℓ(u)·Φ(kcInsN m i (u,r)))`.

4. **The complexification of a real function.**  `norm_fderiv_ofReal_comp` (below) identifies
   `‖fderiv ℝ ((·:ℂ) ∘ G) v e‖ = ‖fderiv ℝ G v e‖` (the Fréchet derivative of `Complex.ofRealCLM ∘ G`
   is `Complex.ofRealCLM.comp (fderiv ℝ G v)`, and `ofRealCLM` preserves norms), which converts the
   right-hand side of step 3 into the target's.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The one-slot insertion `z ↦ kcInsN m i (z, r)` is smooth.  (Proved here to keep this module's
import cone small: `kcInsN m i (·, r)` is `Function.update (kcInsN m i (0,r)) i`, whose smoothness is
`contDiff_update`.) -/
lemma contDiff_kcInsN_ins {m : ℕ} (i : Fin (m + 1)) (r : Submission.BoseGases.X m) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => Submission.BoseGases.kcInsN m i (z, r)) := by
  have hEq : (fun z : E3 => Submission.BoseGases.kcInsN m i (z, r))
      = fun z : E3 => Function.update (Submission.BoseGases.kcInsN m i (0, r)) i z := by
    funext y
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Submission.BoseGases.kc_insN_apply_same]
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [Function.update_apply]
      simp [Submission.BoseGases.kc_insN_apply_succ, Fin.succAbove_ne]
  rw [hEq]
  exact contDiff_update (⊤ : ℕ∞) (Submission.BoseGases.kcInsN m i (0, r)) i

/-- **The complexification does not change the norm of the Fréchet derivative.**  Since
`Complex.ofRealCLM` is a linear isometry (`‖(r : ℂ)‖ = ‖r‖`), the derivative of
`(· : ℂ) ∘ G` at `v` is `Complex.ofRealCLM.comp (fderiv ℝ G v)`, so both sides have the same
operator values. -/
lemma norm_fderiv_ofReal_comp {G : E3 → ℝ} (hG : ContDiff ℝ 1 G) (v e : E3) :
    ‖fderiv ℝ (fun v : E3 => ((G v : ℝ) : ℂ)) v e‖ = ‖fderiv ℝ G v e‖ := by
  have hGd : HasFDerivAt G (fderiv ℝ G v) v :=
    (hG.differentiable (by norm_num) v).hasFDerivAt
  have h1 : HasFDerivAt (fun v : E3 => ((G v : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ G v)) v := by
    have h := (Complex.ofRealCLM.hasFDerivAt (x := G v)).comp v hGd
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using h
  rw [h1.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.norm_real]

/-- **The `χ`-windowed, lattice-image, one-slot pairing bound.**  See the module docstring. -/
theorem imgPair_sq_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {m : ℕ} (i : Fin (m + 1)) (j' : Fin m)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (mm : Fin 3 → ℤ) {r : Submission.BoseGases.X m}
    (hr : r ∈ Submission.BoseGases.abox m ℓ) :
    ‖∫ y : EuclideanSpace ℝ (Fin 3),
        ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((Work.BoseFixR.W1fun v h ℓ (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.boxRestrictR ℓ Φ
                (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ)‖ ^ 2
      ≤ 64 * Real.pi * BoseGases.a v
        * ∑ k : Fin 3, ∫ u : EuclideanSpace ℝ (Fin 3),
            ‖fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) =>
                Submission.BoseGases.chiScale ℓ u
                  * Φ (Submission.BoseGases.kcInsN m i (u, r))) u
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := by
  -- ## 1. the kernel argument is a reflection about `c := r j' + ℓ • latVec mm`
  have hshift : ∀ y : E3, r j' - y + ℓ • Work.BoseBoxFock.latVec mm
      = (r j' + ℓ • Work.BoseBoxFock.latVec mm) - y := by
    intro y
    abel
  -- ## 2. the windowed slot is smooth
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 =>
      Submission.BoseGases.chiScale ℓ u * Φ (Submission.BoseGases.kcInsN m i (u, r))) := by
    refine (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).mul ?_
    exact hΦ.comp (contDiff_kcInsN_ins i r)
  -- ## 3. the pairing in the reflected form, with the box restriction absorbed by the window
  have hL : (∫ y : E3, ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (r j' - y + ℓ • Work.BoseBoxFock.latVec mm) : ℝ) : ℂ)
        * ((Work.BoseBoxFock.boxRestrictR ℓ Φ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ))
      = ∫ y : E3,
        ((Work.BoseFixR.W1fun v h ℓ ((r j' + ℓ • Work.BoseBoxFock.latVec mm) - y) : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ y
            * Φ (Submission.BoseGases.kcInsN m i (y, r)) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hshift y, ← chiScale_mul_boxRestrictR_kcInsN i hℓ hr y]
    push_cast
    ring
  rw [hL]
  -- ## 4. the duality bound at the reflected kernel, with the complexified smooth slot
  have hΨc : ContDiff ℝ (⊤ : ℕ∞) (fun u : E3 =>
      ((Submission.BoseGases.chiScale ℓ u
        * Φ (Submission.BoseGases.kcInsN m i (u, r)) : ℝ) : ℂ)) := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hGc
  have hΨs : HasCompactSupport (fun u : E3 =>
      ((Submission.BoseGases.chiScale ℓ u
        * Φ (Submission.BoseGases.kcInsN m i (u, r)) : ℝ) : ℂ)) := by
    refine HasCompactSupport.mono (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)) ?_
    intro u hu
    exact fun hχ => hu (by simp [hχ])
  refine (imgDualShift (v := v) (h := h) (R := R) (ℓ := ℓ) hR hv hvrad hv_supp hℓ hRℓ
    (r j' + ℓ • Work.BoseBoxFock.latVec mm) hΨc hΨs).trans ?_
  -- ## 5. the Dirichlet energy of the complexification is that of the real slot
  have hsum : (∑ k : Fin 3, ∫ u : E3,
        ‖fderiv ℝ (fun u : E3 => ((Submission.BoseGases.chiScale ℓ u
            * Φ (Submission.BoseGases.kcInsN m i (u, r)) : ℝ) : ℂ)) u
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      = ∑ k : Fin 3, ∫ u : E3,
        ‖fderiv ℝ (fun u : E3 => Submission.BoseGases.chiScale ℓ u
            * Φ (Submission.BoseGases.kcInsN m i (u, r))) u
          (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    apply integral_congr_ae
    filter_upwards with u
    rw [norm_fderiv_ofReal_comp (hGc.of_le (by norm_num)) u (EuclideanSpace.single k (1 : ℝ))]
  rw [hsum]

end Work.BoseBoxFock.PCFU

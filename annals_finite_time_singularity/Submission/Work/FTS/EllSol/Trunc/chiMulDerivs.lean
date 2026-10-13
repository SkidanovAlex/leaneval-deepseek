/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Derivative identities for the truncated datum `g_N = chi N · g`

The truncation `Work.FTS.EllSol.Trunc.chi` of `Submission/Work/FTS/EllSol/Trunc/Defs.lean` is
used in `Trunc.Pass` to reduce `flat2DAgmon` to its compactly-supported case.  The passage
needs the pointwise product rules for the operators `∂_z`, `∂_θ` (here `Work.Spaces.pz`,
`Work.Spaces.pth`) applied to `fun t θ => chi N t * g t θ`:

* `∂_z(chi · g) = (∂_z chi) g + chi ∂_z g`,
* `∂_z²(chi · g) = (∂_z² chi) g + 2 (∂_z chi)(∂_z g) + chi ∂_z² g`,
* `∂_θ(chi · g) = chi ∂_θ g`,  `∂_θ²(chi · g) = chi ∂_θ² g`,
* and `∂_z ∂_θ (chi · g) = ∂_z ∂_θ g` on the *interior* of the plateau `|t| < N`.

All are elementary consequences of `deriv_mul` / `deriv_const_mul` once the relevant slices
are differentiable.  The slice differentiability is extracted from the hypothesis
`ContDiffOn ℝ 2 (uncurry g) (univ ×ˢ Ioo 0 (π/2))` (the set is *open*, so `ContDiffOn` at a
point of it is honest `ContDiffAt`), together with the smoothness of `chi` (`chi_contDiff`).

The file is organised as

* `contDiffOn_uncurry_pz_succ`, `contDiffOn_uncurry_pth_succ` — the finite-order analogue of
  `Work.Spaces.contDiffOn_uncurry_pz`/`_pth` (which are stated only for order `⊤`);
* `curry_differentiableAt_of_contDiffOn` — differentiability of the two curried slices from
  differentiability of the uncurried function;
* `pz_mul_slice`, `pz_pz_mul_slice`, `pth_mul_slice`, `pz_pth_mul_slice`, `pth_pth_mul_slice`
  — the product rules for a `θ`-independent left factor `c`;
* `chi_deriv_eq_zero` — `chi` is locally constant `1` on `|t| < N`, so `deriv (chi N) = 0`
  there;
* `chiMulDerivs` — the requested statement.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.Trunc.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Slice differentiability -/

/-- The `z`-partial of a function of class `C^{n+1}` on an open set is of class `C^n` there.
Finite-order version of `Work.Spaces.contDiffOn_uncurry_pz`. -/
theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a function of class `C^{n+1}` on an open set is of class `C^n` there.
Finite-order version of `Work.Spaces.contDiffOn_uncurry_pth`. -/
theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- Both curried slices of a function of class `C^n` (`n > 0`) on an open set are
differentiable at every point of the set. -/
theorem curry_differentiableAt_of_contDiffOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (hn : 0 < n) (h : ContDiffOn ℝ n (Function.uncurry G) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => G z' θ) z ∧ DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    (h.contDiffAt (hV.mem_nhds hmem)).differentiableAt (by simpa using hn.ne')
  exact ⟨Work.Spaces.differentiableAt_curry_left hd, Work.Spaces.differentiableAt_curry_right hd⟩

/-! ## Product rules for a `θ`-independent left factor -/

/-- `∂_z(c · f) = (∂_z c) f + c ∂_z f` for a function `c` of the single variable `z`. -/
theorem pz_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hc : DifferentiableAt ℝ c t) (hf : DifferentiableAt ℝ (fun s => f s θ) t) :
    Work.Spaces.pz (fun s θ => c s * f s θ) t θ
      = deriv c t * f t θ + c t * Work.Spaces.pz f t θ := by
  show deriv (fun s => c s * f s θ) t = deriv c t * f t θ + c t * deriv (fun s => f s θ) t
  rw [show (fun s => c s * f s θ) = c * (fun s => f s θ) from rfl, deriv_mul hc hf]

/-- `∂_z²(c · f) = (∂_z² c) f + 2 (∂_z c)(∂_z f) + c ∂_z² f`. -/
theorem pz_pz_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hc : Differentiable ℝ c) (hc1 : Differentiable ℝ (deriv c))
    (hf : Differentiable ℝ (fun s => f s θ))
    (hf1 : Differentiable ℝ (fun s => Work.Spaces.pz f s θ)) :
    Work.Spaces.pz (Work.Spaces.pz (fun s θ => c s * f s θ)) t θ
      = deriv (deriv c) t * f t θ + 2 * deriv c t * Work.Spaces.pz f t θ
        + c t * Work.Spaces.pz (Work.Spaces.pz f) t θ := by
  have hpt : (fun s => Work.Spaces.pz (fun s θ => c s * f s θ) s θ)
      = fun s => deriv c s * f s θ + c s * Work.Spaces.pz f s θ :=
    funext fun s => pz_mul_slice c f s θ (hc s) (hf s)
  show deriv (fun s => Work.Spaces.pz (fun s θ => c s * f s θ) s θ) t
    = deriv (deriv c) t * f t θ + 2 * deriv c t * Work.Spaces.pz f t θ
      + c t * Work.Spaces.pz (Work.Spaces.pz f) t θ
  rw [hpt]
  rw [show (fun s => deriv c s * f s θ + c s * Work.Spaces.pz f s θ)
      = (deriv c * (fun s => f s θ)) + (c * (fun s => Work.Spaces.pz f s θ)) from rfl]
  rw [deriv_add ((hc1 t).mul (hf t)) ((hc t).mul (hf1 t))]
  rw [deriv_mul (hc1 t) (hf t), deriv_mul (hc t) (hf1 t)]
  simp only [Work.Spaces.pz]
  ring

/-- `∂_θ(c · f) = c ∂_θ f` for a `θ`-independent factor `c`. -/
theorem pth_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hf : DifferentiableAt ℝ (fun θ' => f t θ') θ) :
    Work.Spaces.pth (fun s θ => c s * f s θ) t θ = c t * Work.Spaces.pth f t θ := by
  show deriv (fun θ' => c t * f t θ') θ = c t * deriv (fun θ' => f t θ') θ
  rw [deriv_const_mul (c t) hf]

/-- `∂_z ∂_θ(c · f) = (∂_z c)(∂_θ f) + c ∂_z ∂_θ f`. -/
theorem pz_pth_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hc : DifferentiableAt ℝ c t) (hf : ∀ s, DifferentiableAt ℝ (fun θ' => f s θ') θ)
    (hf1 : DifferentiableAt ℝ (fun s => Work.Spaces.pth f s θ) t) :
    Work.Spaces.pz (Work.Spaces.pth (fun s θ => c s * f s θ)) t θ
      = deriv c t * Work.Spaces.pth f t θ + c t * Work.Spaces.pz (Work.Spaces.pth f) t θ := by
  have hpt : (fun s => Work.Spaces.pth (fun s θ => c s * f s θ) s θ)
      = fun s => c s * Work.Spaces.pth f s θ :=
    funext fun s => pth_mul_slice c f s θ (hf s)
  show deriv (fun s => Work.Spaces.pth (fun s θ => c s * f s θ) s θ) t
    = deriv c t * Work.Spaces.pth f t θ + c t * Work.Spaces.pz (Work.Spaces.pth f) t θ
  rw [hpt]
  rw [show (fun s => c s * Work.Spaces.pth f s θ) = c * (fun s => Work.Spaces.pth f s θ) from rfl,
      deriv_mul hc hf1]
  simp only [Work.Spaces.pz]

/-- `∂_θ²(c · f) = c ∂_θ² f`. -/
theorem pth_pth_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hf : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2), DifferentiableAt ℝ (fun θ'' => f t θ'') θ')
    (hf1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f t θ') θ) :
    Work.Spaces.pth (Work.Spaces.pth (fun s θ => c s * f s θ)) t θ
      = c t * Work.Spaces.pth (Work.Spaces.pth f) t θ := by
  have hpt : (fun θ' => Work.Spaces.pth (fun s θ => c s * f s θ) t θ')
      =ᶠ[𝓝 θ] (fun θ' => c t * Work.Spaces.pth f t θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact pth_mul_slice c f t θ' (hf θ' hθ')
  show deriv (fun θ' => Work.Spaces.pth (fun s θ => c s * f s θ) t θ') θ
    = c t * Work.Spaces.pth (Work.Spaces.pth f) t θ
  rw [hpt.deriv_eq]
  rw [deriv_const_mul (c t) hf1]
  simp only [Work.Spaces.pth]

/-- On the plateau `|t| < N` the cutoff `chi N` is locally constant `1`, so its derivative
vanishes there. -/
theorem chi_deriv_eq_zero {N t : ℝ} (hN : 0 < N) (h : |t| < N) : deriv (chi N) t = 0 := by
  have hopen : IsOpen {s : ℝ | |s| < N} := isOpen_lt continuous_abs continuous_const
  have hev : chi N =ᶠ[𝓝 t] (fun _ : ℝ => (1:ℝ)) := by
    filter_upwards [hopen.mem_nhds (show t ∈ {s : ℝ | |s| < N} from h)] with s hs
    exact chi_eq_one hN (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-! ## The requested identities -/

theorem chiMulDerivs (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) (N : ℝ) :
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (fun t θ => chi N t * g t θ) t θ
        = deriv (chi N) t * g t θ + chi N t * Work.Spaces.pz g t θ)
    ∧ (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.pz (fun t θ => chi N t * g t θ)) t θ
        = deriv (deriv (chi N)) t * g t θ + 2 * deriv (chi N) t * Work.Spaces.pz g t θ
          + chi N t * Work.Spaces.pz (Work.Spaces.pz g) t θ)
    ∧ (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (fun t θ => chi N t * g t θ) t θ = chi N t * Work.Spaces.pth g t θ)
    ∧ (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (Work.Spaces.pth (fun t θ => chi N t * g t θ)) t θ
        = chi N t * Work.Spaces.pth (Work.Spaces.pth g) t θ)
    ∧ (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ∈ Set.Ioo (-N) N →
      Work.Spaces.pz (Work.Spaces.pth (fun t θ => chi N t * g t θ)) t θ
        = Work.Spaces.pz (Work.Spaces.pth g) t θ) := by
  have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_univ.prod isOpen_Ioo
  have hm : ∀ (t θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (t, θ) ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun t θ hθ => ⟨mem_univ t, hθ⟩
  -- `∂_z g` and `∂_θ g` are of class `C¹` on the open strip
  have hPzC : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz g))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_uncurry_pz_succ hU 1 hg
  have hPthC : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth g))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_uncurry_pth_succ hU 1 hg
  -- differentiability of the slices
  have hGz : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → Differentiable ℝ (fun s => g s θ) :=
    fun θ hθ s => (curry_differentiableAt_of_contDiffOn hU (n := 2) (by norm_num) hg
      (hm s θ hθ)).1
  have hGθ : ∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      DifferentiableAt ℝ (fun θ' => g t θ') θ :=
    fun t θ hθ => (curry_differentiableAt_of_contDiffOn hU (n := 2) (by norm_num) hg
      (hm t θ hθ)).2
  have hPzg : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Differentiable ℝ (fun s => Work.Spaces.pz g s θ) :=
    fun θ hθ s => (curry_differentiableAt_of_contDiffOn hU (n := 1) (by norm_num) hPzC
      (hm s θ hθ)).1
  have hPthz : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Differentiable ℝ (fun s => Work.Spaces.pth g s θ) :=
    fun θ hθ s => (curry_differentiableAt_of_contDiffOn hU (n := 1) (by norm_num) hPthC
      (hm s θ hθ)).1
  have hPthθ : ∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.pth g t θ') θ :=
    fun t θ hθ => (curry_differentiableAt_of_contDiffOn hU (n := 1) (by norm_num) hPthC
      (hm t θ hθ)).2
  -- `chi N` is smooth (indeed `C^∞`)
  have hchi : Differentiable ℝ (chi N) := (chi_contDiff 1 N).differentiable (by norm_num)
  have hchi1 : Differentiable ℝ (deriv (chi N)) := (chi_contDiff 2 N).differentiable_deriv_two
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t θ hθ
    exact pz_mul_slice (chi N) g t θ (hchi t) (hGz θ hθ t)
  · intro t θ hθ
    exact pz_pz_mul_slice (chi N) g t θ hchi hchi1 (hGz θ hθ) (hPzg θ hθ)
  · intro t θ hθ
    exact pth_mul_slice (chi N) g t θ (hGθ t θ hθ)
  · intro t θ hθ
    exact pth_pth_mul_slice (chi N) g t θ hθ (fun θ' hθ' => hGθ t θ' hθ') (hPthθ t θ hθ)
  · intro t θ hθ ht
    have hN : 0 < N := by linarith [ht.1, ht.2]
    have hlt : |t| < N := abs_lt.mpr ht
    rw [pz_pth_mul_slice (chi N) g t θ (hchi t) (fun s => hGθ s θ hθ) (hPthz θ hθ t),
      chi_deriv_eq_zero hN hlt, chi_eq_one hN (le_of_lt hlt)]
    ring

end

end Work.FTS.EllSol.Trunc

/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `σ`-gain of the flat angular coefficient norm, arbitrary order

Let `f` be `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` and suppose that all the mixed
`D`-derivatives of `∂_θ f` of total order `≤ l` are bounded on `Q0` by a constant `K`:

`|D_z^b D_θ^i (∂_θ f)| ≤ K`  for `b + i ≤ l`.

Then every mixed derivative `D_z^b D_θ^a f` of `f` itself with `a ≥ 1` and `a + b ≤ l + 1`
carries at least one factor `sin(2θ)`:

`|D_z^b D_θ^a f| ≤ C · sin(2θ) · K`,

with a constant `C` depending only on `l`.  This is the "σ-gain" of the flat angular
coefficient norm `Work.FTS.VocabO.CoefTh` used by the transport rows `T2S`/`T3S_Dz`.

The mechanism: `D_θ^a f = D_θ^{a-1}(sin(2θ) · ∂_θ f)` (since `D_θ = sin(2θ)∂_θ`), and the
Leibniz rule for `D_θ^{a-1}` expands the right-hand side into the terms
`C(a-1,r)·D_θ^r(sin 2·)·D_θ^{a-1-r}(∂_θ f)`.  The angular coefficients satisfy
`|D_θ^r(sin 2·)| ≤ A·sin(2θ)` on `Iθ` (`Work.FTS.EllipticEst.Lop_iter_sin_bound`), and the
factor `sin(2θ)` does not depend on `z`, hence commutes with `D_z^b`; this reduces the claim
to the hypothesis on the derivatives of `∂_θ f`.

Since `SmoothOpen` only asks for `C^∞`-regularity on the *open* quadrant, the Leibniz rule
used here is proved with *differentiability* hypotheses on the `θ`-slices of the iterates
(`DthIter_mul_eq_of_diffOn`), rather than through the analytic (`ContDiffOn ℝ ⊤`) machinery
of `Work.Spaces.DthIter_mul`.

All declarations here are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.EllipticEst.Lop_iter_sin_bound
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The multiplier `sin(2·)` and the shift identity for the `D_θ`-iterates -/

/-- The angular multiplier `θ ↦ sin(2θ)`, viewed as a function on `(z,θ)`. -/
def Sfun : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- `sin(2θ) ≥ 0` on the open angular interval. -/
theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The multiplier is smooth on the open quadrant. -/
theorem Sfun_smoothOpen : Work.FTS.EllipticEst.SmoothOpen Sfun := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ (θ : ℝ) => Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0
  fun_prop

/-- Shifting the iteration of `D_θ`: `D_θ^{n+1} g = D_θ^{n}(D_θ g)`. -/
theorem DthIter_shift (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter (n + 1) g = Work.Spaces.DthIter n (Work.Spaces.Dth g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, ← Work.Spaces.DthIter_succ]

/-- `D_θ = sin(2θ) · ∂_θ`, in the shape used below. -/
theorem Dth_eq_Sfun_mul_pth (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth f = fun z θ => Sfun z θ * Work.Spaces.pth f z θ := rfl

/-- `D_θ^r` of the multiplier `sin(2·)` is the corresponding iterate of `Lop` applied to the
one-variable function `sin(2·)` (it is independent of `z`). -/
theorem DthIter_Sfun_eq_LopIter (r : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter r Sfun z θ
      = Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ := by
  rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop r Sfun z) θ]
  rfl

/-! ## Leibniz for `D_θ^i` with differentiability hypotheses on the slices -/

/-- **The iterated Leibniz rule for `D_θ`** with only *differentiability* of the `θ`-slices of
the iterates of the two factors.  This is the form that applies to `SmoothOpen` data, for
which no analyticity (or finite-order `C^n`-arithmetic) is available. -/
theorem DthIter_mul_eq_of_diffOn (i : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hf : ∀ a ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter a f z θ')
      (Set.Ioo 0 (π / 2)))
    (hg : ∀ a ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter a g z θ')
      (Set.Ioo 0 (π / 2))) :
    Work.Spaces.DthIter i (fun a b => f a b * g a b) z θ
      = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
          * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (i - a) g z θ) := by
  induction i generalizing θ with
  | zero =>
      simp
  | succ i ih =>
      -- the two `θ`-slices of the iterate `D_θ^i (f·g)` agree with the binomial sum near `θ`
      have hev : (fun θ' => Work.Spaces.DthIter i (fun a b : ℝ => f a b * g a b) z θ')
          =ᶠ[𝓝 θ] (fun θ' => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih hθ' (fun a ha => hf a (by omega)) (fun a ha => hg a (by omega))
      have hderiv : deriv (fun θ' => Work.Spaces.DthIter i
            (fun a b : ℝ => f a b * g a b) z θ') θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ :=
        hev.deriv_eq
      have hsummand : ∀ a ∈ Finset.range (i + 1), DifferentiableAt ℝ
          (fun θ' => (i.choose a : ℝ)
            * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ := by
        intro a ha
        exact (((hf a (by have := Finset.mem_range.mp ha; omega)).differentiableAt
            (isOpen_Ioo.mem_nhds hθ)).mul
          ((hg (i - a) (by omega)).differentiableAt (isOpen_Ioo.mem_nhds hθ))).const_mul _
      have hfunsum : (fun θ' => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ'))
          = ∑ a ∈ Finset.range (i + 1), (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hkey : Work.Spaces.DthIter (i + 1) (fun a b : ℝ => f a b * g a b) z θ
          = ∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (i.choose a : ℝ)
                  * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ := by
        show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i
              (fun a b : ℝ => f a b * g a b) z θ') θ = _
        rw [hderiv, hfunsum, deriv_sum hsummand, Finset.mul_sum]
      rw [hkey]
      have hterm : ∀ a ∈ Finset.range (i + 1),
          Real.sin (2 * θ) * deriv (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ
          = (i.choose a : ℝ)
              * (Work.Spaces.DthIter (a + 1) f z θ * Work.Spaces.DthIter (i - a) g z θ
                + Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (i - a + 1) g z θ) := by
        intro a ha
        have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter a f z θ') θ :=
          (hf a (by have := Finset.mem_range.mp ha; omega)).differentiableAt
            (isOpen_Ioo.mem_nhds hθ)
        have h2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter (i - a) g z θ') θ :=
          (hg (i - a) (by omega)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
        have hder : deriv (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.DthIter a f z θ' * Work.Spaces.DthIter (i - a) g z θ')) θ
            = (i.choose a : ℝ)
                * (deriv (fun θ' => Work.Spaces.DthIter a f z θ') θ
                    * Work.Spaces.DthIter (i - a) g z θ
                  + Work.Spaces.DthIter a f z θ
                    * deriv (fun θ' => Work.Spaces.DthIter (i - a) g z θ') θ) :=
          ((h1.hasDerivAt.mul h2.hasDerivAt).const_mul ((i.choose a : ℝ))).deriv
        rw [hder,
          show Work.Spaces.DthIter (a + 1) f z θ
              = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter a f z θ') θ from rfl,
          show Work.Spaces.DthIter (i - a + 1) g z θ
              = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter (i - a) g z θ') θ
            from rfl]
        ring
      rw [Finset.sum_congr rfl hterm]
      exact Work.Spaces.leibniz_step i (fun a => Work.Spaces.DthIter a f z θ)
        (fun b => Work.Spaces.DthIter b g z θ)

/-! ## `D_z^j` acts termwise on sums with `θ`-only coefficients -/

/-- `D_z^j` of a finite sum of products `cᵢ(θ) · Hᵢ(z,θ)`, with `θ`-only coefficients and
`SmoothOpen` summands, is the sum of `cᵢ(θ) · D_z^j Hᵢ`. -/
theorem DzIter_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (H : ι → ℝ → ℝ → ℝ)
    (hH : ∀ i ∈ s, Work.FTS.EllipticEst.SmoothOpen (H i)) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ) z θ
      = ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
      have hEq : Set.EqOn
          (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ)))
          (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        obtain ⟨z', θ'⟩ := p
        obtain ⟨hz', hθ', hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ih hz' hθ' hθ'1
      have hpz : Work.Spaces.pz
            (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ)) z θ
          = Work.Spaces.pz
            (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ1⟩)
      have hdiff : ∀ i ∈ s, DifferentiableAt ℝ
          (fun z' => Work.Spaces.DzIter j (H i) z' θ) z := by
        intro i hi
        have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j (H i)) :=
          (hH i hi).DzIter j
        exact ((h1.curry_z ⟨hθ, hθ1⟩).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioi.mem_nhds hz)
      have hpz2 : Work.Spaces.pz
            (fun z θ => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z θ) z θ
          = ∑ i ∈ s, c i θ * Work.Spaces.pz (Work.Spaces.DzIter j (H i)) z θ := by
        show deriv (fun z' => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z' θ) z = _
        rw [show (fun z' => ∑ i ∈ s, c i θ * Work.Spaces.DzIter j (H i) z' θ)
              = ∑ i ∈ s, (fun z' => c i θ * Work.Spaces.DzIter j (H i) z' θ) from by
            funext z'
            rw [Finset.sum_apply]]
        rw [deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
        exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i θ)
      show z * Work.Spaces.pz
            (Work.Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * H i z θ)) z θ
          = ∑ i ∈ s, c i θ * Work.Spaces.DzIter (j + 1) (H i) z θ
      rw [hpz, hpz2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [show Work.Spaces.DzIter (j + 1) (H i) z θ
            = z * Work.Spaces.pz (Work.Spaces.DzIter j (H i)) z θ from rfl]
      ring

/-! ## The main estimate -/

theorem flat_mixed_le (l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      ∀ (K : ℝ), 0 ≤ K →
      (∀ b i : ℕ, b + i ≤ l → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ K) →
      ∀ a b : ℕ, 1 ≤ a → a + b ≤ l + 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * Real.sin (2 * θ) * K := by
  classical
  obtain ⟨A, hApos, hAbound⟩ := Work.FTS.EllipticEst.Lop_iter_sin_bound l
  refine ⟨(1 + (2 : ℝ) ^ l) * (A + 1) + 1, by positivity, ?_⟩
  intro f hsm K hK hHyp a b ha hab z θ hz hθ hθ1
  obtain ⟨i, hi⟩ : ∃ i : ℕ, a = i + 1 :=
    ⟨a - 1, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  subst hi
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo ⟨hθ, hθ1⟩
  have hsK : 0 ≤ Real.sin (2 * θ) * K := mul_nonneg hsin hK
  have hil : i ≤ l := by omega
  have hbi : b + i ≤ l := by omega
  -- the angular coefficients
  have hcoef : ∀ r : ℕ, r ≤ l →
      |Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ|
      ≤ A * Real.sin (2 * θ) := fun r hr => hAbound r hr θ ⟨hθ.le, hθ1.le⟩
  -- the Leibniz expansion, as a joint statement on the open quadrant
  have hLeib : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Spaces.DthIter i (fun z θ => Sfun z θ * Work.Spaces.pth f z θ) z' θ'
        = ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ')
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z' θ' := by
    intro z' θ' hz' hθ' hθ'1
    have hf : ∀ c ≤ i, DifferentiableOn ℝ
        (fun θ'' => Work.Spaces.DthIter c Sfun z' θ'') (Set.Ioo 0 (π / 2)) := fun c _ =>
      ((Sfun_smoothOpen.DthIter c).curry_θ hz').differentiableOn (by simp)
    have hg : ∀ c ≤ i, DifferentiableOn ℝ
        (fun θ'' => Work.Spaces.DthIter c (Work.Spaces.pth f) z' θ'')
        (Set.Ioo 0 (π / 2)) := fun c _ =>
      (((hsm.pth).DthIter c).curry_θ hz').differentiableOn (by simp)
    rw [DthIter_mul_eq_of_diffOn i Sfun (Work.Spaces.pth f) ⟨hθ', hθ'1⟩ hf hg]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [DthIter_Sfun_eq_LopIter r z' θ']
    ring
  -- the mixed derivative rewritten as `D_z^b` of that sum
  have hmixed : Work.Spaces.mixed b (i + 1) f z θ
      = Work.Spaces.DzIter b (fun z θ => ∑ r ∈ Finset.range (i + 1),
            ((i.choose r : ℝ)
                * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
              * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z θ) z θ := by
    rw [show Work.Spaces.mixed b (i + 1) f
          = Work.Spaces.DzIter b (Work.Spaces.DthIter (i + 1) f) from rfl, DthIter_shift,
      Dth_eq_Sfun_mul_pth]
    exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i (fun z θ => Sfun z θ * Work.Spaces.pth f z θ))
      (G := fun z θ => ∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z θ) hLeib b z θ hz hθ hθ1
  -- the termwise distribution of `D_z^b`
  have hstep3 : Work.Spaces.DzIter b (fun z θ => ∑ r ∈ Finset.range (i + 1),
        ((i.choose r : ℝ)
            * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
          * Work.Spaces.DthIter (i - r) (Work.Spaces.pth f) z θ) z θ
      = ∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ :=
    DzIter_sum_const_mul (Finset.range (i + 1))
      (fun r θ => (i.choose r : ℝ)
        * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
      (fun r => Work.Spaces.DthIter (i - r) (Work.Spaces.pth f))
      (fun r _ => (hsm.pth).DthIter (i - r)) b hz hθ hθ1
  -- the per-term bound
  have hbd : ∀ r ∈ Finset.range (i + 1),
      |((i.choose r : ℝ)
          * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
        * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ|
        ≤ (i.choose r : ℝ) * (A * Real.sin (2 * θ)) * K := by
    intro r hr
    have hr' : r < i + 1 := Finset.mem_range.mp hr
    have hrl : r ≤ l := le_trans (Nat.lt_succ_iff.mp hr') hil
    have h1 : |Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ|
        ≤ A * Real.sin (2 * θ) := hcoef r hrl
    have h2 : |Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ| ≤ K :=
      hHyp b (i - r) (by omega) z θ hz hθ hθ1
    have hC : (0 : ℝ) ≤ (i.choose r : ℝ) := Nat.cast_nonneg _
    have hAs : 0 ≤ A * Real.sin (2 * θ) := mul_nonneg hApos.le hsin
    rw [abs_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 (abs_nonneg _)
      (mul_nonneg hC hAs)
  calc |Work.Spaces.mixed b (i + 1) f z θ|
      = |∑ r ∈ Finset.range (i + 1),
          ((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ| := by
        rw [hmixed, hstep3]
    _ ≤ ∑ r ∈ Finset.range (i + 1),
          |((i.choose r : ℝ)
              * Work.FTS.EllipticEst.LopIter r (fun t : ℝ => Real.sin (2 * t)) θ)
            * Work.Spaces.mixed b (i - r) (Work.Spaces.pth f) z θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range (i + 1),
          (i.choose r : ℝ) * (A * Real.sin (2 * θ)) * K :=
        Finset.sum_le_sum hbd
    _ = ((2 : ℝ) ^ i * A) * (Real.sin (2 * θ) * K) := by
        have hchoose : (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) = (2 : ℝ) ^ i := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
        ring
    _ ≤ ((1 + (2 : ℝ) ^ l) * (A + 1) + 1) * (Real.sin (2 * θ) * K) := by
        refine mul_le_mul_of_nonneg_right ?_ hsK
        have h2i : (0 : ℝ) ≤ (2 : ℝ) ^ i := pow_nonneg (by norm_num) i
        have h2l : (0 : ℝ) ≤ (2 : ℝ) ^ l := pow_nonneg (by norm_num) l
        have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) hil
        nlinarith [mul_le_mul_of_nonneg_right hpow hApos.le]
    _ = ((1 + (2 : ℝ) ^ l) * (A + 1) + 1) * Real.sin (2 * θ) * K := by ring

end Work.FTS.TransportS

import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.Kfr_eq
import Submission.Work.BoseBoxFock.Middle_eq_of_rows_fixed
import Submission.Work.BoseBoxFock.Middle_k0_hold
import Submission.Work.BoseBoxFock.Middle_row_c_hold
import Submission.Work.BoseBoxFock.Middle_row_d_hold
import Submission.Work.BoseBoxFock.Middle_rows_ab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.UnivFrames` — the `univ`-summed cubic middle kernel

`Work.BoseBoxFock.FRK.PotCubicFreeU` sums the `k`-labels of the cubic row over **all** of
`Lab (HM μ).N` (`Finset.univ`), not over `Work.BoseB7.excited`.  The middle kernel of that row is
therefore

    `MiddleU x y u = Σ_{s∈excited} Σ_{k∈univ} fLh(s)·W1h(k)·star(pinQ (s−k) y)·pinTheta s x·star(pinQ k u)`

(`Middle` in `pcfFrameDefs` sums `k` over `excited`).

This module records:

* the `univ`-frames `KfrU`, `KχfrU` and their splitting `KfrU = Kfr + W1h 0`,
  `KχfrU = Kχfr + W1h 0·χ̂(0)`;
* the splitting `MiddleU = Middle + (k = 0 column)` (the column evaluated by `Middle_k0_hold`);
* the `s`-frame integral identity `ℓ⁻³∫_w χ_Λ(w)·Ksfr(x+w) = Ksχ(x)`, which is what makes the
  `k = 0` column combine with the `excited`-rows into the `univ` frames;
* the **four-channel value of `MiddleU`** at the `univ` frames,

    `MiddleU = ℓ^{-9/2}·(ChAU − ChBU − ChCU + ChDU)`.

Everything is `sorry`-free; the only inputs are the PROVED rows `Middle_row_a/b`, the
`_hold` versions of rows (c),(d), `Middle_eq_of_rows_fixed`, `Middle_k0_hold` and the box Fourier
transform `hatChi_eq_integral_plus` (`Middle_channels_aux`).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

open Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The `univ`-frames -/

/-- The `k`-frame over **all** labels: `Σ_{k∈univ}W1h(k)e^{i⟪κ_k,z⟫}`. -/
def KfrU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (z : Ω) : ℂ :=
  ∑ k : Lab N,
    ((W1h v h μ fu N k : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))

/-- The `χ̂`-weighted `k`-frame over **all** labels. -/
def KχfrU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (z : Ω) : ℂ :=
  ∑ k : Lab N,
    (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))

/-- The `χ̂`-weighted `s`-frame of the `k = 0` column:
`Ksχ(x) = Σ_{s∈excited}fLh(s)·χ̂(ℓκ_s)·e^{i⟪κ_s,x⟫}`. -/
def Ksχ (v : Ω → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s : ℝ) : ℂ) * ((hatChih v μ N s : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))

/-- The `univ`-sum splits as the `excited`-sum plus the `k = 0` term. -/
lemma sum_univ_eq_sum_excited_add {N : ℕ} (f : Lab N → ℂ) :
    (∑ k : Lab N, f k) = (∑ k ∈ Work.BoseB7.excited (Lab N), f k) + f 0 := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Lab N)) f (Finset.mem_univ (0 : Lab N))
  rw [Work.BoseB7.excited]
  exact h.symm

/-- `KfrU = Kfr + W1h 0` (`kmomLab ℓ N 0 = 0`). -/
lemma KfrU_eq (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut)
    (N : ℕ) (z : Ω) :
    KfrU v h μ fu N z = Kfr v h μ fu N z + ((W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ) := by
  rw [KfrU, Kfr, sum_univ_eq_sum_excited_add
    (fun k : Lab N => ((W1h v h μ fu N k : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  congr 1
  rw [k0_kmomLab_zero, inner_zero_left]
  simp

/-- `KχfrU = Kχfr + W1h 0·χ̂(0)`. -/
lemma KχfrU_eq (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut)
    (N : ℕ) (z : Ω) :
    KχfrU v h μ fu N z
      = Kχfr v h μ fu N z
        + ((W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ) * ((hatChih v μ N (0 : Lab N) : ℝ) : ℂ) := by
  rw [KχfrU, Kχfr, sum_univ_eq_sum_excited_add
    (fun k : Lab N => (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  congr 1
  rw [k0_kmomLab_zero, inner_zero_left]
  simp

/-! ## 2. The `univ`-summed middle kernel -/

/-- The middle kernel of the cubic row with the `k`-sum over **all** labels. -/
def MiddleU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (x y u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
      * star (pinQ v μ N (s - k) y) * pinTheta v μ N s x * star (pinQ v μ N k u)

/-- The `k = 0` column of `MiddleU`, in the parenthesisation of `Middle_k0_hold`. -/
def Middle_k0col (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (x y u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s * W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ)
      * (star (pinQ v μ N s y) * pinTheta v μ N s x * star (pinQ v μ N (0 : Lab N) u))

/-- `MiddleU = Middle + (k = 0 column)`. -/
lemma MiddleU_eq_Middle_add_k0col (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x y u : Ω) :
    MiddleU v h fc fu μ N x y u
      = Middle v h fc fu μ N x y u + Middle_k0col v h fc fu μ N x y u := by
  rw [MiddleU, Middle, Middle_k0col,
    Finset.sum_congr rfl (fun s (_ : s ∈ Work.BoseB7.excited (Lab N)) =>
      sum_univ_eq_sum_excited_add
        (fun k : Lab N => ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * star (pinQ v μ N (s - k) y) * pinTheta v μ N s x * star (pinQ v μ N k u))),
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun s _ => by rw [sub_zero]; ring)

/-- The **mirror (h.c.) middle kernel** of the cubic row — the atom-2 channel
`pinQ k (x_i)·star(pinTheta_s y)·pinQ (s−k)(x_j)·star(pinCond c u)`, with the `k`-sum over **all**
labels.  Its four-channel value is the twin of `MiddleU_eq_four` with the creation/annihilation
slots interchanged (the `s`-frame then couples the slot-`j` bra with the slot-`i` ket, and the
`k`-frame the two *creation* slots `x_i, x_j` — see `PCFU/AtomTwoChannels.lean`). -/
def MiddleV (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (c : ℂ) (xi y xj u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
      * pinQ v μ N k xi * star (pinTheta v μ N s y) * pinQ v μ N (s - k) xj
      * star (pinCond v μ c u)

/-! ## 3. The `s`-frame integral identity -/

/-- **The box Fourier transform of the window against the `s`-frame**:
`ℓ⁻³∫_w χ_Λ(w)Ksfr(x+w) = Ksχ(x)`.  This is the identity that turns the `k = 0` column of the
`(c)`/`(d)` channels into the `w`-integral of the `univ` channels. -/
theorem integral_chiLam_Ksfr (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x : Ω) :
    ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * Ksfr v fc μ N (x + w)
      = (((ellH v μ) ^ 3 : ℝ) : ℂ) * Ksχ v fc μ N x := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have h3 : (((ellH v μ) ^ 3 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  -- pointwise expansion of `Ksfr (x + w)`
  have hexp : ∀ s : Lab N, ∀ w : Ω,
      Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ))
        = Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ)) := by
    intro s w
    rw [inner_add_right]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  -- the base integral: `∫_w χ_Λ(w)e^{i⟪κ_s,w⟫} = ℓ³χ̂(ℓκ_s)`
  have hbase : ∀ s : Lab N,
      ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ))
        = (((ellH v μ) ^ 3 : ℝ) : ℂ) * ((hatChih v μ N s : ℝ) : ℂ) := by
    intro s
    have hb := hatChi_eq_integral_plus hℓ (kmomLab (ellH v μ) N s)
    rw [hatChih]
    rw [hb, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
  -- the integral of one summand
  have hterm : ∀ s : Lab N,
      ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ)))
        = (((ellH v μ) ^ 3 : ℝ) : ℂ) * (((fLh v fc μ N s : ℝ) : ℂ)
            * ((hatChih v μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))) := by
    intro s
    rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ))))
        = (fun w : Ω => (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)))
            * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ))))
        from by funext w; rw [hexp s w]; ring]
    rw [MeasureTheory.integral_const_mul, hbase]
    ring
  -- integrability of one summand
  have hint : ∀ s : Lab N, Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (((fLh v fc μ N s : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ)))) := by
    intro s
    have h1 : Integrable (fun w : Ω =>
        ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) w : ℂ))) :=
      integrable_chiLam_mul_exp_plus (ellH v μ) hℓ (kmomLab (ellH v μ) N s)
    have h2 := h1.const_mul (((fLh v fc μ N s : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)))
    refine h2.congr (Filter.Eventually.of_forall (fun w => ?_))
    simp only [hexp s w]
    ring
  -- assemble
  simp only [Ksfr, Ksχ]
  rw [Finset.mul_sum]
  rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (∑ s ∈ Work.BoseB7.excited (Lab N),
            ((fLh v fc μ N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ))))
      = (fun w : Ω => ∑ s ∈ Work.BoseB7.excited (Lab N),
          ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
            * (((fLh v fc μ N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ))))
      from by
    funext w
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum _ (fun s _ => hint s)]
  exact Finset.sum_congr rfl (fun s _ => hterm s)

/-- **The `univ` `k`-frame is the clean periodisation** (no subtracted zero mode, because the
`k = 0` cell is now *inside* the sum): `KfrU z = ℓ³ Σ'_d uvSmear(z + ℓd)`.
This is `Kfr_eq` plus `KfrU_eq`. -/
theorem KfrU_periodisation {v : Ω → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v))
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (ellH v μ)))
    (hev : ∀ x, Work.BoseFixR.W1fun v h (ellH v μ) (-x) = Work.BoseFixR.W1fun v h (ellH v μ) x)
    (hN1 : 1 ≤ N) (z : Ω) :
    KfrU v h μ fu N z = (((ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
      ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
        (z + (ellH v μ) • latVec d) : ℝ) : ℂ))) := by
  rw [KfrU_eq, Kfr_eq hℓ0 hI hcs hev hN1 z]
  ring

/-! ## 4. The four-channel value of `MiddleU` -/

/-- Continuity of the `s`-frame along a shifted argument. -/
lemma continuous_Ksfr_add (v : Ω → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x : Ω) :
    Continuous fun w : Ω => Ksfr v fc μ N (x + w) := by
  rw [show (fun w : Ω => Ksfr v fc μ N (x + w)) = (fun w : Ω =>
      ∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x + w) : ℂ))) from by
    funext w
    simp only [Ksfr]]
  fun_prop

/-- Continuity of the `k`-frame along a shifted argument. -/
lemma continuous_Kfr_add (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (x : Ω) :
    Continuous fun w : Ω => Kfr v h μ fu N (x + w) := by
  rw [show (fun w : Ω => Kfr v h μ fu N (x + w)) = (fun w : Ω =>
      ∑ k ∈ Work.BoseB7.excited (Lab N),
        ((W1h v h μ fu N k : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (x + w) : ℂ))) from by
    funext w
    simp only [Kfr]]
  fun_prop

/-- Continuity of the `χ̂`-weighted `k`-frame. -/
lemma continuous_Kχfr (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Continuous fun w : Ω => Kχfr v h μ fu N w := by
  rw [show (fun w : Ω => Kχfr v h μ fu N w) = (fun w : Ω =>
      ∑ k ∈ Work.BoseB7.excited (Lab N),
        (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) w : ℂ))) from by
    funext w
    simp only [Kχfr]]
  fun_prop

/-- `χ_Λ(w)·(Ksfr(x+w)·g w)` is integrable for continuous `g` (`χ_Λ` is continuous with compact
support). -/
lemma integrable_chiLam_Ksfr_mul (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x : Ω) (g : Ω → ℂ) (hg : Continuous g) :
    Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * (Ksfr v fc μ N (x + w) * g w)) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hχc : Continuous fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont (Work.BoseK15.corpusBox) (ellH v μ))
  exact (hχc.mul ((continuous_Ksfr_add v fc μ N x).mul hg)).integrable_of_hasCompactSupport
    ((hasCompactSupport_chiLam_complex (ellH v μ) hℓ).mul_right
      (f' := fun w : Ω => Ksfr v fc μ N (x + w) * g w))

/-- `χ_Λ(w)·Ksfr(x+w)` is integrable. -/
lemma integrable_chiLam_Ksfr (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x : Ω) :
    Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * Ksfr v fc μ N (x + w)) := by
  refine (integrable_chiLam_Ksfr_mul v h fc μ N x (fun _ => (1 : ℂ)) continuous_const).congr
    (Filter.Eventually.of_forall (fun w => ?_))
  ring

/-- The `(c)`-channel integral over the `univ` `k`-frame, in terms of the `excited` one. -/
lemma integral_chiLam_Ksfr_mul_KfrU (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x u : Ω) :
    ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w)
      = (∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
            * Ksfr v fc μ N (x + w) * Kfr v h μ fu N (u + w))
        + ((W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ) * (((ellH v μ) ^ 3 : ℝ) : ℂ)
            * Ksχ v fc μ N x := by
  have hI1 : Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * Kfr v h μ fu N (u + w)) :=
    (integrable_chiLam_Ksfr_mul v h fc μ N x (fun w => Kfr v h μ fu N (u + w))
      (continuous_Kfr_add v h μ fu N u)).congr (Filter.Eventually.of_forall (fun w => by ring))
  have hI2 : Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * Ksfr v fc μ N (x + w)) :=
    integrable_chiLam_Ksfr v h fc μ N x
  rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w))
      = (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Ksfr v fc μ N (x + w) * Kfr v h μ fu N (u + w)
          + ((W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ)
              * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Ksfr v fc μ N (x + w))) from by
    funext w
    rw [KfrU_eq v h μ fu N (u + w)]
    ring]
  rw [MeasureTheory.integral_add hI1 (hI2.const_mul _), MeasureTheory.integral_const_mul,
    integral_chiLam_Ksfr v h fc μ N x]
  ring

/-- The `(d)`-channel integral over the `univ` `k`-frame, in terms of the `excited` one. -/
lemma integral_chiLam_Ksfr_mul_KχfrU (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x : Ω) :
    ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w
      = (∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
            * Ksfr v fc μ N (x + w) * Kχfr v h μ fu N w)
        + ((W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ) * ((hatChih v μ N (0 : Lab N) : ℝ) : ℂ)
            * (((ellH v μ) ^ 3 : ℝ) : ℂ) * Ksχ v fc μ N x := by
  have hI1 : Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * Kχfr v h μ fu N w) :=
    (integrable_chiLam_Ksfr_mul v h fc μ N x (fun w => Kχfr v h μ fu N w)
      (continuous_Kχfr v h μ fu N)).congr (Filter.Eventually.of_forall (fun w => by ring))
  have hI2 : Integrable (fun w : Ω =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) * Ksfr v fc μ N (x + w)) :=
    integrable_chiLam_Ksfr v h fc μ N x
  rw [show (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w)
      = (fun w : Ω => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Ksfr v fc μ N (x + w) * Kχfr v h μ fu N w
          + ((W1h v h μ fu N (0 : Lab N) : ℝ) : ℂ) * ((hatChih v μ N (0 : Lab N) : ℝ) : ℂ)
              * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Ksfr v fc μ N (x + w))) from by
    funext w
    rw [KχfrU_eq v h μ fu N w]
    ring]
  rw [MeasureTheory.integral_add hI1 (hI2.const_mul _), MeasureTheory.integral_const_mul,
    integral_chiLam_Ksfr v h fc μ N x]
  ring

/-- The `(a)`-channel of `MiddleU`, at the `univ` `k`-frame. -/
def ChAU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (y x u : Ω) : ℂ :=
  Ksfr v fc μ N (x - y) * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
    * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
    * KfrU v h μ fu N (y - u)

/-- The `(b)`-channel of `MiddleU`. -/
def ChBU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (y x u : Ω) : ℂ :=
  Ksfr v fc μ N (x - y) * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u
    * KχfrU v h μ fu N y

/-- The `(c)`-channel of `MiddleU`. -/
def ChCU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (y x u : Ω) : ℂ :=
  Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
    * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
    * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
    * ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KfrU v h μ fu N (u + w)

/-- The `(d)`-channel of `MiddleU`. -/
def ChDU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (y x u : Ω) : ℂ :=
  Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u
    * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
    * ∫ w : Ω, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Ksfr v fc μ N (x + w) * KχfrU v h μ fu N w

/-- **The four-channel value of `MiddleU`**, at the `univ` frames. -/
theorem MiddleU_eq_four (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x y u : Ω)
    (hsub : ∀ s ∈ Work.BoseB7.excited (Lab N), fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab N), W1h v h μ fu N k ≠ 0 →
      kmomLab (ellH v μ) N (s - k) = kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k) :
    MiddleU v h fc fu μ N x y u
      = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ) *
        (ChAU v h fc fu μ N y x u - ChBU v h fc fu μ N y x u
          - ChCU v h fc fu μ N y x u + ChDU v h fc fu μ N y x u) := by
  have hM := Middle_eq_of_rows_fixed v h fc fu μ N x y u
    (Middle_row_a v h fc fu μ N x y u hsub) (Middle_row_b v h fc fu μ N x y u hsub)
    (Middle_row_c_hold v h fc fu μ N x y u hsub) (Middle_row_d_hold v h fc fu μ N x y u hsub)
  have hK := Middle_k0_hold v h fc fu μ N x y u
  simp only [starRingEnd_apply] at hK
  rw [MiddleU_eq_Middle_add_k0col, hM]
  simp only [Middle_k0col]
  rw [hK]
  simp only [ChAU, ChBU, ChCU, ChDU]
  rw [KfrU_eq v h μ fu N (y - u), KχfrU_eq v h μ fu N y,
    integral_chiLam_Ksfr_mul_KfrU v h fc fu μ N x u,
    integral_chiLam_Ksfr_mul_KχfrU v h fc fu μ N x]
  have h3 : (((ellH v μ) ^ 3 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt (ellH_pos v μ))
  rw [ellH_zpow_neg_three (ellH v μ)]
  simp only [Ksχ, hatChih]
  field_simp [h3]
  ring

end Work.BoseBoxFock.PCFU

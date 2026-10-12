import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.TrigIndep
import Submission.Work.BoseBoxFock.corpusChiLam_eq_of_norm_lt
import Submission.Work.BoseBoxFock.corpusChi_zero_near
import Submission.Work.BoseBoxFock.realQuad_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.modeFam_independent` — independence of the physical mode family

The honest model's mode family

  `{1_Λ} ∪ {qVec(kmomLab ℓ N k)}_k ∪ {thetaExp(kmomLab ℓ N s)}_{s ≠ 0}`

is linearly independent (the `s = 0` θ-mode is `1_Λ` itself and is dropped).

## The proof

Write the combination, on the box `Λ(ℓ)` (where `θ = 1_Λ = 1`), as

  `γ + χ_Λ(x) · P(x) + Σ_{s ≠ 0} b s · e^{i⟪ω s, x⟫}`,   `P = Σ_k d k · e^{i⟪ω k, x⟫}`,

with `ω = kmomLab ℓ N`, `γ = c − Σ_k d k χ̂(ℓω k)`.  On the **ball** `‖x‖ < ℓ/4` the corpus χ
is the constant `κ = (∫χ²)^{-1/2}` (`corpusChiLam_eq_of_norm_lt`: the `ContDiffBump` has
`rIn = 1/4` and `χ = χBase/√(∫χBase²)`), so there the combination is the trig polynomial
`γ + Σ_k (κ d k + [k ≠ 0] b k) e^{i⟪ω k, x⟫}`; folding `γ` into the `k = 0` coefficient
(`ω 0 = 0`) and applying the exponential-independence lemma `expSum_eq_zero_of_eqOn_ball`
(of `TrigIndep`, along the explicit separating direction `vDir N`, whose projections separate
the lattice momenta by `realQuad_ne_zero`) gives

  `κ d k + b k = 0` for `k ≠ 0`, and `γ + κ d 0 = 0`.

Substituting both into the box identity leaves `(χ_Λ(x) − κ)·P(x) = 0` on the box, and
`corpusChi_zero_near` provides an open ball inside the box on which `χ_Λ = 0 ≠ κ`; there
`P = 0`, so the same independence lemma gives `d = 0`.  Then `b s = −κ d s = 0` for `s ≠ 0`,
`γ = −κ d 0 = 0` and `c = γ + Σ_k d k χ̂(ℓω k) = 0`.
-/

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Filter

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

-- ================= the lattice data =================

lemma labVec_injective_aux (N : ℕ) : Function.Injective (labVec N) := by
  intro a b h
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun h i)

lemma labVec_zero_aux (N : ℕ) : labVec N (0 : Lab N) = 0 := by
  funext i
  simp [labVec, ZMod.valMinAbs_zero]

lemma labVec_abs_le (N : ℕ) (n : Lab N) (i : Fin 3) : |labVec N n i| ≤ (N : ℤ) := by
  have h := ZMod.natAbs_valMinAbs_le (n := 2 * N + 1) (n i)
  have h2 : (2 * N + 1) / 2 = N := by omega
  rw [h2] at h
  have h3 : (labVec N n i).natAbs ≤ N := h
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h3

lemma boxVec_sub (m m' : Fin 3 → ℤ) :
    Work.BoseB4.vec (m - m') = Work.BoseB4.vec m - Work.BoseB4.vec m' := by
  rw [Work.BoseB4.vec, Work.BoseB4.vec, Work.BoseB4.vec, ← WithLp.toLp_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  push_cast
  ring

noncomputable def vDir (N : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i : Fin 3 => ((4 * (N : ℝ) + 2)⁻¹) ^ (i : ℕ))

lemma inner_vDir (N : ℕ) (u : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ u (vDir N)
      = u 0 + u 1 * ((4 * (N : ℝ) + 2)⁻¹) + u 2 * ((4 * (N : ℝ) + 2)⁻¹) ^ 2 := by
  rw [vDir]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [Fin.sum_univ_three]
  norm_num
  ring

lemma inner_vec_vDir (N : ℕ) (n : Fin 3 → ℤ) :
    inner ℝ (Work.BoseB4.vec n) (vDir N)
      = 2 * Real.pi * ((4 * (N : ℝ) + 2)⁻¹) ^ 2 *
        ((n 0 : ℝ) * (4 * (N : ℝ) + 2) ^ 2 + (n 1 : ℝ) * (4 * (N : ℝ) + 2) + (n 2 : ℝ)) := by
  rw [inner_vDir]
  simp only [Work.BoseB4.vec, WithLp.ofLp_toLp]
  have hM : (4 * (N : ℝ) + 2) ≠ 0 := by positivity
  field_simp

theorem inner_kmomLab_dir_inj {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.Injective (fun k : Lab N => inner ℝ (kmomLab ℓ N k) (vDir N)) := by
  intro k s hks
  have hks' : inner ℝ (kmomLab ℓ N k) (vDir N) = inner ℝ (kmomLab ℓ N s) (vDir N) := hks
  have h0 : inner ℝ (kmomLab ℓ N k - kmomLab ℓ N s) (vDir N) = 0 := by
    rw [inner_sub_left, hks', sub_self]
  have h1 : kmomLab ℓ N k - kmomLab ℓ N s
      = ℓ⁻¹ • Work.BoseB4.vec (labVec N k - labVec N s) := by
    rw [kmomLab, kmomLab, ← smul_sub, boxVec_sub]
  rw [h1, real_inner_smul_left] at h0
  have hℓ' : ℓ⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hℓ)
  have h2 : inner ℝ (Work.BoseB4.vec (labVec N k - labVec N s)) (vDir N) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hℓ'
  rw [inner_vec_vDir] at h2
  have hpi : (2 * Real.pi * ((4 * (N : ℝ) + 2)⁻¹) ^ 2) ≠ 0 := by positivity
  have hbracket0 : (labVec N k - labVec N s) 0 * (4 * (N : ℝ) + 2) ^ 2
      + (labVec N k - labVec N s) 1 * (4 * (N : ℝ) + 2)
      + (labVec N k - labVec N s) 2 = 0 := (mul_eq_zero.mp h2).resolve_left hpi
  have hdiff : labVec N k - labVec N s = 0 := by
    by_contra hne
    have hb := realQuad_ne_zero (B := 2 * N) hne (fun i => by
      rw [Pi.sub_apply]
      have hk := abs_le.mp (labVec_abs_le N k i)
      have hs₂ := abs_le.mp (labVec_abs_le N s i)
      have hcast : ((2 * N : ℕ) : ℤ) = 2 * (N : ℤ) := by push_cast; ring
      rw [hcast]
      exact abs_sub_le_iff.mpr ⟨by linarith [hk.2, hs₂.1], by linarith [hs₂.2, hk.1]⟩)
    have hMeq : 2 * ((2 * N : ℕ) : ℝ) + 2 = 4 * (N : ℝ) + 2 := by push_cast; ring
    rw [hMeq] at hb
    exact hb hbracket0
  exact labVec_injective_aux N (sub_eq_zero.mp hdiff)

lemma ball_subset_box {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < ℓ / 4) :
    x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ := by
  have hmem : ℓ⁻¹ • x ∈ Work.BoseK15.corpusBox.cell := by
    rw [show Work.BoseK15.corpusBox.cell = Work.BoseB4.unitCell from rfl, Work.BoseB4.unitCell]
    intro i
    have h1 : |(ℓ⁻¹ • x) i| ≤ ℓ⁻¹ * ‖x‖ := by
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hℓ))]
      exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le x i)
        (le_of_lt (inv_pos.mpr hℓ))
    have h2 : ℓ⁻¹ * ‖x‖ < 1 / 4 := by
      have h3 := mul_lt_mul_of_pos_left hx (inv_pos.mpr hℓ)
      have h4 : ℓ⁻¹ * (ℓ / 4) = 1 / 4 := by field_simp
      linarith
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  show x ∈ ℓ • Work.BoseK15.corpusBox.cell
  rwa [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]

/-- **Independence of the physical mode family (the input for the `e₀ ∝ θ` pinning).**
The mode family of the honest model,
`{1_Λ} ∪ {qVec(kmomLab ℓ N k)}_{k ∈ Lab N} ∪ {thetaExp(kmomLab ℓ N s)}_{0 ≠ s ∈ Lab N}`,
is linearly independent: a vanishing complex linear combination has all coefficients zero.
(The `s = 0` θ-mode is `1_Λ` itself and is deliberately dropped; the conclusion is therefore
restricted to `s ≠ 0`.)

Proof route as in the module docstring: on the ball `‖x‖ < ℓ/4` the corpus χ is the constant
`κ`, which evaluates the combination to a trigonometric polynomial; exponential independence
(twice: on the ball, and on the open piece of the box where `χ_Λ = 0`) pins every coefficient.
-/
theorem modeFam_independent {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (c : ℂ) (d b : Lab N → ℂ)
    (h : (fun x : EuclideanSpace ℝ (Fin 3) =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x
          + ∑ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) x
          + ∑ s : Lab N, (if s = 0 then 0 else b s) *
              Work.BoseK15.corpusBox.thetaExp ℓ (kmomLab ℓ N s) x) = 0) :
    c = 0 ∧ d = 0 ∧ ∀ s : Lab N, s ≠ 0 → b s = 0 := by
  classical
  set κ : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hκdef
  have hκ0 : κ ≠ 0 := by
    rw [hκdef]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos))
  have hω0 : kmomLab ℓ N (0 : Lab N) = 0 := by
    rw [kmomLab, labVec_zero_aux]
    ext i
    simp [Work.BoseB4.vec]
  set ω : Lab N → EuclideanSpace ℝ (Fin 3) := kmomLab ℓ N with hωdef
  set χh : Lab N → ℝ := fun k => Work.BoseK15.corpusBox.hatChi (ℓ • ω k) with hχhdef
  set γ : ℂ := c - ∑ k : Lab N, d k * (χh k : ℂ) with hγdef
  set D : Lab N → ℂ := fun k => (κ : ℂ) * d k + (if k = 0 then γ else b k) with hDdef
  have hdir : Function.Injective (fun k : Lab N => inner ℝ (ω k) (vDir N)) :=
    inner_kmomLab_dir_inj (N := N) hℓ
  -- **the vanishing on the ball**
  have hball : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < ℓ / 4 →
      ∑ k : Lab N, D k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)) = 0 := by
    intro x hx
    have hxbox : x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ := ball_subset_box hℓ hx
    have hchi : Work.BoseK15.corpusBox.chiLam ℓ x = κ := by
      rw [hκdef]; exact corpusChiLam_eq_of_norm_lt hℓ hx
    have hθ : Work.BoseK15.corpusBox.thetaFun ℓ x = 1 := by
      rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hxbox]
    have h0 : c * (1 : ℂ) + (∑ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (ω k) x)
        + (∑ s : Lab N, (if s = 0 then 0 else b s) *
            Work.BoseK15.corpusBox.thetaExp ℓ (ω s) x) = 0 := by
      have hx0 := congrFun h x
      simpa only [hθ, mul_one, Pi.zero_apply] using hx0
    have hexp1 : (∑ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (ω k) x)
        = (κ : ℂ) * (∑ k : Lab N, d k *
              Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)))
          - ∑ k : Lab N, d k * (χh k : ℂ) := by
      have hterm : ∀ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (ω k) x
          = (κ : ℂ) * (d k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)))
            - d k * (χh k : ℂ) := by
        intro k
        rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, hχhdef]
        rw [hchi, hθ]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib, Finset.mul_sum]
    have hexp2 : (∑ s : Lab N, (if s = 0 then 0 else b s) *
            Work.BoseK15.corpusBox.thetaExp ℓ (ω s) x)
        = ∑ s : Lab N, (if s = 0 then 0 else b s *
            Complex.exp (Complex.I * ((inner ℝ (ω s) x : ℝ) : ℂ))) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Work.BoseB4.BoxData.thetaExp_apply, hθ, mul_one]
      by_cases hs : s = 0
      · simp [hs]
      · simp [hs]
    rw [hexp1, hexp2] at h0
    -- the algebra
    have hDsum : ∑ k : Lab N, D k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ))
        = (∑ k : Lab N, ((κ : ℂ) * d k) *
              Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)))
          + ∑ k : Lab N, (if k = 0 then γ else b k) *
              Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hDdef]
      ring
    have hκsum : (∑ k : Lab N, ((κ : ℂ) * d k) *
          Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)))
        = (κ : ℂ) * ∑ k : Lab N, d k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hsplit : ∑ k : Lab N, D k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ))
        = c + ((κ : ℂ) * (∑ k : Lab N, d k *
              Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)))
          - ∑ k : Lab N, d k * (χh k : ℂ))
        + ∑ s : Lab N, (if s = 0 then 0 else b s *
            Complex.exp (Complex.I * ((inner ℝ (ω s) x : ℝ) : ℂ))) := by
      rw [hDsum, hκsum,
        sum_ite_mul (a := (0 : Lab N)) (z := γ) (y := b)
          (g := fun s => Complex.exp (Complex.I * ((inner ℝ (ω s) x : ℝ) : ℂ)))]
      have hE0x : Complex.exp (Complex.I * ((inner ℝ (ω (0 : Lab N)) x : ℝ) : ℂ)) = 1 := by
        rw [hω0]; simp
      rw [hE0x, mul_one, hγdef]
      ring
    refine hsplit.trans ?_
    simpa using h0
  have hDzero : ∀ k : Lab N, D k = 0 :=
    expSum_eq_zero_of_eqOn_ball (ω := ω) (v := vDir N) hdir D (x₀ := 0) (ε := ℓ / 4)
      (by positivity) (fun x hx => by
        rw [sub_zero] at hx
        exact hball x hx)
  -- consequences of `hDzero`
  have hbne : ∀ s : Lab N, s ≠ 0 → b s = -(κ : ℂ) * d s := by
    intro s hs
    have h1 : (κ : ℂ) * d s + (if s = 0 then γ else b s) = 0 := by
      simpa [hDdef] using hDzero s
    rw [if_neg hs] at h1
    linear_combination h1
  have hγ0 : γ = -(κ : ℂ) * d 0 := by
    have h1 : (κ : ℂ) * d 0 + γ = 0 := by
      simpa [hDdef] using hDzero 0
    linear_combination h1
  -- **the box identity**
  have hbox : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ →
      (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) - (κ : ℂ)) *
        (∑ k : Lab N, d k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ))) = 0 := by
    intro x hxbox
    have hθ : Work.BoseK15.corpusBox.thetaFun ℓ x = 1 := by
      rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos hxbox]
    have h0 : c * (1 : ℂ) + (∑ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (ω k) x)
        + (∑ s : Lab N, (if s = 0 then 0 else b s) *
            Work.BoseK15.corpusBox.thetaExp ℓ (ω s) x) = 0 := by
      have hx0 := congrFun h x
      simpa only [hθ, mul_one, Pi.zero_apply] using hx0
    have hexp1 : (∑ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (ω k) x)
        = (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) *
              (∑ k : Lab N, d k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ))))
          - ∑ k : Lab N, d k * (χh k : ℂ) := by
      have hterm : ∀ k : Lab N, d k * Work.BoseK15.corpusBox.qVec ℓ (ω k) x
          = (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ)) *
              (d k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)))
            - d k * (χh k : ℂ) := by
        intro k
        rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, hχhdef]
        rw [hθ]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib, Finset.mul_sum]
    have hexp2 : (∑ s : Lab N, (if s = 0 then 0 else b s) *
            Work.BoseK15.corpusBox.thetaExp ℓ (ω s) x)
        = ∑ s : Lab N, (if s = 0 then 0 else b s *
            Complex.exp (Complex.I * ((inner ℝ (ω s) x : ℝ) : ℂ))) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Work.BoseB4.BoxData.thetaExp_apply, hθ, mul_one]
      by_cases hs : s = 0
      · simp [hs]
      · simp [hs]
    rw [hexp1, hexp2] at h0
    set E : Lab N → ℂ := fun k => Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)) with hEdef
    have hE0 : E 0 = 1 := by rw [hEdef]; simp [hω0]
    set P : ℂ := ∑ k : Lab N, d k * E k with hPdef
    set Sχ : ℂ := ∑ k : Lab N, d k * (χh k : ℂ) with hSχdef
    have h0' : c + (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * P - Sχ)
        + ∑ s : Lab N, (if s = 0 then 0 else b s * E s) = 0 := by
      simpa [hPdef, hSχdef, hEdef] using h0
    have hT : ∑ s : Lab N, (if s = 0 then 0 else b s * E s)
        = -(κ : ℂ) * (∑ s : Lab N, (if s = 0 then 0 else d s * E s)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      by_cases hs : s = 0
      · simp [hs]
      · rw [hbne s hs]
        simp only [hs, if_false]
        ring
    have hT2 : P = d 0 + ∑ s : Lab N, (if s = 0 then 0 else d s * E s) := by
      rw [hPdef, sum_split_at (a := (0 : Lab N)) (f := fun k => d k * E k), hE0]
      ring
    have hconst : c - Sχ + (κ : ℂ) * d 0 = 0 := by
      have h1 : γ = c - Sχ := by rw [hγdef]
      rw [← h1, hγ0]
      ring
    have h0'' : c + (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * P - Sχ)
        + (-(κ : ℂ) * (P - d 0)) = 0 := by
      have heq : c + (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * P - Sχ)
          + (-(κ : ℂ) * (P - d 0))
          = c + (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * P - Sχ)
            + ∑ s : Lab N, (if s = 0 then 0 else b s * E s) := by
        rw [hT, hT2]
        ring
      rw [heq]
      exact h0'
    have hχP : (((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) - (κ : ℂ)) * P = 0 :=
      by linear_combination h0'' - hconst
    exact hχP
  -- **the box identity forces the χ-coefficients to vanish**
  obtain ⟨x₁, hx₁⟩ := corpusChi_zero_near hℓ
  have hPzero : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x - x₁‖ < ℓ / 20 →
      ∑ k : Lab N, d k * Complex.exp (Complex.I * ((inner ℝ (ω k) x : ℝ) : ℂ)) = 0 := by
    intro x hx
    obtain ⟨hxbox, hxchi⟩ := hx₁ x hx
    have h1 := hbox x hxbox
    rw [hxchi] at h1
    have hne : ((0 : ℝ) : ℂ) - (κ : ℂ) ≠ 0 := by
      simpa using (neg_ne_zero.mpr hκ0)
    exact (mul_eq_zero.mp h1).resolve_left hne
  have hd0 : ∀ k : Lab N, d k = 0 :=
    expSum_eq_zero_of_eqOn_ball (ω := ω) (v := vDir N) hdir d (x₀ := x₁) (ε := ℓ / 20)
      (by positivity) hPzero
  refine ⟨?_, funext hd0, ?_⟩
  · have hγz : γ = 0 := by
      simpa [hd0 0] using hγ0
    have hcz : c = γ + ∑ k : Lab N, d k * (χh k : ℂ) := by rw [hγdef]; ring
    rw [hcz, hγz, Finset.sum_eq_zero (fun k _ => by rw [hd0 k, zero_mul])]
    ring
  · intro s hs
    rw [hbne s hs, hd0 s]
    ring



end Work.BoseBoxFock

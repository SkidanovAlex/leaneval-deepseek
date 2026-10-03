import Mathlib
import Submission.Work.KMTAreas.IWLqBound_of_scalar

/-!
# The scalar `ℓ^q` Ionescu–Wainger bound implies the vector-valued one, with a *uniform* constant

`Work.Analysis.IWMultiplier.IWLqBoundScalar A Φ q C` is the `ℓ^q(ℤ; ℂ)` bound for the
Ionescu–Wainger multiplier with symbol `iwSymbolSet A Φ`; `Work.Analysis.IWMultiplier.IWLqBound`
is the corresponding bound on `ℓ^q(ℤ; H)` for *every* finite dimensional Hilbert space `H`, with a
constant independent of `H`.

The sibling file `Work.KMTAreas.IWLqBound_of_scalar` proves the *implication* with the constant
hidden in an existential: from a scalar bound with constant `C` it produces **some** `C' > 0` with
the vector bound at `C'` — its proof actually gives `C' = (Ck √p / c) · max C 1`, where `Ck, c` are
the Khintchine constants of the exponent `p = q.toReal`.  The `max C 1` is an artefact of that
proof (`C₀ = max C 1` is used only to make the constant positive); the honest dependence is
*linear* in `C`:

  `‖T f‖_{ℓ^q(ℤ;H)} ≤ (Ck √p / c) · C · ‖f‖_{ℓ^q(ℤ;H)}`   whenever `‖T g‖_{ℓ^q(ℤ;ℂ)} ≤ C ‖g‖`

(the degenerate case `C = 0` is included: the identity holds for every `C ≥ 0`, and the chain of
inequalities then closes with the constant `0`).  This
file proves that statement, i.e. the scalar bound implies the vector-valued one with the *same*
constant up to a fixed factor `Kr = Ck √p / c > 0` depending only on `q`:

`IWLqBoundScalar A Φ q C → IWLqBound A Φ q (C * Kr.toNNReal)`.

The main theorem `IWLqBound_of_scalar_mul` is the immediate consequence: there is a single
`K > 0` (namely `Kr.toNNReal`) with `IWLqBoundScalar A Φ q C → IWLqBound A Φ q (C * K)` for all
`A`, `Φ`, `C`.

## The argument

Fix an orthonormal basis `b₁,…b_d` of `H` and let `v_ε = ∑ᵢ εᵢ bᵢ` be the `2^d` sign sums.
Khintchine's inequality for the coefficients `⟪bᵢ,x⟫` of a vector `x ∈ H` gives, pointwise in `n`,
the two bounds (`p = q.toReal`)

`‖x‖^p ≤ c^{-p} 2^{-d} ∑_ε ‖⟪v_ε,x⟫‖^p`,      `2^{-d} ∑_ε ‖⟪v_ε,x⟫‖^p ≤ (Ck p^{1/2})^p ‖x‖^p`,

which are `Work.KMTAreas.khintchine_lower_orthonormal_basis` and
`Work.KMTAreas.khintchine_upper_orthonormal_basis`.  Applying the lower bound at `x = iwConv f n`
and using that the IW multiplier acts coordinatewise (`inner_iwConv`), the scalar sequences
`g_ε = ⟪v_ε, f⟫` satisfy

`∑_n ‖iwConv f n‖^p ≤ c^{-p} 2^{-d} ∑_ε ∑_n ‖iwConv g_ε n‖^p`
`        ≤ c^{-p} 2^{-d} C^p ∑_ε ∑_n ‖g_ε n‖^p`      (scalar hypothesis, one `ε` at a time)
`        ≤ C^p C_k^p p^{p/2} c^{-p} ∑_n ‖f n‖^p`      (upper Khintchine).

Raising to the power `1/p` gives the `ℓ^q(ℤ;H)` bound with `C' = C · C_k √p / c`, which is
*linear in `C`* and independent of `H`.  Taking the `p`-th powers of the `eLpNorm`s turns all the
series above into `∑'` over `ℤ` in `ℝ≥0∞`, so no summability or measurability hypotheses are ever
needed; the only arithmetic input is

`(c^p)⁻¹ · C^p · A^p = (A/c · C)^p`   (`rpow_inv_mul_mul_aux`),

which holds for every `C ≥ 0` (in particular `C = 0`), so the degenerate case needs no separate
treatment.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier
open Work.Analysis.IonescuWainger

/-- The arithmetic behind the *uniform* constant of the Khintchine reduction: for `0 < c` and
nonnegative `C, A` one has `(c ^ p)⁻¹ * C ^ p * A ^ p = (A / c * C) ^ p`.  (For `p > 0` the
quantity on the right is the `p`-th power of `A / c * C`, so the dependence on `C` is exactly
linear.) -/
private lemma rpow_inv_mul_mul_aux {p c C A : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    (c ^ p)⁻¹ * C ^ p * A ^ p = (A / c * C) ^ p := by
  have h1 : (A / c * C) ^ p = (A / c) ^ p * C ^ p :=
    Real.mul_rpow (div_nonneg hA hc.le) hC
  have h2 : (A / c) ^ p = A ^ p / c ^ p := Real.div_rpow hA hc.le p
  rw [h1, h2, div_eq_mul_inv]
  ring

/-- **The sharp form of the Khintchine reduction.**  For `1 ≤ q < ⊤` there is `Kr > 0`, depending
only on `q`, such that a scalar `ℓ^q`-bound with constant `C` upgrades to the vector-valued
`ℓ^q(ℤ;H)` bound (uniformly in the finite dimensional Hilbert space `H`) with constant
`C * Kr.toNNReal`: the upgrade costs a factor `Kr = C_k √p / c` (with `p = q.toReal`),
*independent of `A`, `Φ` and `C`*. -/
private theorem IWLqBound_of_scalar_sharp {q : ENNReal} (hq1 : 1 ≤ q) (hq2 : q < ⊤) :
    ∃ Kr : ℝ, 0 < Kr ∧ ∀ {A : Finset Work.Analysis.IonescuWainger.Circle}
      {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {C : NNReal},
      Work.Analysis.IWMultiplier.IWLqBoundScalar A Φ q C →
      Work.Analysis.IWMultiplier.IWLqBound A Φ q (C * Kr.toNNReal) := by
  classical
  obtain ⟨p, hp1, hqeq⟩ : ∃ p : ℝ, 1 ≤ p ∧ q = ENNReal.ofReal p :=
    ⟨q.toReal,
      by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (lt_top_iff_ne_top.mp hq2) hq1,
      (ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hq2)).symm⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  obtain ⟨c, hc, hlow⟩ := khintchine_lower_orthonormal_basis p hp1
  obtain ⟨Ck, hCk, hup⟩ := khintchine_upper_orthonormal_basis p hp1
  have hKp : 0 < p ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hKpos : 0 < Ck * p ^ ((1 : ℝ) / 2) / c := div_pos (mul_pos hCk hKp) hc
  refine ⟨Ck * p ^ ((1 : ℝ) / 2) / c, hKpos, ?_⟩
  intro A Φ C h
  have hcoeeq : ((C * (Ck * p ^ ((1 : ℝ) / 2) / c).toNNReal : NNReal) : ℝ)
      = Ck * p ^ ((1 : ℝ) / 2) / c * (C : ℝ) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hKpos.le]
    ring
  intro H _ _ _ f hf
  rw [hcoeeq]
  rw [hqeq]
  have h'' : IWLqBoundScalar A Φ (ENNReal.ofReal p) C := by rw [← hqeq]; exact h
  set d : ℕ := Module.finrank ℂ H with hd
  set bb : OrthonormalBasis (Fin d) ℂ H := stdOrthonormalBasis ℂ H with hbb
  set v : (Fin d → Bool) → H :=
    fun ε => ∑ i, (if ε i then (1 : ℂ) else -1) • bb i with hv
  set g : (Fin d → Bool) → ℤ → ℂ := fun ε n => inner ℂ (v ε) (f n) with hgd
  have hgfin : ∀ ε, (Function.support (g ε)).Finite := by
    intro ε
    refine hf.subset ?_
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro hfn
    exact hn (by simp [hgd, hv, hfn])
  have hkey : ∀ (ε : Fin d → Bool) (n : ℤ),
      inner ℂ (v ε) (iwConv A Φ f n) = iwConv A Φ (g ε) n := by
    intro ε n
    have h1 := inner_iwConv A Φ f hf (v ε) n
    rwa [show (fun m => inner ℂ (v ε) (f m)) = g ε from funext fun m => rfl] at h1
  have hlow' : ∀ x : H, enorm x ^ p ≤ (ENNReal.ofReal (c ^ p))⁻¹ *
      (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ * ∑ ε : Fin d → Bool, enorm (inner ℂ (v ε) x) ^ p := by
    intro x
    exact hlow (x := x)
  have hup' : ∀ x : H, (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
      ∑ ε : Fin d → Bool, enorm (inner ℂ (v ε) x) ^ p
      ≤ ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm x ^ p := by
    intro x
    exact hup (x := x)
  -- pointwise lower bound
  have hpt : ∀ n : ℤ, enorm (iwConv A Φ f n) ^ p ≤
      ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
        ∑ ε, enorm (iwConv A Φ (g ε) n) ^ p := by
    intro n
    refine (hlow' (iwConv A Φ f n)).trans_eq ?_
    refine congrArg _ ?_
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hkey ε n]
  -- pointwise upper bound
  have hpu : ∀ n : ℤ, ∑ ε, enorm (g ε n) ^ p ≤
      ENNReal.ofReal ((2:ℝ) ^ d) *
        (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm (f n) ^ p) := by
    intro n
    have hD0 : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by norm_num) d)
    have hDtop : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h1 := hup' (f n)
    calc ∑ ε, enorm (g ε n) ^ p
        = ENNReal.ofReal ((2:ℝ) ^ d) *
            ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ * ∑ ε, enorm (g ε n) ^ p) := by
          rw [ENNReal.mul_inv_cancel_left hD0 hDtop]
      _ ≤ ENNReal.ofReal ((2:ℝ) ^ d) *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm (f n) ^ p) :=
          mul_le_mul_of_nonneg_left h1 bot_le
  have hA : (∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ (ENNReal.ofReal (C : ℝ)) ^ p *
        ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p := by
    calc ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p
        ≤ ∑ ε, (ENNReal.ofReal (C : ℝ) *
            eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p := by
          refine Finset.sum_le_sum fun ε _ => ?_
          exact ENNReal.rpow_le_rpow (h'' (g ε) (hgfin ε)) hp0.le
      _ = (ENNReal.ofReal (C : ℝ)) ^ p *
            ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ε _ => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have hB : (∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ ENNReal.ofReal ((2:ℝ) ^ d) *
        (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) := by
    calc ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p
        = ∑ ε, ∑' n : ℤ, enorm (g ε n) ^ p := by
          refine Finset.sum_congr rfl fun ε _ => ?_
          exact eLpNorm_count_eq_tsum_rpow hp0 (g ε)
      _ = ∑' n : ℤ, ∑ ε, enorm (g ε n) ^ p := by
          rw [show (∑ ε : Fin d → Bool, ∑' n : ℤ, enorm (g ε n) ^ p)
              = ∑' ε : Fin d → Bool, ∑' n : ℤ, enorm (g ε n) ^ p from (tsum_fintype _).symm,
            ENNReal.tsum_comm]
          simp only [tsum_fintype]
      _ ≤ ∑' n : ℤ, ENNReal.ofReal ((2:ℝ) ^ d) *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm (f n) ^ p) :=
          ENNReal.tsum_le_tsum hpu
      _ = ENNReal.ofReal ((2:ℝ) ^ d) *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hB' : (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
        (∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
    have hD0 : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by norm_num) d)
    have hDtop : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
          (∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p)
        ≤ (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            (ENNReal.ofReal ((2:ℝ) ^ d) *
              (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p)) :=
          mul_le_mul_of_nonneg_left hB bot_le
      _ = ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]
  have hAB : (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
        (∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ (ENNReal.ofReal (C : ℝ)) ^ p *
        (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) := by
    calc (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
          (∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p)
        ≤ (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            ((ENNReal.ofReal (C : ℝ)) ^ p *
              ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p) :=
          mul_le_mul_of_nonneg_left hA bot_le
      _ = (ENNReal.ofReal (C : ℝ)) ^ p *
            ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
              ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p) := by
          rw [← mul_assoc,
            mul_comm ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) ((ENNReal.ofReal (C : ℝ)) ^ p),
            mul_assoc]
      _ ≤ (ENNReal.ofReal (C : ℝ)) ^ p *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) :=
          mul_le_mul_of_nonneg_left hB' bot_le
  have hstep1 : ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p ≤
      (ENNReal.ofReal (c ^ p))⁻¹ * ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
        ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p) := by
    calc ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p
        ≤ ∑' n : ℤ, ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑ ε, enorm (iwConv A Φ (g ε) n) ^ p := ENNReal.tsum_le_tsum hpt
      _ = ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑' n : ℤ, ∑ ε, enorm (iwConv A Φ (g ε) n) ^ p := ENNReal.tsum_mul_left
      _ = ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑ ε, ∑' n : ℤ, enorm (iwConv A Φ (g ε) n) ^ p := by
          congr 1
          rw [show (∑ ε : Fin d → Bool, ∑' n : ℤ, enorm (iwConv A Φ (g ε) n) ^ p)
              = ∑' ε : Fin d → Bool, ∑' n : ℤ, enorm (iwConv A Φ (g ε) n) ^ p
              from (tsum_fintype _).symm, ENNReal.tsum_comm]
          simp only [tsum_fintype]
      _ = ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p := by
          congr 1
          refine Finset.sum_congr rfl fun ε _ => ?_
          exact (eLpNorm_count_eq_tsum_rpow hp0 (iwConv A Φ (g ε))).symm
      _ = (ENNReal.ofReal (c ^ p))⁻¹ * ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p) := by
          rw [mul_assoc]
  have harith : (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal (C : ℝ)) ^ p *
      ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p)
      = ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2) / c * (C : ℝ)) ^ p) := by
    have h1 : (ENNReal.ofReal (c ^ p))⁻¹ = ENNReal.ofReal ((c ^ p)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hc p)).symm
    have h2 : (ENNReal.ofReal (C : ℝ)) ^ p = ENNReal.ofReal ((C : ℝ) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg C.2 hp0.le
    rw [h1, h2, ← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos hc p))),
      ← ENNReal.ofReal_mul (by positivity)]
    exact congrArg ENNReal.ofReal
      (rpow_inv_mul_mul_aux hc C.2 (le_of_lt (mul_pos hCk hKp)))
  have hmain : ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p ≤
      ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2) / c * (C : ℝ)) ^ p) *
        ∑' n : ℤ, enorm (f n) ^ p := by
    calc ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p
        ≤ (ENNReal.ofReal (c ^ p))⁻¹ * ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p) :=
          hstep1
      _ ≤ (ENNReal.ofReal (c ^ p))⁻¹ *
            ((ENNReal.ofReal (C : ℝ)) ^ p *
              (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p)) :=
          mul_le_mul_of_nonneg_left hAB bot_le
      _ = (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal (C : ℝ)) ^ p *
            ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
          rw [mul_assoc, mul_assoc]
      _ = ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2) / c * (C : ℝ)) ^ p) *
            ∑' n : ℤ, enorm (f n) ^ p := by rw [harith]
  have hfin : (eLpNorm (iwConv A Φ f) (ENNReal.ofReal p) Measure.count) ^ p ≤
      (ENNReal.ofReal (Ck * p ^ ((1:ℝ)/2) / c * (C : ℝ)) *
        eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p := by
    have hB : (ENNReal.ofReal (Ck * p ^ ((1:ℝ)/2) / c * (C : ℝ))) ^ p
        = ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2) / c * (C : ℝ)) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hKpos.le C.2) hp0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hB,
      eLpNorm_count_eq_tsum_rpow hp0 (iwConv A Φ f), eLpNorm_count_eq_tsum_rpow hp0 f]
    exact hmain
  exact (ENNReal.rpow_le_rpow_iff hp0).mp hfin

/-- **The scalar Ionescu–Wainger `ℓ^q` bound implies the vector-valued one with a uniform
constant.**  For `1 ≤ q < ⊤` there is a single constant `K > 0`, depending only on `q`, such that
for *every* finite set `A ⊆ ℝ/ℤ` of arithmetic frequencies, every symbol `Φ` and every constant
`C`,

`IWLqBoundScalar A Φ q C  →  IWLqBound A Φ q (C * K)`.

In other words the vector-valued formulation of the Ionescu–Wainger multiplier theorem costs at
most a factor `K = C_k √p / c` (with `p = q.toReal`) over the scalar one, uniformly in `A`, `Φ`
and `C`. -/
theorem IWLqBound_of_scalar_mul {q : ENNReal} (hq1 : 1 ≤ q) (hq2 : q < ⊤) :
    ∃ K : NNReal, 0 < K ∧ ∀ {A : Finset Work.Analysis.IonescuWainger.Circle}
      {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {C : NNReal},
      Work.Analysis.IWMultiplier.IWLqBoundScalar A Φ q C →
      Work.Analysis.IWMultiplier.IWLqBound A Φ q (C * K) := by
  obtain ⟨Kr, hKr, hsharp⟩ := IWLqBound_of_scalar_sharp hq1 hq2
  refine ⟨Kr.toNNReal, Real.toNNReal_pos.mpr hKr, ?_⟩
  intro A Φ C h
  exact hsharp h

end Work.KMTAreas

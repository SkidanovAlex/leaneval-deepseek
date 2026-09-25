import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.mstModelFn_modSeq
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le

/-!
# Vocabulary for the MST §4.3 freezing estimate

MST §4.3 (arXiv:1512.07518) compares the level-`s` model evaluated at `(x,x)` with the same frozen
model evaluated at `(x,x+u)`.  The level-`s` model at scale `2^n` is the `ℓ²(ℤ)`-multiplier with
symbol `φ = Φ_{2^n}·ψ_s` applied to the modulated input `mstModSeq G E f x` (`level_l2_mst_large_n_defs`).

This file fixes the vocabulary of the comparison:

* `mstProfBumpFun P d χ η s n` — the *single* symbol `φ = Φ_{2^n}·ψ_s`;
* `mstProfBumpLp` — its `L^∞(𝕋)`-class;
* `mstArcTransLp β Φ` — the translated class `ξ ↦ Φ (ξ-β)` (the arc-`β` piece of the model);
* `mstSymStarLp u Φ` — the class `ξ ↦ star (fourier u ξ) · Φ ξ`; multiplying the symbol by it is
  the same as *shifting the evaluation index by `u`*: `opMul Φ f hf (x+u) = opMul (mstSymStarLp u Φ) f hf x`;
* `mstFreezeSymFun P d χ η s n u β` — the symbol of the freezing difference at the arc `β`,
  `ξ ↦ (star (fourier u (ξ-β)) - 1) · φ (ξ-β)`, whose sup-norm is the `2^{−n/d}` gain: the factor
  `star (fourier u ζ) - 1 = e(−u ζ) - 1` is `O(u|ζ|)` while the profile contributes `O(2^{−n/d}/|ζ|)`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-! ## The symbols -/

/-- The **profile-times-bump symbol** `φ = Φ_{2^n}·ψ_s` of the level-`s` model at the dyadic scale
`2^n` (the symbol of the single multiplier in MST's reduction of the arc model). -/
def mstProfBumpFun (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s n : ℕ) : Circ → ℂ :=
  fun ξ => mstProf P (2 ^ n) ξ * mstEta d χ η s ξ

@[simp] theorem mstProfBumpFun_apply (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s n : ℕ)
    (ξ : Circ) :
    mstProfBumpFun P d χ η s n ξ = mstProf P (2 ^ n) ξ * mstEta d χ η s ξ := rfl

/-- The **symbol of the freezing difference at the arc `β`**:
`ξ ↦ (star (fourier u (ξ-β)) - 1) · Φ_{2^n}(ξ-β) ψ_s(ξ-β)`.  This is the symbol of the difference
between the frozen multiplier evaluated at `x+u` and at `x`, at the arc `β` (up to the unimodular
phase `fourier u β`). -/
def mstFreezeSymFun (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s n u : ℕ) (β : Circ) :
    Circ → ℂ :=
  fun ξ => (star (fourier (u : ℤ) (ξ - β)) - 1) * mstProfBumpFun P d χ η s n (ξ - β)

@[simp] theorem mstFreezeSymFun_apply (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (s n u : ℕ) (β ξ : Circ) :
    mstFreezeSymFun P d χ η s n u β ξ
      = (star (fourier (u : ℤ) (ξ - β)) - 1) * mstProfBumpFun P d χ η s n (ξ - β) := rfl

/-! ## `L^∞`-membership -/

/-- The conjugate character `ξ ↦ star (fourier u ξ)` is `L^∞` with bound `1`. -/
theorem memLp_starFourier (u : ℤ) :
    MemLp (fun ξ : Circ => star (fourier u ξ)) ⊤ haarT := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (continuous_star.comp (map_continuous (fourier u))).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_star, norm_fourier_apply']

/-- The profile-times-bump symbol is `L^∞`. -/
theorem memLp_mstProfBumpFun (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη : Continuous η) (s n : ℕ) :
    MemLp (mstProfBumpFun P d χ η s n) ⊤ haarT := by
  obtain ⟨-, hProf, hBump⟩ := memLp_mst_symbols P (2 ^ n) (mstC d χ s) η hη
  have hEta : MemLp (mstEta d χ η s) ⊤ haarT := hBump
  have hmem : MemLp (mstProf P (2 ^ n) * mstEta d χ η s) ⊤ haarT := hProf.mul hEta
  convert hmem using 1
  funext ξ
  rw [Pi.mul_apply, mstProfBumpFun_apply]

/-- The freezing-difference symbol is `L^∞`. -/
theorem memLp_mstFreezeSymFun (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη : Continuous η) (s n u : ℕ) (β : Circ) :
    MemLp (mstFreezeSymFun P d χ η s n u β) ⊤ haarT := by
  have h1 : MemLp (fun ξ : Circ => star (fourier (u : ℤ) (ξ - β)) - 1) ⊤ haarT := by
    have hcont : Continuous fun ξ : Circ => star (fourier (u : ℤ) (ξ - β)) - 1 :=
      (continuous_star.comp ((map_continuous (fourier (u : ℤ))).comp
        (continuous_id.sub continuous_const))).sub continuous_const
    refine MemLp.of_bound hcont.aestronglyMeasurable 2 ?_
    filter_upwards with ξ
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_star, norm_fourier_apply', norm_one]
    norm_num
  have h2 : MemLp (fun ξ : Circ => mstProfBumpFun P d χ η s n (ξ - β)) ⊤ haarT :=
    memLp_arcTranslate (memLp_mstProfBumpFun P d χ η hη s n) β
  have hmem : MemLp ((fun ξ : Circ => star (fourier (u : ℤ) (ξ - β)) - 1)
      * fun ξ : Circ => mstProfBumpFun P d χ η s n (ξ - β)) ⊤ haarT := h1.mul h2
  convert hmem using 1
  funext ξ
  rw [Pi.mul_apply, mstFreezeSymFun_apply]

/-- The bump `η` is bounded (it is continuous and vanishes off `[-1/2,1/2]`). -/
theorem exists_bound_mstEta (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : ℕ) (ζ : Circ), ‖mstEta d χ η s ζ‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-(1 / 2) : ℝ) (1 / 2)) hηc.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s ζ => ?_⟩
  rw [mstEta_apply]
  by_cases h : |(2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * iwRep ζ| ≤ 1 / 2
  · exact le_trans (hM _ (by rw [Set.mem_Icc]; exact abs_le.mp h)) (le_max_left _ _)
  · rw [not_le] at h
    rw [hηsup _ h.le]
    simp only [norm_zero]
    exact le_max_right M 0

/-! ## The `L^∞`-classes -/

/-- The `L^∞`-class of the profile-times-bump symbol `φ = Φ_{2^n}·ψ_s`. -/
def mstProfBumpLp (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (s n : ℕ) :
    Lp ℂ ⊤ haarT :=
  MemLp.toLp (mstProfBumpFun P d χ η s n) (memLp_mstProfBumpFun P d χ η hη s n)

/-- The `L^∞`-class of the translate `ξ ↦ Φ (ξ - β)`. -/
def mstArcTransLp (β : Circ) (Φ : Lp ℂ ⊤ haarT) : Lp ℂ ⊤ haarT :=
  MemLp.toLp (arcTranslate β (Φ : Circ → ℂ)) (memLp_arcTranslate (Lp.memLp Φ) β)

/-- The `L^∞`-class of `ξ ↦ star (fourier u ξ) · Φ ξ`.  Multiplication of the symbol by this class
is the same as shifting the evaluation index by `u`. -/
def mstSymStarLp (u : ℤ) (Φ : Lp ℂ ⊤ haarT) : Lp ℂ ⊤ haarT :=
  MemLp.toLp (fun ξ : Circ => star (fourier u ξ) * Φ ξ) ((memLp_starFourier u).mul (Lp.memLp Φ))

/-- The `L^∞`-class of the freezing-difference symbol at the arc `β`. -/
def mstFreezeSymLp (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s n u : ℕ) (β : Circ) : Lp ℂ ⊤ haarT :=
  MemLp.toLp (mstFreezeSymFun P d χ η s n u β) (memLp_mstFreezeSymFun P d χ η hη s n u β)

theorem mstProfBumpLp_coeFn (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s n : ℕ) :
    ((mstProfBumpLp P d χ η hη s n : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] mstProfBumpFun P d χ η s n :=
  MemLp.coeFn_toLp _

theorem mstArcTransLp_coeFn (β : Circ) (Φ : Lp ℂ ⊤ haarT) :
    ((mstArcTransLp β Φ : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] arcTranslate β (Φ : Circ → ℂ) :=
  MemLp.coeFn_toLp _

theorem mstSymStarLp_coeFn (u : ℤ) (Φ : Lp ℂ ⊤ haarT) :
    ((mstSymStarLp u Φ : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] fun ξ : Circ => star (fourier u ξ) * Φ ξ :=
  MemLp.coeFn_toLp _

theorem mstFreezeSymLp_coeFn (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s n u : ℕ) (β : Circ) :
    ((mstFreezeSymLp P d χ η hη s n u β : Lp ℂ ⊤ haarT) : Circ → ℂ)
      =ᵐ[haarT] mstFreezeSymFun P d χ η s n u β :=
  MemLp.coeFn_toLp _

/-- `opMul` depends only on the a.e. class of its symbol. -/
theorem opMul_congr_ae {Φ Ψ : Lp ℂ ⊤ haarT} (h : Φ =ᵐ[haarT] Ψ) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    opMul Φ f hf = opMul Ψ f hf := by
  rw [Lp.ext h]

end

end Work.BourgainPlan.Maximal

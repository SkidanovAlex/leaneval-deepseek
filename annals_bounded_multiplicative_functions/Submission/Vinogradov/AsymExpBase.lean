/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymRefine
import Submission.Vinogradov.HolderReduction
import Submission.Vinogradov.UncertaintyBlock

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §4: the exponent functionals `A_l(b)` of the bootstrap — definitions

The exponent functionals of Section 4 of Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ²
decoupling for the moment curve* (arXiv:1912.09798).

The paper defines, for `l ∈ {0, …, k−1}` and `0 < b ≪ 1`, the quantity `A_l(b)` as the infimum of
all exponents `A` such that `B_{l, (k−l+1)b/l, b}(δ) ≲ δ^{-A}`, where `B_{l,a,b}(δ)` is the
asymmetric bilinear decoupling constant of Definition 3.1.  In our dyadic formalisation
(`AsymDec k hk l N m m' C`) the paper's `δ` is `2^{-N}` and the paper's `a`, `b` are the level
ratios `m/N`, `m'/N`; hence "`≲ δ^{-A}`" becomes "`C ≤ K·2^{N A}`", which is the form used below.

The level pair is a **single pair** — the canonical one `(⌊asymRatio k l · b · N⌋, ⌊b·N⌋)` — not a
down-set region.  ROADMAP session 71 (D) shows this is forced: the pair-matching equations of the two
factors of the Hölder step and the cancellation in the telescoping of (4.5) admit *no* consistent
region of pairs except the diagonal, which fails the cancellation; the canonical choice is the one
that both matches the paper and cancels.  The coarser level pairs that the factors need are then
supplied by the coarsening GLYZ Lemma 3.9 in its uniform form
(`UniformChain.asymDec_of_model_uniform`), whose loss is `O(b·εm)` at the recursion's parameters and
therefore vanishes as `εm → 0`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The exponent set of the asymmetric bilinear decoupling -/

/-- The level-ratio coefficient of GLYZ §4: when the second coarse interval has ratio `b`, the
first one may be taken as coarse as ratio `((k−l+1)/l)·b`.  For `l = 0` the paper's `B_{0,a,b}`
does not depend on `a`, and we use the same numerical convention with `asymRatio k 0 = k`, which
makes the recursion at `l = 1` an exact match. -/
def asymRatio (k l : ℕ) : ℝ :=
  if l = 0 then (k : ℝ) else (((k : ℝ) - (l : ℝ) + 1) / (l : ℝ))

/-- The dyadic level of ratio `c` at scale `N`. -/
noncomputable def lvlOf (c : ℝ) (N : ℕ) : ℕ := ⌊c * (N : ℝ)⌋₊

lemma lvlOf_le_of_mul_le {c : ℝ} {N : ℕ} (h : c * (N : ℝ) ≤ (N : ℝ)) : lvlOf c N ≤ N := by
  rcases le_or_gt 0 (c * (N : ℝ)) with hc | hc
  · have h1 : (lvlOf c N : ℝ) ≤ c * (N : ℝ) := Nat.floor_le hc
    have h2 : ((lvlOf c N : ℕ) : ℝ) ≤ (N : ℝ) := le_trans h1 h
    exact_mod_cast h2
  · have h1 : lvlOf c N = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega

lemma two_le_lvlOf {c : ℝ} {N : ℕ} (h : 2 ≤ c * (N : ℝ)) : 2 ≤ lvlOf c N :=
  Nat.le_floor (by exact_mod_cast h)

lemma lvlOf_mono {c c' : ℝ} {N : ℕ} (h : c ≤ c') : lvlOf c N ≤ lvlOf c' N :=
  Nat.floor_mono (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg N))

lemma lvlOf_lt_of_lt {c : ℝ} {N : ℕ} : c * (N : ℝ) - 1 < (lvlOf c N : ℝ) := by
  have h := Nat.lt_floor_add_one (c * (N : ℝ))
  have h2 : ((lvlOf c N : ℕ) : ℝ) = (⌊c * (N:ℝ)⌋₊ : ℝ) := rfl
  rw [h2]; linarith

/-- **The exponent set of the asymmetric bilinear decoupling** `B_{l,a_l(b),b}` at the canonical
level pair `(⌊asymRatio k l · b · N⌋, ⌊b·N⌋)`: the real numbers `A ≥ 0` for which there is `K > 0`
and `N₀` such that for every level `N ≥ N₀` the asymmetric bilinear decoupling inequality holds at
that single pair with constant `K·2^{N·A}`.

The pair is the **canonical** one of the paper; see the module docstring for why a region of pairs
cannot work.  The level conditions `2 ≤ m₁, m₂` are not imposed here: they are automatic for
`N ≥ N₀` once `N₀` is large, and `N₀` is chosen by the statement. -/
def AsymExpSet (k : ℕ) (hk : 1 ≤ k) (l : ℕ) (b : ℝ) : Set ℝ :=
  {A : ℝ | 0 ≤ A ∧ ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      AsymDec k hk l N (lvlOf (asymRatio k l * b) N) (lvlOf b N)
        (ENNReal.ofReal (K * (2 : ℝ) ^ ((N : ℝ) * A)))}

/-- **The paper's `A_l(b)`**: the infimum of the exponents for which the asymmetric bilinear
decoupling inequality at level ratios `(asymRatio k l · b, b)` holds. -/
noncomputable def Aexp (k : ℕ) (hk : 1 ≤ k) (l : ℕ) (b : ℝ) : ℝ :=
  sInf (AsymExpSet k hk l b)

lemma bddBelow_asymExpSet (k : ℕ) (hk : 1 ≤ k) (l : ℕ) (b : ℝ) :
    BddBelow (AsymExpSet k hk l b) :=
  ⟨0, fun A hA => hA.1⟩

/-- **The exponent set is an up-set.** -/
lemma asymExpSet_mono {k : ℕ} {hk : 1 ≤ k} {l : ℕ} {b : ℝ} {A A' : ℝ}
    (hA : A ∈ AsymExpSet k hk l b) (h : A ≤ A') : A' ∈ AsymExpSet k hk l b := by
  obtain ⟨hA0, K, hK, N₀, hN⟩ := hA
  refine ⟨le_trans hA0 h, K, hK, N₀, fun N hNN => ?_⟩
  refine AsymDec_mono ?_ (hN N hNN)
  have h1 : (1 : ℝ) ≤ 2 := by norm_num
  have h2 : (N : ℝ) * A ≤ (N : ℝ) * A' :=
    mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le h1 h2) hK.le)

lemma Aexp_le_of_mem {k : ℕ} {hk : 1 ≤ k} {l : ℕ} {b : ℝ} {A : ℝ}
    (hA : A ∈ AsymExpSet k hk l b) : Aexp k hk l b ≤ A :=
  csInf_le (bddBelow_asymExpSet k hk l b) hA

/-! ## 2. The `sInf` bookkeeping -/

/-- If `A` is strictly above the infimum of the exponent set then it lies in it (provided the set
is nonempty). -/
lemma asymExpSet_of_sInf_lt {k : ℕ} {hk : 1 ≤ k} {l : ℕ} {b : ℝ}
    (hne : (AsymExpSet k hk l b).Nonempty) {A : ℝ}
    (h : Aexp k hk l b < A) : A ∈ AsymExpSet k hk l b := by
  obtain ⟨A', hA', hlt⟩ :=
    (csInf_lt_iff (bddBelow_asymExpSet k hk l b) hne).mp h
  exact asymExpSet_mono hA' hlt.le

/-- The infimum respects a lower bound. -/
lemma Aexp_le_of_forall {k : ℕ} {hk : 1 ≤ k} {l : ℕ} {b : ℝ} {C : ℝ}
    (hne : (AsymExpSet k hk l b).Nonempty)
    (h : ∀ A ∈ AsymExpSet k hk l b, C ≤ A) : C ≤ Aexp k hk l b :=
  le_csInf hne h


/-! ## 4. The level-ratio arithmetic of the recursion -/

lemma asymRatio_of_pos {k l : ℕ} (hl : 1 ≤ l) :
    asymRatio k l = (((k : ℝ) - (l : ℝ) + 1) / (l : ℝ)) := by
  rw [asymRatio, if_neg (by omega)]

lemma asymRatio_zero (k : ℕ) : asymRatio k 0 = (k : ℝ) := by
  rw [asymRatio, if_pos rfl]

lemma asymRatio_one (k : ℕ) : asymRatio k 1 = (k : ℝ) := by
  rw [asymRatio_of_pos le_rfl]
  simp

lemma asymRatio_pos {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    0 < asymRatio k l := by
  rw [asymRatio_of_pos hl]
  have h1 : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  exact div_pos (by linarith) (by positivity)

lemma asymRatio_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    asymRatio k l ≤ (k : ℝ) := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  rw [asymRatio_of_pos hl, div_le_iff₀ hlR]
  have h1 : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  have h2 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hkey : (k : ℝ) * (l : ℝ) - ((k : ℝ) - (l : ℝ) + 1) = ((l : ℝ) - 1) * ((k : ℝ) + 1) := by
    ring
  have h3 : (0 : ℝ) ≤ ((l : ℝ) - 1) * ((k : ℝ) + 1) :=
    mul_nonneg (by linarith) (by linarith)
  linarith


/-! ## The level-ratio arithmetic of GLYZ (4.4) -/

/-- **`asymRatio k l > 0` for the splits `l ≤ k−1`** (including `l = 0`). -/
lemma asymRatio_pos' {k l : ℕ} (hk : 1 ≤ k) (hl : l ≤ k - 1) : 0 < asymRatio k l := by
  rcases eq_or_lt_of_le (Nat.zero_le l) with h0 | h0
  · rw [← h0, asymRatio_zero]
    exact_mod_cast hk
  · have hl1 : 1 ≤ l := by omega
    exact asymRatio_pos hk hl1 (by omega)

/-- **The level-ratio coefficients decrease in `l`**: `asymRatio k l ≤ asymRatio k (l−1)`. -/
lemma asymRatio_le_pred {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) :
    asymRatio k l ≤ asymRatio k (l - 1) := by
  rcases eq_or_lt_of_le hl with h1 | h2
  · rw [← h1, Nat.sub_self, asymRatio_one, asymRatio_zero]
  · have hl2 : 2 ≤ l := by omega
    rw [asymRatio_of_pos hl, asymRatio_of_pos (by omega : 1 ≤ l - 1)]
    have hle : l ≤ k := by omega
    have hlR : (0 : ℝ) < (l : ℝ) := by positivity
    have hlR2 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast h2
    have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ l)]; norm_num
    have hkR : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
    rw [hcast, div_le_div_iff₀ hlR (by linarith)]
    have hkey : ((k : ℝ) - (l : ℝ) + 1) * ((l : ℝ) - 1)
        = ((k : ℝ) - (l : ℝ) + 2) * (l : ℝ) - ((k : ℝ) + 1) := by ring
    rw [hkey]
    linarith [show (0 : ℝ) ≤ (k : ℝ) + 1 from by positivity]

/-- **The level-ratio coefficients compensate**: `1 ≤ asymRatio k (k−l) · asymRatio k l`.  This is
exactly what makes the first slot of the `(k−l)`-factor of `Aexp_recursion` sit inside its
admissible range. -/
lemma one_le_asymRatio_mul {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1) :
    (1 : ℝ) ≤ asymRatio k (k - l) * asymRatio k l := by
  have hkl : 1 ≤ k - l := by omega
  rw [asymRatio_of_pos hl, asymRatio_of_pos hkl]
  have h1 : ((k - l : ℕ) : ℝ) = (k : ℝ) - (l : ℝ) := by
    rw [Nat.cast_sub (by omega : l ≤ k)]
  have hl0 : (0 : ℝ) < (l : ℝ) := by positivity
  have hkl0 : (0 : ℝ) < (k : ℝ) - (l : ℝ) := by
    have hlt : (l : ℝ) < (k : ℝ) := by
      have : l < k := by omega
      exact_mod_cast this
    linarith
  rw [h1, mul_comm, div_mul_div_comm, le_div_iff₀ (mul_pos hl0 hkl0)]
  nlinarith [hl0, hkl0]

end Submission.Vinogradov

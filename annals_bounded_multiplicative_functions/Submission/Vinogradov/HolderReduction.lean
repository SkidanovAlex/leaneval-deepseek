/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.SymFromAsym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 4.1: the Hölder reduction of the asymmetric constants

The exponents `p_j = j(j+1)` satisfy, with `θ = 1/(k-l+1)`,

  `p_l = θ(p_k - p_{k-l}) + (1-θ)p_{l-1}`  and  `p_k - p_l = θ p_{k-l} + (1-θ)(p_k - p_{l-1})`,

i.e. the three points `(p_l, p_k-p_l)`, `(p_k-p_{k-l}, p_{k-l})` and `(p_{l-1}, p_k-p_{l-1})` are
collinear.  Hölder's inequality therefore bounds `B_{l,a,b}` by a geometric mean of `B_{k-l,b,a}`
and `B_{l-1,a,b}` — GLYZ Lemma 4.1.  This module formalises that step for the dyadic
`AsymDec` predicates:

* `sepLevel_comm` — `sepLevel` is symmetric in its two level/blocks arguments;
* `lintegral_rpow_interp` — Hölder in the form `∫ a^θ b^{1-θ} Φ ≤ (∫aΦ)^θ(∫bΦ)^{1-θ}`;
* `convPow_rpow_holder` — the pointwise Hölder *inside* the convolution
  (`convPow r F Φ ≤ (convPow s F Φ)^θ (convPow t F Φ)^{1-θ}` when `r = θs + (1-θ)t`);
* **`asymDec_of_holder`** — GLYZ Lemma 4.1.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov



lemma sepLevel_comm {m m' : ℕ} (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) :
    sepLevel m m' q q' ↔ sepLevel m' m q' q := by
  unfold sepLevel
  rw [abs_sub_comm]
  constructor <;> intro h <;> linarith

lemma lintegral_rpow_interp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {a b Φ : α → ℝ≥0∞} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (hΦ : AEMeasurable Φ μ) :
    ∫⁻ x, a x ^ θ * b x ^ (1 - θ) * Φ x ∂μ
      ≤ (∫⁻ x, a x * Φ x ∂μ) ^ θ * (∫⁻ x, b x * Φ x ∂μ) ^ (1 - θ) := by
  have h1 : ∀ x, a x ^ θ * b x ^ (1 - θ) * Φ x
      = (a x * Φ x) ^ θ * (b x * Φ x) ^ (1 - θ) := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0.le,
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ 1 - θ)]
    rw [show a x ^ θ * Φ x ^ θ * (b x ^ (1 - θ) * Φ x ^ (1 - θ))
        = (a x ^ θ * b x ^ (1 - θ)) * (Φ x ^ θ * Φ x ^ (1 - θ)) from by ring]
    rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0.le (by linarith : (0:ℝ) ≤ 1 - θ)]
    rw [show θ + (1 - θ) = (1 : ℝ) from by ring, ENNReal.rpow_one]
  rw [lintegral_congr h1]
  have hp : Real.HolderConjugate (1 / θ) (1 / (1 - θ)) :=
    ⟨by field_simp; ring, by positivity, by positivity⟩
  have hf : AEMeasurable (fun x => (a x * Φ x) ^ θ) μ := (ha.mul hΦ).pow_const θ
  have hg : AEMeasurable (fun x => (b x * Φ x) ^ (1 - θ)) μ := (hb.mul hΦ).pow_const (1 - θ)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp hf hg
  refine h.trans (le_of_eq ?_)
  have hA : (∫⁻ x, ((a x * Φ x) ^ θ) ^ ((1 : ℝ) / θ) ∂μ) = ∫⁻ x, a x * Φ x ∂μ :=
    lintegral_congr fun x => by
      rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ (ne_of_gt hθ0), ENNReal.rpow_one]
  have hB : (∫⁻ x, ((b x * Φ x) ^ (1 - θ)) ^ ((1 : ℝ) / (1 - θ)) ∂μ)
      = ∫⁻ x, b x * Φ x ∂μ :=
    lintegral_congr fun x => by
      rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ (by linarith : (1:ℝ) - θ ≠ 0),
        ENNReal.rpow_one]
  rw [hA, hB, show (1 : ℝ) / (1 / θ) = θ from by field_simp,
    show (1 : ℝ) / (1 / (1 - θ)) = 1 - θ from by field_simp]

lemma convPow_rpow_holder {k : ℕ} (F : E k → ℂ) (Φ : E k → ℝ≥0∞) (hF : Measurable F)
    (hΦ : Measurable Φ)
    {θ r s t : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hr : r = θ * s + (1 - θ) * t) (x : E k) :
    convPow k r F Φ x ≤ (convPow k s F Φ x) ^ θ * (convPow k t F Φ x) ^ (1 - θ) := by
  have hA : Measurable (fun y : E k => (‖F (x - y)‖₊ : ℝ≥0∞)) :=
    (hF.comp (measurable_const.sub measurable_id)).nnnorm.coe_nnreal_ennreal
  have hpt : (fun y : E k => ((‖F (x - y)‖₊ : ℝ≥0∞) ^ s) ^ θ
        * ((‖F (x - y)‖₊ : ℝ≥0∞) ^ t) ^ (1 - θ) * Φ y)
      = fun y : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ r * Φ y := by
    funext y
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hs hθ0.le)
        (mul_nonneg ht (by linarith : (0:ℝ) ≤ 1 - θ))]
    rw [show s * θ + t * (1 - θ) = r from by linarith]
  have h := lintegral_rpow_interp (μ := (volume : Measure (E k)))
    (a := fun y : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ s)
    (b := fun y : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ t)
    (Φ := Φ) hθ0 hθ1 (hA.pow_const s).aemeasurable (hA.pow_const t).aemeasurable hΦ.aemeasurable
  rw [hpt] at h
  simpa only [convPow] using h

lemma rpow_mul_rpow_add (X : ℝ≥0∞) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c) :
    X ^ a * X ^ b = X ^ c := by
  rw [← ENNReal.rpow_add_of_nonneg a b ha hb, h]

lemma rpow_rpow_eq (X : ℝ≥0∞) {a b c : ℝ} (h : a * b = c) : (X ^ a) ^ b = X ^ c := by
  rw [← ENNReal.rpow_mul, h]

lemma holder_monomial (C₁ C₂ L L' : ℝ≥0∞) {θ pk pl sl tl : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : 0 ≤ 1 - θ) (hpk0 : 0 ≤ pk)
    (hsl : 0 ≤ sl) (htl : 0 ≤ tl) (hsl2 : 0 ≤ pk - sl) (htl2 : 0 ≤ pk - tl)
    (hpl : pl = θ * (pk - sl) + (1 - θ) * tl)
    (hpr : pk - pl = θ * sl + (1 - θ) * (pk - tl)) :
    (C₁ ^ pk * ((L') ^ sl * L ^ (pk - sl))) ^ θ
        * (C₂ ^ pk * (L ^ tl * (L') ^ (pk - tl))) ^ (1 - θ)
      = (C₁ ^ θ * C₂ ^ (1 - θ)) ^ pk * (L ^ pl * (L') ^ (pk - pl)) := by
  have hA : (C₁ ^ pk * ((L') ^ sl * L ^ (pk - sl))) ^ θ
      = (C₁ ^ pk) ^ θ * (((L') ^ sl) ^ θ * (L ^ (pk - sl)) ^ θ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, ENNReal.mul_rpow_of_nonneg _ _ hθ0]
  have hB : (C₂ ^ pk * (L ^ tl * (L') ^ (pk - tl))) ^ (1 - θ)
      = (C₂ ^ pk) ^ (1 - θ) * ((L ^ tl) ^ (1 - θ) * ((L') ^ (pk - tl)) ^ (1 - θ)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ1, ENNReal.mul_rpow_of_nonneg _ _ hθ1]
  rw [hA, hB, ENNReal.mul_rpow_of_nonneg (C₁ ^ θ) (C₂ ^ (1 - θ)) hpk0]
  rw [rpow_rpow_eq L' (show sl * θ = sl * θ from rfl),
    rpow_rpow_eq L (show (pk - sl) * θ = (pk - sl) * θ from rfl),
    rpow_rpow_eq L (show tl * (1 - θ) = tl * (1 - θ) from rfl),
    rpow_rpow_eq L' (show (pk - tl) * (1 - θ) = (pk - tl) * (1 - θ) from rfl),
    rpow_rpow_eq C₁ (show pk * θ = pk * θ from rfl),
    rpow_rpow_eq C₂ (show pk * (1 - θ) = pk * (1 - θ) from rfl),
    rpow_rpow_eq C₁ (show θ * pk = pk * θ from by ring),
    rpow_rpow_eq C₂ (show (1 - θ) * pk = pk * (1 - θ) from by ring)]
  rw [show C₁ ^ (pk * θ) * (L' ^ (sl * θ) * L ^ ((pk - sl) * θ))
        * (C₂ ^ (pk * (1 - θ)) * (L ^ (tl * (1 - θ)) * L' ^ ((pk - tl) * (1 - θ))))
      = C₁ ^ (pk * θ) * C₂ ^ (pk * (1 - θ))
        * ((L' ^ (sl * θ) * L' ^ ((pk - tl) * (1 - θ)))
          * (L ^ ((pk - sl) * θ) * L ^ (tl * (1 - θ)))) from by ring]
  rw [rpow_mul_rpow_add L' (mul_nonneg hsl hθ0) (mul_nonneg htl2 hθ1)
      (show sl * θ + (pk - tl) * (1 - θ) = pk - pl by rw [hpr]; ring),
    rpow_mul_rpow_add L (mul_nonneg hsl2 hθ0) (mul_nonneg htl hθ1)
      (show (pk - sl) * θ + tl * (1 - θ) = pl by rw [hpl]; ring)]
  ring

theorem asymDec_of_holder {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l + 1 ≤ k)
    (hm : 2 ≤ m) (hmN : m ≤ N) (hm' : 2 ≤ m') (hm'N : m' ≤ N)
    {C₁ C₂ : ℝ≥0∞} (hA₁ : AsymDec k hk (k - l) N m' m C₁)
    (hA₂ : AsymDec k hk (l - 1) N m m' C₂) :
    AsymDec k hk l N m m'
      (C₁ ^ ((1 : ℝ) / ((k - l + 1 : ℕ) : ℝ))
        * C₂ ^ (1 - (1 : ℝ) / ((k - l + 1 : ℕ) : ℝ))) := by
  intro q q' hsep f hf
  have hklR : ((k - l : ℕ) : ℝ) = (k : ℝ) - l := Nat.cast_sub (by omega : l ≤ k)
  have hl1R : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub hl]; push_cast; ring
  have hkl1R : ((k - l + 1 : ℕ) : ℝ) = (k : ℝ) - l + 1 := by
    rw [Nat.cast_add, Nat.cast_one, hklR]
  set θ : ℝ := (1 : ℝ) / ((k - l + 1 : ℕ) : ℝ) with hθdef
  have hθnum : (0 : ℝ) < ((k - l + 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < k - l + 1 := by omega
    exact_mod_cast this
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθlt : θ < 1 := by
    rw [hθdef, div_lt_one hθnum]
    have : (1 : ℕ) < k - l + 1 := by omega
    exact_mod_cast this
  have hθle : 0 ≤ θ := hθpos.le
  have h1mθ : 0 ≤ 1 - θ := by linarith
  have hpk0 : 0 ≤ pkExp k := pkExp_nonneg k
  have hsl0 : 0 ≤ pkExp k - plExp (k - l) := by
    rw [pkExp, plExp]
    have h1 : ((k - l : ℕ) : ℝ) ≤ (k : ℝ) := by
      have : k - l ≤ k := Nat.sub_le _ _
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ (k - l : ℕ) := Nat.cast_nonneg _
    nlinarith
  have htl0 : 0 ≤ plExp (l - 1) := plExp_nonneg _
  have h2l0 : 0 ≤ plExp (k - l) := plExp_nonneg _
  have h2r0 : 0 ≤ pkExp k - plExp (l - 1) :=
    pkExp_sub_plExp_nonneg (by omega : l - 1 ≤ k)
  have hne : (k : ℝ) - l + 1 ≠ 0 := by
    rw [← hkl1R]; exact ne_of_gt hθnum
  have hexp1 : plExp l = θ * (pkExp k - plExp (k - l)) + (1 - θ) * plExp (l - 1) := by
    simp only [plExp, pkExp]
    rw [hθdef, hkl1R, hklR, hl1R]
    field_simp
    ring
  have hexp2 : pkExp k - plExp l = θ * plExp (k - l) + (1 - θ) * (pkExp k - plExp (l - 1)) := by
    simp only [plExp, pkExp]
    rw [hθdef, hkl1R, hklR, hl1R]
    field_simp
    ring
  set Fq : E k → ℂ := fun y => ∑ i ∈ blkFin N m q, f i y with hFq
  set Fq' : E k → ℂ := fun y => ∑ i ∈ blkFin N m' q', f i y with hFq'
  set Φq : E k → ℝ≥0∞ := platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) with hΦq
  set Φq' : E k → ℝ≥0∞ := platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q') with hΦq'
  set Aa : Fin (2 ^ N) → ℝ≥0∞ := fun i => lpNorm k (pE k) (f i) with hAa
  have hFqm : Measurable Fq := by
    rw [hFq]
    exact (continuous_finsetSum _ (fun i _ => (hf i).continuous)).measurable
  have hFq'm : Measurable Fq' := by
    rw [hFq']
    exact (continuous_finsetSum _ (fun i _ => (hf i).continuous)).measurable
  have hΦqm : Measurable Φq := (continuous_platePhi k hk _ _).measurable
  have hΦq'm : Measurable Φq' := (continuous_platePhi k hk _ _).measurable
  -- the two pointwise Hölder steps inside the convolutions
  have hpt1 : ∀ x : E k, convPow k (plExp l) Fq Φq x
      ≤ (convPow k (pkExp k - plExp (k - l)) Fq Φq x) ^ θ
        * (convPow k (plExp (l - 1)) Fq Φq x) ^ (1 - θ) :=
    fun x => convPow_rpow_holder Fq Φq hFqm hΦqm hθpos hθlt hsl0 htl0 hexp1 x
  have hpt2 : ∀ x : E k, convPow k (pkExp k - plExp l) Fq' Φq' x
      ≤ (convPow k (plExp (k - l)) Fq' Φq' x) ^ θ
        * (convPow k (pkExp k - plExp (l - 1)) Fq' Φq' x) ^ (1 - θ) :=
    fun x => convPow_rpow_holder Fq' Φq' hFq'm hΦq'm hθpos hθlt h2l0 h2r0 hexp2 x
  have hpt : ∀ x : E k, convPow k (plExp l) Fq Φq x * convPow k (pkExp k - plExp l) Fq' Φq' x
      ≤ ((convPow k (pkExp k - plExp (k - l)) Fq Φq x) * (convPow k (plExp (k - l)) Fq' Φq' x)) ^ θ
        * ((convPow k (plExp (l - 1)) Fq Φq x)
            * (convPow k (pkExp k - plExp (l - 1)) Fq' Φq' x)) ^ (1 - θ) := by
    intro x
    refine (mul_le_mul' (hpt1 x) (hpt2 x)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθle, ENNReal.mul_rpow_of_nonneg _ _ h1mθ]
    ring
  -- the AsymDec inputs
  have hb1 : ∫⁻ x, convPow k (pkExp k - plExp (k - l)) Fq Φq x
        * convPow k (plExp (k - l)) Fq' Φq' x
      ≤ C₁ ^ (pkExp k) * ((l2Of (blkFin N m' q') Aa) ^ (plExp (k - l))
          * (l2Of (blkFin N m q) Aa) ^ (pkExp k - plExp (k - l))) := by
    refine (le_of_eq ?_).trans ((hA₁ q' q ((sepLevel_comm q q').mp hsep) f hf).trans (le_of_eq (by ring)))
    refine lintegral_congr fun x => ?_
    ring
  have hb2 : ∫⁻ x, convPow k (plExp (l - 1)) Fq Φq x
        * convPow k (pkExp k - plExp (l - 1)) Fq' Φq' x
      ≤ C₂ ^ (pkExp k) * ((l2Of (blkFin N m q) Aa) ^ (plExp (l - 1))
          * (l2Of (blkFin N m' q') Aa) ^ (pkExp k - plExp (l - 1))) := by
    refine (le_of_eq ?_).trans ((hA₂ q q' hsep f hf).trans (le_of_eq (by ring)))
    refine lintegral_congr fun x => ?_
    ring
  -- the integral Hölder step
  have hma : AEMeasurable (fun x : E k => convPow k (pkExp k - plExp (k - l)) Fq Φq x
      * convPow k (plExp (k - l)) Fq' Φq' x) volume :=
    ((measurable_convPow k _ hFqm hΦqm).mul (measurable_convPow k _ hFq'm hΦq'm)).aemeasurable
  have hmb : AEMeasurable (fun x : E k => convPow k (plExp (l - 1)) Fq Φq x
      * convPow k (pkExp k - plExp (l - 1)) Fq' Φq' x) volume :=
    ((measurable_convPow k _ hFqm hΦqm).mul (measurable_convPow k _ hFq'm hΦq'm)).aemeasurable
  have hInt := lintegral_rpow_interp (μ := (volume : Measure (E k)))
    (a := fun x : E k => convPow k (pkExp k - plExp (k - l)) Fq Φq x
      * convPow k (plExp (k - l)) Fq' Φq' x)
    (b := fun x : E k => convPow k (plExp (l - 1)) Fq Φq x
      * convPow k (pkExp k - plExp (l - 1)) Fq' Φq' x)
    (Φ := fun _ => 1) hθpos hθlt hma hmb measurable_const.aemeasurable
  simp only [Pi.one_apply, mul_one] at hInt
  refine ((lintegral_mono hpt).trans hInt).trans ?_
  refine (mul_le_mul' (ENNReal.rpow_le_rpow hb1 hθle)
    (ENNReal.rpow_le_rpow hb2 h1mθ)).trans (le_of_eq ?_)
  rw [holder_monomial C₁ C₂ (l2Of (blkFin N m q) Aa) (l2Of (blkFin N m' q') Aa)
    hθle h1mθ hpk0 h2l0 htl0 hsl0 h2r0 hexp1 hexp2]
  ring


end Submission.Vinogradov

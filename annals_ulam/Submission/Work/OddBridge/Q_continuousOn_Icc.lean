import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.Analysis.SpecialFunctions.iteratedDeriv_rpow_comp_bound
import Submission.Work.OddBridge.E1_E2_eq_tailIntegral
import Submission.Work.OddBridge.contDiffOn_Q_Ioo
import Submission.Work.Analysis.Calculus.parametric_iteratedDeriv_bound
import Submission.Work.OddVolterra.Smooth.Slice

/-!
# Continuity of `Q n h` on `[a, 1]`

This file proves `Work.OddBridge.Q_continuousOn_Icc`.  The two components of
`Q n h` are `-E1 n h s + ∂^{n+1}(momentRHS n) s` and `-E2 n h s`.  Since `h` vanishes on the
transition window `[1 - tau, 1]`, both `E1` and `E2` are unchanged there by the corresponding
`h = 0` quantities; the only non-trivial point is the right end point `s = 1`, where the
radicand `1 - (1 + s^2) t^2` vanishes at the two endpoints `t = ±profileX 1` of the
integration interval.

The proof of the endpoint continuity is a dominated-convergence argument:
* the sharp Faà di Bruno bound `iteratedDeriv_rpow_comp_bound_sharp` gives
  `|∂^K (1 - (1 + u^2) t^2)^(K - 1/2)| ≤ K * (1 - (1 + s^2) t^2)^{-1/2}` uniformly in `s`;
* substituting `t = profileX 1 * sin θ` turns the singular weight into the bounded
  `cos θ / sqrt(cos θ ^ 2 + (1 - s^2) sin θ ^ 2 / 2) ≤ 1`.
-/

set_option maxHeartbeats 800000

namespace Work.OddBridge

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval Real

noncomputable section

/-! ## A sharp Faà di Bruno bound for `Φ ^ p`

The Faà di Bruno formula `iteratedDeriv_comp_eq_sum_orderedFinpartition` writes the `(n+1)`-st
derivative of `Φ ^ p` as a sum over ordered partitions of `n + 1`:

`∑ σ, ∂^{σ.length}(y ↦ y^p)(Φ 0) * ∏ j, ∂^{σ.partSize j} Φ 0`.

Since `∂^k(y ↦ y^p)(ρ) = (p)_k * ρ^(p-k)`, each term is bounded by
`B * (Φ 0)^(p - n - 1) * C ^ σ.length` as soon as `0 < Φ 0 ≤ 1` and the derivatives of `Φ` at
`0` are bounded by `C`.  This is the *sharp* version of
`Work.Analysis.SpecialFunctions.iteratedDeriv_rpow_comp_bound`: the constant does not depend on
`Φ 0`. -/

private lemma iteratedDeriv_rpow_sharp (p ρ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => y ^ p) ρ
      = (descPochhammer ℝ k).eval p * ρ ^ (p - (k : ℝ)) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

private lemma abs_descPochhammer_eval_le_sharp (p : ℝ) {k n : ℕ} (hk : k ≤ n + 1) :
    |(descPochhammer ℝ k).eval p| ≤ ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ)) := by
  rw [descPochhammer_eval_eq_prod_range, Finset.abs_prod]
  have h1 : ∏ i ∈ Finset.range k, |p - (i : ℝ)| ≤
      ∏ i ∈ Finset.range k, (1 + |p| + (i : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact abs_nonneg _
    · intro i _
      have hle : |p - (i : ℝ)| ≤ |p| + (i : ℝ) := by
        rw [abs_sub_le_iff]
        constructor
        · have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          linarith [le_abs_self p, hi]
        · linarith [neg_le_abs p]
      linarith
  have h2 : ∏ i ∈ Finset.range k, (1 + |p| + (i : ℝ)) ≤
      ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ)) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _; positivity
    · intro i _ _
      have ha : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have hb : (0 : ℝ) ≤ |p| := abs_nonneg p
      linarith
  exact le_trans h1 h2

/-- **Sharp Faà di Bruno bound.**  If `0 < Φ 0 ≤ 1` and the derivatives of `Φ` at `0` of order
at most `n + 1` are bounded by `C`, then the `(n+1)`-st derivative of `Φ ^ p` at `0` is bounded
by a constant (depending only on `p`, `n`, `C`) times `(Φ 0) ^ (p - (n + 1))`. -/
theorem iteratedDeriv_rpow_comp_bound_sharp (p : ℝ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Φ : ℝ → ℝ) (x : ℝ), ContDiffAt ℝ (n + 1) Φ x → 0 < Φ x → Φ x ≤ 1 →
      (∀ j ≤ n + 1, |iteratedDeriv j Φ x| ≤ C) →
      |iteratedDeriv (n + 1) (fun y : ℝ => (Φ y) ^ p) x| ≤ K * (Φ x) ^ (p - ((n : ℝ) + 1)) := by
  let B : ℝ := ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ))
  have hBnn : 0 ≤ B := by
    show 0 ≤ ∏ i ∈ Finset.range (n + 2), (1 + |p| + (i : ℝ))
    exact Finset.prod_nonneg (fun i _ => by positivity)
  refine ⟨∑ σ : OrderedFinpartition (n + 1), B * C ^ σ.length, ?_, ?_⟩
  · exact Finset.sum_nonneg fun σ _ => mul_nonneg hBnn (pow_nonneg hC _)
  intro Φ x hΦ hΦpos hΦle hderiv
  have hg : ContDiffAt ℝ (n + 1) (fun y : ℝ => y ^ p) (Φ x) :=
    Real.contDiffAt_rpow_const (n := n + 1) (Or.inl hΦpos.ne')
  have hcomp : iteratedDeriv (n + 1) (fun y : ℝ => (Φ y) ^ p) x =
      ∑ σ : OrderedFinpartition (n + 1),
        iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ x) *
          ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ x := by
    have h := iteratedDeriv_comp_eq_sum_orderedFinpartition (𝕜 := ℝ)
      (g := fun y : ℝ => y ^ p) (f := Φ) (x := x) (i := n + 1) hg hΦ le_rfl
    simpa [Function.comp_def] using h
  have htarget : ∀ σ : OrderedFinpartition (n + 1),
      |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ x) *
          ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ x|
        ≤ B * C ^ σ.length * (Φ x) ^ (p - ((n : ℝ) + 1)) := by
    intro σ
    have hslen : σ.length ≤ n + 1 := σ.length_le
    have hP : |∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ x| ≤ C ^ σ.length := by
      rw [Finset.abs_prod]
      calc ∏ j : Fin σ.length, |iteratedDeriv (σ.partSize j) Φ x|
          ≤ ∏ _j : Fin σ.length, C :=
            Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
              (fun j _ => hderiv _ (le_trans (σ.partSize_le j) le_rfl))
        _ = C ^ σ.length := by simp [Finset.prod_const]
    have hA : |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ x)|
        ≤ B * (Φ x) ^ (p - ((n : ℝ) + 1)) := by
      rw [iteratedDeriv_rpow_sharp, abs_mul, abs_of_nonneg (Real.rpow_nonneg hΦpos.le _)]
      refine mul_le_mul (abs_descPochhammer_eval_le_sharp p hslen) ?_ (Real.rpow_nonneg hΦpos.le _) hBnn
      refine Real.rpow_le_rpow_of_exponent_ge hΦpos hΦle ?_
      have hsr : ((σ.length : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hslen
      linarith
    calc |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ x) *
            ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ x|
        = |iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ x)| *
            |∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ x| := abs_mul _ _
      _ ≤ (B * (Φ x) ^ (p - ((n : ℝ) + 1))) * C ^ σ.length :=
            mul_le_mul hA hP (abs_nonneg _) (mul_nonneg hBnn (Real.rpow_nonneg hΦpos.le _))
      _ = B * C ^ σ.length * (Φ x) ^ (p - ((n : ℝ) + 1)) := by ring
  calc |iteratedDeriv (n + 1) (fun y : ℝ => (Φ y) ^ p) x|
      = |∑ σ : OrderedFinpartition (n + 1),
          iteratedDeriv σ.length (fun y : ℝ => y ^ p) (Φ x) *
            ∏ j : Fin σ.length, iteratedDeriv (σ.partSize j) Φ x| := by rw [hcomp]
    _ ≤ ∑ σ : OrderedFinpartition (n + 1),
          B * C ^ σ.length * (Φ x) ^ (p - ((n : ℝ) + 1)) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun σ _ => htarget σ)
    _ = (∑ σ : OrderedFinpartition (n + 1), B * C ^ σ.length) * (Φ x) ^ (p - ((n : ℝ) + 1)) := by
        rw [Finset.sum_mul]

/-! ## The bound after the substitution `t = profileX 1 * sin θ` -/

/-- `Bsub s θ = cos θ ^ 2 + (1 - s ^ 2) sin θ ^ 2 / 2`: the radicand `1 - (1 + s ^ 2) t ^ 2`
after the substitution `t = profileX 1 * sin θ` (using `(profileX 1) ^ 2 = 1 / 2`). -/
def Bsub (s θ : ℝ) : ℝ := Real.cos θ ^ 2 + (1 - s ^ 2) * Real.sin θ ^ 2 / 2

lemma Bsub_pos {s θ : ℝ} (hs : 0 < 1 - s ^ 2) : 0 < Bsub s θ := by
  unfold Bsub
  rcases eq_or_ne (Real.sin θ) 0 with h | h
  · have hc : Real.cos θ ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [h] at this
      nlinarith
    rw [h, hc]
    norm_num
  · have hsin2 : 0 < Real.sin θ ^ 2 := sq_pos_of_ne_zero h
    have h1 : 0 < (1 - s ^ 2) * Real.sin θ ^ 2 / 2 := by positivity
    have hc : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    linarith

lemma Bsub_le_one (s θ : ℝ) : Bsub s θ ≤ 1 := by
  unfold Bsub
  have h := Real.sin_sq_add_cos_sq θ
  nlinarith [h, sq_nonneg s, sq_nonneg (Real.sin θ)]

/-- **The endpoint bound in the substituted variable.**  For `K ≥ 1`,
`|∂^K B(·,θ)^(K - 1/2)(s)| * cos θ` is uniformly bounded on `1/2 < s < 1`,
`|θ| ≤ π/2`.  The exponent `K - 1/2` is exactly the one that makes the singular weight
`B ^ (-1/2)` cancel against the Jacobian `cos θ` of the substitution `t = profileX 1 * sin θ`. -/
theorem cosWeight_bound (K : ℕ) (hK : 1 ≤ K) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1, ∀ θ ∈ Set.Icc (-(π / 2)) (π / 2),
      |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s| * Real.cos θ ≤ Cb := by
  have hF : ContDiffOn ℝ ⊤ (fun q : ℝ × ℝ => Bsub q.2 q.1) Set.univ := by
    refine ContDiff.contDiffOn ?_
    unfold Bsub
    fun_prop
  have hKK : IsCompact (Set.Icc (-(π / 2)) (π / 2) ×ˢ Set.Icc (1 / 2 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hbounds : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ Set.Icc (-(π / 2)) (π / 2) ×ˢ Set.Icc (1 / 2 : ℝ) 1,
        |iteratedDeriv j (fun u : ℝ => Bsub u q.1) q.2| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := Work.Analysis.Calculus.parametric_iteratedDeriv_bound
      (F := fun θ u => Bsub u θ) isOpen_univ hF hKK (Set.subset_univ _) j
    exact ⟨max C 1, le_trans zero_le_one (le_max_right C 1),
      fun q hq => le_trans (hC q hq) (le_max_left _ _)⟩
  choose Cd hCdnn hCd using hbounds
  obtain ⟨Csh, hCshnn, hCsh⟩ := iteratedDeriv_rpow_comp_bound_sharp ((K : ℝ) - 1 / 2) (K - 1)
    (C := ∑ j ∈ Finset.range (K + 1), Cd j) (Finset.sum_nonneg fun j _ => hCdnn j)
  refine ⟨Csh, hCshnn, ?_⟩
  intro s hs θ hθ
  have hs1 : (1 / 2 : ℝ) < s := hs.1
  have hs2 : s < 1 := hs.2
  have hspos : 0 < 1 - s ^ 2 := by nlinarith
  have hBpos : 0 < Bsub s θ := Bsub_pos hspos
  have hBle : Bsub s θ ≤ 1 := Bsub_le_one s θ
  have hderiv : ∀ j ≤ K - 1 + 1,
      |iteratedDeriv j (fun u : ℝ => Bsub u θ) s| ≤ ∑ j ∈ Finset.range (K + 1), Cd j := by
    intro j hj
    have hjK : j ≤ K := by omega
    have hq : (θ, s) ∈ Set.Icc (-(π / 2)) (π / 2) ×ˢ Set.Icc (1 / 2 : ℝ) 1 :=
      ⟨hθ, ⟨hs1.le, hs2.le⟩⟩
    refine le_trans (hCd j (θ, s) hq) ?_
    exact Finset.single_le_sum (fun i _ => hCdnn i) (by simp only [Finset.mem_range]; omega)
  have hcd : ContDiffAt ℝ (K - 1 + 1) (fun u : ℝ => Bsub u θ) s := by
    refine ContDiff.contDiffAt ?_
    unfold Bsub
    fun_prop
  have hmain := hCsh (fun u : ℝ => Bsub u θ) s hcd hBpos hBle hderiv
  have hidx : K - 1 + 1 = K := Nat.sub_add_cancel hK
  rw [hidx] at hmain
  have hcast : (((K - 1 : ℕ)) : ℝ) + 1 = (K : ℝ) := by
    rw [Nat.cast_sub hK]; norm_num
  have hexp : (K : ℝ) - 1 / 2 - (K : ℝ) = -(1 / 2 : ℝ) := by ring
  have hexp' : (K : ℝ) - 1 / 2 - ((((K - 1 : ℕ)) : ℝ) + 1) = -(1 / 2 : ℝ) := by
    rw [hcast]; ring
  first
   | rw [hexp'] at hmain
   | rw [hexp] at hmain
  have hcosnn : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
  have hBpos' : 0 < Bsub s θ := hBpos
  have hBsqrtpos : 0 < Real.sqrt (Bsub s θ) := Real.sqrt_pos.mpr hBpos'
  have hle : Real.cos θ ≤ Real.sqrt (Bsub s θ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hs2nn : 0 ≤ 1 - s ^ 2 := le_of_lt hspos
    have hsin2 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    unfold Bsub
    nlinarith
  calc |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s| * Real.cos θ
      ≤ (Csh * Bsub s θ ^ (-(1 / 2) : ℝ)) * Real.cos θ := mul_le_mul_of_nonneg_right hmain hcosnn
    _ = Csh * (Real.sqrt (Bsub s θ))⁻¹ * Real.cos θ := by
        rw [Real.rpow_neg (le_of_lt hBpos) (1 / 2), ← Real.sqrt_eq_rpow]
    _ ≤ Csh := by
        have h1 : (Real.sqrt (Bsub s θ))⁻¹ * Real.cos θ ≤ 1 := by
          calc (Real.sqrt (Bsub s θ))⁻¹ * Real.cos θ
              ≤ (Real.sqrt (Bsub s θ))⁻¹ * Real.sqrt (Bsub s θ) :=
                mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hBsqrtpos.le)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hBsqrtpos)
        calc Csh * (Real.sqrt (Bsub s θ))⁻¹ * Real.cos θ
            = Csh * ((Real.sqrt (Bsub s θ))⁻¹ * Real.cos θ) := by ring
          _ ≤ Csh * 1 := mul_le_mul_of_nonneg_left h1 hCshnn
          _ = Csh := mul_one Csh

/-! ## The tail integrals and their `θ`-substituted form -/

/-- `profileX 1 ^ 2 = 1 / 2`. -/
lemma profileX_one_sq : (Commons.Geometry.Ulam.profileX 1) ^ 2 = (1 : ℝ) / 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Commons.Geometry.Ulam.profileX, show (1 : ℝ) + 1 ^ 2 = 2 by norm_num, div_pow,
    one_pow, Real.sq_sqrt h2.le]

lemma profileX_one_pos : 0 < Commons.Geometry.Ulam.profileX 1 :=
  Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)

/-- The tail integral over the fixed interval `[-profileX 1, profileX 1]`, with a weight `g`
(the two instances are `g = 1` for `E1` and `g = t` for `E2`). -/
def tailT (K : ℕ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (-(Commons.Geometry.Ulam.profileX 1))..(Commons.Geometry.Ulam.profileX 1),
    g t * iteratedDeriv K (fun u : ℝ => (1 - (1 + u ^ 2) * t ^ 2) ^ ((K : ℝ) - 1 / 2)) s

/-- The same integral after the substitution `t = profileX 1 * sin θ`. -/
def tailTheta (K : ℕ) (g : ℝ → ℝ) (s θ : ℝ) : ℝ :=
  g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ) *
    iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s *
    (Commons.Geometry.Ulam.profileX 1 * Real.cos θ)

/-- **The change of variables `t = profileX 1 * sin θ`** for the tail integrals. -/
lemma tailT_eq_theta (K : ℕ) (g : ℝ → ℝ) (s : ℝ) :
    tailT K g s = ∫ θ in (-(π / 2))..(π / 2), tailTheta K g s θ := by
  have hx2 : (Commons.Geometry.Ulam.profileX 1) ^ 2 = (1 : ℝ) / 2 := profileX_one_sq
  have hpi : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2)
    (f := fun θ : ℝ => Commons.Geometry.Ulam.profileX 1 * Real.sin θ)
    (f' := fun θ : ℝ => Commons.Geometry.Ulam.profileX 1 * Real.cos θ)
    (g := fun t : ℝ => g t *
      iteratedDeriv K (fun u : ℝ => (1 - (1 + u ^ 2) * t ^ 2) ^ ((K : ℝ) - 1 / 2)) s)
    (by fun_prop)
    (fun θ _ => (Real.hasDerivAt_sin θ).const_mul (Commons.Geometry.Ulam.profileX 1))
    (fun θ hθ => by
      simp only [min_eq_left hpi, max_eq_right hpi] at hθ
      exact mul_nonneg (le_of_lt profileX_one_pos)
        (Real.cos_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  simp only [min_eq_left hpi, max_eq_right hpi] at hsub
  have hend_l : Commons.Geometry.Ulam.profileX 1 * Real.sin (-(π / 2))
      = -(Commons.Geometry.Ulam.profileX 1) := by
    rw [Real.sin_neg, Real.sin_pi_div_two]; ring
  have hend_r : Commons.Geometry.Ulam.profileX 1 * Real.sin (π / 2)
      = Commons.Geometry.Ulam.profileX 1 := by
    rw [Real.sin_pi_div_two]; ring
  rw [hend_l, hend_r] at hsub
  unfold tailT tailTheta
  rw [← hsub]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  have hpt : (fun u : ℝ => (1 - (1 + u ^ 2)
        * (Commons.Geometry.Ulam.profileX 1 * Real.sin θ) ^ 2) ^ ((K : ℝ) - 1 / 2))
      = (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) := by
    funext u
    have hb : 1 - (1 + u ^ 2) * (Commons.Geometry.Ulam.profileX 1 * Real.sin θ) ^ 2
        = Bsub u θ := by
      unfold Bsub
      rw [mul_pow, hx2]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hb]
  simp only [Function.comp_apply, hpt]

/-! ## Joint continuity of the parametric iterated derivatives -/

/-- The `K`-th `u`-derivative of `u ↦ Bsub u θ ^ p`, as a function of `(θ, s)`, is continuous
wherever `Bsub s θ > 0`. -/
lemma contDiffOn_iteratedDeriv_Bsub (K : ℕ) (p : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => iteratedDeriv K (fun u : ℝ => Bsub u q.1 ^ p) q.2)
      {q : ℝ × ℝ | 0 < Bsub q.2 q.1} := by
  have hU : IsOpen {q : ℝ × ℝ | 0 < Bsub q.2 q.1} := by
    apply isOpen_lt continuous_const
    unfold Bsub
    fun_prop
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Bsub q.2 q.1 ^ p)
      {q : ℝ × ℝ | 0 < Bsub q.2 q.1} := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Bsub q.2 q.1)
        {q : ℝ × ℝ | 0 < Bsub q.2 q.1} := by
      refine ContDiff.contDiffOn ?_
      unfold Bsub
      fun_prop
    exact h1.rpow_const_of_ne (fun q hq => ne_of_gt hq)
  exact Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv
    (F := fun θ u => Bsub u θ ^ p) hU hF

/-! ## A small almost-everywhere helper -/

private lemma ae_restrict_of_forall_mem {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {p : α → Prop} (h : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ.restrict s, p x := by
  filter_upwards [MeasureTheory.ae_restrict_of_ae (Filter.Eventually.of_forall h),
    MeasureTheory.ae_restrict_mem hs] with x hx hxs
  exact hx hxs

/-! ## Continuity of the tail integral at the right end point -/

/-- **Endpoint continuity of the tail integral.**  For `K ≥ 1` and any weight `g` bounded by `1`
on `[-profileX 1, profileX 1]`, the tail integral is continuous at `s = 1` from the left. -/
theorem tailT_tendsto (K : ℕ) (hK : 1 ≤ K) (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ t : ℝ, |t| ≤ Commons.Geometry.Ulam.profileX 1 → |g t| ≤ 1) :
    Tendsto (tailT K g) (𝓝[Set.Iio 1] 1) (𝓝 (tailT K g 1)) := by
  obtain ⟨Cb, hCbnn, hCb⟩ := cosWeight_bound K hK
  have hXpos : 0 < Commons.Geometry.Ulam.profileX 1 := profileX_one_pos
  have hXnn : 0 ≤ Commons.Geometry.Ulam.profileX 1 := le_of_lt hXpos
  have hpi : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  set l : Filter ℝ := 𝓝[Set.Iio 1] 1 with hl
  set μ : Measure ℝ := volume.restrict (Set.Ioo (-(π / 2)) (π / 2)) with hμ
  have hUopen : IsOpen {q : ℝ × ℝ | 0 < Bsub q.2 q.1} := by
    apply isOpen_lt continuous_const
    unfold Bsub
    fun_prop
  -- continuity of the `θ`-integrand at fixed `s`
  have hcontθ : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      ContinuousOn (fun θ : ℝ => tailTheta K g s θ) (Set.Icc (-(π / 2)) (π / 2)) := by
    intro s hs
    have hjoint := (contDiffOn_iteratedDeriv_Bsub K ((K : ℝ) - 1 / 2)).continuousOn
    have hfam : ContinuousOn
        (fun θ : ℝ => iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s)
        (Set.Icc (-(π / 2)) (π / 2)) := by
      have key : ContinuousOn
          ((fun q : ℝ × ℝ => iteratedDeriv K (fun u : ℝ => Bsub u q.1 ^ ((K : ℝ) - 1 / 2)) q.2)
            ∘ fun θ : ℝ => (θ, s)) (Set.Icc (-(π / 2)) (π / 2)) :=
        hjoint.comp ((continuous_id.prodMk continuous_const).continuousOn)
          (fun θ _ => Bsub_pos (by nlinarith [hs.1, hs.2]))
      simpa only [Function.comp_def] using key
    have hgc : ContinuousOn
        (fun θ : ℝ => g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ))
        (Set.Icc (-(π / 2)) (π / 2)) :=
      hg.comp_continuousOn (by fun_prop)
    have hcc : ContinuousOn
        (fun θ : ℝ => Commons.Geometry.Ulam.profileX 1 * Real.cos θ)
        (Set.Icc (-(π / 2)) (π / 2)) := by fun_prop
    refine ((hgc.mul hfam).mul hcc).congr ?_
    intro θ _
    simp only [tailTheta, Pi.mul_apply]
  have hfin : ∀ᶠ s in l, s ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    have hmem : Set.Ioi (1 / 2 : ℝ) ∈ l :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioi (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hmem] with s hs hs2
    exact ⟨hs2, hs⟩
  have hmeas : ∀ᶠ s in l, AEStronglyMeasurable (tailTheta K g s) μ := by
    filter_upwards [hfin] with s hs
    exact ((hcontθ s hs).mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hbound : ∀ᶠ s in l,
      ∀ᵐ θ ∂μ, ‖tailTheta K g s θ‖ ≤ Commons.Geometry.Ulam.profileX 1 * Cb := by
    filter_upwards [hfin] with s hs
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hcosnn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hg1 : |g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ)| ≤ 1 := hgb _ (by
      rw [abs_mul, abs_of_pos hXpos]
      nlinarith [Real.abs_sin_le_one θ])
    have hbnd := hCb s hs θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1 : |tailTheta K g s θ| ≤ |iteratedDeriv K
          (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s|
          * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ) := by
      have hXc : 0 ≤ Commons.Geometry.Ulam.profileX 1 * Real.cos θ := mul_nonneg hXnn hcosnn
      simp only [tailTheta, abs_mul, abs_of_nonneg hXnn, abs_of_nonneg hcosnn,
        abs_of_nonneg (abs_nonneg _)]
      calc |g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ)|
              * |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s|
              * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ)
          = (|g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ)|
              * |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s|)
              * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ) := by ring
        _ ≤ (1 * |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s|)
              * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hg1 (abs_nonneg _)) hXc
        _ = |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s|
              * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ) := by ring
    calc ‖tailTheta K g s θ‖ = |tailTheta K g s θ| := Real.norm_eq_abs _
      _ ≤ |iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s|
            * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ) := h1
      _ = Commons.Geometry.Ulam.profileX 1
            * (|iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s| * Real.cos θ) := by
          ring
      _ ≤ Commons.Geometry.Ulam.profileX 1 * Cb := mul_le_mul_of_nonneg_left hbnd hXnn
  have hint : Integrable (fun _ : ℝ => Commons.Geometry.Ulam.profileX 1 * Cb) μ := by
    rw [hμ, MeasureTheory.integrable_const_iff]
    exact Or.inr (by
      rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun s : ℝ => tailTheta K g s θ) l (𝓝 (tailTheta K g 1 θ)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hB1 : 0 < Bsub (1 : ℝ) θ := by
      have h : Bsub 1 θ = Real.cos θ ^ 2 := by unfold Bsub; ring
      rw [h]
      exact pow_pos (Real.cos_pos_of_mem_Ioo ⟨hθ.1, hθ.2⟩) 2
    have hjoint := (contDiffOn_iteratedDeriv_Bsub K ((K : ℝ) - 1 / 2)).continuousOn
    have hmemq : (θ, (1 : ℝ)) ∈ {q : ℝ × ℝ | 0 < Bsub q.2 q.1} := hB1
    have hfam : Tendsto
        (fun s : ℝ => iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s) l
        (𝓝 (iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) 1)) := by
      have hcw := (hjoint.continuousWithinAt hmemq).tendsto
      rw [hUopen.nhdsWithin_eq hmemq] at hcw
      have hpath : Tendsto (fun s : ℝ => (θ, s)) l (𝓝 (θ, (1 : ℝ))) :=
        ((continuous_const.prodMk continuous_id).continuousAt).tendsto.mono_left
          nhdsWithin_le_nhds
      have key : Tendsto
          ((fun q : ℝ × ℝ => iteratedDeriv K (fun u : ℝ => Bsub u q.1 ^ ((K : ℝ) - 1 / 2)) q.2)
            ∘ fun s : ℝ => (θ, s)) l
          (𝓝 (iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) 1)) :=
        hcw.comp hpath
      simpa only [Function.comp_def] using key
    have hmain : Tendsto (fun s : ℝ =>
          iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) s
            * (g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ)
              * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ))) l
        (𝓝 (iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) 1
            * (g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ)
              * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ)))) :=
      hfam.mul tendsto_const_nhds
    have hval : iteratedDeriv K (fun u : ℝ => Bsub u θ ^ ((K : ℝ) - 1 / 2)) 1
          * (g (Commons.Geometry.Ulam.profileX 1 * Real.sin θ)
            * (Commons.Geometry.Ulam.profileX 1 * Real.cos θ)) = tailTheta K g 1 θ := by
      unfold tailTheta; ring
    rw [hval] at hmain
    exact hmain.congr (fun s => by unfold tailTheta; ring)
  have hJ : Tendsto (fun s : ℝ => ∫ θ in (-(π / 2))..(π / 2), tailTheta K g s θ) l
      (𝓝 (∫ θ in (-(π / 2))..(π / 2), tailTheta K g 1 θ)) := by
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
      (F := fun s θ => tailTheta K g s θ) (f := fun θ => tailTheta K g 1 θ)
      (bound := fun _ : ℝ => Commons.Geometry.Ulam.profileX 1 * Cb) hmeas hbound hint hlim
    have hconv : ∀ s : ℝ,
        (∫ θ in (-(π / 2))..(π / 2), tailTheta K g s θ) = ∫ θ, tailTheta K g s θ ∂μ := by
      intro s
      rw [hμ, intervalIntegral.integral_of_le hpi, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [show (fun s : ℝ => ∫ θ in (-(π / 2))..(π / 2), tailTheta K g s θ)
          = fun s : ℝ => ∫ θ, tailTheta K g s θ ∂μ from funext hconv, hconv 1]
    exact hmain
  have hTeq : tailT K g =ᶠ[l] fun s : ℝ => ∫ θ in (-(π / 2))..(π / 2), tailTheta K g s θ :=
    Filter.Eventually.of_forall (fun s => tailT_eq_theta K g s)
  have hT1 : tailT K g 1 = ∫ θ in (-(π / 2))..(π / 2), tailTheta K g 1 θ :=
    tailT_eq_theta K g 1
  rw [hT1]
  exact hJ.congr' hTeq.symm

/-! ## Auxiliary facts about the ball right-hand side -/

lemma profileX_one_le_one : Commons.Geometry.Ulam.profileX 1 ≤ 1 := by
  have hsq := profileX_one_sq
  have hpos := profileX_one_pos
  nlinarith

/-- `momentRHS n` is smooth, so its `(n+1)`-st derivative is continuous. -/
lemma continuous_iteratedDeriv_momentRHS (n : ℕ) :
    Continuous (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s) := by
  have hmr : ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.momentRHS n) := by
    unfold Work.OddVolterra.momentRHS
    exact ContDiff.div contDiff_const
      (ContDiff.sqrt (by fun_prop) (fun x => by positivity)) (fun x => by positivity)
  have hderiv : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (n + 1) hmr
  exact hderiv.continuous

/-! ## The target -/

/-- **Continuity of `Q n h` on `[a, 1]`.** -/
theorem Q_continuousOn_Icc (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → h s = 0)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t)
    {a : ℝ} (ha : 0 < a) :
    ContinuousOn (Work.OddVolterra.Q n h) (Set.Icc a 1) := by
  have hQcont : ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.Q n h) (Set.Ioo (0 : ℝ) 1) :=
    contDiffOn_Q_Ioo n hn hh hmid
  -- the two inhomogeneities agree with the tail integrals on `[99/100, 1]`
  have htail_eq : ∀ s ∈ Set.Icc (99 / 100 : ℝ) 1,
      Work.OddVolterra.E1 n h s = tailT (n + 1) (fun _ : ℝ => 1) s ∧
      Work.OddVolterra.E2 n h s = tailT n (fun t : ℝ => t) s := by
    intro s hs
    obtain ⟨h1, h2⟩ := E1_E2_eq_tailIntegral n hn htail hs.1 hs.2
    constructor
    · rw [h1]
      simp only [tailT]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      have hfun : (fun u : ℝ => (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) + 1 / 2))
          = fun u : ℝ => (1 - (1 + u ^ 2) * t ^ 2) ^ ((((n + 1 : ℕ)) : ℝ) - 1 / 2) := by
        funext u
        rw [show (1 - t ^ 2 - u ^ 2 * t ^ 2) = (1 - (1 + u ^ 2) * t ^ 2) by ring,
          show ((n : ℝ) + 1 / 2) = ((((n + 1 : ℕ)) : ℝ) - 1 / 2) by push_cast; ring]
      rw [hfun, one_mul]
    · rw [h2]
      simp only [tailT]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      have hfun : (fun u : ℝ => (1 - t ^ 2 - u ^ 2 * t ^ 2) ^ ((n : ℝ) - 1 / 2))
          = fun u : ℝ => (1 - (1 + u ^ 2) * t ^ 2) ^ ((n : ℝ) - 1 / 2) := by
        funext u
        rw [show (1 - t ^ 2 - u ^ 2 * t ^ 2) = (1 - (1 + u ^ 2) * t ^ 2) by ring]
      rw [hfun]
  -- the two limits at `s = 1`
  have hXle : Commons.Geometry.Ulam.profileX 1 ≤ 1 := profileX_one_le_one
  have hT1 : Tendsto (tailT (n + 1) (fun _ : ℝ => 1)) (𝓝[Set.Iio 1] 1)
      (𝓝 (tailT (n + 1) (fun _ : ℝ => 1) 1)) :=
    tailT_tendsto (n + 1) (by omega) (fun _ : ℝ => 1) continuous_const (fun t _ => by simp)
  have hT2 : Tendsto (tailT n (fun t : ℝ => t)) (𝓝[Set.Iio 1] 1)
      (𝓝 (tailT n (fun t : ℝ => t) 1)) :=
    tailT_tendsto n hn (fun t : ℝ => t) continuous_id (fun t ht => by
      simpa using le_trans ht hXle)
  have hfin : ∀ᶠ s in 𝓝[Set.Iio 1] 1, s ∈ Set.Icc (99 / 100 : ℝ) 1 := by
    have hmem : Set.Ioi (99 / 100 : ℝ) ∈ 𝓝[Set.Iio 1] 1 :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioi (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hmem] with s hs hs2
    exact ⟨le_of_lt hs2, le_of_lt hs⟩
  have hE1tend : Tendsto (fun s : ℝ => Work.OddVolterra.E1 n h s) (𝓝[Set.Iio 1] 1)
      (𝓝 (Work.OddVolterra.E1 n h 1)) := by
    have h1 : Work.OddVolterra.E1 n h 1 = tailT (n + 1) (fun _ : ℝ => 1) 1 :=
      (htail_eq 1 ⟨by norm_num, le_rfl⟩).1
    have hev : tailT (n + 1) (fun _ : ℝ => 1) =ᶠ[𝓝[Set.Iio 1] 1]
        fun s : ℝ => Work.OddVolterra.E1 n h s := by
      filter_upwards [hfin] with s hs
      exact ((htail_eq s hs).1).symm
    rw [h1]
    exact hT1.congr' hev
  have hE2tend : Tendsto (fun s : ℝ => Work.OddVolterra.E2 n h s) (𝓝[Set.Iio 1] 1)
      (𝓝 (Work.OddVolterra.E2 n h 1)) := by
    have h2 : Work.OddVolterra.E2 n h 1 = tailT n (fun t : ℝ => t) 1 :=
      (htail_eq 1 ⟨by norm_num, le_rfl⟩).2
    have hev : tailT n (fun t : ℝ => t) =ᶠ[𝓝[Set.Iio 1] 1]
        fun s : ℝ => Work.OddVolterra.E2 n h s := by
      filter_upwards [hfin] with s hs
      exact ((htail_eq s hs).2).symm
    rw [h2]
    exact hT2.congr' hev
  have hmr_cont : Continuous
      (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s) :=
    continuous_iteratedDeriv_momentRHS n
  have hmrt : Tendsto (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s)
      (𝓝[Set.Iio 1] 1) (𝓝 (iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) 1)) :=
    (hmr_cont.continuousAt (x := 1)).tendsto.mono_left nhdsWithin_le_nhds
  have hQtend : Tendsto (Work.OddVolterra.Q n h) (𝓝[Set.Iio 1] 1)
      (𝓝 (Work.OddVolterra.Q n h 1)) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simpa [Work.OddVolterra.Q] using hE1tend.neg.add hmrt
    · simpa [Work.OddVolterra.Q] using hE2tend.neg
  have hpure : Tendsto (Work.OddVolterra.Q n h) (pure (1 : ℝ))
      (𝓝 (Work.OddVolterra.Q n h 1)) := by
    rw [Filter.Tendsto, Filter.le_def]
    intro V hV
    rw [Filter.mem_map]
    exact Filter.mem_pure.mpr (by simpa using mem_of_mem_nhds hV)
  have hsup : Tendsto (Work.OddVolterra.Q n h) (𝓝[Set.Iio 1] 1 ⊔ pure (1 : ℝ))
      (𝓝 (Work.OddVolterra.Q n h 1)) := hQtend.sup hpure
  -- conclusion, pointwise
  intro x hx
  rcases lt_or_eq_of_le hx.2 with hxlt | rfl
  · exact ((hQcont.continuousOn.continuousAt
      (Ioo_mem_nhds (lt_of_lt_of_le ha hx.1) hxlt))).continuousWithinAt
  · by_cases h1a : (1 : ℝ) ≤ a
    · rcases lt_or_eq_of_le h1a with h | h
      · exact absurd hx.1 (by linarith)
      · subst h
        rw [Set.Icc_self, ContinuousWithinAt, nhdsWithin_singleton]
        exact hpure
    · have ha1 : a < 1 := lt_of_not_ge h1a
      have hle : 𝓝[Set.Icc a 1] (1 : ℝ) ≤ 𝓝[Set.Iio 1] 1 ⊔ pure (1 : ℝ) := by
        have hIcc_eq : Set.Icc a 1 = (Set.Ici a ∩ Set.Iio 1) ∪ ({1} : Set ℝ) := by
          ext y
          simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iio, Set.mem_union,
            Set.mem_singleton_iff]
          constructor
          · intro hy
            rcases lt_or_eq_of_le hy.2 with h | h
            · exact Or.inl ⟨hy.1, h⟩
            · exact Or.inr h
          · rintro (⟨h1, h2⟩ | rfl)
            · exact ⟨h1, le_of_lt h2⟩
            · exact ⟨le_of_lt ha1, le_rfl⟩
        rw [hIcc_eq, nhdsWithin_union, nhdsWithin_singleton,
          nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (Ici_mem_nhds ha1))]
      exact hsup.mono_left hle

end

end Work.OddBridge

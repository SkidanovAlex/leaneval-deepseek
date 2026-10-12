import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.Star.Real
import ChallengeDeps
import Submission.ConcaveUniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Generic real analysis over `atTop` on `ℝ`: pointwise convergent concave
functions on a half-line converge uniformly on *interior* compact intervals.

This is the `ℝ`-indexed analogue of `Submission.ConcaveUniform` (which is
indexed by `ℕ`): the family is `f : ℝ → ℝ → ℝ`, "eventually in `L : ℝ`" is
`∀ᶠ L in atTop`, and pointwise convergence is `Tendsto (fun L => f L x) atTop`.
The proofs mirror the `ℕ` version verbatim; the only change is that
pointwise-convergence ε-control is obtained via `h.eventually
(Metric.ball_mem_nhds _ hε)` rather than `Metric.tendsto_atTop` (which needs
`SemilatticeSup`).  All single-function concavity/Lipschitz machinery
(`concaveOn_upper_Icc`, `concaveOn_lower_Icc`, `concaveOn_lipschitzOn_Icc`,
`concaveLipschitzConst`) is imported from `Submission.ConcaveUniform`.
-/

namespace Submission

open Filter Metric
open scoped Topology

set_option autoImplicit false

/-- The ε-net uniform-convergence argument over `atTop` on `ℝ`: an eventually
equi-Lipschitz family converging pointwise on `[a,b]` converges uniformly. -/
lemma uniformOn_Icc_of_equiLipschitz_R {F : ℝ → ℝ → ℝ} {G : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hLipF : ∀ᶠ L : ℝ in atTop, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |F L x - F L y| ≤ K * |x - y|)
    (hLipG : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |G x - G y| ≤ K * |x - y|)
    (hpt : ∀ x ∈ Set.Icc a b, Tendsto (fun L : ℝ => F L x) atTop (𝓝 (G x))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, ∀ x ∈ Set.Icc a b, |F L x - G x| < ε := by
  intro ε hε
  rcases eq_or_lt_of_le hab with rfl | hab'
  · -- a = b
    have hev : ∀ᶠ L : ℝ in atTop, |F L a - G a| < ε := by
      have hA := hpt a (by simp)
      simpa [Real.dist_eq] using hA.eventually (Metric.ball_mem_nhds (G a) hε)
    filter_upwards [hev] with L hL
    intro x hx
    have hxeq : x = a := by
      linarith [hx.1, hx.2]
    simpa [hxeq] using hL
  · -- a < b
    let η : ℝ := ε / 2
    let ρ : ℝ := (ε - η) / (2 * (K + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hηε : ε - η > 0 := by dsimp [η]; linarith
    have hKp : 0 < K + 1 := by linarith
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    obtain ⟨N, hNbig⟩ := exists_nat_gt ((b - a) / ρ)
    have hNpos : 0 < N := by
      have hpos0 : 0 < (b - a) / ρ := by positivity
      exact_mod_cast (lt_trans hpos0 hNbig)
    have hNℝ : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have hhρ : (b - a) / N < ρ := by
      rw [div_lt_iff₀ hNℝ]
      have hm := (div_lt_iff₀ hρ).mp hNbig
      nlinarith
    let t : ℕ → ℝ := fun i => a + (b - a) * (i : ℝ) / N
    have htmem : ∀ i : ℕ, i ≤ N → t i ∈ Set.Icc a b := by
      intro i hi
      have hiN : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      have hbam : 0 ≤ b - a := by linarith
      constructor
      · have hn0 : 0 ≤ (b - a) * (i : ℝ) / N := by positivity
        dsimp [t]
        linarith
      · have hc : (b - a) * (i : ℝ) / N ≤ b - a := by
          calc
            (b - a) * (i : ℝ) / N ≤ (b - a) * (N : ℝ) / N := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hiN hbam) hNℝ.le
            _ = b - a := by field_simp [hNℝ.ne']
        dsimp [t]
        linarith
    -- pointwise bounds at all mesh points, eventually
    have hmeshEv : ∀ᶠ L : ℝ in atTop, ∀ i : ℕ, i < N →
        |F L (t i) - G (t i)| < η := by
      have hmeshEv' : ∀ᶠ L : ℝ in atTop, ∀ i ∈ Finset.range N,
          |F L (t i) - G (t i)| < η := by
        refine (Filter.eventually_all_finset (Finset.range N)).mpr ?_
        intro i hi
        have hm : t i ∈ Set.Icc a b := htmem i (le_of_lt (Finset.mem_range.mp hi))
        have hA := hpt (t i) hm
        filter_upwards [hA.eventually (Metric.ball_mem_nhds (G (t i)) hη)] with L hL
        simpa [Real.dist_eq] using hL
      simpa [Finset.mem_range] using hmeshEv'
    filter_upwards [hLipF, hmeshEv] with L hLipL hmeshL
    intro x hx
    obtain ⟨i, hiN, hidist⟩ := exists_index_near_Icc hab' N hNpos x hx
    have hmemb : t i ∈ Set.Icc a b := htmem i (le_of_lt hiN)
    have hF1 : |F L x - F L (t i)| ≤ K * ((b - a) / N) := by
      have h1 := hLipL x hx (t i) hmemb
      calc
        |F L x - F L (t i)| ≤ K * |x - t i| := h1
        _ ≤ K * ((b - a) / N) := by
          have hm := mul_le_mul_of_nonneg_left (by simpa [t] using hidist) hK
          simpa [mul_comm] using hm
    have hG1 : |G (t i) - G x| ≤ K * ((b - a) / N) := by
      have h1 := hLipG (t i) hmemb x hx
      calc
        |G (t i) - G x| ≤ K * |t i - x| := h1
        _ ≤ K * ((b - a) / N) := by
          have hh1 : |x - t i| ≤ (b - a) / N := by simpa [t] using hidist
          have hh2 : |t i - x| ≤ (b - a) / N := by
            simpa [abs_sub_comm] using hh1
          have hm := mul_le_mul_of_nonneg_left hh2 hK
          simpa [mul_comm] using hm
    have hmid : |F L (t i) - G (t i)| < η := hmeshL i hiN
    have htri : |F L x - G x| ≤ K * ((b - a) / N) + η + K * ((b - a) / N) := by
      have hB : |F L x - G (t i)| ≤ |F L x - F L (t i)| + |F L (t i) - G (t i)| :=
        abs_sub_le_triangle (a := F L x) (b := F L (t i)) (c := G (t i))
      calc
        |F L x - G x| ≤ |F L x - G (t i)| + |G (t i) - G x| :=
          abs_sub_le_triangle (a := F L x) (b := G (t i)) (c := G x)
        _ ≤ (|F L x - F L (t i)| + |F L (t i) - G (t i)|) + |G (t i) - G x| := by
          have hh := add_le_add_right hB (|G (t i) - G x|)
          simpa [add_comm, add_assoc, add_left_comm] using hh
        _ ≤ K * ((b - a) / N) + η + K * ((b - a) / N) := by
          exact add_le_add (add_le_add hF1 (le_of_lt hmid)) hG1
    have hKh : K * ((b - a) / N) ≤ (K + 1) * ((b - a) / N) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity : 0 ≤ (b - a) / N)
    have hsmall : (2 * (K + 1)) * ((b - a) / N) < ε - η := by
      have hmul := mul_lt_mul_of_pos_left hhρ (by positivity : 0 < 2 * (K + 1))
      have hρeq : (2 * (K + 1)) * ρ = ε - η := by
        dsimp [ρ, η]
        field_simp
      linarith
    have hfinal : K * ((b - a) / N) + η + K * ((b - a) / N) < ε := by
      have hA : K * ((b - a) / N) + η + K * ((b - a) / N) ≤
          (2 * (K + 1)) * ((b - a) / N) + η := by nlinarith [hKh, hK]
      have hB : (2 * (K + 1)) * ((b - a) / N) + η < ε := by linarith [hsmall]
      linarith
    exact lt_of_le_of_lt htri hfinal

/-- Pointwise convergent concave functions on `[0,∞)` converge uniformly on
`[a,b]` in the interior (`0 < a ≤ b`): for every `ε > 0`, eventually in
`L : ℝ` every value on the interval is within `ε` of the limit. -/
lemma concaveOn_uniformOn_Icc_R {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (h0a : 0 < a) (hab : a ≤ b)
    (hf : ∀ L : ℝ, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (f L))
    (hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) g)
    (hpt : ∀ x : ℝ, 0 ≤ x → Tendsto (fun L : ℝ => f L x) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc a b → |f L x - g x| < ε := by
  intro ε hε
  let W : ℝ := |g (a / 2)| + |g (3 * a / 4)| + |g (b + 1)| + 1
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hg1 : |g (a / 2)| ≤ W := by
    dsimp [W]
    nlinarith [abs_nonneg (g (3 * a / 4)), abs_nonneg (g (b + 1))]
  have hg2 : |g (3 * a / 4)| ≤ W := by
    dsimp [W]
    nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (b + 1))]
  have hg3 : |g (b + 1)| ≤ W := by
    dsimp [W]
    nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (3 * a / 4))]
  -- `f L` satisfies the same reference bounds eventually
  have hfEv : ∀ᶠ L : ℝ in atTop,
      |f L (a / 2)| ≤ W ∧ |f L (3 * a / 4)| ≤ W ∧ |f L (b + 1)| ≤ W := by
    have hb1 : ∀ᶠ L : ℝ in atTop, |f L (a / 2)| ≤ W := by
      have hconv := hpt (a / 2) (by positivity)
      filter_upwards [hconv.eventually
          (Metric.ball_mem_nhds (g (a / 2)) (by norm_num : (0 : ℝ) < 1))] with L hL
      have hd : |f L (a / 2) - g (a / 2)| < 1 := by
        simpa [Real.dist_eq] using hL
      calc
        |f L (a / 2)| = |(f L (a / 2) - g (a / 2)) + g (a / 2)| := by congr 1; ring
        _ ≤ |f L (a / 2) - g (a / 2)| + |g (a / 2)| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (3 * a / 4)), abs_nonneg (g (b + 1))]
    have hb2 : ∀ᶠ L : ℝ in atTop, |f L (3 * a / 4)| ≤ W := by
      have hconv := hpt (3 * a / 4) (by positivity)
      filter_upwards [hconv.eventually
          (Metric.ball_mem_nhds (g (3 * a / 4)) (by norm_num : (0 : ℝ) < 1))] with L hL
      have hd : |f L (3 * a / 4) - g (3 * a / 4)| < 1 := by
        simpa [Real.dist_eq] using hL
      calc
        |f L (3 * a / 4)| = |(f L (3 * a / 4) - g (3 * a / 4)) + g (3 * a / 4)| := by congr 1; ring
        _ ≤ |f L (3 * a / 4) - g (3 * a / 4)| + |g (3 * a / 4)| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (b + 1))]
    have hb3 : ∀ᶠ L : ℝ in atTop, |f L (b + 1)| ≤ W := by
      have hconv := hpt (b + 1) (by nlinarith)
      filter_upwards [hconv.eventually
          (Metric.ball_mem_nhds (g (b + 1)) (by norm_num : (0 : ℝ) < 1))] with L hL
      have hd : |f L (b + 1) - g (b + 1)| < 1 := by
        simpa [Real.dist_eq] using hL
      calc
        |f L (b + 1)| = |(f L (b + 1) - g (b + 1)) + g (b + 1)| := by congr 1; ring
        _ ≤ |f L (b + 1) - g (b + 1)| + |g (b + 1)| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (3 * a / 4))]
    exact (hb1.and (hb2.and hb3))
  -- common Lipschitz constant
  let K : ℝ := concaveLipschitzConst a b W
  have hK0 : 0 ≤ K := by
    dsimp [K]
    dsimp [concaveLipschitzConst]
    have hU0 : 0 ≤ W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
      have hbq0 : 0 ≤ b - 3 * a / 4 := by nlinarith [h0a]
      have hqpos : 0 < 3 * a / 4 - a / 2 := by nlinarith [h0a]
      have h1 : 0 ≤ (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
        exact mul_nonneg hbq0 (div_nonneg (by nlinarith) hqpos.le)
      nlinarith
    have hd1 : 0 < a - a / 2 := by nlinarith [h0a]
    have hd2 : 0 < (b + 1) - b := by norm_num
    have ht1 : 0 ≤ (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / (a - a / 2) := by
      exact div_nonneg (by linarith) hd1.le
    have ht2 : 0 ≤ (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / ((b + 1) - b) := by
      exact div_nonneg (by linarith) hd2.le
    change 0 ≤ (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / (a - a / 2) +
      (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / ((b + 1) - b)
    linarith
  have hgLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x - g y| ≤ K * |x - y| := by
    intro x hx y hy
    have hh := concaveOn_lipschitzOn_Icc h0a hab hW hg hg1 hg2 hg3 x y hx hy
    simpa [K] using hh
  have hfLip : ∀ᶠ L : ℝ in atTop, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |f L x - f L y| ≤ K * |x - y| := by
    filter_upwards [hfEv] with L hL
    intro x hx y hy
    have hh := concaveOn_lipschitzOn_Icc h0a hab hW (hf L) hL.1 hL.2.1 hL.2.2 x y hx hy
    simpa [K] using hh
  have hptIcc : ∀ x ∈ Set.Icc a b, Tendsto (fun L : ℝ => f L x) atTop (𝓝 (g x)) := by
    intro x hx
    exact hpt x (le_trans (by positivity : 0 ≤ a) hx.1)
  exact uniformOn_Icc_of_equiLipschitz_R (F := f) (G := g) hab hK0 hfLip hgLip hptIcc ε hε

/-- The sup-limsup exchange over `atTop` on `ℝ`: under the hypotheses of
`concaveOn_uniformOn_Icc_R` (with `0 < a`), the limsup of the supremum over
the compact interval is at most the supremum of the limit. -/
lemma limsup_sup_le_sup_of_concaveOn_R {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (h0a : 0 < a) (hab : a ≤ b)
    (hf : ∀ L : ℝ, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (f L))
    (hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) g)
    (hpt : ∀ x : ℝ, 0 ≤ x → Tendsto (fun L : ℝ => f L x) atTop (𝓝 (g x))) :
    Filter.limsup (fun L : ℝ => sSup ((f L) '' Set.Icc a b)) atTop ≤
      sSup (g '' Set.Icc a b) := by
  let S : ℝ := sSup (g '' Set.Icc a b)
  have haIcc : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  -- g is bounded above on [a,b], so the image is bounded
  have hS_bdd : BddAbove (g '' Set.Icc a b) := by
    let W : ℝ := |g (a / 2)| + |g (3 * a / 4)|
    have hW : 0 ≤ W := by
      dsimp [W]
      positivity
    have hb1 : |g (a / 2)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (3 * a / 4))]
    have hb2 : |g (3 * a / 4)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (a / 2))]
    have hup := concaveOn_upper_Icc h0a hab hW hg hb1 hb2
    refine ⟨W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)), ?_⟩
    rintro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hup x hx
  have hS_nonempty : (g '' Set.Icc a b).Nonempty := ⟨g a, ⟨a, haIcc, rfl⟩⟩
  -- each f L is bounded above on [a,b]
  have hF_bdd : ∀ L : ℝ, BddAbove ((f L) '' Set.Icc a b) := by
    intro L
    let W : ℝ := |f L (a / 2)| + |f L (3 * a / 4)|
    have hW : 0 ≤ W := by
      dsimp [W]
      positivity
    have hb1 : |f L (a / 2)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (f L (3 * a / 4))]
    have hb2 : |f L (3 * a / 4)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (f L (a / 2))]
    have hup := concaveOn_upper_Icc h0a hab hW (hf L) hb1 hb2
    refine ⟨W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)), ?_⟩
    rintro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hup x hx
  have hunif := concaveOn_uniformOn_Icc_R h0a hab hf hg hpt
  -- uniform convergence gives: eventually the sup of f L is ≤ sup g + ε
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ L : ℝ in atTop, sSup ((f L) '' Set.Icc a b) ≤ S + ε := by
    filter_upwards [hunif ε hε] with L hun
    have hnon : ((f L) '' Set.Icc a b).Nonempty := ⟨f L a, ⟨a, haIcc, rfl⟩⟩
    rw [csSup_le_iff (hF_bdd L) hnon]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h1 : |f L x - g x| < ε := hun x hx
    have h1pos : f L x - g x < ε := (abs_lt.mp h1).2
    have hgx : g x ≤ S := le_csSup hS_bdd ⟨x, hx, rfl⟩
    linarith
  have hlim : Filter.limsup (fun L : ℝ => sSup ((f L) '' Set.Icc a b)) atTop ≤ S + ε := by
    -- need coboundedness of the family from below
    have hCob : Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun L => sSup ((f L) '' Set.Icc a b)) := by
      have hlow : ∀ᶠ L : ℝ in atTop, g a - 1 ≤ sSup ((f L) '' Set.Icc a b) := by
        filter_upwards [hunif 1 (by norm_num)] with L hun
        have hmem : f L a ∈ (f L) '' Set.Icc a b := ⟨a, haIcc, rfl⟩
        have hle := le_csSup (hF_bdd L) hmem
        have h1 : |f L a - g a| < 1 := hun a haIcc
        have h1lo : -1 < f L a - g a := (abs_lt.mp h1).1
        linarith
      refine ⟨g a - 1, ?_⟩
      intro x hxu
      have hboth : ∀ᶠ L : ℝ in atTop, g a - 1 ≤ sSup ((f L) '' Set.Icc a b) ∧
          sSup ((f L) '' Set.Icc a b) ≤ x := hlow.and hxu
      have hxlow : ∀ᶠ L : ℝ in atTop, g a - 1 ≤ x :=
        hboth.mono (fun L hL => le_trans hL.1 hL.2)
      exact hxlow.exists.choose_spec
    exact Filter.limsup_le_of_le hCob hev
  dsimp [S] at hlim
  linarith

end Submission

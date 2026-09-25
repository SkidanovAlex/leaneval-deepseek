import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.sigmaN_nested
import Submission.Work.BourgainPlan.Maximal.sigmaN_contains_farey
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.major_arc_nbd_bound
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.mstXi_bound_and_eq_one
import Submission.Work.BourgainPlan.Maximal.mst_weyl_step
import Submission.Work.BourgainPlan.Maximal.mst_smallq_inner
import Submission.Work.BourgainPlan.Maximal.mst_minor_numeric

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-- **Exponential beats the level separation.**  For `d ≥ 2` and `χ < 1/10` one has
`2^{-n(d-χ)} < 2 e^{-n^{1/10}}` for all large `n`.  This is the numerical input of the
disjointness of the level-`n` bumps (`sigmaN_separated` supplies the separation
`2 e^{-(n^l)^{mstRho l}} = 2 e^{-n^{1/10}}`). -/
private lemma exp_neg_sep_bound {d : ℕ} {χ : ℝ} (hd : 2 ≤ d) (hχ : χ < 1 / 10) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
        < 2 * Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 10))) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdχ : (19 / 10 : ℝ) < (d : ℝ) - χ := by linarith
  have hlog : (1 : ℝ) < ((d : ℝ) - χ) * Real.log 2 := by
    have h2 := Real.log_two_gt_d9
    nlinarith [hdχ, h2]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h : (((1 : ℕ)) : ℝ) ≤ (((n : ℕ)) : ℝ) := Nat.cast_le.mpr hn
    simpa using h
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hroot : (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (n : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : ((1 : ℝ) / 10) ≤ 1)
    rwa [Real.rpow_one] at h
  have hL : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))
      = Real.exp (Real.log 2 * (-((n : ℝ) * ((d : ℝ) - χ)))) :=
    Real.rpow_def_of_pos (x := 2) (by norm_num) _
  have hR : 2 * Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 10)))
      = Real.exp (Real.log 2 + -((n : ℝ) ^ ((1 : ℝ) / 10))) := by
    rw [Real.exp_add, Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
  rw [hL, hR, Real.exp_lt_exp]
  nlinarith [hroot, hlog, hnpos, hlog2pos]

/-- **MST's (63): the pointwise minor-arc bound.** For every `α > 0` and every level parameter `l` large enough (in terms of `α`), the density symbol `m_{2^n}` times `1 − Ξ_n` is bounded by `C (n+1)^{−α}` for all `n` large and *all* points of the circle: `sup_ξ |m_{2^n}(ξ)(1 − Ξ_n(ξ))| ≲ (n+1)^{−α}`.

Here `m_{2^n}` is `mstWeyl P (2^n)` (the Weyl kernel `N⁻¹Σ_{j<N}e(θP(j))` read along the canonical lift; its conjugate is the a.e. value of the density class by `khatZMult_coeFn_star_mstWeyl`) and `Ξ_n = mstXi l (P.natDegree) χ η n` is the sum of disjoint level-`n` bumps over `𝒰(n) = mstU l n`, the Farey fractions of denominator `≤ n^l` (Tao's superset `Σ_{n^l}`).

Proof plan, with the two regimes of MST §4.1.
* The bumps `η_n(· − β) = mstEta … n (· − β)`, `β ∈ 𝒰(n)`, have *pairwise disjoint* supports: the points of `𝒰(n)` are `exp(−2n^{1/10})`-separated (`sigmaN_separated`) while the support radius is `2^{−n(d−χ)}/2`.  Hence `Ξ_n(ξ)` is either `0` or a single value `η_n(ξ − β₀)`, so `‖1 − Ξ_n(ξ)‖ ≤ 1 + M`, and `Ξ_n(ξ) = 1` exactly when `ξ` is within the *inner* ball (`radius 2^{−n(d−χ)}/4`) of some `β₀ ∈ 𝒰(n)` (`hη1`).
* Given `ξ` with `θ = iwRep ξ`, apply Dirichlet (`Real.exists_rat_abs_sub_le_and_den_le`) to `c·θ` (`c = P.leadingCoeff`) with parameter `Q = ⌈n^{−β}2^{nd}⌉`: there are `a, q` with `1 ≤ q ≤ Q`, `Int.gcd a q = 1` and `|cθ − a/q| ≤ 1/(qQ)`.  Here `β` is a fixed parameter with `β + 1 ≤ l` (so `n^β ≤ n^{l−1}`, harmless); the exponent of the conclusion is `β/(2d²−2d+1)`, which is why `l` must be large (see also the `log` loss in `MSTWeylBound`).
* If `q ≥ n^β` then `|cθ − a/q| ≤ 1/q²` (because `q ≤ Q`) and the log-loss Weyl bound `MSTWeylBound` applied to `f = C θ * toRealPoly P`, `M = 0` gives `‖m_{2^n}(θ)‖ ≤ C N (1 + log N)(1/q + 1/N + q/N^d)^{1/(2d²−2d+1)} ≤ C' (log N) n^{−β/(2d²−2d+1)}`, a polylog decay.
* If `q < n^β`, then `ξ` is within `n^β 2^{−nd}/c` of the rational point `β₀ := a/(c q)`, whose reduced denominator is `≤ c q ≤ c n^β ≤ n^{l−1} ≤ n^l` for `n` large, so `β₀ ∈ 𝒰(n)` (`sigmaN_contains_farey` for the level `n^l`).  If `Ξ_n(ξ) = 1` we are done (`1 − Ξ_n = 0`); otherwise the profile decays: `major_arc_nbd_bound` (with `2^{l'} = 2^{⌈n/2⌉} ≥ q`, error `2^{l'}(M^{−1}N^{d−1} + N^{−1})`, `M = 1/|θ − a/q|`) gives `‖m_{2^n}(θ)‖ ≤ ‖Φ_{2^n}(θ − a/q)‖ + Cn^β2^{−n/2}`, and `polyProfile_decay_sharp` turns `‖ξ − β₀‖ > 2^{−n(d−χ)}/4` into `‖Φ_{2^n}(θ − a/q)‖ ≤ C(2^{nχ})^{−1/d}`, an exponential decay.
   (The two sub-cases — `ξ` in the annulus of `β₀` and `ξ` outside all supports — are the same computation; the disjointness of the supports supplies `‖1 − Ξ_n(ξ)‖ ≤ 1 + M` in either.) -/
theorem mst_minor_sup (hW : Work.BourgainPlan.Maximal.MSTWeylBound)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    {α : ℝ} (hα : 0 < α) :
    ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        ‖star (Work.BourgainPlan.Maximal.mstWeyl P (2 ^ n) ξ) *
            (1 - Work.BourgainPlan.Maximal.mstXi l P.natDegree χ η n ξ)‖
          ≤ C * ((n : ℝ) + 1) ^ (-α) := by
  -- ### Step 1: the Weyl regime fixes the threshold exponent `γ`
  obtain ⟨γ, hγpos, Cw, hCwpos, Nw, hweyl⟩ := mst_weyl_step hW P hd hc hα
  -- ### Step 2: the eventual numeric estimates at that `γ`
  have hcR : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  obtain ⟨Nnum, hnum⟩ := mst_minor_numeric (d := P.natDegree) (χ := χ) (γ := γ)
    (c := (P.leadingCoeff : ℝ)) hd hχ0 hχ1 hγpos hcR
  -- ### Step 3: the level parameter `l ≥ γ + 2`, and the separation threshold
  refine ⟨⌈γ⌉₊ + 2, fun l hl => ?_⟩
  have hl1 : 1 ≤ l := by omega
  have hlγ : γ + 2 ≤ (l : ℝ) := by
    have h1 : γ ≤ (⌈γ⌉₊ : ℝ) := Nat.le_ceil γ
    have h3 : (((⌈γ⌉₊ + 2 : ℕ)) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    push_cast at h3
    linarith
  have hρpos : 0 < mstRho l := by
    rw [mstRho]
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
    positivity
  obtain ⟨Nsep, hsep_all⟩ := sigmaN_separated (ρ := mstRho l) hρpos
  obtain ⟨Nsep2, hsepbound⟩ := exp_neg_sep_bound (d := P.natDegree) hd hχ1
  have hnposR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
  refine ⟨max 1 ((1 + M) * Cw), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    max Nw (max Nnum (max Nsep Nsep2)), fun n hn ξ => ?_⟩
  have hnw : Nw ≤ n := by omega
  have hnn : Nnum ≤ n := by omega
  have hns : Nsep ≤ n := by omega
  have hns2 : Nsep2 ≤ n := by omega
  obtain ⟨hx1, hγ2n, hiii, hgap, hbig, hcn, h21⟩ := hnum n hnn
  have hn2 : 2 ≤ n := by
    have h : (2 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) h21
    exact_mod_cast h
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- ### the canonical lift `θ = iwRep ξ` and the separation package
  set θ : ℝ := iwRep ξ with hθ
  have htoNat : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
    have h : (P.leadingCoeff.toNat : ℤ) = P.leadingCoeff :=
      Int.toNat_of_nonneg (le_of_lt hc)
    exact_mod_cast h
  have hrpow : (((n ^ l : ℕ) : ℝ)) ^ (mstRho l) = (n : ℝ) ^ ((1 : ℝ) / 10) := by
    have h1 : (((n ^ l : ℕ) : ℝ)) = (n : ℝ) ^ ((l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
    rw [h1, show mstRho l = 1 / (10 * (l : ℝ)) from rfl,
      ← Real.rpow_mul (le_of_lt hnpos)]
    have hexp : ((l : ℕ) : ℝ) * (1 / (10 * (l : ℝ))) = 1 / 10 := by
      have hlne : ((l : ℕ) : ℝ) ≠ 0 := by positivity
      rw [mul_one_div]
      have h := mul_div_mul_right (1 : ℝ) 10 hlne
      simpa using h
    rw [hexp]
  set sep : ℝ := 2 * Real.exp (-(((n ^ l : ℕ) : ℝ) ^ (mstRho l))) with hsepdef
  have hsep : ∀ β ∈ mstU l n, ∀ β' ∈ mstU l n, β ≠ β' → sep ≤ ‖β - β'‖ := by
    intro β hβ β' hβ' hne
    have h1 : Nsep ≤ n ^ l := le_trans hns (Nat.le_self_pow (n := l) (by omega) n)
    have h2 : β ∈ IonescuWainger.sigmaLeFinset (IonescuWainger.taoSetS (mstRho l) (n ^ l))
        (⌊2 / mstRho l⌋₊ + 1) := by simpa [mstU, iwSigma, iwK] using hβ
    have h3 : β' ∈ IonescuWainger.sigmaLeFinset (IonescuWainger.taoSetS (mstRho l) (n ^ l))
        (⌊2 / mstRho l⌋₊ + 1) := by simpa [mstU, iwSigma, iwK] using hβ'
    have := hsep_all (n ^ l) h1 β h2 β' h3 hne
    rwa [hsepdef]
  have hsep_gt : (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) < sep := by
    rw [hsepdef, hrpow]
    exact hsepbound n hns2
  -- ### the two consequences of the geometry lemma
  have hgeom := mstXi_bound_and_eq_one (l := l) (d := P.natDegree) (χ := χ) (η := η) (n := n)
    (sep := sep) (M := M) hηbd hη1 hη2 hsep hsep_gt ξ
  have hXi_le : ‖mstXi l P.natDegree χ η n ξ‖ ≤ M := hgeom.1
  have hXi_one : ∀ β₀ ∈ mstU l n,
      |iwRep (ξ - β₀)| ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) →
      mstXi l P.natDegree χ η n ξ = 1 := hgeom.2
  -- ### the `2^{iwK (mstRho l)} ≤ n^l` hypothesis of the Farey covering
  have hNmem : 2 ^ iwK (mstRho l) ≤ n ^ l := by
    have hK : iwK (mstRho l) = 20 * l + 1 := by
      rw [iwK, mstRho]
      have h1 : 2 / (1 / (10 * (l : ℝ))) = ((20 * l : ℕ) : ℝ) := by
        push_cast
        field_simp
        norm_num
      rw [h1, Nat.floor_natCast]
    rw [hK]
    have h21' : 2 ^ 21 ≤ n := by exact_mod_cast h21
    calc 2 ^ (20 * l + 1) ≤ 2 ^ (21 * l) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ 21) ^ l := by rw [← pow_mul]
      _ ≤ n ^ l := Nat.pow_le_pow_left h21' l
  -- ### theta = 0: the point `0 = a/(c·1)` lies in `𝒰(n)`
  by_cases hθ0 : θ = 0
  · have h1lt : ((1 : ℕ) : ℝ) < (n : ℝ) ^ γ := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn2
      have h3 : (1 : ℝ) < (n : ℝ) ^ γ :=
        lt_of_lt_of_le (Real.one_lt_rpow one_lt_two hγpos)
          (Real.rpow_le_rpow (by norm_num) h2 (le_of_lt hγpos))
      simpa using h3
    have hcnat : P.leadingCoeff.toNat ≤ n := by
      have h : ((P.leadingCoeff.toNat : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
        rw [htoNat]
        exact hcn
      exact Nat.cast_le.mp h
    have hden0 : P.leadingCoeff.toNat * 1 ≤ n ^ l := by
      simpa using le_trans hcnat (Nat.le_self_pow (n := l) (by omega) n)
    have hclose0 : |(P.leadingCoeff : ℝ) * iwRep ξ - ((0 : ℤ) : ℝ) / ((1 : ℕ) : ℝ)|
        ≤ 1 / (((1 : ℕ) : ℝ) * ((n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)))) := by
      rw [← hθ, hθ0]
      simp only [mul_zero, Int.cast_zero, Nat.cast_one, zero_div, sub_zero, abs_zero]
      positivity
    obtain ⟨β₀, hβ₀, hdist⟩ :=
      mst_smallq_inner P hd hc hχ0 hγpos hl1 (n := n) (ξ := ξ) (a := 0) (q := 1)
        le_rfl h1lt hden0 hNmem hgap hbig hclose0
    have hone : mstXi l P.natDegree χ η n ξ = 1 := hXi_one β₀ hβ₀ hdist
    rw [hone, sub_self, mul_zero, norm_zero]
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
      (Real.rpow_nonneg (by positivity) _)
  · -- ### theta ≠ 0: Dirichlet on `c·θ`
    set x : ℝ := (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ))) with hx
    have hx1' : 1 ≤ x := by rw [hx]; exact hx1
    set Q : ℕ := Nat.ceil x with hQ
    have hQpos : 0 < Q := by
      rw [hQ, Nat.ceil_pos]
      linarith
    obtain ⟨r, hrle, hrden⟩ :=
      Real.exists_rat_abs_sub_le_and_den_le (((P.leadingCoeff : ℝ) * θ)) (n := Q) hQpos
    set a : ℤ := r.num with ha
    set q : ℕ := r.den with hq
    have hq1 : 1 ≤ q := r.pos
    have hqQ : q ≤ Q := hrden
    have hx0 : 0 ≤ x := le_trans zero_le_one hx1'
    have hQle : (Q : ℝ) ≤ 2 * x := by
      have h := Nat.ceil_lt_add_one hx0
      have hQcast : ((Q : ℕ) : ℝ) = ((Nat.ceil x : ℕ) : ℝ) := by rw [hQ]
      rw [hQcast] at h ⊢
      linarith
    have hq2x : (q : ℝ) ≤ 2 * (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := by
      have h1 : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
      have h2 : 2 * x = 2 * (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := by
        rw [hx]; ring
      linarith [h1, hQle, h2]
    have hrcast : ((r : ℝ)) = (a : ℝ) / (q : ℝ) := by
      rw [ha, hq]
      exact Rat.cast_def r
    have hcl : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)| ≤ 1 / (((Q : ℝ) + 1) * (q : ℝ)) := by
      have h := hrle
      rw [hrcast, hq] at h
      exact h
    have hxle : x ≤ (Q : ℝ) + 1 := by
      have h := Nat.le_ceil x
      have hQcast : ((Q : ℕ) : ℝ) = ((Nat.ceil x : ℕ) : ℝ) := by rw [hQ]
      rw [hQcast]
      linarith
    have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hcl1 : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)|
        ≤ 1 / ((q : ℝ) * ((n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)))) := by
      refine le_trans hcl ?_
      have hx' : x = (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) := hx
      rw [← hx']
      apply one_div_le_one_div_of_le
      · exact mul_pos hqposR (lt_of_lt_of_le zero_lt_one hx1')
      · nlinarith [hqposR, hxle]
    have hqQ' : (q : ℝ) ≤ (Q : ℝ) + 1 := by
      have hQq : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
      linarith
    have hcl2 : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
      refine le_trans hcl ?_
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hqposR, hqQ']
    have hgcd : Int.gcd a (q : ℤ) = 1 := by
      have h : r.num.natAbs.Coprime r.den := r.reduced
      rw [ha, hq, Int.gcd_eq_natAbs]
      simpa using h
    have hθne : θ ≠ 0 := hθ0
    by_cases hcase : (n : ℝ) ^ γ ≤ (q : ℝ)
    · -- ### the Weyl regime `q ≥ n^γ`
      have hpowlb : (2 : ℝ) ^ (-(n : ℝ)) ≤ (n : ℝ) ^ (-γ) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_neg (le_of_lt hnpos)]
        rw [← one_div, ← one_div]
        have hγ2n' : (n : ℝ) ^ γ ≤ (2 : ℝ) ^ ((n : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]
          exact hγ2n
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos γ) hγ2n'
      have hm := hweyl n hnw a q hq1 hcase hq2x hpowlb hgcd θ hθne hcl2
      have hm' : ‖mstWeyl P (2 ^ n) ξ‖ ≤ Cw * ((n : ℝ) + 1) ^ (-α) := by
        simpa [mstWeyl_apply, hθ] using hm
      have hsub : ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖ ≤ 1 + M := by
        calc ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖
            ≤ ‖(1 : ℂ)‖ + ‖mstXi l P.natDegree χ η n ξ‖ := norm_sub_le _ _
          _ ≤ 1 + M := by rw [norm_one]; linarith
      calc ‖star (mstWeyl P (2 ^ n) ξ) * (1 - mstXi l P.natDegree χ η n ξ)‖
          = ‖mstWeyl P (2 ^ n) ξ‖ * ‖(1 : ℂ) - mstXi l P.natDegree χ η n ξ‖ := by
            rw [norm_mul, norm_star]
        _ ≤ (Cw * ((n : ℝ) + 1) ^ (-α)) * (1 + M) :=
            mul_le_mul hm' hsub (norm_nonneg _) (by positivity)
        _ = (1 + M) * Cw * ((n : ℝ) + 1) ^ (-α) := by ring
        _ ≤ max 1 ((1 + M) * Cw) * ((n : ℝ) + 1) ^ (-α) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
    · -- ### the small-denominator regime `q < n^γ`
      have hqγ : (q : ℝ) < (n : ℝ) ^ γ := not_le.mp hcase
      have hle1 : (1 : ℝ) ≤ (l : ℝ) - γ := by
        have : (1 : ℕ) ≤ l := hl1
        have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast this
        linarith
      have hcle : (P.leadingCoeff : ℝ) ≤ (n : ℝ) ^ ((l : ℝ) - γ) := by
        calc (P.leadingCoeff : ℝ) ≤ (n : ℝ) := hcn
          _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ ((l : ℝ) - γ) := Real.rpow_le_rpow_of_exponent_le hn1R hle1
      have hcqn : (P.leadingCoeff : ℝ) * (q : ℝ) < (n : ℝ) ^ (l : ℝ) := by
        calc (P.leadingCoeff : ℝ) * (q : ℝ) < (P.leadingCoeff : ℝ) * ((n : ℝ) ^ γ) :=
              mul_lt_mul_of_pos_left hqγ hcR
          _ ≤ (n : ℝ) ^ ((l : ℝ) - γ) * (n : ℝ) ^ γ :=
              mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg (by positivity) _)
          _ = (n : ℝ) ^ (l : ℝ) := by
              rw [← Real.rpow_add hnpos]
              congr 1
              ring
      have hden : P.leadingCoeff.toNat * q ≤ n ^ l := by
        have hcast : ((P.leadingCoeff.toNat * q : ℕ) : ℝ)
            = (P.leadingCoeff : ℝ) * (q : ℝ) := by
          rw [Nat.cast_mul, htoNat]
        have : ((P.leadingCoeff.toNat * q : ℕ) : ℝ) < (((n ^ l : ℕ)) : ℝ) := by
          rw [hcast, Nat.cast_pow]
          simpa using hcqn
        exact le_of_lt (Nat.cast_lt.mp this)
      have hcl1' : |(P.leadingCoeff : ℝ) * iwRep ξ - (a : ℝ) / (q : ℝ)|
          ≤ 1 / ((q : ℝ) * ((n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)))) := by
        rw [← hθ]
        exact hcl1
      obtain ⟨β₀, hβ₀, hdist⟩ :=
        mst_smallq_inner P hd hc hχ0 hγpos hl1 hq1 hqγ hden hNmem hgap hbig hcl1'
      have hone : mstXi l P.natDegree χ η n ξ = 1 := hXi_one β₀ hβ₀ hdist
      rw [hone, sub_self, mul_zero, norm_zero]
      exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
        (Real.rpow_nonneg (by positivity) _)

end

end Work.BourgainPlan.Maximal

import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroChain
import Submission.Work.EQ.HeteroRit
import Submission.Work.EQ.HeteroRk
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.tail_H0_data

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md and DESIGN_CORE.md (orchestrator designs; your lemma is one node). Defs: Submission.Work.EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit). The proved UNIFORMIZATION library is in this workspace (Submission.UnifMain etc.; see DESIGN_CORE 'Library use'). NOTE: importing UnifMain makes `open Topology` resolve to `Work.Topology` — write `open _root_.Topology`.

# exists_H0_of_heteroclinic: the real connection gives a point of `⁰H` (2–4k)

**Claim.** `IsHeteroclinic a h r Γ ⇒ (H0 a h).Nonempty`.

**Route.** Fix `t₀ = ε/2`, where `ε` is the germ radius from `hΓ`.
1. Real chain. Put `Pₙ(t) := (Re Γ(λⁿt), Im Γ(λⁿt))` in `ℂ × ℂ`. Then `eqU(Γ s) = Γ(λs)` gives
   `EqRelC(Pₙ, Pₙ₊₁)`. For real points with `y > 0`, the two `≠ 0` conditions are `|P - O₂|² > 0` and
   `|Q - O₁|² > 0`. So `RegPair` holds.
2. Forward tail: `Γ = germPt = germC` (real parts) for small `t`.
3. Backward tail. Reversibility `M ∘ eqU⁻¹ = eqU ∘ M` with `M = -conj` holds on the upper half plane.
   `eqU` is injective there: of the two backward branches, exactly one stays in `y > 0`. Together with the
   mirror clause `Γ(s(t)) = MΓ(t)` this gives `s(λ⁻¹t) = λ s(t)`. Hence
   `Γ(λ^{-n}t) = M germPt(λⁿ s(t)) = ugermC(λⁿ s(t))` for large `n`. So `ψ₂ = s(t)`.
4. Complex family. For `u` near `t₀`:
   * `Pₙ(u) := germC(λⁿu)` for `n ≥ N`;
   * `Pₙ(u)` for `0 ≤ n < N` is obtained by the backward branch (`invBranch` with the sign matching the
     real chain);
   * the negative indices come from the forward branch `Q = -P + s(P-O₂)/ρ`.
   The unstable parameter `v(u)` is the analytic continuation of `s(t)`: invert `ugermC` at index
   `-N` by its `y`-coordinate.
   The tails `Pₙ(u) = ugermC(λⁿ v(u))` hold for real `u` and hence, by the identity theorem, for
   complex `u`. Only finitely many indices need to be checked; beyond them, use the germ step of
   `germC_facts`.
5. Take `f u :=` this chain with `ψ₁ = u` and `ψ₂ = v(u)`. It is continuous, so `f t₀ ∈ H0`.

**Pitfall.** `Γ` is only assumed continuous. Get analyticity from `Γ(t) = U^{-n}(germPt(λⁿt))`.
-/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-! ## The one-parameter family of complex chains

The chain with stable parameter `u` is

`Pₙ(u) = germC (λⁿ u)` for `n ≥ 0` and `Pₙ(u) = Rk (|n|) u` (the `|n|`-fold principal backward
branch iterate of the germ point) for `n < 0`; the unstable parameter is
`ψ₂(u) = λ⁻ᴺ g ((Rk N u).2)`, the analytic continuation of the mirror parameter of the real
connection. -/

/-- The chain point at index `n` of the family. -/
def PFam (a : ℝ) (h : ℂ → ℂ) (u : ℂ) (n : ℤ) : ℂ × ℂ :=
  if 0 ≤ n then germC a h (((eqLam a : ℂ) ^ n.natAbs) * u) else Rk a h n.natAbs u

theorem PFam_nat (a : ℝ) (h : ℂ → ℂ) (u : ℂ) (m : ℕ) :
    PFam a h u (m : ℤ) = germC a h (((eqLam a : ℂ) ^ m) * u) := by
  rw [PFam, if_pos (Int.ofNat_nonneg m)]
  simp

theorem PFam_neg (a : ℝ) (h : ℂ → ℂ) (u : ℂ) (k : ℕ) :
    PFam a h u (-(k : ℤ)) = Rk a h k u := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [PFam, Rk]
  · rw [PFam, if_neg (by omega : ¬ ((0 : ℤ) ≤ -(k : ℤ)))]
    congr 1
    simp

/-- The unstable linearising parameter of the family. -/
def psiFam (a : ℝ) (h : ℂ → ℂ) (N : ℕ) (g : ℂ → ℂ) (u : ℂ) : ℂ :=
  (((eqLam a : ℂ) ^ N)⁻¹) * g ((Rk a h N u).2)

/-- The one-parameter family of complex chains. -/
def chainFam (a : ℝ) (h : ℂ → ℂ) (N : ℕ) (g : ℂ → ℂ) (u : ℂ) : ChainData :=
  ((fun n => PFam a h u n), u, psiFam a h N g u)

@[simp] theorem chainFam_fst (a : ℝ) (h : ℂ → ℂ) (N : ℕ) (g : ℂ → ℂ) (u : ℂ) (n : ℤ) :
    (chainFam a h N g u).1 n = PFam a h u n := rfl

@[simp] theorem chainFam_psi1 (a : ℝ) (h : ℂ → ℂ) (N : ℕ) (g : ℂ → ℂ) (u : ℂ) :
    (chainFam a h N g u).2.1 = u := rfl

@[simp] theorem chainFam_psi2 (a : ℝ) (h : ℂ → ℂ) (N : ℕ) (g : ℂ → ℂ) (u : ℂ) :
    (chainFam a h N g u).2.2 = psiFam a h N g u := rfl

/-! ## Elementary algebra used below -/

theorem bsq_subO1_Rpt_sq (a : ℝ) (z : ℂ) :
    bsq (subO1 a (Rpt z)) = (((z.re + a / 2) ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
  simp only [bsq, subO1, Rpt, Prod.fst, Prod.snd]
  push_cast
  ring

theorem bsq_subO2_Rpt_sq (a : ℝ) (z : ℂ) :
    bsq (subO2 a (Rpt z)) = (((z.re - a / 2) ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
  simp only [bsq, subO2, Rpt, Prod.fst, Prod.snd]
  push_cast
  ring

theorem eqMirror_subO1_bsq (a : ℝ) (P : ℂ × ℂ) :
    bsq (subO1 a (eqMirror P)) = bsq (subO2 a P) := by
  simp only [bsq, subO1, subO2, eqMirror, Prod.fst, Prod.snd]
  ring

theorem eqMirror_subO2_bsq (a : ℝ) (P : ℂ × ℂ) :
    bsq (subO2 a (eqMirror P)) = bsq (subO1 a P) := by
  simp only [bsq, subO2, subO1, eqMirror, Prod.fst, Prod.snd]
  ring

theorem ugermC_subO1_bsq (a : ℝ) (h : ℂ → ℂ) (w : ℂ) :
    bsq (subO1 a (ugermC a h w)) = bsq (subO2 a (germC a h w)) :=
  eqMirror_subO1_bsq a (germC a h w)

theorem ugermC_subO2_bsq (a : ℝ) (h : ℂ → ℂ) (w : ℂ) :
    bsq (subO2 a (ugermC a h w)) = bsq (subO1 a (germC a h w)) :=
  eqMirror_subO2_bsq a (germC a h w)

private theorem analyticAt_eqMirror (P : ℂ × ℂ) : AnalyticAt ℂ eqMirror P := by
  have h1 : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) P :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt P
  have h2 : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) P :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt P
  have hprod : AnalyticAt ℂ (fun Q : ℂ × ℂ => (-Q.1, Q.2)) P := h1.neg.prod h2
  refine hprod.congr ?_
  filter_upwards with Q
  rfl

/-- **The real connection is a point of `⁰H`.** The chain `n ↦ Γ(λⁿ t)` (rectangular
coordinates), with `ψ₁ = t` and `ψ₂` the mirror parameter, continues to complex `t` as a
one-parameter family of complex heteroclinic chains. -/
theorem exists_H0_of_heteroclinic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    {Γ : ℝ → ℂ} (hΓ : IsHeteroclinic a h r Γ) : (H0 a h).Nonempty := by
  have hh : IsStableGerm a h r := hΓ.1
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamC : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hlam0
  obtain ⟨N, t₀, δ, δr, ρ, g0, g, ht₀, hδ, hρ, hg0, ht₀δr, ht₀ρ,
    hanC, hang, hg00, hgy, hRkreal, hreg, hRkNball, hsmall, hid⟩ :=
    tail_H0_data ha0 ha1 hh hΓ
  obtain ⟨_, _, _, hC0, _, _, _⟩ := germC_facts ha0 ha1 hh
  have hnormt₀ : ‖(t₀ : ℂ)‖ = t₀ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀]
  have ht₀δr' : t₀ < δr := lt_of_le_of_lt (le_add_of_nonneg_right hδ.le) ht₀δr
  have ht₀ρ' : t₀ < ρ := lt_of_le_of_lt (le_add_of_nonneg_right hδ.le) ht₀ρ
  have hmem_ball : ∀ {x : ℂ} {rr : ℝ}, ‖x - (t₀ : ℂ)‖ < rr → x ∈ Metric.ball (t₀ : ℂ) rr :=
    fun hx => by simpa [Metric.mem_ball, dist_eq_norm] using hx
  -- ## The germ coordinate at the base point is nonzero (it is the imaginary part of `Γ`)
  have hRkNt₀ : (Rk a h N (t₀ : ℂ)).2 ≠ 0 := by
    rw [hRkreal N t₀ ht₀ ht₀δr']
    simp only [Rpt, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (hΓ.2.2.1 _ (by positivity))
  -- ## All the pairs at the base point are regular and the slit conditions hold
  have hslit_t₀ : ∀ j : ℕ, bsq (subO1 a (Rk a h j (t₀ : ℂ))) ∈ Complex.slitPlane := by
    intro j
    have him := hΓ.2.2.1 ((eqLam a)⁻¹ ^ j * t₀) (by positivity)
    rw [hRkreal j t₀ ht₀ ht₀δr', subO1_Rpt, bsq_ofReal, Complex.ofReal_mem_slitPlane]
    nlinarith [sq_nonneg ((Γ ((eqLam a)⁻¹ ^ j * t₀)).re + a / 2),
      sq_pos_of_ne_zero (ne_of_gt him)]
  have hAnRk_t₀ : ∀ j : ℕ, AnalyticAt ℂ (fun u : ℂ => Rk a h j u) (t₀ : ℂ) := by
    intro j
    refine analyticAt_Rk (k := j) hh ?_ (fun j' _ => hslit_t₀ j')
    refine hanC _ ?_
    rw [Metric.mem_ball, dist_zero_right, hnormt₀]
    exact ht₀ρ'
  have hbsq1_cont : ∀ j : ℕ, ContinuousAt (fun u : ℂ => bsq (subO1 a (Rk a h j u)))
      (t₀ : ℂ) := by
    intro j
    have h1 : Continuous (fun P : ℂ × ℂ => bsq (subO1 a P)) := by
      have hfun : (fun P : ℂ × ℂ => bsq (subO1 a P))
          = fun P => (P.1 + (((a / 2 : ℝ)) : ℂ)) ^ 2 + P.2 ^ 2 := by
        funext P; simp [bsq, subO1]
      rw [hfun]
      exact ((continuous_fst.add continuous_const).pow 2).add (continuous_snd.pow 2)
    exact h1.continuousAt.comp (hAnRk_t₀ j).continuousAt
  have hbsq2_cont : ∀ j : ℕ, ContinuousAt (fun u : ℂ => bsq (subO2 a (Rk a h j u)))
      (t₀ : ℂ) := by
    intro j
    have h1 : Continuous (fun P : ℂ × ℂ => bsq (subO2 a P)) := by
      have hfun : (fun P : ℂ × ℂ => bsq (subO2 a P))
          = fun P => (P.1 - (((a / 2 : ℝ)) : ℂ)) ^ 2 + P.2 ^ 2 := by
        funext P; simp [bsq, subO2]
      rw [hfun]
      exact ((continuous_fst.sub continuous_const).pow 2).add (continuous_snd.pow 2)
    exact h1.continuousAt.comp (hAnRk_t₀ j).continuousAt
  have hgood : ∀ j : ℕ, bsq (subO1 a (Rk a h j (t₀ : ℂ))) ∈ Complex.slitPlane ∧
      bsq (subO2 a (Rk a h j (t₀ : ℂ))) ≠ 0 ∧
      bsq (subO1 a (Rk a h j (t₀ : ℂ))) ≠ 0 := by
    intro j
    refine ⟨hslit_t₀ j, ?_, fun h0 => Complex.zero_notMem_slitPlane (h0 ▸ hslit_t₀ j)⟩
    intro hc
    have him := hΓ.2.2.1 ((eqLam a)⁻¹ ^ j * t₀) (by positivity)
    rw [hRkreal j t₀ ht₀ ht₀δr', subO2_Rpt, bsq_ofReal, Complex.ofReal_eq_zero] at hc
    nlinarith [sq_nonneg ((Γ ((eqLam a)⁻¹ ^ j * t₀)).re - a / 2),
      sq_pos_of_ne_zero (ne_of_gt him)]
  have hloc : ∀ j : ℕ, ∀ᶠ u in 𝓝 (t₀ : ℂ),
      bsq (subO1 a (Rk a h j u)) ∈ Complex.slitPlane ∧ bsq (subO2 a (Rk a h j u)) ≠ 0 ∧
      bsq (subO1 a (Rk a h j u)) ≠ 0 := by
    intro j
    have hslit : ∀ᶠ u in 𝓝 (t₀ : ℂ), bsq (subO1 a (Rk a h j u)) ∈ Complex.slitPlane :=
      (hbsq1_cont j).eventually_mem (isOpen_slitPlane.mem_nhds (hgood j).1)
    have h2 : ∀ᶠ u in 𝓝 (t₀ : ℂ), bsq (subO2 a (Rk a h j u)) ≠ 0 :=
      (hbsq2_cont j).eventually_ne (hgood j).2.1
    have h3 : ∀ᶠ u in 𝓝 (t₀ : ℂ), bsq (subO1 a (Rk a h j u)) ≠ 0 :=
      (hbsq1_cont j).eventually_ne (hgood j).2.2
    exact hslit.and (h2.and h3)
  have hallKey : ∀ M : ℕ, ∀ᶠ u in 𝓝 (t₀ : ℂ), ∀ j : ℕ, j ≤ M →
      bsq (subO1 a (Rk a h j u)) ∈ Complex.slitPlane ∧ bsq (subO2 a (Rk a h j u)) ≠ 0 ∧
      bsq (subO1 a (Rk a h j u)) ≠ 0 := by
    intro M
    induction M with
    | zero =>
        filter_upwards [hloc 0] with u hu j hj
        have hj0 : j = 0 := by omega
        subst hj0; exact hu
    | succ n ih =>
        filter_upwards [ih, hloc (n + 1)] with u hu hu'
        intro j hj
        rcases Nat.lt_or_eq_of_le hj with h | h
        · exact hu j (Nat.lt_succ_iff.mp h)
        · subst h; exact hu'
  have hall := hallKey N
  obtain ⟨η, hηpos, hηb⟩ := Metric.mem_nhds_iff.mp hall
  -- ## the germ coordinate is nonzero on a neighbourhood of the base point
  have hyN_cont : ContinuousAt (fun u : ℂ => (Rk a h N u).2) (t₀ : ℂ) :=
    (AnalyticAt.comp ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (Rk a h N (t₀ : ℂ)))
      (hAnRk_t₀ N)).continuousAt
  obtain ⟨η₁, hη₁pos, hη₁b⟩ := Metric.mem_nhds_iff.mp (hyN_cont.eventually_ne hRkNt₀)
  -- ## the radius of the `H0`-ball
  set ε : ℝ := min η₁ (min η (min δ (t₀ / 2))) with hεdef
  have hεpos : 0 < ε := lt_min hη₁pos (lt_min hηpos (lt_min hδ (by linarith)))
  have hεη₁ : ε ≤ η₁ := min_le_left _ _
  have hεη : ε ≤ η := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεδ : ε ≤ δ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεhalf : ε ≤ t₀ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεt₀ : ε ≤ t₀ := by linarith
  -- ## the chain conditions
  have hchain : ∀ u : ℂ, ‖u - (t₀ : ℂ)‖ < ε → IsChain a h (chainFam a h N g u) := by
    intro u hu
    have huδ : ‖u - (t₀ : ℂ)‖ < δ := lt_of_lt_of_le hu hεδ
    have huη : ‖u - (t₀ : ℂ)‖ < η := lt_of_lt_of_le hu hεη
    have huη₁ : ‖u - (t₀ : ℂ)‖ < η₁ := lt_of_lt_of_le hu hεη₁
    have huρ : ‖u‖ < ρ := by
      have h1 : ‖u‖ ≤ ‖u - (t₀ : ℂ)‖ + ‖(t₀ : ℂ)‖ := norm_le_norm_sub_add u (t₀ : ℂ)
      rw [hnormt₀] at h1
      linarith
    have huηb : ∀ j : ℕ, j ≤ N →
        bsq (subO1 a (Rk a h j u)) ∈ Complex.slitPlane ∧
        bsq (subO2 a (Rk a h j u)) ≠ 0 ∧ bsq (subO1 a (Rk a h j u)) ≠ 0 :=
      hηb (hmem_ball huη)
    have hune : u ≠ 0 := by
      intro h0
      have h1 : ‖u - (t₀ : ℂ)‖ = t₀ := by
        rw [h0, zero_sub, norm_neg, hnormt₀]
      linarith
    have hN1 : (Rk a h N u).2 ≠ 0 :=
      hη₁b (hmem_ball huη₁)
    have hψne : psiFam a h N g u ≠ 0 := by
      intro hc
      apply hN1
      have hc' : (((eqLam a : ℂ) ^ N)⁻¹ * g ((Rk a h N u).2)) = 0 := hc
      rw [hid N u le_rfl huδ, hc', mul_zero]
      simp [ugermC, eqMirror, hC0]
    -- smallness of the underlying germ parameters
    have hpsi_small : ∀ m : ℕ, N ≤ m → ‖((eqLam a : ℂ) ^ m) * psiFam a h N g u‖ < ρ := by
      intro m hm
      have hpowm : ((eqLam a : ℂ) ^ m)
          = ((eqLam a : ℂ) ^ (m - N)) * ((eqLam a : ℂ) ^ N) := by
        rw [← pow_add, Nat.sub_add_cancel hm]
      have h1 : ((eqLam a : ℂ) ^ m) * psiFam a h N g u
          = ((eqLam a : ℂ) ^ (m - N)) * (((eqLam a : ℂ) ^ N) * psiFam a h N g u) := by
        rw [hpowm, mul_assoc]
      have h2 : ((eqLam a : ℂ) ^ N) * psiFam a h N g u = g ((Rk a h N u).2) := by
        rw [psiFam, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero N hlamC), one_mul]
      calc ‖((eqLam a : ℂ) ^ m) * psiFam a h N g u‖
          = ‖((eqLam a : ℂ) ^ (m - N)) * (((eqLam a : ℂ) ^ N) * psiFam a h N g u)‖ := by
            rw [h1]
        _ = (eqLam a) ^ (m - N) * ‖((eqLam a : ℂ) ^ N) * psiFam a h N g u‖ := by
            rw [norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le]
        _ ≤ 1 * ‖((eqLam a : ℂ) ^ N) * psiFam a h N g u‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlam1.le) (norm_nonneg _)
        _ = ‖g ((Rk a h N u).2)‖ := by rw [one_mul, h2]
        _ < ρ := hsmall u huδ
    have hreg_lam : ∀ m : ℕ, ‖((eqLam a : ℂ) ^ m) * u‖ < ρ := by
      intro m
      calc ‖((eqLam a : ℂ) ^ m) * u‖ = ‖((eqLam a : ℂ) ^ m)‖ * ‖u‖ := norm_mul _ _
        _ = (eqLam a) ^ m * ‖u‖ := by rw [norm_pow, Complex.norm_of_nonneg hlam0.le]
        _ ≤ 1 * ‖u‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlam1.le) (norm_nonneg _)
        _ = ‖u‖ := one_mul _
        _ < ρ := huρ
    -- nondegeneracy in the far tail, from the regular germ pairs
    have htail_nd : ∀ m : ℕ, N ≤ m →
        bsq (subO1 a (Rk a h m u)) ≠ 0 ∧ bsq (subO2 a (Rk a h (m + 1) u)) ≠ 0 := by
      intro m hm
      have hvρ := hpsi_small m hm
      have hregv := hreg (((eqLam a : ℂ) ^ m) * psiFam a h N g u) hvρ
      have h1 : Rk a h m u = ugermC a h (((eqLam a : ℂ) ^ m) * psiFam a h N g u) :=
        hid m u hm huδ
      have h2 : Rk a h (m + 1) u
          = ugermC a h (((eqLam a : ℂ) ^ (m + 1)) * psiFam a h N g u) :=
        hid (m + 1) u (by omega) huδ
      have h3 : ((eqLam a : ℂ) ^ (m + 1)) * psiFam a h N g u
          = (eqLam a : ℂ) * (((eqLam a : ℂ) ^ m) * psiFam a h N g u) := by
        rw [pow_succ]; ring
      refine ⟨?_, ?_⟩
      · rw [h1, ugermC_subO1_bsq]
        exact hregv.2.1
      · rw [h2, h3, ugermC_subO2_bsq]
        exact hregv.2.2
    refine ⟨?_, hune, hψne, ?_, ?_⟩
    · -- consecutive points form regular pairs
      intro n
      by_cases hn : 0 ≤ n
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        rw [chainFam_fst, chainFam_fst,
          show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
          PFam_nat, PFam_nat,
          show ((eqLam a : ℂ) ^ (m + 1)) * u = (eqLam a : ℂ) * (((eqLam a : ℂ) ^ m) * u)
            by rw [pow_succ]; ring]
        exact hreg _ (hreg_lam m)
      · -- `n < 0`: write `n = -↑(k+1)`
        obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(((k + 1 : ℕ)) : ℤ) := by
          refine ⟨n.natAbs - 1, ?_⟩
          have h1 : (↑((-n).natAbs) : ℤ) = -n := Int.ofNat_natAbs_of_nonneg (by omega)
          have h2 : (-n).natAbs = n.natAbs := Int.natAbs_neg n
          have h1' : (↑(n.natAbs) : ℤ) = -n := by rw [← h2]; exact h1
          have h3 : 1 ≤ n.natAbs := by omega
          rw [Nat.sub_add_cancel h3, h1', neg_neg]
        subst hk
        have h1 : (-(((k + 1 : ℕ)) : ℤ) + 1) = -((k : ℕ) : ℤ) := by push_cast; ring
        rw [chainFam_fst, chainFam_fst, PFam_neg, h1, PFam_neg]
        by_cases hNk : N ≤ k
        · have hnd := htail_nd k hNk
          refine ⟨?_, hnd.2, hnd.1⟩
          rw [Rk_succ]
          exact eqRelC_invBranch true hnd.1
        · have hnd := huηb k (by omega)
          have hnd' := huηb (k + 1) (by omega)
          refine ⟨?_, hnd'.2.1, hnd.2.2⟩
          rw [Rk_succ]
          exact eqRelC_invBranch true hnd.2.2
    · -- the forward tail
      filter_upwards with n
      rw [chainFam_fst, chainFam_psi1, PFam_nat]
    · -- the backward tail
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [chainFam_fst, chainFam_psi2, PFam_neg]
      exact hid n u hn huδ
  -- ## continuity of the family on the ball
  have hcont : ContinuousOn (chainFam a h N g) (Metric.ball (t₀ : ℂ) ε) := by
    intro x hx
    have hxε : ‖x - (t₀ : ℂ)‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hxδ : ‖x - (t₀ : ℂ)‖ < δ := lt_of_lt_of_le hxε hεδ
    have hxη : ‖x - (t₀ : ℂ)‖ < η := lt_of_lt_of_le hxε hεη
    have hxρ : ‖x‖ < ρ := by
      have h1 : ‖x‖ ≤ ‖x - (t₀ : ℂ)‖ + ‖(t₀ : ℂ)‖ := norm_le_norm_sub_add x (t₀ : ℂ)
      rw [hnormt₀] at h1
      linarith
    have hxηb : ∀ j : ℕ, j ≤ N →
        bsq (subO1 a (Rk a h j x)) ∈ Complex.slitPlane ∧
        bsq (subO2 a (Rk a h j x)) ≠ 0 ∧ bsq (subO1 a (Rk a h j x)) ≠ 0 :=
      hηb (hmem_ball hxη)
    have hxAnC : AnalyticAt ℂ (germC a h) x :=
      hanC x (by rw [Metric.mem_ball, dist_zero_right]; exact hxρ)
    have hxRk : ∀ j : ℕ, j ≤ N → AnalyticAt ℂ (fun u : ℂ => Rk a h j u) x := by
      intro j hj
      exact analyticAt_Rk (k := j) hh hxAnC (fun j' hj' => (hxηb j' (by omega)).1)
    have hxRkN : ContinuousAt (fun u : ℂ => (Rk a h N u).2) x :=
      (AnalyticAt.comp (f := fun u : ℂ => Rk a h N u) (x := x)
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (Rk a h N x)) (hxRk N le_rfl)).continuousAt
    have hgx : ContinuousAt g ((Rk a h N x).2) :=
      (hang _ (hRkNball x hxδ)).continuousAt
    have hyNan : AnalyticAt ℂ (fun u : ℂ => (Rk a h N u).2) x :=
      AnalyticAt.comp ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (Rk a h N x))
        (hxRk N le_rfl)
    have hxpsi_an : AnalyticAt ℂ (fun u : ℂ => psiFam a h N g u) x :=
      analyticAt_const.mul (AnalyticAt.comp (f := fun u : ℂ => (Rk a h N u).2) (x := x)
        (hang _ (hRkNball x hxδ)) hyNan)
    have hxpsi : ContinuousAt (fun u : ℂ => psiFam a h N g u) x := hxpsi_an.continuousAt
    have hxPFam : ∀ n : ℤ, ContinuousAt (fun u : ℂ => PFam a h u n) x := by
      intro n
      by_cases hn : 0 ≤ n
      · -- the forward branch: `PFam u n = germC (λ^{|n|} u)`
        have hb : ‖((eqLam a : ℂ) ^ n.natAbs) * x‖ < ρ := by
          calc ‖((eqLam a : ℂ) ^ n.natAbs) * x‖
              = ‖((eqLam a : ℂ) ^ n.natAbs)‖ * ‖x‖ := norm_mul _ _
            _ = (eqLam a) ^ n.natAbs * ‖x‖ := by rw [norm_pow, Complex.norm_of_nonneg hlam0.le]
            _ ≤ 1 * ‖x‖ :=
                mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlam1.le) (norm_nonneg _)
            _ = ‖x‖ := one_mul _
            _ < ρ := hxρ
        have hgerm : AnalyticAt ℂ (germC a h) (((eqLam a : ℂ) ^ n.natAbs) * x) :=
          hanC _ (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
        have hlin : AnalyticAt ℂ (fun u : ℂ => ((eqLam a : ℂ) ^ n.natAbs) * u) x :=
          analyticAt_const.mul analyticAt_id
        refine ((hgerm.comp hlin).continuousAt).congr ?_
        filter_upwards with u
        rw [PFam, if_pos hn]
        rfl
      · by_cases hkN : N ≤ n.natAbs
        · -- far backward tail: rewrite by the tail identity
          have hb : ‖((eqLam a : ℂ) ^ n.natAbs) * psiFam a h N g x‖ < ρ := by
            have hpowm : ((eqLam a : ℂ) ^ n.natAbs)
                = ((eqLam a : ℂ) ^ (n.natAbs - N)) * ((eqLam a : ℂ) ^ N) := by
              rw [← pow_add, Nat.sub_add_cancel hkN]
            have h1 : ((eqLam a : ℂ) ^ n.natAbs) * psiFam a h N g x
                = ((eqLam a : ℂ) ^ (n.natAbs - N))
                  * (((eqLam a : ℂ) ^ N) * psiFam a h N g x) := by
              rw [hpowm, mul_assoc]
            have h2 : ((eqLam a : ℂ) ^ N) * psiFam a h N g x = g ((Rk a h N x).2) := by
              rw [psiFam, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero N hlamC), one_mul]
            calc ‖((eqLam a : ℂ) ^ n.natAbs) * psiFam a h N g x‖
                = ‖((eqLam a : ℂ) ^ (n.natAbs - N))
                    * (((eqLam a : ℂ) ^ N) * psiFam a h N g x)‖ := by rw [h1]
              _ = (eqLam a) ^ (n.natAbs - N)
                    * ‖((eqLam a : ℂ) ^ N) * psiFam a h N g x‖ := by
                  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hlam0.le]
              _ ≤ 1 * ‖((eqLam a : ℂ) ^ N) * psiFam a h N g x‖ :=
                  mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0.le hlam1.le) (norm_nonneg _)
              _ = ‖g ((Rk a h N x).2)‖ := by rw [one_mul, h2]
              _ < ρ := hsmall x hxδ
          have hug : AnalyticAt ℂ (ugermC a h)
              (((eqLam a : ℂ) ^ n.natAbs) * psiFam a h N g x) := by
            have h1 : ugermC a h = fun w => eqMirror (germC a h w) := rfl
            rw [h1]
            refine (analyticAt_eqMirror _).comp ?_
            refine hanC _ ?_
            rw [Metric.mem_ball, dist_zero_right]
            exact hb
          have hlin : AnalyticAt ℂ
              (fun u : ℂ => ((eqLam a : ℂ) ^ n.natAbs) * psiFam a h N g u) x :=
              analyticAt_const.mul hxpsi_an
          refine ((AnalyticAt.comp (f := fun u : ℂ => ((eqLam a : ℂ) ^ n.natAbs) * psiFam a h N g u)
            (x := x) hug hlin).continuousAt).congr ?_
          filter_upwards [Metric.isOpen_ball.mem_nhds (hmem_ball hxδ)] with w hw
          have hwδ : ‖w - (t₀ : ℂ)‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
          rw [PFam, if_neg hn]
          exact (hid n.natAbs w hkN hwδ).symm
        · -- near backward tail: the iterated branch map is analytic
          refine ((hxRk n.natAbs (by omega)).continuousAt).congr ?_
          filter_upwards with u
          rw [PFam, if_neg hn]
    · -- assemble the components
      rw [continuousWithinAt_prod_iff]
      refine ⟨?_, ?_⟩
      · show Tendsto (fun u : ℂ => (chainFam a h N g u).1) (𝓝[Metric.ball (t₀ : ℂ) ε] x)
          (𝓝 ((chainFam a h N g x).1))
        rw [tendsto_pi_nhds]
        intro n
        exact (hxPFam n).continuousWithinAt
      · rw [continuousWithinAt_prod_iff]
        refine ⟨?_, ?_⟩
        · exact (continuousAt_id (x := x)).continuousWithinAt
        · exact hxpsi.continuousWithinAt
  refine ⟨chainFam a h N g (t₀ : ℂ), ε, hεpos, chainFam a h N g, hcont, rfl, ?_⟩
  intro u hu
  exact ⟨hchain u (by simpa [Metric.mem_ball, dist_eq_norm] using hu), rfl⟩

end

end Work.EQ

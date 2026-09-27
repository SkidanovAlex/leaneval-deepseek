import Mathlib
import Submission.Work.EQ.exists_regular_of_family
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.junction_values_countable_ns
import Submission.Work.EQ.exists_accPt_principal_of_uncountable
import Submission.Work.EQ.H0_reg_wset
import Submission.Work.EQ.junction_open_of_uncountable

/-! # `junction_regular_of_uncountable` (Rychlik step: an uncountable junction set is regular)

Given an uncountable labelled junction set at depth `N` (`ε.length = s.length = N`), the junction
identity holds on an open set: this is `Work.EQ.junction_open_of_uncountable`, which produces an
open `B`, a point `x ∈ B` and an analytic chain `H 0 = fan a h ε`, …, `H N =` the mirrored unstable
fan, with `EqRelC` between consecutive levels.  The lemma `Work.EQ.assembly` below turns exactly
that data into a regular component of `⁰H` with value `C`, by exhibiting the candidate chain
`ψ₁ = z`, `ψ₂ = C/z` (forward fan, middle `H j`, far mirrored fan) and applying
`Work.EQ.exists_regular_of_family`.  The two small lemmas above `assembly` are the two algebraic
steps of that chain (the forward fan step and the far mirrored step of the relation). -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

set_option maxHeartbeats 2000000

/-- The forward step of the stable fan satisfies the equichordal relation. -/
theorem eqRelC_fan_cons {a : ℝ} {h : ℂ → ℂ} {ε' : List Bool} {t : Bool} {u : ℂ}
    (hne : bsq (subO1 a (fan a h ε' (((eqLam a : ℝ) : ℂ) * u))) ≠ 0) :
    EqRelC a (fan a h (t :: ε') u) (fan a h ε' (((eqLam a : ℝ) : ℂ) * u)) := by
  rw [show fan a h (t :: ε') u
      = invBranch a t (fan a h ε' (((eqLam a : ℝ) : ℂ) * u)) from rfl]
  exact eqRelC_invBranch t hne

/-- **Far (mirrored) step.**  Consecutive levels of the mirrored unstable fan satisfy the
equichordal relation. -/
theorem eqRelC_mirror_far {a : ℝ} {h : ℂ → ℂ} {η : List Bool} {u : ℂ} {k : ℕ}
    {ρg : ℝ} (hk : 1 ≤ k)
    (hgreg : ∀ w : ℂ, ‖w‖ < ρg → RegPair a (germC a h w) (germC a h (((eqLam a : ℝ) : ℂ) * w)))
    (hu : ‖(((eqLam a : ℝ) : ℂ) ^ (k - 1) * u)‖ < ρg)
    (hfan : bsq (subO1 a (fan a h (η.drop k) (((eqLam a : ℝ) : ℂ) ^ k * u))) ≠ 0) :
    EqRelC a (eqMirror (fan a h (η.drop k) (((eqLam a : ℝ) : ℂ) ^ k * u)))
      (eqMirror (fan a h (η.drop (k - 1)) (((eqLam a : ℝ) : ℂ) ^ (k - 1) * u))) := by
  have hdrop : η.drop k = (η.drop (k - 1)).drop 1 := by
    rw [show (η.drop (k - 1)).drop 1 = η.drop ((k - 1) + 1) from List.drop_drop]
    congr 1; omega
  have hku : (((eqLam a : ℝ) : ℂ) ^ k * u)
      = ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ (k - 1) * u) := by
    have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk', pow_succ']
    ring
  rcases hc : η.drop (k - 1) with _ | ⟨t, L⟩
  · have hk' : η.drop k = [] := by rw [hdrop, hc]; rfl
    have h1 : fan a h (η.drop k) (((eqLam a : ℝ) : ℂ) ^ k * u)
        = germC a h (((eqLam a : ℝ) : ℂ) ^ k * u) := by rw [hk']; rfl
    have h2 : fan a h [] (((eqLam a : ℝ) : ℂ) ^ (k - 1) * u)
        = germC a h (((eqLam a : ℝ) : ℂ) ^ (k - 1) * u) := rfl
    rw [h1, h2, hku]
    exact eqRelC_mirror_swap (hgreg _ hu).1
  · have hL : L = η.drop k := by rw [hdrop, hc]; rfl
    have h1 : fan a h (t :: L) (((eqLam a : ℝ) : ℂ) ^ (k - 1) * u)
        = invBranch a t (fan a h (η.drop k) (((eqLam a : ℝ) : ℂ) ^ k * u)) := by
      rw [hL, hku]
      rfl
    rw [h1]
    exact eqRelC_mirror_swap (eqRelC_invBranch t hfan)

/-- **The assembly.** -/
theorem assembly {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {N : ℕ} {ε η s : List Bool} {C : ℂ}
    (hε : ε.length = N) (hs : s.length = N) (hC : C ≠ 0)
    {B : Set ℂ} {x : ℂ} {H : ℕ → ℂ → ℂ × ℂ} {δ₁ : ℝ}
    (hδ₁0 : 0 < δ₁) (hBopen : IsOpen B) (hxB : x ∈ B)
    (hBlt : ∀ z ∈ B, ‖z‖ < δ₁)
    (hBΩ : B ⊆ {w : ℂ | w ≠ 0 ∧ ‖((eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁})
    (hH0 : H 0 = fan a h ε)
    (hHan : ∀ j : ℕ, j ≤ N → AnalyticOnNhd ℂ (H j) B)
    (hHrel : ∀ j : ℕ, j < N → ∀ z ∈ B, EqRelC a (H (j + 1) z) (H j z))
    (hHN : ∀ z ∈ B, H N z = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))))
    {Ke Lam Q δFan ρg : ℝ} (hδFan : 0 < δFan) (hρg : 0 < ρg)
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δFan → FanGood a h Ke Lam Q ε' v)
    (hgan : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    (hgreg : ∀ u : ℂ, ‖u‖ < ρg → RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)))
    (hδ₁δFan : δ₁ ≤ δFan) (hδ₁ρg : δ₁ ≤ ρg) :
    ∃ T : Set ChainData, IsRegComp a h T C := by
  classical
  have hlam0 : 0 < eqLam a := eqLam_pos_aux ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one_aux ha0 ha1
  have hlamne : ((eqLam a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  -- the ball inside `B`
  obtain ⟨εx, hεx, hbsub⟩ := Metric.isOpen_iff.mp hBopen x hxB
  set U : Set ℂ := Metric.ball x εx with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self hεx
  have hUconn : IsConnected U := (convex_ball x εx).isConnected ⟨x, hxU⟩
  have hUB : U ⊆ B := hbsub
  have hzB : ∀ z ∈ U, z ∈ B := fun z hz => hUB hz
  have hzlt : ∀ z ∈ U, ‖z‖ < δ₁ := fun z hz => hBlt z (hUB hz)
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz => (hBΩ (hUB hz)).1
  have hzlam : ∀ z ∈ U, ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖ < δ₁ :=
    fun z hz => (hBΩ (hUB hz)).2
  -- norm identities
  have hnormz : ∀ (n : ℤ) (w : ℂ), ‖((eqLam a : ℝ) : ℂ) ^ n * w‖ = (eqLam a) ^ n * ‖w‖ :=
    fun n w => by rw [norm_mul, norm_zpow_eqLam ha0 ha1 n]
  have hnormn : ∀ (k : ℕ) (w : ℂ), ‖((eqLam a : ℝ) : ℂ) ^ k * w‖ = (eqLam a) ^ k * ‖w‖ :=
    fun k w => by rw [norm_mul, norm_pow_eqLam ha0 ha1 k]
  have hzsmall : ∀ z ∈ U, ∀ n : ℤ, 0 ≤ n →
      ‖((eqLam a : ℝ) : ℂ) ^ n * z‖ < δFan ∧ ‖((eqLam a : ℝ) : ℂ) ^ n * z‖ < ρg := by
    intro z hz n hn
    have h1 : ‖((eqLam a : ℝ) : ℂ) ^ n * z‖ = (eqLam a) ^ n * ‖z‖ := hnormz n z
    have h2 : (eqLam a) ^ n ≤ 1 := zpow_le_one_of_nonneg hlam0.le hlam1.le hn
    have h3 : (eqLam a) ^ n * ‖z‖ ≤ ‖z‖ := by
      simpa using mul_le_mul_of_nonneg_right h2 (norm_nonneg z)
    have h4 : ‖z‖ < δ₁ := hzlt z hz
    constructor <;> (rw [h1]; linarith)
  have hzlamN : ∀ z ∈ U, (eqLam a) ^ N * ‖C / z‖ < δ₁ := by
    intro z hz
    have h := hzlam z hz
    rw [hnormn N (C / z)] at h
    exact h
  have hczsmall : ∀ z ∈ U, ∀ k : ℕ, N ≤ k →
      ‖((eqLam a : ℝ) : ℂ) ^ k * (C / z)‖ < δFan ∧
      ‖((eqLam a : ℝ) : ℂ) ^ k * (C / z)‖ < ρg := by
    intro z hz k hk
    have h1 : ‖((eqLam a : ℝ) : ℂ) ^ k * (C / z)‖ = (eqLam a) ^ k * ‖C / z‖ := hnormn k (C / z)
    have h2 : (eqLam a) ^ k ≤ (eqLam a) ^ N := pow_le_pow_of_le_one hlam0.le hlam1.le hk
    have h3 : (eqLam a) ^ k * ‖C / z‖ ≤ (eqLam a) ^ N * ‖C / z‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : (eqLam a) ^ N * ‖C / z‖ < δ₁ := hzlamN z hz
    constructor <;> (rw [h1]; linarith [hδ₁δFan, hδ₁ρg])
  have hrad : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δFan → bsq (subO1 a (fan a h ε' v)) ≠ 0 := by
    intro ε' v hv h0
    have hpos := (hFG ε' v hv).2.2.2.2
    have hb : bsq (subO1 a (fan a h ε' v))
        = ((fan a h ε' v).1 + (a / 2 : ℂ)) ^ 2 + (fan a h ε' v).2 ^ 2 := by
      simp only [bsq, subO1]
      push_cast
      ring
    rw [← hb] at hpos
    rw [h0] at hpos
    simp at hpos
  -- the candidate chain
  set m : ℂ → ℤ → ℂ × ℂ := fun z n =>
    if 0 ≤ n then
      (if n.toNat ≤ N then fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ n * z)
       else germC a h (((eqLam a : ℝ) : ℂ) ^ n * z))
    else
      (if (-n).toNat ≤ N then H ((-n).toNat) z
       else eqMirror (fan a h (η.drop ((-n).toNat - N))
              (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z)))) with hmdef
  have m_pos_fan : ∀ z n, 0 ≤ n → n.toNat ≤ N →
      m z n = fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ n * z) := by
    intro z n hn hnN; simp only [hmdef]; rw [if_pos hn, if_pos hnN]
  have m_pos_germ : ∀ z n, 0 ≤ n → ¬ (n.toNat ≤ N) →
      m z n = germC a h (((eqLam a : ℝ) : ℂ) ^ n * z) := by
    intro z n hn hnN; simp only [hmdef]; rw [if_pos hn, if_neg hnN]
  have m_neg_bwd : ∀ z n, ¬ (0 ≤ n) → (-n).toNat ≤ N → m z n = H ((-n).toNat) z := by
    intro z n hn hnN; simp only [hmdef]; rw [if_neg hn, if_pos hnN]
  have m_neg_far : ∀ z n, ¬ (0 ≤ n) → ¬ ((-n).toNat ≤ N) →
      m z n = eqMirror (fan a h (η.drop ((-n).toNat - N))
        (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z))) := by
    intro z n hn hnN; simp only [hmdef]; rw [if_neg hn, if_neg hnN]
  have m_zero : ∀ z, m z 0 = fan a h ε z := by
    intro z
    rw [m_pos_fan z 0 (le_refl 0) (by omega)]
    simp
  -- the far entries, indexed by their depth
  set G : ℂ → ℕ → ℂ × ℂ := fun z d =>
    eqMirror (fan a h (η.drop (d - N)) (((eqLam a : ℝ) : ℂ) ^ d * (C / z))) with hGdef
  have mG : ∀ z n, ¬ (0 ≤ n) → ¬ ((-n).toNat ≤ N) → m z n = G z ((-n).toNat) := by
    intro z n hn hk
    rw [m_neg_far z n hn hk]
  -- analyticity of the chain entries
  have hm : ∀ n : ℤ, AnalyticOnNhd ℂ (fun z => m z n) U := by
    intro n
    by_cases hn : 0 ≤ n
    · by_cases hnN : n.toNat ≤ N
      · have hrep : (fun z => m z n)
            = fun z => fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ n * z) := by
          funext z; exact m_pos_fan z n hn hnN
        rw [hrep]
        refine analyticOnNhd_fan_comp hFG ?_ ?_ _
        · exact fun z _ => analyticAt_const.mul analyticAt_id
        · intro z hz
          exact (hzsmall z hz n hn).1
      · have hrep : (fun z => m z n) = fun z => germC a h (((eqLam a : ℝ) : ℂ) ^ n * z) := by
          funext z; exact m_pos_germ z n hn hnN
        rw [hrep]
        refine fun z hz => ?_
        have hmem : ((eqLam a : ℝ) : ℂ) ^ n * z ∈ Metric.ball 0 ρg := by
          rw [Metric.mem_ball, dist_zero_right]
          exact (hzsmall z hz n hn).2
        exact (hgan _ hmem).comp (analyticAt_const.mul analyticAt_id)
    · have hn' : n < 0 := by omega
      by_cases hk : (-n).toNat ≤ N
      · have hrep : (fun z => m z n) = H ((-n).toNat) := by
          funext z; exact m_neg_bwd z n hn hk
        rw [hrep]
        exact (hHan (-n).toNat hk).mono (fun z hz => hUB hz)
      · have hrep : (fun z => m z n)
            = fun z => eqMirror (fan a h (η.drop ((-n).toNat - N))
                (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z))) := by
          funext z; exact m_neg_far z n hn hk
        rw [hrep]
        refine fun z hz => ?_
        have hmap : AnalyticAt ℂ
            (fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / w)) z :=
          analyticAt_const.mul (AnalyticAt.div analyticAt_const analyticAt_id (hz0 z hz))
        have hmem : ‖((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z)‖ < δFan :=
          (hczsmall z hz ((-n).toNat) (by omega)).1
        have hf : AnalyticAt ℂ (fan a h (η.drop ((-n).toNat - N)))
            (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / z)) := (hFG _ _ hmem).1
        have h1 : AnalyticAt ℂ (fun w => fan a h (η.drop ((-n).toNat - N))
            (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / w))) z :=
          AnalyticAt.comp (g := fan a h (η.drop ((-n).toNat - N)))
            (f := fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / w)) hf hmap
        exact AnalyticAt.comp (g := fun P : ℂ × ℂ => eqMirror P)
          (f := fun w : ℂ => fan a h (η.drop ((-n).toNat - N))
            (((eqLam a : ℝ) : ℂ) ^ ((-n).toNat) * (C / w)))
          (Work.EQ.analyticAt_eqMirror _) h1
  -- the far step
  have Gstep : ∀ z ∈ U, ∀ d : ℕ, N + 1 ≤ d → EqRelC a (G z d) (G z (d - 1)) := by
    intro z hz d hd
    have hk1 : 1 ≤ d - N := by omega
    have hstep := eqRelC_mirror_far (a := a) (h := h) (η := η)
      (u := ((eqLam a : ℝ) : ℂ) ^ N * (C / z)) (k := d - N) (ρg := ρg) hk1 hgreg ?_ ?_
    · have hmul : ((eqLam a : ℝ) : ℂ) ^ (d - N) * (((eqLam a : ℝ) : ℂ) ^ N * (C / z))
          = ((eqLam a : ℝ) : ℂ) ^ d * (C / z) := by
        have h : d - N + N = d := by omega
        rw [← mul_assoc, ← pow_add, h]
      have hmul' : ((eqLam a : ℝ) : ℂ) ^ (d - N - 1) * (((eqLam a : ℝ) : ℂ) ^ N * (C / z))
          = ((eqLam a : ℝ) : ℂ) ^ (d - 1) * (C / z) := by
        have h : d - N - 1 + N = d - 1 := by omega
        rw [← mul_assoc, ← pow_add, h]
      have hidx : d - N - 1 = d - 1 - N := by omega
      rw [hmul, hmul', hidx] at hstep
      simp only [hGdef]
      exact hstep
    · have h1 : ‖((eqLam a : ℝ) : ℂ) ^ (d - N - 1) * (((eqLam a : ℝ) : ℂ) ^ N * (C / z))‖
          = ‖((eqLam a : ℝ) : ℂ) ^ (d - 1) * (C / z)‖ := by
        have h : d - N - 1 + N = d - 1 := by omega
        rw [← mul_assoc, ← pow_add, h]
      rw [h1, hnormn (d - 1) (C / z)]
      have h2 : (eqLam a) ^ (d - 1) ≤ (eqLam a) ^ N :=
        pow_le_pow_of_le_one hlam0.le hlam1.le (by omega)
      have h3 : (eqLam a) ^ (d - 1) * ‖C / z‖ ≤ (eqLam a) ^ N * ‖C / z‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      have h4 : (eqLam a) ^ N * ‖C / z‖ < δ₁ := hzlamN z hz
      linarith [hδ₁ρg]
    · refine hrad (η.drop (d - N)) _ ?_
      have h1 : ‖((eqLam a : ℝ) : ℂ) ^ (d - N) * (((eqLam a : ℝ) : ℂ) ^ N * (C / z))‖
          = ‖((eqLam a : ℝ) : ℂ) ^ d * (C / z)‖ := by
        have h : d - N + N = d := by omega
        rw [← mul_assoc, ← pow_add, h]
      rw [h1]
      exact (hczsmall z hz d (by omega)).1
  -- the equichordal relation at every step
  have hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a (m z n) (m z (n + 1)) := by
    intro z hz n
    by_cases hn : 0 ≤ n
    · by_cases hnN : n + 1 ≤ N
      · -- forward fan window
        have hkn : n.toNat < ε.length := by
          have h1 : (n + 1).toNat = n.toNat + 1 := by omega
          rw [hε]; omega
        have hdrop : ε.drop n.toNat = ε[n.toNat] :: ε.drop (n.toNat + 1) :=
          (List.getElem_cons_drop hkn).symm
        have hv0 := m_pos_fan z n hn (by omega : n.toNat ≤ N)
        have hv1 : m z (n + 1)
            = fan a h (ε.drop (n.toNat + 1)) (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z) := by
          have h1 : (n + 1).toNat = n.toNat + 1 := by omega
          rw [m_pos_fan z (n + 1) (by omega) (by omega), h1]
        rw [hv0, hv1, hdrop]
        have harg : ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n * z)
            = ((eqLam a : ℝ) : ℂ) ^ (n + 1) * z := by
          rw [zpow_add_one₀ hlamne]; ring
        rw [← harg]
        refine eqRelC_fan_cons ?_
        refine hrad _ _ ?_
        rw [harg]
        exact (hzsmall z hz (n + 1) (by omega)).1
      · -- germ window (`n ≥ N`)
        have hv0 : m z n = germC a h (((eqLam a : ℝ) : ℂ) ^ n * z) := by
          by_cases hnn : n.toNat ≤ N
          · rw [m_pos_fan z n hn hnn]
            have hdrop0 : ε.drop n.toNat = [] := by
              rw [List.drop_eq_nil_of_le]; rw [hε]; omega
            rw [hdrop0]; rfl
          · exact m_pos_germ z n hn hnn
        have hv1 : m z (n + 1) = germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * z) := by
          have h1 : (n + 1).toNat = n.toNat + 1 := by omega
          refine m_pos_germ z (n + 1) (by omega) (by rw [h1]; omega)
        rw [hv0, hv1]
        have hlt : ‖((eqLam a : ℝ) : ℂ) ^ n * z‖ < ρg := (hzsmall z hz n hn).2
        have hlamu : ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n * z)
            = ((eqLam a : ℝ) : ℂ) ^ (n + 1) * z := by
          rw [zpow_add_one₀ hlamne]; ring
        rw [← hlamu]
        exact (hgreg _ hlt).1
    · -- negative indices
      have hn' : n < 0 := by omega
      set d : ℕ := (-n).toNat with hddef
      have hd1 : 1 ≤ d := by omega
      have hn_eq : n = -(d : ℤ) := by
        have h2 : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
        rw [← hddef] at h2
        omega
      have hdd : (-(-(d : ℤ))).toNat = d := by rw [neg_neg, Int.toNat_natCast]
      have hdc : -(d : ℤ) + 1 = -(((d - 1 : ℕ)) : ℤ) := by omega
      have hdn : (-(-(((d - 1 : ℕ)) : ℤ))).toNat = d - 1 := by
        rw [neg_neg, Int.toNat_natCast]
      have hnegc : ¬ (0 ≤ -(d : ℤ)) := by omega
      rcases lt_or_ge d (N + 1) with hdN | hdN
      · -- middle window, `d ≤ N`
        have hdle : d ≤ N := by omega
        have hc2 : (-(-(d : ℤ))).toNat ≤ N := by rw [hdd]; exact hdle
        have hv0 : m z n = H d z := by
          rw [hn_eq]
          simpa only [hdd] using m_neg_bwd z (-(d : ℤ)) hnegc hc2
        have hv1 : m z (n + 1) = H (d - 1) z := by
          rw [hn_eq, hdc]
          by_cases hd0 : d - 1 = 0
          · have h1 : -(((d - 1 : ℕ)) : ℤ) = 0 := by simp [hd0]
            rw [h1, m_zero z, ← hH0, hd0]
          · have hnegc' : ¬ (0 ≤ -(((d - 1 : ℕ)) : ℤ)) := by omega
            have hc4 : (-(-(((d - 1 : ℕ)) : ℤ))).toNat ≤ N := by
              rw [hdn]
              exact le_trans (Nat.sub_le d 1) hdle
            rw [m_neg_bwd z (-(((d - 1 : ℕ)) : ℤ)) hnegc' hc4]
            rw [hdn]
        rw [hv0, hv1]
        have hmain := hHrel (d - 1) (by omega) z (hzB z hz)
        have h4 : d - 1 + 1 = d := by omega
        rw [h4] at hmain
        exact hmain
      · -- far window, `d ≥ N + 1`
        have hdN1 : N + 1 ≤ d := by omega
        have hc2 : ¬ ((-(-(d : ℤ))).toNat ≤ N) := by rw [hdd]; omega
        have hv0 : m z n = G z d := by
          rw [hn_eq]
          simpa only [hdd] using mG z (-(d : ℤ)) hnegc hc2
        have hv1 : m z (n + 1) = G z (d - 1) := by
          rw [hn_eq, hdc]
          rcases lt_or_eq_of_le (show N ≤ d - 1 by omega) with hlt | heq
          · have hnegc' : ¬ (0 ≤ -(((d - 1 : ℕ)) : ℤ)) := by omega
            have hc4 : ¬ ((-(-(((d - 1 : ℕ)) : ℤ))).toNat ≤ N) := by
              rw [hdn]; exact not_le.mpr hlt
            simpa only [hdn] using mG z (-(((d - 1 : ℕ)) : ℤ)) hnegc' hc4
          · have hc4 : (-(-(((d - 1 : ℕ)) : ℤ))).toNat ≤ N := by
              rw [hdn]; exact le_of_eq heq.symm
            by_cases hd0 : d - 1 = 0
            · have hN0 : N = 0 := by omega
              have h1 : -(((d - 1 : ℕ)) : ℤ) = 0 := by simp [hd0]
              subst hN0
              rw [h1, m_zero z, ← hH0, hd0, hGdef]
              simpa using hHN z (hzB z hz)
            · have hnegc' : ¬ (0 ≤ -(((d - 1 : ℕ)) : ℤ)) := by omega
              rw [m_neg_bwd z (-(((d - 1 : ℕ)) : ℤ)) hnegc' hc4, hdn, ← heq, hGdef]
              simpa using hHN z (hzB z hz)
        rw [hv0, hv1]
        exact Gstep z hz d hdN1
  -- the smallness depth
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (eqLam a) ^ K * δ₁ < r := by
    have htend : Tendsto (fun k : ℕ => (eqLam a) ^ k * δ₁) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const δ₁
    exact (htend.eventually (isOpen_Iio.mem_nhds (hh.1))).exists
  set M : ℕ := max (max (N + 1) (N + η.length)) (max K (N + K)) with hMdef
  have hM1 : N + 1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : N + η.length ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3 : K ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM4 : N + K ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsmallM : ∀ z ∈ U, ‖((eqLam a : ℝ) : ℂ) ^ M * (fun z => z) z‖ < r ∧
      ‖((eqLam a : ℝ) : ℂ) ^ M * (fun z => C / z) z‖ < r := by
    intro z hz
    constructor
    · rw [hnormn M z]
      have h2 : (eqLam a) ^ M ≤ (eqLam a) ^ K := pow_le_pow_of_le_one hlam0.le hlam1.le hM3
      have h3 : (eqLam a) ^ M * ‖z‖ ≤ (eqLam a) ^ K * δ₁ :=
        calc (eqLam a) ^ M * ‖z‖ ≤ (eqLam a) ^ K * ‖z‖ :=
              mul_le_mul_of_nonneg_right h2 (norm_nonneg z)
          _ ≤ (eqLam a) ^ K * δ₁ :=
              mul_le_mul_of_nonneg_left (le_of_lt (hzlt z hz)) (pow_nonneg hlam0.le K)
      linarith [hK]
    · rw [hnormn M (C / z)]
      have hsplit : (eqLam a) ^ M * ‖C / z‖
          = (eqLam a) ^ (M - N) * ((eqLam a) ^ N * ‖C / z‖) := by
        have h : M - N + N = M := by omega
        rw [← mul_assoc, ← pow_add, h]
      rw [hsplit]
      have h2 : (eqLam a) ^ (M - N) ≤ (eqLam a) ^ K :=
        pow_le_pow_of_le_one hlam0.le hlam1.le (by omega)
      have h3 : (eqLam a) ^ (M - N) * ((eqLam a) ^ N * ‖C / z‖)
          ≤ (eqLam a) ^ K * δ₁ :=
        mul_le_mul h2 (le_of_lt (hzlamN z hz)) (by positivity) (pow_nonneg hlam0.le K)
      linarith [hK]
  -- the tails
  have hsM : ∀ z ∈ U, ∀ n : ℕ, M ≤ n →
      m z (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * z) := by
    intro z hz n hn
    have h1 : ¬ (((n : ℤ)).toNat ≤ N) := by rw [Int.toNat_natCast]; omega
    rw [m_pos_germ z (n : ℤ) (by omega) h1, zpow_natCast]
  have husM : ∀ z ∈ U, ∀ n : ℕ, M ≤ n →
      m z (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (C / z)) := by
    intro z hz n hn
    have hneq : ¬ ((-(-(n : ℤ))).toNat ≤ N) := by
      rw [neg_neg, Int.toNat_natCast]; omega
    rw [m_neg_far z (-(n : ℤ)) (by omega) hneq]
    have htoNat : (-(-(n : ℤ))).toNat = n := by simp
    rw [htoNat]
    have hdrop : η.drop (n - N) = [] := by
      rw [List.drop_eq_nil_of_le]; omega
    rw [hdrop]
    rfl
  -- the parameter is not constant
  have hnc : ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ := by
    obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
    have hnorm2 : ‖((e / 2 : ℝ) : ℂ)‖ = e / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < e / 2)]
    have hdist : dist (x + ((e / 2 : ℝ) : ℂ)) x = e / 2 := by
      rw [dist_eq_norm, show x + ((e / 2 : ℝ) : ℂ) - x = ((e / 2 : ℝ) : ℂ) by ring, hnorm2]
    refine ⟨x, hxU, x + ((e / 2 : ℝ) : ℂ), hball (Metric.mem_ball.mpr ?_), ?_⟩
    · rw [hdist]; linarith
    · intro hcon; rw [← hcon, dist_self] at hdist; linarith
  -- assemble
  obtain ⟨p, hp, hval⟩ := exists_regular_of_family ha0 ha1 hh hUopen hUconn
    (m := m) (u := fun z => z) (v := fun z => C / z) (c := C) hC hm analyticOnNhd_id
    (fun z hz => hz0 z hz) (fun z hz => mul_div_cancel₀ C (hz0 z hz)) hnc hrel (N := M)
    hsmallM hsM husM
  exact ⟨connectedComponentIn (H0 a h) p, connectedComponentIn_subset (H0 a h) p,
    ⟨p, hp, rfl⟩, hval⟩



/-- **An uncountable junction set is realised by a regular component.** -/
theorem junction_regular_of_uncountable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ (N : ℕ) (ε η s : List Bool) (C : ℂ), ε.length = N → s.length = N →
      C ≠ 0 →
      ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧
          ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁ ∧
          Work.EQ.bwdP a s (Work.EQ.fan a h ε w) =
            Work.EQ.eqMirror (Work.EQ.fan a h η
              (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (C / w)))}.Countable →
      ∃ T : Set Work.EQ.ChainData, Work.EQ.IsRegComp a h T C := by
  obtain ⟨δ₀, hδ₀, hred⟩ := junction_open_of_uncountable ha0 ha1 hh
  obtain ⟨Ke, Lam, Q, δFan, hKe, hLam, hQ, hδFan, hFG'⟩ := fan_induction ha0 ha1 hh
  have hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δFan → FanGood a h Ke Lam Q ε' v :=
    fun ε' v hv => hFG' ε' v (by simpa [Metric.mem_ball, dist_zero_right] using hv)
  obtain ⟨ρg, hρg, hgan, hg0, hgreg', hginj, hgd⟩ := germC_facts ha0 ha1 hh
  have hgreg : ∀ u : ℂ, ‖u‖ < ρg →
      RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)) :=
    fun u hu => (hgreg' u (by simpa [Metric.mem_ball, dist_zero_right] using hu)).1
  refine ⟨min δ₀ (min δFan ρg), lt_min hδ₀ (lt_min hδFan hρg), ?_⟩
  intro N ε η s C hε hs hC hunc
  have hpos : 0 < min δ₀ (min δFan ρg) := lt_min hδ₀ (lt_min hδFan hρg)
  have hle0 : min δ₀ (min δFan ρg) ≤ δ₀ := min_le_left _ _
  have hleF : min δ₀ (min δFan ρg) ≤ δFan := le_trans (min_le_right _ _) (min_le_left _ _)
  have hleρ : min δ₀ (min δFan ρg) ≤ ρg := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨B, x, H, hBopen, hxB, hBlt, hBΩ, hH0, hHan, hHrel, hHN⟩ :=
    hred hpos hle0 N ε η s C hε hs hC hunc
  exact assembly ha0 ha1 hh hε hs hC hpos hBopen hxB hBlt hBΩ hH0 hHan hHrel hHN
    hδFan hρg hFG hgan hgreg hleF hleρ

end

end Work.EQ

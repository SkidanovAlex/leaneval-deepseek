import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.component_shiftZ_invariant
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.TailLocalDef
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.tail_uniform_of_isPreconnected
import Submission.Work.Analysis.Complex.punctured_ball_connected

/-! # Both ends of a compact regular cycle are principal

`Work.EQ.cycle_ends_principal`, the "both ends" interface of `Work.EQ.rational_of_compact_cycle`
(design: `Submission/Work/EQ/DESIGN_CCM.md`, §2 B).

Mathematical content (Rychlik Thm 8(2), "finitely many words over an annulus", read at both ends):

* the compact-modulo-punctures hypothesis `hcpt2` covers `S ∩ {ψ₁ ∈ A}`, for the fixed annulus
  `A`, by a compact subset of `⁰H` together with finitely many *half* punctured charts;
* on each half chart the parameters `ψ₁` and `ψ₂ = c/ψ₁` are bounded: the chart image is
  preconnected, `⁰H` is unramified there, so it is entirely inside the component `S` as soon as it
  meets it, and there `ψ₁ψ₂ = c`;
* `Work.EQ.tail_uniform_of_isPreconnected` then bounds the tail indices uniformly on the compact
  piece and on each half chart;
* shifting back from the annulus with `σᵈ` (inverse shift for the `ψ₁`-end, forward shift for the
  `ψ₂`-end, whose `ψ₁`-annulus is `c/A` by `ψ₁ψ₂ = c`) turns a uniform annulus bound into the
  principal-tail statement at both ends.
-/

namespace Work.EQ

open Filter _root_.Topology Metric
open scoped Topology
open Classical

noncomputable section


/-! ## Elementary facts about `λ = eqLam a` -/

lemma eqLam_pos_of' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma eqLam_lt_one_of' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma eqLamC_ne_zero' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ((eqLam a : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos_of' ha0 ha1))

lemma norm_eqLamC' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eqLam_pos_of' ha0 ha1)]

/-- `‖ψ₁‖` after an integer shift scales by `λ^j`. -/
lemma norm_psi1_shiftZ' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) (q : ChainData) :
    ‖(shiftZ a j q).2.1‖ = (eqLam a) ^ j * ‖q.2.1‖ := by
  rw [shiftZ_psi1, norm_mul, norm_zpow, norm_eqLamC' ha0 ha1]

/-- `‖ψ₂‖` after an integer shift scales by `λ^{-j}`. -/
lemma norm_psi2_shiftZ' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) (q : ChainData) :
    ‖(shiftZ a j q).2.2‖ = (eqLam a) ^ (-j) * ‖q.2.2‖ := by
  rw [shiftZ_psi2, norm_div, norm_zpow, norm_eqLamC' ha0 ha1, div_eq_mul_inv, ← zpow_neg]
  ring

lemma psi1_ne_zero_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    q.2.1 ≠ 0 := (isChain_of_mem_H0 hq).2.1

lemma psi2_ne_zero_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    q.2.2 ≠ 0 := (isChain_of_mem_H0 hq).2.2.1

/-! ## Arithmetic of the shift into the annulus `[1, λ^{-d}]` -/

/-- **Shifting a small modulus into the annulus `[1, λ^{-d}]`.**  If `0 < s < λ^N` then there is
`k` with `N ≤ d * k` and `1 ≤ s * (λ ^ (d * k))⁻¹ ≤ (λ ^ d)⁻¹`. -/
lemma exists_pow_annulus {lam s : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) {d : ℕ}
    (hd : 0 < d) {N : ℕ} (hs0 : 0 < s) (hsN : s < lam ^ N) :
    ∃ k : ℕ, N ≤ d * k ∧ 1 ≤ (lam ^ (d * k))⁻¹ * s ∧ (lam ^ (d * k))⁻¹ * s ≤ (lam ^ d)⁻¹ := by
  have hlamd0 : 0 < lam ^ d := pow_pos hlam0 d
  have hlamd1 : lam ^ d < 1 := pow_lt_one₀ (le_of_lt hlam0) hlam1 (Nat.pos_iff_ne_zero.mp hd)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hs0 hlamd1
  have hk' : lam ^ (d * k) ≤ s := le_of_lt ((pow_mul lam d k).symm ▸ hk)
  have hP : ∃ k : ℕ, lam ^ (d * k) ≤ s := ⟨k, hk'⟩
  set k₀ := Nat.find hP with hk₀def
  have hspec : lam ^ (d * k₀) ≤ s := Nat.find_spec hP
  have hmin : ∀ j < k₀, ¬ (lam ^ (d * j) ≤ s) := fun j hj => Nat.find_min hP hj
  refine ⟨k₀, ?_, ?_, ?_⟩
  · have h1 : lam ^ (d * k₀) < lam ^ N := lt_of_le_of_lt hspec hsN
    have h3 : N < d * k₀ := by
      by_contra hc
      push Not at hc
      have h4 := pow_le_pow_of_le_one (le_of_lt hlam0) (le_of_lt hlam1) hc
      linarith
    omega
  · have hpos : 0 < lam ^ (d * k₀) := pow_pos hlam0 _
    rw [mul_comm ((lam ^ (d * k₀))⁻¹) s, le_mul_inv_iff₀ hpos]
    simpa using hspec
  · have hk0 : 0 < k₀ := by
      rcases Nat.eq_zero_or_pos k₀ with h | h
      · exfalso
        have h2 : lam ^ N ≤ 1 := pow_le_one₀ (le_of_lt hlam0) (le_of_lt hlam1)
        rw [h, mul_zero, pow_zero] at hspec
        linarith
      · exact h
    have h5 : s < lam ^ (d * (k₀ - 1)) := lt_of_not_ge (hmin (k₀ - 1) (by omega))
    have h6 : d * (k₀ - 1) + d = d * k₀ := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h7 : lam ^ (d * k₀) = lam ^ (d * (k₀ - 1)) * lam ^ d := by rw [← pow_add, h6]
    have h10 : lam ^ (d * k₀) * (lam ^ d)⁻¹ = lam ^ (d * (k₀ - 1)) := by
      rw [h7]; field_simp
    have h11 : s ≤ lam ^ (d * k₀) * (lam ^ d)⁻¹ := h10 ▸ le_of_lt h5
    have h12 : (0 : ℝ) ≤ (lam ^ (d * k₀))⁻¹ := inv_nonneg.mpr (pow_pos hlam0 _).le
    calc (lam ^ (d * k₀))⁻¹ * s
        = s * (lam ^ (d * k₀))⁻¹ := by rw [mul_comm]
      _ ≤ (lam ^ (d * k₀) * (lam ^ d)⁻¹) * (lam ^ (d * k₀))⁻¹ :=
          mul_le_mul_of_nonneg_right h11 h12
      _ = (lam ^ d)⁻¹ := by
          rw [mul_assoc, mul_comm ((lam ^ d)⁻¹) ((lam ^ (d * k₀))⁻¹), ← mul_assoc,
            mul_inv_cancel₀ (ne_of_gt (pow_pos hlam0 _)), one_mul]

/-! ## Chart facts -/

/-- Membership in the punctured unit disc, in terms of the modulus. -/
lemma mem_ball_one_punct {ζ : ℂ} : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} ↔ 0 < ‖ζ‖ ∧ ‖ζ‖ < 1 := by
  rw [Set.mem_diff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff, norm_pos_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩


lemma isPuncturedChart_continuousOn {a : ℝ} {h : ℂ → ℂ} {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k) :
    ContinuousOn e {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < 1} := by
  obtain ⟨hk, hu₀, κ, hκ, hchart, hinj, hcont, hmer, hmer'⟩ := he
  refine hcont.mono ?_
  intro ζ hζ
  exact mem_ball_one_punct.mpr hζ

lemma isPuncturedChart_mem_H0 {a : ℝ} {h : ℂ → ℂ} {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k) {ζ : ℂ} (h1 : 0 < ‖ζ‖) (h2 : ‖ζ‖ < 1) :
    e ζ ∈ H0 a h := by
  obtain ⟨hk, hu₀, κ, hκ, hchart, hinj, hcont, hmer, hmer'⟩ := he
  exact (hchart ζ (mem_ball_one_punct.mpr ⟨h1, h2⟩)).1

lemma isPuncturedChart_psi {a : ℝ} {h : ℂ → ℂ} {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k) {ζ : ℂ} (h1 : 0 < ‖ζ‖) (h2 : ‖ζ‖ < 1) :
    ∃ κ : ℂ, κ ≠ 0 ∧ (e ζ).2.1 = u₀ + κ * ζ ^ k := by
  obtain ⟨hk, hu₀, κ, hκ, hchart, hinj, hcont, hmer, hmer'⟩ := he
  exact ⟨κ, hκ, (hchart ζ (mem_ball_one_punct.mpr ⟨h1, h2⟩)).2⟩

/-- On a small disc `‖ζ‖ ≤ δ`, `ψ₁ ∘ e` stays within a factor `3/2` of its centre. -/
lemma puncturedChart_small_disc {a : ℝ} {h : ℂ → ℂ} {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ ≤ δ → ‖(e ζ).2.1 - u₀‖ ≤ ‖u₀‖ / 2 := by
  obtain ⟨hk, hu₀, κ, hκ, hchart, hinj, hcont, hmer, hmer'⟩ := he
  have hκ0 : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  refine ⟨min (1 / 2) (‖u₀‖ / (2 * ‖κ‖)), lt_min (by norm_num) (by positivity), min_le_left _ _,
    ?_⟩
  intro ζ hζ0 hζ
  have hζle : ‖ζ‖ ≤ ‖u₀‖ / (2 * ‖κ‖) := le_trans hζ (min_le_right _ _)
  have hζ12 : ‖ζ‖ ≤ 1 / 2 := le_trans hζ (min_le_left _ _)
  have hζ1 : ‖ζ‖ ≤ 1 := le_trans hζ12 (by norm_num)
  have hmem : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    mem_ball_one_punct.mpr ⟨hζ0, lt_of_le_of_lt hζ12 (by norm_num)⟩
  have hpow : ‖ζ‖ ^ k ≤ ‖ζ‖ := by
    have hk1 : 1 ≤ k := hk
    simpa using pow_le_pow_of_le_one (norm_nonneg ζ) hζ1 hk1
  rw [(hchart ζ hmem).2]
  calc ‖u₀ + κ * ζ ^ k - u₀‖ = ‖κ * ζ ^ k‖ := by rw [add_sub_cancel_left]
    _ = ‖κ‖ * ‖ζ‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ ‖κ‖ * ‖ζ‖ := mul_le_mul_of_nonneg_left hpow (norm_nonneg κ)
    _ ≤ ‖κ‖ * (‖u₀‖ / (2 * ‖κ‖)) := mul_le_mul_of_nonneg_left hζle (norm_nonneg κ)
    _ = ‖u₀‖ / 2 := by field_simp

/-- The image of a punctured disc is preconnected. -/
lemma chart_image_preconnected {e : ℂ → ChainData} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hecont : ContinuousOn e {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < 1}) :
    IsPreconnected (e '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ}) := by
  have hconn : IsPreconnected {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ} := by
    have h := (Work.Analysis.Complex.isConnected_punctured_ball_at (0 : ℂ) hδ0).isPreconnected
    have hset : {z : ℂ | 0 < ‖z - (0 : ℂ)‖ ∧ ‖z - (0 : ℂ)‖ < δ}
        = {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ} := by
      ext z; simp
    rwa [hset] at h
  refine hconn.image e (hecont.mono ?_)
  intro ζ hζ
  exact ⟨hζ.1, lt_of_lt_of_le hζ.2 hδ1⟩

/-- **A chart half disc that meets a component lies in it.** -/
lemma chart_image_subset_of_meets {a : ℝ} {h : ℂ → ℂ} {p : ChainData} {S : Set ChainData}
    (hS : S = connectedComponentIn (H0 a h) p) {e : ℂ → ChainData} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (heH0 : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 → e ζ ∈ H0 a h)
    (hpre : IsPreconnected (e '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ}))
    {q : ChainData} (hq : q ∈ S) (hqe : q ∈ e '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ}) :
    e '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ} ⊆ S := by
  have hTH0 : e '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ} ⊆ H0 a h := by
    rintro - ⟨ζ, hζ, rfl⟩
    exact heH0 ζ hζ.1 (lt_of_lt_of_le hζ.2 hδ1)
  have hcomp : e '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ} ⊆ connectedComponentIn (H0 a h) q :=
    hpre.subset_connectedComponentIn hqe hTH0
  have hq' : q ∈ connectedComponentIn (H0 a h) p := by rw [← hS]; exact hq
  intro x hx
  have hx'' : x ∈ connectedComponentIn (H0 a h) p := by
    rw [connectedComponentIn_eq hq']
    exact hcomp hx
  rw [hS]
  exact hx''

/-- **Uniform tails on a compact subset of `⁰H`.** -/
lemma compact_tails {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {C : Set ChainData} (hC : C ⊆ H0 a h) (hcpt : IsCompact C) :
    ∃ N : ℕ, ∀ q ∈ C, ∀ n : ℕ, N ≤ n →
      q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ (n : ℤ) * q.2.1) ∧
      q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n : ℤ) * q.2.2) := by
  choose Nf Mf Kf ef hεf hNKf hMKf hprop using
    fun x : C => H0_tail_bounded ha0 ha1 hh (x : ChainData) (hC x.2)
  have hcov : C ⊆ ⋃ i : C, tailNbhd (i : ChainData) (Kf i) (ef i) := by
    intro q hq
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩,
      ⟨fun k _ => by simpa using hεf ⟨q, hq⟩, by simpa using hεf ⟨q, hq⟩,
        by simpa using hεf ⟨q, hq⟩⟩⟩
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun i : C => tailNbhd (i : ChainData) (Kf i) (ef i))
    (fun i => isOpen_tailNbhd _ _ _) hcov
  refine ⟨t.sup (fun i => max (Nf i) (Mf i)), ?_⟩
  intro q hq n hn
  obtain ⟨i, hit, hiq⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_biUnion, exists_prop] using ht hq
  have hmax : max (Nf i) (Mf i) ≤ t.sup (fun i => max (Nf i) (Mf i)) :=
    Finset.le_sup (f := fun i => max (Nf i) (Mf i)) hit
  obtain ⟨h1, h2⟩ := hprop i q (hC hq) hiq.1 hiq.2.1 hiq.2.2
  exact ⟨h1 n (le_trans (le_trans (le_max_left _ _) hmax) hn),
    h2 n (le_trans (le_trans (le_max_right _ _) hmax) hn)⟩

/-- The iterated forward shift preserves an invariant set. -/
lemma hShift_iterate_mem {a : ℝ} {S : Set ChainData} {d : ℕ}
    (hcyc : ∀ q ∈ S, (hShift a)^[d] q ∈ S) :
    ∀ j : ℕ, ∀ q ∈ S, (hShift a)^[d * j] q ∈ S := by
  intro j
  induction j with
  | zero => intro q hq; simpa using hq
  | succ j ih =>
    intro q hq
    rw [show d * (j + 1) = d * j + d by ring, Function.iterate_add_apply]
    exact ih _ (hcyc q hq)

/-! ## The uniform bound over an annulus -/

/-- **Uniform tails on the `ψ₁`-annulus.**  Both the forward and the backward tail of every chain
of the component whose `ψ₁`-value lies in the annulus are the principal leaves from one common
index on.  The proof uses only `H0_tail_bounded`, the half-disc compactness hypothesis and
`tail_uniform_of_isPreconnected`. -/
lemma uniform_tails_on_annulus {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) {c : ℂ}
    (hc : ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c) {d : ℕ} (hd : 0 < d)
    (hcyc : ∀ q ∈ connectedComponentIn (H0 a h) p,
      (hShift a)^[d] q ∈ connectedComponentIn (H0 a h) p)
    (hcpt2 : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      ∃ C : Set ChainData, IsCompact C ∧ C ⊆ H0 a h ∧
        ∃ (m : ℕ) (e : Fin m → ℂ → ChainData) (u₀ : Fin m → ℂ) (k : Fin m → ℕ),
          (∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i)) ∧
          connectedComponentIn (H0 a h) p ∩ {q | q.2.1 ∈ K} ⊆
            C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0}))
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') :
    ∃ N : ℕ, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 ∈ Ann ρ ρ' →
      (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ (n : ℤ) * q.2.1)) ∧
      (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n : ℤ) * q.2.2)) := by
  set S : Set ChainData := connectedComponentIn (H0 a h) p with hSdef
  have hSsub : S ⊆ H0 a h := connectedComponentIn_subset (H0 a h) p
  have hc0 : c ≠ 0 := by
    have h1 := hc p (mem_connectedComponentIn hp)
    have h2 := (isChain_of_mem_H0 hp).2
    intro h0
    rw [h0] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h2.1 h
    · exact h2.2.1 h
  -- the annulus is compact and avoids `0`
  have hKcpt : IsCompact (Ann ρ ρ') := by
    have hset : Ann ρ ρ' = Metric.closedBall (0 : ℂ) ρ' ∩ {z : ℂ | ρ ≤ ‖z‖} := by
      ext z
      simp only [Ann, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, Set.mem_inter_iff]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hset]
    exact (isCompact_closedBall (0 : ℂ) ρ').inter_right (isClosed_Ici.preimage continuous_norm)
  have hK0 : (0 : ℂ) ∉ Ann ρ ρ' := by
    intro h0; simp only [Ann, Set.mem_setOf_eq, norm_zero] at h0; linarith [h0.1]
  obtain ⟨C, hCcpt, hCH0, m, e, u₀, k, hcharts, hcover⟩ := hcpt2 (Ann ρ ρ') hKcpt hK0
  -- the bound on the compact piece
  obtain ⟨NC, hNC⟩ := compact_tails ha0 ha1 hh hCH0 hCcpt
  -- the small disc of every chart
  choose δ hδ0 hδ1 hδb using fun i : Fin m => puncturedChart_small_disc (hcharts i)
  -- the compact "shell" of every chart
  have hshellcpt : ∀ i : Fin m, IsCompact (e i '' {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2}) := by
    intro i
    have hcpt : IsCompact {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2} := by
      have hset : {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2}
          = Metric.closedBall (0 : ℂ) (1 / 2) ∩ {ζ : ℂ | δ i ≤ ‖ζ‖} := by
        ext z
        simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, Set.mem_inter_iff]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      rw [hset]
      exact (isCompact_closedBall (0 : ℂ) (1 / 2)).inter_right
        (isClosed_Ici.preimage continuous_norm)
    refine hcpt.image_of_continuousOn ((isPuncturedChart_continuousOn (hcharts i)).mono ?_)
    intro ζ hζ
    exact ⟨by linarith [hζ.1, hδ0 i], by linarith [hζ.2]⟩
  have hshellH0 : ∀ i : Fin m, e i '' {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2} ⊆ H0 a h := by
    intro i
    rintro - ⟨ζ, hζ, rfl⟩
    exact isPuncturedChart_mem_H0 (hcharts i) (by linarith [hζ.1, hδ0 i]) (by linarith [hζ.2])
  have hCp : IsCompact (C ∪ ⋃ i : Fin m, e i '' {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2}) :=
    hCcpt.union (isCompact_iUnion hshellcpt)
  have hCp0 : C ∪ ⋃ i : Fin m, e i '' {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2} ⊆ H0 a h := by
    intro q hq
    rcases hq with hq | hq
    · exact hCH0 hq
    · simp only [Set.mem_iUnion] at hq
      obtain ⟨i, hqi⟩ := hq
      exact hshellH0 i hqi
  obtain ⟨NCp, hNCp⟩ := compact_tails ha0 ha1 hh hCp0 hCp
  -- the bound on each chart half disc
  have hchart_bound : ∀ i : Fin m, ∃ N : ℕ, ∀ q ∈ S,
      q ∈ e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i} →
      (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ (n : ℤ) * q.2.1)) ∧
      (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n : ℤ) * q.2.2)) := by
    intro i
    have hpre : IsPreconnected (e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i}) :=
      chart_image_preconnected (hδ0 i) (by linarith [hδ1 i]) (isPuncturedChart_continuousOn (hcharts i))
    have hsub : e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i} ⊆ H0 a h := by
      rintro - ⟨ζ, hζ, rfl⟩
      exact isPuncturedChart_mem_H0 (hcharts i) hζ.1 (lt_of_lt_of_le hζ.2 (by linarith [hδ1 i]))
    by_cases hne : (e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i} ∩ S).Nonempty
    · obtain ⟨q₀, hq₀T, hq₀S⟩ := hne
      have hsubS : e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i} ⊆ S :=
        chart_image_subset_of_meets hSdef (hδ0 i) (by linarith [hδ1 i])
          (fun ζ hζ0 hζ1 => isPuncturedChart_mem_H0 (hcharts i) hζ0 hζ1) hpre hq₀S hq₀T
      -- bounds on `ψ₁` and `ψ₂` on the chart image
      have hB₁ : ∀ q ∈ e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i},
          ‖q.2.1‖ ≤ max (3 * ‖u₀ i‖ / 2) (2 * ‖c‖ / ‖u₀ i‖) := by
        rintro - ⟨ζ, hζ, rfl⟩
        have h1 : ‖(e i ζ).2.1 - u₀ i‖ ≤ ‖u₀ i‖ / 2 := hδb i ζ hζ.1 (le_of_lt hζ.2)
        refine le_trans ?_ (le_max_left _ _)
        calc ‖(e i ζ).2.1‖ = ‖((e i ζ).2.1 - u₀ i) + u₀ i‖ := by congr 1; ring
          _ ≤ ‖(e i ζ).2.1 - u₀ i‖ + ‖u₀ i‖ := norm_add_le _ _
          _ ≤ 3 * ‖u₀ i‖ / 2 := by linarith
      have hB₂ : ∀ q ∈ e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i},
          ‖q.2.2‖ ≤ max (3 * ‖u₀ i‖ / 2) (2 * ‖c‖ / ‖u₀ i‖) := by
        rintro - ⟨ζ, hζ, rfl⟩
        have h1 : ‖(e i ζ).2.1 - u₀ i‖ ≤ ‖u₀ i‖ / 2 := hδb i ζ hζ.1 (le_of_lt hζ.2)
        have hlow : ‖u₀ i‖ / 2 ≤ ‖(e i ζ).2.1‖ := by
          have h3 : ‖u₀ i‖ ≤ ‖(e i ζ).2.1 - u₀ i‖ + ‖(e i ζ).2.1‖ := by
            have h := norm_add_le (u₀ i - (e i ζ).2.1) ((e i ζ).2.1)
            rw [sub_add_cancel] at h
            rw [norm_sub_rev] at h
            linarith
          linarith
        have hne0 : ‖u₀ i‖ ≠ 0 := norm_ne_zero_iff.mpr (hcharts i).2.1
        have hprod := hc (e i ζ) (hsubS ⟨ζ, hζ, rfl⟩)
        have hψ₁ne : (e i ζ).2.1 ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hprod; exact hc0 hprod.symm
        have h2 : (e i ζ).2.2 = c / (e i ζ).2.1 := by
          rw [eq_div_iff hψ₁ne, mul_comm]; exact hprod
        rw [h2, norm_div]
        refine le_trans ?_ (le_max_right _ _)
        have h4 : ‖c‖ / ‖(e i ζ).2.1‖ ≤ ‖c‖ / (‖u₀ i‖ / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg c) (by positivity) hlow
        calc ‖c‖ / ‖(e i ζ).2.1‖ ≤ ‖c‖ / (‖u₀ i‖ / 2) := h4
          _ = 2 * ‖c‖ / ‖u₀ i‖ := by field_simp
      obtain ⟨N, hN⟩ := tail_uniform_of_isPreconnected ha0 ha1 hh hpre hsub hB₁ hB₂
      exact ⟨N, fun q _ hq => ⟨fun n hn => (hN q hq n hn).1, fun n hn => (hN q hq n hn).2⟩⟩
    · exact ⟨0, fun q hqS hqT => absurd ⟨q, hqT, hqS⟩ hne⟩
  choose Ni hNi using hchart_bound
  refine ⟨max NCp (Finset.univ.sup Ni), ?_⟩
  intro q hqS hqA
  have hcover' := hcover ⟨hqS, hqA⟩
  rcases hcover' with hqC | hqU
  · exact ⟨fun n hn => (hNCp q (Or.inl hqC) n (le_trans (le_max_left _ _) hn)).1,
      fun n hn => (hNCp q (Or.inl hqC) n (le_trans (le_max_left _ _) hn)).2⟩
  · simp only [Set.mem_iUnion, Set.mem_image] at hqU
    obtain ⟨i, ζ, hζ, hζq⟩ := hqU
    have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr (by simpa using hζ.2)
    have hζ12 : ‖ζ‖ < 1 / 2 := by
      have := hζ.1; rwa [Metric.mem_ball, dist_zero_right] at this
    by_cases hsmall : ‖ζ‖ < δ i
    · have hiN : Ni i ≤ max NCp (Finset.univ.sup Ni) :=
        le_trans (Finset.le_sup (f := Ni) (Finset.mem_univ i)) (le_max_right _ _)
      have hqT : q ∈ e i '' {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < δ i} := ⟨ζ, ⟨hζ0, hsmall⟩, hζq⟩
      exact ⟨fun n hn => ((hNi i q hqS hqT).1 n (le_trans hiN hn)),
        fun n hn => ((hNi i q hqS hqT).2 n (le_trans hiN hn))⟩
    · have hshell : q ∈ e i '' {ζ : ℂ | δ i ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 1 / 2} :=
        ⟨ζ, ⟨not_lt.mp hsmall, le_of_lt hζ12⟩, hζq⟩
      exact ⟨fun n hn => (hNCp q (Or.inr (Set.mem_iUnion.mpr ⟨i, hshell⟩)) n
          (le_trans (le_max_left _ _) hn)).1,
        fun n hn => (hNCp q (Or.inr (Set.mem_iUnion.mpr ⟨i, hshell⟩)) n
          (le_trans (le_max_left _ _) hn)).2⟩

/-! ## The main theorem -/

/-- **Both ends of a compact regular cycle are principal.** If the component `S` of `p` has constant `ψ₁ψ₂`, is carried into itself by `σᵈ`, and is compact modulo punctures with every chart used only on its half disc, then every chain of `S` with small `ψ₁` has its index-0 point on the stable germ, and every chain of `S` with small `ψ₂` has its index-0 point on the unstable germ. The proof needs `Submission.Work.EQ.tail_uniform_of_isPreconnected` (lead-dispatched; add its import once it lands). This is an interface of `Work.EQ.rational_of_compact_cycle` (see `Submission/Work/EQ/DESIGN_CCM.md`, §2 B). -/
theorem cycle_ends_principal {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) {c : ℂ}
    (hc : ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c) {d : ℕ} (hd : 0 < d)
    (hcyc : ∀ q ∈ connectedComponentIn (H0 a h) p,
      (hShift a)^[d] q ∈ connectedComponentIn (H0 a h) p)
    (hcpt2 : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      ∃ C : Set ChainData, IsCompact C ∧ C ⊆ H0 a h ∧
        ∃ (m : ℕ) (e : Fin m → ℂ → ChainData) (u₀ : Fin m → ℂ) (k : Fin m → ℕ),
          (∀ i, IsPuncturedChart a h (e i) (u₀ i) (k i)) ∧
          connectedComponentIn (H0 a h) p ∩ {q | q.2.1 ∈ K} ⊆
            C ∪ ⋃ i, e i '' (Metric.ball (0 : ℂ) (1 / 2) \ {0})) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ q ∈ connectedComponentIn (H0 a h) p, ‖q.2.1‖ < ε → q.1 0 = germC a h q.2.1) ∧
      (∀ q ∈ connectedComponentIn (H0 a h) p, ‖q.2.2‖ < ε → q.1 0 = ugermC a h q.2.2) := by
  have hl0 : 0 < eqLam a := eqLam_pos_of' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one_of' ha0 ha1
  have hlamC : ((eqLam a : ℝ) : ℂ) ≠ 0 := eqLamC_ne_zero' ha0 ha1
  set S : Set ChainData := connectedComponentIn (H0 a h) p with hSdef
  have hSsub : S ⊆ H0 a h := connectedComponentIn_subset (H0 a h) p
  have hc0 : c ≠ 0 := by
    have h1 := hc p (mem_connectedComponentIn hp)
    have h2 := (isChain_of_mem_H0 hp).2
    intro h0
    rw [h0] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact h2.1 h
    · exact h2.2.1 h
  have hLd0 : 0 < eqLam a ^ d := pow_pos hl0 d
  have hLd1 : eqLam a ^ d < 1 := by
    exact pow_lt_one₀ (le_of_lt hl0) hl1 (Nat.pos_iff_ne_zero.mp hd)
  -- the two annulus bounds
  obtain ⟨N₁, hN₁⟩ := uniform_tails_on_annulus ha0 ha1 hh hp hc hd hcyc hcpt2
    (ρ := 1) (ρ' := (eqLam a ^ d)⁻¹) one_pos ((one_lt_inv_iff₀).mpr ⟨hLd0, hLd1⟩)
  obtain ⟨N₂, hN₂⟩ := uniform_tails_on_annulus ha0 ha1 hh hp hc hd hcyc hcpt2
    (ρ := ‖c‖ * eqLam a ^ d) (ρ' := ‖c‖)
    (mul_pos (norm_pos_iff.mpr hc0) hLd0)
    (by have h := norm_pos_iff.mpr hc0; nlinarith [h, hLd1])
  refine ⟨min ((eqLam a) ^ N₁) ((eqLam a) ^ N₂),
    lt_min (pow_pos hl0 _) (pow_pos hl0 _), ?_, ?_⟩
  · -- the `ψ₁`-end: shift backwards into the annulus `[1, (λ^d)^{-1}]`
    intro q hqS hq
    have hqne : q.2.1 ≠ 0 := psi1_ne_zero_of_mem_H0 (hSsub hqS)
    have hs0 : 0 < ‖q.2.1‖ := norm_pos_iff.mpr hqne
    have hqN : ‖q.2.1‖ < (eqLam a) ^ N₁ := lt_of_lt_of_le hq (min_le_left _ _)
    obtain ⟨k, hkN, hk1, hk2⟩ := exists_pow_annulus hl0 hl1 hd hs0 hqN
    set D : ℤ := ((d * k : ℕ) : ℤ) with hD
    have hDneg : -D = ((d : ℤ) * (-(k : ℤ))) := by simp only [hD]; push_cast; ring
    have hq'S : shiftZ a (-D) q ∈ S := by
      have := shiftZ_mem_component ha0 ha1 hp hcyc (-(k : ℤ)) q hqS
      rwa [← hDneg] at this
    have hmem : (shiftZ a (-D) q).2.1 ∈ Ann 1 ((eqLam a ^ d)⁻¹) := by
      have hnorm : ‖(shiftZ a (-D) q).2.1‖ = ((eqLam a) ^ (d * k))⁻¹ * ‖q.2.1‖ := by
        rw [norm_psi1_shiftZ' ha0 ha1 (-D) q, hD]
        simp only [zpow_neg, zpow_natCast]
      rw [Ann, Set.mem_setOf_eq, hnorm]
      exact ⟨hk1, hk2⟩
    have htail := (hN₁ (shiftZ a (-D) q) hq'S hmem).1 (d * k) hkN
    have harg : ((eqLam a : ℂ) ^ D) * (shiftZ a (-D) q).2.1 = q.2.1 := by
      rw [shiftZ_psi1, ← mul_assoc, ← zpow_add₀ hlamC, add_neg_cancel, zpow_zero, one_mul]
    have h0 : q.1 0 = (shiftZ a (-D) q).1 ((d * k : ℕ) : ℤ) := by
      have hcancel : shiftZ a D (shiftZ a (-D) q) = q := by
        simpa using (shiftZ_neg_apply ha0 ha1 (-D) q).2
      conv_lhs => rw [← hcancel]
      rw [shiftZ_fst]
      simp only [zero_add, hD]
    rw [h0, htail, harg]
  · -- the `ψ₂`-end: shift forwards into the annulus `[1, (λ^d)^{-1}]`
    intro q hqS hq
    have hqne : q.2.2 ≠ 0 := psi2_ne_zero_of_mem_H0 (hSsub hqS)
    have hs0 : 0 < ‖q.2.2‖ := norm_pos_iff.mpr hqne
    have hqN : ‖q.2.2‖ < (eqLam a) ^ N₂ := lt_of_lt_of_le hq (min_le_right _ _)
    obtain ⟨k, hkN, hk1, hk2⟩ := exists_pow_annulus hl0 hl1 hd hs0 hqN
    set D : ℤ := ((d * k : ℕ) : ℤ) with hD
    have hq''S : (hShift a)^[d * k] q ∈ S := hShift_iterate_mem hcyc k q hqS
    have hq'' : shiftZ a D q = (hShift a)^[d * k] q :=
      (hShift_iterate_eq_shiftZ ha0 ha1 (d * k) q).symm
    have hmemψ₂ : ‖(shiftZ a D q).2.2‖ = ((eqLam a) ^ (d * k))⁻¹ * ‖q.2.2‖ := by
      rw [norm_psi2_shiftZ' ha0 ha1 D q, hD]
      simp only [zpow_neg, zpow_natCast]
    have hpsi₂ : 1 ≤ ‖(shiftZ a D q).2.2‖ ∧ ‖(shiftZ a D q).2.2‖ ≤ (eqLam a ^ d)⁻¹ := by
      rw [hmemψ₂]; exact ⟨hk1, hk2⟩
    -- the `ψ₂`-annulus condition is the `ψ₁`-annulus `[‖c‖λ^d, ‖c‖]`
    have hprod := hc (shiftZ a D q) (hq'' ▸ hq''S)
    have hψ₂ne : (shiftZ a D q).2.2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hprod; exact hc0 hprod.symm
    have hψ₂pos : 0 < ‖(shiftZ a D q).2.2‖ := norm_pos_iff.mpr hψ₂ne
    have hψ₁ : ‖(shiftZ a D q).2.1‖ = ‖c‖ / ‖(shiftZ a D q).2.2‖ := by
      have h2 : (shiftZ a D q).2.1 = c / (shiftZ a D q).2.2 := by
        rw [eq_div_iff hψ₂ne]; exact hprod
      rw [h2, norm_div]
    have hmem : (shiftZ a D q).2.1 ∈ Ann (‖c‖ * eqLam a ^ d) ‖c‖ := by
      rw [Ann, Set.mem_setOf_eq, hψ₁]
      have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hψ₂pos]
        have h5 : eqLam a ^ d * ‖(shiftZ a D q).2.2‖ ≤ 1 := by
          calc eqLam a ^ d * ‖(shiftZ a D q).2.2‖
              ≤ eqLam a ^ d * (eqLam a ^ d)⁻¹ :=
                mul_le_mul_of_nonneg_left hpsi₂.2 hLd0.le
            _ = 1 := mul_inv_cancel₀ (ne_of_gt hLd0)
        calc ‖c‖ * eqLam a ^ d * ‖(shiftZ a D q).2.2‖
            = ‖c‖ * (eqLam a ^ d * ‖(shiftZ a D q).2.2‖) := by ring
          _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left h5 hcpos.le
          _ = ‖c‖ := by ring
      · rw [div_le_iff₀ hψ₂pos]
        have h5 := mul_le_mul_of_nonneg_left hpsi₂.1 hcpos.le
        linarith
    have htail := (hN₂ (shiftZ a D q) (hq'' ▸ hq''S) hmem).2 (d * k) hkN
    have harg : ((eqLam a : ℂ) ^ D) * (shiftZ a D q).2.2 = q.2.2 := by
      rw [shiftZ_psi2, div_eq_mul_inv]
      rw [show ((eqLam a : ℂ) ^ D) * (q.2.2 * ((eqLam a : ℂ) ^ D)⁻¹)
          = q.2.2 * (((eqLam a : ℂ) ^ D) * ((eqLam a : ℂ) ^ D)⁻¹) by ring,
        mul_inv_cancel₀ (zpow_ne_zero _ hlamC), mul_one]
    have h0 : q.1 0 = (shiftZ a D q).1 (-D) := by
      rw [shiftZ_fst]
      simp only [neg_add_cancel]
    rw [h0, htail, harg]

end

end Work.EQ

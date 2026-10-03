/-
# The bad part of the linear lacunary variational estimate (Area A7, §8)

`Work.KMTAreas.A7.Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n` is the predicate "the scale `n` is *core* but
not *narrow*" (`core ∧ ¬ Farey`), i.e. one of the scales on which the Ionescu–Wainger endpoint
bound for narrow symbols cannot be invoked.  This module proves that the `r`-variation of the
family

  `n ↦ (if core n ∧ ¬ Farey n then Tex ρ l₁ (φ_{⌊a n⌋,t}) f else 0)`

is bounded on `ℓ^p(ℤ)` by a *constant* times `‖f‖_{ℓ^p}`, uniformly in the data
`a, l₁, l₂, k₁, k₂, t, f` (the constant may depend on `ρ, C₀, Cρc, Λ, r, p` only).  This is the
"the bad scales cost only a constant" step of the assembly of
`Work.KMTAreas.A7.lacunaryBumpVarEstimate` (see `lacunaryBumpAssembly`).

## Route

* `exists_Lnat_le_of_bad` : on the bad scales `n` (if there is any) the whole multi-index is
  bounded, `Lnat l₁ l₂ k₁ k₂ ≤ B` with `B = B(ρ,C₀,Cρc,Λ)`;
* consequently `¬ Farey` gives `Log ⌊a n⌋ < B + Cρc·2^{ρB} + 1`, so `⌊a n⌋ < X` for the explicit
  constant `X = 2^{B + Cρc·2^{ρB} + 2} + 1`; by lacunarity (`lacunary_index_bound`) all bad
  indices are `< N₀ = ⌈log X / log Λ + 2⌉`;
* the family is supported on the *finite* set `Finset.range N₀`, so `(varsum)` (the finite-support
  bound `eLpNorm_variationalNorm_le_sum` of `Submission/SingleScale.lean`) reduces the estimate to
  the single-scale bounds of its members;
* each member is `Tex ρ l₁ (φ_{N,t}) f = Tle ρ l₁ (φ_{N,t}) f − Tle ρ (l₁−1) (φ_{N,t}) f`
  (`Tex_eq_Tle_sub_of_bounded` for `l₁ ≥ 1`; both sides vanish for `l₁ = 0`), and each
  `Tle ρ l (φ_{N,t})` is bounded on `ℓ^p` by the *constant* `Cfun l` of
  `Tle_varphiNt_single_scale` (the single-scale Young bound, uniform in `N, k₁, t`);
* the constants are made uniform over the finite set `l ≤ B` by summing them.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.exists_Lnat_le_of_bad
import Submission.Work.KMTAreas.A7.lacunary_index_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.Analysis.EndVar Work.KMTContract

/-! ## §1. Elementary side conditions of the `core` regime -/

lemma lacBumpBad_two_le_splitCut (ρ : ℝ) (L : ℕ) : 2 ≤ splitCut ρ L := by
  have h1 : 1 ≤ 2 ^ scaleCount 1 ρ L := by
    have h0 : 0 < 2 ^ scaleCount 1 ρ L := pow_pos (by norm_num) _
    omega
  rw [splitCut]
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ scaleCount 1 ρ L) := pow_le_pow_right' (a := 2) (by norm_num) h1

/-- On the core the height `k₁` is at most `Log N`, hence `2 ^ k₁ ≤ N`. -/
lemma lacBumpBad_two_pow_le_floor_of_core {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ}
    {a : ℕ → NNReal} {n : ℕ} (h : core ρ C₀ l₁ l₂ k₁ k₂ a n) :
    2 ^ k₁ ≤ Nat.floor (a n) := by
  obtain ⟨-, hcut, hmain⟩ := h
  have hN : 2 < Nat.floor (a n) := lt_of_le_of_lt (lacBumpBad_two_le_splitCut ρ _) hcut
  have hk₁ : k₁ ≤ (logN (Nat.floor (a n))).toNat :=
    le_trans (Nat.le_add_right k₁ _) hmain.1
  have hlog : (logN (Nat.floor (a n))).toNat = Nat.log 2 (max (Nat.floor (a n)) 2) := by
    simp [logN]
  have hne : max (Nat.floor (a n)) 2 ≠ 0 := by
    have : 2 ≤ max (Nat.floor (a n)) 2 := le_max_right _ _
    omega
  have hpow : 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) ≤ max (Nat.floor (a n)) 2 :=
    Nat.pow_log_le_self 2 hne
  have hmax : max (Nat.floor (a n)) 2 = Nat.floor (a n) := max_eq_left (le_of_lt hN)
  calc 2 ^ k₁ ≤ 2 ^ (logN (Nat.floor (a n))).toNat :=
        pow_le_pow_right' (a := 2) (by norm_num) hk₁
    _ = 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) := by rw [hlog]
    _ ≤ max (Nat.floor (a n)) 2 := hpow
    _ = Nat.floor (a n) := hmax

/-! ## §2. The `Tex`/`Tle` bridge for all levels -/

/-- The exact-height multiplier is the difference of two height-`≤` multipliers, for bounded input
and *every* level `l` (at `l = 0` both sides vanish). -/
lemma lacBumpBad_tex_eq_tle_sub (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) {φ : ℝ → ℂ}
    (hAdm : Adm (iwArithFreqs ρ l) φ) (hAdm' : Adm (iwArithFreqs ρ (l - 1)) φ)
    {f : ℤ → ℂ} {Bnd : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ Bnd) :
    Tex ρ l φ f = Tle ρ l φ f - Tle ρ (l - 1) φ f := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have h := iwConv_sdiff_of_bounded (A := iwArithFreqs ρ 0) (B := iwArithFreqs ρ 0)
      (Finset.Subset.refl _) hAdm.2.1 hAdm.2.1 hf hAdm.2.2 hAdm.2.2
    have hzero : Tex ρ 0 φ f = 0 := by
      simp only [Tex, iwArithFreqsNew]
      rw [h, sub_self]
    rw [hzero]
    simp
  · exact Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl hAdm hAdm' hf

/-! ## §3. The physical scale of a bad index is bounded -/

/-- If `n` is a bad scale and the loss scale is bounded by `B`, then
`a n < 2^{B + Cρc 2^{ρB} + 2} + 1`. -/
lemma lacBumpBad_scale_bound (ρ : ℝ) (hρ : 0 < ρ) (Cρc : ℝ) (hCρc : 3 ≤ Cρc)
    (B : ℕ) {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ}
    (hL : Lnat l₁ l₂ k₁ k₂ ≤ B)
    (hb : Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n) :
    (a n : ℝ) < (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) + 1 := by
  obtain ⟨-, hnf⟩ := hb
  have hk₁B : k₁ ≤ B := le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) hL
  have hl₁B : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hL
  have hnotF : ¬ ((k₁ : ℤ) - logN (Nat.floor (a n)) ≤ fareyK Cρc ρ l₁) := by
    simpa only [Farey] using hnf
  have hlt : fareyK Cρc ρ l₁ < (k₁ : ℤ) - logN (Nat.floor (a n)) := not_le.mp hnotF
  have hltR : ((fareyK Cρc ρ l₁ : ℤ) : ℝ) < (k₁ : ℝ) - (logN (Nat.floor (a n)) : ℝ) := by
    exact_mod_cast hlt
  have hfk : -(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) - 1 < ((fareyK Cρc ρ l₁ : ℤ) : ℝ) := by
    have h := Int.sub_one_lt_floor (-(Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))
    simpa only [fareyK] using h
  have hlog_lt : (logN (Nat.floor (a n)) : ℝ)
      < (k₁ : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 1 := by linarith
  have hCρc0 : 0 ≤ Cρc := by linarith
  have h2mono : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by have h : (l₁ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hl₁B
          nlinarith [hρ.le])
  have hlog_lt' : (logN (Nat.floor (a n)) : ℝ)
      < (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 1 := by
    have h1 : (k₁ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hk₁B
    have h2 := mul_le_mul_of_nonneg_left h2mono hCρc0
    linarith
  have hM : ((Nat.log 2 (max (Nat.floor (a n)) 2) : ℕ) : ℝ)
      = (logN (Nat.floor (a n)) : ℝ) := by
    simp [logN]
  have hM_lt : ((Nat.log 2 (max (Nat.floor (a n)) 2) : ℕ) : ℝ)
      < (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 1 := by
    rw [hM]; exact hlog_lt'
  have hexp : (((Nat.log 2 (max (Nat.floor (a n)) 2)).succ : ℕ) : ℝ)
      ≤ (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2 := by
    have h1 := hM_lt
    rw [Nat.cast_succ]
    linarith
  have hNnat : Nat.floor (a n) < 2 ^ (Nat.log 2 (max (Nat.floor (a n)) 2)).succ :=
    lt_of_le_of_lt (le_max_left _ _)
      (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max (Nat.floor (a n)) 2))
  have hNreal : ((Nat.floor (a n) : ℕ) : ℝ)
      < (2 : ℝ) ^ ((Nat.log 2 (max (Nat.floor (a n)) 2)).succ) := by
    have h := (Nat.cast_lt (α := ℝ)).mpr hNnat
    simpa [Nat.cast_pow] using h
  have hpow_le : (2 : ℝ) ^ ((Nat.log 2 (max (Nat.floor (a n)) 2)).succ)
      ≤ (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) ((Nat.log 2 (max (Nat.floor (a n)) 2)).succ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hltX : ((Nat.floor (a n) : ℕ) : ℝ)
      < (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) :=
    lt_of_lt_of_le hNreal hpow_le
  have ha_lt : (a n : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (a n)
  linarith

/-! ## §4. The bad family -/

/-- The bad part of the linear family: the exact-height projection of `f` against the modulated
bump `φ_{⌊a n⌋,t}`, kept only on the scales which are *core* but not *Farey*. -/
noncomputable def lacBumpBadFamily (ρ Cρc : ℝ) (C₀ l₁ l₂ k₁ k₂ : ℕ) (a : ℕ → NNReal)
    (t : ℝ) (f : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x => if Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n then
    Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0

/-! ## §5. The bad part estimate -/

theorem lacunaryBumpBadPartBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (f : ℤ → ℂ) (Bf : ℝ) (hBf : ∀ m : ℤ, ‖f m‖ ≤ Bf),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
            ¬ Work.KMTAreas.A7.Farey Cρc ρ l₁ k₁ a n
          then Work.KMTAreas.A7.Tex ρ l₁
            (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  -- the loss scale is bounded on the bad scales
  obtain ⟨B, hB⟩ := exists_Lnat_le_of_bad ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ
  -- the single-scale constants, made uniform over the finitely many levels `l ≤ B`
  have hchoose : ∀ l : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (N k₁ : ℕ), 2 ^ k₁ ≤ N → ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ f : ℤ → ℂ,
        eLpNorm (Tle ρ l (varphiNt N k₁ t) f) p Measure.count
          ≤ ENNReal.ofReal C * eLpNorm f p Measure.count := by
    intro l
    obtain ⟨C, hCpos, hC⟩ := Tle_varphiNt_single_scale ρ hρ l p hp hptop
    exact ⟨(C : ℝ), by exact_mod_cast hCpos, fun N k₁ hNk t ht f => hC N k₁ hNk t ht f⟩
  choose Cfun hCfun_pos hCfun_spec using hchoose
  set Cmax : ℝ := ∑ l ∈ Finset.range (B + 1), Cfun l with hCmax
  have hCfun_le : ∀ l, l ≤ B → Cfun l ≤ Cmax := by
    intro l hl
    rw [hCmax]
    exact Finset.single_le_sum (fun i _ => (hCfun_pos i).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  have hCmax_pos : 0 < Cmax := lt_of_lt_of_le (hCfun_pos 0) (hCfun_le 0 (Nat.zero_le B))
  -- the two constants attached to the bad scales
  set X : ℝ := (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) + 1 with hX
  have hX1 : 1 ≤ X := by
    rw [hX]
    have hpos : 0 < (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith
  set N₀ : ℕ := Nat.ceil (Real.log X / Real.log (Λ : ℝ) + 2) with hN₀
  refine ⟨max 1 ((N₀ : ℝ) * 4 * (2 * Cmax)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ t ht f Bf hBf
  set E : ENNReal := eLpNorm f p Measure.count with hE
  change eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n x)) p Measure.count
    ≤ ENNReal.ofReal (max 1 ((N₀ : ℝ) * 4 * (2 * Cmax))) * E
  -- all bad indices are bounded
  have hbound : ∀ n, Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n → n < N₀ := by
    by_cases hne : ∃ n, Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n
    · have hL : Lnat l₁ l₂ k₁ k₂ ≤ B := hB a ha ha1 l₁ l₂ k₁ k₂ hne
      obtain ⟨K, hKbd, hKn⟩ := lacunary_index_bound Λ hΛ a ha ha1 X hX1
      have hKN₀ : K ≤ N₀ := by
        have h1 : (K : ℝ) ≤ Real.log X / Real.log (Λ : ℝ) + 2 := hKbd
        have h2 : Real.log X / Real.log (Λ : ℝ) + 2 ≤ (N₀ : ℝ) := by
          rw [hN₀]; exact Nat.le_ceil _
        exact_mod_cast (le_trans h1 h2)
      intro n hn
      have hs : (a n : ℝ) < X := by
        rw [hX]
        exact lacBumpBad_scale_bound ρ hρ Cρc hCρc B hL hn
      exact lt_of_lt_of_le (hKn n hs) hKN₀
    · intro n hn
      exact absurd ⟨n, hn⟩ hne
  -- the family vanishes off `range N₀`
  have hu : ∀ n, n ∉ Finset.range N₀ →
      lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n = 0 := by
    intro n hn
    have hn' : ¬ n < N₀ := by simpa using hn
    have hnb : ¬ Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n := fun hb => hn' (hbound n hb)
    funext x
    simp only [lacBumpBadFamily]
    rw [if_neg hnb]
    simp
  -- the single-scale bound for each member of the bad family
  have hstep : ∀ n, eLpNorm (lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n) p Measure.count
      ≤ ENNReal.ofReal (2 * Cmax) * E := by
    intro n
    by_cases hbn : Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n
    · have hne : ∃ n, Bads ρ C₀ Cρc l₁ l₂ k₁ k₂ a n := ⟨n, hbn⟩
      have hL : Lnat l₁ l₂ k₁ k₂ ≤ B := hB a ha ha1 l₁ l₂ k₁ k₂ hne
      have hl₁B : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hL
      have hNk : 2 ^ k₁ ≤ Nat.floor (a n) := lacBumpBad_two_pow_le_floor_of_core hbn.1
      have hAdm : Adm (iwArithFreqs ρ l₁) (varphiNt (Nat.floor (a n)) k₁ t) :=
        adm_of_bump (contDiff_varphiNt _ _ _) (hasCompactSupport_varphiNt _ _ _)
      have hAdm' : Adm (iwArithFreqs ρ (l₁ - 1)) (varphiNt (Nat.floor (a n)) k₁ t) :=
        adm_of_bump (contDiff_varphiNt _ _ _) (hasCompactSupport_varphiNt _ _ _)
      have hTex := lacBumpBad_tex_eq_tle_sub ρ hρ hρ1 l₁ hAdm hAdm' hBf
      have hu' : lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n
          = Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f := by
        funext x
        simp only [lacBumpBadFamily]
        rw [if_pos hbn]
      rw [hu', hTex]
      calc eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f
              - Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f) p Measure.count
          ≤ eLpNorm (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) p Measure.count
            + eLpNorm (Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f)
                p Measure.count :=
            eLpNorm_sub_le (le_of_lt hp)
        _ ≤ ENNReal.ofReal (Cfun l₁) * E + ENNReal.ofReal (Cfun (l₁ - 1)) * E := by
            refine add_le_add ?_ ?_
            · simpa only [hE] using hCfun_spec l₁ (Nat.floor (a n)) k₁ hNk t ht f
            · simpa only [hE] using hCfun_spec (l₁ - 1) (Nat.floor (a n)) k₁ hNk t ht f
        _ ≤ ENNReal.ofReal (2 * Cmax) * E := by
            rw [← add_mul, ← ENNReal.ofReal_add (hCfun_pos l₁).le (hCfun_pos (l₁ - 1)).le]
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have h2 : Cfun (l₁ - 1) ≤ Cmax := hCfun_le (l₁ - 1) (le_trans (Nat.sub_le l₁ 1) hl₁B)
            have h1 : Cfun l₁ ≤ Cmax := hCfun_le l₁ hl₁B
            linarith
    · have hu' : lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n = 0 := by
        funext x
        simp only [lacBumpBadFamily]
        rw [if_neg hbn]
        simp
      rw [hu']
      simp
  -- the finite-support bound `(varsum)` and the summation of the constants
  have hmeas : ∀ n ∈ Finset.range N₀,
      AEStronglyMeasurable (lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n) Measure.count :=
    fun n _ => (measurable_of_countable _).aestronglyMeasurable
  have hsum := Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_sum
    (μ := Measure.count) (r := r) (le_trans (by norm_num : (1 : NNReal) ≤ 2) hr.le)
    (p := p) (le_of_lt hp) (u := lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f)
    (s := Finset.range N₀) hu hmeas
  refine hsum.trans ?_
  calc ∑ n ∈ Finset.range N₀,
          4 * eLpNorm (fun x => lacBumpBadFamily ρ Cρc C₀ l₁ l₂ k₁ k₂ a t f n x)
                p Measure.count
      ≤ ∑ n ∈ Finset.range N₀, 4 * (ENNReal.ofReal (2 * Cmax) * E) :=
        Finset.sum_le_sum (fun n _ => mul_le_mul' le_rfl (hstep n))
    _ = (N₀ : ENNReal) * (4 * (ENNReal.ofReal (2 * Cmax) * E)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((N₀ : ENNReal) * 4 * ENNReal.ofReal (2 * Cmax)) * E := by
        rw [← mul_assoc, ← mul_assoc]
    _ ≤ ENNReal.ofReal (max 1 ((N₀ : ℝ) * 4 * (2 * Cmax))) * E := by
        refine mul_le_mul' ?_ le_rfl
        rw [show (N₀ : ENNReal) = ENNReal.ofReal (N₀ : ℝ) from
              (ENNReal.ofReal_natCast N₀).symm,
            show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) from by simp,
            ← ENNReal.ofReal_mul (p := (N₀ : ℝ)) (q := 4) (by positivity),
            ← ENNReal.ofReal_mul (p := (N₀ : ℝ) * 4) (q := 2 * Cmax) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

end

end Work.KMTAreas.A7

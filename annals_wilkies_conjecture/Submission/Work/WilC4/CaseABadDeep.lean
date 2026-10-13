import Mathlib
import Submission.Work.WilC4.CbzAux
import Submission.Work.WilC4.CbzFlatDeep
import Submission.Work.WilC4.mid_band_unique
import Submission.Work.WilC4.mb_exists_mid_between
import Submission.Work.WilC4.cbz_not_between_trans
import Submission.Work.WilC4.cbz_no_between_limit

set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
open Classical Set
namespace Work.WilC4

open Work.WilC4.Route

variable {k : ℕ}

theorem caseA_bad_bounded_zero_deep {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    {B : Set (Fin (k + 1) → ℝ)} {E : Set ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hgf : Work.WilC4.GoodFibre Y B) (hE : E.Finite) (hne : ∃ ρ ∈ E, 0 < ρ)
    (hsubE : Work.WilC4.Route.ClusterE Y B ⊆ E)
    (hzero : (0 : ℝ) ∉ Work.WilC4.Route.ClusterE Y B)
    {Γ Cbdd : ℝ} (hΓ2 : 2 ≤ Γ)
    (hbdd : ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      Work.WilC4.IsDeepR B c Γ x → Work.WilC4.RatW Y c x w → |w| ≤ Cbdd)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ (M : ℝ) (c : Fin k → ℝ) (x w : ℝ), R ≤ M → 0 < x →
      Work.WilC4.IsDeepR B c M x → Work.WilC4.RatW Y c x w →
      (∀ z ∈ Set.Ioo (x / (2 * M)) (2 * M * x), ∀ u : ℝ,
        Work.WilC4.RatW Y c z u → u ∉ Work.WilC4.Mid E) →
      (MonotoneOn (fun s : ℝ => Work.WilC4.Route.ratioY Y c (x * s))
          (Set.Ioo (1 / M) M) ∨
        AntitoneOn (fun s : ℝ => Work.WilC4.Route.ratioY Y c (x * s))
          (Set.Ioo (1 / M) M)) →
      ¬ (∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1|) := by
  classical
  by_contra hcon
  -- Contrapositive: bad witnesses with the above data exist below every bound.
  have key : ∀ R : ℝ, ∃ (M : ℝ) (c : Fin k → ℝ) (x w : ℝ),
      R ≤ M ∧ 0 < x ∧ IsDeepR B c M x ∧ RatW Y c x w ∧ CbzAvoid Y E M c x ∧
      CbzMono Y M c x ∧ (∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1|) := by
    intro R
    by_contra h
    apply hcon
    refine ⟨R, ?_⟩
    intro M c x w hRM hx hdeep hrat havoid hmono
    intro hbad
    exact h ⟨M, c, x, w, hRM, hx, hdeep, hrat, havoid, hmono, hbad⟩
  -- The bound `Cbdd` is positive, and there is a positive natural `A` above it.
  obtain ⟨M0, c0, x0, w0, hM0, hx0, hdeep0, hrat0, -, -, hbad0⟩ := key Γ
  have hCbdd_pos : 0 < Cbdd := by
    have hdΓ : IsDeepR B c0 Γ x0 := hdeep0.mono (by linarith : (0 : ℝ) < Γ) hM0 hx0
    have hwp : 0 < w0 := cbz_ratW_pos hfun hgf hΓ2 hx0 hdΓ hrat0
    have hb := hbdd c0 x0 w0 hx0 hdΓ hrat0
    rw [abs_of_pos hwp] at hb
    linarith
  obtain ⟨A, hA1, hAC⟩ : ∃ A : ℕ, 1 ≤ A ∧ Cbdd ≤ (A : ℝ) := by
    obtain ⟨A, hA⟩ := exists_nat_ge (max Cbdd 1)
    exact ⟨A, by exact_mod_cast (le_trans (le_max_right Cbdd 1) hA),
      by linarith [le_max_left Cbdd 1]⟩
  -- A natural number above the scale `Γ`, used to keep the resolutions `Nn n` above `Γ`.
  let K : ℕ := Nat.ceil Γ
  have hKΓ : Γ ≤ (K : ℝ) := Nat.le_ceil Γ
  -- The scale of the `k`-th witness, chosen large enough for resolution `k + 2 + K`.
  let mf : ℕ → ℕ := fun k => 2 * (k + 2 + K) * A + 1
  let Rf : ℕ → ℝ := fun k => ((k + 2 + K : ℕ) : ℝ) ^ (2 * mf k + 1)
  have hmf_pos : ∀ k, 0 < mf k := fun k => by simp only [mf]; omega
  have hmf_ge : ∀ k, 2 * (k + 2 + K) * Cbdd ≤ (mf k : ℝ) := by
    intro k
    have h2 : (2 : ℝ) * (k + 2 + K) * Cbdd ≤ (2 : ℝ) * (k + 2 + K) * A := by nlinarith [hAC]
    simp only [mf] at h2 ⊢
    push_cast
    linarith
  have hRf2 : ∀ k, 2 ≤ Rf k := by
    intro k
    have hk2 : (2 : ℝ) ≤ ((k + 2 + K : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 2 + K by omega)
    show 2 ≤ ((k + 2 + K : ℕ) : ℝ) ^ (2 * mf k + 1)
    calc (2 : ℝ) ≤ ((k + 2 + K : ℕ) : ℝ) := hk2
      _ = ((k + 2 + K : ℕ) : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ((k + 2 + K : ℕ) : ℝ) ^ (2 * mf k + 1) := by
          apply pow_le_pow_right₀ (le_trans (by norm_num) hk2); omega
  have hkey' : ∀ n : ℕ, ∃ (M : ℝ) (c : Fin k → ℝ) (x w : ℝ),
      Rf n ≤ M ∧ 0 < x ∧ IsDeepR B c M x ∧ RatW Y c x w ∧ CbzAvoid Y E M c x ∧
      CbzMono Y M c x ∧ (∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1|) := fun n => key (Rf n)
  choose fM fc fx fw hfw using hkey'
  have hMR : ∀ k, Rf k ≤ fM k := fun k => (hfw k).1
  have hxpos : ∀ k, 0 < fx k := fun k => (hfw k).2.1
  have hdeepk : ∀ k, IsDeepR B (fc k) (fM k) (fx k) := fun k => (hfw k).2.2.1
  have hratk : ∀ k, RatW Y (fc k) (fx k) (fw k) := fun k => (hfw k).2.2.2.1
  have havoidk : ∀ k, CbzAvoid Y E (fM k) (fc k) (fx k) := fun k => (hfw k).2.2.2.2.1
  have hmonok : ∀ k, CbzMono Y (fM k) (fc k) (fx k) := fun k => (hfw k).2.2.2.2.2.1
  have hbadk : ∀ k, ∀ ρ ∈ E, 0 < ρ → ε < |fw k / ρ - 1| := fun k => (hfw k).2.2.2.2.2.2
  have hM2 : ∀ k, 2 ≤ fM k := fun k => le_trans (hRf2 k) (hMR k)
  -- Basic facts at every bad witness.
  have hwpos : ∀ k, 0 < fw k := fun k => cbz_ratW_pos hfun hgf (hM2 k) (hxpos k) (hdeepk k) (hratk k)
  have hweq : ∀ k, fw k = ratioY Y (fc k) (fx k) := fun k => cbz_ratW_eq_ratioY hfun (hratk k)
  have hwmid : ∀ k, fw k ∉ Mid E := by
    intro k
    have hfMpos : 0 < fM k := by linarith [hM2 k]
    have hxw : fx k ∈ Set.Ioo (fx k / (2 * fM k)) (2 * fM k * fx k) := by
      refine ⟨?_, by nlinarith [hxpos k, hM2 k]⟩
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * fM k)]
      nlinarith [hxpos k, hM2 k]
    exact havoidk k (fx k) hxw (fw k) (hratk k)
  -- The band label of every bad value.
  have hband_ex : ∀ k, ∃ ρ, ρ ∈ E ∧ 0 < ρ ∧
      ∀ m ∈ Mid E, ¬ (min (fw k) ρ < m ∧ m < max (fw k) ρ) :=
    fun k => (mid_band_unique hE hne (hwpos k) (hwmid k)).exists
  choose rho hrhospec using hband_ex
  have hrhoE : ∀ k, rho k ∈ E := fun k => (hrhospec k).1
  have hrho0 : ∀ k, 0 < rho k := fun k => (hrhospec k).2.1
  have hrhoband : ∀ k, ∀ m ∈ Mid E, ¬ (min (fw k) (rho k) < m ∧ m < max (fw k) (rho k)) :=
    fun k => (hrhospec k).2.2
  have hbadk' : ∀ k, ε < |fw k / rho k - 1| := fun k => hbadk k (rho k) (hrhoE k) (hrho0 k)
  have hdich : ∀ k, rho k * (1 + ε) < fw k ∨ fw k < rho k * (1 - ε) := by
    intro k
    have h := hbadk' k
    have hr := hrho0 k
    have h1 : fw k / rho k - 1 > ε ∨ fw k / rho k - 1 < -ε := by
      rcases lt_trichotomy (fw k / rho k - 1) 0 with hlt | heq | hgt
      · rw [abs_of_neg hlt] at h; right; linarith
      · rw [heq, abs_zero] at h; linarith
      · rw [abs_of_pos hgt] at h; left; linarith
    rcases h1 with h | h
    · left
      have h2 : ε + 1 < fw k / rho k := by linarith
      rw [lt_div_iff₀ hr] at h2
      linarith
    · right
      have h2 : fw k / rho k < 1 - ε := by linarith
      rw [div_lt_iff₀ hr] at h2
      linarith
  -- Extract the subsequence on which the band label, monotonicity type and deviation
  -- type are all constant.
  haveI : Fintype {ρ : ℝ // ρ ∈ E} := hE.fintype
  let monoB : ℕ → Bool := fun k => decide (MonotoneOn (fun s : ℝ => ratioY Y (fc k) (fx k * s))
    (Set.Ioo (1 / fM k) (fM k)))
  let signB : ℕ → Bool := fun k => decide (rho k * (1 + ε) < fw k)
  let tp : ℕ → ({ρ : ℝ // ρ ∈ E} × Bool × Bool) := fun k => (⟨rho k, hrhoE k⟩, monoB k, signB k)
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber tp
  have hainf : (tp ⁻¹' {a}).Infinite := Set.infinite_coe_iff.mp ha
  have hP : ∀ N : ℕ, ∃ n > N, tp n = a := by
    intro N
    obtain ⟨n, hn, hNn⟩ := hainf.exists_gt N
    exact ⟨n, hNn, by simpa using hn⟩
  obtain ⟨φ, hφmono, hφP⟩ := Nat.exists_strictMono_subsequence hP
  have hφid : ∀ n, φ n ≥ n := fun n => hφmono.id_le n
  have hrho_const : ∀ n, rho (φ n) = a.1.1 := by
    intro n
    have h := congrArg (fun t : ({ρ : ℝ // ρ ∈ E} × Bool × Bool) => (t.1 : {ρ : ℝ // ρ ∈ E})) (hφP n)
    have h2 : (⟨rho (φ n), hrhoE (φ n)⟩ : {ρ : ℝ // ρ ∈ E}) = a.1 := by simpa [tp] using h
    exact congrArg Subtype.val h2
  have hmonoB_const : ∀ n, monoB (φ n) = a.2.1 := by
    intro n
    have h := congrArg (fun t : ({ρ : ℝ // ρ ∈ E} × Bool × Bool) => t.2.1) (hφP n)
    simpa [tp] using h
  have hsignB_const : ∀ n, signB (φ n) = a.2.2 := by
    intro n
    have h := congrArg (fun t : ({ρ : ℝ // ρ ∈ E} × Bool × Bool) => t.2.2) (hφP n)
    simpa [tp] using h
  -- Abbreviations for the reindexed sequence.
  let Nn : ℕ → ℕ := fun n => n + 2 + K
  let Wn : ℕ → ℝ := fun n => fM (φ n) / (Nn n)
  let g2 : ℕ → ℝ → ℝ := fun n s => ratioY Y (fc (φ n)) (fx (φ n) * s)
  have hNn_pos : ∀ n, 0 < Nn n := fun n => by simp only [Nn]; omega
  have hNn2 : ∀ n, 2 ≤ Nn n := fun n => by simp only [Nn]; omega
  have hNnR : ∀ n, (2 : ℝ) ≤ (Nn n : ℝ) := fun n => by exact_mod_cast hNn2 n
  have hNΓ : ∀ n, Γ ≤ (Nn n : ℝ) := by
    intro n
    have h1 : (K : ℝ) ≤ (Nn n : ℝ) := by
      simp only [Nn]; push_cast; exact_mod_cast (show K ≤ n + 2 + K by omega)
    linarith [hKΓ]
  have hWn_ge : ∀ n, (Nn n : ℝ) ^ (2 * mf (φ n)) ≤ Wn n := by
    intro n
    have hφn : Nn n ≤ φ n + 2 + K := by have := hφid n; simp only [Nn]; omega
    have hbase : (Nn n : ℝ) ≤ ((φ n + 2 + K : ℕ) : ℝ) := by exact_mod_cast hφn
    have hbase1 : (1 : ℝ) ≤ (Nn n : ℝ) := by
      have : 1 ≤ Nn n := by simp only [Nn]; omega
      exact_mod_cast this
    have hNpos : (0 : ℝ) < (Nn n : ℝ) := by positivity
    have hpow : (Nn n : ℝ) ^ (2 * mf (φ n)) ≤ ((φ n + 2 + K : ℕ) : ℝ) ^ (2 * mf (φ n)) :=
      pow_le_pow_left₀ (le_trans zero_le_one hbase1) hbase _
    have hkey1 : (Nn n : ℝ) ^ (2 * mf (φ n) + 1) ≤ fM (φ n) := by
      calc (Nn n : ℝ) ^ (2 * mf (φ n) + 1)
          = (Nn n : ℝ) ^ (2 * mf (φ n)) * (Nn n : ℝ) := by rw [pow_succ]
        _ ≤ ((φ n + 2 + K : ℕ) : ℝ) ^ (2 * mf (φ n)) * ((φ n + 2 + K : ℕ) : ℝ) :=
            mul_le_mul hpow hbase (le_of_lt hNpos) (by positivity)
        _ = ((φ n + 2 + K : ℕ) : ℝ) ^ (2 * mf (φ n) + 1) := by rw [pow_succ]
        _ ≤ fM (φ n) := hMR (φ n)
    show (Nn n : ℝ) ^ (2 * mf (φ n)) ≤ fM (φ n) / (Nn n : ℝ)
    rw [le_div_iff₀ hNpos]
    rw [pow_succ] at hkey1
    exact hkey1
  have hWn_pos : ∀ n, 0 < Wn n := by
    intro n
    have h1 : (0 : ℝ) < fM (φ n) := by linarith [hM2 (φ n)]
    have h2 : (0 : ℝ) < (Nn n : ℝ) := by exact_mod_cast hNn_pos n
    show (0 : ℝ) < fM (φ n) / (Nn n : ℝ)
    positivity
  have hWn_gt1 : ∀ n, 1 < Wn n := by
    intro n
    have h1 := hWn_ge n
    have h2 : (1 : ℝ) < (Nn n : ℝ) ^ (2 * mf (φ n)) := by
      have h1' : (2 : ℝ) ≤ (Nn n : ℝ) := hNnR n
      have h2' : (1 : ℕ) ≤ 2 * mf (φ n) := by have := hmf_pos (φ n); omega
      calc (1 : ℝ) < 2 := by norm_num
        _ = (2 : ℝ) ^ (1 : ℕ) := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (2 * mf (φ n)) := pow_le_pow_right₀ (by norm_num) h2'
        _ ≤ (Nn n : ℝ) ^ (2 * mf (φ n)) := pow_le_pow_left₀ (by norm_num) h1' _
    linarith
  have hwidthW : ∀ n, (Nn n : ℝ) ^ 2 ≤ (Wn n) ^ ((1 : ℝ) / (mf (φ n) : ℝ)) :=
    fun n => cbz_rpow_inv (hNn_pos n) (hmf_pos (φ n)) (hWn_ge n)
  -- The `m`-bound for `cbz_flat_deep` and the flat-piece construction.
  have hCm : ∀ n, 2 * (Nn n : ℝ) * Cbdd ≤ (mf (φ n) : ℝ) := by
    intro n
    have hge := hmf_ge (φ n)
    have hNle : (Nn n : ℝ) ≤ (φ n : ℝ) + 2 + K := by
      exact_mod_cast (show Nn n ≤ φ n + 2 + K by have := hφid n; simp only [Nn]; omega)
    nlinarith [hge, hNle]
  have build : ∀ n, ∃ (y lam : ℝ), ((Nn n : ℝ) / fM (φ n) ≤ y ∧ y ≤ fM (φ n) / (Nn n : ℝ)) ∧
      lam = g2 n y ∧ (0 < lam ∧ lam ≤ Cbdd) ∧
      ((signB (φ n) = true ∧ fw (φ n) ≤ lam) ∨ (signB (φ n) = false ∧ lam ≤ fw (φ n))) ∧
      (∀ s : ℝ, y / (Nn n : ℝ) ≤ s → s ≤ (Nn n : ℝ) * y →
        |g2 n s - lam| ≤ 1 / (2 * (Nn n : ℝ))) ∧
      (∀ m' ∈ Mid E, ¬ (min (fw (φ n)) lam < m' ∧ m' < max (fw (φ n)) lam)) := by
    intro n
    exact cbz_flat_deep (k := k) hfun hgf hΓ2 hCbdd_pos hbdd (hNΓ n) (hNn2 n) (hmf_pos (φ n))
      (hxpos (φ n)) (hM2 (φ n)) (hCm n) (hWn_ge n) (hdeepk (φ n)) (havoidk (φ n)) (hmonok (φ n))
      (hweq (φ n)) (monoB (φ n)) (signB (φ n)) rfl
  have hsign_fact : ∀ n, (a.2.2 = true → a.1.1 * (1 + ε) < fw (φ n)) ∧
      (a.2.2 = false → fw (φ n) < a.1.1 * (1 - ε)) := by
    intro n
    constructor
    · intro h
      have h2 : signB (φ n) = true := by rw [hsignB_const n, h]
      have h3 : decide (rho (φ n) * (1 + ε) < fw (φ n)) = true := h2
      rw [hrho_const n] at h3
      exact of_decide_eq_true h3
    · intro h
      have h2 : signB (φ n) = false := by rw [hsignB_const n, h]
      have h3 : decide (rho (φ n) * (1 + ε) < fw (φ n)) = false := h2
      rw [hrho_const n] at h3
      rw [decide_eq_false_iff_not] at h3
      have hd := hdich (φ n)
      rw [hrho_const n] at hd
      rcases hd with hlt | hlt
      · exact absurd hlt h3
      · exact hlt
  choose yy llam hbuild using build
  have hyy1 : ∀ n, (Nn n : ℝ) / fM (φ n) ≤ yy n := fun n => (hbuild n).1.1
  have hyy2 : ∀ n, yy n ≤ fM (φ n) / (Nn n : ℝ) := fun n => (hbuild n).1.2
  have hyypos : ∀ n, 0 < yy n := fun n =>
    lt_of_lt_of_le (div_pos (by exact_mod_cast hNn_pos n) (by linarith [hM2 (φ n)])) (hyy1 n)
  have hlam_eq : ∀ n, llam n = g2 n (yy n) := fun n => (hbuild n).2.1
  have hlam_mem : ∀ n, 0 < llam n ∧ llam n ≤ Cbdd := fun n => (hbuild n).2.2.1
  have hlam_ineq : ∀ n, (signB (φ n) = true ∧ fw (φ n) ≤ llam n) ∨
      (signB (φ n) = false ∧ llam n ≤ fw (φ n)) := fun n => (hbuild n).2.2.2.1
  have hlam_flat : ∀ n, ∀ s : ℝ, yy n / (Nn n : ℝ) ≤ s → s ≤ (Nn n : ℝ) * yy n →
      |g2 n s - llam n| ≤ 1 / (2 * (Nn n : ℝ)) := fun n => (hbuild n).2.2.2.2.1
  have hnoMidn : ∀ n, ∀ m' ∈ Mid E,
      ¬ (min (fw (φ n)) (llam n) < m' ∧ m' < max (fw (φ n)) (llam n)) :=
    fun n => (hbuild n).2.2.2.2.2
  have hlam_ineq' : ∀ n, (a.2.2 = true ∧ fw (φ n) ≤ llam n) ∨
      (a.2.2 = false ∧ llam n ≤ fw (φ n)) := by
    intro n
    rcases hlam_ineq n with ⟨h, hle⟩ | ⟨h, hle⟩
    · exact Or.inl ⟨by rw [← hsignB_const n]; exact h, hle⟩
    · exact Or.inr ⟨by rw [← hsignB_const n]; exact h, hle⟩
  have htdeep : ∀ n, IsDeepR B (fc (φ n)) (Nn n) (fx (φ n) * yy n) := by
    intro n
    have hfxn := hxpos (φ n)
    have hMnpos : 0 < fM (φ n) := by linarith [hM2 (φ n)]
    have hNpos : (0 : ℝ) < (Nn n : ℝ) := by exact_mod_cast hNn_pos n
    have hlo : fx (φ n) / (2 * fM (φ n)) ≤ (fx (φ n) * yy n) / (2 * (Nn n : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * fM (φ n))
        (by positivity : (0 : ℝ) < 2 * (Nn n : ℝ))]
      have h : (Nn n : ℝ) ≤ yy n * fM (φ n) := by
        have hh : (Nn n : ℝ) / fM (φ n) ≤ yy n := hyy1 n
        rwa [div_le_iff₀ hMnpos] at hh
      nlinarith [h, hfxn, hMnpos, hNpos]
    have hhi : 2 * (Nn n : ℝ) * (fx (φ n) * yy n) ≤ 2 * fM (φ n) * fx (φ n) := by
      have h : yy n * (Nn n : ℝ) ≤ fM (φ n) := by
        have h2 := hyy2 n
        rwa [le_div_iff₀ hNpos] at h2
      nlinarith [h, hfxn, hMnpos, hNpos]
    intro b hb hb'
    exact hdeepk (φ n) b hb ⟨le_trans hlo hb'.1, le_trans hb'.2 hhi⟩
  have hllam_mem : ∀ n, llam n ∈ Set.Icc (0 : ℝ) Cbdd := fun n =>
    ⟨le_of_lt (hlam_mem n).1, (hlam_mem n).2⟩
  obtain ⟨lam0, hlam0mem, ψ, hψmono, hψtend⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun n => llam n) (fun n => hllam_mem n)
  have hlam0nn : 0 ≤ lam0 := hlam0mem.1
  have hψid : ∀ n, ψ n ≥ n := fun n => hψmono.id_le n
  have hclu : lam0 ∈ ClusterE Y B := by
    intro Bs hBs
    have hBpos : (0 : ℝ) < (Bs : ℝ) := by exact_mod_cast hBs
    have hev : ∀ᶠ n in Filter.atTop, |llam (ψ n) - lam0| < 1 / (2 * (Bs : ℝ)) := by
      have hb : (0 : ℝ) < 1 / (2 * (Bs : ℝ)) := by positivity
      filter_upwards [hψtend.eventually (Metric.ball_mem_nhds lam0 hb)] with n hn
      simpa [Real.dist_eq] using hn
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
    have hNnpsi : (Bs : ℝ) ≤ (Nn (ψ (max N₁ Bs)) : ℝ) := by
      have h1 : Bs ≤ ψ (max N₁ Bs) := le_trans (le_max_right N₁ Bs) (hψid _)
      have h2 : Bs ≤ Nn (ψ (max N₁ Bs)) := by simp only [Nn]; omega
      exact_mod_cast h2
    have hNp : (0 : ℝ) < (Nn (ψ (max N₁ Bs)) : ℝ) := by exact_mod_cast hNn_pos _
    refine ⟨fc (φ (ψ (max N₁ Bs))), fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs)),
      mul_pos (hxpos _) (hyypos _), ?_, ?_⟩
    · exact (htdeep (ψ (max N₁ Bs))).mono hBpos (hNnpsi)
        (mul_pos (hxpos _) (hyypos _))
    · intro t ht1 ht2 y y' hy hy' hy0
      have hfxn := hxpos (φ (ψ (max N₁ Bs)))
      have hxpos' : 0 < fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs)) := mul_pos hfxn (hyypos _)
      have hyy : y = valY Y (fc (φ (ψ (max N₁ Bs)))) t := eq_valY hfun hy
      have hyy' : y' = valY Y (fc (φ (ψ (max N₁ Bs)))) (2 * t) := eq_valY hfun hy'
      have hratio : y' / y = ratioY Y (fc (φ (ψ (max N₁ Bs)))) t := by
        rw [hyy, hyy', ratioY]
      set s : ℝ := t / (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs))
        with hsdef
      have hrat_eq : ratioY Y (fc (φ (ψ (max N₁ Bs)))) t = g2 (ψ (max N₁ Bs)) s := by
        have ht_eq : fx (φ (ψ (max N₁ Bs))) * s = t := by
          rw [hsdef]
          have h1 : fx (φ (ψ (max N₁ Bs))) ≠ 0 := ne_of_gt hfxn
          have h2 : yy (ψ (max N₁ Bs)) ≠ 0 := ne_of_gt (hyypos _)
          field_simp
        rw [← ht_eq]
      have hs1 : yy (ψ (max N₁ Bs)) / (Nn (ψ (max N₁ Bs)) : ℝ) ≤ s := by
        have h1 : (1 : ℝ) / (Nn (ψ (max N₁ Bs)) : ℝ)
            ≤ t / (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs))) := by
          have h2 : (1 : ℝ) / (Bs : ℝ)
              ≤ t / (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs))) := by
            rw [le_div_iff₀ hxpos']
            rw [show (1 : ℝ) / (Bs : ℝ) * (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs)))
                  = (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs))) / (Bs : ℝ) by ring]
            exact ht1
          have h3 : (1 : ℝ) / (Nn (ψ (max N₁ Bs)) : ℝ) ≤ 1 / (Bs : ℝ) :=
            one_div_le_one_div_of_le hBpos (hNnpsi)
          linarith
        calc yy (ψ (max N₁ Bs)) / (Nn (ψ (max N₁ Bs)) : ℝ)
            = yy (ψ (max N₁ Bs)) * (1 / (Nn (ψ (max N₁ Bs)) : ℝ)) := by rw [mul_one_div]
          _ ≤ yy (ψ (max N₁ Bs))
                * (t / (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs)))) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt (hyypos _))
          _ = t / (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs)) := by ring
      have hs2 : s ≤ (Nn (ψ (max N₁ Bs)) : ℝ) * yy (ψ (max N₁ Bs)) := by
        have h4 : t / (fx (φ (ψ (max N₁ Bs))) * yy (ψ (max N₁ Bs)))
            ≤ (Nn (ψ (max N₁ Bs)) : ℝ) := by
          rw [div_le_iff₀ hxpos']
          nlinarith [ht2, hNnpsi, hxpos']
        rw [hsdef]
        exact mul_le_mul_of_nonneg_right h4 (le_of_lt (hyypos _))
      have hflat := hlam_flat (ψ (max N₁ Bs)) s hs1 hs2
      have hclose : |llam (ψ (max N₁ Bs)) - lam0| < 1 / (2 * (Bs : ℝ)) :=
        hN₁ _ (le_max_left N₁ Bs)
      have hle2 : (1 : ℝ) / (2 * (Nn (ψ (max N₁ Bs)) : ℝ)) ≤ 1 / (2 * (Bs : ℝ)) :=
        one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * (Bs : ℝ))
          (by linarith [hNnpsi])
      have hkey : |g2 (ψ (max N₁ Bs)) s - lam0| ≤ 1 / (Bs : ℝ) := by
        calc |g2 (ψ (max N₁ Bs)) s - lam0|
            ≤ |g2 (ψ (max N₁ Bs)) s - llam (ψ (max N₁ Bs))| + |llam (ψ (max N₁ Bs)) - lam0| :=
              abs_sub_le _ _ _
          _ ≤ 1 / (2 * (Nn (ψ (max N₁ Bs)) : ℝ)) + 1 / (2 * (Bs : ℝ)) :=
              add_le_add hflat (le_of_lt hclose)
          _ ≤ 1 / (Bs : ℝ) := by
              have h2 : (1 : ℝ) / (2 * (Bs : ℝ)) + 1 / (2 * (Bs : ℝ)) = 1 / (Bs : ℝ) := by
                have hb : (Bs : ℝ) ≠ 0 := ne_of_gt hBpos
                field_simp
                ring
              linarith [hle2, h2]
      rw [hratio, hrat_eq]
      exact hkey
  have hlam0nz : lam0 ≠ 0 := fun h => hzero (h ▸ hclu)
  have hlam0pos : 0 < lam0 := lt_of_le_of_ne hlam0nn (Ne.symm hlam0nz)
  have hlam0E : lam0 ∈ E := hsubE hclu
  have hnoMid_psi : ∀ n, ∀ m ∈ Mid E,
      ¬ (min a.1.1 (llam (ψ n)) < m ∧ m < max a.1.1 (llam (ψ n))) := by
    intro n m hm
    have h1 : ¬ (min (fw (φ (ψ n))) a.1.1 < m ∧ m < max (fw (φ (ψ n))) a.1.1) := by
      have h := hrhoband (φ (ψ n)) m hm
      rwa [hrho_const (ψ n)] at h
    have h2 : ¬ (min (fw (φ (ψ n))) (llam (ψ n)) < m
        ∧ m < max (fw (φ (ψ n))) (llam (ψ n))) := hnoMidn (ψ n) m hm
    exact cbz_not_between_trans (hwmid (φ (ψ n))) hm h1 h2
  have hnoMid_lim : ∀ m ∈ Mid E, ¬ (min a.1.1 lam0 < m ∧ m < max a.1.1 lam0) :=
    cbz_no_between_limit hnoMid_psi hψtend
  have hrho_pos : 0 < a.1.1 := by
    have h := hrho0 (φ 0)
    rwa [hrho_const 0] at h
  have hlam0_eq : lam0 = a.1.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨m, hmMid, hm1, hm2⟩ := mb_exists_mid_between hE hlam0E hlam0pos (a.1.2) hlt
      exact hnoMid_lim m hmMid
        ⟨by rw [min_eq_right (le_of_lt hlt)]; exact hm1,
         by rw [max_eq_left (le_of_lt hlt)]; exact hm2⟩
    · obtain ⟨m, hmMid, hm1, hm2⟩ := mb_exists_mid_between hE (a.1.2) hrho_pos hlam0E hlt
      exact hnoMid_lim m hmMid
        ⟨by rw [min_eq_left (le_of_lt hlt)]; exact hm1,
         by rw [max_eq_right (le_of_lt hlt)]; exact hm2⟩
  rcases hlam_ineq' 0 with ⟨hb0, -⟩ | ⟨hb0, -⟩
  · have hgt : ∀ n, a.1.1 * (1 + ε) ≤ llam n := by
      intro n
      rcases hlam_ineq' n with ⟨-, hle⟩ | ⟨hf, -⟩
      · exact le_of_lt (lt_of_lt_of_le ((hsign_fact n).1 hb0) hle)
      · exact absurd (hb0.symm.trans hf) (by decide)
    have hlim : a.1.1 * (1 + ε) ≤ lam0 := ge_of_tendsto' hψtend (fun n => hgt (ψ n))
    rw [hlam0_eq] at hlim
    nlinarith [hrho_pos, hε]
  · have hlt2 : ∀ n, llam n ≤ a.1.1 * (1 - ε) := by
      intro n
      rcases hlam_ineq' n with ⟨ht, -⟩ | ⟨-, hle⟩
      · exact absurd (hb0.symm.trans ht) (by decide)
      · exact le_of_lt (lt_of_le_of_lt hle ((hsign_fact n).2 hb0))
    have hlim : lam0 ≤ a.1.1 * (1 - ε) := le_of_tendsto' hψtend (fun n => hlt2 (ψ n))
    rw [hlam0_eq] at hlim
    nlinarith [hrho_pos, hε]

end Work.WilC4

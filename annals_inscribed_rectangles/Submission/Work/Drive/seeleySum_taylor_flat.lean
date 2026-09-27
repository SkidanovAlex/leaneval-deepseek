import Mathlib
import Submission.Work.Drive.seeleyEpsDefs
import Submission.Work.Drive.seeleyEps_flat
import Submission.Work.Drive.seeleySum_taylor_eq
import Submission.Work.Drive.contDiff_iteratedDeriv_fst

set_option maxHeartbeats 1000000

open scoped ContDiff Topology

namespace Work.Drive

/-- The `ℂ^∞`-order used throughout the Seeley construction. -/
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

private lemma opnorm_fst_le_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ‖ContinuousLinearMap.fst ℝ X ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => by
    rw [one_mul]; exact norm_fst_le p)

private lemma opnorm_snd_le_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ‖ContinuousLinearMap.snd ℝ X ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => by
    rw [one_mul]; exact norm_snd_le p)

private lemma prod_norm_le_one {k : ℕ} {c : ℝ} (hc : c ≤ 1) (h0 : 0 ≤ c) :
    ∏ _ : Fin k, c ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => h0) (fun i _ => hc)

/-- Composing with the first projection cannot increase the norm of an iterated derivative. -/
lemma norm_iteratedFDeriv_comp_fst_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (k : ℕ) (p : X × ℝ) :
    ‖iteratedFDeriv ℝ k (fun p : X × ℝ => f p.1) p‖ ≤ ‖iteratedFDeriv ℝ k f p.1‖ := by
  rw [show (fun p : X × ℝ => f p.1) = f ∘ (ContinuousLinearMap.fst ℝ X ℝ) from rfl]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) (ContinuousLinearMap.fst ℝ X ℝ) hf p
    (i := k) (WithTop.coe_le_coe.mpr le_top)]
  calc ‖(iteratedFDeriv ℝ k f p.1).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.fst ℝ X ℝ)‖
      ≤ ‖iteratedFDeriv ℝ k f p.1‖ *
          ∏ _ : Fin k, ‖ContinuousLinearMap.fst ℝ X ℝ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k f p.1‖ * 1 := by
        gcongr
        exact prod_norm_le_one opnorm_fst_le_one (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k f p.1‖ := mul_one _

/-- Composing with the second projection turns the iterated derivative into a one-dimensional one. -/
lemma norm_iteratedFDeriv_comp_snd_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (k : ℕ) (p : X × ℝ) :
    ‖iteratedFDeriv ℝ k (fun p : X × ℝ => w p.2) p‖ ≤ |iteratedDeriv k w p.2| := by
  rw [show (fun p : X × ℝ => w p.2) = w ∘ (ContinuousLinearMap.snd ℝ X ℝ) from rfl]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) (ContinuousLinearMap.snd ℝ X ℝ) hw p
    (i := k) (WithTop.coe_le_coe.mpr le_top)]
  calc ‖(iteratedFDeriv ℝ k w p.2).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.snd ℝ X ℝ)‖
      ≤ ‖iteratedFDeriv ℝ k w p.2‖ *
          ∏ _ : Fin k, ‖ContinuousLinearMap.snd ℝ X ℝ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k w p.2‖ * 1 := by
        gcongr
        exact prod_norm_le_one opnorm_snd_le_one (norm_nonneg _)
    _ = |iteratedDeriv k w p.2| := by
        rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]

/-- `n.descFactorial i ≤ n!`. -/
lemma descFactorial_le_factorial (n i : ℕ) : n.descFactorial i ≤ n.factorial := by
  by_cases h : i ≤ n
  · have h1 := Nat.factorial_mul_descFactorial h
    have h2 : 1 ≤ (n - i).factorial := Nat.factorial_pos _
    calc n.descFactorial i = 1 * n.descFactorial i := (one_mul _).symm
      _ ≤ (n - i).factorial * n.descFactorial i := Nat.mul_le_mul_right _ h2
      _ = n.factorial := h1
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp h)]; exact Nat.zero_le _

/-- The Leibniz bound for `t ↦ (-t)^n * ε t`, given that the derivatives of `ε` up to order `L`
are `O(|s|^L)`. -/
lemma iteratedDeriv_negPow_mul_bound {ε : ℝ → ℝ}
    (hε : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ε) {Cε : ℝ} (hCε : 0 ≤ Cε) {L : ℕ}
    {s : ℝ} (hbd : ∀ j ≤ L, |iteratedDeriv j ε s| ≤ Cε * |s| ^ L)
    (n : ℕ) {k : ℕ} (hk : k ≤ L) (hs : |s| ≤ 1) :
    |iteratedDeriv k (fun t : ℝ => (-t) ^ n * ε t) s|
      ≤ 2 ^ L * (Nat.factorial n : ℝ) * Cε * |s| ^ L := by
  have hsL : (0 : ℝ) ≤ |s| ^ L := pow_nonneg (abs_nonneg _) L
  have hpow : ∀ i : ℕ, |iteratedDeriv i (fun t : ℝ => (-t) ^ n) s| ≤ (Nat.factorial n : ℝ) := by
    intro i
    have h1 : iteratedDeriv i (fun t : ℝ => (-t) ^ n) s
        = ((-1 : ℝ) ^ i) * iteratedDeriv i (fun t : ℝ => t ^ n) (-s) := by
      simpa using iteratedDeriv_comp_neg i (fun t : ℝ => t ^ n) s
    rw [h1, iteratedDeriv_pow]
    have hA : |(-1 : ℝ) ^ i| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have hB : |(-s) ^ (n - i)| = |s| ^ (n - i) := by rw [abs_pow, abs_neg]
    have hC : |(n.descFactorial i : ℝ)| = (n.descFactorial i : ℝ) :=
      abs_of_nonneg (by positivity)
    rw [abs_mul, hA, abs_mul, hC, hB, one_mul]
    calc (n.descFactorial i : ℝ) * |s| ^ (n - i)
        ≤ (n.descFactorial i : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hs) (by positivity)
      _ = (n.descFactorial i : ℝ) := mul_one _
      _ ≤ (Nat.factorial n : ℝ) := by exact_mod_cast descFactorial_le_factorial n i
  have hcd1 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun t : ℝ => (-t) ^ n) s :=
    (by fun_prop : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (fun t : ℝ => (-t) ^ n)).contDiffAt
  have hcd2 : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) ε s :=
    hε.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤))
  have hkey : iteratedDeriv k (fun t : ℝ => (-t) ^ n * ε t) s
      = ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i (fun t : ℝ => (-t) ^ n) s
            * iteratedDeriv (k - i) ε s := by
    rw [show (fun t : ℝ => (-t) ^ n * ε t) = (fun t : ℝ => (-t) ^ n) * ε from rfl]
    rw [iteratedDeriv_mul hcd1 hcd2]
  have hchoose : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    norm_num
  have hterm : ∀ i : ℕ, |(k.choose i : ℝ) * iteratedDeriv i (fun t : ℝ => (-t) ^ n) s
        * iteratedDeriv (k - i) ε s|
      ≤ (k.choose i : ℝ) * (Nat.factorial n : ℝ) * (Cε * |s| ^ L) := by
    intro i
    have hci : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
    have hfn : (0 : ℝ) ≤ (Nat.factorial n : ℝ) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hci]
    refine mul_le_mul ?_ ?_ ?_ ?_
    · exact mul_le_mul_of_nonneg_left (hpow i) hci
    · exact hbd (k - i) (by omega)
    · exact abs_nonneg _
    · exact mul_nonneg hci hfn
  have h1 : |∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * iteratedDeriv i (fun t : ℝ => (-t) ^ n) s
          * iteratedDeriv (k - i) ε s|
      ≤ ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (Nat.factorial n : ℝ) * (Cε * |s| ^ L) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    exact hterm i
  have h2 : (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (Nat.factorial n : ℝ) * (Cε * |s| ^ L))
      = 2 ^ k * (Nat.factorial n : ℝ) * (Cε * |s| ^ L) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
  have h3 : 2 ^ k * (Nat.factorial n : ℝ) * (Cε * |s| ^ L)
      ≤ 2 ^ L * (Nat.factorial n : ℝ) * Cε * |s| ^ L := by
    have h2' : (2 : ℝ) ^ k ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hk
    have hfn : (0 : ℝ) ≤ (Nat.factorial n : ℝ) := by positivity
    have h4 : 2 ^ k * (Nat.factorial n : ℝ) * (Cε * |s| ^ L)
        ≤ 2 ^ L * (Nat.factorial n : ℝ) * (Cε * |s| ^ L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2' hfn) (mul_nonneg hCε hsL)
    exact h4.trans (le_of_eq (by ring))
  rw [hkey]
  exact h1.trans (h2.le.trans h3)

/-- `∑_{i ≤ k} (k choose i) * X ≤ 2 ^ L * X` for `k ≤ L` and `X ≥ 0`. -/
lemma sum_choose_mul_le {k L : ℕ} (hk : k ≤ L) {X : ℝ} (hX : 0 ≤ X) :
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * X) ≤ 2 ^ L * X := by
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) hX

theorem seeleySum_taylor_flat {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ → ℝ}
    (hb : ∀ j : ℕ, 0 < b j) (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hmom : ∀ q : ℕ, ∑' j : ℕ, a j * (b j) ^ q = (-1 : ℝ) ^ q)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q))
    {F : X × ℝ → E} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (N : ℕ) :
    ∀ x₀ : X, ∀ L : ℕ, ∃ C r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x s, ‖x - x₀‖ < r → s < 0 → -r < s → ∀ k ≤ L,
      ‖iteratedFDeriv ℝ k
        (fun p : X × ℝ => Work.Drive.seeleySum a b (Work.Drive.seeleyTaylor F N) p
          - Work.Drive.seeleyTaylor F N p) (x, s)‖ ≤ C * |s| ^ L := by
  intro x₀ L
  obtain ⟨hεcd, Cε, rε, hrε, _hrε1, hεbd⟩ := seeleyEps_flat (a := a) (b := b) hb hsum N L
  set C : ℝ := max Cε 0 with hCdef
  have hC0 : (0 : ℝ) ≤ C := le_max_right _ _
  have hCbd : ∀ n ≤ N, ∀ j ≤ L, ∀ s : ℝ, -rε < s → s < rε →
      |iteratedDeriv j (seeleyEps a b n) s| ≤ C * |s| ^ L := by
    intro n hn j hj s hs1 hs2
    refine (hεbd n hn s hs1 hs2 j hj).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (abs_nonneg _) L)
  set Bf : X → ℝ := fun x => ∑ n ∈ Finset.range (N + 1),
      ∑ j ∈ Finset.range (L + 1), ‖iteratedFDeriv ℝ j (seeleyCoeff F n) x‖ with hBfdef
  have hcs : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyCoeff F n) := by
    intro n
    have h := contDiff_iteratedDeriv_fst hF (2 * n)
    exact h.const_smul (((Nat.factorial (2 * n) : ℝ))⁻¹)
  have hBfcont : Continuous Bf := by
    rw [hBfdef]
    refine continuous_finsetSum _ (fun n _ => ?_)
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact (((hcs n).continuous_iteratedFDeriv (m := j) (WithTop.coe_le_coe.mpr le_top))).norm
  have hev : ∀ᶠ x in 𝓝 x₀, Bf x < Bf x₀ + 1 := by
    have hcat : ContinuousAt Bf x₀ := hBfcont.continuousAt
    have hc := (Metric.continuousAt_iff.mp hcat) 1 (by norm_num)
    obtain ⟨δ, hδ, hδ'⟩ := hc
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    rw [Metric.mem_ball] at hx
    have h1 := hδ' hx
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.2]
  obtain ⟨r₀, hr₀, hr₀'⟩ := Metric.eventually_nhds_iff.mp hev
  set B : ℝ := Bf x₀ + 1 with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    have h1 : (0 : ℝ) ≤ Bf x₀ := by
      rw [hBfdef]
      exact Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
    rw [hBdef]; linarith
  set A : ℝ := 2 ^ L * (Nat.factorial N : ℝ) * C with hAdef
  have hAnn : (0 : ℝ) ≤ A := by
    have h2L : (0 : ℝ) ≤ 2 ^ L := by positivity
    rw [hAdef]
    exact mul_nonneg (mul_nonneg h2L (by positivity)) hC0
  refine ⟨((N + 1 : ℕ) : ℝ) * (2 ^ L * A * B), min (min rε r₀) 1, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hrε hr₀) one_pos
  · exact min_le_right _ _
  · intro x s hx hsneg hs' k hk
    have hrpos : (0 : ℝ) < min (min rε r₀) 1 := lt_min (lt_min hrε hr₀) one_pos
    have hr_rε : min (min rε r₀) 1 ≤ rε := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr_r₀ : min (min rε r₀) 1 ≤ r₀ := le_trans (min_le_left _ _) (min_le_right _ _)
    have hr_1 : min (min rε r₀) 1 ≤ 1 := min_le_right _ _
    have hsabs : |s| < min (min rε r₀) 1 := abs_lt.mpr ⟨hs', lt_trans hsneg hrpos⟩
    obtain ⟨hsr1, hsr2⟩ := abs_lt.mp (lt_of_lt_of_le hsabs hr_rε : |s| < rε)
    have hs1 : |s| ≤ 1 := le_of_lt (lt_of_lt_of_le hsabs hr_1)
    have hxr₀ : ‖x - x₀‖ < r₀ := lt_of_lt_of_le hx hr_r₀
    have hBx : Bf x ≤ B := by
      rw [hBdef]
      refine le_of_lt (hr₀' ?_)
      rwa [dist_eq_norm]
    have hsL : (0 : ℝ) ≤ |s| ^ L := pow_nonneg (abs_nonneg _) L
    -- polynomial part: the `n`-th summand, `s`-variable
    have hpoly : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (-t) ^ n * seeleyEps a b n t) := by
      intro n
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (-t) ^ n) := by fun_prop
      exact h1.mul (hεcd n)
    have hAbound : ∀ n ≤ N, ∀ k' ≤ L,
        |iteratedDeriv k' (fun t : ℝ => (-t) ^ n * seeleyEps a b n t) s| ≤ A * |s| ^ L := by
      intro n hn k' hk'
      have h1 := iteratedDeriv_negPow_mul_bound (hεcd n) hC0 (fun j hj => hCbd n hn j hj s hsr1 hsr2) n hk' hs1
      have hfn : (Nat.factorial n : ℝ) ≤ (Nat.factorial N : ℝ) := by
        exact_mod_cast Nat.factorial_le hn
      have h2L : (0 : ℝ) ≤ 2 ^ L := by positivity
      have hineq : 2 ^ L * (Nat.factorial n : ℝ) * C * |s| ^ L
          ≤ 2 ^ L * (Nat.factorial N : ℝ) * C * |s| ^ L :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfn h2L) hC0) hsL
      exact h1.trans (by rw [hAdef]; exact hineq)
    -- the vector-valued Taylor coefficient
    have hGcont : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : X × ℝ => ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) := by
      intro n
      exact ((hpoly n).comp contDiff_snd).smul ((hcs n).comp contDiff_fst)
    -- the `x`-variable bound
    have hBbound : ∀ n ≤ N, ∀ j ≤ L,
        ‖iteratedFDeriv ℝ j (fun p : X × ℝ => seeleyCoeff F n p.1) (x, s)‖ ≤ B := by
      intro n hn j hj
      refine (norm_iteratedFDeriv_comp_fst_le (hcs n) j (x, s)).trans ?_
      have hmem1 : j ∈ Finset.range (L + 1) := by rw [Finset.mem_range]; omega
      have hmem2 : n ∈ Finset.range (N + 1) := by rw [Finset.mem_range]; omega
      have h1 : ‖iteratedFDeriv ℝ j (seeleyCoeff F n) x‖
          ≤ ∑ j' ∈ Finset.range (L + 1), ‖iteratedFDeriv ℝ j' (seeleyCoeff F n) x‖ :=
        Finset.single_le_sum (f := fun j' => ‖iteratedFDeriv ℝ j' (seeleyCoeff F n) x‖)
          (fun i _ => norm_nonneg _) hmem1
      have h2 : (∑ j' ∈ Finset.range (L + 1), ‖iteratedFDeriv ℝ j' (seeleyCoeff F n) x‖) ≤ Bf x := by
        rw [hBfdef]
        exact Finset.single_le_sum (f := fun n' => ∑ j' ∈ Finset.range (L + 1),
          ‖iteratedFDeriv ℝ j' (seeleyCoeff F n') x‖)
          (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _)) hmem2
      exact h1.trans (h2.trans hBx)
    -- one summand of the expansion
    have hone : ∀ n ≤ N,
        ‖iteratedFDeriv ℝ k (fun p : X × ℝ => ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)‖
          ≤ 2 ^ L * A * B * |s| ^ L := by
      intro n hn
      have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : X × ℝ => (-p.2) ^ n * seeleyEps a b n p.2) := (hpoly n).comp contDiff_snd
      have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : X × ℝ => seeleyCoeff F n p.1) := (hcs n).comp contDiff_fst
      have hsm := norm_iteratedFDeriv_smul_le (𝕜 := ℝ)
        (f := fun p : X × ℝ => (-p.2) ^ n * seeleyEps a b n p.2)
        (g := fun p : X × ℝ => seeleyCoeff F n p.1) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
        hf hg (x, s) (n := k) (WithTop.coe_le_coe.mpr le_top)
      refine hsm.trans ?_
      have hterm : ∀ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (fun p : X × ℝ => (-p.2) ^ n * seeleyEps a b n p.2) (x, s)‖
            * ‖iteratedFDeriv ℝ (k - i) (fun p : X × ℝ => seeleyCoeff F n p.1) (x, s)‖
          ≤ (k.choose i : ℝ) * (A * |s| ^ L) * B := by
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hci : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
        have h1 : ‖iteratedFDeriv ℝ i (fun p : X × ℝ => (-p.2) ^ n * seeleyEps a b n p.2) (x, s)‖
            ≤ A * |s| ^ L :=
          (norm_iteratedFDeriv_comp_snd_le (hpoly n) i (x, s)).trans
            (hAbound n hn i (le_trans hik hk))
        have h2 := hBbound n hn (k - i) (le_trans (Nat.sub_le k i) hk)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hci) h2 (norm_nonneg _)
          (mul_nonneg hci (mul_nonneg hAnn hsL))
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hXX : (0 : ℝ) ≤ A * |s| ^ L := mul_nonneg hAnn hsL
      have h3 : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * |s| ^ L)) ≤ 2 ^ L * (A * |s| ^ L) :=
        sum_choose_mul_le hk hXX
      have h4 : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * |s| ^ L)) * B ≤ (2 ^ L * (A * |s| ^ L)) * B :=
        mul_le_mul_of_nonneg_right h3 hBnn
      refine h4.trans (le_of_eq ?_)
      ring
    -- the identity and the expansion
    have hfun : (fun p : X × ℝ => seeleySum a b (seeleyTaylor F N) p - seeleyTaylor F N p)
        = fun p : X × ℝ => - ∑ n ∈ Finset.range (N + 1),
            ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1 := by
      funext p
      exact seeleySum_taylor_eq hmom hsum N p.1 p.2
    have hneg : iteratedFDeriv ℝ k (fun p : X × ℝ => - ∑ n ∈ Finset.range (N + 1),
          ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)
        = - iteratedFDeriv ℝ k (fun p : X × ℝ => ∑ n ∈ Finset.range (N + 1),
          ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s) := by
      have hfun2 : (fun p : X × ℝ => - ∑ n ∈ Finset.range (N + 1),
          ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1)
          = - (fun p : X × ℝ => ∑ n ∈ Finset.range (N + 1),
          ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) := rfl
      rw [hfun2, iteratedFDeriv_neg]
      rfl
    have hsum1 : iteratedFDeriv ℝ k (fun p : X × ℝ => ∑ n ∈ Finset.range (N + 1),
          ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)
        = ∑ n ∈ Finset.range (N + 1), iteratedFDeriv ℝ k (fun p : X × ℝ =>
            ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s) := by
      rw [congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (i := k) (u := Finset.range (N + 1))
        (fun n _ => (hGcont n).of_le (WithTop.coe_le_coe.mpr le_top))) (x, s)]
      exact Finset.sum_apply _ _ _
    calc ‖iteratedFDeriv ℝ k
          (fun p : X × ℝ => seeleySum a b (seeleyTaylor F N) p - seeleyTaylor F N p) (x, s)‖
        = ‖iteratedFDeriv ℝ k (fun p : X × ℝ => - ∑ n ∈ Finset.range (N + 1),
            ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)‖ := by rw [hfun]
      _ = ‖iteratedFDeriv ℝ k (fun p : X × ℝ => ∑ n ∈ Finset.range (N + 1),
            ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)‖ := by
            rw [hneg, norm_neg]
      _ = ‖∑ n ∈ Finset.range (N + 1), iteratedFDeriv ℝ k (fun p : X × ℝ =>
            ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)‖ := by rw [hsum1]
      _ ≤ ∑ n ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ k (fun p : X × ℝ =>
            ((-p.2) ^ n * seeleyEps a b n p.2) • seeleyCoeff F n p.1) (x, s)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range (N + 1), 2 ^ L * A * B * |s| ^ L :=
            Finset.sum_le_sum (fun n hn => hone n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
      _ = ((N + 1 : ℕ) : ℝ) * (2 ^ L * A * B) * |s| ^ L := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring

end Work.Drive

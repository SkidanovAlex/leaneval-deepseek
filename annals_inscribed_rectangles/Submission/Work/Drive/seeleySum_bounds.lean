import Mathlib
import Submission.Work.Drive.seeleyDefs
import Submission.Work.Drive.seeleyTermDefs

/-!
# Bounds for the scaled Seeley series
-/

set_option linter.unusedSectionVars false

namespace Work.Drive

open scoped ContDiff Topology
open Filter

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Bounds and flatness of the bump `seeleyRho` -/

theorem exists_iteratedDeriv_seeleyRho_bound :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧ ∀ i t, |iteratedDeriv i seeleyRho t| ≤ K i := by
  have hcomp : HasCompactSupport seeleyRho := ContDiffBump.hasCompactSupport seeleyBump
  have hb : ∀ i, ∃ C : ℝ, ∀ t, |iteratedDeriv i seeleyRho t| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (hcomp.iteratedFDeriv i).exists_bound_of_continuous
      (ContDiff.continuous_iteratedFDeriv (m := i) (n := (i : ℕ∞ω)) le_rfl
        ((contDiff_infty.mp seeleyRho_contDiff) i))
    exact ⟨C, fun t => by
      calc |iteratedDeriv i seeleyRho t| = ‖iteratedFDeriv ℝ i seeleyRho t‖ := by
            rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        _ ≤ C := hC t⟩
  choose K hK using hb
  exact ⟨fun i => max (K i) 0, fun i => le_max_right _ _,
    fun i t => (hK i t).trans (le_max_left _ _)⟩

theorem seeleyRho_iteratedDeriv_eq_zero_of_le (i : ℕ) {t : ℝ} (ht : t ≤ -1) :
    iteratedDeriv i seeleyRho t = 0 := by
  induction i generalizing t with
  | zero =>
      rw [iteratedDeriv_zero]
      exact seeleyRho_eq_zero (by rw [abs_of_nonpos (by linarith)]; linarith)
  | succ i ih =>
      have hsucc : iteratedDeriv (Nat.succ i) seeleyRho = deriv (iteratedDeriv i seeleyRho) := by
        simpa [Nat.succ_eq_add_one] using
          (iteratedDeriv_succ : iteratedDeriv (i + 1) seeleyRho = deriv (iteratedDeriv i seeleyRho))
      rw [hsucc]
      rcases lt_or_eq_of_le ht with hlt | heq
      · have hev : iteratedDeriv i seeleyRho =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Iio.mem_nhds hlt] with t' ht'
          exact ih (le_of_lt ht')
        rw [hev.deriv_eq, deriv_const]
      · subst heq
        have hcont : Continuous (deriv (iteratedDeriv i seeleyRho)) := by
          have h := (contDiff_infty.mp seeleyRho_contDiff (i + 1)).continuous_iteratedDeriv
            (i + 1) le_rfl
          rw [← hsucc]
          exact h
        have hev : deriv (iteratedDeriv i seeleyRho)
            =ᶠ[𝓝[Set.Iio (-1)] (-1)] (fun _ => (0 : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin] with t' ht'
          have hev2 : iteratedDeriv i seeleyRho =ᶠ[𝓝 t'] (fun _ => (0 : ℝ)) := by
            filter_upwards [isOpen_Iio.mem_nhds ht'] with t'' ht''
            exact ih (le_of_lt ht'')
          rw [hev2.deriv_eq, deriv_const]
        have h1 : Tendsto (deriv (iteratedDeriv i seeleyRho)) (𝓝[Set.Iio (-1)] (-1))
            (𝓝 (deriv (iteratedDeriv i seeleyRho) (-1))) :=
          hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (deriv (iteratedDeriv i seeleyRho)) (𝓝[Set.Iio (-1)] (-1))
            (𝓝 0) := Tendsto.congr' hev.symm tendsto_const_nhds
        exact tendsto_nhds_unique h1 h2

/-! ## Two composition estimates -/

/-- Norm bound for the iterated derivative of `p ↦ seeleyRho (b * p.2)` on `X × ℝ`. -/
theorem norm_iteratedFDeriv_seeleyRho_comp_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {b : ℝ} (hb : 0 < b) {K : ℕ → ℝ}
    (hK : ∀ i t, |iteratedDeriv i seeleyRho t| ≤ K i) (i : ℕ) (p : X × ℝ) :
    ‖iteratedFDeriv ℝ i (fun p : X × ℝ => seeleyRho (b * p.2)) p‖ ≤ b ^ i * K i := by
  have hmq : ∀ q : X × ℝ, (b • ContinuousLinearMap.snd ℝ X ℝ) q = b * q.2 := fun q => by
    simp
  have hfun : (fun p : X × ℝ => seeleyRho (b * p.2))
      = seeleyRho ∘ (b • ContinuousLinearMap.snd ℝ X ℝ) := by
    funext q
    rw [Function.comp_apply, hmq q]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ _ p (le_rfl : (↑i : ℕ∞ω) ≤ (i : ℕ∞ω))]
  · have hK0 : 0 ≤ K i := (abs_nonneg (iteratedDeriv i seeleyRho 0)).trans (hK i 0)
    have hmnorm : ‖(b • ContinuousLinearMap.snd ℝ X ℝ : X × ℝ →L[ℝ] ℝ)‖ ≤ b := by
      calc ‖(b • ContinuousLinearMap.snd ℝ X ℝ : X × ℝ →L[ℝ] ℝ)‖
          ≤ ‖(b : ℝ)‖ * ‖ContinuousLinearMap.snd ℝ X ℝ‖ :=
            ContinuousLinearMap.opNorm_smul_le b _
        _ ≤ b * 1 := by
            apply mul_le_mul
            · rw [Real.norm_eq_abs, abs_of_pos hb]
            · exact ContinuousLinearMap.norm_snd_le ℝ X ℝ
            · exact norm_nonneg _
            · exact hb.le
        _ = b := by ring
    calc ‖(iteratedFDeriv ℝ i seeleyRho ((b • ContinuousLinearMap.snd ℝ X ℝ) p)).compContinuousLinearMap
            (fun _ => (b • ContinuousLinearMap.snd ℝ X ℝ))‖
        ≤ ‖iteratedFDeriv ℝ i seeleyRho ((b • ContinuousLinearMap.snd ℝ X ℝ) p)‖
            * ∏ _ : Fin i, ‖(b • ContinuousLinearMap.snd ℝ X ℝ : X × ℝ →L[ℝ] ℝ)‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ i seeleyRho ((b • ContinuousLinearMap.snd ℝ X ℝ) p)‖
            * ‖(b • ContinuousLinearMap.snd ℝ X ℝ : X × ℝ →L[ℝ] ℝ)‖ ^ i := by
          simp [Finset.prod_const]
      _ ≤ K i * b ^ i := by
          refine mul_le_mul ?_ ?_ (by positivity) hK0
          · calc ‖iteratedFDeriv ℝ i seeleyRho ((b • ContinuousLinearMap.snd ℝ X ℝ) p)‖
                = ‖iteratedDeriv i seeleyRho ((b • ContinuousLinearMap.snd ℝ X ℝ) p)‖ :=
                  norm_iteratedFDeriv_eq_norm_iteratedDeriv
              _ = |iteratedDeriv i seeleyRho ((b • ContinuousLinearMap.snd ℝ X ℝ) p)| :=
                  Real.norm_eq_abs _
              _ ≤ K i := hK i _
          · exact pow_le_pow_left₀ (norm_nonneg _) hmnorm i
      _ = b ^ i * K i := by ring
  · exact (contDiff_infty.mp seeleyRho_contDiff) i

/-- Norm bound for the iterated derivative of a composition with a continuous linear map. -/
theorem norm_iteratedFDeriv_comp_clm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) {f : F → G} {U : Set F} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) {x : E} (hx : L x ∈ U) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * ‖L‖ ^ i := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) L
    ((contDiffOn_infty.mp hf) i) hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (le_rfl : (↑i : ℕ∞ω) ≤ (i : ℕ∞ω))
  calc ‖iteratedFDeriv ℝ i (f ∘ L) x‖
      = ‖iteratedFDerivWithin ℝ i (f ∘ L) (L ⁻¹' U) x‖ := by
        rw [(iteratedFDerivWithin_of_isOpen i hpre) hx]
    _ = ‖(iteratedFDerivWithin ℝ i f U (L x)).compContinuousLinearMap (fun _ => L)‖ := by
        rw [hcomp]
    _ = ‖(iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap (fun _ => L)‖ := by
        rw [(iteratedFDerivWithin_of_isOpen i hU) hx]
    _ ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * ‖L‖ ^ i := by
        calc ‖(iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap (fun _ => L)‖
            ≤ ‖iteratedFDeriv ℝ i f (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ i f (L x)‖ * ‖L‖ ^ i := by
              simp [Finset.prod_const]

/-! ## The vanishing of the summand when the argument leaves the support -/

/-- If `b * q.2 ≤ -1` then the bump factor `q ↦ seeleyRho (b * q.2)` has vanishing jet of every
order at `q`: the function is flat at the boundary of its support. -/
theorem iteratedFDeriv_seeleyRho_comp_eq_zero {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {b : ℝ} (i : ℕ) {p : X × ℝ} (hp : b * p.2 ≤ -1) :
    iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b * q.2)) p = 0 := by
  have hmq : ∀ q : X × ℝ, (b • ContinuousLinearMap.snd ℝ X ℝ) q = b * q.2 := fun q => by
    simp
  have hfun : (fun q : X × ℝ => seeleyRho (b * q.2))
      = seeleyRho ∘ (b • ContinuousLinearMap.snd ℝ X ℝ) := by
    funext q
    rw [Function.comp_apply, hmq q]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ _ p
    (le_rfl : (↑i : ℕ∞ω) ≤ (i : ℕ∞ω))]
  · have hz : iteratedFDeriv ℝ i seeleyRho (b * p.2) = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        abs_eq_zero]
      exact seeleyRho_iteratedDeriv_eq_zero_of_le i hp
    rw [hmq p, hz]
    ext m
    simp
  · exact (contDiff_infty.mp seeleyRho_contDiff) i

/-! ## The elementary power estimate -/

/-- The arithmetic core of the summand bound: the factors `b^i` (from the derivatives of the
bump), `(-b s)^(N+1-k+i)` (from the flat jet bound for `R`, which is only available when
`-b s < 1`) and `(1+b)^(k-i)` (from the norm of the linear map `(x,s) ↦ (x, -b s)`) combine into
the weight `(1+b)^(2N+1) |s|^(N+1-k)`. -/
theorem seeley_pow_le {b s : ℝ} (hb : 0 < b) (hs : s < 0) (hσ : -b * s < 1)
    {N k i : ℕ} (hi : i ≤ k) (hk : k ≤ N) :
    b ^ i * (-b * s) ^ (N + 1 - (k - i)) * (1 + b) ^ (k - i)
      ≤ (1 + b) ^ (2 * N + 1) * |s| ^ (N + 1 - k) := by
  have hsabs : 0 < |s| := abs_pos.mpr (ne_of_lt hs)
  have hb0 : 0 ≤ b := hb.le
  have h1b : 1 ≤ 1 + b := by linarith
  have hσ' : b * |s| < 1 := by
    have h : -b * s = b * |s| := by rw [abs_of_neg hs]; ring
    rwa [h] at hσ
  have hσnn : 0 ≤ b * |s| := by positivity
  have hexp : N + 1 - (k - i) = (N + 1 - k) + i := by omega
  have hσeq : -b * s = b * |s| := by rw [abs_of_neg hs]; ring
  have hσi : (b * |s|) ^ i ≤ 1 := pow_le_one₀ hσnn hσ'.le
  have hA : (0:ℝ) ≤ (b * |s|) ^ (N + 1 - k) := pow_nonneg hσnn _
  have hB : (0:ℝ) ≤ (1 + b) ^ (k - i) := pow_nonneg (by linarith) _
  have hE : (0:ℝ) ≤ |s| ^ (N + 1 - k) := pow_nonneg hsabs.le _
  calc b ^ i * (-b * s) ^ (N + 1 - (k - i)) * (1 + b) ^ (k - i)
      = b ^ i * ((b * |s|) ^ (N + 1 - k) * (b * |s|) ^ i) * (1 + b) ^ (k - i) := by
        rw [hexp, hσeq, pow_add]
    _ = b ^ i * ((b * |s|) ^ (N + 1 - k) * ((b * |s|) ^ i * (1 + b) ^ (k - i))) := by ring
    _ ≤ b ^ i * ((b * |s|) ^ (N + 1 - k) * (1 * (1 + b) ^ (k - i))) := by
        gcongr
    _ = b ^ i * ((b * |s|) ^ (N + 1 - k) * (1 + b) ^ (k - i)) := by ring
    _ = (b ^ i * b ^ (N + 1 - k)) * (|s| ^ (N + 1 - k) * (1 + b) ^ (k - i)) := by
        rw [mul_pow]; ring
    _ ≤ ((1 + b) ^ i * (1 + b) ^ (N + 1 - k)) * (|s| ^ (N + 1 - k) * (1 + b) ^ (k - i)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hE hB)
        rw [← pow_add, ← pow_add]
        exact pow_le_pow_left₀ hb0 (by linarith) _
    _ = ((1 + b) ^ i * (1 + b) ^ (N + 1 - k) * (1 + b) ^ (k - i)) * |s| ^ (N + 1 - k) := by ring
    _ = (1 + b) ^ (N + 1) * |s| ^ (N + 1 - k) := by
        rw [← pow_add, ← pow_add, show i + (N + 1 - k) + (k - i) = N + 1 by omega]
    _ ≤ (1 + b) ^ (2 * N + 1) * |s| ^ (N + 1 - k) := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact pow_le_pow_right₀ h1b (by omega)

/-! ## The elementary sum comparison, the weight, and smoothness of a summand -/

theorem seeley_choose_sum_mono {K : ℕ → ℝ} (hK : ∀ i, 0 ≤ K i) {k N : ℕ} (hk : k ≤ N) :
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
      ≤ ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * K i := by
  have h2 : (∑ i ∈ Finset.range (N + 1), (if i ≤ k then (k.choose i : ℝ) * K i else 0))
      = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← h2]
  apply Finset.sum_le_sum
  intro i _
  by_cases hik : i ≤ k
  · rw [if_pos hik]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose i hk) (hK i)
  · rw [if_neg hik]
    exact mul_nonneg (Nat.cast_nonneg _) (hK i)

theorem one_add_pow_le (b : ℝ) (hb : 0 ≤ b) (m : ℕ) : (1 + b) ^ m ≤ 2 ^ m * (1 + b ^ m) := by
  have h1 : (1 + b) ^ m ≤ (2 * max 1 b) ^ m := by
    apply pow_le_pow_left₀ (by linarith)
    linarith [le_max_left (1:ℝ) b, le_max_right (1:ℝ) b]
  rw [mul_pow] at h1
  have h2 : (max (1:ℝ) b) ^ m = max 1 (b ^ m) := by
    rcases le_total 1 b with hb1 | hb1
    · rw [max_eq_right hb1, max_eq_right (one_le_pow₀ hb1)]
    · rw [max_eq_left hb1, max_eq_left (pow_le_one₀ hb hb1), one_pow]
  rw [h2] at h1
  have h3 : max (1:ℝ) (b ^ m) ≤ 1 + b ^ m := by
    rcases le_total 1 (b ^ m) with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hb m]
    · rw [max_eq_left h]; linarith [pow_nonneg hb m]
  exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

theorem summable_seeleyWeight {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (hb : ∀ j : ℕ, 0 < b j)
    (N : ℕ) : Summable (fun j : ℕ => seeleyWeight a b N j) := by
  have h1 : Summable (fun j : ℕ => |a j|) := by simpa using hsum 0
  have h2 : Summable (fun j : ℕ => |a j| * (b j) ^ (2 * N + 1)) := hsum (2 * N + 1)
  have h3 : Summable
      (fun j : ℕ => (2:ℝ) ^ (2 * N + 1) * (|a j| + |a j| * (b j) ^ (2 * N + 1))) :=
    (h1.add h2).mul_left _
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h3
  · exact mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hb j]) _)
  · calc seeleyWeight a b N j = |a j| * (1 + b j) ^ (2 * N + 1) := rfl
      _ ≤ |a j| * (2 ^ (2 * N + 1) * (1 + (b j) ^ (2 * N + 1))) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le (b j) (hb j).le _) (abs_nonneg _)
      _ = 2 ^ (2 * N + 1) * (|a j| + |a j| * (b j) ^ (2 * N + 1)) := by ring

theorem contDiffAt_seeleyTerm {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j) {R : X × ℝ → E}
    (hRsmooth : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R z)
    (j : ℕ) {p : X × ℝ} (hp : p.2 < 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyTerm a b R j) p := by
  have hbj : 0 < b j := hb j
  have hlin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => (seeleyL (X := X) (b j)) q) p :=
    (seeleyL (X := X) (b j)).contDiff.contDiffAt
  have hR' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (seeleyL (X := X) (b j) p) :=
    hRsmooth _ (by rw [seeleyL_snd]; nlinarith)
  have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) p := hR'.comp p hlin
  have hscal : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => seeleyRho (b j * q.2)) p := by
    have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : X × ℝ => b j * q.2) p := by
      have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : X × ℝ => ((b j) • ContinuousLinearMap.snd ℝ X ℝ) q) :=
        ((b j) • ContinuousLinearMap.snd ℝ X ℝ).contDiff
      simpa using h3.contDiffAt
    exact seeleyRho_contDiff.contDiffAt.comp p h
  have hprod : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) p :=
    hscal.smul hcomp
  have h4 := hprod.const_smul (a j)
  convert h4 using 1
  funext q
  simp [seeleyTerm, seeleyL_apply]

/-! ## The pointwise bound for one summand -/

theorem seeleyTerm_norm_bound {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    {R : X × ℝ → E}
    (hRsmooth : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R z)
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ x σ, 0 < σ → σ < 1 → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k R (x, σ)‖ ≤ C * σ ^ (N + 1 - k))
    {K : ℕ → ℝ} (hK : ∀ i t, |iteratedDeriv i seeleyRho t| ≤ K i)
    {j : ℕ} {k : ℕ} (hk : k ≤ N) {p : X × ℝ} (hp : p.2 < 0) :
    ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) p‖
      ≤ seeleyWeight a b N j
        * (C * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
        * |p.2| ^ (N + 1 - k) := by
  have hbj : 0 < b j := hb j
  have hK0 : ∀ i, 0 ≤ K i := fun i => (abs_nonneg _).trans (hK i 0)
  have hinf : ∀ k : ℕ, (↑k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun k => WithTop.coe_le_coe.mpr le_top
  have hUopen : IsOpen {q : X × ℝ | q.2 < 0} := isOpen_lt continuous_snd continuous_const
  have hVopen : IsOpen {z : X × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
  have hpU : p ∈ {q : X × ℝ | q.2 < 0} := hp
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : X × ℝ => seeleyRho (b j * q.2)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (seeleyRho ∘ (b j • ContinuousLinearMap.snd ℝ X ℝ)) :=
      seeleyRho_contDiff.comp ((b j • ContinuousLinearMap.snd ℝ X ℝ).contDiff)
    convert h using 1
    ext q
    simp [Function.comp_def]
  have hRm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R {z : X × ℝ | 0 < z.2} :=
    fun z hz => (hRsmooth z hz).contDiffWithinAt
  have hmap : Set.MapsTo (seeleyL (X := X) (b j)) {q : X × ℝ | q.2 < 0}
      {z : X × ℝ | 0 < z.2} := by
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    rw [seeleyL_snd]
    nlinarith
  have hRj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) {q : X × ℝ | q.2 < 0} :=
    hRm.comp (seeleyL (X := X) (b j)).contDiff.contDiffOn hmap
  have hsmul := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (𝕜' := ℝ)
    (f := fun q : X × ℝ => seeleyRho (b j * q.2))
    (g := fun q : X × ℝ => R (seeleyL (X := X) (b j) q))
    (s := {q : X × ℝ | q.2 < 0}) (N := (k : ℕ∞ω))
    ((contDiff_infty.mp hc) k).contDiffOn ((contDiffOn_infty.mp hRj) k)
    hUopen.uniqueDiffOn hpU (n := k) le_rfl
  have hsummand : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ)
          * ‖iteratedFDerivWithin ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2))
              {q : X × ℝ | q.2 < 0} p‖
          * ‖iteratedFDerivWithin ℝ (k - i)
              (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) {q : X × ℝ | q.2 < 0} p‖
      ≤ ((k.choose i : ℝ) * K i)
        * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by
    intro i hi
    have hik : i ≤ k := by
      simp only [Finset.mem_range] at hi
      omega
    rw [(iteratedFDerivWithin_of_isOpen i hUopen) hpU,
      (iteratedFDerivWithin_of_isOpen (k - i) hUopen) hpU]
    by_cases hσ : -b j * p.2 < 1
    · have hσpos : 0 < -b j * p.2 := by nlinarith
      have h1 : ‖iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2)) p‖
          ≤ (b j) ^ i * K i := norm_iteratedFDeriv_seeleyRho_comp_le hbj hK i p
      have h2 : ‖iteratedFDeriv ℝ (k - i)
            (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) p‖
          ≤ C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i) := by
        have hx' : seeleyL (X := X) (b j) p ∈ {z : X × ℝ | 0 < z.2} := by
          simp only [Set.mem_setOf_eq]
          rw [seeleyL_snd]
          exact hσpos
        refine (norm_iteratedFDeriv_comp_clm_le (seeleyL (X := X) (b j)) hVopen hRm hx'
          (k - i)).trans ?_
        have hstep : ‖iteratedFDeriv ℝ (k - i) R (seeleyL (X := X) (b j) p)‖
            ≤ C * (-b j * p.2) ^ (N + 1 - (k - i)) := by
          rw [seeleyL_apply]
          exact hR p.1 (-b j * p.2) hσpos hσ (k - i) (by omega)
        calc ‖iteratedFDeriv ℝ (k - i) R (seeleyL (X := X) (b j) p)‖
              * ‖seeleyL (X := X) (b j)‖ ^ (k - i)
            ≤ (C * (-b j * p.2) ^ (N + 1 - (k - i))) * (1 + b j) ^ (k - i) := by
              apply mul_le_mul hstep (pow_le_pow_left₀ (norm_nonneg _) (norm_seeleyL_le _ hbj) _)
              · positivity
              · positivity
          _ = C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i) := by ring
      have hfac : (0:ℝ) ≤ (k.choose i : ℝ) * K i * C :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK0 i)) hC
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2)) p‖
              * ‖iteratedFDeriv ℝ (k - i) (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) p‖
          ≤ (k.choose i : ℝ) * ((b j) ^ i * K i)
              * (C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
              · exact h2
              · exact norm_nonneg _
              · exact mul_nonneg (Nat.cast_nonneg _)
                  (mul_nonneg (pow_nonneg hbj.le _) (hK0 i))
        _ ≤ ((k.choose i : ℝ) * K i)
              * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by
              have hpw := seeley_pow_le hbj hp hσ hik hk
              calc (k.choose i : ℝ) * ((b j) ^ i * K i)
                    * (C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i))
                  = ((k.choose i : ℝ) * K i * C)
                      * (b j ^ i * (-b j * p.2) ^ (N + 1 - (k - i))
                          * (1 + b j) ^ (k - i)) := by ring
                _ ≤ ((k.choose i : ℝ) * K i * C)
                      * ((1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) :=
                    mul_le_mul_of_nonneg_left hpw hfac
                _ = ((k.choose i : ℝ) * K i)
                      * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by ring
    · have hle : b j * p.2 ≤ -1 := by linarith [not_lt.mp hσ]
      have hzero : ‖iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2)) p‖ = 0 := by
        rw [iteratedFDeriv_seeleyRho_comp_eq_zero i hle, norm_zero]
      rw [hzero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK0 i))
        (mul_nonneg (mul_nonneg hC (pow_nonneg (by linarith [hbj]) _))
          (pow_nonneg (abs_nonneg _) _))
  have hmain : ‖iteratedFDerivWithin ℝ k
        (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
        {q : X × ℝ | q.2 < 0} p‖
      ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
        * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by
    refine hsmul.trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hsummand
  have hprodOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
      {q : X × ℝ | q.2 < 0} := hc.contDiffOn.smul hRj
  have hprodAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) p :=
    hprodOn.contDiffAt (hUopen.mem_nhds hpU)
  have hterm : seeleyTerm a b R j
      = a j • (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) := by
    funext q
    show a j • (seeleyRho (b j * q.2) • R (q.1, -(b j * q.2)))
      = a j • (seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
    rw [seeleyL_apply, ← neg_mul]
  have hnorm : ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) p‖
      = |a j| * ‖iteratedFDeriv ℝ k
          (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) p‖ := by
    rw [hterm, iteratedFDeriv_const_smul_apply (hprodAt.of_le (hinf k)), norm_smul,
      Real.norm_eq_abs]
  rw [hnorm, ← (iteratedFDerivWithin_of_isOpen k hUopen) hpU]
  calc |a j| * ‖iteratedFDerivWithin ℝ k
          (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
          {q : X × ℝ | q.2 < 0} p‖
      ≤ |a j| * ((∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
            * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k))) :=
        mul_le_mul_of_nonneg_left hmain (abs_nonneg _)
    _ = seeleyWeight a b N j * (C * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
          * |p.2| ^ (N + 1 - k) := by
        unfold seeleyWeight
        ring

/-! ## Finitely many non-zero summands near a point of the open lower half space -/

theorem exists_finset_eventually_seeleyRho_eq_zero {b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop) {s : ℝ} (hs : s < 0) :
    ∃ F : Finset ℕ, ∀ᶠ q in 𝓝 s, ∀ j ∉ F, seeleyRho (b j * q) = 0 := by
  have hsabs : 0 < |s| := abs_pos.mpr (ne_of_lt hs)
  obtain ⟨J, hJ⟩ := (tendsto_atTop_atTop.mp hbtend) (2 / |s|)
  refine ⟨Finset.range J, ?_⟩
  have hball : Metric.ball s (|s| / 2) ∈ 𝓝 s :=
    Metric.ball_mem_nhds s (by linarith [hsabs])
  filter_upwards [hball] with q hq
  intro j hj
  have hjJ : J ≤ j := by
    simp only [Finset.mem_range, not_lt] at hj
    exact hj
  have hbj : 2 / |s| ≤ b j := hJ j hjJ
  have hqmem : dist q s < |s| / 2 := hq
  have hqlow : |s| / 2 ≤ |q| := by
    rw [dist_eq_norm, Real.norm_eq_abs] at hqmem
    have h2 : |s - q| = |q - s| := abs_sub_comm s q
    have h1 : |s| - |q| ≤ |q - s| := by
      rw [← h2]; exact abs_sub_abs_le_abs_sub s q
    linarith
  rw [seeleyRho_eq_zero]
  rw [abs_mul, abs_of_pos (hb j)]
  calc (1:ℝ) = (2 / |s|) * (|s| / 2) := by field_simp
    _ ≤ b j * |q| := mul_le_mul hbj hqlow (by linarith [hsabs]) (hb j).le

/-! ## The main bound -/

/-- Bounds for the scaled Seeley series `Σ_j a_j ρ (b_j s) R (x, -b_j s)` on the lower half-plane, given flat jet bounds for a function `R` smooth on the upper half-space. The summands vanish unless `|b_j s| < 1`, and `ρ` is constant `1` near `0`, so the moment sequence `(a,b)` with absolutely summable moments supplies the factor `Σ_j |a_j| b_j^(N+1)`, while the support condition `b_j * |s| < 1` converts `R`'s bound `σ^(N+1-k)` into `|s|^(N+1-k)`. -/
theorem seeleySum_bounds {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ → ℝ}
    (hb : ∀ j : ℕ, 0 < b j) (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q))
    {R : X × ℝ → E} (hRsmooth : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R z)
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ x σ, 0 < σ → σ < 1 → ∀ k ≤ N, ‖iteratedFDeriv ℝ k R (x, σ)‖ ≤ C * σ ^ (N + 1 - k)) :
    ∀ x₀ : X, ∃ C' r' : ℝ, 0 < r' ∧ r' ≤ 1 ∧ ∀ x s, ‖x - x₀‖ < r' → s < 0 → -r' < s → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Work.Drive.seeleySum a b R) (x, s)‖ ≤ C' * |s| ^ (N + 1 - k) := by
  intro x₀
  obtain ⟨K, hK0, hKb⟩ := exists_iteratedDeriv_seeleyRho_bound
  set Λ : ℝ := ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * K i with hΛ
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hK0 i)
  have hWsum : Summable (fun j : ℕ => seeleyWeight a b N j) := summable_seeleyWeight hsum hb N
  refine ⟨(∑' j, seeleyWeight a b N j) * (C * Λ), 1, one_pos, le_rfl, ?_⟩
  intro x s _ hs0 _ k hk
  obtain ⟨F, hF⟩ := exists_finset_eventually_seeleyRho_eq_zero hb hbtend hs0
  have hev : ∀ᶠ q in 𝓝 (x, s), seeleySum a b R q = ∑ j ∈ F, seeleyTerm a b R j q := by
    filter_upwards [(continuous_snd.tendsto (x, s)).eventually hF] with q hq
    change (∑' j, seeleyTerm a b R j q) = ∑ j ∈ F, seeleyTerm a b R j q
    rw [tsum_eq_sum (s := F)]
    intro j hj
    rw [seeleyTerm_apply, hq j hj, zero_smul, smul_zero]
  have heq : iteratedFDeriv ℝ k (seeleySum a b R) (x, s)
      = ∑ j ∈ F, iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s) := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds]
    exact iteratedFDeriv_fun_sum_apply
      (fun j _ => (contDiffAt_seeleyTerm hb hRsmooth j (p := (x, s)) hs0).of_le
        (show (↑k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top))
  rw [heq]
  have hbound : ∀ j ∈ F, ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s)‖
      ≤ seeleyWeight a b N j * (C * Λ) * |s| ^ (N + 1 - k) := by
    intro j _
    have h1 := seeleyTerm_norm_bound (X := X) (E := E) (a := a) (b := b) hb hRsmooth hC hR hKb hk
      (p := (x, s)) hs0 (j := j)
    have h2 : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i) ≤ Λ := by
      rw [hΛ]; exact seeley_choose_sum_mono hK0 hk
    have hw : 0 ≤ seeleyWeight a b N j :=
      mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hb j]) _)
    have hz : 0 ≤ |s| ^ (N + 1 - k) := pow_nonneg (abs_nonneg _) _
    have h3 : seeleyWeight a b N j
          * (C * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
        ≤ seeleyWeight a b N j * (C * Λ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC) hw
    exact h1.trans (mul_le_mul_of_nonneg_right h3 hz)
  calc ‖∑ j ∈ F, iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s)‖
      ≤ ∑ j ∈ F, ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ F, seeleyWeight a b N j * (C * Λ) * |s| ^ (N + 1 - k) := Finset.sum_le_sum hbound
    _ = (∑ j ∈ F, seeleyWeight a b N j) * (C * Λ) * |s| ^ (N + 1 - k) := by
          rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ (∑' j, seeleyWeight a b N j) * (C * Λ) * |s| ^ (N + 1 - k) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hΛnn)
          exact Summable.sum_le_tsum F (fun i _ => mul_nonneg (abs_nonneg _)
            (pow_nonneg (by linarith [hb i]) _)) hWsum

end Work.Drive

import Mathlib
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge
import Submission.Work.Peluse.Concat.arithIcc_shrink_dvd_ge

/-!
# Shrinking the arithmetic-progression direction set `c[L]` to `c[L']` (`t ≥ 2`)

The target `Work.Peluse.Concat.arithIcc_shrink_ge_two` states that for every `t ≥ 2` there is
`C > 0` such that for all `1 ≤ L' ≤ L`, all `c > 0`, all `N` and every `1`-bounded `f` supported in
`[-N,N]`,

`C * ‖f‖^{2^t}_{□^t_{c[L]}([-N,N])} ≤ ‖f‖^{2^t}_{□^t_{c[L']}([-N,N])}`.

## The proof

Two ingredients suffice:

* the **divisible** comparison `Work.Peluse.Concat.arithIcc_shrink_dvd_ge` (proved elsewhere in
  this directory, with constant `1`): for `L' ∣ L`,
  `‖f‖^{2^t}_{□^t_{c[L]}} ≤ ‖f‖^{2^t}_{□^t_{c[L']}}`;
* **monotonicity of the raw box sum** in the direction set (`raw_mono` below): for `t ≥ 2`,
  `L ≤ L'` and any window `S`,
  `L ^ (2*t) * ‖f‖^{2^t}_{□^t_{c[L]}(S)} ≤ L' ^ (2*t) * ‖f‖^{2^t}_{□^t_{c[L']}(S)}`.

Given these, with `m = L / L'` one has `L ≤ (m+1) * L'`, so
`‖f‖_{□^t_{c[L]}} ≤ ((m+1)L'/L)^{2t} ‖f‖_{□^t_{c[(m+1)L']}}`, and `L' ∣ (m+1)L'` together with
`(m+1)L' ≤ L + L' ≤ 2L` yields `‖f‖_{□^t_{c[L]}} ≤ 4^t ‖f‖_{□^t_{c[L']}}`.

`raw_mono` is proved by induction on `t` from the *peel* identity
`boxNormPow_succ_peel` and the level-two monotonicity
`Work.Peluse.BoxNormDilation.pair_sum_mono` (the latter is the special case `t = 2`, where the
raw pair sum is monotone because the level-two box-norm power is a sum of squares).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

open Work.Peluse

/-! ## Elementary lemmas -/

/-- The difference `f (· + h) · conj (f (· + h'))` of a function supported in `[-N,N]` is
supported in `[-(N + |h| + |h'|), N + |h| + |h'|]`. -/
lemma supportIn_delta_aux {N : ℕ} {f : ℤ → ℂ} (hf : SupportIn f N) (h h' : ℤ) :
    SupportIn (fun u : ℤ => f (u + h) * star (f (u + h'))) (N + h.natAbs + h'.natAbs) := by
  intro u hu
  by_cases h1 : f (u + h) = 0
  · simp [h1]
  · have hle : (u + h).natAbs ≤ N := by
      by_contra hc
      exact h1 (hf (u + h) (by omega))
    have htri : u.natAbs ≤ (u + h).natAbs + h.natAbs := by
      have := Int.natAbs_add_le (u + h) (-h)
      rw [show u + h + -h = u by ring, Int.natAbs_neg] at this
      exact this
    omega

/-- A difference of finitely supported functions is finitely supported. -/
lemma finSuppZ_delta_aux {f : ℤ → ℂ} (hf : FinSuppZ f) (h h' : ℤ) :
    FinSuppZ (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  obtain ⟨N, hN⟩ := hf
  exact ⟨_, supportIn_delta_aux hN h h'⟩

/-- A difference of `1`-bounded functions is `1`-bounded. -/
lemma norm_delta_aux {f : ℤ → ℂ} (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (h h' u : ℤ) :
    ‖f (u + h) * star (f (u + h'))‖ ≤ 1 := by
  rw [norm_mul, norm_star]
  calc ‖f (u + h)‖ * ‖f (u + h')‖ ≤ 1 * 1 :=
        mul_le_mul (hf _) (hf _) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- `arithIcc c ·` is monotone in the length. -/
lemma arithIcc_mono_aux {c : ℤ} {L L' : ℕ} (h : L ≤ L') :
    arithIcc c L ⊆ arithIcc c L' := by
  intro x hx
  rw [arithIcc] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hn).1, le_trans (Finset.mem_Icc.mp hn).2 h⟩, rfl⟩

/-- Expanding a nonnegative double sum along an inclusion of index sets. -/
lemma sum_le_sum_expand {A B : Finset ℤ} (hAB : A ⊆ B) (F : ℤ → ℤ → ℝ)
    (hF : ∀ h h', 0 ≤ F h h') :
    (∑ h ∈ A, ∑ h' ∈ A, F h h') ≤ ∑ h ∈ B, ∑ h' ∈ B, F h h' := by
  calc (∑ h ∈ A, ∑ h' ∈ A, F h h') ≤ ∑ h ∈ B, ∑ h' ∈ A, F h h' :=
        Finset.sum_le_sum_of_subset_of_nonneg hAB
          (fun h _ _ => Finset.sum_nonneg (fun h' _ => hF h h'))
    _ ≤ ∑ h ∈ B, ∑ h' ∈ B, F h h' :=
        Finset.sum_le_sum (fun h _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hAB (fun h' _ _ => hF h h'))

/-- The level-two raw pair sum `GG` is monotone in the direction set. -/
lemma pair_sum_mono_full {A B : Finset ℤ} (hAB : A ⊆ B) {f : ℤ → ℂ} (hf : FinSuppZ f) :
    (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ A, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ B, ∑ b ∈ B, ∑' x : ℤ,
          ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2 := by
  have h1 : (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
        ‖∑ k ∈ A, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
          ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2 :=
    Work.Peluse.BoxNormDilation.pair_sum_mono hAB hf
  have h2 : (∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ,
          ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ B, ∑ b ∈ A, ∑' x : ℤ,
          ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hAB (fun a _ _ =>
      Finset.sum_nonneg (fun b _ => tsum_nonneg (fun x => by positivity)))
  have h3 : (∑ a ∈ B, ∑ b ∈ A, ∑' x : ℤ,
          ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2)
      ≤ ∑ a ∈ B, ∑ b ∈ B, ∑' x : ℤ,
          ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2 :=
    Finset.sum_le_sum (fun a _ =>
      Finset.sum_le_sum_of_subset_of_nonneg hAB (fun b _ _ =>
        tsum_nonneg (fun x => by positivity)))
  exact le_trans h1 (le_trans h2 h3)

/-- **Level two**: the raw quantity `L ^ 4 · ‖f‖^4_{□²_{c[L]}(S)}` is monotone in `L`. -/
lemma raw_mono_two {c : ℤ} (hc : 0 < c) {L L' : ℕ} (h1 : 1 ≤ L) (h : L ≤ L')
    (S : Finset ℤ) {f : ℤ → ℂ} (hfZ : FinSuppZ f) :
    (L : ℝ) ^ 4 * boxNormPow 2 (fun _ : Fin 2 => arithIcc c L) S f
      ≤ (L' : ℝ) ^ 4 * boxNormPow 2 (fun _ : Fin 2 => arithIcc c L') S f := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast h1
  have hL'0 : (0 : ℝ) < (L' : ℝ) := by exact_mod_cast (le_trans h1 h)
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL0
  have hcard : ((arithIcc c L).card : ℝ) = (L : ℝ) := by
    rw [card_arithIcc_shrink hcne L]
  have hcard' : ((arithIcc c L').card : ℝ) = (L' : ℝ) := by
    rw [card_arithIcc_shrink hcne L']
  rw [Work.Peluse.BoxNormDilation.boxNormPow_two_eq (arithIcc c L) S hfZ,
      Work.Peluse.BoxNormDilation.boxNormPow_two_eq (arithIcc c L') S hfZ,
      hcard, hcard']
  set G : ℝ := ∑ a ∈ arithIcc c L, ∑ b ∈ arithIcc c L, ∑' x : ℤ,
      ‖∑ k ∈ arithIcc c L, f (x + a + k) * star (f (x + b + k))‖ ^ 2 with hG
  set G' : ℝ := ∑ a ∈ arithIcc c L', ∑ b ∈ arithIcc c L', ∑' x : ℤ,
      ‖∑ k ∈ arithIcc c L', f (x + a + k) * star (f (x + b + k))‖ ^ 2 with hG'
  have hGG : G ≤ G' := by
    rw [hG, hG']
    exact pair_sum_mono_full (arithIcc_mono_aux h) hfZ
  have hfac : (L : ℝ) ^ 4 * ((L : ℝ)⁻¹ ^ 4) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hLne, one_pow]
  have hfac' : (L' : ℝ) ^ 4 * ((L' : ℝ)⁻¹ ^ 4) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hL'0), one_pow]
  have e1 : (L : ℝ) ^ 4 * (((S.card : ℝ))⁻¹ * ((L : ℝ))⁻¹ ^ 4 * G)
      = ((S.card : ℝ))⁻¹ * G := by
    calc (L : ℝ) ^ 4 * (((S.card : ℝ))⁻¹ * ((L : ℝ))⁻¹ ^ 4 * G)
        = ((S.card : ℝ))⁻¹ * (((L : ℝ) ^ 4 * ((L : ℝ))⁻¹ ^ 4) * G) := by ring
      _ = ((S.card : ℝ))⁻¹ * G := by rw [hfac]; ring
  have e2 : (L' : ℝ) ^ 4 * (((S.card : ℝ))⁻¹ * ((L' : ℝ))⁻¹ ^ 4 * G')
      = ((S.card : ℝ))⁻¹ * G' := by
    calc (L' : ℝ) ^ 4 * (((S.card : ℝ))⁻¹ * ((L' : ℝ))⁻¹ ^ 4 * G')
        = ((S.card : ℝ))⁻¹ * (((L' : ℝ) ^ 4 * ((L' : ℝ))⁻¹ ^ 4) * G') := by ring
      _ = ((S.card : ℝ))⁻¹ * G' := by rw [hfac']; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hGG (by positivity)

/-! ## The monotonicity of the raw box sum at every level `t ≥ 2` -/

/-- **Monotonicity of the raw box sum.**  For `t ≥ 2`, `1 ≤ L ≤ L'` and any window `S`,
`L ^ (2*t) · boxNormPow t (c[L]) S f ≤ L' ^ (2*t) · boxNormPow t (c[L']) S f`. -/
theorem raw_mono : ∀ (n : ℕ) {c : ℤ}, 0 < c → ∀ {L L' : ℕ}, 1 ≤ L → L ≤ L' →
    ∀ (S : Finset ℤ) {f : ℤ → ℂ}, FinSuppZ f → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    (L : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L) S f
      ≤ (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L') S f := by
  intro n
  induction n with
  | zero =>
      intro c hc L L' h1 hLL' S f hfZ hb
      exact raw_mono_two hc h1 hLL' S hfZ
  | succ n ih =>
      intro c hc L L' h1 hLL' S f hfZ hb
      have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast h1
      have hL'0 : (0 : ℝ) < (L' : ℝ) := by exact_mod_cast (le_trans h1 hLL')
      have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL0
      have hL'ne : (L' : ℝ) ≠ 0 := ne_of_gt hL'0
      have hcard : ((arithIcc c L).card : ℝ) = (L : ℝ) := by
        rw [card_arithIcc_shrink (ne_of_gt hc) L]
      have hcard' : ((arithIcc c L').card : ℝ) = (L' : ℝ) := by
        rw [card_arithIcc_shrink (ne_of_gt hc) L']
      have hpL := Work.Peluse.BoxNormDilation.boxNormPow_succ_peel (n + 2) (by omega)
        (arithIcc c L) S hfZ
      have hpL' := Work.Peluse.BoxNormDilation.boxNormPow_succ_peel (n + 2) (by omega)
        (arithIcc c L') S hfZ
      rw [hpL, hpL', hcard, hcard']
      -- the per-summand induction hypothesis
      have hterm : ∀ h h' : ℤ,
          (L : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L) S
              (fun u : ℤ => f (u + h) * star (f (u + h')))
            ≤ (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L') S
                (fun u : ℤ => f (u + h) * star (f (u + h'))) :=
        fun h h' => ih hc h1 hLL' S (finSuppZ_delta_aux hfZ h h')
          (fun u => norm_delta_aux hb h h' u)
      -- the algebraic normalisation of the two prefactors
      have hpow : (L : ℝ) ^ (2 * (n + 1 + 2)) * ((L : ℝ))⁻¹ ^ 2
          = (L : ℝ) ^ (2 * (n + 2)) := by
        rw [show 2 * (n + 1 + 2) = 2 * (n + 2) + 2 by ring, pow_add, pow_two]
        field_simp
      have hpow' : (L' : ℝ) ^ (2 * (n + 1 + 2)) * ((L' : ℝ))⁻¹ ^ 2
          = (L' : ℝ) ^ (2 * (n + 2)) := by
        rw [show 2 * (n + 1 + 2) = 2 * (n + 2) + 2 by ring, pow_add, pow_two]
        field_simp
      set SL : ℝ := ∑ h ∈ arithIcc c L, ∑ h' ∈ arithIcc c L,
          boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) with hSL
      set SL' : ℝ := ∑ h ∈ arithIcc c L', ∑ h' ∈ arithIcc c L',
          boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L') S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) with hSL'
      have hfacL : (L : ℝ) ^ (2 * (n + 1 + 2)) * ((L : ℝ)⁻¹ ^ 2 * SL)
          = (L : ℝ) ^ (2 * (n + 2)) * SL := by
        rw [← mul_assoc, hpow]
      have hfacL' : (L' : ℝ) ^ (2 * (n + 1 + 2)) * ((L' : ℝ)⁻¹ ^ 2 * SL')
          = (L' : ℝ) ^ (2 * (n + 2)) * SL' := by
        rw [← mul_assoc, hpow']
      rw [hfacL, hfacL']
      have hp1 : (L : ℝ) ^ (2 * (n + 2)) * (∑ h ∈ arithIcc c L, ∑ h' ∈ arithIcc c L,
            boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L) S
              (fun u : ℤ => f (u + h) * star (f (u + h'))))
          = ∑ h ∈ arithIcc c L, ∑ h' ∈ arithIcc c L,
              (L : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L) S
                (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun h _ => Finset.mul_sum _ _ _)
      have hp2 : (L' : ℝ) ^ (2 * (n + 2)) * (∑ h ∈ arithIcc c L', ∑ h' ∈ arithIcc c L',
            boxNormPow (n + 2) (fun _ : Fin (n + 2) => arithIcc c L') S
              (fun u : ℤ => f (u + h) * star (f (u + h'))))
          = ∑ h ∈ arithIcc c L', ∑ h' ∈ arithIcc c L',
              (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L') S
                (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun h _ => Finset.mul_sum _ _ _)
      have hb1 : (∑ h ∈ arithIcc c L, ∑ h' ∈ arithIcc c L,
            (L : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L) S
                (fun u : ℤ => f (u + h) * star (f (u + h'))))
          ≤ ∑ h ∈ arithIcc c L, ∑ h' ∈ arithIcc c L,
            (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L') S
                (fun u : ℤ => f (u + h) * star (f (u + h'))) :=
        Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => hterm h h'))
      have hb2 : (∑ h ∈ arithIcc c L, ∑ h' ∈ arithIcc c L,
            (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L') S
                (fun u : ℤ => f (u + h) * star (f (u + h'))))
          ≤ ∑ h ∈ arithIcc c L', ∑ h' ∈ arithIcc c L',
            (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L') S
                (fun u : ℤ => f (u + h) * star (f (u + h'))) :=
        sum_le_sum_expand (arithIcc_mono_aux (c := c) hLL')
          (fun h h' => (L' : ℝ) ^ (2 * (n + 2)) * boxNormPow (n + 2)
              (fun _ : Fin (n + 2) => arithIcc c L') S
              (fun u : ℤ => f (u + h) * star (f (u + h'))))
          (fun h h' => mul_nonneg (pow_nonneg (Nat.cast_nonneg L') _)
              (Work.Peluse.BoxNormDilation.boxNormPow_nonneg (n + 2)
                (fun _ : Fin (n + 2) => arithIcc c L') S
                (fun u : ℤ => f (u + h) * star (f (u + h')))))
      rw [hSL, hSL', hp1, hp2]
      exact le_trans hb1 hb2

/-! ## The target -/

theorem arithIcc_shrink_ge_two {t : ℕ} (ht : 2 ≤ t) : ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℤ) (hc : 0 < c) (L' L : ℕ), 1 ≤ L' → L' ≤ L → ∀ {N : ℕ} (f : ℤ → ℂ),
    Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    C * Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L) (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L') (Work.Peluse.symIcc N) f := by
  obtain ⟨C0, hC0, hdvd⟩ := arithIcc_shrink_dvd_ge t
  refine ⟨C0 / 4 ^ t, by positivity, ?_⟩
  intro c hc L' L hL' hLL N f hfN hb
  have hfZ : FinSuppZ f := FinSuppZ.of_supportIn hfN
  have hL1 : 1 ≤ L := le_trans hL' hLL
  have hLne : (L : ℝ) ≠ 0 := by positivity
  have hLpos : (0 : ℝ) < L := by positivity
  have ht2 : 2 ≤ t := ht
  -- monotonicity: compare `c[L]` with `c[(L / L' + 1) * L']`
  have hmult : (L / L') * L' ≤ L := Nat.div_mul_le_self L L'
  have hboundL : L ≤ (L / L' + 1) * L' := by
    have hL'pos : 0 < L' := by omega
    have h : L < (L / L' + 1) * L' :=
      (Nat.div_lt_iff_lt_mul (x := L) (y := L / L' + 1) (Hk := hL'pos)).mp
        (Nat.lt_succ_self (L / L'))
    exact le_of_lt h
  have hmono := raw_mono (t - 2) hc hL1 hboundL (symIcc N) hfZ hb
  -- divisibility: `(L / L' + 1) * L'` is a multiple of `L'`
  have hdvd' : C0 * boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f
      ≤ boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f :=
    hdvd c hc L' ((L / L' + 1) * L') hL' ⟨L / L' + 1, by ring⟩ (f := f) hfN hb
  -- `(L / L' + 1) * L' ≤ 2 * L`
  have hbound : ((L / L' + 1) * L' : ℕ) ≤ 2 * L := by
    have h1 : (L / L') * L' ≤ L := Nat.div_mul_le_self L L'
    have h2 : L' ≤ L := hLL
    nlinarith
  have hpow : ((((L / L' + 1) * L' : ℕ)) : ℝ) ^ (2 * t) ≤ (2 * L : ℝ) ^ (2 * t) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hbound
  have h4 : (2 * (L : ℝ)) ^ (2 * t) = 4 ^ t * (L : ℝ) ^ (2 * t) := by
    rw [mul_pow]
    congr 1
    rw [show (2 : ℝ) ^ (2 * t) = (2 ^ 2) ^ t by rw [pow_mul]]
    norm_num
  -- assemble
  have step1 : (L : ℝ) ^ (2 * t) * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f
      ≤ (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f := by
    have := hmono
    rwa [show t - 2 + 2 = t by omega] at this
  have step2 : C0 * boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f
      ≤ boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f := hdvd'
  have key : C0 * (L : ℝ) ^ (2 * t) * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f
      ≤ (2 * (L : ℝ)) ^ (2 * t) * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f := by
    have hA : C0 * ((L : ℝ) ^ (2 * t) *
        boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f)
        ≤ C0 * ((((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f) :=
      mul_le_mul_of_nonneg_left step1 hC0.le
    have hB : C0 * ((((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f)
        = (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          (C0 * boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f) := by
      ring
    have hC : (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          (C0 * boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f)
        ≤ (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f :=
      mul_le_mul_of_nonneg_left step2 (by positivity)
    have hD : (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
          boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f
        ≤ (2 * (L : ℝ)) ^ (2 * t) * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f :=
      mul_le_mul_of_nonneg_right hpow (Work.Peluse.BoxNormDilation.boxNormPow_nonneg t _ _ _)
    calc C0 * (L : ℝ) ^ (2 * t) * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f
        = C0 * ((L : ℝ) ^ (2 * t) *
            boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f) := by ring
      _ ≤ (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
            (C0 * boxNormPow t (fun _ : Fin t => arithIcc c ((L / L' + 1) * L')) (symIcc N) f) := by
          rw [← hB]; exact hA
      _ ≤ (((L / L' + 1) * L' : ℕ) : ℝ) ^ (2 * t) *
            boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f := hC
      _ ≤ (2 * (L : ℝ)) ^ (2 * t) * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f := hD
  -- divide by `L^(2t)`
  have hdiv : C0 * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f
      ≤ 4 ^ t * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f := by
    have h := key
    rw [h4] at h
    have h2 : C0 * (L : ℝ) ^ (2 * t) *
          boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f
        = (L : ℝ) ^ (2 * t) * (C0 * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f) := by
      ring
    rw [h2] at h
    have hpos : (0 : ℝ) < (L : ℝ) ^ (2 * t) := by positivity
    have h'' : (L : ℝ) ^ (2 * t) * (C0 * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f)
        ≤ (L : ℝ) ^ (2 * t) *
          (4 ^ t * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f) := by
      have hr : 4 ^ t * (L : ℝ) ^ (2 * t) *
            boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f
          = (L : ℝ) ^ (2 * t) *
            (4 ^ t * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f) := by ring
      rwa [hr] at h
    exact le_of_mul_le_mul_left h'' hpos
  calc C0 / 4 ^ t * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f
      = (4 ^ t)⁻¹ * (C0 * boxNormPow t (fun _ : Fin t => arithIcc c L) (symIcc N) f) := by
        rw [div_eq_inv_mul]; ring
    _ ≤ (4 ^ t)⁻¹ * (4 ^ t * boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = boxNormPow t (fun _ : Fin t => arithIcc c L') (symIcc N) f := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity : ((4:ℝ) ^ t) ≠ 0), one_mul]

end

end Work.Peluse.Concat

import Mathlib
import Submission.Work.Peluse.Peel.boxNormPow_diag_peel
import Submission.Work.Peluse.UControl.RouteA

/-!
# The elementary (`L²`-mass) lower bound for the `U^s`-norm of an arbitrary complex function

The target `Work.Peluse.UControl.elementary_bound_v2` is the "small direction length" regime of
Peluse's Theorem 3.7 (S. Peluse, *Bounds for sets with no polynomial progressions*, Forum of Math.
Pi **8** (2020), e16) in the normalisation of the workspace: for a *complex* function `f` supported
in `[-N₀,N₀]` whose `L²`-mass is at least `δ² N₀ / 3` and any direction length `1 ≤ L ≤ N₀`, the
`2^s`-th power of the `U^s`-norm of `f` at the direction set `(deg P)!·lc P [L]` is at least
`c δ^{2^s} / L^s`, with `c > 0` depending on `s` only.  (No polynomial input is used; the only
property of `P` entering is that the direction *set* has at most `L` elements.)

## The diagonal peel

The proof is the standard *diagonal* argument for Gowers box norms, in the form that keeps the exact
power of the direction length:

* **Peeling the top level.**  In the peel identity `Peel.boxSumPow_peel` every lower-level box sum
  is a nonnegative real (`BoxNorm.boxSumPow_eq_boxNormPow`, valid for *any* finitely supported
  function once the level is `>= 1`), so keeping only the diagonal pairs `h = h'` is legitimate.
  Since `Δ'_{h,h} f = |f(·+h)|²` and the box norm is translation invariant
  (`BoxNorm.boxNormPow_shift`), this gives, for every level `t >= 1`,
  `|Q|⁻¹ · ‖|f|²‖_{□^t_Q(S)} ≤ ‖f‖_{□^{t+1}_Q(S)}`
  (`Peel.boxNormPow_diag_step`, iterated as `Peel.diag_iterate`).
  Here the positivity of `f` is *not* needed -- only that the *lower* level is `>= 1`, which is why
  the argument applies to an arbitrary complex function as long as `s >= 2` and stops at level `1`.
* **The level-one base.**  At level `1` the diagonal argument needs `h >= 0`
  (`Peel.level_one_ge_base`): `|Q|⁻¹ (∑_x h(x)²)/|S| ≤ ‖h‖_{□^1_Q(S)}`.
* **Power mean and cardinality.**  `(∑_x ‖f x‖^{2^s})/|S| >= ((∑_x ‖f x‖²)/|S|)^{2^{s-1}}` by the
  power mean inequality (`Peel.powMeanZ`), and `(δ²N₀/3)/|symIcc N₀| >= δ²/9` because
  `|symIcc N₀| = 2N₀+1 ≤ 3N₀` for `N₀ >= 1`.

Taking `c = 9^{-2^{s-1}}` finishes the proof.

## Main results

* `Work.Peluse.UControl.uNormPow_tsum_le` -- the diagonal peel with the exact exponent `|Q|^{-s}`;
* `Work.Peluse.UControl.mass_powmean_ratio` -- the power-mean/cardinality arithmetic;
* `Work.Peluse.UControl.elementary_bound_v2` -- the target.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- **The diagonal peel with the exact exponent `s`.**  For a finitely supported complex function
`f`, a nonempty shift set `Q` and any ambient set `S`, the `2^s`-th power of the box norm at the
constant shift family `Q` (`s ≥ 2`) dominates `|Q|^{-s}` times the normalised `L^{2^s}`-mass of `f`:

`|Q|^{-s} · (∑_x ‖f x‖^{2^s}) / |S| ≤ ‖f‖_{□^s_Q(S)}^{2^s}`.

The `s` factors `|Q|^{-1}` come from the `s-1` diagonal peel steps and the level-one base case; the
exponent `s` (rather than `2^s`, or the mass exponent `2^{s-1}`) is what makes the bound usable
against the `L^{-s}`-loss of the small direction-length regime. -/
theorem uNormPow_tsum_le {s : ℕ} (hs : 2 ≤ s) (Q : Finset ℤ) (hQ : Q.Nonempty) (S : Finset ℤ)
    (f : ℤ → ℂ) (hfs : FinSuppZ f) :
    ((Q.card : ℝ))⁻¹ ^ s * ((∑' x : ℤ, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ))
      ≤ boxNormPow s (fun _ : Fin s => Q) S f := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have h1 := Work.Peluse.Peel.diag_iterate (n := n) hn S (fun _ : Fin (n + 1) => Q) f hfs
    (fun _ => hQ)
  have h2 : ((Q.card : ℝ))⁻¹ * ((∑' x : ℤ, (‖f x‖ ^ (2 ^ n)) ^ 2) / (S.card : ℝ))
      ≤ boxNormPow 1 (fun _ : Fin 1 => Q) S (fun x : ℤ => ((‖f x‖ ^ (2 ^ n) : ℝ) : ℂ)) := by
    obtain ⟨N, hN⟩ := hfs
    exact Work.Peluse.Peel.level_one_ge_base Q S (fun x : ℤ => ‖f x‖ ^ (2 ^ n))
      (fun x => pow_nonneg (norm_nonneg _) _)
      (fun x hx => by
        show ((‖f x‖ ^ (2 ^ n) : ℝ) : ℂ) = 0
        rw [hN x hx, norm_zero, zero_pow (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)),
          Complex.ofReal_zero])
  have hprod : (∏ i : Fin n, ((Q.card : ℝ))⁻¹) = ((Q.card : ℝ))⁻¹ ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hstep : ((Q.card : ℝ))⁻¹ ^ n *
      (((Q.card : ℝ))⁻¹ * ((∑' x : ℤ, (‖f x‖ ^ (2 ^ n)) ^ 2) / (S.card : ℝ)))
      ≤ boxNormPow (n + 1) (fun _ : Fin (n + 1) => Q) S f := by
    calc ((Q.card : ℝ))⁻¹ ^ n *
          (((Q.card : ℝ))⁻¹ * ((∑' x : ℤ, (‖f x‖ ^ (2 ^ n)) ^ 2) / (S.card : ℝ)))
        ≤ ((Q.card : ℝ))⁻¹ ^ n *
            boxNormPow 1 (fun _ : Fin 1 => Q) S (fun x : ℤ => ((‖f x‖ ^ (2 ^ n) : ℝ) : ℂ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (∏ i : Fin n, ((Q.card : ℝ))⁻¹) *
            boxNormPow 1 (fun _ : Fin 1 => Q) S (fun x : ℤ => ((‖f x‖ ^ (2 ^ n) : ℝ) : ℂ)) := by
          rw [hprod]
      _ ≤ boxNormPow (n + 1) (fun _ : Fin (n + 1) => Q) S f := h1
  have e1 : (∑' x : ℤ, (‖f x‖ ^ (2 ^ n)) ^ 2) = ∑' x : ℤ, ‖f x‖ ^ (2 ^ (n + 1)) :=
    tsum_congr (fun x => by rw [← pow_mul, ← Nat.pow_succ])
  rw [e1] at hstep
  have e2 : ((Q.card : ℝ))⁻¹ ^ (n + 1) = ((Q.card : ℝ))⁻¹ ^ n * ((Q.card : ℝ))⁻¹ :=
    pow_succ _ _
  rw [e2, mul_assoc]
  exact hstep

/-- **Power-mean and cardinality arithmetic.**  If `u ≥ 0` on `symIcc N₀` (`N₀ ≥ 1`) has mass at
least `δ²N₀/3`, then the normalised `(2^{s-1})`-th power sum of `u` dominates `(δ²/9)^{2^{s-1}}`
for every `s ≥ 2`.  (The constant `1/9` is sharp at `N₀ = 1`, where `|symIcc N₀| = 3 N₀`.) -/
theorem mass_powmean_ratio {N₀ s : ℕ} (hN₀ : 1 ≤ N₀) (hs : 2 ≤ s) {δ : ℝ} (hδ : 0 < δ)
    {u : ℤ → ℝ} (hu : ∀ x : ℤ, 0 ≤ u x)
    (hmass : δ ^ 2 * (N₀ : ℝ) / 3 ≤ ∑ x ∈ symIcc N₀, u x) :
    (δ ^ 2 / 9) ^ (2 ^ (s - 1)) ≤
      (∑ x ∈ symIcc N₀, u x ^ (2 ^ (s - 1))) / (((symIcc N₀).card : ℕ) : ℝ) := by
  have _ := hδ
  set S : Finset ℤ := symIcc N₀ with hSdef
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have hc : 0 < S.card :=
      Finset.card_pos.mpr ⟨0, by rw [hSdef, symIcc, Finset.mem_Icc]; omega⟩
    exact_mod_cast hc
  have hSle : (S.card : ℝ) ≤ 3 * (N₀ : ℝ) := by
    rw [hSdef, card_symIcc']
    have h1 : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    push_cast
    linarith
  have hmass' : δ ^ 2 * (N₀ : ℝ) / 3 ≤ ∑ x ∈ S, u x := by simpa [hSdef] using hmass
  have hr : 1 ≤ 2 ^ (s - 1) := Nat.one_le_two_pow
  have hAratio : δ ^ 2 / 9 ≤ (∑ x ∈ S, u x) / (S.card : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 9) hSpos]
    have h1 : δ ^ 2 * (S.card : ℝ) ≤ δ ^ 2 * (3 * (N₀ : ℝ)) :=
      mul_le_mul_of_nonneg_left hSle (sq_nonneg δ)
    have hA' : δ ^ 2 * (N₀ : ℝ) ≤ 3 * (∑ x ∈ S, u x) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)] at hmass'
      linarith [hmass']
    nlinarith [h1, hA']
  have hpm := Work.Peluse.Peel.powMeanZ S (r := 2 ^ (s - 1)) hr u (fun x _ => hu x)
  have hstep2 : ((∑ x ∈ S, u x) / (S.card : ℝ)) ^ (2 ^ (s - 1))
      ≤ (∑ x ∈ S, u x ^ (2 ^ (s - 1))) / (S.card : ℝ) := by
    rw [div_pow, div_le_div_iff₀ (pow_pos hSpos _) hSpos]
    have he : (S.card : ℝ) ^ (2 ^ (s - 1) - 1) * (S.card : ℝ)
        = (S.card : ℝ) ^ (2 ^ (s - 1)) := by
      rw [← pow_succ, Nat.sub_add_cancel hr]
    calc (∑ x ∈ S, u x) ^ (2 ^ (s - 1)) * (S.card : ℝ)
        ≤ ((S.card : ℝ) ^ (2 ^ (s - 1) - 1) * ∑ x ∈ S, u x ^ (2 ^ (s - 1)))
            * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpm (le_of_lt hSpos)
      _ = (∑ x ∈ S, u x ^ (2 ^ (s - 1)))
            * ((S.card : ℝ) ^ (2 ^ (s - 1) - 1) * (S.card : ℝ)) := by ring
      _ = (∑ x ∈ S, u x ^ (2 ^ (s - 1))) * (S.card : ℝ) ^ (2 ^ (s - 1)) := by rw [he]
  have hstep1 : (δ ^ 2 / 9) ^ (2 ^ (s - 1))
      ≤ ((∑ x ∈ S, u x) / (S.card : ℝ)) ^ (2 ^ (s - 1)) :=
    pow_le_pow_left₀ (by positivity) hAratio _
  exact le_trans hstep1 hstep2

/-- **The small-direction-length (`L²`-mass) bound.**  For a complex `f` supported in `[-N₀,N₀]`
with `ℓ²`-mass at least `δ²N₀/3`, the `2^s`-th power of Peluse's `U^s`-norm at the direction set
`(deg P)!·lc P [L]` (`1 ≤ L ≤ N₀`) is at least `9^{-2^{s-1}} δ^{2^s}/L^s`. -/
theorem elementary_bound_v2 (P : Polynomial ℤ) (s : ℕ) (hs : 2 ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ {N₀ L : ℕ} {f : ℤ → ℂ} {δ : ℝ},
      1 ≤ N₀ → 1 ≤ L → L ≤ N₀ → 0 < δ → Work.Peluse.SupportIn f N₀ →
      δ ^ 2 * (N₀ : ℝ) / 3 ≤ ∑ x ∈ Work.Peluse.symIcc N₀, ‖f x‖ ^ 2 →
      c * δ ^ (2 ^ s) / ((L : ℝ) ^ s) ≤
        Work.Peluse.uNormPow s (Work.Peluse.arithIcc ((P.natDegree.factorial : ℤ) * P.leadingCoeff) L)
          (Work.Peluse.symIcc N₀) f := by
  refine ⟨((9 : ℝ))⁻¹ ^ (2 ^ (s - 1)), by positivity, ?_⟩
  intro N₀ L f δ hN₀ hL hLN hδ hsup hmass
  have _ := hLN
  set Q : Finset ℤ := arithIcc ((P.natDegree.factorial : ℤ) * P.leadingCoeff) L with hQdef
  set S : Finset ℤ := symIcc N₀ with hSdef
  have hfs : FinSuppZ f := ⟨N₀, hsup⟩
  have hQne : Q.Nonempty := by
    refine ⟨((P.natDegree.factorial : ℤ) * P.leadingCoeff), ?_⟩
    rw [hQdef, arithIcc]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩, by simp⟩
  have hQcard : (Q.card : ℝ) ≤ (L : ℝ) := by
    have h1 : Q.card ≤ (Finset.Icc 1 L).card := by
      rw [hQdef, arithIcc]
      exact Finset.card_image_le
    have h2 : (Finset.Icc 1 L).card = L := by
      rw [Nat.card_Icc]; omega
    calc (Q.card : ℝ) ≤ ((Finset.Icc 1 L).card : ℝ) := by exact_mod_cast h1
      _ = (L : ℝ) := by rw [h2]
  have hQpos : (0 : ℝ) < (Q.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hQne
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have hc : 0 < S.card :=
      Finset.card_pos.mpr ⟨0, by rw [hSdef, symIcc, Finset.mem_Icc]; omega⟩
    exact_mod_cast hc
  -- the diagonal peel
  have hcore := uNormPow_tsum_le (s := s) hs Q hQne S f hfs
  have htsum : (∑' x : ℤ, ‖f x‖ ^ (2 ^ s)) = ∑ x ∈ S, ‖f x‖ ^ (2 ^ s) := by
    refine tsum_eq_sum (fun x hx => ?_)
    rw [hSdef] at hx
    rw [hsup x (natAbs_lt_of_not_mem_symIcc' hx), norm_zero,
      zero_pow (pow_ne_zero s (by norm_num : (2 : ℕ) ≠ 0))]
  rw [htsum] at hcore
  -- the power-mean arithmetic
  have hexp : ∀ x : ℤ, (‖f x‖ ^ 2) ^ (2 ^ (s - 1)) = ‖f x‖ ^ (2 ^ s) := by
    intro x
    rw [← pow_mul, show 2 * 2 ^ (s - 1) = 2 ^ s by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]]
  have hpm := mass_powmean_ratio (N₀ := N₀) (s := s) hN₀ hs hδ (u := fun x : ℤ => ‖f x‖ ^ 2)
    (fun x => sq_nonneg _) (by simpa [hSdef] using hmass)
  have hsumexp : (∑ x ∈ symIcc N₀, (‖f x‖ ^ 2) ^ (2 ^ (s - 1)))
      = ∑ x ∈ symIcc N₀, ‖f x‖ ^ (2 ^ s) := Finset.sum_congr rfl (fun x _ => hexp x)
  rw [hsumexp] at hpm
  have hBr : (δ ^ 2 / 9) ^ (2 ^ (s - 1)) ≤ (∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ) := by
    rw [hSdef]; exact hpm
  -- combine
  have hinv : ((L : ℝ) ^ s)⁻¹ ≤ ((Q.card : ℝ)⁻¹) ^ s := by
    rw [inv_pow]
    exact (inv_le_inv₀ (pow_pos hLpos s) (pow_pos hQpos s)).mpr
      (pow_le_pow_left₀ (le_of_lt hQpos) hQcard s)
  have hmain : ((L : ℝ) ^ s)⁻¹ * ((∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ))
      ≤ boxNormPow s (fun _ : Fin s => Q) S f := by
    have hnn : 0 ≤ (∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ) :=
      div_nonneg (Finset.sum_nonneg (fun x _ => pow_nonneg (norm_nonneg _) _)) (le_of_lt hSpos)
    calc ((L : ℝ) ^ s)⁻¹ * ((∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ))
        ≤ ((Q.card : ℝ)⁻¹) ^ s * ((∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hinv hnn
      _ ≤ boxNormPow s (fun _ : Fin s => Q) S f := hcore
  have he : ((9 : ℝ)⁻¹) ^ (2 ^ (s - 1)) * δ ^ (2 ^ s) = (δ ^ 2 / 9) ^ (2 ^ (s - 1)) := by
    rw [div_pow, div_eq_mul_inv, ← pow_mul, show 2 * 2 ^ (s - 1) = 2 ^ s by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)], inv_pow]
    ring
  have hfin : ((9 : ℝ)⁻¹) ^ (2 ^ (s - 1)) * δ ^ (2 ^ s) / ((L : ℝ) ^ s)
      ≤ boxNormPow s (fun _ : Fin s => Q) S f := by
    rw [div_eq_mul_inv, he]
    calc (δ ^ 2 / 9) ^ (2 ^ (s - 1)) * ((L : ℝ) ^ s)⁻¹
        ≤ ((∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ)) * ((L : ℝ) ^ s)⁻¹ :=
          mul_le_mul_of_nonneg_right hBr (by positivity)
      _ = ((L : ℝ) ^ s)⁻¹ * ((∑ x ∈ S, ‖f x‖ ^ (2 ^ s)) / (S.card : ℝ)) := by ring
      _ ≤ boxNormPow s (fun _ : Fin s => Q) S f := hmain
  simpa only [Work.Peluse.uNormPow] using hfin

end

end Work.Peluse.UControl

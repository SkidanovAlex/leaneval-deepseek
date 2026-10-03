/-
# The degenerate-direction case of `Work.Peluse.PET.boxNormPow_control_linear_v2`

The open Peluse target (`Submission/Work/Peluse/PET/boxNormPow_control_linear_v2.lean`) asks, for the
`(m+1)`-linear average along `(x + c_1 y, …, x + c_m y)` (`c_0 = 0`), a lower bound for the `m`-fold
box norm of the last function `F_m` with the shift sets

`Q_i = arithIcc (c_m - c_i)[H]`,  `i = 0, …, m-1`,  `H = ⌊γ' M⌋`,

i.e. the *non-degenerate* direction family `c_m - c_0, …, c_m - c_{m-1}` (the companion statement
`Work.Peluse.PET.boxNormPow_control_linear` treats the family `c_m - c_1, …, c_m - c_m`, which always
contains the degenerate direction `c_m - c_m = 0`).

This file settles the case where the family `Q` *does* contain a degenerate direction, i.e. where
`c i₀ = c_m` for some `i₀ : Fin m`.  Then `Q i₀ = arithIcc 0 H = {0}` (`H ≥ 1`), and the box norm
collapses losslessly to the `(m-1)`-fold box norm of the squared modulus `|F_m|²` over the remaining
directions.  Since `‖F_m‖ ≤ 1` makes `|F_m|²` a *nonnegative real* function, the iterated
Cauchy–Schwarz bound `cs_iterate_ge` and `gamma_le_nine_beta` control that lower-dimensional box
norm by the hypothesis, giving the target with `K = 2^{m-1}`.

## Contents

* `boxSumPow_singleton_apply` / `boxNormPow_singleton_apply`: **the collapse at an arbitrary
  position** — if the `j`-th shift set is `{0}` then the box sum of order `n+1` is the box sum of
  order `n` of `|f|²` over the remaining directions.  It is obtained from the relabelling
  invariance `Work.Peluse.Track.boxSumPow_comp_bij` (the box sum depends on the direction family
  only up to a bijection of the index set, so the degenerate slot can be moved to the end) and the
  last-slot identity `Work.Peluse.PET.boxSumPow_last_singleton`.
* `boxSumPow_v2_direction_collapse` / `boxNormPow_v2_direction_collapse`: the same statement in the
  exact shape of the target's box norm, i.e. the reduction asked for in
  `NOTES_boxNormPow_control_v2.md` (session 4, tile (iii)).
* `boxNormPow_control_linear_v2_of_degenerate_direction`: **the degenerate-direction case of the
  target**, obtained by combining the collapse with the iterated Cauchy–Schwarz bound
  `Work.Peluse.Track.cs_iterate_ge`, the `L²`-mass lower bound `Work.Peluse.PET.gamma_le_nine_beta`
  (`γ/9 ≤ β`) and the direction bound `Work.Peluse.Track.arithIcc_abs_le_any`.
  Since `c 0 = 0` is a standing hypothesis of the target, the instance `i₀ = 0` of it settles the
  case `c_m = 0`.

Note this is precisely the "degenerate-direction collapse" redirection recorded in
`Submission/Work/Peluse/PET/NOTES_boxNormPow_control_v2.md` after the fourth kill
(`Work.Peluse.Track.kill_offdiag_survival`): the gain is re-derived against the diagonal/degenerate
structure, not against off-diagonal coherence.
-/
import Mathlib
import Submission.Work.Peluse.PET.boxNormPow_control_linear
import Submission.Work.Peluse.Track.boxSumPow_comp_bij
import Submission.Work.Peluse.Track.arithIcc_abs_le_any
import Submission.Work.Peluse.Track.cs_iterate_ge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Track

noncomputable section

/-! ## The collapse at an arbitrary position

The box sum is symmetric under a relabelling of the direction family
(`Work.Peluse.Track.boxSumPow_comp_bij`), so the last-slot collapse
`Work.Peluse.PET.boxSumPow_last_singleton` applies at any position. -/

/-- **Degenerate direction in an arbitrary position.**  If the `j`-th shift set is the singleton
`{0}` (`j : Fin (n+1)` arbitrary), the `2^{n+1}`-th box-sum power of `f` of order `n+1` equals the
`2^n`-th box-sum power of the squared modulus `|f|²` of order `n` taken over the remaining
directions `Q (j.succAbove ·)`. -/
theorem boxSumPow_singleton_apply {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (j : Fin (n + 1)) (hj : Q j = {0}) :
    Work.Peluse.boxSumPow (n + 1) Q S f
      = Work.Peluse.boxSumPow n (fun i : Fin n => Q (j.succAbove i)) S
          (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  classical
  -- the relabelling that moves the slot `j` to the end
  set σ : Fin (n + 1) → Fin (n + 1) := Fin.lastCases j (fun i : Fin n => j.succAbove i) with hσdef
  have hσlast : σ (Fin.last n) = j := Fin.lastCases_last
  have hσcast : ∀ i : Fin n, σ i.castSucc = j.succAbove i := fun i => Fin.lastCases_castSucc i
  have hσinj : Function.Injective σ := by
    intro a b hab
    rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨k, rfl⟩ | rfl
      · rw [hσcast i, hσcast k] at hab
        rw [Fin.succAbove_right_injective hab]
      · rw [hσlast, hσcast i] at hab
        exact absurd hab (Fin.succAbove_ne j i)
    · rw [hσlast] at hab
      rcases Fin.eq_castSucc_or_eq_last b with ⟨k, rfl⟩ | rfl
      · rw [hσcast k] at hab
        exact absurd hab.symm (Fin.succAbove_ne j k)
      · rfl
  have hσbij : Function.Bijective σ :=
    ⟨hσinj, (Finite.injective_iff_surjective).mp hσinj⟩
  have h1 : Work.Peluse.boxSumPow (n + 1) Q S f
      = Work.Peluse.boxSumPow (n + 1) (fun i => Q (σ i)) S f :=
    (boxSumPow_comp_bij Q S f σ hσbij).symm
  rw [h1]
  have hlast : (fun i => Q (σ i)) (Fin.last n) = ({0} : Finset ℤ) := by
    show Q (σ (Fin.last n)) = {0}
    rw [hσlast]; exact hj
  rw [Work.Peluse.PET.boxSumPow_last_singleton (fun i => Q (σ i)) S f hlast]
  have hfam : (fun i : Fin n => (fun i => Q (σ i)) i.castSucc)
      = (fun i : Fin n => Q (j.succAbove i)) := by
    funext i
    show Q (σ i.castSucc) = Q (j.succAbove i)
    rw [hσcast i]
  rw [hfam]

/-- The `boxNormPow` form of the arbitrary-position collapse. -/
theorem boxNormPow_singleton_apply {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) (j : Fin (n + 1)) (hj : Q j = {0}) :
    Work.Peluse.boxNormPow (n + 1) Q S f
      = Work.Peluse.boxNormPow n (fun i : Fin n => Q (j.succAbove i)) S
          (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [Work.Peluse.boxNormPow]
  rw [boxSumPow_singleton_apply Q S f j hj]

/-! ## The target's box norm at a degenerate direction

The reduction asked for in `NOTES_boxNormPow_control_v2.md` (session 4, tile (iii)): when the
direction `c_m - c_i₀` degenerates (`c i₀ = c_m`), the box norm of the target is *literally* the
`(m-1)`-fold box norm of `|F_m|²` over the remaining directions — no loss. -/

/-- **The target's box sum collapses at a degenerate direction.**  With `c : Fin (n+2) → ℤ`,
`i₀ : Fin (n+1)` and `c i₀ = c_m` (so the `i₀`-th shift set of the target is
`arithIcc 0 H = {0}` for `H ≥ 1`), the `(n+1)`-fold box sum of the target on the family
`arithIcc (c_m - c_i) H` is the `n`-fold box sum of the squared modulus `|f|²` on the remaining
directions. -/
theorem boxSumPow_v2_direction_collapse {n : ℕ} (H : ℕ) (hH : 1 ≤ H) (c : Fin (n + 2) → ℤ)
    (i₀ : Fin (n + 1)) (hi₀ : c i₀.castSucc = c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow (n + 1)
        (fun i : Fin (n + 1) =>
          Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i.castSucc) H) S f
      = Work.Peluse.boxSumPow n
          (fun k : Fin n =>
            Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
              - c (i₀.succAbove k).castSucc) H)
          S (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  have hQ : (fun i : Fin (n + 1) =>
      Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i.castSucc) H) i₀
      = ({0} : Finset ℤ) := by
    have hd : c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i₀.castSucc = 0 := by rw [hi₀, sub_self]
    simp only [hd]
    exact Work.Peluse.PET.control_linear_arithIcc_zero hH
  exact boxSumPow_singleton_apply _ S f i₀ hQ

/-- The `boxNormPow` form of the collapse at a degenerate direction (the shape of the target's
conclusion). -/
theorem boxNormPow_v2_direction_collapse {n : ℕ} (H : ℕ) (hH : 1 ≤ H) (c : Fin (n + 2) → ℤ)
    (i₀ : Fin (n + 1)) (hi₀ : c i₀.castSucc = c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
    (N : ℕ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow (n + 1)
        (fun i : Fin (n + 1) =>
          Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i.castSucc) H)
        (Work.Peluse.symIcc N) f
      = Work.Peluse.boxNormPow n
          (fun k : Fin n =>
            Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
              - c (i₀.succAbove k).castSucc) H)
          (Work.Peluse.symIcc N) (fun x : ℤ => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
  have hQ : (fun i : Fin (n + 1) =>
      Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i.castSucc) H) i₀
      = ({0} : Finset ℤ) := by
    have hd : c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i₀.castSucc = 0 := by rw [hi₀, sub_self]
    simp only [hd]
    exact Work.Peluse.PET.control_linear_arithIcc_zero hH
  exact boxNormPow_singleton_apply _ (Work.Peluse.symIcc N) f i₀ hQ

/-! ## The degenerate-direction case of the target -/

/-- **The `v2` target when the direction family degenerates.**  If some direction `c i₀` coincides
with `c_m` (`i₀ : Fin m`, so that `arithIcc (c_m - c_{i₀}) H = {0}` for `H ≥ 1`), then the
conclusion of `Work.Peluse.PET.boxNormPow_control_linear_v2` holds, with `K = 2^(m-1)`.

In particular (taking `i₀ = 0`, using the standing hypothesis `c 0 = 0`) this settles the case
`c_m = 0` of the open target. -/
theorem boxNormPow_control_linear_v2_of_degenerate_direction {m : ℕ} (hm : 0 < m) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ / (1000 * (m + 1)) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (∃ i₀ : Fin m, c i₀.castSucc = c ⟨m, Nat.lt_succ_self m⟩) →
      (γ / 1000) ^ K ≤ Work.Peluse.boxNormPow m
        (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc)
          (⌊γ' * (M : ℝ)⌋).toNat) (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨2 ^ n, Nat.one_le_two_pow, ?_⟩
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hγ'le hHge hLam hdeg
  obtain ⟨i₀, hi₀⟩ := hdeg
  set H : ℕ := ⌊γ' * (M : ℝ)⌋.toNat with hHdef
  set Q : Fin (n + 1) → Finset ℤ :=
    fun i => Work.Peluse.arithIcc (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i.castSucc) H with hQdef
  have hH1 : 1 ≤ H := by rw [hHdef]; exact hHge
  -- the degenerate slot
  have hQj : Q i₀ = ({0} : Finset ℤ) := by
    have hd : c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ - c i₀.castSucc = 0 := by rw [hi₀, sub_self]
    simp only [hQdef, hd]
    exact Work.Peluse.PET.control_linear_arithIcc_zero hH1
  set g : ℤ → ℂ := fun x => ((‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2 : ℝ) : ℂ) with hgdef
  set Q' : Fin n → Finset ℤ := fun k => Q (i₀.succAbove k) with hQ'def
  -- the collapse of the degenerate direction
  have hcollapse := boxNormPow_singleton_apply Q (Work.Peluse.symIcc N)
    (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩) i₀ hQj
  -- the hypotheses of the iterated Cauchy-Schwarz bound
  have hQne : ∀ k : Fin n, (Q' k).Nonempty := by
    intro k
    rw [hQ'def, hQdef]
    exact Work.Peluse.PET.control_linear_arithIcc_nonempty hHge
  have hbd : ∀ k : Fin n, ∀ a ∈ Q' k, |a| ≤ (N : ℤ) := by
    intro k a ha
    rw [hQ'def, hQdef] at ha
    exact arithIcc_abs_le_any (m := n + 1) (Nat.succ_pos n) hN hM c hγ hγ1 hγ'
      (by simpa using hγ'le) hcy ((i₀.succAbove k).castSucc) a (by simpa [hHdef] using ha)
  have hsuppg : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → g x = 0 := by
    intro x hx
    have hxN : N < x.natAbs := by
      by_contra hle
      exact hx (by rw [Work.Peluse.symIcc, Finset.mem_Icc]; omega)
    rw [hgdef]
    show ((‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2 : ℝ) : ℂ) = 0
    have h0 : F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x = 0 := hFs _ x hxN
    rw [h0]
    norm_num
  have hrealg : ∀ x : ℤ, g x = ((‖g x‖ : ℝ) : ℂ) := by
    intro x
    have h0 : (0 : ℝ) ≤ ‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2 := sq_nonneg _
    rw [hgdef]
    simp only [Complex.norm_of_nonneg h0]
  -- the iterated Cauchy-Schwarz bound
  have hiter := cs_iterate_ge Q' hN g hQne hbd hsuppg hrealg
  have hmass : (∑ x ∈ Work.Peluse.symIcc N, ‖g x‖)
      = ∑ x ∈ Work.Peluse.symIcc N, ‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hgdef]
    exact Complex.norm_of_nonneg (sq_nonneg _)
  rw [hmass] at hiter
  -- the hypothesis controls the `L²` mass
  have hβ : γ / 9 ≤ (∑ x ∈ Work.Peluse.symIcc N,
        ‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2)
      / (((Work.Peluse.symIcc N).card : ℕ) : ℝ) :=
    Work.Peluse.PET.gamma_le_nine_beta (m := n + 1) (Nat.succ_pos n) hN hM c F hγ hF hFs hLam
  -- the arithmetic
  have hpow := Work.Peluse.PET.pow_div_le (γ := γ)
    (β := (∑ x ∈ Work.Peluse.symIcc N, ‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2)
      / (((Work.Peluse.symIcc N).card : ℕ) : ℝ))
    (n := 2 ^ n) Nat.one_le_two_pow hγ.le hβ
  have h2pos : (0 : ℝ) < 2 ^ (2 ^ n - 1) := by positivity
  have hfinal : (γ / 1000) ^ (2 ^ n) ≤ Work.Peluse.boxNormPow n Q' (Work.Peluse.symIcc N) g := by
    have h1 : ((∑ x ∈ Work.Peluse.symIcc N,
          ‖F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ x‖ ^ 2)
        / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ n) / 2 ^ (2 ^ n - 1)
        ≤ Work.Peluse.boxNormPow n Q' (Work.Peluse.symIcc N) g := by
      rw [div_le_iff₀ h2pos]
      simpa [mul_comm] using hiter
    exact le_trans hpow h1
  simp only [hQdef, hHdef] at hcollapse ⊢
  rw [hcollapse]
  exact hfinal

end

end Work.Peluse.Track

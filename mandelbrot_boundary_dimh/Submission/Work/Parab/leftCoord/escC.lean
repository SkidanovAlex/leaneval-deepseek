import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.leftCoord.extension
import Submission.Work.Parab.leftCoord.psi_injOn

/-!
# The closed extension of a Fatou coordinate

`extension.lean` extends a local Fatou coordinate `ψ` (with `ψ (G x) = ψ x + 1` on the
half-plane `{Re > N}`) to the escaping set `Esc N G` constructed from the *strict* predicate
`Good N G x n`, which demands that the real parts of `G^0 x, …, G^(n-1) x` are `< N`
**strictly**.

That strictness makes `Esc N G` miss exactly the points whose orbit passes through the level `N`
exactly (`(G^k x).re = N` for some `k`).  For the left chart coordinate this is a genuine loss:
the preimage, under the Fatou coordinate, of a point of Shishikura's sector `QLeft` can be such a
boundary point, so a coordinate built on `Esc` alone would not be surjective onto the sector.

Here we define the *closed* variant

`GoodC N G x n := (∀ k ≤ n, N < ‖G^[k] x‖) ∧ N < (G^[n] x).re`,

which keeps the condition that the orbit stays outside the disc of radius `N` until the entry
index but drops the strict conditions on the earlier real parts.  For the *minimal* witness the
latter are automatic (`re_le_of_lt_nIdxC`: the minimal witness is the first index at which the
orbit enters `{Re > N}`), and the resulting extension `PsiC` has all the properties of `Psi`:
it satisfies the Abel equation (`PsiC_abel`), is holomorphic and injective on its domain
(`PsiC_differentiableOn`, `PsiC_injOn`), is given by the explicit formula `ψ (G^n ·) - n` on the
open set `goodSetC N G n`, and agrees with `Psi` on the smaller set `Esc N G` (`PsiC_eq_Psi`).
-/

open Classical

namespace Work.Parab.leftCoord

open Set Filter Metric
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {N : ℝ} {G ψ : ℂ → ℂ} {x y : ℂ} {k n : ℕ}

/-- The closed version of `Good`: the orbit stays outside the disc of radius `N` up to step `n`,
and at step `n` the real part exceeds `N`.  No condition is imposed on the earlier real parts. -/
def GoodC (N : ℝ) (G : ℂ → ℂ) (x : ℂ) (n : ℕ) : Prop :=
  (∀ k ≤ n, N < ‖G^[k] x‖) ∧ N < (G^[n] x).re

/-- The domain of the closed extension. -/
def EscC (N : ℝ) (G : ℂ → ℂ) : Set ℂ := {x | ∃ n, GoodC N G x n}

/-- The first index at which the orbit enters `{Re > N}` (the minimal `GoodC` witness). -/
noncomputable def nIdxC (N : ℝ) (G : ℂ → ℂ) (x : ℂ) : ℕ :=
  if h : ∃ n, GoodC N G x n then Nat.find h else 0

/-- The closed extension of `ψ`. -/
noncomputable def PsiC (N : ℝ) (G : ℂ → ℂ) (ψ : ℂ → ℂ) (x : ℂ) : ℂ :=
  ψ (G^[nIdxC N G x] x) - (nIdxC N G x : ℂ)

/-- The open set on which the closed extension is given by the explicit formula
`ψ (G^[n] ·) - n`. -/
def goodSetC (N : ℝ) (G : ℂ → ℂ) (n : ℕ) : Set ℂ :=
  {x | (∀ k ≤ n, N < ‖G^[k] x‖) ∧ N < (G^[n] x).re}

lemma mem_goodSetC_iff : x ∈ goodSetC N G n ↔ GoodC N G x n := Iff.rfl

lemma mem_EscC_iff : x ∈ EscC N G ↔ ∃ n, GoodC N G x n := Iff.rfl

/-- The strict predicate implies the closed one (with the same index). -/
lemma goodC_of_good (h : Good N G x n) : GoodC N G x n := ⟨h.1, h.2.2⟩

lemma Esc_subset_EscC (hx : Esc N G x) : EscC N G x :=
  ⟨nIdx N G x, goodC_of_good (nIdx_spec hx)⟩

/-- Points which already have real part `> N` are in `EscC` with index `0`. -/
lemma GoodC.zero (h : N < x.re) : GoodC N G x 0 := by
  refine ⟨?_, by simpa using h⟩
  intro k hk
  rw [Nat.le_zero.mp hk, Function.iterate_zero_apply]
  exact lt_of_lt_of_le h (Complex.re_le_norm x)

lemma nIdxC_spec (h : EscC N G x) : GoodC N G x (nIdxC N G x) := by
  obtain ⟨n, hn⟩ := h
  unfold nIdxC
  rw [dif_pos ⟨n, hn⟩]
  exact Nat.find_spec ⟨n, hn⟩

lemma nIdxC_le (h : GoodC N G x n) : nIdxC N G x ≤ n := by
  unfold nIdxC
  rw [dif_pos ⟨n, h⟩]
  exact Nat.find_min' ⟨n, h⟩ h

lemma PsiC_apply : PsiC N G ψ x = ψ (G^[nIdxC N G x] x) - (nIdxC N G x : ℂ) := rfl

/-- The minimal witness of `GoodC` is the first index at which the orbit enters `{Re > N}`: in
particular the real parts before the entry index are `≤ N`. -/
lemma re_le_of_lt_nIdxC (hx : EscC N G x) {k : ℕ} (hk : k < nIdxC N G x) :
    (G^[k] x).re ≤ N := by
  by_contra hcon
  push_neg at hcon
  have hgood : GoodC N G x k :=
    ⟨fun j hj => (nIdxC_spec hx).1 j (le_trans hj (le_of_lt hk)), hcon⟩
  exact absurd (nIdxC_le hgood) (not_le.mpr hk)

/-- From the entry index on, the real parts along the orbit of a point of `EscC` stay `> N`. -/
lemma re_gt_of_nIdxC (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re) (hx : EscC N G x) :
    ∀ k, nIdxC N G x ≤ k → N < (G^[k] x).re := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact (nIdxC_spec hx).2
  | succ k hk ih =>
      have hnorm : N < ‖G^[k] x‖ := lt_of_lt_of_le ih (Complex.re_le_norm _)
      have hle := hmono (G^[k] x) hnorm
      rw [← Function.iterate_succ_apply' G k x] at hle
      exact lt_of_lt_of_le ih hle

/-- Every iterate of a point of `EscC` has norm `> N`. -/
lemma norm_gt_of_EscC (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re) (hx : EscC N G x) :
    ∀ k, N < ‖G^[k] x‖ := by
  intro k
  rcases lt_or_ge (nIdxC N G x) k with hlt | hge
  · exact lt_of_lt_of_le (re_gt_of_nIdxC hmono hx k (le_of_lt hlt)) (Complex.re_le_norm _)
  · exact (nIdxC_spec hx).1 k hge

lemma EscC_map (hG : ∀ x, N < x.re → N < (G x).re) (hx : EscC N G x) :
    EscC N G (G x) := by
  by_cases h0 : nIdxC N G x = 0
  · have hxN : N < x.re := by
      have h := (nIdxC_spec hx).2
      rw [h0] at h
      simpa using h
    exact ⟨0, GoodC.zero (hG x hxN)⟩
  · have hnpos : 0 < nIdxC N G x := Nat.pos_of_ne_zero h0
    refine ⟨nIdxC N G x - 1, ?_, ?_⟩
    · intro k hk
      have hk' : k + 1 ≤ nIdxC N G x := by omega
      have h := (nIdxC_spec hx).1 (k + 1) hk'
      rwa [← iterate_shift] at h
    · have hs : nIdxC N G x - 1 + 1 = nIdxC N G x := Nat.sub_add_cancel (by omega)
      have h := (nIdxC_spec hx).2
      rw [← hs] at h
      rwa [← iterate_shift] at h

lemma EscC_iterate (hG : ∀ x, N < x.re → N < (G x).re) (hx : EscC N G x) (k : ℕ) :
    EscC N G (G^[k] x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact EscC_map hG ih

/-- **Abel equation for the closed extension.** -/
lemma PsiC_abel (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1) (hx : EscC N G x) :
    PsiC N G ψ (G x) = PsiC N G ψ x + 1 := by
  by_cases h0 : nIdxC N G x = 0
  · have hxN : N < x.re := by
      have h := (nIdxC_spec hx).2
      rw [h0] at h
      simpa using h
    have hGxN : N < (G x).re := hG x hxN
    have h0' : nIdxC N G (G x) = 0 :=
      le_antisymm (nIdxC_le (GoodC.zero hGxN)) (Nat.zero_le _)
    rw [PsiC_apply, PsiC_apply, h0, h0']
    simpa using habel x hxN
  · set n := nIdxC N G x with hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero h0
    have hspec : GoodC N G x n := by rw [hn]; exact nIdxC_spec hx
    have hgoodG : GoodC N G (G x) (n - 1) := by
      refine ⟨?_, ?_⟩
      · intro k hk
        have hk' : k + 1 ≤ n := by omega
        have h := hspec.1 (k + 1) hk'
        rwa [← iterate_shift] at h
      · have hs : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        have h := hspec.2
        rw [← hs] at h
        rwa [← iterate_shift] at h
    have hle : nIdxC N G (G x) ≤ n - 1 := nIdxC_le hgoodG
    have hge : n - 1 ≤ nIdxC N G (G x) := by
      by_contra hcon
      push_neg at hcon
      have hspec' := nIdxC_spec (EscC_map hG hx)
      have hgoodx : GoodC N G x (nIdxC N G (G x) + 1) := by
        refine ⟨?_, ?_⟩
        · intro k hk
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            simpa using hspec.1 0 (Nat.zero_le n)
          · have hk1 : k - 1 ≤ nIdxC N G (G x) := by omega
            have hkk : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
            have h := hspec'.1 (k - 1) hk1
            rwa [iterate_shift, hkk] at h
        · have h := hspec'.2
          rwa [iterate_shift] at h
      have hcontra := nIdxC_le hgoodx
      rw [← hn] at hcontra
      omega
    have heq : nIdxC N G (G x) = n - 1 := le_antisymm hle hge
    have hiter : G^[n - 1] (G x) = G^[n] x := by
      rw [iterate_shift, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have hcast : ((n : ℕ) : ℂ) = ((n - 1 : ℕ) : ℂ) + 1 := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      push_cast
      ring
    rw [PsiC_apply, PsiC_apply, heq, ← hn, hiter, hcast]
    ring

/-- Iterating the Abel equation from a point whose orbit has all real parts `> N`. -/
lemma psi_iterate_abelC (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1) {y : ℂ} {m : ℕ}
    (hre : ∀ j : ℕ, N < (G^[j] (G^[m] y)).re) (k : ℕ) :
    ψ (G^[k] (G^[m] y)) = ψ (G^[m] y) + (k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hre' : N < (G^[k] (G^[m] y)).re := hre k
      rw [Function.iterate_succ_apply', habel _ hre', ih]
      push_cast
      ring

/-- For any `K` beyond the entry index, `ψ` at the `K`-th iterate of `x` equals `PsiC x + K`. -/
lemma psiC_iterate_ge (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hx : EscC N G x) {K : ℕ} (hK : nIdxC N G x ≤ K) :
    ψ (G^[K] x) = PsiC N G ψ x + (K : ℂ) := by
  set n := nIdxC N G x with hn
  have hψn : ψ (G^[n] x) = PsiC N G ψ x + (n : ℂ) := by
    rw [PsiC_apply, ← hn]
    ring
  have hre : ∀ j : ℕ, N < (G^[j] (G^[n] x)).re := by
    intro j
    rw [← Function.iterate_add_apply]
    exact re_gt_of_nIdxC hmono hx _ (Nat.le_add_left n j)
  have h1 : G^[K] x = G^[K - n] (G^[n] x) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hK]
  have h2 : ψ (G^[K - n] (G^[n] x)) = ψ (G^[n] x) + ((K - n : ℕ) : ℂ) :=
    psi_iterate_abelC habel hre (K - n)
  have hcast : ((K : ℕ) : ℂ) = ((n : ℕ) : ℂ) + ((K - n : ℕ) : ℂ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hK]
  rw [h1, h2, hψn, hcast]
  ring

/-- The closed extension satisfies the Abel equation along the whole orbit. -/
lemma PsiC_iterate (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1) (hx : EscC N G x) (k : ℕ) :
    PsiC N G ψ (G^[k] x) = PsiC N G ψ x + (k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', PsiC_abel hG habel (EscC_iterate hG hx k), ih]
      push_cast
      ring

/-- On `Esc N G` the closed extension agrees with the strict one. -/
lemma nIdxC_eq_nIdx (hx : Esc N G x) : nIdxC N G x = nIdx N G x := by
  have hspec := nIdx_spec hx
  have hC : GoodC N G x (nIdx N G x) := goodC_of_good hspec
  refine le_antisymm (nIdxC_le hC) ?_
  by_contra hcon
  push_neg at hcon
  have hCs := nIdxC_spec ⟨nIdx N G x, hC⟩
  exact absurd hCs.2 (not_lt.mpr (le_of_lt (hspec.2.1 _ hcon)))

lemma PsiC_eq_Psi (hx : Esc N G x) : PsiC N G ψ x = Psi N G ψ x := by
  rw [PsiC_apply, Psi_apply, nIdxC_eq_nIdx hx]

/-- **The explicit formula on `goodSetC`.**  On the set `goodSetC N G n` the closed extension is
`ψ (G^n ·) - n`. -/
lemma PsiC_eq_on_goodSetC (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hy : y ∈ goodSetC N G n) : PsiC N G ψ y = ψ (G^[n] y) - (n : ℂ) := by
  have hex : ∃ k, N < (G^[k] y).re := ⟨n, hy.2⟩
  set m := Nat.find hex with hm
  have hmle : m ≤ n := Nat.find_min' hex hy.2
  have hmre : N < (G^[m] y).re := Nat.find_spec hex
  have hspec : GoodC N G y m := ⟨fun j hj => hy.1 j (le_trans hj hmle), hmre⟩
  have hmidx : nIdxC N G y = m := by
    refine le_antisymm (nIdxC_le hspec) ?_
    exact Nat.find_min' hex (nIdxC_spec ⟨m, hspec⟩).2
  have hiter : ∀ j : ℕ, N < (G^[j] (G^[m] y)).re := by
    intro j
    induction j with
    | zero => simpa using hmre
    | succ j ih =>
        have hnorm : N < ‖G^[j] (G^[m] y)‖ := lt_of_lt_of_le ih (Complex.re_le_norm _)
        have hle := hmono (G^[j] (G^[m] y)) hnorm
        rw [← Function.iterate_succ_apply' G j (G^[m] y)] at hle
        exact lt_of_lt_of_le ih hle
  have hpsi : ψ (G^[n] y) = ψ (G^[m] y) + ((n - m : ℕ) : ℂ) := by
    have h1 : G^[n] y = G^[n - m] (G^[m] y) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmle]
    rw [h1]
    exact psi_iterate_abelC habel hiter (n - m)
  have hcast : ((n : ℕ) : ℂ) = ((m : ℕ) : ℂ) + ((n - m : ℕ) : ℂ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hmle]
  rw [PsiC_apply, hmidx, hpsi, hcast]
  ring

/-- The iterates of `G` are continuous at `x` as long as the orbit up to step `n` stays in
`{N < ‖·‖}`, where `G` is differentiable. -/
lemma continuousAt_iterateC (hGd : ∀ x, N < ‖x‖ → DifferentiableAt ℂ G x)
    (hnorm : ∀ k ≤ n, N < ‖G^[k] x‖) : ∀ k ≤ n, ContinuousAt (fun y => G^[k] y) x := by
  intro k
  induction k with
  | zero => intro _; exact continuousAt_id
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
    have hcont : ContinuousAt (fun y => G^[k] y) x := ih hk'
    have hmem : N < ‖G^[k] x‖ := hnorm k hk'
    have hcomp : ContinuousAt (G ∘ fun y => G^[k] y) x :=
      (hGd _ hmem).continuousAt.comp hcont
    simpa only [Function.iterate_succ'] using hcomp

/-- The iterates of `G` are differentiable at `x` as long as the orbit up to step `n` stays in
`{N < ‖·‖}`, where `G` is differentiable. -/
lemma differentiableAt_iterateC (hGd : ∀ x, N < ‖x‖ → DifferentiableAt ℂ G x)
    (hnorm : ∀ k ≤ n, N < ‖G^[k] x‖) : ∀ k ≤ n, DifferentiableAt ℂ (fun y => G^[k] y) x := by
  intro k
  induction k with
  | zero => intro _; exact differentiableAt_id
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
    have hd : DifferentiableAt ℂ (fun y => G^[k] y) x := ih hk'
    have hmem : N < ‖G^[k] x‖ := hnorm k hk'
    have hcomp : DifferentiableAt ℂ (G ∘ fun y => G^[k] y) x :=
      (hGd _ hmem).comp x hd
    simpa only [Function.iterate_succ'] using hcomp

/-- Membership in `goodSetC` is stable under small perturbations. -/
lemma eventually_mem_goodSetC (hGd : ∀ x, N < ‖x‖ → DifferentiableAt ℂ G x)
    (hnorm : ∀ k ≤ n, N < ‖G^[k] x‖) (hre : N < (G^[n] x).re) :
    ∀ᶠ y in 𝓝 x, y ∈ goodSetC N G n := by
  have hcont : ∀ k ≤ n, ContinuousAt (fun y => G^[k] y) x := continuousAt_iterateC hGd hnorm
  have h1 : ∀ᶠ y in 𝓝 x, ∀ k ≤ n, N < ‖G^[k] y‖ := by
    have h1' : ∀ᶠ y in 𝓝 x, ∀ k ∈ Finset.range (n + 1), N < ‖G^[k] y‖ := by
      rw [Filter.eventually_all_finset]
      intro k hk
      have hk' : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      exact ContinuousAt.eventually_lt continuousAt_const (hcont k hk').norm (hnorm k hk')
    exact h1'.mono fun y hy k hk => hy k (Finset.mem_range.mpr (by omega))
  have h2 : ∀ᶠ y in 𝓝 x, N < (G^[n] y).re :=
    ContinuousAt.eventually_lt continuousAt_const
      (Complex.continuous_re.continuousAt.comp (hcont n le_rfl)) hre
  exact (h1.and h2).mono fun y hy => ⟨hy.1, hy.2⟩

/-- `goodSetC` is open. -/
lemma isOpen_goodSetC (hGd : ∀ x, N < ‖x‖ → DifferentiableAt ℂ G x) (n : ℕ) :
    IsOpen (goodSetC N G n) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact eventually_mem_goodSetC hGd hx.1 hx.2

/-- **Holomorphy of the closed extension.** -/
theorem PsiC_differentiableOn {G ψ : ℂ → ℂ} {N : ℝ}
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hGd : ∀ x, N < ‖x‖ → DifferentiableAt ℂ G x)
    (hψ : DifferentiableOn ℂ ψ {x : ℂ | N < x.re}) :
    DifferentiableOn ℂ (PsiC N G ψ) (EscC N G) := by
  intro x hx
  have hspec : GoodC N G x (nIdxC N G x) := nIdxC_spec hx
  have hev : PsiC N G ψ =ᶠ[𝓝 x]
      fun y => ψ (G^[nIdxC N G x] y) - ((nIdxC N G x : ℕ) : ℂ) :=
    (eventually_mem_goodSetC hGd hspec.1 hspec.2).mono fun y hy =>
      PsiC_eq_on_goodSetC (N := N) (G := G) (ψ := ψ) (n := nIdxC N G x) habel hmono hy
  have hdiff : DifferentiableAt ℂ
      (fun y => ψ (G^[nIdxC N G x] y) - ((nIdxC N G x : ℕ) : ℂ)) x := by
    have hiter : DifferentiableAt ℂ (fun y => G^[nIdxC N G x] y) x :=
      differentiableAt_iterateC hGd hspec.1 (nIdxC N G x) le_rfl
    have hψat : DifferentiableAt ℂ ψ (G^[nIdxC N G x] x) :=
      hψ.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspec.2)
    exact (hψat.comp x hiter).sub_const _
  exact (hdiff.congr_of_eventuallyEq hev).differentiableWithinAt

/-- **Injectivity of the closed extension.** -/
theorem PsiC_injOn {G ψ : ℂ → ℂ} {N : ℝ}
    (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hψinj : Set.InjOn ψ {x : ℂ | N < x.re})
    (hGinj : Set.InjOn G {x : ℂ | N < ‖x‖}) :
    Set.InjOn (PsiC N G ψ) (EscC N G) := by
  intro x hx y hy hxy
  have heq : G^[max (nIdxC N G x) (nIdxC N G y)] x
      = G^[max (nIdxC N G x) (nIdxC N G y)] y := by
    have hKx : ψ (G^[max (nIdxC N G x) (nIdxC N G y)] x)
        = PsiC N G ψ x + ((max (nIdxC N G x) (nIdxC N G y) : ℕ) : ℂ) :=
      psiC_iterate_ge hG habel hmono hx (le_max_left _ _)
    have hKy : ψ (G^[max (nIdxC N G x) (nIdxC N G y)] y)
        = PsiC N G ψ y + ((max (nIdxC N G x) (nIdxC N G y) : ℕ) : ℂ) :=
      psiC_iterate_ge hG habel hmono hy (le_max_right _ _)
    have hreKx : N < (G^[max (nIdxC N G x) (nIdxC N G y)] x).re :=
      re_gt_of_nIdxC hmono hx _ (le_max_left _ _)
    have hreKy : N < (G^[max (nIdxC N G x) (nIdxC N G y)] y).re :=
      re_gt_of_nIdxC hmono hy _ (le_max_right _ _)
    apply hψinj hreKx hreKy
    rw [hKx, hKy, hxy]
  exact eq_of_iterate_eq (N := N) (G := G) hGinj
    (fun k _ => norm_gt_of_EscC hmono hx k) (fun k _ => norm_gt_of_EscC hmono hy k) heq

/-- Points with real part `> N` are in `EscC` with index `0`, where the closed extension agrees
with `ψ`. -/
lemma PsiC_eq_of_re (h : N < x.re) : PsiC N G ψ x = ψ x := by
  have h0 : nIdxC N G x = 0 := le_antisymm (nIdxC_le (GoodC.zero h)) (Nat.zero_le _)
  simp [PsiC_apply, h0]

/-- `EscC` is open. -/
lemma isOpen_EscC (hGd : ∀ x, N < ‖x‖ → DifferentiableAt ℂ G x) : IsOpen (EscC N G) := by
  rw [show EscC N G = ⋃ n, goodSetC N G n by
    ext x
    simp only [Set.mem_iUnion, mem_EscC_iff, mem_goodSetC_iff]]
  exact isOpen_iUnion fun n => isOpen_goodSetC hGd n

/-- **The telescoping identity** underlying the asymptotic expansion of the closed extension:
for `x ∈ EscC` and any `J` with `N < (G^[J] x).re`,
`PsiC x - approxCoord x = ∑_{k<J} (approxCoord (G^{k+1} x) - approxCoord (G^k x) - 1)
  + (ψ (G^J x) - approxCoord (G^J x))`. -/
lemma PsiC_sub_approx_eq_sum {c : ℂ} (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hx : EscC N G x) {J : ℕ} (hJ : N < (G^[J] x).re) :
    PsiC N G ψ x - Work.FatouCoord.approxCoord c x
      = (∑ k ∈ Finset.range J,
          (Work.FatouCoord.approxCoord c (G^[k+1] x)
            - Work.FatouCoord.approxCoord c (G^[k] x) - 1))
        + (ψ (G^[J] x) - Work.FatouCoord.approxCoord c (G^[J] x)) := by
  have hnJ : nIdxC N G x ≤ J := by
    by_contra hcon
    push_neg at hcon
    exact absurd hJ (not_lt.mpr (re_le_of_lt_nIdxC hx hcon))
  have hΨJ : PsiC N G ψ x = ψ (G^[J] x) - (J : ℂ) := by
    rw [psiC_iterate_ge hG habel hmono hx hnJ]
    ring
  have h1 : (∑ k ∈ Finset.range J,
        (Work.FatouCoord.approxCoord c (G^[k+1] x)
          - Work.FatouCoord.approxCoord c (G^[k] x) - 1))
      = (Work.FatouCoord.approxCoord c (G^[J] x)
          - Work.FatouCoord.approxCoord c (G^[0] x)) - (J : ℂ) := by
    rw [Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun k => Work.FatouCoord.approxCoord c (G^[k] x)) J]
    simp
  rw [hΨJ, h1, Function.iterate_zero_apply]
  ring

end Work.Parab.leftCoord

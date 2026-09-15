import Submission.Work.KvnBoundary
import Submission.Commons.Combinatorics.Transference.energy_step_core

import Submission.Commons.Combinatorics.Transference.exists_terminate_of_energy

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Furstenberg tower of Green–Tao §7 (abstract form)

Green–Tao's proof of the generalised Koopman–von Neumann structure theorem
(Proposition 8.1 / 7.1) runs an algorithm: starting from the trivial σ-algebra `B_0` and the
empty exceptional set `Ω_0`, at each stage one adjoins to `B_K` the level sets of the dual
function `𝒟F_{K+1}` of the residual `F_{K+1} = (1 - 1_{Ω_K})(f - 𝔼(f|B_K))`, and replaces `Ω_K`
by a slightly larger exceptional set.  If `‖F_{K+1}‖_{U^{k-1}}` is still larger than
`ε^{1/2^k}` then the `L²` energy of `𝔼(f|B_K)` increases by a definite amount `c`, and the
energy is bounded by `(1+τ)²|G|`; hence the algorithm must terminate within
`⌈(1+τ)²|G|/c⌉ + 1` steps.

This file formalises the *iteration* abstractly: the state of the algorithm is
`(n, G, α, T, Ω, ρ)` (number of generators, generators, shifts, boundary sets, exceptional
set, accumulated exceptional mass), and the single-step property is a hypothesis
(`hstep`) — it is discharged by `energy_step_core` once the analytic input
(`bohr_sigma_atom_gen`, i.e. the `bohr-sigma` estimate) is available.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

/-- The state of the Furstenberg tower: number `n` of generators, the generators `G j`, the
shifts `α j`, the boundary sets `T j`, the exceptional set `Ω`, and the accumulated bound `ρ`
on the `(ν+1)`-mass of `Ω`. -/
structure KvnSt (p : ℕ) [Fact p.Prime] where
  n : ℕ
  G : ℕ → ZMod p → ℝ
  α : ℕ → ℝ
  T : ℕ → Finset (ZMod p)
  Ω : Finset (ZMod p)
  ρ : ℝ

namespace KvnSt

variable {p : ℕ} [Fact p.Prime]

/-- The σ-algebra `B_n` attached to the state: the join of the level-set σ-algebras of the
scaled dual functions `𝒟(G j/(2C))`, `j < n`. -/
noncomputable def B (d : ℕ) (C ε : ℝ) (s : KvnSt p) : ZMod p → Finset (ZMod p) :=
  kpart d C ε s.n s.G s.α

/-- The energy `‖(1 - 1_Ω)𝔼(f|B_n)‖²_{L²}` of the state. -/
noncomputable def energy (f : ZMod p → ℝ) (d : ℕ) (C ε : ℝ) (s : KvnSt p) : ℝ :=
  ∑ x ∈ Finset.univ \ s.Ω, (cE (B d C ε s) f x) ^ 2

/-- The residual `F_{n+1} = (1 - 1_Ω)(f - 𝔼(f|B_n))` of the state. -/
noncomputable def residual (f : ZMod p → ℝ) (d : ℕ) (C ε : ℝ) (s : KvnSt p) : ZMod p → ℝ :=
  fun x => if x ∈ s.Ω then 0 else f x - cE (B d C ε s) f x

/-- Termination: the residual is Gowers-uniform at scale `ε^{1/2^k}` (i.e.
`‖residual‖_{U^d}^{2^d} ≤ gr`). -/
noncomputable def term (f : ZMod p → ℝ) (d : ℕ) (C ε gr : ℝ) (s : KvnSt p) : Prop :=
  Unorm d (residual f d C ε s) ^ (2 ^ d) ≤ gr

/-- The invariant maintained by the algorithm. -/
def Inv (d : ℕ) (C ε τ η ρs : ℝ) (ν : ZMod p → ℝ) (s : KvnSt p) : Prop :=
  (∀ x, x ∈ B d C ε s x) ∧
  (∀ x y : ZMod p, y ∈ B d C ε s x → B d C ε s y = B d C ε s x) ∧
  (∀ x ∈ s.Ω, B d C ε s x ⊆ s.Ω) ∧
  (0 ≤ ρs ∧ s.ρ ≤ (s.n + 1) * ρs ∧ ∑ x ∈ s.Ω, (ν x + 1) ≤ s.ρ) ∧
  (∀ x : ZMod p, x ∉ s.Ω → |cE (B d C ε s) (fun y => ν y - 1) x| ≤ τ) ∧
  (∀ j < s.n, ∀ x : ZMod p, |s.G j x| ≤ C * (ν x + 1)) ∧
  (∀ j : ℕ, 0 ≤ s.α j) ∧
  (∀ j : ℕ, s.α j < ε) ∧
  (∀ j < s.n, ∑ y ∈ s.T j, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1)) ∧
  (∀ j < s.n, ∀ y : ZMod p,
    (∃ m : ℤ, |(davg d (fun z => s.G j z / (2 * C)) y - s.α j) / ε - m| ≤ η) → y ∈ s.T j)

end KvnSt

open KvnSt

/-- **The Furstenberg tower terminates.**  If the initial state satisfies the invariant, the
energy of every invariant state is at most `cBnd`, and every non-terminated invariant state with
fewer than `K₀` generators can be advanced to a state with `n` increased by one and energy
increased by `c > 0`, then some invariant state is terminated.

The bound `s.n < K₀` on the single step is essential: the atom count `#B_n` grows like
`(const)^n`, so the analytic smallness conditions of Green–Tao §7 can only be verified for
states with `n < K₀` (and indeed the tower never visits larger states, because the energy
argument forces termination within `K₀` steps). -/
theorem kvn_tower {p : ℕ} [Fact p.Prime]
    (d : ℕ) (C ε τ η ρs gr c cBnd : ℝ) (ν f : ZMod p → ℝ)
    (hc : 0 < c) {K₀ : ℕ} (hK₀ : cBnd < (K₀ : ℝ) * c)
    (s0 : KvnSt p) (h0 : Inv d C ε τ η ρs ν s0) (hn0 : s0.n = 0)
    (henergy : ∀ s : KvnSt p, Inv d C ε τ η ρs ν s → KvnSt.energy f d C ε s ≤ cBnd)
    (hstep : ∀ s : KvnSt p, Inv d C ε τ η ρs ν s → s.n < K₀ → ¬ KvnSt.term f d C ε gr s →
      ∃ s' : KvnSt p, Inv d C ε τ η ρs ν s' ∧ s'.n = s.n + 1 ∧
        KvnSt.energy f d C ε s' ≥ KvnSt.energy f d C ε s + c) :
    ∃ s : KvnSt p, Inv d C ε τ η ρs ν s ∧ s.n ≤ K₀ ∧ KvnSt.term f d C ε gr s := by
  classical
  -- the (total) one-step transition, which only moves states with `Inv` and `n < K₀`
  let next : KvnSt p → KvnSt p := fun s =>
    if _h : Inv d C ε τ η ρs ν s ∧ s.n < K₀ then
      if _h2 : ¬ KvnSt.term f d C ε gr s then
        Classical.choose (hstep s _h.1 _h.2 _h2) else s
    else s
  let it : ℕ → KvnSt p := fun K => Nat.rec s0 (fun _ s => next s) K
  have hnext_eq : ∀ K : ℕ, it (K + 1) = next (it K) := fun K => rfl
  have hspec : ∀ s : KvnSt p, ∀ (hs : Inv d C ε τ η ρs ν s) (hlt : s.n < K₀)
      (hnt : ¬ KvnSt.term f d C ε gr s),
      Inv d C ε τ η ρs ν (next s) ∧ (next s).n = s.n + 1 ∧
        KvnSt.energy f d C ε (next s) ≥ KvnSt.energy f d C ε s + c := by
    intro s hs hlt hnt
    have hval : next s = Classical.choose (hstep s hs hlt hnt) := by
      dsimp only [next]
      rw [dif_pos ⟨hs, hlt⟩, dif_pos hnt]
    rw [hval]
    exact ⟨(Classical.choose_spec (hstep s hs hlt hnt)).1,
      (Classical.choose_spec (hstep s hs hlt hnt)).2.1,
      (Classical.choose_spec (hstep s hs hlt hnt)).2.2⟩
  have hfreeze_term : ∀ s : KvnSt p, KvnSt.term f d C ε gr s → next s = s := by
    intro s ht
    by_cases hs : Inv d C ε τ η ρs ν s ∧ s.n < K₀
    · dsimp only [next]; rw [dif_pos hs, dif_neg (fun h2 => h2 ht)]
    · dsimp only [next]; rw [dif_neg hs]
  have hfreeze_bad : ∀ s : KvnSt p, ¬ (Inv d C ε τ η ρs ν s ∧ s.n < K₀) → next s = s := by
    intro s hs
    dsimp only [next]; rw [dif_neg hs]
  -- the number of generators never exceeds the step index
  have hnle : ∀ K : ℕ, K ≤ K₀ → (it K).n ≤ K := by
    intro K
    induction K with
    | zero => intro _; rw [show it 0 = s0 from rfl, hn0]
    | succ K ih =>
        intro hK
        have hle : K ≤ K₀ := by omega
        have hIK := ih hle
        rw [hnext_eq K]
        by_cases h : Inv d C ε τ η ρs ν (it K) ∧ (it K).n < K₀
        · by_cases h2 : KvnSt.term f d C ε gr (it K)
          · rw [hfreeze_term (it K) h2]; omega
          · have := (hspec (it K) h.1 h.2 h2).2.1
            omega
        · rw [hfreeze_bad (it K) h]; omega
  have hinv : ∀ K : ℕ, K ≤ K₀ → Inv d C ε τ η ρs ν (it K) := by
    intro K
    induction K with
    | zero => intro _; rw [show it 0 = s0 from rfl]; exact h0
    | succ K ih =>
        intro hK
        have hle : K ≤ K₀ := by omega
        have hIK := ih hle
        rw [hnext_eq K]
        by_cases h : Inv d C ε τ η ρs ν (it K) ∧ (it K).n < K₀
        · by_cases h2 : KvnSt.term f d C ε gr (it K)
          · rw [hfreeze_term (it K) h2]; exact hIK
          · exact (hspec (it K) h.1 h.2 h2).1
        · rw [hfreeze_bad (it K) h]; exact hIK
  have hstepE : ∀ K < K₀, ¬ KvnSt.term f d C ε gr (it K) →
      KvnSt.energy f d C ε (it (K + 1)) ≥ KvnSt.energy f d C ε (it K) + c := by
    intro K hK hnt
    have hle : K ≤ K₀ := le_of_lt hK
    rw [hnext_eq K]
    have hn : (it K).n < K₀ := lt_of_le_of_lt (hnle K hle) hK
    exact (hspec (it K) (hinv K hle) hn hnt).2.2
  have hboundE : ∀ K ≤ K₀, KvnSt.energy f d C ε (it K) ≤ cBnd :=
    fun K hK => henergy (it K) (hinv K hK)
  have hzero : 0 ≤ KvnSt.energy f d C ε (it 0) :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  obtain ⟨K, hK, hterm⟩ := exists_terminate_of_energy (E := fun K => KvnSt.energy f d C ε (it K))
    (P := fun K => KvnSt.term f d C ε gr (it K)) hc hK₀ hstepE hboundE hzero
  exact ⟨it K, hinv K (le_of_lt hK), le_trans (hnle K (le_of_lt hK)) (le_of_lt hK), hterm⟩

end GTTrans

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

variable {p : ℕ} [Fact p.Prime]

/-- **The concrete single step of the Furstenberg tower.**  Given an invariant state `s`, a
shift `αnew`, a boundary set `Tnew`, the analytic data (`M`, `εraw`, `δ`, `θ`, `B`, `γ₀`, `ρ`)
and the smallness hypotheses making the correlation positive and the energy increment definite,
the algorithm can be advanced by one step: the new state (with one more generator, the residual
`(1-1_Ω)(f - 𝔼(f|B_s))`) is again invariant and its energy increases by at least `c`.

The construction of the new exceptional set and the energy estimate are `energy_step_core`; the
atom-mass bound `hAtom` is the analytic input supplied by `bohr_sigma_atom_gen`. -/
theorem step_exists_data {d : ℕ} (hd : 1 ≤ d)
    (C ε η τ : ℝ) (hε : 0 < ε)
    (ν f : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (s : KvnSt p) {ρs : ℝ} (hInv : KvnSt.Inv d C ε τ η ρs ν s)
    (αnew : ℝ) (hαnew0 : 0 ≤ αnew) (hαnewε : αnew < ε)
    (Tnew : Finset (ZMod p))
    (hTnew : ∀ y : ZMod p,
      (∃ m : ℤ, |(davg d (fun z => KvnSt.residual f d C ε s z / (2 * C)) y - αnew) / ε - m| ≤ η)
        → y ∈ Tnew)
    (hTnew_mass : ∑ y ∈ Tnew, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1))
    {Mraw εraw δ θ B γ₀ : ℝ} (hMpos : 0 < Mraw) (hεraw : 0 < εraw)
    (hMb : ∀ x, |davg d (KvnSt.residual f d C ε s) x| ≤ Mraw)
    (hQcl : ∀ x y : ZMod p,
      y ∈ kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew x →
        |davg d (KvnSt.residual f d C ε s) y - davg d (KvnSt.residual f d C ε s) x| ≤ εraw)
    (hθ : 0 < θ) (hδ0 : 0 ≤ δ) (hB0 : 0 ≤ B) (hγ0 : 0 ≤ γ₀)
    (hδθ : δ < (Fintype.card (ZMod p) : ℝ) * θ)
    (hAtom : ∀ x, |∑ y ∈ kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew x,
      (ν y - 1)| ≤ δ)
    (hAbound : ∀ x, x ∉ s.Ω → |cE (KvnSt.B d C ε s) f x| ≤ B)
    (hUb : γ₀ ≤ Unorm d (KvnSt.residual f d C ε s) ^ (2 ^ d))
    (hρs : (Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ)
        ≤ ρs)
    (hγpos : Mraw * ((1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ) + (s.n + 1) * ρs))
        + εraw * (∑ x, |KvnSt.residual f d C ε s x|)
        ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2)
    (hτ : 2 * δ / ((Fintype.card (ZMod p) : ℝ) * θ - δ) ≤ τ)
    (hCgen : 1 + B ≤ C)
    {c : ℝ}
    (hsmall : (3 * B ^ 2 + 2 * B) *
        ((Fintype.card (ZMod p) : ℝ) * θ *
          ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ) + (s.n + 1) * ρs)
        + c ≤ ((Fintype.card (ZMod p) : ℝ) * γ₀ / 2) ^ 2 /
            ((Fintype.card (ZMod p) : ℝ) * Mraw ^ 2)) :
    ∃ s' : KvnSt p, KvnSt.Inv d C ε τ η ρs ν s' ∧ s'.n = s.n + 1 ∧
      KvnSt.energy f d C ε s' ≥ KvnSt.energy f d C ε s + c := by
  classical
  haveI : Nonempty (ZMod p) := ⟨0⟩
  obtain ⟨hBmem, hBeq, hΩsat, hρsdata, hcE_old, hGbound, hα0, hαε, hTmass, hTcov⟩ := hInv
  obtain ⟨hρs0, hρsle, hmass_old⟩ := hρsdata
  have hmass : ∑ x ∈ s.Ω, (ν x + 1) ≤ (s.n + 1) * ρs := le_trans hmass_old hρsle
  set P : ZMod p → Finset (ZMod p) := KvnSt.B d C ε s with hPdef
  set Fnew : ZMod p → ℝ := KvnSt.residual f d C ε s with hFdef
  set Q : ZMod p → Finset (ZMod p) := kpartExt d C ε s.n s.G s.α Fnew αnew with hQdef
  have hPmem : ∀ x, x ∈ P x := hBmem
  have hPeq : ∀ x y : ZMod p, y ∈ P x → P y = P x := hBeq
  have hQmem : ∀ x, x ∈ Q x := by
    intro x; rw [hQdef]; exact kpartExt_mem_self d C ε s.n s.G s.α Fnew αnew x
  have hQeq : ∀ x y : ZMod p, y ∈ Q x → Q y = Q x := by
    intro x y hy; rw [hQdef] at hy ⊢; exact kpartExt_eq_of_mem d C ε s.n s.G s.α Fnew αnew hy
  have href : ∀ x, Q x ⊆ P x := by
    intro x; rw [hQdef, hPdef]
    exact kpartExt_subset_kpart d C ε s.n s.G s.α Fnew αnew x
  have hFnew_0 : ∀ x ∈ s.Ω, Fnew x = 0 := by
    intro x hx; rw [hFdef]; simp only [KvnSt.residual, if_pos hx]
  have hFnew_out : ∀ x, x ∉ s.Ω → Fnew x = f x - cE P f x := by
    intro x hx; rw [hFdef, hPdef]; simp only [KvnSt.residual, if_neg hx]
  obtain ⟨Ω', hsub, hsat, hmass', hcE, henergy⟩ :=
    energy_step_core (d := d) hd P Q hPmem hPeq hQmem hQeq href s.Ω hΩsat ν hν f hf0 hfν
      Fnew hFnew_0 hFnew_out hMpos hεraw hMb hQcl hθ hδ0 hB0 hγ0 hδθ hAtom hAbound hUb
      hmass hγpos
  have hFnew_bound : ∀ x, |Fnew x| ≤ C * (ν x + 1) := by
    intro x
    have hle : |Fnew x| ≤ (1 + B) * (ν x + 1) := by
      by_cases hx : x ∈ s.Ω
      · rw [hFnew_0 x hx]
        have h1 : (0 : ℝ) ≤ (1 + B) * (ν x + 1) := by have := hν x; nlinarith
        rw [abs_zero]; exact h1
      · rw [hFnew_out x hx]
        have hab := hAbound x hx
        have h4 : cE P f x ≤ B := (abs_le.mp hab).2
        have h5 : -(cE P f x) ≤ B := by linarith [(abs_le.mp hab).1]
        rw [abs_le]
        constructor
        · nlinarith [hf0 x, h4, hB0, hν x]
        · nlinarith [hfν x, h5, hB0, hν x]
    nlinarith [hle, hν x, hCgen]
  let s' : KvnSt p := ⟨s.n + 1, Function.update s.G s.n Fnew, Function.update s.α s.n αnew,
      Function.update s.T s.n Tnew, Ω', (s.n + 2) * ρs⟩
  have hs'G : s'.G = Function.update s.G s.n Fnew := rfl
  have hs'α : s'.α = Function.update s.α s.n αnew := rfl
  set X : ℝ := (Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ)
    + (s.n + 1) * ρs with hXdef
  set Z : ℝ := (3 * B ^ 2 + 2 * B) * X with hZdef
  set c0 : ℝ := ((Fintype.card (ZMod p) : ℝ) * γ₀ / 2) ^ 2 /
      ((Fintype.card (ZMod p) : ℝ) * Mraw ^ 2) with hc0def
  refine ⟨s', ?_, rfl, ?_⟩
  · -- verify the invariant
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; exact kpart_mem_self d C ε (s.n + 1) _ _ x
    · intro x y hy; exact kpart_eq_of_mem d C ε (s.n + 1) _ _ hy
    · intro x hx; exact hsat x hx
    · refine ⟨hρs0, ?_, ?_⟩
      · have hn' : s'.n = s.n + 1 := rfl
        have hρ' : s'.ρ = (s.n + 2) * ρs := rfl
        rw [hρ', hn']
        push_cast
        exact le_of_eq (by ring)
      · show ∑ x ∈ Ω', (ν x + 1) ≤ (s.n + 2) * ρs
        linarith [hmass', hρs]
    · intro x hx
      exact le_trans (hcE x hx) hτ
    · intro j hj x
      show |(Function.update s.G s.n Fnew) j x| ≤ C * (ν x + 1)
      by_cases hje : j = s.n
      · subst hje; rw [Function.update_self]; exact hFnew_bound x
      · rw [Function.update_of_ne hje]
        exact hGbound j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) (fun h => hje (h ▸ rfl))) x
    · intro j
      show 0 ≤ (Function.update s.α s.n αnew) j
      by_cases hje : j = s.n
      · subst hje; rw [Function.update_self]; exact hαnew0
      · rw [Function.update_of_ne hje]; exact hα0 j
    · intro j
      show (Function.update s.α s.n αnew) j < ε
      by_cases hje : j = s.n
      · subst hje; rw [Function.update_self]; exact hαnewε
      · rw [Function.update_of_ne hje]; exact hαε j
    · intro j hj
      show ∑ y ∈ (Function.update s.T s.n Tnew) j, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1)
      by_cases hje : j = s.n
      · subst hje; rw [Function.update_self]; exact hTnew_mass
      · rw [Function.update_of_ne hje]
        exact hTmass j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) (fun h => hje (h ▸ rfl)))
    · intro j hj y hy
      show y ∈ (Function.update s.T s.n Tnew) j
      by_cases hje : j = s.n
      · subst hje
        rw [hs'G, hs'α] at hy
        rw [Function.update_self, Function.update_self] at hy
        rw [Function.update_self]
        exact hTnew y hy
      · rw [hs'G, hs'α] at hy
        rw [Function.update_of_ne hje, Function.update_of_ne hje] at hy
        rw [Function.update_of_ne hje]
        exact hTcov j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) (fun h => hje (h ▸ rfl))) y hy
  · -- energy increment
    have henergy' : KvnSt.energy f d C ε s + c0 ≤ KvnSt.energy f d C ε s'
          + B ^ 2 * ((Ω' \ s.Ω).card : ℝ)
          + 2 * B * ((1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ *
              ((Finset.univ.image Q).card : ℝ) + (s.n + 1) * ρs)) := by
      rw [hc0def]
      have h := henergy
      simp only [KvnSt.energy, KvnSt.B, hPdef, hQdef] at h ⊢
      exact h
    have hcard : ((Ω' \ s.Ω).card : ℝ) ≤ X := by
      have h1 : ((Ω' \ s.Ω).card : ℝ) ≤ (Ω'.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
      have h2 : (Ω'.card : ℝ) ≤ ∑ x ∈ Ω', (ν x + 1) := by
        have h3 : ∀ x ∈ Ω', (1 : ℝ) ≤ ν x + 1 := fun x _ => by have := hν x; linarith
        calc (Ω'.card : ℝ) = ∑ _x ∈ Ω', (1 : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ ∑ x ∈ Ω', (ν x + 1) := Finset.sum_le_sum h3
      have h4 : ∑ x ∈ Ω', (ν x + 1) ≤ X := by linarith [hmass']
      linarith
    have hc0 : Z + c ≤ c0 := by
      rw [hZdef, hXdef, hc0def]
      exact hsmall
    have hXle : (Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + (s.n + 1) * ρs
        = X := hXdef.symm
    have h5 : B ^ 2 * ((Ω' \ s.Ω).card : ℝ) + 2 * B * ((1 + B) *
        ((Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + (s.n + 1) * ρs))
        ≤ Z := by
      have h1 : B ^ 2 * ((Ω' \ s.Ω).card : ℝ) ≤ B ^ 2 * X :=
        mul_le_mul_of_nonneg_left hcard (sq_nonneg B)
      have h2 : B ^ 2 * X + 2 * B * ((1 + B) * X) = Z := by rw [hZdef]; ring
      calc B ^ 2 * ((Ω' \ s.Ω).card : ℝ) + 2 * B * ((1 + B) *
              ((Fintype.card (ZMod p) : ℝ) * θ * ((Finset.univ.image Q).card : ℝ) + (s.n + 1) * ρs))
          = B ^ 2 * ((Ω' \ s.Ω).card : ℝ) + 2 * B * ((1 + B) * X) := by rw [hXle]
        _ ≤ B ^ 2 * X + 2 * B * ((1 + B) * X) := by linarith
        _ = Z := h2
    have hmain : KvnSt.energy f d C ε s' + Z ≥ KvnSt.energy f d C ε s + c0 := by
      linarith [henergy', h5]
    linarith [hmain, hc0]

end GTTrans

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

variable {p : ℕ} [Fact p.Prime]

/-- The data supplied by the analytic `bohr-sigma` estimate at a state `s` of the tower: a shift
`αnew` and boundary set `Tnew` (from the pigeonhole), the sup-norm bound `Mraw` for the dual
function of the residual (from the linear forms condition), the atom-mass bound `δ` (from
`bohr_sigma_atom_gen`), the threshold `θ`, the constants `B`, `γ₀` and the two quantitative
smallness conditions which hold for `p` suitably large: the atom count `N θ #atoms` is at most
`ρs`, positivity of the correlation (`hγpos`) and domination of the `O(η)` errors by the energy
increment (`hsmall`).

The parameter `ρs` is the per-step bound on the total `(ν+1)`-mass of the exceptional set: the
state invariant records `∑_{s.Ω}(ν+1) ≤ (s.n+1) ρs`, which grows linearly in the number of
generators (as it must). -/
def KvnSt.small (d : ℕ) (C ε η τ c ρs : ℝ) (ν f : ZMod p → ℝ) (s : KvnSt p) : Prop :=
  ∃ (αnew : ℝ) (Tnew : Finset (ZMod p)) (Mraw εraw δ θ B γ₀ : ℝ),
    0 ≤ αnew ∧ αnew < ε ∧
    (∀ y : ZMod p,
      (∃ m : ℤ, |(davg d (fun z => KvnSt.residual f d C ε s z / (2 * C)) y - αnew) / ε
        - (m : ℝ)| ≤ η) → y ∈ Tnew) ∧
    (∑ y ∈ Tnew, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1)) ∧
    0 < Mraw ∧ 0 < εraw ∧
    (∀ x, |davg d (KvnSt.residual f d C ε s) x| ≤ Mraw) ∧
    (∀ x y : ZMod p,
      y ∈ kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew x →
        |davg d (KvnSt.residual f d C ε s) y - davg d (KvnSt.residual f d C ε s) x| ≤ εraw) ∧
    0 < θ ∧ 0 ≤ δ ∧ 0 ≤ B ∧ 0 ≤ γ₀ ∧
    δ < (Fintype.card (ZMod p) : ℝ) * θ ∧
    (∀ x, |∑ y ∈ kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew x,
      (ν y - 1)| ≤ δ) ∧
    (∀ x, x ∉ s.Ω → |cE (KvnSt.B d C ε s) f x| ≤ B) ∧
    γ₀ ≤ Unorm d (KvnSt.residual f d C ε s) ^ (2 ^ d) ∧
    ((Fintype.card (ZMod p) : ℝ) * θ *
        ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ)
      ≤ ρs) ∧
    (Mraw * ((1 + B) * ((Fintype.card (ZMod p) : ℝ) * θ *
        ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ)
        + (s.n + 1) * ρs))
      + εraw * (∑ x, |KvnSt.residual f d C ε s x|) ≤ (Fintype.card (ZMod p) : ℝ) * γ₀ / 2) ∧
    (2 * δ / ((Fintype.card (ZMod p) : ℝ) * θ - δ) ≤ τ) ∧
    1 + B ≤ C ∧
    ((3 * B ^ 2 + 2 * B) * ((Fintype.card (ZMod p) : ℝ) * θ *
        ((Finset.univ.image (kpartExt d C ε s.n s.G s.α (KvnSt.residual f d C ε s) αnew)).card : ℝ)
        + (s.n + 1) * ρs) + c
      ≤ ((Fintype.card (ZMod p) : ℝ) * γ₀ / 2) ^ 2 /
          ((Fintype.card (ZMod p) : ℝ) * Mraw ^ 2))

/-- **Green–Tao Proposition 8.1 (generalised Koopman–von Neumann structure theorem)**, reduced to
the analytic smallness hypothesis `KvnSt.small`.  Under the tower invariants, the bound on the
energy, and the availability of the `bohr-sigma` data at every non-terminated state with fewer
than `K₀` generators, the Furstenberg algorithm terminates and yields a σ-algebra `B` together
with an exceptional set `Ω` such that `Ω` is `B`-saturated, `∑_Ω(ν+1) ≤ (n+1)ρs`,
`|𝔼(ν-1|B)| ≤ τ` outside `Ω`, and the residual `(1 - 1_Ω)(f - 𝔼(f|B))` is Gowers-uniform at
scale `gr`. -/
theorem kvn_decomp {d : ℕ} (hd : 1 ≤ d) (C ε η τ c gr cBnd : ℝ) (hε : 0 < ε)
    (ν f : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (s0 : KvnSt p) {ρs : ℝ} (h0 : KvnSt.Inv d C ε τ η ρs ν s0) (hn0 : s0.n = 0)
    (hc : 0 < c) {K₀ : ℕ} (hK₀ : cBnd < (K₀ : ℝ) * c)
    (henergy : ∀ s : KvnSt p, KvnSt.Inv d C ε τ η ρs ν s → KvnSt.energy f d C ε s ≤ cBnd)
    (hsmall : ∀ s : KvnSt p, KvnSt.Inv d C ε τ η ρs ν s → s.n < K₀ →
      ¬ KvnSt.term f d C ε gr s → KvnSt.small d C ε η τ c ρs ν f s) :
    ∃ s : KvnSt p, KvnSt.Inv d C ε τ η ρs ν s ∧ s.n ≤ K₀ ∧ KvnSt.term f d C ε gr s :=
  kvn_tower d C ε τ η ρs gr c cBnd ν f hc hK₀ s0 h0 hn0 henergy
    (fun s hInv hn hnt => by
      obtain ⟨αnew, Tnew, Mraw, εraw, δ, θ, B, γ₀,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21⟩ := hsmall s hInv hn hnt
      exact step_exists_data (d := d) hd C ε η τ hε ν f hν hf0 hfν s hInv αnew h1 h2 Tnew h3 h4
        (Mraw := Mraw) (εraw := εraw) (δ := δ) (θ := θ) (B := B) (γ₀ := γ₀)
        h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)

end GTTrans

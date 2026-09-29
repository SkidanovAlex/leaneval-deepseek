import Mathlib
import Submission.Work.Resample.buKit

/-!
# `Work.Resample.buMFromParams`: the window half-width `m = egM p α` from the parameters

The one-dimensional `B̃` resampling word (`Work.Resample.buPrep`) is parameterised by
`p, α, s, t`, and the Gaussian half-width used by the `Ẽ` step is

`egM p α = √p / (2α) + 1`   (`Work.Resample.sliceB1defs`).

This module proves that this value can be computed from the four parameters in time polynomial
in `p`:

`∃ prog K, ∀ main p α s t …, Pipe main prog [p,α,s,t] [egM p α, p, α, s, t] (K·(p+1)^K)`.

The program is the straight-line chain

`roll 1 ; dup ; dup ; add ; roll 2 ; dup ; sqrt ; roll 2 ; swap ; tdiv ; push 1 ; add`

which first duplicates `α` twice and adds to get `2α` (keeping a copy of `α`), then duplicates `p`
and takes its integer square root, brings `2α` next to it, divides (truncated division of
non-negative integers = natural division) and adds `1`.  Every value occurring is an integer of at
most `2p+2` bits, and every step touches only values of that size: the rolls are at depth `≤ 2`, so
`s` and `t` (which are not polynomially bounded by `p`) are never looked at.

The cost accounting uses `Pipe.chain_buMFromParams` (chaining the twelve steps along the thirteen windows) with
the uniform per-step budget `Kc·(p+1)^4`, where `Kc` is the sum of the twelve library constants.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## Chaining a list of words along a list of windows

(This is the same construction as in `Work.Resample.auPrep`; it is reproduced here so that the
module is self-contained.) -/

/-- The program `[p₁, …, pₙ]` sequenced in order. -/
private def chainProg (ps : List Cmd) : Cmd := ps.foldr Cmd.seq .skip

private theorem chainProg_nil : chainProg ([] : List Cmd) = .skip := rfl

private theorem chainProg_cons (p : Cmd) (ps : List Cmd) : chainProg (p :: ps) = .seq p (chainProg ps) := rfl

theorem Pipe.skip {main : Cmd} {A : List Val} : Pipe main .skip A A 1 := by
  intro rest vs hvs s R hR
  refine ⟨A ++ rest, s, 1, rfl, Eval.skip s, le_rfl, ?_, ?_⟩
  · rw [← hvs]; exact hR
  · intro k hk; rfl

/-- Chaining words along a list of windows: if `ws = [W₀, …, Wₙ]`, `ps = [p₁, …, pₙ]` and
`pᵢ : Wᵢ → W_{i+1}` costs at most `cb`, then `chainProg ps : W₀ → Wₙ` costs at most `n·cb + 1`. -/
theorem Pipe.chain_buMFromParams {main : Cmd} (ps : List Cmd) (ws : List (List Val)) (cb : ℕ)
    (hlen : ws.length = ps.length + 1)
    (h : ∀ i, i < ps.length →
      Pipe main (ps.getD i .skip) (ws.getD i []) (ws.getD (i + 1) []) cb) :
    Pipe main (chainProg ps) (ws.getD 0 []) (ws.getD ps.length []) (ps.length * cb + 1) := by
  induction ps generalizing ws with
  | nil =>
    have hlen1 : ws.length = 1 := by simpa using hlen
    obtain ⟨w, hw⟩ : ∃ w, ws = [w] := by
      cases ws with
      | nil => simp at hlen1
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t2 => simp at hlen1
    rw [hw]
    simpa [chainProg_nil] using (Pipe.skip (main := main) (A := w))
  | cons p ps ih =>
    cases ws with
    | nil => simp at hlen
    | cons w0 ws' =>
      have hlen' : ws'.length = ps.length + 1 := by simpa using hlen
      have hstep : Pipe main p w0 (ws'.getD 0 []) cb := by
        have h0 := h 0 (by simp)
        simpa using h0
      have hrest : ∀ i, i < ps.length →
          Pipe main (ps.getD i .skip) (ws'.getD i []) (ws'.getD (i + 1) []) cb := by
        intro i hi
        have h1 := h (i + 1) (by simp; omega)
        simpa using h1
      have ihh := ih ws' hlen' hrest
      have hcomp : Pipe main (Cmd.seq p (chainProg ps)) w0 (ws'.getD ps.length [])
          (cb + (ps.length * cb + 1)) := Pipe.comp hstep ihh
      have hcost : cb + (ps.length * cb + 1) ≤ (ps.length + 1) * cb + 1 := by ring_nf; omega
      have hres := Pipe.le hcomp hcost
      simp only [chainProg_cons, List.length_cons, List.getD_cons_zero, List.getD_cons_succ]
      exact hres

/-! ## Sizes of the values occurring in the program -/

theorem buM_isz_natCast_le (n : ℕ) : isz ((n : ℤ)) ≤ n + 2 := by
  simp only [isz, Int.natAbs_natCast]
  have h : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  omega

theorem buM_alpha_le (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) : α ≤ p := by
  have h1 : α ≤ α ^ 2 := by
    calc α = α * 1 := by ring
      _ ≤ α * α := Nat.mul_le_mul_left α (by omega)
      _ = α ^ 2 := by ring
  omega

theorem buM_szα (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) : isz ((α : ℤ)) ≤ p + 2 := by
  have h := buM_isz_natCast_le α
  have h2 := buM_alpha_le p α hα hαp
  omega

theorem buM_sz2α (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) :
    isz (((2 * α : ℕ) : ℤ)) ≤ 2 * p + 2 := by
  have h := buM_isz_natCast_le (2 * α)
  have h2 := buM_alpha_le p α hα hαp
  omega

theorem buM_szsqrt (p : ℕ) : isz (((Nat.sqrt p : ℕ) : ℤ)) ≤ p + 2 := by
  have h := buM_isz_natCast_le (Nat.sqrt p)
  have h2 := Nat.sqrt_le_self p
  omega

theorem buM_szq (p α : ℕ) :
    isz (Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ))) ≤ p + 2 := by
  rw [(Int.ofNat_tdiv (Nat.sqrt p) (2 * α)).symm]
  simp only [isz, Int.natAbs_natCast]
  have h1 : (Nat.sqrt p / (2 * α)).size ≤ Nat.sqrt p / (2 * α) :=
    Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))
  have h2 : Nat.sqrt p / (2 * α) ≤ p := le_trans (Nat.div_le_self _ _) (Nat.sqrt_le_self p)
  omega

theorem buM_sz1 : isz (1 : ℤ) ≤ 3 := by simp only [isz]; norm_num

/-! ## The per-step budget `(p+1)^4` -/

theorem buM_lin_le {p X : ℕ} (hp : 100 ≤ p) (hX : X ≤ 40 * p + 100) : X ≤ (p + 1) ^ 4 := by
  have h1 : 40 * p + 100 ≤ (p + 1) ^ 2 := by nlinarith [sq_nonneg (p : ℤ)]
  have h2 : (p + 1) ^ 2 ≤ (p + 1) ^ 4 := by
    have h3 : (p + 1) ^ 2 * (p + 1) ^ 2 = (p + 1) ^ 4 := by ring
    calc (p + 1) ^ 2 = (p + 1) ^ 2 * 1 := by ring
      _ ≤ (p + 1) ^ 2 * (p + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
      _ = (p + 1) ^ 4 := h3
  omega

theorem buM_prod_le {p X Y : ℕ} (hp : 100 ≤ p) (hX : X ≤ 2 * p + 2) (hY : Y ≤ 2 * p + 2) :
    X * Y ≤ (p + 1) ^ 4 := by
  have h1 : X * Y ≤ (2 * p + 2) * (2 * p + 2) := Nat.mul_le_mul hX hY
  have h1' : (2 * p + 2) * (2 * p + 2) = (2 * p + 2) ^ 2 := by ring
  have h3 : (2 * p + 2) ^ 2 ≤ ((p + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left (by nlinarith [sq_nonneg (p : ℤ)]) 2
  have h4 : ((p + 1) ^ 2) ^ 2 = (p + 1) ^ 4 := by ring
  omega

theorem buM_sq_le {p X : ℕ} (hp : 100 ≤ p) (hX : X ≤ 2 * p + 2) : X ^ 2 ≤ (p + 1) ^ 4 := by
  have h1 : X ^ 2 ≤ (2 * p + 2) ^ 2 := Nat.pow_le_pow_left hX 2
  have h3 : (2 * p + 2) ^ 2 ≤ ((p + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left (by nlinarith [sq_nonneg (p : ℤ)]) 2
  have h4 : ((p + 1) ^ 2) ^ 2 = (p + 1) ^ 4 := by ring
  omega

/-! ## The final value and the final cost arithmetic -/

theorem buM_val_eq (p α : ℕ) :
    (1 : ℤ) + Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ)) =
      ((Work.Resample.egM p α : ℕ) : ℤ) := by
  rw [(Int.ofNat_tdiv (Nat.sqrt p) (2 * α)).symm, Work.Resample.egM]
  omega

theorem buM_toNat (p : ℕ) : ((p : ℤ).toNat) = p := Int.toNat_natCast p

theorem buM_cost_final (Kc p : ℕ) (hp : 100 ≤ p) :
    12 * (Kc * (p + 1) ^ 4) + 1 ≤ max (12 * Kc + 1) 5 * (p + 1) ^ (max (12 * Kc + 1) 5) := by
  have h1 : 12 * (Kc * (p + 1) ^ 4) + 1 ≤ (12 * Kc + 1) * (p + 1) ^ 4 := by
    have h2 : (1 : ℕ) ≤ (p + 1) ^ 4 := Nat.one_le_pow 4 (p + 1) (by omega)
    have h3 : 12 * (Kc * (p + 1) ^ 4) = 12 * Kc * (p + 1) ^ 4 := by ring
    have h4 : (12 * Kc + 1) * (p + 1) ^ 4 = 12 * Kc * (p + 1) ^ 4 + (p + 1) ^ 4 := by ring
    omega
  have h5 : (12 * Kc + 1) ≤ max (12 * Kc + 1) 5 := le_max_left _ _
  have h6 : (p + 1) ^ 4 ≤ (p + 1) ^ (max (12 * Kc + 1) 5) :=
    Nat.pow_le_pow_right (by omega) (le_trans (by norm_num : 4 ≤ 5) (le_max_right _ _))
  calc 12 * (Kc * (p + 1) ^ 4) + 1 ≤ (12 * Kc + 1) * (p + 1) ^ 4 := h1
    _ ≤ max (12 * Kc + 1) 5 * (p + 1) ^ (max (12 * Kc + 1) 5) := Nat.mul_le_mul h5 h6

set_option maxHeartbeats 8000000 in
/-- `egM p α = ⌊√p/(2α)⌋ + 1` is computable from `p, α` (and `s, t`) in time polynomial in `p`. -/
theorem buMFromParams (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main prog
        [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)]
        ([HvdH.Val.int ((Work.Resample.egM p α : ℕ) : ℤ)] ++
          [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)])
        (K * (p + 1) ^ K) := by
  obtain ⟨pushProg, Kpush, hPush⟩ := KL.pushVal
  obtain ⟨dupProg, Kdup, hDup⟩ := KL.dup
  obtain ⟨rollProg, Kroll, hRoll⟩ := KL.roll
  obtain ⟨swapProg, Kswap, hSwap⟩ := KL.swap
  obtain ⟨sqrtProg, Ksqrt, hSqrt⟩ := IL.sqrt
  obtain ⟨tdivProg, Ktdiv, hTdiv⟩ := IL.tdiv
  obtain ⟨addProg, Kadd, hAdd⟩ := IL.add
  set Kc : ℕ := Kpush + Kdup + Kroll + Kswap + Ksqrt + Ktdiv + Kadd + 1 with hKcdef
  refine ⟨chainProg [rollProg 1, dupProg, dupProg, addProg, rollProg 2, dupProg, sqrtProg, rollProg 2,
      swapProg, tdivProg, pushProg (Val.int (1 : ℤ)), addProg], max (12 * Kc + 1) 5, ?_⟩
  intro main p α s t hs hst hα hp htp hαp
  let pv : Val := Val.int (p : ℤ)
  let av : Val := Val.int (α : ℤ)
  let sv : Val := Val.int (s : ℤ)
  let tv : Val := Val.int (t : ℤ)
  let b2 : Val := Val.int (((2 * α : ℕ) : ℤ))
  let rv : Val := Val.int (((Nat.sqrt p : ℕ) : ℤ))
  let qv : Val := Val.int (Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ)))
  let ev : Val := Val.int (1 : ℤ)
  let mv : Val := Val.int ((1 : ℤ) + Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ)))
  have hszp : isz (p : ℤ) ≤ 2 * p + 2 := by have h := buM_isz_natCast_le p; omega
  have hszα : isz (α : ℤ) ≤ 2 * p + 2 := by have h := buM_szα p α hα hαp; omega
  have hsz2α : isz (((2 * α : ℕ) : ℤ)) ≤ 2 * p + 2 := buM_sz2α p α hα hαp
  have hszr : isz (((Nat.sqrt p : ℕ) : ℤ)) ≤ 2 * p + 2 := by have h := buM_szsqrt p; omega
  have hszq : isz (Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ))) ≤ 2 * p + 2 := by
    have h := buM_szq p α; omega
  have hsz1 : isz (1 : ℤ) ≤ 2 * p + 2 := le_trans buM_sz1 (by omega)
  have hne : (((2 * α : ℕ) : ℤ)) ≠ 0 := by
    have h : 0 < 2 * α := by omega
    omega
  refine Pipe.rw (Pipe.le (Pipe.chain_buMFromParams
      [rollProg 1, dupProg, dupProg, addProg, rollProg 2, dupProg, sqrtProg, rollProg 2, swapProg,
        tdivProg, pushProg (Val.int (1 : ℤ)), addProg]
      [[pv,av,sv,tv], [av,pv,sv,tv], [av,av,pv,sv,tv], [av,av,av,pv,sv,tv], [b2,av,pv,sv,tv],
       [pv,b2,av,sv,tv], [pv,pv,b2,av,sv,tv], [rv,pv,b2,av,sv,tv], [b2,rv,pv,av,sv,tv],
       [rv,b2,pv,av,sv,tv], [qv,pv,av,sv,tv], [ev,qv,pv,av,sv,tv], [mv,pv,av,sv,tv]]
      (Kc * (p + 1) ^ 4) (by simp) ?_) (buM_cost_final Kc p hp)) ?_
  · intro i hi
    have hi' : i < 12 := hi
    interval_cases i
    · -- roll 1
      refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [pv, av, sv, tv]) (k := 1)
        (by simp)) (by simp)) (by
        rw [Nat.mul_assoc]
        refine Nat.mul_le_mul (show Kroll ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [pv, av, sv, tv]
        rw [show List.take (1 + 1) [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ),
              Val.int (t : ℤ)] = ([Val.int (p : ℤ), Val.int (α : ℤ)] : List Val) from rfl]
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- dup (α)
      refine Pipe.le (Pipe.appendTail [pv, sv, tv] (Pipe.dup main hDup av)) (by
        refine Nat.mul_le_mul (show Kdup ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [av]
        rw [Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- dup (α)
      refine Pipe.le (Pipe.appendTail [av, pv, sv, tv] (Pipe.dup main hDup av)) (by
        refine Nat.mul_le_mul (show Kdup ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [av]
        rw [Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- add : α + α = 2α
      have hstep : Pipe main addProg ([av, av] ++ [av, pv, sv, tv]) ([b2] ++ [av, pv, sv, tv])
          (Kadd * (isz (α : ℤ) + isz (α : ℤ))) := by
        refine Pipe.rw (Pipe.appendTail [av, pv, sv, tv] (Pipe.binOp (hAdd main)
          (a := (α : ℤ)) (b := (α : ℤ)) trivial)) ?_
        have hsum : (α : ℤ) + (α : ℤ) = (((2 * α : ℕ)) : ℤ) := by push_cast; ring
        rw [hsum]
      exact Pipe.le hstep (by
        refine Nat.mul_le_mul (show Kadd ≤ Kc by rw [hKcdef]; omega) ?_
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- roll 2 : p to the top
      refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [b2, av, pv, sv, tv]) (k := 2)
        (by simp)) (by simp)) (by
        rw [Nat.mul_assoc]
        refine Nat.mul_le_mul (show Kroll ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [b2, av, pv, sv, tv]
        rw [show List.take (2 + 1) [Val.int (((2 * α : ℕ) : ℤ)), Val.int (α : ℤ), Val.int (p : ℤ),
              Val.int (s : ℤ), Val.int (t : ℤ)]
            = ([Val.int (((2 * α : ℕ) : ℤ)), Val.int (α : ℤ), Val.int (p : ℤ)] : List Val)
              from rfl]
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- dup (p)
      refine Pipe.le (Pipe.appendTail [b2, av, sv, tv] (Pipe.dup main hDup pv)) (by
        refine Nat.mul_le_mul (show Kdup ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [pv]
        rw [Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- sqrt
      have hstep : Pipe main sqrtProg ([pv] ++ [pv, b2, av, sv, tv]) ([rv] ++ [pv, b2, av, sv, tv])
          (Ksqrt * isz (p : ℤ) ^ 2) := by
        refine Pipe.rw (Pipe.appendTail [pv, b2, av, sv, tv] (Pipe.unOp (hSqrt main)
          (a := (p : ℤ)) (by positivity))) ?_
        dsimp only [rv]
        rw [buM_toNat]
      exact Pipe.le hstep (by
        refine Nat.mul_le_mul (show Ksqrt ≤ Kc by rw [hKcdef]; omega) ?_
        exact buM_sq_le (p := p) hp hszp)
    · -- roll 2 : 2α next to √p
      refine Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [rv, pv, b2, av, sv, tv]) (k := 2)
        (by simp)) (by simp)) (by
        rw [Nat.mul_assoc]
        refine Nat.mul_le_mul (show Kroll ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [rv, pv, b2, av, sv, tv]
        rw [show List.take (2 + 1) [Val.int (((Nat.sqrt p : ℕ) : ℤ)), Val.int (p : ℤ),
              Val.int (((2 * α : ℕ) : ℤ)), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
            = ([Val.int (((Nat.sqrt p : ℕ) : ℤ)), Val.int (p : ℤ),
                Val.int (((2 * α : ℕ) : ℤ))] : List Val) from rfl]
        simp only [Work.Fx.szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- swap
      refine Pipe.le (Pipe.appendTail [pv, av, sv, tv] (Pipe.swap main hSwap b2 rv)) (by
        refine Nat.mul_le_mul (show Kswap ≤ Kc by rw [hKcdef]; omega) ?_
        dsimp only [b2, rv]
        rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- tdiv
      refine Pipe.le (Pipe.appendTail [pv, av, sv, tv] (Pipe.binOp (hTdiv main)
        (a := ((Nat.sqrt p : ℕ) : ℤ)) (b := (((2 * α : ℕ)) : ℤ)) hne)) (by
        rw [Nat.mul_assoc]
        refine Nat.mul_le_mul (show Ktdiv ≤ Kc by rw [hKcdef]; omega) ?_
        exact buM_prod_le (p := p) hp hszr hsz2α)
    · -- push 1
      refine Pipe.le (Pipe.appendTail [qv, pv, av, sv, tv]
        (Pipe.pushVal hPush (Val.int (1 : ℤ)))) (by
        refine Nat.mul_le_mul (show Kpush ≤ Kc by rw [hKcdef]; omega) ?_
        rw [Work.Fx.vsz_int]
        refine buM_lin_le (p := p) hp ?_
        omega)
    · -- add : + 1
      refine Pipe.le (Pipe.appendTail [pv, av, sv, tv] (Pipe.binOp (hAdd main)
        (a := (1 : ℤ)) (b := Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ))) trivial)) (by
        refine Nat.mul_le_mul (show Kadd ≤ Kc by rw [hKcdef]; omega) ?_
        refine buM_lin_le (p := p) hp ?_
        omega)
  · show ([Val.int ((1 : ℤ) + Int.tdiv (((Nat.sqrt p : ℕ) : ℤ)) (((2 * α : ℕ) : ℤ))),
        Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] : List Val)
      = [Val.int ((egM p α : ℕ) : ℤ)] ++
        [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
    rw [buM_val_eq p α]
    rfl

end Work.Resample

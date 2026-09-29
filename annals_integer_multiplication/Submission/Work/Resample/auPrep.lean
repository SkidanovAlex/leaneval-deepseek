import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.sliceA1prep
import Submission.Work.Fx.piDefs
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.auWtSize
import Submission.Work.Resample.auNsqBounds
import Submission.Work.Resample.auSizeBounds
import Submission.Work.Resample.auInnerElem
import Submission.Work.Resample.auRecWord
import Submission.Work.Resample.auPreChain

/-!
# `Work.Resample.auPrep`: the table word `prep` of the Gaussian resampling

This file builds the (uniform in `p, α, s, t`) word computing the static parameter block
`auPvals p α s t` from `[int p, int α, int s, int t]`, given the π word `piSpec` and the weight word
`wtSpec`.  The construction is the four-phase one documented in `Work.Resample.auPrepDefs`; the
record word (`Work.Resample.auRecWord`) and the element word (`Work.Resample.auInnerElem`) are the
delegated pieces, and the arithmetic facts come from `auWtSize`, `auNsqBounds`, `auSizeBounds`,
`auTableSize`.

Everything here is a `Work.Resample.Pipe` chain: `Pipe main prog A B c` is a `WordR` spec for a word
turning the fixed window `A` into the fixed window `B` at cost `≤ c`.

## The cost accounting

Let `VL = 100·t·(p+1)² + 1` bound the size of the table (and of the label list), and let `SBW` be a
uniform bound for one library call on a window consisting of the table plus `O(1)` integers of size
`≤ auSZ p`.  Both phases are then lists of ≤ 20 such steps; the outer `mapList` costs
`t·(Krec·(p+1)^Krec + Kml·(L+1)) + Kml` with `L = 100(p+1)²`; a final `pow_bound`-style step absorbs
all constants into `K·(t+1)·(p+1)^K`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Chaining a list of words along a list of windows -/

/-- The program `[p₁, …, pₙ]` sequenced in order. -/
def chainProg (ps : List Cmd) : Cmd := ps.foldr Cmd.seq .skip

theorem chainProg_nil : chainProg ([] : List Cmd) = .skip := rfl

theorem chainProg_cons (p : Cmd) (ps : List Cmd) : chainProg (p :: ps) = .seq p (chainProg ps) := rfl

private theorem Pipe.skip {main : Cmd} {A : List Val} : Pipe main .skip A A 1 := by
  intro rest
  refine Work.Kernel.WordR_conseq (Work.Kernel.WordR_skip main) ?_ ?_ ?_
  · intro vs _; trivial
  · intro vs out hvs ho; rw [ho]; exact hvs
  · intro vs _; exact le_rfl

/-- Chaining words along a list of windows: if `ws = [W₀, …, Wₙ]`, `ps = [p₁, …, pₙ]` and
`pᵢ : Wᵢ → W_{i+1}` costs at most `cb`, then `chainProg ps : W₀ → Wₙ` costs at most
`n·cb + 1`. -/
theorem Pipe.chain {main : Cmd} (ps : List Cmd) (ws : List (List Val)) (cb : ℕ)
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

/-! ## A generalised `pow_bound` -/

theorem powBoundGen (M c p : ℕ) (hM : 1 ≤ M) (hp : 2 ≤ p + 1) :
    M * (p + 1) ^ c ≤ (4 * M + 1) * (p + 1) ^ (4 * M + 1 + c) := by
  have h1 : (p + 1) ^ (4 * M + 1 + c) = (p + 1) ^ c * (p + 1) ^ (4 * M + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1]
  have h2 : M ≤ (p + 1) ^ (4 * M + 1) := by
    have h3 : (2 : ℕ) ^ (4 * M + 1) ≤ (p + 1) ^ (4 * M + 1) := Nat.pow_le_pow_left hp _
    have h4 : M ≤ 2 ^ (4 * M + 1) := by
      have h5 := Nat.lt_two_pow_self (n := 4 * M + 1)
      omega
    exact le_trans h4 h3
  calc M * (p + 1) ^ c ≤ (p + 1) ^ (4 * M + 1) * (p + 1) ^ c := Nat.mul_le_mul_right _ h2
    _ = (p + 1) ^ c * (p + 1) ^ (4 * M + 1) := by ring
    _ ≤ (4 * M + 1) * ((p + 1) ^ c * (p + 1) ^ (4 * M + 1)) :=
        Nat.le_mul_of_pos_left _ (by omega)

/-! ## Cost helpers -/

/-- Uniform bound on the size of the table value (and of the label list). -/
def auBQ (p t : ℕ) : ℕ := t * (100 * (p + 1) ^ 2 + 1) + 1

/-- Uniform bound on the cost of one library call on a window consisting of the table plus `O(1)`
integers of size `≤ auSZ p`. -/
def auSBW (KS p t : ℕ) : ℕ := KS * 2000 * (auBQ p t + 40)

theorem auBQ_eq (p t : ℕ) : auBQ p t = 100 * (p + 1) ^ 2 * t + t + 1 := by
  simp only [auBQ]; ring

theorem auBQ_ge (p t : ℕ) (ht : 1 ≤ t) : 100 * (p + 1) ^ 2 ≤ auBQ p t := by
  rw [auBQ_eq]
  calc 100 * (p + 1) ^ 2 = 100 * (p + 1) ^ 2 * 1 := by ring
    _ ≤ 100 * (p + 1) ^ 2 * t := Nat.mul_le_mul_left _ ht
    _ ≤ 100 * (p + 1) ^ 2 * t + t + 1 := by omega

theorem auSZ_le_BQ (p t : ℕ) (ht : 1 ≤ t) : auSZ p ≤ 5 * auBQ p t := by
  have h1 : auSZ p ≤ 410 * (p + 1) := by simp only [auSZ]; omega
  have h2 : 410 * (p + 1) ≤ 500 * (p + 1) ^ 2 := by
    calc 410 * (p + 1) ≤ (500 * (p + 1)) * (p + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = 500 * (p + 1) ^ 2 := by ring
  calc auSZ p ≤ 410 * (p + 1) := h1
    _ ≤ 500 * (p + 1) ^ 2 := h2
    _ = 5 * (100 * (p + 1) ^ 2) := by ring
    _ ≤ 5 * auBQ p t := Nat.mul_le_mul_left 5 (auBQ_ge p t ht)

theorem le_SBW {K KS p t X : ℕ} (hK : K ≤ KS) (hX : X ≤ 2000 * (auBQ p t + 40)) :
    K * X ≤ auSBW KS p t := by
  rw [auSBW]
  calc K * X ≤ KS * X := Nat.mul_le_mul_right _ hK
    _ ≤ KS * (2000 * (auBQ p t + 40)) := Nat.mul_le_mul_left _ hX
    _ = auSBW KS p t := by rw [auSBW]; ring

theorem le_SBW_one {K KS p t v : ℕ} (hK : K ≤ KS) (ht : 1 ≤ t) (hv : v ≤ auSZ p) :
    K * (v + 1) ≤ auSBW KS p t := by
  refine le_SBW hK ?_
  have h2 := auSZ_le_BQ p t ht
  nlinarith [h2, Nat.zero_le (auBQ p t)]

theorem le_SBW_two {K KS p t u v : ℕ} (hK : K ≤ KS) (ht : 1 ≤ t) (hu : u ≤ auSZ p)
    (hv : v ≤ auSZ p) : K * (u + v) ≤ auSBW KS p t := by
  refine le_SBW hK ?_
  have h2 := auSZ_le_BQ p t ht
  nlinarith [h2, Nat.zero_le (auBQ p t)]

theorem le_SBW_three {K KS p t u v w : ℕ} (hK : K ≤ KS) (ht : 1 ≤ t) (hu : u ≤ auSZ p)
    (hv : v ≤ auSZ p) (hw : w ≤ auSZ p) : K * (u + v + w) ≤ auSBW KS p t := by
  refine le_SBW hK ?_
  have h2 := auSZ_le_BQ p t ht
  nlinarith [h2, Nat.zero_le (auBQ p t)]

theorem le_SBW_roll {K KS p t : ℕ} (hK : K ≤ KS) (ht : 1 ≤ t) {A : List Val} {k : ℕ}
    (hk : k + 1 ≤ 8) (hA : szl A ≤ 8 * auBQ p t + 8 * auSZ p) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ auSBW KS p t := by
  have h1 : szl (A.take (k + 1)) ≤ 8 * auBQ p t + 8 * auSZ p := le_trans (szl_take_le A _) hA
  rw [show K * (k + 1) * (szl (A.take (k + 1)) + 1)
      = K * ((k + 1) * (szl (A.take (k + 1)) + 1)) by ring]
  refine le_SBW hK ?_
  have h2 := auSZ_le_BQ p t ht
  calc (k + 1) * (szl (A.take (k + 1)) + 1) ≤ 8 * (8 * auBQ p t + 8 * auSZ p + 1) :=
        Nat.mul_le_mul hk (by omega)
    _ ≤ 2000 * (auBQ p t + 40) := by nlinarith [h2, Nat.zero_le (auBQ p t)]

/-! ## Size bounds used by the chains -/

theorem isz_p_leW (p : ℕ) : isz (p : ℤ) ≤ auSZ p :=
  isz_le_pow2 (le_of_lt (Nat.lt_two_pow_self))

theorem isz_t_leW {p t : ℕ} (ht : t < 2 ^ p) : isz (t : ℤ) ≤ auSZ p := isz_le_pow2 (le_of_lt ht)

theorem isz_off_le' {p α s : ℕ} (h : isz ((auOff p α s : ℕ) : ℤ) ≤ auSZ p) :
    isz (auOff p α s : ℤ) ≤ auSZ p := h

theorem mem_auKs {p t : ℕ} {x : Val} (hx : x ∈ auKs p t) :
    ∃ k, k < t ∧ x = .cons (.int (k : ℤ)) (.int (auPi p)) := by
  simp only [auKs, List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, hk, rfl⟩


/-- Cost bound for dropping one of the small integer values of the output window. -/
theorem le_SBW_dropInt {K KS p t : ℕ} (hK : K ≤ KS) (ht : 1 ≤ t) (z : ℤ)
    (hz : isz z ≤ auSZ p) : K * (vsz (.int z) + 1) ≤ auSBW KS p t := by
  rw [vsz_int']
  exact le_SBW_one hK ht hz

/-! ## The window-size bounds used by the output chain -/

theorem szlWin0 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auCop p α s), .int (auOff p α s)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin1 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auOff p α s)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin2 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (auOff p α s), .int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin3 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin4 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (α : ℤ), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin5 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin6 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (s : ℤ), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (t : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin7 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (t : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin8 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (t : ℤ), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin9 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (auPi p)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin10 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (auPi p), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin11 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin12 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (p : ℤ), A, .int (auOff p α s), .int (auCop p α s)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin13 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (auCop p α s), .int (p : ℤ), A, .int (auOff p α s)] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

theorem szlWin14 (p α s t : ℕ) (A : Val) (hA : vsz A ≤ auBQ p t)
    (hszp : isz (p : ℤ) ≤ auSZ p) (hszα : isz (α : ℤ) ≤ auSZ p)
    (hszs : isz (s : ℤ) ≤ auSZ p) (hszt : isz (t : ℤ) ≤ auSZ p)
    (hszπ : isz (auPi p) ≤ auSZ p) (hOff' : isz (auOff p α s : ℤ) ≤ auSZ p)
    (hCop' : isz (auCop p α s : ℤ) ≤ auSZ p) :
    szl [.int (auOff p α s), .int (auCop p α s), .int (p : ℤ), A] ≤ 8 * auBQ p t + 8 * auSZ p := by
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int']
  omega

/-! ## The output-rearrangement word -/

theorem auPostChain {progRoll : ℕ → Cmd} {Kroll : ℕ}
    (hRoll : ∀ (main : Cmd) (k : ℕ), WordR main (progRoll k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kroll * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {progDrop : Cmd} {Kdrop : ℕ}
    (hDrop : ∀ (main : Cmd), WordR main progDrop (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdrop * (vsz (vs.headD .nil) + 1)))
    {progSwap : Cmd} {Kswap : ℕ}
    (hSwap : ∀ (main : Cmd), WordR main progSwap (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Kswap * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    {KS : ℕ} (hKr : Kroll ≤ KS) (hKd : Kdrop ≤ KS) (hKs : Kswap ≤ KS) :
    ∃ (post : Cmd), ∀ (main : Cmd) (p α s t : ℕ) (A : Val) (hs : 2 ≤ s) (hst : s < t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hA : vsz A ≤ auBQ p t)
      (hOff : isz ((auOff p α s : ℕ) : ℤ) ≤ auSZ p)
      (hCop : isz ((auCop p α s : ℕ) : ℤ) ≤ auSZ p),
      Pipe main post
        [A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p),
          .int (auCop p α s), .int (auOff p α s)]
        [.int (auOff p α s), .int (auCop p α s), .int (p : ℤ), A]
        (14 * auSBW KS p t + 1) := by
  refine ⟨chainProg [progRoll 6, progRoll 7, progRoll 2, progRoll 4, progDrop, progRoll 4, progDrop,
    progRoll 4, progDrop, progRoll 4, progDrop, progRoll 3, progRoll 3, progRoll 3], ?_⟩
  intro main p α s t A hs hst htp hα hp hαp hA hOff hCop
  have ht : 1 ≤ t := by omega
  have hszp : isz (p : ℤ) ≤ auSZ p := isz_p_leW p
  have hαp' : α ≤ 2 ^ p := by
    have h1 : α ≤ α ^ 2 := by nlinarith
    exact le_of_lt (lt_of_le_of_lt h1 (lt_of_lt_of_le hαp (le_of_lt (Nat.lt_two_pow_self))))
  have hszα : isz (α : ℤ) ≤ auSZ p := isz_le_pow2 hαp'
  have hszs : isz (s : ℤ) ≤ auSZ p := isz_le_pow2 (by omega)
  have hszt : isz (t : ℤ) ≤ auSZ p := isz_le_pow2 (by omega)
  have hszπ : isz (auPi p) ≤ auSZ p := isz_auPi_le p
  have hOff' : isz (auOff p α s : ℤ) ≤ auSZ p := hOff
  have hCop' : isz (auCop p α s : ℤ) ≤ auSZ p := hCop
  refine Pipe.chain _
    [[A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auCop p α s), .int (auOff p α s)],
     [.int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auOff p α s)],
     [.int (auOff p α s), .int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)],
     [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)],
     [.int (α : ℤ), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)],
     [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)],
     [.int (s : ℤ), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (t : ℤ), .int (auPi p)],
     [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (t : ℤ), .int (auPi p)],
     [.int (t : ℤ), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (auPi p)],
     [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (auPi p)],
     [.int (auPi p), A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ)],
     [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ)],
     [.int (p : ℤ), A, .int (auOff p α s), .int (auCop p α s)],
     [.int (auCop p α s), .int (p : ℤ), A, .int (auOff p α s)],
     [.int (auOff p α s), .int (auCop p α s), .int (p : ℤ), A]]
    (auSBW KS p t) (by simp) ?_
  intro i hi
  have hi' : i < 14 := by
    simpa only [List.length_cons, List.length_nil] using hi
  interval_cases i
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auCop p α s), .int (auOff p α s)]) (k := 6) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auCop p α s), .int (auOff p α s)]) (k := 6) hKr ht (by omega)
        (szlWin0 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [.int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auOff p α s)]) (k := 7) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [.int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p), .int (auOff p α s)]) (k := 7) hKr ht (by omega)
        (szlWin1 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [.int (auOff p α s), .int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 2) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [.int (auOff p α s), .int (auCop p α s), A, .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 2) hKr ht (by omega)
        (szlWin2 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 4) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 4) hKr ht (by omega)
        (szlWin3 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · refine Pipe.le (Pipe.appendTail _ (Pipe.drop (main := main) hDrop (.int (α : ℤ))))
      (le_SBW_dropInt (p := p) (t := t) hKd ht (α : ℤ) hszα)
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 4) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 4) hKr ht (by omega)
        (szlWin5 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · refine Pipe.le (Pipe.appendTail _ (Pipe.drop (main := main) hDrop (.int (s : ℤ))))
      (le_SBW_dropInt (p := p) (t := t) hKd ht (s : ℤ) hszs)
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 4) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (t : ℤ), .int (auPi p)]) (k := 4) hKr ht (by omega)
        (szlWin7 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · refine Pipe.le (Pipe.appendTail _ (Pipe.drop (main := main) hDrop (.int (t : ℤ))))
      (le_SBW_dropInt (p := p) (t := t) hKd ht (t : ℤ) hszt)
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (auPi p)]) (k := 4) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ), .int (auPi p)]) (k := 4) hKr ht (by omega)
        (szlWin9 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · refine Pipe.le (Pipe.appendTail _ (Pipe.drop (main := main) hDrop (.int (auPi p))))
      (le_SBW_dropInt (p := p) (t := t) hKd ht (auPi p) hszπ)
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ)]) (k := 3) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [A, .int (auOff p α s), .int (auCop p α s), .int (p : ℤ)]) (k := 3) hKr ht (by omega)
        (szlWin11 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [.int (p : ℤ), A, .int (auOff p α s), .int (auCop p α s)]) (k := 3) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [.int (p : ℤ), A, .int (auOff p α s), .int (auCop p α s)]) (k := 3) hKr ht (by omega)
        (szlWin12 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))
  · exact Pipe.le (Pipe.rw (Pipe.roll (main := main) hRoll (A := [.int (auCop p α s), .int (p : ℤ), A, .int (auOff p α s)]) (k := 3) (by simp)) (by simp))
      (le_SBW_roll (p := p) (t := t) (A := [.int (auCop p α s), .int (p : ℤ), A, .int (auOff p α s)]) (k := 3) hKr ht (by omega)
        (szlWin13 p α s t A hA hszp hszα hszs hszt hszπ hOff' hCop'))

/-! ## Sizes of the records, and the label list -/

theorem vsz_ofList_leW {l : List Val} {M : ℕ} (h : ∀ v ∈ l, vsz v ≤ M) :
    vsz (ofList l) ≤ l.length * (M + 1) + 1 := by
  rw [vsz_ofList]
  have h1 : (l.map vsz).sum ≤ (l.map vsz).length * M :=
    list_sum_le_mul (by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact h v hv)
  rw [List.length_map] at h1
  nlinarith

theorem vsz_auWtL_le (p α s t k : ℕ)
    (hW : ∀ (N : ℤ), 0 ≤ N → isz (auWt p α t N) ≤ auSZ p) :
    vsz (ofList (auWtL p α s t k)) ≤ auL p α * (auSZ p + 1) + 1 := by
  have h1 : vsz (ofList (auWtL p α s t k)) ≤ (auWtL p α s t k).length * (auSZ p + 1) + 1 :=
    vsz_ofList_leW (by
      intro v hv
      have hv' : ∃ i, i < auL p α ∧ Val.int (auWt p α t (auNsq p α s t k i)) = v := by
        simpa only [auWtL, List.mem_map, List.mem_range] using hv
      obtain ⟨i, hi, rfl⟩ := hv'
      rw [vsz_int']
      exact hW _ (auNsq_nonneg p α s t k i))
  have h2 : (auWtL p α s t k).length = auL p α := by
    simp only [auWtL, List.length_map, List.length_range]
  rwa [h2] at h1

/-- One record fits in `100·(p+1)²` glyphs (independently of `t`). -/
theorem vsz_auRec_le (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t)
    (hW : ∀ (N : ℤ), 0 ≤ N → isz (auWt p α t N) ≤ auSZ p) :
    vsz (auRec p α s t k) ≤ 100 * (p + 1) ^ 2 := by
  obtain ⟨hM, hL, hK, hC, hOff, hCop, hsl0, hsl1⟩ :=
    auSizeBounds p α s t k hs hst htp hα hp hαp hk
  rw [auRec_eq, vsz_cons, vsz_int']
  have h1 := vsz_auWtL_le p α s t k hW
  have hsl : isz (((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)) ≤ auSZ p := by
    have h2 : ((((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ))).natAbs ≤ 1 := by omega
    have h3 : (((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)).natAbs.size ≤ 1 :=
      Nat.size_le.mpr (by omega)
    simp only [isz, auSZ]; omega
  have hsz : auSZ p = 10 * p + 400 := rfl
  nlinarith [hL, h1, hsz, Nat.zero_le (auL p α), Nat.zero_le (auSZ p)]

/-- The whole table fits in `auBQ p t` glyphs. -/
theorem vsz_auTable_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hW : ∀ (N : ℤ), 0 ≤ N → isz (auWt p α t N) ≤ auSZ p) :
    vsz (auTable p α s t) ≤ auBQ p t := by
  rw [auTable_eq]
  have h1 : vsz (ofList (auRecs p α s t)) ≤ (auRecs p α s t).length * (100 * (p + 1) ^ 2 + 1) + 1 :=
    vsz_ofList_leW (by
      intro v hv
      have hv' : ∃ k, k < t ∧ auRec p α s t k = v := by
        simpa only [auRecs, List.mem_map, List.mem_range] using hv
      obtain ⟨k, hk, rfl⟩ := hv'
      exact vsz_auRec_le p α s t k hs hst htp hα hp hαp hk hW)
  have h2 : (auRecs p α s t).length = t := by simp only [auRecs, List.length_map, List.length_range]
  rw [h2] at h1
  have h3 : t * (100 * (p + 1) ^ 2 + 1) + 1 = auBQ p t := by simp only [auBQ]
  exact le_trans h1 (le_of_eq h3)

/-- A label of the table fits in `100·(p+1)²` glyphs. -/
theorem vsz_auKs_elem_le (p t k : ℕ) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hk : k < t) :
    vsz (.cons (.int (k : ℤ)) (.int (auPi p)) : Val) ≤ 100 * (p + 1) ^ 2 := by
  have h1 : isz (k : ℤ) ≤ p + 3 := by
    have hk2 : k < 2 ^ (p + 1) := lt_of_lt_of_le (lt_trans hk htp)
      (le_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega)))
    have hk3 : k.size ≤ p + 1 := Nat.size_le.mpr hk2
    simp only [isz, Int.natAbs_natCast]
    omega
  have h2 : isz (auPi p) ≤ 10 * p + 400 := by simpa only [auSZ] using isz_auPi_le p
  rw [vsz_cons, vsz_int', vsz_int']
  nlinarith [h1, h2, Nat.zero_le p]

/-! ## Fixed-`rest` `mapList` combinator -/

theorem Pipe.mapListFunFixed {comb : Cmd → Cmd} {Kml : ℕ} (hML : MapListField comb Kml)
    {main q : Cmd} {T : List Val} {xs : List Val} {F : Val → Val} {c L : ℕ}
    (h : ∀ x ∈ xs, Pipe main q (x :: T) (F x :: T) c)
    (hx : ∀ x ∈ xs, vsz x ≤ L) (hy : ∀ x ∈ xs, vsz (F x) ≤ L) :
    Pipe main (comb q) (ofList xs :: T) (ofList (xs.map F) :: T)
      (xs.length * (c + Kml * (L + 1)) + Kml) := by
  intro r0
  have h1 : WordR main (comb q) (fun vs => vs = ofList xs :: (T ++ r0))
      (fun _ out => ∃ ys, out = ofList ys :: (T ++ r0) ∧ List.Forall₂ (fun x y => y = F x) xs ys)
      (fun _ => xs.length * (c + Kml * (L + 1)) + Kml) := by
    refine hML main q (T ++ r0) (fun x => x ∈ xs) (fun x y => y = F x) c L ?_ xs ?_
    · intro x hxmem
      have hp := h x hxmem r0
      refine Work.Kernel.WordR_conseq hp ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out _ hout
        exact ⟨F x, hout, rfl, hy x hxmem⟩
      · intro vs _; exact le_rfl
    · intro x hxmem; exact ⟨hxmem, hx x hxmem⟩
  refine Work.Kernel.WordR_conseq h1 ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hout
    obtain ⟨ys, hout', hf⟩ := hout
    rw [hout', forall₂_map_right hf]
    rfl
  · intro vs _; exact le_rfl

/-! ## The final cost arithmetic -/

/-- The constant multiplying `(t+1)·(p+1)^K`. -/
def auC0 (Kpre Krec Kml KS : ℕ) : ℕ :=
  Kpre + Krec + 101 * Kml + Kml + (4000000 * KS + 1)

/-- The exponent. -/
def auCc (Kpre Krec : ℕ) : ℕ := max (max Kpre Krec) 3

theorem auCost_le {Kpre Krec Kml KS t p : ℕ} (ht : 1 ≤ t) (hp : 2 ≤ p + 1) :
    Kpre * (t + 1) * (p + 1) ^ Kpre
      + (t * (Krec * (p + 1) ^ Krec + Kml * (100 * (p + 1) ^ 2 + 1)) + Kml)
      + (14 * auSBW KS p t + 1)
    ≤ auC0 Kpre Krec Kml KS * (t + 1) * (p + 1) ^ auCc Kpre Krec := by
  have hc1 : Kpre ≤ auCc Kpre Krec := le_trans (le_max_left _ _) (le_max_left _ _)
  have hc2 : Krec ≤ auCc Kpre Krec := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc3 : 2 ≤ auCc Kpre Krec := le_trans (by norm_num) (le_max_right _ _)
  have hP1 : (p + 1) ^ Kpre ≤ (p + 1) ^ auCc Kpre Krec := Nat.pow_le_pow_right (by omega) hc1
  have hP2 : (p + 1) ^ Krec ≤ (p + 1) ^ auCc Kpre Krec := Nat.pow_le_pow_right (by omega) hc2
  have hP3 : (p + 1) ^ 2 ≤ (p + 1) ^ auCc Kpre Krec := Nat.pow_le_pow_right (by omega) hc3
  have hP4 : 1 ≤ (p + 1) ^ auCc Kpre Krec := Nat.one_le_pow _ _ (by omega)
  have h1 : Kpre * (t + 1) * (p + 1) ^ Kpre ≤ Kpre * (t + 1) * (p + 1) ^ auCc Kpre Krec :=
    Nat.mul_le_mul_left _ hP1
  have h2 : t * (Krec * (p + 1) ^ Krec) ≤ Krec * (t + 1) * (p + 1) ^ auCc Kpre Krec :=
    calc t * (Krec * (p + 1) ^ Krec)
        ≤ t * (Krec * (p + 1) ^ auCc Kpre Krec) := Nat.mul_le_mul_left t (Nat.mul_le_mul_left _ hP2)
      _ ≤ (t + 1) * (Krec * (p + 1) ^ auCc Kpre Krec) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = Krec * (t + 1) * (p + 1) ^ auCc Kpre Krec := by ring
  have h3 : t * (Kml * (100 * (p + 1) ^ 2 + 1))
      ≤ 101 * Kml * (t + 1) * (p + 1) ^ auCc Kpre Krec :=
    calc t * (Kml * (100 * (p + 1) ^ 2 + 1))
        ≤ t * (Kml * (101 * (p + 1) ^ auCc Kpre Krec)) :=
          Nat.mul_le_mul_left t (Nat.mul_le_mul_left _ (by nlinarith [hP3, hP4]))
      _ ≤ (t + 1) * (Kml * (101 * (p + 1) ^ auCc Kpre Krec)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 101 * Kml * (t + 1) * (p + 1) ^ auCc Kpre Krec := by ring
  have h4 : Kml ≤ Kml * (t + 1) * (p + 1) ^ auCc Kpre Krec :=
    calc Kml = Kml * 1 * 1 := by ring
      _ ≤ Kml * (t + 1) * (p + 1) ^ auCc Kpre Krec :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hP4
  have h5 : 14 * auSBW KS p t + 1
      ≤ (4000000 * KS + 1) * (t + 1) * (p + 1) ^ auCc Kpre Krec := by
    have hp2 : 1 ≤ (p + 1) ^ 2 := by nlinarith [Nat.zero_le p]
    have h6 : t * (100 * (p + 1) ^ 2 + 1) + 1 + 40 ≤ 142 * ((t + 1) * (p + 1) ^ 2) := by
      nlinarith [Nat.zero_le t, hp2]
    have h6' : 142 * ((t + 1) * (p + 1) ^ 2) ≤ 142 * ((t + 1) * (p + 1) ^ auCc Kpre Krec) :=
      Nat.mul_le_mul_left 142 (Nat.mul_le_mul_left _ hP3)
    have htW : 1 ≤ (t + 1) * (p + 1) ^ auCc Kpre Krec :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc 14 * auSBW KS p t + 1
        = 14 * (KS * 2000 * (t * (100 * (p + 1) ^ 2 + 1) + 1 + 40)) + 1 := by rw [auSBW, auBQ]
      _ ≤ 14 * (KS * 2000 * (142 * ((t + 1) * (p + 1) ^ auCc Kpre Krec))) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 14 (Nat.mul_le_mul_left _
            (le_trans h6 h6'))) 1
      _ = 3976000 * KS * ((t + 1) * (p + 1) ^ auCc Kpre Krec) + 1 := by ring
      _ ≤ (4000000 * KS + 1) * ((t + 1) * (p + 1) ^ auCc Kpre Krec) := by
          nlinarith [Nat.zero_le KS, htW]
      _ = (4000000 * KS + 1) * (t + 1) * (p + 1) ^ auCc Kpre Krec := by ring
  rw [auC0]
  nlinarith [h1, h2, h3, h4, h5, Nat.zero_le t]

theorem auCostFinal {Kpre Krec Kml KS t p : ℕ} (ht : 1 ≤ t) (hp : 2 ≤ p + 1) :
    Kpre * (t + 1) * (p + 1) ^ Kpre
      + (t * (Krec * (p + 1) ^ Krec + Kml * (100 * (p + 1) ^ 2 + 1)) + Kml)
      + (14 * auSBW KS p t + 1)
    ≤ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec) * (t + 1)
      * (p + 1) ^ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec) := by
  have hcl := auCost_le (Kpre := Kpre) (Krec := Krec) (Kml := Kml) (KS := KS) (t := t) (p := p) ht hp
  have hpb := powBoundGen (auC0 Kpre Krec Kml KS) (auCc Kpre Krec) p
    (by simp only [auC0]; omega) (by omega)
  have h2' : auC0 Kpre Krec Kml KS * (t + 1) * (p + 1) ^ (auCc Kpre Krec)
      ≤ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec) * (t + 1)
        * (p + 1) ^ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec) := by
    calc auC0 Kpre Krec Kml KS * (t + 1) * (p + 1) ^ (auCc Kpre Krec)
        = (t + 1) * (auC0 Kpre Krec Kml KS * (p + 1) ^ (auCc Kpre Krec)) := by ring
      _ ≤ (t + 1) * ((4 * auC0 Kpre Krec Kml KS + 1)
            * (p + 1) ^ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec)) :=
          Nat.mul_le_mul_left _ hpb
      _ ≤ (t + 1) * ((4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec)
            * (p + 1) ^ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec) * (t + 1)
            * (p + 1) ^ (4 * auC0 Kpre Krec Kml KS + 1 + auCc Kpre Krec) := by ring
  exact Nat.le_trans hcl h2'

/-! ## The table word `prep` -/

theorem auPrep (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (piProg : HvdH.Cmd) (Kp : ℕ) (piSpec : ∀ (main : HvdH.Cmd) (P : ℕ), 100 ≤ P → HvdH.WordR main piProg (fun vs => ∃ rest, vs = [HvdH.Val.int (P : ℤ)] ++ rest) (fun vs out => ∃ rest, vs = [HvdH.Val.int (P : ℤ)] ++ rest ∧ out = [HvdH.Val.int (Work.Fx.uval P)] ++ rest) (fun _ => Kp * (P + 1) ^ Kp)) (wtProg : HvdH.Cmd) (Kw : ℕ) (wtSpec : ∀ (main : HvdH.Cmd) (p α t : ℕ) (N : ℤ), (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) → (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) → HvdH.WordR main wtProg (fun vs => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest) (fun vs out => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest ∧ out = HvdH.Val.int (auWt p α t N) :: rest) (fun _ => Kw * (p + 1) ^ Kw)) : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p), HvdH.WordR main prog (fun vs => ∃ rest, vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (α : ℤ) :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (t : ℤ) :: rest) (fun vs out => ∃ rest, vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (α : ℤ) :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (t : ℤ) :: rest ∧ out = auPvals p α s t ++ rest) (fun _ => K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨elemProg, KE, hElem⟩ := auInnerElem hk hi wtProg Kw wtSpec
  obtain ⟨recProg, Krec, hRec⟩ := auRecWord hk hi hl ⟨elemProg, KE, hElem⟩
  obtain ⟨preProg, Kpre, hPre⟩ := auPreChain hk hi hl piProg Kp piSpec
  obtain ⟨combML, Kml, hML⟩ := MapListField.of_kernel hk
  obtain ⟨progRoll, Kroll, hRoll⟩ := hk.roll
  obtain ⟨progDrop, Kdrop, hDrop⟩ := hk.drop
  obtain ⟨progSwap, Kswap, hSwap⟩ := hk.swap
  set KS : ℕ := max Kroll (max Kdrop Kswap) + 1 with hKSdef
  have hKr : Kroll ≤ KS := by simp only [hKSdef]; omega
  have hKd : Kdrop ≤ KS := by simp only [hKSdef]; omega
  have hKs : Kswap ≤ KS := by simp only [hKSdef]; omega
  obtain ⟨post, hPost⟩ := auPostChain hRoll hDrop hSwap hKr hKd hKs
  set C0 : ℕ := auC0 Kpre Krec Kml KS with hC0def
  set CC : ℕ := auCc Kpre Krec with hCCdef
  refine ⟨Cmd.seq (Cmd.seq preProg (combML recProg)) post, 4 * C0 + 1 + CC, ?_⟩
  intro main p α s t hs hst htp hα hp hαp
  have ht1 : 1 ≤ t := by omega
  set T : List Val := [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int (auPi p),
    .int (auCop p α s), .int (auOff p α s)] with hT
  have hWtsz : ∀ (N : ℤ), 0 ≤ N → isz (auWt p α t N) ≤ auSZ p :=
    fun N hN => auWtSize p α t N hN hα ht1 hp
  have hB := auSizeBounds p α s t 0 hs hst htp hα hp hαp (by omega)
  have hOff : isz ((auOff p α s : ℕ) : ℤ) ≤ auSZ p := hB.2.2.2.2.1
  have hCop : isz ((auCop p α s : ℕ) : ℤ) ≤ auSZ p := hB.2.2.2.2.2.1
  have hTab : vsz (auTable p α s t) ≤ auBQ p t := vsz_auTable_le p α s t hs hst htp hα hp hαp hWtsz
  have h1 : Pipe main preProg [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)]
      (ofList (auKs p t) :: T) (Kpre * (t + 1) * (p + 1) ^ Kpre) := by
    have hp1 := hPre main p α s t hs hst htp hα hp hαp
    refine Pipe.rw hp1 ?_
    simp only [hT]
  have h2 : Pipe main (combML recProg) (ofList (auKs p t) :: T) (auTable p α s t :: T)
      (t * (Krec * (p + 1) ^ Krec + Kml * (100 * (p + 1) ^ 2 + 1)) + Kml) := by
    have hspec : ∀ x ∈ auKs p t, Pipe main recProg (x :: T) (auRecOf p α s t x :: T)
        (Krec * (p + 1) ^ Krec) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_auKs hx
      have hNbd : ∀ i < auL p α, 0 ≤ auNsq p α s t k i ∧
          auNsq p α s t k i ≤ (2 : ℤ) ^ (4 * p + 8) :=
        fun i hi => auNsqBounds p α s t k i hs hst htp hα hp hαp hk hi
      have hR := hRec main p α s t k hs hst htp hα hp hαp hk hWtsz hNbd
      have hR2 := Pipe.appendTail [.int (auCop p α s), .int (auOff p α s)] hR
      simpa only [hT, auRecOf_cons, List.cons_append, List.nil_append, List.append_assoc] using hR2
    have hx_le : ∀ x ∈ auKs p t, vsz x ≤ 100 * (p + 1) ^ 2 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_auKs hx
      exact vsz_auKs_elem_le p t k hp htp hk
    have hy_le : ∀ x ∈ auKs p t, vsz (auRecOf p α s t x) ≤ 100 * (p + 1) ^ 2 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_auKs hx
      rw [auRecOf_cons]
      exact vsz_auRec_le p α s t k hs hst htp hα hp hαp hk hWtsz
    have hM := Pipe.mapListFunFixed (main := main) (T := T) (xs := auKs p t) (F := auRecOf p α s t)
      hML hspec hx_le hy_le
    have hlen : (auKs p t).length = t := by
      simp only [auKs, List.length_map, List.length_range]
    rw [map_auRecOf p α s t, ← auTable_eq, hlen] at hM
    exact hM
  have h3 : Pipe main post (auTable p α s t :: T)
      [.int (auOff p α s), .int (auCop p α s), .int (p : ℤ), auTable p α s t]
      (14 * auSBW KS p t + 1) := by
    have hp3 := hPost main p α s t (auTable p α s t) hs hst htp hα hp hαp hTab hOff hCop
    simpa only [hT] using hp3
  have h123 : Pipe main (Cmd.seq (Cmd.seq preProg (combML recProg)) post)
      [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ)] (auPvals p α s t)
      (Kpre * (t + 1) * (p + 1) ^ Kpre
        + (t * (Krec * (p + 1) ^ Krec + Kml * (100 * (p + 1) ^ 2 + 1)) + Kml)
        + (14 * auSBW KS p t + 1)) := by
    have h12 := Pipe.comp h1 h2
    have h123' := Pipe.comp h12 h3
    refine Pipe.rw h123' ?_
    simp only [auPvals]
  have hcost := auCostFinal (Kpre := Kpre) (Krec := Krec) (Kml := Kml) (KS := KS) (t := t)
    (p := p) ht1 (by omega)
  have hfinal := Pipe.le h123 hcost
  intro vs hvs s' R hR
  obtain ⟨rest0, hvs0⟩ := hvs
  obtain ⟨out, s2, n, hout, hev, hn, hstk, hoth⟩ := hfinal rest0 vs (by rw [hvs0]; rfl) s' R hR
  exact ⟨out, s2, n, ⟨rest0, hvs0, hout⟩, hev, hn, hstk, hoth⟩

end Work.Resample

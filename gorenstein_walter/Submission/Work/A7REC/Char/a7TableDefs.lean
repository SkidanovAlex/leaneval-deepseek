import Mathlib

/-!
# The A₇ table lemma: definitions

Vocabulary for the finite arithmetic verification of `Work.A7REC.A7TableLemmaProp`.

One "index" of the index set is encoded as an element of `It`: `e = χ(π)`, `a`, `b` with
`χ(z) = b - 2a` and `χ(zσ) = a + b`, and `f = χ(1)`.

The two finite checks are:
* **phase 1** — the three indices with `e ≠ 0` are one of `C0, C1, C2`;
* **phase 2** — for each candidate, the indices with `e = 0` (whose items have to satisfy the
  residual sum constraints) are determined.

All sums are stated in the "integral" normalisation: `w = 2520 / f`, so that e.g. the rational
relation `1 + ∑ c²e/f = 32/35` becomes `∑ c²·e·w = -216`, `1 + ∑ c³/f = 64/35` becomes
`∑ c³·w = 2088`, and `1 + ∑ c²(a+b)/f = 48/35` becomes `∑ c²(a+b)·w = 936`.
-/

namespace Work.A7REC.Char

/-- The character data of one index. -/
structure It where
  e : ℤ
  a : ℤ
  b : ℤ
  f : ℕ
  deriving DecidableEq, Repr

namespace It

/-- `c = χ(z) = b - 2a`. -/
def c (x : It) : ℤ := x.b - 2 * x.a

end It

/-- `2520 / f` as a lookup table (avoids division in kernel computations). -/
def wOf : ℕ → ℤ
  | 2 => 1260 | 3 => 840 | 4 => 630 | 5 => 504 | 6 => 420 | 7 => 360 | 8 => 315 | 9 => 280
  | 10 => 252 | 12 => 210 | 14 => 180 | 15 => 168 | 18 => 140 | 20 => 126 | 21 => 120 | 24 => 105
  | 28 => 90 | 30 => 84 | 35 => 72 | 36 => 70 | 40 => 63 | 42 => 60 | 45 => 56
  | _ => 0

namespace It

/-- `w = 2520 / f` (as a table; equal to the quotient for `f ∈ D50`). -/
def w (x : It) : ℤ := wOf x.f

/-- The congruence `f + 5(b - 2a) + 2e ≡ 0 (mod 8)`. -/
def cong (x : It) : Prop := ((x.f : ℤ) + 5 * (x.b - 2 * x.a) + 2 * x.e) % 8 = 0

/-- The per-index bounds extracted from the hypotheses. -/
def valid (x : It) : Prop :=
  (x.e = -1 ∨ x.e = 0 ∨ x.e = 1) ∧ (-2 ≤ x.a ∧ x.a ≤ 2) ∧ (-2 ≤ x.b ∧ x.b ≤ 2) ∧
    2 ≤ x.f ∧ x.f ≤ 50 ∧ x.f ∣ 2520 ∧ x.cong

/-- The index is not the trivial one. -/
def nz (x : It) : Prop := x.e ≠ 0 ∨ x.a ≠ 0 ∨ x.b ≠ 0

/-- The `(a,b)` type of an index. -/
def typ (x : It) : ℤ × ℤ := (x.a, x.b)

end It

open It

/-! ## Sum functionals on lists -/

def sumE2 (l : List It) : ℤ := (l.map (fun x => x.e ^ 2)).sum
def sumA2 (l : List It) : ℤ := (l.map (fun x => x.a ^ 2)).sum
def sumB2 (l : List It) : ℤ := (l.map (fun x => x.b ^ 2)).sum
def sumEA (l : List It) : ℤ := (l.map (fun x => x.e * x.a)).sum
def sumEB (l : List It) : ℤ := (l.map (fun x => x.e * x.b)).sum
def sumAB (l : List It) : ℤ := (l.map (fun x => x.a * x.b)).sum
def sumEF (l : List It) : ℤ := (l.map (fun x => x.e * Int.ofNat x.f)).sum
def sumAF (l : List It) : ℤ := (l.map (fun x => x.a * Int.ofNat x.f)).sum
def sumBF (l : List It) : ℤ := (l.map (fun x => x.b * Int.ofNat x.f)).sum
def sumC2EW (l : List It) : ℤ := (l.map (fun x => x.c ^ 2 * x.e * x.w)).sum
def sumC3W (l : List It) : ℤ := (l.map (fun x => x.c ^ 3 * x.w)).sum
def sumC2ABW (l : List It) : ℤ := (l.map (fun x => x.c ^ 2 * (x.a + x.b) * x.w)).sum
def sumF2 (l : List It) : ℤ := (l.map (fun x => Int.ofNat x.f ^ 2)).sum

/-! ## Sum functionals on multisets -/

def sumE2M (M : Multiset It) : ℤ := (M.map (fun x => x.e ^ 2)).sum
def sumA2M (M : Multiset It) : ℤ := (M.map (fun x => x.a ^ 2)).sum
def sumB2M (M : Multiset It) : ℤ := (M.map (fun x => x.b ^ 2)).sum
def sumEAM (M : Multiset It) : ℤ := (M.map (fun x => x.e * x.a)).sum
def sumEBM (M : Multiset It) : ℤ := (M.map (fun x => x.e * x.b)).sum
def sumABM (M : Multiset It) : ℤ := (M.map (fun x => x.a * x.b)).sum
def sumEFM (M : Multiset It) : ℤ := (M.map (fun x => x.e * Int.ofNat x.f)).sum
def sumAFM (M : Multiset It) : ℤ := (M.map (fun x => x.a * Int.ofNat x.f)).sum
def sumBFM (M : Multiset It) : ℤ := (M.map (fun x => x.b * Int.ofNat x.f)).sum
def sumC2EWM (M : Multiset It) : ℤ := (M.map (fun x => x.c ^ 2 * x.e * x.w)).sum
def sumC3WM (M : Multiset It) : ℤ := (M.map (fun x => x.c ^ 3 * x.w)).sum
def sumC2ABWM (M : Multiset It) : ℤ := (M.map (fun x => x.c ^ 2 * (x.a + x.b) * x.w)).sum
def sumF2M (M : Multiset It) : ℤ := (M.map (fun x => Int.ofNat x.f ^ 2)).sum

/-! ## Concrete finite data -/

/-- Divisors of `2520` in `[2, 50]`. -/
def D50 : List ℕ :=
  [2,3,4,5,6,7,8,9,10,12,14,15,18,20,21,24,28,30,35,36,40,42,45]

/-- Divisors of `2520` in `[2, 25]` (phase-2 degrees). -/
def D25 : List ℕ := [2,3,4,5,6,7,8,9,10,12,14,15,18,20,21,24]

/-- The possible `(a,b)` pairs with `a ≠ 0` first (so that the enumeration prunes). -/
def ABT : List (ℤ × ℤ) :=
  [(-2,-2),(-2,2),(2,-2),(2,2),(-2,-1),(-2,1),(2,-1),(2,1),(-1,-2),(1,-2),(-1,2),(1,2),
   (-2,0),(2,0),(-1,-1),(1,1),(-1,1),(1,-1),(-1,0),(1,0),(0,-2),(0,2),(0,-1),(0,1)]

/-- The `(a,b)` pairs with `(a,b) ≠ (0,0)`. -/
def ABP : List (ℤ × ℤ) :=
  [(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),
   (0,-2),(0,-1),(0,1),(0,2),(1,-2),(1,-1),(1,0),(1,1),(1,2),
   (2,-2),(2,-1),(2,0),(2,1),(2,2)]

/-- All `(a,b)` pairs (phase-1 indices may have `a = b = 0`). -/
def ABQ : List (ℤ × ℤ) := (0,0) :: ABP

/-- The allowed degrees for `(a,b)` and `e`: `f ∈ D50` with the congruence. -/
def allowedD (A B e : ℤ) : List ℕ :=
  D50.filter (fun ff => ((ff : ℤ) + 5 * (B - 2 * A) + 2 * e) % 8 == 0)

/-- The allowed degrees in the phase-2 range. -/
def allowedD25 (A B : ℤ) : List ℕ :=
  D25.filter (fun ff => ((ff : ℤ) + 5 * (B - 2 * A)) % 8 == 0)

/-- All phase-1 items with `e = sg`. -/
def L1 (sg : ℤ) : List It :=
  (List.flatMap (fun t => (allowedD t.1 t.2 sg).map (fun ff => ⟨sg, t.1, t.2, ff⟩)) ABQ)

/-- All phase-2 items: `e = 0`, `(a,b) ≠ (0,0)`, `f ∈ D25` with the congruence. -/
def L2 : List It :=
  (List.flatMap (fun t => (allowedD25 t.1 t.2).map (fun ff => ⟨0, t.1, t.2, ff⟩))
    (ABP.filter (fun t => decide (t ≠ (0,0)))))

/-- The three candidate configurations for the `e ≠ 0` part. -/
def C0 : List It := [⟨-1,-1,-1,21⟩, ⟨-1,1,1,15⟩, ⟨1,0,-1,35⟩]
def C1 : List It := [⟨-1,0,-1,15⟩, ⟨-1,0,1,21⟩, ⟨1,0,-1,35⟩]
def C2 : List It := [⟨-1,0,1,21⟩, ⟨-1,1,1,15⟩, ⟨1,1,1,35⟩]

/-- The candidate list. -/
def CANDS : List (List It) := [C0, C1, C2]

/-- The `e = 0` part of the `A₇` configuration. -/
def C1T : List It := [⟨0,-1,0,6⟩, ⟨0,1,0,10⟩, ⟨0,1,0,10⟩, ⟨0,-1,0,14⟩, ⟨0,0,2,14⟩]

/-- The full `A₇` multiset. -/
def A7M : Multiset It :=
  (↑([⟨-1,0,-1,15⟩, ⟨-1,0,1,21⟩, ⟨1,0,-1,35⟩] : List It) : Multiset It) +
  ↑([⟨0,-1,0,6⟩, ⟨0,1,0,10⟩, ⟨0,1,0,10⟩, ⟨0,-1,0,14⟩, ⟨0,0,2,14⟩] : List It)

/-! ## Phase 1: the reconstruction and its test -/

/-- The index `s` reconstructed from `p`, `q` and the common sign `sg = e_s`. -/
def mkIt (sg : ℤ) (p q : It) : It :=
  { e := sg, a := p.a + q.a, b := p.b + q.b - sg,
    f := Int.toNat (Int.ofNat p.f + Int.ofNat q.f - sg) }

/-- The phase-1 test on `(sg, p, q)`. -/
@[reducible] def chk1 (sg : ℤ) (p q : It) : Prop :=
  -2 ≤ p.a + q.a ∧ p.a + q.a ≤ 2 ∧ -2 ≤ p.b + q.b - sg ∧ p.b + q.b - sg ≤ 2 ∧
  2 ≤ Int.ofNat p.f + Int.ofNat q.f - sg ∧ Int.ofNat p.f + Int.ofNat q.f - sg ≤ 50 ∧
  Int.toNat (Int.ofNat p.f + Int.ofNat q.f - sg) ∣ 2520 ∧
  ((Int.ofNat p.f + Int.ofNat q.f - sg) + 5 * ((p.b + q.b - sg) - 2 * (p.a + q.a)) + 2 * sg)
      % 8 = 0 ∧
  ((p.b + q.b - sg) - 2 * (p.a + q.a)) ^ 2 *
      wOf (Int.toNat (Int.ofNat p.f + Int.ofNat q.f - sg)) =
    p.c ^ 2 * p.w + q.c ^ 2 * q.w - 216 * sg

/-- The phase-1 enumeration: all configurations produced by the reconstruction. -/
def p1Out : List (List It) :=
  List.flatMap (fun sg : ℤ =>
    List.flatMap (fun p => List.flatMap (fun q =>
      if chk1 sg p q then [[mkIt sg p q, p, q]] else []) (L1 (-sg))) (L1 (-sg))) [1, -1]

/-! ## Phase 2: the enumeration and its test -/

/-- All multisets of `k` elements of `F`, as lists. -/
def fTuples (F : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => F.flatMap (fun ff => (fTuples F k).map (fun r => ff :: r))

/-- The items of type `t` with the degrees `fs`. -/
def itemsOf (t : ℤ × ℤ) (fs : List ℕ) : List It := fs.map (fun ff => ⟨0, t.1, t.2, ff⟩)

/-- `∑ f` over a list of degrees. -/
def fsum (l : List ℕ) : ℤ := (l.map (fun ff => Int.ofNat ff)).sum

/-- `∑ f²` over a list of degrees. -/
def fsq (l : List ℕ) : ℤ := (l.map (fun ff => (Int.ofNat ff) ^ 2)).sum

/-- Boolean version of `aSorted`. -/
def aSortedB : List (ℤ × ℤ) → Bool
  | [] => true
  | t :: ts => (!(t.1 == 0) || ts.all (fun s => s.1 == 0)) && aSortedB ts

/-- Boolean version of `noZero`. -/
def noZeroB : List (ℤ × ℤ) → Bool
  | [] => true
  | t :: ts => (t != (0, 0)) && noZeroB ts

/-- Boolean version of `smallTypes`. -/
def smallTypesB : List (ℤ × ℤ) → Bool
  | [] => true
  | t :: ts => decide (|t.1| ≤ 2) && decide (|t.2| ≤ 2) && smallTypesB ts

/-- `ts` is "a-sorted": once a type with `a = 0` occurs, all following types have `a = 0`. -/
def aSorted : List (ℤ × ℤ) → Prop
  | [] => True
  | t :: ts => (t.1 = 0 → ∀ s ∈ ts, s.1 = 0) ∧ aSorted ts

/-- `ts` contains no zero type. -/
def noZero : List (ℤ × ℤ) → Prop
  | [] => True
  | t :: ts => t ≠ (0,0) ∧ noZero ts

/-- Every type in `ts` has `|a| ≤ 2` and `|b| ≤ 2`. -/
def smallTypes : List (ℤ × ℤ) → Prop
  | [] => True
  | t :: ts => |t.1| ≤ 2 ∧ |t.2| ≤ 2 ∧ smallTypes ts

/-- Enumerate all lists of `e = 0` items with types from `ts` (in the order of `ts`) whose
`∑a²` is `r1`, whose `∑b²` is `r2`, and whose remaining `∑ab`, `∑af`, `∑bf` targets are
`rab, raf, rbf`, with `∑f² ≤ rf2`.

The pruning uses only bounds that are valid for any completion:
* `k·t.1² ≤ r1`, `k·t.2² ≤ r2`;
* a type with `a = 0` can only be used once the `a²` budget is exhausted (all types with `a = 0`
  come last in `ABT`);
* `|∑ab| ≤ (∑a² + ∑b²)/2` and `|∑af| ≤ 2·25·∑a²`, `|∑bf| ≤ 2·25·∑b²` over the remaining items;
* `∑f²` is monotone.
-/
def enumItems : List (ℤ × ℤ) → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → List (List It)
  | [], r1, r2, rab, raf, rbf, rf2 =>
      if r1 = 0 ∧ r2 = 0 ∧ rab = 0 ∧ raf = 0 ∧ rbf = 0 then [[]] else []
  | t :: ts, r1, r2, rab, raf, rbf, rf2 =>
      (List.range 5).flatMap (fun (k : ℕ) =>
        let kk : ℤ := k
        let r1' : ℤ := r1 - kk * t.1 ^ 2
        let r2' : ℤ := r2 - kk * t.2 ^ 2
        (if kk * t.1 ^ 2 ≤ r1 ∧ kk * t.2 ^ 2 ≤ r2 ∧ (t.1 = 0 → r1 = 0) then
          (fTuples (allowedD25 t.1 t.2) k).flatMap (fun fs =>
            let sf : ℤ := fsum fs
            let d_ab : ℤ := t.1 * t.2 * kk
            let d_af : ℤ := t.1 * sf
            let d_bf : ℤ := t.2 * sf
            let d_f2 : ℤ := fsq fs
            (if |rab - d_ab| ≤ (r1' + r2') / 2 ∧ |raf - d_af| ≤ 50 * r1' ∧
                |rbf - d_bf| ≤ 50 * r2' ∧ d_f2 ≤ rf2 then
               (enumItems ts r1' r2' (rab - d_ab) (raf - d_af) (rbf - d_bf) (rf2 - d_f2)).map
                 (fun r => itemsOf t fs ++ r)
             else []))
         else []))

/-- The cheap part of the phase-2 test. -/
def chk2a (rab raf rbf rf2 : ℤ) (l : List It) : Bool :=
  decide (sumAB l = rab) && decide (sumAF l = raf) && decide (sumBF l = rbf) &&
    decide (sumF2 l ≤ rf2)

/-- The expensive part of the phase-2 test. -/
def chk2b (rc3 rc2ab : ℤ) (l : List It) : Bool :=
  decide (sumC3W l = rc3) && decide (sumC2ABW l = rc2ab)

/-- The phase-2 test. -/
def chk2 (rab raf rbf rc3 rc2ab rf2 : ℤ) (l : List It) : Bool :=
  chk2a rab raf rbf rf2 l && chk2b rc3 rc2ab l

/-- The phase-2 enumeration for the given residual targets: the enumeration already enforces the
`a², b², ab, af, bf, f²` relations, and the two cubic relations are tested afterwards. -/
def p2Out (r1 r2 rab raf rbf rc3 rc2ab rf2 : ℤ) : List (List It) :=
  (enumItems ABT r1 r2 rab raf rbf rf2).filter (chk2b rc3 rc2ab)

/-- Residual targets for the candidate `C0`. -/
def res0 : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ := (2, 4, -2, 6, 40, 2208, 912, 628)
/-- Residual targets for the candidate `C1`. -/
def res1 : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ := (4, 4, 0, 0, 28, 2208, 1056, 628)
/-- Residual targets for the candidate `C2`. -/
def res2 : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ := (2, 4, -2, -50, -72, 2208, 336, 628)

/-! ## The table is the true quotient on `D50` -/

theorem wOf_eq_all : D50.all (fun f => wOf f == (2520 / f : ℕ)) = true := by decide

lemma mem_D50 {f : ℕ} (hf : f ∣ 2520) (h2 : 2 ≤ f) (h50 : f ≤ 50) : f ∈ D50 := by
  interval_cases f <;> first | decide | (exfalso; norm_num at hf)

lemma wOf_eq {f : ℕ} (hf : f ∈ D50) : wOf f = ((2520 / f : ℕ) : ℤ) := by
  have h := wOf_eq_all
  rw [List.all_eq_true] at h
  have h' := h f hf
  simpa using h'

end Work.A7REC.Char

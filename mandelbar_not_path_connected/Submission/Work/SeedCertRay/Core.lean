/-
# `Work.SeedCertRay.Core` — the `NC`-independent part of the decidable certificate checker

Core-only module (no `Mathlib` import) so that the kernel-checked `decide` theorems of the
certificate are cheap to elaborate.  All numbers are integers ("mantissas") at scale
`MSZ = 2 ^ 40` (`gen/gen7.py` is the generator; `NOTES.md` §7 has the dictionary).

* `stepOKB` certifies one pull-back step (D1) — source disk of level `k` and angle `j+1`, target
  disk of level `k+1` and angle `j`, certificate triple `(s, ρ, M)`;
* `hpB` is the rational half-plane inequality of one disk;
* `petalDskB` certifies that one disk lies in the petal `Re w < -4` for all `z₁` in the `z₁`-box
  and all `A` in the `A`-box.

The `NC`-dependent parts (`stepQs`, `dirQs`, `dirOKB`, `petalOKB`, the level checkers) are in the
generated module `Work.SeedCertRay.Num`.
-/
namespace Work.SeedCertRay

/-- The scale `2 ^ 40` of all mantissas. -/
def MSZ : Int := 1099511627776

/-- Indexed access into a certificate list. -/
def gI (l : List Int) (i : Nat) : Int := l.getD i 0

/-- The absolute value of an integer, in `Int`. -/
def iabs (x : Int) : Int := max x (-x)

/-- Boolean `and` over a list. -/
def allS {α : Type} (l : List α) (f : α → Bool) : Bool :=
  match l with
  | [] => true
  | a :: t => f a && allS t f

theorem allS_sound {α : Type} {l : List α} {f : α → Bool} (h : allS l f = true) :
    ∀ a, a ∈ l → f a = true := by
  induction l with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons b t ih =>
      intro a ha
      rw [allS, Bool.and_eq_true] at h
      rcases List.mem_cons.mp ha with h1 | h2
      · rw [h1]; exact h.1
      · exact ih h.2 a h2

/-- **(D1) for one step.**  `s`, `t`, `c` are the mantissa lists of the source level, the target
level and the certificate of the source level; `qs` is the index of the source disk, `qt` that of
the target disk (and of the certificate).  `PX + i PY` is the centre of the parameter box (as a
mantissa pair) and `RAD = MSZ * X.rad` its radius bound. -/
def stepOKB (s t c : List Int) (PX PY RAD : Int) (qs qt : Nat) : Bool :=
  decide (0 ≤ gI c (3*qt)) &&
  decide (0 ≤ gI c (3*qt+1)) &&
  decide (gI c (3*qt+1) ≤ 2*gI c (3*qt)) &&
  decide (gI c (3*qt)*gI c (3*qt) ≤ gI t (3*qt)*gI t (3*qt) + gI t (3*qt+1)*gI t (3*qt+1)) &&
  decide ((gI c (3*qt)*gI c (3*qt) + (gI s (3*qs+2) + RAD)*MSZ)
            * (gI c (3*qt)*gI c (3*qt) + (gI s (3*qs+2) + RAD)*MSZ)
          ≤ MSZ*MSZ*((gI s (3*qs)-PX)*(gI s (3*qs)-PX)
                     + (gI s (3*qs+1)-PY)*(gI s (3*qs+1)-PY))) &&
  decide (gI s (3*qs+2) + RAD ≤ gI c (3*qt+2)) &&
  decide (MSZ*MSZ*((gI c (3*qt+2) - gI s (3*qs+2) - RAD)*(gI c (3*qt+2) - gI s (3*qs+2) - RAD))
          ≥ ((gI s (3*qs)-PX)*MSZ - (gI t (3*qt)*gI t (3*qt) - gI t (3*qt+1)*gI t (3*qt+1)))
            * ((gI s (3*qs)-PX)*MSZ - (gI t (3*qt)*gI t (3*qt) - gI t (3*qt+1)*gI t (3*qt+1)))
            + ((gI s (3*qs+1)-PY)*MSZ + 2*gI t (3*qt)*gI t (3*qt+1))
              * ((gI s (3*qs+1)-PY)*MSZ + 2*gI t (3*qt)*gI t (3*qt+1))) &&
  decide (MSZ*gI c (3*qt+2) ≤ gI c (3*qt+1)*(2*gI c (3*qt) - gI c (3*qt+1))) &&
  decide (gI t (3*qt+2) = gI c (3*qt+1))

/-- **(D2) for one disk.**  The rational inequality `(|p| + |q|) * r < p * cx + q * cy` in
mantissa form. -/
def hpB (p q cx cy cr : Int) : Bool :=
  decide ((iabs p + iabs q)*cr < p*cx + q*cy)

/-- **(D3) for one disk of the `alpha_1`-column.**  Mirror of `gen/gen7.py`'s `petalOK`: the disk
`(Bx,By,Br)` lies in the petal of depth `RR` for every `z₁` in the box of half-width `Eta` about
`(Zx,Zy)` and every `A` in the box of half-width `EtaA` about `(Acx,Acy)`. -/
def petalDskB (Bx By Br Zx Zy Eta Acx Acy EtaA RR : Int) : Bool :=
  decide (iabs (2*RR*(Acx*(Bx - Zx) - Acy*(By - Zy)) - MSZ*MSZ*MSZ)
            + 2*RR*(iabs (Acx*(By - Zy) + Acy*(Bx - Zx))
              + (2*EtaA*(iabs (Bx - Zx) + iabs (By - Zy))
                 + (iabs Acx + iabs Acy + 2*EtaA)*(Br + 2*Eta))) < MSZ*MSZ*MSZ)

end Work.SeedCertRay

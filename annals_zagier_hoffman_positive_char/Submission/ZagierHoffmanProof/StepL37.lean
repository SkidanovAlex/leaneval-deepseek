import Submission.ZagierHoffmanProof.StepL3
import Submission.ZagierHoffmanProof.Counting
import Submission.ZagierHoffmanProof.StepL36

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L37: the H₁ base of Prop 3.2 (k = 1)

★ `H1_exp`: every positive-depth tuple `s` is an admissible expansion of itself —
`AdmExp F (weight r s) 1 s` (a `K`-combination of `1`-admissible tuples of weight
`w(s)`).  This is the base of the outer induction of Prop 3.2 and of the measure
recursion, and it nails the exact interface the later induction must deliver.

  Case s₁ ≤ q: admissible unless `s` is the depth-1 tuple (q); the exception is
  resolved by R1 (`zeta_R1`, StepL2): ζ_A(q) = −D1·ζ_A(1, q−1), and (1, q−1) is
  1-admissible of weight q.
  Case s₁ > q: strong induction on s₁; Lemma 2.9 CW(R1) (`lemma_2_9_zeta`, StepL3)
  at depth r−1 with w1 := s₁−q gives
    ζ_A s + Σ_i (aA i)·ζ_A(ca i) + Σ_j (bB j)·ζ_A(1 :: cb j) = 0
  where each `ca i` has first entry < s₁ (⟹ IH) and weight w(s) (⟹ transport), and
  each `(1 :: cb j)` is 1-admissible of weight w(s) (⟹ admExp_self).  The splice
  (`admExp_combine`, StepL36) assembles the expansion.

Supporting infrastructure proved here: `expTail_pad0`, `tailWeight` (the weight of
the tail after the first entry), `zeta_leading_eq_s` (the Lemma-2.9 leading tuple
`(s₁,…,s_r)` has the ζ-value of `s`, via `zeta_reindex_eq`), `head_one_weight` and
`aSide_weight_lt` (the weight/first-entry content of the Lemma-2.9 bounds),
`kAdm1_pair_one`, `admExp_weight_transport` (transport an expansion along a weight
equality), and the admissible-member helper proofs.

LEAN NOTES: `Finset.sum_neg` in this Mathlib is the ordered-<0 theorem — the negated
sum is `Finset.sum_neg_distrib`; PNat-ext equalities need the ℕ-level goal stated
explicitly (change/coes); the IH `r`-argument is implicit — pass `(r := …)`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- Padding of the tail: `pad0 (expTail s) t = pad0 s (1+t)`. -/
lemma expTail_pad0 (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+) (t : ℕ) :
    pad0 (expTail s) t = pad0 s (1 + t) := by
  classical
  by_cases ht : t < r - 1
  · have ht' : t < r - 1 := ht
    have h1 : 1 + t < r := by omega
    have he : (expTail s) ⟨t, ht'⟩ = s ⟨1 + t, h1⟩ := by
      dsimp [expTail]
      change s ⟨t + 1, by omega⟩ = s ⟨1 + t, h1⟩
      have hind : (⟨t + 1, by omega⟩ : Fin r) = ⟨1 + t, by omega⟩ := by
        apply Fin.ext
        change t + 1 = 1 + t
        omega
      rw [hind]
    rw [pad0_of_lt (expTail s) ht', pad0_of_lt s h1]
    exact congrArg (fun q : ℕ+ => (q : ℕ)) he
  · have hge : r - 1 ≤ t := le_of_not_gt ht
    have hge' : r ≤ 1 + t := by omega
    rw [pad0_of_ge (expTail s) hge, pad0_of_ge s hge']

/-- The tail of `s` (after the first entry) has weight `weight r s − s₁`. -/
lemma tailWeight (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+) :
    weight (r - 1) (expTail s) + (s ⟨0, hr⟩ : ℕ) = weight r s := by
  classical
  have hr1 : r = 1 + (r - 1) := by omega
  have hp1 : psum s 1 = (s ⟨0, hr⟩ : ℕ) := by
    change (∑ x ∈ Finset.range 1, pad0 s x) = (s ⟨0, hr⟩ : ℕ)
    rw [Finset.sum_range_one]
    exact pad0_of_lt s hr
  have hsum0 := Finset.sum_range_add (f := pad0 s) 1 (r - 1)
  have hsum : psum s r = psum s 1 + (∑ t ∈ Finset.range (r - 1), pad0 s (1 + t)) := by
    change (∑ x ∈ Finset.range r, pad0 s x) =
      (∑ x ∈ Finset.range 1, pad0 s x) + (∑ t ∈ Finset.range (r - 1), pad0 s (1 + t))
    have hrng : Finset.range r = Finset.range (1 + (r - 1)) := congrArg Finset.range hr1
    rw [hrng]
    exact hsum0
  have htail : (∑ t ∈ Finset.range (r - 1), pad0 s (1 + t)) =
      psum (expTail s) (r - 1) := by
    change (∑ t ∈ Finset.range (r - 1), pad0 s (1 + t)) =
      (∑ t ∈ Finset.range (r - 1), pad0 (expTail s) t)
    apply Finset.sum_congr rfl
    intro t ht
    exact (expTail_pad0 r hr s t).symm
  calc
    weight (r - 1) (expTail s) + (s ⟨0, hr⟩ : ℕ)
        = psum (expTail s) (r - 1) + (s ⟨0, hr⟩ : ℕ) := by
          rw [psum_self (expTail s)]
    _ = (s ⟨0, hr⟩ : ℕ) + psum (expTail s) (r - 1) := by omega
    _ = psum s 1 + psum (expTail s) (r - 1) := by rw [hp1]
    _ = psum s r := by
          rw [hsum, htail]
    _ = weight r s := psum_self s
/-- The `(q+w1)::B`-shaped leading tuple (w1 := s₁−q) has the same ζ-value as `s`. -/
lemma zeta_leading_eq_s (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) :
    ζ_A F (consVec ⟨(qExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F),
        Nat.add_pos_left (PNat.pos (qExp F)) ((s ⟨0, hr⟩ : ℕ) - Nat.card F)⟩
        (expTail s)) = ζ_A F s := by
  classical
  have hrr : (r - 1) + 1 = r := by omega
  let x : ℕ+ := ⟨(qExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F),
    Nat.add_pos_left (PNat.pos (qExp F)) ((s ⟨0, hr⟩ : ℕ) - Nat.card F)⟩
  have hpt : ∀ i : Fin ((r - 1) + 1),
      (consVec x (expTail s)) i = s (Fin.cast hrr i) := by
    intro i
    by_cases hz : (i : ℕ) = 0
    · have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by simpa using hz)
      rw [hi0]
      rw [consVec_zero x (expTail s)]
      apply Subtype.ext
      have hc0 : s (Fin.cast hrr ⟨0, by omega⟩) = s ⟨0, hr⟩ := by
        apply congrArg s
        apply Fin.ext
        simp
      rw [hc0]
      have hq : (qExp F : ℕ) = Nat.card F := by rfl
      change (qExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F) = (s ⟨0, hr⟩ : ℕ)
      rw [hq]
      omega
    · have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hz
      let j : Fin (r - 1) := ⟨(i : ℕ) - 1, by
        have hlt : (i : ℕ) < (r - 1) + 1 := i.isLt
        omega⟩
      have hij : i = ⟨(j : ℕ) + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      rw [hij]
      have hcs' : (consVec x (expTail s)) ⟨(j : ℕ) + 1, by omega⟩ = expTail s j := by
        simpa using (consVec_succ x (expTail s) j)
      rw [hcs']
      change s ⟨(j : ℕ) + 1, by omega⟩ = s (Fin.cast hrr ⟨(j : ℕ) + 1, by omega⟩)
      apply congrArg s
      apply Fin.ext
      simp
  calc
    ζ_A F (consVec ⟨(qExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F),
        Nat.add_pos_left (PNat.pos (qExp F)) ((s ⟨0, hr⟩ : ℕ) - Nat.card F)⟩ (expTail s))
        = ζ_A F (fun i : Fin ((r - 1) + 1) => s (Fin.cast hrr i)) := by
          exact congrArg (ζ_A F) (funext (fun i => hpt i))
    _ = ζ_A F s := zeta_reindex_eq F hrr s

/-- The weight of a 1-admissible-output tuple `(1 :: cb)` with `cb ≤ (q−1)+W`: `w`. -/
lemma head_one_weight (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depb : ι → ℕ) (hdepb : ∀ j, 0 < depb j) (cb : ∀ j, Fin (depb j) → ℕ+)
    (hleB : ∀ j, LePad (cb j) (single (qMinusExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s))) :
    ∀ j, weight (depb j + 1) (consVec oneExp (cb j)) = weight r s := by
  classical
  intro j
  let w1 : ℕ+ := ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
  have hw1 : (w1 : ℕ) = (s ⟨0, hr⟩ : ℕ) - Nat.card F := by rfl
  let B : Fin (r - 1) → ℕ+ := expTail s
  have hleB' : LePad (cb j) (single (qMinusExp F)) (consVec w1 B) := by
    simpa [w1, B] using hleB j
  have hwt := (hleB').1
  have hwcb : weight (depb j) (cb j) = (qMinusExp F : ℕ) +
      (w1 : ℕ) + weight (r - 1) B := by
    -- LePad weight: weight (depb j)(cb j) = weight 1 (single qMinusExp) + weight ((r−1)+1)(consVec w1 B)
    have h1 := hleB'.1
    -- h1 : weight (depb j)(cb j) = weight 1 (single (qMinusExp F)) + weight ((r-1)+1)(consVec w1 B)
    calc
      weight (depb j) (cb j) = weight 1 (single (qMinusExp F)) + weight ((r - 1) + 1) (consVec w1 B) := h1
      _ = (qMinusExp F : ℕ) + (weight ((r - 1) + 1) (consVec w1 B)) := by rw [weight_single]
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - 1) B) := by rw [weight_consVec]
      _ = (qMinusExp F : ℕ) + (w1 : ℕ) + weight (r - 1) B := by omega
  have h1': (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  calc
    weight (depb j + 1) (consVec oneExp (cb j))
        = (oneExp : ℕ) + weight (depb j) (cb j) := by
          rw [weight_consVec]
    _ = 1 + ((qMinusExp F : ℕ) + (w1 : ℕ) + weight (r - 1) B) := by
          rw [hwcb]
          rfl
    _ = Nat.card F + ((w1 : ℕ) + weight (r - 1) B) := by
          rw [h1']
          omega
    _ = (s ⟨0, hr⟩ : ℕ) + weight (r - 1) B := by
          rw [hw1]
          omega
    _ = weight r s := by
          -- s₁ + tailW = weight r s (tailWeight); B = expTail s
          have ht := tailWeight r hr s
          have hB : weight (r - 1) B = weight (r - 1) (expTail s) := by rfl
          rw [hB]
          omega


/-- Transport of an admissible expansion along a weight equality. -/
lemma admExp_weight_transport (w w' k : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (h : AdmExp F w' k s) (hww : w' = w) : AdmExp F w k s := by
  classical
  rcases h with ⟨ι, fin, dep, hdep, c, a, hwt, hadm, hid⟩
  refine ⟨ι, fin, dep, hdep, c, a, ?_, hadm, hid⟩
  intro i
  rw [← hww]
  exact hwt i

/-- The `a`-side members of Lemma 2.9 at depth (r−1) have weight `w(s)` and first
entry `< s₁`. -/
lemma aSide_weight_lt (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depa : ι → ℕ) (hdepa : ∀ i, 0 < depa i) (ca : ∀ i, Fin (depa i) → ℕ+)
    (hleA : ∀ i, LePad (ca i) (single (qExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s)) ∧
        ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) +
          ((s ⟨0, hr⟩ : ℕ) - Nat.card F)) :
    ∀ i, weight (depa i) (ca i) = weight r s ∧
      ((ca i) ⟨0, hdepa i⟩ : ℕ) < (s ⟨0, hr⟩ : ℕ) := by
  classical
  intro i
  constructor
  · let w1 : ℕ+ := ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
    have hw1 : (w1 : ℕ) = (s ⟨0, hr⟩ : ℕ) - Nat.card F := by rfl
    let B : Fin (r - 1) → ℕ+ := expTail s
    have hleA' : LePad (ca i) (single (qExp F)) (consVec w1 B) := by
      simpa [w1, B] using (hleA i).1
    have h1 := hleA'.1
    calc
      weight (depa i) (ca i) = weight 1 (single (qExp F)) + weight ((r - 1) + 1) (consVec w1 B) := h1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - 1) B) := by
            rw [weight_single, weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + weight (r - 1) B) := by rfl
      _ = (s ⟨0, hr⟩ : ℕ) + weight (r - 1) B := by rw [hw1]; omega
      _ = weight r s := by
            have ht := tailWeight r hr s
            rw [show weight (r - 1) B = weight (r - 1) (expTail s) by rfl]
            omega
  · have hlt := (hleA i).2
    -- (qExp : ℕ) + ((s₁) − q) = s₁
    have hq : (qExp F : ℕ) = Nat.card F := by rfl
    have hsum : (qExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F) = (s ⟨0, hr⟩ : ℕ) := by
      rw [hq]
      omega
    simpa [hsum] using hlt

/-- 1-admissibility of a depth-`2` tuple with first entry `1`. -/
lemma kAdm1_pair_one (q : ℕ) (b : ℕ+) (hq1 : 1 ≤ q) :
    kAdmissible q (pair oneExp b) 1 := by
  constructor
  · intro x hx
    have hx0 : x = 0 := by omega
    subst x
    rw [pad0_of_lt (pair oneExp b) (by omega : 0 < 2)]
    change ((pair oneExp b) ⟨0, by omega⟩ : ℕ) ≤ q
    rw [pair_zero]
    exact hq1
  · intro hc2
    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
    omega

/-- ★ Prop 3.2 at k = 1 (the base of the outer induction): every tuple `s` of positive
depth is an admissible expansion of itself (weight `weight r s`, `1`-admissible
outputs).  Case s₁ ≤ q: admissible unless the depth-1 tuple (q), which R1 resolves;
case s₁ > q: Lemma-2.9 CW(R1) with strong induction on s₁. -/
theorem H1_exp (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+) : AdmExp F (weight r s) 1 s := by
  classical
  have hmain : ∀ (v : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+),
      (s ⟨0, hr⟩ : ℕ) = v → AdmExp F (weight r s) 1 s := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
        intro r hr s hv
        let q : ℕ := Nat.card F
        let s1 : ℕ := (s ⟨0, hr⟩ : ℕ)
        have hq1 : 1 ≤ q := by
          have h2 : 2 ≤ Nat.card F := card_ge_two F
          omega
        by_cases hle : s1 ≤ q
        · by_cases hdq : r = 1 ∧ s1 = q
          · -- s = (q): R1
            have hr1 : r = 1 := hdq.1
            have hq' : (s ⟨0, hr⟩ : ℕ) = q := hdq.2
            subst r
            have hmain1 : AdmExp F q 1 (single (qExp F)) := by
              -- expansion via R1: ζ(q) = −D1·ζ(1, q−1)
              have hdepP : ∀ i : PUnit, 0 < (2 : ℕ) := fun i => by omega
              refine ⟨PUnit, inferInstance, (fun _ : PUnit => 2), hdepP,
                (fun _ : PUnit => pair oneExp (qMinusExp F)), (fun _ : PUnit => -D1rat F), ?_, ?_, ?_⟩
              · intro i
                -- weight 2 (pair oneExp qMinusExp) = q
                rw [weight_pair]
                rw [show (oneExp : ℕ) = 1 by rfl]
                rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
                have hq1' : 1 ≤ Nat.card F := by
                  have h2 : 2 ≤ Nat.card F := card_ge_two F
                  omega
                omega
              · intro i
                exact kAdm1_pair_one (Nat.card F) (qMinusExp F) (by
                  have h2 : 2 ≤ Nat.card F := card_ge_two F
                  omega)
              · -- ζ(single qExp) = ((−D1rat):K∞)·ζ(pair oneExp qMinusExp)
                have hcast : (((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) =
                    -(D1rat F : RatFunc.CompletionAtInfty F)) := by
                  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-D1rat F)) =
                    -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (D1rat F))
                  rw [map_neg]
                have hmain1c : ζ_A F (single (qExp F)) =
                    ((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
                      ζ_A F (pair oneExp (qMinusExp F)) := by
                  calc
                    ζ_A F (single (qExp F))
                        = -(D1c F * ζ_A F (pair oneExp (qMinusExp F))) := by
                          exact eq_neg_of_add_eq_zero_left (zeta_R1 F)
                    _ = ((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
                          ζ_A F (pair oneExp (qMinusExp F)) := by
                          rw [hcast]
                          have hd : (D1rat F : RatFunc.CompletionAtInfty F) = D1c F := D1c_eq_D1rat F
                          rw [hd]
                          ring
                simpa using hmain1c
            have hw' : weight 1 s = q := by
              change (∑ i : Fin 1, (s i : ℕ)) = q
              rw [Finset.sum_fin_eq_sum_range]
              rw [Finset.sum_range_one]
              simpa using hq'
            have hsingle : ζ_A F s = ζ_A F (single (qExp F)) := by
              apply congrArg (ζ_A F)
              funext i
              change s i = qExp F
              apply Subtype.ext
              have hqexp : (qExp F : ℕ) = Nat.card F := by rfl
              have hs : (s i : ℕ) = (qExp F : ℕ) := by
                have hi0 : i = ⟨0, by omega⟩ := by
                  apply Fin.ext
                  simp
                rw [hi0]
                rw [hqexp]
                simpa [q] using hq'
              exact hs
            -- transport hmain1 (AdmExp q 1 (single qExp)) to AdmExp (weight 1 s) 1 s
            have htrans : AdmExp F q 1 s := by
              rcases hmain1 with ⟨ι, fin, dep, hdep, c, a, hwt, hadm, hid⟩
              refine ⟨ι, fin, dep, hdep, c, a, hwt, hadm, ?_⟩
              rw [hsingle]
              exact hid
            exact admExp_weight_transport F (weight 1 s) q 1 s rfl htrans hw'.symm
          · -- s₁ ≤ q and not (r=1 ∧ s₁=q): s is 1-admissible
            have hadm : kAdmissible (Nat.card F) s 1 := by
              constructor
              · intro x hx
                have hx0 : x = 0 := by omega
                subst x
                change pad0 s 0 ≤ Nat.card F
                have hp : pad0 s 0 = (s ⟨0, hr⟩ : ℕ) := pad0_of_lt s hr
                rw [hp]
                dsimp [s1, q] at hle
                exact hle
              · intro hc2
                rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
                apply hdq
                constructor
                · omega
                · dsimp [s1, q]
                  have hr1' : r = 1 := by omega
                  subst r
                  simpa using hlast
            exact admExp_self F (weight r s) 1 hr s rfl hadm
        · -- q < s₁
          have hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ) := by
            dsimp [q, s1] at hle
            omega
          let w1 : ℕ+ := ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
          rcases lemma_2_9_zeta F (r - 1) w1 (expTail s) with
            ⟨ιa, fina, depa, hdepa, ca, aA, ιb, finb, depb, hdepb, cb, bB, hleA, hleB, hid⟩
          letI : Fintype ιa := fina
          letI : Fintype ιb := finb
          -- leading has the same ζ-value as s
          have hlead : ζ_A F (consVec ⟨(qExp F : ℕ) + (w1 : ℕ),
              Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ (expTail s)) = ζ_A F s := by
            simpa [w1] using (zeta_leading_eq_s F r hr s hgt)
          have hid0 : ζ_A F s +
              (∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) +
              (∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                  ζ_A F (consVec oneExp (cb j)))) = 0 := by
            rw [hlead] at hid
            simpa [w1] using hid
          -- ζ_A s = −(a-sum + b-sum)
          have hneg : ζ_A F s = -((∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) +
              (∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                  ζ_A F (consVec oneExp (cb j))))) := by
            have hz := eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hid0)
            exact hz
          -- combined member family
          let ιc : Type := ιa ⊕ ιb
          letI : Fintype ιc := inferInstance
          let depc : ιc → ℕ := fun p => match p with | Sum.inl i => depa i | Sum.inr j => depb j + 1
          have hdepc : ∀ p : ιc, 0 < depc p := by
            intro p
            cases p with
            | inl i => dsimp [depc]; exact hdepa i
            | inr j => dsimp [depc]; omega
          let cc : ∀ p : ιc, Fin (depc p) → ℕ+ := fun p => match p with
            | Sum.inl i => ca i
            | Sum.inr j => consVec oneExp (cb j)
          let ac : ιc → RatFunc F := fun p => match p with
            | Sum.inl i => -(aA i)
            | Sum.inr j => -(bB j)
          have hidc : ζ_A F s = ∑ p : ιc, (((ac p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (cc p)) := by
            rw [Fintype.sum_sum_type]
            dsimp [ac, cc]
            rw [hneg]
            rw [neg_add]
            congr 2
            · calc
                -((∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))))
                    = (∑ i : ιa, -(((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) := by
                      exact (Finset.sum_neg_distrib (s := Finset.univ) (fun i : ιa =>
                        (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i)))).symm
                _ = (∑ i : ιa, (((-aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      have hcast : (((-aA i : RatFunc F) : RatFunc.CompletionAtInfty F) =
                          -((aA i : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
                        change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-aA i)) =
                          -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (aA i))
                        rw [map_neg]
                      rw [hcast]
                      ring
            · calc
                -((∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                    ζ_A F (consVec oneExp (cb j)))))
                    = (∑ j : ιb, -(((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                        ζ_A F (consVec oneExp (cb j)))) := by
                      exact (Finset.sum_neg_distrib (s := Finset.univ) (fun j : ιb =>
                        (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                          ζ_A F (consVec oneExp (cb j))))).symm
                _ = (∑ j : ιb, (((-bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                      ζ_A F (consVec oneExp (cb j)))) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      have hcast : (((-bB j : RatFunc F) : RatFunc.CompletionAtInfty F) =
                          -((bB j : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
                        change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-bB j)) =
                          -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (bB j))
                        rw [map_neg]
                      rw [hcast]
                      ring
          -- per-member expansions
          have e : ∀ p : ιc, AdmExp F (weight r s) 1 (cc p) := by
            intro p
            cases p with
            | inl i =>
                -- IH on ca i: first entry < s₁
                have ha := aSide_weight_lt F r hr s hgt depa hdepa ca hleA i
                have hfirst : ((ca i) ⟨0, hdepa i⟩ : ℕ) < v := by
                  simpa [hv] using ha.2
                have hw' : weight (depa i) (ca i) = weight r s := ha.1
                have hih := ih (((ca i) ⟨0, hdepa i⟩ : ℕ)) hfirst (r := depa i) (hdepa i) (ca i) rfl
                -- hih : AdmExp F (weight (depa i)(ca i)) 1 (ca i); transport along hw'
                exact admExp_weight_transport F (weight r s) (weight (depa i) (ca i)) 1 (ca i) hw' hih hw'
            | inr j =>
                -- (1 :: cb j) is 1-admissible of weight weight r s
                have hwj := head_one_weight F r hr s hgt depb hdepb cb hleB j
                have h1ad : kAdmissible (Nat.card F) (consVec oneExp (cb j)) 1 := by
                  -- depth depb j + 1 ≥ 2, first entry 1
                  constructor
                  · intro x hx
                    have hx0 : x = 0 := by omega
                    subst x
                    change pad0 (consVec oneExp (cb j)) 0 ≤ Nat.card F
                    have h00 : 0 < depb j + 1 := by omega
                    have hp : pad0 (consVec oneExp (cb j)) 0 =
                        ((consVec oneExp (cb j)) ⟨0, h00⟩ : ℕ) :=
                      pad0_of_lt (consVec oneExp (cb j)) h00
                    rw [hp]
                    have hc := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero oneExp (cb j))
                    rw [hc]
                    exact hq1
                  · intro hc2
                    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
                    -- depth depb j + 1 = r-arg of kAdmissible: depb j + 1 ≤ 1 impossible
                    have hd := hdepb j
                    omega
                exact admExp_self F (weight r s) 1 (by omega : 0 < depb j + 1) (consVec oneExp (cb j)) hwj h1ad
          -- assemble
          exact admExp_combine F (weight r s) 1 s depc hdepc cc ac hidc e
  exact hmain (s ⟨0, hr⟩ : ℕ) hr s rfl



end ZagierHoffmanPositiveChar

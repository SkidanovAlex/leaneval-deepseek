import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.chirpAux

/-!
# `Work.Transform.chirpPostWord`

Given a word that computes the pointwise conjugate `ab` of a disc vector `a` **consuming** the
precision `p` (`int p :: cvecVal a :: R ↦ cvecVal ab :: int p :: R`, as produced by
`Work.Transform.conjVecWord`), `chirpPostWord` wraps it into a word that *keeps* the original `a`
below the output:

`cvecVal a :: int p :: R ↦ cvecVal a :: cvecVal ab :: int p :: R`.

The program is `pick 0 ;;; roll 2 ;;; conjProg ;;; roll 2`:

* `pick 0` duplicates the top value (`a`), giving `a :: a :: p :: R`;
* `roll 2` moves `p` to the top, giving `p :: a :: a :: R`, the precondition of the conjugate word
  with the frame parameter `R` replaced by `a :: R`;
* `conjProg` conjugates the first `a`, giving `ab :: p :: a :: R`;
* `roll 2` moves the preserved `a` back to the top, giving `a :: ab :: p :: R`.

Every stage costs `O(n p²)` (`n` is the vector length); the four stage budgets add up to
`K·(n·p² + 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH

/-- The conjugation post-condition: same length, still in the disc, pointwise conjugate. -/
def ConjPost (p n : ℕ) (a ab : List (ℤ × ℤ)) : Prop :=
  ab.length = n ∧ InDiscVec p n ab ∧
    ∀ i < n, ab.getD i (0, 0) = ((a.getD i (0, 0)).1, -(a.getD i (0, 0)).2)

/-- Encoding size of a disc vector, in the form used by the cost budget `n p² + 1`. -/
theorem vsz_cvecVal_le_twelve {p n : ℕ} {a : List (ℤ × ℤ)} (hp : 100 ≤ p) (hn : 1 ≤ n)
    (h : InDiscVec p n a) : vsz (cvecVal a) ≤ 12 * (n * p ^ 2) := by
  have h1 := chirpAux_vsz_cvecVal_le h
  nlinarith [hp, hn]

/-- Encoding size of the precision value `int p` (`p ≥ 100`, `n ≥ 1`). -/
theorem vsz_int_le_four {p n : ℕ} (hp : 100 ≤ p) (hn : 1 ≤ n) :
    vsz (Val.int (p : ℤ)) ≤ 4 * (n * p ^ 2) := by
  have h : vsz (Val.int (p : ℤ)) ≤ p + 3 := by
    rw [chirpAux_vsz_int, isz, Int.natAbs_natCast]
    have h2 : p.size ≤ p + 1 :=
      Nat.size_le.mpr (lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ p)))
    omega
  nlinarith [hp, hn]

/-- The conjugate word's budget `Kc (n p²) + Kc` fits in `2 Kc (n p² + 1)`. -/
theorem cost_conj (Kc n p : ℕ) :
    Kc * (n * p ^ 2) + Kc ≤ 2 * Kc * (n * p ^ 2 + 1) := by
  have h : Kc * (n * p ^ 2) + Kc = Kc * (n * p ^ 2 + 1) := by ring
  rw [h]
  calc Kc * (n * p ^ 2 + 1) = Kc * (n * p ^ 2 + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ Kc * (n * p ^ 2 + 1) * 2 := Nat.mul_le_mul_left _ (by norm_num)
    _ = 2 * Kc * (n * p ^ 2 + 1) := by ring

theorem chirpPostWord (hK : HvdH.KernelLib) (hI : HvdH.IntLib)
    (conjProg : HvdH.Cmd) (Kc : ℕ)
    (hconj : ∀ (main : HvdH.Cmd) (p n : ℕ) (a : List (ℤ × ℤ)) (R : List HvdH.Val),
      100 ≤ p → 1 ≤ n → a.length = n → HvdH.InDiscVec p n a →
      HvdH.WordR main conjProg (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R)
        (fun vs out => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
          ∃ (ab : List (ℤ × ℤ)), out = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
          ab.length = n ∧ HvdH.InDiscVec p n ab ∧
          ∀ i < n, ab.getD i (0, 0) = ((a.getD i (0, 0)).1, -(a.getD i (0, 0)).2))
        (fun _ => Kc * (n * p ^ 2) + Kc)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p n : ℕ) (a : List (ℤ × ℤ)) (R : List HvdH.Val),
      100 ≤ p → 1 ≤ n → a.length = n → HvdH.InDiscVec p n a →
      HvdH.WordR main prog (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
        (fun vs out => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R ∧
          ∃ (ab : List (ℤ × ℤ)),
            out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
          ab.length = n ∧ HvdH.InDiscVec p n ab ∧
          ∀ i < n, ab.getD i (0, 0) = ((a.getD i (0, 0)).1, -(a.getD i (0, 0)).2))
        (fun _ => K * (n * p ^ 2) + K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := hK.pick
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  refine ⟨.seq (pickP 0) (.seq (rollP 2) (.seq conjProg (rollP 2))),
    1000 * (Kpick + Kroll + Kc + 1), ?_⟩
  intro main p n a R hp hn hlen hdisc
  -- ## Stage 1: `pick 0` : `a :: p :: R ↦ a :: a :: p :: R`
  have h1 : HvdH.WordR main (pickP 0)
      (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => out = HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ => 12 * Kpick * (n * p ^ 2 + 1)) := by
    refine hK.conseq main (pickP 0) _ _ _ _ _ _ (hpick main 0) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; simpa using hout
    · intro vs hvs
      rw [hvs]
      have hS := vsz_cvecVal_le_twelve hp hn hdisc
      have he : (((HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R).take 1).map HvdH.vsz).sum
          = HvdH.vsz (HvdH.cvecVal a) := by simp
      rw [he]
      nlinarith [hS]
  -- ## Stage 2: `roll 2` : `a :: a :: p :: R ↦ p :: a :: a :: R`
  have h2 : HvdH.WordR main (rollP 2)
      (fun vs => vs = HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => out = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R)
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1)) := by
    refine hK.conseq main (rollP 2) _ _ _ _ _ _ (hroll main 2) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; simp
    · intro vs out hvs hout; rw [hvs] at hout; simpa using hout
    · intro vs hvs
      rw [hvs]
      have hS := vsz_cvecVal_le_twelve hp hn hdisc
      have hP := vsz_int_le_four hp hn
      have he : (((HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R).take 3).map
            HvdH.vsz).sum
          = HvdH.vsz (HvdH.cvecVal a) + HvdH.vsz (HvdH.cvecVal a)
            + HvdH.vsz (HvdH.Val.int (p : ℤ)) := by
        simp; omega
      rw [he]
      nlinarith [hS, hP]
  -- ## Stage 3: the conjugate word, run on `p :: a :: a :: R`
  have h3 : HvdH.WordR main conjProg
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R)
      (fun vs out => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R ∧
        ∃ ab, out = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
          ConjPost p n a ab)
      (fun _ => 2 * Kc * (n * p ^ 2 + 1)) := by
    refine hK.conseq main conjProg _ _ _ _ _ _
      (hconj main p n a (HvdH.cvecVal a :: R) hp hn hlen hdisc) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hout; exact hout
    · intro vs hvs; exact cost_conj Kc n p
  -- ## Stage 4: `roll 2` : `ab :: p :: a :: R ↦ a :: ab :: p :: R`
  have h4 : HvdH.WordR main (rollP 2)
      (fun vs => ∃ ab, vs = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
        ConjPost p n a ab)
      (fun vs out => ∃ ab, vs = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
        ConjPost p n a ab ∧ out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1)) := by
    refine hK.conseq main (rollP 2) _ _ _ _ _ _ (hroll main 2) ?_ ?_ ?_
    · intro vs hvs
      obtain ⟨ab, rfl, -⟩ := hvs
      simp
    · intro vs out hvs hout
      obtain ⟨ab, rfl, hcp⟩ := hvs
      refine ⟨ab, rfl, hcp, ?_⟩
      simpa using hout
    · intro vs hvs
      obtain ⟨ab, rfl, hcp⟩ := hvs
      have hSp := vsz_cvecVal_le_twelve hp hn hcp.2.1
      have hS := vsz_cvecVal_le_twelve hp hn hdisc
      have hP := vsz_int_le_four hp hn
      have he : (((HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R).take 3).map
            HvdH.vsz).sum
          = HvdH.vsz (HvdH.cvecVal ab) + HvdH.vsz (HvdH.Val.int (p : ℤ))
            + HvdH.vsz (HvdH.cvecVal a) := by
        simp; omega
      rw [he]
      nlinarith [hSp, hS, hP]
  -- ## Composition: `conjProg ;;; roll 2`
  have hinner := hK.seq main conjProg (rollP 2)
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R)
      (fun vs out => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R ∧
        ∃ ab, out = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
          ConjPost p n a ab)
      (fun _ => 2 * Kc * (n * p ^ 2 + 1))
      (fun vs => ∃ ab, vs = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
        ConjPost p n a ab)
      (fun vs out => ∃ ab, vs = HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: R ∧
        ConjPost p n a ab ∧ out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1))
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1))
      h3 h4 (fun vs mid _ hq => ⟨hq.2, le_refl _⟩)
  have hinner' : HvdH.WordR main (.seq conjProg (rollP 2))
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R)
      (fun vs out => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R ∧
        ∃ ab, out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧ ConjPost p n a ab)
      (fun _ => 2 * Kc * (n * p ^ 2 + 1) + 87 * Kroll * (n * p ^ 2 + 1)) := by
    refine hK.conseq main (.seq conjProg (rollP 2)) _ _ _ _ _ _ hinner
      (fun vs hvs => hvs) ?_ (fun vs _ => le_refl _)
    intro vs out hvs hq
    obtain ⟨m, ⟨-, ab, -, hcp⟩, ab', -, hcp', hout⟩ := hq
    exact ⟨hvs, ab', hout, hcp'⟩
  -- ## Composition: `roll 2 ;;; conjProg ;;; roll 2`
  have htail := hK.seq main (rollP 2) (.seq conjProg (rollP 2))
      (fun vs => vs = HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => out = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R)
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1))
      (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R)
      (fun vs out => vs = HvdH.Val.int (p : ℤ) :: HvdH.cvecVal a :: HvdH.cvecVal a :: R ∧
        ∃ ab, out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧ ConjPost p n a ab)
      (fun _ => 2 * Kc * (n * p ^ 2 + 1) + 87 * Kroll * (n * p ^ 2 + 1))
      (fun _ => 2 * Kc * (n * p ^ 2 + 1) + 87 * Kroll * (n * p ^ 2 + 1))
      h2 hinner' (fun vs mid _ hq => ⟨hq, le_refl _⟩)
  have htail' : HvdH.WordR main (.seq (rollP 2) (.seq conjProg (rollP 2)))
      (fun vs => vs = HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => ∃ ab, out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
        ConjPost p n a ab)
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1) + (2 * Kc * (n * p ^ 2 + 1)
        + 87 * Kroll * (n * p ^ 2 + 1))) := by
    refine hK.conseq main (.seq (rollP 2) (.seq conjProg (rollP 2))) _ _ _ _ _ _ htail
      (fun vs hvs => hvs) ?_ (fun vs _ => le_refl _)
    intro vs out hvs hq
    obtain ⟨m, -, -, ab, hout, hcp⟩ := hq
    exact ⟨ab, hout, hcp⟩
  -- ## Composition: `pick 0 ;;; roll 2 ;;; conjProg ;;; roll 2`
  have hfinal := hK.seq main (pickP 0) (.seq (rollP 2) (.seq conjProg (rollP 2)))
      (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => out = HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ => 12 * Kpick * (n * p ^ 2 + 1))
      (fun vs => vs = HvdH.cvecVal a :: HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => ∃ ab, out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
        ConjPost p n a ab)
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1) + (2 * Kc * (n * p ^ 2 + 1)
        + 87 * Kroll * (n * p ^ 2 + 1)))
      (fun _ => 87 * Kroll * (n * p ^ 2 + 1) + (2 * Kc * (n * p ^ 2 + 1)
        + 87 * Kroll * (n * p ^ 2 + 1)))
      h1 htail' (fun vs mid _ hq => ⟨hq, le_refl _⟩)
  have hfinal' : HvdH.WordR main (.seq (pickP 0) (.seq (rollP 2) (.seq conjProg (rollP 2))))
      (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
      (fun _ out => ∃ ab, out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
        ConjPost p n a ab)
      (fun _ => 12 * Kpick * (n * p ^ 2 + 1) + (87 * Kroll * (n * p ^ 2 + 1)
        + (2 * Kc * (n * p ^ 2 + 1) + 87 * Kroll * (n * p ^ 2 + 1)))) := by
    refine hK.conseq main (.seq (pickP 0) (.seq (rollP 2) (.seq conjProg (rollP 2)))) _ _ _ _ _ _
      hfinal (fun vs hvs => hvs) ?_ (fun vs _ => le_refl _)
    intro vs out hvs hq
    obtain ⟨m, -, ab, hout, hcp⟩ := hq
    exact ⟨ab, hout, hcp⟩
  -- ## Final re-bounding and post-condition cleanup
  refine hK.conseq main (.seq (pickP 0) (.seq (rollP 2) (.seq conjProg (rollP 2))))
    (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
    (fun vs => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R)
    (fun _ out => ∃ ab, out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
      ConjPost p n a ab)
    (fun vs out => vs = HvdH.cvecVal a :: HvdH.Val.int (p : ℤ) :: R ∧
      ∃ (ab : List (ℤ × ℤ)),
        out = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.Val.int (p : ℤ) :: R ∧
      ab.length = n ∧ HvdH.InDiscVec p n ab ∧
      ∀ i < n, ab.getD i (0, 0) = ((a.getD i (0, 0)).1, -(a.getD i (0, 0)).2))
    (fun _ => 12 * Kpick * (n * p ^ 2 + 1) + (87 * Kroll * (n * p ^ 2 + 1)
      + (2 * Kc * (n * p ^ 2 + 1) + 87 * Kroll * (n * p ^ 2 + 1))))
    (fun _ => 1000 * (Kpick + Kroll + Kc + 1) * (n * p ^ 2) + 1000 * (Kpick + Kroll + Kc + 1))
    hfinal' (fun vs hvs => hvs)
    (fun vs out hvs hq => ⟨hvs, hq⟩)
    (fun vs hvs => by
      have h : 12 * Kpick + 174 * Kroll + 2 * Kc ≤ 1000 * (Kpick + Kroll + Kc + 1) := by
        omega
      have h2 := Nat.mul_le_mul_right (n * p ^ 2 + 1) h
      calc 12 * Kpick * (n * p ^ 2 + 1) + (87 * Kroll * (n * p ^ 2 + 1)
            + (2 * Kc * (n * p ^ 2 + 1) + 87 * Kroll * (n * p ^ 2 + 1)))
          = (12 * Kpick + 174 * Kroll + 2 * Kc) * (n * p ^ 2 + 1) := by ring
        _ ≤ (1000 * (Kpick + Kroll + Kc + 1)) * (n * p ^ 2 + 1) := h2
        _ = 1000 * (Kpick + Kroll + Kc + 1) * (n * p ^ 2)
            + 1000 * (Kpick + Kroll + Kc + 1) := by ring)

end Work.Transform

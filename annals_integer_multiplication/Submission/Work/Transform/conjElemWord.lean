import Mathlib
import Submission.Work.Transform.conjKit
import Submission.Work.Transform.chirpAux

/-!
# `Work.Transform.conjElemWord`: conjugating a single fixed-point coefficient

The value `cfxVal z = cons (int z.1) (int z.2)` on top of the value stack is replaced by
`cfxVal (z.1, -z.2) = cons (int z.1) (int (-z.2))`, i.e. the second component is negated.

The program is the composition

`unconsV ⨾ swap ⨾ neg ⨾ swap ⨾ consV`,

so its cost is `K * (isz z.1 + isz z.2 + 1) + ...`; the hypothesis `z ∈ C̃◦` (`inDisc p z`) gives
`isz z.1, isz z.2 ≤ p + 3`, hence the announced cost bound `K * (p + 1)`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- Monotonicity of `WordR` in pre/post-condition and cost: the same statement as the
`KernelLib.conseq` field, proved directly from the definition (which is available here). -/
theorem wordR_mono {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (h1 : ∀ vs, P' vs → P vs)
    (h2 : ∀ vs out, P' vs → Q vs out → Q' vs out) (h3 : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hp s R hs
  obtain ⟨out, s', n, hQ, hev, hn, hl, hk⟩ := h vs (h1 vs hp) s R hs
  exact ⟨out, s', n, h2 vs out hp hQ, hev, le_trans hn (h3 vs hp), hl, hk⟩

/-- Five `WordR` words with constant costs and concrete singleton pre/post states compose into one
word (left-nested `seq`), the cost being the sum of the five. -/
theorem wordR_seq5 {main : Cmd} {q₁ q₂ q₃ q₄ q₅ : Cmd} {v₀ v₁ v₂ v₃ v₄ v₅ : List Val}
    {a b c d e : ℕ}
    (h₁ : WordR main q₁ (fun vs => vs = v₀) (fun _ out => out = v₁) (fun _ => a))
    (h₂ : WordR main q₂ (fun vs => vs = v₁) (fun _ out => out = v₂) (fun _ => b))
    (h₃ : WordR main q₃ (fun vs => vs = v₂) (fun _ out => out = v₃) (fun _ => c))
    (h₄ : WordR main q₄ (fun vs => vs = v₃) (fun _ out => out = v₄) (fun _ => d))
    (h₅ : WordR main q₅ (fun vs => vs = v₄) (fun _ out => out = v₅) (fun _ => e)) :
    WordR main (.seq (.seq (.seq (.seq q₁ q₂) q₃) q₄) q₅)
      (fun vs => vs = v₀) (fun _ out => out = v₅) (fun _ => a + b + c + d + e) := by
  intro vs hv s R hs
  obtain ⟨o₁, s₁, n₁, hp₁, he₁, hn₁, hl₁, hk₁⟩ := h₁ vs hv s R hs
  obtain ⟨o₂, s₂, n₂, hp₂, he₂, hn₂, hl₂, hk₂⟩ := h₂ o₁ hp₁ s₁ R hl₁
  obtain ⟨o₃, s₃, n₃, hp₃, he₃, hn₃, hl₃, hk₃⟩ := h₃ o₂ hp₂ s₂ R hl₂
  obtain ⟨o₄, s₄, n₄, hp₄, he₄, hn₄, hl₄, hk₄⟩ := h₄ o₃ hp₃ s₃ R hl₃
  obtain ⟨o₅, s₅, n₅, hp₅, he₅, hn₅, hl₅, hk₅⟩ := h₅ o₄ hp₄ s₄ R hl₄
  refine ⟨o₅, s₅, n₁ + n₂ + n₃ + n₄ + n₅, hp₅, ?_, ?_, hl₅, ?_⟩
  · exact Eval.seq (Eval.seq (Eval.seq (Eval.seq he₁ he₂) he₃) he₄) he₅
  · have i₁ : n₁ ≤ a := hn₁
    have i₂ : n₂ ≤ b := hn₂
    have i₃ : n₃ ≤ c := hn₃
    have i₄ : n₄ ≤ d := hn₄
    have i₅ : n₅ ≤ e := hn₅
    show n₁ + n₂ + n₃ + n₄ + n₅ ≤ a + b + c + d + e
    omega
  · intro k hk
    rw [hk₅ k hk, hk₄ k hk, hk₃ k hk, hk₂ k hk, hk₁ k hk]

/-- `isz` is invariant under negation. -/
theorem isz_neg (a : ℤ) : isz (-a) = isz a := by simp [isz, Int.natAbs_neg]

theorem conjElemWord : HvdH.KernelLib → HvdH.IntLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p : ℕ) (z : ℤ × ℤ) (rest : List HvdH.Val),
        HvdH.inDisc p z →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.cfxVal z :: rest)
          (fun _ out => out = HvdH.cfxVal (z.1, -z.2) :: rest)
          (fun _ => K * (p + 1)) := by
  intro hKer hInt
  obtain ⟨q₁, K₁, hq₁⟩ := hKer.unconsV
  obtain ⟨q₂, K₂, hq₂⟩ := hKer.swap
  obtain ⟨q₃, K₃, hq₃⟩ := hInt.neg
  obtain ⟨q₅, K₅, hq₅⟩ := hKer.consV
  refine ⟨.seq (.seq (.seq (.seq q₁ q₂) q₃) q₂) q₅, 16 * (K₁ + K₂ + K₃ + K₅ + 1), ?_⟩
  intro main p z rest hd
  -- 1. split `cons (int z.1) (int z.2)` into its two components
  have hA : WordR main q₁ (fun vs => vs = cfxVal z :: rest)
      (fun _ out => out = .int z.1 :: .int z.2 :: rest) (fun _ => K₁) :=
    wordR_mono (hq₁ main)
      (fun vs hvs => ⟨.int z.1, .int z.2, rest, by rw [hvs]; rfl⟩)
      (fun vs out hvs hQ => by
        obtain ⟨a, b, r, hv, ho⟩ := hQ
        rw [hvs] at hv
        cases hv
        exact ho)
      (fun _ _ => le_rfl)
  -- 2. bring `int z.2` on top
  have hB : WordR main q₂ (fun vs => vs = .int z.1 :: .int z.2 :: rest)
      (fun _ out => out = .int z.2 :: .int z.1 :: rest)
      (fun _ => K₂ * (isz z.1 + isz z.2 + 1)) :=
    wordR_mono (hq₂ main)
      (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hQ => by
        obtain ⟨a, b, r, hv, ho⟩ := hQ
        rw [hvs] at hv
        cases hv
        exact ho)
      (fun vs hvs => by rw [hvs]; simp [chirpAux_vsz_int])
  -- 3. negate the top integer `int z.2`
  have hC : WordR main q₃ (fun vs => vs = .int z.2 :: .int z.1 :: rest)
      (fun _ out => out = .int (-z.2) :: .int z.1 :: rest) (fun _ => K₃ * isz z.2) :=
    wordR_mono (hq₃ main)
      (fun vs hvs => ⟨z.2, .int z.1 :: rest, by rw [hvs]; exact ⟨rfl, trivial⟩⟩)
      (fun vs out hvs hQ => by
        obtain ⟨a, r, hv, ho⟩ := hQ
        rw [hvs] at hv
        cases hv
        exact ho)
      (fun vs hvs => by rw [hvs]; exact le_rfl)
  -- 4. bring `int z.1` back on top
  have hD : WordR main q₂ (fun vs => vs = .int (-z.2) :: .int z.1 :: rest)
      (fun _ out => out = .int z.1 :: .int (-z.2) :: rest)
      (fun _ => K₂ * (isz (-z.2) + isz z.1 + 1)) :=
    wordR_mono (hq₂ main)
      (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hQ => by
        obtain ⟨a, b, r, hv, ho⟩ := hQ
        rw [hvs] at hv
        cases hv
        exact ho)
      (fun vs hvs => by rw [hvs]; simp [chirpAux_vsz_int])
  -- 5. rebuild the pair
  have hE : WordR main q₅ (fun vs => vs = .int z.1 :: .int (-z.2) :: rest)
      (fun _ out => out = cfxVal (z.1, -z.2) :: rest) (fun _ => K₅) :=
    wordR_mono (hq₅ main)
      (fun vs hvs => by rw [hvs]; simp)
      (fun vs out hvs hQ => by
        obtain ⟨a, b, r, hv, ho⟩ := hQ
        rw [hvs] at hv
        cases hv
        rw [ho]
        rfl)
      (fun _ _ => le_rfl)
  refine wordR_mono (wordR_seq5 hA hB hC hD hE) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ => ?_)
  show K₁ + K₂ * (isz z.1 + isz z.2 + 1) + K₃ * isz z.2
      + K₂ * (isz (-z.2) + isz z.1 + 1) + K₅ ≤ 16 * (K₁ + K₂ + K₃ + K₅ + 1) * (p + 1)
  obtain ⟨h1, h2⟩ := chirpAux_isz_le_of_inDisc hd
  rw [isz_neg]
  nlinarith [Nat.zero_le K₁, Nat.zero_le K₂, Nat.zero_le K₃, Nat.zero_le K₅, Nat.zero_le p,
    h1, h2]

end Work.Transform

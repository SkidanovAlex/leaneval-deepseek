import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.piDefs

/-!
# Assembly of `Work.Resample.sliceAu`

The one-dimensional windowed Gaussian resampling word of paper Lemma 4.9, assembled from the
pieces: the fixed-point π word, the weight word, the table word `prep`, the convolution word `q`,
and the two analytic facts (weight accuracy and truncation tail).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- the fixed-point π word (pinned output `uval P`) -/
def AuPiWordSpec : Prop :=
  ∀ (KL : KernelLib) (IL : IntLib), ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (P : ℕ), 100 ≤ P → WordR main prog
      (fun vs => ∃ rest, vs = [Val.int (P : ℤ)] ++ rest)
      (fun vs out => ∃ rest, vs = [Val.int (P : ℤ)] ++ rest ∧
        out = [Val.int (Work.Fx.uval P)] ++ rest)
      (fun _ => K * (P + 1) ^ K)

/-- the weight word (one `auWt` value from `p, α, t, N, auPi p`) -/
def AuWtWordSpec : Prop :=
  ∀ (KL : KernelLib) (IL : IntLib), ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p α t : ℕ) (N : ℤ), (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) →
      (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) → WordR main prog
        (fun vs => ∃ rest, vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ),
          Val.int N, Val.int (auPi p)] ++ rest)
        (fun vs out => ∃ rest, vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ),
          Val.int N, Val.int (auPi p)] ++ rest ∧ out = Val.int (auWt p α t N) :: rest)
        (fun _ => K * (p + 1) ^ K)

/-- the table word `prep` -/
def AuPrepSpec : Prop :=
  ∀ (KL : KernelLib) (IL : IntLib) (LL : LayoutLib) (piProg : Cmd) (Kp : ℕ)
    (piSpec : ∀ (main : Cmd) (P : ℕ), 100 ≤ P → WordR main piProg
      (fun vs => ∃ rest, vs = [Val.int (P : ℤ)] ++ rest)
      (fun vs out => ∃ rest, vs = [Val.int (P : ℤ)] ++ rest ∧
        out = [Val.int (Work.Fx.uval P)] ++ rest)
      (fun _ => Kp * (P + 1) ^ Kp))
    (wtProg : Cmd) (Kw : ℕ)
    (wtSpec : ∀ (main : Cmd) (p α t : ℕ) (N : ℤ), (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) →
      (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) → WordR main wtProg
        (fun vs => ∃ rest, vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ),
          Val.int N, Val.int (auPi p)] ++ rest)
        (fun vs out => ∃ rest, vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (t : ℤ),
          Val.int N, Val.int (auPi p)] ++ rest ∧ out = Val.int (auWt p α t N) :: rest)
        (fun _ => Kw * (p + 1) ^ Kw)), ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (hαp : α ^ 2 < p), WordR main prog
      (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
        out = auPvals p α s t ++ rest)
      (fun _ => K * (t + 1) * (p + 1) ^ K)

/-- the convolution word `q` -/
def AuConvSpec : Prop :=
  ∀ (KL : KernelLib) (IL : IntLib) (LL : LayoutLib), ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm →
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (htp : t < 2 ^ p) (hKN : K * p < N), WordR main prog
      (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧
        u.length = s ∧ (∀ z ∈ u, inDisc p z))
      (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧
        out = cvecVal w :: auPvals p α s t ++ rest ∧ w.length = t ∧ (∀ z ∈ w, inDisc p z) ∧
        (∀ k : Fin t, w.getD k (0,0) = auPhi p α s t (fun j => u.getD j (0,0)) k))
      (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1))

/-- the two properties of `auPhi` -/
def AuFinalSpec : Prop :=
  ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hAnorm : ∀ (u : Fin s → ℂ), ‖(resA s t α).mulVec u‖ ≤ 3 / 4 * ‖u‖)
    (hwt : ∀ (N : ℕ), |(auWt p α t (N : ℤ) : ℝ) - (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) *
      Real.exp (-(Real.pi * (N : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))| ≤ 2)
    (htail : ∀ (u : Fin s → ℂ), ‖u‖ ≤ 1 → ∀ k : Fin t,
      ‖(∑ i ∈ Finset.range (auL p α), ((auWi p α s t (k : ℕ) i : ℝ) : ℂ) *
        u ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩) -
        (resA s t α).mulVec u k‖ ≤ (2 : ℝ) ^ (-(p : ℤ))),
    (∀ (w : Fin s → ℤ × ℤ), (∀ j, inDisc p (w j)) → ∀ k : Fin t, inDisc p (auPhi p α s t w k)) ∧
    (∀ (w : Fin s → ℤ × ℤ), (∀ j, inDisc p (w j)) → ∀ k : Fin t,
      ‖fxC p (auPhi p α s t w k) - (resA s t α).mulVec (fun j => fxC p (w j)) k‖ *
        (2 : ℝ) ^ p < (p : ℝ) ^ 2)

/-- the weight accuracy bound -/
def AuWtErrSpec : Prop :=
  ∀ (p α t : ℕ) (N : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (ht : 1 ≤ t)
    (hpi : |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1),
    |(auWt p α t (N : ℤ) : ℝ) - (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) *
      Real.exp (-(Real.pi * (N : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))| ≤ 2

/-- the truncation-tail bound -/
def AuTailSpec : Prop :=
  ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (hαp : α ^ 2 < p),
    ∀ (u : Fin s → ℂ), ‖u‖ ≤ 1 → ∀ k : Fin t,
      ‖(∑ i ∈ Finset.range (auL p α), ((auWi p α s t (k : ℕ) i : ℝ) : ℂ) *
        u ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩) -
        (resA s t α).mulVec u k‖ ≤ (2 : ℝ) ^ (-(p : ℤ))

/-- the π error bound -/
def AuPiBoundSpec : Prop :=
  ∀ (p : ℕ), 100 ≤ p → |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1

/-- **`sliceAu` assembled from its pieces.** -/
theorem sliceAu_of_pieces (hPiW : AuPiWordSpec) (hWtW : AuWtWordSpec) (hPrep : AuPrepSpec)
    (hConv : AuConvSpec) (hFinal : AuFinalSpec) (hWtErr : AuWtErrSpec) (hTail : AuTailSpec)
    (hPiB : AuPiBoundSpec) :
    ∀ (KL : KernelLib) (IL : IntLib) (LL : LayoutLib) (FL : FxLib) (RM : ResMath1DProp),
      ∃ (prep q : Cmd) (K : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
        (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
        (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
      ∃ (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (P : List Val),
        (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
          WordR main prep
            (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
            (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
              out = P ++ rest)
            (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
        (∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
          WordR main q
            (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
              vs = ofList (u.map cfxVal) :: P ++ rest ∧
              u.length = s ∧ (∀ z ∈ u, inDisc p z))
            (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
              vs = ofList (u.map cfxVal) :: P ++ rest ∧
              out = cvecVal w :: P ++ rest ∧ w.length = t ∧ (∀ z ∈ w, inDisc p z) ∧
              (∀ k : Fin t, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
            (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1))) ∧
        (∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t, inDisc p (Φ w k)) ∧
        (∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t,
          ‖fxC p (Φ w k) - (resA s t α).mulVec (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p
            < (p : ℝ) ^ 2) := by
  intro KL IL LL FL RM
  obtain ⟨piProg, Kp, hpiSpec⟩ := hPiW KL IL
  obtain ⟨wtProg, Kw, hwtSpec⟩ := hWtW KL IL
  obtain ⟨prepProg, Kprep, hprepSpec⟩ := hPrep KL IL LL piProg Kp hpiSpec wtProg Kw hwtSpec
  obtain ⟨qProg, Kq, hqSpec⟩ := hConv KL IL LL
  refine ⟨prepProg, qProg, max Kq (max Kprep 1), ?_⟩
  intro p α s t hs hst hcop htp hα hp hαp hθ
  have ht : 1 ≤ t := by omega
  have hKq : Kq ≤ max Kq (max Kprep 1) := le_max_left _ _
  have hKp : Kprep ≤ max Kq (max Kprep 1) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK1 : 1 ≤ max Kq (max Kprep 1) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hpiB : |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1 := hPiB p hp
  have hwtAll : ∀ (N : ℕ), |(auWt p α t (N : ℤ) : ℝ) - (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) *
      Real.exp (-(Real.pi * (N : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))| ≤ 2 :=
    fun N => hWtErr p α t N hp hα ht hpiB
  have htailAll := hTail p α s t hs hst hcop hα hp hαp
  have hAnorm : ∀ (u : Fin s → ℂ), ‖(resA s t α).mulVec u‖ ≤ 3 / 4 * ‖u‖ :=
    (RM s t α p hs hst hcop hα hαp hθ).2.1
  have hff := hFinal p α s t hs hst hcop htp hα hp hαp hAnorm hwtAll htailAll
  refine ⟨auPhi p α s t, auPvals p α s t, ?_, ?_, hff.1, hff.2⟩
  · -- the table word
    intro main N Cm hCm hMul hKN
    have hKNp : Kprep * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hKp) hKN
    have hW := hprepSpec main p α s t hs hst htp hα hp hαp
    refine KL.conseq (main := main) (p := prepProg)
      (P := fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (P' := fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (Q := fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
        out = auPvals p α s t ++ rest)
      (Q' := fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
        out = auPvals p α s t ++ rest)
      (C := fun _ => Kprep * (t + 1) * (p + 1) ^ Kprep)
      (C' := fun _ => max Kq (max Kprep 1) * (t + 1) * (p + 1) ^ (max Kq (max Kprep 1)))
      hW (fun vs h => h) (fun vs out h1 h2 => h2) ?_
    intro vs _
    have hp1 : (p + 1) ^ Kprep ≤ (p + 1) ^ (max Kq (max Kprep 1)) :=
      Nat.pow_le_pow_right (by omega) hKp
    have h1 : Kprep * (t + 1) ≤ max Kq (max Kprep 1) * (t + 1) :=
      Nat.mul_le_mul_right (t + 1) hKp
    exact le_trans (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_left _ hp1)
  · -- the convolution word
    intro main N Cm hCm hMul hKN
    have hKNq : Kq * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hKq) hKN
    have hW := hqSpec main N Cm hCm hMul p α s t hs hst hα hp hαp htp hKNq
    refine KL.conseq (main := main) (p := qProg)
      (P := fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧
        u.length = s ∧ (∀ z ∈ u, inDisc p z))
      (P' := fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List Val),
        vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧
        u.length = s ∧ (∀ z ∈ u, inDisc p z))
      (Q := fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧
        out = cvecVal w :: auPvals p α s t ++ rest ∧ w.length = t ∧ (∀ z ∈ w, inDisc p z) ∧
        (∀ k : Fin t, w.getD k (0,0) = auPhi p α s t (fun j => u.getD j (0,0)) k))
      (Q' := fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List Val) (w : List (ℤ × ℤ)),
        vs = ofList (u.map cfxVal) :: auPvals p α s t ++ rest ∧
        out = cvecVal w :: auPvals p α s t ++ rest ∧ w.length = t ∧ (∀ z ∈ w, inDisc p z) ∧
        (∀ k : Fin t, w.getD k (0,0) = auPhi p α s t (fun j => u.getD j (0,0)) k))
      (C := fun _ => Kq * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kq * p) + p + 1))
      (C' := fun _ => max Kq (max Kprep 1) * (t + 1) * (Nat.sqrt p + 1) * (α + 1) *
        (Cm (max Kq (max Kprep 1) * p) + p + 1))
      hW (fun vs h => h) (fun vs out h1 h2 => h2) ?_
    intro vs _
    have hCm1 : Cm (Kq * p) ≤ Cm (max Kq (max Kprep 1) * p) :=
      hCm (Nat.mul_le_mul_right p hKq)
    have hlast : Cm (Kq * p) + p + 1 ≤ Cm (max Kq (max Kprep 1) * p) + p + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_right hCm1 p) 1
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hKq le_rfl) le_rfl) le_rfl)
      hlast

end Work.Resample
